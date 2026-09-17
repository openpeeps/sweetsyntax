# A powerful generic parser and AST explorer
# for analyzing programming languages!
#
# (c) 2026 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

## This module implements a Pratt parser that can be configured via a YAML specification.
## The specification defines the syntax of a language, including operator precedence,
## statement keywords, block delimiters, and feature flags. The parser uses this configuration
## to parse source code into a predefined abstract syntax tree (AST) represented by `Node` objects.
## 
## The main components are:
## - `GenericParser`: The core parser object that holds the lexer, current tokens, and configuration tables.
## - `parseExpression`: The Pratt parsing function that handles operator precedence and associativity.
## - `parseStatement`: The function that dispatches to statement handlers based on keywords.
## - `compile`: A function that takes a `SweetSpec` (parsed from YAML) and builds the necessary tables for parsing.
## - `parseScript`: A high-level function that reads a source file, initializes the parser, and produces an AST.

import std/[tables, strutils, math, options, sets, os, macros]

import pkg/openparser/json
import ../[config, sweetlexer]
import ../tokenizer, ./ast

type
  PrefixHandler* = proc(p: var GenericParser, minPrec: int = 0): Node {.closure.}
  StmtHandler* = proc(p: var GenericParser, parentCol: int = -1): Node {.closure.}
  ExpressionHandler* = proc(p: var GenericParser, lhs: Node, minPrec: int): Node {.nimcall.}

  GenericParser* = object
    lexer*: SweetLexer
    prev*, curr*, next*: TokenTuple

    # Language spec data (moved from SweetSpec for compile-time prebuilding)
    symbols*: Table[string, string]
    identifiers*: Table[string, string]
    inlineCommentOpt*: Option[string]
    blockCommentSpec*: array[2, string]

    # Precompiled lookup tables from YAML
    infixTable*: Table[string, InfixEntry]
    assignOps*: Table[string, bool]
    prefixOps*: HashSet[string]
    postfixOps*: HashSet[string]
    keywordPrefixOps*: HashSet[string]

    # Statement keyword > handler name
    stmtKeywords*: Table[string, string]
    # Statement handler name > proc
    stmtHandlers*: Table[string, StmtHandler]
    # Prefix handler registry (for special constructs)
    prefixHandlers*: Table[string, PrefixHandler]
    # Expression handler registry (for language-specific expression transformations)
    expressionHandlers*: Table[string, ExpressionHandler]
    # Language-specific brace `{ }` handler (object literal, set literal, etc.)
    braceHandler*: proc(p: var GenericParser, minPrec: int = 0): Node {.nimcall.}
    expectRegexTokens*: seq[string]
    expectRegexKeywords*: seq[string]
    expectRegexTokenSet*: HashSet[string]
      ## hash-set mirror of `expectRegexTokens` for O(1) checks in `walk`
    expectRegexKeywordSet*: HashSet[string]
      ## hash-set mirror of `expectRegexKeywords` for O(1) checks in `walk`
    blockOpen*, blockClose*: string
    features*: set[LanguageFeature]
      ## Set of enabled language features (e.g. featAsync, featGenerators) that can be used
    strictStatements*: bool
      ## Enforce strict statement termination (PHP-like): a bare `;` raises a
      ## parse error and expression statements must end with `;`.
    statementTerminated*: bool
      ## Set by handlers that consume their own statement terminator (or end
      ## with `}`), so the strict `;` check can be skipped for them.
    noSymbolArgCall*: bool
      ## When set, language-specific bare-call handlers must not treat a
      ## leading `:` symbol as a call argument (used for Ruby `if x: ...`,
      ## hash keys and keyword arguments, which conflict with `attr_accessor :x`).
    inControlClause*: bool
      ## When set, a `{` after a bare TypeName-form operand (`T`, `pkg.T`,
      ## `T[P]`) does NOT start a composite literal: it opens the block of
      ## an `if`/`for`/`switch` header (cf. go/parser's `exprLev < 0`).
      ## Structural literal types (`[]T`, `map[K]V`, `struct{...}`) still do.
    funcDepth*: int
      ## Function-body nesting depth, maintained by language handlers that
      ## need declaration-context checks (e.g. Go rejects nested named
      ## function declarations and imports inside function bodies, while
      ## allowing anonymous function literals there). The engine itself
      ## never touches this counter.
    inTypeContext*: bool
      ## In a type expression: `(` never starts call arguments. Set by
      ## language handlers around type parsing (Go conversions like
      ## `[]byte(s)` apply OUTSIDE the type: the call binds after the
      ## full `[]byte`, not inside its element type).
    inParenGroup*: bool
      ## Inside a `(...)` group (set by parseGroupExpr): a `;` separates
      ## group items, so item parsers must not consume it as their own
      ## statement terminator (Nim `if (let x = ...; x):`, Ruby `(a; b)`).

  
  OpenAstParsingError* = object of CatchableError

#
# Walk helpers
#
proc walk*(p: var GenericParser, offset = 1) {.inline.} =
  p.prev = p.curr
  p.curr = p.next
  # Set expectRegex before reading the next token so the lexer can
  # correctly distinguish regex literals from division after tokens
  # like `=`, `(`, `return`, `var`, etc.
  p.lexer.expectRegex =
    (p.curr.kind == tkPunct and p.curr.value in p.expectRegexTokenSet) or
    (p.curr.kind == tkIdentifier and p.curr.value in p.expectRegexKeywordSet)
  p.next = p.getToken()

proc walkOpt*(p: var GenericParser, val: string) {.inline.} =
  if p.curr.kind == tkPunct and p.curr.value == val:
    walk p

proc error*(p: var GenericParser, msg: string) =
  let context = getContext(p.lexer, p.curr.pos)
  raise newException(OpenAstParsingError,
    "\n" & context & "\nError (" & $p.curr.line & ":" & $p.curr.col & ") " & msg)

proc expect*(p: var GenericParser, expectedKind: SweetTokenKind, msg: string = "") =
  if p.curr.kind != expectedKind:
    let emsg = if msg.len > 0: msg
               else: "Expected " & $expectedKind & ", got " & $p.curr.kind & " ('" & p.curr.value & "')"
    error(p, emsg)

proc expectWalk*(p: var GenericParser, val: string, msg: string = "") =
  if p.curr.kind == tkPunct and p.curr.value == val:
    walk p
  elif val == ";" and p.lexer.tagTerminated:
    # a close tag (e.g. PHP's `?>`) implicitly terminates the statement
    p.lexer.tagTerminated = false
  else:
    let emsg = if msg.len > 0: msg
               else: "Expected '" & val & "', got '" & p.curr.value & "'"
    error(p, emsg)

#
# Pratt parser core
#

proc parsePrefix(p: var GenericParser, minPrec: int = 0): Node
proc parseExpression*(p: var GenericParser, minPrec: int = 0): Node
proc parseStatement*(p: var GenericParser, parentCol: int = -1): Node
proc parseBlock*(p: var GenericParser, indentPos: int = -1): Node

proc cStringOpenQuote(s: string): int =
  ## Index of the opening `"` in a C string token raw (`"..."`,
  ## `L"..."`, `u8"..."`), or -1 when there is none.
  result = 0
  while result < s.len and s[result] in {'u', 'U', 'L'}:
    inc result
  # `u8` prefix
  if result + 1 < s.len and s[result] == '8' and s[result + 1] == '"':
    return result + 1
  if result < s.len and s[result] == '"':
    return result
  return -1

proc canConcatCString(a, b: string): bool =
  ## Both token raws are double-quoted C string literals.
  a.len >= 2 and a[^1] == '"' and cStringOpenQuote(b) >= 0

proc concatCString(a, b: string): string =
  ## Fold two C string token raws, keeping the first literal's prefix:
  ## `"a" "b"` → `"ab"`, `L"a" L"b"` → `L"ab"`.
  let openIdx = cStringOpenQuote(b)
  a[0..^2] & b[openIdx + 1..^1]

#
# Generic prefix handlers
#

proc parseHexFloat*(s: string): float =
  ## Parse a hexadecimal floating-point literal (`0x1.8p3`, `0x.8p-1`,
  ## `0x1P+2`; underscores allowed). The lexer's `extended_numbers`
  ## mode produces these as `tkFloat`, but Nim's `parseFloat` only
  ## handles decimal — so this mirrors it for base 16.
  var t = s.replace("_", "")
  var i = 2 # skip `0x`
  var mant = 0.0
  while i < t.len and t[i] in {'0'..'9', 'a'..'f', 'A'..'F'}:
    mant = mant * 16.0 + float(parseHexInt($t[i]))
    inc i
  if i < t.len and t[i] == '.':
    inc i
    var f = 1.0 / 16.0
    while i < t.len and t[i] in {'0'..'9', 'a'..'f', 'A'..'F'}:
      mant += float(parseHexInt($t[i])) * f
      f /= 16.0
      inc i
  inc i # skip `p`/`P`
  var neg = false
  if i < t.len and t[i] in {'+', '-'}:
    neg = t[i] == '-'
    inc i
  var exp = 0
  while i < t.len and t[i] in {'0'..'9'}:
    exp = exp * 10 + (ord(t[i]) - ord('0'))
    inc i
  if neg: exp = -exp
  result = mant * pow(2.0, float(exp))

proc parseLiteral(p: var GenericParser, minPrec: int = 0): Node =
  ## Handles int, float, string, hex, octal, binary, bigint literals
  case p.curr.kind
  of tkInt:
    let tk = p.curr
    var val = tk.value
    # Strip Nim type suffix like 0'i32, 1'u64
    let apostrophe = val.find('\'')
    if apostrophe >= 0:
      val = val[0 ..< apostrophe]
    result = Node(kind: nkLitInt, valInt: parseInt(val)).stamp(tk)
    walk p
  of tkFloat:
    let fv = p.curr.value
    if fv.len > 1 and fv[0] == '0' and fv[1] in {'x', 'X'}:
      result = Node(kind: nkLitFloat, valFloat: parseHexFloat(fv)
      ).stamp(p.curr)
    else:
      result = Node(kind: nkLitFloat, valFloat: parseFloat(fv)
      ).stamp(p.curr)
    walk p
  of tkImag:
    result = Node(kind: nkImaginary, valImag: p.curr.value).stamp(p.curr)
    walk p
  of tkHex:
    var hexVal = p.curr.value
    let hexApos = hexVal.find('\'')
    if hexApos >= 0:
      hexVal = hexVal[0 ..< hexApos]
    result = Node(kind: nkLitInt, valInt: parseHexInt(hexVal)).stamp(p.curr)
    walk p
  of tkOctal:
    var octVal = p.curr.value
    let octApos = octVal.find('\'')
    if octApos >= 0:
      octVal = octVal[0 ..< octApos]
    result = Node(kind: nkLitInt, valInt: parseOctInt(octVal)).stamp(p.curr)
    walk p
  of tkBinary:
    var binVal = p.curr.value
    let binApos = binVal.find('\'')
    if binApos >= 0:
      binVal = binVal[0 ..< binApos]
    result = Node(kind: nkLitInt, valInt: parseBinInt(binVal)).stamp(p.curr)
    walk p
  of tkBigInt:
    result = Node(kind: nkLitBigInt, valBigInt: p.curr.value).stamp(p.curr)
    walk p
  of tkString:
    result = Node(kind: nkLitString, valStr: p.curr.value).stamp(p.curr)
    walk p
  of tkRegex:
    let tk = p.curr
    result = Node(kind: nkRegex,
      children: @[Node(kind: nkLitString, valStr: tk.value).stamp(tk)]).stamp(tk)
    walk p
  else:
    error(p, "Unhandled literal kind: " & $p.curr.kind)

proc parseCommentGeneric*(p: var GenericParser, minPrec: int = 0): Node =
  let tk = p.curr
  result = case p.curr.kind
    of tkComment: newInlineComment(p.curr.value)
    of tkDocComment: newDocComment(p.curr.value)
    else: nil
  if result != nil:
    result.stamp(tk)
    if result.children.len > 0:
      result.children[0].stamp(tk)
  walk p

proc stampMissing*(n: Node, tk: TokenTuple): Node {.discardable, inline.} =
  ## Generic fallback: if a language handler forgot to stamp its root node,
  ## anchor it at the token where the construct started instead of leaving
  ## `ln: 0, col: 0`. Handlers that stamp precisely are untouched.
  if n != nil and n.ln == 0 and n.col == 0:
    n.ln = tk.line
    n.col = tk.col
  n

proc parseBoolOrIdent(p: var GenericParser, minPrec: int = 0): Node =
  ## Handles identifiers, true/false, null/undefined, this/super
  let tk = p.curr
  let val = tk.value
  case val
  of "true", "false":
    result = Node(kind: nkLitBool, valBool: val == "true").stamp(tk)
    walk p
  of "null", "undefined":
    result = Node(kind: nkNil).stamp(tk)
    walk p
  of "this", "super":
    result = Node(kind: nkIdent, name: val).stamp(tk)
    walk p
  else:
    result = Node(kind: nkIdent, name: val).stamp(tk)
    walk p

proc parsePrefixOp(p: var GenericParser, minPrec: int = 0): Node =
  let opTk = p.curr
  let op = opTk.value
  walk p
  # Unary prefix operators bind tighter than all binary operators.
  # Use 13 — one above the highest binary precedence (12 for **),
  # but below member access (14–15) so typeof obj.prop works.
  const prefixPrec = 13
  # For type-taking keywords like sizeof, typeof, check if `(` follows
  # and consume the whole group as the operand (e.g., sizeof(T), typeof(x.y))
  let operand =
    if op in ["sizeof", "typeof"] and
       p.curr.kind == tkPunct and p.curr.value == "(":
      parseExpression(p, 0)
    else:
      parseExpression(p, prefixPrec)
  result = Node(kind: nkPrefix,
    children: @[Node(kind: nkIdent, name: op).stamp(opTk), operand]).stamp(opTk)

proc parseGroupExpr*(p: var GenericParser, minPrec: int = 0): Node =
  ## Generic grouping: (expr) or (expr, expr, ...) for IIFE/comma operator.
  ## If the closing ')' is immediately followed by '(' or another call infix
  ## operator, it must be parsed as a comma-expression to allow IIFE pattern.
  let openTk = p.curr
  walk p # consume '('

  # Skip leading comments
  while p.curr.kind in {tkComment, tkDocComment}:
    discard parseCommentGeneric(p)

  # Empty parens: () — could be a function call / arrow params
  if p.curr.kind == tkPunct and p.curr.value == ")":
    walk p
    return Node(kind: nkEmpty)

  var items: seq[Node] = @[]
  let savedInParenGroup = p.inParenGroup
  p.inParenGroup = true
  items.add(parseExpression(p, 0))
  # Handle Nim tuple/colon syntax: `(name: value, ...)` or `(name: Type, ...)`
  if p.curr.kind == tkPunct and p.curr.value == ":":
    let colonTk = p.curr
    walk p
    items[^1] = Node(kind: nkColonExpr,
      children: @[items[^1], parseExpression(p, 0)]).stampFrom(items[^1])

  while p.curr.kind == tkPunct and p.curr.value in [",", ";"]:
    walk p # consume ','/';' (`;` separates group items in Nim
    # `if (let x = ...; x):` and Ruby `(a; b)`)
    # Skip comments after comma before next expression
    while p.curr.kind in {tkComment, tkDocComment}:
      discard parseCommentGeneric(p)
    items.add(parseExpression(p, 0))
    # Handle tuple colon after each item
    if p.curr.kind == tkPunct and p.curr.value == ":":
      walk p
      items[^1] = Node(kind: nkColonExpr,
        children: @[items[^1], parseExpression(p, 0)]).stampFrom(items[^1])

  p.inParenGroup = savedInParenGroup
  p.expectWalk(")")

  result = if items.len == 1: items[0]
           else: Node(kind: nkStatement,
             children: @[Node(kind: nkIdent, name: "comma").stamp(openTk)] & items).stamp(openTk)

  # Cast: `(type) operand` (PHP `(string) $x`, C `(int) x`). A group holding
  # a single cast-type name followed by an operand-start token is a cast,
  # not a parenthesized expression. Member/call continuations (`[`, `.`,
  # `->`, `::`, `=>`) bind tighter and are left to the Pratt loop.
  if items.len == 1 and items[0].kind == nkIdent and
     items[0].name in ["int", "integer", "bool", "boolean", "float",
                       "double", "real", "string", "binary", "array",
                       "object", "unset", "char", "short", "long",
                       "void", "signed", "unsigned"]:
    var isOperand = false
    case p.curr.kind
    of tkIdentifier:
      isOperand = not (p.stmtKeywords.hasKey(p.curr.value) or
                       p.infixTable.hasKey(p.curr.value))
    of tkInt, tkFloat, tkString, tkHex, tkOctal, tkBinary, tkBigInt,
       tkImag, tkChar, tkRegex:
      isOperand = true
    of tkPunct:
      isOperand = p.curr.value == "("
    else:
      discard
    if isOperand:
      result = Node(kind: nkPrefix,
        children: @[Node(kind: nkIdent, name: "cast").stamp(openTk), items[0],
                    parseExpression(p, 13)]).stamp(openTk)

proc parseArrayLiteral*(p: var GenericParser, minPrec: int = 0): Node =
  let openTk = p.curr
  result = Node(kind: nkArrayLit).stamp(openTk)
  walk p # consume '['
  while not (p.curr.kind == tkPunct and p.curr.value == "]"):
    if p.curr.kind == tkEOF: error(p, "Unexpected EOF in array")
    if p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p)); continue
    # Handle holes: [a,,b] or [,,a]
    if p.curr.kind == tkPunct and p.curr.value in [",", "]"]:
      result.children.add(Node(kind: nkEmpty))
    else:
      let key = parseExpression(p)
      # key => value pairs (PHP arrays, match-style mappings)
      if p.curr.kind == tkPunct and p.curr.value == "=>":
        walk p
        result.children.add(Node(kind: nkColonExpr,
          children: @[key, parseExpression(p)]).stampFrom(key))
      else:
        result.children.add(key)
    p.walkOpt(",")
  p.expectWalk("]")

proc parseObjectLiteral*(p: var GenericParser, minPrec: int = 0): Node =
  let openTk = p.curr
  result = Node(kind: nkBlock).stamp(openTk)
  walk p # consume '{'
  # Original parseObjectLiteral (JS-style object literals)...
  while not (p.curr.kind == tkPunct and p.curr.value == "}"):
    if p.curr.kind == tkEOF: error(p, "Unexpected EOF in object")
    if p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p)); continue
    if p.curr.kind == tkPunct and p.curr.value == "...":
      # Spread element: { ...expr }
      let spreadTk = p.curr
      walk p
      let spreadExpr = parseExpression(p)
      result.children.add(Node(kind: nkCall,
        children: @[Node(kind: nkIdent, name: "spread").stamp(spreadTk), spreadExpr]).stamp(spreadTk))
      p.walkOpt(",")
      continue
    # Generator method marker `*` (JS): { *method() { ... } }
    var isGenerator = false
    if p.curr.kind == tkPunct and p.curr.value == "*":
      walk p
      isGenerator = true
    let keyTk = p.curr
    let key =
      if p.curr.kind == tkPunct and p.curr.value == "[":
        # Computed property key: [expr] — marked so consumers can tell
        # `{[k]: v}` apart from `{k: v}`
        walk p
        let k = parseExpression(p)
        p.expectWalk("]")
        Node(kind: nkStatement,
          children: @[Node(kind: nkIdent, name: "computed").stamp(keyTk), k]).stamp(keyTk)
      elif p.curr.kind == tkString:
        let n = Node(kind: nkLitString, valStr: p.curr.value).stamp(p.curr); walk p; n
      else:
        let n = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr); walk p; n
    if p.curr.kind == tkPunct and p.curr.value == "(":
      # ES6 method shorthand: key(params) { body }  or *key(params) { body }
      walk p # consume '('
      let params = Node(kind: nkIdentDefs).stampFrom(key)
      while not (p.curr.kind == tkPunct and p.curr.value == ")"):
        if p.curr.kind == tkEOF: error(p, "Unexpected EOF in method params")
        params.children.add(Node(kind: nkIdent, name: p.curr.value).stamp(p.curr))
        walk p
        p.walkOpt(",")
      p.expectWalk(")")
      let body = parseBlock(p)
      var fnNode = Node(kind: nkFunction,
        children: @[Node(kind: nkEmpty), params, body]).stampFrom(key)
      if isGenerator:
        fnNode = Node(kind: nkFunction,
          children: @[Node(kind: nkIdent, name: "*").stamp(keyTk), params, body]).stamp(keyTk)
      result.children.add(Node(kind: nkColonExpr,
        children: @[key, fnNode]).stampFrom(key))
    elif p.curr.kind == tkPunct and p.curr.value in [",", "}"]:
      # ES6 shorthand property: { key } → { key: key }
      let val = if key.kind == nkIdent: Node(kind: nkIdent, name: key.name).stampFrom(key)
                else: key
      result.children.add(Node(kind: nkColonExpr,
        children: @[key, val]).stampFrom(key))
    else:
      # Ruby-style hash rockets: { key => value } (also `:` pairs)
      if p.curr.kind == tkPunct and p.curr.value == "=>":
        walk p
      else:
        p.expectWalk(":")
      let val = parseExpression(p)
      result.children.add(Node(kind: nkColonExpr, children: @[key, val]).stampFrom(key))
    p.walkOpt(",")
  p.expectWalk("}")

#
# Infix parsing (Pratt loop)
#

proc parseCommaExpr*(p: var GenericParser): Node =
  ## Parse a comma-separated sequence of expressions (comma operator).
  ## Returns a single node if only one expression,
  ## or nkStatement("comma", expr, expr, ...) for multiple.
  result = parseExpression(p)
  if p.curr.kind == tkPunct and p.curr.value == ",":
    let commaTk = p.curr
    let commaExpr = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "comma").stamp(commaTk), result]).stampFrom(result)
    while p.curr.kind == tkPunct and p.curr.value == ",":
      walk p # consume ','
      # guard: stop if next token cannot start an expression
      if p.curr.kind == tkEOF or
         (p.curr.kind == tkPunct and p.curr.value in [")", "]", "}", ";"]):
        break
      commaExpr.children.add(parseExpression(p))
    result = commaExpr

proc parseExpression*(p: var GenericParser, minPrec: int = 0): Node =
  # Prepend leading comments to the expression result
  var leadingComments: seq[Node]
  while p.curr.kind in {tkComment, tkDocComment}:
    leadingComments.add(parseCommentGeneric(p))

  # Get prefix via dedicated dispatch
  var lhs = parsePrefix(p, minPrec)

  # After-prefix expression handler hook (language-specific, e.g. Nim export marker, command call)
  if p.expressionHandlers.hasKey("afterPrefix"):
    let handled = p.expressionHandlers["afterPrefix"](p, lhs, minPrec)
    if handled != nil:
      return handled

  # Pratt infix/postfix loop
  while true:
    # Skip interleaved comments
    while p.curr.kind in {tkComment, tkDocComment}:
      let c = parseCommentGeneric(p)
      lhs = Node(kind: nkCommentGroup, children: @[lhs, c]).stampFrom(lhs)

    # Adjacent string literal concatenation (C): "a" "b" folds into one
    # string, keeping the first literal's prefix (`L"a" L"b"`). Runs
    # before the template-literal check so JS backticks keep their
    # tag-call meaning. Also folds `"a" MACRO "b"` chains where MACRO
    # is an object-like macro expanding to a string (e.g. EV_SOCK_FMT):
    # two adjacent expressions with no operator are only valid C as
    # concatenation, so `string ident` / `concat string` become an
    # `nkInfix("concat", ...)` node instead of a parse error.
    if p.curr.kind == tkString and featAdjacentConcat in p.features and
       lhs.kind == nkLitString and canConcatCString(lhs.valStr, p.curr.value):
      lhs = Node(kind: nkLitString,
        valStr: concatCString(lhs.valStr, p.curr.value)).stampFrom(lhs)
      walk p
      continue
    if featAdjacentConcat in p.features and
       (lhs.kind == nkLitString or
        (lhs.kind == nkInfix and lhs.children.len == 3 and
         lhs.children[0].kind == nkIdent and lhs.children[0].name == "concat")):
      if p.curr.kind == tkString:
        let strTk = p.curr
        lhs = Node(kind: nkInfix, children: @[
          Node(kind: nkIdent, name: "concat").stamp(strTk), lhs,
          Node(kind: nkLitString, valStr: strTk.value).stamp(strTk)]).stampFrom(lhs)
        walk p
        continue
      elif p.curr.kind == tkIdentifier and
           not p.stmtKeywords.hasKey(p.curr.value) and
           not p.infixTable.hasKey(p.curr.value) and
           not (p.next.kind == tkPunct and p.next.value == "("):
        let macroNode = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
        walk p
        lhs = Node(kind: nkInfix, children: @[
          Node(kind: nkIdent, name: "concat").stampFrom(lhs), lhs, macroNode]).stampFrom(lhs)
        continue

    # Tagged template: `tag`...``` — a string token directly after an
    # expression is only valid as a template tag call.
    if p.curr.kind == tkString and featTemplateLit in p.features and
       lhs.kind in {nkIdent, nkDotExpr, nkCall, nkBracketExpr, nkInfix}:
      let strTk = p.curr
      lhs = Node(kind: nkCall,
        children: @[lhs, Node(kind: nkLitString, valStr: strTk.value).stamp(strTk)]).stampFrom(lhs)
      walk p
      continue

    case p.curr.kind
    of tkPunct:
      let op = p.curr.value

      # Stop tokens
      if op in [")", "]", "}", ";", ",", ":", p.blockClose]:
        break
      
      # Arrow function: (params) => body  or  param => body
      if op == "=>" and featArrowFn in p.features:
        let arrowTk = p.curr
        walk p  # consume '=>'
        let params = Node(kind: nkIdentDefs).stamp(arrowTk)
        # Reinterpret lhs as parameter list
        case lhs.kind
        of nkEmpty:
          discard  # () => body — empty params
        of nkIdent:
          params.children.add(lhs)  # x => body — single param
        of nkStatement:
          # (a, b, c) => body — comma from parseGroupExpr
          if lhs.children.len > 0 and lhs.children[0].kind == nkIdent and
             lhs.children[0].name == "comma":
            for i in 1 ..< lhs.children.len:
              params.children.add(lhs.children[i])
          else:
            params.children.add(lhs)
        else:
          params.children.add(lhs)
        
        # Parse body: { block } or expression
        let body =
          if p.curr.kind == tkPunct and p.curr.value == p.blockOpen:
            parseBlock(p)
          else:
            parseExpression(p, 0)
        lhs = Node(kind: nkFunction, children: @[Node(kind: nkEmpty), params, body]).stampFrom(lhs)
        continue

      # Postfix operators
      if p.postfixOps.contains(op):
        let opTk = p.curr
        lhs = Node(kind: nkPostfix,
          children: @[lhs, Node(kind: nkIdent, name: op).stamp(opTk)]).stampFrom(lhs)
        walk p
        continue

      # Ternary
      if p.infixTable.hasKey(op) and p.infixTable[op].special == "ternary":
        let prec = p.infixTable[op].precedence
        if prec < minPrec: break
        let qTk = p.curr
        walk p # consume '?'
        # `: value` here is the ternary separator, not a bare-call symbol arg
        let savedNoSymbol = p.noSymbolArgCall
        p.noSymbolArgCall = true
        # Elvis `?:` (PHP, GNU C): empty then-branch
        let thenExpr =
          if p.curr.kind == tkPunct and p.curr.value == ":":
            Node(kind: nkEmpty)
          else:
            parseExpression(p, 0)
        p.expectWalk(":")
        let elseExpr = parseExpression(p, prec) # right-assoc
        p.noSymbolArgCall = savedNoSymbol
        lhs = Node(kind: nkCall, children: @[
          Node(kind: nkIdent, name: "ternary").stamp(qTk), lhs, thenExpr, elseExpr]).stampFrom(lhs)
        continue

      # Assignment (right-associative)
      if p.assignOps.hasKey(op):
        if 1 < minPrec: break
        let opTk = p.curr
        walk p
        let rhs = parseExpression(p, 0)
        lhs = Node(kind: nkInfix,
          children: @[Node(kind: nkIdent, name: op).stamp(opTk), lhs, rhs]).stampFrom(lhs)
        continue

      # Special infix: dot access
      if p.infixTable.hasKey(op) and p.infixTable[op].special == "dot":
        let entry = p.infixTable[op]
        if entry.precedence < minPrec: break
        let opTk = p.curr
        walk p
        if p.curr.kind == tkPunct and p.curr.value == "{":
          # Dynamic member: `$service->{$expr}(...)`
          walk p
          let propExpr = parseExpression(p, 0)
          p.expectWalk("}")
          lhs = Node(kind: nkBracketExpr, children: @[lhs, propExpr]).stampFrom(lhs)
          continue
        if p.curr.kind == tkPunct and p.curr.value == "(" and
           p.expressionHandlers.hasKey("dotParen"):
          # Opt-in: `x.(...)` type assertion or similar (Go). A nil
          # return declines back to plain member access below.
          let handled = p.expressionHandlers["dotParen"](p, lhs, minPrec)
          if handled != nil:
            lhs = handled
            continue
        let prop = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr); walk p
        lhs = Node(kind: nkDotExpr, children: @[lhs, prop]).stampFrom(lhs)
        continue

      # Special infix: bracket access
      if p.infixTable.hasKey(op) and p.infixTable[op].special == "bracket":
        let entry = p.infixTable[op]
        if entry.precedence < minPrec: break
        if p.expressionHandlers.hasKey("bracket"):
          # Opt-in: language-specific index/slice/instantiation (Go).
          # A nil return declines back to the generic logic below.
          let handled = p.expressionHandlers["bracket"](p, lhs, minPrec)
          if handled != nil:
            lhs = handled
            continue
        let openTk = p.curr
        walk p
        # Handle empty brackets `[]` (pointer dereference in Nim)
        if p.curr.kind == tkPunct and p.curr.value == "]":
          walk p
          lhs = Node(kind: nkBracketExpr, children: @[lhs, Node(kind: nkEmpty)]).stampFrom(lhs)
          continue
        # Handle Nim generic instantiation `[:type]`
        if p.curr.kind == tkPunct and p.curr.value == ":":
          walk p
          var items = @[Node(kind: nkEmpty), parseExpression(p, 0)]
          while p.curr.kind == tkPunct and p.curr.value == ",":
            walk p
            items.add(parseExpression(p, 0))
          p.expectWalk("]")
          lhs = Node(kind: nkBracketExpr, children: @[lhs] & items).stampFrom(lhs)
          continue
        var items: seq[Node]
        proc parseBracketItem(p: var GenericParser): Node =
          result = parseExpression(p, 0)
          if p.curr.kind == tkPunct and p.curr.value == ":":
            walk p
            let fieldType = parseExpression(p, 0)
            result = Node(kind: nkColonExpr, children: @[result, fieldType]).stampFrom(result)
        items.add(parseBracketItem(p))
        while p.curr.kind == tkPunct and p.curr.value == ",":
          walk p
          items.add(parseBracketItem(p))
        p.expectWalk("]")
        lhs = if items.len == 1: Node(kind: nkBracketExpr, children: @[lhs, items[0]]).stampFrom(lhs)
              else: Node(kind: nkBracketExpr, children: @[lhs] & items).stampFrom(lhs)
        continue

      # Special infix: function call
      if p.infixTable.hasKey(op) and p.infixTable[op].special == "call":
        let entry = p.infixTable[op]
        if entry.precedence < minPrec: break
        if p.inTypeContext: break # calls are never types; the `(` belongs
          # to an outer conversion or grouping, handled after the type
        let openTk = p.curr
        walk p
        let call = Node(kind: nkCall, children: @[lhs]).stampFrom(lhs)
        # Within call arguments, `: value` is a keyword/named argument, not a
        # bare-call symbol argument (e.g. Ruby `foo(a: 1)`).
        let savedNoSymbol = p.noSymbolArgCall
        p.noSymbolArgCall = true
        while not (p.curr.kind == tkPunct and p.curr.value == ")"):
          if p.curr.kind == tkEOF: error(p, "Unexpected EOF in call")
          if p.curr.kind in {tkComment, tkDocComment}:
            call.children.add(parseCommentGeneric(p)); continue
          # Variadic: `f(...$args)` unpack, `f(...)` first-class callable
          if p.curr.kind == tkPunct and p.curr.value == "...":
            let dotsTk = p.curr
            walk p
            if p.curr.kind == tkPunct and p.curr.value == ")":
              call.children.add(Node(kind: nkIdent, name: "...").stamp(dotsTk))
            else:
              let spreadTk = dotsTk
              call.children.add(Node(kind: nkCall,
                children: @[Node(kind: nkIdent, name: "spread").stamp(spreadTk),
                            parseExpression(p, 0)]).stamp(spreadTk))
            p.walkOpt(",")
            continue
          let arg0 = parseExpression(p, 0)
          # Trailing `...`: spread call argument (`f(s...)`).
          var arg = arg0
          if p.curr.kind == tkPunct and p.curr.value == "...":
            let dotsTk = p.curr
            walk p
            arg = Node(kind: nkCall, children: @[
              Node(kind: nkIdent, name: "spread").stamp(dotsTk),
              arg]).stamp(dotsTk)
          # Named/keyword args: `name: value`
          if p.curr.kind == tkPunct and p.curr.value == ":":
            walk p
            call.children.add(Node(kind: nkColonExpr,
              children: @[arg, parseExpression(p, 0)]).stampFrom(arg))
          else:
            call.children.add(arg)
          p.walkOpt(",")
        p.expectWalk(")")
        p.noSymbolArgCall = savedNoSymbol
        lhs = call
        continue

      # Regular binary infix
      if p.infixTable.hasKey(op):
        let entry = p.infixTable[op]
        if entry.precedence < minPrec: break
        let opTk = p.curr
        walk p
        let nextMin = if entry.assoc == rightAssoc: entry.precedence
                      else: entry.precedence + 1
        let rhs = parseExpression(p, nextMin)
        lhs = Node(kind: nkInfix,
          children: @[Node(kind: nkIdent, name: op).stamp(opTk), lhs, rhs]).stampFrom(lhs)
        continue

      break # unknown operator, stop

    of tkIdentifier:
      # Keyword-based infix operators (e.g. instanceof, in, and, or)
      let key = p.curr.value
      if p.infixTable.hasKey(key):
        let entry = p.infixTable[key]
        if entry.precedence < minPrec: break
        let opTk = p.curr
        walk p
        let nextMin = if entry.assoc == rightAssoc: entry.precedence
                      else: entry.precedence + 1
        let rhs = parseExpression(p, nextMin)
        lhs = Node(kind: nkInfix,
          children: @[Node(kind: nkIdent, name: key).stamp(opTk), lhs, rhs]).stampFrom(lhs)
        continue
      break

    else: discard
    break

  result = lhs
  # Language-specific continuation hook (e.g. Ruby bare calls, blocks, modifiers).
  # Called after the infix/postfix loop breaks; the handler consumes its own
  # continuation, so no re-entry into the loop is required.
  if p.expressionHandlers.hasKey("infix"):
    let handled = p.expressionHandlers["infix"](p, result, minPrec)
    if handled != nil:
      result = handled
  # Prepend any leading comments
  if leadingComments.len > 0:
    result = Node(kind: nkCommentGroup,
      children: leadingComments & @[result]).stampFrom(result)

#
# Statement parsing
#

proc parsePrefix(p: var GenericParser, minPrec: int = 0): Node =
  ## Dispatch to the appropriate prefix handler based on the current token.
  ## Called by `parseExpression` to get the left-hand side of an expression.
  
  # Check registered prefix handlers first (language-specific overrides)
  let key = p.curr.value
  if p.prefixHandlers.hasKey(key):
    let entryTk = p.curr
    result = p.prefixHandlers[key](p, minPrec)
    return result.stampMissing(entryTk)

  case p.curr.kind
  of tkInt, tkFloat, tkString, tkHex, tkOctal, tkBinary, tkBigInt, tkImag, tkRegex:
    result = parseLiteral(p)
  of tkComment, tkDocComment:
    result = parseCommentGeneric(p)
  of tkIdentifier:
    # Statement handlers are also valid as expression prefixes
    # (function expr, class expr, etc.)
    if p.stmtKeywords.hasKey(key):
      let handlerName = p.stmtKeywords[key]
      if p.stmtHandlers.hasKey(handlerName):
        let entryTk = p.curr
        result = p.stmtHandlers[handlerName](p)
        result = result.stampMissing(entryTk)
      else:
        error(p, "No handler registered for '" & key & "' (expected '" & handlerName & "')")
    elif p.keywordPrefixOps.contains(key):
      result = parsePrefixOp(p)
    else:
      result = parseBoolOrIdent(p)
  of tkPunct:
    if p.prefixOps.contains(key):
      result = parsePrefixOp(p)
    elif key == "(":
      result = parseGroupExpr(p)
    elif key == "[":
      result = parseArrayLiteral(p)
    elif key == "{":
      if p.braceHandler != nil:
        result = p.braceHandler(p, minPrec)
      else:
        result = parseObjectLiteral(p)
    else:
      error(p, "Unexpected prefix token: '" & key & "'")
  else:
    error(p, "Unexpected token kind: " & $p.curr.kind)

proc parseBlock*(p: var GenericParser, indentPos: int = -1): Node =
  ## Parse a block of statements.
  ## 
  ## For brace-delimited languages: consumes `{` and parses until `}`
  ## For indent-based languages: parses while p.curr.col > indentPos
  ## 
  ## `indentPos` is the column of the statement that introduced this block.
  ## If -1, uses brace-based parsing (default for backward compatibility).
  result = Node(kind: nkBlock).stamp(p.curr)
  
  if indentPos >= 0:
    # Indent-based: stop when column <= parent's column
    while p.curr.kind != tkEOF:
      if p.curr.col <= indentPos: break
      if p.curr.kind in {tkComment, tkDocComment}:
        result.children.add(parseCommentGeneric(p))
        continue
      if p.curr.kind == tkPunct and p.curr.value in [")", "]", "}", ";"]:
        break
      result.children.add(parseStatement(p, indentPos))
  else:
    # Brace-based: original behavior
    p.expectWalk(p.blockOpen)
    while not (p.curr.kind == tkPunct and p.curr.value == p.blockClose):
      if p.curr.kind == tkEOF: error(p, "Unexpected EOF in block")
      if p.curr.kind in {tkComment, tkDocComment}:
        result.children.add(parseCommentGeneric(p))
        continue
      result.children.add(parseStatement(p))
    p.expectWalk(p.blockClose)

proc parseIndentBlock*(p: var GenericParser): Node =
  ## Parse an indented block (e.g. for Python-like syntax) until EOF or dedent.
  result = Node(kind: nkBlock, ln: p.curr.line, col: p.curr.col)
  while p.curr.kind != tkEOF:
    if p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p))
      continue
    if p.curr.col <= result.col:
      # We've dedented back to the same level as the block start, so the block is done.
      break
    result.children.add(parseStatement(p))

proc parseStatement*(p: var GenericParser, parentCol: int = -1): Node =
  if p.curr.kind == tkEOF: return
  if p.curr.kind in {tkComment, tkDocComment}:
    return parseCommentGeneric(p)
  if p.curr.kind == tkIdentifier:
    let key = p.curr.value
    if p.stmtKeywords.hasKey(key):
      let handlerName = p.stmtKeywords[key]
      if p.stmtHandlers.hasKey(handlerName):
        let entryTk = p.curr
        result = p.stmtHandlers[handlerName](p, parentCol)
        return result.stampMissing(entryTk)

  if p.curr.kind == tkPunct and p.curr.value == p.blockOpen:
    if p.next.kind == tkPunct and p.next.value == ".":
      if p.braceHandler != nil:
        discard p.braceHandler(p)
      else:
        discard parseObjectLiteral(p)
      return
    return parseBlock(p)

  if p.curr.kind == tkPunct and p.curr.value == ";":
    if p.strictStatements:
      error(p, "unexpected token `;`")
    # Stray `;` is an empty statement (cf. go/parser's EmptyStmt): keep a
    # stamped placeholder so statement lists never hold nil children.
    let semiTk = p.curr
    walk p
    return Node(kind: nkEmpty).stamp(semiTk)

  # Generator method: *name(params) { body } — used in class/object bodies
  # (gated: a leading `*` is dereference in C-like languages).
  if featGenerators in p.features and
     p.curr.kind == tkPunct and p.curr.value == "*":
    let starTk = p.curr
    walk p
    let name = if p.curr.kind == tkIdentifier:
                 let n = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr); walk p; n
               else:
                 Node(kind: nkEmpty)
    let params = Node(kind: nkIdentDefs).stamp(starTk)
    p.expectWalk("(")
    while not (p.curr.kind == tkPunct and p.curr.value == ")"):
      if p.curr.kind == tkEOF: error(p, "Unexpected EOF in generator params")
      params.children.add(Node(kind: nkIdent, name: p.curr.value).stamp(p.curr))
      walk p
      p.walkOpt(",")
    p.expectWalk(")")
    let body = if p.curr.kind == tkPunct and p.curr.value == p.blockOpen:
                 parseBlock(p)
               else:
                 parseStatement(p)
    return Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "function").stamp(starTk),
                  Node(kind: nkIdent, name: "*").stamp(starTk), name, params, body]).stamp(starTk)

  # Labeled statement: identifier : statement (JS only)
  if featLabeledStmt in p.features and
     p.curr.kind == tkIdentifier and p.next.kind == tkPunct and p.next.value == ":":
    let labelTk = p.curr
    let label = Node(kind: nkIdent, name: p.curr.value).stamp(labelTk)
    walk p
    p.expectWalk(":")
    var inner: Node
    if p.curr.kind == tkPunct and p.curr.value == p.blockClose:
      # `label: }` labels an empty statement (cf. go/parser, which yields
      # an EmptyStmt at `}`); the block loop consumes the `}` itself.
      inner = Node(kind: nkEmpty).stamp(p.curr)
    else:
      inner = parseStatement(p)
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "label").stamp(labelTk), label, inner]).stamp(labelTk)
    return

  # Nim command call: identifier arg1, arg2: body
  if featCommandSyntax in p.features and p.curr.kind == tkIdentifier and
     not (p.next.kind == tkPunct and
          p.next.value in [".", "*", "=", "+=", "-=", "*=", "/=", "%=", "&=", "|=", "^=", "<<=", ">>="]) and
     # A binary-only operator after the identifier starts an infix
     # expression (`a & b`, `a == b`), not a command call. Operators
     # that can also begin an argument (`-x`, `not x`) stay allowed.
     not (p.next.kind == tkPunct and p.infixTable.hasKey(p.next.value) and
          p.infixTable[p.next.value].special == "" and
          not p.prefixOps.contains(p.next.value)) and
     # A keyword operator after the identifier is infix (`a and b`),
     # and a statement keyword can never be a command argument.
     not (p.next.kind == tkIdentifier and
          (p.infixTable.hasKey(p.next.value) or
           p.stmtKeywords.hasKey(p.next.value))) and
     not p.infixTable.hasKey(p.curr.value):
    # Only trigger command syntax when not followed by a field access, colon, or assignment
    # (those are regular expressions/assignments/labeled-stmts, not command calls)

    let cmdTk = p.curr
    let cmdCol = cmdTk.col
    result = Node(kind: nkCall).stamp(cmdTk)
    result.children.add(Node(kind: nkIdent, name: cmdTk.value).stamp(cmdTk))
    walk p
    var gotBody = false
    while p.curr.kind notin {tkEOF}:
      if p.curr.kind in {tkComment, tkDocComment}:
        result.children.add(parseCommentGeneric(p)); continue
      if p.curr.kind == tkPunct and p.curr.value == ":":
        walk p
        let body = if p.curr.kind == tkPunct and p.curr.value == p.blockOpen:
                     parseBlock(p)
                   else:
                     parseBlock(p, cmdCol)
        result.children.add(body)
        gotBody = true
        break
      if p.curr.kind == tkPunct and p.curr.value in [")", "]", "}", ";"]:
        break
      if p.curr.kind == tkPunct and p.curr.value == ",":
        walk p; continue
      # Arguments on following lines must indent past the command;
      # a dedented token starts a new statement.
      if p.curr.line != cmdTk.line and p.curr.col <= cmdCol:
        break
      if p.curr.kind == tkIdentifier and
         ((p.stmtKeywords.hasKey(p.curr.value) and
           p.curr.value != "do") or
          p.infixTable.hasKey(p.curr.value) or
          p.curr.value in ["else", "of", "elif", "except", "finally"]):
        break
      result.children.add(parseExpression(p))
    if not gotBody:
      p.walkOpt(";")
    return

  # Default: expression statement
  p.statementTerminated = false
  result = parseCommaExpr(p)
  if p.strictStatements and not p.statementTerminated and not p.lexer.tagTerminated:
    p.expectWalk(";")
  else:
    p.walkOpt(";")
    p.lexer.tagTerminated = false

#
# Compiler: build tables from SweetSpec
#
proc compile*(spec: SweetSpec): GenericParser =
  ## Build a GenericParser from a specification file.
  ## 
  ## This function processes the configuration and populates the parser's lookup tables
  ## for infix operators, statement keywords, block delimiters, and feature flags. The resulting
  ## `GenericParser` is then ready to be used for parsing source code according to the defined syntax
  result = GenericParser()
  result.symbols = spec.symbols
  result.identifiers = spec.identifiers
  result.inlineCommentOpt = spec.inline_comment
  result.blockCommentSpec = spec.block_comment
  result.blockOpen = if spec.blocks != nil: spec.blocks.open else: "{"
  result.blockClose = if spec.blocks != nil: spec.blocks.close else: "}"

  # Build infix precedence table
  if spec.operators != nil:
    for group in spec.operators.infix:
      let assoc = if group.assoc == assocRight: rightAssoc else: leftAssoc
      for tok in group.tokens:
        result.infixTable[tok] = InfixEntry(
          precedence: group.precedence,
          assoc: assoc,
          special: group.handler
        )
      for kw in group.keywords:
        result.infixTable[kw] = InfixEntry(
          precedence: group.precedence,
          assoc: assoc,
          special: group.handler
        )

    # Assignment ops > right-assoc, prec 0
    if spec.operators.assignment != nil:
      for tok in spec.operators.assignment.tokens:
        result.assignOps[tok] = true
        result.infixTable[tok] = InfixEntry(
          precedence: 0, assoc: rightAssoc, special: ""
        )

    if spec.operators.ternary != nil:
      result.infixTable[spec.operators.ternary.token] = InfixEntry(
        precedence: spec.operators.ternary.precedence,
        assoc: rightAssoc,
        special: "ternary"
      )

    # Prefix ops
    if spec.operators.prefix.len > 0:
      for group in spec.operators.prefix:
        if group.isKeyword:
          for tok in group.tokens:
            result.keywordPrefixOps.incl(tok)
        else:
          for tok in group.tokens:
            result.prefixOps.incl(tok)

    # Postfix ops
    if spec.operators.postfix.len > 0:
      for group in spec.operators.postfix:
        for tok in group.tokens:
          result.postfixOps.incl(tok)

  # Statement keywords
  if spec.statements.len > 0:
    for name, stmt in spec.statements.pairs:
      if stmt.handler.len == 0: continue  # ← skip expect_regex_after etc.
      let handlerName = stmt.handler
      if stmt.keyword.len > 0:
        result.stmtKeywords[stmt.keyword] = handlerName
      for kw in stmt.keywords:
        result.stmtKeywords[kw] = handlerName

  # Expect-regex hints (lexer configuration, not statements)
  if spec.statements.hasKey("expect_regex_after"):
    let era = spec.statements["expect_regex_after"]
    result.expectRegexTokens = era.tokens
    result.expectRegexKeywords = era.keywords
    result.expectRegexTokenSet = era.tokens.toHashSet()
    result.expectRegexKeywordSet = era.keywords.toHashSet()

  # Feature flags
  if spec.features != nil:

    if spec.features.regexLiterals: result.features.incl(featRegex)
    if spec.features.asyncAwait: result.features.incl(featAsync)
    if spec.features.generators: result.features.incl(featGenerators)
    if spec.features.arrowFunctions: result.features.incl(featArrowFn)
    if spec.features.templateLiterals: result.features.incl(featTemplateLit)
    if spec.features.labeledStatements: result.features.incl(featLabeledStmt)
    if spec.features.commandSyntax: result.features.incl(featCommandSyntax)
    if spec.features.adjacentConcat: result.features.incl(featAdjacentConcat)

type
  ParsingCallback* = proc(p: var GenericParser)
    ## Optional callback type that can be used to customize the parser before parsing begins.
    ## For example, you could use this to register custom statement or prefix handlers based on the
    ## syntax specification or other criteria

template stmtHandler*(parser: untyped, name: string, body: untyped) {.dirty.} =
  ## Helper macro to define statement handlers with cleaner syntax.
  `parser`.stmtHandlers[name] =
    proc (p: var GenericParser, parentCol: int = -1): Node =
      body

template prefixHandler*(parser: untyped, name: string, body: untyped) {.dirty.} =
  ## Helper macro to define prefix handlers with cleaner syntax.
  `parser`.prefixHandlers[name] =
    proc (p: var GenericParser, minPrec: int = 0): Node =
      body

template exprHandler*(parser: untyped, name: string, body: untyped) {.dirty.} =
  ## Helper macro to define expression handlers with cleaner syntax.
  `parser`.expressionHandlers[name] =
    proc(p: var GenericParser, lhs: Node, minPrec: int): Node {.nimcall.} = body

proc applyPrecompiled*(p: var GenericParser, init: SweetLexerInit) =
  ## Apply compile-time prebuilt tables to a GenericParser.
  ## Eliminates the need for compile() + YAML spec at runtime.
  p.symbols = init.symbols
  p.identifiers = init.identifiers
  p.inlineCommentOpt = init.inlineComment
  p.blockCommentSpec = init.blockComment
  p.features = init.features
  p.infixTable = init.infixTable
  p.assignOps = init.assignOps
  p.prefixOps = init.prefixOps
  p.postfixOps = init.postfixOps
  p.keywordPrefixOps = init.keywordPrefixOps
  p.stmtKeywords = init.stmtKeywords
  p.expectRegexTokens = init.expectRegexTokens
  p.expectRegexKeywords = init.expectRegexKeywords
  p.expectRegexTokenSet = init.expectRegexTokens.toHashSet()
  p.expectRegexKeywordSet = init.expectRegexKeywords.toHashSet()
  p.blockOpen = init.blockOpen
  p.blockClose = init.blockClose

proc parseScript*(path: string, parsingCallback: ParsingCallback = nil,
            features: set[LanguageFeature] = {}): OpenAstProgram {.discardable.} =
  ## Parse a script from the given file path using the compiled syntax specification.
  let ext = path.splitFile().ext
  let syntax = getKnownSyntax(parseEnum[KnownSyntax](ext[1..^1]))
  var p = compile(syntax.spec)
  p.features = p.features + features
  if parsingCallback != nil: parsingCallback(p)
  
  let code = readFile(path)
  p.lexer = initLexer(syntax.spec, code)
  p.curr = p.getToken()
  p.next = p.getToken()

  result = OpenAstProgram()
  while p.curr.kind != tkEOF:
    result.nodes.add(parseStatement(p))

