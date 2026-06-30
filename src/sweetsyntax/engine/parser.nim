# A powerful generic parser and AST explorer for analyzing
# programming languages!
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

import std/[tables, strutils, options, sets, os, macros]

import pkg/openparser/json
import ../[config, sweetlexer]
import ../tokenizer, ./ast

type
  Assoc* = enum
    leftAssoc = "left"
    rightAssoc = "right"

  InfixEntry* = object
    precedence*: int
    assoc*: Assoc
    special*: string   # "dot", "bracket", "call", "ternary", ""

  PrefixHandler* = proc(p: var GenericParser, minPrec: int = 0): Node {.closure.}
  StmtHandler* = proc(p: var GenericParser, parentCol: int = -1): Node {.closure.}

  GenericParser* = object
    lexer*: SweetLexer
    prev*, curr*, next*: TokenTuple

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
    expectRegexTokens*: seq[string]
    expectRegexKeywords*: seq[string]
    blockOpen*, blockClose*: string
    features*: set[LanguageFeature]
      ## Set of enabled language features (e.g. featAsync, featGenerators) that can be used
  
  OpenAstParsingError* = object of CatchableError

#
# Walk helpers
#
proc walk*(p: var GenericParser, offset = 1) =
  p.prev = p.curr
  p.curr = p.next
  # Set expectRegex before reading the next token so the lexer can
  # correctly distinguish regex literals from division after tokens
  # like `=`, `(`, `return`, `var`, etc.
  p.lexer.expectRegex =
    (p.curr.kind == tkPunct and p.curr.value in p.expectRegexTokens) or
    (p.curr.kind == tkIdentifier and p.curr.value in p.expectRegexKeywords)
  p.next = p.getToken()

proc walkOpt*(p: var GenericParser, val: string) =
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

#
# Generic prefix handlers
#

proc parseLiteral(p: var GenericParser, minPrec: int = 0): Node =
  ## Handles int, float, string, hex, octal, binary, bigint literals
  case p.curr.kind
  of tkInt:
    result = Node(kind: nkLitInt, valInt: parseInt(p.curr.value))
    walk p
  of tkFloat:
    result = Node(kind: nkLitFloat, valFloat: parseFloat(p.curr.value))
    walk p
  of tkHex:
    result = Node(kind: nkLitInt, valInt: parseHexInt(p.curr.value))
    walk p
  of tkOctal:
    result = Node(kind: nkLitInt, valInt: parseOctInt(p.curr.value))
    walk p
  of tkBinary:
    result = Node(kind: nkLitInt, valInt: parseBinInt(p.curr.value))
    walk p
  of tkBigInt:
    result = Node(kind: nkLitBigInt, valBigInt: p.curr.value)
    walk p
  of tkString:
    result = Node(kind: nkLitString, valStr: p.curr.value)
    walk p
  of tkRegex:
    result = Node(kind: nkRegex,
      children: @[Node(kind: nkLitString, valStr: p.curr.value)])
    walk p
  else:
    error(p, "Unhandled literal kind: " & $p.curr.kind)

proc parseCommentGeneric*(p: var GenericParser, minPrec: int = 0): Node =
  result = case p.curr.kind
    of tkComment: newInlineComment(p.curr.value)
    of tkDocComment: newDocComment(p.curr.value)
    else: Node(kind: nkEmpty)
  walk p

proc parseBoolOrIdent(p: var GenericParser, minPrec: int = 0): Node =
  ## Handles identifiers, true/false, null/undefined, this/super
  let val = p.curr.value
  case val
  of "true", "false":
    result = Node(kind: nkLitBool, valBool: val == "true")
    walk p
  of "null", "undefined":
    result = Node(kind: nkNil)
    walk p
  of "this", "super":
    result = Node(kind: nkIdent, name: val)
    walk p
  else:
    result = Node(kind: nkIdent, name: val)
    walk p

proc parsePrefixOp(p: var GenericParser, minPrec: int = 0): Node =
  let op = p.curr.value
  walk p
  # Unary prefix operators bind tighter than all binary operators.
  # Use 13 — one above the highest binary precedence (12 for **),
  # but below member access (14–15) so typeof obj.prop works.
  const prefixPrec = 13
  let operand = parseExpression(p, prefixPrec)
  result = Node(kind: nkPrefix, children: @[Node(kind: nkIdent, name: op), operand])

proc parseGroupExpr(p: var GenericParser, minPrec: int = 0): Node =
  ## Generic grouping: (expr) or (expr, expr, ...) for IIFE/comma operator.
  ## If the closing ')' is immediately followed by '(' or another call infix
  ## operator, it must be parsed as a comma-expression to allow IIFE pattern.
  walk p # consume '('

  # Skip leading comments
  while p.curr.kind in {tkComment, tkDocComment}:
    discard parseCommentGeneric(p)

  # Empty parens: () — could be a function call / arrow params
  if p.curr.kind == tkPunct and p.curr.value == ")":
    walk p
    return Node(kind: nkEmpty)

  var items: seq[Node] = @[parseExpression(p, 0)]
  while p.curr.kind == tkPunct and p.curr.value == ",":
    walk p # consume ','
    # Skip comments after comma before next expression
    while p.curr.kind in {tkComment, tkDocComment}:
      discard parseCommentGeneric(p)
    items.add(parseExpression(p, 0))

  p.expectWalk(")")

  result = if items.len == 1: items[0]
           else: Node(kind: nkStatement,
             children: @[Node(kind: nkIdent, name: "comma")] & items)

proc parseArrayLiteral(p: var GenericParser, minPrec: int = 0): Node =
  result = Node(kind: nkBracketExpr)
  walk p # consume '['
  while not (p.curr.kind == tkPunct and p.curr.value == "]"):
    if p.curr.kind == tkEOF: error(p, "Unexpected EOF in array")
    if p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p)); continue
    # Handle holes: [a,,b] or [,,a]
    if p.curr.kind == tkPunct and p.curr.value in [",", "]"]:
      result.children.add(Node(kind: nkEmpty))
    else:
      result.children.add(parseExpression(p))
    p.walkOpt(",")
  p.expectWalk("]")

proc parseObjectLiteral(p: var GenericParser, minPrec: int = 0): Node =
  result = Node(kind: nkBlock)
  walk p # consume '{'
  while not (p.curr.kind == tkPunct and p.curr.value == "}"):
    if p.curr.kind == tkEOF: error(p, "Unexpected EOF in object")
    if p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p)); continue
    if p.curr.kind == tkPunct and p.curr.value == "...":
      # Spread element: { ...expr }
      walk p
      let spreadExpr = parseExpression(p)
      result.children.add(Node(kind: nkCall,
        children: @[Node(kind: nkIdent, name: "spread"), spreadExpr]))
      p.walkOpt(",")
      continue
    # Generator method marker `*` (JS): { *method() { ... } }
    var isGenerator = false
    if p.curr.kind == tkPunct and p.curr.value == "*":
      walk p
      isGenerator = true
    let key =
      if p.curr.kind == tkPunct and p.curr.value == "[":
        # Computed property key: [expr]
        walk p
        let k = parseExpression(p)
        p.expectWalk("]")
        k
      elif p.curr.kind == tkString:
        let n = Node(kind: nkLitString, valStr: p.curr.value); walk p; n
      else:
        let n = Node(kind: nkIdent, name: p.curr.value); walk p; n
    if p.curr.kind == tkPunct and p.curr.value == "(":
      # ES6 method shorthand: key(params) { body }  or *key(params) { body }
      walk p # consume '('
      let params = Node(kind: nkIdentDefs)
      while not (p.curr.kind == tkPunct and p.curr.value == ")"):
        if p.curr.kind == tkEOF: error(p, "Unexpected EOF in method params")
        params.children.add(Node(kind: nkIdent, name: p.curr.value))
        walk p
        p.walkOpt(",")
      p.expectWalk(")")
      let body = parseBlock(p)
      var fnNode = Node(kind: nkFunction,
        children: @[Node(kind: nkEmpty), params, body])
      if isGenerator:
        fnNode = Node(kind: nkFunction,
          children: @[Node(kind: nkIdent, name: "*"), params, body])
      result.children.add(Node(kind: nkColonExpr,
        children: @[key, fnNode]))
    elif p.curr.kind == tkPunct and p.curr.value in [",", "}"]:
      # ES6 shorthand property: { key } → { key: key }
      result.children.add(Node(kind: nkColonExpr,
        children: @[key, Node(kind: nkIdent, name: key.name)]))
    else:
      p.expectWalk(":")
      let val = parseExpression(p)
      result.children.add(Node(kind: nkColonExpr, children: @[key, val]))
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
    let commaExpr = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "comma"), result])
    while p.curr.kind == tkPunct and p.curr.value == ",":
      walk p # consume ','
      # guard: stop if next token cannot start an expression
      if p.curr.kind == tkEOF or
         (p.curr.kind == tkPunct and p.curr.value in [")", "]", "}", ";"]):
        break
      commaExpr.children.add(parseExpression(p))
    result = commaExpr

proc parseExpression*(p: var GenericParser, minPrec: int = 0): Node =
  # Skip leading comments so the actual expression is parsed,
  # not just a comment node that leaves the real expression unconsumed
  while p.curr.kind in {tkComment, tkDocComment}:
    discard parseCommentGeneric(p)

  # # Get prefix
  # var lhs: Node
  # # Check registered prefix handlers first
  # let key = p.curr.value
  # if p.prefixHandlers.hasKey(key):
  #   lhs = p.prefixHandlers[key](p, minPrec)
  # else:
  #   case p.curr.kind
  #   of tkInt, tkFloat, tkString, tkHex, tkOctal, tkBinary, tkBigInt, tkRegex:
  #     lhs = parseLiteral(p)
  #   of tkComment, tkDocComment:
  #     lhs = parseCommentGeneric(p)
  #   of tkIdentifier:
  #     # Check if this is a known prefix operator (keyword-based)
  #     if p.keywordPrefixOps.contains(key):
  #       lhs = parsePrefixOp(p)
  #     else:
  #       lhs = parseBoolOrIdent(p)
  #   of tkPunct:
  #     # Check if this is a registered prefix operator
  #     if p.prefixOps.contains(key):
  #       lhs = parsePrefixOp(p)
  #     elif key == "(":
  #       lhs = parseGroupExpr(p)
  #     elif key == "[":
  #       lhs = parseArrayLiteral(p)
  #     elif key == "{":
  #       lhs = parseObjectLiteral(p)
  #     else:
  #       error(p, "Unexpected prefix token: '" & key & "'")
  #   else:
  #     error(p, "Unexpected token kind: " & $p.curr.kind)

  # Get prefix via dedicated dispatch
  var lhs = parsePrefix(p, minPrec)

  # Pratt infix/postfix loop (unchanged from here down)
  while true:
    # Skip interleaved comments
    while p.curr.kind in {tkComment, tkDocComment}:
      let c = parseCommentGeneric(p)
      lhs = Node(kind: nkBlock, children: @[lhs, c])

    case p.curr.kind
    of tkPunct:
      let op = p.curr.value

      # Stop tokens
      if op in [")", "]", "}", ";", ",", ":", p.blockClose]:
        break
      
      # Arrow function: (params) => body  or  param => body
      if op == "=>" and featArrowFn in p.features:
        walk p  # consume '=>'
        let params = Node(kind: nkIdentDefs)
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
        let body = if p.curr.kind == tkPunct and p.curr.value == p.blockOpen:
          parseBlock(p)
        else:
          parseExpression(p, 0)
        lhs = Node(kind: nkFunction,
          children: @[Node(kind: nkEmpty), params, body])
        continue

      # Postfix operators
      if p.postfixOps.contains(op):
        lhs = Node(kind: nkPostfix,
          children: @[lhs, Node(kind: nkIdent, name: op)])
        walk p
        continue

      # Ternary
      if p.infixTable.hasKey(op) and p.infixTable[op].special == "ternary":
        let prec = p.infixTable[op].precedence
        if prec < minPrec: break
        walk p # consume '?'
        let thenExpr = parseExpression(p, 0)
        p.expectWalk(":")
        let elseExpr = parseExpression(p, prec) # right-assoc
        lhs = Node(kind: nkCall, children: @[
          Node(kind: nkIdent, name: "ternary"), lhs, thenExpr, elseExpr])
        continue

      # Assignment (right-associative)
      if p.assignOps.hasKey(op):
        if 1 < minPrec: break
        walk p
        let rhs = parseExpression(p, 0)
        lhs = Node(kind: nkInfix,
          children: @[Node(kind: nkIdent, name: op), lhs, rhs])
        continue

      # Special infix: dot access
      if p.infixTable.hasKey(op) and p.infixTable[op].special == "dot":
        let entry = p.infixTable[op]
        if entry.precedence < minPrec: break
        walk p
        let prop = Node(kind: nkIdent, name: p.curr.value); walk p
        lhs = Node(kind: nkDotExpr, children: @[lhs, prop])
        continue

      # Special infix: bracket access
      if p.infixTable.hasKey(op) and p.infixTable[op].special == "bracket":
        let entry = p.infixTable[op]
        if entry.precedence < minPrec: break
        walk p
        let idx = parseExpression(p, 0)
        p.expectWalk("]")
        lhs = Node(kind: nkBracketExpr, children: @[lhs, idx])
        continue

      # Special infix: function call
      if p.infixTable.hasKey(op) and p.infixTable[op].special == "call":
        let entry = p.infixTable[op]
        if entry.precedence < minPrec: break
        walk p
        let call = Node(kind: nkCall, children: @[lhs])
        while not (p.curr.kind == tkPunct and p.curr.value == ")"):
          if p.curr.kind == tkEOF: error(p, "Unexpected EOF in call")
          if p.curr.kind in {tkComment, tkDocComment}:
            call.children.add(parseCommentGeneric(p)); continue
          call.children.add(parseExpression(p, 0))
          p.walkOpt(",")
        p.expectWalk(")")
        lhs = call
        continue

      # Regular binary infix
      if p.infixTable.hasKey(op):
        let entry = p.infixTable[op]
        if entry.precedence < minPrec: break
        walk p
        let nextMin = if entry.assoc == rightAssoc: entry.precedence
                      else: entry.precedence + 1
        let rhs = parseExpression(p, nextMin)
        lhs = Node(kind: nkInfix,
          children: @[Node(kind: nkIdent, name: op), lhs, rhs])
        continue

      break # unknown operator, stop

    of tkIdentifier:
      # Keyword-based infix operators (e.g. instanceof, in, and, or)
      let key = p.curr.value
      if p.infixTable.hasKey(key):
        let entry = p.infixTable[key]
        if entry.precedence < minPrec: break
        walk p
        let nextMin = if entry.assoc == rightAssoc: entry.precedence
                      else: entry.precedence + 1
        let rhs = parseExpression(p, nextMin)
        lhs = Node(kind: nkInfix,
          children: @[Node(kind: nkIdent, name: key), lhs, rhs])
        continue
      break

    else: break

  result = lhs

#
# Statement parsing
#

proc parsePrefix(p: var GenericParser, minPrec: int = 0): Node =
  ## Dispatch to the appropriate prefix handler based on the current token.
  ## Called by `parseExpression` to get the left-hand side of an expression.
  
  # Check registered prefix handlers first (language-specific overrides)
  let key = p.curr.value
  if p.prefixHandlers.hasKey(key):
    return p.prefixHandlers[key](p, minPrec)

  case p.curr.kind
  of tkInt, tkFloat, tkString, tkHex, tkOctal, tkBinary, tkBigInt, tkRegex:
    result = parseLiteral(p)
  of tkComment, tkDocComment:
    result = parseCommentGeneric(p)
  of tkIdentifier:
    # Statement handlers are also valid as expression prefixes
    # (function expr, class expr, etc.)
    if p.stmtKeywords.hasKey(key):
      let handlerName = p.stmtKeywords[key]
      if p.stmtHandlers.hasKey(handlerName):
        result = p.stmtHandlers[handlerName](p)
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
  result = Node(kind: nkBlock)
  
  if indentPos >= 0:
    # Indent-based: stop when column <= parent's column
    while p.curr.kind != tkEOF:
      if p.curr.col <= indentPos: break
      if p.curr.kind in {tkComment, tkDocComment}:
        result.children.add(parseCommentGeneric(p))
        continue
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
  if p.curr.kind in {tkComment, tkDocComment}:
    return parseCommentGeneric(p)
  
  if p.curr.kind == tkIdentifier:
    let key = p.curr.value
    if p.stmtKeywords.hasKey(key):
      let handlerName = p.stmtKeywords[key]
      if p.stmtHandlers.hasKey(handlerName):
        return p.stmtHandlers[handlerName](p, parentCol)

  if p.curr.kind == tkPunct and p.curr.value == p.blockOpen:
    return parseBlock(p)

  if p.curr.kind == tkPunct and p.curr.value == ";":
    walk p
    return Node(kind: nkEmpty)

  # Generator method: *name(params) { body } — used in class/object bodies
  if p.curr.kind == tkPunct and p.curr.value == "*":
    walk p
    let name = if p.curr.kind == tkIdentifier:
                 let n = Node(kind: nkIdent, name: p.curr.value); walk p; n
               else:
                 Node(kind: nkEmpty)
    let params = Node(kind: nkIdentDefs)
    p.expectWalk("(")
    while not (p.curr.kind == tkPunct and p.curr.value == ")"):
      if p.curr.kind == tkEOF: error(p, "Unexpected EOF in generator params")
      params.children.add(Node(kind: nkIdent, name: p.curr.value))
      walk p
      p.walkOpt(",")
    p.expectWalk(")")
    let body = if p.curr.kind == tkPunct and p.curr.value == p.blockOpen:
                 parseBlock(p)
               else:
                 parseStatement(p)
    return Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "function"),
                  Node(kind: nkIdent, name: "*"), name, params, body])

  # Labeled statement: identifier : statement
  if p.curr.kind == tkIdentifier and p.next.kind == tkPunct and p.next.value == ":":
    let label = Node(kind: nkIdent, name: p.curr.value)
    walk p
    p.expectWalk(":")
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "label"), label, parseStatement(p)])
    return

  # Default: expression statement
  result = parseCommaExpr(p)
  p.walkOpt(";")

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

  # Feature flags
  if spec.features != nil:
    if spec.features.regexLiterals: result.features.incl(featRegex)
    if spec.features.asyncAwait: result.features.incl(featAsync)
    if spec.features.generators: result.features.incl(featGenerators)
    if spec.features.arrowFunctions: result.features.incl(featArrowFn)
    if spec.features.templateLiterals: result.features.incl(featTemplateLit)
    if spec.features.labeledStatements: result.features.incl(featLabeledStmt)

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

proc parseScript*(path: string, parsingCallback: ParsingCallback = nil,
            features: set[LanguageFeature] = {}): OpenAstProgram {.discardable.} =
  ## Parse a script from the given file path using the compiled syntax specification.
  let ext = path.splitFile().ext
  let syntax = getKnownSyntax(parseEnum[KnownSyntax](ext[1..^1]))
  let code = readFile(path)
  var p = compile(syntax.spec)
  p.features = features
  if parsingCallback != nil: parsingCallback(p)
  
  p.lexer = initLexer(syntax.spec, code)
  p.curr = p.getToken()
  p.next = p.getToken()

  result = OpenAstProgram()
  while p.curr.kind != tkEOF:
    result.nodes.add(parseStatement(p))

