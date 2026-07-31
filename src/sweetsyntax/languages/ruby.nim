# A powerful generic parser and AST explorer for analyzing
# programming languages!
#
# (c) 2026 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

import std/[tables, strutils]
import ../[config, sweetlexer]
import ../engine/[ast, parser]

const
  rubyModifiers = ["if", "unless", "while", "until", "rescue"]
  # Keywords that terminate bare-call argument lists / act as block markers
  rubyContinuationKeywords = ["do", "end", "then", "else", "elsif", "when",
                              "rescue", "ensure", "and", "or", "not", "in",
                              "retry", "redo", "alias", "undef"]

proc parseRubyBody(p: var GenericParser, stopKeywords: seq[string]): Node
proc parseRubyBrace(p: var GenericParser, minPrec = 0): Node
proc parseRubyBraceContent(p: var GenericParser): tuple[params, body: Node, isHash: bool]
proc maybeModifier(p: var GenericParser, node: Node): Node

proc canStartRubyExpr(p: var GenericParser): bool =
  ## Whether the current token can begin an expression (bare-call argument).
  case p.curr.kind
  of tkIdentifier:
    not (p.stmtKeywords.hasKey(p.curr.value) or
         p.curr.value in rubyContinuationKeywords)
  of tkInt, tkFloat, tkString, tkHex, tkOctal, tkBinary, tkBigInt, tkChar, tkRegex:
    true
  of tkPunct:
    p.curr.value in ["(", "[", "{", "@", "@@", ":", "->", "*", "**", "&",
                     "-", "+", "!", "~", "%", "'", "\""]
  else:
    false

proc isRubyKeyword(p: var GenericParser, name: string): bool =
  name in p.identifiers or name in rubyContinuationKeywords

proc parseRubyBody(p: var GenericParser, stopKeywords: seq[string]): Node =
  ## Parse statements until one of `stopKeywords` (consumed by the caller).
  result = Node(kind: nkBlock)
  while not (p.curr.kind == tkIdentifier and p.curr.value in stopKeywords):
    if p.curr.kind == tkEOF:
      error(p, "Unexpected EOF, expected '" & stopKeywords[^1] & "'")
    if p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p))
      continue
    if p.curr.kind == tkPunct and p.curr.value == ";":
      walk p
      continue
    let stmt = parseStatement(p)
    if stmt != nil:
      result.children.add(stmt)

proc parseRubyThen(p: var GenericParser) =
  ## Consume an optional `then`, `;` or `:` separator after a condition.
  if p.curr.kind == tkIdentifier and p.curr.value == "then":
    walk p
  elif p.curr.kind == tkPunct and p.curr.value in [":", ";"]:
    walk p

proc expectRubyKeyword(p: var GenericParser, kw: string) =
  ## Consume an identifier keyword (e.g. `end`) or raise.
  if p.curr.kind == tkIdentifier and p.curr.value == kw:
    walk p
  else:
    error(p, "Expected '" & kw & "', got '" & p.curr.value & "'")

proc maybeModifier(p: var GenericParser, node: Node): Node =
  ## Apply trailing modifiers: `node if/unless/while/until/rescue cond`.
  result = node
  while p.curr.kind == tkIdentifier and p.curr.value in rubyModifiers and
        p.curr.line == p.prev.line:
    let kw = p.curr.value
    walk p
    let cond = parseExpression(p, 0)
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: kw), result, cond])

proc parseRubyHashAfter(p: var GenericParser): Node =
  ## Parse hash pairs; assumes '{' consumed, consumes up to '}'.
  result = Node(kind: nkStatement, children: @[Node(kind: nkIdent, name: "hash")])
  while not (p.curr.kind == tkPunct and p.curr.value == "}"):
    if p.curr.kind == tkEOF: error(p, "Unexpected EOF in hash")
    let savedNoSymbol = p.noSymbolArgCall
    p.noSymbolArgCall = true
    let key = parseExpression(p, 0)
    p.noSymbolArgCall = savedNoSymbol
    if p.curr.kind == tkPunct and p.curr.value in [":", "=>"]:
      walk p
      result.children.add(Node(kind: nkColonExpr,
        children: @[key, parseExpression(p, 0)]))
    else:
      result.children.add(key)
    p.walkOpt(",")
  p.expectWalk("}")

proc looksLikeHashStart(p: var GenericParser): bool =
  ## Called with the first token after '{'; true when the content is a hash.
  if p.curr.kind == tkPunct and p.curr.value in [":", "*", "**"]:
    true
  elif p.curr.kind in {tkIdentifier, tkString, tkInt, tkFloat, tkChar} and
       p.next.kind == tkPunct and p.next.value in [":", "=>"]:
    true
  else:
    false

proc parseBlockParams(p: var GenericParser): Node =
  ## Parse `|x, y|` block parameters (assumes '|' current).
  result = Node(kind: nkIdentDefs)
  walk p
  while not (p.curr.kind == tkPunct and p.curr.value == "|"):
    if p.curr.kind == tkEOF: error(p, "Unexpected EOF in block params")
    result.children.add(Node(kind: nkIdent, name: p.curr.value))
    walk p
    p.walkOpt(",")
  p.expectWalk("|")

type RubyBraceContent = tuple
  params, body: Node
  isHash: bool

proc parseRubyBraceContent(p: var GenericParser): RubyBraceContent =
  ## Assumes '{' consumed; parses `|params|` then body (hash or statements).
  result.params = Node(kind: nkIdentDefs)
  if p.curr.kind == tkPunct and p.curr.value == "|":
    result.params = parseBlockParams(p)
  if looksLikeHashStart(p):
    result.isHash = true
    result.body = parseRubyHashAfter(p)
  else:
    result.body = Node(kind: nkBlock)
    while not (p.curr.kind == tkPunct and p.curr.value == "}"):
      if p.curr.kind == tkEOF: error(p, "Unexpected EOF in block")
      let stmt = parseStatement(p)
      if stmt != nil:
        result.body.children.add(stmt)
    p.expectWalk("}")

proc parseRubyDoBlock(p: var GenericParser): tuple[params, body: Node] =
  ## Parse `do |params| ... end`.
  walk p # consume 'do'
  result.params = Node(kind: nkIdentDefs)
  if p.curr.kind == tkPunct and p.curr.value == "|":
    result.params = parseBlockParams(p)
  result.body = parseRubyBody(p, @["end"])
  p.expectRubyKeyword("end")

proc parseRubyBrace(p: var GenericParser, minPrec = 0): Node =
  ## `{ |x| body }` block or `{ a: 1 }` hash literal.
  p.expectWalk("{")
  let content = parseRubyBraceContent(p)
  if content.isHash:
    result = content.body
  else:
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "block"), Node(kind: nkEmpty),
                  content.params, content.body])

proc parseRubyParams(p: var GenericParser): Node =
  ## Parse a method parameter list: (a, b = 1, *rest, k:, k: v, **kw, &block)
  result = Node(kind: nkIdentDefs)
  p.expectWalk("(")
  while not (p.curr.kind == tkPunct and p.curr.value == ")"):
    if p.curr.kind == tkEOF: error(p, "Unexpected EOF in params")
    var param: Node
    if p.curr.kind == tkPunct and p.curr.value == "*":
      walk p
      if p.curr.kind == tkPunct and p.curr.value == "*":
        walk p
        param = Node(kind: nkIdent, name: "**" & p.curr.value)
        walk p
      else:
        param = Node(kind: nkIdent, name: "*" & p.curr.value)
        walk p
    elif p.curr.kind == tkPunct and p.curr.value == "&":
      walk p
      param = Node(kind: nkIdent, name: "&" & p.curr.value)
      walk p
    elif p.curr.kind == tkIdentifier:
      let name = p.curr.value
      walk p
      if p.curr.kind == tkPunct and p.curr.value == ":":
        walk p
        param = Node(kind: nkIdentDefs,
          children: @[Node(kind: nkIdent, name: name & ":")])
        if canStartRubyExpr(p):
          param.children.add(parseExpression(p, 0))
      elif p.curr.kind == tkPunct and p.curr.value == "=":
        walk p
        param = Node(kind: nkIdentDefs,
          children: @[Node(kind: nkIdent, name: name), parseExpression(p, 0)])
      else:
        param = Node(kind: nkIdentDefs, children: @[Node(kind: nkIdent, name: name)])
    else:
      param = Node(kind: nkIdentDefs, children: @[Node(kind: nkIdent, name: p.curr.value)])
      walk p
    result.children.add(param)
    p.walkOpt(",")
  p.expectWalk(")")

proc parseRubyMethodName(p: var GenericParser): Node =
  ## `foo`, `foo?`, `foo=`, `self.foo`, `Foo.bar`
  result = Node(kind: nkIdent, name: p.curr.value)
  walk p
  if p.curr.kind == tkPunct and p.curr.value == ".":
    walk p
    var suffix = p.curr.value
    walk p
    if p.curr.kind == tkPunct and p.curr.value == "=":
      suffix &= "="
      walk p
    result = Node(kind: nkDotExpr,
      children: @[result, Node(kind: nkIdent, name: suffix)])
  elif p.curr.kind == tkPunct and p.curr.value == "=":
    result.name &= "="
    walk p

proc parseRescueClauses(p: var GenericParser, parent: Node): Node =
  ## Append `rescue`/`else`/`ensure` clauses to `parent`.
  result = parent
  while p.curr.kind == tkIdentifier and p.curr.value in ["rescue", "else", "ensure"]:
    let kw = p.curr.value
    walk p
    if kw == "rescue":
      let clause = Node(kind: nkStatement, children: @[Node(kind: nkIdent, name: "rescue")])
      if p.curr.kind == tkPunct and p.curr.value == "=>":
        walk p
        clause.children.add(Node(kind: nkIdent, name: p.curr.value))
        walk p
      else:
        while p.curr.kind == tkIdentifier and
              p.curr.value notin ["then", "end", "else", "ensure", "rescue"]:
          clause.children.add(Node(kind: nkIdent, name: p.curr.value))
          walk p
          if p.curr.kind == tkPunct and p.curr.value == "|":
            walk p
          else:
            break
        if p.curr.kind == tkPunct and p.curr.value == "=>":
          walk p
          clause.children.add(Node(kind: nkIdent, name: p.curr.value))
          walk p
      clause.children.add(parseRubyBody(p, @["rescue", "else", "ensure", "end"]))
      result.children.add(clause)
    else:
      let clause = Node(kind: nkStatement, children: @[Node(kind: nkIdent, name: kw)])
      clause.children.add(parseRubyBody(p, @["rescue", "ensure", "end"]))
      result.children.add(clause)

proc parseRubyName(p: var GenericParser): Node =
  ## Symbol or identifier (for alias/undef).
  if p.curr.kind == tkPunct and p.curr.value == ":":
    walk p
    result = Node(kind: nkIdent, name: ":" & p.curr.value)
    walk p
  else:
    result = Node(kind: nkIdent, name: p.curr.value)
    walk p

proc parseSimpleControl(p: var GenericParser, name: string): Node =
  ## return/break/next/redo/retry/yield [expr] [if/unless/... cond]
  result = Node(kind: nkStatement, children: @[Node(kind: nkIdent, name: name)])
  walk p
  if canStartRubyExpr(p):
    result.children.add(parseExpression(p, 0))
  result = maybeModifier(p, result)

proc rubyHandlers*(p: var GenericParser) =
  # Register Ruby-specific statement and prefix handlers.

  stmtHandler p, "def":
    ## def name(params) -> Type body [rescue] end  |  def self.name ... end
    result = Node(kind: nkFunction)
    walk p # consume 'def'
    result.children.add(parseRubyMethodName(p))
    if p.curr.kind == tkPunct and p.curr.value == "(":
      result.children.add(parseRubyParams(p))
    else:
      result.children.add(Node(kind: nkIdentDefs))
    if p.curr.kind == tkPunct and p.curr.value == "->":
      walk p
      discard parseExpression(p, 0)
    result.children.add(parseRubyBody(p, @["rescue", "else", "ensure", "end"]))
    result = parseRescueClauses(p, result)
    p.expectRubyKeyword("end")

  stmtHandler p, "class":
    ## class Name < Super ... end
    result = Node(kind: nkStatement, children: @[Node(kind: nkIdent, name: "class")])
    walk p
    result.children.add(parseRubyMethodName(p))
    if p.curr.kind == tkPunct and p.curr.value == "<":
      walk p
      result.children.add(Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "superclass"),
                    Node(kind: nkIdent, name: p.curr.value)]))
      walk p
    result.children.add(parseRubyBody(p, @["end"]))
    p.expectRubyKeyword("end")

  stmtHandler p, "module":
    result = Node(kind: nkStatement, children: @[Node(kind: nkIdent, name: "module")])
    walk p
    result.children.add(parseRubyMethodName(p))
    result.children.add(parseRubyBody(p, @["end"]))
    p.expectRubyKeyword("end")

  stmtHandler p, "conditional":
    ## if/unless cond [then] body [elsif ...]* [else ...] end
    let kw = p.curr.value
    walk p
    let savedNoSymbol = p.noSymbolArgCall
    p.noSymbolArgCall = true
    let cond = parseExpression(p, 0)
    p.noSymbolArgCall = savedNoSymbol
    parseRubyThen(p)
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: kw), cond,
                  parseRubyBody(p, @["elsif", "else", "end"])])
    while p.curr.kind == tkIdentifier and p.curr.value == "elsif":
      walk p
      let saved2 = p.noSymbolArgCall
      p.noSymbolArgCall = true
      let c = parseExpression(p, 0)
      p.noSymbolArgCall = saved2
      parseRubyThen(p)
      result.children.add(c)
      result.children.add(parseRubyBody(p, @["elsif", "else", "end"]))
    if p.curr.kind == tkIdentifier and p.curr.value == "else":
      walk p
      result.children.add(parseRubyBody(p, @["end"]))
    p.expectRubyKeyword("end")

  stmtHandler p, "loop":
    ## while/until cond [do|then] body end
    let kw = p.curr.value
    walk p
    let savedNoSymbol = p.noSymbolArgCall
    p.noSymbolArgCall = true
    let cond = parseExpression(p, 0)
    p.noSymbolArgCall = savedNoSymbol
    if p.curr.kind == tkIdentifier and p.curr.value == "do":
      walk p
    parseRubyThen(p)
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: kw), cond,
                  parseRubyBody(p, @["end"])])
    p.expectRubyKeyword("end")

  stmtHandler p, "for_loop":
    ## for x in arr [do] body end
    walk p
    result = Node(kind: nkStatement, children: @[Node(kind: nkIdent, name: "for")])
    result.children.add(parseExpression(p, 0))
    if p.curr.kind != tkIdentifier or p.curr.value != "in":
      error(p, "Expected 'in' in for loop")
    walk p
    let savedNoSymbol = p.noSymbolArgCall
    p.noSymbolArgCall = true
    result.children.add(parseExpression(p, 0))
    p.noSymbolArgCall = savedNoSymbol
    if p.curr.kind == tkIdentifier and p.curr.value == "do":
      walk p
    result.children.add(parseRubyBody(p, @["end"]))
    p.expectRubyKeyword("end")

  stmtHandler p, "case":
    ## case expr when val [, val] [then] body ... [else body] end
    walk p
    result = Node(kind: nkStatement, children: @[Node(kind: nkIdent, name: "case")])
    if p.curr.kind == tkIdentifier and p.curr.value in ["when", "else", "end"]:
      result.children.add(Node(kind: nkEmpty))
    else:
      let savedNoSymbol = p.noSymbolArgCall
      p.noSymbolArgCall = true
      result.children.add(parseExpression(p, 0))
      p.noSymbolArgCall = savedNoSymbol
    while p.curr.kind == tkIdentifier and p.curr.value == "when":
      walk p
      let clause = Node(kind: nkStatement, children: @[Node(kind: nkIdent, name: "when")])
      clause.children.add(parseExpression(p, 0))
      while p.curr.kind == tkPunct and p.curr.value == ",":
        walk p
        clause.children.add(parseExpression(p, 0))
      parseRubyThen(p)
      clause.children.add(parseRubyBody(p, @["when", "else", "end"]))
      result.children.add(clause)
    if p.curr.kind == tkIdentifier and p.curr.value == "else":
      walk p
      result.children.add(Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "else"),
                    parseRubyBody(p, @["end"])]))
    p.expectRubyKeyword("end")

  stmtHandler p, "begin":
    ## begin body [rescue ...]* [else body] [ensure body] end
    walk p
    result = Node(kind: nkStatement, children: @[Node(kind: nkIdent, name: "begin")])
    result.children.add(parseRubyBody(p, @["rescue", "else", "ensure", "end"]))
    result = parseRescueClauses(p, result)
    p.expectRubyKeyword("end")

  stmtHandler p, "return":
    result = parseSimpleControl(p, "return")

  stmtHandler p, "break":
    result = parseSimpleControl(p, "break")

  stmtHandler p, "next":
    result = parseSimpleControl(p, "next")

  stmtHandler p, "redo":
    result = parseSimpleControl(p, "redo")

  stmtHandler p, "retry":
    result = parseSimpleControl(p, "retry")

  stmtHandler p, "yield":
    result = parseSimpleControl(p, "yield")

  stmtHandler p, "alias":
    ## alias new old  |  alias :new :old
    walk p
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "alias"),
                  parseRubyName(p), parseRubyName(p)])

  stmtHandler p, "undef":
    walk p
    result = Node(kind: nkStatement, children: @[Node(kind: nkIdent, name: "undef")])
    while true:
      result.children.add(parseRubyName(p))
      if p.curr.kind == tkPunct and p.curr.value == ",":
        walk p
      else:
        break

  stmtHandler p, "end":
    error(p, "unexpected end")

  #
  # Expression prefix handlers
  #

  prefixHandler p, "@":
    ## @ivar  |  @[1, 2] array literal
    walk p # consume '@'
    if p.curr.kind == tkPunct and p.curr.value == "[":
      let arr = parseArrayLiteral(p)
      result = Node(kind: nkPrefix,
        children: @[Node(kind: nkIdent, name: "@"), arr])
    else:
      result = Node(kind: nkIdent, name: "@" & p.curr.value)
      walk p

  prefixHandler p, "@@":
    ## @@cvar
    walk p
    result = Node(kind: nkIdent, name: "@@" & p.curr.value)
    walk p

  prefixHandler p, ":":
    ## :symbol
    walk p
    result = Node(kind: nkIdent, name: ":" & p.curr.value)
    walk p

  prefixHandler p, "defined?":
    walk p
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "defined?")])
    if p.curr.kind == tkPunct and p.curr.value == "(":
      walk p
      result.children.add(parseExpression(p, 0))
      p.expectWalk(")")

  prefixHandler p, "->":
    ## ->(params) { body }  |  -> { body }  |  ->(params) do ... end
    walk p
    result = Node(kind: nkFunction, children: @[Node(kind: nkEmpty)])
    if p.curr.kind == tkPunct and p.curr.value == "(":
      result.children.add(parseRubyParams(p))
    else:
      result.children.add(Node(kind: nkIdentDefs))
    if p.curr.kind == tkPunct and p.curr.value == "{":
      p.expectWalk("{")
      let content = parseRubyBraceContent(p)
      result.children.add(Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "block"), Node(kind: nkEmpty),
                    content.params, content.body]))
    elif p.curr.kind == tkIdentifier and p.curr.value == "do":
      let (params, body) = parseRubyDoBlock(p)
      result.children.add(Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "block"), Node(kind: nkEmpty),
                    params, body]))

  # `{` at expression start: hash literal or block
  p.braceHandler = parseRubyBrace

  #
  # Infix expression continuation: bare calls, blocks, modifiers
  #
  exprHandler p, "infix":
    result = nil
    var node = lhs
    var changed = false
    while true:
      # Blocks: `call do |x| ... end` / `call { |x| ... }`
      if p.curr.kind == tkIdentifier and p.curr.value == "do" and
         p.curr.line == p.prev.line:
        let (params, body) = parseRubyDoBlock(p)
        node = Node(kind: nkStatement,
          children: @[Node(kind: nkIdent, name: "block"), node, params, body])
        changed = true
        continue
      if p.curr.kind == tkPunct and p.curr.value == "{" and
         p.curr.line == p.prev.line:
        p.expectWalk("{")
        let content = parseRubyBraceContent(p)
        node = Node(kind: nkStatement,
          children: @[Node(kind: nkIdent, name: "block"), node,
                      content.params, content.body])
        changed = true
        continue
      # Modifiers: `expr if cond`
      if p.curr.kind == tkIdentifier and p.curr.value in rubyModifiers and
         p.curr.line == p.prev.line:
        node = maybeModifier(p, node)
        changed = true
        continue
      # Bare (paren-less) method call: `puts arg1, arg2`
      let callable =
        case node.kind
        of nkIdent: not isRubyKeyword(p, node.name)
        of nkCall, nkDotExpr, nkBracketExpr: true
        else: false
      if callable and canStartRubyExpr(p) and p.curr.line == p.prev.line:
        if p.noSymbolArgCall and p.curr.kind == tkPunct and p.curr.value == ":":
          break
        let newCall =
          if node.kind == nkCall:
            Node(kind: nkCall, children: @[node.children[0]])
          else:
            Node(kind: nkCall, children: @[node])
        if node.kind == nkCall:
          for i in 1 ..< node.children.len:
            newCall.children.add(node.children[i])
        var first = true
        while canStartRubyExpr(p) and (first or p.curr.line == p.prev.line):
          newCall.children.add(parseExpression(p, 0))
          first = false
          if p.curr.kind == tkPunct and p.curr.value == ",":
            walk p
          else:
            break
        node = newCall
        changed = true
        continue
      break
    if changed:
      result = node

proc parseRuby*(path: string): OpenAstProgram =
  ## Parse a Ruby script
  try:
    result = parseScript(path, rubyHandlers)
  except OpenAstParsingError as e:
    echo e.msg
