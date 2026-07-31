# A powerful generic parser and AST explorer for analyzing
# programming languages!
#
# (c) 2026 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

import std/[tables, strutils]
import ../[config, sweetlexer]
import ../engine/[ast, parser]

proc parsePhpTypeName(p: var GenericParser): Node
proc parseFunctionDecl(p: var GenericParser): Node
proc parseClassBody(p: var GenericParser, isEnum = false): Node

#
# Shared helpers
#

proc parsePhpTypeName(p: var GenericParser): Node =
  ## Parse a PHP type: ?Type, Type, or union Type1|Type2|...
  ## Returns nkEmpty when no type is present (e.g. the parameter is `$var`).
  result = Node(kind: nkEmpty)
  var nullable = false
  if p.curr.kind == tkPunct and p.curr.value == "?":
    nullable = true
    walk p
  if p.curr.kind != tkIdentifier or p.curr.value[0] == '$':
    return
  var typeNode = Node(kind: nkIdent, name: p.curr.value)
  walk p
  while p.curr.kind == tkPunct and p.curr.value == "|":
    walk p
    if typeNode.kind != nkStatement:
      typeNode = Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "union"), typeNode])
    typeNode.children.add(Node(kind: nkIdent, name: p.curr.value))
    walk p
  if nullable:
    result = Node(kind: nkPrefix,
      children: @[Node(kind: nkIdent, name: "?"), typeNode])
  else:
    result = typeNode

proc parseFunctionParams(p: var GenericParser): Node =
  ## Parse a parameter list: ( [Type] &...$var [= default], ... )
  result = Node(kind: nkIdentDefs)
  p.expectWalk("(")
  while not (p.curr.kind == tkPunct and p.curr.value == ")"):
    if p.curr.kind == tkEOF: error(p, "Unexpected EOF in params")
    let typeNode = parsePhpTypeName(p)
    if p.curr.kind == tkPunct and p.curr.value == "&":
      walk p # by-reference
    if p.curr.kind == tkPunct and p.curr.value == "...":
      walk p # variadic
    if p.curr.kind != tkIdentifier or p.curr.value[0] != '$':
      error(p, "Expected parameter variable")
    let param = Node(kind: nkIdentDefs)
    param.children.add(Node(kind: nkIdent, name: p.curr.value))
    walk p
    if typeNode != nil and typeNode.kind != nkEmpty:
      param.children.add(typeNode)
    if p.curr.kind == tkPunct and p.curr.value == "=":
      walk p
      param.children.add(parseExpression(p))
    result.children.add(param)
    p.walkOpt(",")
  p.expectWalk(")")

proc parseFunctionReturnType(p: var GenericParser) =
  ## Consume an optional `: Type` return type annotation.
  if p.curr.kind == tkPunct and p.curr.value == ":":
    walk p
    discard parsePhpTypeName(p)

proc parseFunctionDecl(p: var GenericParser): Node =
  ## function [&]name(params) [: Type] { body } or `;` (abstract/interface).
  result = p.curr.newFunction()
  walk p # consume 'function'
  if p.curr.kind == tkPunct and p.curr.value == "&":
    walk p # by-reference return
  if p.curr.kind == tkIdentifier:
    result.children.add(Node(kind: nkIdent, name: p.curr.value))
    walk p
  else:
    result.children.add(Node(kind: nkEmpty))
  result.children.add(parseFunctionParams(p))
  parseFunctionReturnType(p)
  if p.curr.kind == tkPunct and p.curr.value == p.blockOpen:
    result.children.add(parseBlock(p))
  else:
    result.children.add(Node(kind: nkEmpty))
    p.expectWalk(";")

proc parsePhpBody(p: var GenericParser,
                  endKeywords: openArray[string]): Node =
  ## Parse a statement body which is either `{ ... }`, `: ... end*`, or a
  ## single statement. Stops before any of `endKeywords`.
  if p.curr.kind == tkPunct and p.curr.value == "{":
    result = parseBlock(p)
  elif p.curr.kind == tkPunct and p.curr.value == ":":
    walk p # consume ':'
    result = Node(kind: nkBlock)
    while not (p.curr.kind == tkIdentifier and p.curr.value in endKeywords):
      if p.curr.kind == tkEOF: error(p, "Unexpected EOF in block")
      if p.curr.kind in {tkComment, tkDocComment}:
        result.children.add(parseCommentGeneric(p))
        continue
      let stmt = parseStatement(p)
      if stmt != nil:
        result.children.add(stmt)
  else:
    result = parseStatement(p)
    if result == nil:
      result = Node(kind: nkEmpty)

proc parseConstClause(p: var GenericParser): Node =
  ## const NAME = expr [, ...];
  result = Node(kind: nkStatement, children: @[Node(kind: nkIdent, name: "const")])
  walk p # consume 'const'
  while true:
    let name = Node(kind: nkIdent, name: p.curr.value)
    walk p
    p.expectWalk("=")
    let val = parseExpression(p)
    result.children.add(Node(kind: nkIdentDefs, children: @[name, val]))
    if p.curr.kind == tkPunct and p.curr.value == ",":
      walk p
    else:
      break
  p.expectWalk(";")

proc parseUseClause(p: var GenericParser): Node =
  ## use Namespace\Sub;  |  use function/const ...;  |  use Trait { ... };
  walk p # consume 'use'
  result = Node(kind: nkStatement, children: @[Node(kind: nkIdent, name: "use")])
  # use Trait { ... } — trait conflict resolution
  if p.curr.kind == tkPunct and p.curr.value == "{":
    result.children.add(parseBlock(p))
    p.expectWalk(";")
    return
  if p.curr.kind == tkIdentifier and p.curr.value in ["function", "const"]:
    result.children.add(Node(kind: nkIdent, name: p.curr.value))
    walk p
  proc parseNsPath(p: var GenericParser): string =
    result = p.curr.value
    walk p
    while p.curr.kind == tkPunct and p.curr.value == "\\":
      walk p
      result &= "\\" & p.curr.value
      walk p
  result.children.add(Node(kind: nkIdent, name: parseNsPath(p)))
  while p.curr.kind == tkPunct and p.curr.value == ",":
    walk p
    result.children.add(Node(kind: nkIdent, name: parseNsPath(p)))
  if p.curr.kind == tkIdentifier and p.curr.value == "as":
    walk p
    result.children.add(Node(kind: nkIdent, name: p.curr.value))
    walk p
  p.expectWalk(";")

proc parseProperty(p: var GenericParser, typeNode: Node): Node =
  ## [Type] $name [= default], ...;
  result = Node(kind: nkStatement, children: @[Node(kind: nkIdent, name: "prop")])
  if typeNode != nil and typeNode.kind != nkEmpty:
    result.children.add(typeNode)
  while true:
    if p.curr.kind != tkIdentifier or p.curr.value[0] != '$':
      error(p, "Expected property variable")
    let name = Node(kind: nkIdent, name: p.curr.value)
    walk p
    let def = Node(kind: nkIdentDefs, children: @[name])
    if p.curr.kind == tkPunct and p.curr.value == "=":
      walk p
      def.children.add(parseExpression(p))
    result.children.add(def)
    if p.curr.kind == tkPunct and p.curr.value == ",":
      walk p
    else:
      break
  p.expectWalk(";")

proc parseEnumCase(p: var GenericParser): Node =
  ## case NAME;  or  case NAME = expr;
  walk p # consume 'case'
  result = Node(kind: nkStatement,
    children: @[Node(kind: nkIdent, name: "case"),
                Node(kind: nkIdent, name: p.curr.value)])
  walk p
  if p.curr.kind == tkPunct and p.curr.value == "=":
    walk p
    result.children.add(parseExpression(p))
  p.expectWalk(";")

proc parseAttributes(p: var GenericParser): Node =
  ## #[Attr, Attr(args)] — PHP 8 attributes. Returns the attribute list.
  result = Node(kind: nkStatement, children: @[Node(kind: nkIdent, name: "attr")])
  p.expectWalk("#")
  p.expectWalk("[")
  while not (p.curr.kind == tkPunct and p.curr.value == "]"):
    if p.curr.kind == tkEOF: error(p, "Unexpected EOF in attribute")
    var name = p.curr.value
    walk p
    while p.curr.kind == tkPunct and p.curr.value == "\\":
      walk p
      name &= "\\" & p.curr.value
      walk p
    let attr = Node(kind: nkIdent, name: name)
    if p.curr.kind == tkPunct and p.curr.value == "(":
      walk p
      let call = Node(kind: nkCall, children: @[attr])
      while not (p.curr.kind == tkPunct and p.curr.value == ")"):
        if p.curr.kind == tkEOF: error(p, "Unexpected EOF in attribute args")
        call.children.add(parseExpression(p))
        p.walkOpt(",")
      p.expectWalk(")")
      result.children.add(call)
    else:
      result.children.add(attr)
    p.walkOpt(",")
  p.expectWalk("]")

proc parseClassBody(p: var GenericParser, isEnum = false): Node =
  ## Parse the body of a class/interface/trait/enum, handling visibility
  ## modifiers, methods, constants, properties, trait use and enum cases.
  result = Node(kind: nkBlock)
  p.expectWalk("{")
  while not (p.curr.kind == tkPunct and p.curr.value == "}"):
    if p.curr.kind == tkEOF: error(p, "Unexpected EOF in class body")
    if p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p))
      continue
    if p.curr.kind == tkPunct and p.curr.value == "#":
      result.children.add(parseAttributes(p))
      continue
    # visibility / modifier keywords
    var mods: seq[Node]
    while p.curr.kind == tkIdentifier and
          p.curr.value in ["public", "private", "protected", "static",
                           "abstract", "final", "readonly", "var"]:
      mods.add(Node(kind: nkIdent, name: p.curr.value))
      walk p
    var member: Node
    if p.curr.kind == tkPunct and p.curr.value == "?":
      member = parseProperty(p, parsePhpTypeName(p))
    elif p.curr.kind == tkIdentifier and p.curr.value == "function":
      member = parseFunctionDecl(p)
    elif p.curr.kind == tkIdentifier and p.curr.value == "const":
      member = parseConstClause(p)
    elif p.curr.kind == tkIdentifier and p.curr.value == "use":
      member = parseUseClause(p)
    elif p.curr.kind == tkIdentifier and p.curr.value == "case" and isEnum:
      member = parseEnumCase(p)
    elif p.curr.kind == tkIdentifier and p.curr.value[0] == '$':
      member = parseProperty(p, Node(kind: nkEmpty))
    elif p.curr.kind == tkIdentifier:
      let typeNode = parsePhpTypeName(p)
      if p.curr.kind == tkIdentifier and p.curr.value[0] == '$':
        member = parseProperty(p, typeNode)
      else:
        error(p, "Expected class member")
    else:
      error(p, "Expected class member")
    # wrap member with its modifiers
    if mods.len > 0:
      let modsNode = Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "mods")] & mods)
      member = Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "member"), modsNode, member])
    else:
      member = Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "member"), member])
    result.children.add(member)
  p.expectWalk("}")

proc parseFuncLikeCall(p: var GenericParser, name: string): Node =
  ## Parse a function-like keyword call: isset($a, $b), empty($x), list($a), ...
  result = Node(kind: nkCall, children: @[Node(kind: nkIdent, name: name)])
  walk p # consume the keyword
  p.expectWalk("(")
  while not (p.curr.kind == tkPunct and p.curr.value == ")"):
    if p.curr.kind == tkEOF: error(p, "Unexpected EOF in call")
    result.children.add(parseExpression(p))
    p.walkOpt(",")
  p.expectWalk(")")

proc parseExitCall(p: var GenericParser, name: string): Node =
  ## exit;  |  exit(expr);  — `die` is an alias.
  result = Node(kind: nkCall, children: @[Node(kind: nkIdent, name: name)])
  walk p # consume exit/die
  if p.curr.kind == tkPunct and p.curr.value == "(":
    walk p
    if not (p.curr.kind == tkPunct and p.curr.value == ")"):
      result.children.add(parseExpression(p))
    p.expectWalk(")")

proc parseSwitchCases(p: var GenericParser,
                      endClose: string,
                      endKeyword: string): seq[Node] =
  ## Parse `case`/`default` blocks inside a switch, until the brace close or
  ## the alternative-syntax end keyword.
  while true:
    if p.curr.kind == tkEOF: error(p, "Unexpected EOF in switch")
    if p.curr.kind == tkPunct and p.curr.value == endClose:
      break
    if endKeyword.len > 0 and
       p.curr.kind == tkIdentifier and p.curr.value == endKeyword:
      break
    if p.curr.kind == tkIdentifier and p.curr.value == "case":
      walk p
      let caseExpr = parseExpression(p)
      p.expectWalk(":")
      let caseBody = Node(kind: nkBlock)
      while not (p.curr.kind == tkIdentifier and
                  p.curr.value in ["case", "default", endKeyword]) and
            not (p.curr.kind == tkPunct and p.curr.value == endClose):
        if p.curr.kind == tkEOF: error(p, "Unexpected EOF in case")
        caseBody.children.add(parseStatement(p))
      result.add(Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "case"), caseExpr, caseBody]))
    elif p.curr.kind == tkIdentifier and p.curr.value == "default":
      walk p
      p.expectWalk(":")
      let defaultBody = Node(kind: nkBlock)
      while not (p.curr.kind == tkPunct and p.curr.value == endClose) and
            not (endKeyword.len > 0 and
                 p.curr.kind == tkIdentifier and p.curr.value == endKeyword):
        if p.curr.kind == tkEOF: error(p, "Unexpected EOF in default")
        defaultBody.children.add(parseStatement(p))
      result.add(Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "default"), defaultBody]))
    else:
      error(p, "Expected 'case' or 'default' in switch")

proc parseClassName(p: var GenericParser): string =
  ## Parse a class name, which may be namespaced (Foo\Bar) or fully-qualified
  ## with a leading backslash (\Foo\Bar).
  if p.curr.kind == tkPunct and p.curr.value == "\\":
    walk p # leading backslash
    result = "\\"
  if p.curr.kind == tkIdentifier:
    result.add p.curr.value
    walk p
    while p.curr.kind == tkPunct and p.curr.value == "\\":
      walk p
      result.add "\\" & p.curr.value
      walk p

proc parseNew(p: var GenericParser): Node =
  ## new Foo(args)  |  new Foo\Bar  |  new class(args) extends Base { ... }
  result = Node(kind: nkStatement, children: @[Node(kind: nkIdent, name: "new")])
  walk p # consume 'new'
  if p.curr.kind == tkIdentifier and p.curr.value == "class":
    walk p
    if p.curr.kind == tkPunct and p.curr.value == "(":
      walk p
      let call = Node(kind: nkCall)
      while not (p.curr.kind == tkPunct and p.curr.value == ")"):
        if p.curr.kind == tkEOF: error(p, "Unexpected EOF in anonymous class args")
        call.children.add(parseExpression(p))
        p.walkOpt(",")
      p.expectWalk(")")
      result.children.add(call)
    if p.curr.kind == tkIdentifier and p.curr.value == "extends":
      walk p
      let parent = parseClassName(p)
      result.children.add(Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "extends"),
                    Node(kind: nkIdent, name: parent)]))
    result.children.add(parseClassBody(p))
    return
  let cls = Node(kind: nkIdent, name: parseClassName(p))
  if p.curr.kind == tkPunct and p.curr.value == "(":
    walk p
    let call = Node(kind: nkCall, children: @[cls])
    while not (p.curr.kind == tkPunct and p.curr.value == ")"):
      if p.curr.kind == tkEOF: error(p, "Unexpected EOF in new args")
      call.children.add(parseExpression(p))
      p.walkOpt(",")
    p.expectWalk(")")
    result.children.add(call)
  else:
    result.children.add(cls)

#
# PHP handlers
#

proc parseVarDeclarator(p: var GenericParser, kw: string): Node =
  ## var $x = expr, $y = expr, ...;  (also used for `static $x`)
  result = Node(kind: nkStatement)
  result.children.add(Node(kind: nkIdent, name: kw))
  walk p
  while true:
    let varDef = Node(kind: nkIdentDefs)
    varDef.children.add(Node(kind: nkIdent, name: p.curr.value))
    walk p
    if p.curr.kind == tkPunct and p.curr.value == "=":
      walk p
      varDef.children.add(parseExpression(p))
    result.children.add(varDef)
    if p.curr.kind == tkPunct and p.curr.value == ",":
      walk p
    else:
      break
  p.expectWalk(";")
  p.statementTerminated = true

proc phpHandlers*(p: var GenericParser) =
  # Register PHP-specific statement and prefix handlers.
  p.strictStatements = true

  stmtHandler p, "declarator":
    result = parseVarDeclarator(p, p.curr.value)

  prefixHandler p, "static":
    ## static $x = ...;  (declaration)  or  static::method();  (scope resolution)
    if p.next.kind == tkIdentifier and p.next.value[0] == '$':
      result = parseVarDeclarator(p, p.curr.value)
    else:
      # Treat as a plain identifier; the Pratt loop resolves `::` access.
      result = Node(kind: nkIdent, name: p.curr.value)
      walk p

  stmtHandler p, "const_decl":
    result = parseConstClause(p)

  stmtHandler p, "function":
    result = parseFunctionDecl(p)

  stmtHandler p, "return":
    walk p # consume 'return'
    result = Node(kind: nkReturn)
    if (p.curr.kind == tkPunct and p.curr.value in [";", "}"]) or
      p.curr.kind == tkEOF:
      p.expectWalk(";")
      return
    result.children.add(parseExpression(p))
    p.expectWalk(";")

  stmtHandler p, "conditional":
    ## if (cond) body [elseif (cond) body]* [else body]
    ## Supports both { } and : ... endif; styles.
    walk p # consume 'if'
    p.expectWalk("(")
    let cond = parseExpression(p)
    p.expectWalk(")")
    var children = @[cond]
    children.add(parsePhpBody(p, ["elseif", "else", "endif"]))
    while p.curr.kind == tkIdentifier and p.curr.value in ["elseif", "else"]:
      let isElseIf = p.curr.value == "elseif"
      walk p
      if isElseIf:
        p.expectWalk("(")
        children.add(parseExpression(p))
        p.expectWalk(")")
      children.add(parsePhpBody(p, ["elseif", "else", "endif"]))
      if not isElseIf: break
      if p.curr.kind != tkIdentifier or p.curr.value notin ["elseif", "else"]:
        break
    if p.curr.kind == tkIdentifier and p.curr.value == "endif":
      walk p
      p.expectWalk(";")
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "if")] & children)

  stmtHandler p, "loop":
    ## while (cond) body  |  while (cond): ... endwhile;
    walk p # consume 'while'
    p.expectWalk("(")
    let cond = parseExpression(p)
    p.expectWalk(")")
    let body = parsePhpBody(p, ["endwhile"])
    if p.curr.kind == tkIdentifier and p.curr.value == "endwhile":
      walk p
      p.expectWalk(";")
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "while"), cond, body])

  stmtHandler p, "do_loop":
    walk p # consume 'do'
    let body = parseBlock(p)
    if p.curr.kind != tkIdentifier or p.curr.value != "while":
      error(p, "Expected 'while' after do block")
    walk p # consume 'while'
    p.expectWalk("(")
    let cond = parseExpression(p)
    p.expectWalk(")")
    p.expectWalk(";")
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "do-while"), body, cond])

  stmtHandler p, "for_loop":
    ## for (init; cond; update) body  |  for (...): ... endfor;
    walk p # consume 'for'
    p.expectWalk("(")
    var initNode: Node
    if p.curr.kind == tkPunct and p.curr.value == ";":
      initNode = Node(kind: nkEmpty)
      walk p
    else:
      initNode = parseCommaExpr(p)
      p.expectWalk(";")
    var condNode: Node
    if p.curr.kind == tkPunct and p.curr.value == ";":
      condNode = Node(kind: nkEmpty)
      walk p
    else:
      condNode = parseExpression(p)
      p.expectWalk(";")
    var updateNode: Node
    if p.curr.kind == tkPunct and p.curr.value == ")":
      updateNode = Node(kind: nkEmpty)
    else:
      updateNode = parseCommaExpr(p)
    p.expectWalk(")")
    let body = parsePhpBody(p, ["endfor"])
    if p.curr.kind == tkIdentifier and p.curr.value == "endfor":
      walk p
      p.expectWalk(";")
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "for"),
                  initNode, condNode, updateNode, body])

  stmtHandler p, "foreach_loop":
    ## foreach (iterable as $val) body  |  foreach (iterable as $k => $v) body
    walk p # consume 'foreach'
    p.expectWalk("(")
    let iterable = parseExpression(p)
    if p.curr.kind != tkIdentifier or p.curr.value != "as":
      error(p, "Expected 'as' in foreach")
    walk p # consume 'as'
    var keyNode, valNode: Node
    valNode = parseExpression(p)
    if p.curr.kind == tkPunct and p.curr.value == "=>":
      walk p
      keyNode = valNode
      valNode = parseExpression(p)
    else:
      keyNode = Node(kind: nkEmpty)
    p.expectWalk(")")
    let body = parsePhpBody(p, ["endforeach"])
    if p.curr.kind == tkIdentifier and p.curr.value == "endforeach":
      walk p
      p.expectWalk(";")
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "foreach"),
                  iterable, keyNode, valNode, body])

  stmtHandler p, "throw":
    walk p # consume 'throw'
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "throw")])
    result.children.add(parseExpression(p))
    p.expectWalk(";")

  prefixHandler p, "throw":
    ## PHP 8: throw is also an expression: $x = $y ?? throw new Exception();
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "throw")])
    walk p
    result.children.add(parseExpression(p, 0))

  stmtHandler p, "break":
    walk p # consume 'break'
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "break")])
    if p.curr.kind == tkInt:
      result.children.add(Node(kind: nkLitInt, valInt: parseInt(p.curr.value)))
      walk p
    p.expectWalk(";")

  stmtHandler p, "continue":
    walk p # consume 'continue'
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "continue")])
    if p.curr.kind == tkInt:
      result.children.add(Node(kind: nkLitInt, valInt: parseInt(p.curr.value)))
      walk p
    p.expectWalk(";")

  stmtHandler p, "try_catch":
    ## try { } catch (Type $var) { } [catch ...] [finally { }]
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "try"))
    walk p # consume 'try'
    result.children.add(parseBlock(p))
    while p.curr.kind == tkIdentifier and p.curr.value == "catch":
      walk p # consume 'catch'
      p.expectWalk("(")
      let catchBlock = Node(kind: nkStatement)
      catchBlock.children.add(Node(kind: nkIdent, name: "catch"))
      let types = Node(kind: nkStatement)
      types.children.add(Node(kind: nkIdent, name: p.curr.value))
      walk p
      while p.curr.kind == tkPunct and p.curr.value == "|":
        walk p
        types.children.add(Node(kind: nkIdent, name: p.curr.value))
        walk p
      catchBlock.children.add(types)
      if p.curr.kind == tkIdentifier and p.curr.value[0] == '$':
        catchBlock.children.add(Node(kind: nkIdent, name: p.curr.value))
        walk p
      p.expectWalk(")")
      catchBlock.children.add(parseBlock(p))
      result.children.add(catchBlock)
    if p.curr.kind == tkIdentifier and p.curr.value == "finally":
      walk p
      result.children.add(Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "finally"), parseBlock(p)]))

  stmtHandler p, "switch":
    ## switch (expr) { case val: ... }  |  switch (expr): ... endswitch;
    walk p # consume 'switch'
    p.expectWalk("(")
    let cond = parseExpression(p)
    p.expectWalk(")")
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "switch"), cond])
    if p.curr.kind == tkPunct and p.curr.value == "{":
      walk p
      for c in parseSwitchCases(p, "}", ""):
        result.children.add(c)
      p.expectWalk("}")
    else:
      p.expectWalk(":")
      for c in parseSwitchCases(p, "", "endswitch"):
        result.children.add(c)
      walk p # consume 'endswitch'
      p.expectWalk(";")

  stmtHandler p, "class":
    ## [abstract|final|readonly] class Name [extends Parent] [implements I1, I2] { }
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "class"))
    walk p # consume 'class'
    result.children.add(Node(kind: nkIdent, name: p.curr.value))
    walk p
    if p.curr.kind == tkIdentifier and p.curr.value == "extends":
      walk p
      result.children.add(Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "extends"),
                    Node(kind: nkIdent, name: p.curr.value)]))
      walk p
    if p.curr.kind == tkIdentifier and p.curr.value == "implements":
      walk p
      let ifaces = Node(kind: nkStatement)
      ifaces.children.add(Node(kind: nkIdent, name: "implements"))
      ifaces.children.add(Node(kind: nkIdent, name: p.curr.value))
      walk p
      while p.curr.kind == tkPunct and p.curr.value == ",":
        walk p
        ifaces.children.add(Node(kind: nkIdent, name: p.curr.value))
        walk p
      result.children.add(ifaces)
    result.children.add(parseClassBody(p))

  stmtHandler p, "interface":
    ## interface Name [extends I1, I2] { }
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "interface"))
    walk p
    result.children.add(Node(kind: nkIdent, name: p.curr.value))
    walk p
    if p.curr.kind == tkIdentifier and p.curr.value == "extends":
      walk p
      let exts = Node(kind: nkStatement)
      exts.children.add(Node(kind: nkIdent, name: "extends"))
      exts.children.add(Node(kind: nkIdent, name: p.curr.value))
      walk p
      while p.curr.kind == tkPunct and p.curr.value == ",":
        walk p
        exts.children.add(Node(kind: nkIdent, name: p.curr.value))
        walk p
      result.children.add(exts)
    result.children.add(parseClassBody(p))

  stmtHandler p, "trait":
    ## trait Name { }
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "trait"))
    walk p
    result.children.add(Node(kind: nkIdent, name: p.curr.value))
    walk p
    result.children.add(parseClassBody(p))

  stmtHandler p, "enum":
    ## enum Name [: backed_type] { case Foo; case Bar = 1; }
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "enum"))
    walk p
    result.children.add(Node(kind: nkIdent, name: p.curr.value))
    walk p
    if p.curr.kind == tkPunct and p.curr.value == ":":
      walk p
      result.children.add(Node(kind: nkIdent, name: p.curr.value))
      walk p
    result.children.add(parseClassBody(p, isEnum = true))

  stmtHandler p, "echo":
    ## echo expr, expr, ...;
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "echo"))
    walk p # consume 'echo'
    result.children.add(parseExpression(p))
    while p.curr.kind == tkPunct and p.curr.value == ",":
      walk p
      result.children.add(parseExpression(p))
    p.expectWalk(";")

  stmtHandler p, "include":
    ## include/require/include_once/require_once expr;
    let kw = p.curr.value
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: kw))
    walk p
    result.children.add(parseExpression(p))
    p.expectWalk(";")

  stmtHandler p, "use":
    result = parseUseClause(p)

  stmtHandler p, "namespace":
    ## namespace Foo\Bar;  |  namespace { ... }  |  namespace Foo\Bar { ... }
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "namespace")])
    walk p # consume 'namespace'
    if p.curr.kind == tkIdentifier:
      var ns = p.curr.value
      walk p
      while p.curr.kind == tkPunct and p.curr.value == "\\":
        walk p
        ns &= "\\" & p.curr.value
        walk p
      result.children.add(Node(kind: nkIdent, name: ns))
    if p.curr.kind == tkPunct and p.curr.value == "{":
      result.children.add(parseBlock(p))
    else:
      p.expectWalk(";")

  stmtHandler p, "goto":
    ## goto label;
    walk p # consume 'goto'
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "goto"),
                  Node(kind: nkIdent, name: p.curr.value)])
    walk p
    p.expectWalk(";")

  stmtHandler p, "declare":
    ## declare(strict_types=1);  |  declare(...): ... enddeclare;
    walk p # consume 'declare'
    p.expectWalk("(")
    let entries = Node(kind: nkIdentDefs)
    while not (p.curr.kind == tkPunct and p.curr.value == ")"):
      if p.curr.kind == tkEOF: error(p, "Unexpected EOF in declare")
      let name = Node(kind: nkIdent, name: p.curr.value)
      walk p
      p.expectWalk("=")
      entries.children.add(Node(kind: nkColonExpr,
        children: @[name, parseExpression(p)]))
      p.walkOpt(",")
    p.expectWalk(")")
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "declare"), entries])
    if p.curr.kind == tkPunct and p.curr.value == "{":
      result.children.add(parseBlock(p))
    elif p.curr.kind == tkPunct and p.curr.value == ":":
      walk p
      let body = Node(kind: nkBlock)
      while not (p.curr.kind == tkIdentifier and p.curr.value == "enddeclare"):
        if p.curr.kind == tkEOF: error(p, "Unexpected EOF in declare")
        let stmt = parseStatement(p)
        if stmt != nil:
          body.children.add(stmt)
      walk p # consume 'enddeclare'
      p.expectWalk(";")
      result.children.add(body)
    else:
      p.expectWalk(";")

  stmtHandler p, "global":
    ## global $a, $b;
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "global")])
    walk p # consume 'global'
    while true:
      result.children.add(Node(kind: nkIdent, name: p.curr.value))
      walk p
      if p.curr.kind == tkPunct and p.curr.value == ",":
        walk p
      else:
        break
    p.expectWalk(";")

  #
  # Expression prefix handlers
  #

  prefixHandler p, "\\":
    ## Fully-qualified name: \Foo\Bar or \Foo\Bar\CONST
    walk p # consume leading '\'
    var name = p.curr.value
    walk p
    while p.curr.kind == tkPunct and p.curr.value == "\\":
      walk p
      name &= "\\" & p.curr.value
      walk p
    result = Node(kind: nkIdent, name: name)

  prefixHandler p, "fn":
    ## fn(params): Type => expr — arrow function
    walk p # consume 'fn'
    let params = parseFunctionParams(p)
    parseFunctionReturnType(p)
    p.expectWalk("=>")
    let body = parseExpression(p, 0)
    result = Node(kind: nkFunction,
      children: @[Node(kind: nkEmpty), params, body])

  prefixHandler p, "match":
    ## match(expr) { c1, c2 => value, default => value }
    walk p # consume 'match'
    p.expectWalk("(")
    let cond = parseExpression(p)
    p.expectWalk(")")
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "match"), cond])
    p.expectWalk("{")
    while not (p.curr.kind == tkPunct and p.curr.value == "}"):
      if p.curr.kind == tkEOF: error(p, "Unexpected EOF in match")
      let arm = Node(kind: nkStatement)
      if p.curr.kind == tkIdentifier and p.curr.value == "default":
        walk p
        arm.children.add(Node(kind: nkIdent, name: "default"))
      else:
        arm.children.add(parseExpression(p))
        while p.curr.kind == tkPunct and p.curr.value == ",":
          walk p
          arm.children.add(parseExpression(p))
      p.expectWalk("=>")
      arm.children.add(parseExpression(p, 0))
      result.children.add(arm)
      p.walkOpt(",")
    p.expectWalk("}")

  prefixHandler p, "new":
    result = parseNew(p)

  prefixHandler p, "clone":
    ## clone $obj
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "clone")])
    walk p
    result.children.add(parseExpression(p, 0))

  prefixHandler p, "isset":
    result = parseFuncLikeCall(p, "isset")

  prefixHandler p, "empty":
    result = parseFuncLikeCall(p, "empty")

  prefixHandler p, "unset":
    result = parseFuncLikeCall(p, "unset")

  prefixHandler p, "list":
    result = parseFuncLikeCall(p, "list")

  prefixHandler p, "eval":
    result = parseFuncLikeCall(p, "eval")

  prefixHandler p, "exit":
    result = parseExitCall(p, "exit")

  prefixHandler p, "die":
    result = parseExitCall(p, "die")

  prefixHandler p, "print":
    ## print expr
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "print")])
    walk p
    result.children.add(parseExpression(p, 0))

  prefixHandler p, "#":
    ## #[Attr, ...] followed by a class/function/... declaration
    result = parseAttributes(p)
    let decl = parseStatement(p)
    if decl != nil:
      result.children.add(decl)
    p.statementTerminated = true

proc parsePHP*(path: string): OpenAstProgram =
  ## Parse a PHP script
  try:
    result = parseScript(path, phpHandlers,
      features = {featLabeledStmt, featGenerators})
  except OpenAstParsingError as e:
    echo e.msg
