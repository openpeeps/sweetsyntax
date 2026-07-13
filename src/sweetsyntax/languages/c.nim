# A powerful generic parser and AST explorer for analyzing
# programming languages!
#
# (c) 2026 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

import std/strutils
import ../[config, sweetlexer]
import ../engine/[ast, parser]

const
  cSpecifiers* = ["void", "char", "short", "int", "long", "float", "double",
                   "signed", "unsigned", "_Bool", "_Complex", "_Imaginary",
                   "typeof", "struct", "union", "enum",
                   "auto", "register", "static", "extern",
                   "const", "volatile", "restrict", "inline"]

proc parseDeclarator(p: var GenericParser): Node
proc parseDirectDeclarator(p: var GenericParser): Node

proc parseDeclarator(p: var GenericParser): Node =
  var ptrs = 0
  while p.curr.kind == tkPunct and p.curr.value == "*":
    inc ptrs
    walk p
    while p.curr.kind == tkIdentifier and
          p.curr.value in ["const", "volatile", "restrict", "_Atomic"]:
      walk p

  result = parseDirectDeclarator(p)

  for i in 1..ptrs:
    result = Node(kind: nkPrefix,
      children: @[Node(kind: nkIdent, name: "*"), result])

proc parseDirectDeclarator(p: var GenericParser): Node =
  if p.curr.kind == tkPunct and p.curr.value == "(":
    walk p
    result = parseDeclarator(p)
    p.expectWalk(")")
  elif p.curr.kind == tkIdentifier:
    result = Node(kind: nkIdent, name: p.curr.value)
    walk p
  else:
    error(p, "Expected identifier or '(' in declarator")

  while true:
    if p.curr.kind == tkPunct and p.curr.value == "[":
      walk p
      let size = if p.curr.kind == tkPunct and p.curr.value == "]":
                   newEmptyNode()
                 else:
                   parseExpression(p, 0)
      p.expectWalk("]")
      result = Node(kind: nkBracketExpr, children: @[result, size])
    elif p.curr.kind == tkPunct and p.curr.value == "(":
      walk p
      let params = Node(kind: nkIdentDefs)
      while not (p.curr.kind == tkPunct and p.curr.value == ")"):
        if p.curr.kind == tkEOF:
          error(p, "Unexpected EOF in function parameters")
        if p.curr.kind in {tkComment, tkDocComment}:
          discard parseCommentGeneric(p)
          continue
        # Parse a single parameter using the full declarator machinery
        var specifiers: seq[string]
        while p.curr.kind == tkIdentifier and p.curr.value in cSpecifiers:
          specifiers.add(p.curr.value)
          walk p
        let paramDecl = parseDeclarator(p)
        let paramNode = if specifiers.len > 0:
          Node(kind: nkPrefix, children: @[Node(kind: nkIdent, name: specifiers.join(" ")), paramDecl])
        else:
          paramDecl
        params.children.add(paramNode)
        p.walkOpt(",")
      p.expectWalk(")")
      result = Node(kind: nkCall, children: @[result, params])
    else:
      break

proc parseStructBody(p: var GenericParser): Node =
  result = Node(kind: nkBlock)
  p.expectWalk("{")
  while not (p.curr.kind == tkPunct and p.curr.value == "}"):
    if p.curr.kind == tkEOF:
      error(p, "Unexpected EOF in struct/union body")
    if p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p))
      continue
    if p.curr.kind == tkPunct and p.curr.value == "}":
      break
    result.children.add(parseStatement(p))
  p.expectWalk("}")

proc parseEnumBody(p: var GenericParser): Node =
  result = Node(kind: nkBlock)
  p.expectWalk("{")
  while not (p.curr.kind == tkPunct and p.curr.value == "}"):
    if p.curr.kind == tkEOF:
      error(p, "Unexpected EOF in enum body")
    if p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p))
      continue
    if p.curr.kind == tkIdentifier:
      let member = Node(kind: nkStatement)
      member.children.add(Node(kind: nkIdent, name: p.curr.value))
      walk p
      if p.curr.kind == tkPunct and p.curr.value == "=":
        walk p
        member.children.add(parseExpression(p, 0))
      result.children.add(member)
      p.walkOpt(",")
    else:
      break
  p.expectWalk("}")

proc parseStructUnionDecl(p: var GenericParser, kind: string): Node =
  result = Node(kind: nkStatement)
  result.children.add(Node(kind: nkIdent, name: kind))
  walk p

  var tag: Node
  var body: Node

  if p.curr.kind == tkPunct and p.curr.value == "{":
    body = parseStructBody(p)
  elif p.curr.kind == tkIdentifier:
    tag = Node(kind: nkIdent, name: p.curr.value)
    result.children.add(tag)
    walk p
    if p.curr.kind == tkPunct and p.curr.value == "{":
      body = parseStructBody(p)
    else:
      if body == nil:
        body = newEmptyNode()
  else:
    error(p, "Expected identifier or '{' after '" & kind & "'")

  if body != nil:
    result.children.add(body)
  elif tag != nil:
    result.children.add(newEmptyNode())

  while true:
    if p.curr.kind == tkPunct and p.curr.value == ";":
      walk p
      return
    elif p.curr.kind == tkPunct and p.curr.value == ",":
      walk p
      let decl = parseDeclarator(p)
      var init: Node
      if p.curr.kind == tkPunct and p.curr.value == "=":
        walk p
        init = if p.curr.kind == tkPunct and p.curr.value == "{":
                 parseBlock(p)
               else:
                 parseExpression(p, 0)
      else:
        init = newEmptyNode()
      result.children.add(Node(kind: nkIdentDefs, children: @[decl, init]))
    else:
      let decl = parseDeclarator(p)
      var init: Node
      if p.curr.kind == tkPunct and p.curr.value == "=":
        walk p
        init = if p.curr.kind == tkPunct and p.curr.value == "{":
                 parseBlock(p)
               else:
                 parseExpression(p, 0)
      else:
        init = newEmptyNode()
      result.children.add(Node(kind: nkIdentDefs, children: @[decl, init]))

proc cHandlers*(p: var GenericParser) =
  prefixHandler p, "*":
    walk p
    let operand = parseExpression(p, 0)
    result = Node(kind: nkPrefix,
      children: @[Node(kind: nkIdent, name: "*"), operand])

  prefixHandler p, "&":
    walk p
    let operand = parseExpression(p, 0)
    result = Node(kind: nkPrefix,
      children: @[Node(kind: nkIdent, name: "&"), operand])

  ## declare: parse any number of specifiers, then (comma-separated) declarators
  ## with optional initializers. If a declarator has function params and is
  ## followed by `{` we create a function definition.
  stmtHandler p, "declarator":
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "decl"))

    var specifiers: seq[string]
    while p.curr.kind == tkIdentifier and p.curr.value in cSpecifiers:
      if p.curr.value in ["struct", "union", "enum"]:
        break
      specifiers.add(p.curr.value)
      walk p

    for s in specifiers:
      result.children.add(Node(kind: nkIdent, name: s))

    template parseOne: Node =
      let decl = parseDeclarator(p)
      var init: Node
      if p.curr.kind == tkPunct and p.curr.value == "=":
        walk p
        init = if p.curr.kind == tkPunct and p.curr.value == "{":
                 parseBlock(p)
               else:
                 parseExpression(p, 0)
      else:
        init = newEmptyNode()

      if p.curr.kind == tkPunct and p.curr.value == "{" and
         decl.kind == nkCall and decl.children.len >= 2:
        let fnNode = Node(kind: nkFunction)
        fnNode.children.add(decl.children[0])
        fnNode.children.add(decl.children[1])
        fnNode.children.add(parseBlock(p))
        return fnNode

      Node(kind: nkIdentDefs, children: @[decl, init])

    result.children.add(parseOne())
    while p.curr.kind == tkPunct and p.curr.value == ",":
      walk p
      result.children.add(parseOne())

    p.walkOpt(";")

  stmtHandler p, "conditional":
    walk p
    p.expectWalk("(")
    let cond = parseCommaExpr(p)
    p.expectWalk(")")
    var children = @[cond]
    children.add(
      if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
      else: parseStatement(p))
    while p.curr.kind == tkIdentifier and p.curr.value == "else":
      walk p
      if p.curr.kind == tkIdentifier and p.curr.value == "if":
        walk p
        p.expectWalk("(")
        children.add(parseExpression(p))
        p.expectWalk(")")
      children.add(
        if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
        else: parseStatement(p))
      if p.prev.value != "if":
        break
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "if")] & children)

  stmtHandler p, "loop":
    walk p
    p.expectWalk("(")
    let cond = parseExpression(p)
    p.expectWalk(")")
    let body = if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
               else: parseStatement(p)
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "while"), cond, body])

  stmtHandler p, "do_loop":
    walk p
    let body = if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
               else: parseStatement(p)
    if p.curr.kind != tkIdentifier or p.curr.value != "while":
      error(p, "Expected 'while' after do block")
    walk p
    p.expectWalk("(")
    let cond = parseExpression(p)
    p.expectWalk(")")
    p.walkOpt(";")
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "do-while"), body, cond])

  stmtHandler p, "for_loop":
    walk p
    p.expectWalk("(")
    var initNode: Node
    if p.curr.kind == tkPunct and p.curr.value == ";":
      initNode = Node(kind: nkEmpty)
      walk p
    elif p.curr.kind == tkIdentifier and p.curr.value in cSpecifiers:
      initNode = Node(kind: nkStatement)
      initNode.children.add(Node(kind: nkIdent, name: "decl"))
      while p.curr.kind == tkIdentifier and p.curr.value in cSpecifiers:
        if p.curr.value in ["struct", "union", "enum"]:
          break
        initNode.children.add(Node(kind: nkIdent, name: p.curr.value))
        walk p
      let decl = parseDeclarator(p)
      var initVal: Node
      if p.curr.kind == tkPunct and p.curr.value == "=":
        walk p
        initVal = parseExpression(p, 0)
      else:
        initVal = newEmptyNode()
      initNode.children.add(Node(kind: nkIdentDefs, children: @[decl, initVal]))
      p.expectWalk(";")
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
    let body = if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
               else: parseStatement(p)
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "for"),
                  initNode, condNode, updateNode, body])

  stmtHandler p, "switch":
    walk p
    p.expectWalk("(")
    let scrutinee = parseExpression(p)
    p.expectWalk(")")
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "switch"))
    result.children.add(scrutinee)
    let body = Node(kind: nkBlock)
    p.expectWalk("{")
    while not (p.curr.kind == tkPunct and p.curr.value == "}"):
      if p.curr.kind == tkEOF: error(p, "Unexpected EOF in switch")
      if p.curr.kind in {tkComment, tkDocComment}:
        body.children.add(parseCommentGeneric(p))
        continue
      body.children.add(parseStatement(p))
    p.expectWalk("}")
    result.children.add(body)

  stmtHandler p, "case":
    let isDefault = p.curr.value == "default"
    walk p
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent,
      name: if isDefault: "default" else: "case"))
    if not isDefault:
      result.children.add(parseExpression(p))
    p.expectWalk(":")
    var caseBody = Node(kind: nkBlock)
    while not (p.curr.kind == tkPunct and p.curr.value == "}") and
          not (p.curr.kind == tkIdentifier and
               p.curr.value in ["case", "default"]):
      if p.curr.kind == tkEOF:
        error(p, "Unexpected EOF in case body")
      if p.curr.kind in {tkComment, tkDocComment}:
        caseBody.children.add(parseCommentGeneric(p))
        continue
      caseBody.children.add(parseStatement(p))
    result.children.add(caseBody)

  stmtHandler p, "return":
    walk p
    result = Node(kind: nkReturn)
    if (p.curr.kind == tkPunct and p.curr.value in [";", "}"]) or
       p.curr.kind == tkEOF:
      p.walkOpt(";")
      return
    result.children.add(parseCommaExpr(p))
    p.walkOpt(";")

  stmtHandler p, "break":
    walk p
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "break")])
    p.walkOpt(";")

  stmtHandler p, "continue":
    walk p
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "continue")])
    p.walkOpt(";")

  stmtHandler p, "goto":
    walk p
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "goto"))
    if p.curr.kind != tkIdentifier:
      error(p, "Expected label name after 'goto'")
    result.children.add(Node(kind: nkIdent, name: p.curr.value))
    walk p
    p.walkOpt(";")

  stmtHandler p, "typedef":
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "typedef"))
    walk p
    var specifiers: seq[string]
    while p.curr.kind == tkIdentifier and p.curr.value in cSpecifiers:
      if p.curr.value in ["struct", "union", "enum"]:
        break
      specifiers.add(p.curr.value)
      walk p
    for s in specifiers:
      result.children.add(Node(kind: nkIdent, name: s))
    var first = true
    while true:
      if not first:
        if p.curr.kind == tkPunct and p.curr.value == ",":
          walk p
        else:
          break
      first = false
      let decl = parseDeclarator(p)
      result.children.add(Node(kind: nkIdentDefs, children: @[decl, newEmptyNode()]))
    p.walkOpt(";")

  stmtHandler p, "struct":
    result = parseStructUnionDecl(p, "struct")

  stmtHandler p, "union":
    result = parseStructUnionDecl(p, "union")

  stmtHandler p, "enum":
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "enum"))
    walk p
    if p.curr.kind == tkPunct and p.curr.value == "{":
      result.children.add(parseEnumBody(p))
    elif p.curr.kind == tkIdentifier:
      let tag = Node(kind: nkIdent, name: p.curr.value)
      result.children.add(tag)
      walk p
      if p.curr.kind == tkPunct and p.curr.value == "{":
        result.children.add(parseEnumBody(p))
      else:
        result.children.add(newEmptyNode())
    else:
      error(p, "Expected identifier or '{' after 'enum'")
    while not (p.curr.kind == tkPunct and p.curr.value == ";"):
      if p.curr.kind == tkPunct and p.curr.value == ",":
        walk p
        let decl = parseDeclarator(p)
        var init: Node
        if p.curr.kind == tkPunct and p.curr.value == "=":
          walk p
          init = parseExpression(p, 0)
        else:
          init = newEmptyNode()
        result.children.add(Node(kind: nkIdentDefs, children: @[decl, init]))
      else:
        let decl = parseDeclarator(p)
        var init: Node
        if p.curr.kind == tkPunct and p.curr.value == "=":
          walk p
          init = parseExpression(p, 0)
        else:
          init = newEmptyNode()
        result.children.add(Node(kind: nkIdentDefs, children: @[decl, init]))
    walk p

  stmtHandler p, "static_assert":
    walk p
    p.expectWalk("(")
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "_Static_assert"))
    result.children.add(parseExpression(p, 0))
    p.expectWalk(",")
    result.children.add(parseExpression(p, 0))
    p.expectWalk(")")
    p.walkOpt(";")

proc parseC*(path: string): OpenAstProgram =
  try:
    result = parseScript(path, cHandlers,
      features = {featLabeledStmt})
  except OpenAstParsingError as e:
    echo e.msg
