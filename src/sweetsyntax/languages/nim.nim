# A powerful generic parser and AST explorer for analyzing
# programming languages!
#
# (c) 2026 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

import std/[tables, strutils]
import pkg/sweetsyntax/[config, sweetlexer]

import ./openast/[ast, parser]

proc nimHandlers(p: var GenericParser) =
  # Register Nim-specific statement handlers.

  prefixHandler p, "$":
    ## `$` string conversion operator: `$expr` converts to string
    walk p # consume '$'
    let operand = parseExpression(p, 13) # bind tighter than binary ops
    result = Node(kind: nkPrefix,
      children: @[Node(kind: nkIdent, name: "$"), operand])

  stmtHandler p, "declarator":
    ## let/const/var name [= expr], name2 [= expr], ...
    ## Also handles: let/const/var name: Type [= expr]
    result = Node(kind: nkStatement)
    let kw = p.curr.value
    result.children.add(Node(kind: nkIdent, name: kw))
    walk p
    while true:
      let varDef = Node(kind: nkIdentDefs)
      # name
      varDef.children.add(Node(kind: nkIdent, name: p.curr.value))
      walk p
      # optional type annotation: `: Type`
      if p.curr.kind == tkPunct and p.curr.value == ":":
        walk p
        # parse type (possibly qualified: `seq[int]`, `Table[string, int]`, etc.)
        varDef.children.add(parseExpression(p))
      # optional default value: `= expr`
      if p.curr.kind == tkPunct and p.curr.value == "=":
        walk p
        varDef.children.add(parseExpression(p))
      result.children.add(varDef)
      if p.curr.kind == tkPunct and p.curr.value == ",":
        walk p
      else: break
    # Nim uses `;` or newline; for brace mode use `;`
    p.expectWalk(";")

  stmtHandler p, "const_decl":
    ## const NAME: Type = expr;  or  const NAME = expr;
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "const"))
    walk p # consume 'const'
    let name = Node(kind: nkIdent, name: p.curr.value)
    walk p
    # optional type annotation
    var typeNode: Node
    if p.curr.kind == tkPunct and p.curr.value == ":":
      walk p
      typeNode = parseExpression(p)
    else:
      typeNode = Node(kind: nkEmpty)
    p.expectWalk("=")
    let val = parseExpression(p)
    result.children.add(Node(kind: nkIdentDefs, children: @[name, typeNode, val]))
    p.expectWalk(";")

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
    ## if cond: body  elif cond: body  else: body
    ## In brace mode: if (cond) { body } elif (cond) { body } else { body }
    walk p # consume 'if'
    p.expectWalk("(")
    let cond = parseExpression(p)
    p.expectWalk(")")
    var children = @[cond]
    children.add(
      if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
      else: parseStatement(p))
    while p.curr.kind == tkIdentifier and p.curr.value in ["elif", "else"]:
      let isElif = p.curr.value == "elif"
      walk p
      if isElif:
        p.expectWalk("(")
        children.add(parseExpression(p))
        p.expectWalk(")")
      children.add(
        if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
        else: parseStatement(p))
      if not isElif: break
      if p.curr.kind != tkIdentifier or p.curr.value notin ["elif", "else"]:
        break
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "if")] & children)

  stmtHandler p, "loop":
    ## while cond: body
    ## In brace mode: while (cond) { body }
    walk p # consume 'while'
    p.expectWalk("(")
    let cond = parseExpression(p)
    p.expectWalk(")")
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "while"), cond, parseBlock(p)])

  stmtHandler p, "for_loop":
    ## for i in 0 ..< 10: body
    ## In brace mode: for (i in 0 ..< 10) { body }
    walk p # consume 'for'
    p.expectWalk("(")
    # left-hand side of `in`: variable(s)
    var vars = Node(kind: nkIdentDefs)
    vars.children.add(Node(kind: nkIdent, name: p.curr.value))
    walk p
    while p.curr.kind == tkPunct and p.curr.value == ",":
      walk p
      vars.children.add(Node(kind: nkIdent, name: p.curr.value))
      walk p
    # `in` keyword
    if p.curr.kind == tkIdentifier and p.curr.value == "in":
      walk p
    else:
      error(p, "Expected 'in' in for loop")
    # right-hand side: range / iterable expression
    let iterable = parseExpression(p)
    p.expectWalk(")")
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "for"), vars, iterable, parseBlock(p)])

  stmtHandler p, "case":
    ## case expr
    ##   of pat1, pat2: body
    ##   of pat3: body
    ##   else: body
    ## In brace mode: case (expr) { of (pat1) { body } else { body } }
    walk p # consume 'case'
    let scrutinee = parseExpression(p)
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "case"), scrutinee])
    p.expectWalk("{")
    while not (p.curr.kind == tkPunct and p.curr.value == "}"):
      if p.curr.kind == tkEOF: error(p, "Unexpected EOF in case")
      if p.curr.kind == tkIdentifier and p.curr.value == "of":
        walk p
        let pattern = Node(kind: nkStatement)
        pattern.children.add(Node(kind: nkIdent, name: "of"))
        # parse pattern(s): comma-separated
        pattern.children.add(parseExpression(p))
        while p.curr.kind == tkPunct and p.curr.value == ",":
          walk p
          pattern.children.add(parseExpression(p))
        p.expectWalk(":")
        # body
        if p.curr.kind == tkPunct and p.curr.value == "{":
          pattern.children.add(parseBlock(p))
        else:
          pattern.children.add(parseStatement(p))
        result.children.add(pattern)
      elif p.curr.kind == tkIdentifier and p.curr.value == "else":
        walk p
        p.expectWalk(":")
        let elseBranch = Node(kind: nkStatement)
        elseBranch.children.add(Node(kind: nkIdent, name: "else"))
        if p.curr.kind == tkPunct and p.curr.value == "{":
          elseBranch.children.add(parseBlock(p))
        else:
          elseBranch.children.add(parseStatement(p))
        result.children.add(elseBranch)
      else:
        error(p, "Expected 'of' or 'else' in case")
    p.expectWalk("}")

  stmtHandler p, "try_catch":
    ## try: body  except: body  finally: body
    ## In brace mode: try { } except { } finally { }
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "try"))
    walk p # consume 'try'
    result.children.add(parseBlock(p))
    # except blocks (Nim uses `except`, not `catch`)
    while p.curr.kind == tkIdentifier and p.curr.value == "except":
      walk p
      let exceptBlock = Node(kind: nkStatement)
      exceptBlock.children.add(Node(kind: nkIdent, name: "except"))
      # optional exception type(s)
      if p.curr.kind != tkPunct or p.curr.value != "{":
        # parse exception type: `ExceptDefect` or `AssertionDefect` etc.
        exceptBlock.children.add(Node(kind: nkIdent, name: p.curr.value))
        walk p
      exceptBlock.children.add(parseBlock(p))
      result.children.add(exceptBlock)
    # finally
    if p.curr.kind == tkIdentifier and p.curr.value == "finally":
      walk p
      result.children.add(Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "finally"), parseBlock(p)]))

  stmtHandler p, "block":
    ## block label: body  or  block: body
    ## In brace mode: block (label) { body }  or  block { body }
    walk p # consume 'block'
    let labelNode =
      if p.curr.kind == tkPunct and p.curr.value == "(":
        walk p
        let lbl = Node(kind: nkIdent, name: p.curr.value)
        walk p
        p.expectWalk(")")
        lbl
      elif p.curr.kind == tkIdentifier:
        let lbl = Node(kind: nkIdent, name: p.curr.value)
        walk p
        lbl
      else:
        Node(kind: nkEmpty)
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "block"), labelNode, parseBlock(p)])

  stmtHandler p, "import":
    ## import module  or  import module / sub  or  import module1, module2
    walk p # consume 'import'
    result = Node(kind: nkImport)
    result.children.add(Node(kind: nkIdent, name: p.curr.value))
    walk p
    while p.curr.kind == tkPunct and p.curr.value == ",":
      walk p
      result.children.add(Node(kind: nkIdent, name: p.curr.value))
      walk p
    p.expectWalk(";")

  stmtHandler p, "from":
    ## from module import name1, name2
    walk p # consume 'from'
    let moduleName = Node(kind: nkIdent, name: p.curr.value)
    walk p
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "from"))
    result.children.add(moduleName)
    if p.curr.kind == tkIdentifier and p.curr.value == "import":
      walk p
      let imports = Node(kind: nkIdentDefs)
      imports.children.add(Node(kind: nkIdent, name: p.curr.value))
      walk p
      while p.curr.kind == tkPunct and p.curr.value == ",":
        walk p
        imports.children.add(Node(kind: nkIdent, name: p.curr.value))
        walk p
      result.children.add(imports)
    p.expectWalk(";")

  stmtHandler p, "include":
    ## include file  or  include "file.nim"
    walk p # consume 'include'
    result = Node(kind: nkInclude)
    result.children.add(Node(kind: nkLitString, valStr: p.curr.value))
    walk p
    p.expectWalk(";")

  stmtHandler p, "export":
    ## export name  or  export module/name
    walk p # consume 'export'
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "export"))
    result.children.add(Node(kind: nkIdent, name: p.curr.value))
    walk p
    p.expectWalk(";")

  stmtHandler p, "function":
    ## proc/func/method/iterator/converter name(params): returnType = body
    ## In brace mode: proc name(params) { body }
    result = Node(kind: nkFunction)
    let keyword = p.curr.value
    result.children.add(Node(kind: nkIdent, name: keyword))
    walk p # consume proc/func/method/iterator/converter
    # optional name
    if p.curr.kind == tkIdentifier:
      result.children.add(Node(kind: nkIdent, name: p.curr.value))
      walk p
    else:
      result.children.add(Node(kind: nkEmpty))
    # params: (name: Type, name2: Type)
    let params = Node(kind: nkIdentDefs)
    p.expectWalk("(")
    while not (p.curr.kind == tkPunct and p.curr.value == ")"):
      if p.curr.kind == tkEOF: error(p, "Unexpected EOF in params")
      # param name
      let paramName = Node(kind: nkIdent, name: p.curr.value)
      walk p
      # optional type annotation
      if p.curr.kind == tkPunct and p.curr.value == ":":
        walk p
        let paramType = parseExpression(p)
        # optional default value
        if p.curr.kind == tkPunct and p.curr.value == "=":
          walk p
          params.children.add(Node(kind: nkIdentDefs,
            children: @[paramName, paramType, parseExpression(p)]))
        else:
          params.children.add(Node(kind: nkIdentDefs,
            children: @[paramName, paramType]))
      else:
        params.children.add(paramName)
      p.walkOpt(",")
    p.expectWalk(")")
    result.children.add(params)
    # optional return type: ): ReturnType
    if p.curr.kind == tkPunct and p.curr.value == ":":
      walk p
      result.children.add(parseExpression(p))
    else:
      result.children.add(Node(kind: nkEmpty))
    # body: `= expr` or `= block` or `{ block }`
    if p.curr.kind == tkPunct and p.curr.value == "=":
      walk p
      if p.curr.kind == tkPunct and p.curr.value == p.blockOpen:
        result.children.add(parseBlock(p))
      else:
        result.children.add(parseExpression(p))
    elif p.curr.kind == tkPunct and p.curr.value == p.blockOpen:
      result.children.add(parseBlock(p))
    else:
      # forward declaration (no body)
      result.children.add(Node(kind: nkEmpty))

  stmtHandler p, "macro":
    ## template/macro name(params) = body
    result = Node(kind: nkFunction)
    let keyword = p.curr.value
    result.children.add(Node(kind: nkIdent, name: keyword))
    walk p # consume template/macro
    # optional name
    if p.curr.kind == tkIdentifier:
      result.children.add(Node(kind: nkIdent, name: p.curr.value))
      walk p
    else:
      result.children.add(Node(kind: nkEmpty))
    # params
    let params = Node(kind: nkIdentDefs)
    p.expectWalk("(")
    while not (p.curr.kind == tkPunct and p.curr.value == ")"):
      if p.curr.kind == tkEOF: error(p, "Unexpected EOF in params")
      params.children.add(Node(kind: nkIdent, name: p.curr.value))
      walk p
      p.walkOpt(",")
    p.expectWalk(")")
    result.children.add(params)
    # return type
    result.children.add(Node(kind: nkEmpty))
    # body
    if p.curr.kind == tkPunct and p.curr.value == "=":
      walk p
      if p.curr.kind == tkPunct and p.curr.value == p.blockOpen:
        result.children.add(parseBlock(p))
      else:
        result.children.add(parseExpression(p))
    elif p.curr.kind == tkPunct and p.curr.value == p.blockOpen:
      result.children.add(parseBlock(p))
    else:
      result.children.add(Node(kind: nkEmpty))

  stmtHandler p, "type":
    ## type Name = object
    ##   field: Type
    ##   field2: Type
    walk p # consume 'type'
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "type"))
    # parse type definitions (one or more)
    result.children.add(parseBlock(p))

  stmtHandler p, "defer":
    ## defer: body
    walk p # consume 'defer'
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "defer"), parseBlock(p)])

  stmtHandler p, "raise":
    ## raise newException(...)  or  raise expr
    walk p # consume 'raise'
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "raise"))
    if p.curr.kind notin {tkEOF} and
       not (p.curr.kind == tkPunct and p.curr.value in [";", "}"]):
      result.children.add(parseExpression(p))
    p.expectWalk(";")

  stmtHandler p, "discard":
    ## discard expr  or  discard
    walk p # consume 'discard'
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "discard"))
    if p.curr.kind notin {tkEOF} and
       not (p.curr.kind == tkPunct and p.curr.value in [";", "}"]):
      result.children.add(parseExpression(p))
    p.expectWalk(";")

  stmtHandler p, "break":
    ## break  or  break label
    walk p # consume 'break'
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "break")])
    # optional label
    if p.curr.kind == tkIdentifier:
      result.children.add(Node(kind: nkIdent, name: p.curr.value))
      walk p
    p.expectWalk(";")

  stmtHandler p, "continue":
    ## continue
    walk p # consume 'continue'
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "continue")])
    p.expectWalk(";")

  stmtHandler p, "yield":
    ## yield expr
    walk p # consume 'yield'
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "yield"))
    if p.curr.kind notin {tkEOF} and
       not (p.curr.kind == tkPunct and p.curr.value in [";", "}"]):
      result.children.add(parseExpression(p))
    p.expectWalk(";")

  stmtHandler p, "do_block":
    ## do: body  — used in callback style: foo do (x, y): echo x + y
    ## In brace mode: do { body }
    walk p # consume 'do'
    let body = parseBlock(p)
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "do"), body])

  stmtHandler p, "asm":
    ## asm: ...code...
    walk p # consume 'asm'
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "asm"))
    if p.curr.kind == tkPunct and p.curr.value == p.blockOpen:
      result.children.add(parseBlock(p))
    else:
      # inline asm string
      result.children.add(Node(kind: nkLitString, valStr: p.curr.value))
      walk p
    p.expectWalk(";")

  stmtHandler p, "static":
    ## static: body  — static block for compile-time execution
    walk p # consume 'static'
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "static"))
    if p.curr.kind == tkPunct and p.curr.value == p.blockOpen:
      result.children.add(parseBlock(p))
    else:
      result.children.add(parseStatement(p))

  stmtHandler p, "with":
    ## with resource: body
    walk p # consume 'with'
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "with"))
    result.children.add(parseExpression(p))
    result.children.add(parseBlock(p))

  stmtHandler p, "without":
    ## without trait: body
    walk p # consume 'without'
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "without"))
    result.children.add(parseExpression(p))
    result.children.add(parseBlock(p))

  stmtHandler p, "end":
    ## end — explicit block terminator (Nim optional style)
    walk p # consume 'end'
    result = Node(kind: nkEmpty)

try:
  parseScript("./sample.nim", nimHandlers)
except OpenAstParsingError as e:
  echo e.msg
