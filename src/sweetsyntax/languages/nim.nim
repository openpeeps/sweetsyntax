# A powerful generic parser and AST explorer for analyzing
# programming languages!
#
# (c) 2026 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

import std/[tables, strutils, options]
import ../[config, sweetlexer]
import ../engine/[ast, parser]

proc parseImportPath(p: var GenericParser): Node =
  ## Parse a Nim import path like `module/sub/[a, b]` or `../relative/path`
  result = Node(kind: nkIdentDefs)
  let startCol = p.curr.col
    # Parse path segments separated by `/`
  while true:
    if p.curr.col < startCol:
      # Next token is at a lower indentation — new statement, not a path segment
      break
    if p.curr.kind == tkString:
      result.children.add(Node(kind: nkLitString, valStr: p.curr.value))
      walk p
    elif p.curr.kind == tkIdentifier:
      result.children.add(Node(kind: nkIdent, name: p.curr.value))
      walk p
    elif p.curr.kind == tkPunct and p.curr.value == "/":
      result.children.add(Node(kind: nkIdent, name: "/"))
      walk p
    elif p.curr.kind == tkPunct and p.curr.value in [".", ".."]:
      result.children.add(Node(kind: nkIdent, name: p.curr.value))
      walk p
    elif p.curr.kind == tkPunct and p.curr.value == "[":
      # Submodule bracket group: [mod1/sub, mod2]
      walk p
      while not (p.curr.kind == tkPunct and p.curr.value == "]"):
        if p.curr.kind == tkEOF: error(p, "Unexpected EOF in import bracket group")
        if p.curr.kind in {tkComment, tkDocComment}:
          discard parseCommentGeneric(p)
          continue
        if p.curr.kind == tkIdentifier:
          result.children.add(Node(kind: nkIdent, name: p.curr.value))
          walk p
        elif p.curr.kind == tkPunct and p.curr.value in [",", "/", ".", ".."]:
          result.children.add(Node(kind: nkIdent, name: p.curr.value))
          walk p
        else:
          error(p, "Expected identifier, '/', or ',' in import bracket group")
      result.children.add(Node(kind: nkIdent, name: "]"))
      p.expectWalk("]")
      break
    else:
      break

proc nimHandlers*(p: var GenericParser) =
  # Register Nim-specific statement handlers.
  p.stmtKeywords["type"] = "type_handler"

  prefixHandler p, "$":
    ## `$` string conversion operator: `$expr` converts to string
    walk p # consume '$'
    let operand = parseExpression(p, 13) # bind tighter than binary ops
    result = Node(kind: nkPrefix,
      children: @[Node(kind: nkIdent, name: "$"), operand])

  stmtHandler p, "declarator":
    ## let/const/var name [= expr], name2 [= expr], ...
    ## Also handles: let/const/var name: Type [= expr], let (a, b) = expr
    result = Node(kind: nkStatement)
    let kw = p.curr.value
    result.children.add(Node(kind: nkIdent, name: kw))
    walk p
    while true:
      if p.curr.kind == tkPunct and p.curr.value == "(":
        # Tuple destructuring: let (a, b) = expr
        let pattern = parseExpression(p)
        result.children.add(pattern)
        if p.curr.kind == tkPunct and p.curr.value == "=":
          walk p
          result.children.add(parseExpression(p))
        else:
          result.children.add(ast.newEmptyNode())
      else:
        let varDef = Node(kind: nkIdentDefs)
        var fieldName = Node(kind: nkIdent, name: p.curr.value)
        walk p
        # Nim export marker `*` after name (e.g., `invalidFilenameChars*`)
        if p.curr.kind == tkPunct and p.curr.value == "*":
          fieldName = Node(kind: nkPostfix,
            children: @[fieldName, Node(kind: nkIdent, name: "*")])
          walk p
        varDef.children.add(fieldName)
        # optional type annotation: `: Type`
        if p.curr.kind == tkPunct and p.curr.value == ":":
          walk p
          varDef.children.add(parseExpression(p))
        else:
          varDef.children.add(ast.newEmptyNode())
        # optional default value: `= expr`
        if p.curr.kind == tkPunct and p.curr.value == "=":
          walk p
          varDef.children.add(parseExpression(p))
        else:
          varDef.children.add(ast.newEmptyNode())
        result.children.add(varDef)
      if p.curr.kind == tkPunct and p.curr.value == ",":
        walk p
      else: break
    p.walkOpt(";")
    p.walkOpt(";")

  stmtHandler p, "const_decl":
    ## const NAME: Type = expr;  or  const NAME = expr;
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "const"))
    walk p # consume 'const'
    var name = Node(kind: nkIdent, name: p.curr.value)
    walk p
    # Nim export marker `*` after name
    if p.curr.kind == tkPunct and p.curr.value == "*":
      name = Node(kind: nkPostfix,
        children: @[name, Node(kind: nkIdent, name: "*")])
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
    p.walkOpt(";")

  stmtHandler p, "return":
    walk p # consume 'return'
    result = Node(kind: nkReturn)
    if (p.curr.kind == tkPunct and p.curr.value in [";", "}"]) or
       p.curr.kind == tkEOF:
      p.walkOpt(";")
      return
    while p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p))
    if p.curr.kind == tkIdentifier and p.curr.value in ["of", "else", "elif"]:
      p.walkOpt(";")
      return
    result.children.add(parseExpression(p))
    p.walkOpt(";")

  stmtHandler p, "conditional":
    ## if cond: body  elif cond: body  else: body
    ## Supports both `if cond:` (Nim) and `if (cond)` (brace-style)
    walk p # consume 'if'/'when'
    let condCol = p.prev.col
    var children: seq[Node]
    if p.curr.kind == tkPunct and p.curr.value == "(":
      walk p
      children.add(parseExpression(p))
      p.expectWalk(")")
    else:
      children.add(parseExpression(p, 1))
    let colonLine = p.curr.line
    children.add(
      if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
      elif p.curr.kind == tkPunct and p.curr.value == ":":
        walk p
        if p.curr.line == colonLine: parseStatement(p)
        else: parseBlock(p, condCol)
      else: parseStatement(p))
    while p.curr.kind == tkIdentifier and p.curr.value in ["elif", "else", "of"]:
      let isElif = p.curr.value in ["elif", "of"]
      walk p
      if isElif:
        if p.curr.kind == tkPunct and p.curr.value == "(":
          walk p
          children.add(parseExpression(p))
          p.expectWalk(")")
        else:
          children.add(parseExpression(p, 1))
      let colonLine2 = p.curr.line
      children.add(
        if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
        elif p.curr.kind == tkPunct and p.curr.value == ":":
          walk p
          if p.curr.line == colonLine2: parseStatement(p)
          else: parseBlock(p, condCol)
        else: parseStatement(p))
      if not isElif: break
      if p.curr.kind != tkIdentifier or p.curr.value notin ["elif", "else", "of"]:
        break
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "if")] & children)

  stmtHandler p, "loop":
    ## while cond: body
    ## Supports both `while cond:` (Nim) and `while (cond)` (brace-style)
    walk p # consume 'while'
    let whileCol = p.prev.col
    let cond = if p.curr.kind == tkPunct and p.curr.value == "(":
                 walk p; let c = parseExpression(p); p.expectWalk(")"); c
               else:
                 parseExpression(p)
    let body = if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
               elif p.curr.kind == tkPunct and p.curr.value == ":":
                 walk p; parseBlock(p, whileCol)
               else: parseStatement(p)
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "while"), cond, body])

  stmtHandler p, "for_loop":
    ## for i in 0 ..< 10: body
    ## Supports both `for i in iterable:` (Nim) and `for (i in iterable)` (brace-style)
    walk p # consume 'for'
    let forCol = p.prev.col
    let hasParens = p.curr.kind == tkPunct and p.curr.value == "("
    if hasParens: walk p
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
    if hasParens:
      p.expectWalk(")")
    let body = if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
               elif p.curr.kind == tkPunct and p.curr.value == ":":
                 walk p; parseBlock(p, forCol)
               else: parseStatement(p)
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "for"), vars, iterable, body])

  stmtHandler p, "case":
    ## case expr
    ##   of pat1, pat2: body
    ##   of pat3: body
    ##   else: body
    ## In brace mode: case (expr) { of (pat1) { body } else { body } }
    walk p # consume 'case'
    # Use high minPrec to avoid consuming `of` as a binary infix operator
    let scrutinee = parseExpression(p, 6)
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "case"), scrutinee])
    if p.curr.kind == tkPunct and p.curr.value == "{":
      # Brace mode: case expr { of pat { body } else { body } }
      walk p
      while not (p.curr.kind == tkPunct and p.curr.value == "}"):
        if p.curr.kind == tkEOF: error(p, "Unexpected EOF in case")
        if p.curr.kind == tkIdentifier and p.curr.value == "of":
          walk p
          let pattern = Node(kind: nkStatement)
          pattern.children.add(Node(kind: nkIdent, name: "of"))
          pattern.children.add(parseExpression(p))
          while p.curr.kind == tkPunct and p.curr.value == ",":
            walk p
            pattern.children.add(parseExpression(p))
          p.expectWalk(":")
          pattern.children.add(
            if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
            else: parseStatement(p))
          result.children.add(pattern)
        elif p.curr.kind == tkIdentifier and p.curr.value == "else":
          walk p
          p.expectWalk(":")
          let elseBranch = Node(kind: nkStatement)
          elseBranch.children.add(Node(kind: nkIdent, name: "else"))
          elseBranch.children.add(
            if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
            else: parseStatement(p))
          result.children.add(elseBranch)
        else:
          error(p, "Expected 'of' or 'else' in case")
      p.expectWalk("}")

    else:
      # Indent mode: case expr\n of pat: body\n of pat: body\n else: body
      if p.curr.kind == tkPunct and p.curr.value == ":":
        walk p
      while p.curr.kind == tkIdentifier and p.curr.value in ["of", "else"]:
        let isOf = p.curr.value == "of"
        let branchCol = p.curr.col
        walk p
        if isOf:
          let pattern = Node(kind: nkStatement)
          pattern.children.add(Node(kind: nkIdent, name: "of"))
          pattern.children.add(parseExpression(p))
          while p.curr.kind == tkPunct and p.curr.value == ",":
            walk p
            pattern.children.add(parseExpression(p))
          if p.curr.kind == tkPunct and p.curr.value == ":":
            walk p
          # Temporarily remove `of` and `else` from infixTable to prevent
          # them from being consumed as binary infix operators in case branch bodies
          var savedOf: Option[InfixEntry]
          var savedElse: Option[InfixEntry]
          if p.infixTable.hasKey("of"):
            savedOf = some(p.infixTable["of"])
            p.infixTable.del("of")
          if p.infixTable.hasKey("else"):
            savedElse = some(p.infixTable["else"])
            p.infixTable.del("else")
          var body = Node(kind: nkBlock)
          while p.curr.kind != tkEOF and p.curr.col > branchCol:
            if p.curr.kind in {tkComment, tkDocComment}:
              body.children.add(parseCommentGeneric(p))
              continue
            body.children.add(parseExpression(p, 0))
          if savedOf.isSome: p.infixTable["of"] = savedOf.get
          if savedElse.isSome: p.infixTable["else"] = savedElse.get
          pattern.children.add(body)
          result.children.add(pattern)
        else:
          if p.curr.kind == tkPunct and p.curr.value == ":":
            walk p
          var savedOf2: Option[InfixEntry]
          var savedElse2: Option[InfixEntry]
          if p.infixTable.hasKey("of"):
            savedOf2 = some(p.infixTable["of"])
            p.infixTable.del("of")
          if p.infixTable.hasKey("else"):
            savedElse2 = some(p.infixTable["else"])
            p.infixTable.del("else")
          var body = Node(kind: nkBlock)
          while p.curr.kind != tkEOF and p.curr.col > branchCol:
            if p.curr.kind in {tkComment, tkDocComment}:
              body.children.add(parseCommentGeneric(p))
              continue
            body.children.add(parseExpression(p, 0))
          if savedOf2.isSome: p.infixTable["of"] = savedOf2.get
          if savedElse2.isSome: p.infixTable["else"] = savedElse2.get
          let elseBranch = Node(kind: nkStatement)
          elseBranch.children.add(Node(kind: nkIdent, name: "else"))
          elseBranch.children.add(body)
          result.children.add(elseBranch)
          break

  proc parseTryBody(p: var GenericParser, parentCol: int): Node =
    if p.curr.kind == tkPunct and p.curr.value == "{":
      parseBlock(p)
    elif p.curr.kind == tkPunct and p.curr.value == ":":
      walk p; parseBlock(p, parentCol)
    else:
      parseStatement(p)

  stmtHandler p, "try_catch":
    ## try: body  except: body  finally: body
    ## In brace mode: try { } except { } finally { }
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "try"))
    walk p # consume 'try'
    let tryCol = p.prev.col
    result.children.add(parseTryBody(p, tryCol))
    # except blocks (Nim uses `except`, not `catch`)
    while p.curr.kind == tkIdentifier and p.curr.value == "except":
      walk p
      let exceptBlock = Node(kind: nkStatement)
      exceptBlock.children.add(Node(kind: nkIdent, name: "except"))
      # optional exception type(s) and `as variable`
      if p.curr.kind != tkPunct or p.curr.value notin [":", "{"]:
        exceptBlock.children.add(parseExpression(p))
        # handle `as variableName` after exception type
        if p.curr.kind == tkIdentifier and p.curr.value == "as":
          walk p
          exceptBlock.children.add(Node(kind: nkIdent, name: p.curr.value))
          walk p
      exceptBlock.children.add(parseTryBody(p, tryCol))
      result.children.add(exceptBlock)
    # finally
    if p.curr.kind == tkIdentifier and p.curr.value == "finally":
      walk p
      result.children.add(Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "finally"), parseTryBody(p, tryCol)]))

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
    ## import module/path, module2/path
    ## import module/[sub1, sub2]
    walk p # consume 'import'
    result = Node(kind: nkImport)
    while true:
      result.children.add(parseImportPath(p))
      if p.curr.kind == tkPunct and p.curr.value == ",":
        walk p
      else:
        break
    p.walkOpt(";")

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
    p.walkOpt(";")

  proc parsePragma(p: var GenericParser): Node =
    ## Parse a Nim pragma starting after `{` is consumed.
    ## Supports {.abc.}, {.abc, efg.}, {.deprecated: [TFile: File].}
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "pragma"))
    if p.curr.kind == tkPunct and p.curr.value == ".":
      walk p
    while not (p.curr.kind == tkPunct and p.curr.value == "}"):
      if p.curr.kind == tkEOF: error(p, "Unexpected EOF in pragma")
      if p.curr.kind in {tkComment, tkDocComment}:
        discard parseCommentGeneric(p); continue
      if p.curr.kind == tkIdentifier:
        let identVal = p.curr.value
        walk p
        if p.curr.kind == tkPunct and p.curr.value == ":":
          walk p
          result.children.add(Node(kind: nkColonExpr,
            children: @[Node(kind: nkIdent, name: identVal), parseExpression(p, 15)]))
        else:
          result.children.add(Node(kind: nkIdent, name: identVal))
      elif p.curr.kind == tkPunct and p.curr.value == ".":
        if p.next.kind == tkPunct and p.next.value == "}":
          walk p
        else:
          walk p
      elif p.curr.kind == tkPunct and p.curr.value == ",":
        walk p
      else:
        result.children.add(parseExpression(p))
    if p.curr.kind == tkPunct and p.curr.value == ".":
      walk p
    p.expectWalk("}")

  proc parseNimBrace(p: var GenericParser, minPrec: int = 0): Node =
    walk p # consume '{'
    if p.curr.kind == tkPunct and p.curr.value == ".":
      return parsePragma(p)
    result = Node(kind: nkBlock)
    while not (p.curr.kind == tkPunct and p.curr.value == "}"):
      if p.curr.kind == tkEOF: error(p, "Unexpected EOF in brace expr")
      if p.curr.kind in {tkComment, tkDocComment}:
        discard parseCommentGeneric(p); continue
      result.children.add(parseExpression(p))
      p.walkOpt(",")
    p.expectWalk("}")

  p.braceHandler = parseNimBrace

  stmtHandler p, "function":
    ## proc/func/method/iterator/converter name(params): returnType = body
    ## In brace mode: proc name(params) { body }
    result = Node(kind: nkFunction)
    let keyword = p.curr.value
    result.children.add(Node(kind: nkIdent, name: keyword))
    let fnCol = p.curr.col
    walk p # consume proc/func/method/iterator/converter
    # optional name
    if p.curr.kind == tkIdentifier:
      var fnName = Node(kind: nkIdent, name: p.curr.value)
      walk p
      # Nim export marker `*` after name (e.g., `proc walk*`)
      if p.curr.kind == tkPunct and p.curr.value == "*":
        fnName = Node(kind: nkPostfix,
          children: @[fnName, Node(kind: nkIdent, name: "*")])
        walk p
      result.children.add(fnName)
    else:
      result.children.add(Node(kind: nkEmpty))
    # Nim pragma before params (e.g., `proc name {.pragma.}(params)`)
    while p.curr.kind == tkPunct and p.curr.value == "{" and
          p.next.kind == tkPunct and p.next.value == ".":
      walk p
      result.children.add(parsePragma(p))
    # params: (name: Type, name2: Type)
    let params = Node(kind: nkIdentDefs)
    if p.curr.kind == tkPunct and p.curr.value == "(":
      walk p
      while not (p.curr.kind == tkPunct and p.curr.value == ")"):
        if p.curr.kind == tkEOF: error(p, "Unexpected EOF in params")
        let paramName = Node(kind: nkIdent, name: p.curr.value)
        walk p
        if p.curr.kind == tkPunct and p.curr.value == ":":
          walk p
          let paramType = parseExpression(p)
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
    # Nim pragma {.abc, efg.}
    while p.curr.kind == tkPunct and p.curr.value == "{" and
          p.next.kind == tkPunct and p.next.value == ".":
      walk p # consume '{'
      result.children.add(parsePragma(p))
    # body: `= expr` or `= block` or `{ block }`
    if p.curr.kind == tkPunct and p.curr.value == "=":
      let bodyLine = p.curr.line
      walk p
      if p.curr.kind == tkPunct and p.curr.value == p.blockOpen:
        result.children.add(parseBlock(p))
      elif p.curr.line != bodyLine:
        result.children.add(parseBlock(p, fnCol))
      else:
        result.children.add(parseExpression(p))
    elif p.curr.kind == tkPunct and p.curr.value == p.blockOpen:
      result.children.add(parseBlock(p))
    else:
      result.children.add(Node(kind: nkEmpty))

  stmtHandler p, "macro":
    ## template/macro name(params) = body
    result = Node(kind: nkFunction)
    let keyword = p.curr.value
    result.children.add(Node(kind: nkIdent, name: keyword))
    walk p # consume template/macro
    # optional name
    if p.curr.kind == tkIdentifier:
      var fnName = Node(kind: nkIdent, name: p.curr.value)
      walk p
      # Nim export marker `*` after name (e.g., `template stmtHandler*`)
      if p.curr.kind == tkPunct and p.curr.value == "*":
        fnName = Node(kind: nkPostfix,
          children: @[fnName, Node(kind: nkIdent, name: "*")])
        walk p
      result.children.add(fnName)
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
    # return type: `: ReturnType`
    if p.curr.kind == tkPunct and p.curr.value == ":":
      walk p
      result.children.add(parseExpression(p))
    else:
      result.children.add(Node(kind: nkEmpty))
    # Nim pragma {.abc, efg.}
    while p.curr.kind == tkPunct and p.curr.value == "{" and
          p.next.kind == tkPunct and p.next.value == ".":
      walk p # consume '{'
      result.children.add(parsePragma(p))
    # body
    if p.curr.kind == tkPunct and p.curr.value == "=":
      let bodyCol2 = p.curr.col
      walk p
      if p.curr.kind == tkPunct and p.curr.value == p.blockOpen:
        result.children.add(parseBlock(p))
      elif p.curr.col > bodyCol2:
        result.children.add(parseBlock(p, bodyCol2))
      else:
        result.children.add(parseExpression(p))
    elif p.curr.kind == tkPunct and p.curr.value == p.blockOpen:
      result.children.add(parseBlock(p))
    else:
      result.children.add(Node(kind: nkEmpty))

  stmtHandler p, "type_handler":
    ## type Name = object
    ##   field: Type
    ##   field2: Type
    walk p # consume 'type'
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "type"))
    # parse type definitions (one or more)
    let body = Node(kind: nkBlock)
    let indent = if parentCol >= 0: parentCol else: max(0, p.curr.col - 1)
    if p.curr.kind == tkPunct and p.curr.value == "{":
      result.children.add(parseBlock(p))
    else:
      if p.curr.kind == tkPunct and p.curr.value == ":":
        walk p
      while p.curr.kind != tkEOF and p.curr.col > indent:
        if p.curr.kind in {tkComment, tkDocComment}:
          body.children.add(parseCommentGeneric(p))
          continue
        if p.curr.kind == tkIdentifier:
          var fieldName = Node(kind: nkIdent, name: p.curr.value)
          walk p
          if p.curr.kind == tkPunct and p.curr.value == "*":
            fieldName = Node(kind: nkPostfix,
              children: @[fieldName, Node(kind: nkIdent, name: "*")])
            walk p
          # Handle comma-separated fields: prev*, curr*: Type
          if p.curr.kind == tkPunct and p.curr.value == ",":
            body.children.add(fieldName)
            walk p
          elif p.curr.kind == tkPunct and p.curr.value in ["=", ":"]:
            walk p
            body.children.add(Node(kind: nkInfix,
              children: @[Node(kind: nkIdent, name: p.curr.value),
                         fieldName,
                         parseExpression(p)]))
          else:
            body.children.add(fieldName)
        else:
          body.children.add(parseStatement(p, indent))
      result.children.add(body)

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
    while p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p))
    if p.curr.kind notin {tkEOF} and
       not (p.curr.kind == tkPunct and p.curr.value in [";", "}", ":"]) and
       not (p.curr.kind == tkIdentifier and p.curr.value in ["of", "else", "elif"]):
      result.children.add(parseExpression(p))
    p.walkOpt(";")

  stmtHandler p, "discard":
    ## discard expr  or  discard
    walk p # consume 'discard'
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "discard"))
    while p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p))
    if p.curr.kind notin {tkEOF} and
       not (p.curr.kind == tkPunct and p.curr.value in [";", "}", ":"]) and
       not (p.curr.kind == tkIdentifier and p.curr.value in ["of", "else", "elif"]):
      result.children.add(parseExpression(p))
    p.walkOpt(";")

  stmtHandler p, "break":
    ## break  or  break label
    walk p # consume 'break'
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "break")])
    # optional label (must be on same line as `break`)
    if p.curr.kind == tkIdentifier and p.curr.line == p.prev.line:
      result.children.add(Node(kind: nkIdent, name: p.curr.value))
      walk p
    p.walkOpt(";")

  stmtHandler p, "continue":
    ## continue
    walk p # consume 'continue'
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "continue")])
    p.walkOpt(";")

  stmtHandler p, "yield":
    ## yield expr
    walk p # consume 'yield'
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "yield"))
    while p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p))
    if p.curr.kind notin {tkEOF} and
       not (p.curr.kind == tkPunct and p.curr.value in [";", "}", ":"]) and
       not (p.curr.kind == tkIdentifier and p.curr.value in ["of", "else", "elif"]):
      result.children.add(parseExpression(p))
    p.walkOpt(";")

  stmtHandler p, "do_block":
    ## do: body  — used in callback style: foo do (x, y): echo x + y
    ## In brace mode: do { body }
    walk p # consume 'do'
    let body = if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
               elif p.curr.kind == tkPunct and p.curr.value == ":":
                 walk p
                 let indent = if parentCol >= 0: parentCol else: max(0, p.curr.col - 1)
                 parseBlock(p, indent)
               else: parseBlock(p)
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
    p.walkOpt(";")

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

  stmtHandler p, "from":
    ## from module/path import name1, name2
    walk p # consume 'from'
    let modulePath = parseImportPath(p)
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "from"))
    result.children.add(modulePath)
    if p.curr.kind == tkIdentifier and p.curr.value == "import":
      walk p
      let imports = Node(kind: nkIdentDefs)
      while p.curr.kind == tkIdentifier:
        imports.children.add(Node(kind: nkIdent, name: p.curr.value))
        walk p
        p.walkOpt(",")
      result.children.add(imports)
    p.walkOpt(";")

  stmtHandler p, "include":
    ## include file  or  include "file.nim"
    walk p # consume 'include'
    result = Node(kind: nkInclude)
    if p.curr.kind == tkString:
      result.children.add(Node(kind: nkLitString, valStr: p.curr.value))
      walk p
    else:
      result.children.add(parseImportPath(p))
    p.walkOpt(";")

  stmtHandler p, "export":
    ## export name  or  export module/path
    walk p # consume 'export'
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "export"))
    result.children.add(parseImportPath(p))
    p.walkOpt(";")

proc parseNim*(path: string): OpenAstProgram =
  ## Parse a Nim script
  try:
    result = parseScript(path, nimHandlers, features = {featCommandSyntax})
  except OpenAstParsingError as e:
    echo e.msg
