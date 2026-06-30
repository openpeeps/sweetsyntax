# A high-performance tokenizer, parser and AST generator.
#   (c) 2026 George Lemon | LGPL-v3 License
#       Made by Humans from OpenPeeps
#       https://github.com/openpeeps/openast

import std/[tables, strutils]
import ../[config, sweetlexer]
import ../engine/[ast, parser]

proc jsHandlers(p: var GenericParser) =
  # Register Nim-specific statement handlers.

  template expectSemiColonNewLine() =
    if p.next.kind != tkEOF and p.next.line == p.prev.line: 
      p.walkOpt(";")

  stmtHandler p, "declarator":
    ## let/const/var name [= expr], name2 [= expr], ...
    ## Also handles: let/const/var name: Type [= expr]
    result = Node(kind: nkStatement)
    let kw = p.curr.value
    result.children.add(Node(kind: nkIdent, name: kw))
    walk p
    while true:
      # Skip comments between declarations
      while p.curr.kind in {tkComment, tkDocComment}:
        discard parseCommentGeneric(p)
      if p.curr.kind == tkPunct and p.curr.value in ["{", "["]:
        # Destructuring: let { a, b } = obj or let [ a, b ] = arr
        let pattern = parseExpression(p)
        result.children.add(pattern)
        if p.curr.kind == tkPunct and p.curr.value == "=":
          walk p
          result.children.add(parseExpression(p))
        else:
          result.children.add(newEmptyNode())
        if p.curr.kind == tkPunct and p.curr.value == ",":
          walk p
        else: break
      elif p.curr.kind == tkIdentifier:
        let varDef = Node(kind: nkIdentDefs)
        varDef.children.add(Node(kind: nkIdent, name: p.curr.value))
        walk p

        # optional type annotation: `: Type`
        if p.curr.kind == tkPunct and p.curr.value == ":":
          walk p
          varDef.children.add(parseExpression(p))
        else:
          varDef.children.add(newEmptyNode())
        
        # optional default value: `= expr`
        if p.curr.kind == tkPunct and p.curr.value == "=":
          walk p
          varDef.children.add(parseExpression(p))
        else:
          varDef.children.add(newEmptyNode())
        
        result.children.add(varDef)
        if p.curr.kind == tkPunct and p.curr.value == ",":
          walk p
        else: break
      else:
        error(p, "Expected identifier in variable declaration")
    expectSemiColonNewLine()

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
      typeNode = newEmptyNode()
    p.expectWalk("=")
    let val = parseExpression(p)
    result.children.add(Node(kind: nkIdentDefs, children: @[name, typeNode, val]))
    expectSemiColonNewLine()

  stmtHandler p, "return":
    walk p # consume 'return'
    result = Node(kind: nkReturn)
    if (p.curr.kind == tkPunct and p.curr.value in [";", "}"]) or p.curr.kind == tkEOF:
      expectSemiColonNewLine()
      return
    result.children.add(parseCommaExpr(p))
    expectSemiColonNewLine()

  stmtHandler p, "throw":
    walk p # consume 'throw'
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "throw")])
    result.children.add(parseExpression(p))
    p.walkOpt(";")

  stmtHandler p, "conditional":
    ## if cond: body  elif cond: body  else: body
    ## In brace mode: if (cond) { body } elif (cond) { body } else { body }
    walk p # consume 'if'
    p.expectWalk("(")
    let cond = parseCommaExpr(p)
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
    let cond = parseCommaExpr(p)
    p.expectWalk(")")
    let body = if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
               else: parseStatement(p)
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "while"), cond, body])

  stmtHandler p, "do_loop":
    ## do { body } while (cond);  or  do stmt; while (cond);
    walk p # consume 'do'
    let body = if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
               else: parseStatement(p)
    if p.curr.kind != tkIdentifier or p.curr.value != "while":
      error(p, "Expected 'while' after do block")
    walk p # consume 'while'
    p.expectWalk("(")
    let cond = parseExpression(p)
    p.expectWalk(")")
    p.walkOpt(";")
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "do-while"), body, cond])

  stmtHandler p, "for_loop":
    ## for (init; cond; update) { body }
    ## for (var x in obj) { body }
    ## for (var x of iter) { body }
    walk p # consume 'for'
    p.expectWalk("(")

    var initNode: Node
    var loopType = ""  # "", "in", "of", or "c-style"

    if p.curr.kind == tkPunct and p.curr.value == ";":
      # for (;;) or for (; cond; update)
      initNode = Node(kind: nkEmpty)
      loopType = "c-style"
    elif p.curr.kind == tkIdentifier and p.curr.value in ["var", "let", "const"]:
      # for (var/let/const decl; ...) or for (var/let/const x in/of ...)
      initNode = Node(kind: nkStatement)
      initNode.children.add(Node(kind: nkIdent, name: p.curr.value))
      walk p
      while true:
        if p.curr.kind == tkPunct and p.curr.value in ["{", "["]:
          # Destructuring: let { a, b } = obj or let [ a, b ] = arr
          let pattern = parseExpression(p)
          initNode.children.add(pattern)
          if p.curr.kind == tkPunct and p.curr.value == "=":
            walk p
            initNode.children.add(parseExpression(p))
          else:
            initNode.children.add(newEmptyNode())
        else:
          let varDef = Node(kind: nkIdentDefs)
          if p.curr.kind != tkIdentifier:
            error(p, "Expected identifier in variable declaration")
          varDef.children.add(Node(kind: nkIdent, name: p.curr.value))
          walk p
          # optional type annotation
          if p.curr.kind == tkPunct and p.curr.value == ":":
            walk p
            varDef.children.add(parseExpression(p))
          else:
            varDef.children.add(newEmptyNode())
          # optional default value
          if p.curr.kind == tkPunct and p.curr.value == "=":
            walk p
            varDef.children.add(parseExpression(p))
          else:
            varDef.children.add(newEmptyNode())
          initNode.children.add(varDef)
        if p.curr.kind == tkPunct and p.curr.value == ",":
          walk p
        else:
          break
      if p.curr.kind == tkPunct and p.curr.value == ";":
        loopType = "c-style"
      elif p.curr.kind == tkIdentifier and p.curr.value == "in":
        loopType = "in"
      elif p.curr.kind == tkIdentifier and p.curr.value == "of":
        loopType = "of"
    else:
      # for (expr; ...) or for (expr in/of ...)
      if p.curr.kind == tkIdentifier and p.next.kind == tkIdentifier and
         p.next.value in ["in", "of"]:
        # for (variable in/of ...) — single variable, no var/let/const
        initNode = Node(kind: nkIdent, name: p.curr.value)
        walk p
        loopType = p.curr.value
      else:
        # C-style: for (expr; ...) or for (expr, ...; ...)
        initNode = parseCommaExpr(p)
        if p.curr.kind == tkPunct and p.curr.value == ";":
          loopType = "c-style"

    # Dispatch based on loop type
    if loopType == "c-style":
      walk p
      var condNode: Node
      if p.curr.kind == tkPunct and p.curr.value == ";":
        condNode = Node(kind: nkEmpty)
        walk p
      else:
        condNode = parseExpression(p)
        p.walkOpt(";")
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
    elif loopType == "in" or loopType == "of":
      walk p
      let iterable = parseExpression(p)
      p.expectWalk(")")
      let body = if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
                 else: parseStatement(p)
      result = Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "for"), initNode, iterable, body])
    else:
      error(p, "Expected ';', 'in', or 'of' in for loop")

  stmtHandler p, "class":
    ## class Name { ... } or class Name extends Base { ... }
    walk p # consume 'class'
    let name = Node(kind: nkIdent, name: p.curr.value)
    walk p
    var parent: Node
    if p.curr.kind == tkIdentifier and p.curr.value == "extends":
      walk p
      parent = parseExpression(p)
    else:
      parent = newEmptyNode()
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "class"), name, parent, parseBlock(p)])

  stmtHandler p, "switch":
    ## switch (expr) { case x: body; ... }
    walk p # consume 'switch'
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
      if p.curr.kind == tkIdentifier and p.curr.value == "case":
        walk p
        let caseNode = Node(kind: nkStatement)
        caseNode.children.add(Node(kind: nkIdent, name: "case"))
        caseNode.children.add(parseExpression(p))
        p.expectWalk(":")
        var caseBody = Node(kind: nkBlock)
        while not (p.curr.kind == tkPunct and p.curr.value == "}") and
              not (p.curr.kind == tkIdentifier and p.curr.value in ["case", "default"]):
          if p.curr.kind == tkEOF: error(p, "Unexpected EOF in case")
          if p.curr.kind in {tkComment, tkDocComment}:
            caseBody.children.add(parseCommentGeneric(p))
            continue
          caseBody.children.add(parseStatement(p))
        caseNode.children.add(caseBody)
        body.children.add(caseNode)
      elif p.curr.kind == tkIdentifier and p.curr.value == "default":
        walk p
        let defaultNode = Node(kind: nkStatement)
        defaultNode.children.add(Node(kind: nkIdent, name: "default"))
        p.expectWalk(":")
        var defaultBody = Node(kind: nkBlock)
        while not (p.curr.kind == tkPunct and p.curr.value == "}") and
              not (p.curr.kind == tkIdentifier and p.curr.value in ["case", "default"]):
          if p.curr.kind == tkEOF: error(p, "Unexpected EOF in default")
          if p.curr.kind in {tkComment, tkDocComment}:
            defaultBody.children.add(parseCommentGeneric(p))
            continue
          defaultBody.children.add(parseStatement(p))
        defaultNode.children.add(defaultBody)
        body.children.add(defaultNode)
      else:
        body.children.add(parseStatement(p))
    p.expectWalk("}")
    result.children.add(body)

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
        newEmptyNode()
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

  stmtHandler p, "include":
    ## include file  or  include "file.nim"
    walk p # consume 'include'
    result = Node(kind: nkInclude)
    result.children.add(Node(kind: nkLitString, valStr: p.curr.value))
    walk p
    p.walkOpt(";")

  stmtHandler p, "export":
    ## export name  or  export module/name
    walk p # consume 'export'
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "export"))
    result.children.add(Node(kind: nkIdent, name: p.curr.value))
    walk p
    p.walkOpt(";")

  type
    FunctionKind = enum
      fkProc, fkMacro, fkTemplate

  proc registerFunction(p: var GenericParser, keyword: string, kind: FunctionKind): Node =
    ## Register a function-like statement handler for `proc`, `func`, `template` or `macro`
    result = Node(kind: nkFunction)
    result.children.add(Node(kind: nkIdent, name: keyword))
    let parentCol = p.curr.col  # capture the column of `proc`/`func`/etc.
    walk p

    # optional generator marker `*` (JS generators)
    if p.curr.kind == tkPunct and p.curr.value == "*":
      walk p
      result.children.add(Node(kind: nkIdent, name: "*"))
    else:
      result.children.add(newEmptyNode())
    
    # optional name
    if p.curr.kind == tkIdentifier:
      var fnIdent = p.curr.newIdent(p.curr.value)
      walk p
      if p.curr.kind == tkPunct and p.curr.value == "*":
        fnIdent = newPostfix(p.curr.newIdent("*"), fnIdent)
        walk p
      result.children.add(fnIdent)
    else:
      result.children.add(newEmptyNode())
    
    # generic parameters (e.g. `[T]`)
    if p.curr.kind == tkPunct and p.curr.value == "[":
      let generics = Node(kind: nkIdentDefs)
      walk p
      while not (p.curr.kind == tkPunct and p.curr.value == "]"):
        if p.curr.kind == tkEOF: error(p, "Unexpected EOF in generic parameters")
        if p.curr.kind == tkIdentifier:
          generics.children.add(Node(kind: nkIdent, name: p.curr.value))
          walk p
          if p.curr.kind == tkPunct and p.curr.value == ",":
            walk p
          elif p.curr.kind == tkPunct and p.curr.value == "]":
            break
          else:
            error(p, "Expected ',' or ']' in generic parameters")
        else:
          error(p, "Expected identifier in generic parameters")
      p.expectWalk("]")
      result.children.add(generics)
    else:
      result.children.add(newEmptyNode())

    # params
    let params = Node(kind: nkIdentDefs)
    p.expectWalk("(")
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
      elif p.curr.kind == tkPunct and p.curr.value == "=":
        walk p
        params.children.add(Node(kind: nkIdentDefs,
          children: @[paramName, newEmptyNode(), parseExpression(p)]))
      else:
        params.children.add(paramName)
      p.walkOpt(",")
    p.expectWalk(")")
    result.children.add(params)
    
    # optional return type
    if p.curr.kind == tkPunct and p.curr.value == ":":
      walk p
      p.expect(tkIdentifier)
      result.children.add(parseExpression(p))
    else:
      result.children.add(newEmptyNode())
    
    # body
    if p.curr.kind == tkPunct and p.curr.value == "=":
      walk p  # consume '='
      result.children.add(parseBlock(p, parentCol))  # pass parentCol
    elif p.curr.kind == tkIdentifier:
      result.children.add(parseBlock(p, parentCol))
    elif p.curr.kind == tkPunct and p.curr.value == p.blockOpen:
      result.children.add(parseBlock(p))
    else:
      result.children.add(newEmptyNode())

  stmtHandler p, "function":
    registerFunction(p, "function", fkProc)

  stmtHandler p, "macro":
    ## template/macro name(params) = body
    registerFunction(p, "macro", fkMacro)

  stmtHandler p, "type":
    let parentCol =
      if p.next.line > p.curr.line:
        p.next.col
      else:
        p.curr.col
    walk p # consume 'type'
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "type"))
    
    # parse type name
    let typeIdent = p.curr.newIdent(p.curr.value)
    if p.next.kind == tkPunct and p.next.value == "*":
      walk p
      result.children.add(newPostfix(p.curr.newIdent("*"), typeIdent))
      walk p
    else:
      result.children.add(typeIdent)
      walk p
    
    # parse '='
    if p.curr.kind == tkPunct and p.curr.value == "=":
      walk p
    
    # parse type kind: object, ref object, enum, tuple, distinct, or type alias
    result.children.add(parseExpression(p))
    
    # parse indented fields (object fields, enum variants, etc.)
    if p.curr.col > parentCol:
      while p.curr.kind != tkEOF and p.curr.col > parentCol:
        if p.curr.kind in {tkComment, tkDocComment}:
          result.children.add(parseCommentGeneric(p))
          continue
        # field definition: [name*] [: Type] [= default]
        let field = Node(kind: nkIdentDefs, ln: p.curr.line, col: p.curr.col)
        if p.curr.kind == tkIdentifier:
          var fieldName = p.curr.value
          walk p
          # export marker: `name*`
          if p.curr.kind == tkPunct and p.curr.value == "*":
            walk p
            field.children.add(Node(kind: nkPostfix,
              children: @[Node(kind: nkIdent, name: "*"),
                        Node(kind: nkIdent, name: fieldName)]))
          else:
            field.children.add(Node(kind: nkIdent, name: fieldName))

          # optional type annotation: `: Type`
          if p.curr.kind == tkPunct and p.curr.value == ":":
            walk p
            field.children.add(parseExpression(p))
          else:
            field.children.add(newEmptyNode())
          # optional default value: `= expr`
          if p.curr.kind == tkPunct and p.curr.value == "=":
            walk p
            field.children.add(parseExpression(p))
          else:
            field.children.add(newEmptyNode())

          result.children.add(field)
        else:
          break

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
    p.walkOpt(";")

  stmtHandler p, "discard":
    ## discard expr  or  discard
    walk p # consume 'discard'
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "discard"))
    if p.curr.kind notin {tkEOF} and
       not (p.curr.kind == tkPunct and p.curr.value in [";", "}"]):
      result.children.add(parseExpression(p))
    p.walkOpt(";")

  stmtHandler p, "break":
    ## break  or  break label
    walk p # consume 'break'
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "break")])
    # optional label
    if p.curr.kind == tkIdentifier:
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
    if p.curr.kind notin {tkEOF} and
       not (p.curr.kind == tkPunct and p.curr.value in [";", "}"]):
      result.children.add(parseExpression(p))
    p.walkOpt(";")

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
    result = newEmptyNode()

proc parseJavaScript*(path: string): OpenAstProgram =
  ## Parse a JavaScript file
  try:
    result = parseScript(path, jsHandlers, features = {featAsync, featArrowFn, featGenerators, featLabeledStmt, featTemplateLit})
  except OpenAstParsingError as e:
    echo e.msg
