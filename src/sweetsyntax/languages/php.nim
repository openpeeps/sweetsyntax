import std/[tables, strutils]
import pkg/sweetsyntax/[config, sweetlexer]

import ./openast/[ast, parser]

proc phpHandlers(p: var GenericParser) =
  # Register PHP-specific statement handlers.
  prefixHandler p, "$":
    # `$` prefix handler for PHP variables: $var, $this, $$var (variable variables)
    walk p # consume '$'
    # variable variables: $$
    if p.curr.kind == tkPunct and p.curr.value == "$":
      walk p
      let inner = Node(kind: nkIdent, name: p.curr.value)
      walk p
      result = Node(kind: nkPrefix,
        children: @[Node(kind: nkIdent, name: "$"), inner])
    else:
      result = Node(kind: nkIdent, name: "$" & p.curr.value)
      walk p

  stmtHandler p, "declarator":
    ## var $x = expr, $y = expr, ...;  or  static $x = expr;
    result = Node(kind: nkStatement)
    let kw = p.curr.value
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
      else: break
    p.expectWalk(";")

  stmtHandler p, "const_decl":
    ## const NAME = expr;
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "const"))
    walk p # consume 'const'
    let name = Node(kind: nkIdent, name: p.curr.value)
    walk p
    p.expectWalk("=")
    let val = parseExpression(p)
    result.children.add(Node(kind: nkIdentDefs, children: @[name, val]))
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
    ## if (cond) { } elseif (cond) { } else { }
    walk p # consume 'if'
    p.expectWalk("(")
    let cond = parseExpression(p)
    p.expectWalk(")")
    var children = @[cond]
    children.add(
      if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
      else: parseStatement(p))
    while p.curr.kind == tkIdentifier and p.curr.value in ["else", "elseif"]:
      let isElseIf = p.curr.value == "elseif"
      walk p
      if isElseIf:
        p.expectWalk("(")
        children.add(parseExpression(p))
        p.expectWalk(")")
      children.add(
        if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
        else: parseStatement(p))
      if not isElseIf: break
      # after elseif, check for another else/elseif
      if p.curr.kind != tkIdentifier or p.curr.value notin ["else", "elseif"]:
        break
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "if")] & children)

  stmtHandler p, "loop":
    walk p # consume 'while'
    p.expectWalk("(")
    let cond = parseExpression(p)
    p.expectWalk(")")
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "while"), cond, parseBlock(p)])

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
    ## for (init; cond; update) { body }
    walk p # consume 'for'
    p.expectWalk("(")
    # init
    var initNode: Node
    if p.curr.kind == tkPunct and p.curr.value == ";":
      initNode = Node(kind: nkEmpty)
      walk p
    else:
      initNode = parseCommaExpr(p)
      p.expectWalk(";")
    # condition
    var condNode: Node
    if p.curr.kind == tkPunct and p.curr.value == ";":
      condNode = Node(kind: nkEmpty)
      walk p
    else:
      condNode = parseExpression(p)
      p.expectWalk(";")
    # update
    var updateNode: Node
    if p.curr.kind == tkPunct and p.curr.value == ")":
      updateNode = Node(kind: nkEmpty)
    else:
      updateNode = parseCommaExpr(p)
    p.expectWalk(")")
    let body = parseBlock(p)
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "for"),
                  initNode, condNode, updateNode, body])

  stmtHandler p, "foreach_loop":
    ## foreach ($arr as $val) { }  or  foreach ($arr as $key => $val) { }
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
    let body = parseBlock(p)
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "foreach"),
                  iterable, keyNode, valNode, body])

  stmtHandler p, "function":
    ## function [name]([params])[: returntype] { body }
    result = p.curr.newFunction()
    walk p # consume 'function'
    # optional reference: function &name
    if p.curr.kind == tkPunct and p.curr.value == "&":
      walk p
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
      # optional type hint
      if p.curr.kind == tkIdentifier:
        # skip type hints like int, string, ?string, array, callable, etc.
        let typeName = p.curr.value
        walk p
        # optional & (pass by reference)
        if p.curr.kind == tkPunct and p.curr.value == "&":
          walk p
        # optional variadic ...
        if p.curr.kind == tkPunct and p.curr.value == "...":
          walk p
        let param = Node(kind: nkIdent, name: p.curr.value)
        walk p
        # default value
        if p.curr.kind == tkPunct and p.curr.value == "=":
          walk p
          params.children.add(Node(kind: nkIdentDefs,
            children: @[param, parseExpression(p)]))
        else:
          params.children.add(param)
      else:
        # no type hint, just $param
        if p.curr.kind == tkPunct and p.curr.value == "&":
          walk p
        if p.curr.kind == tkPunct and p.curr.value == "...":
          walk p
        params.children.add(Node(kind: nkIdent, name: p.curr.value))
        walk p
        if p.curr.kind == tkPunct and p.curr.value == "=":
          walk p
          let idx = params.children.len - 1
          let defaultVal = parseExpression(p)
          let paramNode = params.children[idx]
          params.children[idx] = Node(kind: nkIdentDefs,
            children: @[paramNode, defaultVal])
      p.walkOpt(",")
    p.expectWalk(")")
    # optional return type: ): Type
    if p.curr.kind == tkPunct and p.curr.value == ":":
      walk p
      # consume return type identifier (possibly nullable ?Type)
      if p.curr.kind == tkPunct and p.curr.value == "?":
        walk p
      walk p # consume type name
    result.children.add(params)
    # body: { block } for regular functions, ; for interface/abstract methods
    if p.curr.kind == tkPunct and p.curr.value == p.blockOpen:
      result.children.add(parseBlock(p))
    else:
      result.children.add(Node(kind: nkEmpty))
      p.expectWalk(";")

  stmtHandler p, "throw":
    walk p # consume 'throw'
    result = Node(kind: nkReturn) # reuse nkReturn or a dedicated nkThrow
    result.children.add(parseExpression(p))
    p.expectWalk(";")

  stmtHandler p, "break":
    walk p # consume 'break'
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "break")])
    # optional level: break 2;
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
    # catch blocks
    while p.curr.kind == tkIdentifier and p.curr.value == "catch":
      walk p # consume 'catch'
      p.expectWalk("(")
      let catchBlock = Node(kind: nkStatement)
      catchBlock.children.add(Node(kind: nkIdent, name: "catch"))
      # exception type(s): Type1 | Type2
      let types = Node(kind: nkStatement)
      types.children.add(Node(kind: nkIdent, name: p.curr.value))
      walk p
      while p.curr.kind == tkPunct and p.curr.value == "|":
        walk p
        types.children.add(Node(kind: nkIdent, name: p.curr.value))
        walk p
      catchBlock.children.add(types)
      # variable
      if p.curr.kind == tkIdentifier and p.curr.value[0] == '$':
        catchBlock.children.add(Node(kind: nkIdent, name: p.curr.value))
        walk p
      p.expectWalk(")")
      catchBlock.children.add(parseBlock(p))
      result.children.add(catchBlock)
    # finally
    if p.curr.kind == tkIdentifier and p.curr.value == "finally":
      walk p
      result.children.add(Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "finally"), parseBlock(p)]))

  stmtHandler p, "switch":
    ## switch (expr) { case val: ... break; default: ... }
    walk p # consume 'switch'
    p.expectWalk("(")
    let cond = parseExpression(p)
    p.expectWalk(")")
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "switch"), cond])
    p.expectWalk("{")
    while not (p.curr.kind == tkPunct and p.curr.value == "}"):
      if p.curr.kind == tkEOF: error(p, "Unexpected EOF in switch")
      if p.curr.kind == tkIdentifier and p.curr.value == "case":
        walk p
        let caseExpr = parseExpression(p)
        p.expectWalk(":")
        let caseBody = Node(kind: nkBlock)
        while not (p.curr.kind == tkIdentifier and
                    p.curr.value in ["case", "default"]) and
              not (p.curr.kind == tkPunct and p.curr.value == "}"):
          if p.curr.kind == tkEOF: error(p, "Unexpected EOF in case")
          caseBody.children.add(parseStatement(p))
        result.children.add(Node(kind: nkStatement,
          children: @[Node(kind: nkIdent, name: "case"), caseExpr, caseBody]))
      elif p.curr.kind == tkIdentifier and p.curr.value == "default":
        walk p
        p.expectWalk(":")
        let defaultBody = Node(kind: nkBlock)
        while not (p.curr.kind == tkPunct and p.curr.value == "}"):
          if p.curr.kind == tkEOF: error(p, "Unexpected EOF in default")
          defaultBody.children.add(parseStatement(p))
        result.children.add(Node(kind: nkStatement,
          children: @[Node(kind: nkIdent, name: "default"), defaultBody]))
      else:
        error(p, "Expected 'case' or 'default' in switch")
    p.expectWalk("}")

  stmtHandler p, "class":
    ## [abstract|final] class Name [extends Parent] [implements I1, I2] { }
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "class"))
    walk p # consume 'class'
    let className = Node(kind: nkIdent, name: p.curr.value)
    result.children.add(className)
    walk p
    # extends
    if p.curr.kind == tkIdentifier and p.curr.value == "extends":
      walk p
      result.children.add(Node(kind: nkIdent, name: p.curr.value))
      walk p
    # implements
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
    result.children.add(parseBlock(p))

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
    result.children.add(parseBlock(p))

  stmtHandler p, "trait":
    ## trait Name { }
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "trait"))
    walk p
    result.children.add(Node(kind: nkIdent, name: p.curr.value))
    walk p
    result.children.add(parseBlock(p))

  stmtHandler p, "enum":
    ## enum Name [: backed_type] { case Foo; case Bar = 1; }
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "enum"))
    walk p
    result.children.add(Node(kind: nkIdent, name: p.curr.value))
    walk p
    # backed enum: enum Foo: string { }
    if p.curr.kind == tkPunct and p.curr.value == ":":
      walk p
      result.children.add(Node(kind: nkIdent, name: p.curr.value))
      walk p
    result.children.add(parseBlock(p))

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
    ## use Namespace\Sub;  or  use function ...;  or  use const ...;
    ## also: use Trait { Trait::method as alias; }
    walk p # consume 'use'
    # use Trait { ... } — trait conflict resolution
    if p.curr.kind == tkPunct and p.curr.value == "{":
      result = Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "use")])
      result.children.add(parseBlock(p))
      p.expectWalk(";")
      return
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "use"))
    # optional modifier: function, const
    if p.curr.kind == tkIdentifier and p.curr.value in ["function", "const"]:
      result.children.add(Node(kind: nkIdent, name: p.curr.value))
      walk p
    # namespace path: Foo\Bar\Baz
    var nsPath = p.curr.value
    walk p
    while p.curr.kind == tkPunct and p.curr.value == "\\":
      walk p
      nsPath &= "\\" & p.curr.value
      walk p
    result.children.add(Node(kind: nkIdent, name: nsPath))
    # optional: as Alias
    if p.curr.kind == tkIdentifier and p.curr.value == "as":
      walk p
      result.children.add(Node(kind: nkIdent, name: p.curr.value))
      walk p
    p.expectWalk(";")

try:
  parseScript("./sample.php", phpHandlers,
      features = {featArrowFn, featGenerators}
  )
except OpenAstParsingError as e:
  echo e.msg