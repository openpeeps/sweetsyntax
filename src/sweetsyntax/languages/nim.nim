# A powerful generic parser and AST explorer for analyzing
# programming languages!
#
# (c) 2026 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

import std/[tables, strutils, options, sets]
import ../[config, sweetlexer, tokenizer]
import ../engine/[ast, parser]

template expectIdent(body: untyped) {.dirty.} =
  if p.curr.kind == tkIdentifier:
    body
  else:
    error(p, "Expected identifier")

template expectIdentOrLit(body: untyped) {.dirty.} =
  if p.curr.kind in {tkIdentifier, tkString}:
    body
  else:
    error(p, "Expected identifier or string literal")

template expectString(body: untyped) {.dirty.} =
  if p.curr.kind == tkString:
    body
  else:
    error(p, "Expected string literal")

template isPragmaOpen: bool {.dirty.} =
  ## The lexer emits Nim's pragma opener as a single `{.` token
  ## (see `pragmaOpen` in nim.yaml), not `{` + `.`.
  p.curr.kind == tkPunct and p.curr.value == "{."

proc parseNimPragma(p: var GenericParser): Node =
  ## Parse a Nim pragma starting after `{.` is consumed.
  ## Supports {.abc.}, {.abc, efg.}, {.deprecated: [TFile: File].}
  ## Module-level (not nested in `nimHandlers`) so declaration helpers
  ## defined earlier in the file can call it.
  result = Node(kind: nkStatement)
  result.children.add(Node(kind: nkIdent, name: "pragma"))
  if p.curr.kind == tkPunct and p.curr.value == ".":
    walk p
  while not (p.curr.kind == tkPunct and p.curr.value == "}"):
    if p.curr.kind == tkEOF: error(p, "Unexpected EOF in pragma")
    if p.curr.kind in {tkComment, tkDocComment}:
      discard parseCommentGeneric(p); continue
    if p.curr.kind == tkIdentifier:
      let identTk = p.curr
      let identVal = identTk.value
      walk p
      if p.curr.kind == tkPunct and p.curr.value == ":":
        walk p
        result.children.add(Node(kind: nkColonExpr,
          children: @[Node(kind: nkIdent, name: identVal).stamp(identTk),
                       parseExpression(p, 15)]).stamp(identTk))
      else:
        result.children.add(Node(kind: nkIdent, name: identVal).stamp(identTk))
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
  # Anchor the pragma node and its keyword at the first entry, if any;
  # callers may re-stamp the root when they hold the `{.` token.
  if result.children.len > 1:
    result.children[0].stampFrom(result.children[1])
    result.stampFrom(result.children[1])

proc closeNimBlock(blk: Node) =
  ## Anchor a synthetic `nkBlock` at its first child when non-empty,
  ## so generated blocks never sit at 0:0.
  if blk.children.len > 0:
    blk.stampFrom(blk.children[0])

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
      result.children.add(Node(kind: nkLitString, valStr: p.curr.value).stamp(p.curr))
      walk p
    elif p.curr.kind == tkIdentifier:
      result.children.add(Node(kind: nkIdent, name: p.curr.value).stamp(p.curr))
      walk p
    elif p.curr.kind == tkPunct and p.curr.value == "/":
      result.children.add(Node(kind: nkIdent, name: "/").stamp(p.curr))
      walk p
    elif p.curr.kind == tkPunct and p.curr.value in [".", ".."]:
      result.children.add(Node(kind: nkIdent, name: p.curr.value).stamp(p.curr))
      walk p
    elif p.curr.kind == tkPunct and p.curr.value == ",":
      walk p # TODO check for indentation
    elif p.curr.kind == tkPunct and p.curr.value == "[":
      # Submodule bracket group: [mod1/sub, mod2]
      walk p
      while not (p.curr.kind == tkPunct and p.curr.value == "]"):
        if p.curr.kind == tkEOF: error(p, "Unexpected EOF in import bracket group")
        if p.curr.kind in {tkComment, tkDocComment}:
          discard parseCommentGeneric(p)
          continue
        if p.curr.kind == tkIdentifier:
          result.children.add(Node(kind: nkIdent, name: p.curr.value).stamp(p.curr))
          walk p
        elif p.curr.kind == tkPunct and p.curr.value in [",", "/", ".", ".."]:
          result.children.add(Node(kind: nkIdent, name: p.curr.value).stamp(p.curr))
          walk p
        else:
          error(p, "Expected identifier, '/', or ',' in import bracket group")
      result.children.add(Node(kind: nkIdent, name: "]").stamp(p.curr))
      p.expectWalk("]")
      break
    else:
      break
  if result.children.len > 0:
    result.stampFrom(result.children[0])

proc nimHandlers*(p: var GenericParser) =
  # Register Nim-specific statement handlers.
  p.stmtKeywords["type"] = "type_handler"
  # `static` needs its own handler (block vs declaration disambiguation);
  # the YAML maps it to `declarator` as a fallback.
  p.stmtKeywords["static"] = "static"
  p.keywordPrefixOps.incl("ref")
  p.keywordPrefixOps.incl("ptr")

  prefixHandler p, "$":
    ## `$` string conversion operator: `$expr` converts to string
    let dollarTk = p.curr
    walk p # consume '$'
    let operand = parseExpression(p, 13) # bind tighter than binary ops
    result = Node(kind: nkPrefix,
      children: @[Node(kind: nkIdent, name: "$").stamp(dollarTk), operand]).stamp(dollarTk)

  prefixHandler p, "&":
    ## `&"..."` string interpolation: `&` directly before a string literal.
    ## (A `&` between expressions is the infix concat operator instead,
    ## which the Pratt loop handles — this only fires in operand position.)
    let ampTk = p.curr
    walk p # consume '&'
    if p.curr.kind != tkString:
      error(p, "Expected string literal after '&'")
    result = Node(kind: nkPrefix,
      children: @[Node(kind: nkIdent, name: "&").stamp(ampTk),
                  Node(kind: nkLitString, valStr: p.curr.value).stamp(p.curr)]).stamp(ampTk)
    walk p

  prefixHandler p, "%":
    ## `%expr` JSON conversion operator (`%x`, `%*{"a": 1}`).
    ## (Between expressions `%` is infix modulo — handled by the Pratt loop.)
    let pctTk = p.curr
    walk p # consume '%'
    let operand = parseExpression(p, 13) # bind tighter than binary ops
    result = Node(kind: nkPrefix,
      children: @[Node(kind: nkIdent, name: "%").stamp(pctTk), operand]).stamp(pctTk)

  prefixHandler p, "{.":
    ## Top-level (or expression-position) pragma: {.experimental: "x".}.
    ## The lexer emits `{.` as one token, so the brace handler never sees it.
    let pragmaTk = p.curr
    walk p # consume '{.'
    result = parseNimPragma(p).stamp(pragmaTk)

  proc parseNimType(p: var GenericParser): Node =
    ## A type annotation: optional `var`/`lent`/`sink`/`out`/`static`
    ## modifier plus the type. Uses minPrec 2 so `=` stays outside the
    ## type (`x: T = v` splits into type + default) and command syntax
    ## cannot trigger. A bare `static[int]` keeps its bracket shape (the
    ## modifier requires a plain identifier after it).
    var modifier = ""
    if p.curr.kind == tkIdentifier and
       p.curr.value in ["var", "lent", "sink", "out", "static"] and
       p.next.kind == tkIdentifier:
      modifier = p.curr.value
      walk p
    result = parseExpression(p, 2)
    if modifier.len > 0:
      result = Node(kind: nkVarTy, children: @[result]).stampFrom(result)

  proc parseNimVarDef(p: var GenericParser, stmt: Node, kwCol: int) =
    ## Parse one `name[*], ... [: Type] [= value]` definition (or an
    ## `(a, b) = value` destructuring) and append it to `stmt`.
    ## Commas before any `:`/`=` join names sharing the definition
    ## (`a, b: int`, `a, b = v`); a comma after the value starts a new
    ## definition and is left for the caller. Stops before `,`/`;`/dedent.
    if p.curr.kind == tkPunct and p.curr.value == "(":
      # Tuple destructuring: let (a, b) = expr
      let pattern = parseExpression(p)
      stmt.children.add(pattern)
      if p.curr.kind == tkPunct and p.curr.value == "=":
        let eqLine = p.curr.line
        walk p
        if p.curr.line != eqLine and p.curr.col <= kwCol:
          error(p, "Expected expression after '='")
        stmt.children.add(parseExpression(p))
      else:
        stmt.children.add(ast.newEmptyNode())
      return
    let varDef = Node(kind: nkIdentDefs)
    while true:
      expectIdent:
        discard
      var fieldName = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
      walk p
      # Nim export marker `*` after name (e.g., `invalidFilenameChars*`)
      if p.curr.kind == tkPunct and p.curr.value == "*":
        fieldName = Node(kind: nkPostfix,
          children: @[fieldName, Node(kind: nkIdent, name: "*").stamp(p.curr)]).stampFrom(fieldName)
        walk p
      # Pragma on the name: `x {.guard.} [: T] [= v]`
      while isPragmaOpen:
        walk p
        stmt.children.add(parseNimPragma(p))
      varDef.children.add(fieldName)
      if p.curr.kind == tkPunct and p.curr.value == ",":
        walk p
        continue
      break
    # optional type annotation shared by all names: `: Type`
    if p.curr.kind == tkPunct and p.curr.value == ":":
      walk p
      varDef.children.add(parseNimType(p))
    else:
      varDef.children.add(ast.newEmptyNode())
    # optional default value shared by all names: `= expr`
    if p.curr.kind == tkPunct and p.curr.value == "=":
      let eqLine = p.curr.line
      walk p
      if p.curr.line != eqLine and p.curr.col <= kwCol:
        error(p, "Expected expression after '='")
      varDef.children.add(parseExpression(p))
    else:
      varDef.children.add(ast.newEmptyNode())
    varDef.stampFrom(varDef.children[0])
    stmt.children.add(varDef)

  proc parseNimDeclarator(p: var GenericParser, kw: string, kwTk: TokenTuple): Node =
    ## `let`/`const`/`var`/`static` declarations: either a single-line
    ## comma-separated list or an indented section of one definition
    ## per line (`var` newline `  x = 1` newline `  y: int`).
    let kwCol = kwTk.col
    result = Node(kind: nkStatement).stamp(kwTk)
    result.children.add(Node(kind: nkIdent, name: kw).stamp(kwTk))
    while p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p))
    if p.curr.kind != tkEOF and p.curr.line > kwTk.line and p.curr.col > kwCol:
      # Section mode: one definition per line while indented past `kw`.
      while p.curr.kind != tkEOF and p.curr.col > kwCol:
        if p.curr.kind in {tkComment, tkDocComment}:
          result.children.add(parseCommentGeneric(p))
          continue
        parseNimVarDef(p, result, kwCol)
        if p.curr.kind == tkPunct and p.curr.value == ",":
          walk p
          continue
        # A `;` ends the section; anything else dedents out via the
        # column check above.
        p.walkOpt(";")
    else:
      # Single-line mode: comma-separated definitions.
      while true:
        parseNimVarDef(p, result, kwCol)
        if p.curr.kind == tkPunct and p.curr.value == ",":
          walk p
        else: break
    p.walkOpt(";")
    p.walkOpt(";")

  proc parseNimRoutineParams(p: var GenericParser): Node =
    ## `(name, name2: Type = default; ...)`: routine parameter list shared
    ## by proc/func/method/iterator/converter/template/macro/do. Handles
    ## `var`/`lent`/`sink`/`out`/`static` modifiers (wrapped in `nkVarTy`),
    ## comma-separated names sharing a type, defaults, and `,`/`;`
    ## separators. A lone name without type/default stays a bare `nkIdent`.
    result = Node(kind: nkIdentDefs)
    if p.curr.kind != tkPunct or p.curr.value != "(":
      # No parameter list (`proc name = body`): anchor at the last token
      # (usually the name) so the placeholder is not left at 0:0.
      result.stamp(p.prev)
      return
    let openTk = p.curr
    result.stamp(openTk)
    walk p # consume '('
    while not (p.curr.kind == tkPunct and p.curr.value == ")"):
      if p.curr.kind == tkEOF: error(p, "Unexpected EOF in params")
      if p.curr.kind in {tkComment, tkDocComment}:
        discard parseCommentGeneric(p)
        continue
      # one or more names sharing the type/default
      var names: seq[Node]
      while true:
        expectIdent:
          discard
        names.add(Node(kind: nkIdent, name: p.curr.value).stamp(p.curr))
        walk p
        if p.curr.kind == tkPunct and p.curr.value == ",":
          walk p
          continue
        break
      var typeNode = Node(kind: nkEmpty)
      if p.curr.kind == tkPunct and p.curr.value == ":":
        walk p
        typeNode = parseNimType(p)
      var defaultVal = Node(kind: nkEmpty)
      if p.curr.kind == tkPunct and p.curr.value == "=":
        walk p
        defaultVal = parseExpression(p)
      if names.len == 1 and typeNode.kind == nkEmpty and
         defaultVal.kind == nkEmpty:
        result.children.add(names[0])
      else:
        result.children.add(Node(kind: nkIdentDefs,
          children: names & @[typeNode, defaultVal]).stampFrom(names[0]))
      p.walkOpt(",")
      p.walkOpt(";")
    p.expectWalk(")")

  proc parseNimGenerics(p: var GenericParser): Node =
    ## `[T, U: Constraint = Default]`: generic parameter list. Returns nil
    ## when there is no `[`. Constrained params become `nkIdentDefs`.
    result = nil
    if p.curr.kind != tkPunct or p.curr.value != "[":
      return
    result = Node(kind: nkBracketExpr).stamp(p.curr)
    walk p # consume '['
    while not (p.curr.kind == tkPunct and p.curr.value == "]"):
      if p.curr.kind == tkEOF: error(p, "Unexpected EOF in generic params")
      if p.curr.kind in {tkComment, tkDocComment}:
        discard parseCommentGeneric(p)
        continue
      expectIdent:
        discard
      let name = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
      walk p
      var typeNode = Node(kind: nkEmpty)
      if p.curr.kind == tkPunct and p.curr.value == ":":
        walk p
        typeNode = parseNimType(p)
      var defaultVal = Node(kind: nkEmpty)
      if p.curr.kind == tkPunct and p.curr.value == "=":
        walk p
        defaultVal = parseExpression(p)
      if typeNode.kind == nkEmpty and defaultVal.kind == nkEmpty:
        result.children.add(name)
      else:
        result.children.add(Node(kind: nkIdentDefs,
          children: @[name, typeNode, defaultVal]).stampFrom(name))
      p.walkOpt(",")
    p.expectWalk("]")

  stmtHandler p, "declarator":
    ## let/const/var name [= expr], name2 [= expr], ...
    ## Also handles sections, shared names/types, destructuring, pragmas.
    let kwTk = p.curr
    let kw = kwTk.value
    walk p
    result = parseNimDeclarator(p, kw, kwTk)

  stmtHandler p, "return":
    walk p # consume 'return'
    let retTk = p.prev
    result = Node(kind: nkReturn).stamp(retTk)
    if (p.curr.kind == tkPunct and p.curr.value in [";", "}"]) or
       p.curr.kind == tkEOF:
      p.walkOpt(";")
      return
    while p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p))
    if p.curr.kind == tkIdentifier and p.curr.value in ["of", "else", "elif"]:
      p.walkOpt(";")
      return
    # Bare `return`: the next statement starts on a later line at the
    # same or lower indentation (an indented later line is a continuation).
    if p.curr.line != retTk.line and p.curr.col <= retTk.col:
      p.walkOpt(";")
      return
    result.children.add(parseExpression(p))
    p.walkOpt(";")

  stmtHandler p, "conditional":
    ## if cond: body  elif cond: body  else: body
    ## Supports both `if cond:` (Nim) and `if (cond)` (brace-style)
    let ifTk = p.curr
    walk p # consume 'if'/'when'
    let ifCol = ifTk.col
    let condCol = ifCol
    var children: seq[Node]
    # A leading `(` is just a parenthesized condition: parseGroupExpr runs
    # inside parseExpression, so infix operators after `)` (`(a) != 0`,
    # `(a) or b`) continue naturally through the Pratt loop.
    children.add(parseExpression(p, 1))
    let colonLine = p.curr.line
    children.add(
      if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
      elif p.curr.kind == tkPunct and p.curr.value == ":":
        walk p
        if p.curr.line == colonLine: parseStatement(p)
        else: parseBlock(p, condCol)
      else: parseStatement(p))
    # Continuation keywords must align with (or indent past) this `if`:
    # a dedented `else`/`elif` belongs to an outer statement, and `of`
    # never belongs to `if` (it belongs to an enclosing `case`).
    while p.curr.kind == tkIdentifier and p.curr.value in ["elif", "else"] and
        p.curr.col >= ifCol:
      let isElif = p.curr.value == "elif"
      walk p
      if isElif:
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
      if p.curr.kind != tkIdentifier or p.curr.value notin ["elif", "else"]:
        break
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "if").stamp(ifTk)] & children).stamp(ifTk)

  stmtHandler p, "loop":
    ## while cond: body
    ## Supports both `while cond:` (Nim) and `while (cond)` (brace-style)
    let whileTk = p.curr
    walk p # consume 'while'
    let whileCol = whileTk.col
    let cond = if p.curr.kind == tkPunct and p.curr.value == "(":
                 walk p; let c = parseExpression(p); p.expectWalk(")"); c
               else:
                 # minPrec 1 keeps command syntax out of the condition so a
                 # trailing `:` still introduces the loop body (`while x:`).
                 parseExpression(p, 1)
    let body = if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
               elif p.curr.kind == tkPunct and p.curr.value == ":":
                 walk p; parseBlock(p, whileCol)
               else: parseStatement(p)
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "while").stamp(whileTk), cond, body]).stamp(whileTk)

  stmtHandler p, "for_loop":
    ## for i in 0 ..< 10: body
    ## Supports both `for i in iterable:` (Nim) and `for (i in iterable)` (brace-style)
    let forTk = p.curr
    walk p # consume 'for'
    let forCol = forTk.col
    let hasParens = p.curr.kind == tkPunct and p.curr.value == "("
    if hasParens: walk p
    # left-hand side of `in`: variable(s)
    var vars = Node(kind: nkIdentDefs)
    expectIdent:
      vars.children.add(Node(kind: nkIdent, name: p.curr.value).stamp(p.curr))
    vars.stampFrom(vars.children[0])
    walk p
    while p.curr.kind == tkPunct and p.curr.value == ",":
      walk p
      expectIdent:
        vars.children.add(Node(kind: nkIdent, name: p.curr.value).stamp(p.curr))
      walk p
    # `in` keyword
    if p.curr.kind == tkIdentifier and p.curr.value == "in":
      walk p
    else:
      error(p, "Expected 'in' in for loop")
    # right-hand side: range / iterable expression (minPrec 1 keeps a
    # trailing `:` for the loop body: `for i in x:`)
    let iterable = parseExpression(p, 1)
    if hasParens:
      p.expectWalk(")")
    let body = if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
               elif p.curr.kind == tkPunct and p.curr.value == ":":
                 walk p; parseBlock(p, forCol)
               else: parseStatement(p)
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "for").stamp(forTk), vars, iterable, body]).stamp(forTk)

  stmtHandler p, "case":
    ## case expr
    ##   of pat1, pat2: body
    ##   of pat3: body
    ##   else: body
    ## In brace mode: case (expr) { of (pat1) { body } else { body } }
    let caseTk = p.curr
    walk p # consume 'case'
    let scrutinee = parseExpression(p, 6)
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "case").stamp(caseTk), scrutinee]).stamp(caseTk)
    if p.curr.kind == tkPunct and p.curr.value == "{":
      # Brace mode: case expr { of pat { body } else { body } }
      walk p
      while not (p.curr.kind == tkPunct and p.curr.value == "}"):
        if p.curr.kind == tkEOF: error(p, "Unexpected EOF in case")
        if p.curr.kind == tkIdentifier and p.curr.value == "of":
          let ofTk = p.curr
          walk p
          let pattern = Node(kind: nkStatement).stamp(ofTk)
          pattern.children.add(Node(kind: nkIdent, name: "of").stamp(ofTk))
          pattern.children.add(parseExpression(p, 6))
          while p.curr.kind == tkPunct and p.curr.value == ",":
            walk p
            pattern.children.add(parseExpression(p, 6))
          p.expectWalk(":")
          pattern.children.add(
            if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
            else: parseStatement(p))
          result.children.add(pattern)
        elif p.curr.kind == tkIdentifier and p.curr.value == "else":
          let elseTk = p.curr
          walk p
          p.expectWalk(":")
          let elseBranch = Node(kind: nkStatement).stamp(elseTk)
          elseBranch.children.add(Node(kind: nkIdent, name: "else").stamp(elseTk))
          elseBranch.children.add(
            if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
            else: parseStatement(p))
          result.children.add(elseBranch)
        else:
          error(p, "Expected 'of' or 'else' in case")
      p.expectWalk("}")

    else:
      # Indent mode: case expr\n of pat: body\n of pat: body\n else: body
      # The first branch sets the anchor: later `of`/`else` keywords must
      # align with (or indent past) it, otherwise they belong to an outer
      # `case` (this `case` may sit nested in its branch body). The first
      # branch is always accepted so a mid-line `result = case ...` keeps
      # working with dedented branches.
      if p.curr.kind == tkPunct and p.curr.value == ":":
        walk p
      var branchCol = -1
      while p.curr.kind == tkIdentifier and p.curr.value in ["of", "else"] and
          (branchCol < 0 or p.curr.col >= branchCol):
        if branchCol < 0:
          branchCol = p.curr.col
        let isOf = p.curr.value == "of"
        let branchTk = p.curr
        let bodyCol = branchTk.col
        walk p
        if isOf:
          let pattern = Node(kind: nkStatement).stamp(branchTk)
          pattern.children.add(Node(kind: nkIdent, name: "of").stamp(branchTk))
          pattern.children.add(parseExpression(p, 6))
          while p.curr.kind == tkPunct and p.curr.value == ",":
            walk p
            pattern.children.add(parseExpression(p, 6))
          if p.curr.kind == tkPunct and p.curr.value == ":":
            walk p
          var savedOf: Option[InfixEntry]
          var savedElse: Option[InfixEntry]
          if p.infixTable.hasKey("of"):
            savedOf = some(p.infixTable["of"])
            p.infixTable.del("of")
          if p.infixTable.hasKey("else"):
            savedElse = some(p.infixTable["else"])
            p.infixTable.del("else")
          var body = Node(kind: nkBlock)
          while p.curr.kind != tkEOF and p.curr.col > bodyCol:
            if p.curr.kind in {tkComment, tkDocComment}:
              body.children.add(parseCommentGeneric(p))
              continue
            body.children.add(parseStatement(p))
          if savedOf.isSome: p.infixTable["of"] = savedOf.get
          if savedElse.isSome: p.infixTable["else"] = savedElse.get
          if body.children.len > 0:
            body.stampFrom(body.children[0])
          else:
            body.stamp(branchTk)
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
          while p.curr.kind != tkEOF and p.curr.col > bodyCol:
            if p.curr.kind in {tkComment, tkDocComment}:
              body.children.add(parseCommentGeneric(p))
              continue
            body.children.add(parseStatement(p))
          if savedOf2.isSome: p.infixTable["of"] = savedOf2.get
          if savedElse2.isSome: p.infixTable["else"] = savedElse2.get
          if body.children.len > 0:
            body.stampFrom(body.children[0])
          else:
            body.stamp(branchTk)
          let elseBranch = Node(kind: nkStatement).stamp(branchTk)
          elseBranch.children.add(Node(kind: nkIdent, name: "else").stamp(branchTk))
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
    let tryTk = p.curr
    result = Node(kind: nkStatement).stamp(tryTk)
    result.children.add(Node(kind: nkIdent, name: "try").stamp(tryTk))
    walk p # consume 'try'
    let tryCol = tryTk.col
    result.children.add(parseTryBody(p, tryCol))
    # except blocks (Nim uses `except`, not `catch`).
    # Continuations must align with (or indent past) this `try`.
    while p.curr.kind == tkIdentifier and p.curr.value == "except" and
        p.curr.col >= tryCol:
      let exceptTk = p.curr
      walk p
      let exceptBlock = Node(kind: nkStatement).stamp(exceptTk)
      exceptBlock.children.add(Node(kind: nkIdent, name: "except").stamp(exceptTk))
      # optional exception type(s) and `as variable` (a type position:
      # minPrec 2 keeps `=` and command syntax out, so a trailing `:`
      # still introduces the handler body: `except IOError:`)
      if p.curr.kind != tkPunct or p.curr.value notin [":", "{"]:
        exceptBlock.children.add(parseNimType(p))
        # handle `as variableName` after exception type
        if p.curr.kind == tkIdentifier and p.curr.value == "as":
          walk p
          expectIdent:
            exceptBlock.children.add(Node(kind: nkIdent, name: p.curr.value).stamp(p.curr))
          walk p
      exceptBlock.children.add(parseTryBody(p, tryCol))
      result.children.add(exceptBlock)
    # finally
    if p.curr.kind == tkIdentifier and p.curr.value == "finally" and
        p.curr.col >= tryCol:
      let finallyTk = p.curr
      walk p
      result.children.add(Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "finally").stamp(finallyTk),
                    parseTryBody(p, tryCol)]).stamp(finallyTk))

  stmtHandler p, "block":
    ## block label: body  or  block: body
    ## In brace mode: block (label) { body }  or  block { body }
    let blockTk = p.curr
    walk p # consume 'block'
    let labelNode =
      if p.curr.kind == tkPunct and p.curr.value == "(":
        walk p
        expectIdent:
          discard
        let lbl = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
        walk p
        p.expectWalk(")")
        lbl
      elif p.curr.kind == tkIdentifier:
        let lbl = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
        walk p
        lbl
      else:
        Node(kind: nkEmpty)
    let blockCol = p.prev.col
    let body =
      if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
      elif p.curr.kind == tkPunct and p.curr.value == ":":
        walk p; parseBlock(p, blockCol)
      else: parseBlock(p, blockCol)
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "block").stamp(blockTk), labelNode, body]).stamp(blockTk)

  stmtHandler p, "import":
    ## import module/path, module2/path
    ## import module/[sub1, sub2]
    let importTk = p.curr
    walk p # consume 'import'
    result = Node(kind: nkImport).stamp(importTk)
    while true:
      result.children.add(parseImportPath(p))
      if p.curr.kind == tkPunct and p.curr.value == ",":
        walk p
      else:
        break
    p.walkOpt(";")

  stmtHandler p, "from":
    ## from module/path import name1, name2
    let fromTk = p.curr
    walk p # consume 'from'
    result = Node(kind: nkStatement).stamp(fromTk)
    result.children.add(Node(kind: nkIdent, name: "from").stamp(fromTk))
    result.children.add(parseImportPath(p))
    if p.curr.kind == tkIdentifier and p.curr.value == "import":
      let importTk = p.curr
      walk p
      let imports = Node(kind: nkIdentDefs).stamp(importTk)
      imports.children.add(parseImportPath(p))
      while p.curr.kind == tkPunct and p.curr.value == ",":
        walk p
        imports.children.add(parseImportPath(p))
      result.children.add(imports)
    p.walkOpt(";")

  proc parseNimBrace(p: var GenericParser, minPrec: int = 0): Node =
    let braceTk = p.curr
    walk p # consume '{'
    if p.curr.kind == tkPunct and p.curr.value == ".":
      return parseNimPragma(p)
    result = Node(kind: nkBlock).stamp(braceTk)
    while not (p.curr.kind == tkPunct and p.curr.value == "}"):
      if p.curr.kind == tkEOF: error(p, "Unexpected EOF in brace expr")
      if p.curr.kind in {tkComment, tkDocComment}:
        discard parseCommentGeneric(p); continue
      let item = parseExpression(p)
      # Table constructor entry: `{key: value, ...}`
      if p.curr.kind == tkPunct and p.curr.value == ":":
        walk p
        result.children.add(Node(kind: nkColonExpr,
          children: @[item, parseExpression(p)]).stampFrom(item))
      else:
        result.children.add(item)
      p.walkOpt(",")
    p.expectWalk("}")

  # Command call: `callee arg1, arg2: body` (first arg on same line).
  # Shared by `afterPrefix` (plain-identifier callees) and the `infix`
  # hook (field-access / call-result callees, which only exist after the
  # Pratt loop: `obj.m arg`, `f(x) do: ...`).
  # Exclude infix operators as command names (e.g., `of`/`else`).
  # Exclude block continuations (`else`, `elif`, `except`, `finally`) as
  # arguments — otherwise `if c: x else: y` parses `else:` into the call.
  # A `:` starts a command block only at end-of-line (`foo:` + indented
  # block); a same-line `:` is a type/symbol annotation (`x: int`).
  proc parseNimCommand(p: var GenericParser, callee: Node): Node =
    let cmdLine = p.prev.line
    let cmdCol = callee.col
    var args: seq[Node] = @[callee]
    while p.curr.kind notin {tkEOF}:
      if p.curr.kind in {tkComment, tkDocComment}:
        args.add(parseCommentGeneric(p)); continue
      if p.curr.kind == tkPunct and p.curr.value == ":":
        let colonLine = p.curr.line
        walk p
        let body = if p.curr.kind == tkPunct and p.curr.value == p.blockOpen:
                     parseBlock(p)
                   elif p.curr.line != colonLine:
                     parseBlock(p, cmdCol)
                   else:
                     parseExpression(p, 0)
        args.add(body)
        break
      if p.curr.kind == tkPunct and p.curr.value in [")", "]", "}", ";"]:
        break
      if p.curr.kind == tkPunct and p.curr.value == ",":
        walk p; continue
      # Arguments on following lines must indent past the command;
      # a dedented token starts a new statement.
      if p.curr.line != cmdLine and p.curr.col <= cmdCol:
        break
      if p.curr.kind == tkIdentifier and
         p.curr.value in ["else", "elif", "except", "finally"]:
        break
      args.add(parseExpression(p, 0))
    Node(kind: nkCall, children: args).stampFrom(callee)

  template commandEntryOpen(allowEolColon: bool): bool {.dirty.} =
    ## True when `p.curr` can start a command argument list. A leading `:`
    ## is only a command block at end-of-line (`foo:` + indented block); a
    ## same-line `:` is a type/symbol annotation (`x: int`). End-of-line
    ## `:` is only allowed at minPrec 0 — deeper levels use `:` for bodies
    ## and type slots (`while x:`, `x: T`), which must keep working.
    p.curr.kind notin {tkEOF, tkComment, tkDocComment} and
    p.curr.line == p.prev.line and
    not (p.curr.kind == tkPunct and p.curr.value != ":") and
    (allowEolColon or
     not (p.curr.kind == tkPunct and p.curr.value == ":")) and
    not (p.curr.kind == tkPunct and p.curr.value == ":" and
         p.next.line == p.curr.line) and
    not (p.curr.kind == tkIdentifier and
         (p.infixTable.hasKey(p.curr.value) or
          (p.stmtKeywords.hasKey(p.curr.value) and
           p.curr.value != "do") or
          p.curr.value in ["else", "elif", "except", "finally"]))

  # Expression handlers
  exprHandler p, "afterPrefix":
    ## Nim export marker `*` after identifiers, and command call syntax.
    ## (Numeric type suffixes like `0b1010'u8` lex as one token — the
    ## lexer consumes the suffix and the engine strips it for the value.)
    if lhs.kind != nkIdent:
      return nil
    # Export marker: `name*` (not followed by expression start).
    if p.curr.kind == tkPunct and p.curr.value == "*" and
       p.next.kind notin {tkIdentifier, tkInt, tkFloat, tkString, tkHex, tkOctal, tkBinary, tkBigInt} and
       not (p.next.kind == tkPunct and p.next.value in ["(", "[", "{", "+", "-", "~", "!", "@", "^", "?"]):
      result = Node(kind: nkPostfix,
        children: @[lhs, Node(kind: nkIdent, name: "*")])
      walk p
      return
    # Commands nest inside infix right-hand sides (`a + b c` is
    # `a + (b c)`): allow entry above minPrec 0, but without a leading
    # end-of-line `:` (reserved for bodies and type slots there).
    if commandEntryOpen(minPrec == 0) and
       not p.infixTable.hasKey(lhs.name):
      return parseNimCommand(p, lhs)
    return nil

  exprHandler p, "infix":
    ## Command calls on field accesses and call results (`obj.m arg`,
    ## `f(x) do: ...`): the Pratt loop stops before the arguments
    ## (`afterPrefix` only sees pre-infix nodes), so continue here.
    if lhs.kind in {nkDotExpr, nkCall} and
       commandEntryOpen(minPrec == 0):
      return parseNimCommand(p, lhs)
    return nil

  p.braceHandler = parseNimBrace

  stmtHandler p, "function":
    ## proc/func/method/iterator/converter name(params): returnType = body
    ## In brace mode: proc name(params) { body }
    let fnTk = p.curr
    result = Node(kind: nkFunction).stamp(fnTk)
    let keyword = fnTk.value
    result.children.add(Node(kind: nkIdent, name: keyword).stamp(fnTk))
    let fnCol = fnTk.col
    walk p # consume proc/func/method/iterator/converter
    # optional name
    if p.curr.kind == tkIdentifier:
      var fnName = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
      walk p
      # Nim export marker `*` after name (e.g., `proc walk*`)
      if p.curr.kind == tkPunct and p.curr.value == "*":
        fnName = Node(kind: nkPostfix,
          children: @[fnName, Node(kind: nkIdent, name: "*").stamp(p.curr)]).stampFrom(fnName)
        walk p
      result.children.add(fnName)
    else:
      result.children.add(Node(kind: nkEmpty))
    # generic params: [T, U: Constraint = Default, ...]
    let genericParams = parseNimGenerics(p)
    if genericParams != nil:
      result.children.add(genericParams)
    # Nim pragma before params (e.g., `proc name {.pragma.}(params)`)
    while isPragmaOpen:
      walk p
      result.children.add(parseNimPragma(p))
    result.children.add(parseNimRoutineParams(p))
    # optional return type: ): ReturnType
    if p.curr.kind == tkPunct and p.curr.value == ":":
      walk p
      result.children.add(parseNimType(p))
    else:
      result.children.add(Node(kind: nkEmpty))
    # Nim pragma {.abc, efg.}
    while isPragmaOpen:
      walk p # consume '{.'
      result.children.add(parseNimPragma(p))
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
    let macroTk = p.curr
    result = Node(kind: nkFunction).stamp(macroTk)
    let keyword = macroTk.value
    result.children.add(Node(kind: nkIdent, name: keyword).stamp(macroTk))
    walk p # consume template/macro
    # optional name
    if p.curr.kind == tkIdentifier:
      var fnName = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
      walk p
      # Nim export marker `*` after name (e.g., `template stmtHandler*`)
      if p.curr.kind == tkPunct and p.curr.value == "*":
        fnName = Node(kind: nkPostfix,
          children: @[fnName, Node(kind: nkIdent, name: "*").stamp(p.curr)]).stampFrom(fnName)
        walk p
      result.children.add(fnName)
    else:
      result.children.add(Node(kind: nkEmpty))
    # generic params: [T, U: Constraint, ...]
    let macroGenerics = parseNimGenerics(p)
    if macroGenerics != nil:
      result.children.add(macroGenerics)
    # params (optional — Nim allows `proc name = body`)
    result.children.add(parseNimRoutineParams(p))
    # return type: `: ReturnType`
    if p.curr.kind == tkPunct and p.curr.value == ":":
      walk p
      result.children.add(parseNimType(p))
    else:
      result.children.add(Node(kind: nkEmpty))
    # Nim pragma {.abc, efg.}
    while isPragmaOpen:
      walk p # consume '{.'
      result.children.add(parseNimPragma(p))
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

  proc parseObjectBody(p: var GenericParser, indent: int): Node =
    ## Parse the body of an object type (fields, object variants, doc comments).
    ## Handles patterns like:
    ##   ln*, col*: int
    ##   case kind*: NodeKind
    ##     of nkLitBigInt: valBigInt*: string
    ##     of nkIdent: name*: string
    ##     else:
    ##       children*: seq[Node]
    ##         ## doc comment
    ## Synthetic blocks anchor at their first child when non-empty.
    result = Node(kind: nkBlock)
    while p.curr.kind != tkEOF and p.curr.col >= indent:
      if p.curr.kind in {tkComment, tkDocComment}:
        result.children.add(parseCommentGeneric(p))
        continue
      if p.curr.kind == tkIdentifier:
        let key = p.curr.value
        if key == "case":
          let caseTk = p.curr
          walk p
          expectIdent:
            discard
          let caseNode = Node(kind: nkStatement).stamp(caseTk)
          caseNode.children.add(Node(kind: nkIdent, name: "case").stamp(caseTk))
          var disc = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
          walk p
          if p.curr.kind == tkPunct and p.curr.value == "*":
            disc = Node(kind: nkPostfix,
              children: @[disc, Node(kind: nkIdent, name: "*").stamp(p.curr)]).stampFrom(disc)
            walk p
          # Save/restore of/else from infixTable BEFORE parsing discriminant
          var savedOf: Option[InfixEntry]
          var savedElse: Option[InfixEntry]
          if p.infixTable.hasKey("of"):
            savedOf = some(p.infixTable["of"])
            p.infixTable.del("of")
          if p.infixTable.hasKey("else"):
            savedElse = some(p.infixTable["else"])
            p.infixTable.del("else")
          if p.curr.kind == tkPunct and p.curr.value == ":":
            let colonTk = p.curr
            walk p
            let discExpr = parseExpression(p, 6)
            caseNode.children.add(Node(kind: nkInfix,
              children: @[Node(kind: nkIdent, name: ":").stamp(colonTk), disc, discExpr]).stamp(colonTk))
          else:
            caseNode.children.add(disc)
          if p.curr.kind == tkPunct and p.curr.value == ":":
            walk p
          var branches = Node(kind: nkBlock)
          while p.curr.kind == tkIdentifier and p.curr.value in ["of", "else"]:
            let branchTk = p.curr
            let branchCol = branchTk.col
            let isOf = branchTk.value == "of"
            walk p
            if isOf:
              let pattern = Node(kind: nkStatement).stamp(branchTk)
              pattern.children.add(Node(kind: nkIdent, name: "of").stamp(branchTk))
              pattern.children.add(parseExpression(p, 6))
              while p.curr.kind == tkPunct and p.curr.value == ",":
                walk p
                pattern.children.add(parseExpression(p, 6))
              if p.curr.kind == tkPunct and p.curr.value == ":":
                walk p
              pattern.children.add(parseObjectBody(p, branchCol + 2))
              branches.children.add(pattern)
            else:
              if p.curr.kind == tkPunct and p.curr.value == ":":
                walk p
              let elseBranch = Node(kind: nkStatement).stamp(branchTk)
              elseBranch.children.add(Node(kind: nkIdent, name: "else").stamp(branchTk))
              elseBranch.children.add(parseObjectBody(p, branchCol + 2))
              branches.children.add(elseBranch)
          if savedOf.isSome: p.infixTable["of"] = savedOf.get
          if savedElse.isSome: p.infixTable["else"] = savedElse.get
          closeNimBlock(branches)
          caseNode.children.add(branches)
          result.children.add(caseNode)
          continue
        elif p.stmtKeywords.hasKey(key):
          result.children.add(parseStatement(p))
          continue
        # Parse field definition
        # Parse field definition
        var fieldName = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
        walk p
        if p.curr.kind == tkPunct and p.curr.value == "*":
          fieldName = Node(kind: nkPostfix,
            children: @[fieldName, Node(kind: nkIdent, name: "*").stamp(p.curr)]).stampFrom(fieldName)
          walk p
        # Handle Nim pragma {.xxx.} after field name
        while isPragmaOpen:
          walk p
          result.children.add(parseNimPragma(p))
        if p.curr.kind == tkPunct and p.curr.value == ",":
          result.children.add(fieldName)
          walk p
        elif p.curr.kind == tkPunct and p.curr.value in ["=", ":"]:
          let opTk = p.curr
          walk p
          result.children.add(Node(kind: nkInfix,
            children: @[Node(kind: nkIdent, name: opTk.value).stamp(opTk),
                       fieldName,
                       parseExpression(p)]).stamp(opTk))
        else:
          result.children.add(fieldName)
      else:
        result.children.add(parseStatement(p))
    closeNimBlock(result)

  proc parseEnumBody(p: var GenericParser, indent: int): Node =
    ## Parse the body of an enum type.
    ## Handles patterns like:
    ##   one = "value"
    ##   two
    ##   three
    ##   four # comment
    result = Node(kind: nkBlock)
    while p.curr.kind != tkEOF and p.curr.col >= indent:
      if p.curr.kind in {tkComment, tkDocComment}:
        result.children.add(parseCommentGeneric(p))
        continue
      if p.curr.kind == tkIdentifier:
        var memberName = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
        walk p
        if p.curr.kind == tkPunct and p.curr.value == "*":
          memberName = Node(kind: nkPostfix,
            children: @[memberName, Node(kind: nkIdent, name: "*").stamp(p.curr)]).stampFrom(memberName)
          walk p
        if p.curr.kind == tkPunct and p.curr.value == "=":
          let eqTk = p.curr
          walk p
          result.children.add(Node(kind: nkInfix,
            children: @[Node(kind: nkIdent, name: "=").stamp(eqTk),
                       memberName,
                       parseExpression(p)]).stamp(eqTk))
          if p.curr.kind == tkPunct and p.curr.value == ",":
            walk p
        elif p.curr.kind == tkPunct and p.curr.value == ",":
          result.children.add(memberName)
          walk p
        else:
          result.children.add(memberName)
      else:
        result.children.add(parseStatement(p))
    closeNimBlock(result)

  stmtHandler p, "type_handler":
    ## type Name = object
    ##   field: Type
    ##   field2: Type
    let typeTk = p.curr
    walk p # consume 'type'
    result = Node(kind: nkStatement).stamp(typeTk)
    result.children.add(Node(kind: nkIdent, name: "type").stamp(typeTk))
    # parse type definitions (one or more)
    let body = Node(kind: nkBlock)
    let indent = if parentCol >= 0: parentCol else: max(0, p.curr.col - 1)
    if p.curr.kind == tkPunct and p.curr.value == ":":
      walk p
    
    if p.curr.kind == tkEOF:
      error(p, "Expected type name after 'type'")
    while p.curr.kind != tkEOF and p.curr.col > indent:
      if p.curr.kind in {tkComment, tkDocComment}:
        body.children.add(parseCommentGeneric(p))
        continue
      if p.curr.kind == tkIdentifier:
        # Dispatch statement keywords (proc, func, etc.) to their handlers
        if p.stmtKeywords.hasKey(p.curr.value):
          body.children.add(parseStatement(p, indent))
          break
        var fieldName = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
        walk p
        if p.curr.kind == tkPunct and p.curr.value == "*":
          fieldName = Node(kind: nkPostfix,
            children: @[fieldName, Node(kind: nkIdent, name: "*").stamp(p.curr)]).stampFrom(fieldName)
          walk p
        # Handle Nim pragma {.xxx.} after field/type name
        while isPragmaOpen:
          walk p # consume '{.'
          body.children.add(parseNimPragma(p))
        template addTypeDef(rhsName: string) {.dirty.} =
          ## `Name = rhsName`: op and infix stamped, rhs anchored at its token.
          body.children.add(Node(kind: nkInfix,
            children: @[Node(kind: nkIdent, name: "=").stamp(eqTk),
                        fieldName,
                        Node(kind: nkIdent, name: rhsName).stamp(p.curr)]).stampFrom(fieldName))
        # Handle comma-separated fields: prev*, curr*: Type
        if p.curr.kind == tkPunct and p.curr.value == ",":
          body.children.add(fieldName)
          walk p
        elif p.curr.kind == tkPunct and p.curr.value == "=":
          let eqTk = p.curr
          walk p
          let rhsStart = p.curr.value
          if rhsStart == "object":
            addTypeDef("object")
            walk p
            let objIndent = p.curr.col
            if p.curr.kind == tkIdentifier and p.curr.value == "of":
              walk p
              body.children.add(Node(kind: nkIdent, name: p.curr.value).stamp(p.curr))
              walk p
            body.children.add(parseObjectBody(p, objIndent))
          elif rhsStart == "ref" and p.next.kind == tkIdentifier and
                p.next.value == "object":
            walk p
            addTypeDef("ref object")
            walk p # consume 'object'
            let objIndent = p.curr.col
            if p.curr.kind == tkIdentifier and p.curr.value == "of":
              walk p
              body.children.add(Node(kind: nkIdent, name: p.curr.value).stamp(p.curr))
              walk p
            body.children.add(parseObjectBody(p, objIndent))
          elif rhsStart == "ptr" and p.next.kind == tkIdentifier and
                p.next.value == "object":
            walk p
            addTypeDef("ptr object")
            walk p # consume 'object'
            let objIndent = p.curr.col
            body.children.add(parseObjectBody(p, objIndent))
          elif rhsStart == "enum":
            addTypeDef("enum")
            walk p
            let enumIndent = p.curr.col
            body.children.add(parseEnumBody(p, enumIndent))
          elif rhsStart == "tuple":
            addTypeDef("tuple")
            walk p
            let tupIndent = p.curr.col
            body.children.add(parseObjectBody(p, tupIndent))
          else:
            body.children.add(Node(kind: nkInfix,
              children: @[Node(kind: nkIdent, name: "=").stamp(eqTk),
                          fieldName,
                          parseExpression(p)]).stampFrom(fieldName))
        elif p.curr.kind == tkPunct and p.curr.value == ":":
          let colonTk = p.curr
          walk p
          body.children.add(Node(kind: nkInfix,
            children: @[Node(kind: nkIdent, name: ":").stamp(colonTk),
                        fieldName,
                        parseExpression(p)]).stampFrom(fieldName))
        else:
          body.children.add(fieldName)
      else:
        body.children.add(parseStatement(p, indent))
    closeNimBlock(body)
    result.children.add(body)

  stmtHandler p, "defer":
    ## defer: body
    let deferTk = p.curr
    walk p # consume 'defer'
    let defCol = deferTk.col
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "defer").stamp(deferTk),
        if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
        elif p.curr.kind == tkPunct and p.curr.value == ":":
          walk p; parseBlock(p, defCol)
        else: parseBlock(p, defCol)]).stamp(deferTk)

  stmtHandler p, "raise":
    ## raise newException(...)  or  raise expr  or bare `raise` (re-raise)
    walk p # consume 'raise'
    let raiseTk = p.prev
    result = Node(kind: nkStatement).stamp(raiseTk)
    result.children.add(Node(kind: nkIdent, name: "raise").stamp(raiseTk))
    while p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p))
    # Bare `raise`: the next statement starts on a later line at the same
    # or lower indentation (an indented later line is a continuation).
    if p.curr.line != raiseTk.line and p.curr.col <= raiseTk.col:
      p.walkOpt(";")
      return result
    if p.curr.kind notin {tkEOF} and
       not (p.curr.kind == tkPunct and p.curr.value in [";", "}", ":"]) and
       not (p.curr.kind == tkIdentifier and p.curr.value in ["of", "else", "elif"]):
      result.children.add(parseExpression(p))
    p.walkOpt(";")

  stmtHandler p, "discard":
    ## discard expr  or  discard
    let discardTk = p.curr
    walk p # consume 'discard'
    result = Node(kind: nkStatement).stamp(discardTk)
    result.children.add(Node(kind: nkIdent, name: "discard").stamp(discardTk))
    while p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p))
    if p.curr.kind notin {tkEOF} and
       not (p.curr.kind == tkPunct and p.curr.value in [";", "}", ":"]) and
       not (p.curr.kind == tkIdentifier and p.curr.value in ["of", "else", "elif"]):
      result.children.add(parseExpression(p))
    p.walkOpt(";")

  stmtHandler p, "break":
    ## break  or  break label
    let breakTk = p.curr
    walk p # consume 'break'
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "break").stamp(breakTk)]).stamp(breakTk)
    # optional label (must be on same line as `break`)
    if p.curr.kind == tkIdentifier and p.curr.line == p.prev.line:
      result.children.add(Node(kind: nkIdent, name: p.curr.value).stamp(p.curr))
      walk p
    p.walkOpt(";")

  stmtHandler p, "continue":
    ## continue
    let continueTk = p.curr
    walk p # consume 'continue'
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "continue").stamp(continueTk)]).stamp(continueTk)
    p.walkOpt(";")

  stmtHandler p, "yield":
    ## yield expr
    let yieldTk = p.curr
    walk p # consume 'yield'
    result = Node(kind: nkStatement).stamp(yieldTk)
    result.children.add(Node(kind: nkIdent, name: "yield").stamp(yieldTk))
    while p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p))
    if p.curr.kind notin {tkEOF} and
       not (p.curr.kind == tkPunct and p.curr.value in [";", "}", ":"]) and
       not (p.curr.kind == tkIdentifier and p.curr.value in ["of", "else", "elif"]):
      result.children.add(parseExpression(p))
    p.walkOpt(";")

  stmtHandler p, "do_block":
    ## do: body  — used in callback style: foo do (x, y): echo x + y
    ## do (x, y: T) -> R: body  — anonymous routine with params/return type
    ## In brace mode: do { body }
    walk p # consume 'do'
    let doTk = p.prev
    let doParams = parseNimRoutineParams(p)
    var doRet = Node(kind: nkEmpty)
    if p.curr.kind == tkPunct and p.curr.value == "->":
      walk p
      doRet = parseNimType(p)
    let body = if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
               elif p.curr.kind == tkPunct and p.curr.value == ":":
                 walk p
                 let indent = if parentCol >= 0: parentCol else: max(0, p.curr.col - 1)
                 parseBlock(p, indent)
               else: parseBlock(p)
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "do").stamp(doTk),
                  doParams, doRet, body]).stamp(doTk)

  stmtHandler p, "asm":
    ## asm: ...code...
    let asmTk = p.curr
    walk p # consume 'asm'
    result = Node(kind: nkStatement).stamp(asmTk)
    result.children.add(Node(kind: nkIdent, name: "asm").stamp(asmTk))
    if p.curr.kind == tkPunct and p.curr.value == p.blockOpen:
      result.children.add(parseBlock(p))
    else:
      # inline asm string
      expectString:
        result.children.add(Node(kind: nkLitString, valStr: p.curr.value).stamp(p.curr))
      walk p
    p.walkOpt(";")

  stmtHandler p, "echo_handler":
    ## echo expr or echo expr1, expr2, ...
    let echoTk = p.curr
    walk p # consume 'echo'
    result = Node(kind: nkCall).stamp(echoTk)
    result.children.add(Node(kind: nkIdent, name: "echo").stamp(echoTk))
    while p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p))
    if p.curr.kind in {tkEOF} or
       p.curr.line != p.prev.line or
       (p.curr.kind == tkPunct and p.curr.value in [";", "}", ":", p.blockClose]):
      if p.curr.kind == tkPunct and p.curr.value == ";":
        walk p
      error(p, "Expected expression after 'echo'")
    result.children.add(parseExpression(p))
    while p.curr.kind == tkPunct and p.curr.value == ",":
      walk p
      result.children.add(parseExpression(p))
    p.walkOpt(";")

  stmtHandler p, "static":
    ## static: body  — static block for compile-time execution, or
    ## static name = expr — a compile-time declaration (declarator path).
    let staticTk = p.curr
    walk p # consume 'static'
    if p.curr.kind == tkPunct and p.curr.value == ":":
      walk p # consume ':'
      result = Node(kind: nkStatement).stamp(staticTk)
      result.children.add(Node(kind: nkIdent, name: "static").stamp(staticTk))
      result.children.add(parseBlock(p, staticTk.col))
    elif p.curr.kind == tkPunct and p.curr.value == p.blockOpen:
      result = Node(kind: nkStatement).stamp(staticTk)
      result.children.add(Node(kind: nkIdent, name: "static").stamp(staticTk))
      result.children.add(parseBlock(p))
    else:
      result = parseNimDeclarator(p, "static", staticTk)

  stmtHandler p, "with":
    ## with resource: body
    let withTk = p.curr
    walk p # consume 'with'
    result = Node(kind: nkStatement).stamp(withTk)
    result.children.add(Node(kind: nkIdent, name: "with").stamp(withTk))
    result.children.add(parseExpression(p))
    result.children.add(parseBlock(p))

  stmtHandler p, "without":
    ## without trait: body
    let withoutTk = p.curr
    walk p # consume 'without'
    result = Node(kind: nkStatement).stamp(withoutTk)
    result.children.add(Node(kind: nkIdent, name: "without").stamp(withoutTk))
    result.children.add(parseExpression(p))
    result.children.add(parseBlock(p))

  stmtHandler p, "end":
    ## end — explicit block terminator (Nim optional style)
    walk p # consume 'end'
    result = Node(kind: nkEmpty)

  stmtHandler p, "include":
    ## include file  or  include "file.nim"
    let includeTk = p.curr
    walk p # consume 'include'
    result = Node(kind: nkInclude).stamp(includeTk)
    if p.curr.kind == tkString:
      result.children.add(Node(kind: nkLitString, valStr: p.curr.value).stamp(p.curr))
      walk p
    else:
      result.children.add(parseImportPath(p))
    p.walkOpt(";")

  stmtHandler p, "export":
    ## export name, name2  or  export module/path
    let exportTk = p.curr
    walk p # consume 'export'
    result = Node(kind: nkStatement).stamp(exportTk)
    result.children.add(Node(kind: nkIdent, name: "export").stamp(exportTk))
    result.children.add(parseImportPath(p))
    while p.curr.kind == tkPunct and p.curr.value == ",":
      walk p
      result.children.add(parseImportPath(p))
    p.walkOpt(";")

proc parseNim*(path: string): OpenAstProgram =
  ## Parse a Nim script
  try:
    result = parseScript(path, nimHandlers, features = {featCommandSyntax})
  except OpenAstParsingError as e:
    echo e.msg
