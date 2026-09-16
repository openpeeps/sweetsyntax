# A powerful generic parser and AST explorer for analyzing
# programming languages!
#
# (c) 2026 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

import std/[sets, strutils]
import ../[config, sweetlexer]
import ../engine/[ast, parser]

const
  cSpecifiers* = ["void", "char", "short", "int", "long", "float", "double",
                   "signed", "unsigned", "_Bool", "_Complex", "_Imaginary",
                   "typeof", "struct", "union", "enum",
                   "auto", "register", "static", "extern",
                   "const", "volatile", "restrict", "inline"]

proc parseDeclarator(p: var GenericParser, allowAbstract: bool = false): Node
proc parseDirectDeclarator(p: var GenericParser, allowAbstract: bool = false): Node
proc parseCInitializer(p: var GenericParser, minPrec: int = 0): Node

var cTypedefNames: HashSet[string]
  ## Typedef aliases declared so far in the current file. Real C frontends
  ## consult the symbol table to tell `(name)` casts from `(expr)` groups;
  ## the speculative cast parser below does the same with this set.
  ## Cleared for every file in `cHandlers`.

proc unwrapCPointers(d: Node): Node =
  ## Peel `*` prefix wrappers: `int *foo()` parses as `Prefix(*, Call)`.
  result = d
  while result.kind == nkPrefix and result.children.len == 2 and
        result.children[0].kind == nkIdent and
        result.children[0].name == "*":
    result = result.children[1]

proc cPrevBreakContinued(lx: SweetLexer, pos: int): bool =
  ## Whether the physical line break before source offset `pos` ends
  ## with a backslash (C line continuation). Uses raw source via the
  ## generic lexer API, so no lexer changes are needed.
  var i = pos - 1
  while i >= 0 and lx.charAt(i) in {' ', '\t'}:
    dec i
  if i >= 0 and lx.charAt(i) == '\n':
    var j = i - 1
    if j >= 0 and lx.charAt(j) == '\r':
      dec j
    if j >= 0 and lx.charAt(j) == '\\':
      return true
  false

proc declaratorBaseName(d: Node): string =
  ## Base identifier of a declarator: `*name`, `name[N]`, `(*fn)(...)`.
  case d.kind
  of nkIdent:
    d.name
  of nkPrefix, nkPostfix:
    if d.children.len == 2: declaratorBaseName(d.children[1]) else: ""
  of nkBracketExpr, nkCall:
    if d.children.len >= 1: declaratorBaseName(d.children[0]) else: ""
  else: ""

proc parseCSpecifiers(p: var GenericParser): seq[string] =
  ## Type specifiers, folding `struct Tag` / `union Tag` / `enum Tag`
  ## into a single specifier (C library headers declare almost
  ## everything against opaque struct pointers).
  while p.curr.kind == tkIdentifier and p.curr.value in cSpecifiers:
    if p.curr.value in ["struct", "union", "enum"]:
      var spec = p.curr.value
      walk p
      if p.curr.kind == tkIdentifier:
        spec &= " " & p.curr.value
        walk p
      result.add(spec)
    else:
      result.add(p.curr.value)
      walk p

proc parseDeclarator(p: var GenericParser, allowAbstract: bool = false): Node =
  var ptrs = 0
  var firstStarTk = p.curr
  var sawStar = false
  while p.curr.kind == tkPunct and p.curr.value == "*":
    if not sawStar:
      firstStarTk = p.curr
      sawStar = true
    inc ptrs
    walk p
    while p.curr.kind == tkIdentifier and
          p.curr.value in ["const", "volatile", "restrict", "_Atomic"]:
      walk p

  result = parseDirectDeclarator(p, allowAbstract)

  for i in 1..ptrs:
    let inner = result
    result = Node(kind: nkPrefix,
      children: @[Node(kind: nkIdent, name: "*").stamp(firstStarTk), inner]).stamp(firstStarTk)

proc parseDirectDeclarator(p: var GenericParser, allowAbstract: bool = false): Node =
  if p.curr.kind == tkPunct and p.curr.value == "(":
    walk p
    result = parseDeclarator(p, allowAbstract)
    p.expectWalk(")")
  elif p.curr.kind == tkIdentifier:
    result = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
    walk p
  elif allowAbstract and p.curr.kind == tkPunct and p.curr.value in [",", ")"]:
    # Unnamed (abstract) declarator, e.g. `struct event_base *` or
    # `void` in a prototype parameter list.
    result = newEmptyNode()
  else:
    error(p, "Expected identifier or '(' in declarator")

  while true:
    if p.curr.kind == tkPunct and p.curr.value == "[":
      let openTk = p.curr
      walk p
      let size = if p.curr.kind == tkPunct and p.curr.value == "]":
                   newEmptyNode()
                 else:
                   parseExpression(p, 0)
      p.expectWalk("]")
      let base = result
      result = Node(kind: nkBracketExpr, children: @[base, size]).stampFrom(base)
    elif p.curr.kind == tkPunct and p.curr.value == "(":
      let openTk = p.curr
      walk p
      let params = Node(kind: nkIdentDefs).stamp(openTk)
      while not (p.curr.kind == tkPunct and p.curr.value == ")"):
        if p.curr.kind == tkEOF:
          error(p, "Unexpected EOF in function parameters")
        if p.curr.kind in {tkComment, tkDocComment}:
          discard parseCommentGeneric(p)
          continue
        # Parse a single parameter using the full declarator machinery
        # (parameter names may be omitted in prototypes).
        if p.curr.kind == tkPunct and p.curr.value == "...":
          params.children.add(Node(kind: nkIdent, name: "...").stamp(p.curr))
          walk p
          p.walkOpt(",")
          continue
        let specTk = p.curr
        let specifiers = parseCSpecifiers(p)
        var paramDecl = parseDeclarator(p, allowAbstract = true)
        var typePrefix = ""
        var typePrefixTk = p.curr
        if specifiers.len == 0 and paramDecl.kind == nkIdent and
           (p.curr.kind == tkIdentifier or
            (p.curr.kind == tkPunct and p.curr.value == "*")):
          # `f(sometype x)` / `f(sometype *x)`: the first ident was an
          # undeclared type name (e.g. a header typedef), not the
          # parameter name.
          typePrefix = paramDecl.name
          typePrefixTk = p.curr
          paramDecl = parseDeclarator(p, allowAbstract = true)
        let paramNode = if typePrefix.len > 0:
          Node(kind: nkPrefix, children: @[
            Node(kind: nkIdent, name: typePrefix).stamp(typePrefixTk), paramDecl]).stamp(typePrefixTk)
        elif specifiers.len > 0:
          Node(kind: nkPrefix, children: @[Node(kind: nkIdent, name: specifiers.join(" ")).stamp(specTk), paramDecl]).stamp(specTk)
        else:
          paramDecl
        params.children.add(paramNode)
        p.walkOpt(",")
      p.expectWalk(")")
      let base = result
      result = Node(kind: nkCall, children: @[base, params]).stampFrom(base)
    else:
      break

proc parseStructBody(p: var GenericParser): Node =
  let openTk = p.curr
  result = Node(kind: nkBlock).stamp(openTk)
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
  let openTk = p.curr
  result = Node(kind: nkBlock).stamp(openTk)
  p.expectWalk("{")
  while not (p.curr.kind == tkPunct and p.curr.value == "}"):
    if p.curr.kind == tkEOF:
      error(p, "Unexpected EOF in enum body")
    if p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p))
      continue
    if p.curr.kind == tkIdentifier:
      let memberTk = p.curr
      let member = Node(kind: nkStatement).stamp(memberTk)
      member.children.add(Node(kind: nkIdent, name: p.curr.value).stamp(memberTk))
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
  let kwTk = p.curr
  result = Node(kind: nkStatement).stamp(kwTk)
  result.children.add(Node(kind: nkIdent, name: kind).stamp(kwTk))
  walk p

  var tag: Node
  var body: Node

  if p.curr.kind == tkPunct and p.curr.value == "{":
    body = parseStructBody(p)
  elif p.curr.kind == tkIdentifier:
    tag = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
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

  # After tag/body: trailing declarators (`struct S a, *b;`). But a bare
  # `struct Tag` followed by anything else is a type reference — e.g. a
  # macro argument (`EVUTIL_UPCAST(p, struct event, x)`) — not a
  # declaration, so stop and let the caller own `,`/`)`.
  if p.curr.kind == tkPunct and p.curr.value == ";":
    walk p
    return
  if p.curr.kind != tkIdentifier and
     not (p.curr.kind == tkPunct and p.curr.value == "*"):
    return

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
      result.children.add(Node(kind: nkIdentDefs, children: @[decl, init]).stampFrom(decl))
    else:
      let decl = parseDeclarator(p)
      let fnDecl = unwrapCPointers(decl)
      if p.curr.kind == tkPunct and p.curr.value == "{" and
         fnDecl.kind == nkCall and fnDecl.children.len >= 2:
        # Function definition with a struct/union return type, possibly
        # split across lines (`struct event_base *\nevent_init(void) {`).
        let fnNode = Node(kind: nkFunction).stampFrom(fnDecl)
        fnNode.children.add(fnDecl.children[0])
        fnNode.children.add(fnDecl.children[1])
        fnNode.children.add(parseBlock(p))
        return fnNode
      var init: Node
      if p.curr.kind == tkPunct and p.curr.value == "=":
        walk p
        init = if p.curr.kind == tkPunct and p.curr.value == "{":
                 parseBlock(p)
               else:
                 parseExpression(p, 0)
      else:
        init = newEmptyNode()
      result.children.add(Node(kind: nkIdentDefs, children: @[decl, init]).stampFrom(decl))

proc parseCInitializer(p: var GenericParser, minPrec: int = 0): Node =
  ## C brace initializer list: `{ expr, expr, ... }`, including nested
  ## braces, `.field =` / `[i] =` designators, and `#` directives
  let openTk = p.curr
  result = Node(kind: nkArrayLit).stamp(openTk)
  walk p # consume '{'
  while not (p.curr.kind == tkPunct and p.curr.value == "}"):
    if p.curr.kind == tkEOF:
      error(p, "Unexpected EOF in initializer list")
    if p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p))
      continue
    if p.curr.kind == tkPunct and p.curr.value == "." and
       p.next.kind == tkIdentifier:
      # `.field = value` designator
      let dotTk = p.curr
      walk p
      let field = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
      walk p
      p.expectWalk("=")
      result.children.add(Node(kind: nkColonExpr,
        children: @[field, parseExpression(p, 0)]).stamp(dotTk))
    elif p.curr.kind == tkPunct and p.curr.value == "[":
      # `[index] = value` designator; plain `[N]` array sizes cannot
      # appear here, so a `[` always starts a designator.
      let openBrTk = p.curr
      walk p
      let idx = parseExpression(p, 0)
      p.expectWalk("]")
      p.expectWalk("=")
      result.children.add(Node(kind: nkColonExpr,
        children: @[idx, parseExpression(p, 0)]).stamp(openBrTk))
    else:
      result.children.add(parseExpression(p, 0))
    p.walkOpt(",")
  p.expectWalk("}")

proc cTypeNode(names: seq[string], ptrs: int, line = 0, col = 0): Node =
  ## Build a type node from specifier names plus pointer depth.
  ## Generic `stamp` helpers keep every level positioned: the cast site
  ## passes its `(` token so no `nkPrefix`/`nkIdent` is left at 0:0.
  result = Node(kind: nkIdent, name: names.join(" ")).stamp(line, col)
  for i in 1..ptrs:
    let inner = result
    result = Node(kind: nkPrefix,
      children: @[Node(kind: nkIdent, name: "*").stamp(line, col), inner]).stamp(line, col)

proc tryParseCCast(p: var GenericParser): Node =
  ## Speculatively parse `(type)operand` (C cast) or a bare `(type)`
  ## (as in `sizeof(int)`). Returns nil with the parser rewound when the
  ## parens hold a plain expression instead.
  ##
  ## Like a real C frontend this consults the typedef table: a bare
  ## `(name)` is a type only for known specifiers (`unsigned`,
  ## `struct event_base`, ...) or previously declared typedefs
  ## (`ev_uintptr_t`), so `if (x) foo()` and `(a)*b` still parse as
  ## groups while `(T*)p` and `(ev_uintptr_t)e->ptr` become casts.
  let mark = (lex: markLexer(p.lexer), prev: p.prev,
              curr: p.curr, next: p.next)
  template rewind(): Node =
    restoreLexer(p.lexer, mark.lex)
    p.prev = mark.prev
    p.curr = mark.curr
    p.next = mark.next
    nil
  walk p # consume '('
  if p.curr.kind == tkPunct and p.curr.value == ")":
    return rewind() # `()` — a group, handled by the caller
  let names = parseCSpecifiers(p)
  let hadSpecs = names.len > 0
  var typeNames = names
  if not hadSpecs:
    if p.curr.kind == tkIdentifier and
       not p.stmtKeywords.hasKey(p.curr.value):
      typeNames.add(p.curr.value)
      walk p
    else:
      return rewind()
  let typeKnown = hadSpecs or (typeNames[0] in cTypedefNames)
  # Abstract declarator: pointers (with quals) and balanced
  # `[...]` / `(...)` chunks (arrays, function-pointer params).
  var ptrs = 0
  while true:
    if p.curr.kind == tkPunct and p.curr.value == "*":
      inc ptrs
      walk p
      while p.curr.kind == tkIdentifier and p.curr.value in
            ["const", "volatile", "restrict", "_Atomic"]:
        walk p
    elif p.curr.kind == tkPunct and
         (p.curr.value == "[" or p.curr.value == "("):
      let open = p.curr.value
      let close = if open == "[": "]" else: ")"
      var depth = 0
      while true:
        if p.curr.kind == tkEOF:
          return rewind()
        if p.curr.kind == tkPunct:
          if p.curr.value == open:
            inc depth
          elif p.curr.value == close:
            dec depth
            if depth == 0:
              walk p
              break
        walk p
    else:
      break
  if p.curr.kind == tkPunct and p.curr.value == ")":
    walk p
  else:
    return rewind()
  var isOperand = false
  var isDelim = false
  case p.curr.kind
  of tkIdentifier:
    if not p.stmtKeywords.hasKey(p.curr.value):
      if typeKnown:
        isOperand = true
      else:
        # Unknown `(x) ident`: a cast in expression continuations
        # (`= (T)p`, `f((T)p)`, `return (T)p`), but a condition group
        # after `if`/`while`/`for`/`switch` (`if (x) foo()`).
        isOperand = not (mark.prev.kind == tkIdentifier and
                         mark.prev.value in ["if", "while", "for", "switch"])
  of tkInt, tkFloat, tkString, tkHex, tkOctal, tkBinary, tkBigInt,
     tkChar, tkRegex:
    isOperand = typeKnown
  of tkPunct:
    if p.curr.value == "(" or p.curr.value == "{":
      isOperand = typeKnown
    elif p.curr.value in [",", ";", ")", "]", "}"]:
      isDelim = true
    elif typeKnown and p.curr.value in ["&", "*", "-", "+", "!", "~"]:
      # `(void*)&x`, `(int)-1`: a bare `(T)` is never a valid
      # expression, so a unary operator after a known type always
      # starts the cast operand (for unknown names `(a)-b` stays a
      # group, i.e. binary minus).
      isOperand = true
  else:
    discard
  if isOperand:
    let operand = parseExpression(p, 13)
    result = Node(kind: nkPrefix, children: @[
      Node(kind: nkIdent, name: "cast").stamp(mark.curr),
      cTypeNode(typeNames, ptrs, mark.curr.line, mark.curr.col), operand]).stamp(mark.curr)
  elif isDelim and typeKnown:
    result = cTypeNode(typeNames, ptrs, mark.curr.line, mark.curr.col)
  else:
    return rewind()

proc cOperatorOperand(p: var GenericParser, minPrec: int = 0): Node =
  ## A bare operator where an operand is expected: comparison operators
  ## passed as macro arguments (`evutil_timercmp(&a, &b, <)`). Invalid
  ## anywhere else in C, so keep the lexeme as an identifier node.
  result = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
  walk p

proc parseCDeclOne(p: var GenericParser): Node =
  ## One declarator with optional initializer, bitfield width, or
  ## function body (shared by the `declarator` handler and the
  ## unknown-type recovery in `afterPrefix`).
  var decl = if p.curr.kind == tkPunct and p.curr.value == ":":
               # Anonymous bitfield, e.g. `unsigned : 8;`
               newEmptyNode()
             else:
               parseDeclarator(p)
  var init: Node
  if p.curr.kind == tkPunct and p.curr.value == "=":
    walk p
    init = if p.curr.kind == tkPunct and p.curr.value == "{":
             parseBlock(p)
           else:
             parseExpression(p, 0)
  else:
    init = newEmptyNode()

  if p.curr.kind == tkPunct and p.curr.value == ":":
    # Bitfield width, e.g. `unsigned added : 1;`
    walk p
    let width = parseExpression(p, 0)
    return Node(kind: nkColonExpr, children: @[
      Node(kind: nkIdentDefs, children: @[decl, init]).stampFrom(decl), width]).stampFrom(decl)

  if p.curr.kind == tkPunct and p.curr.value == "{" and
     unwrapCPointers(decl).kind == nkCall and
     unwrapCPointers(decl).children.len >= 2:
    let fnDecl = unwrapCPointers(decl)
    let fnNode = Node(kind: nkFunction).stampFrom(fnDecl)
    fnNode.children.add(fnDecl.children[0])
    fnNode.children.add(fnDecl.children[1])
    fnNode.children.add(parseBlock(p))
    return fnNode

  Node(kind: nkIdentDefs, children: @[decl, init]).stampFrom(decl)

proc parseCDeclRest(p: var GenericParser, stmtNode: Node): Node =
  ## Comma-separated declarator list plus `;` for a declaration whose
  ## specifiers are already recorded in `stmtNode`. Returns the function
  ## definition node when a declarator turns out to be one (so the
  ## statement handler can return it directly instead of nesting it
  ## under a `decl` statement), else nil.
  result = nil
  let first = parseCDeclOne(p)
  if first.kind == nkFunction:
    p.walkOpt(";")
    return first
  stmtNode.children.add(first)
  while p.curr.kind == tkPunct and p.curr.value == ",":
    walk p
    stmtNode.children.add(parseCDeclOne(p))
  p.walkOpt(";")

const cSeedTypedefs = [
  # Fixed-width integers (stdint.h) and POSIX / system types: never
  # declared in the file itself, but used as declarations, casts and
  # `sizeof` operands throughout real-world C.
  "size_t", "ssize_t", "ptrdiff_t", "intptr_t", "uintptr_t", "off_t",
  "time_t", "clock_t", "pid_t", "uid_t", "gid_t", "socklen_t",
  "in_addr_t", "in_port_t", "sa_family_t",
  "int8_t", "int16_t", "int32_t", "int64_t",
  "uint8_t", "uint16_t", "uint32_t", "uint64_t",
]

proc cHandlers*(p: var GenericParser) =
  cTypedefNames.clear()
  for t in cSeedTypedefs:
    cTypedefNames.incl(t)
  p.braceHandler = parseCInitializer
  for op in ["<", ">", "<=", ">=", "==", "!="]:
    p.prefixHandlers[op] = cOperatorOperand

  exprHandler p, "afterPrefix":
    ## Unknown type name starting a declaration (`size_t n;`,
    ## `mytype foo(void) { ... }`): typedefs from headers are never
    ## predeclared in the file. Two adjacent identifiers are never a
    ## valid C expression, so this is always a declaration.
    if minPrec == 0 and lhs.kind == nkIdent and
       p.curr.kind == tkIdentifier:
      result = Node(kind: nkStatement).stampFrom(lhs)
      result.children.add(Node(kind: nkIdent, name: "decl").stampFrom(lhs))
      result.children.add(Node(kind: nkIdent, name: lhs.name).stampFrom(lhs))
      let fnNode = parseCDeclRest(p, result)
      if fnNode != nil:
        return fnNode
    else:
      result = nil

  prefixHandler p, "(":
    ## C cast `(type)expr` vs parenthesized `(expr)`: speculate, and
    ## fall back to the generic group on rewind.
    let castNode = tryParseCCast(p)
    if castNode != nil:
      result = castNode
    else:
      result = parseGroupExpr(p)

  prefixHandler p, "#":
    ## Preprocessor directive: skip the whole logical line and keep the
    ## directive name (`include`, `ifdef`, ...) for the AST.
    ## Backslash-newline continuations are spliced by the generic lexer
    ## (which still advances the physical line counter), so a multi-line
    ## `#define ... do { ... } while (0)` spans several `line` values.
    let hashTk = p.curr
    let startLine = hashTk.line
    walk p # consume '#'
    var name = ""
    var nameTk = hashTk
    if p.curr.kind == tkIdentifier:
      name = p.curr.value
      nameTk = p.curr
      walk p
    while p.curr.kind != tkEOF and p.curr.line == startLine:
      walk p
    while p.curr.kind != tkEOF and cPrevBreakContinued(p.lexer, p.curr.pos):
      let l = p.curr.line
      while p.curr.kind != tkEOF and p.curr.line == l:
        walk p
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "directive").stamp(hashTk),
                  Node(kind: nkIdent, name: name).stamp(nameTk)]).stamp(hashTk)

  prefixHandler p, "*":
    let starTk = p.curr
    walk p
    let operand = parseExpression(p, 0)
    result = Node(kind: nkPrefix,
      children: @[Node(kind: nkIdent, name: "*").stamp(starTk), operand]).stamp(starTk)

  prefixHandler p, "&":
    let ampTk = p.curr
    walk p
    let operand = parseExpression(p, 0)
    result = Node(kind: nkPrefix,
      children: @[Node(kind: nkIdent, name: "&").stamp(ampTk), operand]).stamp(ampTk)

  ## declare: parse any number of specifiers, then (comma-separated) declarators
  ## with optional initializers. If a declarator has function params and is
  ## followed by `{` we create a function definition.
  stmtHandler p, "declarator":
    let kwTk = p.curr
    result = Node(kind: nkStatement).stamp(kwTk)
    result.children.add(Node(kind: nkIdent, name: "decl").stamp(kwTk))

    let specifiers = parseCSpecifiers(p)

    for s in specifiers:
      result.children.add(Node(kind: nkIdent, name: s).stampFrom(result))

    let fnNode = parseCDeclRest(p, result)
    if fnNode != nil:
      return fnNode

  stmtHandler p, "conditional":
    let kwTk = p.curr
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
      children: @[Node(kind: nkIdent, name: "if").stamp(kwTk)] & children).stamp(kwTk)

  stmtHandler p, "loop":
    let kwTk = p.curr
    walk p
    p.expectWalk("(")
    let cond = parseExpression(p)
    p.expectWalk(")")
    let body = if p.curr.kind == tkPunct and p.curr.value == "{": parseBlock(p)
               else: parseStatement(p)
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "while").stamp(kwTk), cond, body]).stamp(kwTk)

  stmtHandler p, "do_loop":
    let kwTk = p.curr
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
      children: @[Node(kind: nkIdent, name: "do-while").stamp(kwTk), body, cond]).stamp(kwTk)

  stmtHandler p, "for_loop":
    let kwTk = p.curr
    walk p
    p.expectWalk("(")
    var initNode: Node
    if p.curr.kind == tkPunct and p.curr.value == ";":
      initNode = Node(kind: nkEmpty)
      walk p
    elif p.curr.kind == tkIdentifier and p.curr.value in cSpecifiers:
      initNode = Node(kind: nkStatement).stamp(kwTk)
      initNode.children.add(Node(kind: nkIdent, name: "decl").stamp(kwTk))
      while p.curr.kind == tkIdentifier and p.curr.value in cSpecifiers:
        if p.curr.value in ["struct", "union", "enum"]:
          break
        initNode.children.add(Node(kind: nkIdent, name: p.curr.value).stamp(p.curr))
        walk p
      let decl = parseDeclarator(p)
      var initVal: Node
      if p.curr.kind == tkPunct and p.curr.value == "=":
        walk p
        initVal = parseExpression(p, 0)
      else:
        initVal = newEmptyNode()
      initNode.children.add(Node(kind: nkIdentDefs, children: @[decl, initVal]).stampFrom(decl))
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
      children: @[Node(kind: nkIdent, name: "for").stamp(kwTk),
                  initNode, condNode, updateNode, body]).stamp(kwTk)

  stmtHandler p, "switch":
    let kwTk = p.curr
    walk p
    p.expectWalk("(")
    let scrutinee = parseExpression(p)
    p.expectWalk(")")
    result = Node(kind: nkStatement).stamp(kwTk)
    result.children.add(Node(kind: nkIdent, name: "switch").stamp(kwTk))
    result.children.add(scrutinee)
    let body = Node(kind: nkBlock).stamp(kwTk)
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
    let kwTk = p.curr
    let isDefault = kwTk.value == "default"
    walk p
    result = Node(kind: nkStatement).stamp(kwTk)
    result.children.add(Node(kind: nkIdent,
      name: if isDefault: "default" else: "case").stamp(kwTk))
    if not isDefault:
      result.children.add(parseExpression(p))
    p.expectWalk(":")
    var caseBody = Node(kind: nkBlock).stamp(kwTk)
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
    let kwTk = p.curr
    walk p
    result = Node(kind: nkReturn).stamp(kwTk)
    if (p.curr.kind == tkPunct and p.curr.value in [";", "}"]) or
       p.curr.kind == tkEOF:
      p.walkOpt(";")
      return
    result.children.add(parseCommaExpr(p))
    p.walkOpt(";")

  stmtHandler p, "break":
    let kwTk = p.curr
    walk p
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "break").stamp(kwTk)]).stamp(kwTk)
    p.walkOpt(";")

  stmtHandler p, "continue":
    let kwTk = p.curr
    walk p
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "continue").stamp(kwTk)]).stamp(kwTk)
    p.walkOpt(";")

  stmtHandler p, "goto":
    let kwTk = p.curr
    walk p
    result = Node(kind: nkStatement).stamp(kwTk)
    result.children.add(Node(kind: nkIdent, name: "goto").stamp(kwTk))
    if p.curr.kind != tkIdentifier:
      error(p, "Expected label name after 'goto'")
    result.children.add(Node(kind: nkIdent, name: p.curr.value).stamp(p.curr))
    walk p
    p.walkOpt(";")

  stmtHandler p, "typedef":
    let kwTk = p.curr
    result = Node(kind: nkStatement).stamp(kwTk)
    result.children.add(Node(kind: nkIdent, name: "typedef").stamp(kwTk))
    walk p
    let specifiers = parseCSpecifiers(p)
    for s in specifiers:
      result.children.add(Node(kind: nkIdent, name: s).stampFrom(result))
    var first = true
    while true:
      if not first:
        if p.curr.kind == tkPunct and p.curr.value == ",":
          walk p
        else:
          break
      first = false
      let decl = parseDeclarator(p)
      let baseName = declaratorBaseName(decl)
      if baseName.len > 0:
        cTypedefNames.incl(baseName)
      result.children.add(Node(kind: nkIdentDefs, children: @[decl, newEmptyNode()]).stampFrom(decl))
    p.walkOpt(";")

  stmtHandler p, "struct":
    result = parseStructUnionDecl(p, "struct")

  stmtHandler p, "union":
    result = parseStructUnionDecl(p, "union")

  stmtHandler p, "enum":
    let kwTk = p.curr
    result = Node(kind: nkStatement).stamp(kwTk)
    result.children.add(Node(kind: nkIdent, name: "enum").stamp(kwTk))
    walk p
    if p.curr.kind == tkPunct and p.curr.value == "{":
      result.children.add(parseEnumBody(p))
    elif p.curr.kind == tkIdentifier:
      let tag = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
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
        result.children.add(Node(kind: nkIdentDefs, children: @[decl, init]).stampFrom(decl))
      else:
        let decl = parseDeclarator(p)
        var init: Node
        if p.curr.kind == tkPunct and p.curr.value == "=":
          walk p
          init = parseExpression(p, 0)
        else:
          init = newEmptyNode()
        result.children.add(Node(kind: nkIdentDefs, children: @[decl, init]).stampFrom(decl))
    walk p

  stmtHandler p, "sizeof":
    ## `sizeof(expr)` / `sizeof(type)` / `sizeof expr`.
    let kwTk = p.curr
    walk p
    result = Node(kind: nkPrefix,
      children: @[Node(kind: nkIdent, name: "sizeof").stamp(kwTk)]).stamp(kwTk)
    if p.curr.kind == tkPunct and p.curr.value == "(":
      let castNode = tryParseCCast(p)
      if castNode != nil:
        result.children.add(castNode)
      else:
        result.children.add(parseGroupExpr(p))
    else:
      result.children.add(parseExpression(p, 13))

  stmtHandler p, "static_assert":
    let kwTk = p.curr
    walk p
    p.expectWalk("(")
    result = Node(kind: nkStatement).stamp(kwTk)
    result.children.add(Node(kind: nkIdent, name: "_Static_assert").stamp(kwTk))
    result.children.add(parseExpression(p, 0))
    p.expectWalk(",")
    result.children.add(parseExpression(p, 0))
    p.expectWalk(")")
    p.walkOpt(";")

proc parseC*(path: string): OpenAstProgram =
  try:
    result = parseScript(path, cHandlers,
      features = {featLabeledStmt, featAdjacentConcat})
  except OpenAstParsingError as e:
    echo e.msg
