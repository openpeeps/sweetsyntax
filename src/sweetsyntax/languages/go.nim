# A powerful generic parser and AST explorer for analyzing
# programming languages!
#
# (c) 2026 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

## Go language support (syntax-only: no type checking, no name resolution).
##
## Grammar reference: https://go.dev/ref/spec
## Statement termination follows the spec's semicolon-insertion rules and is
## modeled with token line comparisons (there are no newline tokens).
##
## AST shape conventions (all pre-existing node kinds):
## - Struct/interface types: `nkStatement [kw, members...]`; struct fields
##   are `nkIdentDefs [names..., type, tagOrEmpty]`, embedded fields exactly
##   `[type, tagOrEmpty]`.
## - Composite types: slices `nkBracketExpr [empty, elem]`, arrays
##   `nkBracketExpr [len, elem]` (`...` length is `nkIdent("...")`),
##   maps `nkBracketExpr [mapIdent, key, value]`, channels
##   `nkPrefix [chan|<-chan|chan<- ident, elem]`.
## - Funcs (decls, methods, literals, types): uniform arity-5 `nkFunction
##   [nameOrEmpty, receiverOrEmpty, params, resultsOrEmpty, bodyOrEmpty]`;
##   generic names are `nkBracketExpr [name, typeParam...]`, type params are
##   `nkIdentDefs [names..., constraintOrEmpty]`. Comma-items parse
##   per-item (go/parser's parseParamDecl) with a merge pass sharing one
##   type across consecutive names (`[a],[b],[c,int]` → `[a,b,c,int]`);
##   `x [N]T` vs `T[K]` follows go/parser's array/instantiation dance.
## - `var`/`const`: `nkStatement [kw, nkIdentDefs[names..., typeOrEmpty,
##   valueOrEmpty]...]` (grouped blocks append one def per line).
## - `type`: `nkStatement [kw, spec...]`, spec is `nkStatement
##   [name, typeParamsOrEmpty, aliasMarkOrEmpty, target]`.
## - Composite literals: `nkObjConstr [base, elements...]` (elements bare
##   or `nkColonExpr [key, value]`; elided nested literals use `nkEmpty`
##   as base). Unary prefixes re-wrap outside (`*T{}`, `&T{}`).
## - Type assertions: `nkTypeAssert [x, type]` (`x.(type)` keeps an
##   `nkIdent("type")` child).
## - Brackets: index `nkBracketExpr [base, idx]`, instantiation
##   `nkBracketExpr [base, args...]`, 2-slice `nkBracketExpr [base,
##   nkColonExpr [lowOrEmpty, highOrEmpty]]`, 3-slice `nkBracketExpr
##   [base, nkColonExpr [lowOrEmpty, highOrEmpty, maxOrEmpty]]`.
##   Conversions are plain `nkCall [type, args...]`; spreads wrap in
##   `nkCall [spread, arg]`.
## - Declaration fidelity (cf. go/parser, all validated differentially):
##   parameter/result lists reject mixed named and unnamed items;
##   type-parameter lists require names with constraints (unions may start
##   with a name: `[T|U]` is an unnamed constraint); an empty `[]`
##   errors. `type A[N]T` parses an array type while `type A[T C]`
##   parses type parameters. Method declarations and interface methods
##   reject type parameters. Named `func` declarations and `import`s are
##   top-level-only (anonymous literals nest freely).
## - Statement fidelity: `go`/`defer` operands must be calls; `goto`
##   labels count only on the same line; `fallthrough` takes nothing on
##   its line; select matches allow at most two receive variables and a
##   single send target; `for range` allows at most two variables.

import std/[tables, strutils, options, sets]
import ../[config, sweetlexer, tokenizer]
import ../engine/[ast, parser]

template expectIdent(body: untyped) {.dirty.} =
  if p.curr.kind == tkIdentifier:
    body
  else:
    error(p, "Expected identifier")

template expectString(body: untyped) {.dirty.} =
  if p.curr.kind == tkString:
    body
  else:
    error(p, "Expected string literal")

template atGoTypeStart: bool {.dirty.} =
  ## Whether the current token can start a Go type.
  ## `struct`/`interface`/`map`/`chan`/`func` lex as identifiers.
  p.curr.kind == tkIdentifier or
  (p.curr.kind == tkPunct and p.curr.value in ["*", "[", "(", "<-"])

proc collectGoNames(p: var GenericParser): seq[Node] =
  ## Collect an `a, b, ...` identifier run extending ONLY across commas
  ## (go/parser's parseVarList). The follower decides the meaning:
  ## `,`/`)`/`]` means unnamed types, anything else starts a shared type.
  while p.curr.kind == tkIdentifier:
    result.add(Node(kind: nkIdent, name: p.curr.value).stamp(p.curr))
    walk p
    if p.curr.kind == tkPunct and p.curr.value == ",":
      walk p # consume `,`, the run may continue
      continue
    break

proc parseGoType(p: var GenericParser): Node
proc parseGoParams(p: var GenericParser): Node
proc parseGoTypeParams(p: var GenericParser): Node
proc parseGoStructType(p: var GenericParser): Node
proc parseGoInterfaceType(p: var GenericParser): Node
proc parseGoFuncType(p: var GenericParser): Node
proc parseGoResult(p: var GenericParser, parenLine: int): Node
proc isArrayTypeAhead(p: var GenericParser): bool
proc parseGoBracketTail(p: var GenericParser, base: Node): Node
proc parseGoParamDecl(p: var GenericParser, tparams: bool): Node
proc parseGoParamList(p: var GenericParser, open, close: string): Node
proc mergeGoParamItems(p: var GenericParser, items: seq[Node],
                       closing: string): seq[Node]
proc parseGoCompositeLit(p: var GenericParser, base: Node): Node
proc parseGoElement(p: var GenericParser, lit: Node): Node
proc parseGoElementValue(p: var GenericParser): Node
proc parseGoBracketExpr(p: var GenericParser, base: Node): Node
proc goCompositeBase(lhs: Node): Node
proc goIsBareCore(n: Node): bool
proc goFinishComposite(p: var GenericParser, node: Node): Node
proc parseGoCallArgs(p: var GenericParser, callee: Node): Node

proc goFieldNode(names: seq[Node], ty, tag: Node): Node =
  ## Struct field: `nkIdentDefs [names..., type, tagOrEmpty]`
  ## (embedded fields pass no names).
  result = Node(kind: nkIdentDefs, children: names & @[ty, tag])
  if names.len > 0:
    result.stampFrom(names[0])
  else:
    result.stampFrom(ty)

proc parseGoTag(p: var GenericParser): Node =
  ## Optional struct tag (raw backquote or interpreted string, kept verbatim).
  if p.curr.kind == tkString:
    result = Node(kind: nkLitString, valStr: p.curr.value).stamp(p.curr)
    walk p
  else:
    result = newEmptyNode()

proc parseGoType(p: var GenericParser): Node =
  ## Full Go type grammar (spec §Types). Unions (`a | b`) and `~T`
  ## flow through expression parsing; callers in union-free positions
  ## (fields, results) simply never feed them one.
  if p.curr.kind == tkIdentifier:
    case p.curr.value
    of "struct":
      return parseGoStructType(p)
    of "interface":
      return parseGoInterfaceType(p)
    of "func":
      return parseGoFuncType(p)
    of "map":
      if p.next.kind == tkPunct and p.next.value == "[":
        let mapTk = p.curr
        walk p # consume `map`
        walk p # consume `[`
        let key = parseGoType(p)
        p.expectWalk("]")
        let val = parseGoType(p)
        return Node(kind: nkBracketExpr, children: @[
          Node(kind: nkIdent, name: "map").stamp(mapTk),
          key, val]).stamp(mapTk)
    of "chan":
      let chanTk = p.curr
      walk p # consume `chan`
      if p.curr.kind == tkPunct and p.curr.value == "<-":
        let opTk = p.curr
        walk p
        let elem = parseGoType(p)
        return Node(kind: nkPrefix, children: @[
          Node(kind: nkIdent, name: "chan<-").stamp(opTk),
          elem]).stamp(chanTk)
      let elem = parseGoType(p)
      return Node(kind: nkPrefix, children: @[
        Node(kind: nkIdent, name: "chan").stamp(chanTk),
        elem]).stamp(chanTk)
    else:
      discard
  if p.curr.kind == tkPunct and p.curr.value == "<-":
    # `<-chan T`
    let opTk = p.curr
    walk p
    if p.curr.kind == tkIdentifier and p.curr.value == "chan":
      walk p
    let elem = parseGoType(p)
    return Node(kind: nkPrefix, children: @[
      Node(kind: nkIdent, name: "<-chan").stamp(opTk),
      elem]).stamp(opTk)
  if p.curr.kind == tkPunct and p.curr.value == "[":
    # `[]T` slice, `[N]T` / `[...]T` array.
    let openTk = p.curr
    walk p
    if p.curr.kind == tkPunct and p.curr.value == "]":
      walk p
      let elem = parseGoType(p)
      return Node(kind: nkBracketExpr,
        children: @[newEmptyNode(), elem]).stamp(openTk)
    var lenNode: Node
    if p.curr.kind == tkPunct and p.curr.value == "...":
      lenNode = Node(kind: nkIdent, name: "...").stamp(p.curr)
      walk p
    else:
      lenNode = parseExpression(p, 0)
    p.expectWalk("]")
    let elem = parseGoType(p)
    return Node(kind: nkBracketExpr, children: @[lenNode, elem]).stamp(openTk)
  if p.curr.kind == tkPunct and p.curr.value == "*":
    # Pointer: explicit recursion (so `*[]int`, `**T` work).
    let starTk = p.curr
    walk p
    let base = parseGoType(p)
    return Node(kind: nkPrefix, children: @[
      Node(kind: nkIdent, name: "*").stamp(starTk), base]).stamp(starTk)
  if p.curr.kind == tkPunct and p.curr.value == "~":
    # `~T` underlying-type term, plus `|`-separated unions (`~int|~string`;
    # cf. go/parser's embeddedElem). Only valid in constraints; lenient.
    let tildeTk = p.curr
    walk p
    var ty = Node(kind: nkPrefix, children: @[
      Node(kind: nkIdent, name: "~").stamp(tildeTk),
      parseGoType(p)]).stamp(tildeTk)
    while p.curr.kind == tkPunct and p.curr.value == "|":
      let orTk = p.curr
      walk p
      ty = Node(kind: nkInfix, children: @[
        Node(kind: nkIdent, name: "|").stamp(orTk), ty,
        parseGoType(p)]).stamp(orTk)
    return ty
  if p.curr.kind == tkPunct and p.curr.value == "...":
    # Variadic `...T` (only valid in parameters; lenient elsewhere).
    let dotsTk = p.curr
    walk p
    let elem = parseGoType(p)
    return Node(kind: nkPrefix, children: @[
      Node(kind: nkIdent, name: "...").stamp(dotsTk), elem]).stamp(dotsTk)
  # Identifier, qualified `pkg.T`, instantiation `F[T]`,
  # parenthesized `(T)`, unions, `~T`. minPrec 2 keeps assignment
  # (`=`, `||` and below stay outside — cf. engine's `1 < minPrec` guard):
  # `var x T = v`, not `x (T = v)`. Calls are suppressed: a `(` after a
  # type belongs to an outer conversion (`[]byte(s)`), never the type.
  let savedTypeCtx = p.inTypeContext
  p.inTypeContext = true
  try:
    result = parseExpression(p, 2)
  finally:
    p.inTypeContext = savedTypeCtx

proc parseGoStructFields(p: var GenericParser, body: Node) =
  ## Append one or more fields to a struct body. The `x [N]T` (named)
  ## vs `T[K]` (embedded generic) ambiguity is resolved by scanning to
  ## the matching `]`: a type starting on the same line right after
  ## means named, anything else means embedded (this matches go/parser
  ## on all valid inputs; genuinely ambiguous inputs need a symbol
  ## table, which a syntax-only parser never has).
  let mark = (lex: markLexer(p.lexer), prev: p.prev,
              curr: p.curr, next: p.next)
  template restore() =
    restoreLexer(p.lexer, mark.lex)
    p.prev = mark.prev
    p.curr = mark.curr
    p.next = mark.next
  if p.curr.kind == tkPunct and p.curr.value == "*":
    # Embedded `*T`
    let ty = parseExpression(p, 2)
    body.children.add(goFieldNode(@[], ty, parseGoTag(p)))
    return
  if p.curr.kind != tkIdentifier:
    error(p, "Expected field name or embedded type in struct")
  let names = collectGoNames(p)
  let lastLine = p.prev.line
  if p.curr.kind == tkString or p.curr.kind == tkEOF or
     (p.curr.kind == tkPunct and p.curr.value in [";", "}"]) or
     p.curr.line != lastLine:
    # Embedded: `T` or `T "tag"`. Several names without a type
    # (`struct{ A, B }`) are invalid Go — same as gc, error here.
    if names.len > 1:
      error(p, "Expected field type after field names")
    var tag = newEmptyNode()
    if p.curr.kind == tkString:
      tag = parseGoTag(p)
    for n in names:
      body.children.add(goFieldNode(@[], n, tag))
    return
  if p.curr.kind == tkPunct and p.curr.value == ".":
    # Embedded qualified `pkg.T` (optionally generic): reparse as a
    # type expression for a uniform shape. A name list before the dot
    # (`A, B.C`) is invalid Go — same as gc, error here.
    if names.len > 1:
      error(p, "Expected type, found '.'")
    restore()
    let ty = parseExpression(p, 2)
    body.children.add(goFieldNode(@[], ty, parseGoTag(p)))
    return
  if p.curr.kind == tkPunct and p.curr.value == "[":
    # `x [N]T` (named array) vs `T[K]` (embedded instantiation).
    if isArrayTypeAhead(p):
      let ty = parseGoType(p)
      body.children.add(goFieldNode(names, ty, parseGoTag(p)))
    else:
      if names.len > 1:
        error(p, "Expected type, found '['")
      restore()
      let ty = parseExpression(p, 2)
      body.children.add(goFieldNode(@[], ty, parseGoTag(p)))
    return
  # Named: `x, y T ["tag"]` — names already collected.
  let ty = parseGoType(p)
  body.children.add(goFieldNode(names, ty, parseGoTag(p)))

proc parseGoStructType(p: var GenericParser): Node =
  let kwTk = p.curr
  walk p # consume `struct`
  result = Node(kind: nkStatement, children: @[
    Node(kind: nkIdent, name: "struct").stamp(kwTk)]).stamp(kwTk)
  p.expectWalk("{")
  while not (p.curr.kind == tkPunct and p.curr.value == "}"):
    if p.curr.kind == tkEOF:
      error(p, "Unexpected EOF in struct type")
    if p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p))
      continue
    if p.curr.kind == tkPunct and p.curr.value == ";":
      walk p
      continue
    parseGoStructFields(p, result)
  walk p # consume `}`
  # NB: no composite handling here — a same-line `{` may be a function
  # body (`func f() struct{...} { ... }`); literals ride the `infix`
  # hook, which sees the struct node as its base.

proc goIsGenericMethodAhead(p: var GenericParser): bool =
  ## curr is an identifier and next is `[`: scan the bracket content and
  ## report whether this is a generic method `M[T any](...)` rather than
  ## an embedded instantiation `L[K]`. Mirrors go/parser's parseMethodSpec:
  ## generic iff the first content item is a bare name followed by more
  ## (a constraint starting with an identifier, `~`, or `[`); a `,`, `]`,
  ## `.`, operator, or anything else means instantiation/array. Restores.
  let mark = (lex: markLexer(p.lexer), prev: p.prev,
              curr: p.curr, next: p.next)
  template restore() =
    restoreLexer(p.lexer, mark.lex)
    p.prev = mark.prev
    p.curr = mark.curr
    p.next = mark.next
  walk p # consume the name
  walk p # consume `[`
  var toks: seq[TokenTuple] = @[]
  var depth = 1
  while depth > 0:
    if p.curr.kind == tkEOF:
      restore()
      return false
    if p.curr.kind == tkPunct:
      if p.curr.value == "[":
        inc depth
      elif p.curr.value == "]":
        dec depth
        if depth == 0:
          break
    if depth == 1:
      toks.add(p.curr)
    walk p
  restore()
  if toks.len < 2 or toks[0].kind != tkIdentifier:
    return false
  result = toks[1].kind == tkIdentifier or
    (toks[1].kind == tkPunct and toks[1].value == "~") or
    (toks[1].kind == tkPunct and toks[1].value == "[")

proc goBracketIsTypeParams(p: var GenericParser): bool =
  ## curr must be `[` in a type-spec name position (`type A[...] ...`):
  ## report whether the bracket holds a type-parameter list rather than
  ## an array/slice length. Mirrors go/parser's parseTypeSpec tilt: a
  ## top-level `,` means type parameters, as does a second item starting
  ## a constraint (`T any`, `T ~int`, `P []E`, `T func()` — keywords lex
  ## as identifiers). A single name, a non-identifier start, and
  ## expression lengths (`[5]`, `[N]`, `[T*E]`, `[T|U]`) mean an
  ## array/slice type. Restores.
  let mark = (lex: markLexer(p.lexer), prev: p.prev,
              curr: p.curr, next: p.next)
  template restore() =
    restoreLexer(p.lexer, mark.lex)
    p.prev = mark.prev
    p.curr = mark.curr
    p.next = mark.next
  walk p # consume `[`
  var toks: seq[TokenTuple] = @[]
  var depth = 1
  while depth > 0:
    if p.curr.kind == tkEOF:
      restore()
      return false
    if p.curr.kind == tkPunct:
      if p.curr.value == "[":
        inc depth
      elif p.curr.value == "]":
        dec depth
        if depth == 0:
          break
    if depth == 1:
      toks.add(p.curr)
    walk p
  restore()
  if toks.len == 0 or toks[0].kind != tkIdentifier:
    return false
  if toks.len == 1:
    return false
  for t in toks:
    if t.kind == tkPunct and t.value == ",":
      return true
  if toks[1].kind == tkIdentifier:
    return true
  if toks[1].kind == tkPunct and toks[1].value in ["~", "["]:
    return true
  result = false

proc parseGoInterfaceType(p: var GenericParser): Node =
  let kwTk = p.curr
  walk p # consume `interface`
  result = Node(kind: nkStatement, children: @[
    Node(kind: nkIdent, name: "interface").stamp(kwTk)]).stamp(kwTk)
  p.expectWalk("{")
  while not (p.curr.kind == tkPunct and p.curr.value == "}"):
    if p.curr.kind == tkEOF:
      error(p, "Unexpected EOF in interface type")
    if p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p))
      continue
    if p.curr.kind == tkPunct and p.curr.value == ";":
      walk p
      continue
    if p.curr.kind == tkIdentifier and
       p.next.kind == tkPunct and p.next.value == "(":
      # Method: `Name(params) [results]` (no `func` keyword, no type params).
      let nameTk = p.curr
      let name = Node(kind: nkIdent, name: p.curr.value).stamp(nameTk)
      walk p
      let params = parseGoParams(p)
      let res = parseGoResult(p, p.prev.line)
      result.children.add(Node(kind: nkFunction, children: @[
        name, newEmptyNode(), params, res,
        newEmptyNode()]).stamp(nameTk))
    elif p.curr.kind == tkIdentifier and
         p.next.kind == tkPunct and p.next.value == "[" and
         goIsGenericMethodAhead(p):
      # Generic method `M[T any](...)`: parsed for recovery, then
      # rejected (cf. go/parser's parseMethodSpec).
      let nameTk = p.curr
      let name = Node(kind: nkIdent, name: p.curr.value).stamp(nameTk)
      walk p
      discard parseGoTypeParams(p)
      let params = parseGoParams(p)
      let res = parseGoResult(p, p.prev.line)
      result.children.add(Node(kind: nkFunction, children: @[
        name, newEmptyNode(), params, res,
        newEmptyNode()]).stamp(nameTk))
      error(p, "interface method must have no type parameters")
    else:
      # Embedded interface, union member, or `~T` term (no `=` inside types).
      result.children.add(parseExpression(p, 2))
  walk p # consume `}`

proc parseGoFuncType(p: var GenericParser): Node =
  ## `func(params) [results]` type (no name, no body).
  let kwTk = p.curr
  walk p # consume `func`
  let params = parseGoParams(p)
  let res = parseGoResult(p, p.prev.line)
  result = Node(kind: nkFunction, children: @[
    newEmptyNode(), newEmptyNode(), params, res,
    newEmptyNode()]).stamp(kwTk)

proc parseGoResult(p: var GenericParser, parenLine: int): Node =
  ## Optional result after a parameter list: `(...)` or one same-line type.
  result = newEmptyNode()
  if p.curr.kind == tkPunct and p.curr.value == "(":
    result = parseGoParams(p)
  elif p.curr.line == parenLine and atGoTypeStart:
    result = parseGoType(p)

proc isArrayTypeAhead(p: var GenericParser): bool =
  ## curr must be `[`: scans to the matching `]` (restoring afterwards)
  ## and reports whether a type starts right after on the same line.
  ## True means `x [N]T` keeps its name (array/slice type); false means
  ## an instantiation tail `T[K]` (the name becomes the base).
  ## Mirrors go/parser's parseArrayFieldOrTypeInstance, plus a same-line
  ## guard (a newline after `]` ends the construct per §Semicolons).
  let mark = (lex: markLexer(p.lexer), prev: p.prev,
              curr: p.curr, next: p.next)
  var depth = 0
  while true:
    if p.curr.kind == tkEOF:
      break
    if p.curr.kind == tkPunct:
      if p.curr.value == "[":
        inc depth
      elif p.curr.value == "]":
        dec depth
        if depth == 0:
          break
    walk p
  var isArray = false
  if p.curr.kind == tkPunct and p.curr.value == "]":
    let closeLine = p.curr.line
    walk p # consume `]`
    isArray = atGoTypeStart and p.curr.line == closeLine
  restoreLexer(p.lexer, mark.lex)
  p.prev = mark.prev
  p.curr = mark.curr
  p.next = mark.next
  result = isArray

proc parseGoBracketTail(p: var GenericParser, base: Node): Node =
  ## `base[T, ...]` instantiation tail; curr must be `[`.
  let openTk = p.curr
  walk p # consume `[`
  result = Node(kind: nkBracketExpr, children: @[base]).stamp(openTk)
  while true:
    if p.curr.kind == tkPunct and p.curr.value == "]":
      break
    if p.curr.kind == tkEOF:
      error(p, "Unexpected EOF in type arguments")
    if p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p))
      continue
    result.children.add(parseGoType(p))
    if p.curr.kind == tkPunct and p.curr.value == ",":
      walk p
      continue
    break
  p.expectWalk("]")

proc parseGoParamDecl(p: var GenericParser, tparams: bool): Node =
  ## ONE comma-item of a parameter/result/type-parameter list, following
  ## go/parser's parseParamDecl: one provisional name, then a follower
  ## decision. Returns `nkIdentDefs`: `[name, type]`, `[type]`, or
  ## `[name]` (provisional — resolved by the merge pass). Variadic
  ## `...T` wraps in `nkPrefix`. In type-parameter lists (`tparams`) a `|`
  ## after the provisional name starts an unnamed union constraint
  ## (`[T|U]`, `[int|string]` — cf. go/parser, which clears the name);
  ## a `~` after a value-parameter name is invalid Go (same as gc).
  if p.curr.kind == tkPunct and p.curr.value == "...":
    # Bare variadic `...T`
    let dotsTk = p.curr
    walk p
    let ty = parseGoType(p)
    return Node(kind: nkIdentDefs, children: @[Node(kind: nkPrefix,
      children: @[Node(kind: nkIdent, name: "...").stamp(dotsTk),
      ty]).stamp(dotsTk)]).stamp(dotsTk)
  if p.curr.kind != tkIdentifier:
    # Unnamed composite type, e.g. `[]int`
    let ty = parseGoType(p)
    return Node(kind: nkIdentDefs, children: @[ty]).stampFrom(ty)
  let nameTk = p.curr
  let name = Node(kind: nkIdent, name: p.curr.value).stamp(nameTk)
  walk p
  if tparams and p.curr.kind == tkPunct and p.curr.value == "|":
    # Union constraint starting with a name: the name belongs to the
    # union, so the whole item is unnamed (`[T|U]` means constraint
    # `T|U` with no parameter name — same as gc).
    var ty: Node = name
    while p.curr.kind == tkPunct and p.curr.value == "|":
      let orTk = p.curr
      walk p
      ty = Node(kind: nkInfix, children: @[
        Node(kind: nkIdent, name: "|").stamp(orTk), ty,
        parseGoType(p)]).stamp(orTk)
    return Node(kind: nkIdentDefs, children: @[ty]).stampFrom(ty)
  if not tparams and p.curr.kind == tkPunct and p.curr.value == "~":
    error(p, "Expected type, found '~'")
  if p.curr.kind == tkPunct and p.curr.value in [",", ")", "]"]:
    # Unnamed (resolved by the merge pass) or list separator ahead.
    return Node(kind: nkIdentDefs, children: @[name]).stamp(nameTk)
  if p.curr.kind == tkPunct and p.curr.value == ".":
    # Qualified type: the name becomes its own type (`f(A, B.C)`).
    var ty: Node = name
    while p.curr.kind == tkPunct and p.curr.value == ".":
      let dotTk = p.curr
      walk p
      expectIdent:
        ty = Node(kind: nkDotExpr, children: @[ty,
          Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)]
        ).stamp(dotTk)
        walk p
    if p.curr.kind == tkPunct and p.curr.value == "[":
      ty = parseGoBracketTail(p, ty)
    return Node(kind: nkIdentDefs, children: @[ty]).stampFrom(ty)
  if p.curr.kind == tkPunct and p.curr.value == "[":
    # The careful dance: `x [N]T` array vs `T[K]` instantiation.
    if isArrayTypeAhead(p):
      let ty = parseGoType(p)
      return Node(kind: nkIdentDefs,
        children: @[name, ty]).stamp(nameTk)
    var ty: Node = name
    ty = parseGoBracketTail(p, ty)
    return Node(kind: nkIdentDefs, children: @[ty]).stampFrom(ty)
  if p.curr.kind == tkPunct and p.curr.value == "...":
    # Named variadic `args ...T`
    let dotsTk = p.curr
    walk p
    let ty = parseGoType(p)
    return Node(kind: nkIdentDefs, children: @[name, Node(kind: nkPrefix,
      children: @[Node(kind: nkIdent, name: "...").stamp(dotsTk),
      ty]).stamp(dotsTk)]).stamp(nameTk)
  # Named with a type (`x int`, `x *T`, `T comparable`): anything else
  # starting a type, or a natural error for `;`/`{`/`=`/etc.
  let ty = parseGoType(p)
  result = Node(kind: nkIdentDefs, children: @[name, ty]).stamp(nameTk)

proc mergeGoParamItems(p: var GenericParser, items: seq[Node],
                       closing: string): seq[Node] =
  ## Distribute pass (cf. go/parser's parseParameterList): consecutive
  ## provisional `[name]` items merge into a following `[name, type]`
  ## (`[a],[b],[c,int]` → `[a,b,c,int]`); leading/trailing provisionals
  ## without a typed follower are bare types (`[A],[B]` stay separate).
  ## A named item mixed with bare types errors (`(a int, string)`), same
  ## as gc. In type-parameter lists (`closing == "]"`) a named list with
  ## leftover bare items means a missing constraint, and an all-bare list
  ## means a missing name or constraint (go/parser's messages).
  let isTParams = closing == "]"
  if isTParams:
    var anyParam = false
    for it in items:
      if it.kind notin {nkInlineComment, nkDocComment}:
        anyParam = true
        break
    if not anyParam:
      error(p, "empty type parameter list")
  var pending: seq[Node] = @[]
  var hasNamed = false
  var hasBare = false
  var typedCount = 0
  var itemCount = 0
  template flushPendingAsTypes() =
    for n in pending:
      result.add(Node(kind: nkIdentDefs,
        children: @[n]).stampFrom(n))
      hasBare = true
      inc itemCount
    pending = @[]
  for it in items:
    if it.kind in {nkInlineComment, nkDocComment}:
      # Comments barrier the merge but are not parameters.
      flushPendingAsTypes()
      result.add(it)
      continue
    if it.kind == nkIdentDefs and it.children.len == 2:
      if pending.len > 0:
        let finalName = it.children[0]
        result.add(Node(kind: nkIdentDefs,
          children: pending & @[finalName, it.children[1]]
        ).stampFrom(pending[0]))
        pending = @[]
      else:
        result.add(it)
      hasNamed = true
      inc itemCount
      inc typedCount
    elif it.kind == nkIdentDefs and it.children.len == 1 and
         it.children[0].kind == nkIdent:
      pending.add(it.children[0])
    else:
      # Complete type (qualified, instantiation, composite, variadic,
      # union): provisionals before it are bare types.
      flushPendingAsTypes()
      result.add(it)
      hasBare = true
      inc itemCount
      inc typedCount
  flushPendingAsTypes()
  if isTParams:
    if not hasNamed:
      if typedCount == 0:
        error(p, "missing type constraint")
      else:
        var msg = "missing type parameter name"
        if itemCount == 1:
          msg &= " or invalid array length"
        error(p, msg)
    elif hasBare:
      error(p, "missing type constraint")
  elif hasNamed and hasBare:
    error(p, "mixed named and unnamed parameters")

proc parseGoParamList(p: var GenericParser, open, close: string): Node =
  ## `(...)` or `[...]` list of comma-items with merge; comments pass
  ## through in order (barriering the merge, like any complete item).
  result = Node(kind: nkIdentDefs)
  result.stamp(p.curr)
  p.expectWalk(open)
  var items: seq[Node] = @[]
  while not (p.curr.kind == tkPunct and p.curr.value == close):
    if p.curr.kind == tkEOF:
      error(p, "Unexpected EOF in parameter list")
    if p.curr.kind in {tkComment, tkDocComment}:
      items.add(parseCommentGeneric(p))
      continue
    items.add(parseGoParamDecl(p, close == "]"))
    if p.curr.kind == tkPunct and p.curr.value == ",":
      walk p # consume `,`
      continue
    # Anything else loops back for the `close` check (or a natural
    # error inside the next parseGoParamDecl).
  p.expectWalk(close)
  for m in mergeGoParamItems(p, items, close):
    result.children.add(m)

proc parseGoParams(p: var GenericParser): Node =
  ## `(a, b int, c ...string)`.
  result = parseGoParamList(p, "(", ")")

proc parseGoTypeParams(p: var GenericParser): Node =
  ## `[T Constraint, K comparable]`; curr must be `[`.
  result = parseGoParamList(p, "[", "]")

proc parseGoAssertTail(p: var GenericParser, base: Node, dotTk: TokenTuple): Node =
  ## curr must be `(`: the `(T)` / `(type)` tail of `x.(T)`.
  walk p # consume `(`
  var ty: Node
  if p.curr.kind == tkIdentifier and p.curr.value == "type":
    ty = Node(kind: nkIdent, name: "type").stamp(p.curr)
    walk p
  else:
    ty = parseGoType(p)
  while p.curr.kind in {tkComment, tkDocComment}:
    walk p # comments before `)` are dropped (rare)
  p.expectWalk(")")
  result = Node(kind: nkTypeAssert, children: @[base, ty]).stamp(dotTk)

proc goFinishComposite(p: var GenericParser, node: Node): Node =
  ## Post-`{...}` continuations the engine loop never sees (it already
  ## broke): further `{...}` tails, trailing postfix (`.F`, `.(T)`,
  ## `[i]`, `(args)`), and binary infix (`T{1} == U{2}`,
  ## `[]int{1}[0] == 1`). Same-line only — a newline ends the operand
  ## per §Semicolons. Binary mirrors the engine's branch; each rhs is
  ## finished recursively so `U{2}` forms inside `==`. Go has no ternary
  ## and assignment after a composite is invalid, so plain table infix
  ## suffices (`=`, `:=`, `<-`, `,` are not table infix).
  result = node
  while true:
    if p.curr.kind == tkPunct and p.curr.value == "{" and
       p.curr.line == p.prev.line:
      let core = goCompositeBase(result)
      if core != nil and
         not (p.inControlClause and goIsBareCore(core)):
        var wrappers: seq[Node] = @[]
        var n = result
        while n != core:
          wrappers.add(n.children[0])
          n = n.children[1]
        result = parseGoCompositeLit(p, core)
        for i in countdown(wrappers.high, 0):
          result = Node(kind: nkPrefix,
            children: @[wrappers[i], result]).stampFrom(wrappers[i])
        continue
    if p.curr.kind == tkPunct and p.curr.line == p.prev.line:
      if p.curr.value == ".":
        if p.next.kind == tkPunct and p.next.value == "(":
          let dotTk = p.curr
          walk p # consume `.`
          result = parseGoAssertTail(p, result, dotTk)
          continue
        let dotTk = p.curr
        walk p # consume `.`
        if p.curr.kind != tkIdentifier:
          error(p, "Expected selector after '.'")
        result = Node(kind: nkDotExpr, children: @[result,
          Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)]
        ).stamp(dotTk)
        walk p
        continue
      elif p.curr.value == "[":
        result = parseGoBracketExpr(p, result)
        continue
      elif p.curr.value == "(":
        result = parseGoCallArgs(p, result)
        continue
    if p.curr.kind == tkPunct and p.curr.line == p.prev.line and
       p.infixTable.hasKey(p.curr.value) and
       p.infixTable[p.curr.value].special == "":
      let entry = p.infixTable[p.curr.value]
      let opTk = p.curr
      walk p
      let nextMin = if entry.assoc == rightAssoc: entry.precedence
                    else: entry.precedence + 1
      let rhs = goFinishComposite(p, parseExpression(p, nextMin))
      result = Node(kind: nkInfix, children: @[
        Node(kind: nkIdent, name: opTk.value).stamp(opTk), result, rhs]
      ).stampFrom(result)
      continue
    break

proc goCompositeBase(lhs: Node): Node =
  ## Peel unary prefixes (`*T`, `&T`, `-T`, `<-T`) to the composite core:
  ## an identifier, selector, any bracket, or struct type. Anything else
  ## (calls, func types, literals, assertions, interfaces) is not a
  ## composite base — returns nil. Mirrors the `LBRACE` case of
  ## go/parser's parsePrimaryExpr (parenthesization is already stripped
  ## by the engine's group parsing).
  var n = lhs
  while n != nil and n.kind == nkPrefix and n.children.len == 2 and
        n.children[0].kind == nkIdent and n.children[0].name in
        ["*", "&", "+", "-", "!", "^", "~", "<-"]:
    n = n.children[1]
  if n == nil:
    return nil
  case n.kind
  of nkIdent, nkDotExpr, nkBracketExpr:
    result = n
  of nkStatement:
    if n.children.len > 0 and n.children[0].kind == nkIdent and
       n.children[0].name == "struct":
      result = n
    else:
      result = nil
  else:
    result = nil

proc goIsBareCore(n: Node): bool =
  ## Whether a composite core is a bare TypeName form (banned in control
  ## clauses, where `{` opens the header body). Slices (`[]T`: empty
  ## head), maps (`map[K]V`), and struct types always count as literal
  ## types. Array lengths (`[3]int`) share the index shape and stay
  ## banned there — a documented rare-case deviation from go/parser.
  case n.kind
  of nkIdent, nkDotExpr:
    result = true
  of nkBracketExpr:
    if n.children.len == 0:
      return true
    let first = n.children[0]
    if first.kind == nkEmpty:
      return false
    if first.kind == nkIdent and first.name == "map" and
       n.children.len == 3:
      return false
    result = true
  of nkStatement:
    result = false
  else:
    result = true

proc parseGoElementValue(p: var GenericParser): Node =
  ## One composite element key or value: an elided `{...}` nested literal
  ## or a full expression (which may itself be `T{...}`).
  if p.curr.kind == tkPunct and p.curr.value == "{":
    result = parseGoCompositeLit(p, newEmptyNode())
  else:
    result = parseExpression(p, 0)

proc parseGoElement(p: var GenericParser, lit: Node): Node =
  ## One composite element appended to `lit`: `[key :] value`. Comments
  ## around the key/colon attach to the literal (struct fields precedent).
  while p.curr.kind in {tkComment, tkDocComment}:
    lit.children.add(parseCommentGeneric(p))
  let key = parseGoElementValue(p)
  while p.curr.kind in {tkComment, tkDocComment}:
    lit.children.add(parseCommentGeneric(p))
  if p.curr.kind == tkPunct and p.curr.value == ":":
    let colonTk = p.curr
    walk p # consume `:`
    let val = parseGoElementValue(p)
    result = Node(kind: nkColonExpr, children: @[key, val]).stamp(colonTk)
  else:
    result = key

proc parseGoCompositeLit(p: var GenericParser, base: Node): Node =
  ## curr must be `{`: `{ element... }` (spec §Composite literals).
  ## `nkObjConstr [base, elements...]`; elements are bare or
  ## `nkColonExpr [key, value]`. A trailing comma is optional; a missing
  ## comma between elements errors (a newline there inserts `;` per
  ## §Semicolons, surfacing as the same error — same as gc).
  let openTk = p.curr
  walk p # consume `{`
  result = Node(kind: nkObjConstr, children: @[base])
  if base.kind == nkEmpty:
    result.stamp(openTk)
  else:
    result.stampFrom(base)
  while true:
    if p.curr.kind == tkPunct and p.curr.value == "}":
      break
    if p.curr.kind == tkEOF:
      error(p, "Unexpected EOF in composite literal")
    if p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p))
      continue
    result.children.add(parseGoElement(p, result))
    while p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p))
    if p.curr.kind == tkPunct and p.curr.value == ",":
      walk p # consume `,`
      continue
    if p.curr.kind == tkPunct and p.curr.value == "}":
      break
    error(p, "Expected ',' or '}' in composite literal")
  walk p # consume `}`

proc parseGoBracketExpr(p: var GenericParser, base: Node): Node =
  ## `base[...]`: index, instantiation, or 2/3-slice (spec §Index and
  ## §Slice expressions; cf. go/parser's parseIndexOrSliceOrInstance).
  ## curr must be `[`. Shapes: index `nkBracketExpr [base, idx]`;
  ## instantiation `nkBracketExpr [base, args...]`; 2-slice
  ## `nkBracketExpr [base, nkColonExpr [lowOrEmpty, highOrEmpty]]`;
  ## 3-slice `nkBracketExpr [base, nkColonExpr [lowOrEmpty, highOrEmpty,
  ## maxOrEmpty]]`. A 3-slice requires its middle and final index,
  ## same as gc.
  let openTk = p.curr
  walk p # consume `[`
  if p.curr.kind == tkPunct and p.curr.value == "]":
    # Tolerated like go/parser (which errors but keeps parsing).
    walk p
    return Node(kind: nkBracketExpr, children: @[base, newEmptyNode()]
    ).stamp(openTk)
  var first = newEmptyNode()
  if not (p.curr.kind == tkPunct and p.curr.value == ":"):
    first = parseExpression(p, 0)
  if p.curr.kind == tkPunct and p.curr.value == ",":
    # Instantiation `F[T, U]`.
    result = Node(kind: nkBracketExpr, children: @[base, first]
    ).stamp(openTk)
    while p.curr.kind == tkPunct and p.curr.value == ",":
      walk p # consume `,`
      if p.curr.kind == tkPunct and p.curr.value == "]":
        break # trailing comma tolerance
      if p.curr.kind == tkEOF:
        error(p, "Unexpected EOF in type arguments")
      if p.curr.kind in {tkComment, tkDocComment}:
        result.children.add(parseCommentGeneric(p))
        continue
      result.children.add(parseExpression(p, 0))
    p.expectWalk("]")
    return
  if p.curr.kind == tkPunct and p.curr.value == ":":
    walk p # consume first `:`
    var bounds: seq[Node] = @[first]
    var isSlice3 = false
    while true:
      while p.curr.kind in {tkComment, tkDocComment}:
        walk p # comments inside slice bounds are dropped (rare)
      if p.curr.kind == tkPunct and p.curr.value in [":", "]"]:
        bounds.add(newEmptyNode())
      elif p.curr.kind == tkEOF:
        error(p, "Unexpected EOF in slice expression")
      else:
        bounds.add(parseExpression(p, 0))
      if p.curr.kind == tkPunct and p.curr.value == ":":
        if isSlice3:
          break # third `:`: natural error at the `]` expectation
        isSlice3 = true
        walk p # consume second `:`
        continue
      break
    p.expectWalk("]")
    if isSlice3:
      if bounds[1].kind == nkEmpty:
        error(p, "middle index required in 3-index slice")
      if bounds[2].kind == nkEmpty:
        error(p, "final index required in 3-index slice")
    result = Node(kind: nkBracketExpr, children: @[base, Node(
      kind: nkColonExpr, children: bounds).stamp(openTk)]).stamp(openTk)
    return
  p.expectWalk("]")
  result = Node(kind: nkBracketExpr, children: @[base, first]
  ).stamp(openTk)

proc parseGoVarDef(p: var GenericParser, allowInherit: bool,
                    seenValue: var bool): Node =
  ## `a, b T [= v]`: the type is same-line only (a newline after the
  ## names ends the declaration per §Semicolons), `=` is same-line only,
  ## the value may continue lines via operators or brackets.
  ## A `.` right after the names (`var c, pkg.T`) and a declaration
  ## with neither type nor value (`var x`) are invalid Go — errors,
  ## same as gc. `[` after the names scans like a struct field.
  ## In grouped `const` blocks an empty spec repeats the first preceding
  ## non-empty expression (`MB` after `KB = ...`): `allowInherit` permits
  ## valueless items once `seenValue` is set (spec §Constant declarations).
  let firstTk = p.curr
  let names = collectGoNames(p)
  if names.len == 0:
    error(p, "Expected variable name")
  if p.curr.kind == tkPunct and p.curr.value == ".":
    error(p, "Expected type, found '.'")
  if p.curr.kind == tkPunct and p.curr.value == "[" and
     not isArrayTypeAhead(p):
    error(p, "Expected type, found '['")
  let nameLine = p.prev.line
  var ty = newEmptyNode()
  if p.curr.line == nameLine and atGoTypeStart:
    ty = parseGoType(p)
  var val = newEmptyNode()
  if p.curr.kind == tkPunct and p.curr.value == "=" and
     p.curr.line == p.prev.line:
    walk p # consume `=`
    # Value list (`var x, y = 1, 2`; single defs have exactly one).
    var vals: seq[Node] = @[]
    while true:
      vals.add(parseExpression(p, 0))
      if p.curr.kind == tkPunct and p.curr.value == ",":
        walk p # consume `,`
        continue
      break
    val = vals[0]
    if vals.len > 1:
      val = Node(kind: nkStatement, children: vals).stampFrom(vals[0])
  if ty.kind == nkEmpty and val.kind == nkEmpty:
    if not (allowInherit and seenValue):
      error(p, "Expected type or value in '" & names[0].name & "' declaration")
  if val.kind != nkEmpty:
    seenValue = true
  result = Node(kind: nkIdentDefs,
    children: names & @[ty, val]).stamp(firstTk)

proc parseGoVarConst(p: var GenericParser, kwTk: TokenTuple): Node =
  ## `var`/`const`: single `x T = v` or grouped `( ... )` block.
  let kw = kwTk.value
  result = Node(kind: nkStatement, children: @[
    Node(kind: nkIdent, name: kw).stamp(kwTk)]).stamp(kwTk)
  var seenValue = false
  if p.curr.kind == tkPunct and p.curr.value == "(":
    walk p
    while not (p.curr.kind == tkPunct and p.curr.value == ")"):
      if p.curr.kind == tkEOF:
        error(p, "Unexpected EOF in " & kw & " block")
      if p.curr.kind in {tkComment, tkDocComment}:
        result.children.add(parseCommentGeneric(p))
        continue
      if p.curr.kind == tkPunct and p.curr.value == ";":
        walk p
        continue
      # Only grouped `const` inherits previous expressions; `var` and
      # single specs always need a type, a value, or both.
      result.children.add(parseGoVarDef(p, kw == "const", seenValue))
    walk p # consume `)`
  else:
    result.children.add(parseGoVarDef(p, false, seenValue))
  p.walkOpt(";")

proc parseGoTypeSpec(p: var GenericParser): Node =
  ## One `Name [params] [=] Target`; `nkStatement [name, typeParams,
  ## aliasMarkOrEmpty, target]`. A `[` after the name is a type-parameter
  ## list or an array/slice length (cf. go/parser's parseTypeSpec tilt).
  expectIdent:
    let name = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
    walk p
    var params = newEmptyNode()
    if p.curr.kind == tkPunct and p.curr.value == "[" and
       goBracketIsTypeParams(p):
      params = parseGoTypeParams(p)
    var alias = newEmptyNode()
    if p.curr.kind == tkPunct and p.curr.value == "=" and
       p.curr.line == p.prev.line:
      alias = Node(kind: nkIdent, name: "=").stamp(p.curr)
      walk p
    let target = parseGoType(p)
    result = Node(kind: nkStatement,
      children: @[name, params, alias, target]).stampFrom(name)

proc parseGoSimpleStmt(p: var GenericParser): Node =
  ## One Go SimpleStmt (spec §Statements). Multi-target `=`/`:=` and
  ## channel send ride the `infix` continuation hook, so a plain
  ## expression parse covers everything with uniform shapes.
  result = parseExpression(p, 0)

proc parseGoBlock(p: var GenericParser): Node =
  ## `parseBlock` that tracks function-body depth: named function/method
  ## declarations and imports are top-level-only in Go (cf. go/parser,
  ## whose parseStmt has no FUNC/IMPORT case), while anonymous function
  ## literals may appear anywhere. Nested blocks inherit the depth via
  ## save/restore.
  let outerDepth = p.funcDepth
  p.funcDepth = outerDepth + 1
  try:
    result = parseBlock(p)
  finally:
    p.funcDepth = outerDepth

proc parseGoCallArgs(p: var GenericParser, callee: Node): Node =
  ## curr must be `(`; wraps `nkCall [callee, args...]`. A trailing `...`
  ## on an argument is a spread (`nkCall [spread, arg]`, same as the
  ## engine's call parsing); a bare `(...)` is a first-class `...`.
  let callTk = p.curr
  walk p
  var args: seq[Node] = @[callee]
  while true:
    if p.curr.kind == tkPunct and p.curr.value == ")":
      break
    if p.curr.kind == tkEOF:
      error(p, "Unexpected EOF in call arguments")
    if p.curr.kind in {tkComment, tkDocComment}:
      args.add(parseCommentGeneric(p))
      continue
    if p.curr.kind == tkPunct and p.curr.value == "...":
      let dotsTk = p.curr
      walk p
      if p.curr.kind == tkPunct and p.curr.value == ")":
        args.add(Node(kind: nkIdent, name: "...").stamp(dotsTk))
      else:
        args.add(Node(kind: nkCall, children: @[
          Node(kind: nkIdent, name: "spread").stamp(dotsTk),
          parseExpression(p, 0)]).stamp(dotsTk))
      p.walkOpt(",")
      continue
    args.add(parseExpression(p, 0))
    let argIdx = args.high
    while p.curr.kind in {tkComment, tkDocComment}:
      args.add(parseCommentGeneric(p))
    if p.curr.kind == tkPunct and p.curr.value == "...":
      let dotsTk = p.curr
      walk p
      args[argIdx] = Node(kind: nkCall, children: @[
        Node(kind: nkIdent, name: "spread").stamp(dotsTk),
        args[argIdx]]).stamp(dotsTk)
    if p.curr.kind == tkPunct and p.curr.value == ",":
      walk p
      continue
    break
  p.expectWalk(")")
  result = Node(kind: nkCall, children: args).stamp(callTk)

proc parseGoCaseBody(p: var GenericParser, clause: Node) =
  ## StatementList ending at `case`/`default`/`}`/EOF. Nested constructs
  ## consume their own cases and braces first, so the flat check is safe
  ## (`case`/`default` are reserved and can never start a statement).
  while true:
    if p.curr.kind == tkEOF:
      break
    if p.curr.kind == tkPunct and p.curr.value == "}":
      break
    if p.curr.kind == tkIdentifier and p.curr.value in ["case", "default"]:
      break
    clause.children.add(parseStatement(p))

proc scanGoSwitchPrelude(p: var GenericParser): tuple[hasInit, isType: bool] =
  ## Token-level scan of `switch ... {`: a depth-0 `;` means an init
  ## statement is present; a `.` `(` `type` `)` subsequence means a
  ## type-switch guard. A guard pattern before the `;` belongs to the
  ## init statement and does not count. Restores before returning.
  let mark = (lex: markLexer(p.lexer), prev: p.prev,
              curr: p.curr, next: p.next)
  var hasInit = false
  var semiSeen = false
  var prePattern = false
  var postPattern = false
  var depthP = 0
  var depthB = 0
  var win: seq[tuple[kind: SweetTokenKind, val: string]] = @[]
  template pushTok() =
    win.add((p.curr.kind, p.curr.value))
    if win.len > 3:
      win.delete(0)
  template guardPattern(): bool =
    win.len == 3 and
    win[0].kind == tkPunct and win[0].val == "." and
    win[1].kind == tkPunct and win[1].val == "(" and
    win[2].kind == tkIdentifier and win[2].val == "type"
  while true:
    if p.curr.kind == tkEOF:
      break
    if p.curr.kind == tkPunct:
      case p.curr.value
      of "(", "[":
        inc depthP
      of ")", "]":
        if p.curr.value == ")" and guardPattern():
          if semiSeen:
            postPattern = true
          else:
            prePattern = true
        dec depthP
      of "{":
        if depthP == 0 and depthB == 0:
          break # body starts: no init/expr beyond this point
        inc depthB
      of "}":
        if depthP == 0 and depthB == 0:
          break
        dec depthB
      of ";":
        if depthP == 0 and depthB == 0:
          hasInit = true
          semiSeen = true
        # Continue scanning: the guard (if any) comes after.
      else:
        discard
    pushTok()
    walk p
  restoreLexer(p.lexer, mark.lex)
  p.prev = mark.prev
  p.curr = mark.curr
  p.next = mark.next
  result = (hasInit, postPattern or (prePattern and not hasInit))

proc scanGoCommMatch(p: var GenericParser): tuple[op: string, lhs: int] =
  ## Token-level scan of a select `case` match up to the terminating `:`:
  ## classifies the depth-0 match operator (`=`, `:=`, or send `<-`) and
  ## counts the comma-separated left-hand segments. A `<-` with nothing
  ## before it is a receive prefix (`<-ch`), not a send. Honors Go
  ## semicolon insertion like the `infix` hook scan (a newline after an
  ## operand ends the match). Restores before returning.
  let mark = (lex: markLexer(p.lexer), prev: p.prev,
              curr: p.curr, next: p.next)
  var depth = 0
  var braceDepth = 0
  var op = ""
  var lhs = 1
  var seenToken = false
  var prevLine = p.curr.line
  var prevEndsStmt = false
  while true:
    if p.curr.kind == tkEOF:
      break
    if p.curr.line > prevLine and prevEndsStmt:
      break # newline after an operand: match ended
    if p.curr.kind == tkPunct:
      case p.curr.value
      of "(", "[":
        inc depth
      of ")", "]":
        if depth > 0:
          dec depth
        else:
          break
      of "{":
        inc braceDepth
      of "}":
        if braceDepth > 0:
          dec braceDepth
        else:
          break
      of ":":
        if depth == 0 and braceDepth == 0:
          break # match ends here
      of ";":
        break
      of ",":
        if depth == 0 and braceDepth == 0:
          inc lhs
      of "=", ":=":
        if depth == 0 and braceDepth == 0:
          op = p.curr.value
          break
      of "<-":
        if depth == 0 and braceDepth == 0 and op == "" and seenToken:
          op = "<-"
      else:
        discard
    elif p.curr.kind notin {tkComment, tkDocComment}:
      seenToken = true
    prevEndsStmt = p.curr.kind in {tkIdentifier, tkInt, tkFloat,
      tkString, tkChar, tkHex, tkOctal, tkBinary, tkBigInt, tkImag} or
      (p.curr.kind == tkPunct and
       p.curr.value in [")", "]", "}", "++", "--"])
    prevLine = p.curr.line
    walk p
  restoreLexer(p.lexer, mark.lex)
  p.prev = mark.prev
  p.curr = mark.curr
  p.next = mark.next
  result = (op, lhs)

proc parseGoGuardBase(p: var GenericParser): Node =
  ## PrimaryExpr chain for a type-switch guard. Parsed manually because
  ## the `.` infix would swallow `.(`/`.type`. Supports selectors,
  ## calls, indexes, slices, generic args, and parenthesized bases.
  if p.curr.kind == tkPunct and p.curr.value == "(":
    walk p
    result = parseGoGuardBase(p)
    p.expectWalk(")")
  elif p.curr.kind == tkIdentifier:
    result = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
    walk p
  else:
    error(p, "Expected identifier in type-switch guard")
  while true:
    if p.curr.kind == tkPunct and p.curr.value == ".":
      if p.next.kind == tkPunct and p.next.value == "(":
        break # guard tail `.(type)`
      let dotTk = p.curr
      walk p
      expectIdent:
        result = Node(kind: nkDotExpr, children: @[result,
          Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)]
        ).stamp(dotTk)
        walk p
    elif p.curr.kind == tkPunct and p.curr.value == "[":
      result = parseGoBracketExpr(p, result)
    elif p.curr.kind == tkPunct and p.curr.value == "(":
      result = parseGoCallArgs(p, result)
    else:
      break

proc goHandlers*(p: var GenericParser) =
  exprHandler p, "infix":
    ## Go statement-level continuations invisible to the Pratt loop:
    ## multi-target `a, b = ...` / `a, b := ...` (`nkInfix
    ## [op, lhs..., rhs...]`, same head shape as the engine's single
    ## `nkInfix [op, lhs, rhs]`) and channel send `expr <- v`
    ## (`nkInfix [<-, chan, value]`; receive stays prefix).
    ## Both shapes are invalid outside statement level, so taking them
    ## here is safe: calls `f(a, b)`, instantiations `F[T, U]`, returns,
    ## and case lists all fail the speculative `=`/`:=` scan and decline.
    ## `nil` declines back to the engine.
    result = nil
    if minPrec != 0:
      return
    if p.curr.kind == tkPunct and p.curr.value == "<-" and
       p.curr.line == p.prev.line:
      let opTk = p.curr
      walk p # consume `<-`
      let val = parseExpression(p, 0)
      result = Node(kind: nkInfix, children: @[
        Node(kind: nkIdent, name: "<-").stamp(opTk), lhs, val]
      ).stampFrom(lhs)
      return
    if p.curr.kind == tkPunct and p.curr.value == "{" and
       p.curr.line == p.prev.line:
      # Composite literal `T{...}` (spec §Composite literals). Structural
      # bases (`[]T`, `map[K]V`, `struct{...}`) always count; bare
      # TypeName forms (`T`, `pkg.T`, `T[P]`, `*T`, `&T`) are blocked in
      # control clauses, where the brace opens the header body (cf.
      # go/parser's `exprLev < 0`). Trailing operators ride
      # goFinishComposite (the engine loop already broke).
      let core = goCompositeBase(lhs)
      if core != nil and
         not (p.inControlClause and goIsBareCore(core)):
        result = goFinishComposite(p, lhs)
        return
    if not (p.curr.kind == tkPunct and p.curr.value == ","):
      return
    # Speculative scan for a depth-0 `=`/`:=` before any closer:
    # only then is this a multi-target assignment. The scan honors
    # Go semicolon insertion: a newline after an operand (ident,
    # literal, `)`, `]`, `}`, `++`, `--`) ends the statement, so a
    # later line's `=` must not leak into this one. (A newline right
    # after `,` or an opener is a continuation and keeps scanning.)
    let mark = (lex: markLexer(p.lexer), prev: p.prev,
                curr: p.curr, next: p.next)
    var depth = 0
    var foundOp = false
    var prevLine = p.curr.line
    var prevEndsStmt = false
    while true:
      if p.curr.kind == tkEOF:
        break
      if p.curr.line > prevLine and prevEndsStmt:
        break # newline after an operand: statement ended
      if p.curr.kind == tkPunct:
        case p.curr.value
        of "(", "[":
          inc depth
        of ")", "]", "}", "{", ";", ":":
          if p.curr.value in [")", "]"] and depth > 0:
            dec depth
          else:
            break # closer/separator: not multi-assign
        of "=", ":=":
          if depth == 0:
            foundOp = true
            break
        else:
          discard
      prevEndsStmt = p.curr.kind in {tkIdentifier, tkInt, tkFloat,
        tkString, tkChar, tkHex, tkOctal, tkBinary, tkBigInt, tkImag} or
        (p.curr.kind == tkPunct and
         p.curr.value in [")", "]", "}", "++", "--"])
      prevLine = p.curr.line
      walk p
    restoreLexer(p.lexer, mark.lex)
    p.prev = mark.prev
    p.curr = mark.curr
    p.next = mark.next
    if not foundOp:
      return
    var targets = @[lhs]
    while p.curr.kind == tkPunct and p.curr.value == ",":
      walk p # consume `,`
      targets.add(parseExpression(p, 2))
    if p.curr.kind == tkPunct and p.curr.value in ["=", ":="]:
      let opTk = p.curr
      walk p
      var rhs: seq[Node] = @[]
      while true:
        rhs.add(parseExpression(p, 0))
        if p.curr.kind == tkPunct and p.curr.value == ",":
          walk p
          continue
        break
      result = Node(kind: nkInfix, children: @[
        Node(kind: nkIdent, name: opTk.value).stamp(opTk)] &
        targets & rhs).stampFrom(lhs)
    else:
      error(p, "Expected '=' or ':=' in assignment")

  exprHandler p, "dotParen":
    ## `x.(T)` / `x.(type)` (spec §Type assertions). The engine consumed
    ## `.`; curr is `(`. Shape `nkTypeAssert [x, type]` (`(type)` keeps an
    ## `nkIdent("type")` child). Declines outside statement level, where
    ## a parenthesized type can never start an operand. `nil` declines
    ## back to the engine's plain member access.
    result = nil
    if minPrec != 0:
      return
    let dotTk = p.prev
    result = parseGoAssertTail(p, lhs, dotTk)

  exprHandler p, "bracket":
    ## Index, instantiation, and slice expressions (Phase 3).
    result = parseGoBracketExpr(p, lhs)

  prefixHandler p, "[":
    ## Array/slice types in expression position (`[]byte(s)`,
    ## `[3]int{...}`); a following `{` becomes a composite literal via
    ## the `infix` hook afterwards.
    result = parseGoType(p)

  stmtHandler p, "package":
    ## `package main`
    let kwTk = p.curr
    if p.funcDepth > 0:
      error(p, "expected statement, found 'package'")
    walk p # consume `package`
    expectIdent:
      result = Node(kind: nkStatement, children: @[
        Node(kind: nkIdent, name: "package").stamp(kwTk),
        Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)]).stamp(kwTk)
      walk p
    p.walkOpt(";")

  stmtHandler p, "import":
    ## `import "fmt"`, `import f "fmt"`, `import _ "x"`, `import . "x"`,
    ## and grouped `import ( ... )`. Top-level-only (cf. go/parser, whose
    ## parseStmt has no IMPORT case).
    let kwTk = p.curr
    if p.funcDepth > 0:
      error(p, "expected statement, found 'import'")
    walk p # consume `import`
    result = Node(kind: nkStatement, children: @[
      Node(kind: nkIdent, name: "import").stamp(kwTk)]).stamp(kwTk)
    template importSpec {.dirty.} =
      var alias = newEmptyNode()
      if p.curr.kind == tkIdentifier:
        alias = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
        walk p
      elif p.curr.kind == tkPunct and p.curr.value == ".":
        alias = Node(kind: nkIdent, name: ".").stamp(p.curr)
        walk p
      expectString:
        result.children.add(Node(kind: nkImport, children: @[
          Node(kind: nkLitString, valStr: p.curr.value).stamp(p.curr),
          alias]).stamp(p.curr))
        walk p
      p.walkOpt(";")
    if p.curr.kind == tkPunct and p.curr.value == "(":
      walk p
      while not (p.curr.kind == tkPunct and p.curr.value == ")"):
        if p.curr.kind == tkEOF: error(p, "Unexpected EOF in import block")
        if p.curr.kind in {tkComment, tkDocComment}:
          result.children.add(parseCommentGeneric(p))
          continue
        importSpec()
      walk p # consume `)`
    else:
      importSpec()
    p.walkOpt(";")

  stmtHandler p, "function":
    ## Decls (`func f`, `func (r T) M`, `func F[P C]`), literals
    ## (`func(params) [results] {body} [(args)]`), and types.
    ## Uniform `nkFunction [name, receiver, params, results, body]`
    ## (empty slots are `nkEmpty`); generic names wrap in `nkBracketExpr`.
    let kwTk = p.curr
    walk p # consume `func`
    var recv = newEmptyNode()
    var name = newEmptyNode()
    var firstParams: Node = nil
    if p.curr.kind == tkPunct and p.curr.value == "(":
      # Receiver `(r T)` or literal params: identical prefix, branch by
      # what follows. An empty `()` is never a receiver (go/parser
      # requires exactly one); otherwise an identifier followed by `(`
      # or `[` is a method name (`(r T) M(...)`), while anything else
      # continues the literal (`() int {`, `(r T) int {`, `(r T) (x)`).
      firstParams = parseGoParams(p)
      if firstParams.children.len > 0 and
         p.curr.kind == tkIdentifier and
         p.next.kind == tkPunct and p.next.value in ["(", "["]:
        recv = firstParams
        firstParams = nil
        name = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
        walk p
    elif p.curr.kind == tkIdentifier:
      name = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
      walk p
    if name.kind != nkEmpty and
       p.curr.kind == tkPunct and p.curr.value == "[":
      let tparams = parseGoTypeParams(p)
      name = Node(kind: nkBracketExpr,
        children: @[name] & tparams.children).stampFrom(name)
    if p.funcDepth > 0 and
       (name.kind != nkEmpty or recv.kind != nkEmpty):
      # Named function/method declarations are top-level-only (cf.
      # go/parser, whose parseStmt has no FUNC case); anonymous function
      # literals and types stay allowed at any depth.
      error(p, "expected statement, found 'func'")
    if recv.kind != nkEmpty and name.kind == nkBracketExpr:
      # Method declarations have no type parameters. Parsed for recovery,
      # then rejected (cf. go/parser's parseFuncDecl).
      error(p, "method must have no type parameters")
    let params = if firstParams != nil: firstParams else: parseGoParams(p)
    let res = parseGoResult(p, p.prev.line)
    var body = newEmptyNode()
    if p.curr.kind == tkPunct and p.curr.value == "{":
      body = parseGoBlock(p)
    result = Node(kind: nkFunction,
      children: @[name, recv, params, res, body]).stamp(kwTk)
    if name.kind == nkEmpty and recv.kind == nkEmpty:
      # Trailing call args on literals: `func(){}()`.
      while p.curr.kind == tkPunct and p.curr.value == "(":
        result = parseGoCallArgs(p, result)
    p.walkOpt(";")

  stmtHandler p, "declarator":
    ## `var x T = v`, `var x = v`, `var x T`, and grouped `var ( ... )`.
    let kwTk = p.curr
    walk p # consume `var`
    result = parseGoVarConst(p, kwTk)

  stmtHandler p, "const_decl":
    ## `const x = v`, `const x T = v`, grouped blocks (`iota` is a plain ident).
    let kwTk = p.curr
    walk p # consume `const`
    result = parseGoVarConst(p, kwTk)

  stmtHandler p, "type_decl":
    ## `type Name [params] [=] Target` and grouped `type ( ... )`.
    let kwTk = p.curr
    walk p # consume `type`
    result = Node(kind: nkStatement, children: @[
      Node(kind: nkIdent, name: "type").stamp(kwTk)]).stamp(kwTk)
    if p.curr.kind == tkPunct and p.curr.value == "(":
      walk p
      while not (p.curr.kind == tkPunct and p.curr.value == ")"):
        if p.curr.kind == tkEOF:
          error(p, "Unexpected EOF in type block")
        if p.curr.kind in {tkComment, tkDocComment}:
          result.children.add(parseCommentGeneric(p))
          continue
        if p.curr.kind == tkPunct and p.curr.value == ";":
          walk p
          continue
        result.children.add(parseGoTypeSpec(p))
      walk p # consume `)`
    else:
      result.children.add(parseGoTypeSpec(p))
    p.walkOpt(";")

  stmtHandler p, "struct_type":
    ## `struct { ... }` in any type position (also reached via
    ## expression dispatch since `struct` is a statement keyword).
    result = parseGoStructType(p)

  stmtHandler p, "interface_type":
    ## `interface { ... }` in any type position.
    result = parseGoInterfaceType(p)

  stmtHandler p, "map_type":
    ## `map[K]V` in any type position.
    let mapTk = p.curr
    walk p # consume `map`
    p.expectWalk("[")
    let key = parseGoType(p)
    p.expectWalk("]")
    let val = parseGoType(p)
    result = Node(kind: nkBracketExpr, children: @[
      Node(kind: nkIdent, name: "map").stamp(mapTk),
      key, val]).stamp(mapTk)
    # NB: no composite handling here — a same-line `{` may be a function
    # body (`func f() map[string]int { ... }`); literals ride the
    # `infix` hook, which sees the map node as its base.

  stmtHandler p, "chan_type":
    ## `chan T`, `chan<- T`, `<-chan T` in any type position.
    ## (Reached via expression dispatch, not statement position.)
    let chanTk = p.curr
    if p.curr.kind == tkPunct and p.curr.value == "<-":
      walk p
      if p.curr.kind == tkIdentifier and p.curr.value == "chan":
        walk p
      let elem = parseGoType(p)
      result = Node(kind: nkPrefix, children: @[
        Node(kind: nkIdent, name: "<-chan").stamp(chanTk),
        elem]).stamp(chanTk)
    else:
      walk p # consume `chan`
      if p.curr.kind == tkPunct and p.curr.value == "<-":
        let opTk = p.curr
        walk p
        let elem = parseGoType(p)
        result = Node(kind: nkPrefix, children: @[
          Node(kind: nkIdent, name: "chan<-").stamp(opTk),
          elem]).stamp(chanTk)
      else:
        let elem = parseGoType(p)
        result = Node(kind: nkPrefix, children: @[
          Node(kind: nkIdent, name: "chan").stamp(chanTk),
          elem]).stamp(chanTk)

  stmtHandler p, "conditional":
    ## `if [init;] cond body [else if|else]` (spec §If statements).
    ## Shape `nkStatement [if, initOrEmpty, cond, then, elseOrEmpty]`.
    let kwTk = p.curr
    walk p # consume `if`
    # Control clause: a bare `T {` opens the body, never a composite
    # literal (cf. go/parser's `exprLev = -1` in parseIfHeader).
    p.inControlClause = true
    if p.curr.kind == tkPunct and p.curr.value == "{":
      error(p, "Expected expression after 'if'")
    result = Node(kind: nkStatement, children: @[
      Node(kind: nkIdent, name: "if").stamp(kwTk)]).stamp(kwTk)
    let s = parseGoSimpleStmt(p)
    if p.curr.kind == tkPunct and p.curr.value == ";":
      walk p # consume `;`
      result.children.add(s)
      result.children.add(parseExpression(p, 0))
    else:
      result.children.add(newEmptyNode())
      result.children.add(s)
    p.inControlClause = false
    result.children.add(parseGoBlock(p))
    if p.curr.kind == tkIdentifier and p.curr.value == "else":
      walk p # consume `else`
      if p.curr.kind == tkIdentifier and p.curr.value == "if":
        result.children.add(parseStatement(p))
      elif p.curr.kind == tkPunct and p.curr.value == "{":
        result.children.add(parseGoBlock(p))
      else:
        error(p, "Expected 'if' or '{' after 'else'")
    else:
      result.children.add(newEmptyNode())
    p.walkOpt(";")

  stmtHandler p, "for_loop":
    ## All four forms (spec §For statements): `for {}`, `for cond {}`,
    ## `for [init];[cond];[post] {}`, `for [vars =|:=] range expr {}`.
    ## Clause shape `nkStatement [for, init, cond, post, body]` (empty
    ## slots are `nkEmpty`); range shape `nkStatement
    ## [for, varsOrEmpty, rangeExpr, body]` with vars `nkIdentDefs
    ## [lhs..., =|:=]`.
    let kwTk = p.curr
    walk p # consume `for`
    # Control clause (cf. go/parser's `exprLev = -1` in parseForStmt):
    # covers init/cond/post and the range expression alike.
    p.inControlClause = true
    let header = Node(kind: nkIdent, name: "for").stamp(kwTk)
    var rangeVars = newEmptyNode()
    var rangeExpr: Node = nil
    var isRange = false
    if not (p.curr.kind == tkPunct and p.curr.value in [";", "{"]):
      let mark = (lex: markLexer(p.lexer), prev: p.prev,
                  curr: p.curr, next: p.next)
      block attempt:
        if p.curr.kind == tkIdentifier and p.curr.value == "range":
          walk p # consume `range`
        else:
          var lhs: seq[Node] = @[parseExpression(p, 2)]
          while p.curr.kind == tkPunct and p.curr.value == ",":
            walk p # consume `,`
            lhs.add(parseExpression(p, 2))
          if p.curr.kind == tkPunct and p.curr.value in ["=", ":="]:
            let opTk = p.curr
            walk p
            rangeVars = Node(kind: nkIdentDefs, children: lhs & @[
              Node(kind: nkIdent, name: opTk.value).stamp(opTk)]
            ).stampFrom(lhs[0])
          else:
            break attempt
          if not (p.curr.kind == tkIdentifier and p.curr.value == "range"):
            break attempt
          walk p # consume `range`
        if p.curr.kind == tkPunct and p.curr.value == "{":
          break attempt # `for range {` has no range expression
        rangeExpr = parseExpression(p, 0)
        if p.curr.kind == tkPunct and p.curr.value != "{":
          break attempt
        if rangeVars.kind == nkIdentDefs and rangeVars.children.len > 3:
          # Children are `[lhs..., =|:=]`; at most two iteration
          # variables (same as gc).
          error(p, "expected at most 2 expressions")
        isRange = true
      if not isRange:
        restoreLexer(p.lexer, mark.lex)
        p.prev = mark.prev
        p.curr = mark.curr
        p.next = mark.next
    if isRange:
      p.inControlClause = false
      result = Node(kind: nkStatement, children: @[header, rangeVars,
        rangeExpr, parseGoBlock(p)]).stamp(kwTk)
    elif p.curr.kind == tkPunct and p.curr.value == "{":
      p.inControlClause = false
      result = Node(kind: nkStatement, children: @[header,
        newEmptyNode(), newEmptyNode(), newEmptyNode(),
        parseGoBlock(p)]).stamp(kwTk)
    else:
      var init = newEmptyNode()
      if not (p.curr.kind == tkPunct and p.curr.value == ";"):
        init = parseGoSimpleStmt(p)
      if p.curr.kind == tkPunct and p.curr.value == ";":
        walk p # consume first `;`
        var cond = newEmptyNode()
        if not (p.curr.kind == tkPunct and p.curr.value == ";"):
          cond = parseExpression(p, 0)
        p.expectWalk(";")
        var post = newEmptyNode()
        if not (p.curr.kind == tkPunct and p.curr.value == "{"):
          post = parseGoSimpleStmt(p)
        p.inControlClause = false
        result = Node(kind: nkStatement, children: @[header, init,
          cond, post, parseGoBlock(p)]).stamp(kwTk)
      else:
        # The init parse was the condition (`for a < b {`).
        p.inControlClause = false
        result = Node(kind: nkStatement, children: @[header,
          newEmptyNode(), init, newEmptyNode(),
          parseGoBlock(p)]).stamp(kwTk)
    p.walkOpt(";")

  stmtHandler p, "switch":
    ## Expression and type switches (spec §Switch statements), sharing
    ## `nkStatement [switch, initOrEmpty, exprOrGuard, clause...]`.
    ## Clauses are `nkStatement [case|default, matches, body]` with
    ## matches `nkIdentDefs` (empty for `default`) and body `nkBlock`.
    ## A type guard `[name :=] base.(type)` is `nkStatement
    ## [nameOrEmpty, base]`; `fallthrough` is illegal in type switches
    ## (left to a later semantic layer, per the syntax-only rule).
    let kwTk = p.curr
    walk p # consume `switch`
    # A lone `;` before the operand list is tolerated like go/parser
    # (`switch ; { ... }` ≡ `switch { ... }`).
    p.walkOpt(";")
    # Control clause (cf. go/parser's `exprLev = -1` in parseSwitchStmt).
    p.inControlClause = true
    result = Node(kind: nkStatement, children: @[
      Node(kind: nkIdent, name: "switch").stamp(kwTk)]).stamp(kwTk)
    var isType = false
    if p.curr.kind == tkPunct and p.curr.value == "{":
      result.children.add(newEmptyNode())
      result.children.add(newEmptyNode())
    else:
      let prelude = scanGoSwitchPrelude(p)
      isType = prelude.isType
      if prelude.hasInit:
        result.children.add(parseGoSimpleStmt(p))
        p.expectWalk(";")
      else:
        result.children.add(newEmptyNode())
      if isType:
        var gname = newEmptyNode()
        if p.curr.kind == tkIdentifier and
           p.next.kind == tkPunct and p.next.value == ":=":
          gname = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
          walk p
          walk p # consume `ident` `:=`
        let base = parseGoGuardBase(p)
        p.expectWalk(".")
        p.expectWalk("(")
        if not (p.curr.kind == tkIdentifier and p.curr.value == "type"):
          error(p, "Expected 'type' in type-switch guard")
        walk p
        p.expectWalk(")")
        result.children.add(Node(kind: nkStatement,
          children: @[gname, base]).stampFrom(base))
      elif p.curr.kind == tkPunct and p.curr.value == "{":
        result.children.add(newEmptyNode())
      else:
        result.children.add(parseGoSimpleStmt(p))
    p.inControlClause = false
    p.expectWalk("{")
    while not (p.curr.kind == tkPunct and p.curr.value == "}"):
      if p.curr.kind == tkEOF:
        error(p, "Unexpected EOF in switch body")
      if p.curr.kind in {tkComment, tkDocComment}:
        result.children.add(parseCommentGeneric(p))
        continue
      if not (p.curr.kind == tkIdentifier and
              p.curr.value in ["case", "default"]):
        error(p, "Expected 'case' or 'default' in switch body")
      let caseTk = p.curr
      let isDefault = p.curr.value == "default"
      walk p
      let matches = Node(kind: nkIdentDefs).stamp(caseTk)
      if not isDefault:
        while true:
          if isType:
            matches.children.add(parseGoType(p))
          else:
            matches.children.add(parseExpression(p, 0))
          if p.curr.kind == tkPunct and p.curr.value == ",":
            walk p
            continue
          break
      p.expectWalk(":")
      let body = Node(kind: nkBlock).stamp(caseTk)
      parseGoCaseBody(p, body)
      result.children.add(Node(kind: nkStatement, children: @[
        Node(kind: nkIdent, name: caseTk.value).stamp(caseTk),
        matches, body]).stamp(caseTk))
    walk p # consume `}`
    p.walkOpt(";")

  stmtHandler p, "select":
    ## `select { case comm: ... [default: ...] }` (spec §Select).
    ## Comm clauses reuse the switch clause shape with a single match.
    let kwTk = p.curr
    walk p # consume `select`
    result = Node(kind: nkStatement, children: @[
      Node(kind: nkIdent, name: "select").stamp(kwTk)]).stamp(kwTk)
    p.expectWalk("{")
    while not (p.curr.kind == tkPunct and p.curr.value == "}"):
      if p.curr.kind == tkEOF:
        error(p, "Unexpected EOF in select body")
      if p.curr.kind in {tkComment, tkDocComment}:
        result.children.add(parseCommentGeneric(p))
        continue
      if not (p.curr.kind == tkIdentifier and
              p.curr.value in ["case", "default"]):
        error(p, "Expected 'case' or 'default' in select body")
      let caseTk = p.curr
      let isDefault = p.curr.value == "default"
      walk p
      let matches = Node(kind: nkIdentDefs).stamp(caseTk)
      if not isDefault:
        # Comm clause (spec §Select): send (`ch <- v`), receive (`<-ch`,
        # `x := <-ch`, `k, v := <-ch`), or a plain expression. The match
        # operator and left-hand count come from a token pre-scan so
        # arity errors match gc (`expected 1 or 2 expressions`,
        # `expected 1 expression`); the operands themselves ride the
        # full expression machinery (composites, calls, nesting).
        let pre = scanGoCommMatch(p)
        if pre.op in ["=", ":="]:
          if pre.lhs > 2:
            error(p, "expected 1 or 2 expressions")
        elif pre.op == "<-":
          if pre.lhs > 1:
            error(p, "expected 1 expression")
        matches.children.add(parseGoSimpleStmt(p))
      p.expectWalk(":")
      let body = Node(kind: nkBlock).stamp(caseTk)
      parseGoCaseBody(p, body)
      result.children.add(Node(kind: nkStatement, children: @[
        Node(kind: nkIdent, name: caseTk.value).stamp(caseTk),
        matches, body]).stamp(caseTk))
    walk p # consume `}`
    p.walkOpt(";")

  stmtHandler p, "case":
    error(p, "'case' outside 'switch' or 'select'")

  stmtHandler p, "go_stmt":
    ## `go call` (spec §Go statements; the operand must be a call —
    ## cf. go/parser's parseCallExpr — conversions count as calls).
    let kwTk = p.curr
    walk p # consume `go`
    let call = parseExpression(p, 0)
    if call.kind != nkCall:
      error(p, "expression in go must be function call")
    result = Node(kind: nkStatement, children: @[
      Node(kind: nkIdent, name: "go").stamp(kwTk), call]).stamp(kwTk)
    p.walkOpt(";")

  stmtHandler p, "defer":
    ## `defer call` (spec §Defer statements; same call rule as `go`).
    let kwTk = p.curr
    walk p # consume `defer`
    let call = parseExpression(p, 0)
    if call.kind != nkCall:
      error(p, "expression in defer must be function call")
    result = Node(kind: nkStatement, children: @[
      Node(kind: nkIdent, name: "defer").stamp(kwTk), call]).stamp(kwTk)
    p.walkOpt(";")

  stmtHandler p, "break":
    ## `break [label]` — the label only counts on the same line.
    let kwTk = p.curr
    walk p # consume `break`
    result = Node(kind: nkStatement, children: @[
      Node(kind: nkIdent, name: "break").stamp(kwTk)]).stamp(kwTk)
    if p.curr.kind == tkIdentifier and p.curr.line == kwTk.line:
      result.children.add(Node(kind: nkIdent, name: p.curr.value
      ).stamp(p.curr))
      walk p
    else:
      result.children.add(newEmptyNode())
    p.walkOpt(";")

  stmtHandler p, "continue":
    ## `continue [label]` — the label only counts on the same line.
    let kwTk = p.curr
    walk p # consume `continue`
    result = Node(kind: nkStatement, children: @[
      Node(kind: nkIdent, name: "continue").stamp(kwTk)]).stamp(kwTk)
    if p.curr.kind == tkIdentifier and p.curr.line == kwTk.line:
      result.children.add(Node(kind: nkIdent, name: p.curr.value
      ).stamp(p.curr))
      walk p
    else:
      result.children.add(newEmptyNode())
    p.walkOpt(";")

  stmtHandler p, "goto":
    ## `goto label` — the label only counts on the same line (a newline
    ## after `goto` ends the statement per §Semicolons, same as gc).
    let kwTk = p.curr
    walk p # consume `goto`
    result = Node(kind: nkStatement, children: @[
      Node(kind: nkIdent, name: "goto").stamp(kwTk)]).stamp(kwTk)
    if p.curr.kind == tkIdentifier and p.curr.line == kwTk.line:
      result.children.add(Node(kind: nkIdent, name: p.curr.value
      ).stamp(p.curr))
      walk p
    else:
      result.children.add(newEmptyNode())
    p.walkOpt(";")

  stmtHandler p, "fallthrough":
    ## Bare `fallthrough` (only valid ending a non-final expression-
    ## switch clause — left to a later semantic layer). Anything else on
    ## the same line errors (same as gc); a trailing comment stays for
    ## the block loop.
    let kwTk = p.curr
    walk p # consume `fallthrough`
    result = Node(kind: nkStatement, children: @[
      Node(kind: nkIdent, name: "fallthrough").stamp(kwTk)]).stamp(kwTk)
    if p.curr.kind notin {tkComment, tkDocComment} and
       p.curr.kind != tkEOF and p.curr.line == kwTk.line and
       not (p.curr.kind == tkPunct and p.curr.value in [";", "}"]):
      error(p, "expected ';', found '" & p.curr.value & "'")
    p.walkOpt(";")

  stmtHandler p, "return":
    ## `return [expr, ...]` — results only when on the same line
    ## (a newline after `return` ends the statement per spec §Semicolons).
    ## A trailing comment is not a result (`return // done` is bare; the
    ## comment stays for the block loop, like `return x // c`).
    let kwTk = p.curr
    walk p # consume `return`
    result = Node(kind: nkStatement, children: @[
      Node(kind: nkIdent, name: "return").stamp(kwTk)]).stamp(kwTk)
    if p.curr.kind in {tkComment, tkDocComment}:
      let mark = (lex: markLexer(p.lexer), prev: p.prev,
                  curr: p.curr, next: p.next)
      while p.curr.kind in {tkComment, tkDocComment}:
        walk p
      let bare = p.curr.kind == tkEOF or p.curr.line != kwTk.line or
        (p.curr.kind == tkPunct and p.curr.value in [";", "}"])
      restoreLexer(p.lexer, mark.lex)
      p.prev = mark.prev
      p.curr = mark.curr
      p.next = mark.next
      if bare:
        p.walkOpt(";")
        return
    if p.curr.kind != tkEOF and p.curr.line == kwTk.line and
       not (p.curr.kind == tkPunct and p.curr.value in [";", "}"]):
      while true:
        result.children.add(parseExpression(p, 0))
        while p.curr.kind in {tkComment, tkDocComment}:
          result.children.add(parseCommentGeneric(p))
        if p.curr.kind == tkPunct and p.curr.value == ",":
          walk p
          continue
        break
    p.walkOpt(";")

proc parseGo*(path: string): OpenAstProgram =
  try:
    result = parseScript(path, goHandlers,
      features = {featLabeledStmt})
  except OpenAstParsingError as e:
    echo e.msg
