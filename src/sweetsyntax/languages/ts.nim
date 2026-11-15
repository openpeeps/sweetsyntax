# A powerful generic parser and AST explorer for analyzing
# programming languages!
#
# (c) 2026 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

## TypeScript parser: a strict superset layer over the JavaScript handlers.
##
## `tsHandlers` calls `js.jsHandlers` first, then registers the eight
## `ts.yaml` statements JS lacks (`type_alias`, `interface`, `enum`,
## `namespace`, `module`, `declare`, `abstract_class`, `using`) and
## overrides the handlers whose syntax TypeScript extends: `declarator`
## (type annotations are full types, `!` definite assignment, `const enum`),
## `function` (angle-bracket generics, typed params, overloads without a
## body), `class` (generics, `implements`, decorators, accessibility and
## variance modifiers, parameter properties, index signatures), `import` /
## `export` (`type` modifier, `export =`, `import =`) and `async_function`
## (typed and generic arrows).
##
## Types are parsed by a dedicated recursive-descent chain (`parseTSType`
## and friends) rather than the Pratt loop, so `<`/`>` nest as generics
## instead of comparisons and `as`/`satisfies` take a type rhs (via the
## `infix:as` / `infix:satisfies` expression hooks). Value positions that
## stay ambiguous (`f<T>(x)` vs `a < b`) use speculative parsing with
## `markLexer` / `restoreLexer`: a generic call commits only when type
## arguments parse cleanly *and* a call paren follows, otherwise the
## default comparison path runs untouched.
##
## AST shapes (all node kinds already exist in `ast.nim`):
## - `Foo<Bar, Baz>` reference: `nkBracketExpr [base, args...]`
## - unions/intersections: `nkInfix [| or &, lhs, rhs]` (engine order)
## - `T extends U ? A : B`: `nkCall [conditional-type, T, U, A, B]`
## - `(x: T) => R`: `nkFunction [function-type, params, return]`
## - `new (x: T) => R`: `nkFunction [construct, params, return]`
## - object types / interface bodies: `nkBlock` of member statements
## - property: `nkStatement [property, readonly?, key, type]`
## - method (type level): `nkStatement [method, key, fn]`
## - index signature: `nkStatement [index, nkIdentDefs[name, keyType], valueType]`
## - call/construct signature: `nkStatement [call | construct, params, return]`
## - mapped type: `nkStatement [mapped, constraint, valueType]`
## - tuple: `nkArrayLit` (`...T` is `nkCall [spread, T]`, `l: T` is
##   `nkColonExpr`, `T?` is `nkPostfix [T, ?]`)
## - optional `?` / definite `!` on names: `nkPostfix [name, ? | !]`
## - type alias: `nkStatement [type, name, genericsOrEmpty, aliased]`
## - interface: `nkInterface [name, genericsOrEmpty, extendsStmtOrEmpty, body]`
## - enum: `nkStatement [enum, name, body]`, members are
##   `nkIdentDefs [name, empty, initOrEmpty]`
## - namespace/module: `nkStatement [namespace | module, name, bodyOrEmpty]`
## - declare: `nkStatement [declare, decl]`
## - abstract class: `nkStatement [abstract, classNode]`
## - using: `nkStatement [using, nkIdentDefs [name, typeOrEmpty, init]]`
## - decorator: `nkPrefix [@, dec]`; decorated decls:
##   `nkPragmaBlock [nkBlock(decs), decl]`
## - `import type` / `export type` (braced/star): trailing `nkIdent("type")`
## - angle assertion `<T>x`: `nkCast [type, operand]`; `.tsx` never takes
##   this path (see the `<` prefix handler).
## - function declarations mirror `js.registerFunction`'s seven slots
##   `[keyword, star, name, generics, params, return, body]`; methods are
##   `nkColonExpr [key, nkFunction(flags..., generics, params, return, body)]`;
##   fields are `nkStatement [field, flags..., key, typeOrEmpty, initOrEmpty]`.
## - generic arrows: `nkFunction [generics, params, returnOrEmpty, body]`;
##   async arrows: `nkFunction [async, genericsOrEmpty, params, returnOrEmpty, body]`.
## - `x as T` / `x satisfies T`: `nkInfix [as | satisfies, x, T]`.
## - `a?.b` / `x!`: engine default `nkInfix [?., a, b]` / `nkPostfix [x, !]`.
##
## Known limitations (documented, not bugs): JSX elements are not parsed —
## `.tsx` only disables angle assertions; full JSX grammar is a separate
## chunk. Angle assertions accept a reference type (`<Foo<Bar>>x`), not an
## arbitrary type (`<(A | B)>x` needs `as`). `>>`/`>>>` splitting covers
## generic nesting; `>=` never appears in type position.

import std/[tables, strutils]
import ../[config, sweetlexer]
import ../engine/[ast, parser]
import ./js

template expectTSIdent(body: untyped) {.dirty.} =
  if p.curr.kind == tkIdentifier:
    body
  else:
    error(p, "Expected identifier")

proc parseTSType(p: var GenericParser): Node
proc parseTSUnionType(p: var GenericParser): Node
proc parseTSParams(p: var GenericParser): Node
proc parseTSParamsRest(p: var GenericParser): Node
proc parseTSGenericParams(p: var GenericParser): Node
proc parseTSHeritage(p: var GenericParser): Node
proc parseTSDecorators(p: var GenericParser): seq[Node]

proc skipTSComments(p: var GenericParser) {.inline.} =
  while p.curr.kind in {tkComment, tkDocComment}:
    discard parseCommentGeneric(p)

proc consumeTypeCloser(p: var GenericParser): int =
  ## Consume one `>` worth of closer and return the byte end of the full
  ## closer token. Generic nesting lexes `>>` / `>>>` as single shift
  ## tokens, so split them in place instead of walking: the outer level
  ## still sees (and consumes) its own `>`. Split extents are remembered
  ## per token start (first split wins: the innermost, fullest extent),
  ## because the mutated token understates its length and a later walk
  ## would otherwise miss the remainder.
  if p.curr.kind == tkPunct and p.curr.value == ">":
    let pos = p.curr.pos
    walk p
    result = max(p.consumedEnd(), p.closerEnds.getOrDefault(pos, -1))
  elif p.curr.kind == tkPunct and p.curr.value == ">>":
    let pos = p.curr.pos
    if not p.closerEnds.hasKey(pos):
      p.closerEnds[pos] = pos + 2
    p.curr.value = ">"
    result = pos + 2
  elif p.curr.kind == tkPunct and p.curr.value == ">>>":
    let pos = p.curr.pos
    if not p.closerEnds.hasKey(pos):
      p.closerEnds[pos] = pos + 3
    p.curr.value = ">>"
    result = pos + 3
  else:
    error(p, "Expected '>' to close generic arguments")

proc parseTSQualifiedName(p: var GenericParser): Node =
  ## `A`, `A.B.C` — no generic arguments, no array suffixes.
  expectTSIdent:
    result = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
  walk p
  while p.curr.kind == tkPunct and p.curr.value == ".":
    walk p
    expectTSIdent:
      let part = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
      result = Node(kind: nkDotExpr, children: @[result, part]).stampFrom(result)
    walk p

proc dottedPath(n: Node): seq[string] =
  ## Flatten a qualified name (`A.B.C`) to its path. Empty when any part
  ## is not a plain identifier.
  var cur = n
  var rev: seq[string] = @[]
  while cur != nil and cur.kind == nkDotExpr and cur.children.len == 2:
    if cur.children[1].kind != nkIdent:
      return @[]
    rev.add(cur.children[1].name)
    cur = cur.children[0]
  if cur != nil and cur.kind == nkIdent:
    rev.add(cur.name)
    result = rev
    for i in 0 ..< result.len div 2:
      swap(result[i], result[result.len - 1 - i])
  else:
    result = @[]

proc patternIdents(n: Node): seq[string] =
  ## Bound names in a destructuring pattern. Shape-aware: values of
  ## pairs, pattern slots of IdentDefs, elements of array patterns and
  ## spread inners are bound; defaults and computed keys are not.
  if n.isNil:
    return @[]
  case n.kind
  of nkIdent:
    result = @[n.name]
  of nkIdentDefs:
    if n.children.len > 0:
      result = patternIdents(n.children[0])
  of nkColonExpr:
    if n.children.len > 1:
      result = patternIdents(n.children[1])
  of nkBlock, nkArrayLit:
    for c in n.children:
      result.add(patternIdents(c))
  of nkPrefix:
    for i in 1 ..< n.children.len:
      result.add(patternIdents(n.children[i]))
  of nkInfix:
    # `a = default`: the lhs binds. (Any other infix cannot appear in
    # a pattern; ignore it.)
    if n.children.len > 1 and n.children[0].kind == nkIdent and
        n.children[0].name == "=":
      result = patternIdents(n.children[1])
  of nkPostfix:
    if n.children.len > 0:
      result = patternIdents(n.children[0])
  else:
    discard

proc exportDeclNames(n: Node): seq[string] =
  ## Exported binding names of a declaration node (for `export ...`
  ## inside namespaces: `N.<name> = <name>` assignments).
  if n.isNil:
    return @[]
  case n.kind
  of nkFunction:
    if n.children.len > 2 and n.children[2].kind == nkIdent:
      result = @[n.children[2].name]
  of nkStatement:
    if n.children.len == 0 or n.children[0].kind != nkIdent:
      return @[]
    case n.children[0].name
    of "var", "let", "const":
      for i in 1 ..< n.children.len:
        let e = n.children[i]
        if e.kind == nkIdent:
          result.add(e.name)
        else:
          result.add(patternIdents(e))
    of "class", "enum", "type":
      if n.children.len > 1 and n.children[1].kind == nkIdent:
        result = @[n.children[1].name]
    of "namespace", "module":
      if n.children.len > 1:
        let path = dottedPath(n.children[1])
        if path.len > 0:
          result = @[path[^1]]
    of "declare", "abstract":
      if n.children.len > 1:
        result = exportDeclNames(n.children[1])
    else:
      # abstract methods, overloads...: no namespace assignment.
      discard
  of nkInterface:
    if n.children.len > 0 and n.children[0].kind == nkIdent:
      result = @[n.children[0].name]
  else:
    discard

proc parseTSGenericArgs(p: var GenericParser): seq[Node] =
  ## Called with `curr == "<"`. Parses `<A, B<C>>` into type nodes,
  ## handling `>>` / `>>>` splitting on the way out.
  result = @[]
  let eraseFrom = p.markPos()
  walk p # consume `<`
  skipTSComments(p)
  var closerEnd = -1
  while true:
    if p.curr.kind == tkEOF:
      error(p, "Unexpected EOF in generic arguments")
    result.add(parseTSType(p))
    skipTSComments(p)
    if p.curr.kind == tkPunct and p.curr.value == ",":
      walk p
      skipTSComments(p)
    elif p.curr.kind == tkPunct and p.curr.value in [">", ">>", ">>>"]:
      closerEnd = consumeTypeCloser(p)
      break
    else:
      error(p, "Expected ',' or '>' in generic arguments")
  p.stripSince(eraseFrom, upto = closerEnd)

proc parseTSTypeSuffixes(p: var GenericParser, base: Node): Node =
  ## Array shorthands and indexed access: `T[]`, `T[K]`, `T[K][]`, `(A|B)[K]`.
  result = base
  while p.curr.kind == tkPunct and p.curr.value == "[":
    walk p # consume `[`
    skipTSComments(p)
    if p.curr.kind == tkPunct and p.curr.value == "]":
      walk p
      result = Node(kind: nkBracketExpr,
        children: @[result, newEmptyNode()]).stampFrom(result)
    else:
      let idx = parseTSType(p)
      skipTSComments(p)
      p.expectWalk("]")
      result = Node(kind: nkBracketExpr,
        children: @[result, idx]).stampFrom(result)

proc parseTSTypeRef(p: var GenericParser): Node =
  ## A named type: `A.B<C>[]`, `A.B<C>[K]`. In type position `<` always
  ## opens generic arguments (comparisons never appear here), so no
  ## lookahead is needed.
  result = parseTSQualifiedName(p)
  skipTSComments(p)
  if p.curr.kind == tkPunct and p.curr.value == "<":
    let args = parseTSGenericArgs(p)
    result = Node(kind: nkBracketExpr, children: @[result] & args).stampFrom(result)
  result = parseTSTypeSuffixes(p, result)

proc parseTSHeritage(p: var GenericParser): Node =
  ## `extends` / `implements` reference: a qualified name with optional
  ## generic arguments and optional call suffixes (`extends mix(Base)`).
  ## Unions and intersections never appear here.
  result = parseTSQualifiedName(p)
  skipTSComments(p)
  if p.curr.kind == tkPunct and p.curr.value == "<":
    let args = parseTSGenericArgs(p)
    result = Node(kind: nkBracketExpr, children: @[result] & args).stampFrom(result)
  while p.curr.kind == tkPunct and p.curr.value == "(":
    let openTk = p.curr
    walk p
    let call = Node(kind: nkCall, children: @[result]).stamp(openTk)
    while not (p.curr.kind == tkPunct and p.curr.value == ")"):
      if p.curr.kind == tkEOF:
        error(p, "Unexpected EOF in heritage call")
      if p.curr.kind in {tkComment, tkDocComment}:
        call.children.add(parseCommentGeneric(p))
        continue
      if p.curr.kind == tkPunct and p.curr.value == "...":
        let dotsTk = p.curr
        walk p
        call.children.add(Node(kind: nkCall,
          children: @[Node(kind: nkIdent, name: "spread").stamp(dotsTk),
                      parseExpression(p, 0)]).stamp(dotsTk))
      else:
        call.children.add(parseExpression(p, 0))
      p.walkOpt(",")
    p.expectWalk(")")
    result = call

proc parseTSObjectType(p: var GenericParser): Node
proc parseTSTupleType(p: var GenericParser): Node

proc parseTSPrimaryType(p: var GenericParser): Node =
  ## Single types: literals, references, parenthesized / function types,
  ## object literals, tuples.
  skipTSComments(p)
  case p.curr.kind
  of tkString, tkInt, tkFloat, tkHex, tkOctal, tkBinary, tkBigInt:
    result = parseLiteral(p)
  of tkIdentifier:
    case p.curr.value
    of "true", "false":
      result = Node(kind: nkLitBool, valBool: p.curr.value == "true").stamp(p.curr)
      walk p
    of "null", "undefined":
      result = Node(kind: nkNil).stamp(p.curr)
      walk p
    else:
      result = parseTSTypeRef(p)
  of tkPunct:
    if p.curr.value == "{":
      result = parseTSObjectType(p)
    elif p.curr.kind == tkPunct and p.curr.value == "[":
      result = parseTSTupleType(p)
    elif p.curr.kind == tkPunct and p.curr.value == "<":
      # Generic arrow type: `<T>(x: T) => R`. Unlike the expression-level
      # `<` prefix there is no assertion fallback here — `<` in type
      # position always opens generic parameters.
      let generics = parseTSGenericParams(p)
      let params = parseTSParams(p)
      skipTSComments(p)
      p.expectWalk("=>")
      skipTSComments(p)
      let ret = parseTSType(p)
      result = Node(kind: nkFunction,
        children: @[generics, params, ret])
    elif p.curr.value == "(":
      walk p # consume `(`
      skipTSComments(p)
      var items: seq[Node] = @[]
      var named: seq[bool] = @[]
      if not (p.curr.kind == tkPunct and p.curr.value == ")"):
        while true:
          skipTSComments(p)
          if p.curr.kind == tkPunct and p.curr.value == "...":
            let dotsTk = p.curr
            walk p
            expectTSIdent:
              var rp = Node(kind: nkIdentDefs)
              rp.children.add(Node(kind: nkIdent, name: p.curr.value).stamp(p.curr))
              walk p
              if p.curr.kind == tkPunct and p.curr.value == ":":
                walk p
                rp.children.add(parseTSType(p))
              else:
                rp.children.add(newEmptyNode())
              items.add(Node(kind: nkPrefix,
                children: @[Node(kind: nkIdent, name: "...").stamp(dotsTk), rp]).stamp(dotsTk))
              named.add(true)
          elif p.curr.kind == tkIdentifier and
              (p.next.kind == tkPunct and p.next.value in [":", "?"]):
            let nm = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
            walk p
            var opt = false
            var qTk = p.curr
            if p.curr.kind == tkPunct and p.curr.value == "?":
              opt = true
              qTk = p.curr
              walk p
            var ty = newEmptyNode()
            if p.curr.kind == tkPunct and p.curr.value == ":":
              walk p
              ty = parseTSType(p)
            let key = if opt: Node(kind: nkPostfix,
              children: @[nm, Node(kind: nkIdent, name: "?").stamp(qTk)]).stampFrom(nm)
                        else: nm
            items.add(Node(kind: nkIdentDefs, children: @[key, ty]))
            named.add(true)
          else:
            items.add(parseTSType(p))
            named.add(false)
          skipTSComments(p)
          if p.curr.kind == tkPunct and p.curr.value == ",":
            walk p
            continue
          break
      p.expectWalk(")")
      if p.curr.kind == tkPunct and p.curr.value == "=>":
        # Function type: bare identifiers are parameter *names* (`(A) => R`
        # means a parameter named `A`), anything else must already be a
        # named `x: T` entry.
        walk p # consume `=>`
        let ret = parseTSType(p)
        let params = Node(kind: nkIdentDefs)
        for i, it in items:
          if named[i]:
            params.children.add(it)
          elif it.kind == nkIdent:
            params.children.add(it)
          else:
            error(p, "Function type parameters must be named (`name: Type`)")
        result = Node(kind: nkFunction,
          children: @[Node(kind: nkIdent, name: "function-type"), params, ret])
      else:
        if items.len != 1 or named[0]:
          error(p, "Expected a single type in parentheses")
        # `(A | B)[]`, `(A)[K]` — suffixes bind the parenthesized type.
        result = parseTSTypeSuffixes(p, items[0])
    else:
      error(p, "Unexpected token in type: '" & p.curr.value & "'")
  else:
    error(p, "Unexpected token in type")

proc parseTSUnaryType(p: var GenericParser): Node =
  ## `keyof` / `typeof` / `readonly` / `infer` / `unique` / `abstract` /
  ## constructor types. Everything else is a primary type.
  skipTSComments(p)
  if p.curr.kind == tkIdentifier and p.curr.value in
      ["keyof", "typeof", "readonly", "infer", "unique", "abstract", "new"]:
    let kw = p.curr.value
    let kwTk = p.curr
    walk p
    case kw
    of "new":
      # `new (x: T) => R`
      p.expectWalk("(")
      let params = Node(kind: nkIdentDefs)
      skipTSComments(p)
      if not (p.curr.kind == tkPunct and p.curr.value == ")"):
        # Reuse the parenthesized-type item logic via a synthetic group:
        # parse items exactly like `(…)` above by rewinding one token.
        # Simpler: parse named entries directly (construct signatures are
        # always named).
        while true:
          skipTSComments(p)
          if p.curr.kind == tkPunct and p.curr.value == "...":
            let dotsTk = p.curr
            walk p
            expectTSIdent:
              var rp = Node(kind: nkIdentDefs)
              rp.children.add(Node(kind: nkIdent, name: p.curr.value).stamp(p.curr))
              walk p
              if p.curr.kind == tkPunct and p.curr.value == ":":
                walk p
                rp.children.add(parseTSType(p))
              else:
                rp.children.add(newEmptyNode())
              params.children.add(Node(kind: nkPrefix,
                children: @[Node(kind: nkIdent, name: "...").stamp(dotsTk), rp]).stamp(dotsTk))
          elif p.curr.kind == tkIdentifier:
            let nm = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
            walk p
            var key: Node = nm
            if p.curr.kind == tkPunct and p.curr.value == "?":
              let qqTk = p.curr
              walk p
              key = Node(kind: nkPostfix,
                children: @[nm, Node(kind: nkIdent, name: "?").stamp(qqTk)]).stampFrom(nm)
            var ty = newEmptyNode()
            if p.curr.kind == tkPunct and p.curr.value == ":":
              walk p
              ty = parseTSType(p)
            params.children.add(Node(kind: nkIdentDefs, children: @[key, ty]))
          else:
            error(p, "Expected parameter in construct signature")
          skipTSComments(p)
          if p.curr.kind == tkPunct and p.curr.value == ",":
            walk p
            continue
          break
      p.expectWalk(")")
      p.expectWalk("=>")
      let ret = parseTSType(p)
      result = Node(kind: nkFunction,
        children: @[Node(kind: nkIdent, name: "construct").stamp(kwTk), params, ret]).stamp(kwTk)
    of "infer":
      expectTSIdent:
        let nm = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
        walk p
        result = Node(kind: nkPrefix,
          children: @[Node(kind: nkIdent, name: "infer").stamp(kwTk), nm]).stamp(kwTk)
        skipTSComments(p)
        if p.curr.kind == tkIdentifier and p.curr.value == "extends":
          walk p
          let constraint = parseTSType(p)
          result = Node(kind: nkInfix,
            children: @[Node(kind: nkIdent, name: "extends").stamp(kwTk),
                        result, constraint]).stamp(kwTk)
    of "typeof":
      if p.curr.kind == tkIdentifier and p.curr.value == "import" and
          p.next.kind == tkPunct and p.next.value == "(":
        walk p # consume `import`
        walk p # consume `(`
        if p.curr.kind != tkString:
          error(p, "Expected module string in `typeof import(...)`")
        let path = Node(kind: nkLitString, valStr: p.curr.value).stamp(p.curr)
        walk p
        p.expectWalk(")")
        result = Node(kind: nkCall,
          children: @[Node(kind: nkIdent, name: "import-type").stamp(kwTk), path]).stamp(kwTk)
        while p.curr.kind == tkPunct and p.curr.value == ".":
          walk p
          expectTSIdent:
            let part = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
            result = Node(kind: nkDotExpr, children: @[result, part]).stampFrom(result)
          walk p
      else:
        let operand = parseTSQualifiedName(p)
        result = Node(kind: nkPrefix,
          children: @[Node(kind: nkIdent, name: "typeof").stamp(kwTk), operand]).stamp(kwTk)
    else:
      let operand = parseTSUnaryType(p)
      result = Node(kind: nkPrefix,
        children: @[Node(kind: nkIdent, name: kw).stamp(kwTk), operand]).stamp(kwTk)
  else:
    result = parseTSPrimaryType(p)

proc parseTSIntersectionType(p: var GenericParser): Node =
  result = parseTSUnaryType(p)
  while p.curr.kind == tkPunct and p.curr.value == "&":
    let opTk = p.curr
    walk p
    skipTSComments(p)
    let rhs = parseTSUnaryType(p)
    result = Node(kind: nkInfix,
      children: @[Node(kind: nkIdent, name: "&").stamp(opTk), result, rhs]).stampFrom(result)

proc parseTSUnionType(p: var GenericParser): Node =
  result = parseTSIntersectionType(p)
  while p.curr.kind == tkPunct and p.curr.value == "|":
    let opTk = p.curr
    walk p
    skipTSComments(p)
    let rhs = parseTSIntersectionType(p)
    result = Node(kind: nkInfix,
      children: @[Node(kind: nkIdent, name: "|").stamp(opTk), result, rhs]).stampFrom(result)

proc parseTSType(p: var GenericParser): Node =
  ## Full conditional type: `T extends U ? A : B`. The `?` only belongs to
  ## a conditional after an `extends` clause, so optional markers (`x?: T`,
  ## `T?`) stay with their callers and never reach this branch.
  result = parseTSUnionType(p)
  skipTSComments(p)
  if p.curr.kind == tkIdentifier and p.curr.value == "extends":
    let extTk = p.curr
    walk p
    let extendsTy = parseTSType(p)
    skipTSComments(p)
    p.expectWalk("?")
    let trueTy = parseTSType(p)
    skipTSComments(p)
    p.expectWalk(":")
    let falseTy = parseTSType(p)
    result = Node(kind: nkCall,
      children: @[Node(kind: nkIdent, name: "conditional-type").stamp(extTk),
                  result, extendsTy, trueTy, falseTy]).stampFrom(result)

proc parseTSObjectType(p: var GenericParser): Node =
  ## `{ a?: T; readonly [k: string]: V; (x: T): R; [K in T]: V }`.
  ## Members need no separators (newlines suffice, like class bodies);
  ## optional `;` / `,` are tolerated.
  result = Node(kind: nkBlock).stamp(p.curr)
  walk p # consume `{`
  while not (p.curr.kind == tkPunct and p.curr.value == "}"):
    if p.curr.kind == tkEOF:
      error(p, "Unexpected EOF in object type")
    if p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p))
      continue
    if p.curr.kind == tkPunct and p.curr.value in [";", ","]:
      walk p
      continue
    skipTSComments(p)
    var readonly: Node = nil
    if p.curr.kind == tkIdentifier and p.curr.value == "readonly":
      readonly = Node(kind: nkIdent, name: "readonly").stamp(p.curr)
      walk p
    # Mapped type: `[K in T as U]?: V` (with optional +/- modifiers).
    if p.curr.kind == tkPunct and p.curr.value == "[":
      let mark = (lex: markLexer(p.lexer), prev: p.prev, curr: p.curr, next: p.next)
      var isMapped = false
      try:
        walk p # consume `[`
        if p.curr.kind == tkIdentifier:
          walk p
          if p.curr.kind == tkIdentifier and p.curr.value == "in":
            isMapped = true
      except OpenAstParsingError:
        discard
      restoreLexer(p.lexer, mark.lex)
      p.prev = mark.prev
      p.curr = mark.curr
      p.next = mark.next
      if isMapped:
        walk p # consume `[`
        let paramName = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
        walk p # consume name
        walk p # consume `in`
        let inTy = parseTSType(p)
        var asTy = newEmptyNode()
        skipTSComments(p)
        if p.curr.kind == tkIdentifier and p.curr.value == "as":
          walk p
          asTy = parseTSType(p)
        p.expectWalk("]")
        var optMark = newEmptyNode()
        if p.curr.kind == tkPunct and p.curr.value in ["?", "-?", "+?"]:
          optMark = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
          walk p
        p.expectWalk(":")
        let valTy = parseTSType(p)
        var mapped = Node(kind: nkStatement,
          children: @[Node(kind: nkIdent, name: "mapped"),
                      Node(kind: nkIdentDefs,
                        children: @[paramName, inTy, asTy]), optMark, valTy])
        if readonly != nil:
          mapped.children.insert(readonly, 1)
        result.children.add(mapped)
        p.walkOpt(";")
        p.walkOpt(",")
        continue
      # Index signature `[k: string]: V` vs computed member — reuse the
      # class-member lookahead shape: `[` ident `:` means an index.
      if p.next.kind == tkIdentifier:
        let mark2 = (lex: markLexer(p.lexer), prev: p.prev, curr: p.curr, next: p.next)
        var isIndex = false
        try:
          walk p
          walk p
          isIndex = p.curr.kind == tkPunct and p.curr.value == ":"
        except OpenAstParsingError:
          discard
        restoreLexer(p.lexer, mark2.lex)
        p.prev = mark2.prev
        p.curr = mark2.curr
        p.next = mark2.next
        if isIndex:
          walk p # consume `[`
          let nm = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
          walk p
          p.expectWalk(":")
          let keyTy = parseTSType(p)
          p.expectWalk("]")
          p.expectWalk(":")
          let valTy = parseTSType(p)
          var idx = Node(kind: nkStatement,
            children: @[Node(kind: nkIdent, name: "index"),
                        Node(kind: nkIdentDefs, children: @[nm, keyTy]), valTy])
          if readonly != nil:
            idx.children.insert(readonly, 1)
          result.children.add(idx)
          p.walkOpt(";")
          p.walkOpt(",")
          continue
    # Call / construct signature, optionally generic: `<T>(x: T): R`.
    if p.curr.kind == tkPunct and p.curr.value == "(" or
        (p.curr.kind == tkPunct and p.curr.value == "<"):
      var sigGenerics = newEmptyNode()
      if p.curr.kind == tkPunct and p.curr.value == "<":
        sigGenerics = parseTSGenericParams(p)
      let params = parseTSParams(p)
      var ret = newEmptyNode()
      if p.curr.kind == tkPunct and p.curr.value == ":":
        walk p
        ret = parseTSType(p)
      result.children.add(Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "call"), sigGenerics, params, ret]))
      p.walkOpt(";")
      p.walkOpt(",")
      continue
    if p.curr.kind == tkIdentifier and p.curr.value == "new" and
        p.next.kind == tkPunct and p.next.value in ["(", "<"]:
      walk p
      var ctorGenerics = newEmptyNode()
      if p.curr.kind == tkPunct and p.curr.value == "<":
        ctorGenerics = parseTSGenericParams(p)
      let params = parseTSParams(p)
      var ret = newEmptyNode()
      if p.curr.kind == tkPunct and p.curr.value == ":":
        walk p
        ret = parseTSType(p)
      result.children.add(Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "construct"), ctorGenerics, params, ret]))
      p.walkOpt(";")
      p.walkOpt(",")
      continue
    # Property or method: key [`?`] [generics] [(params) | : type].
    var key: Node
    if p.curr.kind == tkString:
      key = Node(kind: nkLitString, valStr: p.curr.value).stamp(p.curr)
      walk p
    elif p.curr.kind == tkInt:
      key = Node(kind: nkLitInt, valInt: parseInt(p.curr.value)).stamp(p.curr)
      walk p
    elif p.curr.kind == tkPunct and p.curr.value == "[":
      let openTk = p.curr
      walk p
      let e = parseExpression(p, 0)
      p.expectWalk("]")
      key = Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "computed").stamp(openTk), e]).stamp(openTk)
    else:
      expectTSIdent:
        key = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
      walk p
    if p.curr.kind == tkPunct and p.curr.value == "?":
      let qTk = p.curr
      walk p
      key = Node(kind: nkPostfix,
        children: @[key, Node(kind: nkIdent, name: "?").stamp(qTk)]).stampFrom(key)
    if p.curr.kind == tkPunct and p.curr.value == "<":
      let generics = parseTSGenericParams(p)
      p.expectWalk("(")
      let params = parseTSParamsRest(p)
      var ret = newEmptyNode()
      if p.curr.kind == tkPunct and p.curr.value == ":":
        walk p
        ret = parseTSType(p)
      let fn = Node(kind: nkFunction,
        children: @[generics, params, ret])
      result.children.add(Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "method"), key, fn]))
      p.walkOpt(";")
      p.walkOpt(",")
      continue
    if p.curr.kind == tkPunct and p.curr.value == "(":
      let params = parseTSParams(p)
      var ret = newEmptyNode()
      if p.curr.kind == tkPunct and p.curr.value == ":":
        walk p
        ret = parseTSType(p)
      let fn = Node(kind: nkFunction,
        children: @[newEmptyNode(), params, ret])
      result.children.add(Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "method"), key, fn]))
      p.walkOpt(";")
      p.walkOpt(",")
      continue
    # Property.
    var ty = newEmptyNode()
    if p.curr.kind == tkPunct and p.curr.value == ":":
      walk p
      ty = parseTSType(p)
    var member = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "property"), key, ty])
    if readonly != nil:
      member.children.insert(readonly, 1)
    result.children.add(member)
    p.walkOpt(";")
    p.walkOpt(",")
  walk p # consume `}`

proc parseTSTupleType(p: var GenericParser): Node =
  ## `[A, label: B, C?, ...D]`.
  result = Node(kind: nkArrayLit).stamp(p.curr)
  walk p # consume `[`
  while not (p.curr.kind == tkPunct and p.curr.value == "]"):
    if p.curr.kind == tkEOF:
      error(p, "Unexpected EOF in tuple type")
    if p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p))
      continue
    if p.curr.kind == tkPunct and p.curr.value == ",":
      result.children.add(newEmptyNode())
      walk p
      continue
    skipTSComments(p)
    if p.curr.kind == tkPunct and p.curr.value == "...":
      let dotsTk = p.curr
      walk p
      if p.curr.kind == tkIdentifier and p.next.kind == tkPunct and
          p.next.value == ":":
        let nm = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
        walk p
        walk p # consume `:`
        let ty = parseTSType(p)
        result.children.add(Node(kind: nkPrefix,
          children: @[Node(kind: nkIdent, name: "...").stamp(dotsTk),
                      Node(kind: nkIdentDefs,
                        children: @[nm, ty, newEmptyNode()])]).stamp(dotsTk))
      else:
        let ty = parseTSType(p)
        result.children.add(Node(kind: nkCall,
          children: @[Node(kind: nkIdent, name: "spread").stamp(dotsTk), ty]).stamp(dotsTk))
    elif p.curr.kind == tkIdentifier and p.next.kind == tkPunct and
        p.next.value == ":":
      let nm = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
      walk p
      walk p # consume `:`
      result.children.add(Node(kind: nkColonExpr,
        children: @[nm, parseTSType(p)]).stampFrom(nm))
    else:
      # `second?: number` needs one more token of lookahead than
      # `curr`/`next` provide: try the labeled-optional shape, else
      # rewind and parse a plain (possibly optional) element type.
      var item: Node = nil
      if p.curr.kind == tkIdentifier and p.next.kind == tkPunct and
          p.next.value == "?":
        let mark = (lex: markLexer(p.lexer), prev: p.prev, curr: p.curr, next: p.next)
        let slen = p.stripSpans.len
        let nm0 = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
        walk p
        walk p
        if p.curr.kind == tkPunct and p.curr.value == ":":
          let qTk = p.prev # the `?` just consumed
          walk p
          let ty = parseTSType(p)
          let onm = Node(kind: nkPostfix,
            children: @[nm0, Node(kind: nkIdent, name: "?").stamp(qTk)]).stampFrom(nm0)
          item = Node(kind: nkColonExpr, children: @[onm, ty]).stampFrom(nm0)
        else:
          p.stripSpans.setLen(slen)
          restoreLexer(p.lexer, mark.lex)
          p.prev = mark.prev
          p.curr = mark.curr
          p.next = mark.next
      if item == nil:
        item = parseTSType(p)
        if p.curr.kind == tkPunct and p.curr.value == "?":
          let qTk = p.curr
          walk p
          item = Node(kind: nkPostfix,
            children: @[item, Node(kind: nkIdent, name: "?").stamp(qTk)]).stampFrom(item)
      result.children.add(item)
    p.walkOpt(",")
  walk p # consume `]`
  result = parseTSTypeSuffixes(p, result)

proc parseTSGenericParams(p: var GenericParser): Node =
  ## Called with `curr == "<"`. Parses `<T, U extends C = D>` into
  ## `nkIdentDefs` of `nkIdentDefs [name, constraintOrEmpty, defaultOrEmpty]`.
  result = Node(kind: nkIdentDefs).stamp(p.curr)
  let eraseFrom = p.markPos()
  walk p # consume `<`
  skipTSComments(p)
  var closerEnd = -1
  while true:
    if p.curr.kind == tkEOF:
      error(p, "Unexpected EOF in generic parameters")
    if p.curr.kind != tkIdentifier:
      error(p, "Expected type parameter name")
    let nm = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
    walk p
    var constraint = newEmptyNode()
    var default = newEmptyNode()
    skipTSComments(p)
    if p.curr.kind == tkIdentifier and p.curr.value == "extends":
      walk p
      constraint = parseTSType(p)
      skipTSComments(p)
    if p.curr.kind == tkPunct and p.curr.value == "=":
      walk p
      default = parseTSType(p)
      skipTSComments(p)
    result.children.add(Node(kind: nkIdentDefs,
      children: @[nm, constraint, default]))
    if p.curr.kind == tkPunct and p.curr.value == ",":
      walk p
      skipTSComments(p)
    elif p.curr.kind == tkPunct and p.curr.value in [">", ">>", ">>>"]:
      closerEnd = consumeTypeCloser(p)
      break
    else:
      error(p, "Expected ',' or '>' in generic parameters")
  p.stripSince(eraseFrom, upto = closerEnd)

proc parseTSParamsRest(p: var GenericParser): Node =
  ## Parse function parameters after the opening `(` was consumed.
  ## Entries are plain idents when bare, else
  ## `nkIdentDefs [nameOrPattern, typeOrEmpty, defaultOrEmpty]`; entries
  ## with accessibility / `readonly` / decorator modifiers become
  ## `nkStatement [param, flags, nameOrPattern, typeOrEmpty, defaultOrEmpty]`.
  result = Node(kind: nkIdentDefs)
  while not (p.curr.kind == tkPunct and p.curr.value == ")"):
    if p.curr.kind == tkEOF:
      error(p, "Unexpected EOF in parameters")
    if p.curr.kind in {tkComment, tkDocComment}:
      discard parseCommentGeneric(p)
      continue
    # `this: Type` parameters carry no runtime value: erase the whole
    # entry including a following comma. (`this` takes no modifiers, so
    # this check runs before the flags loop.)
    if p.curr.kind == tkIdentifier and p.curr.value == "this" and
        p.next.kind == tkPunct and p.next.value == ":":
      let thisFrom = p.markPos()
      walk p # consume `this`
      walk p # consume `:`
      discard parseTSType(p)
      skipTSComments(p)
      if p.curr.kind == tkPunct and p.curr.value == ",":
        walk p
      p.stripSince(thisFrom)
      continue
    var flags: seq[Node] = @[]
    while p.curr.kind == tkPunct and p.curr.value == "@":
      for d in parseTSDecorators(p):
        flags.add(d)
    while p.curr.kind == tkIdentifier and p.curr.value in
        ["public", "private", "protected", "readonly", "override"]:
      flags.add(Node(kind: nkIdent, name: p.curr.value).stamp(p.curr))
      p.stripCurrPast()
    if p.curr.kind == tkPunct and p.curr.value == "...":
      let dotsTk = p.curr
      walk p
      var inner: Node
      if p.curr.kind == tkPunct and p.curr.value in ["{", "["]:
        let pattern = parseExpression(p)
        var ty = newEmptyNode()
        if p.curr.kind == tkPunct and p.curr.value == ":":
          let tstart = p.markPos()
          walk p
          ty = parseTSType(p)
          p.stripSince(tstart)
        inner = Node(kind: nkIdentDefs, children: @[pattern, ty, newEmptyNode()])
      else:
        expectTSIdent:
          let nm = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
          walk p
          var ty = newEmptyNode()
          if p.curr.kind == tkPunct and p.curr.value == ":":
            let tstart = p.markPos()
            walk p
            ty = parseTSType(p)
            p.stripSince(tstart)
          inner = Node(kind: nkIdentDefs, children: @[nm, ty, newEmptyNode()])
      result.children.add(Node(kind: nkPrefix,
        children: @[Node(kind: nkIdent, name: "...").stamp(dotsTk), inner]).stamp(dotsTk))
      p.walkOpt(",")
      continue
    if p.curr.kind == tkPunct and p.curr.value in ["{", "["]:
      let pattern = parseExpression(p)
      var ty = newEmptyNode()
      if p.curr.kind == tkPunct and p.curr.value == ":":
        let tstart = p.markPos()
        walk p
        ty = parseTSType(p)
        p.stripSince(tstart)
      var default = newEmptyNode()
      if p.curr.kind == tkPunct and p.curr.value == "=":
        walk p
        default = parseExpression(p)
      let entry = Node(kind: nkIdentDefs, children: @[pattern, ty, default])
      if flags.len > 0:
        result.children.add(Node(kind: nkStatement,
          children: @[Node(kind: nkIdent, name: "param")] & flags & @[entry]))
      else:
        result.children.add(entry)
      p.walkOpt(",")
      continue
    if p.curr.kind != tkIdentifier:
      error(p, "Expected parameter name")
    var nm: Node = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
    walk p
    if p.curr.kind == tkPunct and p.curr.value == "?":
      p.stripCurr()
      let qTk = p.curr
      walk p
      nm = Node(kind: nkPostfix,
        children: @[nm, Node(kind: nkIdent, name: "?").stamp(qTk)]).stampFrom(nm)
    var ty = newEmptyNode()
    if p.curr.kind == tkPunct and p.curr.value == ":":
      let tstart = p.markPos()
      walk p
      ty = parseTSType(p)
      p.stripSince(tstart)
    var default = newEmptyNode()
    if p.curr.kind == tkPunct and p.curr.value == "=":
      walk p
      default = parseExpression(p)
    if ty.kind == nkEmpty and default.kind == nkEmpty and flags.len == 0:
      result.children.add(nm)
    elif flags.len > 0:
      result.children.add(Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "param")] & flags &
                    @[nm, ty, default]))
    else:
      result.children.add(Node(kind: nkIdentDefs, children: @[nm, ty, default]))
    p.walkOpt(",")
  p.expectWalk(")")

proc parseTSParams(p: var GenericParser): Node =
  p.expectWalk("(")
  result = parseTSParamsRest(p)

proc parseTSDecorators(p: var GenericParser): seq[Node] =
  ## One or more `@expr` decorators. Each is `nkPrefix [@, target]` where
  ## the target is a qualified name with an optional call. Decorators have
  ## no lowering (v1): record an unsupported span and let the consumer
  ## raise with position.
  result = @[]
  let decFrom = p.markPos()
  var sawDec = false
  while p.curr.kind == tkPunct and p.curr.value == "@":
    sawDec = true
    let atTk = p.curr
    walk p # consume `@`
    skipTSComments(p)
    var target = parseTSQualifiedName(p)
    if p.curr.kind == tkPunct and p.curr.value == "<":
      let args = parseTSGenericArgs(p)
      target = Node(kind: nkBracketExpr, children: @[target] & args).stampFrom(target)
    if p.curr.kind == tkPunct and p.curr.value == "(":
      let openTk = p.curr
      walk p
      let call = Node(kind: nkCall, children: @[target]).stamp(openTk)
      while not (p.curr.kind == tkPunct and p.curr.value == ")"):
        if p.curr.kind == tkEOF:
          error(p, "Unexpected EOF in decorator arguments")
        if p.curr.kind in {tkComment, tkDocComment}:
          call.children.add(parseCommentGeneric(p))
          continue
        if p.curr.kind == tkPunct and p.curr.value == "...":
          let dotsTk = p.curr
          walk p
          call.children.add(Node(kind: nkCall,
            children: @[Node(kind: nkIdent, name: "spread").stamp(dotsTk),
                        parseExpression(p, 0)]).stamp(dotsTk))
        else:
          call.children.add(parseExpression(p, 0))
        p.walkOpt(",")
      p.expectWalk(")")
      target = call
    result.add(Node(kind: nkPrefix,
      children: @[Node(kind: nkIdent, name: "@").stamp(atTk), target]).stamp(atTk))
    skipTSComments(p)
  if sawDec:
    p.stripError(decFrom,
      "Decorators are not supported (TypeScript v1: remove them or use plain JavaScript)")

proc parseTSReturnType(p: var GenericParser): Node =
  ## Assertion signatures (`: asserts x is T`) or plain types after `:`.
  result = newEmptyNode()
  if p.curr.kind == tkPunct and p.curr.value == ":":
    let tstart = p.markPos()
    walk p
    skipTSComments(p)
    if p.curr.kind == tkIdentifier and p.curr.value == "asserts":
      let aTk = p.curr
      walk p
      if p.curr.kind == tkIdentifier and
          p.next.kind == tkIdentifier and p.next.value == "is":
        let nm = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
        walk p
        walk p # consume `is`
        let ty = parseTSType(p)
        result = Node(kind: nkStatement,
          children: @[Node(kind: nkIdent, name: "asserts").stamp(aTk), nm, ty]).stamp(aTk)
      elif p.curr.kind == tkIdentifier:
        let nm = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
        walk p
        result = Node(kind: nkStatement,
          children: @[Node(kind: nkIdent, name: "asserts").stamp(aTk),
                      nm, newEmptyNode()]).stamp(aTk)
      else:
        result = Node(kind: nkIdent, name: "asserts").stamp(aTk)
    else:
      result = parseTSType(p)
    p.stripSince(tstart)

proc isOverloadImplAhead(p: var GenericParser, name: string): bool =
  ## Speculative check: does a same-name function *implementation* (a body
  ## block) follow the current position? Consecutive overload signatures
  ## are skipped over; `export` / `default` / `async` prefixes are allowed
  ## per declaration. Restores all parser/lexer state either way; drops
  ## trial spans.
  let mark = (lex: markLexer(p.lexer), prev: p.prev, curr: p.curr, next: p.next)
  let slen = p.stripSpans.len
  template restore() =
    restoreLexer(p.lexer, mark.lex)
    p.prev = mark.prev
    p.curr = mark.curr
    p.next = mark.next
    p.stripSpans.setLen(slen)
  try:
    while true:
      while p.curr.kind in {tkComment, tkDocComment}:
        walk p
      while p.curr.kind == tkIdentifier and p.curr.value in ["export", "default"]:
        walk p
        while p.curr.kind in {tkComment, tkDocComment}:
          walk p
      if p.curr.kind == tkIdentifier and p.curr.value == "async" and
          p.next.kind == tkIdentifier and p.next.value == "function":
        walk p
      if not (p.curr.kind == tkIdentifier and p.curr.value == "function"):
        restore()
        return false
      walk p
      if p.curr.kind == tkPunct and p.curr.value == "*":
        walk p
      if p.curr.kind == tkIdentifier:
        if p.curr.value != name:
          restore()
          return false
        walk p
      elif name.len > 0:
        restore()
        return false
      if p.curr.kind == tkPunct and p.curr.value == "<":
        discard parseTSGenericParams(p)
      if not (p.curr.kind == tkPunct and p.curr.value == "("):
        restore()
        return false
      discard parseTSParams(p)
      discard parseTSReturnType(p)
      while p.curr.kind in {tkComment, tkDocComment}:
        walk p
      if p.curr.kind == tkPunct and p.curr.value == "{":
        result = true
        break
      # Another bodiless signature: keep scanning for the implementation.
      if p.curr.kind == tkPunct and p.curr.value == ";":
        walk p
  except OpenAstParsingError:
    result = false
  restore()

proc parseTSFunctionDecl(p: var GenericParser, keyword: string,
    fnFrom = -1): Node =
  ## Shared tail for `function` declarations (and the `function` half of
  ## `async function` / `export default function`). Mirrors
  ## `js.registerFunction`'s seven slots, with `<>` generics and overloads.
  ## `fnFrom` is the byte offset of the declaration start (the `function`
  ## or `async` keyword); overload signatures are erased, lone
  ## implementation-less declarations recorded as errors.
  let declFrom = if fnFrom >= 0: fnFrom else: p.markPos()
  result = Node(kind: nkFunction)
  result.children.add(Node(kind: nkIdent, name: keyword))
  walk p # consume `function`
  skipTSComments(p)
  if p.curr.kind == tkPunct and p.curr.value == "*":
    walk p
    result.children.add(Node(kind: nkIdent, name: "*"))
  else:
    result.children.add(newEmptyNode())
  skipTSComments(p)
  if p.curr.kind == tkIdentifier:
    result.children.add(Node(kind: nkIdent, name: p.curr.value).stamp(p.curr))
    walk p
  else:
    result.children.add(newEmptyNode())
  skipTSComments(p)
  if p.curr.kind == tkPunct and p.curr.value == "<":
    result.children.add(parseTSGenericParams(p))
  else:
    result.children.add(newEmptyNode())
  skipTSComments(p)
  result.children.add(parseTSParams(p))
  skipTSComments(p)
  result.children.add(parseTSReturnType(p))
  skipTSComments(p)
  if p.curr.kind == tkPunct and p.curr.value == "{":
    result.children.add(parseBlock(p))
  elif p.curr.kind == tkPunct and p.curr.value == ";":
    walk p
    result.children.add(newEmptyNode())
    # Overload signature (dropped) or missing implementation (error).
    var fnName = ""
    if result.children.len > 2 and result.children[2].kind == nkIdent:
      fnName = result.children[2].name
    if isOverloadImplAhead(p, fnName):
      p.stripSince(declFrom)
    else:
      p.stripError(declFrom,
        "Function '" & (if fnName.len > 0: fnName else: "<anonymous>") &
        "' lacks an implementation (overload signatures must be followed by an implementation)")
  else:
    result.children.add(newEmptyNode())
    var fnName = ""
    if result.children.len > 2 and result.children[2].kind == nkIdent:
      fnName = result.children[2].name
    if isOverloadImplAhead(p, fnName):
      p.stripSince(declFrom)
    else:
      p.stripError(declFrom,
        "Function '" & (if fnName.len > 0: fnName else: "<anonymous>") &
        "' lacks an implementation (overload signatures must be followed by an implementation)")

proc parseTSObjectLiteral(p: var GenericParser, minPrec: int = 0): Node =
  ## Object literals with typed methods: `{ m<T>(x: T): R { … }, async
  ## m() {}, *gen() {}, ...spread, key: value, shorthand }`. Mirrors the
  ## engine's `parseObjectLiteral` shapes, but method functions carry
  ## `[flags..., generics, params, return, body]` like TS class methods.
  let openTk = p.curr
  result = Node(kind: nkBlock).stamp(openTk)
  walk p # consume `{`
  while not (p.curr.kind == tkPunct and p.curr.value == "}"):
    if p.curr.kind == tkEOF:
      error(p, "Unexpected EOF in object literal")
    if p.curr.kind in {tkComment, tkDocComment}:
      result.children.add(parseCommentGeneric(p))
      continue
    if p.curr.kind == tkPunct and p.curr.value == "...":
      let spreadTk = p.curr
      walk p
      result.children.add(Node(kind: nkCall,
        children: @[Node(kind: nkIdent, name: "spread").stamp(spreadTk),
                    parseExpression(p)]).stamp(spreadTk))
      p.walkOpt(",")
      continue
    var isGenerator = false
    if p.curr.kind == tkPunct and p.curr.value == "*":
      walk p
      isGenerator = true
    var isAsync = false
    if p.curr.kind == tkIdentifier and p.curr.value == "async" and
        p.next.kind != tkPunct:
      # `async m() {}` — but not shorthand `{ async }` (next is `,`/`}`).
      isAsync = true
      walk p
    let keyTk = p.curr
    let key =
      if p.curr.kind == tkPunct and p.curr.value == "[":
        walk p
        let k = parseExpression(p)
        p.expectWalk("]")
        Node(kind: nkStatement,
          children: @[Node(kind: nkIdent, name: "computed").stamp(keyTk), k]).stamp(keyTk)
      elif p.curr.kind == tkString:
        let n = Node(kind: nkLitString, valStr: p.curr.value).stamp(p.curr)
        walk p
        n
      elif p.curr.kind == tkInt:
        let n = Node(kind: nkLitInt, valInt: parseInt(p.curr.value)).stamp(p.curr)
        walk p
        n
      else:
        let n = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
        walk p
        n
    if p.curr.kind == tkPunct and p.curr.value == "<":
      let generics = parseTSGenericParams(p)
      p.expectWalk("(")
      let params = parseTSParamsRest(p)
      var ret = newEmptyNode()
      if p.curr.kind == tkPunct and p.curr.value == ":":
        walk p
        ret = parseTSType(p)
      let fnBody = parseBlock(p)
      var flags: seq[Node] = @[]
      if isAsync:
        flags.add(Node(kind: nkIdent, name: "async").stamp(keyTk))
      if isGenerator:
        flags.add(Node(kind: nkIdent, name: "*").stamp(keyTk))
      result.children.add(Node(kind: nkColonExpr,
        children: @[key, Node(kind: nkFunction,
          children: flags & @[generics, params, ret, fnBody]).stampFrom(key)]).stampFrom(key))
    elif p.curr.kind == tkPunct and p.curr.value == "(":
      walk p
      let params = parseTSParamsRest(p)
      var ret = newEmptyNode()
      if p.curr.kind == tkPunct and p.curr.value == ":":
        walk p
        ret = parseTSType(p)
      let fnBody = parseBlock(p)
      var flags: seq[Node] = @[]
      if isAsync:
        flags.add(Node(kind: nkIdent, name: "async").stamp(keyTk))
      if isGenerator:
        flags.add(Node(kind: nkIdent, name: "*").stamp(keyTk))
      result.children.add(Node(kind: nkColonExpr,
        children: @[key, Node(kind: nkFunction,
          children: flags & @[newEmptyNode(), params, ret, fnBody]).stampFrom(key)]).stampFrom(key))
    elif p.curr.kind == tkPunct and p.curr.value in [",", "}"]:
      let val = if key.kind == nkIdent: Node(kind: nkIdent, name: key.name).stampFrom(key)
                else: key
      result.children.add(Node(kind: nkColonExpr,
        children: @[key, val]).stampFrom(key))
    elif p.curr.kind == tkPunct and p.curr.value == "=":
      let eqTk = p.curr
      walk p
      result.children.add(Node(kind: nkColonExpr,
        children: @[key, parseExpression(p),
                    Node(kind: nkIdent, name: "=").stamp(eqTk)]).stampFrom(key))
    else:
      if p.curr.kind == tkPunct and p.curr.value == "=>":
        walk p
      else:
        p.expectWalk(":")
      result.children.add(Node(kind: nkColonExpr,
        children: @[key, parseExpression(p)]).stampFrom(key))
    p.walkOpt(",")
  p.expectWalk("}")

proc isGenericCallAhead(p: var GenericParser): bool =
  ## Speculative check: does `curr == "<"` open generic arguments followed
  ## by a call paren (`f<T>(x)`)? Restores all parser/lexer state either way.
  let mark = (lex: markLexer(p.lexer), prev: p.prev, curr: p.curr, next: p.next)
  let slen = p.stripSpans.len
  template restore() =
    restoreLexer(p.lexer, mark.lex)
    p.prev = mark.prev
    p.curr = mark.curr
    p.next = mark.next
  try:
    discard parseTSGenericArgs(p)
    skipTSComments(p)
    result = p.curr.kind == tkPunct and p.curr.value == "("
  except OpenAstParsingError:
    result = false
  # Speculation always rewinds: drop any spans the trial parse recorded.
  p.stripSpans.setLen(slen)
  restore()

proc tsHandlers*(p: var GenericParser) =
  ## Register TypeScript statement, prefix and expression handlers on top
  ## of the JavaScript ones.
  jsHandlers(p)
  p.stripPostfix.incl("!")
  p.braceHandler = parseTSObjectLiteral

  exprHandler p, "infix:as":
    let opTk = p.curr
    let eraseFrom = p.markPos()
    walk p # consume `as`
    let rhs = parseTSType(p)
    p.stripSince(eraseFrom)
    result = Node(kind: nkInfix,
      children: @[Node(kind: nkIdent, name: "as").stamp(opTk), lhs, rhs]).stampFrom(lhs)

  exprHandler p, "infix:satisfies":
    let opTk = p.curr
    let eraseFrom = p.markPos()
    walk p # consume `satisfies`
    let rhs = parseTSType(p)
    p.stripSince(eraseFrom)
    result = Node(kind: nkInfix,
      children: @[Node(kind: nkIdent, name: "satisfies").stamp(opTk),
                  lhs, rhs]).stampFrom(lhs)

  exprHandler p, "infix:<":
    ## `f<T>(x)` vs `a < b`: commit to generic arguments only when they
    ## parse cleanly and a call paren follows; otherwise decline (nil) so
    ## the engine takes the default comparison path without consuming.
    if not isGenericCallAhead(p):
      return nil
    let args = parseTSGenericArgs(p)
    result = Node(kind: nkBracketExpr, children: @[lhs] & args).stampFrom(lhs)

  prefixHandler p, "@":
    let decs = parseTSDecorators(p)
    skipTSComments(p)
    if p.curr.kind == tkEOF or
        (p.curr.kind == tkPunct and p.curr.value in ["}", ")", "]", ";"]):
      error(p, "Expected declaration after decorator")
    let decl = parseStatement(p)
    let decBlock = Node(kind: nkBlock, children: decs)
    result = Node(kind: nkPragmaBlock, children: @[decBlock, decl]).stampFrom(decl)

  prefixHandler p, "<":
    ## Expression-start `<`: generic arrow params or an angle-bracket
    ## assertion. Comparisons never start an expression, so no speculation
    ## is needed — but `.tsx` forbids assertions (they clash with JSX),
    ## mirroring tsc.
    let ltTk = p.curr
    let eraseFrom = p.markPos()
    var closerEnd = -1
    walk p # consume `<`
    skipTSComments(p)
    if p.curr.kind == tkPunct and p.curr.value == ">":
      error(p, "Expected type parameter or type after '<'")
    # First element: an identifier either way (param name or type name).
    if p.curr.kind != tkIdentifier:
      error(p, "Expected identifier after '<'")
    let first = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
    walk p
    skipTSComments(p)
    if p.curr.kind == tkPunct and p.curr.value == "<":
      # `<Foo<Bar>>x` — assertion over a generic reference. Arrows never
      # have `<` directly after the first name.
      if p.isTSX:
        error(p, "Angle-bracket assertions are not allowed in .tsx files; use `as`")
      var refNode: Node = first
      let args = parseTSGenericArgs(p)
      refNode = Node(kind: nkBracketExpr, children: @[refNode] & args).stampFrom(first)
      while p.curr.kind == tkPunct and p.curr.value == ".":
        walk p
        expectTSIdent:
          let part = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
          refNode = Node(kind: nkDotExpr, children: @[refNode, part]).stampFrom(refNode)
        walk p
        if p.curr.kind == tkPunct and p.curr.value == "<":
          let more = parseTSGenericArgs(p)
          refNode = Node(kind: nkBracketExpr, children: @[refNode] & more).stampFrom(refNode)
      p.expectWalk(">")
      p.stripSince(eraseFrom)
      let operand = parseExpression(p, 13)
      return Node(kind: nkCast, children: @[refNode, operand]).stamp(ltTk)
    # Generic parameter list (each may carry `extends` / `=`).
    let generics = Node(kind: nkIdentDefs)
    var firstConstraint = newEmptyNode()
    var firstDefault = newEmptyNode()
    if p.curr.kind == tkIdentifier and p.curr.value == "extends":
      walk p
      firstConstraint = parseTSType(p)
      skipTSComments(p)
    if p.curr.kind == tkPunct and p.curr.value == "=":
      walk p
      firstDefault = parseTSType(p)
      skipTSComments(p)
    generics.children.add(Node(kind: nkIdentDefs,
      children: @[first, firstConstraint, firstDefault]))
    var multi = false
    while p.curr.kind == tkPunct and p.curr.value == ",":
      multi = true
      walk p
      skipTSComments(p)
      if p.curr.kind != tkIdentifier:
        error(p, "Expected type parameter name")
      let nm = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
      walk p
      var constraint = newEmptyNode()
      var default = newEmptyNode()
      skipTSComments(p)
      if p.curr.kind == tkIdentifier and p.curr.value == "extends":
        walk p
        constraint = parseTSType(p)
        skipTSComments(p)
      if p.curr.kind == tkPunct and p.curr.value == "=":
        walk p
        default = parseTSType(p)
        skipTSComments(p)
      generics.children.add(Node(kind: nkIdentDefs,
        children: @[nm, constraint, default]))
    if p.curr.kind == tkPunct and p.curr.value in [">", ">>", ">>>"]:
      closerEnd = consumeTypeCloser(p)
    else:
      error(p, "Expected '>' after generic parameters")
    skipTSComments(p)
    if p.curr.kind == tkPunct and p.curr.value == "(":
      # Ambiguous: generic arrow `<T>(x: T): R => body` or assertion
      # over a parenthesized operand `<T>(x)`. Try the arrow first;
      # without `=>` it is an assertion (mirroring tsc).
      let mark = (lex: markLexer(p.lexer), prev: p.prev, curr: p.curr, next: p.next)
      let slen = p.stripSpans.len
      var arrowFn: Node = nil
      try:
        let params = parseTSParams(p)
        let ret = parseTSReturnType(p)
        skipTSComments(p)
        if p.curr.kind == tkPunct and p.curr.value == "=>":
          walk p # consume `=>`
          skipTSComments(p)
          let body = if p.curr.kind == tkPunct and p.curr.value == "{":
                       parseBlock(p)
                     else:
                       parseExpression(p, 0)
          arrowFn = Node(kind: nkFunction,
            children: @[generics, params, ret, body]).stamp(ltTk)
      except OpenAstParsingError:
        discard
      if arrowFn != nil:
        p.stripSince(eraseFrom, upto = closerEnd)
        return arrowFn
      restoreLexer(p.lexer, mark.lex)
      p.prev = mark.prev
      p.curr = mark.curr
      p.next = mark.next
      p.stripSpans.setLen(slen)
    # Otherwise it was an assertion `<T>x` (single plain parameter only).
    if multi or firstConstraint.kind != nkEmpty or firstDefault.kind != nkEmpty:
      error(p, "Expected '(' and '=>' after generic parameters")
    if p.isTSX:
      error(p, "Angle-bracket assertions are not allowed in .tsx files; use `as`")
    p.stripSince(eraseFrom, upto = closerEnd)
    let operand = parseExpression(p, 13)
    return Node(kind: nkCast, children: @[first, operand]).stamp(ltTk)

  prefixHandler p, "(":
    ## Typed arrow parameters: `(x: T): R => body`. Speculative: parse
    ## as TS params and commit only on `)` + optional return type +
    ## `=>`; otherwise rewind for the default group parse. (Plain
    ## untyped arrows never take this path: `parseTSParamsRest` rejects
    ## their contents and the group parse runs untouched.)
    let mark = (lex: markLexer(p.lexer), prev: p.prev, curr: p.curr, next: p.next)
    let slen = p.stripSpans.len
    var arrowFn: Node = nil
    try:
      walk p # consume `(`
      let params = parseTSParamsRest(p)
      var ret = newEmptyNode()
      if p.curr.kind == tkPunct and p.curr.value == ":":
        ret = parseTSReturnType(p)
      skipTSComments(p)
      if p.curr.kind == tkPunct and p.curr.value == "=>":
        walk p # consume `=>`
        skipTSComments(p)
        let body = if p.curr.kind == tkPunct and p.curr.value == "{":
                     parseBlock(p)
                   else:
                     parseExpression(p, 0)
        arrowFn = Node(kind: nkFunction,
          children: @[newEmptyNode(), params, ret, body])
    except OpenAstParsingError:
      discard
    if arrowFn != nil:
      return arrowFn
    restoreLexer(p.lexer, mark.lex)
    p.prev = mark.prev
    p.curr = mark.curr
    p.next = mark.next
    p.stripSpans.setLen(slen)
    return parseGroupExpr(p)

  prefixHandler p, "new":
    ## `new` with optional generic arguments. `new Foo < bar` stays a
    ## comparison: type arguments commit only on a clean parse, matching
    ## the `infix:<` rule.
    let newTk = p.curr
    walk p # consume `new`
    skipTSComments(p)
    var base: Node
    if p.curr.kind == tkPunct and p.curr.value == "(":
      base = parseGroupExpr(p)
    else:
      base = parseTSQualifiedName(p)
      skipTSComments(p)
      if p.curr.kind == tkPunct and p.curr.value == "<":
        let mark = (lex: markLexer(p.lexer), prev: p.prev, curr: p.curr, next: p.next)
        let slen = p.stripSpans.len
        var args: seq[Node] = @[]
        var ok = false
        try:
          args = parseTSGenericArgs(p)
          ok = true
        except OpenAstParsingError:
          ok = false
        if not ok:
          p.stripSpans.setLen(slen)
          restoreLexer(p.lexer, mark.lex)
          p.prev = mark.prev
          p.curr = mark.curr
          p.next = mark.next
        else:
          base = Node(kind: nkBracketExpr, children: @[base] & args).stampFrom(base)
    if p.curr.kind == tkPunct and p.curr.value == "(":
      let openTk = p.curr
      walk p
      let call = Node(kind: nkCall, children: @[base]).stamp(openTk)
      while not (p.curr.kind == tkPunct and p.curr.value == ")"):
        if p.curr.kind == tkEOF:
          error(p, "Unexpected EOF in new expression")
        if p.curr.kind in {tkComment, tkDocComment}:
          call.children.add(parseCommentGeneric(p))
          continue
        if p.curr.kind == tkPunct and p.curr.value == "...":
          let dotsTk = p.curr
          walk p
          call.children.add(Node(kind: nkCall,
            children: @[Node(kind: nkIdent, name: "spread").stamp(dotsTk),
                        parseExpression(p, 0)]).stamp(dotsTk))
        else:
          call.children.add(parseExpression(p, 0))
        p.walkOpt(",")
      p.expectWalk(")")
      result = Node(kind: nkPrefix,
        children: @[Node(kind: nkIdent, name: "new").stamp(newTk), call]).stamp(newTk)
    else:
      result = Node(kind: nkPrefix,
        children: @[Node(kind: nkIdent, name: "new").stamp(newTk), base]).stamp(newTk)

  stmtHandler p, "try_js":
    ## Same as the JS `try`/`catch`/`finally`, plus an optional catch
    ## parameter annotation (`catch (e: any)`, the only forms tsc allows).
    walk p # consume 'try'
    if not (p.curr.kind == tkPunct and p.curr.value == "{"):
      error(p, "Expected '{' after 'try'")
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "try"))
    result.children.add(parseBlock(p))
    while true:
      while p.curr.kind in {tkComment, tkDocComment}:
        discard parseCommentGeneric(p)
      if p.curr.kind == tkIdentifier and p.curr.value == "catch":
        walk p
        var param = newEmptyNode()
        if p.curr.kind == tkPunct and p.curr.value == "(":
          walk p
          if p.curr.kind == tkIdentifier:
            param = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
            walk p
            if p.curr.kind == tkPunct and p.curr.value == ":":
              let tstart = p.markPos()
              walk p
              discard parseTSType(p)
              p.stripSince(tstart)
          elif p.curr.kind == tkPunct and p.curr.value == "{":
            # destructured catch param — keep the raw braces
            var depth = 0
            let startPos = p.lexer.pos
            while true:
              if p.curr.kind == tkEOF: error(p, "Unexpected EOF in catch parameter")
              if p.curr.kind == tkPunct and p.curr.value == "{": inc depth
              elif p.curr.kind == tkPunct and p.curr.value == "}":
                dec depth
                if depth == 0: break
              walk p
            param = Node(kind: nkLitString,
              valStr: "{" & p.lexer.getLexeme(startPos + 1, p.lexer.pos - 1) & "}")
          p.expectWalk(")")
        if not (p.curr.kind == tkPunct and p.curr.value == "{"):
          error(p, "Expected '{' after 'catch'")
        result.children.add(Node(kind: nkStatement,
          children: @[Node(kind: nkIdent, name: "except"), param, parseBlock(p)]))
      elif p.curr.kind == tkIdentifier and p.curr.value == "finally":
        walk p
        if not (p.curr.kind == tkPunct and p.curr.value == "{"):
          error(p, "Expected '{' after 'finally'")
        result.children.add(Node(kind: nkStatement,
          children: @[Node(kind: nkIdent, name: "finally"), parseBlock(p)]))
      else:
        break

  stmtHandler p, "declarator":
    ## `let` / `var` / `const` with full type annotations, `!` definite
    ## assignment and `const enum` delegation. `as const` still parses:
    ## the annotation position uses `parseTSType`, never the Pratt loop.
    ## Unlike the JS handler the trailing `;` is always consumed, so
    ## `parseScript` never emits a phantom `nkEmpty` for it.
    if p.curr.kind == tkIdentifier and p.curr.value == "const" and
        p.next.kind == tkIdentifier and p.next.value == "enum":
      let constTk = p.curr
      let constFrom = p.markPos()
      walk p # consume `const`
      let enumNode = p.stmtHandlers["enum"](p)
      # `const enum` lowers like `enum`; extend the recorded span over
      # the `const` prefix so no modifier is left behind.
      if p.stripSpans.len > 0 and p.stripSpans[^1].kind == skEnum and
          p.stripSpans[^1].span.a >= constFrom:
        p.stripSpans[^1].span.a = constFrom
      result = Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "const").stamp(constTk), enumNode]).stamp(constTk)
      return
    result = Node(kind: nkStatement)
    let kw = p.curr.value
    result.children.add(Node(kind: nkIdent, name: kw))
    walk p
    while true:
      while p.curr.kind in {tkComment, tkDocComment}:
        discard parseCommentGeneric(p)
      if p.curr.kind == tkPunct and p.curr.value in ["{", "["]:
        let pattern = parseExpression(p, 1)
        var ty = newEmptyNode()
        if p.curr.kind == tkPunct and p.curr.value == ":":
          let tstart = p.markPos()
          walk p
          ty = parseTSType(p)
          p.stripSince(tstart)
        var init = newEmptyNode()
        if p.curr.kind == tkPunct and p.curr.value == "=":
          walk p
          init = parseExpression(p)
        result.children.add(Node(kind: nkIdentDefs, children: @[pattern, ty, init]))
        if p.curr.kind == tkPunct and p.curr.value == ",":
          walk p
        else: break
      elif p.curr.kind == tkIdentifier:
        var nm: Node = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
        walk p
        if p.curr.kind == tkPunct and p.curr.value == "!":
          p.stripCurr()
          let bTk = p.curr
          walk p
          nm = Node(kind: nkPostfix,
            children: @[nm, Node(kind: nkIdent, name: "!").stamp(bTk)]).stampFrom(nm)
        var ty = newEmptyNode()
        if p.curr.kind == tkPunct and p.curr.value == ":":
          let tstart = p.markPos()
          walk p
          ty = parseTSType(p)
          p.stripSince(tstart)
        var init = newEmptyNode()
        if p.curr.kind == tkPunct and p.curr.value == "=":
          walk p
          init = parseExpression(p)
        result.children.add(Node(kind: nkIdentDefs, children: @[nm, ty, init]))
        if p.curr.kind == tkPunct and p.curr.value == ",":
          walk p
        else: break
      else:
        error(p, "Expected identifier in variable declaration")
    p.walkOpt(";")

  stmtHandler p, "function":
    result = parseTSFunctionDecl(p, "function")

  stmtHandler p, "async_function":
    ## `async function f<T>() {}` or typed/generic async arrows.
    let asyncFrom = p.markPos()
    walk p # consume `async`
    skipTSComments(p)
    if p.curr.kind == tkIdentifier and p.curr.value == "function":
      let fn = parseTSFunctionDecl(p, "function", asyncFrom)
      result = Node(kind: nkStatement)
      result.children.add(Node(kind: nkIdent, name: "async"))
      result.children.add(fn)
    else:
      var generics = newEmptyNode()
      if p.curr.kind == tkPunct and p.curr.value == "<":
        generics = parseTSGenericParams(p)
        skipTSComments(p)
      var params = Node(kind: nkIdentDefs)
      if p.curr.kind == tkPunct and p.curr.value == "(":
        params = parseTSParams(p)
      elif p.curr.kind == tkIdentifier:
        params.children.add(Node(kind: nkIdent, name: p.curr.value).stamp(p.curr))
        walk p
      else:
        error(p, "Expected 'function' or arrow parameters after 'async'")
      let ret = parseTSReturnType(p)
      skipTSComments(p)
      p.expectWalk("=>")
      skipTSComments(p)
      let body = if p.curr.kind == tkPunct and p.curr.value == "{":
                   parseBlock(p)
                 else:
                   parseExpression(p, 0)
      result = Node(kind: nkFunction,
        children: @[Node(kind: nkIdent, name: "async"), generics, params, ret, body])

  stmtHandler p, "class":
    ## `class Name<T> extends Base<T> implements I, J { ... }` with
    ## decorators and TS member modifiers. Value-level `extends` heritage
    ## (e.g. `extends mix(Base)`) parses through `parseTSHeritage`.
    var leadingDecs: seq[Node] = @[]
    while p.curr.kind == tkPunct and p.curr.value == "@":
      for d in parseTSDecorators(p):
        leadingDecs.add(d)
      skipTSComments(p)
    walk p # consume `class`
    skipTSComments(p)
    var name: Node
    if p.curr.kind == tkIdentifier and p.curr.value notin ["extends", "implements"]:
      name = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
      walk p
    else:
      name = newEmptyNode()
    skipTSComments(p)
    var generics = newEmptyNode()
    if p.curr.kind == tkPunct and p.curr.value == "<":
      generics = parseTSGenericParams(p)
      skipTSComments(p)
    var parent = newEmptyNode()
    while p.curr.kind in {tkComment, tkDocComment}:
      discard parseCommentGeneric(p)
    if p.curr.kind == tkIdentifier and p.curr.value == "extends":
      walk p
      skipTSComments(p)
      parent = parseTSHeritage(p)
      skipTSComments(p)
    var impls = newEmptyNode()
    if p.curr.kind == tkIdentifier and p.curr.value == "implements":
      let implFrom = p.markPos()
      walk p
      skipTSComments(p)
      impls = Node(kind: nkIdentDefs)
      while true:
        impls.children.add(parseTSHeritage(p))
        skipTSComments(p)
        if p.curr.kind == tkPunct and p.curr.value == ",":
          walk p
          skipTSComments(p)
        else: break
      p.stripSince(implFrom)
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "class"), name, generics, parent, impls])
    p.expectWalk("{")
    let body = Node(kind: nkBlock)
    var bodiedKeys: seq[(string, int)] = @[]
    var pendingBodiless: seq[(string, int, int)] = @[]
    while not (p.curr.kind == tkPunct and p.curr.value == "}"):
      if p.curr.kind == tkEOF:
        error(p, "Unexpected EOF in class body")
      if p.curr.kind in {tkComment, tkDocComment}:
        body.children.add(parseCommentGeneric(p))
        continue
      if p.curr.kind == tkPunct and p.curr.value == ";":
        walk p
        continue
      if p.curr.kind == tkIdentifier and p.curr.value == "static" and
          p.next.kind == tkPunct and p.next.value == "{":
        walk p # consume `static`
        body.children.add(Node(kind: nkStatement,
          children: @[Node(kind: nkIdent, name: "static-block"), parseBlock(p)]))
        continue
      var decs: seq[Node] = @[]
      let memberFrom = p.markPos()
      while p.curr.kind == tkPunct and p.curr.value == "@":
        for d in parseTSDecorators(p):
          decs.add(d)
        skipTSComments(p)
      var flags: seq[Node] = @[]
      var dropMember = false
      while true:
        if p.curr.kind == tkPunct and p.curr.value == "*":
          flags.add(Node(kind: nkIdent, name: "*"))
          walk p
          continue
        if p.curr.kind == tkIdentifier and p.curr.value in
            ["static", "abstract", "override", "readonly", "declare",
             "public", "private", "protected", "async", "get", "set", "accessor"]:
          let nxt = p.next
          # `get`/`set` before `<` is always the member name: accessors
          # cannot be generic, so `get<K>()` is a method named `get`.
          # (`async`/`static` before `<` stay modifiers: `static <T>m()`.)
          if p.curr.value in ["get", "set"] and nxt.kind == tkPunct and
              nxt.value == "<":
            break
          let isName = nxt.kind == tkEOF or
            (nxt.kind == tkPunct and nxt.value in ["(", "=", ";", "}", ":", "?", "!"]) or
            (nxt.kind == tkIdentifier and nxt.value in ["=", ":"])
          if isName: break
          if p.curr.value in ["declare", "abstract"]:
            # Ambient or abstract members have no runtime shape here:
            # the whole member is erased below.
            dropMember = true
          let flagName = p.curr.value
          let flagTk = p.curr
          if p.curr.value notin ["static", "async", "get", "set"]:
            p.stripCurrPast()
          else:
            walk p
          flags.add(Node(kind: nkIdent, name: flagName).stamp(flagTk))
          continue
        break
      # Index signature: `[k: string]: T`.
      if p.curr.kind == tkPunct and p.curr.value == "[" and
          p.next.kind == tkIdentifier:
        let mark = (lex: markLexer(p.lexer), prev: p.prev, curr: p.curr, next: p.next)
        var isIndex = false
        try:
          walk p
          walk p
          isIndex = p.curr.kind == tkPunct and p.curr.value == ":"
        except OpenAstParsingError:
          discard
        restoreLexer(p.lexer, mark.lex)
        p.prev = mark.prev
        p.curr = mark.curr
        p.next = mark.next
        if isIndex:
          walk p
          let nm = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
          walk p
          p.expectWalk(":")
          let keyTy = parseTSType(p)
          p.expectWalk("]")
          p.expectWalk(":")
          let valTy = parseTSType(p)
          p.walkOpt(";")
          p.stripSince(memberFrom)
          var idx = Node(kind: nkStatement,
            children: @[Node(kind: nkIdent, name: "index"),
                        Node(kind: nkIdentDefs, children: @[nm, keyTy]), valTy])
          if decs.len > 0:
            idx = Node(kind: nkPragmaBlock,
              children: @[Node(kind: nkBlock, children: decs), idx])
          body.children.add(idx)
          continue
      var key: Node
      if p.curr.kind == tkPunct and p.curr.value == "[":
        let openTk = p.curr
        walk p
        let e = parseExpression(p, 0)
        p.expectWalk("]")
        key = Node(kind: nkStatement,
          children: @[Node(kind: nkIdent, name: "computed").stamp(openTk), e]).stamp(openTk)
      elif p.curr.kind == tkString:
        key = Node(kind: nkLitString, valStr: p.curr.value).stamp(p.curr)
        walk p
      elif p.curr.kind == tkInt:
        key = Node(kind: nkLitInt, valInt: parseInt(p.curr.value)).stamp(p.curr)
        walk p
      else:
        expectTSIdent:
          key = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
        walk p
      if p.curr.kind == tkPunct and p.curr.value in ["?", "!"]:
        p.stripCurr()
        let mTk = p.curr
        walk p
        key = Node(kind: nkPostfix,
          children: @[key, Node(kind: nkIdent, name: mTk.value).stamp(mTk)]).stampFrom(key)
      var methGenerics = newEmptyNode()
      if p.curr.kind == tkPunct and p.curr.value == "<":
        methGenerics = parseTSGenericParams(p)
      if p.curr.kind == tkPunct and p.curr.value == "(":
        let params = parseTSParams(p)
        let ret = parseTSReturnType(p)
        var fnBody = newEmptyNode()
        var keyName = ""
        case key.kind
        of nkIdent: keyName = key.name
        of nkLitString: keyName = key.valStr
        of nkLitInt: keyName = $key.valInt
        else: discard
        if p.curr.kind == tkPunct and p.curr.value == "{":
          let bracePos = p.markPos()
          fnBody = parseBlock(p)
          if keyName.len > 0:
            bodiedKeys.add((keyName, memberFrom))
          # Constructor parameter properties (`constructor(private x)`)
          # need `this.x = x` assignments: replace the `{` with itself
          # plus the assignments.
          if keyName == "constructor" and not dropMember:
            var propNames: seq[string] = @[]
            var propBad = false
            for entry in params.children:
              if entry.kind != nkStatement or entry.children.len < 2 or
                  entry.children[0].kind != nkIdent or
                  entry.children[0].name != "param":
                continue
              let last = entry.children[^1]
              var flagEnd = entry.children.len - 1
              var nm: Node = nil
              if last.kind == nkIdentDefs and last.children.len > 0:
                if last.children[0].kind == nkIdent:
                  nm = last.children[0]
                else:
                  propBad = true
              elif entry.children.len >= 4 and
                  entry.children[^3].kind == nkIdent:
                nm = entry.children[^3]
                flagEnd = entry.children.len - 3
              else:
                continue
              var isProp = false
              for fi in 1 ..< flagEnd:
                let f = entry.children[fi]
                if f.kind == nkIdent and f.name in ["public", "private",
                    "protected", "readonly"]:
                  isProp = true
                  break
              if isProp:
                if nm != nil:
                  propNames.add(nm.name)
                else:
                  propBad = true
            if propBad:
              p.stripError(memberFrom,
                "Destructured constructor parameter properties are not supported (TypeScript v1)")
            elif propNames.len > 0:
              var synth = "{"
              for pn in propNames:
                synth.add("\nthis." & pn & " = " & pn & ";")
              p.stripSpans.add(StripSpan(kind: skReplace,
                span: bracePos ..< bracePos + 1, text: synth))
        else:
          p.walkOpt(";")
          if dropMember:
            p.stripSince(memberFrom)
          elif keyName.len > 0:
            pendingBodiless.add((keyName, memberFrom, p.consumedEnd()))
          else:
            # Computed keys cannot be matched to an implementation here.
            p.stripError(memberFrom,
              "Computed method lacks an implementation")
        let fnNode = Node(kind: nkFunction,
          children: flags & @[methGenerics, params, ret, fnBody])
        var member = Node(kind: nkColonExpr, children: @[key, fnNode])
        if decs.len > 0:
          member = Node(kind: nkPragmaBlock,
            children: @[Node(kind: nkBlock, children: decs), member])
        body.children.add(member)
      else:
        var ty = newEmptyNode()
        if p.curr.kind == tkPunct and p.curr.value == ":":
          let tstart = p.markPos()
          walk p
          ty = parseTSType(p)
          p.stripSince(tstart)
        var init = newEmptyNode()
        if p.curr.kind == tkPunct and p.curr.value == "=":
          walk p
          init = parseExpression(p)
        p.walkOpt(";")
        if dropMember:
          p.stripSince(memberFrom)
        var fieldStmt = Node(kind: nkStatement)
        fieldStmt.children.add(Node(kind: nkIdent, name: "field"))
        fieldStmt.children.add(flags)
        fieldStmt.children.add(key)
        fieldStmt.children.add(ty)
        fieldStmt.children.add(init)
        if decs.len > 0:
          fieldStmt = Node(kind: nkPragmaBlock,
            children: @[Node(kind: nkBlock, children: decs), fieldStmt])
        body.children.add(fieldStmt)
    # Overload signatures resolve against same-key implementations in
    # this body: drop the signature, or record a missing-implementation
    # error. (Abstract/declare members were erased inline above.)
    for (keyName, sigFrom, sigEnd) in pendingBodiless:
      var hasImpl = false
      for (bk, bpos) in bodiedKeys:
        if bk == keyName and bpos > sigEnd:
          hasImpl = true
          break
      if hasImpl:
        if sigEnd > sigFrom:
          p.stripSpans.add(StripSpan(kind: skErase, span: sigFrom ..< sigEnd))
      else:
        p.stripSpans.add(StripSpan(kind: skError,
          span: sigFrom ..< max(sigEnd, sigFrom),
          text: "Method '" & keyName &
          "' lacks an implementation (overload signatures must be followed by an implementation)"))
    p.expectWalk("}")
    result.children.add(body)
    if leadingDecs.len > 0:
      result = Node(kind: nkPragmaBlock,
        children: @[Node(kind: nkBlock, children: leadingDecs), result]).stampFrom(result)

  stmtHandler p, "for_loop":
    ## Same shapes as the JS loop, but `var`/`let`/`const` items carry
    ## full types (`for (let x: Foo<Bar> of xs)`), parsed with
    ## `parseTSType` instead of the value loop.
    walk p # consume `for`
    var isAwait = false
    if p.curr.kind == tkIdentifier and p.curr.value == "await":
      isAwait = true
      walk p
    p.expectWalk("(")
    var initNode: Node
    var loopType = ""
    if p.curr.kind == tkPunct and p.curr.value == ";":
      initNode = Node(kind: nkEmpty)
      loopType = "c-style"
    elif p.curr.kind == tkIdentifier and p.curr.value in ["var", "let", "const"]:
      initNode = Node(kind: nkStatement)
      initNode.children.add(Node(kind: nkIdent, name: p.curr.value).stamp(p.curr))
      walk p
      while true:
        while p.curr.kind in {tkComment, tkDocComment}:
          discard parseCommentGeneric(p)
        if p.curr.kind == tkPunct and p.curr.value in ["{", "["]:
          let pattern = parseExpression(p)
          var ty = newEmptyNode()
          if p.curr.kind == tkPunct and p.curr.value == ":":
            let tstart = p.markPos()
            walk p
            ty = parseTSType(p)
            p.stripSince(tstart)
          var init = newEmptyNode()
          if p.curr.kind == tkPunct and p.curr.value == "=":
            walk p
            init = parseExpression(p)
          initNode.children.add(Node(kind: nkIdentDefs,
            children: @[pattern, ty, init]))
        else:
          if p.curr.kind != tkIdentifier:
            error(p, "Expected identifier in variable declaration")
          var nm: Node = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
          walk p
          if p.curr.kind == tkPunct and p.curr.value == "!":
            p.stripCurr()
            let bTk = p.curr
            walk p
            nm = Node(kind: nkPostfix,
              children: @[nm, Node(kind: nkIdent, name: "!").stamp(bTk)]).stampFrom(nm)
          var ty = newEmptyNode()
          if p.curr.kind == tkPunct and p.curr.value == ":":
            let tstart = p.markPos()
            walk p
            ty = parseTSType(p)
            p.stripSince(tstart)
          var init = newEmptyNode()
          if p.curr.kind == tkPunct and p.curr.value == "=":
            walk p
            init = parseExpression(p)
          initNode.children.add(Node(kind: nkIdentDefs,
            children: @[nm, ty, init]))
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
      if p.curr.kind == tkIdentifier and p.next.kind == tkIdentifier and
          p.next.value in ["in", "of"]:
        initNode = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
        walk p
        loopType = p.curr.value
      else:
        initNode = parseCommaExpr(p)
        if p.curr.kind == tkPunct and p.curr.value == ";":
          loopType = "c-style"
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
      result = Node(kind: nkStatement)
      result.children.add(Node(kind: nkIdent, name: "for"))
      result.children.add(Node(kind: nkIdent,
        name: (if isAwait: "await-" & loopType else: loopType)))
      result.children.add(initNode)
      result.children.add(iterable)
      result.children.add(body)
    else:
      error(p, "Expected ';', 'in', or 'of' in for loop")

  stmtHandler p, "type_alias":
    let aliasFrom = p.markPos()
    walk p # consume `type`
    skipTSComments(p)
    expectTSIdent:
      result = Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "type"),
                    Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)])
    walk p
    skipTSComments(p)
    if p.curr.kind == tkPunct and p.curr.value == "<":
      result.children.add(parseTSGenericParams(p))
    else:
      result.children.add(newEmptyNode())
    skipTSComments(p)
    p.expectWalk("=")
    skipTSComments(p)
    result.children.add(parseTSType(p))
    p.walkOpt(";")
    p.stripSince(aliasFrom)

  stmtHandler p, "interface":
    let ifaceFrom = p.markPos()
    walk p # consume `interface`
    skipTSComments(p)
    expectTSIdent:
      result = Node(kind: nkInterface,
        children: @[Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)])
    walk p
    skipTSComments(p)
    if p.curr.kind == tkPunct and p.curr.value == "<":
      result.children.add(parseTSGenericParams(p))
    else:
      result.children.add(newEmptyNode())
    skipTSComments(p)
    if p.curr.kind == tkIdentifier and p.curr.value == "extends":
      walk p
      skipTSComments(p)
      var exts = Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "extends")])
      while true:
        exts.children.add(parseTSHeritage(p))
        skipTSComments(p)
        if p.curr.kind == tkPunct and p.curr.value == ",":
          walk p
          skipTSComments(p)
        else: break
      result.children.add(exts)
    else:
      result.children.add(newEmptyNode())
    skipTSComments(p)
    # Body members share the object-type grammar (no initializers or
    # bodies can appear: `=` / `{` after a member simply won't match).
    if p.curr.kind != tkPunct or p.curr.value != "{":
      error(p, "Expected '{' after interface header")
    result.children.add(parseTSObjectType(p))
    p.stripSince(ifaceFrom)

  stmtHandler p, "enum":
    let enumFrom = p.markPos()
    walk p # consume `enum`
    skipTSComments(p)
    var name: Node
    if p.curr.kind == tkIdentifier:
      name = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
      walk p
    else:
      name = newEmptyNode()
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "enum"), name])
    skipTSComments(p)
    p.expectWalk("{")
    let body = Node(kind: nkBlock)
    var enumMembers: seq[EnumMember] = @[]
    while not (p.curr.kind == tkPunct and p.curr.value == "}"):
      if p.curr.kind == tkEOF:
        error(p, "Unexpected EOF in enum")
      if p.curr.kind in {tkComment, tkDocComment}:
        body.children.add(parseCommentGeneric(p))
        continue
      if p.curr.kind == tkPunct and p.curr.value == ",":
        walk p
        continue
      var member: Node
      let mstart = p.markPos()
      if p.curr.kind == tkString:
        member = Node(kind: nkLitString, valStr: p.curr.value).stamp(p.curr)
        walk p
      else:
        expectTSIdent:
          member = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
        walk p
      var init = newEmptyNode()
      var em = EnumMember(line: member.ln)
      if member.kind == nkLitString:
        em.strName = true
        em.nameSpan = mstart ..< p.consumedEnd()
      else:
        em.name = member.name
      if p.curr.kind == tkPunct and p.curr.value == "=":
        walk p
        let istart = p.markPos()
        init = parseExpression(p)
        let iend = p.consumedEnd()
        case init.kind
        of nkLitInt:
          em.initKind = ikInt
          em.intVal = init.valInt
          em.initSpan = istart ..< iend
        of nkLitString:
          em.initKind = ikStr
          em.strVal = init.valStr
          em.initSpan = istart ..< iend
        else:
          em.initKind = ikExpr
          em.initSpan = istart ..< iend
      body.children.add(Node(kind: nkIdentDefs,
        children: @[member, newEmptyNode(), init]))
      enumMembers.add(em)
      p.walkOpt(",")
    p.expectWalk("}")
    if p.curr.kind == tkPunct and p.curr.value == ";":
      walk p # a trailing `;` belongs to the declaration
    result.children.add(body)
    if name.kind == nkIdent:
      p.stripSpans.add(StripSpan(kind: skEnum,
        span: enumFrom ..< p.consumedEnd(),
        text: name.name, members: enumMembers))
    # Anonymous enums only occur with `export default` (rejected as ESM
    # downstream); leave them untouched.

  stmtHandler p, "namespace":
    let kwTk = p.curr
    let kw = p.curr.value
    let nsFrom = p.markPos()
    walk p # consume `namespace` / `module`
    skipTSComments(p)
    var name: Node
    if p.curr.kind == tkString:
      name = Node(kind: nkLitString, valStr: p.curr.value).stamp(p.curr)
      walk p
    else:
      name = parseTSQualifiedName(p)
    skipTSComments(p)
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: kw).stamp(kwTk), name])
    if p.curr.kind == tkPunct and p.curr.value == "{":
      result.children.add(parseBlock(p))
      if p.curr.kind == tkPunct and p.curr.value == ";":
        walk p # a trailing `;` belongs to the declaration
      let path = if name.kind == nkLitString: @[] else: dottedPath(name)
      p.stripSpans.add(StripSpan(kind: skNamespace,
        span: nsFrom ..< p.consumedEnd(), path: path))
    elif p.curr.kind == tkPunct and p.curr.value == ";":
      walk p
      result.children.add(newEmptyNode())
      p.stripSince(nsFrom)
    else:
      result.children.add(newEmptyNode())

  stmtHandler p, "module":
    let kwTk = p.curr
    let modFrom = p.markPos()
    walk p # consume `module`
    skipTSComments(p)
    var name: Node
    if p.curr.kind == tkString:
      name = Node(kind: nkLitString, valStr: p.curr.value).stamp(p.curr)
      walk p
    else:
      name = parseTSQualifiedName(p)
    skipTSComments(p)
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "module").stamp(kwTk), name])
    if p.curr.kind == tkPunct and p.curr.value == "{":
      result.children.add(parseBlock(p))
      if p.curr.kind == tkPunct and p.curr.value == ";":
        walk p # a trailing `;` belongs to the declaration
      let path = if name.kind == nkLitString: @[] else: dottedPath(name)
      p.stripSpans.add(StripSpan(kind: skNamespace,
        span: modFrom ..< p.consumedEnd(), path: path))
    elif p.curr.kind == tkPunct and p.curr.value == ";":
      walk p
      result.children.add(newEmptyNode())
      p.stripSince(modFrom)
    else:
      result.children.add(newEmptyNode())

  stmtHandler p, "declare":
    let decTk = p.curr
    let decFrom = p.markPos()
    walk p # consume `declare`
    skipTSComments(p)
    if p.curr.kind == tkIdentifier and p.curr.value == "global":
      let gTk = p.curr
      walk p
      skipTSComments(p)
      result = Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "declare").stamp(decTk),
                    Node(kind: nkIdent, name: "global").stamp(gTk)])
      if p.curr.kind == tkPunct and p.curr.value == "{":
        result.children.add(parseBlock(p))
      else:
        result.children.add(newEmptyNode())
      p.stripSince(decFrom)
      return
    if p.curr.kind == tkIdentifier and p.stmtKeywords.hasKey(p.curr.value):
      let decl = p.stmtHandlers[p.stmtKeywords[p.curr.value]](p)
      result = Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "declare").stamp(decTk), decl]).stamp(decTk)
      p.stripSince(decFrom)
    else:
      error(p, "Expected declaration after 'declare'")

  stmtHandler p, "abstract_class":
    let absTk = p.curr
    let absFrom = p.markPos()
    walk p # consume `abstract`
    skipTSComments(p)
    if p.curr.kind == tkIdentifier and p.curr.value == "class":
      let classStart = p.markPos()
      let classNode = p.stmtHandlers["class"](p)
      result = Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "abstract").stamp(absTk), classNode]).stamp(absTk)
      if classStart > absFrom:
        p.stripSpans.add(StripSpan(kind: skErase, span: absFrom ..< classStart))
    else:
      error(p, "Expected 'class' after 'abstract'")

  stmtHandler p, "using":
    let usingTk = p.curr
    let usingFrom = p.markPos()
    walk p # consume `using`
    skipTSComments(p)
    expectTSIdent:
      let nm = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
      walk p
      var ty = newEmptyNode()
      if p.curr.kind == tkPunct and p.curr.value == ":":
        let tstart = p.markPos()
        walk p
        ty = parseTSType(p)
        p.stripSince(tstart)
      p.expectWalk("=")
      let init = parseExpression(p)
      result = Node(kind: nkStatement,
        children: @[Node(kind: nkIdent, name: "using").stamp(usingTk),
                    Node(kind: nkIdentDefs, children: @[nm, ty, init])]).stamp(usingTk)
      p.walkOpt(";")
      # `using` (5 chars) and `const` (5 chars) swap exactly.
      p.stripSpans.add(StripSpan(kind: skReplace,
        span: usingFrom ..< usingFrom + 5, text: "const"))

  stmtHandler p, "import":
    ## `import type ...` plus the full JS import grammar underneath.
    let impFrom = p.markPos()
    walk p # consume `import`
    skipTSComments(p)
    result = Node(kind: nkImport)
    var typeOnly = false
    var importAssign = false
    if p.curr.kind == tkIdentifier and p.curr.value == "type" and
        not (p.next.kind == tkPunct and p.next.value in [",", "="]):
      # `import type X from` / `import type {…}` / `import type * as` —
      # but not `import type, …` (a default import *named* `type`).
      typeOnly = true
      walk p
      skipTSComments(p)
    if p.curr.kind == tkString:
      result.children.add(newEmptyNode())
      result.children.add(Node(kind: nkLitString, valStr: p.curr.value).stamp(p.curr))
      walk p
      p.walkOpt(";")
    elif p.curr.kind == tkPunct and p.curr.value == "{":
      result.children.add(newEmptyNode())
      walk p
      let named = Node(kind: nkIdentDefs)
      while not (p.curr.kind == tkPunct and p.curr.value == "}"):
        if p.curr.kind == tkEOF:
          error(p, "Unexpected EOF in import")
        if p.curr.kind in {tkComment, tkDocComment}:
          discard parseCommentGeneric(p)
          continue
        if p.curr.kind == tkIdentifier:
          let nm = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
          walk p
          if p.curr.kind == tkIdentifier and p.curr.value == "as":
            walk p
            expectTSIdent:
              named.children.add(Node(kind: nkInfix,
                children: @[Node(kind: nkIdent, name: "as"),
                            nm, Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)]))
            walk p
          else:
            named.children.add(nm)
        p.walkOpt(",")
      p.expectWalk("}")
      result.children.add(named)
      if p.curr.kind == tkIdentifier and p.curr.value == "from":
        walk p
        if p.curr.kind != tkString:
          error(p, "Expected module string after 'from'")
        result.children.add(Node(kind: nkLitString, valStr: p.curr.value).stamp(p.curr))
        walk p
      p.walkOpt(";")
    elif p.curr.kind == tkPunct and p.curr.value == "*":
      result.children.add(newEmptyNode())
      walk p
      if p.curr.kind == tkIdentifier and p.curr.value == "as":
        walk p
        expectTSIdent:
          result.children.add(Node(kind: nkInfix,
            children: @[Node(kind: nkIdent, name: "as"),
                        Node(kind: nkIdent, name: "*"),
                        Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)]))
        walk p
      if p.curr.kind == tkIdentifier and p.curr.value == "from":
        walk p
        if p.curr.kind != tkString:
          error(p, "Expected module string after 'from'")
        result.children.add(Node(kind: nkLitString, valStr: p.curr.value).stamp(p.curr))
        walk p
      p.walkOpt(";")
    elif p.curr.kind == tkIdentifier:
      let defaultName = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
      walk p
      if p.curr.kind == tkPunct and p.curr.value == "=":
        # `import x = A.B.C` (import-assignment) or
        # `import x = require("m")` (external module reference).
        importAssign = true
        let eqTk = p.curr
        walk p
        result.children.add(defaultName)
        result.children.add(Node(kind: nkIdent, name: "=").stamp(eqTk))
        var rhs = parseTSQualifiedName(p)
        skipTSComments(p)
        if rhs.kind == nkIdent and rhs.name == "require" and
            p.curr.kind == tkPunct and p.curr.value == "(":
          let openTk = p.curr
          walk p
          let call = Node(kind: nkCall, children: @[rhs]).stamp(openTk)
          while not (p.curr.kind == tkPunct and p.curr.value == ")"):
            if p.curr.kind == tkEOF:
              error(p, "Unexpected EOF in import")
            if p.curr.kind in {tkComment, tkDocComment}:
              call.children.add(parseCommentGeneric(p))
              continue
            call.children.add(parseExpression(p, 0))
            p.walkOpt(",")
          p.expectWalk(")")
          rhs = call
        result.children.add(rhs)
        p.walkOpt(";")
      elif p.curr.kind == tkIdentifier and p.curr.value == "from":
        result.children.add(defaultName)
        walk p
        if p.curr.kind != tkString:
          error(p, "Expected module string after 'from'")
        result.children.add(Node(kind: nkLitString, valStr: p.curr.value).stamp(p.curr))
        walk p
        p.walkOpt(";")
      elif p.curr.kind == tkPunct and p.curr.value == ",":
        result.children.add(defaultName)
        walk p
        if p.curr.kind == tkPunct and p.curr.value == "{":
          let named = Node(kind: nkIdentDefs)
          walk p
          while not (p.curr.kind == tkPunct and p.curr.value == "}"):
            if p.curr.kind == tkEOF:
              error(p, "Unexpected EOF in import")
            if p.curr.kind in {tkComment, tkDocComment}:
              discard parseCommentGeneric(p)
              continue
            if p.curr.kind == tkIdentifier:
              let nm = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
              walk p
              if p.curr.kind == tkIdentifier and p.curr.value == "as":
                walk p
                expectTSIdent:
                  named.children.add(Node(kind: nkInfix,
                    children: @[Node(kind: nkIdent, name: "as"),
                                nm, Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)]))
                walk p
              else:
                named.children.add(nm)
            p.walkOpt(",")
          p.expectWalk("}")
          result.children.add(named)
          if p.curr.kind == tkIdentifier and p.curr.value == "from":
            walk p
            if p.curr.kind != tkString:
              error(p, "Expected module string after 'from'")
            result.children.add(Node(kind: nkLitString, valStr: p.curr.value).stamp(p.curr))
            walk p
          p.walkOpt(";")
        elif p.curr.kind == tkPunct and p.curr.value == "*":
          walk p
          if p.curr.kind == tkIdentifier and p.curr.value == "as":
            walk p
            expectTSIdent:
              result.children.add(Node(kind: nkInfix,
                children: @[Node(kind: nkIdent, name: "as"),
                            Node(kind: nkIdent, name: "*"),
                            Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)]))
            walk p
          if p.curr.kind == tkIdentifier and p.curr.value == "from":
            walk p
            if p.curr.kind != tkString:
              error(p, "Expected module string after 'from'")
            result.children.add(Node(kind: nkLitString, valStr: p.curr.value).stamp(p.curr))
            walk p
          p.walkOpt(";")
        else:
          error(p, "Expected '{' or '*' after ',' in import")
      else:
        result.children.add(defaultName)
        p.walkOpt(";")
    else:
      error(p, "Unexpected token in import")
    if typeOnly:
      result.children.add(Node(kind: nkIdent, name: "type"))
      p.stripSince(impFrom)
    elif importAssign:
      # `import` (6 chars) and `const ` (6 chars) swap exactly.
      p.stripSpans.add(StripSpan(kind: skReplace,
        span: impFrom ..< impFrom + 6, text: "const "))

  stmtHandler p, "export":
    ## `export type …`, `export = …` plus the JS export grammar and
    ## delegation to TS declaration handlers.
    let expFrom = p.markPos()
    walk p # consume `export`
    skipTSComments(p)
    result = Node(kind: nkStatement)
    result.children.add(Node(kind: nkIdent, name: "export"))
    var typeOnly = false
    if p.curr.kind == tkIdentifier and p.curr.value == "type" and
        p.next.kind == tkPunct and p.next.value in ["{", "*"]:
      typeOnly = true
      walk p
      skipTSComments(p)
    if p.curr.kind == tkPunct and p.curr.value == "=":
      walk p
      result.children.add(Node(kind: nkIdent, name: "="))
      result.children.add(parseExpression(p))
      p.walkOpt(";")
      p.stripSpans.add(StripSpan(kind: skExportEq,
        span: expFrom ..< p.consumedEnd()))
      return
    if p.curr.kind == tkIdentifier and p.curr.value == "default":
      walk p
      skipTSComments(p)
      result.children.add(Node(kind: nkIdent, name: "default"))
      if p.curr.kind == tkIdentifier and p.curr.value in
          ["function", "class", "interface", "abstract"] or
          (p.curr.kind == tkIdentifier and p.stmtKeywords.hasKey(p.curr.value)):
        let h = p.stmtKeywords[p.curr.value]
        if p.stmtHandlers.hasKey(h):
          let declStart = p.markPos()
          let decl = p.stmtHandlers[h](p)
          result.children.add(decl)
          if h in ["type_alias", "interface", "declare"] and
              p.stripSpans.len > 0 and
              p.stripSpans[^1].kind == skErase and
              p.stripSpans[^1].span.a == declStart:
            # Type-only declarations vanish with `export default`.
            p.stripSpans[^1].span.a = expFrom
          else:
            p.stripSpans.add(StripSpan(kind: skExportKw,
              span: expFrom ..< expFrom + 6, names: exportDeclNames(decl),
              defaultExport: true))
          return
      result.children.add(parseExpression(p))
      p.walkOpt(";")
      p.stripSpans.add(StripSpan(kind: skExportKw,
        span: expFrom ..< expFrom + 6, defaultExport: true))
      return
    if p.curr.kind == tkPunct and p.curr.value == "{":
      let listFrom = p.markPos()
      walk p
      let named = Node(kind: nkIdentDefs)
      var pairs: seq[string] = @[]
      while not (p.curr.kind == tkPunct and p.curr.value == "}"):
        if p.curr.kind == tkEOF:
          error(p, "Unexpected EOF in export")
        if p.curr.kind in {tkComment, tkDocComment}:
          discard parseCommentGeneric(p)
          continue
        if p.curr.kind == tkIdentifier:
          let nm = Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)
          walk p
          if p.curr.kind == tkIdentifier and p.curr.value == "as":
            walk p
            expectTSIdent:
              let alias = p.curr.value
              named.children.add(Node(kind: nkInfix,
                children: @[Node(kind: nkIdent, name: "as"), nm,
                            Node(kind: nkIdent, name: alias).stamp(p.curr)]))
              pairs.add(nm.name)
              pairs.add(alias)
            walk p
          else:
            named.children.add(nm)
            pairs.add(nm.name)
            pairs.add(nm.name)
        p.walkOpt(",")
      p.expectWalk("}")
      result.children.add(named)
      var fromMod = ""
      if p.curr.kind == tkIdentifier and p.curr.value == "from":
        walk p
        if p.curr.kind != tkString:
          error(p, "Expected module string after 'from'")
        fromMod = p.curr.value
        result.children.add(Node(kind: nkLitString, valStr: p.curr.value).stamp(p.curr))
        walk p
      if typeOnly:
        result.children.add(Node(kind: nkIdent, name: "type"))
      else:
        # Keyword + list lower only inside namespaces; elsewhere ESM.
        p.stripSpans.add(StripSpan(kind: skExportKw,
          span: expFrom ..< expFrom + 6))
        p.stripSpans.add(StripSpan(kind: skExportList,
          span: listFrom ..< p.consumedEnd(), names: pairs,
          text: fromMod))
      p.walkOpt(";")
      if typeOnly:
        p.stripSince(expFrom)
      return
    if p.curr.kind == tkPunct and p.curr.value == "*":
      walk p
      if p.curr.kind == tkIdentifier and p.curr.value == "as":
        walk p
        expectTSIdent:
          result.children.add(Node(kind: nkInfix,
            children: @[Node(kind: nkIdent, name: "as"),
                        Node(kind: nkIdent, name: "*"),
                        Node(kind: nkIdent, name: p.curr.value).stamp(p.curr)]))
        walk p
      else:
        result.children.add(Node(kind: nkIdent, name: "*"))
      var fromMod = ""
      if p.curr.kind == tkIdentifier and p.curr.value == "from":
        walk p
        if p.curr.kind != tkString:
          error(p, "Expected module string after 'from'")
        fromMod = p.curr.value
        result.children.add(Node(kind: nkLitString, valStr: p.curr.value).stamp(p.curr))
        walk p
      if typeOnly:
        result.children.add(Node(kind: nkIdent, name: "type"))
      else:
        p.stripSpans.add(StripSpan(kind: skExportKw,
          span: expFrom ..< expFrom + 6))
        p.stripSpans.add(StripSpan(kind: skExportList,
          span: expFrom ..< p.consumedEnd(), text: fromMod))
      p.walkOpt(";")
      if typeOnly:
        p.stripSince(expFrom)
      return
    if p.curr.kind == tkIdentifier and p.curr.value in
        ["function", "class", "interface", "type", "enum",
         "namespace", "module", "declare", "abstract",
         "var", "let", "const"]:
      let h = p.stmtKeywords[p.curr.value]
      let declStart = p.markPos()
      let decl = p.stmtHandlers[h](p)
      result.children.add(decl)
      if h in ["type_alias", "interface", "declare"] and
          p.stripSpans.len > 0 and
          p.stripSpans[^1].kind == skErase and
          p.stripSpans[^1].span.a == declStart:
        # Type-only declarations vanish with their `export` keyword.
        p.stripSpans[^1].span.a = expFrom
      else:
        p.stripSpans.add(StripSpan(kind: skExportKw,
          span: expFrom ..< expFrom + 6, names: exportDeclNames(decl)))
      return
    expectTSIdent:
      result.children.add(Node(kind: nkIdent, name: p.curr.value).stamp(p.curr))
    walk p
    p.walkOpt(";")
    p.stripSpans.add(StripSpan(kind: skExportKw,
      span: expFrom ..< expFrom + 6,
      names: @[result.children[^1].name]))

proc parseTypeScript*(path: string): OpenAstProgram =
  ## Parse a TypeScript file (`.ts` / `.tsx`; `.tsx` additionally rejects
  ## angle-bracket assertions, mirroring tsc).
  try:
    result = parseScript(path, tsHandlers,
      features = {featAsync, featArrowFn, featGenerators,
                  featLabeledStmt, featTemplateLit})
  except OpenAstParsingError as e:
    echo e.msg
