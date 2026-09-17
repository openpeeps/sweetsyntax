import std/[unittest, os, strutils]
import ../src/sweetsyntax
import ../src/sweetsyntax/tokenizer
import ../src/sweetsyntax/languages/go as goHandlersMod

const goFixtureDir = currentSourcePath().parentDir / "data" / "go"

proc parseGo(code: string): Node =
  let syntax = getKnownSyntax(KnownSyntax.go)
  var p = compile(syntax.spec)
  p.lexer = initLexer(syntax.spec, code)
  goHandlersMod.goHandlers(p)
  p.features.incl(featLabeledStmt)
  p.curr = p.getToken()
  p.next = p.getToken()
  parseStatement(p)

proc parseGoStmts(code: string): seq[Node] =
  let syntax = getKnownSyntax(KnownSyntax.go)
  var p = compile(syntax.spec)
  p.lexer = initLexer(syntax.spec, code)
  goHandlersMod.goHandlers(p)
  p.features.incl(featLabeledStmt)
  p.curr = p.getToken()
  p.next = p.getToken()
  while p.curr.kind != tkEOF:
    result.add(parseStatement(p))

proc parseGoFile(path: string): seq[Node] =
  let syntax = getKnownSyntax(KnownSyntax.go)
  var p = compile(syntax.spec)
  p.lexer = initLexerFromFile(syntax.spec, path)
  goHandlersMod.goHandlers(p)
  p.features.incl(featLabeledStmt)
  p.curr = p.getToken()
  p.next = p.getToken()
  while p.curr.kind != tkEOF:
    result.add(parseStatement(p))

proc countNodes(n: Node): int =
  result = 1
  if n != nil:
    case n.kind
    of nkEmpty, nkNil, nkLitBool, nkLitInt, nkLitFloat, nkLitString,
       nkLitBigInt, nkIdent:
      discard
    else:
      for c in n.children:
        result += countNodes(c)

suite "Go parser (Phase 0)":
  test "package clause":
    let n = parseGo("package main")
    check n.kind == nkStatement
    check n[0].name == "package"
    check n[1].name == "main"

  test "single import":
    let n = parseGo("import \"fmt\"")
    check n.kind == nkStatement
    check n[0].name == "import"
    check n[1].kind == nkImport
    check n[1][1].kind == nkEmpty

  test "aliased, blank and dot imports":
    check parseGo("import f \"fmt\"")[1][1].name == "f"
    check parseGo("import _ \"x\"")[1][1].name == "_"
    check parseGo("import . \"x\"")[1][1].name == "."

  test "grouped imports":
    let n = parseGo("import (\n\"fmt\"\n\tm \"math\"\n)")
    check n.kind == nkStatement
    check n.len == 3

  test "empty func":
    let n = parseGo("func main() {}")
    check n.kind == nkFunction
    check n[0].name == "main"
    check n[1].kind == nkEmpty
    check n[2].kind == nkIdentDefs
    check n[4].kind == nkBlock

  test "func params split names and types":
    let n = parseGo("func add(a, b int) int { return a }")
    check n.kind == nkFunction
    check n[2].len == 1
    check n[2][0].len == 3
    check n[2][0][0].name == "a"
    check n[2][0][1].name == "b"
    check n[2][0][2].name == "int"
    check n[3].name == "int"

  test "func unnamed params stay separate":
    let n = parseGo("func f(int, string) {}")
    check n[2].len == 2
    check n[2][0][0].name == "int"
    check n[2][1][0].name == "string"

  test "short var decl and call in body":
    let n = parseGo("func f() {\nx := 1\nprintln(x)\n}")
    check n[4].len == 2

  test "return stops at newline":
    let n = parseGo("return\nx")
    check n.kind == nkStatement
    check n.len == 1

suite "Go parser (Phase 1: declarations)":
  test "var with type and value":
    let n = parseGo("var x int = 42")
    check n.kind == nkStatement
    check n[0].name == "var"
    check n[1][0].name == "x"
    check n[1][1].name == "int"
    check n[1][2].valInt == 42

  test "var value-only and type-only":
    check parseGo("var x = 1")[1][1].kind == nkEmpty
    check parseGo("var x int")[1][2].kind == nkEmpty

  test "var grouped block":
    let n = parseGo("var (\nx = 1\ny int\n)")
    check n.len == 3
    check n[1][0].name == "x"
    check n[2][0].name == "y"

  test "const with iota":
    let n = parseGo("const x = iota")
    check n[0].name == "const"
    check n[1][2].name == "iota"

  test "type definition and alias":
    let n = parseGo("type Point struct { x int }")
    check n[0].name == "type"
    check n[1][0].name == "Point"
    check n[1][2].kind == nkEmpty
    check n[1][3][0].name == "struct"
    let a = parseGo("type A = B")
    check a[1][2].name == "="
    check a[1][3].name == "B"

  test "struct fields, tags and embedding":
    let n = parseGo("type T struct {\nx, y int `json:\"p\"`\n*Base\npkg.E\n}")
    let st = n[1][3]
    check st.len == 4
    check st[1].len == 4
    check st[1][3].kind == nkLitString
    check st[2].len == 2
    check st[2][0].kind == nkPrefix
    check st[3][0].kind == nkDotExpr

  test "array field vs generic embedding":
    let a = parseGo("type T struct { x [3]int }")
    check a[1][3][1][1][0].valInt == 3
    let g = parseGo("type T struct { L[K] }")
    check g[1][3][1][0].kind == nkBracketExpr

  test "interface methods, embedding and union":
    let n = parseGo("type R interface {\nRead(p []byte) (int, error)\nio.Writer\n~int | ~string\n}")
    let it = n[1][3]
    check it[0].name == "interface"
    check it[1].kind == nkFunction
    check it[1][0].name == "Read"
    check it[1][2][0][1][0].kind == nkEmpty
    check it[2].kind == nkDotExpr
    check it[2][1].name == "Writer"
    check it[3].kind == nkInfix

  test "method with pointer receiver":
    let n = parseGo("func (p *Point) Scale(f float64) {}")
    check n.kind == nkFunction
    check n[0].name == "Scale"
    check n[1][0][0].name == "p"
    check n[1][0][1].kind == nkPrefix

  test "generic func with constraint":
    let n = parseGo("func Less[T Ordered](x, y T) bool { return x }")
    check n[0].kind == nkBracketExpr
    check n[0][0].name == "Less"
    check n[0][1][1].name == "Ordered"
    check n[2][0][2].name == "T"
    check n[3].name == "bool"

  test "slice, map and chan types":
    check parseGo("var s []int")[1][1][0].kind == nkEmpty
    let m = parseGo("var m map[string]int")
    check m[1][1][0].name == "map"
    check m[1][1][1].name == "string"
    let c = parseGo("var ch <-chan int")
    check c[1][1][0].name == "<-chan"

  test "multiline raw string keeps later line numbers":
    let nodes = parseGoStmts("var s = `a\nb`\nvar t = 1")
    check nodes.len == 2
    check nodes[0][1][2].valStr == "`a\nb`"
    check nodes[1].ln == 3
    check nodes[1][1][0].name == "t"

suite "Go parser (Phase 2: statements)":
  test "if without init or else":
    let n = parseGo("if x > 0 { y() }")
    check n.kind == nkStatement
    check n[0].name == "if"
    check n[1].kind == nkEmpty
    check n[2].kind == nkInfix
    check n[3].kind == nkBlock
    check n[4].kind == nkEmpty

  test "if with init and else":
    let n = parseGo("if x := f(); x > 0 { a() } else { b() }")
    check n[1].kind == nkInfix
    check n[1][0].name == ":="
    check n[2].kind == nkInfix
    check n[4].kind == nkBlock

  test "if else-if chain":
    let n = parseGo("if a { x() } else if b { y() } else { z() }")
    check n[4].kind == nkStatement
    check n[4][0].name == "if"
    check n[4][4].kind == nkBlock

  test "multi-target assignment and send":
    let a = parseGo("a, b = b, a")
    check a.kind == nkInfix
    check a[0].name == "="
    check a.len == 5
    let s = parseGo("ch <- 3")
    check s.kind == nkInfix
    check s[0].name == "<-"
    check s[1].name == "ch"
    let r = parseGo("x, ok := <-ch")
    check r[0].name == ":="
    check r.len == 4

  test "infinite and condition for loops":
    let inf = parseGo("for { work() }")
    check inf[1].kind == nkEmpty
    check inf[2].kind == nkEmpty
    check inf[3].kind == nkEmpty
    check inf[4].kind == nkBlock
    let c = parseGo("for i < n { i++ }")
    check c[1].kind == nkEmpty
    check c[2].kind == nkInfix
    check c[4][0].kind == nkPostfix

  test "classic for clause":
    let n = parseGo("for i := 0; i < 10; i++ { f(i) }")
    check n[1].kind == nkInfix
    check n[2].kind == nkInfix
    check n[3].kind == nkPostfix
    check n[4].kind == nkBlock

  test "for with empty clause parts":
    let n = parseGo("for ;; { x() }")
    check n[1].kind == nkEmpty
    check n[2].kind == nkEmpty
    check n[3].kind == nkEmpty

  test "for range forms":
    let kv = parseGo("for k, v := range m { f(k) }")
    check kv.len == 4
    check kv[1][2].name == ":="
    check kv[2].name == "m"
    let eq = parseGo("for k, v = range m { }")
    check eq[1][2].name == "="
    let bare = parseGo("for range ch { drain() }")
    check bare[1].kind == nkEmpty
    check bare[2].name == "ch"
    let overInt = parseGo("for i := range 10 { f(i) }")
    check overInt[2].valInt == 10

  test "expression switch":
    let n = parseGo("switch tag { case 1, 2: a(); default: b() }")
    check n[1].kind == nkEmpty
    check n[2].name == "tag"
    check n[3][0].name == "case"
    check n[3][1].len == 2
    check n[4][0].name == "default"
    check n[4][2].kind == nkBlock

  test "switch with init and missing expression":
    let n = parseGo("switch x := f(); { case x < 0: return -x }")
    check n[1].kind == nkInfix
    check n[2].kind == nkEmpty

  test "type switch with guard":
    let n = parseGo("switch i := x.(type) { case int: a(); case nil: b(); default: c() }")
    check n[1].kind == nkEmpty
    check n[2].kind == nkStatement
    check n[2][0].name == "i"
    check n[2][1].name == "x"
    check n[3][1][0].name == "int"
    check n[4][1][0].name == "nil"

  test "select with send, receive and default":
    let n = parseGo("select { case v := <-ch: f(v); case ch <- 1: g(); default: h() }")
    check n[1][0].name == "case"
    check n[1][1][0].kind == nkInfix
    check n[2][1][0].kind == nkInfix
    check n[2][1][0][0].name == "<-"
    check n[3][0].name == "default"

  test "go and defer":
    check parseGo("go f(x)")[1].kind == nkCall
    let lit = parseGo("go func() { work() }()")
    check lit[1].kind == nkCall
    check lit[1][0].kind == nkFunction
    check parseGo("defer f()")[0].name == "defer"

  test "break, continue, goto, fallthrough, labels":
    check parseGo("break")[1].kind == nkEmpty
    check parseGo("break Loop")[1].name == "Loop"
    check parseGo("break\nLoop")[1].kind == nkEmpty
    check parseGo("continue")[1].kind == nkEmpty
    check parseGo("goto done")[1].name == "done"
    let lab = parseGo("outer: x()")
    check lab[0].name == "label"
    check lab[1].name == "outer"
    let sw = parseGo("switch x { case 1: fallthrough; case 2: y() }")
    check sw[3][2][0][0].name == "fallthrough"

suite "Go parser (param semantics)":
  test "qualified types split comma items":
    let n = parseGo("func f(A, B.C) {}")
    check n[2].len == 2
    check n[2][0].len == 1
    check n[2][0][0].name == "A"
    check n[2][1][0].kind == nkDotExpr

  test "shared array type across names":
    let n = parseGo("func f(a, b [3]int) {}")
    check n[2].len == 1
    check n[2][0].len == 3
    check n[2][0][2][0].valInt == 3

  test "generic instantiation as param type":
    let n = parseGo("func g(x T[P]) {}")
    check n[2][0][1][0].name == "T"
    check n[2][0][1][1].name == "P"

  test "named variadic param":
    let n = parseGo("func Or[T comparable](vals ...T) T { return zero }")
    check n[2][0][0].name == "vals"
    check n[2][0][1].kind == nkPrefix
    check n[2][0][1][0].name == "..."

  test "tilde constraint on slice":
    let n = parseGo("func Insert[S ~[]E, E any](s S, i int, v E) {}")
    check n[0][1][1].kind == nkPrefix
    check n[0][1][1][0].name == "~"
    check n[0][1][1][1][0].kind == nkEmpty

  test "multi-value var keeps type slot":
    let n = parseGo("var x, y = 1, 2")
    check n[1].len == 4
    check n[1][2].kind == nkEmpty
    check n[1][3].kind == nkStatement
    check n[1][3].len == 2

  test "call args with commas are not assignments":
    let n = parseGo("f(a, b)")
    check n.kind == nkCall
    check n.len == 3

  test "guard with call base":
    let n = parseGo("switch v := foo(x).(type) { case int: a() }")
    check n[2][0].name == "v"
    check n[2][1].kind == nkCall

  test "invalid declarations error like gc":
    expect OpenAstParsingError:
      discard parseGo("var c, pkg.T")
    expect OpenAstParsingError:
      discard parseGo("type S struct { A, B }")
    expect OpenAstParsingError:
      discard parseGo("var x")

suite "Go parser (Phase 3: composite literals)":
  test "bare and keyed struct literals":
    let n = parseGo("x := Point{1, 2}")
    check n[2].kind == nkObjConstr
    check n[2][0].name == "Point"
    check n[2].len == 3
    let k = parseGo("x := T{A: 1, B: 2}")
    check k[2][1].kind == nkColonExpr
    check k[2][1][0].name == "A"
    check k[2].len == 3

  test "empty literal and statement literal":
    check parseGo("x := T{}")[2].len == 1
    check parseGo("Point{1, 2}").kind == nkObjConstr

  test "slice, array, ellipsis and map literals":
    let s = parseGo("x := []int{1, 2}")
    check s[2][0][0].kind == nkEmpty
    check s[2][0][1].name == "int"
    let a = parseGo("x := [3]int{2: 5}")
    check a[2][0][0].valInt == 3
    check a[2][1].kind == nkColonExpr
    let e = parseGo("x := [...]int{1}")
    check e[2][0][0].name == "..."
    let m = parseGo("x := map[string]int{\"a\": 1}")
    check m[2][0][0].name == "map"
    check m[2][1].kind == nkColonExpr

  test "anonymous struct and address-of literals":
    let s = parseGo("x := struct{A int}{A: 1}")
    check s[2][0][0].name == "struct"
    let p = parseGo("x := &T{A: 1}")
    check p[2].kind == nkPrefix
    check p[2][0].name == "&"
    check p[2][1].kind == nkObjConstr
    let d = parseGo("x := *T{}")
    check d[2][0].name == "*"
    check d[2][1].kind == nkObjConstr

  test "nested and elided literals":
    let n = parseGo("x := [][]int{{1}, {2}}")
    check n[2][1].kind == nkObjConstr
    check n[2][1][0].kind == nkEmpty
    let m = parseGo("x := map[string]Point{\"o\": {1, 2}}")
    check m[2][1][1].kind == nkObjConstr
    check m[2][1][1][0].kind == nkEmpty

  test "literals in calls, returns and sends":
    let c = parseGo("f(T{A: 1}, 2)")
    check c[1].kind == nkObjConstr
    let r = parseGo("return T{}, nil")
    check r[1].kind == nkObjConstr
    let v = parseGo("var x = T{A: 1}")
    check v[1][2].kind == nkObjConstr

  test "header ambiguity follows go/parser":
    # Bare `T {` in a header opens the body (spec: must parenthesize).
    expect OpenAstParsingError:
      discard parseGoStmts("if T{} == x {}")
    check parseGo("if x {}").kind == nkStatement
    # Structural bases still parse in headers and ranges.
    check parseGo("if []int{1}[0] == 1 {}").kind == nkStatement
    check parseGo("for v := range []int{1, 2} {}").kind == nkStatement
    check parseGoStmts("switch x { case Point{1, 2}: }").len == 1

suite "Go parser (Phase 3: assertions, slices, conversions)":
  test "type assertions":
    let n = parseGo("x := v.(T)")
    check n[2].kind == nkTypeAssert
    check n[2][0].name == "v"
    check n[2][1].name == "T"
    let d = parseGo("x := v.Interface().(Unmarshaler)")
    check d[2].kind == nkTypeAssert
    check d[2][0].kind == nkCall
    let c = parseGo("x := a.(B).(C)")
    check c[2].kind == nkTypeAssert
    check c[2][0].kind == nkTypeAssert

  test "two-index slices":
    let f = parseGo("x := s[1:2]")
    check f[2][1].kind == nkColonExpr
    check f[2][1].len == 2
    let l = parseGo("x := s[:2]")
    check l[2][1][0].kind == nkEmpty
    let h = parseGo("x := s[1:]")
    check h[2][1][1].kind == nkEmpty
    let b = parseGo("x := s[:]")
    check b[2][1][0].kind == nkEmpty
    check b[2][1][1].kind == nkEmpty

  test "three-index slices and index preservation":
    let t = parseGo("x := s[1:2:3]")
    check t[2][1].len == 3
    let m = parseGo("x := s[:2:3]")
    check m[2][1][0].kind == nkEmpty
    let i = parseGo("x := s[i]")
    check i[2].len == 2
    check i[2][1].name == "i"
    expect OpenAstParsingError:
      discard parseGo("x := s[i:j:]")
    expect OpenAstParsingError:
      discard parseGo("x := s[i::k]")

  test "conversions are calls on types":
    check parseGo("x := int(v)")[2].kind == nkCall
    check parseGo("x := string(b)")[2].kind == nkCall
    let s = parseGo("x := []byte(str)")
    check s[2].kind == nkCall
    check s[2][0].kind == nkBracketExpr
    check parseGo("x := interface{}(nil)")[2].kind == nkCall

  test "spread call arguments":
    let n = parseGo("f(s...)")
    check n[1].kind == nkCall
    check n[1][0].name == "spread"
    let a = parseGo("append(s, x...)")
    check a[2].kind == nkCall

  test "func literal values and trailing calls":
    let v = parseGo("f := func() int { return 1 }")
    check v[2].kind == nkFunction
    let g = parseGo("go func() {}()")
    check g[1].kind == nkCall
    let d = parseGo("defer func(x int) { _ = x }(42)")
    check d[1].kind == nkCall
    check d[1].len == 2
    # Empty parens are never a receiver; `int` needs paren-lookahead.
    let m = parseGoStmts("func (r T) M(a int) int { return a }")
    check m[0][0].name == "M"
    check m[0][1].kind == nkIdentDefs

  test "literals continue past postfix and binary operators":
    let i = parseGo("x := []int{1}[0]")
    check i[2].kind == nkBracketExpr
    check i[2][0].kind == nkObjConstr
    let e = parseGo("x := T{1} == U{2}")
    check e[2].kind == nkInfix
    check e[2][0].name == "=="
    check e[2][1].kind == nkObjConstr
    check e[2][2].kind == nkObjConstr

  test "struct results keep their bodies":
    let n = parseGoStmts("func (c T) Done() <-chan struct{} {\n\tx := 1\n}")
    check n[0][4].kind == nkBlock
    let m = parseGo("x := map[string]int{\"a\": 1}")
    check m[2].kind == nkObjConstr

  test "comments around returns and literals":
    let b = parseGoStmts("func f() {\nreturn // done\n}")
    check b[0][4][0].len == 1
    check b[0][4].len == 2
    let r = parseGo("return x, y")
    check r.len == 3
    let c = parseGo("x := T{A: 1, B: 2}")
    check c[2].len == 3
    let ml = parseGoStmts("x := T{\n// leading\nA: 1,\nB: 2,\n}")
    check ml[0][2].kind == nkObjConstr

suite "Go parser (numbers and const elision)":
  test "extended float forms":
    check parseGo("x := 1.")[2].valFloat == 1.0
    check parseGo("x := 1.e10")[2].valFloat == 1e10
    check parseGo("x := .5")[2].valFloat == 0.5
    check parseGo("x := 1e1_0")[2].valFloat == 1e10
    check parseGo("x := 1_000")[2].valInt == 1000
    check parseGo("x := 0x_12")[2].valInt == 18
    check parseGo("x := 0755")[2].valInt == 493

  test "hex floats":
    check parseGo("x := 0x1p-2")[2].valFloat == 0.25
    check parseGo("x := 0x1.P1")[2].valFloat == 2.0
    check parseGo("x := 0x.8p1")[2].valFloat == 1.0
    check parseGo("x := 0x1P+2")[2].valFloat == 4.0

  test "imaginary literals":
    let n = parseGo("x := 1i")
    check n[2].kind == nkImaginary
    check n[2].valImag == "1i"
    check parseGo("x := 1.5i")[2].valImag == "1.5i"
    check parseGo("x := 1e10i")[2].valImag == "1e10i"
    check parseGo("x := 0xFFi")[2].valImag == "0xFFi"
    check parseGo("x := 0x1p-2i")[2].valImag == "0x1p-2i"
    check parseGo("x := .5i")[2].valImag == ".5i"
    check parseGo("const im = 1i")[1][2].kind == nkImaginary

  test "grouped const inherits expressions":
    let n = parseGoStmts("const (\nKB = 1 << 10\nMB\n)")
    check n[0].len == 3
    check n[0][2][0].name == "MB"
    check n[0][2][1].kind == nkEmpty
    check n[0][2][2].kind == nkEmpty
    expect OpenAstParsingError:
      discard parseGoStmts("const (\nx\n)")
    expect OpenAstParsingError:
      discard parseGo("const x")
    expect OpenAstParsingError:
      discard parseGo("var x")

  test "body-less func is syntactically fine":
    let n = parseGoStmts("func stub()\nfunc main() {}")
    check n[0][0].name == "stub"
    check n[0][4].kind == nkEmpty

suite "Go parser (comprehensive fixture)":
  test "go_comprehensive.go parses fully":
    let nodes = parseGoFile(goFixtureDir / "go_comprehensive.go")
    var decls = 0
    var imags = 0
    var tags = 0
    var unpos = 0
    proc walk(n: Node) =
      if n == nil: return
      if n.kind == nkImaginary: inc imags
      if n.kind == nkLitString and "json" in n.valStr: inc tags
      if n.kind != nkEmpty and n.ln == 0: inc unpos
      if n.kind notin {nkEmpty, nkNil, nkLitBool, nkLitInt, nkLitFloat,
          nkLitString, nkLitBigInt, nkIdent, nkImaginary}:
        for c in n.children: walk(c)
    for n in nodes:
      if n != nil and n.kind notin {nkInlineComment, nkDocComment}:
        inc decls
      walk(n)
    check decls == 24
    check imags == 6
    check tags == 3
    check unpos == 0

suite "Go parser (Phase 4: declaration fidelity)":
  test "mixed named and unnamed parameters error like gc":
    expect OpenAstParsingError:
      discard parseGo("func f(a int, string) {}")
    expect OpenAstParsingError:
      discard parseGo("func f() (a int, string) {}")
    # Leading provisionals share the following type (`string` is a name
    # here); only trailing bare items are mixed.
    let r = parseGo("func f(string, a int) {}")
    check r[2].len == 1
    check r[2][0].len == 3
    check r[2][0][0].name == "string"
    # All-unnamed and all-named lists stay separate shapes.
    let u = parseGo("func f(int, string) {}")
    check u[2].len == 2
    let n = parseGo("func f(a, b int) {}")
    check n[2].len == 1
    check n[2][0].len == 3

  test "type parameter lists require names with constraints":
    expect OpenAstParsingError:
      discard parseGo("func f[]() {}")
    expect OpenAstParsingError:
      discard parseGo("func f[T any, U](x T) {}")
    expect OpenAstParsingError:
      discard parseGo("func f[T, U](x T) {}")
    expect OpenAstParsingError:
      discard parseGo("type A[T any, U] any")
    let s = parseGo("func f[T, U any](x T, y U) {}")
    check s[0][0].name == "f"
    check s[0][1].len == 3
    check s[0][1][0].name == "T"
    check s[0][1][1].name == "U"
    check s[0][1][2].name == "any"

  test "union constraints in type parameters":
    let u = parseGo("func f[T ~int | ~string](x T) {}")
    check u[0][1][0].name == "T"
    check u[0][1][1].kind == nkPrefix
    check u[0][1][1][0].name == "~"
    check u[0][1][1][1].kind == nkInfix
    check u[0][1][1][1][0].name == "|"
    # A bare union is an unnamed constraint, not a named parameter.
    expect OpenAstParsingError:
      discard parseGo("func f[T|U](x T) {}")
    expect OpenAstParsingError:
      discard parseGo("func f(T ~int) {}")
    expect OpenAstParsingError:
      discard parseGo("func f(T|U) {}")

  test "methods and interface methods reject type parameters":
    expect OpenAstParsingError:
      discard parseGo("func (r T) M[T any](x T) {}")
    expect OpenAstParsingError:
      discard parseGo("type I interface { M[T any](x T) }")
    # Embedded instantiations are not methods.
    check parseGo("type I interface { L[K] }")[1][3][1].kind == nkBracketExpr
    check parseGo("type I interface { M[T, U] }")[1][3][1].kind == nkBracketExpr

  test "array lengths and type parameters tilt like go/parser":
    let a = parseGo("type A[5]int")
    check a[1][1].kind == nkEmpty
    check a[1][3][0].valInt == 5
    check a[1][3][1].name == "int"
    check parseGo("type A[]int")[1][3][0].kind == nkEmpty
    check parseGo("type A[...]int")[1][3][0].name == "..."
    check parseGo("type A[T|U] any")[1][3][0].kind == nkInfix
    check parseGo("type A[T *int] any")[1][3][0].kind == nkInfix
    let g = parseGo("type A[T any] B[T]")
    check g[1][1][0][1].name == "any"

  test "named declarations and imports are top-level-only":
    expect OpenAstParsingError:
      discard parseGoStmts("func f() { func g() {} }")
    expect OpenAstParsingError:
      discard parseGoStmts("func f() { func (r T) M() {} }")
    expect OpenAstParsingError:
      discard parseGoStmts("func f() { import \"x\" }")
    expect OpenAstParsingError:
      discard parseGoStmts("func f() { package p }")
    # Anonymous literals nest freely, with working bodies.
    let lit = parseGoStmts("func f() { g := func() { a, b := 1, 2; _ = a + b } }")
    check lit[0][4][0][2].kind == nkFunction

suite "Go parser (Phase 4: statement fidelity)":
  test "go and defer operands must be calls":
    expect OpenAstParsingError:
      discard parseGoStmts("func f() { go x }")
    expect OpenAstParsingError:
      discard parseGoStmts("func f() { defer x }")
    check parseGo("go f(x)")[1].kind == nkCall
    check parseGo("go func() {}()")[1].kind == nkCall
    check parseGo("defer int(x)")[1].kind == nkCall

  test "goto labels count only on the same line":
    let s = parseGoStmts("func f() { goto done; done: }")
    check s[0][4][0][1].name == "done"
    let n = parseGoStmts("func f() {\ngoto\ndone\ndone:\n}")
    check n[0][4][0][1].kind == nkEmpty
    check n[0][4][1].kind == nkIdent
    check n[0][4][1].name == "done"
    check n[0][4][2][2].kind == nkEmpty

  test "fallthrough takes no operand":
    expect OpenAstParsingError:
      discard parseGoStmts("func f() { switch x { case 1: fallthrough g(); case 2: h() } }")
    check parseGoStmts("func f() { switch x { case 1: fallthrough; case 2: h() } }").len == 1

  test "labels and empty statements":
    let e = parseGoStmts("func f() { done: }")
    check e[0][4][0][2].kind == nkEmpty
    check parseGoStmts("func f() { done: ; }").len == 1
    check parseGoStmts("func f() { ; }")[0][4][0].kind == nkEmpty

  test "select match arity errors like gc":
    expect OpenAstParsingError:
      discard parseGoStmts("func f() { select { case a, b, c := <-ch: g() } }")
    expect OpenAstParsingError:
      discard parseGoStmts("func f() { select { case a, b <- ch: g() } }")
    let two = parseGoStmts("func f() { select { case a, b := <-ch: g() } }")
    check two[0][4][0][1][1][0][0].name == ":="
    check parseGoStmts("func f() { select { case <-ch: g() } }").len == 1
    # go/parser does not check that assign matches receive.
    check parseGoStmts("func f() { select { case x := 1: g() } }").len == 1

  test "range variables and switch prelude edge cases":
    expect OpenAstParsingError:
      discard parseGoStmts("func f() { for a, b, c := range m { g() } }")
    check parseGoStmts("func f() { for a, b := range m { g() } }").len == 1
    let sw = parseGoStmts("func f() { switch ; { case 1: g() } }")
    check sw[0][4][0][1].kind == nkEmpty
    check sw[0][4][0][2].kind == nkEmpty
