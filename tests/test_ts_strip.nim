import std/[unittest, strutils]
import ../src/sweetsyntax
import ../src/sweetsyntax/tokenizer
import ../src/sweetsyntax/engine/[ast, parser]
import ../src/sweetsyntax/languages/ts as tsHandlersMod

proc parseSpans(code: string): seq[StripSpan] =
  let syntax = getKnownSyntax(KnownSyntax.ts)
  var p = compile(syntax.spec)
  p.lexer = initLexer(syntax.spec, code)
  tsHandlersMod.tsHandlers(p)
  p.features = p.features + {featAsync, featArrowFn, featGenerators,
    featLabeledStmt, featTemplateLit}
  p.curr = p.getToken()
  p.next = p.getToken()
  while p.curr.kind != tkEOF:
    discard parseStatement(p)
  p.stripSpans

proc slices(code: string): seq[(StripKind, string)] =
  # NOTE: `..<` stores an inclusive end (`9 ..< 10` -> a=9, b=9), so
  # slice with `..` here.
  for s in parseSpans(code):
    result.add((s.kind, code[s.span.a .. s.span.b]))

suite "TypeScript lowering spans":
  test "erasure preserves newlines":
    let code = "let x: Foo<Bar> = 1;\nlet y = 2;\n"
    # Nested erasures (inner generic args + whole annotation) merge
    # in the consumer.
    check slices(code) ==
      @[(skErase, "<Bar>"), (skErase, ": Foo<Bar>")]

  test "type-only declarations erase whole":
    check slices("type A = string;") == @[(skErase, "type A = string;")]
    check slices("interface I { x: string; }") ==
      @[(skErase, "interface I { x: string; }")]
    check slices("declare const x: number;") ==
      @[(skErase, ": number"), (skErase, "declare const x: number;")]
    check slices("import type { A } from \"m\";") ==
      @[(skErase, "import type { A } from \"m\";")]
    check slices("export type { A };") ==
      @[(skErase, "export type { A };")]

  test "as and satisfies erase from the keyword":
    check slices("let v = x as string;") == @[(skErase, "as string")]
    check slices("let v = <string>x;") == @[(skErase, "<string>")]

  test "non-null assertion erases the marker":
    check slices("let v = x!;") == @[(skErase, "!")]

  test "functions erase generics, params, returns":
    check slices("function f<T>(x: T): T { return x; }") ==
      @[(skErase, "<T>"), (skErase, ": T"), (skErase, ": T")]

  test "overload signatures erase, lone declarations error":
    check slices("function f(x: string): void; function f(x: any) { }") ==
      @[(skErase, ": string"), (skErase, ": void"),
        (skErase, "function f(x: string): void;"), (skErase, ": any")]
    check slices("function f(x: string): void; function f(x: number): void; function f(x: any) { }") ==
      @[(skErase, ": string"), (skErase, ": void"),
        (skErase, "function f(x: string): void;"),
        (skErase, ": number"), (skErase, ": void"),
        (skErase, "function f(x: number): void;"), (skErase, ": any")]
    let bad = parseSpans("function f(x: string): void;")
    check bad.len == 3
    check bad[^1].kind == skError

  test "class members erase types and modifiers":
    let got = slices("class C extends Base<T> implements I { private x: number = 1; }")
    check got == @[(skErase, "<T>"), (skErase, "implements I"),
      (skErase, "private "), (skErase, ": number")]

  test "enum records members":
    let spans = parseSpans("enum E { A, B = 2, C = \"x\" };")
    check spans.len == 1
    check spans[0].kind == skEnum
    check spans[0].text == "E"
    check spans[0].members.len == 3
    check spans[0].members[0].name == "A"
    check spans[0].members[0].initKind == ikAuto
    check spans[0].members[1].initKind == ikInt
    check spans[0].members[1].intVal == 2
    check spans[0].members[2].initKind == ikStr
    check spans[0].members[2].initSpan.a > 0
    check "enum E { A, B = 2, C = \"x\" };"[spans[0].members[2].initSpan.a ..
      spans[0].members[2].initSpan.b] == "\"x\""

  test "using and import-assign rewrite keywords":
    check slices("using r = get();") ==
      @[(skReplace, "using")]
    check parseSpans("using r = get();")[0].text == "const"
    check slices("import x = require(\"m\");") ==
      @[(skReplace, "import")]
    check slices("import x = A.B.C;") ==
      @[(skReplace, "import")]

  test "export-eq records a span":
    let spans = parseSpans("export = foo;")
    check spans.len == 1
    check spans[0].kind == skExportEq

  test "namespace records a path":
    let spans = parseSpans("namespace A.B { export const x = 1; }")
    check spans.len == 2
    var nsIdx = -1
    var kwIdx = -1
    for i, s in spans:
      if s.kind == skNamespace: nsIdx = i
      if s.kind == skExportKw: kwIdx = i
    check nsIdx >= 0
    check kwIdx >= 0
    check spans[nsIdx].path == @["A", "B"]

  test "decorators record an error":
    let spans = parseSpans("@dec class C {}")
    check spans[^1].kind == skError
    check "ecorator" in spans[^1].text

  test "nested generics erase the split closer":
    check slices("let f = g<A<B>>();") ==
      @[(skErase, "<B>>"), (skErase, "<A<B>>")]

  test "this-params erase with the comma":
    check slices("class C { constructor(this: Foo, x: number) {} }") ==
      @[(skErase, "this: Foo,"), (skErase, ": number")]

  test "catch annotations erase":
    check slices("try {} catch (e: any) {}") ==
      @[(skErase, ": any")]

  test "constructor parameter properties synthesize assignments":
    let spans = parseSpans("class C { constructor(private x: number, readonly y = 1) {} }")
    var found = false
    for s in spans:
      if s.kind == skReplace and s.text.contains("this.x = x"):
        found = true
        check s.text.contains("this.y = y")
    check found
