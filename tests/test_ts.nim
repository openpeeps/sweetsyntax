import std/[unittest, os]
import ../src/sweetsyntax
import ../src/sweetsyntax/tokenizer
import ../src/sweetsyntax/languages/ts as tsHandlersMod
import ../src/sweetsyntax/languages/js as jsHandlersMod

const tsFeatures = {featAsync, featArrowFn, featGenerators,
                    featLabeledStmt, featTemplateLit}

proc parseTS(code: string, isTSX = false): Node =
  let syntax = getKnownSyntax(KnownSyntax.ts)
  var p = compile(syntax.spec)
  p.lexer = initLexer(syntax.spec, code)
  tsHandlersMod.tsHandlers(p)
  p.features = p.features + tsFeatures
  p.isTSX = isTSX
  p.curr = p.getToken()
  p.next = p.getToken()
  parseStatement(p)

proc parseJS(code: string): Node =
  let syntax = getKnownSyntax(KnownSyntax.js)
  var p = compile(syntax.spec)
  p.lexer = initLexer(syntax.spec, code)
  jsHandlersMod.jsHandlers(p)
  p.features = p.features + tsFeatures
  p.curr = p.getToken()
  p.next = p.getToken()
  parseStatement(p)

proc parseJSAll(code: string): seq[Node] =
  let syntax = getKnownSyntax(KnownSyntax.js)
  var p = compile(syntax.spec)
  p.lexer = initLexer(syntax.spec, code)
  jsHandlersMod.jsHandlers(p)
  p.features = p.features + tsFeatures
  p.curr = p.getToken()
  p.next = p.getToken()
  while p.curr.kind != tkEOF:
    result.add(parseStatement(p))

proc parseTSFile(path: string): seq[Node] =
  let syntax = getKnownSyntax(KnownSyntax.ts)
  var p = compile(syntax.spec)
  p.lexer = initLexerFromFile(syntax.spec, path)
  tsHandlersMod.tsHandlers(p)
  p.features = p.features + tsFeatures
  p.curr = p.getToken()
  p.next = p.getToken()
  while p.curr.kind != tkEOF:
    result.add(parseStatement(p))

suite "TypeScript declarations":
  test "type alias":
    let n = parseTS("type A = string;")
    check n.kind == nkStatement
    check n.children[0].name == "type"

  test "generic type alias with union":
    let n = parseTS("type Box<T> = T | null;")
    check n.kind == nkStatement
    check n.children[1].name == "Box"
    check n.children[2].kind == nkIdentDefs

  test "interface with members":
    let n = parseTS("interface P { name: string; age?: number; }")
    check n.kind == nkInterface

  test "interface extends":
    let n = parseTS("interface A extends B, C<T> { x: T; }")
    check n.kind == nkInterface
    check n.children[2].kind == nkStatement

  test "enum and const enum":
    check parseTS("enum E { A, B = 2, C = \"x\" }").kind == nkStatement
    let n = parseTS("const enum F { A }")
    check n.kind == nkStatement
    check n.children[0].name == "const"

  test "namespace and module":
    check parseTS("namespace A.B { export const x = 1; }").kind == nkStatement
    check parseTS("module \"m\" { export const x = 1; }").kind == nkStatement

  test "declare function and declare module":
    check parseTS("declare function f(): void;").kind == nkStatement
    check parseTS("declare module \"m\" { const x: number; }").kind == nkStatement
    check parseTS("declare global { var x: number; }").kind == nkStatement
    check parseTS("declare const x: number;").kind == nkStatement

  test "abstract class":
    let n = parseTS("abstract class C { abstract m(): void; }")
    check n.kind == nkStatement
    check n.children[0].name == "abstract"

  test "using declarations":
    check parseTS("using x = get();").kind == nkStatement
    let n = parseTS("await using y: T = get();")
    check n.kind == nkPrefix

suite "TypeScript types":
  test "unions, intersections, arrays":
    check parseTS("let x: A | B & C[];").kind == nkStatement
    check parseTS("let v: T[K];").kind == nkStatement
    check parseTS("let w: T[\"key\"][];").kind == nkStatement
    check parseTS("let g: Promise<T[K]>;").kind == nkStatement

  test "tuples with labels, optionals and rest":
    check parseTS("let t: [first: string, second?: number, ...rest: string[]];").kind == nkStatement

  test "conditional and infer":
    check parseTS("type C<T> = T extends U ? A : B;").kind == nkStatement
    check parseTS("type U<T> = T extends infer R ? R : never;").kind == nkStatement

  test "keyof, typeof, mapped":
    check parseTS("let k: keyof T;").kind == nkStatement
    check parseTS("let t: typeof foo.bar;").kind == nkStatement
    check parseTS("type M<T> = { [K in keyof T]: T[K] };").kind == nkStatement

  test "function and construct types":
    check parseTS("let f: (x: string) => number;").kind == nkStatement
    check parseTS("let c: new (x: string) => Foo;").kind == nkStatement

  test "object type with call and index signatures":
    check parseTS("let o: { (x: string): number; [k: string]: any };").kind == nkStatement
    check parseTS("interface F { <T>(x: T): T; new (x: string): F; }").kind == nkInterface

  test "template literal types are opaque literals":
    check parseTS("let s: `prefix-${string}`;").kind == nkStatement

  test "assertion signatures":
    check parseTS("function isStr(x: any): asserts x is string { }").kind == nkFunction
    check parseTS("function a(x: any): asserts x { }").kind == nkFunction

suite "TypeScript expressions":
  test "as and satisfies take type operands":
    let n = parseTS("let x = y as const;")
    check n.kind == nkStatement
    let m = parseTS("let x = y satisfies Foo<Bar>;")
    check m.kind == nkStatement
    check parseTS("const t = await fetchData() satisfies Response;").kind == nkStatement

  test "non-null assertion and optional chaining":
    check parseTS("let x = a!.b?.c;").kind == nkStatement

  test "generic calls commit, comparisons do not":
    let n = parseTS("foo<Bar>(x);")
    check n.kind == nkCall
    check n.children[0].kind == nkBracketExpr
    let m = parseTS("a < b;")
    check m.kind == nkInfix
    let k = parseTS("a < b && c>(x);")
    check k.kind == nkInfix

  test "nested generic args split >> correctly":
    let n = parseTS("let x = foo<A<B<C>>>(y);")
    check n.kind == nkStatement

  test "new with type arguments":
    check parseTS("let x = new Foo<Bar>(y);").kind == nkStatement
    check parseTS("let x = new Foo(y);").kind == nkStatement

  test "angle assertion in ts, rejected in tsx":
    let n = parseTS("let x = <string>y;")
    check n.kind == nkStatement
    check n.children[^1].children[^1].kind == nkCast
    expect OpenAstParsingError:
      discard parseTS("let x = <string>y;", isTSX = true)
    check parseTS("let x = y as string;", isTSX = true).kind == nkStatement

  test "assertion over parenthesized operand":
    for code in ["let y = <string>(a);", "let y = <string>(a + b);"]:
      let n = parseTS(code)
      check n.kind == nkStatement
      check n.children[^1].children[^1].kind == nkCast

  test "generic arrows":
    let n = parseTS("const f = <T>(x: T): T => x;")
    check n.kind == nkStatement
    check parseTS("const f = <T>(x: T): T => x;", isTSX = true).kind == nkStatement
    check parseTS("type F = <T>(x: T) => T;").kind == nkStatement

  test "async typed and generic arrows":
    check parseTS("const f = async (x: string): Promise<string> => x;").kind == nkStatement
    check parseTS("const f = async <T>(x: T) => x;").kind == nkStatement

  test "typed for-loop variables and object literal methods":
    check parseTS("for (let x: Foo<Bar> of xs) { }").kind == nkStatement
    check parseTS("for (const [k, v] of Object.entries(o)) { }").kind == nkStatement
    let n = parseTS("const o = { m<T>(x: T): T { return x; }, async n() { } };")
    check n.kind == nkStatement

suite "TypeScript classes":
  test "generics, extends and implements":
    let n = parseTS("class C<T> extends Base<T> implements I, J<T> { }")
    check n.kind == nkStatement
    check n.children[2].kind == nkIdentDefs

  test "static blocks":
    check parseTS("class C { static { init(); } }").kind == nkStatement
    check parseJS("class C { static { init(); } }").kind == nkStatement

  test "decorators on class and members":
    let n = parseTS("@Component({}) class C { @Input() x: string = \"\"; }")
    check n.kind == nkPragmaBlock
    let m = parseTS("class C { @ dec async method<T>(x: T): T { return x; } }")
    check m.kind == nkStatement

  test "parameter properties and modifiers":
    check parseTS("class C { constructor(private x: string, readonly y?: number) { } }").kind == nkStatement
    check parseTS("class C { static count = 0; declare name: string; accessor v: number = 1; }").kind == nkStatement

  test "overloads without bodies":
    check parseTS("class C { m(x: string): void; m(x: number): void { } }").kind == nkStatement

  test "function overloads":
    check parseTS("function f(x: string): void; function f(x: any) { }").kind == nkFunction

suite "TypeScript modules":
  test "import type and export type":
    let n = parseTS("import type { A } from \"m\";")
    check n.kind == nkImport
    check n.children[^1].name == "type"
    let m = parseTS("export type { A };")
    check m.kind == nkStatement
    check parseTS("import x = require(\"m\");").kind == nkImport
    check parseTS("export = foo;").kind == nkStatement

  test "export default with declarations":
    check parseTS("export default function f() { }").kind == nkStatement
    check parseTS("export default interface I { x: string; }").kind == nkStatement

  test "exported declarations delegate":
    check parseTS("export interface I { x: string; }").kind == nkStatement
    check parseTS("export abstract class C { }").kind == nkStatement

suite "TypeScript via parseScript":
  test ".ts and .tsx files route to tsHandlers with the tsx flag":
    let dir = getTempDir() / "sweetsyntax_ts_test"
    createDir(dir)
    let tsPath = dir / "a.ts"
    writeFile(tsPath, "let x = <string>y;\n")
    check parseScript(tsPath, tsHandlersMod.tsHandlers).nodes.len == 1
    let tsxPath = dir / "b.tsx"
    writeFile(tsxPath, "let x = y as string;\n")
    check parseScript(tsxPath, tsHandlersMod.tsHandlers).nodes.len == 1
    expect OpenAstParsingError:
      let badPath = dir / "c.tsx"
      writeFile(badPath, "let x = <string>y;\n")
      discard parseScript(badPath, tsHandlersMod.tsHandlers)

suite "JSDoc-typed JavaScript still parses":
  test "@param and @type annotations are inert doc comments":
    ## A leading doc comment is its own statement; the declaration follows.
    ## (A trailing `;` at EOF may add a JS `nkEmpty`, so check order.)
    let a = parseJSAll("/** @param {string} x */ function f(x) { return x; }")
    check a.len == 2
    check a[0].kind == nkDocComment
    check a[1].kind == nkFunction
    let b = parseJSAll("/** @type {string} */ let x = \"a\";")
    check b.len >= 2
    check b[0].kind == nkDocComment
    check b[1].kind == nkStatement
    let c = parseJSAll("/** @returns {number} */ function g() { return 1; }")
    check c.len == 2
    check c[1].kind == nkFunction
