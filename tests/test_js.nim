import std/unittest
import ../src/sweetsyntax
import ../src/sweetsyntax/tokenizer
import ../src/sweetsyntax/languages/js as jsHandlersMod

proc parseJS(code: string): Node =
  let syntax = getKnownSyntax(KnownSyntax.js)
  var p = compile(syntax.spec)
  p.lexer = initLexer(syntax.spec, code)
  jsHandlersMod.jsHandlers(p)
  p.curr = p.getToken()
  p.next = p.getToken()
  parseStatement(p)

suite "JavaScript parser":
  test "variable declaration":
    let n = parseJS("let x = 42;")
    check n.kind == nkStatement

  test "function declaration":
    let n = parseJS("function foo() {}")
    check n.kind == nkFunction

  test "arrow function":
    let n = parseJS("(x) => x + 1")
    check n.kind == nkFunction

  test "if statement with brace body":
    let n = parseJS("if (true) { let x = 1; }")
    check n.kind == nkStatement

  test "object literal":
    let n = parseJS("({a: 1, b: 2})")
    check n.kind notin {nkEmpty}
