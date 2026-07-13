import std/[unittest, tables]
import ../src/sweetsyntax
import ../src/sweetsyntax/tokenizer
import ../src/sweetsyntax/languages/js as jsHandlersMod
import ../src/sweetsyntax/languages/nim as nimHandlersMod
import ../src/sweetsyntax/languages/c as cHandlersMod

proc parseJS(code: string): Node =
  let syntax = getKnownSyntax(KnownSyntax.js)
  var p = compile(syntax.spec)
  p.lexer = initLexer(syntax.spec, code)
  jsHandlersMod.jsHandlers(p)
  p.curr = p.getToken()
  p.next = p.getToken()
  parseStatement(p)

proc parseNim(code: string): Node =
  let syntax = getKnownSyntax(KnownSyntax.nim)
  var p = compile(syntax.spec)
  p.lexer = initLexer(syntax.spec, code)
  nimHandlersMod.nimHandlers(p)
  p.features.incl(featCommandSyntax)
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

suite "Nim parser":
  test "proc declaration":
    let n = parseNim("proc foo() = discard")
    check n.kind == nkFunction

  test "let binding":
    let n = parseNim("let x = 42")
    check n.kind == nkStatement

  test "type definition":
    let n = parseNim("type Foo = int")
    check n.kind == nkStatement

  test "if statement":
    let n = parseNim("if true: discard")
    check n.kind == nkStatement

  test "case statement":
    let n = parseNim("case x\nof 1: discard\nelse: discard")
    check n.kind == nkStatement

  test "for loop":
    let n = parseNim("for i in 0..10: discard")
    check n.kind == nkStatement

proc parseC(code: string): Node =
  let syntax = getKnownSyntax(KnownSyntax.c)
  var p = compile(syntax.spec)
  p.lexer = initLexer(syntax.spec, code)
  cHandlersMod.cHandlers(p)
  p.curr = p.getToken()
  p.next = p.getToken()
  parseStatement(p)

suite "C parser":
  test "variable declaration":
    let n = parseC("int x = 42;")
    check n.kind == nkStatement

  test "function definition":
    let n = parseC("int main() { return 0; }")
    check n.kind == nkFunction

  test "if-else statement":
    let n = parseC("if (x) { return 1; } else { return 2; }")
    check n.kind == nkStatement

  test "while loop":
    let n = parseC("while (i < 10) { i = i + 1; }")
    check n.kind == nkStatement

  test "for loop":
    let n = parseC("for (int i = 0; i < 10; i++) { }")
    check n.kind == nkStatement

  test "pointer declaration":
    let n = parseC("int *p = NULL;")
    check n.kind == nkStatement

  test "struct declaration":
    let n = parseC("struct point { int x; int y; };")
    check n.kind == nkStatement

  test "enum declaration":
    let n = parseC("enum color { RED, GREEN, BLUE };")
    check n.kind == nkStatement
