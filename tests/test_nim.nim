import std/unittest
import ../src/sweetsyntax
import ../src/sweetsyntax/tokenizer
import ../src/sweetsyntax/languages/nim as nimHandlersMod

proc parseNim(code: string): Node =
  let syntax = getKnownSyntax(KnownSyntax.nim)
  var p = compile(syntax.spec)
  p.lexer = initLexer(syntax.spec, code)
  nimHandlersMod.nimHandlers(p)
  p.features.incl(featCommandSyntax)
  p.curr = p.getToken()
  p.next = p.getToken()
  parseStatement(p)

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
