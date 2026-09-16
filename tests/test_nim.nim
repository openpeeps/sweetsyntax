import std/[unittest, os, strutils]
import ../src/sweetsyntax
import ../src/sweetsyntax/tokenizer
import ../src/sweetsyntax/languages/nim as nimHandlersMod

const nimFixtureDir = currentSourcePath().parentDir / "data" / "nim"

proc parseNim(code: string): Node =
  let syntax = getKnownSyntax(KnownSyntax.nim)
  var p = compile(syntax.spec)
  p.lexer = initLexer(syntax.spec, code)
  nimHandlersMod.nimHandlers(p)
  p.features.incl(featCommandSyntax)
  p.curr = p.getToken()
  p.next = p.getToken()
  parseStatement(p)

proc parseNimFile(path: string): seq[Node] =
  let syntax = getKnownSyntax(KnownSyntax.nim)
  var p = compile(syntax.spec)
  p.lexer = initLexerFromFile(syntax.spec, path)
  nimHandlersMod.nimHandlers(p)
  p.features.incl(featCommandSyntax)
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

proc countUnpositioned(n: Node): int =
  ## Nodes without line info (`nkEmpty` placeholders excluded).
  if n == nil or n.kind == nkEmpty:
    return 0
  if n.ln == 0 and n.col == 0:
    result = 1
  case n.kind
  of nkEmpty, nkNil, nkLitBool, nkLitInt, nkLitFloat, nkLitString,
     nkLitBigInt, nkIdent:
    discard
  else:
    for c in n.children:
      result += countUnpositioned(c)

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

  test "typed let splits type and default":
    let n = parseNim("let x: int = 5")
    check n.kind == nkStatement
    check n[1].kind == nkIdentDefs
    check n[1][0].name == "x"
    check n[1][1].kind == nkIdent
    check n[1][1].name == "int"
    check n[1][2].kind == nkLitInt

  test "shared names and types":
    let n = parseNim("let a, b: int")
    check n[1].kind == nkIdentDefs
    check n[1][0].name == "a"
    check n[1][1].name == "b"
    check n[1][2].name == "int"

  test "var section parses multiple definitions":
    let n = parseNim("var\n  x = 1\n  y: string = \"s\"\n")
    check n.kind == nkStatement
    check n[0].name == "var"
    check n[1].kind == nkIdentDefs
    check n[2].kind == nkIdentDefs
    check n[2][0].name == "y"

  test "var parameter wraps in nkVarTy":
    let n = parseNim("proc f(items: var seq[int]) = discard")
    check n.kind == nkFunction
    check n[2][0][1].kind == nkVarTy

  test "semicolon-separated params":
    let n = parseNim("proc f(a: int; b: string) = discard")
    check n[2].len == 2
    check n[2][1][0].name == "b"

  test "generic constraint":
    let n = parseNim("proc f[T: string](x: T) = discard")
    check n[2].kind == nkBracketExpr
    check n[2][0].kind == nkIdentDefs
    check n[2][0][0].name == "T"

  test "defer statement":
    check parseNim("defer: foo()").kind == nkStatement

  test "echo call":
    let n = parseNim("echo \"a\", 1")
    check n.kind == nkCall
    check n[0].name == "echo"
    check n.len == 3

  test "static block":
    let n = parseNim("static:\n  foo()\n")
    check n.kind == nkStatement
    check n[0].name == "static"

  test "table constructor":
    let n = parseNim("let t = {\"a\": 1}")
    check n[1][2].kind == nkBlock
    check n[1][2][0].kind == nkColonExpr

  test "if expression":
    let n = parseNim("let x = if t: a else: b")
    check n[1][2].kind == nkStatement
    check n[1][2][0].name == "if"

  test "command call on field access":
    let n = parseNim("a.b c")
    check n.kind == nkCall
    check n[0].kind == nkDotExpr

  test "do block fuses into command":
    let n = parseNim("quote do:\n  x\n")
    check n.kind == nkCall
    check n[0].name == "quote"

  test "percent prefix":
    let n = parseNim("let j = %x")
    check n[1][2].kind == nkPrefix

  test "string interpolation prefix":
    let n = parseNim("let s = &\"a{b}c\"")
    check n[1][2].kind == nkPrefix
    check n[1][2][0].name == "&"

  test "binary literal type suffix":
    let n = parseNim("let x = 0b1010'u8")
    check n[1][2].kind == nkLitInt
    check n[1][2].valInt == 10

  test "cast call":
    let n = parseNim("let c = cast[int](3.5)")
    check n[1][2].kind == nkCall

  test "export marker on proc":
    let n = parseNim("proc f*() = discard")
    check n[1].kind == nkPostfix

suite "Nim fixtures":
  test "comprehensive fixture parses with positions":
    let nodes = parseNimFile(nimFixtureDir / "nim_comprehensive.nim")
    check nodes.len >= 1
    var total = 0
    var missing = 0
    for n in nodes:
      total += countNodes(n)
      missing += countUnpositioned(n)
    echo "nim_comprehensive.nim AST nodes: ", total
    check total > 400
    check missing == 0

suite "dumpTree":
  test "leaf values render as kind=value with 2-space indent":
    let n = parseNim("folds.sort")
    check dumpTree(n) == "nkDotExpr\n  nkIdent=folds\n  nkIdent=sort\n"

  test "literals render their values":
    check dumpTree(parseNim("let x = 42")[1][2]) == "nkLitInt=42\n"
    check dumpTree(parseNim("let s = \"hi\"")[1][2]) == "nkLitString=\"hi\"\n"
    check dumpTree(parseNim("let b = true")[1][2]) == "nkLitBool=true\n"

  test "nested tree indents two spaces per level":
    let n = parseNim("a.b c")
    let lines = dumpTree(n).splitLines()
    check lines[0] == "nkCall"
    check lines[1] == "  nkDotExpr"
    check lines[2] == "    nkIdent=a"
    check lines[3] == "    nkIdent=b"
    check lines[4] == "  nkIdent=c"

  test "program overload renders all top-level nodes":
    let a = parseNim("a")
    let b = parseNim("b")
    let prog = OpenAstProgram(nodes: @[a, b])
    check dumpTree(prog) == dumpTree(a) & dumpTree(b)
    check dumpTree(prog).splitLines()[0] == treeRepr(a)
