import std/[unittest, os]
import ../src/sweetsyntax
import ../src/sweetsyntax/tokenizer
import ../src/sweetsyntax/languages/c as cHandlersMod

const cFixtureDir = currentSourcePath().parentDir / "data" / "c"

proc parseC(code: string): Node =
  let syntax = getKnownSyntax(KnownSyntax.c)
  var p = compile(syntax.spec)
  p.lexer = initLexer(syntax.spec, code)
  cHandlersMod.cHandlers(p)
  p.features.incl(featLabeledStmt)
  p.features.incl(featAdjacentConcat)
  p.curr = p.getToken()
  p.next = p.getToken()
  parseStatement(p)

proc parseCFile(path: string): seq[Node] =
  let syntax = getKnownSyntax(KnownSyntax.c)
  var p = compile(syntax.spec)
  p.lexer = initLexerFromFile(syntax.spec, path)
  cHandlersMod.cHandlers(p)
  p.features.incl(featLabeledStmt)
  p.features.incl(featAdjacentConcat)
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

  test "preprocessor directive":
    let n = parseC("#include <stdio.h>\nint x = 1;")
    check n.kind == nkStatement
    check n[0].name == "directive"
    check n[1].name == "include"

  test "adjacent string literals concatenate":
    let n = parseC("const char *s = \"a\" \"b\";")
    check n.kind == nkStatement

  test "cast expression":
    let n = parseC("unsigned u = (unsigned) x;")
    check n.kind == nkStatement

  test "sizeof type and expression":
    check parseC("int n = sizeof(int);").kind == nkStatement
    check parseC("int n = sizeof *p;").kind == nkStatement

suite "C fixtures":
  test "libevent event.c parses":
    let nodes = parseCFile(cFixtureDir / "libevent_event.c")
    check nodes.len >= 1
    var total = 0
    for n in nodes: total += countNodes(n)
    echo "libevent event.c AST nodes: ", total
    check total > 1000
