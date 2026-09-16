import std/[unittest, os]
import ../src/sweetsyntax
import ../src/sweetsyntax/tokenizer
import ../src/sweetsyntax/languages/js as jsHandlersMod

const jsFixtureDir = currentSourcePath().parentDir / "data" / "js"

const jsFeatures = {featAsync, featArrowFn, featGenerators,
                    featLabeledStmt, featTemplateLit}

proc parseJS(code: string): Node =
  let syntax = getKnownSyntax(KnownSyntax.js)
  var p = compile(syntax.spec)
  p.lexer = initLexer(syntax.spec, code)
  jsHandlersMod.jsHandlers(p)
  p.features = p.features + jsFeatures
  p.curr = p.getToken()
  p.next = p.getToken()
  parseStatement(p)

proc parseJSFile(path: string): seq[Node] =
  let syntax = getKnownSyntax(KnownSyntax.js)
  var p = compile(syntax.spec)
  p.lexer = initLexerFromFile(syntax.spec, path)
  jsHandlersMod.jsHandlers(p)
  p.features = p.features + jsFeatures
  p.curr = p.getToken()
  p.next = p.getToken()
  while p.curr.kind != tkEOF:
    result.add(parseStatement(p))

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

suite "JavaScript fixtures":
  test "d3.js parses":
    let nodes = parseJSFile(jsFixtureDir / "d3.js")
    check nodes.len >= 1
    var total = 0
    for n in nodes: total += countNodes(n)
    echo "d3 AST nodes: ", total
    check total > 100000

  test "react-dom.development.js parses":
    let nodes = parseJSFile(jsFixtureDir / "react-dom.development.js")
    check nodes.len >= 1
    var total = 0
    for n in nodes: total += countNodes(n)
    echo "react-dom AST nodes: ", total
    check total > 100000
