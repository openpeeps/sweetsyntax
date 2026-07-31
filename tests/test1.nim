import std/[unittest, tables, strutils]
import pkg/openparser/json
import ../src/sweetsyntax
import ../src/sweetsyntax/tokenizer
import ../src/sweetsyntax/languages/js as jsHandlersMod
import ../src/sweetsyntax/languages/nim as nimHandlersMod
import ../src/sweetsyntax/languages/c as cHandlersMod
import ../src/sweetsyntax/renderers/jsonrenderer
import ../src/sweetsyntax/renderers/foldrenderer

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

suite "JSON renderer":
  proc highlight(code: string): seq[JsonNode] =
    let syntax = getKnownSyntax(KnownSyntax.c)
    var lx = initLexer(syntax.spec, code)
    var lines = highlightJsonLd(lx).splitLines()
    for line in lines:
      if line.len > 0:
        result.add(parseJson(line))

  test "each token emits one NDJSON line":
    let tokens = highlight("int x = 42;")
    check tokens.len == 5
    check tokens[0]["kind"].getStr == "ident"
    check tokens[0]["scope"].getStr == "storage.type"
    check tokens[0]["value"].getStr == "int"
    check tokens[1]["value"].getStr == "x"
    check tokens[1]["scope"].getStr == "variable"
    check tokens[2]["scope"].getStr == "keyword.operator"
    check tokens[3]["kind"].getStr == "int"
    check tokens[3]["scope"].getStr == "constant.numeric.integer"
    check tokens[3]["value"].getStr == "42"

  test "comments, strings and doc comments get scopes":
    let tokens = highlight("""// line
/* block */
/** doc */
char c = 'a';
""")
    check tokens[0]["kind"].getStr == "comment"
    check tokens[0]["scope"].getStr == "comment.line"
    check tokens[1]["kind"].getStr == "comment"
    check tokens[1]["scope"].getStr == "comment.line"
    check tokens[2]["kind"].getStr == "doc_comment"
    check tokens[2]["scope"].getStr == "comment.block.documentation"
    check tokens[3]["scope"].getStr == "storage.type"
    check tokens[6]["kind"].getStr == "string"
    check tokens[6]["value"].getStr == "'a'"

  test "offsets are non-overlapping and slice to the token value":
    let code = "int x = 42;"
    let tokens = highlight(code)
    check tokens[0]["start"].getInt == 0
    check tokens[0]["stop"].getInt == 3
    for i in 0 ..< tokens.len:
      let start = tokens[i]["start"].getInt
      let stop = tokens[i]["stop"].getInt
      check start < stop
      check code[start ..< stop] == tokens[i]["value"].getStr

suite "Fold renderer":
  proc folds(code: string, mode: FoldMode = fmAuto,
             pre = false): seq[FoldRegion] =
    let syntax = getKnownSyntax(KnownSyntax.c)
    var lx = initLexer(syntax.spec, code)
    computeFolds(lx, mode, pre)

  test "brace folding of a function body":
    let regions = folds("int main() {\n  return 0;\n}")
    check regions.len == 1
    check regions[0].kind == fkBlock
    check regions[0].startLine == 1
    check regions[0].endLine == 3

  test "nested braces produce nested regions":
    let regions = folds("void f() {\n  if (x) {\n    y();\n  }\n}")
    check regions.len == 2
    check regions[0].kind == fkBlock
    check regions[0].startLine == 1
    check regions[0].endLine == 5
    check regions[1].kind == fkBlock
    check regions[1].startLine == 2
    check regions[1].endLine == 4

  test "same-line braces and braces in strings do not fold":
    check folds("int x; { foo(); }").len == 0
    check folds("char *s = \"{\";\n}").len == 0

  test "multi-line block and doc comments fold, single-line do not":
    let blockRegs = folds("/* line1\n   line2 */\nint x;")
    check blockRegs.len == 1
    check blockRegs[0].kind == fkComment
    check blockRegs[0].startLine == 1
    check blockRegs[0].endLine == 2
    let doc = folds("/** doc\n    more */\nint x;")
    check doc.len == 1
    check doc[0].kind == fkDocComment
    check folds("// single line\nint x;").len == 0

  test "preprocessor folding is opt-in":
    let code = "#if 0\nint x;\n#endif"
    check folds(code).len == 0
    let regions = folds(code, pre = true)
    check regions.len == 1
    check regions[0].kind == fkPreprocessor
    check regions[0].startLine == 1
    check regions[0].endLine == 3

  test "indent folding of python-style blocks":
    let regions = folds("def f():\n    x = 1\n    y = 2", fmIndent)
    check regions.len == 1
    check regions[0].kind == fkIndent
    check regions[0].startLine == 1
    check regions[0].endLine == 3

  test "indent folding handles nested blocks and else branches":
    let nested = folds("def f():\n    if x:\n        pass\n    y = 1", fmIndent)
    check nested.len == 2
    check nested[0].startLine == 1 and nested[0].endLine == 4
    check nested[1].startLine == 2 and nested[1].endLine == 3
    let branches = folds("if x:\n    a()\nelse:\n    b()", fmIndent)
    check branches.len == 2
    check branches[0].startLine == 1 and branches[0].endLine == 2
    check branches[1].startLine == 3 and branches[1].endLine == 4

  test "indent folding ignores comment-only lines":
    let regions = folds("def f():\n    # note\n    x = 1", fmIndent)
    check regions.len == 1
    check regions[0].startLine == 1
    check regions[0].endLine == 3

  test "foldsToJsonLd emits parseable NDJSON":
    let syntax = getKnownSyntax(KnownSyntax.c)
    var lx = initLexer(syntax.spec, "int main() {\n  return 0;\n}")
    var lines = foldsToJsonLd(computeFolds(lx)).splitLines()
    for line in lines:
      if line.len == 0:
        continue
      let node = parseJson(line)
      check node["kind"].getStr == "block"
      check node["start"]["line"].getInt == 1
      check node["end"]["line"].getInt == 3
