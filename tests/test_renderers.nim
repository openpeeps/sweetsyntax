import std/[unittest, strutils]
import pkg/openparser/json
import ../src/sweetsyntax
import ../src/sweetsyntax/renderers/jsonrenderer
import ../src/sweetsyntax/renderers/foldrenderer

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

  test "comments with no trailing text keep a non-zero span":
    let code = "//\n/* */\n/**/\nint x;"
    let tokens = highlight(code)
    check tokens[0]["kind"].getStr == "comment"
    check tokens[1]["kind"].getStr == "comment"
    check tokens[2]["kind"].getStr == "doc_comment"
    for i in 0 ..< 3:
      let start = tokens[i]["start"].getInt
      let stop = tokens[i]["stop"].getInt
      check start < stop

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
