import std/[unittest, strutils, os, sequtils]
import pkg/openparser/json
import ../src/sweetsyntax
import ../src/sweetsyntax/renderers/highlight

type Tok = tuple[kind: string, value: string, attrs: seq[string]]

proc tokens(lang: KnownSyntax, code: string): seq[Tok] =
  let syntax = getKnownSyntax(lang)
  var lx = initLexer(syntax.spec, code, enableFilters = true)
  var tok = lx.getToken()
  while tok.kind != tkEOF:
    result.add(($tok.kind, lx.getTokenValue(tok), tok.attr))
    tok = lx.getToken()

proc findAttr(toks: seq[Tok], value: string, attr: string): bool =
  for t in toks:
    if t.value == value and attr in t.attrs:
      return true
  false

proc findKind(toks: seq[Tok], value: string, kind: string): bool =
  for t in toks:
    if t.value == value and t.kind == kind:
      return true
  false

suite "YAML lexer":
  test "mapping keys get property.name":
    let toks = tokens(KnownSyntax.yaml, "name: value\nempty:\n")
    check findAttr(toks, "name", "property.name")
    check findAttr(toks, "empty", "property.name")

  test "urls are not mistaken for keys":
    let toks = tokens(KnownSyntax.yaml, "url: http://example.com\n")
    check findAttr(toks, "url", "property.name")
    check not findAttr(toks, "http", "property.name")

  test "comments lex as comments":
    let toks = tokens(KnownSyntax.yaml, "# note\nkey: v\n")
    check findKind(toks, "note", "comment")

  test "document marker, tags and anchors":
    let toks = tokens(KnownSyntax.yaml,
      "---\nkey: !!str\nref: &a 1\nuse: *a\n")
    # `---` lexes as three `-` puncts; the filter hit covers all three
    check findAttr(toks, "-", "markup.frontmatter")
    check findAttr(toks, "str", "entity.name.tag")
    check findAttr(toks, "a", "entity.name.tag")

  test "block scalar indicator":
    let toks = tokens(KnownSyntax.yaml, "text: |\n  raw\n")
    check findAttr(toks, "|", "markup.indicator")

  test "quoted scalars are strings and booleans are identifiers":
    let toks = tokens(KnownSyntax.yaml, "a: \"x\"\nb: 'y'\nc: true\nd: null\n")
    check findKind(toks, "\"x\"", "string")
    check findKind(toks, "'y'", "string")
    check findAttr(toks, "true", "true")
    check findAttr(toks, "null", "null")

suite "JSON lexer":
  test "object keys get property.name":
    let toks = tokens(KnownSyntax.json, """{"key": "value", "n": 1}""")
    check findAttr(toks, "\"key\"", "property.name")
    check findAttr(toks, "\"n\"", "property.name")
    check not findAttr(toks, "\"value\"", "property.name")

  test "literals and nesting":
    let toks = tokens(KnownSyntax.json,
      """{"a": [1, 2.5, true, false, null], "b": {"c": "d"}}""")
    check findKind(toks, "{", "punct")
    check findKind(toks, "[", "punct")
    check findKind(toks, "1", "int")
    check findKind(toks, "2.5", "float")
    check findAttr(toks, "true", "true")
    check findAttr(toks, "null", "null")

  test "hash is not a comment in JSON":
    let toks = tokens(KnownSyntax.json, """{"a": "#notcomment"}""")
    check not findKind(toks, "#notcomment", "comment")
    check findKind(toks, "\"#notcomment\"", "string")

suite "TOML lexer":
  test "keys and tables":
    let toks = tokens(KnownSyntax.toml, "title = \"TOML\"\n[owner]\nname = 'x'\n")
    check findAttr(toks, "title", "property.name")
    check findAttr(toks, "name", "property.name")
    check findAttr(toks, "owner", "entity.name.tag")

  test "date-times and times":
    let toks = tokens(KnownSyntax.toml, "dob = 1979-05-27T07:32:00Z\n")
    check findAttr(toks, "1979", "constant.numeric.date")
    check findAttr(toks, "27", "constant.numeric.date")

  test "comments and multi-line strings":
    let toks = tokens(KnownSyntax.toml, "# c\ns = \"\"\"a\nb\"\"\"\n")
    check findKind(toks, "c", "comment")
    check toks.anyIt(it.kind == "string" and it.value.startsWith("\"\"\""))

suite "CSV lexer":
  test "fields, numbers and quoted fields":
    let toks = tokens(KnownSyntax.csv, "a,b,c\n1,2.5,3\n\"x,y\",z,NA\n")
    check findKind(toks, ",", "punct")
    check findKind(toks, "1", "int")
    check findKind(toks, "2.5", "float")
    check findKind(toks, "\"x,y\"", "string")
    check findAttr(toks, "NA", "NA")

suite "Data format scopes":
  test "YAML key scope is variable.other.property":
    let jsonLd = highlight(KnownSyntax.yaml, "name: value\n", hfJson)
    check "variable.other.property" in jsonLd

  test "JSON key scope is variable.other.property":
    check "variable.other.property" in
      highlight(KnownSyntax.json, """{"a": 1}""", hfJson)

  test "TOML table scope is entity.name.tag":
    check "entity.name.tag" in
      highlight(KnownSyntax.toml, "[owner]\n", hfJson)

  test "YAML frontmatter scope":
    check "markup.frontmatter" in highlight(KnownSyntax.yaml, "---\na: 1\n", hfJson)

  test "all data formats highlight to every output format":
    for lang in [KnownSyntax.yaml, KnownSyntax.json, KnownSyntax.toml,
                 KnownSyntax.csv]:
      check highlight(lang, "a: 1", hfHtml).len > 0
      check highlight(lang, "a: 1", hfAscii).len > 0
      check highlight(lang, "a: 1", hfJson).len > 0

suite "Data format extensions":
  test "syntaxForExt resolves data extensions":
    check syntaxForExt("yaml") == KnownSyntax.yaml
    check syntaxForExt("yml") == KnownSyntax.yaml
    check syntaxForExt("json") == KnownSyntax.json
    check syntaxForExt("toml") == KnownSyntax.toml
    check syntaxForExt("csv") == KnownSyntax.csv
    check syntaxForExt("tsv") == KnownSyntax.csv

  test "highlightFile resolves data extensions":
    let dir = getTempDir() / "sweetsyntax_data_test"
    createDir(dir)
    let cases = {
      "conf.yaml": ("name: value\n", "variable.other.property"),
      "conf.yml": ("name: value\n", "variable.other.property"),
      "data.json": ("{\"a\": 1}", "variable.other.property"),
      "conf.toml": ("[owner]\n", "entity.name.tag"),
      "rows.csv": ("a,b\n1,2\n", "punct"),
    }.toTable
    for (name, pair) in cases.pairs:
      let path = dir / name
      writeFile(path, pair[0])
      check highlightFile(path, hfJson).len > 0
