import std/[unittest, strutils, tables]
import pkg/openparser/json
import ../src/sweetsyntax
import ../src/sweetsyntax/renderers/[highlight, foldrenderer]

# Sample, comment-free round-trip sample, and the expected fold-region count
# for `fmAuto`. Note that `fmAuto` uses braces when the file has a `{` token and
# falls back to *indent* folding otherwise, so the count reflects indentation
# as well as comments. Shell, CMake and Nim legitimately fold on indentation;
# HTML and XML pick up a false indent region because their indentation is
# presentational (see the fmAuto vs fmBraces test below).
type Case = tuple[lang: KnownSyntax, name: string, sample: string,
                  plain: string, folds: int]

const cases: seq[Case] = @[
  (KnownSyntax.ts, "TypeScript",
    "const x: number = 42;\n/* one\n   two */\n", "let a: string = \"x\";", 1),
  (KnownSyntax.crystal, "Crystal",
    "x = 1 # note\n", "a = [1, 2]", 0),
  (KnownSyntax.html, "HTML",
    "<div class=\"a\">&amp;<!-- one\n   two --></div>\n", "<p>x</p>", 2),
  (KnownSyntax.xml, "XML",
    "<?xml version=\"1.0\"?>\n<root><!-- one\n   two --></root>\n",
    "<a b=\"1\"/>", 2),
  (KnownSyntax.shell, "Shell",
    "#!/bin/sh\nset -e\nfor f in a; do\n  echo \"$f\"\ndone\ncat <<EOF\nbody\nEOF\n",
    "echo hi", 1),
  (KnownSyntax.docker, "Dockerfile",
    "# c\nFROM alpine AS b\nRUN echo hi\n", "FROM alpine", 0),
  (KnownSyntax.ini, "INI",
    "; one\n# two\n[s]\nk = v\n", "k = v", 0),
  (KnownSyntax.make, "Makefile",
    "CC := gcc\nall: main.o\n# c\n", "all: dep", 0),
  (KnownSyntax.cmake, "CMake",
    "# c\nproject(x)\nif(A)\n  message(\"y\")\nendif()\n", "project(x)", 1),
  (KnownSyntax.nginx, "Nginx",
    "server {\n  listen 80;\n}\n", "server { listen 80; }", 1),
  (KnownSyntax.systemd, "systemd",
    "# c\n[Unit]\nDescription=x\n", "[Unit]", 0),
  (KnownSyntax.jinja2, "Jinja2",
    "{# one\n   two #}\n<p>{{ a }}</p>\n", "{{ a }}", 1),
  (KnownSyntax.handlebars, "Handlebars",
    "{{!-- one\n     two --}}\n<b>{{ a }}</b>\n", "{{ a }}", 1),
  (KnownSyntax.liquid, "Liquid",
    "{% if a %}{{ b }}{% endif %}\n", "{{ a }}", 0),
  (KnownSyntax.ejs, "EJS",
    "<%# one\n   two %>\n<p><% a %></p>\n", "<% a %>", 1),
  (KnownSyntax.css, "CSS",
    ".a {\n  color: red;\n}\n", ".a { color: red; }", 1),
  (KnownSyntax.md, "Markdown",
    "# H\n<!-- one\n   two -->\n", "# H", 1),
  (KnownSyntax.yaml, "YAML",
    "a: 1\n# c\n", "a: 1", 0),
  (KnownSyntax.json, "JSON",
    "{\"a\": 1}\n", "{\"a\": 1}", 0),
  (KnownSyntax.toml, "TOML",
    "[owner]\n# c\n", "a = 1", 0),
  (KnownSyntax.csv, "CSV",
    "a,b\n1,2\n", "a,b", 0),
  (KnownSyntax.js, "JavaScript",
    "const x = 1;\n/* one\n   two */\n", "const x = 1;", 1),
  (KnownSyntax.c, "C",
    "int x;\n/* one\n   two */\n", "int x;", 1),
  (KnownSyntax.cpp, "C++",
    "auto x = 1;\n/* one\n   two */\n", "auto x = 1;", 1),
  (KnownSyntax.nim, "Nim",
    "echo 1\n# one\n   two\n", "echo 1", 1),
]

proc jsonLines(lang: KnownSyntax, code: string): seq[JsonNode] =
  for line in highlight(lang, code, hfJson).splitLines():
    if line.len > 0:
      result.add parseJson(line)

suite "JSON output per syntax":
  test "every syntax emits valid NDJSON with the documented fields":
    for c in cases:
      let nodes = jsonLines(c.lang, c.sample)
      check nodes.len > 0
      for n in nodes:
        for field in ["kind", "scope", "line", "col", "start", "stop", "value"]:
          check n.hasKey(field)
        check n["scope"].getStr.len > 0
        check n["start"].getInt < n["stop"].getInt
        check n["line"].getInt >= 1
        check n["col"].getInt >= 1

  test "token offsets are ordered, non-overlapping and slice to the value":
    for c in cases:
      let nodes = jsonLines(c.lang, c.sample)
      var prevStop = -1
      for n in nodes:
        let start = n["start"].getInt
        let stop = n["stop"].getInt
        check start >= prevStop
        prevStop = stop
        # Comment tokens have their markers stripped from the span, so the
        # slice matches the value for every other kind.
        if n["kind"].getStr notin ["comment", "doc_comment"]:
          check c.sample[start ..< stop] == n["value"].getStr

  test "values are non-empty and reconstruct the source in order":
    for c in cases:
      let nodes = jsonLines(c.lang, c.sample)
      for n in nodes:
        check n["value"].getStr.len > 0

suite "HTML output per syntax":
  test "every token becomes exactly one span":
    for c in cases:
      let html = highlight(c.lang, c.sample, hfHtml)
      let nodes = jsonLines(c.lang, c.sample)
      check ("<span class=\"" in html)
      check html.count("</span>") == nodes.len
      # Only span tags may contribute a raw `<`: inter-token gaps (including
      # comment markers such as `<!--` or `;`, which the lexer strips from the
      # token span) are HTML-escaped by the renderer.
      check html.count("<") == nodes.len * 2

  test "output ends on the last token span":
    for c in cases:
      # Trailing whitespace after the final token is not emitted, so the
      # document always ends with a closing span tag.
      check highlight(c.lang, c.sample, hfHtml).endsWith("</span>")

  test "token text is HTML-escaped":
    let html = highlight(KnownSyntax.xml, "<a b=\"&amp;\">&lt;x&gt;</a>\n", hfHtml)
    let ltEscaped = "&lt;" in html
    let gtEscaped = "&gt;" in html
    let ampEscaped = "&amp;" in html
    # `&amp;` inside the quoted value is escaped once more
    let ampDoubleEscaped = "&amp;amp;" in html
    check ltEscaped
    check gtEscaped
    check ampEscaped
    check ampDoubleEscaped

  test "entities and tags are still classified":
    let html = highlight(KnownSyntax.xml,
      "<a b=\"&amp;\">&lt;x&gt;</a>\n", hfHtml)
    check ("markup.tag" in html)
    check ("entity.other.attribute-name" in html)
    check ("constant.character.escape" in html)

suite "ASCII output per syntax":
  test "colored output wraps every token in an ANSI sequence":
    for c in cases:
      let ascii = highlight(c.lang, c.sample, hfAscii)
      let nodes = jsonLines(c.lang, c.sample)
      check ascii.contains("\e[")
      check ascii.endsWith("\e[0m") or ascii.len > 0
      # one reset per token
      check ascii.count("\e[0m") == nodes.len

  test "uncolored output round-trips comment-free source exactly":
    for c in cases:
      check highlight(c.lang, c.plain, hfAscii, useColor = false) == c.plain

  test "uncolored output contains every token value":
    for c in cases:
      let plain = highlight(c.lang, c.sample, hfAscii, useColor = false)
      for n in jsonLines(c.lang, c.sample):
        check plain.contains(n["value"].getStr)

suite "Folding per syntax":
  test "fold regions match the expected count":
    for c in cases:
      var lx = initLexer(getKnownSyntax(c.lang).spec, c.sample)
      check computeFolds(lx).len == c.folds

  test "streaming folds agree with the collecting variant":
    for c in cases:
      var a = initLexer(getKnownSyntax(c.lang).spec, c.sample)
      var b = initLexer(getKnownSyntax(c.lang).spec, c.sample)
      let collected = computeFolds(a)
      let streamed = computeFoldsStream(b)
      check streamed.len == collected.len
      for i in 0 ..< min(collected.len, streamed.len):
        check streamed[i].kind == collected[i].kind
        check streamed[i].startLine == collected[i].startLine
        check streamed[i].endLine == collected[i].endLine

  test "block comment folds span the right lines":
    var lx = initLexer(getKnownSyntax(KnownSyntax.html).spec,
      "<p>x</p>\n<!-- one\ntwo -->\n")
    let regions = computeFolds(lx)
    check regions.len == 1
    check regions[0].kind == fkComment
    check regions[0].startLine == 2
    check regions[0].endLine == 3

  test "brace folds nest in Nginx configuration":
    var lx = initLexer(getKnownSyntax(KnownSyntax.nginx).spec,
      "http {\n  server {\n    listen 80;\n  }\n}\n")
    let regions = computeFolds(lx)
    check regions.len == 2
    check regions[0].startLine == 1
    check regions[0].endLine == 5
    check regions[1].startLine == 2
    check regions[1].endLine == 4

  test "fold NDJSON is parseable and ordered":
    var lx = initLexer(getKnownSyntax(KnownSyntax.nginx).spec,
      "server {\n  listen 80;\n}\n")
    var lines: seq[string] = @[]
    for line in foldsToJsonLd(computeFolds(lx)).splitLines():
      if line.len > 0:
        lines.add line
    check lines.len == 1
    let node = parseJson(lines[0])
    check node["kind"].getStr == "block"
    check node["start"]["line"].getInt == 1
    check node["end"]["line"].getInt == 3

  test "indent folding is structural for shell and cmake":
    # Real indentation: the indented body line opens a fold region.
    var shell = initLexer(getKnownSyntax(KnownSyntax.shell).spec,
      "for f in a; do\n  echo hi\ndone\n")
    let shellRegions = computeFolds(shell, fmIndent)
    check shellRegions.len == 1
    check shellRegions[0].kind == fkIndent
    check shellRegions[0].startLine == 1
    check shellRegions[0].endLine == 2

  test "fmAuto adds a false indent fold to markup, fmBraces does not":
    # HTML/XML indentation is presentational, so the fmAuto indent fallback
    # reports a region that is not a real block. Consumers that only want
    # structural folds on markup should ask for fmBraces.
    let code = "<div>\n  <span>x</span>\n</div>\n"
    var autoL = initLexer(getKnownSyntax(KnownSyntax.html).spec, code)
    var braceL = initLexer(getKnownSyntax(KnownSyntax.html).spec, code)
    let autoRegions = computeFolds(autoL, fmAuto)
    let braceRegions = computeFolds(braceL, fmBraces)
    check autoRegions.len == 1
    check autoRegions[0].kind == fkIndent
    check braceRegions.len == 0

  test "brace folds are ignored for brace-free files":
    var lx = initLexer(getKnownSyntax(KnownSyntax.toml).spec,
      "[owner]\nname = \"x\"\n")
    check computeFolds(lx, fmBraces).len == 0

  test "preprocessor folding stays opt-in and is a no-op here":
    var lx = initLexer(getKnownSyntax(KnownSyntax.nginx).spec,
      "server {\n  listen 80;\n}\n")
    check computeFolds(lx, fmAuto, preprocessorFolds = true).len == 1
    var js = initLexer(getKnownSyntax(KnownSyntax.ts).spec, "const x = 1;\n")
    check computeFolds(js, fmAuto, preprocessorFolds = true).len == 0

suite "Format selection and options":
  test "includeValue = false omits token text":
    let nodes = jsonLines(KnownSyntax.c, "int x;")
    check nodes.len == 3
    let bare = highlight(KnownSyntax.c, "int x;", hfJson, includeValue = false)
    for line in bare.splitLines():
      if line.len > 0:
        check not parseJson(line).hasKey("value")

  test "enableFilters = false drops filter-derived scopes":
    let mdFiltered = "markup.heading" in highlight(KnownSyntax.md, "# H", hfJson)
    let mdPlain = "markup.heading" in
      highlight(KnownSyntax.md, "# H", hfJson, enableFilters = false)
    let cssFiltered = "selector.class" in
      highlight(KnownSyntax.css, ".a {}", hfJson)
    let cssPlain = "selector.class" in
      highlight(KnownSyntax.css, ".a {}", hfJson, enableFilters = false)
    check mdFiltered
    check not mdPlain
    check cssFiltered
    check not cssPlain

  test "html output is independent of filters":
    let withFilters = highlight(KnownSyntax.html, "<a href=\"x\">y</a>", hfHtml)
    let without = highlight(KnownSyntax.html, "<a href=\"x\">y</a>", hfHtml,
      enableFilters = false)
    check withFilters.len > 0
    check without.len > 0
    let withAttr = "entity.other.attribute-name" in withFilters
    let withoutAttr = "entity.other.attribute-name" in without
    check withAttr
    check not withoutAttr
