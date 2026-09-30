import std/[unittest, strutils, os]
import pkg/openparser/json
import ../src/sweetsyntax
import ../src/sweetsyntax/renderers/highlight

suite "highlight proc":
  test "every known syntax highlights to all formats":
    let samples = [
      (KnownSyntax.js, "const x = 42;"),
      (KnownSyntax.nim, "echo 42"),
      (KnownSyntax.c, "int x = 42;"),
      (KnownSyntax.cpp, "int x = 42;"),
      (KnownSyntax.go, "package main"),
      (KnownSyntax.ruby, "puts 42"),
      (KnownSyntax.php, "echo 42;"),
      (KnownSyntax.py, "x = 42"),
      (KnownSyntax.rust, "let x = 42;"),
      (KnownSyntax.d, "int x = 42;"),
      (KnownSyntax.css, ".foo { color: red; }"),
      (KnownSyntax.md, "# Hello"),
    ]
    for (lang, code) in samples:
      let ascii = highlight(lang, code, hfAscii)
      let html = highlight(lang, code, hfHtml)
      let js = highlight(lang, code, hfJson)
      check ascii.len > 0
      check html.len > 0
      check js.len > 0

  test "invalid code still highlights without parsing":
    # `if (` is a parse error everywhere but must still tokenize
    check highlight(KnownSyntax.js, "if (", hfHtml).len > 0
    check highlight(KnownSyntax.nim, "if (", hfAscii).len > 0
    check highlight(KnownSyntax.c, "int x = ;", hfJson).len > 0
    check highlight(KnownSyntax.cpp, "template<", hfJson).len > 0

  test "html preserves whitespace between tokens":
    let html = highlight(KnownSyntax.c, "int x;", hfHtml)
    check "int</span> <span" in html

  test "ascii without color returns raw source":
    check highlight(KnownSyntax.c, "int x = 42;",
      hfAscii, useColor = false) == "int x = 42;"

  test "json lines parse with kind/scope/value":
    let lines = highlight(KnownSyntax.c, "int x = 42;", hfJson).splitLines()
    var count = 0
    for line in lines:
      if line.len == 0:
        continue
      let node = parseJson(line)
      check node.hasKey("kind")
      check node.hasKey("scope")
      check node.hasKey("value")
      inc count
    check count == 5

  test "filters on by default: md heading and css class scopes":
    let mdScopes = highlight(KnownSyntax.md, "# H\n", hfJson)
    check "markup.heading" in mdScopes
    let cssScopes = highlight(KnownSyntax.css, ".foo { color: red; }", hfJson)
    check "selector.class" in cssScopes

  test "syntaxForExt resolves common extensions":
    check syntaxForExt("js") == KnownSyntax.js
    check syntaxForExt(".jsx") == KnownSyntax.js
    check syntaxForExt("TS") == KnownSyntax.ts
    check syntaxForExt("nim") == KnownSyntax.nim
    check syntaxForExt("c") == KnownSyntax.c
    check syntaxForExt("cpp") == KnownSyntax.cpp
    check syntaxForExt(".hpp") == KnownSyntax.cpp
    check syntaxForExt("cc") == KnownSyntax.cpp
    check syntaxForExt("rb") == KnownSyntax.ruby
    check syntaxForExt("php") == KnownSyntax.php
    check syntaxForExt("css") == KnownSyntax.css
    check syntaxForExt("markdown") == KnownSyntax.md

  test "syntaxForExt raises on unknown extension":
    expect SweetHighlightError:
      discard syntaxForExt("xyz")

  test "highlightFile resolves by extension and highlights":
    let dir = getTempDir() / "sweetsyntax_highlight_test"
    createDir(dir)
    let mdPath = dir / "doc.md"
    writeFile(mdPath, "# Hello\n")
    check "markup.heading" in highlightFile(mdPath, hfJson)
    let cssPath = dir / "style.css"
    writeFile(cssPath, ".foo { color: red; }")
    check "selector.class" in highlightFile(cssPath, hfJson)
    let jsPath = dir / "app.jsx"
    writeFile(jsPath, "const x = 42;")
    check "const" in highlightFile(jsPath, hfHtml)
    let cppPath = dir / "main.cpp"
    writeFile(cppPath, "int main() { return 0; }")
    check "storage.type" in highlightFile(cppPath, hfJson)

  test "highlightFile raises on unknown extension or missing ext":
    let dir = getTempDir() / "sweetsyntax_highlight_test"
    createDir(dir)
    let badPath = dir / "file.xyz"
    writeFile(badPath, "hello")
    expect SweetHighlightError:
      discard highlightFile(badPath, hfHtml)
    expect SweetHighlightError:
      discard highlightFile(dir / "noext", hfHtml)

  test "highlightFile names the offending extension":
    let dir = getTempDir() / "sweetsyntax_highlight_test"
    createDir(dir)
    let badPath = dir / "file.xyz"
    writeFile(badPath, "hello")
    try:
      discard highlightFile(badPath, hfHtml)
      check false
    except SweetHighlightError as e:
      check ".xyz" in e.msg
