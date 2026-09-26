import std/[unittest, strutils]
import pkg/openparser/json
import ../src/sweetsyntax
import ../src/sweetsyntax/renderers/jsonrenderer

proc lexFilter(code: string): tuple[lexer: SweetLexer, tokens: seq[Token]] =
  let syntax = getKnownSyntax(KnownSyntax.md)
  var lx = initLexer(syntax.spec, code, enableFilters = true)
  var toks: seq[Token] = @[]
  var tok = lx.getToken()
  while tok.kind != tkEOF:
    toks.add(tok)
    tok = lx.getToken()
  (lx, toks)

proc hasAttr(toks: seq[Token], attr: string): bool =
  for t in toks:
    if attr in t.attr:
      return true
  false

suite "Markdown lexer":
  test "heading filter":
    let (_, toks) = lexFilter("# Hello\n")
    check hasAttr(toks, "markup.heading")

  test "bold, italic and strikethrough filters":
    check hasAttr(lexFilter("**bold**\n").tokens, "markup.bold")
    check hasAttr(lexFilter("__bold__\n").tokens, "markup.bold")
    check hasAttr(lexFilter("*em*\n").tokens, "markup.italic")
    check hasAttr(lexFilter("~~gone~~\n").tokens, "markup.strikethrough")

  test "inline and fenced code filters":
    check hasAttr(lexFilter("`code`\n").tokens, "markup.raw.inline")
    check hasAttr(lexFilter("```nim\necho 1\n```\n").tokens, "markup.raw.block")

  test "link and image filters":
    check hasAttr(lexFilter("[text](https://example.com)\n").tokens, "markup.link")
    check hasAttr(lexFilter("![alt](img.png)\n").tokens, "markup.image")

  test "list, quote and hr filters":
    check hasAttr(lexFilter("- item\n").tokens, "markup.list")
    check hasAttr(lexFilter("> quote\n").tokens, "markup.quote")
    check hasAttr(lexFilter("---\n").tokens, "markup.hr")

  test "html comments lex as comments":
    let syntax = getKnownSyntax(KnownSyntax.md)
    var lx = initLexer(syntax.spec, "<!-- note -->\n# H\n")
    let tok = lx.getToken()
    check tok.kind == tkComment

  test "hash heading is not a comment":
    let syntax = getKnownSyntax(KnownSyntax.md)
    var lx = initLexer(syntax.spec, "# Hello\n")
    let tok = lx.getToken()
    check tok.kind != tkComment

  test "offsets slice to token values":
    let code = "# Hello\n"
    let (lx, toks) = lexFilter(code)
    check toks.len > 0
    for t in toks:
      check t.start < t.stop
      check code[t.start ..< t.stop] == lx.getTokenValue(t)

suite "Markdown scopes":
  test "heading scope":
    let (lx, toks) = lexFilter("# Hello\n")
    var found = false
    for t in toks:
      if "markup.heading" in t.attr:
        check scopeForToken(lx, t) == "markup.heading"
        found = true
    check found

  test "NDJSON output carries markup scopes":
    let syntax = getKnownSyntax(KnownSyntax.md)
    var lx = initLexer(syntax.spec, "# H\n**b**\n", enableFilters = true)
    let lines = highlightJsonLd(lx).splitLines()
    var scopes: seq[string] = @[]
    for line in lines:
      if line.len > 0:
        scopes.add(parseJson(line)["scope"].getStr)
    check "markup.heading" in scopes
    check "markup.bold" in scopes
