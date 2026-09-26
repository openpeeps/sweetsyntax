import std/[unittest, strutils]
import pkg/openparser/json
import ../src/sweetsyntax
import ../src/sweetsyntax/renderers/[jsonrenderer, foldrenderer]

proc lexNoFilter(code: string): seq[Token] =
  let syntax = getKnownSyntax(KnownSyntax.css)
  var lx = initLexer(syntax.spec, code)
  var tok = lx.getToken()
  while tok.kind != tkEOF:
    result.add(tok)
    tok = lx.getToken()

proc lexFilter(code: string): tuple[lexer: SweetLexer, tokens: seq[Token]] =
  let syntax = getKnownSyntax(KnownSyntax.css)
  var lx = initLexer(syntax.spec, code, enableFilters = true)
  var toks: seq[Token] = @[]
  var tok = lx.getToken()
  while tok.kind != tkEOF:
    toks.add(tok)
    tok = lx.getToken()
  (lx, toks)

proc values(lexer: SweetLexer, toks: seq[Token]): seq[string] =
  for t in toks:
    result.add(lexer.getTokenValue(t))

suite "CSS lexer":
  test "block comments lex as comments":
    let toks = lexNoFilter("/* hello */\n.foo { color: red; }")
    check toks[0].kind == tkComment

  test "hash id selector is not a comment":
    let toks = lexNoFilter("#main { color: red; }")
    check toks[0].kind == tkPunct
    check toks.len > 1
    check toks[1].kind == tkIdentifier

  test "braces, colon and semicolon tokenize":
    let (lx, toks) = lexFilter(".foo { color: red; }")
    let vals = values(lx, toks)
    check "{" in vals
    check "}" in vals
    check ":" in vals
    check ";" in vals

  test "dimensions split into number and unit":
    let (lx, toks) = lexFilter("p { margin: 12px; width: 100%; }")
    let vals = values(lx, toks)
    check "12" in vals
    check "px" in vals
    check "100" in vals
    check "%" in vals

  test "hex colors split into hash and ident":
    let toks = lexNoFilter("p { color: #fff; }")
    var kinds: seq[string] = @[]
    for t in toks:
      kinds.add($t.kind)
    check $tkPunct in kinds
    check $tkIdentifier in kinds

  test "offsets slice to token values":
    let code = ".foo { color: red; }"
    let (lx, toks) = lexFilter(code)
    for t in toks:
      check t.start < t.stop
      check code[t.start ..< t.stop] == lx.getTokenValue(t)

suite "CSS filters and scopes":
  test "class selector gets selector.class scope":
    let (lx, toks) = lexFilter(".foo { color: red; }")
    var found = false
    for t in toks:
      if lx.getTokenValue(t) == ".foo" or
         (t.kind == tkPunct and lx.getTokenValue(t) == "."):
        check "selector.class" in t.attr
        check scopeForToken(lx, t) == "selector.class"
        found = true
    check found

  test "id selector gets selector.id scope":
    let (lx, toks) = lexFilter("#main { color: red; }")
    var found = false
    for t in toks:
      if "selector.id" in t.attr:
        check scopeForToken(lx, t) == "selector.id"
        found = true
    check found

  test "at-rule gets at.rule scope":
    let (lx, toks) = lexFilter("@media screen { p { color: red; } }")
    var found = false
    for t in toks:
      if "at.rule" in t.attr:
        check scopeForToken(lx, t) == "at.rule"
        found = true
    check found

  test "property name maps to variable.other.property":
    let (lx, toks) = lexFilter("p { color: red; }")
    var found = false
    for t in toks:
      if "property.name" in t.attr:
        check scopeForToken(lx, t) == "variable.other.property"
        found = true
    check found

  test "NDJSON output carries scopes":
    let syntax = getKnownSyntax(KnownSyntax.css)
    var lx = initLexer(syntax.spec, ".foo { color: red; }", enableFilters = true)
    let lines = highlightJsonLd(lx).splitLines()
    var scopes: seq[string] = @[]
    for line in lines:
      if line.len > 0:
        scopes.add(parseJson(line)["scope"].getStr)
    check "selector.class" in scopes
    check "variable.other.property" in scopes

suite "CSS folds":
  test "brace folding of a rule":
    let syntax = getKnownSyntax(KnownSyntax.css)
    var lx = initLexer(syntax.spec, ".foo {\n  color: red;\n}")
    let regions = computeFolds(lx)
    check regions.len == 1
    check regions[0].kind == fkBlock
    check regions[0].startLine == 1
    check regions[0].endLine == 3
