import std/[unittest, strutils, os]
import ../src/sweetsyntax
import ../src/sweetsyntax/renderers/[highlight, foldrenderer]

# C++ is a highlight-only syntax: the lexer plus the renderers, with no
# parser, no handlers and therefore no AST. These tests cover tokenization and
# rendering only; `parseScript` has no C++ handlers by design.

type Tok = tuple[kind: string, value: string, attrs: seq[string]]

proc tokens(lang: KnownSyntax, code: string): seq[Tok] =
  let syntax = getKnownSyntax(lang)
  var lx = initLexer(syntax.spec, code, enableFilters = true)
  var tok = lx.getToken()
  while tok.kind != tkEOF:
    result.add(($tok.kind, lx.getTokenValue(tok), tok.attr))
    tok = lx.getToken()

proc hasAttr(toks: seq[Tok], value, attr: string): bool =
  for t in toks:
    if t.value == value and attr in t.attrs:
      return true
  false

proc hasKind(toks: seq[Tok], value, kind: string): bool =
  for t in toks:
    if t.value == value and t.kind == kind:
      return true
  false

proc puncts(toks: seq[Tok]): seq[string] =
  for t in toks:
    if t.kind == "punct": result.add(t.value)

proc scopes(code: string): string =
  highlight(KnownSyntax.cpp, code, hfJson)

suite "C++ spec loads":
  test "name, extensions and flags":
    let spec = getKnownSyntax(KnownSyntax.cpp).spec
    check spec.name == "C++"
    for ext in ["cpp", "cc", "cxx", "c++", "hpp", "hh", "hxx", "h++", "inl",
                "ipp", "tcc"]:
      check ext in spec.extension
    check spec.inline_comment == some("//")
    check spec.block_comment == ["/*", "*/"]
    check spec.int_suffixes
    # Highlight-only: no parser tables at all.
    check spec.operators.isNil
    check spec.statements.len == 0
    check spec.heredocs == false

  test "symbol table covers C++ multi-character operators":
    let toks = tokens(KnownSyntax.cpp,
      "a::b; a->b; a.*b; a->*b; x <=> y; m ## n; ++i; --j;")
    for op in ["::", "->", ".*", "->*", "<=>", "##", "++", "--"]:
      check op in puncts(toks)
    check hasAttr(toks, "::", "scope")
    check hasAttr(toks, "<=>", "spaceship")

  test "C++ keywords carry their spec attributes":
    let toks = tokens(KnownSyntax.cpp,
      "namespace n { template<class T> constexpr auto f() -> T; }")
    check hasAttr(toks, "namespace", "namespace")
    check hasAttr(toks, "template", "template")
    check hasAttr(toks, "constexpr", "constexpr")
    check hasAttr(toks, "class", "class")
    check hasAttr(toks, "auto", "auto")

suite "C++ comments and preprocessor":
  test "line, block and doc comments":
    let toks = tokens(KnownSyntax.cpp,
      "// line\n/* block */\n/** doc */\nint x;\n")
    # `//` and the whitespace after it are stripped from the token
    check hasKind(toks, "line", "comment")
    check hasKind(toks, " block ", "comment")
    check hasKind(toks, " doc ", "doc_comment")

  test "preprocessor directives keep their hash punctuation":
    let toks = tokens(KnownSyntax.cpp, "#include <vector>\n#define N 1\n")
    check hasAttr(toks, "#", "hash")
    check hasKind(toks, "include", "ident")
    check hasKind(toks, "define", "ident")

suite "C++ string literals":
  test "encoding prefixes form a single string token":
    let toks = tokens(KnownSyntax.cpp, "u8\"hi\" L'a' u\"q\" U\"r\" L\"s\"")
    for lit in ["u8\"hi\"", "L'a'", "u\"q\"", "U\"r\"", "L\"s\""]:
      check hasKind(toks, lit, "string")

  test "a prefix only counts when glued to the quote":
    # `u` and `R` are ordinary identifiers unless a quote follows directly.
    let toks = tokens(KnownSyntax.cpp, "int u = 1; int R = 2; u8x v;")
    check hasKind(toks, "u", "ident")
    check hasKind(toks, "R", "ident")
    check hasKind(toks, "u8x", "ident")

  test "C++17 delimited raw strings keep embedded quotes":
    # The body runs to `)"`, so the embedded quote does not close it early.
    let toks = tokens(KnownSyntax.cpp, "auto s = R\"(a \" b)\";")
    check hasKind(toks, "R\"(a \" b)\"", "string")

  test "delimited raw strings honour their tag":
    # Only `)tag"` ends it; the earlier `)` is ordinary body text.
    let toks = tokens(KnownSyntax.cpp, "auto s = R\"tag(a )body )tag\";")
    check hasKind(toks, "R\"tag(a )body )tag\"", "string")

  test "wide raw string prefixes are supported":
    let toks = tokens(KnownSyntax.cpp, "auto s = u8R\"t(x)t\"; auto v = LR\"y\";")
    check hasKind(toks, "u8R\"t(x)t\"", "string")
    check hasKind(toks, "LR\"y\"", "string")

suite "C++ number literals":
  test "C integer and float suffixes fold into the number":
    let toks = tokens(KnownSyntax.cpp, "auto v = 1ULL + 0xFFu + 1.5f + 42;")
    check hasKind(toks, "1ULL", "int")
    check hasKind(toks, "0xFFu", "tkHex")
    check hasKind(toks, "1.5f", "float")
    check hasKind(toks, "42", "int")

suite "C++ highlights without parsing":
  test "shift is not mistaken for a heredoc":
    # A `<<` whose operand happens to be a bare line must not open a
    # here-document: only specs with `heredocs: true` scan for one.
    let toks = tokens(KnownSyntax.cpp, "cout << \"x\";\nhi\n")
    check hasAttr(toks, "<<", "shiftLeft")
    check hasKind(toks, "hi", "ident")

  test "renders to every format":
    let code = "namespace n { auto f() -> int { return 0; } }\n"
    check highlight(KnownSyntax.cpp, code, hfAscii).len > 0
    check highlight(KnownSyntax.cpp, code, hfHtml).len > 0
    check highlight(KnownSyntax.cpp, code, hfJson).len > 0

  test "ascii without color reproduces the source":
    let code = "int x = 42; // note"
    check highlight(KnownSyntax.cpp, code, hfAscii, useColor = false) == code

  test "html spans carry the token kind and keyword attributes":
    let html = highlight(KnownSyntax.cpp, "namespace n {}", hfHtml)
    check "<span class=\"ident namespace\">namespace</span>" in html
    check "<span class=\"punct curl\">{</span>" in html
    # `<` and `>` from a template are escaped inside their spans.
    check "<span class=\"punct lt\">&lt;</span>" in
      highlight(KnownSyntax.cpp, "template<class T> f();", hfHtml)

  test "keyword scopes reach the JSON renderer":
    check "keyword.control" in scopes("namespace n { return 0; }")
    check "storage.type" in scopes("wchar_t *x = 0;")
    # `constexpr`/`auto` declare a binding, they are not types
    check "storage.modifier" in scopes("constexpr auto x = 0;")
    check "constant.language.null" in scopes("auto p = nullptr;")
    check "variable.language" in scopes("this->f();")
    check "string.quoted.double" in scopes("auto s = u8\"x\";")

  test "broken code still highlights":
    # No parser runs, so unbalanced input tokenizes instead of erroring.
    check highlight(KnownSyntax.cpp, "template<", hfHtml).len > 0
    check highlight(KnownSyntax.cpp, "void f(", hfAscii).len > 0

  test "brace blocks fold like any other brace language":
    let code = "namespace n {\n  int x;\n}\n"
    var lx = initLexer(getKnownSyntax(KnownSyntax.cpp).spec, code)
    let regions = computeFolds(lx)
    check regions.len == 1
    check regions[0].kind == fkBlock
    check regions[0].endLine == 3

suite "C++ extension routing":
  test "every C++ extension resolves to the C++ spec":
    for ext in ["cpp", "cc", "cxx", "c++", "hpp", "hh", "hxx", "h++", "inl",
                "ipp", "tcc"]:
      check syntaxForExt(ext) == KnownSyntax.cpp

  test "C extensions still resolve to C":
    for ext in ["c", "h", "c99", "c11", "c17", "c23"]:
      check syntaxForExt(ext) == KnownSyntax.c

  test "extension matching is case-insensitive":
    check syntaxForExt("CPP") == KnownSyntax.cpp
    check syntaxForExt(".Hpp") == KnownSyntax.cpp

  test "highlightFile resolves a C++ file by extension":
    let dir = getTempDir() / "sweetsyntax_cpp_test"
    createDir(dir)
    let path = dir / "main.cpp"
    writeFile(path, "int main() { return 0; }\n")
    check "storage.type" in highlightFile(path, hfJson)
