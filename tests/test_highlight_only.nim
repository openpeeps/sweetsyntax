import std/[unittest, strutils, tables, sets, os, sequtils]
import pkg/openparser/json
import ../src/sweetsyntax
import ../src/sweetsyntax/renderers/[highlight, foldrenderer]

# The highlight-only contract, asserted for every language listed below:
# a YAML spec drives the lexer and the renderers with no parser, no handlers
# and no AST involved, so invalid or unfinished code still tokenizes.
#
# Each row pins the language's own comment forms, literal forms, multi-char
# operators and keyword attributes, then a shared set of invariants runs for
# every row:
#   * all three renderers produce output
#   * the token stream tiles the source exactly once, in order (no token lost,
#     none overlapping, none empty)
#   * ascii without colour reproduces the source
#   * a truncated (syntactically broken) prefix still highlights
#   * folding computes without error
#
# Add a row here when a new language is verified. `test_cpp.nim` covers the
# C++-specific lexer primitives (string prefixes, raw strings, no-heredoc).

type Case = object
  lang: KnownSyntax
  name: string
  ext: string
  code: string
    ## representative snippet exercising this language's lexical forms
  comments: seq[string]
    ## expected comment/doc-comment bodies (delimiters stripped by the lexer)
  strings: seq[string]
    ## expected single-token literals
  regexes: seq[string]
    ## expected regex literals, which need the parser-free heuristic
  puncts: seq[string]
    ## expected multi-character operators, which must not be split
  keywords: seq[string]
    ## expected keywords, which must carry their spec attribute

const cases: seq[Case] = @[
  Case(lang: KnownSyntax.c, name: "C", ext: "c",
    code: "// line\n/* block */\n/** doc */\n#define N 0xFFu\n" &
         "static const char *s = \"hi\";\n" &
         "int main(void) { int a = 1; return a == N && s != 0 || a <<= 2; }\n",
    comments: @["line", " block ", " doc "],
    strings: @["\"hi\""],
    regexes: @[],
    puncts: @["<<=", "==", "!=", "&&", "||"],
    keywords: @["int", "static", "const", "char", "return", "void"]),

  Case(lang: KnownSyntax.cpp, name: "C++", ext: "cpp",
    code: "namespace n {\n// line\ntemplate <class T>\n" &
         "constexpr auto f(T&& v, T* p) -> T { auto s = u8\"hi\"; " &
         "auto r = R\"t(x)t\"; v = v <=> v; p->*p = n::k; return s; }\n}\n",
    comments: @["line"],
    strings: @["u8\"hi\"", "R\"t(x)t\""],
    regexes: @[],
    puncts: @["->", "<=>", "->*", "&&", "::"],
    keywords: @["namespace", "template", "class", "constexpr", "auto",
                "return"]),

  Case(lang: KnownSyntax.go, name: "Go", ext: "go",
    code: "// line\n/* block */\npackage main\n\n" &
         "const raw = `a` + `b\nc`\n\n" &
         "func f(ch chan int) int {\n  x := <-ch\n  return x<<1 | 1i\n}\n",
    comments: @["line", " block "],
    strings: @["`a`", "`b\nc`"],
    regexes: @[],
    puncts: @["<-", "<<", ":=", "|"],
    keywords: @["package", "func", "return", "const", "chan"]),

  Case(lang: KnownSyntax.nim, name: "Nim", ext: "nim",
    code: "# line\n#[ block\n   comment ]#\n\n" &
         "proc f*(v: seq[int]): int =\n  ## doc\n  let s = \"hi\"\n" &
         "  var r = 0x1F'u8\n  echo v.len .. 3\n  return s.len\n",
    comments: @["line", " block\n   comment ", "# doc"],
    strings: @["\"hi\""],
    regexes: @[],
    puncts: @[".."],
    keywords: @["proc", "let", "var", "return"]),

  Case(lang: KnownSyntax.js, name: "JavaScript", ext: "js",
    code: "// line\n/* block */\nconst re = /ab+c/gi;\n" &
         "const t = `a${1}b`;\nconst q = a / b;\n" &
         "function f() { return /x/.test(s); }\n" &
         "x = a === b ?? c?.d ** 2;\n",
    comments: @["line", " block "],
    strings: @["`a${1}b`"],
    regexes: @["/ab+c/gi", "/x/"],
    puncts: @["===", "??", "**"],
    keywords: @["const", "function", "return"]),

  Case(lang: KnownSyntax.ruby, name: "Ruby", ext: "rb",
    code: "# line\n=begin\nblock comment\n=end\n\n" &
         "def f(a)\n  msg = <<~EOS\n    hello\n  EOS\n  words = %w[a b]\n" &
         "  m = a % b\n  r = /re/ =~ msg\n  n = a <=> b\n  valid?\nend\n",
    comments: @["line", "\nblock comment\n"],
    strings: @["%w[a b]", "<<~EOS\n    hello\n  EOS\n"],
    regexes: @["/re/"],
    puncts: @["=~", "%", "<=>"],
    keywords: @["def", "end"]),

  Case(lang: KnownSyntax.php, name: "PHP", ext: "php",
    code: "<?php\n// line\n# hash line\n/* block */\n$re = '/ab/i';\n" &
         "$d = $a / $b;\n$o = $a->b === $c;\n" &
         "function f($x) { return <<<EOT\nhi\nEOT;\n}\n",
    comments: @["line", "hash line", " block "],
    strings: @["'/ab/i'", "<<<EOT\nhi\nEOT"],
    regexes: @[],
    puncts: @["->", "==="],
    keywords: @["function", "return"]),
]

# One token as the renderer sees it, in stream order.
type Tok = object
  kind, scope, value: string
  start, stop: int
  attr: HashSet[string]

proc jsonTokens(lang: KnownSyntax, code: string): seq[Tok] =
  for line in highlight(lang, code, hfJson).splitLines():
    if line.len == 0:
      continue
    let node = parseJson(line)
    check node.hasKey("kind")
    check node.hasKey("scope")
    check node.hasKey("value")
    var attrs = initHashSet[string]()
    if node.hasKey("attr"):
      for a in node["attr"].getElems: attrs.incl(a.getStr)
    result.add(Tok(
      kind: node["kind"].getStr,
      scope: node["scope"].getStr,
      value: node["value"].getStr,
      start: node["start"].getInt,
      stop: node["stop"].getInt,
      attr: attrs))

proc lex(lang: KnownSyntax, code: string): seq[Tok] =
  ## Tokenize the way a lexer-only consumer does, so per-case expectations
  ## are checked against the raw stream rather than a rendered string.
  var lx = initLexer(getKnownSyntax(lang).spec, code, enableFilters = true)
  lx.inferRegex = true
  var tok = lx.getToken()
  while tok.kind != tkEOF:
    check tok != nil
    result.add(Tok(
      kind: $tok.kind,
      scope: "",
      value: lx.getTokenValue(tok),
      start: tok.start,
      stop: tok.stop,
      attr: tok.attr.toHashSet()))
    tok = lx.getToken()

proc hasKind(toks: seq[Tok], kind, value: string): bool =
  for t in toks:
    if t.kind == kind and t.value == value:
      return true
  false

proc isKeyword(toks: seq[Tok], name: string): bool =
  ## A keyword must be a single identifier token carrying its own spec
  ## attribute, so it renders with a keyword scope rather than as a variable.
  for t in toks:
    if t.kind == "ident" and t.value == name:
      return name in t.attr
  false

suite "Highlight-only: renders to every format":
  for c in cases:
    test c.name & ": ascii, html and json all produce output":
      check highlight(c.lang, c.code, hfAscii).len > 0
      check highlight(c.lang, c.code, hfHtml).len > 0
      check highlight(c.lang, c.code, hfJson).len > 0

suite "Highlight-only: the token stream is lossless":
  for c in cases:
    test c.name & ": token spans tile the source exactly, in order":
      let toks = jsonTokens(c.lang, c.code)
      check toks.len > 0
      var prevStop = 0
      var rebuilt = ""
      for t in toks:
        # positions monotonic, non-overlapping, non-empty
        check t.start >= prevStop
        check t.stop > t.start
        check t.kind.len > 0
        check t.scope.len > 0
        # the reported value really is the source text for that span
        check c.code[t.start ..< t.stop] == t.value
        if t.start > prevStop:
          rebuilt.add c.code[prevStop ..< t.start] # inter-token gap
        rebuilt.add t.value
        prevStop = t.stop
      # every token recovered; only trailing whitespace is dropped
      check rebuilt == c.code.strip(trailing = true)

    test c.name & ": ascii without colour reproduces the source":
      check highlight(c.lang, c.code, hfAscii, useColor = false) ==
        c.code.strip(trailing = true)

    test c.name & ": a truncated, broken prefix still highlights":
      # No parser runs, so a half-written file must tokenize, not throw.
      let broken = c.code[0 ..< min(c.code.len, 60)]
      check highlight(c.lang, broken, hfAscii).len > 0
      check highlight(c.lang, broken, hfHtml).len > 0
      check highlight(c.lang, broken, hfJson).len > 0

    test c.name & ": folding computes without error":
      var lx = initLexer(getKnownSyntax(c.lang).spec, c.code)
      discard computeFolds(lx)

suite "Highlight-only: language lexical forms":
  for c in cases:
    test c.name & ": comments, literals, operators and keywords":
      let toks = lex(c.lang, c.code)
      for want in c.comments:
        check hasKind(toks, "comment", want) or
              hasKind(toks, "doc_comment", want)
      for want in c.strings:
        check hasKind(toks, "string", want)
      for want in c.regexes:
        check hasKind(toks, "regex", want)
      for want in c.puncts:
        check hasKind(toks, "punct", want)
      for want in c.keywords:
        check isKeyword(toks, want)

suite "Highlight-only: regex literals need no parser":
  # The lexer only treats `/` as a regex when the parser supplies the hint.
  # `highlight` has no parser, so it infers the same verdict from each spec's
  # `expect_regex_after` list.
  test "JavaScript: regex and division are told apart":
    let toks = lex(KnownSyntax.js,
      "const a = /re/gi;\nconst b = x / y;\nconst c = 10 / 2;\n")
    check hasKind(toks, "regex", "/re/gi")
    check hasKind(toks, "punct", "/")
    check not toks.anyIt(it.kind == "regex" and it.value.len > 1 and
                          it.value.startsWith("/ "))

  test "a regex may follow return, an assignment or an open paren":
    check hasKind(lex(KnownSyntax.js, "function f() { return /x/; }"),
      "regex", "/x/")
    check hasKind(lex(KnownSyntax.js, "const r = /x/;"), "regex", "/x/")
    check hasKind(lex(KnownSyntax.js, "f(/x/);"), "regex", "/x/")
    check hasKind(lex(KnownSyntax.js, "x ? /a/ : /b/"), "regex", "/a/")
    check hasKind(lex(KnownSyntax.js, "x ? /a/ : /b/"), "regex", "/b/")

  test "a regex does not follow a value":
    check not hasKind(lex(KnownSyntax.js, "const d = a / b;"), "regex", "/ b")
    check not hasKind(lex(KnownSyntax.js, "f(a) / 2;"), "regex", "/ 2")

  test "a regex at the very start of a file is a regex":
    check hasKind(lex(KnownSyntax.js, "/re/.test(x)"), "regex", "/re/")

  test "Ruby and PHP get regex literals too":
    check hasKind(lex(KnownSyntax.ruby, "a = /re/\n"), "regex", "/re/")
    check hasKind(lex(KnownSyntax.php, "<?php $r = /ab/i;\n"),
      "regex", "/ab/i")

  test "Ruby division is never mistaken for a percent or a regex":
    let toks = lex(KnownSyntax.ruby, "b = x % y\nc = 10 % 3\nd = a / b\n")
    check hasKind(toks, "punct", "%")
    check not toks.anyIt(it.kind == "string")
    check not toks.anyIt(it.kind == "regex")

  test "a language with no expect_regex_after never sees a regex":
    let toks = lex(KnownSyntax.c, "int x = a / b;\n")
    check hasKind(toks, "punct", "/")
    check not toks.anyIt(it.kind == "regex")

suite "Highlight-only: Ruby percent literals":
  test "each percent form is a single string token":
    let toks = lex(KnownSyntax.ruby,
      "a = %w[x y]\nb = %i(x)\nc = %q{it's}\nd = %Q<hi>\ne = %W{a}\n")
    for want in ["%w[x y]", "%i(x)", "%q{it's}", "%Q<hi>", "%W{a}"]:
      check hasKind(toks, "string", want)

  test "a bare %[...] needs no kind letter only when it is unambiguous":
    # Ruby allows `%(...)` and `%[...]`, but `a % (b)` is modulo by a
    # parenthesised value. Requiring the kind letter keeps `%` correct in the
    # common case, so `%[...]` deliberately stays an operator here.
    let toks = lex(KnownSyntax.ruby, "e = %[br]\n")
    check not hasKind(toks, "string", "%[br]")
    check hasKind(toks, "punct", "%")

  test "a percent literal does not swallow the rest of the file":
    let toks = lex(KnownSyntax.ruby, "a = %w[x y]\nputs a\n")
    check hasKind(toks, "string", "%w[x y]")
    check hasKind(toks, "ident", "puts")

  test "nested paired delimiters are balanced":
    check hasKind(lex(KnownSyntax.ruby, "a = %w[x [y] z]\n"),
      "string", "%w[x [y] z]")

  test "an apostrophe inside a percent literal is literal":
    check hasKind(lex(KnownSyntax.ruby, "a = %q{it's}\nb = 1\n"),
      "string", "%q{it's}")
    check hasKind(lex(KnownSyntax.ruby, "a = %q{it's}\nb = 1\n"),
      "ident", "b")

  test "the `%` operator still works when no percent form matches":
    let toks = lex(KnownSyntax.ruby, "def f(a)\n  a % b\nend\n")
    check hasKind(toks, "punct", "%")
    check not toks.anyIt(it.kind == "string")
    check hasKind(toks, "ident", "end")

suite "Highlight-only: Ruby =begin/=end block comments":
  test "the block comment is one token and the code after it survives":
    let toks = lex(KnownSyntax.ruby, "=begin\nblock comment\n=end\nputs 1\n")
    check hasKind(toks, "comment", "\nblock comment\n")
    check hasKind(toks, "ident", "puts")
    check hasKind(toks, "int", "1")

suite "Highlight-only: every row is reachable by extension":
  test "each language resolves from its own extension":
    for c in cases:
      check syntaxForExt(c.ext) == c.lang
      check syntaxForExt("." & c.ext.toUpperAscii) == c.lang

  test "highlightFile highlights a file on disk for each row":
    let dir = getTempDir() / "sweetsyntax_highlight_only_test"
    createDir(dir)
    for c in cases:
      let path = dir / ("sample." & c.ext)
      writeFile(path, c.code)
      check highlightFile(path, hfJson).len > 0
      check highlightFile(path, hfHtml).len > 0
      check highlightFile(path, hfAscii).len > 0
