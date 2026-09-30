import std/[unittest, strutils, os, tables]
import ../src/sweetsyntax
import ../src/sweetsyntax/renderers/[highlight, foldrenderer]

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

proc scopes(lang: KnownSyntax, code: string): string =
  highlight(lang, code, hfJson)

suite "Tier 0: wired TypeScript and Crystal":
  test "TypeScript spec loads and highlights types":
    let toks = tokens(KnownSyntax.ts, "const x: number = 42;\n")
    check hasKind(toks, "const", "ident")
    check hasAttr(toks, "number", "number")
    check hasKind(toks, "42", "int")

  test "TypeScript routes its own extensions, not JavaScript":
    for ext in ["ts", "tsx", "mts", "cts", "dts"]:
      check syntaxForExt(ext) == KnownSyntax.ts
    check syntaxForExt("jsx") == KnownSyntax.js
    check syntaxForExt("mjs") == KnownSyntax.js

  test "Crystal spec loads and highlights":
    let toks = tokens(KnownSyntax.crystal, "# c\nx = 1\nputs x\n")
    check hasKind(toks, "c", "comment")
    check hasKind(toks, "1", "int")
    check syntaxForExt("cr") == KnownSyntax.crystal

  test "hash comment syntax still works for Crystal":
    let toks = tokens(KnownSyntax.crystal, "x = 1 # note\n")
    check hasKind(toks, "note", "comment")

suite "New syntaxes load and render":
  test "every new syntax highlights to all formats":
    let samples = {
      KnownSyntax.html: "<p class=\"a\">hi</p>",
      KnownSyntax.xml: "<root a=\"1\"><b/></root>",
      KnownSyntax.shell: "echo hi",
      KnownSyntax.docker: "FROM alpine",
      KnownSyntax.ini: "k = v",
      KnownSyntax.make: "all:\n\techo hi",
      KnownSyntax.cmake: "project(x)",
      KnownSyntax.nginx: "server { listen 80; }",
      KnownSyntax.systemd: "[Unit]\nDescription=x",
      KnownSyntax.jinja2: "{{ a }}",
      KnownSyntax.handlebars: "{{#each a}}{{b}}{{/each}}",
      KnownSyntax.liquid: "{% if a %}{{ b }}{% endif %}",
      KnownSyntax.ejs: "<% x %>",
      KnownSyntax.ts: "const x = 1;",
      KnownSyntax.crystal: "x = 1",
    }.toTable
    for lang, code in samples.pairs:
      check highlight(lang, code, hfHtml).len > 0
      check highlight(lang, code, hfAscii).len > 0
      check highlight(lang, code, hfJson).len > 0

suite "HTML and XML":
  test "tags, attributes, entities and comments":
    let toks = tokens(KnownSyntax.html,
      "<!DOCTYPE html>\n<a href=\"x\" id='y'>&amp;<!-- c --></a>\n")
    check hasAttr(toks, "DOCTYPE", "markup.tag")
    check hasAttr(toks, "a", "markup.tag")
    check hasAttr(toks, "href", "entity.other.attribute-name")
    check hasAttr(toks, "amp", "constant.character.escape")
    # block comment markers are stripped, leaving the inner text
    check hasKind(toks, " c ", "comment")

  test "html comment scope is a comment block":
    check "comment" in scopes(KnownSyntax.html, "<!-- c -->\n")

  test "XML processing instruction and namespaced tags":
    let toks = tokens(KnownSyntax.xml,
      "<?xml version=\"1.0\"?>\n<ns:tag ns:a=\"1\"/>\n")
    check hasAttr(toks, "?", "markup.tag")
    # `ns:tag` lexes as three tokens; the filter covers the whole name
    check hasAttr(toks, "ns", "markup.tag")
    check hasAttr(toks, "tag", "markup.tag")
    check hasAttr(toks, "a", "entity.other.attribute-name")

  test "tag scope reaches the JSON renderer":
    check "markup.tag" in scopes(KnownSyntax.html, "<div>x</div>")
    check "entity.other.attribute-name" in scopes(KnownSyntax.html, "<a href=\"x\">")

suite "Shell, Dockerfile, Make, CMake":
  test "shell comments, keywords and heredocs":
    let toks = tokens(KnownSyntax.shell,
      "# note\nfor f in a; do\n  echo \"$f\"\ndone\ncat <<EOF\nbody\nEOF\n")
    check hasKind(toks, "note", "comment")
    check hasAttr(toks, "for", "for")
    check hasAttr(toks, "done", "done")
    var heredoc = false
    for t in toks:
      if t.kind == "string" and t.value.startsWith("<<EOF"):
        check "heredoc" in t.attrs
        heredoc = true
    check heredoc

  test "dockerfile instructions and comments":
    let toks = tokens(KnownSyntax.docker, "# c\nFROM alpine AS b\nRUN echo hi\n")
    check hasKind(toks, "c", "comment")
    check hasAttr(toks, "FROM", "FROM")
    check hasAttr(toks, "RUN", "RUN")
    check hasAttr(toks, "AS", "AS")

  test "ini supports both semicolon and hash comments":
    let toks = tokens(KnownSyntax.ini, "; one\n# two\n[s]\nk = v\n")
    check hasKind(toks, "one", "comment")
    check hasKind(toks, "two", "comment")

  test "makefile targets and variables get property.name":
    let toks = tokens(KnownSyntax.make, "CC := gcc\nall: main.o\n# c\n")
    check hasAttr(toks, "CC", "property.name")
    check hasAttr(toks, "all", "property.name")
    check hasKind(toks, "c", "comment")

  test "cmake commands and comments":
    let toks = tokens(KnownSyntax.cmake, "# c\nproject(x)\nif(A)\nendif()\n")
    check hasKind(toks, "c", "comment")
    check hasAttr(toks, "project", "project")
    check hasAttr(toks, "endif", "endif")

suite "Nginx and systemd":
  test "nginx directives and brace folding":
    let toks = tokens(KnownSyntax.nginx, "# c\nserver {\n  listen 80;\n}\n")
    check hasKind(toks, "c", "comment")
    check hasAttr(toks, "server", "server")
    check hasAttr(toks, "listen", "listen")
    var lx = initLexer(getKnownSyntax(KnownSyntax.nginx).spec,
      "server {\n  listen 80;\n}\n")
    let regions = computeFolds(lx)
    check regions.len == 1
    check regions[0].kind == fkBlock
    check regions[0].endLine == 3

  test "systemd sections and keys":
    let toks = tokens(KnownSyntax.systemd,
      "# c\n[Unit]\nDescription=x\nAfter=network.target\n")
    check hasKind(toks, "c", "comment")
    check hasAttr(toks, "Unit", "entity.name.tag")
    check hasAttr(toks, "Description", "property.name")
    check hasAttr(toks, "After", "property.name")

suite "Template engines":
  test "jinja2 delimiters and comments":
    let toks = tokens(KnownSyntax.jinja2,
      "{% for i in x %}<li>{{ i }}</li>{% endfor %}\n{# note #}\n")
    check hasAttr(toks, "%", "markup.tag")
    # `{# ... #}` markers are stripped, leaving the inner text
    check hasKind(toks, " note ", "comment")
    check hasAttr(toks, "for", "for")
    check hasAttr(toks, "endfor", "endfor")

  test "handlebars block and expression delimiters":
    let toks = tokens(KnownSyntax.handlebars, "{{#each items}}{{name}}{{/each}}\n")
    check hasAttr(toks, "#", "markup.tag")
    check hasKind(toks, "name", "ident")
    check hasAttr(toks, "each", "each")

  test "liquid output and statement delimiters":
    let toks = tokens(KnownSyntax.liquid, "{% if a %}{{ b }}{% endif %}\n")
    check hasAttr(toks, "%", "markup.tag")
    check hasAttr(toks, "if", "if")

  test "ejs scriptlet delimiters":
    let toks = tokens(KnownSyntax.ejs, "<ul><% for (const i of x) { %><%= i %><% } %></ul>\n")
    check hasAttr(toks, "%", "markup.tag")
    check hasAttr(toks, "for", "for")

  test "html tags still win inside templates":
    for lang in [KnownSyntax.jinja2, KnownSyntax.handlebars,
                 KnownSyntax.liquid, KnownSyntax.ejs]:
      check "markup.tag" in scopes(lang, "<div class=\"a\">{{ x }}</div>")

suite "Highlight-only languages lex multi-character operators":
  # `allOps` is seeded from the spec's `symbols` table, so a spec with no
  # `operators:` section (every highlight-only language) still lexes `==`,
  # `->`, `:=` and friends as single tokens instead of splitting them.
  test "python operators stay whole":
    let toks = tokens(KnownSyntax.py, "a += 1\nb = a ** c // d\n")
    for op in ["+=", "**", "//"]:
      check hasKind(toks, op, "punct")

  test "d operators stay whole":
    let toks = tokens(KnownSyntax.d, "x = a >>> b >>>= c;\n")
    check hasKind(toks, ">>>", "punct")
    check hasKind(toks, ">>>=", "punct")

  test "rust operators stay whole":
    let toks = tokens(KnownSyntax.rust, "fn f() -> bool { a >= b }\n")
    check hasKind(toks, "->", "punct")
    check hasKind(toks, ">=", "punct")

  test "markup and config operators stay whole":
    let toks = tokens(KnownSyntax.make, "CC := gcc\n")
    check hasKind(toks, ":=", "punct")
    let sh = tokens(KnownSyntax.shell, "a; case x in y) ;; esac\n")
    check hasKind(sh, ";;", "punct")
    let yml = tokens(KnownSyntax.yaml, "a: 1\n<<: *base\n")
    check hasKind(yml, "<<", "punct")

suite "Lexer flags from the spec":
  test "heredocs are opt-in":
    # Only specs that declare here-documents scan for a terminator line, so
    # `<<` stays a plain shift everywhere else.
    for lang in [KnownSyntax.ruby, KnownSyntax.php, KnownSyntax.shell]:
      check getKnownSyntax(lang).spec.heredocs
    for lang in [KnownSyntax.cpp, KnownSyntax.c, KnownSyntax.js,
                 KnownSyntax.nim, KnownSyntax.py]:
      check not getKnownSyntax(lang).spec.heredocs

  test "a shift is never a heredoc without the flag":
    let cpp = tokens(KnownSyntax.cpp, "cout << \"x\";\nhi\n")
    check hasKind(cpp, "<<", "punct")
    check hasAttr(cpp, "<<", "shiftLeft")
    check hasKind(cpp, "hi", "ident")

  test "specs with heredocs still lex theirs":
    let toks = tokens(KnownSyntax.ruby, "msg = <<EOS\nhello\nEOS\n")
    var found = false
    for t in toks:
      if t.kind == "string" and t.value.startsWith("<<EOS"):
        check "heredoc" in t.attrs
        found = true
    check found

  test "string prefixes are opt-in":
    check getKnownSyntax(KnownSyntax.cpp).spec.string_prefixes.len > 0
    check getKnownSyntax(KnownSyntax.cpp).spec.raw_string_delims
    check getKnownSyntax(KnownSyntax.c).spec.string_prefixes.len == 0
    check not getKnownSyntax(KnownSyntax.c).spec.raw_string_delims

  test "an unprefixed quote still starts a string without the flag":
    let toks = tokens(KnownSyntax.c, "char *s = \"hi\"; char c = 'a';\n")
    check hasKind(toks, "\"hi\"", "string")
    check hasKind(toks, "'a'", "string")

suite "Filename resolution":
  test "well-known bare filenames resolve":
    let dir = getTempDir() / "sweetsyntax_expansion_test"
    createDir(dir)
    let cases = {
      "Dockerfile": KnownSyntax.docker,
      "dockerfile": KnownSyntax.docker,
      "Makefile": KnownSyntax.make,
      "GNUmakefile": KnownSyntax.make,
      "CMakeLists.txt": KnownSyntax.cmake,
      ".env": KnownSyntax.ini,
    }.toTable
    for (name, expected) in cases.pairs:
      let path = dir / name
      writeFile(path, "x\n")
      check highlightFile(path, hfJson).len > 0
      discard syntaxForFilename(name) == expected

  test "unknown bare filename raises":
    expect SweetHighlightError:
      discard syntaxForFilename("noext")

  test "extension still wins over filename":
    check syntaxForExt("html") == KnownSyntax.html
    check syntaxForExt("sh") == KnownSyntax.shell
    check syntaxForExt("j2") == KnownSyntax.jinja2
    check syntaxForExt("hbs") == KnownSyntax.handlebars
    check syntaxForExt("service") == KnownSyntax.systemd
    check syntaxForExt("cmake") == KnownSyntax.cmake
    check syntaxForExt("conf") == KnownSyntax.ini
    check syntaxForExt("svg") == KnownSyntax.xml
