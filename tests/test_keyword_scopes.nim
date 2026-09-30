import std/[unittest, strutils, tables]
import ../src/sweetsyntax
import ../src/sweetsyntax/renderers/jsonrenderer
import ../src/sweetsyntax/languages/prepared/js

proc scopesForSpec(spec: SweetSpec, code: string): Table[string, string] =
  ## lexeme -> TextMate scope for every token in `code`
  var lx = initLexer(spec, code)
  var tok = lx.getToken()
  while tok.kind != tkEOF:
    result[lx.getTokenValue(tok)] = scopeForToken(lx, tok)
    tok = lx.getToken()

proc scopesFor(lang: KnownSyntax, code: string): Table[string, string] =
  scopesForSpec(getKnownSyntax(lang).spec, code)

proc scopeOf(lang: KnownSyntax, word: string): string =
  scopesFor(lang, word)[word]

proc scopes(pairs: openArray[(string, seq[string])]): KeywordScopes =
  ## `@[...]` literals infer as arrays, so spell the seq type out once here.
  for pair in pairs:
    result[pair[0]] = pair[1]

proc inventedSpec(keywords: openArray[string], scopes: KeywordScopes): SweetSpec =
  ## A spec for a language no renderer has ever heard of. Its whole point is
  ## that the classification comes from `scopes` and nothing else.
  result = SweetSpec(
    name: "Zork",
    extension: @[".zrk"],
    block_comment: ["", ""],
    symbols: {"comma": ",", "scolon": ";", "assign": "=", "curr": "{", "curl": "}"}.toTable,
    identifiers: (block:
      var t = initTable[string, string]()
      for kw in keywords: t[kw] = kw
      t),
    keyword_scopes: scopes)

suite "keyword scopes":
  test "a spec classifies its own keywords":
    let s = scopesFor(KnownSyntax.c, "char *p; const int n = 1; if (n) return NULL;")
    check s["char"] == "storage.type"
    check s["const"] == "storage.modifier"
    check s["int"] == "storage.type"
    check s["if"] == "keyword.control"
    check s["return"] == "keyword.control"
    check s["NULL"] == "constant.language.null"
    check s["n"] == "variable"
    check s["p"] == "variable"

  test "a declared keyword with no scope is a plain keyword":
    # `sizeof` is a keyword in C but not a type, a modifier or control flow
    check scopeOf(KnownSyntax.c, "sizeof") == "keyword"
    check scopeOf(KnownSyntax.c, "struct") == "keyword"

  test "a word the renderer has never heard of is scoped from the spec":
    # Nothing anywhere knows these lexemes; the scope must come from the spec.
    let spec = inventedSpec(["zork", "blarg", "quux"],
      scopes({"storage.type": @["zork"], "keyword.control": @["blarg"]}))
    let s = scopesForSpec(spec, "zork blarg quux x;")
    check s["zork"] == "storage.type"
    check s["blarg"] == "keyword.control"
    check s["quux"] == "keyword"
    check s["x"] == "variable"

  test "a spec without keyword_scopes falls back to a plain keyword":
    let spec = inventedSpec(["zork", "blarg"], KeywordScopes())
    let s = scopesForSpec(spec, "zork blarg;")
    check s["zork"] == "keyword"
    check s["blarg"] == "keyword"

  test "keyword_scopes cannot promote a word that is not an identifier":
    # Guards the ordering: `identifiers` decides what counts as a keyword, so a
    # stale or misspelled entry cannot turn a variable into a type.
    let spec = inventedSpec(["zork"],
      scopes({"storage.type": @["zork", "notakeyword"]}))
    let s = scopesForSpec(spec, "zork notakeyword;")
    check s["zork"] == "storage.type"
    check s["notakeyword"] == "variable"

  test "CSS at-rules are not control flow":
    # These words used to sit in the renderer's `controlKeywords` list, copied
    # straight out of css.yaml, so `@media` reported `keyword.control`.
    # `font-face` is omitted: css.yaml declares it, but `-` ends an identifier
    # so the word can never be lexed whole and the entry is unreachable.
    for word in ["media", "keyframes", "supports", "page", "namespace", "charset"]:
      check scopeOf(KnownSyntax.css, word) == "keyword"
    check "@media".len > 0

  test "declaration keywords are not storage types in every language":
    # `def` used to be a `storageTypeKeywords` entry, so it reported
    # `storage.type` in whatever spec mentioned it.
    check scopeOf(KnownSyntax.py, "def") == "keyword"
    check scopeOf(KnownSyntax.py, "lambda") == "keyword"
    check scopeOf(KnownSyntax.js, "function") == "keyword"

  test "null and boolean words are per-spec":
    check scopeOf(KnownSyntax.c, "NULL") == "constant.language.null"
    check scopeOf(KnownSyntax.cpp, "nullptr") == "constant.language.null"
    check scopeOf(KnownSyntax.go, "nil") == "constant.language.null"
    check scopeOf(KnownSyntax.ruby, "nil") == "constant.language.null"
    check scopeOf(KnownSyntax.nim, "nil") == "constant.language.null"
    check scopeOf(KnownSyntax.php, "null") == "constant.language.null"
    check scopeOf(KnownSyntax.ts, "undefined") == "constant.language.null"
    for lang in [KnownSyntax.c, KnownSyntax.cpp, KnownSyntax.js,
                 KnownSyntax.nim, KnownSyntax.go, KnownSyntax.ruby,
                 KnownSyntax.php]:
      check scopeOf(lang, "true") == "constant.language.boolean"
      check scopeOf(lang, "false") == "constant.language.boolean"

  test "language-specific vocabulary keeps its own scope":
    check scopeOf(KnownSyntax.ruby, "self") == "variable.language"
    check scopeOf(KnownSyntax.php, "self") == "variable.language"
    check scopeOf(KnownSyntax.php, "parent") == "variable.language"
    check scopeOf(KnownSyntax.cpp, "this") == "variable.language"
    check scopeOf(KnownSyntax.ruby, "__FILE__") == "constant.language"
    check scopeOf(KnownSyntax.c, "__func__") == "constant.language"

  test "operators and punctuation are unaffected":
    let s = scopesFor(KnownSyntax.c, "a += b; (c);")
    check s["+="] == "keyword.operator"
    check s[";"] == "punctuation"
    check s["("] == "punctuation"
    check s[")"] == "punctuation"

  test "the prebuilt lexer init agrees with the spec":
    # `buildPrepared` emits the table at compile time, so a mistake there would
    # leave the generated path silently disagreeing with the SweetSpec path.
    let code = "const x = 1; if (x) return true;"
    let spec = getKnownSyntax(KnownSyntax.js).spec
    let fromSpec = scopesForSpec(spec, code)
    var lx = initLexer(jsInitData, code)
    var fromPre: Table[string, string]
    var tok = lx.getToken()
    while tok.kind != tkEOF:
      fromPre[lx.getTokenValue(tok)] = scopeForToken(lx, tok)
      tok = lx.getToken()
    check fromPre == fromSpec
    check fromPre["const"] == "storage.modifier"
    check fromPre["if"] == "keyword.control"
    check fromPre["true"] == "constant.language.boolean"
