import std/[unittest, strutils, tables]
import ../src/sweetsyntax
import ../src/sweetsyntax/renderers/[jsonrenderer, foldrenderer, highlight]

# Java, C#, Kotlin, Perl, OCaml, Lua, Haskell and Zig are highlight-only specs:
# no parser handler, no AST. These tests pin down the lexer behaviour the
# renderers depend on, including the two lexer features added for them (Lua
# long bracket strings and `(**)` doc comments), and the documented gaps.

proc lex(lang: KnownSyntax, code: string,
         enableFilters = true): tuple[lexer: SweetLexer, tokens: seq[Token]] =
  let syntax = getKnownSyntax(lang)
  var lx = initLexer(syntax.spec, code, enableFilters = enableFilters)
  var toks: seq[Token] = @[]
  var tok = lx.getToken()
  while tok.kind != tkEOF:
    toks.add(tok)
    tok = lx.getToken()
  (lx, toks)

proc scopeValues(lang: KnownSyntax, code: string, value: string): seq[string] =
  ## Every token's rendered scope, for tokens whose value is exactly `value`.
  let (lx, toks) = lex(lang, code)
  for t in toks:
    if lx.getTokenValue(t) == value:
      result.add scopeForToken(lx, t)

proc hasTokenKind(toks: seq[Token], kind: SweetTokenKind): bool =
  for t in toks:
    if t.kind == kind: return true
  false

proc valueIs(lang: KnownSyntax, code: string, kind: SweetTokenKind): bool =
  ## True when some token of `kind` carries exactly this text.
  let (lx, toks) = lex(lang, code)
  for t in toks:
    if t.kind == kind and lx.getTokenValue(t) == code: return true
  false

proc tokenValues(lang: KnownSyntax, code: string): seq[string] =
  let (lx, toks) = lex(lang, code)
  for t in toks:
    result.add lx.getTokenValue(t)

suite "registration and flags":
  test "each language resolves by extension":
    check syntaxForExt("java") == KnownSyntax.java
    check syntaxForExt("cs") == KnownSyntax.csharp
    check syntaxForExt("csx") == KnownSyntax.csharp
    check syntaxForExt("kt") == KnownSyntax.kotlin
    check syntaxForExt("kts") == KnownSyntax.kotlin
    check syntaxForExt("pl") == KnownSyntax.perl
    check syntaxForExt("pm") == KnownSyntax.perl
    check syntaxForExt("ml") == KnownSyntax.ocaml
    check syntaxForExt("mli") == KnownSyntax.ocaml
    check syntaxForExt("lua") == KnownSyntax.lua
    check syntaxForExt("hs") == KnownSyntax.haskell
    check syntaxForExt("lhs") == KnownSyntax.haskell
    check syntaxForExt("zig") == KnownSyntax.zig
    check syntaxForExt("zon") == KnownSyntax.zig

  test "each language declares its own comment syntax":
    ## The point of this suite: no two of these eight share comment syntax, so
    ## each flag must be set individually and correctly.
    let slashes = [KnownSyntax.java, KnownSyntax.csharp, KnownSyntax.kotlin,
                   KnownSyntax.zig]
    for lang in slashes:
      check getKnownSyntax(lang).spec.inline_comment == some("//")
      check getKnownSyntax(lang).spec.block_comment == ["/*", "*/"]

    check getKnownSyntax(KnownSyntax.perl).spec.hash_comments
    check getKnownSyntax(KnownSyntax.perl).spec.inline_comment.isNone

    check getKnownSyntax(KnownSyntax.ocaml).spec.inline_comment.isNone
    check getKnownSyntax(KnownSyntax.ocaml).spec.block_comment == ["(*", "*)"]

    check getKnownSyntax(KnownSyntax.lua).spec.inline_comment == some("--")
    check getKnownSyntax(KnownSyntax.lua).spec.block_comment == ["--[[", "]]"]

    check getKnownSyntax(KnownSyntax.haskell).spec.inline_comment == some("--")
    check getKnownSyntax(KnownSyntax.haskell).spec.block_comment == ["{-", "-}"]

  test "lexer-only languages keep their distinctive lexer flags":
    check getKnownSyntax(KnownSyntax.perl).spec.heredocs
    check getKnownSyntax(KnownSyntax.csharp).spec.string_prefixes ==
      ["@", "$", "@$", "$@"]
    check getKnownSyntax(KnownSyntax.lua).spec.long_brackets
    ## Only Lua enables long brackets: a `[` must keep its meaning elsewhere.
    for lang in KnownSyntax:
      if lang != KnownSyntax.lua:
        check not getKnownSyntax(lang).spec.long_brackets

  test "no new language grew a parser operator table":
    for lang in [KnownSyntax.java, KnownSyntax.csharp, KnownSyntax.kotlin,
                 KnownSyntax.perl, KnownSyntax.ocaml, KnownSyntax.lua,
                 KnownSyntax.haskell, KnownSyntax.zig]:
      let spec = getKnownSyntax(lang).spec
      check spec.statements.len == 0
      check spec.operators.isNil or
        (spec.operators.prefix.len == 0 and spec.operators.postfix.len == 0 and
         spec.operators.infix.len == 0)

suite "Java":
  test "annotations get a tag scope":
    check "entity.name.tag" in scopeValues(KnownSyntax.java,
      "@Override\n", "@")
    check "entity.name.tag" in scopeValues(KnownSyntax.java,
      "@Override\n", "Override")
    check "entity.name.tag" in scopeValues(KnownSyntax.java,
      "@SuppressWarnings(\"x\")\n", "SuppressWarnings")

  test "an at sign inside a string or comment is not an annotation":
    ## This is what `filters_skip_literals` buys: a loose `@word` pattern would
    ## otherwise restyle the whole string literal.
    let code = "String s = \"a@b.com\";\n// @deprecated\n"
    let (lx, toks) = lex(KnownSyntax.java, code)
    for t in toks:
      if t.kind == tkString:
        check scopeForToken(lx, t) == "string.quoted.double"
      elif t.kind == tkComment:
        check scopeForToken(lx, t).startsWith("comment")

  test "text blocks lex as a single string token":
    check valueIs(KnownSyntax.java, "\"\"\"\nabc\n\"\"\"", tkString)

  test "primitive types, modifiers and `_` are distinguished":
    let types: seq[string] = @["int", "boolean", "char", "double", "void"]
    for ty in types:
      let scopes = scopeValues(KnownSyntax.java, ty & " x;", ty)
      check scopes.len == 1
      check scopes[0] == "storage.type"
    check scopeValues(KnownSyntax.java, "public int x;", "public") ==
      ["storage.modifier"]
    check scopeValues(KnownSyntax.java, "int x;", "this").len == 0
    check scopeValues(KnownSyntax.java, "return null;", "null") ==
      ["constant.language.null"]
    check scopeValues(KnownSyntax.java, "switch (x) { }", "switch") ==
      ["keyword.control"]
    ## `_` has been reserved since Java 9
    check scopeValues(KnownSyntax.java, "int _ = 1;", "_") == ["keyword"]

  test "numeric literal bases and separators lex as one token":
    let numbers: seq[string] = @["0xFF", "0b1010", "0o17", "1_000_000", "0xFFL"]
    for num in numbers:
      let vals = tokenValues(KnownSyntax.java, num & ";")
      check vals.len == 2
      check vals[0] == num
      check vals[1] == ";"

suite "C#":
  test "verbatim and interpolated strings fold into one token":
    ## `@` is punctuation, not an identifier start, so the prefix scan has to
    ## arm on the prefix's own first character for `@"..."` to work at all.
    check valueIs(KnownSyntax.csharp, "@\"a\"", tkString)
    check valueIs(KnownSyntax.csharp, "$\"a\"", tkString)
    check valueIs(KnownSyntax.csharp, "$@\"a\"", tkString)
    check valueIs(KnownSyntax.csharp, "@$\"a\"", tkString)

  test "an at sign inside a string is not a verbatim string":
    ## Regression guard: the relaxed prefix check must not split `user@host`.
    check tokenValues(KnownSyntax.csharp, "\"a@b\"") == ["\"a@b\""]

  test "preprocessor directives get the preprocessor scope":
    check "meta.preprocessor" in scopeValues(KnownSyntax.csharp,
      "#nullable enable\n", "nullable")
    check "meta.preprocessor" in scopeValues(KnownSyntax.csharp,
      "#region setup\n", "region")
    ## `#` is not a comment in C#
    check not hasTokenKind(lex(KnownSyntax.csharp, "#if X\n").tokens, tkComment)

  test "preprocessor-looking text in a string is left alone":
    let (lx, toks) = lex(KnownSyntax.csharp, "var s = \"#if X\";\n")
    for t in toks:
      if t.kind == tkString:
        check scopeForToken(lx, t) == "string.quoted.double"

  test "types, modifiers and keywords are distinguished":
    let types: seq[string] = @["int", "string", "object", "double", "bool", "var"]
    for ty in types:
      let scopes = scopeValues(KnownSyntax.csharp, ty & " x;", ty)
      check scopes.len == 1
      check scopes[0] == "storage.type"
    check scopeValues(KnownSyntax.csharp, "public int x;", "public") ==
      ["storage.modifier"]
    check scopeValues(KnownSyntax.csharp, "await x;", "await") ==
      ["keyword.control"]
    check scopeValues(KnownSyntax.csharp, "var x = null;", "null") ==
      ["constant.language.null"]

  test "raw string literals lex as a single string token":
    check valueIs(KnownSyntax.csharp, "\"\"\"\nabc\n\"\"\"", tkString)

suite "Kotlin":
  test "line and block comments lex as comments":
    check hasTokenKind(lex(KnownSyntax.kotlin, "// c\n").tokens, tkComment)
    check hasTokenKind(lex(KnownSyntax.kotlin, "/* c */\n").tokens, tkComment)
    check hasTokenKind(lex(KnownSyntax.kotlin, "/** doc */\n").tokens,
      tkDocComment)

  test "types, modifiers and keywords are distinguished":
    let types: seq[string] = @["Int", "String", "Boolean", "Unit", "List",
      "MutableList"]
    for ty in types:
      let scopes = scopeValues(KnownSyntax.kotlin, "val v: " & ty, ty)
      check scopes.len == 1
      check scopes[0] == "storage.type"
    check scopeValues(KnownSyntax.kotlin, "private val x = 1", "private") ==
      ["storage.modifier"]
    check scopeValues(KnownSyntax.kotlin, "fun f() {}", "fun") == ["keyword"]
    check scopeValues(KnownSyntax.kotlin, "when (x) { }", "when") ==
      ["keyword.control"]

  test "string templates stay inside one string token":
    ## Documented gap: `"$name"` and `"${expr}"` are not highlighted as code.
    check valueIs(KnownSyntax.kotlin, "\"a$b\"", tkString)
    check tokenValues(KnownSyntax.kotlin, "\"a$b\"") == ["\"a$b\""]

  test "ranges lex as single operator tokens":
    let ranges: seq[string] = @["..", "..<"]
    for op in ranges:
      let vals = tokenValues(KnownSyntax.kotlin, "val r = 1" & op & "2")
      check vals.len == 6
      check vals[0] == "val"
      check vals[1] == "r"
      check vals[2] == "="
      check vals[3] == "1"
      check vals[4] == op
      check vals[5] == "2"

suite "Perl":
  test "hash comments lex as comments, including the shebang":
    check hasTokenKind(lex(KnownSyntax.perl, "# c\n").tokens, tkComment)
    let (lx, toks) = lex(KnownSyntax.perl, "#!/usr/bin/perl\n")
    check toks.len == 1
    check lx.getTokenValue(toks[0]).contains("usr/bin/perl")

  test "dollar sigils are part of the identifier token":
    ## `$` is an identifier start, so these need no spec support at all.
    check tokenValues(KnownSyntax.perl, "$x = 1") == ["$x", "=", "1"]
    check tokenValues(KnownSyntax.perl, "$_ = 1") == ["$_", "=", "1"]
    check tokenValues(KnownSyntax.perl, "$$ = 1") == ["$$", "=", "1"]

  test "at and percent sigils read as punctuation then a variable":
    ## Documented gap: unlike `$`, `@` and `%` are not identifier starts.
    check tokenValues(KnownSyntax.perl, "@ARGV") == ["@", "ARGV"]
    check tokenValues(KnownSyntax.perl, "%ENV") == ["%", "ENV"]

  test "special variables get a variable scope":
    ## Only `$` followed by identifier characters scans as one token; `$@`,
    ## `$!` and `$?` stop at the sigil, which the spec documents.
    let vars: seq[string] = @["$_", "$0", "$$"]
    for v in vars:
      let scopes = scopeValues(KnownSyntax.perl, v & " = 1;", v)
      check scopes.len == 1
      check scopes[0] == "variable.language"

  test "heredocs lex as one string token running to the terminator":
    ## Perl terminates the opener with `;`, which only the opt-in
    ## `heredoc_opener_punctuation` accepts. `getTokenValue` strips the string
    ## delimiters, so the value starts after `<<"`.
    let code = "print <<\"EOF\";\nbody\nEOF\n"
    let (lx, toks) = lex(KnownSyntax.perl, code)
    check toks.len == 2
    check toks[0].kind == tkIdentifier
    check toks[1].kind == tkString
    let value = lx.getTokenValue(toks[1])
    check value.contains("body")
    check value.endsWith("EOF\n")

  test "bareword quotes are a documented gap":
    ## `qw(...)` does not become a string; it is a call to a variable named
    ## `qw`. Pinned so the gap is explicit rather than accidental.
    check not valueIs(KnownSyntax.perl, "qw(a b)", tkString)

  test "control flow, builtins and compile-time constants are distinguished":
    check scopeValues(KnownSyntax.perl, "if (1) { }", "if") == ["keyword.control"]
    check scopeValues(KnownSyntax.perl, "print 1;", "print") == ["keyword"]
    check scopeValues(KnownSyntax.perl, "my $x = 1;", "my") == ["storage.modifier"]
    check scopeValues(KnownSyntax.perl, "print __LINE__;", "__LINE__") ==
      ["constant.language"]

suite "OCaml":
  test "block comments lex as comments and doc comments are recognised":
    ## The `(**` doc-comment form needed the block-doc check generalised from
    ## `/*` to `(*`.
    check hasTokenKind(lex(KnownSyntax.ocaml, "(* c *)\n").tokens, tkComment)
    check hasTokenKind(lex(KnownSyntax.ocaml, "(** doc *)\n").tokens,
      tkDocComment)
    check hasTokenKind(lex(KnownSyntax.ocaml, "(*! bang *)\n").tokens,
      tkDocComment)

  test "there is no inline comment form":
    ## `//` is not a comment in OCaml, so it lexes as two operators.
    check not hasTokenKind(lex(KnownSyntax.ocaml, "// c\n").tokens, tkComment)
    check tokenValues(KnownSyntax.ocaml, "// c") == ["/", "/", "c"]

  test "predefined types and keywords are distinguished":
    let types: seq[string] = @["int", "float", "string", "bool", "unit", "list"]
    for ty in types:
      let scopes = scopeValues(KnownSyntax.ocaml, "let x : " & ty, ty)
      check scopes.len == 1
      check scopes[0] == "storage.type"
    check scopeValues(KnownSyntax.ocaml, "let x = 1", "let") == ["keyword"]
    check scopeValues(KnownSyntax.ocaml, "match x with", "match") ==
      ["keyword.control"]
    check scopeValues(KnownSyntax.ocaml, "let x = true", "true") ==
      ["constant.language.boolean"]

  test "dotted and double-semicolon operators lex as single tokens":
    check tokenValues(KnownSyntax.ocaml, "f x |> g") == ["f", "x", "|>", "g"]
    check tokenValues(KnownSyntax.ocaml, "let x = 1;;") ==
      ["let", "x", "=", "1", ";;"]

suite "Lua":
  test "line comments, long comments and long strings all lex correctly":
    check hasTokenKind(lex(KnownSyntax.lua, "-- c\n").tokens, tkComment)
    check hasTokenKind(lex(KnownSyntax.lua, "--[[ c ]]\n").tokens, tkComment)
    check valueIs(KnownSyntax.lua, "[[a\nb]]", tkString)
    check valueIs(KnownSyntax.lua, "[==[a]]b]==]", tkString)

  test "a long comment wins over an inline comment":
    ## Block comments are checked before inline comments, so `--[[ x ]]` is a
    ## comment and not a `--` comment followed by table syntax.
    let (lx, toks) = lex(KnownSyntax.lua, "--[[ x ]]\n")
    check toks.len == 1
    check toks[0].kind == tkComment

  test "a newline after the long-bracket opener is skipped":
    check tokenValues(KnownSyntax.lua, "local s = [[\nbody]]\n") ==
      ["local", "s", "=", "[[\nbody]]"]

  test "table indexing is not mistaken for a long bracket":
    ## Regression guard for the new lexer branch: `[` must only open a string
    ## when a matching `[` (with optional `=`) follows it.
    check tokenValues(KnownSyntax.lua, "t[1] = 2") == ["t", "[", "1", "]", "=", "2"]
    check tokenValues(KnownSyntax.lua, "t[k] = 1") == ["t", "[", "k", "]", "=", "1"]
    check tokenValues(KnownSyntax.lua, "s = a[b][c]") ==
      ["s", "=", "a", "[", "b", "]", "[", "c", "]"]

  test "keywords, booleans, nil and self are distinguished":
    check scopeValues(KnownSyntax.lua, "if x then end", "if") ==
      ["keyword.control"]
    check scopeValues(KnownSyntax.lua, "local function f() end", "local") ==
      ["keyword"]
    check scopeValues(KnownSyntax.lua, "local x = true", "true") ==
      ["constant.language.boolean"]
    check scopeValues(KnownSyntax.lua, "local x = nil", "nil") ==
      ["constant.language.null"]
    check scopeValues(KnownSyntax.lua, "function f() return self end",
      "self") == ["variable.language"]

suite "Haskell":
  test "line comments and block comments lex as comments":
    check hasTokenKind(lex(KnownSyntax.haskell, "-- c\n").tokens, tkComment)
    check hasTokenKind(lex(KnownSyntax.haskell, "{- c -}\n").tokens, tkComment)

  test "the arrow operator is shadowed by the line comment":
    ## Documented gap: `--` starts a comment, so `a --> b` comments out the
    ## rest of the line. Pinned so the behaviour is explicit.
    check hasTokenKind(lex(KnownSyntax.haskell, "a --> b\n").tokens, tkComment)

  test "types and keywords are distinguished":
    let types: seq[string] = @["Int", "String", "Bool", "Maybe", "Either", "IO"]
    for ty in types:
      let scopes = scopeValues(KnownSyntax.haskell, "f :: " & ty, ty)
      check scopes.len == 1
      check scopes[0] == "storage.type"
    check scopeValues(KnownSyntax.haskell, "module M where", "module") ==
      ["keyword"]
    check scopeValues(KnownSyntax.haskell, "case x of", "case") ==
      ["keyword.control"]
    check scopeValues(KnownSyntax.haskell, "f x = True", "True") ==
      ["constant.language.boolean"]

  test "operators lex as single tokens":
    check tokenValues(KnownSyntax.haskell, "f :: Int -> Int") ==
      ["f", "::", "Int", "->", "Int"]
    check tokenValues(KnownSyntax.haskell, "f x >>= g") ==
      ["f", "x", ">>=", "g"]
    check tokenValues(KnownSyntax.haskell, "f x = [1] ++ [2]") ==
      ["f", "x", "=", "[", "1", "]", "++", "[", "2", "]"]

suite "Zig":
  test "line and block comments lex as comments":
    check hasTokenKind(lex(KnownSyntax.zig, "// c\n").tokens, tkComment)
    check hasTokenKind(lex(KnownSyntax.zig, "/* c */\n").tokens, tkComment)

  test "the bang and slash doc comments are ordinary comments":
    ## Documented gap: the lexer has no inline doc-comment form, so `//!` and
    ## `///` keep their marker in the comment text.
    check hasTokenKind(lex(KnownSyntax.zig, "//! c\n").tokens, tkComment)
    check hasTokenKind(lex(KnownSyntax.zig, "/// c\n").tokens, tkComment)

  test "primitive types, modifiers and keywords are distinguished":
    let types: seq[string] = @["u8", "i32", "f64", "bool", "void",
      "comptime_int"]
    for ty in types:
      let scopes = scopeValues(KnownSyntax.zig, "var x: " & ty, ty)
      check scopes.len == 1
      check scopes[0] == "storage.type"
    check scopeValues(KnownSyntax.zig, "pub fn f() void {}", "pub") ==
      ["storage.modifier"]
    check scopeValues(KnownSyntax.zig, "fn f() void {}", "fn") == ["keyword"]
    check scopeValues(KnownSyntax.zig, "while (x) {}", "while") ==
      ["keyword.control"]
    check scopeValues(KnownSyntax.zig, "var x: ?u8 = null", "null") ==
      ["constant.language.null"]

  test "numeric literal bases lex as one token":
    let numbers: seq[string] = @["0xFF", "0b1010", "0o17", "1_000", "0xff_00"]
    for num in numbers:
      let vals = tokenValues(KnownSyntax.zig, "var x: u32 = " & num & ";")
      check vals.len == 7
      check vals[5] == num
      check vals[6] == ";"

suite "folding":
  test "brace languages fold on braces":
    let braces = [KnownSyntax.java, KnownSyntax.csharp, KnownSyntax.kotlin,
                  KnownSyntax.zig]
    for lang in braces:
      var lx = initLexer(getKnownSyntax(lang).spec,
        "fun f() {\n  return 1\n}\n")
      let regions = computeFolds(lx, fmBraces)
      check regions.len == 1
      check regions[0].startLine == 1
      check regions[0].endLine == 3

  test "indent languages fold on indentation":
    ## OCaml, Lua and Haskell express blocks with layout, so `fmAuto` picks
    ## indent folding for them when the sample has no brace token.
    let indented = [
      (KnownSyntax.ocaml, "let f x =\n  x + 1\n"),
      (KnownSyntax.lua, "function f()\n  return 1\nend\n"),
      (KnownSyntax.haskell, "f x =\n  x + 1\n")
    ]
    for (lang, code) in indented:
      var lx = initLexer(getKnownSyntax(lang).spec, code)
      let regions = computeFolds(lx)
      check regions.len == 1
      check regions[0].kind == fkIndent

suite "uncolored output round-trips":
  test "each new spec reconstructs its comment-free source exactly":
    let samples = [
      (KnownSyntax.java, "int x = 0x1F;"),
      (KnownSyntax.csharp, "var s = @\"a\";"),
      (KnownSyntax.kotlin, "val v: Int = 1"),
      (KnownSyntax.perl, "my $x = 1;"),
      (KnownSyntax.ocaml, "let x = 1"),
      (KnownSyntax.lua, "local s = [[a]]"),
      (KnownSyntax.haskell, "f x = x + 1"),
      (KnownSyntax.zig, "const x: u8 = 1;")
    ]
    for (lang, code) in samples:
      check highlight(lang, code, hfAscii, useColor = false) == code
