import std/[unittest, strutils, tables]
import ../src/sweetsyntax
import ../src/sweetsyntax/renderers/[jsonrenderer, foldrenderer, highlight]

# Swift, D and Objective-C are highlight-only specs: no parser handler, no AST.
# These tests pin down the lexer behaviour the renderers depend on, plus the
# two known limitations that are properties of the lexer rather than the specs.

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
  ## Every token's rendered scope, for the tokens whose value is `value`.
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

suite "specs are registered":
  test "swift and objc resolve by name and extension":
    check getKnownSyntax(KnownSyntax.swift).spec.name == "Swift"
    check getKnownSyntax(KnownSyntax.objc).spec.name == "Objective-C"
    check syntaxForExt("swift") == KnownSyntax.swift
    check syntaxForExt("m") == KnownSyntax.objc
    check syntaxForExt("mm") == KnownSyntax.objc
    check syntaxForExt("d") == KnownSyntax.d

  test "all three declare comments, blocks and no parser operators":
    for lang in [KnownSyntax.swift, KnownSyntax.objc, KnownSyntax.d]:
      let spec = getKnownSyntax(lang).spec
      check spec.inline_comment == some("//")
      check spec.block_comment == ["/*", "*/"]
      check spec.blocks.open == "{"
      check spec.blocks.close == "}"
      ## No `operators:`/`statements:` sections: these are highlight-only specs
      ## and must not grow Pratt-parser tables or statement handlers.
      check spec.statements.len == 0
      check spec.operators.isNil or
        (spec.operators.prefix.len == 0 and spec.operators.postfix.len == 0 and
         spec.operators.infix.len == 0)

suite "D lexer":
  test "line and block comments lex as comments":
    let (_, toks) = lex(KnownSyntax.d, "// line\n/* block */\n")
    check hasTokenKind(toks, tkComment)
    check toks.len == 2

  test "doc comments are recognised":
    let (_, toks) = lex(KnownSyntax.d, "/** doc */\n")
    check hasTokenKind(toks, tkDocComment)

  test "string prefixes fold into one string token":
    check valueIs(KnownSyntax.d, "c\"abc\"", tkString)
    check valueIs(KnownSyntax.d, "w\"wide\"", tkString)
    check valueIs(KnownSyntax.d, "q\"quoted\"", tkString)
    check valueIs(KnownSyntax.d, "hex\"ff\"", tkString)

  test "backtick token strings lex as strings":
    check valueIs(KnownSyntax.d, "`ident`", tkString)

  test "numeric suffixes stay inside the number token":
    check valueIs(KnownSyntax.d, "10L", tkInt)
    check valueIs(KnownSyntax.d, "0xFFUL", tkHex)

  test "builtin types and modifiers get their own scopes":
    check "storage.type" in scopeValues(KnownSyntax.d, "int", "int")
    check "storage.type" in scopeValues(KnownSyntax.d, "void", "void")
    check "storage.type" in scopeValues(KnownSyntax.d, "string", "string")
    check "storage.modifier" in scopeValues(KnownSyntax.d, "immutable", "immutable")
    check "storage.modifier" in scopeValues(KnownSyntax.d, "inout", "inout")

  test "control flow, constants and `this` are distinguished":
    check "keyword.control" in scopeValues(KnownSyntax.d, "foreach", "foreach")
    check "constant.language.boolean" in scopeValues(KnownSyntax.d, "true", "true")
    check "constant.language.null" in scopeValues(KnownSyntax.d, "null", "null")
    check "variable.language" in scopeValues(KnownSyntax.d, "this", "this")

suite "Swift lexer":
  test "line and block comments lex as comments":
    check hasTokenKind(lex(KnownSyntax.swift, "// line\n").tokens, tkComment)
    check hasTokenKind(lex(KnownSyntax.swift, "/* block */\n").tokens, tkComment)

  test "multiline strings lex as a single string token":
    ## The lexer's triple-quote branch covers Swift's `"""`.
    check valueIs(KnownSyntax.swift, "\"\"\"\nabc\n\"\"\"", tkString)

  test "hash is not a comment":
    ## `#if` is a compiler directive in Swift, never a comment.
    let (_, toks) = lex(KnownSyntax.swift, "#if DEBUG\n")
    check not hasTokenKind(toks, tkComment)
    check hasTokenKind(toks, tkIdentifier)

  test "compiler directives get the preprocessor scope":
    check "meta.preprocessor" in
      scopeValues(KnownSyntax.swift, "#if DEBUG\n", "#")
    check "meta.preprocessor" in
      scopeValues(KnownSyntax.swift, "#if DEBUG\n", "if")

  test "directives inside literals and comments are left alone":
    ## `filters_skip_literals` keeps the directive filter from restyling a
    ## string or comment that merely contains `#if`.
    let code = "let s = \"#if\"\n// #endif\n"
    let (lx, toks) = lex(KnownSyntax.swift, code)
    for t in toks:
      let value = lx.getTokenValue(t)
      if t.kind == tkString:
        check scopeForToken(lx, t) == "string.quoted.double"
      elif t.kind == tkComment:
        check scopeForToken(lx, t).startsWith("comment")
      else:
        check value.len > 0

  test "declaration keywords, types and `self` are distinguished":
    check "keyword" in scopeValues(KnownSyntax.swift, "func f() {}", "func")
    check "storage.type" in scopeValues(KnownSyntax.swift, "var x: Int = 0", "Int")
    check "storage.type" in scopeValues(KnownSyntax.swift, "var s: String", "String")
    check "variable.language" in scopeValues(KnownSyntax.swift, "self.x", "self")
    check "keyword.control" in scopeValues(KnownSyntax.swift, "guard let x = y", "guard")

  test "standard library types are storage types":
    for ty in ["Bool", "Double", "Optional", "Array", "Dictionary", "UInt8"]:
      check scopeValues(KnownSyntax.swift, "var v: " & ty, ty) == ["storage.type"]

  test "nil and boolean literals get their scopes":
    check scopeValues(KnownSyntax.swift, "var v: Int? = nil", "nil") ==
      ["constant.language.null"]
    check scopeValues(KnownSyntax.swift, "var v = true", "true") ==
      ["constant.language.boolean"]

suite "Objective-C lexer":
  test "line and block comments lex as comments":
    check hasTokenKind(lex(KnownSyntax.objc, "// line\n").tokens, tkComment)
    check hasTokenKind(lex(KnownSyntax.objc, "/* block */\n").tokens, tkComment)

  test "hash is not a comment":
    let (_, toks) = lex(KnownSyntax.objc, "#import <Foundation/Foundation.h>\n")
    check not hasTokenKind(toks, tkComment)

  test "preprocessor directives get the preprocessor scope":
    for directive in ["import", "define", "ifdef", "endif", "pragma", "warning"]:
      let code = "#" & directive & "\n"
      check "meta.preprocessor" in scopeValues(KnownSyntax.objc, code, directive)

  test "directives inside literals and comments are left alone":
    let code = "char *s = \"#define\";\n// #import old\n"
    let (lx, toks) = lex(KnownSyntax.objc, code)
    for t in toks:
      if t.kind == tkString:
        check scopeForToken(lx, t) == "string.quoted.double"
      elif t.kind == tkComment:
        check scopeForToken(lx, t).startsWith("comment")

  test "at-keywords get keyword scopes":
    check "keyword" in
      scopeValues(KnownSyntax.objc, "@interface Foo : NSObject\n", "interface")
    check "keyword" in
      scopeValues(KnownSyntax.objc, "@implementation Foo\n", "implementation")
    check "keyword" in
      scopeValues(KnownSyntax.objc, "@property int x;\n", "property")
    check "keyword" in
      scopeValues(KnownSyntax.objc, "@selector(foo)\n", "selector")

  test "objc types are storage types":
    for ty in ["id", "Class", "SEL", "IMP", "BOOL", "instancetype"]:
      check scopeValues(KnownSyntax.objc, ty & " x;", ty) == ["storage.type"]

  test "constants and self are distinguished":
    check scopeValues(KnownSyntax.objc, "x = YES;", "YES") ==
      ["constant.language.boolean"]
    check scopeValues(KnownSyntax.objc, "x = nil;", "nil") ==
      ["constant.language.null"]
    check "variable.language" in scopeValues(KnownSyntax.objc, "[self x]", "self")

  test "c keywords are still scoped":
    check "keyword.control" in scopeValues(KnownSyntax.objc, "if (x) { }", "if")
    check "storage.type" in scopeValues(KnownSyntax.objc, "int x;", "int")
    check "storage.modifier" in scopeValues(KnownSyntax.objc, "static int x;", "static")

suite "folding":
  test "brace blocks fold in all three languages":
    for lang in [KnownSyntax.swift, KnownSyntax.objc, KnownSyntax.d]:
      var lx = initLexer(getKnownSyntax(lang).spec,
        "void f() {\n  int x = 1;\n}\n")
      let regions = computeFolds(lx, fmBraces)
      check regions.len == 1
      check regions[0].startLine == 1
      check regions[0].endLine == 3

  test "block comment folds in all three languages":
    for lang in [KnownSyntax.swift, KnownSyntax.objc, KnownSyntax.d]:
      var lx = initLexer(getKnownSyntax(lang).spec,
        "int a;\n/* one\n   two */\nint b;\n")
      ## Comment folds are always collected, whatever the brace mode is.
      let regions = computeFolds(lx, fmBraces)
      check regions.len == 1
      check regions[0].kind == fkComment
      check regions[0].startLine == 2
      check regions[0].endLine == 3

suite "spec integrity (every known language)":
  test "each keyword_scopes lexeme is also declared in identifiers":
    ## A lexeme listed only in `keyword_scopes` is never classified as a
    ## keyword by the lexer, so its scope silently does nothing. Two of the
    ## specs written here (`Codable`, `Array`) shipped with exactly that bug.
    var offenders: seq[string] = @[]
    for lang in KnownSyntax:
      let spec = getKnownSyntax(lang).spec
      for scope, lexemes in spec.keyword_scopes:
        for lex in lexemes:
          if lex notin spec.identifiers:
            offenders.add($lang & ": " & lex & " (" & scope & ")")
    check offenders.len == 0

  test "each keyword_scopes lexeme appears in exactly one scope":
    var offenders: seq[string] = @[]
    for lang in KnownSyntax:
      let spec = getKnownSyntax(lang).spec
      var seen = initTable[string, string]()
      for scope, lexemes in spec.keyword_scopes:
        for lex in lexemes:
          if lex in seen:
            offenders.add($lang & ": " & lex & " (" & seen[lex] &
              " and " & scope & ")")
          else:
            seen[lex] = scope
    check offenders.len == 0

  test "only markdown declares no identifiers":
    ## Markdown is entirely filter-driven and has no keyword vocabulary. Every
    ## other spec must declare at least one identifier, so a new spec cannot
    ## ship with an empty vocabulary unnoticed.
    for lang in KnownSyntax:
      let count = getKnownSyntax(lang).spec.identifiers.len
      if lang == KnownSyntax.md:
        check count == 0
      else:
        check count > 0

suite "uncolored output round-trips":
  test "each spec reconstructs its source exactly":
    ## The renderers emit the gaps *between* tokens. Whitespace after the final
    ## token is not emitted, so a trailing newline is dropped; every other byte
    ## is preserved, including string prefixes and backtick literals.
    let samples = [
      (KnownSyntax.d, "void main() {\n  auto x = c\"a\" + `b`;\n}\n"),
      (KnownSyntax.swift, "func f(x: Int) -> Int {\n  return x + 1\n}\n"),
      (KnownSyntax.objc, "int main(void) {\n  return 0;\n}\n")
    ]
    for (lang, code) in samples:
      let expected = code.strip(chars = {'\n'})
      check highlight(lang, code, hfAscii, useColor = false) == expected

  test "trailing whitespace after the last token is dropped":
    for lang in [KnownSyntax.swift, KnownSyntax.objc, KnownSyntax.d]:
      check highlight(lang, "int a = 1;\n\n\n", hfAscii,
        useColor = false) == "int a = 1;"
