# A powerful generic parser and AST explorer for analyzing
# programming languages!
#
# (c) 2026 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

## This module provides functionality to render tokens as line-delimited JSON
## (NDJSON). Each token is emitted as a self-contained JSON object on its own
## line, making the output easy to stream over websocket/udp for syntax
## highlighting in editors and other higher-level applications.
##
## Every token object exposes:
## - `kind`: the raw token kind (e.g. "ident", "string", "comment")
## - `scope`: a TextMate-style scope derived from the token kind and attributes
## - `attr`: user-defined attributes (e.g. keyword names, YAML filter hits)
## - `line`, `col`: 1-based line/column of the token start
## - `start`, `stop`: byte offsets into the source (stop is exclusive)
## - `value`: the token lexeme (source text)

import std/tables
import pkg/openparser/json
import ../sweetlexer

const
  operatorChars = {'+', '-', '*', '/', '%', '=', '<', '>', '!', '&', '|', '^', '~', '?'}
    # A punctuation token is reported as `keyword.operator` when it opens with
    # one of these. This is deliberately kept here rather than read from the
    # spec: it describes the orthography shared by every language (operators
    # are spelled with operator characters) and not any one language's
    # vocabulary. It also has to stay usable for specs that declare no
    # `operators:` block at all -- highlight-only specs like `cpp.yaml` have
    # none, since that table exists for the Pratt parser, so the operator
    # vocabulary cannot come from there without making lexer-only rendering
    # depend on a parser table. Per-language refinement belongs in the spec's
    # own `symbols` names and, where finer control is needed, in
    # `keyword_scopes`.


proc scopeForFilterAttr(tok: Token): string =
  ## Filter-driven scopes for non-programming languages (CSS, Markdown).
  ## Returns "" when no filter attr applies so kind-based mapping below runs.
  for a in tok.attr:
    case a
    of "markup.heading", "markup.bold", "markup.italic",
       "markup.strikethrough", "markup.raw.block", "markup.raw.inline",
       "markup.link", "markup.image", "markup.list", "markup.quote",
       "markup.hr", "markup.table", "markup.frontmatter",
       "markup.indicator", "markup.tag",
       "entity.name.tag", "entity.other.attribute-name",
       "constant.numeric.date", "constant.character.escape",
       "selector.id", "selector.class", "at.rule":
      return a
    of "property.name":
      return "variable.other.property"
    else:
      discard
  ""

proc scopeForToken*(lexer: SweetLexer, tok: Token): string =
  ## Derive a TextMate-style scope for the given token, based on the token
  ## kind and the tables declared in the syntax YAML spec.
  ##
  ## Keyword classification is entirely the spec's business: a spec lists the
  ## lexemes it wants scoped in `keyword_scopes` and the renderer just looks
  ## the lexeme up, so no vocabulary is baked in here. A spec that declares no
  ## scopes gets a flat `keyword` for every identifier it lists. `tok.attr`
  ## holds keyword lexemes (e.g. "int", "if"), not semantic classes, so it is
  ## never used to classify. YAML `filters` (CSS, Markdown) are the exception:
  ## their dotted attrs (e.g. "markup.heading") map 1:1 to scopes.
  let filterScope = scopeForFilterAttr(tok)
  if filterScope.len > 0:
    return filterScope
  case tok.kind
  of tkComment: result = "comment.line"
  of tkDocComment: result = "comment.block.documentation"
  of tkString: result = "string.quoted.double"
  of tkChar: result = "string.quoted.single"
  of tkRegex: result = "string.regexp"
  of tkInt, tkHex, tkOctal, tkBinary, tkBigInt: result = "constant.numeric.integer"
  of tkFloat: result = "constant.numeric.float"
  of tkImag: result = "constant.numeric.imaginary"
  of tkPunct:
    let value = lexer.getTokenValue(tok)
    if value.len > 0 and value[0] in operatorChars:
      result = "keyword.operator"
    else:
      result = "punctuation"
  of tkIdentifier:
    let value = lexer.getTokenValue(tok)
    if "field.name" in tok.attr:
      result = "variable.other.property"
    elif value in lexer.identifiers:
      # The spec declared this word a keyword; it may refine that with a
      # scope. Testing `identifiers` first means a stale or misspelled entry
      # in `keyword_scopes` cannot promote a plain variable to a keyword.
      if lexer.keywordScopes.hasKey(value):
        result = lexer.keywordScopes[value]
      else:
        result = "keyword"
    else:
      result = "variable"
  of tkEOF: result = "source"

proc tokenToJson*(lexer: SweetLexer, tok: Token, includeValue = true): JsonNode =
  ## Build a JSON object for a single token.
  result = newJObject()
  result["kind"] = newJString($tok.kind)
  result["scope"] = %scopeForToken(lexer, tok)
  if tok.attr.len > 0:
    var attrs = newJArray()
    for a in tok.attr:
      attrs.add(%a)
    result["attr"] = attrs
  result["line"] = %tok.line
  result["col"] = %tok.col
  result["start"] = %tok.start
  result["stop"] = %tok.stop
  if includeValue:
    result["value"] = %lexer.getTokenValue(tok)

proc tokenToJsonLd*(lexer: SweetLexer, tok: Token, includeValue = true): string =
  ## Render a single token as one line of NDJSON, terminated by a newline.
  result = $tokenToJson(lexer, tok, includeValue) & "\n"

proc highlightJsonLd*(lexer: var SweetLexer, includeValue = true): string =
  ## Render the full source as line-delimited JSON.
  ## Optionally emits a `meta` header line describing the document.
  var tok = lexer.getToken()
  while tok.kind != tkEOF:
    result.add tokenToJsonLd(lexer, tok, includeValue)
    tok = lexer.getToken()
