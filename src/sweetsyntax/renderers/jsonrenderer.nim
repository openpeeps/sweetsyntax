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
  storageTypeKeywords = [
    "auto", "char", "const", "double", "enum", "extern", "float", "int",
    "long", "register", "restrict", "short", "signed", "static", "struct",
    "typedef", "union", "unsigned", "void", "volatile",
    "_Bool", "_Complex", "_Imaginary", "class", "interface", "type", "def",
    "fn", "func", "proc", "let", "var", "bool", "byte", "string", "object",
    "array", "public", "private", "protected", "abstract", "final", "impl"]
  controlKeywords = [
    "if", "else", "for", "while", "do", "switch", "case", "default",
    "return", "break", "continue", "goto", "try", "catch", "finally",
    "throw", "import", "export", "from", "yield", "await", "new", "delete",
    "typeof", "instanceof", "in", "of", "when", "elif", "except", "raise",
    "block", "with", "without", "match", "as", "async", "loop"]

proc scopeForToken*(lexer: SweetLexer, tok: Token): string =
  ## Derive a TextMate-style scope for the given token, based on the token
  ## kind and the keyword table declared in the syntax YAML spec.
  ##
  ## Note: `tok.attr` holds keyword lexemes (e.g. "int", "if"), not semantic
  ## classes, so scopes are derived from the kind and the identifiers table
  ## rather than from attributes.
  case tok.kind
  of tkComment: result = "comment.line"
  of tkDocComment: result = "comment.block.documentation"
  of tkString: result = "string.quoted.double"
  of tkChar: result = "string.quoted.single"
  of tkRegex: result = "string.regexp"
  of tkInt, tkHex, tkOctal, tkBinary, tkBigInt: result = "constant.numeric.integer"
  of tkFloat: result = "constant.numeric.float"
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
    elif value in ["true", "false"]:
      result = "constant.language.boolean"
    elif value in ["null", "undefined"]:
      result = "constant.language.null"
    elif value in lexer.identifiers:
      if value in storageTypeKeywords:
        result = "storage.type"
      elif value in controlKeywords:
        result = "keyword.control"
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
