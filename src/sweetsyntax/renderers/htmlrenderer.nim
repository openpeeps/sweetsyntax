# A powerful generic parser and AST explorer for analyzing
# programming languages!
#
# (c) 2026 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

## This module provides functionality to render the tokens
## for Web, using HTML spans with classes corresponding to token types and
## attributes for styling via CSS

import std/[strutils]
import ../sweetlexer

proc htmlEscape(s: string): string =
  result = s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")

proc tokenToHtml*(lexer: var SweetLexer, tok: Token): string =
  let lexeme = lexer.getLexeme(tok.start, tok.stop)
  let kindClass = $tok.kind
  let attrClasses = tok.attr.join(" ")
  let classes = if attrClasses.len > 0: kindClass & " " & attrClasses else: kindClass
  "<span class=\"" & classes & "\">" & htmlEscape(lexeme) & "</span>"

proc highlightHtml*(lexer: var SweetLexer): string =
  ## Render full source with HTML highlighting.
  ## Preserves skipped whitespace/newlines between tokens (mirrors
  ## `highlightAscii`), HTML-escaped so `int x` keeps its space.
  var prevStop = 0
  var tok = lexer.getToken()
  while tok.kind != tkEOF:
    if tok.start > prevStop:
      result.add htmlEscape(lexer.getLexeme(prevStop, tok.start)) # whitespace/gaps
    result.add tokenToHtml(lexer, tok)
    prevStop = tok.stop
    tok = lexer.getToken()