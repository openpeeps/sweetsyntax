# A generic syntax highlighter
#
# (c) 2025 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

## This module provides functionality to render the tokens
## for Web, using HTML spans with classes corresponding to token types and
## attributes for styling via CSS

import std/[strutils]
import ../sweetlexer

proc htmlEscape(s: string): string =
  result = s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")

proc tokenToHtml*(lexer: var SweetLexer, tok: SweetTokenRange): string =
  let lexeme = lexer.getLexeme(tok.start, tok.stop)
  let kindClass = $tok.kind
  let attrClasses = tok.attr.join(" ")
  let classes = if attrClasses.len > 0: kindClass & " " & attrClasses else: kindClass
  "<span class=\"" & classes & "\">" & htmlEscape(lexeme) & "</span>"

proc highlightHtml*(lexer: var SweetLexer): string =
  var html = ""
  var tok = lexer.getToken()
  while tok.kind != tkEOF:
    html.add tokenToHtml(lexer, tok)
    tok = lexer.getToken()
  html