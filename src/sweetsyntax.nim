# A generic syntax highlighter
#
# (c) 2025 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

import std/tables
import ./sweetsyntax/[config, sweetlexer]

export config, sweetlexer

when isMainModule:
  import std/[strformat, strutils]
  # example tokenizing javascript
  let jsSyntax = getKnownSyntax(KnownSyntax.js)
  # let jsCode = """var x = 10;"""
  let jsCode = readFile("./react.development.js")
  var lexer = initLexer(jsSyntax.spec, jsCode)
  var defs: seq[tuple[kind: SweetTokenKind, ident: string, value: string, line: int, col: int]] = @[]
  while true:
    let token = lexer.getToken()
    if token.kind == tkEOF:
      break
    let val = lexer.getTokenValue(token)
    if token.kind == tkPunct and jsSyntax.spec.symbols.hasKey(val):
      defs.add((token.kind, jsSyntax.spec.symbols[val], val, token.line, token.col))
    else:
      if jsSyntax.spec.identifiers.hasKey(val):
        defs.add((token.kind, jsSyntax.spec.identifiers[val], val, token.line, token.col))
      else:
        defs.add((token.kind, "", val, token.line, token.col))
  # echo defs
