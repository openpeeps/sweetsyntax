import std/[os, strutils]
import sweetsyntax
import sweetsyntax/renderers/jsonrenderer

if paramCount() < 1:
  echo "Usage: json <js|nim|c|...> [code]"
  quit 1

let syntax = getKnownSyntax(parseEnum[KnownSyntax](paramStr(1)))
let code =
  if paramCount() > 1:
    paramStr(2)
  else:
    stdin.readAll()

var lx = initLexer(syntax.spec, code)
stdout.write(highlightJsonLd(lx))
