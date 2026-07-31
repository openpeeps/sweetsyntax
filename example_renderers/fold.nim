import std/[os, strutils]
import sweetsyntax
import sweetsyntax/renderers/foldrenderer

if paramCount() < 1:
  echo "Usage: fold <js|nim|c|...> [--indent] [--pre] [code]"
  quit 1

let syntax = getKnownSyntax(parseEnum[KnownSyntax](paramStr(1)))
var mode = fmAuto
var pre = false
var codeArgs: seq[string]
for i in 2 .. paramCount():
  case paramStr(i)
  of "--indent": mode = fmIndent
  of "--pre": pre = true
  else: codeArgs.add(paramStr(i))

let code =
  if codeArgs.len > 0:
    codeArgs.join(" ")
  else:
    stdin.readAll()

var lx = initLexer(syntax.spec, code)
stdout.write(foldsToJsonLd(computeFolds(lx, mode, pre)))
