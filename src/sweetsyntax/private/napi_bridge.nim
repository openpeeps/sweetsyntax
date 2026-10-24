## Node.js addon surface for sweetsyntax (napibuild only).
import std/json except `%*`
import pkg/openparser/json except `%*`
import ../config
import ../tokenizer
import ../sweetlexer
import ../engine/[ast, parser]
import ../renderers/highlight
import ../languages/[js, nim, c, php, ruby, go]

proc languageHandlers(ext: string): (ParsingCallback, set[LanguageFeature]) =
  let e = ext.strip(chars = {'.'}).toLowerAscii()
  case e
  of "js", "jsx", "mjs", "cjs", "ts", "tsx", "mts", "cts", "dts":
    result = (js.jsHandlers, {featAsync, featArrowFn, featGenerators,
                              featLabeledStmt, featTemplateLit})
  of "nim", "nims":
    result = (nim.nimHandlers, {})
  of "c", "h":
    result = (c.cHandlers, {featLabeledStmt, featAdjacentConcat})
  of "php", "phtml", "php3", "php4", "php5", "phps":
    result = (php.phpHandlers, {featLabeledStmt, featGenerators})
  of "rb", "ruby", "rake", "gemspec":
    result = (ruby.rubyHandlers, {})
  of "go":
    result = (go.goHandlers, {featLabeledStmt})
  else:
    result = (nil, {})

proc parseCode(code, ext: string): OpenAstProgram =
  let ks = syntaxForExt(ext)
  let syntax = getKnownSyntax(ks)
  let (handler, features) = languageHandlers(ext)
  var p = compile(syntax.spec)
  p.features = p.features + features
  if handler != nil: handler(p)
  p.lexer = initLexer(syntax.spec, code)
  p.curr = p.getToken()
  p.next = p.getToken()
  result = OpenAstProgram()
  while p.curr.kind != tkEOF:
    result.nodes.add(parseStatement(p))

init proc(module: Module) =
  proc parseScript(code: string, ext: string) {.export_napi.} =
    ## Parse a source string to an AST.
    let c = args.get("code").getStr()
    let e = args.get("ext").getStr()
    let program = parseCode(c, e)
    return jsParse(parseJson(toJson(program)))

  proc parseFileScript(path: string) {.export_napi.} =
    ## Parse a file to an AST.
    let p = args.get("path").getStr()
    let code = readFile(p)
    let ext = p.splitFile().ext
    let program = parseCode(code, ext)
    return jsParse(parseJson(toJson(program)))

  proc highlightScript(code: string, ext: string,
                      format: string) {.export_napi.} =
    ## Highlight a source string.
    let c = args.get("code").getStr()
    let e = args.get("ext").getStr()
    let f = args.get("format").getStr()
    let ks = syntaxForExt(e)
    let hf = case f.toLowerAscii()
      of "ascii", "ansi", "terminal": hfAscii
      of "html": hfHtml
      of "json", "ndjson": hfJson
      else: hfHtml
    return %* highlight(ks, c, hf)

  proc highlightFileScript(path: string,
                           format: string) {.export_napi.} =
    ## Highlight a file.
    let p = args.get("path").getStr()
    let f = args.get("format").getStr()
    let hf = case f.toLowerAscii()
      of "ascii", "ansi", "terminal": hfAscii
      of "html": hfHtml
      of "json", "ndjson": hfJson
      else: hfHtml
    return %* highlightFile(p, hf)
