# A powerful generic parser and AST explorer for analyzing
# programming languages!
#
# (c) 2026 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

## SweetSyntax is a powerful YAML-based generic parser and AST explorer for analyzing
## programming languages.
## 
## Written in Nim, it provides a flexible foundation for building high-level parsers,
## syntax highlighters, domain-specific languages, bundlers, minifiers, obfuscators, linters,
## or any sweet tool that requires a structured representation of source code.

when defined(napibuild):
  # Node.js native addon entry point. Built separately via
  # `denim build src/sweetsyntax.nim --cmake -y` so the library itself
  # gains no denim dependency and zero overhead.
  import denim
  include ./sweetsyntax/private/napi_convert
  include ./sweetsyntax/private/napi_bridge

import ./sweetsyntax/[config, sweetlexer]
import ./sweetsyntax/engine/[ast, parser]
import ./sweetsyntax/renderers/highlight
export config, sweetlexer, ast, parser, highlight

when isMainModule and not defined(napibuild):
  import std/[tables, os, parseopt, strutils]
  import pkg/openparser/json
  import ./sweetsyntax/languages/[js, nim, c, php, ruby, go]

  const versionStr = "0.2.1"

  const
    ansiReset = "\e[0m"
    ansiBoldWhite = "\e[1;37m"
    ansiGrey = "\e[90m"
    ansiRed = "\e[31m"

  proc useColor(): bool =
    getEnv("NO_COLOR") == "" and getEnv("TERM") != "dumb"

  proc paint(s, code: string): string =
    if useColor():
      code & s & ansiReset
    else:
      s

  proc label(s: string): string =
    paint(s, ansiBoldWhite)

  proc grey(s: string): string =
    paint(s, ansiGrey)

  proc errPrefix(): string =
    paint("error:", ansiRed)

  proc printHelp() =
    echo grey("sweetsyntax " & versionStr & " - generic parser and AST explorer") & "\n"
    echo grey("MIT license | Made by Humans from OpenPeeps\n  https://github.com/openpeeps/sweetsyntax")
    echo ""
    echo "usage: sweetsyntax <command> <file> [options]"
    echo ""
    echo label("commands:")
    echo "  parse               " & grey("validate: parse and report errors")
    echo "  ast                 " & grey("print the full AST as JSON")
    echo "  tree                " & grey("print the AST as an indent-based tree")
    echo "  highlight           " & grey("highlight a file with the lexer only, no parsing or AST")
    echo ""
    echo label("options:")
    echo "  --format:<fmt>      " & grey("highlight only: ascii, html or json (default: ascii)")
    echo "  -o                  " & grey("ast: write <file>.json next to the input; highlight: write <file>.txt/.html/.json")
    echo "  -y                  " & grey("ast: overwrite the existing JSON file without asking")
    echo "  --no-color          " & grey("highlight: drop ANSI codes from ascii output")
    echo "  -h, --help          " & grey("show this help")
    echo "  --version           " & grey("show version")

  proc getLanguageHandlers(ext: string): (ParsingCallback, set[LanguageFeature]) =
    ## Resolve language handlers and features by file extension.
    ## NOTE: `result` is assigned explicitly in every branch. Returning a
    ## bare `(nil, {})` literal in the `else` branch would be fully
    ## compile-time-known, so the C backend would lift it into a
    ## `static const` aggregate initialized from another static, which
    ## Apple Clang on ARM64 rejects
    ## (`error: initializer element is not a compile-time constant`).
    case ext
    of "js", "jsx", "ts", "tsx":
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
      result[0] = nil
      result[1] = {}

  proc extOf(path: string): string =
    let ext = path.splitFile.ext
    if ext.len > 1: ext[1..^1].toLowerAscii else: ""

  proc confirmOverwrite(path: string): bool =
    stdout.write("Confirm overwrite of the existing JSON file (" &
      extractFilename(path) & ")? [y/N]: ")
    stdout.flushFile()
    try:
      result = stdin.readLine().strip().toLowerAscii in ["y", "yes"]
    except EOFError:
      result = false

  proc parseCommand(srcPath: string): int =
    let ext = extOf(srcPath)
    let (handler, features) = getLanguageHandlers(ext)
    if handler == nil:
      echo errPrefix() & " unsupported file extension: ." & ext
      return 1
    try:
      discard parseScript(srcPath, handler, features)
    except OpenAstParsingError as e:
      echo e.msg
      return 1
    0

  proc astCommand(srcPath: string, writeOut, overwrite: bool): int =
    # Generate the AST of a script file, either to stdout or to a sibling
    # JSON file next to the input.
    let absPath = absolutePath(srcPath)
    let ext = extOf(absPath)
    let (handler, features) = getLanguageHandlers(ext)
    if handler == nil:
      echo errPrefix() & " unsupported file extension: ." & ext
      return 1
    try:
      let astProgram = parseScript(absPath, handler, features)
      if writeOut:
        let outputPath = absPath.changeFileExt("json")
        if fileExists(outputPath):
          if not overwrite and not confirmOverwrite(outputPath):
            return 0
        writeFile(outputPath, toJson(astProgram))
      else:
        echo toJson(astProgram)
    except OpenAstParsingError as e:
      echo e.msg
      return 1
    0

  proc treeCommand(srcPath: string): int =
    # Print the AST of a script file as an indent-based tree
    # (2 spaces per level), Nim dumpTree-style.
    let absPath = absolutePath(srcPath)
    let ext = extOf(absPath)
    let (handler, features) = getLanguageHandlers(ext)
    if handler == nil:
      echo errPrefix() & " unsupported file extension: ." & ext
      return 1
    try:
      let astProgram = parseScript(absPath, handler, features)
      stdout.write dumpTree(astProgram)
    except OpenAstParsingError as e:
      echo e.msg
      return 1
    0

  proc highlightCommand(srcPath, formatArg: string, useColor,
      writeOut: bool): int =
    # Lexer-only highlighting: tokenize with the language's YAML spec and
    # render, without parsing or validating. Works for every known syntax,
    # including the highlight-only ones that have no parser handlers.
    var format = hfAscii
    case formatArg.toLowerAscii
    of "ascii", "ansi", "terminal": discard
    of "html": format = hfHtml
    of "json", "ndjson": format = hfJson
    else:
      echo errPrefix() & " unknown format: use ascii, html or json"
      return 1
    var output: string
    try:
      output = highlightFile(srcPath, format, useColor)
    except SweetHighlightError as e:
      echo errPrefix() & " " & e.msg
      return 1
    if writeOut:
      let outExt =
        if format == hfHtml: ".html"
        elif format == hfJson: ".json"
        else: ".txt"
      let outPath = srcPath.changeFileExt(outExt)
      writeFile(outPath, output)
      echo "Wrote " & outPath
    else:
      stdout.write output
    0

  proc main(): int =
    var positionals: seq[string] = @[]
    var formatArg = "ascii"
    var writeOut = false
    var overwrite = false
    var noColor = false
    var showHelp = false
    var showVersion = false
    var p = initOptParser(commandLineParams())
    for kind, key, val in p.getopt():
      case kind
      of cmdArgument:
        positionals.add(key)
      of cmdLongOption, cmdShortOption:
        case key
        of "help", "h":
          showHelp = true
        of "version":
          showVersion = true
        of "format":
          formatArg = val
        of "o":
          writeOut = true
        of "y":
          overwrite = true
        of "no-color":
          noColor = true
        else:
          echo errPrefix() & " unknown option --" & key
          printHelp()
          return 1
      of cmdEnd:
        discard
    if showVersion:
      echo versionStr
      return 0
    if showHelp:
      printHelp()
      return 0
    if positionals.len == 0:
      printHelp()
      echo "\n" & errPrefix() & " a command is required"
      return 1
    let cmd = positionals[0].toLowerAscii
    if cmd in ["help", "--help", "-h"]:
      printHelp()
      return 0
    if cmd notin ["parse", "ast", "tree", "highlight"]:
      echo errPrefix() & " unknown command: " & cmd
      printHelp()
      return 1
    if positionals.len < 2:
      printHelp()
      echo "\n" & errPrefix() & " " & cmd & " needs a file"
      return 1
    let srcPath = positionals[1]
    case cmd
    of "parse":
      return parseCommand(srcPath)
    of "ast":
      return astCommand(srcPath, writeOut, overwrite)
    of "tree":
      return treeCommand(srcPath)
    else:
      return highlightCommand(srcPath, formatArg, not noColor, writeOut)

  quit(main())
