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

import ./sweetsyntax/[config, sweetlexer]
import ./sweetsyntax/engine/[ast, parser]

when isMainModule:
  import std/[tables, os, strutils]
  import pkg/openparser/json
  import pkg/kapsis
  import pkg/kapsis/[runtime, interactive/prompts]
  import ./sweetsyntax/languages/[js, nim]

  proc getLanguageHandlers(ext: string): (ParsingCallback, set[LanguageFeature]) =
    ## Resolve language handlers and features by file extension.
    case ext
    of "js", "jsx", "ts", "tsx":
      (js.jsHandlers, {featAsync, featArrowFn, featGenerators,
                        featLabeledStmt, featTemplateLit})
    of "nim", "nims":
      (nim.nimHandlers, {})
    else:
      (nil, {})

  proc parseCommand(v: Values) =
    let srcPath = $(v.get("script").getPath)
    let ext = srcPath.splitFile.ext[1..^1].toLowerAscii
    let (handler, features) = getLanguageHandlers(ext)
    if handler == nil:
      echo "Unsupported file extension: ." & ext
      quit 1
    try:
      discard parseScript(srcPath, handler, features)
    except OpenAstParsingError as e:
      echo e.msg
      quit 1

  proc astCommand(v: Values) =
    # kapsis command handler for generating the AST of a script file
    let srcPath = absolutePath($(v.get("script").getPath))
    let splitFileTuple = srcPath.splitFile()
    let ext = splitFileTuple.ext[1..^1].toLowerAscii
    let (handler, features) = getLanguageHandlers(ext)
    if handler == nil:
      echo "Unsupported file extension: ." & ext
      quit 1
    try:
      let astProgram = parseScript(srcPath, handler, features)
      if v.has("-o"):
        let outputPath = srcPath.changeFileExt("json")
        if fileExists(outputPath):
          if not v.has("-y") and promptConfirm("Confirm overwrite of the existing JSON file (" & extractFilename(outputPath) & ")?") == false:
            quit 0
        writeFile(outputPath, toJson(astProgram))
      else:
        echo toJson(astProgram)
    except OpenAstParsingError as e:
      echo e.msg
      quit 1    

  initKapsis do:
    commands:
      parse path(script):
        ## Parse a script by extension
      ast path(script), ?bool("-o"), ?bool("-y"):
        ## Generate AST of a script by extension
