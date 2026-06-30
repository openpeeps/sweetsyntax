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

import std/[tables, strutils]
import ./sweetsyntax/[config, sweetlexer]
import ./sweetsyntax/engine/[ast, parser]

when isMainModule:
  import pkg/openparser/json
  include ./sweetsyntax/languages/js
  discard parseJavaScript("d3.js")