# Package

version       = "0.2.1"
author        = "George Lemon"
description   = "A generic syntax highlighter, tokenizer, parser and AST explorer"
license       = "MIT"
srcDir        = "src"
bin           = @["sweetsyntax"]
binDir        = "bin"

# Dependencies

requires "nim >= 2.0.0"
requires "openparser >= 0.3.4"
requires "kapsis >= 0.4.8"