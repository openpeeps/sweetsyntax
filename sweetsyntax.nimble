# Package

version       = "0.1.0"
author        = "George Lemon"
description   = "A generic syntax highlighter, tokenizer, parser and AST explorer"
license       = "MIT"
srcDir        = "src"
bin           = @["sweetsyntax"]
binDir        = "bin"

# Dependencies

requires "nim >= 2.0.0"
requires "openparser"