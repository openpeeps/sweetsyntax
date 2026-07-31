<p align="center">
  SweetSyntax 🍭 A generic parser and AST explorer<br>for analyzing programming languages 
</p>

<p align="center">
  <code>nimble install sweetsyntax</code>
</p>

<p align="center">
  <a href="https://openpeeps.github.io/sweetsyntax">API reference</a><br>
  <img src="https://github.com/openpeeps/sweetsyntax/workflows/test/badge.svg" alt="Github Actions">  <img src="https://github.com/openpeeps/sweetsyntax/workflows/docs/badge.svg" alt="Github Actions">
</p>

## 😍 Key Features
- Fast, compiled and efficient ([check benchmarks section](#benchmarks))
- Generic parser & AST explorer
- **Embeddable in other languages** via FFI 👉 Lua, JavaScript (N-API), Ruby, Python, PHP
- Easy-to-use API for integration into various applications
- Built-in syntax support for: C, Crystal, D lang, Go, JavaScript, Nim, PHP, Python, Ruby, and Rust
- Zero-copy parsing using MemFiles
- **Context-aware error** reporting while parsing
- Written in Nim

## What's this for?
SweetSyntax is a powerful and flexible generic parser and AST explorer for analyzing programming languages! It is designed to be integrated into other applications, such as code editors, documentation generators, linting tools and other sweet things!

Parse any language by defining its grammar in a YAML specification file: **tokens**, **operators** (prefix, infix, postfix, assignment), **statement keywords**, block delimiters, and **feature flags** (arrow functions, generators, async/await, template literals). The parser uses a **Pratt parsing** approach with a language-agnostic core and per-language statement handlers.

Key capabilities:
- **Lexer**: Generic tokenizer handling identifiers, literals (int, float, hex, octal, binary, bigint, string, regex), comments, and operators
- **Parser**: Pratt (precedence-climbing) parser with configurable operator precedence and associativity
- **AST**: Typed node tree with support for statements, expressions, infix/prefix/postfix operations, function declarations, and more
- **YAML-driven**: Language syntaxes are pure YAML, allowing for custom statement handlers
- **Renderers**: Terminal (ANSI), HTML, line-delimited JSON for editors/higher-level apps, and tree-sitter style code folding

### Renderers
SweetSyntax ships a family of token-level renderers that turn a lexer into a usable output stream. All renderers consume a `SweetLexer` directly, so they work with any YAML syntax spec.

| Renderer | Module | Output |
|----------|--------|--------|
| **Terminal** | `renderers/asciirenderer` | Source text with ANSI color codes |
| **Web** | `renderers/htmlrenderer` | Source text wrapped in `<span class="...">` for CSS styling |
| **JSON** | `renderers/jsonrenderer` | Line-delimited JSON (NDJSON) — one self-contained token object per line |
| **Folds** | `renderers/foldrenderer` | Tree-sitter style fold regions as NDJSON |

#### JSON renderer
The JSON renderer emits each token as its own NDJSON line, designed to be streamed to higher-level applications over websocket/udp so editors and IDEs can build syntax highlighting:

```json
{"kind":"ident","scope":"storage.type","attr":["int"],"line":1,"col":1,"start":0,"stop":3,"value":"int"}
{"kind":"ident","scope":"variable","line":1,"col":5,"start":4,"stop":5,"value":"x"}
{"kind":"int","scope":"constant.numeric.integer","line":1,"col":9,"start":8,"stop":10,"value":"42"}
```

Every token exposes its **kind**, a derived TextMate-style **scope** (e.g. `keyword.control`, `string.quoted.double`, `constant.numeric.integer`, `storage.type`), user-defined **attributes**, 1-based line/column, byte offsets (`start`/`stop`), and the token **value**.

```nim
import sweetsyntax
import sweetsyntax/renderers/jsonrenderer

let syntax = getKnownSyntax(KnownSyntax.c)
var lx = initLexer(syntax.spec, "int x = 42;")
echo highlightJsonLd(lx)   # one JSON token per line
```

#### Code folding
Code folding is fully **optional** and opt-in. `computeFolds` derives tree-sitter style fold regions from the token stream and emits them as their own NDJSON stream, so editors can subscribe to folds independently of token highlighting:

```json
{"kind":"block","start":{"line":1,"col":12,"offset":11},"end":{"line":5,"col":1,"offset":38}}
```

Fold sources (controlled via `FoldMode` and flags):
- **Braces** (`fmBraces`, or `fmAuto` when the file contains `{`): `{...}` blocks spanning multiple lines
- **Indentation** (`fmIndent`): Python/Nim-style blocks, including nested blocks and `else`/`elif` branches
- **Comments**: multi-line `/* ... */` and `/** ... */` doc comments
- **Preprocessor** (`preprocessorFolds = true`): `#if/#ifdef/#ifndef ... #endif` and `#region ... #endregion`

```nim
import sweetsyntax
import sweetsyntax/renderers/foldrenderer

let syntax = getKnownSyntax(KnownSyntax.c)
var lx = initLexer(syntax.spec, "int main() {\n  return 0;\n}")
echo foldsToJsonLd(computeFolds(lx))   # fold regions as NDJSON
```

### Embeddable SweetSyntax
SweetSyntax is written in Nim, and thanks to Nim's versatile compilation model, can be embedded natively into a wide range of host languages. This is WIP via https://github.com/openpeeps/clue toolkit

| Language | Integration |
|----------|------------|
| **Lua** | Load the compiled `.so`/`.dll` via LuaJIT FFI or a lightweight C binding |
| **JavaScript** | Use as a Node.js native addon via N-API |
| **Ruby** | Bundle as a Ruby C extension |
| **Python** | Call through Python's CFFI or `ctypes` |
| **PHP** | Expose as a PHP extension written in C |

The Nim library compiles to a small, self-contained shared object that any FFI-capable language can load, making SweetSyntax a portable parsing engine for your polyglot projects.

## Examples

Parse a C file into an AST:

```nim
import sweetsyntax
import sweetsyntax/languages/c
import pkg/openparser/json

let ast = parseScript("hello.c", cHandlers, {featLabeledStmt})
echo toJson(ast)
```

Parse a PHP file (namespaces, classes, typed signatures, arrow functions, match, and more):

```nim
import sweetsyntax
import sweetsyntax/languages/php
import pkg/openparser/json

let ast = parsePHP("hello.php")
echo toJson(ast)
```

PHP support includes namespaces, `class`/`interface`/`trait`/`enum` bodies with visibility modifiers and typed properties, nullable/union signatures, arrow functions (`fn`), `match`, `goto`/labels, `declare`, function-like keywords (`new`, `isset`, `empty`, `unset`, `list`, `clone`, `exit`/`die`, `print`), `throw` as an expression, PHP 8 attributes (`#[...]`), alternative control-flow syntax (`if: ... endif;`), and multi-block `<?php ... ?>` files.

Highlight source as ANSI or HTML, or stream tokens/folds as NDJSON:

```nim
import sweetsyntax
import sweetsyntax/renderers/[asciirenderer, htmlrenderer, jsonrenderer, foldrenderer]

let syntax = getKnownSyntax(KnownSyntax.js)
var lx = initLexer(syntax.spec, "const x = 42;")

echo highlightAscii(lx)             # terminal output with colors
echo highlightJsonLd(lx)            # one JSON token per line
echo foldsToJsonLd(computeFolds(lx)) # fold regions as NDJSON
```

Interactive renderer examples live in `example_renderers/`.

### Error Reporting
SweetSyntax has built-in support for context-aware reporting. For example:
```
  return a == null || b == null ## NaN : a < b ? -1 : a > b ? 1 : a >= b ? 0 : NaN;
                                ^
Error (2:33) Unexpected prefix token: '#'
```

### Benchmarks
SweetSyntax is built for speed. Below is a **hyperfine** benchmark parsing and validating a full copy of **d3.js** (v7.9.0, ~20k lines, unminified, [from cdnjs.com](https://cdnjs.com/libraries/d3)). The entire pipeline (**lexing**, **parsing**, and **AST generation**) completes in under 120ms on my 🔥 rastafarian Ryzen 5 with 6 cores/12 threads:
```
hyperfine --runs 4 './sweetsyntax_benc_d3'
Benchmark 1: ./sweetsyntax_benc_d3
  Time (mean ± σ):     116.5 ms ±   1.1 ms    [User: 107.5 ms, System: 7.1 ms]
  Range (min … max):   115.9 ms … 118.2 ms    4 runs
```

### ❤ Contributions & Support
- 🐛 Found a bug? [Create a new Issue](https://github.com/openpeeps/sweetsyntax/issues)
- 👋 Wanna help? [Fork it!](https://github.com/openpeeps/sweetsyntax/fork)

|  |  |
|---|---|
| <a href="https://opencode.ai/go?ref=BHMEEK48QX"><img src="https://github.com/openpeeps/pistachio/blob/main/.github/opencode.png" alt="OpenCode"></a> | Switch to **Open-Source LLMs** via OpenCode GO, choosing from a variety of powerful models such as DeepSeek, Qwen, Kimi, GLM-5, MiniMax, MiMo. 🍕 [Use our referral link to get started!](https://opencode.ai/go?ref=BHMEEK48QX)|

### 🎩 License
LGPLv3 license. [Made by Humans from OpenPeeps](https://github.com/openpeeps).<br>
Copyright OpenPeeps & Contributors &mdash; All rights reserved.
