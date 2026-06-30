<p align="center">
  <img src="https://raw.githubusercontent.com/openpeeps/sweetsyntax/main/.github/sweetsyntax.png" alt="SweetSyntax - Generic parser, AST explorer and analyzer" width="120px" height="120px"><br>
  A generic parser, AST explorer and analyzer
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

### Embeddable SweetSyntax
SweetSyntax is written in Nim, and thanks to Nim's versatile compilation model, can be embedded natively into a wide range of host languages

| Language | Integration |
|----------|------------|
| **Lua** | Load the compiled `.so`/`.dll` via LuaJIT FFI or a lightweight C binding |
| **JavaScript** | Use as a Node.js native addon via N-API |
| **Ruby** | Bundle as a Ruby C extension |
| **Python** | Call through Python's CFFI or `ctypes` |
| **PHP** | Expose as a PHP extension written in C |

The Nim library compiles to a small, self-contained shared object that any FFI-capable language can load, making SweetSyntax a portable parsing engine for your polyglot projects.

## Examples

### Parsing JavaScript

```nim
import sweetsyntax

# Parse a file — the library detects the language from the extension
let program = parseJavaScript("app.js")
echo toJson(program)
```

### Parsing with custom features

```nim
let program = parseScript("module.ts", jsHandlers,
  features = {featAsync, featArrowFn, featGenerators,
              featLabeledStmt, featTemplateLit})
```

### Parsing with custom language handlers

```nim
proc myHandlers(p: var GenericParser) =
  stmtHandler p, "myKeyword":
    walk p
    result = Node(kind: nkStatement,
      children: @[Node(kind: nkIdent, name: "myKeyword"), parseExpression(p)])

let program = parseScript("file.ext", myHandlers,
  features = {featAsync, featArrowFn})
```

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
| <a href="https://opencode.ai/go?ref=BHMEEK48QX"><img src="https://github.com/openpeeps/pistachio/blob/main/.github/opencode.png" alt="OpenCode"></a> | Switch to **Open-Source LLM models** via OpenCode AI, choosing from a variety of powerful models such as DeepSeek, Qwen, Kimi, GLM-5, MiniMax, MiMo. 🍕 [Use our referral link to get started!](https://opencode.ai/go?ref=BHMEEK48QX)|

### 🎩 License
Original logo made by [Vedran Klemens](https://www.behance.net/klemens) via Magnific.

LGPLv3 license. [Made by Humans from OpenPeeps](https://github.com/openpeeps).<br>
Copyright OpenPeeps & Contributors &mdash; All rights reserved.
