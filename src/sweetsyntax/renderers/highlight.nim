# A powerful generic parser and AST explorer for analyzing
# programming languages!
#
# (c) 2026 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

## Unified lexer-only highlighting for every supported language.
##
## `highlight` / `highlightFile` tokenize with the language's YAML spec
## and render to ascii, html or json without touching the Pratt parser,
## so invalid or incomplete code still highlights. For validation and
## ASTs use `parseScript` with the language handlers instead.

import std/[os, strutils, tables]
import ../[config, sweetlexer]
import ./[asciirenderer, htmlrenderer, jsonrenderer]

type
  HighlightFormat* = enum
    hfAscii   ## Terminal output with ANSI colors (whitespace preserved)
    hfHtml    ## HTML spans with token classes (whitespace preserved)
    hfJson    ## Line-delimited JSON, one token object per line

  SweetHighlightError* = object of CatchableError
    ## Raised for unknown file extensions or unreadable files.

const extToSyntax = {
  "js": KnownSyntax.js, "jsx": KnownSyntax.js, "mjs": KnownSyntax.js,
  "cjs": KnownSyntax.js,
  "ts": KnownSyntax.ts, "tsx": KnownSyntax.ts, "mts": KnownSyntax.ts,
  "cts": KnownSyntax.ts, "dts": KnownSyntax.ts,
  "py": KnownSyntax.py, "pyw": KnownSyntax.py,
  "nim": KnownSyntax.nim, "nims": KnownSyntax.nim,
  "c": KnownSyntax.c, "h": KnownSyntax.c,
  "c99": KnownSyntax.c, "c11": KnownSyntax.c,
  "c17": KnownSyntax.c, "c23": KnownSyntax.c,
  "rs": KnownSyntax.rust,
  "rb": KnownSyntax.ruby, "ruby": KnownSyntax.ruby,
  "rake": KnownSyntax.ruby, "gemspec": KnownSyntax.ruby,
  "php": KnownSyntax.php, "phtml": KnownSyntax.php,
  "php3": KnownSyntax.php, "php4": KnownSyntax.php,
  "php5": KnownSyntax.php, "phps": KnownSyntax.php,
  "go": KnownSyntax.go,
  "d": KnownSyntax.d, "di": KnownSyntax.d,
  "cr": KnownSyntax.crystal,
  "css": KnownSyntax.css,
  "md": KnownSyntax.md, "markdown": KnownSyntax.md,
  "mdown": KnownSyntax.md, "mkd": KnownSyntax.md,
  "yaml": KnownSyntax.yaml, "yml": KnownSyntax.yaml,
  "json": KnownSyntax.json,
  "toml": KnownSyntax.toml,
  "csv": KnownSyntax.csv, "tsv": KnownSyntax.csv,
  "html": KnownSyntax.html, "htm": KnownSyntax.html, "xhtml": KnownSyntax.html,
  "xml": KnownSyntax.xml, "xsd": KnownSyntax.xml, "xsl": KnownSyntax.xml,
  "xslt": KnownSyntax.xml, "svg": KnownSyntax.xml, "plist": KnownSyntax.xml,
  "pom": KnownSyntax.xml,
  "sh": KnownSyntax.shell, "bash": KnownSyntax.shell,
  "zsh": KnownSyntax.shell, "ksh": KnownSyntax.shell, "ash": KnownSyntax.shell,
  "ini": KnownSyntax.ini, "cfg": KnownSyntax.ini, "conf": KnownSyntax.ini,
  "properties": KnownSyntax.ini,
  "mak": KnownSyntax.make, "mk": KnownSyntax.make, "make": KnownSyntax.make,
  "cmake": KnownSyntax.cmake,
  "dockerfile": KnownSyntax.docker,
  "nginx": KnownSyntax.nginx,
  "service": KnownSyntax.systemd, "socket": KnownSyntax.systemd,
  "timer": KnownSyntax.systemd, "target": KnownSyntax.systemd,
  "mount": KnownSyntax.systemd, "path": KnownSyntax.systemd,
  "slice": KnownSyntax.systemd, "scope": KnownSyntax.systemd,
  "device": KnownSyntax.systemd, "automount": KnownSyntax.systemd,
  "swap": KnownSyntax.systemd,
  "j2": KnownSyntax.jinja2, "jinja": KnownSyntax.jinja2,
  "jinja2": KnownSyntax.jinja2, "twig": KnownSyntax.jinja2,
  "hbs": KnownSyntax.handlebars, "handlebars": KnownSyntax.handlebars,
  "mustache": KnownSyntax.handlebars,
  "liquid": KnownSyntax.liquid,
  "ejs": KnownSyntax.ejs,
}.toTable

const
  filenameToSyntax = {
    "dockerfile": KnownSyntax.docker,
    "containerfile": KnownSyntax.docker,
    "makefile": KnownSyntax.make,
    "gnumakefile": KnownSyntax.make,
    "cmakelists.txt": KnownSyntax.cmake,
    ".env": KnownSyntax.ini,
    ".env.local": KnownSyntax.ini,
    ".env.production": KnownSyntax.ini,
  }.toTable

proc syntaxForFilename*(path: string): KnownSyntax =
  ## Resolve a bare filename (no useful extension) to its `KnownSyntax`.
  ## Returns false via `hasFilenameSyntax` when the name is not special.
  let name = extractFilename(path).toLowerAscii
  if filenameToSyntax.hasKey(name):
    return filenameToSyntax[name]
  raise newException(SweetHighlightError,
    "No syntax for filename: " & name)

proc syntaxForExt*(ext: string): KnownSyntax =
  ## Resolve a file extension (with or without leading dot, any case)
  ## to its `KnownSyntax`. Raises `SweetHighlightError` when unknown.
  let key = ext.strip(chars = {'.'}).toLowerAscii()
  if extToSyntax.hasKey(key):
    return extToSyntax[key]
  raise newException(SweetHighlightError,
    "Unsupported file extension: ." & key)

proc highlight*(lang: KnownSyntax, code: string,
                format: HighlightFormat = hfHtml,
                useColor = true, enableFilters = true,
                includeValue = true): string =
  ## Highlight `code` written in language `lang` to `format`.
  ## Lexer-only: no parsing or validation is performed.
  let syntax = getKnownSyntax(lang)
  var lx = initLexer(syntax.spec, code, enableFilters)
  case format
  of hfAscii:
    result = highlightAscii(lx, useColor)
  of hfHtml:
    result = highlightHtml(lx)
  of hfJson:
    result = highlightJsonLd(lx, includeValue)

proc highlightFile*(path: string,
                    format: HighlightFormat = hfHtml,
                    useColor = true, enableFilters = true,
                    includeValue = true): string =
  ## Highlight the file at `path`, resolving the language from its
  ## extension, or from a well-known bare filename (`Dockerfile`,
  ## `Makefile`, `CMakeLists.txt`, `.env`) when there is no usable
  ## extension. Raises `SweetHighlightError` when neither resolves.
  let name = extractFilename(path)
  var ext = name.splitFile.ext
  var lang: KnownSyntax
  if ext.len > 1 and extToSyntax.hasKey(ext.strip(chars = {'.'}).toLowerAscii):
    lang = syntaxForExt(ext)
  else:
    lang = syntaxForFilename(name)   # raises when unknown
  let code =
    try:
      readFile(path)
    except IOError as e:
      raise newException(SweetHighlightError,
        "Cannot read file '" & path & "': " & e.msg)
  highlight(lang, code, format, useColor, enableFilters, includeValue)
