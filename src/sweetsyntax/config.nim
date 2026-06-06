# A generic syntax highlighter
#
# (c) 2025 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

import std/[tables, options, strutils, strformat, os]
import pkg/openparser/[json, yaml]

type
  SymbolsTable* = Table[string, string]
    ## A table mapping symbol names to their literal representations, e.g. "plus" -> "+"
  IdentsTable* = Table[string, string]
    ## A table mapping identifier names to their literal representations
  
  Definition* = ref object
    ## A definition represents a more complex token pattern that may
    ## involve multiple symbols or identifiers.
    name*: string
      ## the name of the definition. Should match
      ## the name used in the `identifiers` table for the relevant token(s)
    patterns*: seq[seq[string]]
      ## a list of patterns, where each pattern is a sequence of
      ## symbol/identifier names. For example: `[["string"], ["from", "string"]]`

  Definitions* = seq[Definition]
  
  SweetFilter* = ref object
    ## A filter defines a regex pattern to match tokens in the input,
    ## along with metadata for how to style them.
    name*: string
    pattern*: string
    group*: int
    attr*: string

  SweetSpec* = ref object
    name*: string
      ## the name of the syntax specification, e.g. "JavaScript"
    extension*: seq[string]
      ## file extensions associated with this syntax, e.g. [".js", ".jsx"]
    inline_comment*: Option[string]
      ## the syntax for inline comments, e.g. "//"
    block_comment*: array[2, string]
      ## the syntax for block comments, e.g. ["/*", "*/"]
    symbols*: SymbolsTable
      ## mapping of symbol names to their literal representations, e.g. "plus" -> "+"
    identifiers*: IdentsTable
      ## mapping of identifier names to their literal representations, e.g. "let" -> "let"
    filters*: seq[SweetFilter]
      ## list of filters that define regex patterns for token matching
    definitions*: Definitions
      ## mapping of definition names to their details, used for more complex token patterns

  KnownSyntax* = enum
    js = "javascript"
    py = "python"
    nim = "nim"
    c = "c"
    rust = "rust"
    ruby = "ruby"
    php = "php"
    go = "go"
    d = "d"

  SweetSyntax* = ref object
    spec*: SweetSpec
      ## the syntax specification containing tokens, identifiers, and other rules

const
  knownSyntaxTable* = {
    "javascript": staticRead(currentSourcePath().parentDir / "syntaxes" / "javascript.yaml"),
    "python": staticRead(currentSourcePath().parentDir / "syntaxes" / "python.yaml"),
    "nim": staticRead(currentSourcePath().parentDir / "syntaxes" / "nim.yaml"),
    "c": staticRead(currentSourcePath().parentDir / "syntaxes" / "c.yaml"),
    "rust": staticRead(currentSourcePath().parentDir / "syntaxes" / "rust.yaml"),
    "ruby": staticRead(currentSourcePath().parentDir / "syntaxes" / "ruby.yaml"),
    "php": staticRead(currentSourcePath().parentDir / "syntaxes" / "php.yaml"),
    "go": staticRead(currentSourcePath().parentDir / "syntaxes" / "go.yaml"),
    "d": staticRead(currentSourcePath().parentDir / "syntaxes" / "d.yaml")
  }.toTable

proc parseHook*(p: var YamlParser, v: var SymbolsTable) =
  ## Parse a YAML mapping into SymbolsTable (Table[string, string])
  v = initTable[string, string]()
  parseYamlMappingPairs do:
    var item: string
    p.parseHook(item)
    # we are swapping key and value here because in the YAML, we want the symbol name
    # to be the key for readability, but in the table we want the literal symbol to be
    # the value for easy lookup
    v[item] = key

proc parseHook*(p: var YamlParser, v: var Definitions) =
  ## Parse a YAML sequence into Definitions
  v = @[]
  case p.curr.kind
  of ytkLB:
    p.advance() # '['
    while p.curr.kind != ytkRB:
      if p.curr.kind == ytkEOF:
        p.error("Unexpected EOF in definitions array")
      var def: Definition
      p.parseHook(def)
      v.add(def)
      if p.curr.kind == ytkComma: p.advance()
    p.advance() # ']'
  of ytkDash:
    let seqIndent = p.curr.indent
    while p.curr.kind == ytkDash and p.curr.indent == seqIndent:
      let dashLine = p.curr.line
      p.advance() # consume '-'
      var def: Definition
      if p.curr.kind != ytkEOF and
         (p.curr.line == dashLine or p.curr.indent > seqIndent):
        p.parseHook(def)
      v.add(def)
  else:
    p.error("Expected sequence for `definitions`")

proc parseHook*(p: var YamlParser, v: var SweetFilter) =
  ## Parse one YAML filter object:
  ## - name: ...
  ##   pattern: ...
  ##   group: ...
  ##   attr: ...
  if v.isNil:
    v = SweetFilter()
  parseYamlMappingPairs do:
    case key
    of "name": p.parseHook(v.name)
    of "pattern": p.parseHook(v.pattern)
    of "group": p.parseHook(v.group)
    of "attr": p.parseHook(v.attr)
    else:
      p.error(&"Unknown filter property: {key}")

proc newSyntax*(specPath: string): SweetSyntax =
  ## Initialize a new Syntax for the given YAML specification file path
  result = SweetSyntax(spec: parseYAML(readFile(specPath), SweetSpec))

proc getKnownSyntax*(knownSyntax: KnownSyntax): SweetSyntax =
  ## Get a predefined syntax by name, e.g. getKnownSyntax(js) returns the JavaScript syntax
  result = SweetSyntax(spec: parseYAML(knownSyntaxTable[$knownSyntax], SweetSpec))
  # echo toJson(result)