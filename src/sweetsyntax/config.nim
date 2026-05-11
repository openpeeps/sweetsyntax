# A generic syntax highlighter
#
# (c) 2025 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

import std/[tables, options, strutils, strformat]
import pkg/openparser/[json, yaml]

type
  SymbolsTable* = Table[string, string]
  IdentsTable* = Table[string, string]
  
  # Definition* = ref object
  #   `type`: string
  #   sample: seq[string]

  # Definitions* = ref object
  #   prefix*: OrderedTableRef[string, Definition]
  
  SweetFilter* = ref object
    name*: string
    pattern*: string
    group*: int
    attr*: string

  SweetSpec* = ref object
    name*: string
      ## the name of the syntax specification, e.g. "JavaScript"
    extension*: seq[string]
      ## file extensions associated with this syntax, e.g. [".js", ".jsx"]
    symbols*: SymbolsTable
      ## mapping of symbol names to their literal representations, e.g. "plus" -> "+"
    identifiers*: IdentsTable
      ## mapping of identifier names to their literal representations, e.g. "let" -> "let"
    filters*: seq[SweetFilter]

  SweetSyntax* = ref object
    spec*: SweetSpec
      ## the syntax specification containing tokens, identifiers, and other rules

proc parseHook*(parser: var YamlParser, v: var SymbolsTable) =
  ## Parse a YAML mapping into SymbolsTable (Table[string, string])
  v = initTable[string, string]()
  parseYamlMappingPairs do:
    var item: string
    parser.parseHook(item)
    v[key] = item

proc parseHook*(parser: var YamlParser, v: var SweetFilter) =
  ## Parse one YAML filter object:
  ## - name: ...
  ##   pattern: ...
  ##   group: ...
  ##   attr: ...
  if v.isNil:
    v = SweetFilter()
  parseYamlMappingPairs do:
    case key
    of "name": parser.parseHook(v.name)
    of "pattern": parser.parseHook(v.pattern)
    of "group": parser.parseHook(v.group)
    of "attr": parser.parseHook(v.attr)
    else:
      parser.error(&"Unknown filter property: {key}")

proc newSyntax*(specPath: string): SweetSyntax =
  ## Initialize a new Syntax for the given YAML specification file path
  result = SweetSyntax(spec: parseYAML(readFile(specPath), SweetSpec))