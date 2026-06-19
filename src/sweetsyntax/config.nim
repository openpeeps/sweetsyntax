# A generic syntax highlighter
#
# (c) 2025 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

## This module defines the core data structures and parsing logic for the SweetSyntax library,
## which provides a flexible syntax specification system for parsing and analyzing programming languages based on YAML configuration files.

import std/[tables, options, strutils, strformat, os, sets]
import pkg/openparser/[json, yaml]

type
  SymbolsTable* = Table[string, string]
    ## A table mapping symbol names to their literal representations, e.g. "plus" -> "+"
  IdentsTable* = Table[string, string]
    ## A table mapping identifier names to their literal representations
  
  AstNode* = object
    kind: string
    `from`: string

  Pattern* = object
    match: seq[string]
    produces: seq[AstNode]

  Definition* = ref object
    ## A definition represents a more complex token pattern that may
    ## involve multiple symbols or identifiers.
    name*: string
      ## the name of the definition. Should match
      ## the name used in the `identifiers` table for the relevant token(s)
    patterns*: seq[Pattern]
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


  AssocKind* = enum
    assocLeft = "left"
    assocRight = "right"

  InfixGroup* = ref object
    precedence*: int
    tokens*: seq[string]
    keywords*: seq[string]
    assoc*: AssocKind
    handler*: string       # "dot", "bracket", "call", "ternary", "" (normal)

  PrefixGroup* = ref object
    tokens*: seq[string]
    isKeyword*: bool
    handler*: string

  PostfixGroup* = ref object
    tokens*: seq[string]

  AssignmentDef* = ref object
    tokens*: seq[string]

  TernaryDef* = ref object
    token*: string
    separator*: string
    precedence*: int

  OperatorsSpec* = ref object
    ## Specification of operators, including their tokens, precedence, associativity, and handler types.
    prefix*: seq[PrefixGroup]
      ## Groups of prefix operators, each with its own handler type (e.g. "dot" for member access, "call" for function calls, etc.)
    postfix*: seq[PostfixGroup]
      ## Groups of postfix operators, each with its own handler type
    infix*: seq[InfixGroup]
      ## Groups of infix operators, each with its own precedence, associativity, and handler type
    assignment*: AssignmentDef
      ## Definition of assignment operators, which may have special handling in the parser
    ternary*: TernaryDef
      ## Definition of ternary operators, which may have special handling in the parser

  StatementSpec* = ref object
    ## Specification for a statement type, including its handler function and associated keywords/tokens.
    handler*: string
      ## the name of the handler function to use for this statement type, e.g. "ifHandler", "forHandler", etc.
    keyword*: string            # single keyword (for simple statements)
    keywords*: seq[string]      # multiple keywords (for var/let/const)
    tokens*: seq[string]

  StatementsSpec* = Table[string, StatementSpec]
    ## Mapping of statement types to their specifications, e.g. "if", "for", "while", etc.

  BlocksSpec* = ref object
    ## Specification for block delimiters, which may be used for defining the syntax of code blocks in the language.
    open*: string
      ## the token that opens a block, e.g. "{" for C-like languages
    close*: string
      ## the token that closes a block, e.g. "}" for C-like languages

  FeaturesSpec* = ref object
    ## A set of language features that may require special
    ## handling in the parser, e.g. async/await, generators, etc.
    regexLiterals*: bool
      ## whether the language supports regex literals (e.g. /regex/ in JavaScript)
    asyncAwait*: bool
      ## whether the language supports async/await syntax
    generators*: bool
      ## whether the language supports generator functions (e.g. function* in JavaScript)
    arrowFunctions*: bool
      ## whether the language supports arrow function syntax (e.g. () => {} in JavaScript)
    templateLiterals*: bool
      ## whether the language supports template literals (e.g. `template ${expr}` in JavaScript)
    labeledStatements*: bool
      ## whether the language supports labeled statements (e.g. label: statement in JavaScript)

  LanguageFeature* = enum
    featRegex = "regex_literals"
    featAsync = "async_await"
    featGenerators = "generators"
    featArrowFn = "arrow_functions"
    featTemplateLit = "template_literals"
    featLabeledStmt = "labeled_statements"

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
    operators*: OperatorsSpec
      ## specification of operators, including their tokens, precedence, associativity, and handler types
    statements*: StatementsSpec
      ## mapping of statement types to their specifications, e.g. "if", "for", "while", etc.
    blocks*: BlocksSpec
      ## the syntax for block delimiters, e.g. open: "{", close: "}"
    features*: FeaturesSpec
      ## a set of language features that may require special handling in the parser, e.g. async/await, generators, etc.
    open_tag*: Option[string]   # e.g. "<?php"
    close_tag*: Option[string]  # e.g. "?>"

  KnownSyntax* = enum
    js = "js"
    py = "py"
    nim = "nim"
    c = "c"
    rust = "rs"
    ruby = "rb"
    php = "php"
    go = "go"
    d = "d"

  SweetSyntax* = ref object
    spec*: SweetSpec
      ## the syntax specification containing tokens, identifiers, and other rules

const
  knownSyntaxTable* = {
    "js": staticRead(currentSourcePath().parentDir / "syntaxes" / "js.yaml"),
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

proc parseHook*(p: var YamlParser, v: var PrefixGroup) =
  ## Parse a YAML mapping into PrefixGroup, which may include
  ## tokens, is_keyword flag, and handler type
  if v.isNil: v = PrefixGroup()
  parseYamlMappingPairs do:
    case key
    of "tokens":     p.parseHook(v.tokens)
    of "is_keyword": p.parseHook(v.isKeyword)   # ← this mapping
    of "handler":    p.parseHook(v.handler)
    else: discard  

proc parseHook*(p: var YamlParser, v: var StatementSpec) =
  ## Parse a YAML mapping into StatementSpec, which may include a
  ## handler and associated keywords/tokens for a particular statement type.
  if v.isNil: v = StatementSpec()
  parseYamlMappingPairs do:
    case key
    of "handler":   p.parseHook(v.handler)
    of "keyword":   p.parseHook(v.keyword)
    of "keywords":  p.parseHook(v.keywords)
    of "tokens":    p.parseHook(v.tokens)
    else: discard

proc newSyntax*(specPath: string): SweetSyntax =
  ## Initialize a new Syntax for the given YAML specification file path
  result = SweetSyntax(spec: parseYAML(readFile(specPath), SweetSpec))

proc getKnownSyntax*(knownSyntax: KnownSyntax): SweetSyntax =
  ## Get a predefined syntax by name, e.g. getKnownSyntax(js) returns the JavaScript syntax
  result = SweetSyntax(spec: parseYAML(knownSyntaxTable[$knownSyntax], SweetSpec))
  # echo toJson(result)