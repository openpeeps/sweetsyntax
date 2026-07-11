import std/[macros, options, strutils, tables, sets]
import pkg/openparser/yaml
import ../../config

macro buildPrepared*(yamlPath: static string): untyped =
  let spec = parseYAML(staticRead(yamlPath), SweetSpec)

  # Helper: escape a string for use as a Nim string literal
  func q(s: string): string =
    result = "\""
    for c in s:
      case c
      of '\\': result.add "\\\\"
      of '\"': result.add "\\\""
      of '\n': result.add "\\n"
      of '\r': result.add "\\r"
      of '\t': result.add "\\t"
      else: result.add c
    result.add "\""

  let body = newStmtList()
  body.add parseStmt("var t = SweetLexerInit()")

  # symbols — emit as array of tuples then toTable
  var symbolPairs: seq[string]
  for raw, name in spec.symbols:
    symbolPairs.add "(" & q(raw) & ", " & q(name) & ")"
  if symbolPairs.len > 0:
    body.add parseStmt("t.symbols = [" & symbolPairs.join(", ") & "].toTable()")

  # identifiers
  var identPairs: seq[string]
  for raw, name in spec.identifiers:
    identPairs.add "(" & q(raw) & ", " & q(name) & ")"
  if identPairs.len > 0:
    body.add parseStmt("t.identifiers = [" & identPairs.join(", ") & "].toTable()")

  # inline comment
  if spec.inline_comment.isSome:
    body.add parseStmt("t.inlineComment = some(" & q(spec.inline_comment.get) & ")")

  # block comment
  body.add parseStmt("t.blockComment = [" & q(spec.blockComment[0]) & ", " & q(spec.blockComment[1]) & "]")

  # open/close tags
  if spec.open_tag.isSome:
    body.add parseStmt("t.openTag = some(" & q(spec.open_tag.get) & ")")
  if spec.close_tag.isSome:
    body.add parseStmt("t.closeTag = some(" & q(spec.close_tag.get) & ")")

  # filters (not prebuilt — SweetFilter is ref object, runtime-only)

  # features
  var feats: seq[string]
  if spec.features.regexLiterals: feats.add "featRegex"
  if spec.features.asyncAwait: feats.add "featAsync"
  if spec.features.generators: feats.add "featGenerators"
  if spec.features.arrowFunctions: feats.add "featArrowFn"
  if spec.features.templateLiterals: feats.add "featTemplateLit"
  if spec.features.labeledStatements: feats.add "featLabeledStmt"
  if spec.features.commandSyntax: feats.add "featCommandSyntax"
  if feats.len > 0:
    body.add parseStmt("t.features = {" & feats.join(", ") & "}")

  # block open/close
  if spec.blocks != nil:
    body.add parseStmt("t.blockOpen = " & q(spec.blocks.open))
    body.add parseStmt("t.blockClose = " & q(spec.blocks.close))

  # allOps — array literal
  var ops: seq[string]
  for raw, _ in spec.symbols: ops.add q(raw)
  if spec.operators != nil:
    for g in spec.operators.prefix:
      for tok in g.tokens: ops.add q(tok)
    for g in spec.operators.infix:
      for tok in g.tokens: ops.add q(tok)
      for kw in g.keywords: ops.add q(kw)
    if spec.operators.assignment != nil:
      for tok in spec.operators.assignment.tokens: ops.add q(tok)
    if spec.operators.ternary != nil:
      ops.add q(spec.operators.ternary.token)
  if ops.len > 0:
    body.add parseStmt("t.allOps = @[" & ops.join(", ") & "]")

  # infixTable — array of tuples then toTable
  var infixPairs: seq[string]
  if spec.operators != nil:
    for g in spec.operators.infix:
      let assoc = if g.assoc == assocRight: "rightAssoc" else: "leftAssoc"
      let entry = "InfixEntry(precedence: " & $g.precedence & ", assoc: " & assoc & ", special: " & q(g.handler) & ")"
      for tok in g.tokens:
        infixPairs.add "(" & q(tok) & ", " & entry & ")"
      for kw in g.keywords:
        infixPairs.add "(" & q(kw) & ", " & entry & ")"
    if spec.operators.assignment != nil:
      for tok in spec.operators.assignment.tokens:
        infixPairs.add "(" & q(tok) & ", InfixEntry(precedence: 0, assoc: rightAssoc, special: \"\"))"
    if spec.operators.ternary != nil:
      infixPairs.add "(" & q(spec.operators.ternary.token) & ", InfixEntry(precedence: " & $spec.operators.ternary.precedence & ", assoc: rightAssoc, special: \"ternary\"))"
  if infixPairs.len > 0:
    body.add parseStmt("t.infixTable = [" & infixPairs.join(", ") & "].toTable()")

  # assignOps
  var assignTokens: seq[string]
  if spec.operators != nil and spec.operators.assignment != nil:
    for tok in spec.operators.assignment.tokens:
      assignTokens.add "(" & q(tok) & ", true)"
  if assignTokens.len > 0:
    body.add parseStmt("t.assignOps = [" & assignTokens.join(", ") & "].toTable()")

  # prefixOps — HashSet from array
  var prefixTokens: seq[string]
  if spec.operators != nil:
    for g in spec.operators.prefix:
      if not g.isKeyword:
        for tok in g.tokens: prefixTokens.add q(tok)
  if prefixTokens.len > 0:
    body.add parseStmt("t.prefixOps = [" & prefixTokens.join(", ") & "].toHashSet()")

  # keywordPrefixOps
  var kwPrefixTokens: seq[string]
  if spec.operators != nil:
    for g in spec.operators.prefix:
      if g.isKeyword:
        for tok in g.tokens: kwPrefixTokens.add q(tok)
  if kwPrefixTokens.len > 0:
    body.add parseStmt("t.keywordPrefixOps = [" & kwPrefixTokens.join(", ") & "].toHashSet()")

  # postfixOps
  var postfixTokens: seq[string]
  if spec.operators != nil:
    for g in spec.operators.postfix:
      for tok in g.tokens: postfixTokens.add q(tok)
  if postfixTokens.len > 0:
    body.add parseStmt("t.postfixOps = [" & postfixTokens.join(", ") & "].toHashSet()")

  # stmtKeywords — array of tuples then toTable
  var stmtPairs: seq[string]
  for name, stmt in spec.statements:
    if stmt.handler.len == 0: continue
    if stmt.keyword.len > 0:
      stmtPairs.add "(" & q(stmt.keyword) & ", " & q(stmt.handler) & ")"
    for kw in stmt.keywords:
      stmtPairs.add "(" & q(kw) & ", " & q(stmt.handler) & ")"
  if stmtPairs.len > 0:
    body.add parseStmt("t.stmtKeywords = [" & stmtPairs.join(", ") & "].toTable()")

  # expectRegex
  if spec.statements.hasKey("expect_regex_after"):
    let era = spec.statements["expect_regex_after"]
    var tokensLit: seq[string]
    for tk in era.tokens: tokensLit.add q(tk)
    body.add parseStmt("t.expectRegexTokens = @[" & tokensLit.join(", ") & "]")
    var keywordsLit: seq[string]
    for kw in era.keywords: keywordsLit.add q(kw)
    body.add parseStmt("t.expectRegexKeywords = @[" & keywordsLit.join(", ") & "]")

  body.add parseStmt("t")
  result = newBlockStmt(body)
  
  # echo result.repr # for debug only
