import std/unittest
import ../src/sweetsyntax
import ../src/sweetsyntax/tokenizer
import ../src/sweetsyntax/languages/ruby as rubyHandlersMod

proc parseRuby(code: string): Node =
  let syntax = getKnownSyntax(KnownSyntax.ruby)
  var p = compile(syntax.spec)
  p.lexer = initLexer(syntax.spec, code)
  rubyHandlersMod.rubyHandlers(p)
  p.curr = p.getToken()
  p.next = p.getToken()
  parseStatement(p)

suite "Ruby parser":
  test "method definition":
    let n = parseRuby("def foo(a, b = 1)\n  a + b\nend")
    check n.kind == nkFunction
    check n[0].kind == nkIdent
    check n[0].name == "foo"

  test "singleton method definition":
    let n = parseRuby("def self.bar(x)\n  x\nend")
    check n.kind == nkFunction
    check n[0].kind == nkDotExpr

  test "class and module":
    check parseRuby("class Foo < Bar\nend").kind == nkStatement
    check parseRuby("module M\nend").kind == nkStatement

  test "if-elsif-else":
    let n = parseRuby("if x > 1\n  puts 'big'\nelsif x < 0\n  puts 'neg'\nelse\n  puts 'mid'\nend")
    check n.kind == nkStatement
    check n[0].name == "if"

  test "if then one-liner":
    let n = parseRuby("if x: puts 'y' end")
    check n.kind == nkStatement
    check n[0].name == "if"

  test "modifier if and unless":
    check parseRuby("puts 'dbg' if debug").kind == nkCall
    let n = parseRuby("return nil unless ok")
    check n.kind == nkStatement
    check n[0].name == "return"

  test "while and until":
    check parseRuby("while i < 10\n  i += 1\nend").kind == nkStatement
    let m = parseRuby("i += 1 while i < 10")
    check m.kind == nkInfix

  test "for-in loop":
    let n = parseRuby("for x in [1, 2, 3]\n  puts x\nend")
    check n.kind == nkStatement
    check n[0].name == "for"

  test "case-when":
    let n = parseRuby("case color\nwhen 'red'\n  puts 1\nelse\n  puts 0\nend")
    check n.kind == nkStatement
    check n[0].name == "case"

  test "begin-rescue-ensure":
    let n = parseRuby("begin\n  risky\nrescue StandardError => e\n  puts e\nensure\n  cleanup\nend")
    check n.kind == nkStatement
    check n[0].name == "begin"

  test "do-end block":
    let n = parseRuby("[1, 2].each do |x|\n  puts x\nend")
    check n.kind == nkStatement
    check n[0].name == "block"
    check n[2].len == 1

  test "brace block":
    let n = parseRuby("[1, 2].each { |x| puts x }")
    check n.kind == nkStatement
    check n[0].name == "block"

  test "block with modifier":
    let n = parseRuby("items.each do |x|\n  puts x\nend if enabled")
    check n.kind == nkStatement
    check n[0].name == "if"

  test "bare method calls":
    let n = parseRuby("attr_accessor :name, :age")
    check n.kind == nkCall
    check n[0].name == "attr_accessor"
    check n[1].name == ":name"
    check parseRuby("require 'json'").kind == nkCall
    check parseRuby("puts result, more").kind == nkCall

  test "hash literals":
    let n = parseRuby("h = { name: 'Ruby', year: 1995 }")
    check n.kind == nkInfix
    check n[2].kind == nkStatement
    check n[2][0].name == "hash"
    check parseRuby("h = { :name => 'Ruby', 'key' => 1 }").kind == nkInfix

  test "instance, class and global variables":
    check parseRuby("@name = :sym").kind == nkInfix
    check parseRuby("@@count += 1").kind == nkInfix
    check parseRuby("$global = 1").kind == nkInfix

  test "ternary and ranges":
    check parseRuby("x = a ? b : c").kind == nkInfix
    let r = parseRuby("r = 1..10")
    check r.kind == nkInfix
    check r[2].kind == nkInfix
    check r[2][0].name == ".."

  test "lambda literal":
    let n = parseRuby("f = ->(x) { x * 2 }")
    check n.kind == nkInfix
    check n[2].kind == nkFunction

  test "keyword arguments":
    let n = parseRuby("configure(verbose: true, level: 2)")
    check n.kind == nkCall
    check n[1].kind == nkColonExpr

  test "string interpolation stays a string token":
    check parseRuby("puts \"hi #{name}\"").kind == nkCall

  test "hash comments":
    let syntax = getKnownSyntax(KnownSyntax.ruby)
    var p = compile(syntax.spec)
    p.lexer = initLexer(syntax.spec, "# comment\nx = 1")
    rubyHandlersMod.rubyHandlers(p)
    p.curr = p.getToken()
    p.next = p.getToken()
    var nodes: seq[Node]
    while p.curr.kind != tkEOF:
      nodes.add(parseStatement(p))
    check nodes.len == 2
    check nodes[0].kind == nkInlineComment
    check nodes[1].kind == nkInfix

  test "safe navigation":
    check parseRuby("user&.name").kind == nkDotExpr

  test "method names ending in ? and !":
    let n = parseRuby("if items.empty?\n  items << 1\nend")
    check n.kind == nkStatement
    check n[0].name == "if"

  test "splat parameters":
    let n = parseRuby("def f(*args)\n  args\nend")
    check n.kind == nkFunction

  test "defined? and alias":
    check parseRuby("puts defined?(foo)").kind == nkCall
    check parseRuby("alias new_name old_name").kind == nkStatement
    check parseRuby("undef old_name, other").kind == nkStatement
