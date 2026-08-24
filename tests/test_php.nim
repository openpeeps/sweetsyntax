import std/[unittest, os]
import ../src/sweetsyntax
import ../src/sweetsyntax/tokenizer
import ../src/sweetsyntax/languages/php as phpHandlersMod

proc parsePHP(code: string): Node =
  let syntax = getKnownSyntax(KnownSyntax.php)
  var p = compile(syntax.spec)
  p.lexer = initLexer(syntax.spec, code)
  phpHandlersMod.phpHandlers(p)
  p.features.incl(featLabeledStmt)
  p.features.incl(featGenerators)
  p.curr = p.getToken()
  p.next = p.getToken()
  parseStatement(p)

suite "PHP parser":
  test "variable declaration":
    let n = parsePHP("var $x = 5;")
    check n.kind == nkStatement
    check n[0].name == "var"

  test "static declaration":
    let n = parsePHP("static $count = 0;")
    check n.kind == nkStatement
    check n[0].name == "static"

  test "function definition with typed params":
    let n = parsePHP("function foo(int $a, ?string $b = null): ?int { return $a; }")
    check n.kind == nkFunction
    check n[0].name == "foo"
    check n[1].kind == nkIdentDefs

  test "if-elseif-else":
    let n = parsePHP("if ($x) { echo 1; } elseif ($y) { echo 2; } else { echo 3; }")
    check n.kind == nkStatement
    check n[0].name == "if"

  test "while loop":
    let n = parsePHP("while ($i < 10) { $i++; }")
    check n.kind == nkStatement
    check n[0].name == "while"

  test "foreach with key and value":
    let n = parsePHP("foreach ($arr as $k => $v) { echo $v; }")
    check n.kind == nkStatement
    check n[0].name == "foreach"
    check n[2].kind == nkIdent
    check n[2].name == "$k"
    check n[3].name == "$v"

  test "switch statement":
    let n = parsePHP("switch ($x) { case 1: break; default: break; }")
    check n.kind == nkStatement
    check n[0].name == "switch"

  test "class with members":
    let n = parsePHP("class Foo { private int $x = 1; public static function bar($y) {} }")
    check n.kind == nkStatement
    check n[0].name == "class"
    check n[2].kind == nkBlock
    check n[2].len == 2

  test "interface and trait":
    check parsePHP("interface I { public function f(): void; }").kind == nkStatement
    check parsePHP("trait T { use U; }").kind == nkStatement

  test "enum with backed values":
    let n = parsePHP("enum Suit: string { case Hearts = 'H'; case Spades = 'S'; }")
    check n.kind == nkStatement
    check n[0].name == "enum"
    check n[3].kind == nkBlock

  test "try-catch-finally":
    let n = parsePHP("try { foo(); } catch (Exception $e) { bar(); } finally { baz(); }")
    check n.kind == nkStatement
    check n[0].name == "try"

  test "namespace declaration":
    let n = parsePHP("namespace App\\Models;")
    check n.kind == nkStatement
    check n[0].name == "namespace"
    check n[1].name == "App\\Models"

  test "new and isset expressions":
    check parsePHP("$o = new Foo($a);").kind == nkInfix
    let n = parsePHP("if (isset($a, $b)) { }")
    check n.kind == nkStatement

  test "arrow function":
    let n = parsePHP("$f = fn(int $x): int => $x * 2;")
    check n.kind == nkInfix
    check n[2].kind == nkFunction

  test "match expression":
    let n = parsePHP("$r = match($v) { 1, 2 => 'a', default => 'b' };")
    check n.kind == nkInfix
    check n[2].kind == nkStatement

  test "goto and labels":
    check parsePHP("goto end;").kind == nkStatement
    let n = parsePHP("end: echo 'done';")
    check n.kind == nkStatement
    check n[0].name == "label"

  test "declare and global":
    check parsePHP("declare(strict_types=1);").kind == nkStatement
    check parsePHP("global $a, $b;").kind == nkStatement

  test "array literal with keys":
    let n = parsePHP("$m = [1 => 'a', 2 => 'b'];")
    check n.kind == nkInfix
    check n[2].kind == nkBracketExpr
    check n[2][0].kind == nkColonExpr

  test "alternative control flow syntax":
    let n = parsePHP("if ($x): echo 1; else: echo 2; endif;")
    check n.kind == nkStatement
    check n[0].name == "if"
    let w = parsePHP("while ($i < 3): $i++; endwhile;")
    check w.kind == nkStatement
    check w[0].name == "while"

  test "php attributes":
    let n = parsePHP("#[Attr(1)] class Foo { }")
    check n.kind == nkStatement
    check n[0].name == "attr"

  test "hash comments":
    proc parseAll(code: string): seq[Node] =
      let syntax = getKnownSyntax(KnownSyntax.php)
      var p = compile(syntax.spec)
      p.lexer = initLexer(syntax.spec, code)
      phpHandlersMod.phpHandlers(p)
      p.features.incl(featLabeledStmt)
      p.features.incl(featGenerators)
      p.curr = p.getToken()
      p.next = p.getToken()
      while p.curr.kind != tkEOF:
        result.add(parseStatement(p))
    let nodes = parseAll("# this is a comment\n$x = 1;")
    check nodes.len == 2
    check nodes[0].kind == nkInlineComment
    check nodes[1].kind == nkInfix
    let attrs = parseAll("# comment\n#[Attr] class Foo { }")
    check attrs.len == 2
    check attrs[0].kind == nkInlineComment
    check attrs[1].kind == nkStatement
    check attrs[1][0].name == "attr"

  test "bare hash comment with no text":
    proc parseAll(code: string): seq[Node] =
      let syntax = getKnownSyntax(KnownSyntax.php)
      var p = compile(syntax.spec)
      p.lexer = initLexer(syntax.spec, code)
      phpHandlersMod.phpHandlers(p)
      p.features.incl(featLabeledStmt)
      p.features.incl(featGenerators)
      p.curr = p.getToken()
      p.next = p.getToken()
      while p.curr.kind != tkEOF:
        result.add(parseStatement(p))
    let nodes = parseAll("#\n$x = 1;")
    check nodes.len == 2
    check nodes[0].kind == nkInlineComment

  test "scope resolution and qualified names":
    let n = parsePHP("Foo::bar($x);")
    check n.kind == nkCall
    check n[0].kind == nkDotExpr
    check parsePHP("$x = new \\LogicException('m');").kind == nkInfix
    check parsePHP("throw new \\App\\Error('m');").kind == nkStatement
    check parsePHP("static::init();").kind == nkCall

  test "throw as expression":
    let n = parsePHP("$x = $y ?? throw new Exception('m');")
    check n.kind == nkInfix
    check n[2].kind == nkInfix
    check n[2][2].kind == nkStatement
    check n[2][2][0].name == "throw"

  test "exit, die, print and list":
    check parsePHP("exit;").kind == nkCall
    check parsePHP("die('bye');").kind == nkCall
    check parsePHP("print $x;").kind == nkStatement
    check parsePHP("list($a, $b) = $pair;").kind == nkInfix

  test "strict statement termination":
    proc parseAll(code: string): seq[Node] =
      let syntax = getKnownSyntax(KnownSyntax.php)
      var p = compile(syntax.spec)
      p.lexer = initLexer(syntax.spec, code)
      phpHandlersMod.phpHandlers(p)
      p.features.incl(featLabeledStmt)
      p.features.incl(featGenerators)
      p.curr = p.getToken()
      p.next = p.getToken()
      while p.curr.kind != tkEOF:
        result.add(parseStatement(p))

    proc expectError(code: string) =
      var threw = false
      try:
        discard parseAll(code)
      except OpenAstParsingError:
        threw = true
      check threw

    expectError("<?php ;")
    expectError("<?php 123")
    expectError("123")
    check parseAll("<?php 123 ?>").len == 1
    check parseAll("<?php echo 1 ?>").len == 1
    check parseAll("#[Attr] class Foo { }").len == 1
    check parseAll("static $count = 0;").len == 1

  test "multi-block php files":
    let syntax = getKnownSyntax(KnownSyntax.php)
    var p = compile(syntax.spec)
    p.lexer = initLexer(syntax.spec, "<?php $x = 1; ?> <html> <?php $y = 2; ?>")
    phpHandlersMod.phpHandlers(p)
    p.features.incl(featLabeledStmt)
    p.features.incl(featGenerators)
    p.curr = p.getToken()
    p.next = p.getToken()
    var count = 0
    while p.curr.kind != tkEOF:
      discard parseStatement(p)
      inc count
    check count == 2
