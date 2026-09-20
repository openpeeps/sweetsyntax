import std/[unittest, os]
import ../src/sweetsyntax
import ../src/sweetsyntax/tokenizer
import ../src/sweetsyntax/languages/c as cHandlersMod

const cFixtureDir = currentSourcePath().parentDir / "data" / "c"

proc parseC(code: string): Node =
  let syntax = getKnownSyntax(KnownSyntax.c)
  var p = compile(syntax.spec)
  p.lexer = initLexer(syntax.spec, code)
  cHandlersMod.cHandlers(p)
  p.features.incl(featLabeledStmt)
  p.features.incl(featAdjacentConcat)
  p.curr = p.getToken()
  p.next = p.getToken()
  parseStatement(p)

proc parseCStmts(code: string): seq[Node] =
  let syntax = getKnownSyntax(KnownSyntax.c)
  var p = compile(syntax.spec)
  p.lexer = initLexer(syntax.spec, code)
  cHandlersMod.cHandlers(p)
  p.features.incl(featLabeledStmt)
  p.features.incl(featAdjacentConcat)
  p.curr = p.getToken()
  p.next = p.getToken()
  while p.curr.kind != tkEOF:
    result.add(parseStatement(p))

proc parseCFile(path: string): seq[Node] =
  let syntax = getKnownSyntax(KnownSyntax.c)
  var p = compile(syntax.spec)
  p.lexer = initLexerFromFile(syntax.spec, path)
  cHandlersMod.cHandlers(p)
  p.features.incl(featLabeledStmt)
  p.features.incl(featAdjacentConcat)
  p.curr = p.getToken()
  p.next = p.getToken()
  while p.curr.kind != tkEOF:
    result.add(parseStatement(p))

proc countNodes(n: Node): int =
  result = 1
  if n != nil:
    case n.kind
    of nkEmpty, nkNil, nkLitBool, nkLitInt, nkLitFloat, nkLitString,
       nkLitBigInt, nkIdent:
      discard
    else:
      for c in n.children:
        result += countNodes(c)

suite "C parser":
  test "variable declaration":
    let n = parseC("int x = 42;")
    check n.kind == nkStatement

  test "function definition":
    let n = parseC("int main() { return 0; }")
    check n.kind == nkFunction

  test "if-else statement":
    let n = parseC("if (x) { return 1; } else { return 2; }")
    check n.kind == nkStatement

  test "while loop":
    let n = parseC("while (i < 10) { i = i + 1; }")
    check n.kind == nkStatement

  test "for loop":
    let n = parseC("for (int i = 0; i < 10; i++) { }")
    check n.kind == nkStatement

  test "pointer declaration":
    let n = parseC("int *p = NULL;")
    check n.kind == nkStatement

  test "struct declaration":
    let n = parseC("struct point { int x; int y; };")
    check n.kind == nkStatement

  test "enum declaration":
    let n = parseC("enum color { RED, GREEN, BLUE };")
    check n.kind == nkStatement

  test "preprocessor directive":
    let n = parseC("#include <stdio.h>\nint x = 1;")
    check n.kind == nkStatement
    check n[0].name == "directive"
    check n[1].name == "include"

  test "adjacent string literals concatenate":
    let n = parseC("const char *s = \"a\" \"b\";")
    check n.kind == nkStatement

  test "cast expression":
    let n = parseC("unsigned u = (unsigned) x;")
    check n.kind == nkStatement

  test "sizeof type and expression":
    check parseC("int n = sizeof(int);").kind == nkStatement
    check parseC("int n = sizeof *p;").kind == nkStatement

suite "C fixtures":
  test "libevent event.c parses":
    let nodes = parseCFile(cFixtureDir / "libevent_event.c")
    check nodes.len >= 1
    var total = 0
    for n in nodes: total += countNodes(n)
    echo "libevent event.c AST nodes: ", total
    check total > 1000

suite "C vars and simple declarations":
  test "bare declaration":
    let n = parseC("int x;")
    check n.kind == nkStatement
    check n[0].name == "decl"
    check n[1].name == "int"
    check n[2].kind == nkIdentDefs
    check n[2][0].name == "x"
    check n[2][1].kind == nkEmpty

  test "declaration with int initializer":
    let n = parseC("int x = 42;")
    check n[2][0].name == "x"
    check n[2][1].kind == nkLitInt
    check n[2][1].valInt == 42

  test "multiple declarators in one statement":
    let n = parseC("int a, b = 2, c;")
    check n.kind == nkStatement
    check n.len == 5
    check n[2][0].name == "a"
    check n[2][1].kind == nkEmpty
    check n[3][0].name == "b"
    check n[3][1].valInt == 2
    check n[4][0].name == "c"

  test "float, double and char declarations":
    check parseC("float f = 1.5;")[2][1].valFloat == 1.5
    check parseC("double d;")[1].name == "double"
    check parseC("char c = 'a';")[2][1].kind == nkLitString
    check parseC("char c = 'a';")[2][1].valStr == "'a'"

  test "hex, octal and plain int literals keep kind":
    check parseC("int x = 0xFF;")[2][1].kind == nkLitInt
    check parseC("int x = 0xFF;")[2][1].valInt == 255
    check parseC("int x = 0755;")[2][1].kind == nkLitInt

  test "string initializer":
    let n = parseC("""char *s = "hi";""")
    check n[2][0].kind == nkPrefix
    check n[2][0][0].name == "*"
    check n[2][1].kind == nkLitString

  test "unknown type name starts a declaration":
    let n = parseC("mytype foo;")
    check n.kind == nkStatement
    check n[0].name == "decl"
    check n[1].name == "mytype"
    check n[2][0].name == "foo"

  test "multi-statement decl block":
    let nodes = parseCStmts("""
      int x = 1;
      float y = 2.5;
      """)
    check nodes.len == 2
    check nodes[0][1].name == "int"
    check nodes[0][2][1].valInt == 1
    check nodes[1][1].name == "float"
    check nodes[1][2][1].valFloat == 2.5

suite "C specifiers, qualifiers and storage":
  test "static const unsigned long":
    let n = parseC("static const unsigned long x = 1;")
    check n[0].name == "decl"
    check n[1].name == "static"
    check n[2].name == "const"
    check n[3].name == "unsigned"
    check n[4].name == "long"
    check n[5][0].name == "x"

  test "volatile, signed and extern":
    check parseC("volatile int v;")[1].name == "volatile"
    check parseC("signed char c;")[1].name == "signed"
    check parseC("extern int e;")[1].name == "extern"

  test "short, long long and unsigned":
    let n = parseC("unsigned u = (unsigned) x;")
    check n[1].name == "unsigned"
    check parseC("long x;")[1].name == "long"
    check parseC("short s;")[1].name == "short"

  test "_Bool and void pointer decl":
    check parseC("_Bool b;")[1].name == "_Bool"
    let n = parseC("void *p;")
    check n[1].name == "void"
    check n[2][0][0].name == "*"

suite "C pointers, arrays and strings":
  test "single pointer":
    let n = parseC("int *p;")
    check n[2][0].kind == nkPrefix
    check n[2][0][0].name == "*"
    check n[2][0][1].name == "p"

  test "double pointer":
    let n = parseC("char **argv;")
    check n[2][0].kind == nkPrefix
    check n[2][0][1].kind == nkPrefix
    check n[2][0][1][1].name == "argv"

  test "array with size":
    let n = parseC("int a[10];")
    check n[2][0].kind == nkBracketExpr
    check n[2][0][0].name == "a"
    check n[2][0][1].valInt == 10

  test "multidimensional array":
    let n = parseC("int m[2][3];")
    check n[2][0].kind == nkBracketExpr
    check n[2][0][0].kind == nkBracketExpr
    check n[2][0][0][1].valInt == 2
    check n[2][0][1].valInt == 3

  test "deref and address-of expressions":
    let d = parseC("*p;")
    check d.kind == nkPrefix
    check d[0].name == "*"
    check d[1].name == "p"
    let a = parseC("&x;")
    check a[0].name == "&"
    check a[1].name == "x"

  test "adjacent strings concatenate":
    let n = parseC("""const char *s = "a" "b";""")
    check n.kind == nkStatement
    check n[3][1].kind == nkLitString
    check n[3][1].valStr == "\"ab\""

suite "C functions":
  test "prototype with named params":
    let n = parseC("int add(int a, int b);")
    check n[0].name == "decl"
    check n[2][0].kind == nkCall
    check n[2][0][0].name == "add"
    check n[2][0][1].kind == nkIdentDefs
    check n[2][0][1].len == 2
    check n[2][0][1][0][1].name == "a"

  test "void param prototype":
    let n = parseC("int f(void);")
    check n[2][0][1][0].kind == nkPrefix
    check n[2][0][1][0][0].name == "void"

  test "variadic prototype":
    let n = parseC("int printf(const char *fmt, ...);")
    check n[2][0][0].name == "printf"
    check n[2][0][1][^1].name == "..."

  test "empty definition":
    let n = parseC("int f() { return 0; }")
    check n.kind == nkFunction
    check n[0].name == "f"
    check n[1].kind == nkIdentDefs
    check n[2].kind == nkBlock
    check n[2][0].kind == nkReturn

  test "definition with params and static":
    let n = parseC("static int g(int x) { return x; }")
    check n.kind == nkFunction
    check n[0].name == "g"
    check n[1][0][1].name == "x"
    check n[2][0].kind == nkReturn

  test "function pointer declarator":
    let n = parseC("int (*fp)(int);")
    check n[2][0].kind == nkCall
    check n[2][0][0].kind == nkPrefix
    check n[2][0][0][0].name == "*"
    check n[2][0][0][1].name == "fp"

  test "fib recursion shape":
    let nodes = parseCStmts("""
      int fib(int n) {
        if (n < 2) return n;
        return fib(n - 1) + fib(n - 2);
      }
      """)
    check nodes.len == 1
    check nodes[0].kind == nkFunction
    check nodes[0][0].name == "fib"
    check nodes[0][2].len == 2
    check nodes[0][2][0][0].name == "if"
    check nodes[0][2][1].kind == nkReturn

suite "C typedefs":
  test "simple typedef":
    let n = parseC("typedef int myint;")
    check n.kind == nkStatement
    check n[0].name == "typedef"
    check n[1].name == "int"
    check n[2][0].name == "myint"

  test "typedef with long and pointer":
    check parseC("typedef unsigned long myu;")[2].name == "long"
    let n = parseC("typedef int *iptr;")
    check n[2][0].kind == nkPrefix
    check n[2][0][1].name == "iptr"

  test "seed typedefs usable as casts":
    let n = parseC("(size_t)x;")
    check n.kind == nkPrefix
    check n[0].name == "cast"
    check n[1].name == "size_t"
    check n[2].name == "x"

  test "custom type name usable in later decl":
    let n = parseC("myu v = 1;")
    check n[0].name == "decl"
    check n[1].name == "myu"

suite "C struct and union":
  test "struct with two fields":
    let n = parseC("struct P { int x; int y; };")
    check n[0].name == "struct"
    check n[1].name == "P"
    check n[2].kind == nkBlock
    check n[2].len == 2
    check n[2][0][2][0].name == "x"

  test "struct trailing declarators":
    let n = parseC("struct S a, *b;")
    check n[1].name == "S"
    check n[3][0].name == "a"
    check n[4][0][0].name == "*"

  test "forward struct declaration":
    let n = parseC("struct Fwd;")
    check n[0].name == "struct"
    check n[1].name == "Fwd"
    check n[2].kind == nkEmpty

  test "nested struct":
    let n = parseC("""
      struct Outer { struct Inner { int a; } in; int b; };
      """)
    check n[1].name == "Outer"
    check n[2][0][0].name == "struct"
    check n[2][0][1].name == "Inner"
    check n[2][1][2][0].name == "b"

  test "union body":
    let n = parseC("union U { int i; float f; };")
    check n[0].name == "union"
    check n[1].name == "U"
    check n[2][0][1].name == "int"
    check n[2][1][1].name == "float"

  test "named bitfield":
    let n = parseC("unsigned a : 1;")
    check n[0].name == "decl"
    check n[2].kind == nkColonExpr
    check n[2][0][0].name == "a"
    check n[2][1].valInt == 1

  test "anonymous bitfield":
    let n = parseC("unsigned : 8;")
    check n[2].kind == nkColonExpr
    check n[2][0][0].kind == nkEmpty
    check n[2][1].valInt == 8

suite "C enums":
  test "enum with explicit value":
    let n = parseC("enum C { RED, GREEN = 5, BLUE };")
    check n[0].name == "enum"
    check n[1].name == "C"
    check n[2].kind == nkBlock
    check n[2][0][0].name == "RED"
    check n[2][1][0].name == "GREEN"
    check n[2][1][1].valInt == 5
    check n[2][2][0].name == "BLUE"

  test "anonymous enum member":
    let n = parseC("enum E { A };")
    check n[1].name == "E"
    check n[2][0][0].name == "A"

suite "C if statements":
  test "if without else":
    let n = parseC("if (x) f();")
    check n.kind == nkStatement
    check n[0].name == "if"
    check n[1].name == "x"
    check n[2].kind == nkCall

  test "if-else with single statements":
    let n = parseC("if (x) return 1; else return 2;")
    check n[1].name == "x"
    check n[2].kind == nkReturn
    check n[3].kind == nkReturn

  test "if-else with blocks":
    let n = parseC("if (x) { return 1; } else { return 2; }")
    check n[2].kind == nkBlock
    check n[3].kind == nkBlock

  test "comparison condition":
    let n = parseC("if (n < 2) return n;")
    check n[1].kind == nkInfix
    check n[1][0].name == "<"
    check n[2].kind == nkReturn

  test "else-if chain":
    let n = parseC("if (a) x(); else if (b) y();")
    check n[0].name == "if"
    check n[1].name == "a"
    check n[2].kind == nkCall
    check n[3].name == "b"
    check n[4].kind == nkCall

  test "nested if in function":
    let nodes = parseCStmts("""
      int f(int x) {
        if (x > 0) {
          return 1;
        } else {
          return 0;
        }
      }
      """)
    check nodes[0][2][0][0].name == "if"
    check nodes[0][2][0][2].kind == nkBlock

suite "C switch, case and default":
  test "switch with case and default":
    let n = parseC("switch(x){ case 1: break; default: break; }")
    check n[0].name == "switch"
    check n[1].name == "x"
    check n[2].kind == nkBlock
    check n[2][0][0].name == "case"
    check n[2][0][1].valInt == 1
    check n[2][0][2].kind == nkBlock
    check n[2][1][0].name == "default"

  test "switch over call with two cases":
    let nodes = parseCStmts("""
      int f(int x) {
        switch (x) {
          case 1: return 10;
          case 2: return 20;
          default: return 0;
        }
      }
      """)
    check nodes[0][2][0][0].name == "switch"
    check nodes[0][2][0][2][0][0].name == "case"
    check nodes[0][2][0][2][2][0].name == "default"

suite "C loops":
  test "while with block":
    let n = parseC("while (i < 10) { i = i + 1; }")
    check n[0].name == "while"
    check n[1].kind == nkInfix
    check n[1][0].name == "<"
    check n[2].kind == nkBlock

  test "while with single statement":
    let n = parseC("while (1) break;")
    check n[1].valInt == 1
    check n[2][0].name == "break"

  test "do-while with block":
    let n = parseC("do { x++; } while (x < 10);")
    check n[0].name == "do-while"
    check n[1].kind == nkBlock
    check n[2].kind == nkInfix

  test "do-while with single statement":
    let n = parseC("do x++; while (x < 3);")
    check n[1].kind == nkPostfix
    check n[2][0].name == "<"

  test "classic for with decl init":
    let n = parseC("for (int i = 0; i < 10; i++) { }")
    check n[0].name == "for"
    check n[1].kind == nkStatement
    check n[1][0].name == "decl"
    check n[2][0].name == "<"
    check n[3].kind == nkPostfix
    check n[4].kind == nkBlock

  test "for with empty slots":
    let n = parseC("for (;;) { }")
    check n[1].kind == nkEmpty
    check n[2].kind == nkEmpty
    check n[3].kind == nkEmpty

  test "for with spaced empty slots":
    let n = parseC("for ( ; ; ) { }")
    check n[1].kind == nkEmpty
    check n[2].kind == nkEmpty
    check n[3].kind == nkEmpty

  test "for with expr init and missing update":
    let n = parseC("for (i = 0; i < 10;) { }")
    check n[1].kind == nkInfix
    check n[1][0].name == "="
    check n[3].kind == nkEmpty

  test "for with comma init":
    let n = parseC("for (i = 0, j = 0; i < n; i++) { }")
    check n[1].kind == nkStatement
    check n[1][0].name == "comma"

  test "loop combo with break and continue":
    let nodes = parseCStmts("""
      void loop(void) {
        for (;;) break;
      }
      """)
    check nodes[0][2][0][0].name == "for"
    check nodes[0][2][0][4][0].name == "break"

suite "C jumps, labels and return":
  test "bare return":
    check parseC("return;").kind == nkReturn

  test "return with value":
    let n = parseC("return 0;")
    check n.kind == nkReturn
    check n[0].valInt == 0

  test "return with comma expression":
    let n = parseC("return a, b;")
    check n.kind == nkReturn
    check n[0].kind == nkStatement
    check n[0][0].name == "comma"

  test "break and continue":
    check parseC("break;")[0].name == "break"
    check parseC("continue;")[0].name == "continue"

  test "goto and label":
    let g = parseC("goto l;")
    check g[0].name == "goto"
    check g[1].name == "l"
    let l = parseC("l: x = 1;")
    check l[0].name == "label"
    check l[1].name == "l"
    check l[2].kind == nkInfix

  test "goto combo":
    let nodes = parseCStmts("""
      goto l;
      l: x = 1;
      """)
    check nodes.len == 2
    check nodes[0][0].name == "goto"
    check nodes[1][0].name == "label"

suite "C expressions and operators":
  test "precedence multiplies before adding":
    let n = parseC("x = a + b * c;")
    check n[0].name == "="
    check n[2][0].name == "+"
    check n[2][2][0].name == "*"

  test "parens override precedence":
    let n = parseC("x = (a + b) * c;")
    check n[2][0].name == "*"
    check n[2][1][0].name == "+"

  test "logical and binds tighter than or":
    let n = parseC("a && b || c;")
    check n.kind == nkInfix
    check n[0].name == "||"
    check n[1][0].name == "&&"

  test "shifts, bitwise and comparisons":
    check parseC("x << 2;")[0].name == "<<"
    check parseC("x >> 2;")[0].name == ">>"
    check parseC("a & b;")[0].name == "&"
    check parseC("a | b;")[0].name == "|"
    check parseC("a == b;")[0].name == "=="
    check parseC("a != b;")[0].name == "!="

  test "compound assignment":
    check parseC("x += 1;")[0].name == "+="
    check parseC("x -= 1;")[0].name == "-="
    check parseC("x *= 2;")[0].name == "*="

  test "prefix operators":
    check parseC("!x;")[0].name == "!"
    check parseC("~x;")[0].name == "~"
    check parseC("-x;")[0].name == "-"
    check parseC("--i;")[0].name == "--"
    check parseC("--i;")[1].name == "i"

  test "postfix increment":
    let n = parseC("i++;")
    check n.kind == nkPostfix
    check n[0].name == "i"
    check n[1].name == "++"

  test "ternary expression":
    let n = parseC("a ? b : c;")
    check n.kind == nkCall
    check n[0].name == "ternary"
    check n[1].name == "a"
    check n[2].name == "b"
    check n[3].name == "c"

  test "ternary binds looser than addition":
    let n = parseC("s = a ? b : c + d;")
    check n[2][0].name == "ternary"
    check n[2][3][0].name == "+"

  test "comma expression statement":
    let n = parseC("x = y, z;")
    check n.kind == nkStatement
    check n[0].name == "comma"

  test "call, subscript, dot and arrow":
    let c = parseC("f(1, 2);")
    check c.kind == nkCall
    check c[0].name == "f"
    check c.len == 3
    check parseC("a[i];").kind == nkBracketExpr
    check parseC("s.x;").kind == nkDotExpr
    let ar = parseC("p->x;")
    check ar.kind == nkInfix
    check ar[0].name == "->"

  test "group stays a group":
    let n = parseC("(a+b)*c;")
    check n.kind == nkInfix
    check n[0].name == "*"
    check n[1][0].name == "+"

  test "unknown name in parens is not a cast":
    let n = parseC("r = (a)-b;")
    check n[2][0].name == "-"
    check n[2][1].name == "a"
    check n[2][2].name == "b"

suite "C casts and sizeof":
  test "simple cast":
    let n = parseC("(int)x;")
    check n.kind == nkPrefix
    check n[0].name == "cast"
    check n[1].name == "int"
    check n[2].name == "x"

  test "cast of float literal":
    let n = parseC("int q = (int)3.5;")
    check n[2][1][0].name == "cast"
    check n[2][1][2].valFloat == 3.5

  test "pointer cast":
    let n = parseC("int w = (int *)0;")
    check n[2][1][0].name == "cast"
    check n[2][1][1].kind == nkPrefix
    check n[2][1][1][0].name == "*"

  test "cast binds tighter than addition":
    let n = parseC("r = (unsigned)x + 1;")
    check n[2][0].name == "+"
    check n[2][1][0].name == "cast"

  test "sizeof bare type":
    let n = parseC("int n = sizeof(int);")
    check n[2][1].kind == nkPrefix
    check n[2][1][0].name == "sizeof"
    check n[2][1][1].name == "int"

  test "sizeof expression forms":
    check parseC("int n = sizeof x;")[2][1][1].name == "x"
    let p = parseC("int n = sizeof *p;")
    check p[2][1][1].kind == nkPrefix
    check p[2][1][1][0].name == "*"

  test "static assert with simple args":
    let n = parseC("""_Static_assert(1, "bad");""")
    check n.kind == nkStatement
    check n[0].name == "_Static_assert"
    check n[1].valInt == 1

suite "C initializers":
  test "array initializer list":
    let n = parseC("int a[] = {1, 2};")
    check n[2][0].kind == nkBracketExpr
    check n[2][0][1].kind == nkEmpty
    check n[2][1].kind == nkBlock

  test "sized array initializer":
    let n = parseC("int arr[3] = {1};")
    check n[2][0][1].valInt == 3
    check n[2][1].kind == nkBlock
    check n[2][1][0].kind == nkLitInt

  test "multi-element init holds comma list":
    let n = parseC("int a[3] = {1, 2, 3};")
    check n[2][1][0].kind == nkStatement
    check n[2][1][0][0].name == "comma"

suite "C preprocessor":
  test "includes":
    check parseC("#include <stdio.h>")[1].name == "include"
    check parseC("""#include "x.h"""")[1].name == "include"

  test "define variants":
    check parseC("#define N 10")[1].name == "define"
    check parseC("#define M(a, b) ((a) + (b))")[1].name == "define"

  test "conditionals and pragma":
    check parseC("#ifdef X")[1].name == "ifdef"
    check parseC("#ifndef X")[1].name == "ifndef"
    check parseC("#pragma once")[1].name == "pragma"

  test "directive then code":
    let nodes = parseCStmts("""
      #include <stdio.h>
      int x = 1;
      """)
    check nodes.len == 2
    check nodes[0][1].name == "include"
    check nodes[1][2][1].valInt == 1

suite "C comments, positions and combos":
  test "line comment node":
    let n = parseC("// hello")
    check n.kind == nkInlineComment

  test "positions start at 1:1":
    let n = parseC("int x;")
    check n.ln == 1
    check n.col == 1
    check n[2].ln == 1

  test "multiline positions advance":
    let nodes = parseCStmts("""
      int x = 1;
      float y = 2.5;
      """)
    check nodes.len == 2
    check nodes[1].ln == nodes[0].ln + 1
    check nodes[0][2][0].name == "x"
    check nodes[1][2][0].name == "y"

  test "kitchen-sink program":
    let nodes = parseCStmts("""
      #include <stdio.h>
      typedef unsigned long myu;
      struct Point { int x; int y; };
      enum Color { RED, GREEN = 5, BLUE };
      static int total = 0;
      int add(int a, int b) {
        return a + b;
      }
      int main(void) {
        int i = 0;
        for (i = 0; i < 10; i++) {
          if (i == 5) continue;
          total += i;
        }
        while (total > 100) {
          total = total - 1;
        }
        switch (total) {
          case 1: break;
          default: break;
        }
        goto done;
        done: return total;
      }
      """)
    check nodes.len == 7
    check nodes[0][1].name == "include"
    check nodes[1][0].name == "typedef"
    check nodes[2][0].name == "struct"
    check nodes[3][0].name == "enum"
    check nodes[5].kind == nkFunction
    check nodes[6].kind == nkFunction
    check nodes[6][0].name == "main"
    var total = 0
    for n in nodes: total += countNodes(n)
    check total > 100

suite "C errors":
  test "missing initializer errors":
    expect OpenAstParsingError:
      discard parseC("int x = ;")

  test "unclosed if paren errors":
    expect OpenAstParsingError:
      discard parseC("if (x { }")

  test "unclosed while block errors":
    expect OpenAstParsingError:
      discard parseC("while (x) {")

  test "unclosed struct body errors":
    expect OpenAstParsingError:
      discard parseC("struct S { int x;")

  test "unclosed enum body errors":
    expect OpenAstParsingError:
      discard parseC("enum E { A")

  test "bad function params error":
    expect OpenAstParsingError:
      discard parseC("int f( { }")

  test "goto needs a label name":
    expect OpenAstParsingError:
      discard parseC("goto 123;")

  test "bad declarator errors":
    expect OpenAstParsingError:
      discard parseC("int 123;")
