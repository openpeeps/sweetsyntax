# A powerful generic parser and AST explorer for analyzing
# programming languages!
#
# (c) 2026 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

import std/sequtils
import std/strutils
import ../tokenizer

type
  NodeKind* = enum
    ## The different kinds of AST nodes we can have. This is a very basic set of node kinds,
    ## and can be extended as needed for specific languages or constructs
    nkEmpty
    nkLitBool
    nkLitInt
    nkLitFloat
    nkLitString
    nkLitBigInt

    nkIdent
    nkVarTy
    nkNil
    nkIdentDefs

    nkPrefix
    nkPostfix
    nkInfix
    nkDotExpr
    nkBracketExpr
    nkColonExpr
    nkCall
    nkCast
      ## C-style cast: `[typeNode, operand]` (`(int)x`, `(T*)p`).
    nkRegex
    nkReturn

    nkImport
    nkInclude

    nkInlineComment
    nkDocComment

    nkFunction
    nkClass
    nkInterface

    nkVar
    nkStatement
    nkBlock
    nkPragmaBlock
      ## Pragma applied to a statement: `[pragma, body]`
      ## (Nim `{.cast(...).}: stmt` — cf. `parseStmtPragma`).
    nkArrayLit
      ## Array literal `[a, b, c]` — distinct from `nkBracketExpr`,
      ## which is reserved for subscript access `a[i]`.
    nkCommentGroup
      ## An expression with interleaved comments attached:
      ## `[expr, comment]`. Chains nest.
    nkObjConstr
      ## Composite literal / object construction: `[base, elements...]`
      ## (Go `T{...}`; elided nested literals use `nkEmpty` as base).
      ## Elements are bare values or `nkColonExpr [key, value]`.
    nkTypeAssert
      ## Type assertion: `[x, type]` (Go `x.(T)`; `x.(type)` uses
      ## an `nkIdent("type")` as the type child).
    nkImaginary
      ## Imaginary literal (Go `1i`, `1.5i`, `0x1p-2i`): raw source
      ## text, e.g. `"1.5i"`. A string payload like bigint (parsing
      ## hex-float mantissas is a language quirk, not AST business).

  Node* {.acyclic.} = ref object
    ## A node in the abstract syntax tree, representing a construct in the source code.
    ln*, col*: int
    case kind*: NodeKind
    of nkEmpty, nkNil: discard
    of nkLitBool: valBool*: bool
    of nkLitInt: valInt*: int
    of nkLitFloat: valFloat*: float
    of nkLitString: valStr*: string
    of nkLitBigInt: valBigInt*: string
    of nkImaginary: valImag*: string
    of nkIdent: name*: string
    else:
      children*: seq[Node]
        ## For non-leaf nodes, we store their children in a sequence.
        ## The interpretation of these children depends on the node kind

  OpenAstProgram* = ref object
    ## The root of the AST, representing an entire program or module
    nodes*: seq[Node]
      ## The root of the AST, containing a sequence of top-level
      ## nodes (e.g., statements or declarations)

const LeafNodes* = {nkEmpty..nkIdent, nkImaginary}
  ## A set of node kinds that are considered leaf
  ## nodes (i.e., they do not have children)

proc len*(node: Node): int =
  ## Return the number of children for a non-leaf node, or 0 for leaf nodes.
  result = node.children.len

proc `[]`*(node: Node, index: int | BackwardsIndex): Node =
  ## Access a child node by index, supporting both forward and backward indexing.
  result = node.children[index]

proc `[]`*(node: Node, slice: HSlice): seq[Node] =
  ## Access a slice of child nodes, returning a sequence of nodes.
  result = node.children[slice]

proc `[]=`*(node: Node, index: int | BackwardsIndex, child: Node) =
  ## Set a child node at the specified index, supporting both forward and backward indexing.
  node.children[index] = child

iterator items*(node: Node): Node =
  ## Iterate over the children of a node, yielding each child node.
  when compiles(NodeKind.nkHtmlElement):
    if node.kind == nkHtmlElement:
      for child in node.childElements:
        yield child
    else:  
      for child in node.children:
        yield child
  else:
    for child in node.children:
      yield child

iterator pairs*(node: Node): tuple[i: int, n: Node] =
  ## Iterate over the children of a node, yielding both the index and the child node.
  for i, child in node.children:
    yield (i, child)

proc add*(node, child: Node): Node {.discardable.} =
  ## Add a single child node to the given node's children sequence,
  ## and return the parent node for chaining.
  node.children.add(child)
  result = node

proc add*(node: Node, children: openArray[Node]): Node {.discardable.} =
  ## Add multiple child nodes to the given node's children sequence,
  ## and return the parent node for chaining.
  node.children.add(children)
  result = node

proc newNode*(val: string): Node =
  ## Create a new nkLitString
  Node(kind: nkLitString, valStr: val)

template newBlockNode*: untyped =
  ## Create a new block node with an empty children sequence.
  Node(kind: nkBlock, ln: p.curr.line, col: p.curr.col)

template newNode*(nodeKind: NodeKind): untyped =
  ## Template for creating a new nodes. This is using the current token
  ## position for the line and column, which is useful when parsing code and building the AST
  Node(kind: nodeKind, ln: p.curr.line, col: p.curr.col)

proc newInlineComment*(val: string): Node =
  ## Create a new inline comment node with the given comment text.
  Node(kind: nkInlineComment, children: @[Node(kind: nkLitString, valStr: val)])

proc newDocComment*(val: string): Node =
  ## Create a new documentation comment node with the given comment text.
  Node(kind: nkDocComment, children: @[Node(kind: nkLitString, valStr: val)])

proc newFunction*(name: string, params: seq[Node], body: Node): Node =
  ## Create a new function node with the given name, parameters, and body.
  Node(kind: nkFunction, children: @[Node(kind: nkIdent, name: name)] & params & @[body])

proc newFunction*(tk: TokenTuple): Node =
  ## Create a new function node with the given token (for the name), parameters, and body.
  Node(kind: nkFunction, ln: tk.line, col: tk.col)

proc newIdent*(name: string, ln, col: int): Node =
  ## Create a new identifier node with the given name.
  Node(kind: nkIdent, name: name, ln: ln, col: col)

proc newIdent*(tk: TokenTuple, id: string): Node =
  ## Create a new identifier node with the given name and token position.
  Node(kind: nkIdent, name: id, ln: tk.line, col: tk.col)

proc newPostfix*(op: Node, operand: Node): Node =
  ## Create a new postfix operator node with the given operator and operand.
  Node(kind: nkPostfix, children: @[op, operand])

proc newEmptyNode*: Node =
  ## Create a new empty node, which can be used as a placeholder in the AST.
  Node(kind: nkEmpty)

proc stamp*(n: Node, line, col: int): Node {.discardable, inline.} =
  ## Generic helper: attach source position to any node.
  ## Every language handler (`c`, `js`, `php`, `ruby`, `nim`) can use this
  ## so AST nodes always carry `ln`/`col` from the token that produced them.
  if n != nil:
    n.ln = line
    n.col = col
  n

proc stamp*(n: Node, tk: TokenTuple): Node {.discardable, inline.} =
  ## Overload taking a token tuple directly.
  if n != nil:
    n.ln = tk.line
    n.col = tk.col
  n

proc stampFrom*(n, src: Node): Node {.discardable, inline.} =
  ## Copy position from another node (e.g. an `nkInfix` takes the
  ## position of its left-hand side, so the node points at the start
  ## of the expression).
  if n != nil and src != nil:
    n.ln = src.ln
    n.col = src.col
  n

proc treeRepr*(n: Node): string =
  ## Single-line representation of a node: its kind plus `=value`
  ## for leaf payloads (e.g. `nkIdent=folds`), Nim `dumpTree`-style.
  ## String values keep their stored form; only control characters
  ## are escaped so each node stays on one line.
  result = $n.kind
  case n.kind
  of nkIdent: result.add("=" & n.name)
  of nkLitBool: result.add("=" & $n.valBool)
  of nkLitInt: result.add("=" & $n.valInt)
  of nkLitFloat: result.add("=" & $n.valFloat)
  of nkLitString:
    result.add("=" & n.valStr.multiReplace(
      ("\\", "\\\\"), ("\n", "\\n"), ("\r", "\\r"), ("\t", "\\t")))
  of nkLitBigInt: result.add("=" & n.valBigInt)
  of nkImaginary: result.add("=" & n.valImag)
  of nkEmpty, nkNil: discard
  else: discard

proc dumpTree*(n: Node, indent = 0): string =
  ## Render a node and its children as an indent-based tree
  ## (2 spaces per level), just like Nim's `dumpTree`.
  result = "  ".repeat(indent) & treeRepr(n) & "\n"
  if n.kind notin LeafNodes and n.children.len > 0:
    for child in n.children:
      if child != nil:
        result.add dumpTree(child, indent + 1)

proc dumpTree*(program: OpenAstProgram): string =
  ## Render every top-level node of a program as an indent-based tree.
  for node in program.nodes:
    if node != nil:
      result.add dumpTree(node, 0)