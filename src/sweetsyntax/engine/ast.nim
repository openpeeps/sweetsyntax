# A powerful generic parser and AST explorer for analyzing
# programming languages!
#
# (c) 2026 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

import std/sequtils
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

const LeafNodes* = {nkEmpty..nkIdent}
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