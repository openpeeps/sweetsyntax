## Stress-test scratch for the Nim handler (dev only, not a fixture).
## Must stay valid Nim: check with `nim check bin/test.nim`.
import std/[tables, strutils, macros]

const
  greeting = "hi"
  answer: int = 42

var
  counter = 0
  name*: string = "x"
  pair = (a: 1, b: 2)

let
  fixed = 7
  first, second = 1

type
  Color = enum
    red = "r"
    green
    blue
  Shape = object
    x, y*: int
    label: string
  NodeRef = ref object
    kids: seq[NodeRef]
  Kind = distinct int
  Alias = Table[string, seq[int]]

{.experimental: "codeReordering".}

proc add(a, b: int): int = a + b

proc greet(name: string; punct = "!"): string =
  result = "hi " & name & punct

proc find[T: string | int](items: seq[T]; want: T): int =
  for i, it in items:
    if it == want:
      return i
  return -1

iterator countUp(n: int): int =
  var i = 0
  while i < n:
    yield i
    inc i

proc bump(items: var seq[int]; more: openArray[int] = []) =
  for m in more:
    items.add(m)

method describe(s: Shape): string {.base.} = "shape"

when defined(debug):
  echo "debug on"
else:
  echo "debug off"

static:
  echo "static block"

converter toStr(x: int): string = $x

template withEcho(body: untyped): untyped =
  echo "start"
  body
  echo "done"

macro dumpIt(x: typed): untyped =
  quote do:
    echo `x`

proc useThings() =
  defer: echo "cleaning"
  echo greeting, answer
  static:
    echo "compile time"
  var local {.volatile.} = 1
  discard local
  let v = if counter > 0:
    "pos"
  else:
    "neg"
  let w = block:
    var t = 1
    t + 1
  let c = cast[int](3.5)
  let p = addr(counter)
  try:
    raise newException(ValueError, "bad")
  except ValueError as e:
    echo e.msg
  finally:
    inc counter
  withEcho:
    echo v
  for k, val in {"a": 1, "b": 2}:
    echo k, val
  case counter
  of 0, 1:
    echo "low"
  else:
    echo "high"
  while counter < 3:
    inc counter
  bind helper
  mixin unknownCall
