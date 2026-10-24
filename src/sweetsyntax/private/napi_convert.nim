## Shared JsonNode converters for the Node.js addon.
import std/json except `%*`
import std/[os, strutils]

template jsParse(node: JsonNode): napi_value =
  ## Bridge a JsonNode to a live JS object via JSON.parse.
  napiCall("JSON.parse", [%* $node])
