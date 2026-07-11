import std/[os, options, tables, sets]
import ../../config
import ./buildprepared

const jsYamlPath* = currentSourcePath().parentDir / ".." / ".." / "syntaxes" / "js.yaml"
const jsInitData* = buildPrepared(jsYamlPath)
