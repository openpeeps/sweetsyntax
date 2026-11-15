import std/[os, options, tables, sets]
import ../../config
import ./buildprepared

const tsYamlPath* = currentSourcePath().parentDir / ".." / ".." / "syntaxes" / "ts.yaml"
const tsInitData* = buildPrepared(tsYamlPath)
