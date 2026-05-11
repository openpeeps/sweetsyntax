# A generic syntax highlighter
#
# (c) 2025 George Lemon | LGPL-v3 License
#          Made by Humans from OpenPeeps
#          https://github.com/openpeeps/sweetsyntax

import ./sweetsyntax/[config, sweetlexer]
export config, sweetlexer

when isMainModule:
  import std/[terminal, strformat, strutils]

  import ./sweetsyntax/renderers/htmlrenderer
  import ./sweetsyntax/renderers/asciirenderer

  block:
    type RenderMode = enum
      rmAnsi, rmHtml

    proc parseMode(s: string): RenderMode =
      case s.toLowerAscii()
      of "html": rmHtml
      else: rmAnsi

    proc renderOutput(spec: SweetSpec, buffer: string, mode: RenderMode) =
      eraseScreen()
      setCursorPos(0, 0)

      stdout.writeLine("SweetSyntax live renderer")
      stdout.writeLine("ESC/Ctrl-C/Ctrl-D: quit | Enter: newline | Backspace: delete")
      stdout.writeLine("")
      stdout.writeLine("Input:")
      stdout.writeLine(buffer)
      stdout.writeLine("")
      stdout.writeLine("Output:")

      var lx = initLexer(spec, buffer)
      case mode
      of rmHtml:
        stdout.writeLine(highlightHtml(lx))
      of rmAnsi:
        stdout.writeLine(highlightAscii(lx, useColor = true))

    proc runLive(specPath: string, mode: RenderMode) =
      let syntax = newSyntax(specPath)
      var buffer = ""

      hideCursor()
      defer:
        showCursor()
        stdout.writeLine("")

      renderOutput(syntax.spec, buffer, mode)

      while true:
        let ch = getch()
        case ch
        of '\x1b', '\x03', '\x04':
          break
        of '\x7f', '\b':
          if buffer.len > 0:
            buffer.setLen(buffer.len - 1)
        of '\r', '\n':
          buffer.add('\n')
        else:
          if ch >= ' ':
            buffer.add(ch)

        renderOutput(syntax.spec, buffer, mode)

    runLive("./src/sweetsyntax/syntaxes/javascript.yaml", rmHtml)