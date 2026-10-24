'use strict';
const { describe, it } = require('node:test');
const assert = require('node:assert/strict');
const m = require('../index.js');

describe('sweetsyntax', () => {
  it('highlights js', () => {
    const out = m.highlightScript('const x = 1;', 'js', 'html');
    assert.ok(typeof out === 'string' && out.length > 0);
  });
  it('parses js to an AST', () => {
    const ast = m.parseScript('const x = 1;', 'js');
    assert.ok(ast && Array.isArray(ast.nodes));
  });
  it('highlights a file', () => {
    const fs = require('fs');
    const os = require('os');
    const path = require('path');
    const tmp = path.join(os.tmpdir(), 'ss_test.js');
    fs.writeFileSync(tmp, 'const x = 1;\n');
    const out = m.highlightFileScript(tmp, 'html');
    assert.ok(typeof out === 'string' && out.length > 0);
    fs.unlinkSync(tmp);
  });
});
