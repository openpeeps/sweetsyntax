'use strict';
const fs = require('fs');
const path = require('path');

const SUPPORTED = {
  darwin: ['arm64', 'x64'],
  linux: ['arm64', 'x64'],
};

function candidates() {
  const list = [];
  const pair = `${process.platform}-${process.arch}`;
  list.push(path.join(__dirname, 'bin', pair, 'sweetsyntax.node'));
  list.push(path.join(__dirname, '..', '..', 'bin', 'sweetsyntax.node'));
  return { list, pair };
}

let loaded = null;
let loadedFrom = null;
const { list, pair } = candidates();
for (const p of list) {
  if (fs.existsSync(p)) {
    loadedFrom = p;
    loaded = require(p);
    break;
  }
}

if (loaded === null) {
  const supported = Object.entries(SUPPORTED)
    .map(([plat, archs]) => archs.map((a) => `${plat}-${a}`).join(', '))
    .join(', ');
  throw new Error(
    `sweetsyntax-napi: no prebuilt binary for ${pair} and no dev fallback found. Tried:\n` +
      list.join('\n') +
      `\nSupported: ${supported}.\n` +
      'Build it with `npm run build` on the target host ' +
      '(requires Nim, denim and cmake-js).'
  );
}

module.exports = loaded;
module.exports.binaryPath = loadedFrom;
module.exports.nativePair = pair;
