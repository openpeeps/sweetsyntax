'use strict';
const fs = require('fs');
const os = require('os');
const path = require('path');

const PLATFORMS = {
  darwin: ['arm64', 'x64'],
  linux: ['arm64', 'x64'],
  win32: ['x64'],
};

const repoRoot = path.resolve(__dirname, '..', '..', '..');
const src = path.join(repoRoot, 'bin', 'sweetsyntax.node');

const plat = PLATFORMS[os.platform()] ? os.platform() : null;
if (plat === null || !PLATFORMS[plat].includes(os.arch())) {
  console.error(
    `sweetsyntax-napi: unsupported host ${os.platform()}-${os.arch()}. ` +
      'Supported: ' +
      Object.entries(PLATFORMS)
        .map(([p, archs]) => archs.map((a) => `${p}-${a}`).join(', '))
        .join(', ')
  );
  process.exit(1);
}

if (!fs.existsSync(src)) {
  console.error(`sweetsyntax-napi: ${src} not found. Run denim build first.`);
  process.exit(1);
}

const destDir = path.join(__dirname, '..', 'bin', `${plat}-${os.arch()}`);
fs.mkdirSync(destDir, { recursive: true });
fs.copyFileSync(src, path.join(destDir, 'sweetsyntax.node'));
console.log(`sweetsyntax-napi: placed binary for ${plat}-${os.arch()}`);
