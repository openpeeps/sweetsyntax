# Test fixtures (real-world source files)

Each subdirectory holds vendored, read-only source files used as
parse fixtures. Files are pinned to a specific upstream tag so the
suite stays reproducible.

## `ruby/vagrant_bundler.rb`

- Source: https://github.com/hashicorp/vagrant/blob/v2.4.9/lib/vagrant/bundler.rb
- Upstream tag: `v2.4.9`
- License: BUSL-1.1, `Copyright (c) HashiCorp, Inc.` (header kept intact)
- Why this file: nested classes, kwargs with defaults (`plugin_file:`,
  `solution_file: nil`), `**opts`, safe navigation (`&.`), symbol-to-proc
  (`&:full_name`), a regex with named captures, inline `rescue` modifiers
  and `retry`, deep `::` paths. It exercises the lexer and parser gaps
  tracked for Ruby support.

To refresh: download the same path from the pinned tag above.
Do not reformat; the parser must handle the file verbatim.

## `js/d3.js`

- Source: `bin/d3.js` (d3.js v7.9.0, unminified, ~20k lines)
- License: ISC, `Copyright 2010-2023 Mike Bostock` (header kept intact)
- Why this file: the project's standard benchmark input (see README
  benchmarks); exercises functions, closures, method chains and
  operators end to end.

## `js/react-dom.development.js`

- Source: `bin/react-dom.development.js` (React development build)
- License: MIT, `Copyright (c) Facebook, Inc. and its affiliates`
  (header kept intact)
- Why this file: large real-world bundle with UMD wrapper, `'use strict'`,
  classes, template literals, and deep call/member chains.

To refresh: copy the same files from `bin/` (tracked upstream of this repo).
Do not reformat; the parser must handle the files verbatim.

## `php/ContainerBuilder.php`

- Source: https://github.com/symfony/symfony/blob/v7.2.0/src/Symfony/Component/DependencyInjection/ContainerBuilder.php
- Upstream tag: `v7.2.0` (1778 lines)
- License: MIT, `(c) Fabien Potencier <fabien@symfony.com>` (header kept intact)
- Why this file: namespaced class with `use` imports, typed/nullable/union
  signatures, closures, `match`, attributes, and deep call chains. It
  exercises the PHP statement handlers end to end.

To refresh: download the same path from the pinned tag above.
Do not reformat; the parser must handle the file verbatim.

## `c/libevent_event.c`

- Source: https://github.com/libevent/libevent/blob/release-2.1.12-stable/event.c
- Upstream tag: `release-2.1.12-stable` (4020 lines)
- License: BSD-3-Clause, `Copyright (c) 2000-2007 Niels Provos`
  (header kept intact)
- Why this file: the event core in classic C with `#include`, `#ifdef`/
  `#else`/`#endif` platform branches, function definitions with pointer
  params, `struct`/`static` declarations, `switch`/`case`/`goto`, and
  `/* */` comments. It exercises the C statement handlers and
  preprocessor skipping end to end.

To refresh: download the same path from the pinned tag above.
Do not reformat; the parser must handle the file verbatim.
