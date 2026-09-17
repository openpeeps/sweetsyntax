# Go fixture corpus

Real-world Go files used to validate the Go language implementation
(zero-error `sweetsyntax parse` sweep + AST position audit).

## Provenance

Vendored verbatim from the Go standard library (`golang/go`, go1.23.0),
which is BSD-3-Clause licensed. Each file keeps its original copyright
header. Upstream: https://github.com/golang/go

| Fixture | Upstream path | Lines | Grammar coverage |
|---|---|---|---|
| `stdlib_cmp.go` | `src/cmp/cmp.go` | 77 | generics, `~int \| ~string` union constraints |
| `stdlib_context.go` | `src/context/context.go` | 792 | interfaces, struct embedding, value receivers, `<-chan`, `select`, `go`/`defer`, closures |
| `stdlib_slices.go` | `src/slices/slices.go` | 509 | generics, `...` spread, `range`, func values |
| `stdlib_json_decode.go` | `src/encoding/json/decode.go` | 1,302 | `.(type)` switches, conversions, composite literals, `&`/`*` |
| `go_comprehensive.go` | authored (this repo) | | struct tags, all four `for` forms, labeled `break`/`continue`, every assignment operator, imaginary/float literal forms, grouped-`const` elision |

`go_comprehensive.go` pins constructs the stdlib files do not
exercise: struct tags, all four `for` forms, labeled `break`/`continue`,
every assignment operator, imaginary literals, array/slice type specs,
methods on generic instantiations, embedded instantiations in
interfaces, two-value `select` receives, and edge cases. It is
`gofmt`-clean and `go build`/`go vet`-clean (checked in CI style via a
throwaway module), so it is both syntactically and semantically valid
Go — unlike the stdlib files it must also *compile*.
