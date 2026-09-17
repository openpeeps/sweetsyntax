// Package gofixture pins Go constructs for parser validation,
// especially ones the vendored stdlib files do not exercise.
package gofixture

import (
	"fmt"
	str "strings"
	_ "unicode"
	. "unicode/utf8"
)

const (
	_  = iota
	KB = 1 << (10 * iota)
	MB
	pi       = 3.14159
	imagUnit = 1i
	greeting = "hello"
)

var (
	hexVal       = 0xFF
	hexUnder     = 0x_12
	octVal       = 0o777
	legacyOct    = 0755
	binVal       = 0b1010
	underscored  = 1_000_000
	trailingDot  = 1.
	leadingDot   = .5
	expVal       = 1e10
	expUnder     = 1e1_0
	hexFloat     = 0x1p-2
	hexFloatDot  = 0x1.p1
	hexLeadDot   = 0x.8p1
	imagOne      = 1i
	imagFloat    = 1.5i
	imagExp      = 1e10i
	imagHex      = 0xFFi
	imagHexFloat = 0x1p-2i
	charVal      = 'a'
	newlineChar  = '\n'
	unicodeChar  = '☃'
	quoteChar    = '\''
	escapes      = "\a\b\f\n\r\t\v\\'\""
	uniEscape    = "caf\u00e9\U0001F600"
	rawPath      = `C:\path\to`
)

type Tagged struct {
	Name    string `json:"name"`
	Ignored int    `json:"-"`
	Inline  struct {
		X int `yaml:"x"`
	} `json:"inline"`
	hidden string
}

type Base struct{ ID int }

type Other struct{ N int }

type Child struct {
	Base
	*Other
	Extra string
}

type (
	Stringer interface {
		String() string
	}
	Number interface {
		~int | ~float64
	}
	Alias    = []string
	NameMap  = map[string]int
	RecvChan = <-chan int
	SendChan = chan<- string
	Handler  = func(int) string
	AnySlice = any
	IntList  G[int]
)

type G[T any] struct {
	V T
}

type Matrix [2][3]int

type IntSlice []int

type Lister interface {
	G[int]
	String() string
}

type Seq[T any] interface {
	First() T
}

func (b Base) Value() int { return b.ID }

func (Base) Nameless() {}

func (c *Child) Rename(s string) { c.Extra = s }

func (g G[int]) Get() int { return g.V }

func Min[T Number](a, b T) T {
	if a < b {
		return a
	}
	return b
}

func first[S ~[]E, E any](s S) E { return s[0] }

func spreadInts(vals ...int) int {
	total := 0
	for _, v := range vals {
		total += v
	}
	return total
}

func divmod(a, b int) (q, r int) {
	q, r = a/b, a%b
	return
}

func exercise(count int, name string) (int, error) {
	x := 1
	x += 2
	x -= 1
	x *= 3
	x /= 2
	x %= 2
	x <<= 1
	x >>= 1
	x &= 3
	x |= 4
	x ^= 5
	x &^= 6
	y, z := 1, 2
	y, z = z, y
	_ = y + z
	x++
	x--
	a1 := 1
	a2 := 2
	_ = a1 + a2
	_ = (1 + 2) * 3
	_ = -x + +x - ^x
	_ = !true && false || true
	_ = 1&2 | 3 ^ 4&^5
	_ = 1 << 2 >> 1
	_ = 1 < 2
	_ = "a" + "b"
	_ = &x
	_ = *(&x)

	goto done
done:

outer:
	for i := 0; i < 3; i++ {
		for j := 0; j < 3; j++ {
			if j == 1 {
				continue outer
			}
			if j == 2 {
				break outer
			}
		}
	}
	for {
		break
	}
	alive := true
	for alive {
		alive = false
	}
	for k := 0; k < 1; k++ {
		_ = k
	}
	for i, v := range []int{7, 8} {
		_, _ = i, v
	}
	for range "ab" {
		break
	}

	switch x {
	case 1, 2:
		fallthrough
	case 3:
		x = 30
	default:
		x = 0
	}
	switch {
	case x > 100:
		x = 100
	}
	switch y := exercise2(); y {
	case 1:
		x = y
	}
	switch v := any(x).(type) {
	case int:
		_ = v
	case string, []byte:
		_ = v
	default:
	}

	ch := make(chan int, 1)
	ch <- 1
	select {
	case v := <-ch:
		_ = v
	case n, ok := <-ch:
		_, _ = n, ok
	case ch <- 2:
	default:
	}

	defer fmt.Println("deferred", name)
	go fmt.Println("async", count)

	fn := func(n int) int { return n * 2 }
	_ = fn(21)
	_ = func() int { return 1 }()

	s := []int{1, 2, 3, 4, 5}
	_ = s[1:3]
	_ = s[:2]
	_ = s[2:]
	_ = s[:]
	_ = s[1:3:4]
	_ = s[:2:3]
	arr := [3]int{1, 2, 3}
	_ = arr
	ell := [...]int{1, 2}
	_ = ell
	indexed := [3]int{2: 5}
	_ = indexed
	empty := struct{}{}
	_ = empty
	m := map[string]G[int]{"o": {V: 1}}
	_ = m
	nested := [][]int{{1}, {2, 3}}
	_ = nested
	gi := G[int]{V: count}
	_ = gi
	_ = gi.Get()
	convSrc := 3.7
	conv := int(convSrc)
	_ = conv
	_ = string([]byte("hi"))
	_ = []byte("hi")
	iface := any(42)
	if n2, ok := iface.(int); ok {
		_ = n2
	}
	_ = iface.(int)
	_ = <-ch
	_ = str.Contains(name, "x")
	_ = RuneCountInString(name)
	fmt.Println("done", count)
	return x, nil
}

func exercise2() int { return 1 }
