// ---- inty-go runtime ------------------------------------------------------
//
// Helpers the generated code calls into. Everything here implements a
// JavaScript semantic that has no direct Go equivalent (number
// formatting, `%` on doubles, ToInt32 for bitwise operators, the
// higher-order Array methods). Kept small so the Go compiler inlines the
// hot ones.

var intyOut = bufio.NewWriterSize(os.Stdout, 1<<16)

// intyZero is a non-constant 0 so `x / 0` doesn't become a Go
// compile-time division by zero.
var intyZero float64

func intyLog(s string) {
	intyOut.WriteString(s)
	intyOut.WriteByte('\n')
}

func intyBoolStr(b bool) string {
	if b {
		return "true"
	}
	return "false"
}

// intyNumStr implements ECMAScript Number::toString(10).
func intyNumStr(f float64) string {
	if f != f {
		return "NaN"
	}
	if f == 0 {
		return "0"
	}
	if math.IsInf(f, 1) {
		return "Infinity"
	}
	if math.IsInf(f, -1) {
		return "-Infinity"
	}
	if f == math.Trunc(f) && math.Abs(f) <= 9007199254740991 {
		return strconv.FormatInt(int64(f), 10)
	}
	s := strconv.FormatFloat(f, 'e', -1, 64) // shortest round-trip: d.ddde±XX
	neg := s[0] == '-'
	if neg {
		s = s[1:]
	}
	epos := strings.IndexByte(s, 'e')
	exp, _ := strconv.Atoi(s[epos+1:])
	digits := strings.Replace(s[:epos], ".", "", 1)
	k := len(digits)
	n := exp + 1
	var out string
	switch {
	case k <= n && n <= 21:
		out = digits + strings.Repeat("0", n-k)
	case 0 < n && n <= 21:
		out = digits[:n] + "." + digits[n:]
	case -6 < n && n <= 0:
		out = "0." + strings.Repeat("0", -n) + digits
	default:
		e := n - 1
		sign := "+"
		if e < 0 {
			sign = "-"
			e = -e
		}
		if k == 1 {
			out = digits + "e" + sign + strconv.Itoa(e)
		} else {
			out = digits[:1] + "." + digits[1:] + "e" + sign + strconv.Itoa(e)
		}
	}
	if neg {
		return "-" + out
	}
	return out
}

// intyInspectNum is how console.log shows a number: like
// Number::toString, except -0 prints as "-0".
func intyInspectNum(f float64) string {
	if f == 0 && math.Signbit(f) {
		return "-0"
	}
	return intyNumStr(f)
}

// intyMod is JavaScript `%` on doubles (truncating, sign of the
// dividend). Non-negative safe integers take an integer fast path.
func intyMod(a, b float64) float64 {
	if a >= 0 && b > 0 && a <= 9007199254740991 && b <= 9007199254740991 &&
		a == math.Trunc(a) && b == math.Trunc(b) {
		return float64(int64(a) % int64(b))
	}
	return math.Mod(a, b)
}

// intyToInt32 is ECMAScript ToInt32, used by the bitwise operators.
func intyToInt32(f float64) int32 {
	if f >= -2147483648 && f <= 2147483647 {
		return int32(f)
	}
	if f != f || math.IsInf(f, 0) {
		return 0
	}
	return int32(uint32(int64(math.Mod(math.Trunc(f), 4294967296))))
}

func intyToUint32(f float64) uint32 { return uint32(intyToInt32(f)) }

// intyRound is Math.round: round half up (towards +Infinity).
func intyRound(f float64) float64 {
	if f != f || math.IsInf(f, 0) {
		return f
	}
	r := math.Floor(f)
	if f-r >= 0.5 {
		r++
	}
	if r == 0 && (f < 0 || math.Signbit(f)) {
		return math.Copysign(0, -1)
	}
	return r
}

func intySign(f float64) float64 {
	switch {
	case f > 0:
		return 1
	case f < 0:
		return -1
	}
	return f // ±0 and NaN
}

func intyStrIndexOf(s, sub string) int { return strings.Index(s, sub) }

func intyClampIndex(i float64, n int) int {
	if i != i {
		return 0
	}
	if i < 0 {
		i += float64(n)
		if i < 0 {
			return 0
		}
	}
	if i > float64(n) {
		return n
	}
	return int(i)
}

func intyStrSlice(s string, start, end float64) string {
	a, b := intyClampIndex(start, len(s)), intyClampIndex(end, len(s))
	if a >= b {
		return ""
	}
	return s[a:b]
}

func intyStrSubstring(s string, start, end float64) string {
	clamp := func(f float64) int {
		if f != f || f < 0 {
			return 0
		}
		if f > float64(len(s)) {
			return len(s)
		}
		return int(f)
	}
	a, b := clamp(start), clamp(end)
	if a > b {
		a, b = b, a
	}
	return s[a:b]
}

func intyFromCharCode(c float64) string { return string(rune(intyToUint32(c) & 0xffff)) }

// ---- Arrays: JS arrays are reference types, so they map to *[]T. -----

func intyPush[T any](a *[]T, v T) int {
	intyAppend(a, v)
	return len(*a)
}

// intyAppend is `a.push(v)` as a statement. A full array grows to twice
// its length: Go's append grows large slices by only 1.25x, so an array
// built by pushing millions of elements (a JS idiom) would be copied
// about five times over; doubling copies it about once, like V8's 1.5x.
func intyAppend[T any](a *[]T, v T) {
	s := *a
	if len(s) == cap(s) {
		s = intyGrow(s)
	}
	*a = append(s, v)
}

//go:noinline
func intyGrow[T any](s []T) []T { return slices.Grow(s, len(s)+1) }

func intyPop[T any](a *[]T) T {
	s := *a
	v := s[len(s)-1]
	*a = s[:len(s)-1]
	return v
}

// intyUnshift is Array.prototype.unshift with one element.
func intyUnshift[T any](a *[]T, v T) int {
	*a = slices.Insert(*a, 0, v)
	return len(*a)
}

// intySplice is Array.prototype.splice(start, deleteCount, ...items): it
// replaces the deleted range with items in place and returns the removed
// elements. An omitted deleteCount is +Inf (remove to the end).
func intySplice[T any](a *[]T, start, del float64, items ...T) *[]T {
	i, j := intySpliceRange(len(*a), start, del)
	removed := append([]T{}, (*a)[i:j]...)
	*a = slices.Replace(*a, i, j, items...)
	return &removed
}

// intySpliceStmt is intySplice in statement position: the removed
// elements are not collected.
func intySpliceStmt[T any](a *[]T, start, del float64, items ...T) {
	i, j := intySpliceRange(len(*a), start, del)
	*a = slices.Replace(*a, i, j, items...)
}

func intySpliceRange(n int, start, del float64) (int, int) {
	i := intyClampIndex(math.Trunc(start), n)
	d := 0
	if del == del && del > 0 {
		d = int(min(math.Trunc(del), float64(n-i)))
	}
	return i, i + d
}

func intyIndexOf[T comparable](a *[]T, v T) int {
	for i, x := range *a {
		if x == v {
			return i
		}
	}
	return -1
}

func intyIncludes[T comparable](a *[]T, v T) bool { return intyIndexOf(a, v) >= 0 }

func intySlice[T any](a *[]T, start, end float64) *[]T {
	s := *a
	i, j := intyClampIndex(start, len(s)), intyClampIndex(end, len(s))
	out := []T{}
	if i < j {
		out = append(out, s[i:j]...)
	}
	return &out
}

func intyConcat[T any](a, b *[]T) *[]T {
	out := make([]T, 0, len(*a)+len(*b))
	out = append(append(out, *a...), *b...)
	return &out
}

func intyFill[T any](a *[]T, v T) *[]T {
	s := *a
	for i := range s {
		s[i] = v
	}
	return a
}

func intyReverse[T any](a *[]T) *[]T {
	s := *a
	for i, j := 0, len(s)-1; i < j; i, j = i+1, j-1 {
		s[i], s[j] = s[j], s[i]
	}
	return a
}

func intyMap[T, U any](a *[]T, f func(T) U) *[]U {
	out := make([]U, len(*a))
	for i, x := range *a {
		out[i] = f(x)
	}
	return &out
}

func intyFilter[T any](a *[]T, f func(T) bool) *[]T {
	out := []T{}
	for _, x := range *a {
		if f(x) {
			out = append(out, x)
		}
	}
	return &out
}

func intyForEach[T any](a *[]T, f func(T)) {
	for i := 0; i < len(*a); i++ {
		f((*a)[i])
	}
}

func intyReduce[T, U any](a *[]T, f func(U, T) U, acc U) U {
	for i := 0; i < len(*a); i++ {
		acc = f(acc, (*a)[i])
	}
	return acc
}

func intySome[T any](a *[]T, f func(T) bool) bool {
	for _, x := range *a {
		if f(x) {
			return true
		}
	}
	return false
}

func intyEvery[T any](a *[]T, f func(T) bool) bool {
	for _, x := range *a {
		if !f(x) {
			return false
		}
	}
	return true
}

func intyFindIndex[T any](a *[]T, f func(T) bool) int {
	for i, x := range *a {
		if f(x) {
			return i
		}
	}
	return -1
}

func intyJoin[T any](a *[]T, sep string, str func(T) string) string {
	// Strings: strings.Join sizes the result once instead of growing it.
	if ss, ok := any(*a).([]string); ok {
		return strings.Join(ss, sep)
	}
	var b strings.Builder
	for i, x := range *a {
		if i > 0 {
			b.WriteString(sep)
		}
		b.WriteString(str(x))
	}
	return b.String()
}

// intySet is `a[i] = v`: JS grows the array when writing past the end
// (holes are filled with the zero value; JS would leave them empty).
func intySet[T any](a *[]T, j int, v T) {
	s := *a
	if j < len(s) {
		s[j] = v
		return
	}
	for len(s) < j {
		var zero T
		s = append(s, zero)
	}
	*a = append(s, v)
}

// ---- Numbers ------------------------------------------------------------

// An inty `Int` is a Go int. JS computes on doubles, which hold every
// integer up to 2^53 exactly; past that the two would silently disagree,
// so the operations that can get there (multiplication, and a double
// becoming an Int: Math.floor and friends) stop the program instead.

const intyMaxSafe = 1 << 53

// intyToInt is a double known to be an integer (or a trap) as an Int.
// (NaN fails the comparison too.)
func intyToInt(f float64) int {
	if !(f < intyMaxSafe && f > -intyMaxSafe) {
		panic("inty: a number converted to an integer is not a safe integer (|n| < 2^53)")
	}
	return int(f)
}

// intyIMul is `a * b` on Ints. Small enough to inline: the product as a
// double decides (a product it can't represent exactly is at least 2^53
// in magnitude, so it's caught).
func intyIMul(a, b int) int {
	if f := float64(a) * float64(b); f >= intyMaxSafe || f <= -intyMaxSafe {
		panic("inty: an integer product is not a safe integer (|n| < 2^53); " +
			"JavaScript would compute a different value")
	}
	return a * b
}

func intyFloorInt(f float64) int { return intyToInt(math.Floor(f)) }
func intyCeilInt(f float64) int  { return intyToInt(math.Ceil(f)) }
func intyTruncInt(f float64) int { return intyToInt(math.Trunc(f)) }
func intyRoundInt(f float64) int { return intyToInt(intyRound(f)) }

func intyAbsInt(i int) int {
	if i < 0 {
		return -i
	}
	return i
}

// intyStrSliceI is intyStrSlice with Int bounds.
func intyStrSliceI(s string, a, b int) string {
	n := len(s)
	if a < 0 {
		a = max(a+n, 0)
	} else if a > n {
		a = n
	}
	if b < 0 {
		b = max(b+n, 0)
	} else if b > n {
		b = n
	}
	if a >= b {
		return ""
	}
	return s[a:b]
}

// intyStrSubstringI is intyStrSubstring with Int bounds.
func intyStrSubstringI(s string, a, b int) string {
	a, b = min(max(a, 0), len(s)), min(max(b, 0), len(s))
	if a > b {
		a, b = b, a
	}
	return s[a:b]
}

func intyTruthy(f float64) bool { return f != 0 && f == f }

func intyLogErr(s string) {
	intyOut.Flush()
	os.Stderr.WriteString(s + "\n")
}

// intyPow is `**` / Math.pow; differs from math.Pow only where JS
// returns NaN for a base of ±1 with a NaN or infinite exponent.
func intyPow(x, y float64) float64 {
	if y != y || (math.IsInf(y, 0) && (x == 1 || x == -1)) {
		return math.NaN()
	}
	return math.Pow(x, y)
}

func intyImul(a, b float64) int { return int(intyToInt32(a) * intyToInt32(b)) }

func intyFround(f float64) float64 { return float64(float32(f)) }

func intyClz32(f float64) int { return bits.LeadingZeros32(intyToUint32(f)) }

func intyIsInteger(f float64) bool { return !math.IsInf(f, 0) && f == math.Trunc(f) }

var _ = rand.Float64

var intyStart = time.Now()

// intyNow is performance.now(): milliseconds since program start.
func intyNow() float64 { return float64(time.Since(intyStart).Nanoseconds()) / 1e6 }

func intyStrIndexOfFrom(s, sub string, from float64) int {
	i := intyClampIndex(max(from, 0), len(s))
	if j := strings.Index(s[i:], sub); j >= 0 {
		return i + j
	}
	return -1
}

// intyStartsWithAt is startsWith(x, pos).
func intyStartsWithAt(s, x string, pos float64) bool {
	return strings.HasPrefix(s[intyClampIndex(max(pos, 0), len(s)):], x)
}

func intyCharAt(s string, i float64) string {
	if i != i {
		i = 0
	}
	i = math.Trunc(i)
	if i < 0 || i >= float64(len(s)) {
		return ""
	}
	return s[int(i) : int(i)+1]
}

// intySplit is String.prototype.split with a string separator. An empty
// separator splits into single bytes (code units, for ASCII).
func intySplit(s, sep string, limit float64) *[]string {
	var parts []string
	if sep == "" {
		parts = make([]string, len(s))
		for i := range s {
			parts[i] = s[i : i+1]
		}
	} else {
		parts = strings.Split(s, sep)
	}
	if !math.IsInf(limit, 1) {
		n := int(uint32(intyToInt32(limit)))
		if n < len(parts) {
			parts = parts[:n]
		}
	}
	return &parts
}

// intyReplace is String.prototype.replace / replaceAll with a string
// pattern (n = 1 or -1), including the `$$`, `$&`, "$`" and `$'`
// replacement patterns.
func intyReplace(s, pat, rep string, n int) string {
	if !strings.Contains(rep, "$") {
		if pat == "" && n < 0 {
			return strings.Replace(s, pat, rep, len(s)+1)
		}
		return strings.Replace(s, pat, rep, n)
	}
	var b strings.Builder
	last := 0
	for n != 0 {
		i := strings.Index(s[last:], pat)
		if i < 0 {
			break
		}
		at := last + i
		b.WriteString(s[last:at])
		for k := 0; k < len(rep); k++ {
			if rep[k] != '$' || k+1 == len(rep) {
				b.WriteByte(rep[k])
				continue
			}
			switch rep[k+1] {
			case '$':
				b.WriteByte('$')
			case '&':
				b.WriteString(pat)
			case '`':
				b.WriteString(s[:at])
			case '\'':
				b.WriteString(s[at+len(pat):])
			default:
				b.WriteByte('$')
				continue
			}
			k++
		}
		last = at + len(pat)
		if pat == "" {
			if at < len(s) {
				b.WriteByte(s[at])
			}
			last = at + 1
			if last > len(s) {
				return b.String()
			}
		}
		n--
	}
	b.WriteString(s[min(last, len(s)):])
	return b.String()
}

func intyPad(s string, n float64, pad string, start bool) string {
	want := int(max(math.Trunc(n), 0)) - len(s)
	if want <= 0 || pad == "" {
		return s
	}
	fill := strings.Repeat(pad, want/len(pad)+1)[:want]
	if start {
		return fill + s
	}
	return s + fill
}

// ---- Node built-ins (node:fs, node:process) ---------------------------------

// process.argv: Node puts the executable and the script path first, so
// `process.argv.slice(2)` is the user's arguments on both sides.
var intyArgv = func() *[]string {
	a := append([]string{os.Args[0], os.Args[0]}, os.Args[1:]...)
	return &a
}()

// intyFail reports an I/O error the way an uncaught Node exception
// would end the process: a message on stderr and exit status 1.
func intyFail(err error) {
	intyOut.Flush()
	os.Stderr.WriteString("Error: " + err.Error() + "\n")
	os.Exit(1)
}

func intyReadFileSync(path, enc string) string {
	b, err := os.ReadFile(path)
	if err != nil {
		intyFail(err)
	}
	return string(b)
}

func intyWriteFileSync(path, data string) {
	if err := os.WriteFile(path, []byte(data), 0o666); err != nil {
		intyFail(err)
	}
}

func intyAppendFileSync(path, data string) {
	f, err := os.OpenFile(path, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0o666)
	if err == nil {
		_, err = f.WriteString(data)
		if cerr := f.Close(); err == nil {
			err = cerr
		}
	}
	if err != nil {
		intyFail(err)
	}
}

func intyExistsSync(path string) bool {
	_, err := os.Stat(path)
	return err == nil
}

func intyExit(code float64) {
	intyOut.Flush()
	os.Exit(int(intyToInt32(code)))
}

func intyStdoutWrite(s string) bool {
	intyOut.WriteString(s)
	return true
}

func intyStderrWrite(s string) bool {
	intyOut.Flush()
	os.Stderr.WriteString(s)
	return true
}

var _ = unicode.IsSpace
