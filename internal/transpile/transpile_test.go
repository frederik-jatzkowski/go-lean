package transpile_test

import (
	"os"
	"os/exec"
	"path/filepath"
	"strings"
	"testing"

	"github.com/frederik-jatzkowski/go-lean/internal/transpile"
)

func writeFile(t *testing.T, path, content string) {
	t.Helper()
	if err := os.MkdirAll(filepath.Dir(path), 0o755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(path, []byte(content), 0o644); err != nil {
		t.Fatal(err)
	}
}

func newModule(t *testing.T) string {
	t.Helper()
	dir := t.TempDir()
	writeFile(t, filepath.Join(dir, "go.mod"), "module example.test/sample\n\ngo 1.27.0\n")
	return dir
}

func TestLowerSSA(t *testing.T) {
	path := filepath.Join(newModule(t), "input.go")
	writeFile(t, path, `package match
//golean:verify
func def(x int64) int64 {
	x = -x
	if x < 0 {
		x := -x
		if x == 0 {
			return -0x8000_0000_0000_0000
		}
		return x
	}
	return x
}
//golean:verify
func folded() int64 {
	return ((9223372036854775807 + 1) - 1) - (4 / 2)
}
`)
	outputs, err := transpile.Generate(filepath.Dir(path))
	if err != nil {
		t.Fatal(err)
	}
	got := outputs[0].Source
	for _, want := range []string{
		"def «example.test/sample».«input».«def»",
		"(-«v0_x»)",
		"(Int64.ofInt (-9223372036854775808))",
		"(Int64.ofInt (9223372036854775805))",
	} {
		if !strings.Contains(got, want) {
			t.Errorf("missing %q in output:\n%s", want, got)
		}
	}
}

func TestMachineWordTargetWidth(t *testing.T) {
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "input.go"), `package sample
//golean:verify
func roundTrip(x int) int { return int(uint(x)) }
//golean:verify
func signedRemainder(x, y int) int { return x % y }
//golean:verify
func unsignedRemainder(x, y uint) uint { return x % y }
`)
	t.Setenv("GOOS", "linux")
	for _, target := range []struct{ arch, width string }{{"386", "32"}, {"amd64", "64"}} {
		t.Run(target.arch, func(t *testing.T) {
			t.Setenv("GOARCH", target.arch)
			outputs, err := transpile.Generate(dir)
			if err != nil {
				t.Fatal(err)
			}
			got := outputs[0].Source
			for _, want := range []string{
				".GoTypes.Int := Int" + target.width,
				".GoTypes.UInt := UInt" + target.width,
				").toInt" + target.width,
				").toUInt" + target.width,
				" : Option Int" + target.width + " := do",
				" : Option UInt" + target.width + " := do",
				"then none else some («v0_x» % «v1_y»)",
			} {
				if !strings.Contains(got, want) {
					t.Errorf("missing %q in output:\n%s", want, got)
				}
			}
		})
	}
}

func TestConcreteMethods(t *testing.T) {
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "policy", "policy.go"), `package policy
type Tier uint8
func (t Tier) Limit() uint8 { return uint8(t) }
`)
	writeFile(t, filepath.Join(dir, "input.go"), `package sample
import "example.test/sample/policy"
type First uint8
type Second struct{}
//golean:verify
func (f First) Limit() uint8 { return policy.Tier(f).Limit() }
//golean:verify
func (*Second) Limit() uint8 { return 25 }
//golean:verify
func Limit() uint8 { return First(1).Limit() + (*Second)(nil).Limit() }
`)
	outputs, err := transpile.Generate(dir)
	if err != nil {
		t.Fatal(err)
	}
	got := outputs[0].Source
	for _, want := range []string{
		"«First$Limit»", "«Second$Limit»", "«example.test/sample/policy».«Tier$Limit»",
		"«input».«Limit»", "«Second$Limit» none)",
	} {
		if !strings.Contains(got, want) {
			t.Errorf("missing %q in output:\n%s", want, got)
		}
	}
}

func TestRejectUnsupportedStatefulMethods(t *testing.T) {
	for _, test := range []struct{ name, body, want string }{
		{"untracked pointer", "func (r *Record) f(other *Record) int { r.value++; other.value++; return r.value }", "unsupported stateful method parameter"},
		{"receiver escape", "func (r *Record) f() int { r.value++; escaped = r; return r.value }", "unsupported receiver-state instruction"},
		{"slice write", "func (r *Record) f() int { r.value++; r.items[0] = 1; return r.value }", "unsupported receiver-state instruction"},
		{"unbounded", "func (r *Record) f() int { for r.value < 100 { r.value-- }; return r.value }", "one cursor increment on every back edge"},
		{"no increment", "func (r *Record) f() int { for r.value < len(r.items) { if r.items[r.value] == 0 { r.value++ } }; return r.value }", "one cursor increment on every back edge"},
		{"helper changes cursor on back edge", "func (r *Record) f() int { for r.value < len(r.items) { r.track(); r.value++ }; return r.value }; func (r *Record) track() { r.advance() }; func (r *Record) advance() { r.value++ }", "one cursor increment on every back edge"},
		{"changes input on back edge", "func (r *Record) f(items []int) int { for r.value < len(r.items) { r.items = items; r.value++ }; return r.value }", "one cursor increment on every back edge"},
	} {
		t.Run(test.name, func(t *testing.T) {
			dir := newModule(t)
			writeFile(t, filepath.Join(dir, "input.go"), "package sample\ntype Record struct { value int; items []int }\nvar escaped *Record\n//golean:verify\n"+test.body+"\n")
			if _, err := transpile.Generate(dir); err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("got %v, want %q", err, test.want)
			}
		})
	}
}

func TestNestedRecordDefinitionOrder(t *testing.T) {
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "input.go"), `package sample
type AOuter struct { ZInner }
type ZInner struct { X int64 }
//golean:verify
func selectX(s AOuter) int64 { return s.X }
`)
	outputs, err := transpile.Generate(dir)
	if err != nil {
		t.Fatal(err)
	}
	got := outputs[0].Source
	inner := strings.Index(got, "structure «example.test/sample».«input».«ZInner»")
	outer := strings.Index(got, "structure «example.test/sample».«input».«AOuter»")
	if inner < 0 || outer < 0 || inner >= outer {
		t.Fatalf("expected the embedded structure before its parent:\n%s", got)
	}
}

func TestIndexesTemporaryArrayValue(t *testing.T) {
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "input.go"), `package sample
func copyValue(xs [4]int64) [4]int64 { return xs }

//golean:verify
func at(xs [4]int64, index int) int64 { return copyValue(xs)[index] }
`)
	outputs, err := transpile.Generate(dir)
	if err != nil {
		t.Fatal(err)
	}
	got := outputs[0].Source
	if !strings.Contains(got, "Vector Int64 4") || !strings.Contains(got, ".toArray)[") {
		t.Fatalf("missing checked indexing of the array value:\n%s", got)
	}
}

func TestCountedLoopPreservesItsUpdate(t *testing.T) {
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "input.go"), `package sample
//golean:verify
func power(seed, factor int64, count uint8) int64 {
	result := seed
	for i := uint8(0); i < count; i++ {
		result *= factor
	}
	return result
}
`)
	outputs, err := transpile.Generate(dir)
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{
		"«power$loop»", "Nat → Int64 → Int64", " * «v1_factor»", "«v2_count»).toNat «v0_seed»",
	} {
		if !strings.Contains(outputs[0].Source, want) {
			t.Errorf("missing %q in output:\n%s", want, outputs[0].Source)
		}
	}
}

func TestRangeFoldPreservesSeedAndUpdate(t *testing.T) {
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "input.go"), `package sample
//golean:verify
func accumulate(input []int64, seed, scale int64) int64 {
	total := seed
	for _, item := range input {
		total -= item * scale
	}
	return total
}
`)
	outputs, err := transpile.Generate(dir)
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{"List.foldl (fun", " * «v2_scale»", " - ", ") «v1_seed» «v0_input»"} {
		if !strings.Contains(outputs[0].Source, want) {
			t.Errorf("missing %q in output:\n%s", want, outputs[0].Source)
		}
	}
}

func TestFreshSliceBuildPreservesElementUpdate(t *testing.T) {
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "input.go"), `package sample
//golean:verify
func double(xs []int64) []int64 {
	result := make([]int64, len(xs))
	for i, value := range xs {
		result[i] = 2 * value
	}
	return result
}
`)
	outputs, err := transpile.Generate(dir)
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{"return List.map (fun", "Int64.ofInt (2)", " * "} {
		if !strings.Contains(outputs[0].Source, want) {
			t.Errorf("missing %q in output:\n%s", want, outputs[0].Source)
		}
	}
}

func TestCommaOKMapLookup(t *testing.T) {
	dir := newModule(t)
	t.Setenv("GOARCH", "386")
	writeFile(t, filepath.Join(dir, "input.go"), `package sample
//golean:verify
func read(m map[uint8]int, key uint8) int {
	value, ok := m[key]
	if ok { return value }
	return value + 1
}
//golean:verify
func readNil(key uint8) int { return read(nil, key) }
`)
	outputs, err := transpile.Generate(dir)
	if err != nil {
		t.Fatal(err)
	}
	got := outputs[0].Source
	for _, want := range []string{"List (UInt8 × Int32)", "(Option Int32)", "Option.getD", "Int32.ofInt (0)", "Option.isSome", "«read» []"} {
		if !strings.Contains(got, want) {
			t.Errorf("missing %q in output:\n%s", want, got)
		}
	}
	if strings.Count(got, "List.lookup") != 1 {
		t.Errorf("expected one lookup shared by the value and presence results:\n%s", got)
	}
}

func TestFreshMapReadsCurrentState(t *testing.T) {
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "input.go"), `package sample
//golean:verify
func build(k uint8, value int32) map[uint8]int32 {
	m := make(map[uint8]int32)
	m[k] = value
	prior, _ := m[k]
	m[k] = prior + 1
	return m
}
`)
	outputs, err := transpile.Generate(dir)
	if err != nil {
		t.Fatal(err)
	}
	got := outputs[0].Source
	for _, want := range []string{"Option (List (UInt8 × Int32))", "(List.lookup «v0_k» «v3_t0»)", "(«v3_t0»).filter"} {
		if !strings.Contains(got, want) {
			t.Errorf("missing %q in output:\n%s", want, got)
		}
	}
}

const genericSliceBuilder = `
func transform[T any](xs []T, apply func(T) T) []T {
	dst := make([]T, len(xs))
	for i, value := range xs {
		dst[i] = apply(value)
	}
	return dst
}
`

func TestGenericSliceBuilderInstances(t *testing.T) {
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "input.go"), `package sample
//golean:verify
func wide(xs []int64) []int64 { return transform(xs, increment) }
//golean:verify
func narrow(xs []uint8) []uint8 { return transform(xs, func(x uint8) uint8 { return x * 3 }) }
//golean:verify
func wideAgain(xs []int64) []int64 { return transform(xs, func(x int64) int64 { return x - 1 }) }
func increment(x int64) int64 { return x + 1 }
`+genericSliceBuilder)
	outputs, err := transpile.Generate(dir)
	if err != nil {
		t.Fatal(err)
	}
	got := outputs[0].Source
	for _, want := range []string{"Int64 → Int64", "UInt8 → UInt8", "«increment»", "«wideAgain$1»", "UInt8.ofNat (3)"} {
		if !strings.Contains(got, want) {
			t.Errorf("missing %q in output:\n%s", want, got)
		}
	}
	if strings.Count(got, "return List.map") != 2 {
		t.Errorf("expected one slice builder per concrete type:\n%s", got)
	}
}

func TestRejectGenericSliceCallbacks(t *testing.T) {
	for _, test := range []struct{ name, body, want string }{
		{"unknown callback", "func f(xs []int64, apply func(int64) int64) []int64 { return transform(xs, apply) }", "parameter must have a supported"},
		{"nil callback", "func f(xs []int64) []int64 { return transform(xs, nil) }", "statically known function"},
	} {
		t.Run(test.name, func(t *testing.T) {
			dir := newModule(t)
			writeFile(t, filepath.Join(dir, "input.go"), "package sample\n//golean:verify\n"+test.body+"\n"+genericSliceBuilder)
			if _, err := transpile.Generate(dir); err == nil || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("got %v, want %q", err, test.want)
			}
		})
	}
}

func TestChainRecursionPreservesBaseAndStep(t *testing.T) {
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "input.go"), `package sample
type cell struct { link *cell; weight int64 }
//golean:verify
func weighted(p *cell) int64 {
	if nil != p {
		return p.weight * 2 + weighted(p.link)
	}
	return 7
}
`)
	outputs, err := transpile.Generate(dir)
	if err != nil {
		t.Fatal(err)
	}
	got := outputs[0].Source
	for _, want := range []string{"| [] => (Int64.ofInt (7))", " :: ", "(«weighted» ", "Int64.ofInt (2)", " * ", " + ", "termination_by structural"} {
		if !strings.Contains(got, want) {
			t.Errorf("missing %q in output:\n%s", want, got)
		}
	}
}

func TestRejectUnsupportedSSA(t *testing.T) {
	tests := []struct {
		name, source, want string
	}{
		{"bitwise or", "func f(x int64) int64 { return x | 2 }", "unsupported runtime operation |"},
		{"parameter", "func f(x complex64) int64 { return 0 }", "parameter must have a supported scalar or record type"},
		{"result", "func f(x int64) complex64 { return 1 }", "with supported results"},
		{"unsupported second result", "func f(x int64) (int64, complex64) { return x, 1 }", "with supported results"},
		{"second result escapes pointer", "func f(p *point) (bool, *point) { return true, p }; type point struct { X int64 }", "record pointers may not escape as results"},
		{"borrowed second map result", "func f(m map[int64]int64) (bool, map[int64]int64) { return true, m }", "map results require a fresh local allocation"},
		{"borrowed second slice result", "func f(xs []int64) (bool, []int64) { return true, xs }", "slice results require a validated fresh construction"},
		{"duplicate local maps", "func f() (map[int64]int64, map[int64]int64) { m := make(map[int64]int64); return m, m }", "map results require a fresh local allocation"},
		{"duplicate forwarded maps", "func f() (map[int64]int64, map[int64]int64) { m := fresh(); return m, m }; func fresh() map[int64]int64 { return make(map[int64]int64) }", "aggregate results must have distinct fresh sources"},
		{"duplicate forwarded slices", "func f(xs []int64) ([]int64, []int64) { ys, _ := fresh(xs); return ys, ys }; func fresh(xs []int64) ([]int64, int) { ys := make([]int64, len(xs)); n := copy(ys, xs); return ys, n }", "aggregate results must have distinct fresh sources"},
		{"multi-result callback", "func f(g func(int64) (int64, bool), x int64) int64 { y, _ := g(x); return y }", "parameter must have a supported"},
		{"dynamic any", "func f(x any) int64 { return 0 }", "parameter must have a supported scalar or record type"},
		{"record escape", "func f(x int64) int64 { p := point{X: x}; saved = &p; return p.X }; type point struct { X int64 }; var saved *point", "local record address must not escape"},
		{"record pointer mutation", "func f(p *point) int64 { p.X = 1; return p.X }; type point struct { X int64 }", "unsupported store"},
		{"record pointer escape", "func f(p *point) *point { return p }; type point struct { X int64 }", "record pointers may not escape as results"},
		{"record pointer identity", "func f(p, q *point) bool { return p == q }; type point struct { X int64 }", "unsupported runtime operation =="},
		{"caller slice mutation", "func f(xs []int64) int64 { xs[0] = 1; return xs[0] }", "slice elements are read-only"},
		{"slice field mutation", "func f(x data) int64 { x.values[0] = 1; return x.values[0] }; type data struct { values []int64 }", "slice elements are read-only"},
		{"recursive slice field", "func f(x data) int { return len(x.values) }; type data struct { values []data }", "parameter must have a supported"},
		{"caller map mutation", "func f(m map[int64]int64, k int64) int64 { m[k] = 1; return 1 }", "map writes require a validated fresh map"},
		{"caller map return", "func f(m map[int64]int64) map[int64]int64 { return m }", "map results require a fresh local allocation"},
		{"nil map mutation", "func f(k int64) int64 { var m map[int64]int64; m[k] = 1; return k }", "map writes require a validated fresh map"},
		{"map escapes through call", "func f(k int64) map[int64]int64 { m := make(map[int64]int64); m[k] = observe(m, k); return m }; func observe(m map[int64]int64, k int64) int64 { v, _ := m[k]; return v }", "map results require a fresh local allocation"},
		{"map literal with potentially duplicate keys", "func f(a, b int64) map[int64]int64 { return map[int64]int64{a: 1, b: 2} }", "map results require a fresh local allocation"},
		{"map return from different allocations", "func f(flag bool) map[int64]int64 { m := make(map[int64]int64); if flag { return make(map[int64]int64) }; return m }", "map results require a fresh local allocation"},
		{"map nil test", "func f(m map[int64]int64) bool { return m == nil }", "unsupported runtime operation =="},
		{"noninteger map key", "func f(m map[string]int64) int64 { v, _ := m[\"key\"]; return v }", "parameter must have a supported"},
		{"array escape", "func f(xs [4]int64) int64 { saved = &xs; return xs[0] }; var saved *[4]int64", "local array address must not escape"},
		{"array field element escape", "func f(x data) int64 { saved = &x.values[0]; return x.values[0] }; type data struct { values [4]int64 }; var saved *int64", "element addresses must stay local"},
		{"caller slice escape", "func f(xs []int64) []int64 { return xs }", "slice results require a validated fresh construction"},
		{"different slice length", "func f(xs []int64) []int64 { dst := make([]int64, len(xs)+1); for i, v := range xs { dst[i] = v }; return dst }", "slice results require a validated fresh construction"},
		{"slice write repeated on a branch", "func f(xs []int64) []int64 { dst := make([]int64, len(xs)); for i, x := range xs { dst[i] = x; if x < 0 { dst[i] = 0 } }; return dst }", "slice results require a validated fresh construction"},
		{"slice write skipped on a branch", "func f(xs []int64) []int64 { dst := make([]int64, len(xs)); for i, x := range xs { if x != 0 { dst[i] = x } }; return dst }", "slice results require a validated fresh construction"},
		{"index bounded by different slice", "func f(xs, ys []int64) int64 { var total int64; for i := 0; i < len(xs); i++ { total += ys[i] }; return total }", "control-flow loops are unsupported"},
		{"wrong slice write index", "func f(xs []int64) []int64 { dst := make([]int64, len(xs)); for _, v := range xs { dst[0] = v }; return dst }", "slice results require a validated fresh construction"},
		{"fresh slice escapes before return", "func f(xs []int64) []int64 { dst := make([]int64, len(xs)); save = dst; for i, v := range xs { dst[i] = v }; return dst }; var save []int64", "slice results require a validated fresh construction"},
		{"constrained generic", "func f[T interface{ M() }](x T) T { return x }", "must use the unrestricted any constraint"},
		{"closure writes capture", "func f(x int64) int64 { add := func() int64 { x++; return x }; return add() }", "closure captures may only be read"},
		{"parent writes capture", "func f(x int64) int64 { read := func() int64 { return x }; x++; return read() }", "unsupported local allocation or mutable capture"},
		{"closure initialization does not dominate", "func f(flag bool, x int64) int64 { var y int64; if flag { y = x }; read := func() int64 { return y }; return read() }", "unsupported local allocation or mutable capture"},
		{"closure escapes", "func f(x int64) int64 { saved = func() int64 { return x }; return x }; var saved func() int64", "closures may only be used in direct calls"},
		{"float32 multiply", "func f(x float32) float32 { return x * 2 }", "unsupported runtime operation *"},
		{"float64 addition", "func f(x float64) float64 { return x + 2 }", "unsupported runtime operation +"},
		{"loop", "func f(x int64) int64 { for x > 0 { x = x - 1 }; return x }", "control-flow loops are unsupported"},
		{"counted loop with nonunit step", "func f(x int64, count uint8) int64 { var acc int64; for i := uint8(0); i < count; i += 2 { acc += x }; return acc }", "control-flow loops are unsupported"},
		{"counted loop with changing bound", "func f(x int64, count uint8) int64 { var acc int64; for i := uint8(0); i < count; i++ { acc += x; count-- }; return acc }", "control-flow loops are unsupported"},
		{"range reads different index", "func f(xs []int64) int64 { var acc int64; for i := range xs { acc += xs[i+1] }; return acc }", "control-flow loops are unsupported"},
		{"range mutates slice", "func f(xs []int64) int64 { var acc int64; for i, v := range xs { xs[i] = 0; acc += v }; return acc }", "control-flow loops are unsupported"},
		{"global", "func f() int64 { return n }; var n int64", "unsupported unary operation *"},
		{"recursion", "func f(x int64) int64 { return f(x) }", "recursive calls are unsupported"},
		{"linked list recurses on original", "func f(p *cell) int64 { if p == nil { return 0 }; return 1+f(p) }; type cell struct { next *cell; value int64 }", "linked-list inputs require nil-guarded read-only recursion"},
		{"linked list without nil guard", "func f(p *cell) int64 { return 1+f(p.next) }; type cell struct { next *cell; value int64 }", "linked-list inputs require nil-guarded read-only recursion"},
		{"linked list skips nullable link", "func f(p *cell) int64 { if p == nil { return 0 }; return 1+f(p.next.next) }; type cell struct { next *cell; value int64 }", "linked-list inputs require nil-guarded read-only recursion"},
		{"linked list mutation", "func f(p *cell) int64 { if p == nil { return 0 }; p.value++; return f(p.next) }; type cell struct { next *cell; value int64 }", "linked-list inputs require nil-guarded read-only recursion"},
		{"panic", "func f(x int64) int64 { panic(x) }", "unsupported SSA instruction"},
	}
	for _, test := range tests {
		t.Run(test.name, func(t *testing.T) {
			path := filepath.Join(newModule(t), "input.go")
			writeFile(t, path, "package sample\n//golean:verify\n"+test.source+"\n")
			_, err := transpile.Generate(filepath.Dir(path))
			if err == nil || !strings.Contains(err.Error(), path+":3:") || !strings.Contains(err.Error(), test.want) {
				t.Fatalf("got %v, want a source position and %q", err, test.want)
			}
		})
	}
}

func TestTransitiveImportedCalls(t *testing.T) {
	dir := newModule(t)
	path := filepath.Join(dir, "input.go")
	writeFile(t, path, `package sample
import "example.test/sample/middle"
//golean:verify
func Root(x int64) int64 { return middle.Add(x) + middle.Add(x) }
`)
	writeFile(t, filepath.Join(dir, "middle", "middle.go"), `package middle
import "example.test/sample/leaf"
func Add(x int64) int64 { return leaf.Add(x) }
`)
	leaf := filepath.Join(dir, "leaf", "leaf.go")
	writeFile(t, leaf, "package leaf\nfunc Add(x int64) int64 { return x + 1 }\n")

	outputs, err := transpile.Generate(dir)
	if err != nil {
		t.Fatal(err)
	}
	got := outputs[0].Source
	leafDef := "def «example.test/sample».«input».Dependencies.«example.test/sample/leaf».«Add»"
	middleDef := "def «example.test/sample».«input».Dependencies.«example.test/sample/middle».«Add»"
	rootDef := "def «example.test/sample».«input».«Root»"
	if strings.Count(got, leafDef) != 1 || strings.Count(got, middleDef) != 1 ||
		strings.Index(got, leafDef) >= strings.Index(got, middleDef) ||
		strings.Index(got, middleDef) >= strings.Index(got, rootDef) {
		t.Fatalf("expected one definition per function in dependency order:\n%s", got)
	}

	writeFile(t, leaf, "package leaf\nfunc Add(x int64) int64 { return x | 2 }\n")
	_, err = transpile.Generate(dir)
	for _, want := range []string{"call to example.test/sample/middle.Add", "call to example.test/sample/leaf.Add", "unsupported runtime operation |"} {
		if err == nil || !strings.Contains(err.Error(), want) {
			t.Errorf("got %v, want %q in the call chain", err, want)
		}
	}
}

func TestOrdinaryGenericInstancesAndSliceLength(t *testing.T) {
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "input.go"), `package sample
func identity[T any](x T) T { return x }
//golean:verify
func length(xs []int64) int {
	if identity[bool](true) {
		return identity[int](len(xs))
	}
	return 0
}
`)
	outputs, err := transpile.Generate(dir)
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{"identity$instance0", "identity$instance1", ".length"} {
		if !strings.Contains(outputs[0].Source, want) {
			t.Errorf("missing %q in output:\n%s", want, outputs[0].Source)
		}
	}
}

func TestLocalRecordFieldUpdates(t *testing.T) {
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "input.go"), `package sample
type point struct { X, Y int64 }
type outer struct { Inner point; Flag bool }
//golean:verify
func update(flag bool) int64 {
	var r outer
	r.Inner.X = 4
	if flag {
		r.Inner.X = 7
	}
	return r.Inner.X + r.Inner.Y
}
`)
	outputs, err := transpile.Generate(dir)
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{"with", "Int64.ofInt (0)", "if "} {
		if !strings.Contains(outputs[0].Source, want) {
			t.Errorf("missing %q in output:\n%s", want, outputs[0].Source)
		}
	}
	checkGeneratedLean(t, dir, outputs[0].Path, outputs[0].Source, `
open GoLean.«example.test/sample».input
example : update true = 7 := by decide
example : update false = 4 := by decide
`)
}

func TestIndexedTraversalsAndConditionalMapUpdate(t *testing.T) {
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "input.go"), `package sample
//golean:verify
func sum(xs []int64) int64 {
	var result int64
	for i := 0; i < len(xs); i++ {
		result += xs[i]
	}
	return result
}
//golean:verify
func double(xs []int64) []int64 {
	result := make([]int64, len(xs))
	for i := 0; i < len(xs); i++ {
		result[i] = 2 * xs[i]
	}
	return result
}
//golean:verify
func literal(first, second int64) map[int64]int64 {
	return map[int64]int64{1: first, 2: second}
}
//golean:verify
func mapWithBranch(key int64, set bool) map[int64]int64 {
	result := make(map[int64]int64, 2)
	if set {
		result[key] = 3
	}
	current := result[key]
	result[key] = current + 1
	return result
}
`)
	outputs, err := transpile.Generate(dir)
	if err != nil {
		t.Fatal(err)
	}
	for _, want := range []string{"List.foldl", "List.map", "if ", "List.lookup «v0_key» «v3_t0»", "List.lookup «v0_key» «v2_t0»"} {
		if !strings.Contains(outputs[0].Source, want) {
			t.Errorf("missing %q in output:\n%s", want, outputs[0].Source)
		}
	}
	checkGeneratedLean(t, dir, outputs[0].Path, outputs[0].Source, `
open GoLean.«example.test/sample».input
example : mapWithBranch 4 true = some [(4, 4)] := by decide
example : mapWithBranch 4 false = some [(4, 1)] := by decide
example : (literal 7 8).bind (List.lookup 2) = some 8 := by decide
example : sum [1, 2, 3] = 6 := by decide
example : double [1, 2, 3] = some [2, 4, 6] := by decide
`)
}

func TestGeneralizedTraversalsInLean(t *testing.T) {
	dir := newModule(t)
	writeFile(t, filepath.Join(dir, "input.go"), `package sample
//golean:verify
func convert(xs []int64) []bool {
	out := make([]bool, len(xs))
	for i := 0; i < len(xs); i++ {
		x := xs[i]
		if x < 0 {
			x = 0
		}
		out[i] = x != 0
	}
	return out
}
//golean:verify
func clamp(xs []int64) []int64 {
	out := make([]int64, len(xs))
	for i, x := range xs {
		if x < 0 {
			out[i] = 0
		} else {
			out[i] = x
		}
	}
	return out
}
//golean:verify
func offset(xs []int64, delta int64) []int64 {
	return transform(xs, func(x int64) int64 { return x + delta })
}
//golean:verify
func divide(xs []int64) []int64 {
	return transform(xs, reciprocal)
}
//golean:verify
func divideDirect(xs []int64) []int64 {
	result := make([]int64, len(xs))
	for i, x := range xs {
		result[i] = reciprocal(x)
	}
	return result
}
func reciprocal(x int64) int64 { return 12 / x }
type node struct { next *node; weight int32; metadata string }
//golean:verify
func weighted(p *node, scale int32) int32 {
	if p == nil { return 0 }
	return p.weight*scale + weighted(p.next, scale)
}
//golean:verify
func sumReciprocals(xs []int64) int64 {
	var total int64
	for _, value := range xs {
		total += reciprocal(value)
	}
	return total
}
//golean:verify
func summarize(xs []int64) int64 {
	var total, count int64
	for _, x := range xs {
		if x > 0 {
			total += x
			count++
		}
	}
	return total + count
}
//golean:verify
func counter(start, limit int, seed int64) int64 {
	end := limit + 1
	state := seed * 2
	for i := start; end > i; i++ {
		state += 3
	}
	return state - 1
}
//golean:verify
func countSelected(start, end int, initial bool) int {
	total, selected := 0, 0
	accept := initial
	for i := start; i < end; i++ {
		if accept {
			total += i
			selected++
		}
		accept = !accept
	}
	return total + selected
}
type batch struct { cursor int; items []int; processed int }
func (b *batch) track() { b.processed++ }
//golean:verify
func (b *batch) run() int {
	b.processed = 0
	for b.cursor < len(b.items) {
		b.track()
		b.cursor++
	}
	return b.processed
}
`+genericSliceBuilder)
	outputs, err := transpile.Generate(dir)
	if err != nil {
		t.Fatal(err)
	}
	checkGeneratedLean(t, dir, outputs[0].Path, outputs[0].Source, `
open GoLean.«example.test/sample».input
example : weighted [2, 3] 4 = 20 := by decide
example : convert [-1, 2, 3] = some [false, true, true] := by decide
example : clamp [-1, 2, 3] = some [0, 2, 3] := by decide
example : offset [1, 3] 4 = some [5, 7] := by decide
example : divide [2, 3] = some [6, 4] := by decide
example : divide [2, 0, 3] = none := by decide
example : divideDirect [2, 0, 3] = none := by decide
example : divideDirect [] = some [] := by decide
example : sumReciprocals [2, 3] = some 10 := by decide
example : sumReciprocals [2, 0, 3] = none := by decide
example : summarize [-4, 2, 3] = 7 := by decide
example : summarize [] = 0 := by decide
example : counter 2 3 5 = 15 := by decide
example : counter 2 (-3) 5 = 9 := by decide
example : countSelected 2 6 true = 8 := by decide
example : countSelected 6 2 true = 0 := by decide
example : («batch$run» (some { «field:cursor» := 0, «field:items» := some [10, 20], «field:processed» := 99 })).map Prod.snd = some 2 := by decide
`)
}

func checkGeneratedLean(t *testing.T, dir, path, definitions, assertions string) {
	t.Helper()
	lean, err := exec.LookPath("lean")
	if err != nil {
		t.Log("Lean is unavailable on PATH")
		return
	}
	source := definitions + assertions
	writeFile(t, path, source)
	if result, err := exec.Command(lean, "--root="+dir, path).CombinedOutput(); err != nil {
		t.Fatalf("Lean failed: %v\n%s\n%s", err, result, source)
	}
}
