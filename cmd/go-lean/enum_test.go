package main

import (
	"os/exec"
	"strings"
	"testing"
)

const enumFixture = `//golean:generate:enum Expr { Lit default, Add }
package model

type Lit struct { Value byte }
type Children struct { Left, Right Expr }
type Add struct { Children Children }

func initial() Expr {
 var zero Expr
 return zero
}

func continued(expr Expr) byte {
 switch value := expr.Case().(type) {
 case Lit:
  return value.Value
 case Add:
 }
 return 9
}

//golean:termination:by sizeOf expr
func evaluate(expr Expr) byte {
 switch value := expr.Case().(type) {
 case Lit:
  return value.Value
 case Add:
  return evaluate(value.Children.Left) + evaluate(value.Children.Right)
 }
 return 0
}

//golean:verify enumZero : «initial» = Expr.Lit (Lit.mk 0)
//golean:verify enumResult : «demo» = 16
func demo() byte {
 left := NewExprLit(Lit{Value: 3})
 right := NewExprLit(Lit{Value: 4})
 tree := NewExprAdd(Add{Children: Children{Left: left, Right: right}})
 return evaluate(tree) + continued(tree)
}
`

func TestGeneratedEnum(t *testing.T) {
	workspace(t, false)
	put(t, "model.go", enumFixture)
	if err := command("transpile", "."); err == nil || !strings.Contains(err.Error(), "go-lean generate") {
		t.Fatalf("missing enum output: %v", err)
	}
	if err := command("generate", "."); err != nil {
		t.Fatal(err)
	}
	generated := get(t, "lean.gen.go")
	if err := command("generate", "."); err != nil {
		t.Fatal(err)
	}
	if get(t, "lean.gen.go") != generated {
		t.Fatal("unstable enum output")
	}
	put(t, "lean.gen.go", generated+"\n// modified\n")
	if err := command("transpile", "."); err == nil || !strings.Contains(err.Error(), "stale") {
		t.Fatalf("modified enum output: %v", err)
	}
	if err := command("generate", "."); err != nil {
		t.Fatal(err)
	}
	if err := command("transpile", "."); err != nil {
		t.Fatal(err)
	}
	put(t, "runtime_test.go", `package model
import "testing"

func TestRuntime(t *testing.T) {
 if initial().Case().(Lit).Value != 0 || (Expr{}).Case().(Lit) != NewExprLit(Lit{}).Case().(Lit) || demo() != 16 {
  t.Fatal("unexpected enum evaluation")
 }
}
`)
	if output, err := exec.Command("go", "test", ".").CombinedOutput(); err != nil {
		t.Fatalf("%v\n%s", err, output)
	}
	if _, err := exec.LookPath("lake"); err != nil {
		t.Skip("lake is unavailable")
	}
	proofs := "model_proofs.lean"
	text := strings.Replace(get(t, proofs), "  sorry", "  rfl", 1)
	text = strings.Replace(text, "  sorry", "  simp [Laws.«enumResult», demo, evaluate.eq_def, continued]", 1)
	put(t, proofs, text)
	if err := command("verify", "."); err != nil {
		t.Fatal(err)
	}
}

func TestEnumRejections(t *testing.T) {
	for _, tc := range []struct{ name, suffix, want string }{
		{"forge", "func forge() Expr { return Expr{payload: uint8(99)} }", "generated constructors"},
		{"read private storage", "func leak(x Expr) byte { var _ = x.payload; return 0 }", "private to lean.gen.go"},
		{"escape case", "func escape(x Expr) byte { var _ = x.Case(); return 0 }", "only supported in an exhaustive enum switch"},
		{"missing match case", "func missing(x Expr) byte { switch x.Case().(type) { case Lit: return 0 }; return 1 }", "missing Add"},
		{"default match case", "func extra(x Expr) byte { switch x.Case().(type) { case Lit: return 0; case Add: return 1; default: return 2 } }", "no default"},
		{"multiple defaults", "", "exactly one default"},
		{"zero cycle", "", "cyclic enum zero value"},
	} {
		t.Run(tc.name, func(t *testing.T) {
			workspace(t, false)
			source := enumFixture + tc.suffix
			switch tc.name {
			case "multiple defaults":
				source = strings.Replace(source, "Lit default, Add", "Lit default, Add default", 1)
			case "zero cycle":
				source = strings.Replace(source, "Lit default, Add", "Lit, Add default", 1)
			}
			put(t, "model.go", source)
			err := command("generate", ".")
			if err == nil {
				err = command("transpile", ".")
			}
			if err == nil || !strings.Contains(err.Error(), tc.want) {
				t.Fatalf("wanted %q, got %v", tc.want, err)
			}
		})
	}
}

func TestBoxedEnumDefault(t *testing.T) {
	if _, err := exec.LookPath("lake"); err != nil {
		t.Skip("lake is unavailable")
	}
	workspace(t, true)
	put(t, "model.go", `//golean:generate:enum Tree { Branch default, Leaf }
package model
import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

type Branch struct { Next lean.Box[Tree] }
type Leaf byte

//golean:termination:by sizeOf tree
func count(tree Tree) byte {
 switch item := tree.Case().(type) {
 case Branch:
  if item.Next.IsSome() {
   return count(item.Next.Get()) + 1
  }
  return 0
 case Leaf:
  return 1
 }
 return 0
}

type Root struct { Tree Tree }

//golean:verify boxedZero : demo = 3
func demo() byte {
 empty := lean.Box[Root]{}
 root := empty.Get()
 example := NewTreeBranch(Branch{Next: lean.NewBox(NewTreeLeaf(0))})
 return count(root.Tree) + count(example) + count(NewTreeLeaf(0))
}
`)
	if err := command("generate", "."); err != nil {
		t.Fatal(err)
	}
	if err := command("transpile", "."); err != nil {
		t.Fatal(err)
	}
	proof := "model_proofs.lean"
	put(t, proof, strings.Replace(get(t, proof), "  sorry", "  simp [Laws.«boxedZero», demo, count.eq_def]", 1))
	if err := command("verify", "."); err != nil {
		t.Fatal(err)
	}
}
