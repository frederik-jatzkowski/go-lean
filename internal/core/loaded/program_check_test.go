package loaded

import (
	"testing"

	"github.com/frederik-jatzkowski/go-lean/pkg/lean"
)

func TestCheckRejectsProgramWithoutPublishingPartialResult(t *testing.T) {
	pkg := Package{
		Path: "example.test/model", Modeled: true,
		Declarations: lean.ArrayFromSlice([]Declaration{
			{Pos: "model.go:2:6", Object: 1},
			{Pos: "model.go:3:5", Object: 2},
			{Pos: "model.go:4:5", Object: 3},
		}),
	}
	program := Program{
		SelectedPackages: lean.ArrayFromSlice([]string{pkg.Path}),
		Packages:         lean.OrderedMap[string, Package]{}.Insert(pkg.Path, pkg),
		Objects: lean.ArrayFromSlice([]Object{
			{},
			{Kind: TypeName, Name: "Counter", Type: 1},
			{Kind: Variable, Name: "first"},
			{Kind: Variable, Name: "second"},
		}),
		Types: lean.ArrayFromSlice([]Type{{}, {Kind: BasicType, Basic: "uint8"}}),
	}

	checked := program.Check()
	if !checked.Complete {
		t.Fatal("checking exhausted its traversal bound")
	}
	issue := checked.Failure.Diagnostic
	if issue.Code != UnsupportedPackageVariable || issue.Pos != "model.go:3:5" {
		t.Fatalf("expected the first variable diagnostic, got %+v", issue)
	}
	if checked.Program.Packages.Size() != 0 {
		t.Fatal("checking returned partially validated packages")
	}
}
