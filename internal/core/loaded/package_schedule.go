package loaded

import "github.com/frederik-jatzkowski/go-lean/pkg/lean"

// PackageSchedule retains discovery order while visiting package declarations.
type PackageSchedule struct {
	Pending                        lean.Array[string]
	PackageIndex, DeclarationIndex uint
}

type PackageStep struct {
	Schedule    PackageSchedule
	Package     Package
	Declaration lean.Option[Declaration]
	Done        bool
}

// Enqueue records a discovered package when its declarations are modeled.
// The caller records the first discovery of each package.
//
//golean:export
func (s PackageSchedule) Enqueue(pkg Package) PackageSchedule {
	if !pkg.Modeled {
		return s
	}
	return PackageSchedule{Pending: s.Pending.Push(pkg.Path), PackageIndex: s.PackageIndex, DeclarationIndex: s.DeclarationIndex}
}

// NextDeclaration advances the source-order traversal. A step can finish a
// package without returning a declaration.
//
//golean:export
func (s PackageSchedule) NextDeclaration(source Program) PackageStep {
	path := s.Pending.Get(s.PackageIndex)
	if !path.IsSome() {
		return PackageStep{Schedule: s, Package: source.PackageOrMissing(""), Declaration: lean.None[Declaration](), Done: true}
	}
	pkg := source.PackageOrMissing(path.UnwrapOr(""))
	declaration := pkg.Declarations.Get(s.DeclarationIndex)
	if !declaration.IsSome() {
		next := PackageSchedule{Pending: s.Pending, PackageIndex: s.PackageIndex + 1, DeclarationIndex: 0}
		return PackageStep{Schedule: next, Package: pkg, Declaration: declaration, Done: false}
	}
	next := PackageSchedule{Pending: s.Pending, PackageIndex: s.PackageIndex, DeclarationIndex: s.DeclarationIndex + 1}
	return PackageStep{Schedule: next, Package: pkg, Declaration: declaration, Done: false}
}
