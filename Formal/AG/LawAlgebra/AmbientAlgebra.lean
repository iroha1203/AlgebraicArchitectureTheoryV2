import Formal.AG.LawAlgebra.Coordinate
import Mathlib.Algebra.MvPolynomial.Basic

namespace AAT.AG
namespace LawAlgebra

universe u v

/--
III.定義4.1: free typed commutative algebra over a coordinate type.

This is a definitional bridge to Mathlib's `MvPolynomial`. Later structural
relations quotient this algebra; law witness equations are not quotiented out
at the ambient stage.
-/
abbrev FreeCommAlg (Coord : Type u) (k : Type v) [CommSemiring k] : Type (max u v) :=
  MvPolynomial Coord k

/--
III.定義4.1: `FreeCommAlg_k(Coord_X(W))` for a selected coordinate family.

The bridge is intentionally definitional, so Mathlib's polynomial API is
available without a new free-algebra theory.
-/
abbrev FreeTypedCommAlg {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {W : Site.ArchitectureContext A} (F : CoordinateFamily W)
    (k : Type v) [CommSemiring k] : Type (max u v) :=
  FreeCommAlg F.CoordX k

namespace FreeTypedCommAlg

/-- III.定義4.1 bridge: the selected free algebra is exactly `MvPolynomial`. -/
theorem eq_mvPolynomial {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {W : Site.ArchitectureContext A} (F : CoordinateFamily W)
    (k : Type v) [CommSemiring k] :
    FreeTypedCommAlg F k = MvPolynomial F.CoordX k :=
  rfl

/-- III.定義4.1: the polynomial variable attached to a coordinate. -/
noncomputable def coordVar {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {W : Site.ArchitectureContext A} (F : CoordinateFamily W)
    (k : Type v) [CommSemiring k] (c : F.CoordX) : FreeTypedCommAlg F k :=
  MvPolynomial.X c

/-- III.定義4.1: variables are Mathlib `MvPolynomial.X`. -/
theorem coordVar_eq_X {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {W : Site.ArchitectureContext A} (F : CoordinateFamily W)
    (k : Type v) [CommSemiring k] (c : F.CoordX) :
    coordVar F k c = MvPolynomial.X c :=
  rfl

end FreeTypedCommAlg

end LawAlgebra
end AAT.AG
