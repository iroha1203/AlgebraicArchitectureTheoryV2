import ResearchLean.AG.RealizationReconstruction.FiniteAxisFoldSignatureFiberPresentation
import Formal.Util.AssertStandardAxioms

/-!
# Fixed singleton and coefficient rigidity in the residual kernel

The residual kernel left by the finite axis and signature projections still
quantifies over every automorphism of the actual normalized endpoint.  This
module discharges two complete computational components forced by the fixed
finite-axis-fold input: the singleton invariant-index map and the unital
endomorphism of the coefficient ring `Int`.

No object map, operation map, context equivalence, Atom equivalence, or local
geometry comparison is supplied as an input.  Those remaining components are
not claimed to be rigid or source-covered here.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport

noncomputable section

private abbrev ResidualAutomorphism :=
  FiniteAxisFoldNormalizedAxisSignatureKernel

/-- Membership in the first kernel fixes the complete global axis function. -/
theorem finiteAxisFoldResidual_axisMap_eq_id
    (remainder : ResidualAutomorphism) :
    remainder.1.1.hom.f.hom.base.upper.axisMap = _root_.id :=
  finiteAxisFoldNormalizedAxisKernel_axisMap remainder.1

/-- Membership in the second kernel fixes every coordinate equivalence, not
only the distinguished diagonal values used to define its finite subgroup. -/
theorem finiteAxisFoldResidual_coordinateEquiv_eq_refl
    (remainder : ResidualAutomorphism) (axis : Fin 3) :
    remainder.1.1.hom.f.hom.base.upper.coordinateEquiv axis =
      Equiv.refl (Fin 3) := by
  apply Equiv.ext
  intro coordinate
  have kernelEquality := MonoidHom.mem_ker.mp remainder.2
  have evaluated := congrArg
    (fun permutation : FiniteAxisFoldSignatureFiberPermutation =>
      permutation.1 (axis, coordinate)) kernelEquality
  exact congrArg Prod.snd evaluated

/-- The invariant-index function of every residual normalized automorphism is
the identity on the fixed singleton index type. -/
theorem finiteAxisFoldResidual_invariantMap_eq_id
    (remainder : ResidualAutomorphism) :
    remainder.1.1.hom.f.hom.base.upper.invariantMap = _root_.id := by
  funext index
  cases index
  rfl

/-- A unital ring endomorphism of `Int` is uniquely the identity; hence the
full coefficient component of every residual normalized automorphism is fixed. -/
theorem finiteAxisFoldResidual_coefficientHom_eq_id
    (remainder : ResidualAutomorphism) :
    remainder.1.1.hom.f.hom.geometry.coefficientHom = RingHom.id Int := by
  exact RingHom.ext_int _ _

end


end AAT.AG.RealizationReconstruction

#assert_standard_axioms_only AAT.AG.RealizationReconstruction
