import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredComparatorInductionObstruction

/-!
# Non-axis collapse audit for the fixed authored support package

The fixed lax package inherits the singleton invariant index of the finite
model.  Equation-index transport, primitive Atom transport, and every
coordinate transport are equivalences by the exact-hom schema.  Consequently
none of those fields can provide the noninjective collapse sought as an
alternative to the obstructed axis-fold route.

This module is an elimination checkpoint.  It does not claim that every exact
endomorphism is classified by these fields; object and operation maps remain
to be audited before a global fixed-fixture reduction can be stated.
-/

namespace AAT.AG.DoctrineFiberProduct

open AtomFoundation

/-- Every exact endomorphism of the fixed package has the singleton invariant map. -/
theorem finiteAxisFoldSupportPackage_invariantMap_eq_id
    (hom : SignedExactCoreReadingHom finiteAxisFoldSupportPackage
      finiteAxisFoldSupportPackage) :
    hom.invariantMap = _root_.id := by
  funext index
  change PUnit at index
  cases index
  rfl

/-- Hence the invariant-index map cannot supply a collapse. -/
theorem finiteAxisFoldSupportPackage_invariantMap_injective
    (hom : SignedExactCoreReadingHom finiteAxisFoldSupportPackage
      finiteAxisFoldSupportPackage) :
    Function.Injective hom.invariantMap := by
  rw [finiteAxisFoldSupportPackage_invariantMap_eq_id hom]
  exact Function.injective_id

/-- The equation-index map cannot supply a collapse because it comes from an equivalence. -/
theorem finiteAxisFoldSupportPackage_equationMap_injective
    (hom : SignedExactCoreReadingHom finiteAxisFoldSupportPackage
      finiteAxisFoldSupportPackage) :
    Function.Injective hom.equationMap :=
  hom.equationEquiv.injective

/-- Primitive Atom transport is injective because exact morphisms store an equivalence. -/
theorem finiteAxisFoldSupportPackage_atomMap_injective
    (hom : SignedExactCoreReadingHom finiteAxisFoldSupportPackage
      finiteAxisFoldSupportPackage) :
    Function.Injective hom.atomMap :=
  hom.atomEquiv.injective

/-- Each dependent signature-coordinate transport is injective. -/
theorem finiteAxisFoldSupportPackage_coordinateEquiv_injective
    (hom : SignedExactCoreReadingHom finiteAxisFoldSupportPackage
      finiteAxisFoldSupportPackage)
    (axis : finiteAxisFoldSupportPackage.reading.signatureReading.Axis) :
    Function.Injective (hom.coordinateEquiv axis) :=
  (hom.coordinateEquiv axis).injective

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
