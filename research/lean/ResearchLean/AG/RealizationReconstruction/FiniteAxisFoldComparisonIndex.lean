import ResearchLean.AG.RealizationReconstruction.G122OriginalInput
import Formal.Util.AssertStandardAxioms

/-!
# Finite index of the fixed G-122 comparison cases

The three comparison cases required by G-123(D) are indexed here by a finite
type and evaluated to the actual arrows constructed in G-122.  The
generated-cochain `barBeta` remains distinct from the five-factor `barAlpha`,
while the constant-one `barBeta` evaluates to that same `barAlpha`.  Thus the
case evaluation records their semantic equality and inequality; it does not
replace any arrow by a simpler witness.

## Implementation notes

The index type has exactly the three fixed cases and no completed arrow field.
Its evaluator names already-constructed outputs in the display-independent
generated-object category from `G122OriginalInput`; it is not a finite recipe
for constructing those arrows.  This case index neither restricts arbitrary
`GeometryTotalHom` values nor supplies an extension, fullness, faithfulness,
idempotent splitting, or retract-generation certificate.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory GeometryTransport

/-- The three card-mandated finite axis-fold comparison cases: the
unchanged five-factor comparison, the generated-cochain comparison, and the
constant-one comparison. -/
inductive FiniteAxisFoldComparisonCode
  /-- The unchanged actual five-factor comparison. -/
  | barAlpha
  /-- The actual comparison selected by the generated cochain. -/
  | generatedBarBeta
  /-- The actual comparison selected by the constant-one cochain. -/
  | identityBarBeta
  deriving DecidableEq, Fintype

namespace FiniteAxisFoldComparisonCode

/-- Evaluate a comparison-case index to the corresponding actual arrow between
the common endpoint packages.  The constant-one endpoint packages are
definitionally the same packages proved equal in Cycle 44, although their
generated-object tags remain distinct. -/
noncomputable def evaluate : FiniteAxisFoldComparisonCode →
    GeometryTotalHom
      ((G122GeneratedGeometryObject.direct
        finiteAxisFoldG122CellInput).package finiteAxisFoldG122FamilyInput)
      ((G122GeneratedGeometryObject.viaBase
        finiteAxisFoldG122CellInput).package finiteAxisFoldG122FamilyInput)
  | .barAlpha => G122GeneratedGeometryObject.barAlpha
      finiteAxisFoldG122FamilyInput finiteAxisFoldG122CellInput
  | .generatedBarBeta => G122GeneratedGeometryObject.barBeta
      finiteAxisFoldG122FamilyInput finiteAxisFoldG122CellInput
  | .identityBarBeta => G122GeneratedGeometryObject.barBeta
      finiteAxisFoldG122FamilyInput
      finiteAxisFoldIdentityCochainG122CellInput

/-- The `barAlpha` code evaluates to the actual five-factor comparison. -/
@[simp] theorem evaluate_barAlpha : evaluate .barAlpha =
    G122GeneratedGeometryObject.barAlpha finiteAxisFoldG122FamilyInput
      finiteAxisFoldG122CellInput :=
  rfl

/-- The generated-cochain code evaluates to the actual noninvertible
comparison, not to an identity or a replacement arrow. -/
@[simp] theorem evaluate_generatedBarBeta : evaluate .generatedBarBeta =
    G122GeneratedGeometryObject.barBeta finiteAxisFoldG122FamilyInput
      finiteAxisFoldG122CellInput :=
  rfl

/-- The constant-one code evaluates to the actual comparison generated from
the constant-one cochain on the same endpoint packages. -/
@[simp] theorem evaluate_identityBarBeta : evaluate .identityBarBeta =
    G122GeneratedGeometryObject.barBeta finiteAxisFoldG122FamilyInput
      finiteAxisFoldIdentityCochainG122CellInput :=
  rfl

/-- The generated-cochain comparison is distinct from the actual five-factor
comparison in the common underlying endpoint-package Hom type. -/
theorem generatedBarBeta_ne_barAlpha :
    evaluate .generatedBarBeta ≠ evaluate .barAlpha := by
  change G122GeneratedGeometryObject.barBeta finiteAxisFoldG122FamilyInput
      finiteAxisFoldG122CellInput ≠
    G122GeneratedGeometryObject.barAlpha finiteAxisFoldG122FamilyInput
      finiteAxisFoldG122CellInput
  intro equality
  apply finiteAxisFold_generatedGeometry_barBeta_not_isIso
  have alphaIso :=
    (G122GeneratedGeometryObject.barAlphaIso finiteAxisFoldG122FamilyInput
      finiteAxisFoldG122CellInput).isIso_hom
  exact equality.symm ▸ alphaIso

/-- The constant-one comparison case and the five-factor case evaluate to the
same actual arrow, recording only their syntactic provenance aliasing. -/
theorem evaluate_identityBarBeta_eq_barAlpha :
    evaluate .identityBarBeta = evaluate .barAlpha :=
  finiteAxisFold_identityCochain_barBeta_eq_barAlpha.trans
    finiteAxisFold_barAlpha_identityCochain.symm

/-- The exact case-index fiber over the five-factor comparison consists of the
`barAlpha` and constant-one comparison codes. -/
theorem evaluate_eq_barAlpha_iff (code : FiniteAxisFoldComparisonCode) :
    evaluate code = evaluate .barAlpha ↔
      code = .barAlpha ∨ code = .identityBarBeta := by
  cases code with
  | barAlpha => exact ⟨fun _ => Or.inl rfl, fun _ => rfl⟩
  | generatedBarBeta =>
      constructor
      · intro h
        exact (generatedBarBeta_ne_barAlpha h).elim
      · intro h
        rcases h with h | h <;> nomatch h
  | identityBarBeta =>
      constructor
      · intro _
        exact Or.inr rfl
      · intro _
        exact evaluate_identityBarBeta_eq_barAlpha

/-- The generated-cochain comparison has a singleton case-index fiber among the
three fixed codes. -/
theorem evaluate_eq_generatedBarBeta_iff
    (code : FiniteAxisFoldComparisonCode) :
    evaluate code = evaluate .generatedBarBeta ↔ code = .generatedBarBeta := by
  cases code with
  | barAlpha =>
      constructor
      · intro h
        exact (generatedBarBeta_ne_barAlpha h.symm).elim
      · intro h
        nomatch h
  | generatedBarBeta => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | identityBarBeta =>
      constructor
      · intro h
        exact (generatedBarBeta_ne_barAlpha
          (h.symm.trans evaluate_identityBarBeta_eq_barAlpha)).elim
      · intro h
        nomatch h

/-- The case evaluator is not injective: precisely the five-factor and
constant-one indices name the same semantic comparison.  This syntactic
aliasing is not the kernel-and-lift information loss required later by G-123. -/
theorem evaluate_not_injective : ¬ Function.Injective evaluate := by
  intro injective
  have codeEquality := injective evaluate_identityBarBeta_eq_barAlpha
  exact FiniteAxisFoldComparisonCode.noConfusion codeEquality

end FiniteAxisFoldComparisonCode

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
