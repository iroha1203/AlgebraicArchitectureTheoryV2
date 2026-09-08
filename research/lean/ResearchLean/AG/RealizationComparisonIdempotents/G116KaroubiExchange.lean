import ResearchLean.AG.RealizationComparisonIdempotents.G116KaroubiPlacement

/-!
# Realizing the G-116 Karoubi comparison from the raw mate

This file completes G-119(C).  It independently places the existing reversible
mate `α` in `Kar(Arr(CoreFiber NE))` with endpoint idempotents
`(β ≫ α⁻¹, E)`.  The exchange functor's normalized comparison is proved to be
the existing `β` Karoubi comparison placed in the preceding module.

## Implementation notes

The raw comparison is `α`, not `β`.  Its source idempotent is taken from the
existing G-116 source Karoubi object and its target idempotent is the existing
cell projector.  The Arrow square, normalized comparison, and final object
equality are derived from `β = α ≫ E`, invertibility of `α`, and idempotence of
`E`; none is supplied as a new premise or certificate.
-/

open CategoryTheory CategoryTheory.Idempotents

namespace AAT.AG.RealizationComparisonIdempotents

open AtomFoundation CrossStageCoherence TransportCoherence
open DoctrineFiberProduct

universe u

set_option maxHeartbeats 1000000

/-- The A-side object built from the raw reversible mate `α` and endpoint
idempotents `(β ≫ α⁻¹, E)`. -/
noncomputable def authoredDiagnosticRawIdempotentComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    Karoubi (Arrow
      (CoreFiber input.context.square.semantic.square.northeast)) where
  X := Arrow.mk ((authoredSupportCanonicalMate input.context).app cell)
  p := Arrow.homMk
    (authoredDiagnosticImageSourceKaroubi input cochain cell).p
    (authoredDiagnosticImageTargetKaroubi input cochain cell).p
    (by
      rw [authoredDiagnosticImageSourceKaroubi_p,
        authoredDiagnosticImageTargetKaroubi_p]
      simp only [Arrow.mk_hom, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
      exact authoredDiagnosticObjectCollapseComparisonAtCochain_app
        input cochain cell)
  idem := by
    apply Arrow.hom_ext
    · exact (authoredDiagnosticImageSourceKaroubi input cochain cell).idem
    · exact (authoredDiagnosticImageTargetKaroubi input cochain cell).idem

/-- Normalization rule: the raw comparison underlying the A-side object is
the existing reversible mate `α`. -/
@[simp]
theorem authoredDiagnosticRawIdempotentComparison_X_hom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    (authoredDiagnosticRawIdempotentComparison input cochain cell).X.hom =
      (authoredSupportCanonicalMate input.context).app cell :=
  rfl

/-- Normalization rule: the source idempotent is `α⁻¹β`, written in Lean's
composition order as `β ≫ α⁻¹`. -/
@[simp]
theorem authoredDiagnosticRawIdempotentComparison_p_left
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    (authoredDiagnosticRawIdempotentComparison input cochain cell).p.left =
      (authoredDiagnosticObjectCollapseComparisonAtCochain input cochain).app cell ≫
        inv ((authoredSupportCanonicalMate input.context).app cell) :=
  rfl

/-- The source idempotent is equivalently the conjugate `α⁻¹Eα`, written in
Lean's composition order as `α ≫ E ≫ α⁻¹`. -/
theorem authoredDiagnosticRawIdempotentComparison_p_left_conjugate
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    (authoredDiagnosticRawIdempotentComparison input cochain cell).p.left =
      (authoredSupportCanonicalMate input.context).app cell ≫
        authoredViaBaseDiagnosticObjectCollapseComponentAtCochain input cochain cell ≫
          inv ((authoredSupportCanonicalMate input.context).app cell) := by
  rw [authoredDiagnosticRawIdempotentComparison_p_left,
    authoredDiagnosticObjectCollapseComparisonAtCochain_app]
  simp only [Category.assoc]

/-- Normalization rule: the target idempotent is the existing cell projector `E`. -/
@[simp]
theorem authoredDiagnosticRawIdempotentComparison_p_right
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    (authoredDiagnosticRawIdempotentComparison input cochain cell).p.right =
      authoredViaBaseDiagnosticObjectCollapseComponentAtCochain
        input cochain cell :=
  rfl

/-- The derived exchange equation `Eα = αe`, in Lean's composition order
`e ≫ α = α ≫ E`. -/
theorem authoredDiagnosticRawIdempotentComparison_intertwining
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    (authoredDiagnosticRawIdempotentComparison input cochain cell).p.left ≫
        (authoredDiagnosticRawIdempotentComparison input cochain cell).X.hom =
      (authoredDiagnosticRawIdempotentComparison input cochain cell).X.hom ≫
        (authoredDiagnosticRawIdempotentComparison input cochain cell).p.right :=
  Arrow.w (authoredDiagnosticRawIdempotentComparison input cochain cell).p

/-- The exchange functor normalizes the raw mate and endpoint idempotents to
the existing comparison `β`. -/
theorem authoredDiagnosticRawIdempotentComparison_normalized_hom
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    (karoubiArrowToArrowKaroubiObj
      (authoredDiagnosticRawIdempotentComparison input cochain cell)).hom.f =
      (authoredDiagnosticObjectCollapseComparisonAtCochain input cochain).app cell := by
  rw [karoubiArrowToArrowKaroubiObj_hom_f,
    authoredDiagnosticRawIdempotentComparison_p_left,
    authoredDiagnosticRawIdempotentComparison_X_hom,
    authoredDiagnosticRawIdempotentComparison_p_right]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc]
  rw [authoredDiagnosticObjectCollapseComparisonAtCochain_app]
  simpa only [Category.assoc] using congrArg
    (fun morphism =>
      (authoredSupportCanonicalMate input.context).app cell ≫ morphism)
    (authoredViaBaseDiagnosticObjectCollapseComponentAtCochain_comp
      input cochain cell)

/-- G-119(C): the exchange functor sends the independently constructed
raw-`α` idempotent square to the actual G-116 Karoubi comparison object. -/
theorem authoredDiagnosticRawIdempotentComparison_exchange
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cochain : DefectCochain input.toTransportData)
    (cell : input.context.Category) :
    karoubiArrowToArrowKaroubiObj
        (authoredDiagnosticRawIdempotentComparison input cochain cell) =
      authoredDiagnosticKaroubiComparison input cochain cell := by
  change karoubiArrowToArrowKaroubiObj
      (authoredDiagnosticRawIdempotentComparison input cochain cell) =
    Arrow.mk (authoredDiagnosticObjectCollapseKaroubiIso input cochain cell).hom
  refine Arrow.ext (by rfl) (by rfl) ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply Karoubi.Hom.ext
  exact authoredDiagnosticRawIdempotentComparison_normalized_hom
    input cochain cell

#assert_standard_axioms_only AAT.AG.RealizationComparisonIdempotents

end AAT.AG.RealizationComparisonIdempotents
