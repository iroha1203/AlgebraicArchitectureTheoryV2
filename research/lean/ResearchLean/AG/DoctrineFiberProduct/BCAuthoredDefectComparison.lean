import ResearchLean.AG.DoctrineFiberProduct.BCAuthoredSupportCanonicalMate

/-!
# Authored Beck--Chevalley comparison from the G-106 raw defect

The authored comparator is not used as a free twist of the canonical
Beck--Chevalley mate.  Instead, this module first forms the existing G-106 raw
defect: the authored endpoint comparator relative to the universal-property
comparator of the two diagnostic paths.  That defect is realized as a natural
endomorphism of the southwest support, transported through the direct route,
and only then composed with the canonical mate.

Thus coherent authored data, whose initial raw defect is the identity
cochain, produces exactly the canonical mate.  Conversely a nonidentity
transported defect refutes the public relative coherence relation.  The
construction accepts no comparison, mate, expected equality, or defect
certificate from the caller.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

set_option maxHeartbeats 3000000

/-! ## The G-106 defect on authored support -/

/-- The total morphism underlying the initial G-106 raw defect at one cell. -/
noncomputable def authoredInitialDefectTotal
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    input.context.supportPackage cell ⟶ input.context.supportPackage cell :=
  PackageFiberAut.hom
    (initialRawDefectCochain input.toTransportData cell)

/-- The initial raw defect lies over the southwest identity. -/
theorem authoredInitialDefectTotal_isHomLift
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    (packageProjection U).IsHomLift
      (𝟙 input.context.square.semantic.square.southwest)
      (authoredInitialDefectTotal input cell) := by
  apply CategoryTheory.IsHomLift.of_commsq
    (packageProjection U)
    (𝟙 input.context.square.semantic.square.southwest)
    (authoredInitialDefectTotal input cell)
    (input.context.endpoint_eq cell)
    (input.context.endpoint_eq cell)
  rw [packageProjection_map, authoredInitialDefectTotal,
    PackageFiberAut.hom_base_eq]
  rw [Category.comp_id]
  exact Category.id_comp _

/-- One initial raw defect as an endomorphism in the southwest core fiber. -/
noncomputable def authoredInitialDefectComponent
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    input.context.supportObject cell ⟶ input.context.supportObject cell :=
  ⟨authoredInitialDefectTotal input cell,
    authoredInitialDefectTotal_isHomLift input cell⟩

/-- The complete initial G-106 raw defect on the fixed discrete support. -/
noncomputable def authoredInitialDefectAutomorphism
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U) :
    input.context.supportFunctor ⟶ input.context.supportFunctor :=
  Discrete.natTrans fun cell => authoredInitialDefectComponent input cell.as

@[simp]
theorem authoredInitialDefectAutomorphism_app
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (cell : input.context.square.semantic.diagnostic.TwoCell) :
    (authoredInitialDefectAutomorphism input).app (Discrete.mk cell) =
      authoredInitialDefectComponent input cell :=
  rfl

/-! ## Defect transport and the authored comparison -/

/-- Transport a southwest-support endomorphism through the exact direct route. -/
noncomputable def authoredSupportDirectEndomorphism
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (context : AuthoredSupportContext U)
    (alpha : context.supportFunctor ⟶ context.supportFunctor) :
    authoredSupportDirectRoute context ⟶
      authoredSupportDirectRoute context := by
  rcases context with ⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩
  cases realization_eq
  exact Functor.whiskerRight alpha
    (selectedCoreFiberReindexFunctor
        (typedRealizableHom (bcLeftPresentation presentation)) ⋙
      coreFiberTransportFunctor
        (typedPresentationToSemantic (bcTopPresentation presentation)))

/-- Transporting the identity support endomorphism gives the identity route map. -/
theorem authoredSupportDirectEndomorphism_id
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (context : AuthoredSupportContext U) :
    authoredSupportDirectEndomorphism context
        (𝟙 context.supportFunctor) =
      𝟙 (authoredSupportDirectRoute context) := by
  rcases context with ⟨⟨semantic, presentation, realization_eq⟩,
    lift, endpoint_eq⟩
  cases realization_eq
  ext cell
  simp [authoredSupportDirectEndomorphism, authoredSupportDirectRoute]

/-- The initial G-106 defect transported through the direct BC route. -/
noncomputable def authoredDirectRouteDefect
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U) :
    authoredSupportDirectRoute input.context ⟶
      authoredSupportDirectRoute input.context :=
  authoredSupportDirectEndomorphism input.context
    (authoredInitialDefectAutomorphism input)

/--
The authored comparison generated from the G-106 relative defect and the
universal-property Beck--Chevalley mate.
-/
noncomputable def authoredDefectComparison
    (U : AtomCarrier.{u}) [DecidableEq U.Atom] :
    AuthoredComparisonProducerSignature
      (authoredSupportDirectRouteFamily U)
      (authoredSupportViaBaseRouteFamily U) :=
  fun input => authoredDirectRouteDefect input ≫
    authoredSupportCanonicalMate input.context

/-- Public authored-relative mate coherence predicate. -/
def MateCoherentRel
    (U : AtomCarrier.{u}) [DecidableEq U.Atom] :
    MateCoherentRelSignature U :=
  mateCoherentRelEquation (authoredDefectComparison U)
    (authoredSupportCanonicalMateFamily U)

@[simp]
theorem MateCoherentRel_iff
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U) :
    MateCoherentRel U input ↔
      authoredDefectComparison U input =
        authoredSupportCanonicalMate input.context :=
  Iff.rfl

/-! ## Coherent and incoherent criteria -/

/-- Identity initial raw cochain gives the identity support defect. -/
theorem authoredInitialDefectAutomorphism_eq_identity
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (hdefect : initialRawDefectCochain input.toTransportData =
      identityDefectCochain input.toTransportData) :
    authoredInitialDefectAutomorphism input =
      𝟙 input.context.supportFunctor := by
  ext cell
  rcases cell with ⟨cell⟩
  change authoredInitialDefectTotal input cell =
    Subtype.val (𝟙 (input.context.supportObject cell))
  change PackageFiberAut.hom
      (initialRawDefectCochain input.toTransportData cell) =
    𝟙 (input.context.supportPackage cell)
  rw [congrFun hdefect cell]
  rfl

/-- Identity support defect remains identity after the direct route. -/
theorem authoredDirectRouteDefect_eq_identity
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (hdefect : initialRawDefectCochain input.toTransportData =
      identityDefectCochain input.toTransportData) :
    authoredDirectRouteDefect input =
      𝟙 (authoredSupportDirectRoute input.context) := by
  rw [authoredDirectRouteDefect,
    authoredInitialDefectAutomorphism_eq_identity input hdefect]
  exact authoredSupportDirectEndomorphism_id input.context

/-- A coherent initial G-106 datum induces exactly the canonical BC mate. -/
theorem mateCoherentRel_of_initialRawDefect_eq_identity
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (hdefect : initialRawDefectCochain input.toTransportData =
      identityDefectCochain input.toTransportData) :
    MateCoherentRel U input := by
  change authoredDirectRouteDefect input ≫
      authoredSupportCanonicalMate input.context =
    authoredSupportCanonicalMate input.context
  rw [authoredDirectRouteDefect_eq_identity input hdefect]
  exact Category.id_comp _

/-- A nonidentity transported G-106 defect refutes relative mate coherence. -/
theorem not_mateCoherentRel_of_directRouteDefect_ne_identity
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : AuthoredBCDatumSquare U)
    (hdefect : authoredDirectRouteDefect input ≠
      𝟙 (authoredSupportDirectRoute input.context)) :
    ¬ MateCoherentRel U input := by
  intro coherent
  apply hdefect
  rw [← cancel_mono (authoredSupportCanonicalMate input.context)]
  simpa [authoredDefectComparison] using coherent

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
