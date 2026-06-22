import Formal.AG.Research.QualitySurface.SemanticFiberAwareViewerCriterion

/-!
Cycle 83 evidence for `G-aat-quality-surface-01`.

This file isolates the exact residual-component invariant missing from
component-only semantic readings.  A support can cover every residual component
through some semantic atom and still fail semantic repair closure if that atom
is only an alias.  Semantic repair closure is therefore decomposed into
component-level residual coverage plus residual-component faithfulness.

The result remains finite and semantic-support-level.  It does not assert
source extraction completeness, ArchMap correctness, runtime repair synthesis,
canonical global semantic ontology, general sheaf gluing, global sheaf
completeness, or whole-codebase quality.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticResidualComponentFaithfulness

open HeterogeneousRouteInteraction
open HeterogeneousRouteInteraction.BridgeComponent
open HandoffRepairTransversalTheorem
open HandoffCechExactness
open HandoffCechOverlapBasis
open SemanticSupportProjectionKernel
open SemanticResidualAliasNonfaithfulness
open SemanticFiberAwareViewerCriterion

/-! ## Residual-aware readings -/

/--
A residual-atom-aware reading preserves support exactly on atoms that are
residual for the selected projection and cover.
-/
def ResidualAtomAwareReading
    {Atom : Type u}
    (projection : Atom -> BridgeComponent)
    (cover : HandoffCechCover)
    (sourceSupport targetSupport : Atom -> Prop) : Prop :=
  forall residual,
    SemanticProjectedResidual projection cover residual ->
      (sourceSupport residual <-> targetSupport residual)

/--
Residual-atom-aware readings reflect semantic repair closure.  They preserve
exactly the atom identities that the closure predicate asks the support to hit.
-/
theorem residualAtomAwareReading_reflects_semanticRepairClosed
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {sourceSupport targetSupport : Atom -> Prop}
    (hreading :
      ResidualAtomAwareReading projection cover sourceSupport targetSupport)
    (hclosed :
      SemanticRepairClosed projection cover sourceSupport) :
    SemanticRepairClosed projection cover targetSupport := by
  intro residual hresidual
  exact (hreading residual hresidual).mp (hclosed residual hresidual)

/--
For a closed source support, target closure is exactly residual-atom-aware
reading from source to target.
-/
theorem residualAtomAwareReading_iff_target_semanticRepairClosed_of_source_closed
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {sourceSupport targetSupport : Atom -> Prop}
    (hclosed :
      SemanticRepairClosed projection cover sourceSupport) :
    ResidualAtomAwareReading projection cover sourceSupport targetSupport <->
      SemanticRepairClosed projection cover targetSupport := by
  constructor
  · intro hreading
    exact residualAtomAwareReading_reflects_semanticRepairClosed
      hreading hclosed
  · intro htargetClosed residual hresidual
    constructor
    · intro _hsource
      exact htargetClosed residual hresidual
    · intro _htarget
      exact hclosed residual hresidual

/-- Atom-level semantic-fiber-aware readings are sufficient for residual-aware readings. -/
theorem semanticFiberAwareReading_implies_residualAtomAwareReading
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {sourceSupport targetSupport : Atom -> Prop}
    (hreading :
      SemanticFiberAwareReading sourceSupport targetSupport) :
    ResidualAtomAwareReading projection cover sourceSupport targetSupport := by
  intro residual _hresidual
  exact hreading residual

/--
A residual alias gap obstructs residual-atom-aware reading, because the target
support misses the actual residual atom closed by the source.
-/
theorem residualAliasGap_obstructs_residualAtomAwareReading
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {sourceSupport targetSupport : Atom -> Prop}
    (hgap :
      ResidualAliasGap projection cover sourceSupport targetSupport) :
    Not
      (ResidualAtomAwareReading
        projection cover sourceSupport targetSupport) := by
  intro hreading
  rcases hgap with
    ⟨residual, _aliasAtom, hresidual, hsource, htargetMiss,
      _htargetAlias, _hprojection⟩
  exact htargetMiss ((hreading residual hresidual).mp hsource)

/-! ## Residual component coverage and faithfulness -/

/--
The support covers every residual component, possibly through an alias semantic
atom in the same projected component.
-/
def ResidualComponentCoveredSupport
    {Atom : Type u}
    (projection : Atom -> BridgeComponent)
    (cover : HandoffCechCover)
    (support : Atom -> Prop) : Prop :=
  forall residual,
    SemanticProjectedResidual projection cover residual ->
      SemanticComponentSupport projection support (projection residual)

/--
The support is faithful along residual components: if a supported candidate
covers the component of a residual atom, then the actual residual atom is also
supported.
-/
def ResidualComponentFaithfulSupport
    {Atom : Type u}
    (projection : Atom -> BridgeComponent)
    (cover : HandoffCechCover)
    (support : Atom -> Prop) : Prop :=
  forall residual candidate,
    SemanticProjectedResidual projection cover residual ->
      support candidate ->
        projection candidate = projection residual ->
          support residual

/--
Semantic repair closure is exactly component-level residual coverage plus
faithfulness back to the actual residual atom.
-/
theorem semanticRepairClosed_iff_residualComponentCovered_and_faithful
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {support : Atom -> Prop} :
    SemanticRepairClosed projection cover support <->
      ResidualComponentCoveredSupport projection cover support /\
        ResidualComponentFaithfulSupport projection cover support := by
  constructor
  · intro hclosed
    constructor
    · intro residual hresidual
      exact ⟨residual, hclosed residual hresidual, rfl⟩
    · intro residual _candidate hresidual _hsupport _hprojection
      exact hclosed residual hresidual
  · intro hsupport residual hresidual
    rcases hsupport.1 residual hresidual with
      ⟨candidate, hcandidate, hprojection⟩
    exact hsupport.2 residual candidate hresidual hcandidate hprojection

/--
Residual singleton fibers are a strong sufficient condition for residual
component faithfulness, but the faithfulness invariant can be stated directly
on the support.
-/
theorem residualFiberSingleton_implies_residualComponentFaithfulSupport
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {support : Atom -> Prop}
    (hsingleton : ResidualFiberSingleton projection cover) :
    ResidualComponentFaithfulSupport projection cover support := by
  intro residual candidate hresidual hcandidate hprojection
  have hcandidate_eq : candidate = residual :=
    hsingleton residual candidate hresidual hprojection
  subst candidate
  exact hcandidate

/--
Same component projection transfers residual component coverage from a closed
source support to the target support.
-/
theorem sameComponentProjection_transfers_residualComponentCoverage
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {sourceSupport targetSupport : Atom -> Prop}
    (hsame :
      SameSemanticComponentProjection projection sourceSupport targetSupport)
    (hclosed :
      SemanticRepairClosed projection cover sourceSupport) :
    ResidualComponentCoveredSupport projection cover targetSupport := by
  intro residual hresidual
  have hsource : sourceSupport residual :=
    hclosed residual hresidual
  exact
    (hsame (projection residual)).mp
      ⟨residual, hsource, rfl⟩

/--
Component-projection equality reflects semantic repair closure precisely when
the target support is faithful along residual components.
-/
theorem componentProjection_reflects_semanticRepairClosed_of_residualComponentFaithful
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {sourceSupport targetSupport : Atom -> Prop}
    (hfaithful :
      ResidualComponentFaithfulSupport projection cover targetSupport)
    (hsame :
      SameSemanticComponentProjection projection sourceSupport targetSupport)
    (hclosed :
      SemanticRepairClosed projection cover sourceSupport) :
    SemanticRepairClosed projection cover targetSupport := by
  exact
    semanticRepairClosed_iff_residualComponentCovered_and_faithful.mpr
      ⟨sameComponentProjection_transfers_residualComponentCoverage hsame hclosed,
        hfaithful⟩

/--
A residual alias gap is exactly a witness that residual component coverage is
not faithful back to the actual residual atom.
-/
theorem residualAliasGap_obstructs_residualComponentFaithfulSupport
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {sourceSupport targetSupport : Atom -> Prop}
    (hgap :
      ResidualAliasGap projection cover sourceSupport targetSupport) :
    Not (ResidualComponentFaithfulSupport projection cover targetSupport) := by
  intro hfaithful
  rcases hgap with
    ⟨residual, aliasAtom, hresidual, _hsource, htargetMiss,
      htargetAlias, hprojection⟩
  exact
    htargetMiss
      (hfaithful residual aliasAtom hresidual htargetAlias hprojection)

/-! ## Selected refined semantic repair witness -/

/-- The selected surface support covers every selected residual component. -/
theorem surfaceRepairSupport_residualComponentCovered :
    ResidualComponentCoveredSupport
      refinedSemanticComponent
      repairFrontierOverlapBasisCover
      surfaceRepairSupport := by
  intro residual hresidual
  have hcomponent :
      refinedSemanticComponent residual = BridgeComponent.repairFrontier :=
    (repairFrontierLawDeletion_componentSupport_iff
      (refinedSemanticComponent residual)).mp
      (by
        simpa [SemanticProjectedResidual, repairFrontierOverlapBasisCover,
          HandoffCechOverlapSupport] using hresidual)
  cases residual with
  | traceContract =>
      simp [refinedSemanticComponent] at hcomponent
  | repairFrontierSurface =>
      exact ⟨RefinedSemanticRepairAtom.repairFrontierSurface, trivial, rfl⟩
  | repairFrontierObligation =>
      exact ⟨RefinedSemanticRepairAtom.repairFrontierSurface, trivial, rfl⟩

/-- The selected complete support is faithful along residual components. -/
theorem completeRepairSupport_residualComponentFaithful :
    ResidualComponentFaithfulSupport
      refinedSemanticComponent
      repairFrontierOverlapBasisCover
      completeRepairSupport := by
  intro residual _candidate _hresidual _hcandidate _hprojection
  cases residual <;> trivial

/--
The selected surface support has component coverage but fails residual
component faithfulness.
-/
theorem surfaceRepairSupport_componentCovered_not_faithful :
    ResidualComponentCoveredSupport
        refinedSemanticComponent
        repairFrontierOverlapBasisCover
        surfaceRepairSupport /\
      Not
        (ResidualComponentFaithfulSupport
          refinedSemanticComponent
          repairFrontierOverlapBasisCover
          surfaceRepairSupport) := by
  exact
    ⟨surfaceRepairSupport_residualComponentCovered,
      residualAliasGap_obstructs_residualComponentFaithfulSupport
        selected_repairFrontierResidualAliasGap⟩

/--
The selected surface support demonstrates why component coverage alone does not
imply semantic repair closure.
-/
theorem surfaceRepairSupport_componentCoverage_without_semanticClosure :
    ResidualComponentCoveredSupport
        refinedSemanticComponent
        repairFrontierOverlapBasisCover
        surfaceRepairSupport /\
      Not
        (SemanticRepairClosed
          refinedSemanticComponent
          repairFrontierOverlapBasisCover
          surfaceRepairSupport) /\
      Not
        (ResidualComponentFaithfulSupport
          refinedSemanticComponent
          repairFrontierOverlapBasisCover
          surfaceRepairSupport) := by
  exact
    ⟨surfaceRepairSupport_residualComponentCovered,
      surfaceRepairSupport_not_semanticRepairClosed,
      surfaceRepairSupport_componentCovered_not_faithful.2⟩

/-- Support that records both repair-frontier semantic atoms but not trace. -/
def repairFrontierOnlySupport : RefinedSemanticRepairSupport
  | RefinedSemanticRepairAtom.traceContract => False
  | RefinedSemanticRepairAtom.repairFrontierSurface => True
  | RefinedSemanticRepairAtom.repairFrontierObligation => True

/--
On the selected repair-frontier cover, complete support and repair-frontier-only
support agree on every residual atom.
-/
theorem complete_and_repairFrontierOnly_residualAtomAwareReading :
    ResidualAtomAwareReading
      refinedSemanticComponent
      repairFrontierOverlapBasisCover
      completeRepairSupport
      repairFrontierOnlySupport := by
  intro residual hresidual
  have hcomponent :
      refinedSemanticComponent residual = BridgeComponent.repairFrontier :=
    (repairFrontierLawDeletion_componentSupport_iff
      (refinedSemanticComponent residual)).mp
      (by
        simpa [SemanticProjectedResidual, repairFrontierOverlapBasisCover,
          HandoffCechOverlapSupport] using hresidual)
  cases residual with
  | traceContract =>
      simp [refinedSemanticComponent] at hcomponent
  | repairFrontierSurface =>
      simp [completeRepairSupport, repairFrontierOnlySupport]
  | repairFrontierObligation =>
      simp [completeRepairSupport, repairFrontierOnlySupport]

/--
Residual-aware reading is strictly weaker than atom-level semantic-fiber-aware
reading on the selected cover: trace support may differ when trace is not a
residual atom of this cover.
-/
theorem selected_residualAtomAwareReading_not_semanticFiberAware :
    ResidualAtomAwareReading
        refinedSemanticComponent
        repairFrontierOverlapBasisCover
        completeRepairSupport
        repairFrontierOnlySupport /\
      Not
        (SemanticFiberAwareReading
          completeRepairSupport
          repairFrontierOnlySupport) := by
  constructor
  · exact complete_and_repairFrontierOnly_residualAtomAwareReading
  · intro hreading
    exact
      (hreading RefinedSemanticRepairAtom.traceContract).mp trivial

/--
The selected complete support satisfies the exact decomposition of semantic
repair closure.
-/
theorem completeRepairSupport_closed_decomposes_as_componentCoverage_and_faithfulness :
    ResidualComponentCoveredSupport
        refinedSemanticComponent
        repairFrontierOverlapBasisCover
        completeRepairSupport /\
      ResidualComponentFaithfulSupport
        refinedSemanticComponent
        repairFrontierOverlapBasisCover
        completeRepairSupport := by
  exact
    semanticRepairClosed_iff_residualComponentCovered_and_faithful.mp
      completeRepairSupport_semanticRepairClosed

/-! ## Theorem package -/

/--
Cycle-83 theorem package: semantic repair closure decomposes into residual
component coverage and residual-component faithfulness; the selected surface
support has the former but not the latter.
-/
theorem semanticResidualComponentFaithfulness_package :
    (forall {Atom : Type u}
      {projection : Atom -> BridgeComponent}
      {cover : HandoffCechCover}
      {sourceSupport targetSupport : Atom -> Prop},
      SemanticRepairClosed projection cover sourceSupport ->
        (ResidualAtomAwareReading projection cover sourceSupport targetSupport <->
          SemanticRepairClosed projection cover targetSupport)) /\
      (forall {Atom : Type u}
      {projection : Atom -> BridgeComponent}
      {cover : HandoffCechCover}
      {support : Atom -> Prop},
      SemanticRepairClosed projection cover support <->
        ResidualComponentCoveredSupport projection cover support /\
          ResidualComponentFaithfulSupport projection cover support) /\
      (forall {Atom : Type u}
        {projection : Atom -> BridgeComponent}
        {cover : HandoffCechCover}
        {sourceSupport targetSupport : Atom -> Prop},
        ResidualComponentFaithfulSupport projection cover targetSupport ->
          SameSemanticComponentProjection projection sourceSupport targetSupport ->
            SemanticRepairClosed projection cover sourceSupport ->
              SemanticRepairClosed projection cover targetSupport) /\
      ResidualComponentCoveredSupport
        refinedSemanticComponent
        repairFrontierOverlapBasisCover
        surfaceRepairSupport /\
      Not
        (ResidualComponentFaithfulSupport
          refinedSemanticComponent
          repairFrontierOverlapBasisCover
          surfaceRepairSupport) /\
      Not
        (SemanticRepairClosed
          refinedSemanticComponent
          repairFrontierOverlapBasisCover
          surfaceRepairSupport) /\
      Not
        (ResidualAtomAwareReading
          refinedSemanticComponent
          repairFrontierOverlapBasisCover
          completeRepairSupport
          surfaceRepairSupport) /\
      ResidualAtomAwareReading
        refinedSemanticComponent
        repairFrontierOverlapBasisCover
        completeRepairSupport
        repairFrontierOnlySupport /\
      Not
        (SemanticFiberAwareReading
          completeRepairSupport
          repairFrontierOnlySupport) /\
      ResidualComponentCoveredSupport
        refinedSemanticComponent
        repairFrontierOverlapBasisCover
        completeRepairSupport /\
      ResidualComponentFaithfulSupport
        refinedSemanticComponent
          repairFrontierOverlapBasisCover
          completeRepairSupport := by
  exact
    ⟨fun {Atom} {projection} {cover} {sourceSupport} {targetSupport} =>
        residualAtomAwareReading_iff_target_semanticRepairClosed_of_source_closed,
      fun {Atom} {projection} {cover} {support} =>
        semanticRepairClosed_iff_residualComponentCovered_and_faithful,
      fun {Atom} {projection} {cover} {sourceSupport} {targetSupport} =>
        componentProjection_reflects_semanticRepairClosed_of_residualComponentFaithful,
      surfaceRepairSupport_residualComponentCovered,
      surfaceRepairSupport_componentCovered_not_faithful.2,
      surfaceRepairSupport_not_semanticRepairClosed,
      residualAliasGap_obstructs_residualAtomAwareReading
        selected_repairFrontierResidualAliasGap,
      selected_residualAtomAwareReading_not_semanticFiberAware.1,
      selected_residualAtomAwareReading_not_semanticFiberAware.2,
      completeRepairSupport_closed_decomposes_as_componentCoverage_and_faithfulness.1,
      completeRepairSupport_closed_decomposes_as_componentCoverage_and_faithfulness.2⟩

end SemanticResidualComponentFaithfulness
end QualitySurface
end Formal.AG.Research
