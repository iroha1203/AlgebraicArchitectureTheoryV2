import ResearchLean.AG.QualitySurface.SemanticResidualComponentFaithfulness

/-!
Cycle 84 evidence for `G-aat-quality-surface-01`.

This file upgrades the residual-alias obstruction from a sufficient failure
criterion to a constructive normal form for missed semantic residuals under the
same component projection.  If a target support misses a semantic residual that
the source support contains, and the two supports have the same component
projection, then the missed residual must be represented by a target-supported
alias atom in the same component.

The result remains a finite semantic-support classification.  It does not
extract witnesses from a bare negated closure statement, and it does not assert
source extraction completeness, ArchMap correctness, runtime repair synthesis,
canonical global semantic ontology, general sheaf gluing, global sheaf
completeness, or whole-codebase quality.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticResidualAliasClassification

open HeterogeneousRouteInteraction
open HeterogeneousRouteInteraction.BridgeComponent
open HandoffCechExactness
open HandoffCechOverlapBasis
open SemanticSupportProjectionKernel
open SemanticResidualAliasNonfaithfulness
open SemanticResidualComponentFaithfulness

/-! ## Missed residual normal form -/

/--
A missed semantic residual is an actual residual atom carried by the source
support and missed by the target support.
-/
def MissedSemanticResidual
    {Atom : Type u}
    (projection : Atom -> BridgeComponent)
    (cover : HandoffCechCover)
    (sourceSupport targetSupport : Atom -> Prop) : Prop :=
  exists residual,
    SemanticProjectedResidual projection cover residual /\
      sourceSupport residual /\
      Not (targetSupport residual)

/-- Every residual alias gap contains a missed semantic residual. -/
theorem missedSemanticResidual_of_residualAliasGap
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {sourceSupport targetSupport : Atom -> Prop}
    (hgap :
      ResidualAliasGap projection cover sourceSupport targetSupport) :
    MissedSemanticResidual projection cover sourceSupport targetSupport := by
  rcases hgap with
    ⟨residual, _aliasAtom, hresidual, hsource, htargetMiss,
      _htargetAlias, _hprojection⟩
  exact ⟨residual, hresidual, hsource, htargetMiss⟩

/--
Under the same component projection, a missed semantic residual determines a
residual alias gap: the target support must cover the missed component through
some alias atom.
-/
theorem residualAliasGap_of_missedSemanticResidual_of_sameComponentProjection
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {sourceSupport targetSupport : Atom -> Prop}
    (hsame :
      SameSemanticComponentProjection projection sourceSupport targetSupport)
    (hmissed :
      MissedSemanticResidual projection cover sourceSupport targetSupport) :
    ResidualAliasGap projection cover sourceSupport targetSupport := by
  rcases hmissed with
    ⟨residual, hresidual, hsource, htargetMiss⟩
  have htargetComponent :
      SemanticComponentSupport projection targetSupport
        (projection residual) :=
    (hsame (projection residual)).mp
      ⟨residual, hsource, rfl⟩
  rcases htargetComponent with ⟨aliasAtom, htargetAlias, hprojection⟩
  exact
    ⟨residual, aliasAtom, hresidual, hsource, htargetMiss,
      htargetAlias, hprojection⟩

/--
With the same component projection, residual alias gaps are exactly missed
semantic residuals.
-/
theorem residualAliasGap_iff_missedSemanticResidual_of_sameComponentProjection
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {sourceSupport targetSupport : Atom -> Prop}
    (hsame :
      SameSemanticComponentProjection projection sourceSupport targetSupport) :
    ResidualAliasGap projection cover sourceSupport targetSupport <->
      MissedSemanticResidual projection cover sourceSupport targetSupport := by
  constructor
  · exact missedSemanticResidual_of_residualAliasGap
  · exact residualAliasGap_of_missedSemanticResidual_of_sameComponentProjection
      hsame

/-- In any residual alias gap, the alias atom is distinct from the missed residual atom. -/
theorem aliasAtom_ne_residual_of_residualAliasGap
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {sourceSupport targetSupport : Atom -> Prop}
    (hgap :
      ResidualAliasGap projection cover sourceSupport targetSupport) :
    exists residual aliasAtom,
      SemanticProjectedResidual projection cover residual /\
        sourceSupport residual /\
        Not (targetSupport residual) /\
        targetSupport aliasAtom /\
        projection aliasAtom = projection residual /\
        aliasAtom ≠ residual := by
  rcases hgap with
    ⟨residual, aliasAtom, hresidual, hsource, htargetMiss,
      htargetAlias, hprojection⟩
  have hne : aliasAtom ≠ residual := by
    intro heq
    subst aliasAtom
    exact htargetMiss htargetAlias
  exact
    ⟨residual, aliasAtom, hresidual, hsource, htargetMiss,
      htargetAlias, hprojection, hne⟩

/-- A missed semantic residual obstructs target semantic repair closure. -/
theorem missedSemanticResidual_obstructs_target_semanticRepairClosed
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {sourceSupport targetSupport : Atom -> Prop}
    (hmissed :
      MissedSemanticResidual projection cover sourceSupport targetSupport) :
    Not (SemanticRepairClosed projection cover targetSupport) := by
  intro hclosed
  rcases hmissed with
    ⟨residual, hresidual, _hsource, htargetMiss⟩
  exact htargetMiss (hclosed residual hresidual)

/-- Target semantic repair closure rules out missed semantic residual witnesses. -/
theorem target_semanticRepairClosed_obstructs_missedSemanticResidual
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {sourceSupport targetSupport : Atom -> Prop}
    (hclosed :
      SemanticRepairClosed projection cover targetSupport) :
    Not (MissedSemanticResidual projection cover sourceSupport targetSupport) := by
  intro hmissed
  exact missedSemanticResidual_obstructs_target_semanticRepairClosed
    hmissed hclosed

/--
Same component projection turns an explicit missed residual witness into the
same failure package previously obtained from a residual alias gap.
-/
theorem semanticRepairClosed_nonfaithful_of_missedResidual
    {Atom : Type u}
    {projection : Atom -> BridgeComponent}
    {cover : HandoffCechCover}
    {sourceSupport targetSupport : Atom -> Prop}
    (hsame :
      SameSemanticComponentProjection projection sourceSupport targetSupport)
    (hclosed :
      SemanticRepairClosed projection cover sourceSupport)
    (hmissed :
      MissedSemanticResidual projection cover sourceSupport targetSupport) :
    SameSemanticComponentProjection projection sourceSupport targetSupport /\
      SemanticRepairClosed projection cover sourceSupport /\
      Not (SemanticRepairClosed projection cover targetSupport) /\
      Not (ResidualFiberSingleton projection cover) := by
  exact
    semanticRepairClosed_nonfaithful_of_residualAliasGap
      hsame hclosed
      (residualAliasGap_of_missedSemanticResidual_of_sameComponentProjection
        hsame hmissed)

/-! ## Selected refined semantic repair witness -/

/-- The selected refined witness has an explicit missed repair-frontier residual. -/
theorem selected_missedRepairFrontierResidual :
    MissedSemanticResidual
      refinedSemanticComponent
      repairFrontierOverlapBasisCover
      completeRepairSupport
      surfaceRepairSupport :=
  missedSemanticResidual_of_residualAliasGap
    selected_repairFrontierResidualAliasGap

/-- In the selected witness, the alias gap is classified by the missed residual. -/
theorem selected_residualAliasGap_iff_missedResidual :
    ResidualAliasGap
        refinedSemanticComponent
        repairFrontierOverlapBasisCover
        completeRepairSupport
        surfaceRepairSupport <->
      MissedSemanticResidual
        refinedSemanticComponent
        repairFrontierOverlapBasisCover
        completeRepairSupport
        surfaceRepairSupport :=
  residualAliasGap_iff_missedSemanticResidual_of_sameComponentProjection
    complete_and_surface_same_semanticComponentProjection

/-- The selected missed residual obstructs surface semantic repair closure. -/
theorem selected_missedResidual_obstructs_surfaceClosure :
    Not
      (SemanticRepairClosed
        refinedSemanticComponent
        repairFrontierOverlapBasisCover
        surfaceRepairSupport) :=
  missedSemanticResidual_obstructs_target_semanticRepairClosed
    selected_missedRepairFrontierResidual

/--
The selected missed residual reproduces the semantic closure nonfaithfulness
package under the same component projection.
-/
theorem selected_semanticRepairClosed_nonfaithful_of_missedResidual :
    SameSemanticComponentProjection
        refinedSemanticComponent completeRepairSupport surfaceRepairSupport /\
      SemanticRepairClosed
        refinedSemanticComponent repairFrontierOverlapBasisCover
        completeRepairSupport /\
      Not
        (SemanticRepairClosed
          refinedSemanticComponent repairFrontierOverlapBasisCover
          surfaceRepairSupport) /\
      Not
        (ResidualFiberSingleton
          refinedSemanticComponent repairFrontierOverlapBasisCover) := by
  exact
    semanticRepairClosed_nonfaithful_of_missedResidual
      complete_and_surface_same_semanticComponentProjection
      completeRepairSupport_semanticRepairClosed
      selected_missedRepairFrontierResidual

/-- The selected residual alias witness uses two distinct refined semantic atoms. -/
theorem selected_aliasAtom_ne_residual :
    exists residual aliasAtom,
      SemanticProjectedResidual
          refinedSemanticComponent repairFrontierOverlapBasisCover residual /\
        completeRepairSupport residual /\
        Not (surfaceRepairSupport residual) /\
        surfaceRepairSupport aliasAtom /\
        refinedSemanticComponent aliasAtom = refinedSemanticComponent residual /\
        aliasAtom ≠ residual :=
  aliasAtom_ne_residual_of_residualAliasGap
    selected_repairFrontierResidualAliasGap

/-! ## Theorem package -/

/--
Cycle-84 theorem package: under the same component projection, residual alias
gaps are exactly missed semantic residual witnesses.
-/
theorem semanticResidualAliasClassification_package :
    (forall {Atom : Type u}
      {projection : Atom -> BridgeComponent}
      {cover : HandoffCechCover}
      {sourceSupport targetSupport : Atom -> Prop},
      SameSemanticComponentProjection projection sourceSupport targetSupport ->
        (ResidualAliasGap projection cover sourceSupport targetSupport <->
          MissedSemanticResidual
            projection cover sourceSupport targetSupport)) /\
      (forall {Atom : Type u}
        {projection : Atom -> BridgeComponent}
        {cover : HandoffCechCover}
        {sourceSupport targetSupport : Atom -> Prop},
        MissedSemanticResidual projection cover sourceSupport targetSupport ->
          Not (SemanticRepairClosed projection cover targetSupport)) /\
      MissedSemanticResidual
        refinedSemanticComponent
        repairFrontierOverlapBasisCover
        completeRepairSupport
        surfaceRepairSupport /\
      (ResidualAliasGap
          refinedSemanticComponent
          repairFrontierOverlapBasisCover
          completeRepairSupport
          surfaceRepairSupport <->
        MissedSemanticResidual
          refinedSemanticComponent
          repairFrontierOverlapBasisCover
          completeRepairSupport
          surfaceRepairSupport) /\
      SameSemanticComponentProjection
        refinedSemanticComponent completeRepairSupport surfaceRepairSupport /\
      SemanticRepairClosed
        refinedSemanticComponent repairFrontierOverlapBasisCover
        completeRepairSupport /\
      Not
        (SemanticRepairClosed
          refinedSemanticComponent repairFrontierOverlapBasisCover
          surfaceRepairSupport) /\
      Not
        (ResidualFiberSingleton
          refinedSemanticComponent repairFrontierOverlapBasisCover) /\
      (exists residual aliasAtom,
        SemanticProjectedResidual
            refinedSemanticComponent repairFrontierOverlapBasisCover residual /\
          completeRepairSupport residual /\
          Not (surfaceRepairSupport residual) /\
          surfaceRepairSupport aliasAtom /\
          refinedSemanticComponent aliasAtom =
            refinedSemanticComponent residual /\
          aliasAtom ≠ residual) := by
  exact
    ⟨fun {Atom} {projection} {cover} {sourceSupport} {targetSupport} =>
        residualAliasGap_iff_missedSemanticResidual_of_sameComponentProjection,
      fun {Atom} {projection} {cover} {sourceSupport} {targetSupport} =>
        missedSemanticResidual_obstructs_target_semanticRepairClosed,
      selected_missedRepairFrontierResidual,
      selected_residualAliasGap_iff_missedResidual,
      selected_semanticRepairClosed_nonfaithful_of_missedResidual.1,
      selected_semanticRepairClosed_nonfaithful_of_missedResidual.2.1,
      selected_semanticRepairClosed_nonfaithful_of_missedResidual.2.2.1,
      selected_semanticRepairClosed_nonfaithful_of_missedResidual.2.2.2,
      selected_aliasAtom_ne_residual⟩

end SemanticResidualAliasClassification
end QualitySurface
end ResearchLean.AG
