import ResearchLean.AG.CrossStageCoherence.IdentityEdgeLiftSpecialization

/-!
# G-109 shared-edge triangle refutation witness

This module realizes witness (w3) from the fixed G-109 target.  On one vertex
with loop edges `active` and `strict`, the active cells carry the reviewed
comparators `visibleComposite` and `shiftedVisibleComposite`, while the strict
cell joining their right boundaries carries `1`.  Compatible local
trivializers exist and every parallel-pair two-chain is trivial, but the typed
three-chain has holonomy `shiftedVisibleComposite⁻¹ * visibleComposite ≠ 1`.

## Implementation notes

The compatible pair is built explicitly: constant core and upper edge
sections use the common visible projection, and only the cell with authored
comparator `1` belongs to the strict sector.  The proof that every parallel
two-chain is trivial does not inspect selected examples; it proves uniqueness
of any two typed steps with the same endpoints in this finite presentation.
The final non-joint theorem uses the actual three-chain route at the unit
coordinate, so no chain condition is added to `CompatiblePairs`.
-/

namespace AAT.AG.CrossStageCoherence

open CategoryTheory
open AtomFoundation
open GeometryTransport
open TransportCoherence

set_option maxHeartbeats 4000000

namespace SharedEdgeTriangleWitness

open FiniteCrossStageWitness

/-- Empty path at the unique fixture vertex. -/
def nil_path : PresentedPath WitnessEdgeFamily PUnit.unit PUnit.unit :=
  .nil PUnit.unit

/-- One-edge path along the active loop. -/
def active_path : PresentedPath WitnessEdgeFamily PUnit.unit PUnit.unit :=
  .cons .active nil_path

/-- One-edge path along the strict loop. -/
def strict_path : PresentedPath WitnessEdgeFamily PUnit.unit PUnit.unit :=
  .cons .strict nil_path

/-- Finite presentation of cells `A : nil → active`,
`B : nil → strict`, and `S : active → strict`. -/
noncomputable abbrev presentation : FiniteTransportPresentation where
  Vertex := WitnessVertex
  vertexFintype := inferInstance
  Edge := WitnessEdgeFamily
  edgeFintype := fun _ _ => witnessEdgeFintype
  TwoCell := WitnessTwoCell
  twoCellFintype := witnessTwoCellFintype
  twoSource := fun _ => PUnit.unit
  twoTarget := fun _ => PUnit.unit
  twoLeft
    | .activeFirst => nil_path
    | .activeSecond => nil_path
    | .strict => active_path
  twoRight
    | .activeFirst => active_path
    | .activeSecond => strict_path
    | .strict => strict_path
  ThreeCell := PEmpty
  threeCellFintype := inferInstance
  threeSource := fun cell => nomatch cell
  threeTarget := fun cell => nomatch cell
  threeStart := fun cell => nomatch cell
  threeFinish := fun cell => nomatch cell
  threeLeft := fun cell => nomatch cell
  threeRight := fun cell => nomatch cell

/-- Authored comparators prescribed by fixed witness w3. -/
noncomputable def comparator :
    WitnessTwoCell → CompositeFiberAut package
  | .activeFirst => visibleComposite
  | .activeSecond => CompatiblePairRefutation.shiftedVisibleComposite
  | .strict => 1

/-- Identity-edge-lift transport datum carrying the w3 authored comparators. -/
noncomputable abbrev data :
    TwoLayerTransportData presentation FiniteModel.carrier :=
  IdentityEdgeLiftSpecialization.data presentation package comparator

/-- Constant core edge reselection used by the compatible local datum. -/
noncomputable def core_reselection : EdgeReselection data.coreData.lift :=
  fun _ _ _ => visibleCore

/-- The constant core reselection is coherent for all three cells because the
two active comparators have the same visible core projection. -/
theorem core_reselection_coherent :
    CoherentAt data.coreData core_reselection := by
  intro cell
  cases cell
  all_goals simp only [presentation, nil_path, active_path, strict_path,
      reselectedPathLift, reselectLiftData, AdmissibleLiftData.pathLift,
      reselectedEdgeLift, IdentityEdgeLiftSpecialization.data,
      TwoLayerTransportData.coreData, TwoLayerLiftData.coreLiftData,
      IdentityEdgeLiftSpecialization.liftData, core_reselection, comparator,
      visibleComposite_pushforward,
      CompatiblePairRefutation.shiftedVisibleComposite_pushforward,
      map_one]
  all_goals rfl

/-- Core trivializer used in the explicit compatible-pair witness. -/
noncomputable def core_trivializer : CoreTrivializer data where
  reselection := core_reselection
  coherent := core_reselection_coherent

/-- Constant upper edge section lifting the shared core reselection. -/
noncomputable def edge_section : EdgeSectionFamily data where
  core := core_reselection
  lift := fun _ _ _ => visibleComposite
  projects := by
    intro _ _ edge
    cases edge <;> exact visibleComposite_pushforward

/-- The edge section aligns with the coherent constant core reselection. -/
theorem edge_section_alignment : CoreAlignmentAt data edge_section :=
  core_reselection_coherent

/-- The strict cell is qualified: its identity authored comparator projects
to identity and its two identity-lift paths have the same base. -/
theorem strict_qualified : StrictCellQualified data .strict := by
  constructor
  · have pathEquality :=
      (IdentityEdgeLiftSpecialization.path_lift_eq_id presentation package
        (presentation.twoLeft WitnessTwoCell.strict)).trans
      (IdentityEdgeLiftSpecialization.path_lift_eq_id presentation package
        (presentation.twoRight WitnessTwoCell.strict)).symm
    exact congrArg GeometryTotalHom.base pathEquality
  · change compositeFiberPushforward package
      (1 : CompositeFiberAut package) = 1
    exact map_one _

/-- The prescribed strict cell genuinely inhabits the maximal strict sector;
the strict-trivializer part of w3 is therefore not vacuous. -/
theorem strict_sector_nonempty : Nonempty (StrictTwoCell data) :=
  ⟨⟨.strict, strict_qualified⟩⟩

/-- The first active cell is excluded from the strict sector by its nontrivial
visible core projection. -/
theorem active_first_not_qualified :
    ¬ StrictCellQualified data .activeFirst := by
  intro qualified
  have pushed := qualified.2
  change compositeFiberPushforward package visibleComposite = 1 at pushed
  rw [visibleComposite_pushforward] at pushed
  exact visibleCore_ne_one pushed

/-- The second active cell is likewise excluded despite its different upper
comparator, because it has the same nontrivial core projection. -/
theorem active_second_not_qualified :
    ¬ StrictCellQualified data .activeSecond := by
  intro qualified
  have pushed := qualified.2
  change compositeFiberPushforward package
      CompatiblePairRefutation.shiftedVisibleComposite = 1 at pushed
  rw [CompatiblePairRefutation.shiftedVisibleComposite_pushforward] at pushed
  exact visibleCore_ne_one pushed

/-- Identity inner-fiber reselection on the genuine strict sector. -/
noncomputable def strict_reselection : StrictEdgeReselection data.lift := 1

/-- Every qualified strict authored comparator is identity; the two active
constructors cannot inhabit the qualified subtype. -/
theorem strict_authored_eq_one
    (qualified : StrictCellQualified data .strict) :
    strictAuthoredComparator data ⟨.strict, qualified⟩ = 1 := by
  apply Subtype.ext
  rfl

/-- The identity strict reselection is coherent on the sole qualified cell. -/
theorem strict_reselection_coherent :
    StrictCoherentAt data strict_reselection := by
  intro cell
  rcases cell with ⟨cell, qualified⟩
  cases cell
  · exact False.elim (active_first_not_qualified qualified)
  · exact False.elim (active_second_not_qualified qualified)
  · rw [strict_authored_eq_one qualified]
    simp [presentation, nil_path, active_path, strict_path,
      upperReselectedPathLift, upperReselectLiftData,
      TwoLayerLiftData.pathLift, upperReselectedEdgeLift,
      strictToUpperReselection, strict_reselection,
      IdentityEdgeLiftSpecialization.data,
      IdentityEdgeLiftSpecialization.liftData]
    exact Category.comp_id
      (self := geometryTotalCategory FiniteModel.carrier) _

/-- Strict trivializer used in the explicit compatible pair. -/
noncomputable def strict_trivializer : StrictTrivializer data where
  reselection := strict_reselection
  coherent := strict_reselection_coherent

/-- With identity strict correction, the relative upper reselection is exactly
the chosen constant edge lift. -/
theorem relative_upper_eq_edge_lift :
    relativeUpperReselection edge_section strict_trivializer.reselection =
      edge_section.lift := by
  funext i j edge
  cases i
  cases j
  cases edge <;>
    change innerFiberInclusion package (1 : InnerFiberAut package) *
        visibleComposite = visibleComposite <;>
    rw [map_one, one_mul]

/-- The core/strict local data share the required boundary restriction. -/
theorem shared_restriction :
    SharedBoundaryCompatible edge_section strict_trivializer := by
  intro cell
  rcases cell with ⟨cell, qualified⟩
  cases cell
  · exact False.elim (active_first_not_qualified qualified)
  · exact False.elim (active_second_not_qualified qualified)
  · rw [relative_upper_eq_edge_lift]
    simp [presentation, nil_path, active_path, strict_path,
      upperReselectedPathLift, upperReselectLiftData,
      TwoLayerLiftData.pathLift, upperReselectedEdgeLift,
      edge_section, IdentityEdgeLiftSpecialization.data,
      IdentityEdgeLiftSpecialization.liftData, comparator]
    exact Category.comp_id
      (self := geometryTotalCategory FiniteModel.carrier) _

/-- Explicit compatible local core/strict datum for witness w3.  It contains
no cell-chain condition. -/
noncomputable def compatible_pair : CompatiblePairs data where
  coreTrivializer := core_trivializer
  edgeSection := edge_section
  core_restriction := rfl
  alignment := edge_section_alignment
  strictTrivializer := strict_trivializer
  restriction := shared_restriction

/-- The pairwise obstruction vanishes on the shared-edge triangle fixture. -/
theorem compatible_pairwise_vanishes : CompatiblePairwiseVanishes data :=
  ⟨compatible_pair⟩

/-- Empty-path node at which the typed three-chain begins and ends. -/
noncomputable abbrev node0 :
    CellChainNode presentation PUnit.unit PUnit.unit :=
  CellChainNode.left presentation WitnessTwoCell.activeFirst

/-- Active-edge node reached after traversing cell `A`. -/
noncomputable abbrev nodeA :
    CellChainNode presentation PUnit.unit PUnit.unit :=
  CellChainNode.right presentation WitnessTwoCell.activeFirst

/-- Strict-edge node reached after traversing cell `S`. -/
noncomputable abbrev nodeS :
    CellChainNode presentation PUnit.unit PUnit.unit :=
  CellChainNode.right presentation WitnessTwoCell.activeSecond

/-- Forward traversal of active cell `A : nil → active`. -/
noncomputable def stepA : CellChainStep presentation node0 nodeA where
  cell := .activeFirst
  source_eq := rfl
  target_eq := rfl
  orientation := .forward
  before_eq := rfl
  after_eq := rfl

/-- Forward traversal of strict cell `S : active → strict`. -/
noncomputable def stepS : CellChainStep presentation nodeA nodeS where
  cell := .strict
  source_eq := rfl
  target_eq := rfl
  orientation := .forward
  before_eq := rfl
  after_eq := rfl

/-- Backward traversal of active cell `B : nil → strict`. -/
noncomputable def stepBInv : CellChainStep presentation nodeS node0 where
  cell := .activeSecond
  source_eq := rfl
  target_eq := rfl
  orientation := .backward
  before_eq := rfl
  after_eq := rfl

/-- Typed closed three-chain `A ; S ; B⁻¹`. -/
noncomputable def triangle_chain : CellChain presentation node0 node0 :=
  .cons stepA (.cons stepS (.cons stepBInv (.nil node0)))

/-- Authored factor contributed by the first active step. -/
theorem authored_factor_step_a :
    cellAuthoredFactor data stepA = visibleComposite := by
  rfl

/-- The strict middle step contributes identity. -/
theorem authored_factor_step_s :
    cellAuthoredFactor data stepS = 1 := by
  rfl

/-- Backward traversal of `B` contributes the inverse shifted comparator. -/
theorem authored_factor_step_b_inv :
    cellAuthoredFactor data stepBInv =
      CompatiblePairRefutation.shiftedVisibleComposite⁻¹ := by
  rfl

/-- The three-chain holonomy is the prescribed noncommutative comparator ratio. -/
theorem triangle_holonomy_eq :
    CellChainHolonomy data triangle_chain =
      CompatiblePairRefutation.shiftedVisibleComposite⁻¹ *
        visibleComposite := by
  rw [cellChainHolonomy_eq_authoredWord]
  simp [triangle_chain, cellAuthoredWord, authored_factor_step_a,
    authored_factor_step_s, authored_factor_step_b_inv]

/-- The prescribed ratio is nonidentity because the two reviewed upper
comparators are different despite sharing their core projection. -/
theorem triangle_holonomy_ne_one :
    CellChainHolonomy data triangle_chain ≠ 1 := by
  rw [triangle_holonomy_eq]
  intro equality
  apply CompatiblePairRefutation.shiftedVisibleComposite_ne_visible
  calc
    CompatiblePairRefutation.shiftedVisibleComposite =
        CompatiblePairRefutation.shiftedVisibleComposite * 1 := by simp
    _ = CompatiblePairRefutation.shiftedVisibleComposite *
        (CompatiblePairRefutation.shiftedVisibleComposite⁻¹ *
          visibleComposite) := by rw [equality]
    _ = visibleComposite := by group

/-- Any two typed one-cell steps with the same endpoints in this presentation
are equal.  This is the structural reason all parallel-pair two-chains vanish. -/
theorem parallel_step_unique
    {before after : CellChainNode presentation PUnit.unit PUnit.unit}
    (first second : CellChainStep presentation before after) :
    first = second := by
  rcases first with
    ⟨firstCell, firstSource, firstTarget, firstOrientation,
      firstBefore, firstAfter⟩
  rcases second with
    ⟨secondCell, secondSource, secondTarget, secondOrientation,
      secondBefore, secondAfter⟩
  have beforeEquality := firstBefore.symm.trans secondBefore
  have afterEquality := firstAfter.symm.trans secondAfter
  cases firstSource
  cases firstTarget
  cases secondSource
  cases secondTarget
  cases firstCell <;> cases secondCell <;>
    cases firstOrientation <;> cases secondOrientation
  all_goals
    simp [orientedCellBeforePath, orientedCellAfterPath,
      presentation, nil_path, active_path, strict_path,
      castPresentedPath] at beforeEquality afterEquality
  all_goals
    apply CellChainStep.ext <;> rfl

/-- Every parallel-pair two-chain in w3 has trivial holonomy, not merely the
three named pairs appearing in its diagram. -/
theorem every_parallel_two_chain_trivial
    {left right : CellChainNode presentation PUnit.unit PUnit.unit}
    (first second : CellChainStep presentation left right) :
    CellChainHolonomy data (parallelCellTwoChain first second) = 1 := by
  rw [parallel_step_unique first second]
  rw [parallelCellTwoChain_holonomy]
  simp

/-- The nontrivial actual three-chain contradicts joint vanishing. -/
theorem not_joint : ¬ JointVanishes data := by
  intro joint
  have coherent := jointVanishes_cellChainCoherent data joint
  have routeIdentity := coherent PUnit.unit PUnit.unit node0 triangle_chain
  have atOne := congrArg
    (fun route : CompositeFiberAut package ≃ CompositeFiberAut package =>
      route 1)
    routeIdentity
  exact triangle_holonomy_ne_one atOne

/-- The two loop edges used by w3 are distinct. -/
theorem edges_distinct :
    WitnessEdge.active ≠ WitnessEdge.strict := by
  decide

/-- The three named cells used by w3 are pairwise distinct. -/
theorem cells_pairwise_distinct :
    WitnessTwoCell.activeFirst ≠ WitnessTwoCell.activeSecond ∧
      WitnessTwoCell.activeSecond ≠ WitnessTwoCell.strict ∧
      WitnessTwoCell.strict ≠ WitnessTwoCell.activeFirst := by
  decide

/-- Explicit nonemptiness checks for every combinatorial layer used by w3. -/
theorem fixture_nonempty :
    Nonempty presentation.Vertex ∧
      Nonempty (presentation.Edge PUnit.unit PUnit.unit) ∧
      Nonempty presentation.TwoCell ∧
      Nonempty (CellChain presentation node0 node0) :=
  ⟨⟨PUnit.unit⟩, ⟨WitnessEdge.active⟩,
    ⟨WitnessTwoCell.activeFirst⟩, ⟨triangle_chain⟩⟩

/-- Fixed G-109 witness (w3): compatible local data and all parallel two-chain
tests vanish, while the explicit shared-edge three-chain is nontrivial and
joint vanishing fails. -/
theorem w3_shared_edge_triangle :
    (Nonempty presentation.Vertex ∧
      Nonempty (presentation.Edge PUnit.unit PUnit.unit) ∧
      Nonempty presentation.TwoCell ∧
      Nonempty (CellChain presentation node0 node0)) ∧
      WitnessEdge.active ≠ WitnessEdge.strict ∧
      (WitnessTwoCell.activeFirst ≠ WitnessTwoCell.activeSecond ∧
        WitnessTwoCell.activeSecond ≠ WitnessTwoCell.strict ∧
        WitnessTwoCell.strict ≠ WitnessTwoCell.activeFirst) ∧
      Nonempty (StrictTwoCell data) ∧
      CompatiblePairwiseVanishes data ∧
      (∀ {left right : CellChainNode presentation PUnit.unit PUnit.unit}
        (first second : CellChainStep presentation left right),
        CellChainHolonomy data (parallelCellTwoChain first second) = 1) ∧
      CellChainHolonomy data triangle_chain ≠ 1 ∧
      ¬ JointVanishes data :=
  ⟨fixture_nonempty, edges_distinct, cells_pairwise_distinct,
    strict_sector_nonempty, compatible_pairwise_vanishes,
    every_parallel_two_chain_trivial, triangle_holonomy_ne_one, not_joint⟩

end SharedEdgeTriangleWitness

end AAT.AG.CrossStageCoherence

#assert_standard_axioms_only AAT.AG.CrossStageCoherence
