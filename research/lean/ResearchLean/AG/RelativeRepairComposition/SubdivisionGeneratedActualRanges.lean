import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedActualNative
import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedNativeRanges
import ResearchLean.AG.RelativeRepairComposition.RangeMaps

/-!
# Full actual extraction and restoration commute with all independent generated range inclusions

## Implementation notes

Only permissions change. Every original actual choice, every local generator
and every native vertex label remains the same. Both directions of full actual
restoration and the complete native functor commute with each inclusion.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualRanges
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uG uI uE uB uD vE vB vD
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k]
variable {K : FiniteTransportPresentation.{uG}} {I : Type uI} [Fintype I] [DecidableEq I]
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (factor : Factorization T chosen)
variable [∀ v, Module k (T.toTower.localCoefficients.A v)]
attribute [local instance] LinearCoefficients.coefficientModules
variable (bases : FiniteFamily.Bases (k := k) T.toTower.localCoefficients.A)
variable (U : I → ClosedRegion K) (P : ClosedRegion K)
variable [∀ j, DecidablePred (· ∈ (U j).vertices)]
variable [∀ j, DecidablePred (· ∈ (U j).edges)] [∀ j, DecidablePred (· ∈ (U j).faces)]
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (owner : I) (hi : chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates owner)
variable (hlinear : ∀ {s t : K.Vertex} (e : K.Edge s t) (a : k)
  (x : T.toTower.localCoefficients.A s),
  T.toTower.localCoefficients.edge e (a • x) = a • T.toTower.localCoefficients.edge e x)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (ek : FiniteElimination.Enumeration k)
variable (ee : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (ef : FiniteElimination.Enumeration K.TwoCell)
local notation "Mo" => T.toTower.localCoefficients
local notation "Mn" => (TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower T chosen factor)))
local notation "Bn" => FiniteBases.expandedBases T chosen factor bases
local notation "Un" => (fun j => expandedRegion K chosen (U j))
local notation "Pn" => expandedRegion K chosen P
local notation "Cn" => oldEdgeSet K chosen candidates
local notation "en" => FiniteEnumerations.edgeEnumeration K chosen ee
local notation "Aw" => Additive (Kernel p q factor.middle)


variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))
variable (ei : FiniteElimination.Enumeration I) (hc : ClosedRegion.IndexedCover U)
variable (allowed : Set (EdgeName (K := K)))
local notation "fixed" => fixedEdgesForRange P.edges candidates allowed
local notation "values" => (fun j => -CoverEquation.defect Mo P (ActualEquation.defectFamily T P hfixed) (U j))


variable (S V : Set (EdgeName (K := K))) (hSV : S ⊆ V)
local notation "FS" => fixedEdgesForRange P.edges candidates S
local notation "FV" => fixedEdgesForRange P.edges candidates V
local notation "oldE" R => GeneratedCoverRestoration.oldObjectEquiv T bases U P candidates hlinear ek ee ef hfixed ei hc R
local notation "newE" R => GeneratedCoverRestoration.newObjectEquiv T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc R

/-- Actual old extraction retains the same independent generated family under every permission inclusion. -/
theorem old_extraction_include (R : SupportedRepair T FS) :
    (oldE V) (repairInclusion T (fixedEdgesForRange_antitone P.edges candidates hSV) R) =
    RelativeGeneratedCoverRanges.includeObjects Mo bases U P candidates hlinear ek ee ef S V hSV values ((oldE S) R) := by
  apply Subtype.ext
  rfl

omit [Fintype (EdgeName (K := K))] in
/-- Actual new extraction retains the same independently generated family under every original permission inclusion. -/
theorem new_extraction_include
    (R : SupportedRepair (originalTower T chosen factor) (oldEdgeSet K chosen FS)) :
    (newE V) (repairInclusion (originalTower T chosen factor)
      (old_set_mono K chosen (fixedEdgesForRange_antitone P.edges candidates hSV)) R) =
    GeneratedCoverRanges.includeNew T chosen factor bases U P candidates owner hi hlinear ek ee ef S V hSV values ((newE S) R) := by
  apply Subtype.ext
  rfl

/-- Full actual old restoration commutes with every independent generated permission inclusion. -/
theorem old_restore_include
    (y : GeneratedStrictObjects.OldObjects T bases U P candidates hlinear ek ee ef values (candidates \ S)) :
    (oldE V).symm (RelativeGeneratedCoverRanges.includeObjects Mo bases U P candidates hlinear ek ee ef S V hSV values y) =
      repairInclusion T (fixedEdgesForRange_antitone P.edges candidates hSV) ((oldE S).symm y) := by
  apply (oldE V).injective
  rw [Equiv.apply_symm_apply,old_extraction_include,Equiv.apply_symm_apply]

omit [Fintype (EdgeName (K := K))] in
/-- Full actual new restoration commutes with every independent generated permission inclusion. -/
theorem new_restore_include
    (y : GeneratedStrictObjects.NewObjects T chosen factor bases U P candidates owner hi hlinear ek ee ef values (candidates \ S)) :
    (newE V).symm (GeneratedCoverRanges.includeNew T chosen factor bases U P candidates owner hi hlinear ek ee ef S V hSV values y) =
      repairInclusion (originalTower T chosen factor)
        (old_set_mono K chosen (fixedEdgesForRange_antitone P.edges candidates hSV)) ((newE S).symm y) := by
  apply (newE V).injective
  rw [Equiv.apply_symm_apply,new_extraction_include,Equiv.apply_symm_apply]

/-- The actual new range inclusion retains every original repair choice and every actual vertex label. -/
noncomputable def actualFunctor :
    RepairGroupoid (originalTower T chosen factor) (Sum.inl '' P.vertices) (oldEdgeSet K chosen FS) ⥤
      RepairGroupoid (originalTower T chosen factor) (Sum.inl '' P.vertices) (oldEdgeSet K chosen FV) where
  obj R := (repairInclusion (originalTower T chosen factor)
    (old_set_mono K chosen (fixedEdgesForRange_antitone P.edges candidates hSV)) R.back :
    RepairGroupoid (originalTower T chosen factor) (Sum.inl '' P.vertices) (oldEdgeSet K chosen FV))
  map {R _} b :=
    ⟨Multiplicative.ofAdd (gaugeInclusion (originalTower T chosen factor) (Sum.inl '' P.vertices)
      (old_set_mono K chosen (fixedEdgesForRange_antitone P.edges candidates hSV)) b.1.toAdd),
      (gauge_inclusion (originalTower T chosen factor) (Sum.inl '' P.vertices)
        (old_set_mono K chosen (fixedEdgesForRange_antitone P.edges candidates hSV)) b.1.toAdd R.back).symm.trans
      (congrArg (repairInclusion (originalTower T chosen factor)
        (old_set_mono K chosen (fixedEdgesForRange_antitone P.edges candidates hSV))) b.2)⟩
  map_id _ := Subtype.ext (congrArg Multiplicative.ofAdd (Subtype.ext rfl))
  map_comp _ _ := Subtype.ext (congrArg Multiplicative.ofAdd (Subtype.ext rfl))

/-- Current independent actual extraction and native permission inclusion commute on all objects and arrows. -/
theorem native_extraction_include :
    actualFunctor T chosen factor P candidates S V hSV ⋙
      (GeneratedActualNative.equivalence T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc V).functor =
    (GeneratedActualNative.equivalence T chosen factor bases U P candidates owner hi hlinear ek ee ef hfixed ei hc S).functor ⋙
      GeneratedNativeRanges.functor T chosen factor bases U P candidates owner hi hlinear ek ee ef S V hSV values := by
  rfl

omit [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
  [DecidablePred (· ∈ candidates)] [Fintype (EdgeName (K := K))]
  [DecidableEq (EdgeName (K := K))] [Fintype K.TwoCell] [DecidableEq K.TwoCell] in
/-- Every original actual vertex label remains literal in the entire new permission-inclusion functor. -/
theorem actual_label
    {x y : RepairGroupoid (originalTower T chosen factor) (Sum.inl '' P.vertices) (oldEdgeSet K chosen FS)}
    (f : x ⟶ y) (v : (presentation K chosen).Vertex) :
    (((actualFunctor T chosen factor P candidates S V hSV).map f).1.toAdd).1 v = f.1.toAdd.1 v := rfl

end AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualRanges
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.GeneratedActualRanges
