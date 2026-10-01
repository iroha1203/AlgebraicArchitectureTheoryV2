import ResearchLean.AG.RelativeRepairComposition.NativeAffineRepairs
import ResearchLean.AG.RelativeRepairComposition.NativeAffineGroupoid
import ResearchLean.AG.RelativeRepairComposition.OriginalRangeClassification
import ResearchLean.AG.RelativeRepairComposition.RelativeComplex

/-! # All original affine repair ranges and the same relative obstruction -/
namespace AAT.AG.RelativeRepairComposition.NativeAffine
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uA uG
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable (K : FiniteTransportPresentation.{uG})
variable (L R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)
variable (c : K.TwoCell → A)
variable (hfaces : ∀ f : K.TwoCell,
  (GroupExtension.pathValue K R (K.twoLeft f)).linear =
    (GroupExtension.pathValue K R (K.twoRight f)).linear)
variable (P : ClosedRegion K)
variable (hfixed : ∀ f ∈ P.faces,
  translation (k := k) (c f) * GroupExtension.pathValue K R (K.twoLeft f) =
    GroupExtension.pathValue K R (K.twoRight f))
local notation "T" => tower K L R c hfaces
local notation "M" => TowerPresentation.localCoefficients
  (OriginalTowerPresentation.toTower (tower K L R c hfaces))

include hfixed in
/-- Physical coherence of the original affine reference on P is the exact native fixed-face condition. -/
theorem fixed_native (f : K.TwoCell) (hf : f ∈ P.faces) :
    (T).toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom ((T).comparator f) =
      (T).toTower.upper.pathLift (K.twoRight f) := by
  rw [tower_path_value, tower_path_value]
  exact hfixed f hf

/-- Relaxing fixed original edge names includes the very same independent actual affine operation. -/
def repairInclude {fixed larger : Set (EdgeName (K := K))} (h : fixed ⊆ larger)
    (s : Repair K R c larger) : Repair K R c fixed where
  operation := s.operation
  linear := s.linear
  face := s.face
  fixed_value e he := s.fixed_value e (h he)

/-- Including all-S repairs preserves each original real edge value, including candidate names. -/
theorem repair_include_value {fixed larger : Set (EdgeName (K := K))} (h : fixed ⊆ larger)
    (s : Repair K R c larger) {i j : K.Vertex} (e : K.Edge i j) :
    (repairInclude K R c h s).operation e = s.operation e := rfl

/-- The real affine correspondence commutes exactly with relaxation of the same original fixed names. -/
theorem repair_include_native {fixed larger : Set (EdgeName (K := K))} (h : fixed ⊆ larger)
    (s : SupportedRepair (T) larger) :
    repairEquivalence K L R c hfaces fixed (repairInclusion (T) h s) =
      repairInclude K R c h (repairEquivalence K L R c hfaces larger s) := rfl

/-- Range relaxation retains each full original real vertex label as an additive homomorphism. -/
def labelInclude (vertices : Set K.Vertex) {fixed larger : Set (EdgeName (K := K))}
    (h : fixed ⊆ larger) : gaugeLabels K R vertices larger →+ gaugeLabels K R vertices fixed where
  toFun b := ⟨b.1, b.2.1, fun e he => b.2.2 e (h he)⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- Real range relaxation commutes with each full actual reidentification at every original edge. -/
theorem repair_include_gauge (vertices : Set K.Vertex)
    {fixed larger : Set (EdgeName (K := K))} (h : fixed ⊆ larger)
    (b : gaugeLabels K R vertices larger) (s : Repair K R c larger) :
    repairInclude K R c h (gauge K L R c hfaces vertices larger b s) =
      gauge K L R c hfaces vertices fixed (labelInclude K R vertices h b) (repairInclude K R c h s) := by
  apply Repair.ext
  intro i j e
  rw [repair_include_value, gauge_value, gauge_value, repair_include_value]
  rfl

/-- Relaxing an original range includes every original affine repair and every full gauge arrow. -/
noncomputable def affineRangeFunctor (vertices : Set K.Vertex)
    {fixed larger : Set (EdgeName (K := K))} (h : fixed ⊆ larger) :
    Groupoid K L R c hfaces vertices larger ⥤ Groupoid K L R c hfaces vertices fixed := by
  letI := gaugeAddAction K L R c hfaces vertices larger
  letI := gaugeAddAction K L R c hfaces vertices fixed
  exact {
    obj := fun s => (repairInclude K R c h s.back : Groupoid K L R c hfaces vertices fixed)
    map := fun {s _} b => ⟨Multiplicative.ofAdd (labelInclude K R vertices h b.1.toAdd),
      (repair_include_gauge K L R c hfaces vertices h b.1.toAdd s.back).symm.trans
        (congrArg (repairInclude K R c h) b.2)⟩
    map_id := fun _ => Subtype.ext rfl
    map_comp := fun _ _ => Subtype.ext rfl }

variable (candidates allowed : Set (EdgeName (K := K)))
variable (hthree : ∀ s : K.ThreeCell,
  pastingOperation K R c (K.threeLeft s) = pastingOperation K R c (K.threeRight s))

/-- Real affine repairs on every original range exist exactly when the same full relative obstruction vanishes. -/
theorem affine_repair_iff_obstruction_zero :
    Nonempty (Repair K R c (fixedEdgesForRange P.edges candidates allowed)) ↔
      ActualRelative.obstructionClass (T) P candidates allowed
        (fixed_native K L R c hfaces P hfixed)
        (authored_syzygy K L R c hfaces hthree) = 0 :=
  (repairEquivalence K L R c hfaces _).nonempty_congr.symm.trans
    (ActualRelative.repair_nonempty_iff_obstruction_zero (T) P candidates allowed
      (fixed_native K L R c hfaces P hfixed) (authored_syzygy K L R c hfaces hthree))

variable [DecidablePred (· ∈ candidates)]
variable (houtside : ∀ e ∈ candidates, e ∉ P.edges)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]

/-- All independently specified actual affine repairs obey the original always-quotient range membership criterion. -/
theorem affine_repair_iff_range (S : Set candidates) :
    Nonempty (Repair K R c
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S))) ↔
      OriginalRangeClassification.obstruction (k := k) (T) P candidates
        (edge_linear K L R c hfaces) (fixed_native K L R c hfaces P hfixed) ∈
          NamedDual.ranges
            (OriginalRanges.column (k := k) (M) P candidates houtside (edge_linear K L R c hfaces)) S :=
  (repairEquivalence K L R c hfaces _).nonempty_congr.symm.trans
    (OriginalRangeClassification.repair_nonempty_iff_range (k := k) (T) P candidates houtside
      (edge_linear K L R c hfaces) (fixed_native K L R c hfaces P hfixed) S)

/-- All independently specified actual affine repairs obey the full original quotient-dual hitting criterion. -/
theorem affine_repair_iff_hits (S : Set candidates) :
    Nonempty (Repair K R c
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S))) ↔
      NamedDual.Hits
        (OriginalRanges.column (k := k) (M) P candidates houtside (edge_linear K L R c hfaces))
        (OriginalRangeClassification.obstruction (k := k) (T) P candidates
          (edge_linear K L R c hfaces) (fixed_native K L R c hfaces P hfixed)) S :=
  (repairEquivalence K L R c hfaces _).nonempty_congr.symm.trans
    (OriginalRangeClassification.repair_nonempty_iff_hits (k := k) (T) P candidates houtside
      (edge_linear K L R c hfaces) (fixed_native K L R c hfaces P hfixed) S)

/-- Inclusion-minimal independently specified original affine repair ranges are exactly the same minimal dual transversals. -/
theorem affine_minimal_repair_iff (S : Set candidates) :
    Minimal (fun V => Nonempty (Repair K R c
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates V)))) S ↔
      Minimal (NamedDual.Hits
        (OriginalRanges.column (k := k) (M) P candidates houtside (edge_linear K L R c hfaces))
        (OriginalRangeClassification.obstruction (k := k) (T) P candidates
          (edge_linear K L R c hfaces) (fixed_native K L R c hfaces P hfixed))) S := by
  simp only [Minimal, affine_repair_iff_hits K L R c hfaces P hfixed candidates houtside]

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
