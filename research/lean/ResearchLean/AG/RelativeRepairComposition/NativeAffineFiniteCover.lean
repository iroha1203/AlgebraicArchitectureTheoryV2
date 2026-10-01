import ResearchLean.AG.RelativeRepairComposition.NativeAffineFiniteInput
import ResearchLean.AG.RelativeRepairComposition.NativeAffineRanges
import ResearchLean.AG.RelativeRepairComposition.NativeAffineGroupoid
import ResearchLean.AG.RelativeRepairComposition.NativeAffineCorrection
import ResearchLean.AG.RelativeRepairComposition.GeneratedCoverRestoration

/-! # Full finite cover coordinates and reconstruction of original affine repairs -/
namespace AAT.AG.RelativeRepairComposition.NativeAffine
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 100000
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uG uI
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k] (d : Nat)
variable (K : FiniteTransportPresentation.{uG})
variable (L R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k (Fin d → k))
variable (c : K.TwoCell → (Fin d → k))
variable (hfaces : ∀ f : K.TwoCell,
  (GroupExtension.pathValue K R (K.twoLeft f)).linear =
    (GroupExtension.pathValue K R (K.twoRight f)).linear)
variable {I : Type uI} [Fintype I] [DecidableEq I]
variable (P : ClosedRegion K) (U : I → ClosedRegion K)
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable [∀ i, DecidablePred (· ∈ (U i).vertices)]
variable [∀ i, DecidablePred (· ∈ (U i).edges)] [∀ i, DecidablePred (· ∈ (U i).faces)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (hfixed : ∀ f ∈ P.faces,
  translation (k := k) (c f) * GroupExtension.pathValue K R (K.twoLeft f) =
    GroupExtension.pathValue K R (K.twoRight f))
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (enumK : FiniteElimination.Enumeration k)
variable (enumEdges : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (enumFaces : FiniteElimination.Enumeration K.TwoCell)
variable (enumI : FiniteElimination.Enumeration I) (hc : ClosedRegion.IndexedCover U)
variable (allowed : Set (EdgeName (K := K)))
local notation "T" => tower K L R c hfaces
local notation "M" => TowerPresentation.localCoefficients
  (OriginalTowerPresentation.toTower (tower K L R c hfaces))
local notation "bases" => standardBases d K L R c hfaces
local notation "lin" => edge_linear K L R c hfaces
local notation "fix" => fixed_native K L R c hfaces P hfixed
local notation "delta" => ActualEquation.defectFamily (tower K L R c hfaces) P
  (fixed_native K L R c hfaces P hfixed)
local notation "fixed" => fixedEdgesForRange P.edges candidates allowed
local notation "GE" => GeneratedCoverRestoration.objectEquiv (T) bases P U candidates lin fix
  enumK enumEdges enumFaces enumI hc allowed
local notation "GB" => GeneratedCoverRestoration.labelEquiv (T) P U candidates enumI hc allowed
local notation "Q" => repairEquivalence K L R c hfaces fixed
local notation "B" => gaugeLabelEquivalence K L R c hfaces P.vertices fixed

/-- Full independent affine repairs are mutually inverse with all generated public coordinates and full private kernels. -/
noncomputable def finiteObjectEquivalence : Repair K R c fixed ≃
    GeneratedStrictCover.Objects (M) bases P U candidates lin delta enumK enumEdges enumFaces allowed :=
  (Q).symm.trans (GE)

/-- The full independent translation labels correspond to every strict compatible native local label. -/
noncomputable def finiteLabelEquivalence : gaugeLabels K R P.vertices fixed ≃+
    StrictSupportedCover.Labels (M) P U candidates allowed :=
  (B).symm.trans (GB)

/-- The generated finite action is the same actual affine action with every original full label retained. -/
theorem finite_equivariant (b : gaugeLabels K R P.vertices fixed) (s : Repair K R c fixed) :
    finiteObjectEquivalence d K L R c hfaces P U candidates hfixed enumK enumEdges enumFaces enumI hc allowed
      (gauge K L R c hfaces P.vertices fixed b s) =
        GeneratedCoverAction.gauge (M) bases P U candidates lin delta enumK enumEdges enumFaces allowed
          (finiteLabelEquivalence d K L R c hfaces P U candidates enumI hc allowed b)
          (finiteObjectEquivalence d K L R c hfaces P U candidates hfixed enumK enumEdges enumFaces enumI hc allowed s) := by
  change (GE) ((Q).symm ((Q) (repairGauge (T) P.vertices fixed ((B).symm b) ((Q).symm s)))) = _
  rw [Equiv.symm_apply_apply]
  exact GeneratedCoverRestoration.equivariant (T) bases P U candidates lin fix
    enumK enumEdges enumFaces enumI hc allowed (Multiplicative.ofAdd ((B).symm b)) ((Q).symm s)

/-- Every independent affine object and every full original translation arrow has generated finite cover coordinates. -/
noncomputable def finiteGroupoidEquivalence : Groupoid K L R c hfaces P.vertices fixed ≌
    GeneratedCoverAction.Groupoid (M) bases P U candidates lin delta enumK enumEdges enumFaces allowed := by
  letI := gaugeAddAction K L R c hfaces P.vertices fixed
  exact changedLabelEquivalence
    (finiteLabelEquivalence d K L R c hfaces P U candidates enumI hc allowed).toMultiplicative
    (finiteObjectEquivalence d K L R c hfaces P U candidates hfixed enumK enumEdges enumFaces enumI hc allowed)
    (fun b s => finite_equivariant d K L R c hfaces P U candidates hfixed
      enumK enumEdges enumFaces enumI hc allowed b.toAdd s)

/-- Reconstructing generated finite coordinates restores each original real object and every full gauge arrow exactly. -/
theorem finite_functor_inverse :
    (finiteGroupoidEquivalence d K L R c hfaces P U candidates hfixed enumK enumEdges enumFaces enumI hc allowed).functor ⋙
      (finiteGroupoidEquivalence d K L R c hfaces P U candidates hfixed enumK enumEdges enumFaces enumI hc allowed).inverse =
        𝟭 (Groupoid K L R c hfaces P.vertices fixed) := by
  letI := gaugeAddAction K L R c hfaces P.vertices fixed
  exact changed_label_functor_inverse
    (finiteLabelEquivalence d K L R c hfaces P U candidates enumI hc allowed).toMultiplicative
    (finiteObjectEquivalence d K L R c hfaces P U candidates hfixed enumK enumEdges enumFaces enumI hc allowed)
    (fun b s => finite_equivariant d K L R c hfaces P U candidates hfixed
      enumK enumEdges enumFaces enumI hc allowed b.toAdd s)

/-- Recoordinating real affine repairs restores every public value, full private vector and full label exactly. -/
theorem finite_inverse_functor :
    (finiteGroupoidEquivalence d K L R c hfaces P U candidates hfixed enumK enumEdges enumFaces enumI hc allowed).inverse ⋙
      (finiteGroupoidEquivalence d K L R c hfaces P U candidates hfixed enumK enumEdges enumFaces enumI hc allowed).functor =
        𝟭 (GeneratedCoverAction.Groupoid (M) bases P U candidates lin delta enumK enumEdges enumFaces allowed) := by
  letI := gaugeAddAction K L R c hfaces P.vertices fixed
  exact changed_label_inverse_functor
    (finiteLabelEquivalence d K L R c hfaces P U candidates enumI hc allowed).toMultiplicative
    (finiteObjectEquivalence d K L R c hfaces P U candidates hfixed enumK enumEdges enumFaces enumI hc allowed)
    (fun b s => finite_equivariant d K L R c hfaces P U candidates hfixed
      enumK enumEdges enumFaces enumI hc allowed b.toAdd s)

include enumI hc in
/-- All-S independently specified affine repair existence is the same strict generated public relation existence. -/
theorem affine_repair_iff_public : Nonempty (Repair K R c fixed) ↔
    Nonempty (GeneratedPublicRelations.Objects (M) bases P U candidates lin delta enumK enumEdges enumFaces allowed) :=
  (Q).nonempty_congr.symm.trans (GeneratedCoverRestoration.repair_nonempty_iff_public
    (T) bases P U candidates lin fix enumK enumEdges enumFaces enumI hc allowed)

/-- Generated finite coordinates retain the independently evaluated real correction on every original edge in each region. -/
theorem finite_forward_edge_value (s : Repair K R c fixed) (i : I) (e : (U i).edges) :
    coefficient K L R c hfaces e.1.2.1
      (((GeneratedStrictCover.restore (M) bases P U candidates lin delta enumK enumEdges enumFaces allowed
        (finiteObjectEquivalence d K L R c hfaces P U candidates hfixed enumK enumEdges enumFaces enumI hc allowed s)).1 i).1.1.1 e) =
          realCorrection K R c fixed s e.1 := by
  change coefficient K L R c hfaces e.1.2.1
    (((GeneratedStrictCover.restore (M) bases P U candidates lin delta enumK enumEdges enumFaces allowed
      ((GE) ((Q).symm s))).1 i).1.1.1 e) = _
  rw [GeneratedCoverRestoration.forward_edge_value]
  have h := real_correction_native K L R c hfaces fixed ((Q).symm s) e.1
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

/-- Full generated finite reconstruction returns the actual corrected affine operation of every same original edge. -/
theorem finite_inverse_edge_value
    (y : GeneratedStrictCover.Objects (M) bases P U candidates lin delta enumK enumEdges enumFaces allowed)
    (i : I) (e : (U i).edges) :
    ((finiteObjectEquivalence d K L R c hfaces P U candidates hfixed enumK enumEdges enumFaces enumI hc allowed).symm y).operation e.1.2.2 =
      translation (k := k) (coefficient K L R c hfaces e.1.2.1
        (((GeneratedStrictCover.restore (M) bases P U candidates lin delta enumK enumEdges enumFaces allowed y).1 i).1.1.1 e)) *
          R e.1.2.2 := by
  change ((Q) ((GE).symm y)).operation e.1.2.2 = _
  rw [native_repair_correction_value, GeneratedCoverRestoration.inverse_edge_value]

omit [Fintype k] [DecidableEq k] [Fintype I] [DecidableEq I] [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
  [∀ i, DecidablePred (· ∈ (U i).edges)] [∀ i, DecidablePred (· ∈ (U i).faces)]
  [DecidablePred (· ∈ candidates)] [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
  [Fintype K.TwoCell] [DecidableEq K.TwoCell] in
/-- Every full finite-cover label has the same original real vector in each region, including stabilizer labels. -/
theorem finite_forward_label_value (b : gaugeLabels K R P.vertices fixed) (i : I) (v : (U i).vertices) :
    coefficient K L R c hfaces v.1
      (((finiteLabelEquivalence d K L R c hfaces P U candidates enumI hc allowed b).1 i).1.1 v) = b.1 v.1 := by
  change coefficient K L R c hfaces v.1 ((((GB) ((B).symm b)).1 i).1.1 v) = _
  rw [GeneratedCoverRestoration.label_value]
  exact (coefficient K L R c hfaces v.1).apply_symm_apply (b.1 v.1)

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
