import Formal.Util.AssertStandardAxioms
import ResearchLean.AG.RelativeRepairComposition.SupportedEquation
import ResearchLean.AG.RelativeRepairComposition.NativeEquationBridge
import ResearchLean.AG.RelativeRepairComposition.InterfaceFunctorInverses

/-!
# Every original supported actual repair and its full affine coordinates

## Implementation notes

The actual objects fix the reference morphisms on P and on every forbidden
candidate. Strong uniqueness identifies precisely those conditions with zero
original corrections. The complete vertex-label subgroup is transported through
the accepted original-coordinate map; no label is replaced by its effect.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory TransportCoherence AbelianLiftingObstruction TransportCoherence.Arbitrary
universe uG uE uB uD vE vB vD
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
namespace SupportedNativeEquation
variable (T : OriginalTowerPresentation K p q) (P : ClosedRegion K)
variable (candidates allowed : Set (EdgeName (K := K)))
local notation "M" => T.toTower.localCoefficients
local notation "fixed" => fixedEdgesForRange P.edges candidates allowed

/-- Retain the same actual repair while remembering its fixed P arrows. -/
def baseRepair (R : SupportedRepair T fixed) : SupportedRepair T P.edges :=
  ⟨R.1,fun e he => R.2 e (Or.inl he)⟩

/-- Retain the same full vertex label while remembering its fixed P arrows. -/
def baseGauge (b : supportedC0 T P.vertices fixed) : supportedC0 T P.vertices P.edges :=
  ⟨b.1,b.2.1,fun e he => b.2.2 e (Or.inl he)⟩

/-- Full original supported labels correspond to the same forbidden-edge coboundary condition. -/
noncomputable def gaugeEquiv : supportedC0 T P.vertices fixed ≃+
    SupportedEquation.Labels M P ClosedRegion.all candidates allowed where
  toFun b := ⟨ActualEquation.originalGaugeEquiv T P (baseGauge T P candidates allowed b),by
    intro e he
    have hd := congrArg (fun h => h.1 e.1)
      (ActualEquation.original_d0 T P (baseGauge T P candidates allowed b))
    exact hd.trans (b.2.2 e.1 (Or.inr he))⟩
  invFun c :=
    let b := (ActualEquation.originalGaugeEquiv T P).symm c.1
    ⟨b.1,b.2.1,by
      intro e he
      rcases he with hp | hf
      · exact b.2.2 e hp
      · have hd := congrArg (fun h => h.1 e) (ActualEquation.original_d0 T P b)
        have hc : ActualEquation.originalGaugeEquiv T P b = c.1 :=
          (ActualEquation.originalGaugeEquiv T P).apply_symm_apply c.1
        rw [hc] at hd
        exact hd.symm.trans (c.2 ⟨e,Set.mem_univ e⟩ hf)⟩
  left_inv b := by
    apply Subtype.ext
    exact congrArg (fun c : supportedC0 T P.vertices P.edges => c.1)
      ((ActualEquation.originalGaugeEquiv T P).symm_apply_apply
      (baseGauge T P candidates allowed b))
  right_inv c := by
    apply Subtype.ext
    exact (ActualEquation.originalGaugeEquiv T P).apply_symm_apply c.1
  map_add' b c := by
    apply Subtype.ext
    exact (ActualEquation.originalGaugeEquiv T P).map_add
      (baseGauge T P candidates allowed b) (baseGauge T P candidates allowed c)

/-- The forward supported-label map preserves every original vertex value. -/
theorem gauge_value (b : supportedC0 T P.vertices fixed) (v : K.Vertex) :
    (gaugeEquiv T P candidates allowed b).1.1 ⟨v,Set.mem_univ v⟩ = b.1 v :=
  ActualEquation.original_gauge_value T P (baseGauge T P candidates allowed b) v

/-- The inverse supported-label map restores every original vertex value. -/
theorem gauge_inverse_value (b : SupportedEquation.Labels M P ClosedRegion.all candidates allowed)
    (v : K.Vertex) : ((gaugeEquiv T P candidates allowed).symm b).1 v = b.1.1 ⟨v,Set.mem_univ v⟩ :=
  ActualEquation.original_gauge_inverse_value T P b.1 v

variable (hfixed : ∀ f ∈ P.faces,
  T.toTower.upper.pathLift (K.twoLeft f) ≫ FiberAut.hom (T.comparator f) =
    T.toTower.upper.pathLift (K.twoRight f))
local notation "δ" => ActualEquation.defectFamily T P hfixed

/-- All independent actual supported repairs have exactly the supported original affine coordinates. -/
noncomputable def repairEquiv : SupportedRepair T fixed ≃
    SupportedEquation.Objects M P ClosedRegion.all candidates allowed δ where
  toFun R := ⟨ActualEquation.originalRepairEquiv T P hfixed
    (baseRepair T P candidates allowed R),by
      intro e he
      have hv := ActualEquation.original_repair_obj_value T P hfixed
        ⟨(),baseRepair T P candidates allowed R⟩ e.1
      exact hv.trans ((solution_correction_zero_iff_edge T R.1 e.1.2.2).mpr
        (R.2 e.1 (Or.inr he)))⟩
  invFun h :=
    let R := (ActualEquation.originalRepairEquiv T P hfixed).symm h.1
    ⟨R.1,by
      intro e he
      rcases he with hp | hf
      · exact R.2 e hp
      · apply (solution_correction_zero_iff_edge T R.1 e.2.2).mp
        exact (ActualEquation.original_repair_inverse_obj_value T P hfixed ⟨(),h.1⟩ e).trans
          (h.2 ⟨e,Set.mem_univ e⟩ hf)⟩
  left_inv R := by
    apply Subtype.ext
    exact congrArg (fun R : SupportedRepair T P.edges => R.1)
      ((ActualEquation.originalRepairEquiv T P hfixed).symm_apply_apply
      (baseRepair T P candidates allowed R))
  right_inv h := by
    apply Subtype.ext
    exact (ActualEquation.originalRepairEquiv T P hfixed).apply_symm_apply h.1

/-- Complete supported labels act by the same original reidentification in both coordinates. -/
theorem repair_equivariant (b : Multiplicative (supportedC0 T P.vertices fixed))
    (R : SupportedRepair T fixed) :
    repairEquiv T P candidates allowed hfixed (b • R) =
      (gaugeEquiv T P candidates allowed).toMultiplicative b •
        repairEquiv T P candidates allowed hfixed R := by
  apply Subtype.ext
  exact ActualEquation.original_repair_equivariant T P hfixed
    (Multiplicative.ofAdd (baseGauge T P candidates allowed b.toAdd))
    (baseRepair T P candidates allowed R)

/-- Every original actual repair and every full allowed gauge arrow correspond. -/
noncomputable def equivalence : RepairGroupoid T P.vertices fixed ≌
    SupportedEquation.Groupoid M P ClosedRegion.all candidates allowed δ :=
  changedLabelEquivalence (gaugeEquiv T P candidates allowed).toMultiplicative
    (repairEquiv T P candidates allowed hfixed) (repair_equivariant T P candidates allowed hfixed)

/-- Every original candidate and edge correction value survives the forward coordinate map. -/
theorem repair_value (R : SupportedRepair T fixed) (e : EdgeName (K := K)) :
    (repairEquiv T P candidates allowed hfixed R).1.1.1 ⟨e,Set.mem_univ e⟩ =
      T.solutionCorrection R.1 e :=
  ActualEquation.original_repair_obj_value T P hfixed ⟨(),baseRepair T P candidates allowed R⟩ e

/-- Every inverse coordinate map restores the full correction on the same original edge. -/
theorem repair_inverse_value
    (h : SupportedEquation.Objects M P ClosedRegion.all candidates allowed δ) (e : EdgeName (K := K)) :
    T.solutionCorrection ((repairEquiv T P candidates allowed hfixed).symm h).1 e =
      h.1.1.1 ⟨e,Set.mem_univ e⟩ :=
  ActualEquation.original_repair_inverse_obj_value T P hfixed ⟨(),h.1⟩ e

/-- Restoring supported coordinates gives the same actual original morphism choice. -/
theorem inverse_choice
    (h : SupportedEquation.Objects M P ClosedRegion.all candidates allowed δ)
    {i j : K.Vertex} (e : K.Edge i j) :
    ((repairEquiv T P candidates allowed hfixed).symm h).1.choice e =
      T.correctionChoice (ActualEquation.originalEdgeEquiv T P h.1.1).1 e :=
  ActualEquation.original_repair_inverse_choice T P hfixed ⟨(),h.1⟩ e

/-- Both coordinate compositions are exactly the identity on full actual objects and arrows. -/
theorem functor_inverse :
    (equivalence T P candidates allowed hfixed).functor ⋙
      (equivalence T P candidates allowed hfixed).inverse = 𝟭 (RepairGroupoid T P.vertices fixed) :=
  changed_label_functor_inverse (gaugeEquiv T P candidates allowed).toMultiplicative
    (repairEquiv T P candidates allowed hfixed) (repair_equivariant T P candidates allowed hfixed)

/-- Both coordinate compositions are exactly the identity on full supported affine objects and arrows. -/
theorem inverse_functor :
    (equivalence T P candidates allowed hfixed).inverse ⋙
      (equivalence T P candidates allowed hfixed).functor =
        𝟭 (SupportedEquation.Groupoid M P ClosedRegion.all candidates allowed δ) :=
  changed_label_inverse_functor (gaugeEquiv T P candidates allowed).toMultiplicative
    (repairEquiv T P candidates allowed hfixed) (repair_equivariant T P candidates allowed hfixed)

/-- Forward supported arrows keep the full original vertex label. -/
theorem functor_label_value {R Q : RepairGroupoid T P.vertices fixed} (f : R ⟶ Q) (v : K.Vertex) :
    ((equivalence T P candidates allowed hfixed).functor.map f).1.toAdd.1.1 ⟨v,Set.mem_univ v⟩ =
      f.1.toAdd.1 v := gauge_value T P candidates allowed f.1.toAdd v

/-- Inverse supported arrows restore the full original vertex label. -/
theorem inverse_label_value
    {h k : SupportedEquation.Groupoid M P ClosedRegion.all candidates allowed δ} (f : h ⟶ k)
    (v : K.Vertex) :
    ((equivalence T P candidates allowed hfixed).inverse.map f).1.toAdd.1 v =
      f.1.toAdd.1.1 ⟨v,Set.mem_univ v⟩ := gauge_inverse_value T P candidates allowed f.1.toAdd v

end SupportedNativeEquation
end AAT.AG.RelativeRepairComposition
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
