import ResearchLean.AG.AbelianLiftingObstruction.VertexGauge
import Mathlib.CategoryTheory.Action
import ResearchLean.AG.RelativeRepairComposition.LabeledAction

/-!
# Fixed actual arrows and supported corrections

G-130 A: the objects are independent actual `Solution`s with fixed-arrow
equalities. Strong uniqueness identifies those equalities with correction
zero. Vertex reidentifications retain their original zero-cochain labels.

## Implementation notes

Fixed edges and vertices are sets of the original typed generators. This
arrow-level API accepts arbitrary sets; the closed-subpresentation layer
supplies the fixed part and forbidden candidates. It does not replace actual
arrow equality by equality of coordinates in the object definition.
-/

namespace AAT.AG.RelativeRepairComposition

open CategoryTheory TransportCoherence TransportCoherence.Arbitrary
open AbelianLiftingObstruction

universe uG uE uB uD vE vB vD

variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q)

/-- The original typed edge names, with both endpoints retained. -/
abbrev EdgeName := Σ i : K.Vertex, Σ j : K.Vertex, K.Edge i j

/-- Strong uniqueness cancels the original edge without assuming it is an isomorphism. -/
theorem solution_edge_eq_iff_choice (R : Solution T) {i j : K.Vertex}
    (e : K.Edge i j) :
    (selectedUpper K p q T.original R.choice).edgeLift e = T.toTower.upper.edgeLift e ↔
      R.choice e = T.lift e := by
  constructor
  · intro h
    exact FiberAut.ext_of_strong_fac (T.original.edgeLift e)
      (T.original.edgeStrong e) _ _ h
  · intro h
    change T.original.edgeLift e ≫ FiberAut.hom (R.choice e) =
      T.original.edgeLift e ≫ FiberAut.hom (T.lift e)
    rw [h]

/-- G-130 A: correction zero is precisely equality with the same physical reference edge. -/
theorem solution_correction_zero_iff_edge (R : Solution T) {i j : K.Vertex}
    (e : K.Edge i j) :
    T.solutionCorrection R ⟨i, j, e⟩ = 0 ↔
      (selectedUpper K p q T.original R.choice).edgeLift e = T.toTower.upper.edgeLift e := by
  rw [solution_edge_eq_iff_choice]
  constructor
  · intro h
    have hc := T.correctionChoice_solutionCorrection R e
    change kernelInclusion p q (T.original.object j)
      (Additive.toMul (T.solutionCorrection R ⟨i, j, e⟩) :
        Kernel p q (T.original.object j)) * T.lift e = R.choice e at hc
    rw [h] at hc
    simpa using hc.symm
  · intro h
    change Additive.ofMul (liftDifference p q (T.original.object j)
      (R.choice e) (T.lift e) _) = 0
    apply Additive.toMul.injective
    apply kernelInclusion_injective p q (T.original.object j)
    change R.choice e * (T.lift e)⁻¹ = 1
    rw [h, mul_inv_cancel]

/-- The subgroup of the same edge cochains that vanish on the fixed names. -/
def supportedC1 (fixed : Set (EdgeName (K := K))) :
    AddSubgroup (C1 T.toTower.localCoefficients) where
  carrier := {h | ∀ e ∈ fixed, h e = 0}
  zero_mem' := by intro e _; rfl
  add_mem' := by intro h k hh hk e he; simp [hh e he, hk e he]
  neg_mem' := by intro h hh e he; simp [hh e he]

/-- Membership API for the fixed-edge subgroup. -/
theorem mem_supportedC1 (fixed : Set (EdgeName (K := K)))
    (h : C1 T.toTower.localCoefficients) :
    h ∈ supportedC1 T fixed ↔ ∀ e ∈ fixed, h e = 0 := Iff.rfl

/-- Independent actual repairs retaining the same named fixed arrows. -/
def SupportedRepair (fixed : Set (EdgeName (K := K))) :=
  {R : Solution T // ∀ e ∈ fixed,
    (selectedUpper K p q T.original R.choice).edgeLift e.2.2 =
      T.toTower.upper.edgeLift e.2.2}

/-- Supported solutions of the original correction equation. -/
def SupportedCorrection (fixed : Set (EdgeName (K := K))) :=
  {h : supportedC1 T fixed // d1 T.toTower.localCoefficients h.1 = -T.toTower.defect}

/-- Coordinates of each independent actual repair, preserving all edge names. -/
noncomputable def repairCoord (fixed : Set (EdgeName (K := K)))
    (R : SupportedRepair T fixed) : SupportedCorrection T fixed :=
  ⟨⟨T.solutionCorrection R.1, fun e he =>
    (solution_correction_zero_iff_edge T R.1 e.2.2).mpr (R.2 e he)⟩,
    T.solutionCorrection_d1 R.1⟩

/-- Restore the original actual edge choices from a supported correction. -/
noncomputable def repairRec (fixed : Set (EdgeName (K := K)))
    (h : SupportedCorrection T fixed) : SupportedRepair T fixed :=
  ⟨T.solutionOfCorrection h.1.1 h.2, by
    intro e he
    apply (solution_correction_zero_iff_edge T _ e.2.2).mp
    rw [T.solutionCorrection_solutionOfCorrection]
    exact h.1.2 e he⟩

/-- The two constructions are inverse on all actual original-edge repairs. -/
theorem repairRec_coord (fixed : Set (EdgeName (K := K)))
    (R : SupportedRepair T fixed) : repairRec T fixed (repairCoord T fixed R) = R := by
  apply Subtype.ext
  exact T.solutionOfCorrection_solutionCorrection R.1

/-- The two constructions are inverse on all supported corrections. -/
theorem repairCoord_rec (fixed : Set (EdgeName (K := K)))
    (h : SupportedCorrection T fixed) : repairCoord T fixed (repairRec T fixed h) = h := by
  apply Subtype.ext
  apply Subtype.ext
  exact T.solutionCorrection_solutionOfCorrection h.1.1 h.2

/-- G-130 A: the fixed-arrow object correspondence is an equivalence. -/
noncomputable def repairEquiv (fixed : Set (EdgeName (K := K))) :
    SupportedRepair T fixed ≃ SupportedCorrection T fixed where
  toFun := repairCoord T fixed
  invFun := repairRec T fixed
  left_inv := repairRec_coord T fixed
  right_inv := repairCoord_rec T fixed

/-- The actual vertex cochains which fix the specified vertices and arrows. -/
def supportedC0 (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K))) :
    AddSubgroup (C0 T.toTower.localCoefficients) where
  carrier := {b | (∀ v ∈ vertices, b v = 0) ∧
    d0 T.toTower.localCoefficients b ∈ supportedC1 T fixed}
  zero_mem' := by
    constructor
    · intro v _; rfl
    · change (d0Hom T.toTower.localCoefficients) 0 ∈ supportedC1 T fixed
      rw [map_zero]; exact (supportedC1 T fixed).zero_mem
  add_mem' := by
    intro b c hb hc
    constructor
    · intro v hv; simp [hb.1 v hv, hc.1 v hv]
    · rw [d0_add]; exact (supportedC1 T fixed).add_mem hb.2 hc.2
  neg_mem' := by
    intro b hb
    constructor
    · intro v hv; simp [hb.1 v hv]
    · change (d0Hom T.toTower.localCoefficients) (-b) ∈ supportedC1 T fixed
      rw [map_neg]; exact (supportedC1 T fixed).neg_mem hb.2

/-- Apply an allowed original vertex reidentification to an actual repair. -/
noncomputable def repairGauge (vertices : Set K.Vertex)
    (fixed : Set (EdgeName (K := K)))
    (b : supportedC0 T vertices fixed) (R : SupportedRepair T fixed) :
    SupportedRepair T fixed :=
  ⟨T.vertexGauge b.1 R.1, by
    intro e he
    apply (solution_correction_zero_iff_edge T _ e.2.2).mp
    rw [T.vertexGauge_correction]
    change T.solutionCorrection R.1 e + d0 T.toTower.localCoefficients b.1 e = 0
    have hr : T.solutionCorrection R.1 e = 0 := (repairCoord T fixed R).1.2 e he
    rw [hr, b.2.2 e he, add_zero]⟩

/-- The coordinate of an actual gauge action is addition of the same coboundary. -/
theorem repairGauge_coord (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))
    (b : supportedC0 T vertices fixed) (R : SupportedRepair T fixed) :
    (repairCoord T fixed (repairGauge T vertices fixed b R)).1.1 =
      (repairCoord T fixed R).1.1 + d0 T.toTower.localCoefficients b.1 :=
  T.vertexGauge_correction b.1 R.1

/-- Allowed vertex labels act on actual repairs without quotienting stabilizers. -/
noncomputable instance repairAddAction (vertices : Set K.Vertex)
    (fixed : Set (EdgeName (K := K))) :
    AddAction (supportedC0 T vertices fixed) (SupportedRepair T fixed) where
  vadd := repairGauge T vertices fixed
  zero_vadd R := Subtype.ext (T.vertexGauge_zero R.1)
  add_vadd b c R := Subtype.ext (T.vertexGauge_add b.1 c.1 R.1)

/-- The native action groupoid retains every original vertex-cochain label. -/
abbrev RepairGroupoid (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K))) :=
  ActionCategory (Multiplicative (supportedC0 T vertices fixed)) (SupportedRepair T fixed)

/-- Actual arrows between repairs correspond to the same labels solving the gauge equation. -/
noncomputable def repairHomEquiv (vertices : Set K.Vertex)
    (fixed : Set (EdgeName (K := K))) (R Q : SupportedRepair T fixed) :
    {b : supportedC0 T vertices fixed // repairGauge T vertices fixed b R = Q} ≃
    {b : supportedC0 T vertices fixed //
      (repairCoord T fixed Q).1.1 = (repairCoord T fixed R).1.1 +
        d0 T.toTower.localCoefficients b.1} where
  toFun b := ⟨b.1, (congrArg (fun Q => (repairCoord T fixed Q).1.1) b.2).symm.trans
    (repairGauge_coord T vertices fixed b.1 R)⟩
  invFun b := ⟨b.1, by
    apply (repairEquiv T fixed).injective
    apply Subtype.ext
    apply Subtype.ext
    exact (repairGauge_coord T vertices fixed b.1 R).trans b.2.symm⟩
  left_inv b := Subtype.ext rfl
  right_inv b := Subtype.ext rfl

/-- Every gauge-equation morphism has exactly its original vertex label. -/
theorem repairHomEquiv_label (vertices : Set K.Vertex)
    (fixed : Set (EdgeName (K := K))) (R Q : SupportedRepair T fixed)
    (b : {b : supportedC0 T vertices fixed // repairGauge T vertices fixed b R = Q}) :
    (repairHomEquiv T vertices fixed R Q b).1 = b.1 := rfl

/-- Fixed endpoints of a gauge force its coboundary to vanish on every fixed arrow. -/
theorem gauge_between_supported (vertices : Set K.Vertex)
    (fixed : Set (EdgeName (K := K))) (b : C0 T.toTower.localCoefficients)
    (hb : ∀ v ∈ vertices, b v = 0) (R Q : SupportedRepair T fixed)
    (h : T.vertexGauge b R.1 = Q.1) : b ∈ supportedC0 T vertices fixed := by
  refine ⟨hb, ?_⟩
  intro e he
  have hr : T.solutionCorrection R.1 e = 0 := (repairCoord T fixed R).1.2 e he
  have hq : T.solutionCorrection Q.1 e = 0 := (repairCoord T fixed Q).1.2 e he
  have heq := congrFun ((T.vertexGauge_correction b R.1).symm.trans
    (congrArg T.solutionCorrection h)) e
  simpa only [Pi.add_apply, hr, hq, zero_add] using heq

/-- The full original set of reidentifications between fixed repairs has the same labels. -/
noncomputable def originalHomEquiv (vertices : Set K.Vertex)
    (fixed : Set (EdgeName (K := K))) (R Q : SupportedRepair T fixed) :
    {b : C0 T.toTower.localCoefficients //
      (∀ v ∈ vertices, b v = 0) ∧ T.vertexGauge b R.1 = Q.1} ≃
    {b : supportedC0 T vertices fixed // repairGauge T vertices fixed b R = Q} where
  toFun b := ⟨⟨b.1, gauge_between_supported T vertices fixed b.1 b.2.1 R Q b.2.2⟩,
    Subtype.ext b.2.2⟩
  invFun b := ⟨b.1.1, b.1.2.1, congrArg Subtype.val b.2⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext (Subtype.ext rfl)

/-- Direct coboundary addition on supported correction solutions. -/
noncomputable def correctionGauge (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))
    (b : supportedC0 T vertices fixed) (h : SupportedCorrection T fixed) :
    SupportedCorrection T fixed :=
  ⟨⟨h.1.1 + d0 T.toTower.localCoefficients b.1,
    (supportedC1 T fixed).add_mem h.1.2 b.2.2⟩, by
      rw [d1_add, h.2, d1_d0, add_zero]⟩

/-- Coordinate action intertwines the independent actual vertex action. -/
theorem coord_gauge (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))
    (b : supportedC0 T vertices fixed) (R : SupportedRepair T fixed) :
    repairCoord T fixed (repairGauge T vertices fixed b R) =
      correctionGauge T vertices fixed b (repairCoord T fixed R) := by
  apply Subtype.ext
  apply Subtype.ext
  exact repairGauge_coord T vertices fixed b R

/-- Restoration intertwines the same labeled coboundary action. -/
theorem rec_gauge (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))
    (b : supportedC0 T vertices fixed) (h : SupportedCorrection T fixed) :
    repairRec T fixed (correctionGauge T vertices fixed b h) =
      repairGauge T vertices fixed b (repairRec T fixed h) := by
  apply (repairEquiv T fixed).injective
  change repairCoord T fixed _ = repairCoord T fixed _
  rw [repairCoord_rec, coord_gauge, repairCoord_rec]

/-- The supported correction action uses direct addition, retaining all vertex labels. -/
noncomputable instance correctionAddAction (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K))) :
    AddAction (supportedC0 T vertices fixed) (SupportedCorrection T fixed) where
  vadd := correctionGauge T vertices fixed
  zero_vadd h := by
    apply Subtype.ext; apply Subtype.ext
    change h.1.1 + (d0Hom T.toTower.localCoefficients) 0 = h.1.1
    rw [map_zero, add_zero]
  add_vadd b c h := by
    apply Subtype.ext; apply Subtype.ext
    change h.1.1 + d0 T.toTower.localCoefficients (b.1 + c.1) =
      (h.1.1 + d0 T.toTower.localCoefficients c.1) + d0 T.toTower.localCoefficients b.1
    rw [d0_add]; abel

/-- Native correction action groupoid for the same permitted vertex labels. -/
abbrev CorrectionGroupoid (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K))) :=
  ActionCategory (Multiplicative (supportedC0 T vertices fixed)) (SupportedCorrection T fixed)

/-- G-130 A: the coordinate functor preserves every actual gauge label. -/
noncomputable def coordFunctor (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K))) :
    RepairGroupoid T vertices fixed ⥤ CorrectionGroupoid T vertices fixed where
  obj R := (repairCoord T fixed R.back : CorrectionGroupoid T vertices fixed)
  map {R _} b := ⟨b.1, (coord_gauge T vertices fixed b.1.toAdd R.back).symm.trans
    (congrArg (repairCoord T fixed) b.2)⟩
  map_id _ := Subtype.ext rfl
  map_comp _ _ := Subtype.ext rfl

/-- G-130 A: the restoration functor preserves every actual gauge label. -/
noncomputable def recFunctor (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K))) :
    CorrectionGroupoid T vertices fixed ⥤ RepairGroupoid T vertices fixed where
  obj h := (repairRec T fixed h.back : RepairGroupoid T vertices fixed)
  map {h _} b := ⟨b.1, (rec_gauge T vertices fixed b.1.toAdd h.back).symm.trans
    (congrArg (repairRec T fixed) b.2)⟩
  map_id _ := Subtype.ext rfl
  map_comp _ _ := Subtype.ext rfl

/-- The functors restore the same actual object, including its original edge choices. -/
theorem rec_coord_obj (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))
    (R : RepairGroupoid T vertices fixed) :
    (recFunctor T vertices fixed).obj ((coordFunctor T vertices fixed).obj R) = R := by
  have h := repairRec_coord T fixed R.back
  exact (congrArg (fun R : SupportedRepair T fixed =>
    (R : RepairGroupoid T vertices fixed)) h).trans (ActionCategory.back_coe R)

/-- The functors restore the same correction object. -/
theorem coord_rec_obj (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))
    (h : CorrectionGroupoid T vertices fixed) :
    (coordFunctor T vertices fixed).obj ((recFunctor T vertices fixed).obj h) = h := by
  have hk := repairCoord_rec T fixed h.back
  exact (congrArg (fun h : SupportedCorrection T fixed =>
    (h : CorrectionGroupoid T vertices fixed)) hk).trans (ActionCategory.back_coe h)

/-- Both functors preserve labels exactly, so no distinct reidentifications are merged. -/
theorem coordFunctor_map_label (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))
    {R Q : RepairGroupoid T vertices fixed} (b : R ⟶ Q) :
    ((coordFunctor T vertices fixed).map b).1 = b.1 := rfl

/-- The restoration functor also preserves labels exactly. -/
theorem recFunctor_map_label (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))
    {h k : CorrectionGroupoid T vertices fixed} (b : h ⟶ k) :
    ((recFunctor T vertices fixed).map b).1 = b.1 := rfl

/-- G-130 A: actual repair coordinates induce a native equivalence retaining all morphisms. -/
noncomputable def repairGroupoidEquivalence (vertices : Set K.Vertex)
    (fixed : Set (EdgeName (K := K))) :
    RepairGroupoid T vertices fixed ≌ CorrectionGroupoid T vertices fixed :=
  labeledActionEquivalence (G := Multiplicative (supportedC0 T vertices fixed))
    (repairEquiv T fixed) (fun b R => coord_gauge T vertices fixed b.toAdd R)

/-- Relaxing fixed-edge conditions includes the same actual repair. -/
def repairInclusion {fixed larger : Set (EdgeName (K := K))}
    (h : fixed ⊆ larger) (R : SupportedRepair T larger) : SupportedRepair T fixed :=
  ⟨R.1, fun e he => R.2 e (h he)⟩

/-- Relaxing fixed-edge conditions includes the same correction solution. -/
def correctionInclusion {fixed larger : Set (EdgeName (K := K))}
    (h : fixed ⊆ larger) (x : SupportedCorrection T larger) : SupportedCorrection T fixed :=
  ⟨⟨x.1.1, fun e he => x.1.2 e (h he)⟩, x.2⟩

/-- Coordinates commute with relaxing the fixed-arrow conditions. -/
theorem coord_inclusion {fixed larger : Set (EdgeName (K := K))}
    (h : fixed ⊆ larger) (R : SupportedRepair T larger) :
    repairCoord T fixed (repairInclusion T h R) =
      correctionInclusion T h (repairCoord T larger R) := rfl

/-- Restoration commutes with relaxing the fixed-arrow conditions. -/
theorem rec_inclusion {fixed larger : Set (EdgeName (K := K))}
    (h : fixed ⊆ larger) (x : SupportedCorrection T larger) :
    repairRec T fixed (correctionInclusion T h x) = repairInclusion T h (repairRec T larger x) := rfl

/-- Relaxation includes each original gauge label as an additive homomorphism. -/
def gaugeInclusion (vertices : Set K.Vertex) {fixed larger : Set (EdgeName (K := K))}
    (h : fixed ⊆ larger) : supportedC0 T vertices larger →+ supportedC0 T vertices fixed where
  toFun b := ⟨b.1, b.2.1, fun e he => b.2.2 e (h he)⟩
  map_zero' := Subtype.ext rfl
  map_add' _ _ := Subtype.ext rfl

/-- Relaxation commutes with every permitted actual vertex reidentification. -/
theorem gauge_inclusion (vertices : Set K.Vertex) {fixed larger : Set (EdgeName (K := K))}
    (h : fixed ⊆ larger) (b : supportedC0 T vertices larger) (R : SupportedRepair T larger) :
    repairInclusion T h (repairGauge T vertices larger b R) =
      repairGauge T vertices fixed (gaugeInclusion T vertices h b) (repairInclusion T h R) := rfl

/-- A change range fixes precisely the fixed-part edges and forbidden candidate names. -/
def fixedEdgesForRange (part candidates allowed : Set (EdgeName (K := K))) :
    Set (EdgeName (K := K)) := part ∪ (candidates \ allowed)

/-- Increasing the allowed change range relaxes fixed conditions on the same names. -/
theorem fixedEdgesForRange_antitone (part candidates : Set (EdgeName (K := K)))
    {S U : Set (EdgeName (K := K))} (h : S ⊆ U) :
    fixedEdgesForRange part candidates U ⊆ fixedEdgesForRange part candidates S := by
  rintro e (he | ⟨hc, hu⟩)
  · exact Or.inl he
  · exact Or.inr ⟨hc, fun hs => hu (h hs)⟩

/-- The actual supported repairs exist exactly when the supported equation has a solution. -/
theorem supported_repair_nonempty_iff (fixed : Set (EdgeName (K := K))) :
    Nonempty (SupportedRepair T fixed) ↔
      ∃ h : C1 T.toTower.localCoefficients,
        (∀ e ∈ fixed, h e = 0) ∧ d1 T.toTower.localCoefficients h = -T.toTower.defect := by
  constructor
  · rintro ⟨R⟩
    exact ⟨(repairCoord T fixed R).1.1, (repairCoord T fixed R).1.2,
      (repairCoord T fixed R).2⟩
  · rintro ⟨h, hf, hd⟩
    exact ⟨repairRec T fixed ⟨⟨h, hf⟩, hd⟩⟩

/-- A stabilizer label is precisely a degree-zero cocycle; it is retained as a morphism. -/
theorem repairGauge_eq_self_iff (vertices : Set K.Vertex)
    (fixed : Set (EdgeName (K := K))) (b : supportedC0 T vertices fixed)
    (R : SupportedRepair T fixed) :
    repairGauge T vertices fixed b R = R ↔ d0 T.toTower.localCoefficients b.1 = 0 := by
  constructor
  · intro h
    have hc := (repairGauge_coord T vertices fixed b R).symm.trans
      (congrArg (fun Q => (repairCoord T fixed Q).1.1) h)
    exact (add_eq_left.mp hc)
  · intro h
    apply (repairEquiv T fixed).injective
    apply Subtype.ext; apply Subtype.ext
    change (repairCoord T fixed (repairGauge T vertices fixed b R)).1.1 =
      (repairCoord T fixed R).1.1
    rw [repairGauge_coord, h, add_zero]

end AAT.AG.RelativeRepairComposition

#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
