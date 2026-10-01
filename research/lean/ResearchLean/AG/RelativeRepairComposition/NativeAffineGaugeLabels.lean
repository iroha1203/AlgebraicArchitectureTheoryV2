import ResearchLean.AG.RelativeRepairComposition.NativeAffineRepairs

/-! # All original translation labels preserving fixed vertices and reference arrows -/
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
variable (vertices : Set K.Vertex) (fixed : Set (EdgeName (K := K)))
local notation "M" => TowerPresentation.localCoefficients
  (OriginalTowerPresentation.toTower (tower K L R c hfaces))

/-- Full original vector labels vanishing at fixed vertices and preserving each fixed real reference edge. -/
def gaugeLabels : AddSubgroup (K.Vertex → A) where
  carrier := {b | (∀ v ∈ vertices, b v = 0) ∧
    ∀ e ∈ fixed, b e.2.1 = (R e.2.2).linear (b e.1)}
  zero_mem' := by constructor <;> intro x hx <;> simp
  add_mem' := by
    intro b a hb ha
    constructor
    · intro v hv; simp [hb.1 v hv, ha.1 v hv]
    · intro e he; simp [hb.2 e he, ha.2 e he]
  neg_mem' := by
    intro b hb
    constructor
    · intro v hv; simp [hb.1 v hv]
    · intro e he; simp [hb.2 e he]

/-- Full vector labels and all original native vertex cochains satisfy exactly the same fixed conditions. -/
theorem gauge_label_conditions (b : C0 (M)) :
    b ∈ supportedC0 (tower K L R c hfaces) vertices fixed ↔
      (fun v => coefficient K L R c hfaces v (b v)) ∈ gaugeLabels K R vertices fixed := by
  constructor
  · intro hb
    constructor
    · intro v hv
      change coefficient K L R c hfaces v (b v) = 0
      rw [hb.1 v hv, map_zero]
    · intro e he
      have hz := congrArg (coefficient K L R c hfaces e.2.1) (hb.2 e he)
      change coefficient K L R c hfaces e.2.1 (b e.2.1 - (M).edge e.2.2 (b e.1)) =
        coefficient K L R c hfaces e.2.1 0 at hz
      rw [map_sub, edge_coefficient, map_zero] at hz
      exact sub_eq_zero.mp hz
  · intro hb
    constructor
    · intro v hv
      apply (coefficient K L R c hfaces v).injective
      rw [map_zero]
      exact hb.1 v hv
    · intro e he
      apply (coefficient K L R c hfaces e.2.1).injective
      change coefficient K L R c hfaces e.2.1 (b e.2.1 - (M).edge e.2.2 (b e.1)) =
        coefficient K L R c hfaces e.2.1 0
      rw [map_sub, edge_coefficient, map_zero]
      exact sub_eq_zero.mpr (hb.2 e he)

/-- The entire original native gauge subgroup equals the full independent translation-label subgroup. -/
noncomputable def gaugeLabelEquivalence : supportedC0 (tower K L R c hfaces) vertices fixed ≃+
    gaugeLabels K R vertices fixed where
  toFun b := ⟨fun v => coefficient K L R c hfaces v (b.1 v),
    (gauge_label_conditions K L R c hfaces vertices fixed b.1).mp b.2⟩
  invFun b := ⟨fun v => (coefficient K L R c hfaces v).symm (b.1 v), by
    apply (gauge_label_conditions K L R c hfaces vertices fixed _).mpr
    simpa only [AddEquiv.apply_symm_apply] using b.2⟩
  left_inv b := by apply Subtype.ext; funext v; exact AddEquiv.symm_apply_apply _ _
  right_inv b := by apply Subtype.ext; funext v; exact AddEquiv.apply_symm_apply _ _
  map_add' b a := by apply Subtype.ext; funext v; exact map_add _ _ _

/-- Forward labels retain every original vertex vector, including labels acting trivially. -/
theorem gaugeLabelEquivalence_value
    (b : supportedC0 (tower K L R c hfaces) vertices fixed) (v : K.Vertex) :
    (gaugeLabelEquivalence K L R c hfaces vertices fixed b).1 v =
      coefficient K L R c hfaces v (b.1 v) := rfl

/-- Inverse labels restore every full original kernel coordinate at every vertex. -/
theorem gaugeLabelEquivalence_inverse_value (b : gaugeLabels K R vertices fixed) (v : K.Vertex) :
    ((gaugeLabelEquivalence K L R c hfaces vertices fixed).symm b).1 v =
      (coefficient K L R c hfaces v).symm (b.1 v) := rfl

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
