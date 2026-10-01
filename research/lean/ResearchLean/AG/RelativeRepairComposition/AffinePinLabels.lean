import ResearchLean.AG.RelativeRepairComposition.AffineSingletonEnvironment
import ResearchLean.AG.RelativeRepairComposition.NativeAffineGroupoid

/-!
# All original vertex labels surviving the singleton environment

Pins impose the full old zero-coboundary condition. They add no fixed vertices
and do not discard nonzero stabilizer vectors. The same vectors label the real
pointwise conjugation arrows.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine.ParallelPins
open TransportCoherence AbelianLiftingObstruction
universe uk uA uG
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable (K : FiniteTransportPresentation.{uG})
variable (R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)
variable (fixed : Set (EdgeName (K := K))) (vertices : Set K.Vertex)
variable (t : EdgeName (K := K) → A)
local notation "J" => ParallelPinGeometry.presentation K

/-- Every permitted pin label is precisely a full old label preserving all shared edges. -/
theorem pin_label_conditions (b : K.Vertex → A) :
    b ∈ gaugeLabels J (reference K R t) vertices (forbidden K fixed) ↔
      b ∈ gaugeLabels K R vertices Set.univ := by
  constructor
  · intro hb
    refine ⟨hb.1, ?_⟩
    intro e _
    have h := hb.2 (ParallelPinGeometry.pinEdgeName K e) (Or.inr ⟨e, rfl⟩)
    change b e.2.1 = (reference K R t (.inr e.2.2)).linear (b e.1) at h
    rw [pin_linear] at h
    exact h
  · intro hb
    refine ⟨hb.1, ?_⟩
    intro e he
    rcases he with ⟨a, _, rfl⟩ | ⟨a, rfl⟩
    · exact hb.2 a trivial
    · change b a.2.1 = (reference K R t (.inr a.2.2)).linear (b a.1)
      rw [pin_linear]
      exact hb.2 a trivial

/-- The entire label subgroup agrees, including every ineffective or nonzero stabilizer. -/
theorem pin_label_subgroup :
    gaugeLabels J (reference K R t) vertices (forbidden K fixed) =
      gaugeLabels K R vertices Set.univ := by
  apply AddSubgroup.ext
  exact pin_label_conditions K R fixed vertices t

/-- The unchanged vector family supplies mutually inverse full-label coordinates. -/
def pinLabelEquivalence :
    gaugeLabels J (reference K R t) vertices (forbidden K fixed) ≃+
      gaugeLabels K R vertices Set.univ where
  toFun b := ⟨b.1, (pin_label_conditions K R fixed vertices t b.1).mp b.2⟩
  invFun b := ⟨b.1, (pin_label_conditions K R fixed vertices t b.1).mpr b.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- Forward labels preserve the actual vector at every original vertex. -/
theorem pin_label_value
    (b : gaugeLabels J (reference K R t) vertices (forbidden K fixed)) (v : K.Vertex) :
    (pinLabelEquivalence K R fixed vertices t b).1 v = b.1 v := rfl

/-- Every full old zero-coboundary label fixes every real shared repair by conjugation. -/
theorem whole_label_stabilizes (c : K.TwoCell → A)
    (b : gaugeLabels K R vertices Set.univ) (s : Repair K R c fixed)
    {i j : K.Vertex} (e : K.Edge i j) :
    translation (k := k) (b.1 j) * s.operation e * translation (k := k) (-b.1 i) =
      s.operation e := by
  apply AffineEquiv.ext
  intro x
  change b.1 j + s.operation e (-b.1 i + x) = s.operation e x
  calc
    b.1 j + s.operation e (-b.1 i + x) =
        b.1 j + ((s.operation e).linear (-b.1 i + x) + s.operation e 0) := by
          rw [operation_apply]
    _ = (s.operation e).linear x + s.operation e 0 := by
      rw [map_add, map_neg, s.linear, ← b.2.2 ⟨i,j,e⟩ trivial]
      abel
    _ = s.operation e x := (operation_apply (s.operation e) x).symm

/-- Each old full stabilizer vector gives an actual arrow, without identifying distinct labels. -/
def wholeLabelArrow (c : K.TwoCell → A)
    (b : gaugeLabels K R vertices Set.univ) (s : Repair K R c fixed) :
    Arrow K R c vertices fixed s s :=
  ⟨⟨b.1, ⟨b.2.1, fun e _ => b.2.2 e trivial⟩⟩,
    fun {_ _} e => (whole_label_stabilizes K R fixed vertices c b s e).symm⟩

/-- The actual stabilizer arrow retains every vector of the original full label. -/
theorem whole_label_arrow_value (c : K.TwoCell → A)
    (b : gaugeLabels K R vertices Set.univ) (s : Repair K R c fixed) (v : K.Vertex) :
    (wholeLabelArrow K R fixed vertices c b s).1.1 v = b.1 v := rfl

end AAT.AG.RelativeRepairComposition.NativeAffine.ParallelPins
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.NativeAffine.ParallelPins
