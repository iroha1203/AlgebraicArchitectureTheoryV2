import ResearchLean.AG.RelativeRepairComposition.NativeAffineGaugeLabels
import ResearchLean.AG.RelativeRepairComposition.InterfaceFunctorInverses

/-! # Full affine repair arrows on the original vertices and edges

## Implementation notes

The gauge action is transported through the full object and label equivalences
so that the established native action laws apply on the same labels. Defining a
second action directly by pointwise conjugation would duplicate those laws and
their correspondence proofs. The independent Arrow predicate and gauge_value
still compare the transported action with the actual affine conjugation formula;
labels that act trivially remain distinct morphisms in ActionCategory.
-/
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
local notation "T" => tower K L R c hfaces
local notation "Q" => repairEquivalence K L R c hfaces fixed
local notation "B" => gaugeLabelEquivalence K L R c hfaces vertices fixed

/-- Reidentifying each original vertex changes the real edge by target and inverse source translations. -/
theorem native_gauge_value (b : supportedC0 (T) vertices fixed)
    (s : SupportedRepair (T) fixed) {i j : K.Vertex} (e : K.Edge i j) :
    ((Q) (repairGauge (T) vertices fixed b s)).operation e =
      translation (k := k) (((B) b).1 j) * ((Q) s).operation e *
        translation (k := k) (-((B) b).1 i) := by
  have h := (T).vertexGauge_edge_arrow b.1 s.1 e
  change (show Operations k A from
    (selectedUpper K _ _ (original K L) ((T).vertexGauge b.1 s.1).choice).edgeLift e) =
      (show Operations k A from
        FiberAut.hom (kernelInclusion _ _ ((T).original.object j)
          (Additive.toMul (b.1 j)))) *
      ((show Operations k A from
        (selectedUpper K _ _ (original K L) s.1.choice).edgeLift e) *
        (show Operations k A from
          FiberAut.hom (kernelInclusion _ _ ((T).original.object i)
            (Additive.toMul (-b.1 i))))) at h
  rw [coefficient_inclusion K L R c hfaces j (b.1 j),
    coefficient_inclusion K L R c hfaces i (-b.1 i), map_neg] at h
  exact h.trans (mul_assoc _ _ _).symm

/-- Full vector labels act on independent affine repairs through their original native reidentifications. -/
noncomputable def gauge (b : gaugeLabels K R vertices fixed) (s : Repair K R c fixed) :
    Repair K R c fixed :=
  (Q) (repairGauge (T) vertices fixed ((B).symm b) ((Q).symm s))

/-- Every independent affine gauge evaluates to the stated actual edge formula. -/
theorem gauge_value (b : gaugeLabels K R vertices fixed) (s : Repair K R c fixed)
    {i j : K.Vertex} (e : K.Edge i j) :
    (gauge K L R c hfaces vertices fixed b s).operation e =
      translation (k := k) (b.1 j) * s.operation e * translation (k := k) (-b.1 i) := by
  unfold gauge
  rw [native_gauge_value, AddEquiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The full label action obeys addition without quotienting out stabilizer labels. -/
noncomputable def gaugeAddAction :
    AddAction (gaugeLabels K R vertices fixed) (Repair K R c fixed) where
  vadd := gauge K L R c hfaces vertices fixed
  zero_vadd s := by
    change (Q) (repairGauge (T) vertices fixed ((B).symm 0) ((Q).symm s)) = s
    rw [map_zero]
    change (Q) ((0 : supportedC0 (T) vertices fixed) +ᵥ ((Q).symm s)) = s
    rw [zero_vadd, Equiv.apply_symm_apply]
  add_vadd b a s := by
    change (Q) (repairGauge (T) vertices fixed ((B).symm (b + a)) ((Q).symm s)) =
      (Q) (repairGauge (T) vertices fixed ((B).symm b)
        ((Q).symm ((Q) (repairGauge (T) vertices fixed ((B).symm a) ((Q).symm s)))))
    rw [Equiv.symm_apply_apply, map_add]
    change (Q) ((((B).symm b) + ((B).symm a)) +ᵥ ((Q).symm s)) =
      (Q) (((B).symm b) +ᵥ (((B).symm a) +ᵥ ((Q).symm s)))
    rw [add_vadd]

/-- Independent actual gauge arrows retain every vertex vector and all original real edge equalities. -/
def Arrow (s t : Repair K R c fixed) :=
  {b : gaugeLabels K R vertices fixed // ∀ {i j : K.Vertex} (e : K.Edge i j),
    t.operation e = translation (k := k) (b.1 j) * s.operation e *
      translation (k := k) (-b.1 i)}

/-- The independent pointwise real arrow equations are precisely the full action equation. -/
theorem gauge_eq_iff (b : gaugeLabels K R vertices fixed) (s t : Repair K R c fixed) :
    gauge K L R c hfaces vertices fixed b s = t ↔
      ∀ {i j : K.Vertex} (e : K.Edge i j),
        t.operation e = translation (k := k) (b.1 j) * s.operation e *
          translation (k := k) (-b.1 i) := by
  constructor
  · intro h i j e
    rw [← h, gauge_value]
  · intro h
    apply Repair.ext
    intro i j e
    exact (gauge_value K L R c hfaces vertices fixed b s e).trans (h e).symm

/-- Native action category with all independent original affine repair objects and full translation arrows. -/
abbrev Groupoid :=
  letI := gaugeAddAction K L R c hfaces vertices fixed
  ActionCategory (Multiplicative (gaugeLabels K R vertices fixed)) (Repair K R c fixed)

/-- The object and full label coordinates intertwine the native actual gauge action. -/
theorem repair_equivariant (b : supportedC0 (T) vertices fixed)
    (s : SupportedRepair (T) fixed) :
    (Q) (repairGauge (T) vertices fixed b s) =
      gauge K L R c hfaces vertices fixed ((B) b) ((Q) s) := by
  change (Q) (repairGauge (T) vertices fixed b s) =
    (Q) (repairGauge (T) vertices fixed ((B).symm ((B) b)) ((Q).symm ((Q) s)))
  rw [AddEquiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- Every original native actual repair and full gauge arrow corresponds to a real affine repair and arrow. -/
noncomputable def groupoidEquivalence :
    RepairGroupoid (T) vertices fixed ≌ Groupoid K L R c hfaces vertices fixed := by
  letI := gaugeAddAction K L R c hfaces vertices fixed
  exact changedLabelEquivalence (B).toMultiplicative (Q)
    (fun b s => repair_equivariant K L R c hfaces vertices fixed b.toAdd s)

/-- The native real-affine hom type is exactly the independently defined full-label real edge equations. -/
noncomputable def arrowEquivalence (s t : Groupoid K L R c hfaces vertices fixed) :
    letI := gaugeAddAction K L R c hfaces vertices fixed
    (s ⟶ t) ≃ Arrow K R c vertices fixed s.back t.back := by
  letI := gaugeAddAction K L R c hfaces vertices fixed
  exact {
    toFun := fun b => ⟨b.1.toAdd,
      (gauge_eq_iff K L R c hfaces vertices fixed b.1.toAdd s.back t.back).mp b.2⟩
    invFun := fun b => ⟨Multiplicative.ofAdd b.1,
      (gauge_eq_iff K L R c hfaces vertices fixed b.1 s.back t.back).mpr b.2⟩
    left_inv := fun _ => Subtype.ext rfl
    right_inv := fun _ => Subtype.ext rfl }

/-- Mapping each full original gauge arrow keeps its real vector at every original vertex. -/
theorem groupoid_forward_label {s t : RepairGroupoid (T) vertices fixed} (b : s ⟶ t)
    (v : K.Vertex) :
    ((groupoidEquivalence K L R c hfaces vertices fixed).functor.map b).1.toAdd.1 v =
      coefficient K L R c hfaces v (b.1.toAdd.1 v) := rfl

/-- Inverting each full real gauge arrow restores its original kernel coordinate at every vertex. -/
theorem groupoid_inverse_label {s t : Groupoid K L R c hfaces vertices fixed} (b : s ⟶ t)
    (v : K.Vertex) :
    ((groupoidEquivalence K L R c hfaces vertices fixed).inverse.map b).1.toAdd.1 v =
      (coefficient K L R c hfaces v).symm (b.1.toAdd.1 v) := rfl

/-- The inverse functor restores all original choices and every full gauge label exactly. -/
theorem groupoid_functor_inverse :
    (groupoidEquivalence K L R c hfaces vertices fixed).functor ⋙
      (groupoidEquivalence K L R c hfaces vertices fixed).inverse =
        𝟭 (RepairGroupoid (T) vertices fixed) := by
  letI := gaugeAddAction K L R c hfaces vertices fixed
  exact changed_label_functor_inverse (B).toMultiplicative (Q)
    (fun b s => repair_equivariant K L R c hfaces vertices fixed b.toAdd s)

/-- The forward functor restores all actual affine edge values and every full translation label exactly. -/
theorem groupoid_inverse_functor :
    (groupoidEquivalence K L R c hfaces vertices fixed).inverse ⋙
      (groupoidEquivalence K L R c hfaces vertices fixed).functor =
        𝟭 (Groupoid K L R c hfaces vertices fixed) := by
  letI := gaugeAddAction K L R c hfaces vertices fixed
  exact changed_label_inverse_functor (B).toMultiplicative (Q)
    (fun b s => repair_equivariant K L R c hfaces vertices fixed b.toAdd s)

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
