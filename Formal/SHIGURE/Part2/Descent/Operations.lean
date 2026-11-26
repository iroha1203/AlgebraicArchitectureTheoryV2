import Formal.SHIGURE.Part2.Descent.Tensor
import Formal.SHIGURE.Part2.Realizations.TensorCoefficientExtension

/-! # Effective descent of finite operations

Lemma B.5 reduces a multilinear operation to the linear map on its
actual finite tensor of inputs. The comparison of B.4 handles compatible
maps, while the tensor comparison of B.3 identifies their domains.

## Implementation notes

The finite tensor is the same `PiTensorProduct` used for the typed
arity in Part II. Its universal equivalence with mathlib multilinear
maps includes the empty arity. The source module of a designated
element is the regular module with standard descent.
-/

namespace SHIGURE.CoefficientDescent

open TensorProduct CategoryTheory PiTensorProduct TensorRealization
open scoped TensorProduct

noncomputable section

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {S : Type u} [Module.FaithfullyFlat A B]

/-- The native carriers of a family of descent data. -/
def nativeFamily (D : S → DescentModule A B) (s : S) : ModuleCat.{u} B :=
  ModuleCat.of B (D s).carrier

/-- The family of actual fixed-vector modules assigned by B.4. -/
def fixedFamily (D : S → DescentModule A B) (s : S) : ModuleCat.{u} A :=
  ModuleCat.of A (D s).datum.toCoaction.descended

/-- Extension of the base unit is the empty native input tensor. -/
private def emptyInputComparison (D : S → DescentModule A B) :
    (B ⊗[A] A) ≃ₗ[B] InputTensor B (nativeFamily D) [] :=
  AlgebraTensorModule.rid A B B ≪≫ₗ (inputTensorUnit B (nativeFamily D)).symm

/-- Equip the actual finite input tensor with the iterated tensors of its native overlaps. -/
def inputDatum (D : S → DescentModule A B) :
    (Γ : List S) → Datum A B (InputTensor B (nativeFamily D) Γ)
  | [] => (standardDatum (A := A) (B := B) (M := A)).transport (emptyInputComparison D)
  | s :: Γ => ((D s).datum.tensor (inputDatum D Γ)).transport (inputTensorCons B (nativeFamily D) s Γ).symm

/-- The descended native input tensor is the finite tensor of the fixed-vector modules. -/
def inputDescendedEquiv (D : S → DescentModule A B) :
    (Γ : List S) → InputTensor A (fixedFamily D) Γ ≃ₗ[A] (inputDatum D Γ).toCoaction.descended
  | [] => inputTensorUnit A (fixedFamily D) ≪≫ₗ standardUnitEquiv (A := A) (B := B) (M := A) ≪≫ₗ
    Datum.descendEquiv _ _ (emptyInputComparison D) (Datum.transport_compatible _ _)
  | s :: Γ => inputTensorCons A (fixedFamily D) s Γ ≪≫ₗ
    TensorProduct.congr (.refl A _) (inputDescendedEquiv D Γ) ≪≫ₗ
    (D s).datum.tensorDescendedEquiv (inputDatum D Γ) ≪≫ₗ
    Datum.descendEquiv _ _ (inputTensorCons B (nativeFamily D) s Γ).symm (Datum.transport_compatible _ _)

/-- The finite input comparison preserves every pure tensor of fixed vectors. -/
theorem inputDescendedEquiv_tprod (D : S → DescentModule A B) (Γ : List S)
    (x : ∀ i : TensorPosition Γ, fixedFamily D i.1) :
    (inputDescendedEquiv D Γ (tprod A x)).val = tprod B (fun i => (x i).val) := by
  induction Γ with
  | nil =>
    simp only [inputDescendedEquiv, LinearEquiv.trans_apply, inputTensorUnit_tprod, Datum.descendEquiv_apply_val]
    change emptyInputComparison D ((1 : B) ⊗ₜ[A] (1 : A)) = _
    apply (inputTensorUnit B (nativeFamily D)).injective
    simp only [emptyInputComparison, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      AlgebraTensorModule.rid_tmul, one_smul]
    exact (inputTensorUnit_tprod B (nativeFamily D) (fun i => (x i).val)).symm
  | cons s Γ ih =>
    let tip : (D s).datum.toCoaction.descended := x ⟨s, .here⟩
    let xs (i : TensorPosition Γ) : fixedFamily D i.1 := x ⟨i.1, .there i.2⟩
    let tail := inputDescendedEquiv D Γ (tprod A xs)
    let e := inputTensorCons B (nativeFamily D) s Γ
    let z := (D s).datum.tensorDescendedEquiv (inputDatum D Γ) (tip ⊗ₜ[A] tail)
    apply e.injective
    simp only [inputDescendedEquiv, LinearEquiv.trans_apply, inputTensorCons_tprod,
      TensorProduct.congr_tmul, LinearEquiv.refl_apply, Datum.descendEquiv_apply_val]
    change e (e.symm z.val) = e (tprod B (fun i => (x i).val))
    rw [e.apply_symm_apply]
    calc
      z.val = tip.val ⊗ₜ[B] tail.val :=
        (D s).datum.tensorDescendedEquiv_tmul (inputDatum D Γ) tip tail
      _ = tip.val ⊗ₜ[B] tprod B (fun i => (xs i).val) :=
        congrArg (fun t => tip.val ⊗ₜ[B] t) (ih xs)
      _ = e (tprod B (fun i => (x i).val)) :=
        (inputTensorCons_tprod B (nativeFamily D) (fun i => (x i).val)).symm

/-- Taking the finite tensor of compatible sort maps respects the iterated native overlap. -/
theorem inputMap_compatible (D E : S → DescentModule A B) (Γ : List S)
    (f : ∀ s, (D s).carrier →ₗ[B] (E s).carrier)
    (hf : ∀ s, (D s).datum.Compatible (E s).datum (f s)) :
    (inputDatum D Γ).Compatible (inputDatum E Γ) (PiTensorProduct.map (fun i : TensorPosition Γ => f i.1)) := by
  induction Γ with
  | nil =>
    let d := standardDatum (A := A) (B := B) (M := A)
    let e := emptyInputComparison D
    let e' := emptyInputComparison E
    have compatible := d.transport_map_compatible d e e' LinearMap.id d.compatible_id
    change (d.transport e).Compatible (d.transport e') _
    convert compatible using 1
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    change PiTensorProduct.map (fun i : TensorPosition [] => f i.1) (tprod B x) =
      e' (e.symm (tprod B x))
    have source : e ((1 : B) ⊗ₜ[A] (1 : A)) = tprod B x := by
      apply (inputTensorUnit B (nativeFamily D)).injective
      simp only [e, emptyInputComparison, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
        AlgebraTensorModule.rid_tmul, one_smul, inputTensorUnit_tprod]
    rw [← source, e.symm_apply_apply]
    rw [PiTensorProduct.map_tprod]
    apply (inputTensorUnit B (nativeFamily E)).injective
    simp only [e', emptyInputComparison, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      AlgebraTensorModule.rid_tmul, one_smul]
    exact inputTensorUnit_tprod B (nativeFamily E) (fun i => f i.1 (x i))
  | cons s Γ ih =>
    let e := inputTensorCons B (nativeFamily D) s Γ
    let e' := inputTensorCons B (nativeFamily E) s Γ
    let F := PiTensorProduct.map (fun i : TensorPosition Γ => f i.1)
    have compatible := ((D s).datum.tensor (inputDatum D Γ)).transport_map_compatible
      ((E s).datum.tensor (inputDatum E Γ)) e.symm e'.symm (TensorProduct.map (f s) F)
      ((D s).datum.tensor_map_compatible (inputDatum D Γ) (E s).datum (inputDatum E Γ) (f s) F (hf s) ih)
    change (((D s).datum.tensor (inputDatum D Γ)).transport e.symm).Compatible
      (((E s).datum.tensor (inputDatum E Γ)).transport e'.symm) _
    convert compatible using 1
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    change PiTensorProduct.map (fun i : TensorPosition (s :: Γ) => f i.1) (tprod B x) =
      e'.symm (TensorProduct.map (f s) F (e (tprod B x)))
    apply e'.injective
    rw [e'.apply_symm_apply, PiTensorProduct.map_tprod]
    have input := inputTensorCons_tprod B (nativeFamily D) x
    have output := inputTensorCons_tprod B (nativeFamily E) (fun i => f i.1 (x i))
    change _ = TensorProduct.map (f s) F ((inputTensorCons B (nativeFamily D) s Γ) (tprod B x))
    rw [input, TensorProduct.map_tmul]
    exact output.trans (congrArg (fun t => f s (x ⟨s, .here⟩) ⊗ₜ[B] t)
      (PiTensorProduct.map_tprod (fun i : TensorPosition Γ => f i.1) (fun i => x ⟨i.1, .there i.2⟩)).symm)

/-- The comparison for the finite input tensor intertwines compatible sort maps. -/
theorem inputMap_natural (D E : S → DescentModule A B) (Γ : List S)
    (f : ∀ s, (D s).carrier →ₗ[B] (E s).carrier)
    (hf : ∀ s, (D s).datum.Compatible (E s).datum (f s)) :
    (inputDescendedEquiv E Γ).toLinearMap.comp
      (PiTensorProduct.map (fun i : TensorPosition Γ => (D i.1).datum.descendMap (E i.1).datum (f i.1) (hf i.1))) =
    ((inputDatum D Γ).descendMap (inputDatum E Γ) (PiTensorProduct.map (fun i : TensorPosition Γ => f i.1))
      (inputMap_compatible D E Γ f hf)).comp (inputDescendedEquiv D Γ).toLinearMap := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  apply Subtype.ext
  change (inputDescendedEquiv E Γ (PiTensorProduct.map
      (fun i : TensorPosition Γ => (D i.1).datum.descendMap (E i.1).datum (f i.1) (hf i.1)) (tprod A x))).val =
    ((inputDatum D Γ).descendMap (inputDatum E Γ) (PiTensorProduct.map (fun i : TensorPosition Γ => f i.1))
      (inputMap_compatible D E Γ f hf) (inputDescendedEquiv D Γ (tprod A x))).val
  rw [PiTensorProduct.map_tprod, Datum.descendMap_apply]
  let fixed (i : TensorPosition Γ) : fixedFamily E i.1 :=
    (D i.1).datum.descendMap (E i.1).datum (f i.1) (hf i.1) (x i)
  have first := inputDescendedEquiv_tprod E Γ fixed
  have second := inputDescendedEquiv_tprod D Γ x
  calc
    _ = tprod B (fun i => (fixed i).val) := first
    _ = (PiTensorProduct.map (fun i : TensorPosition Γ => f i.1)) (tprod B (fun i => (x i).val)) :=
      (PiTensorProduct.map_tprod (fun i : TensorPosition Γ => f i.1) (fun i => (x i).val)).symm
    _ = _ := congrArg _ second.symm

/-- An operation on the cover is compatible if its tensor linearization respects the actual overlap. -/
def CompatibleOperation (D : S → DescentModule A B) (Γ : List S) (E : DescentModule A B)
    (op : MultilinearMap B (fun i : TensorPosition Γ => nativeFamily D i.1) E.carrier) : Prop :=
  (inputDatum D Γ).Compatible E.datum (PiTensorProduct.lift op)

/-- B.5 gives the full correspondence of native compatible operations and descended operations. -/
def operationEquiv (D : S → DescentModule A B) (Γ : List S) (E : DescentModule A B) :
    { op : MultilinearMap B (fun i : TensorPosition Γ => nativeFamily D i.1) E.carrier //
        CompatibleOperation D Γ E op } ≃
      MultilinearMap A (fun i : TensorPosition Γ => fixedFamily D i.1) E.datum.toCoaction.descended :=
  (Equiv.subtypeEquiv PiTensorProduct.lift.toEquiv (fun _ => Iff.rfl)).trans
    (((inputDatum D Γ).descendMapEquiv E.datum).trans
      ((LinearEquiv.arrowCongr (inputDescendedEquiv D Γ).symm (.refl A _)).toEquiv.trans
        PiTensorProduct.lift.symm.toEquiv))

/-- The descended operation on fixed inputs has exactly the original native value. -/
theorem operationEquiv_apply (D : S → DescentModule A B) (Γ : List S) (E : DescentModule A B)
    (op : MultilinearMap B (fun i : TensorPosition Γ => nativeFamily D i.1) E.carrier)
    (compatible : CompatibleOperation D Γ E op) (x : ∀ i : TensorPosition Γ, fixedFamily D i.1) :
    (operationEquiv D Γ E ⟨op, compatible⟩ x).val = op (fun i => (x i).val) := by
  change ((inputDatum D Γ).descendMap E.datum (PiTensorProduct.lift op) compatible
    (inputDescendedEquiv D Γ (tprod A x))).val = _
  rw [Datum.descendMap_apply, inputDescendedEquiv_tprod]
  exact PiTensorProduct.lift.tprod (φ := op) _

/-- The native scalar module carries the standard descent induced by the base scalar module. -/
def unitDatum (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] : Datum A B B :=
  (standardDatum (A := A) (B := B) (M := A)).transport (AlgebraTensorModule.rid A B B)

omit [Module.FaithfullyFlat A B] in
/-- The standard coaction of the scalar module inserts the unit. -/
theorem unitDatum_coaction (b : B) : (unitDatum A B).coactionMap b = b ⊗ₜ[A] (1 : B) := by
  change ((standardDatum (A := A) (B := B) (M := A)).transport
    (AlgebraTensorModule.rid A B B)).overlap (b ⊗ₜ[A] (1 : B)) = _
  rw [Datum.transport_overlap_tmul]
  have expand : (AlgebraTensorModule.rid A B B).symm b = b ⊗ₜ[A] (1 : A) := rfl
  rw [expand]
  change ((AlgebraTensorModule.rid A B B).restrictScalars A).toLinearMap.lTensor B
    (standardOverlap (A := A) (B := B) (M := A) ((b ⊗ₜ[A] (1 : A)) ⊗ₜ[A] (1 : B))) = _
  rw [standardOverlap_tmul, LinearMap.lTensor_tmul, LinearEquiv.coe_coe,
    LinearEquiv.restrictScalars_apply, AlgebraTensorModule.rid_tmul, one_smul]

variable {X : Type u} [AddCommGroup X] [Module A X] [Module B X] [IsScalarTower A B X]

omit [Module.FaithfullyFlat A B] in
/-- A designated element is compatible exactly when the associated linear map from the scalar module is. -/
theorem element_compatible_iff (D : Datum A B X) (x : X) :
    (unitDatum A B).Compatible D (LinearMap.toSpanSingleton B X x) ↔ x ∈ D.toCoaction.descended := by
  rw [(unitDatum A B).compatible_iff_coaction D _, D.toCoaction.descended_iff]
  constructor
  · intro compatible
    have atOne := compatible 1
    rw [unitDatum_coaction, LinearMap.baseChange_tmul, LinearMap.restrictScalars_apply,
      LinearMap.toSpanSingleton_apply_one] at atOne
    exact atOne.symm
  · intro fixed b
    change D.coactionMap x = 1 ⊗ₜ[A] x at fixed
    rw [unitDatum_coaction, LinearMap.baseChange_tmul, LinearMap.restrictScalars_apply,
      LinearMap.toSpanSingleton_apply_one]
    change b ⊗ₜ[A] x = D.coactionMap (b • x)
    rw [map_smul, fixed, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

/-- Chosen elements compatible with the overlap are exactly the elements of the descended module. -/
def elementEquiv (D : Datum A B X) :
    {x : X // (unitDatum A B).Compatible D (LinearMap.toSpanSingleton B X x)} ≃ D.toCoaction.descended :=
  ⟨fun x => ⟨x.val, (element_compatible_iff D x.val).1 x.property⟩,
    fun x => ⟨x.val, (element_compatible_iff D x.val).2 x.property⟩, fun _ => rfl, fun _ => rfl⟩

end

end SHIGURE.CoefficientDescent
