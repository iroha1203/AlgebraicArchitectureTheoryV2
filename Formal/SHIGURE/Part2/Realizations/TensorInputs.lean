import Formal.SHIGURE.Part2.Realizations.TensorExpressions
import Mathlib.Data.Finite.Sum

/-!
# Typed input tensors

An empty arity uses the scalar module. Adding an input takes the binary
tensor product with the carrier of that variable. The comparisons are
given by the mathlib equivalences on the indexed tensor product.
-/

open CategoryTheory TensorProduct PiTensorProduct
open scoped TensorProduct

universe u

noncomputable section

namespace SHIGURE.TensorRealization

variable {K : Type u}

/-- Positions in an extended context consist of the new position and the old positions. -/
def consPositions (s : K) (Γ : List K) :
    PUnit.{1} ⊕ TensorPosition Γ ≃ TensorPosition (s :: Γ) where
  toFun
    | .inl _ => ⟨s, .here⟩
    | .inr ⟨t, i⟩ => ⟨t, .there i⟩
  invFun
    | ⟨_, .here⟩ => .inl PUnit.unit
    | ⟨t, .there i⟩ => .inr ⟨t, i⟩
  left_inv
    | .inl ⟨⟩ => rfl
    | .inr ⟨_, _⟩ => rfl
  right_inv
    | ⟨_, .here⟩ => rfl
    | ⟨_, .there _⟩ => rfl

/-- A typed arity has finitely many argument positions. -/
instance finitePositions (Γ : List K) : Finite (TensorPosition Γ) := by
  induction Γ with
  | nil =>
    letI : IsEmpty (TensorPosition ([] : List K)) := ⟨fun i => nomatch i.2⟩
    infer_instance
  | cons s Γ ih =>
    letI := ih
    exact Finite.of_equiv _ (consPositions s Γ)

variable (k : Type u) [CommRing k] (M : K → ModuleCat.{u} k)

/-- The tensor of the carriers of a typed input context. -/
abbrev InputTensor (Γ : List K) :=
  ⨂[k] i : TensorPosition Γ, M i.1

/-- The tensor product of an empty family is the coefficient module. -/
def inputTensorUnit : InputTensor k M [] ≃ₗ[k] k :=
  letI : IsEmpty (TensorPosition ([] : List K)) := ⟨fun i => nomatch i.2⟩
  PiTensorProduct.isEmptyEquiv (TensorPosition ([] : List K))

/-- The empty pure tensor is the unit of the scalar module. -/
@[simp]
theorem inputTensorUnit_tprod (x : ∀ i : TensorPosition ([] : List K), M i.1) :
    inputTensorUnit k M (tprod k x) = 1 := by
  letI : IsEmpty (TensorPosition ([] : List K)) := ⟨fun i => nomatch i.2⟩
  exact PiTensorProduct.isEmptyEquiv_apply_tprod (TensorPosition ([] : List K)) x

/-- Split the first factor off an extended tensor context using mathlib's Sum comparison. -/
def inputTensorCons (s : K) (Γ : List K) :
    InputTensor k M (s :: Γ) ≃ₗ[k] M s ⊗[k] InputTensor k M Γ :=
  let e := consPositions s Γ
  (PiTensorProduct.reindex k (fun i : TensorPosition (s :: Γ) => M i.1) e.symm).trans
    ((PiTensorProduct.tmulEquivDep k (fun i => M (e i).1)).symm.trans
      (TensorProduct.congr
        (PiTensorProduct.subsingletonEquiv (R := k) (s := fun _ : PUnit.{1} => M s) PUnit.unit)
        (LinearEquiv.refl k _)))

/-- The first-factor comparison on pure tensors. -/
@[simp]
theorem inputTensorCons_tprod {s : K} {Γ : List K}
    (x : ∀ i : TensorPosition (s :: Γ), M i.1) :
    inputTensorCons k M s Γ (tprod k x) =
      x ⟨s, .here⟩ ⊗ₜ[k] tprod k (fun i : TensorPosition Γ => x ⟨i.1, .there i.2⟩) := by
  simp only [inputTensorCons, LinearEquiv.trans_apply, reindex_tprod]
  let e := consPositions s Γ
  let N (i : PUnit.{1} ⊕ TensorPosition Γ) := M (e i).1
  have h := tmulEquivDep_symm_apply (R := k) (N := fun i => (N i : Type u))
    (fun i => x (e i))
  change (TensorProduct.congr (subsingletonEquiv (R := k) (s := fun _ : PUnit.{1} => M s)
      PUnit.unit) (LinearEquiv.refl k (InputTensor k M Γ)))
    ((tmulEquivDep k (fun i => (N i : Type u))).symm (tprod k (fun i => x (e i)))) = _
  rw [h]
  rw [TensorProduct.congr_tmul]
  congr 1
  exact subsingletonEquiv_apply_tprod _ _

end SHIGURE.TensorRealization
