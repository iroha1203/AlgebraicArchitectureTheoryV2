import Formal.SHIGURE.Part2.Realizations.TensorCoefficientExtension

/-!
# Tensor scalar extension on structures and arrows

The maps on carriers are the usual linear scalar extension. Unit and tower
comparisons preserve each operation by evaluating on the unit tensors,
which determine the extended multilinear maps.
-/

open CategoryTheory
open scoped TensorProduct

universe u

noncomputable section

namespace SHIGURE.TensorRealization

variable {k R : Type u} [CommRing k] [CommRing R] [Algebra k R]
variable {sig : Signature.{u}}

/-- Extend a commuting primitive square by checking its unit-coefficient tuples. -/
private theorem extendOperation_natural {K : Type u} {Γ : List K}
    {M N : K → ModuleCat.{u} k} {P Q : ModuleCat.{u} k}
    (f : ∀ s, M s →ₗ[k] N s) (g : P →ₗ[k] Q)
    (a : MultilinearMap k (fun i : TensorPosition Γ => M i.1) P)
    (b : MultilinearMap k (fun i : TensorPosition Γ => N i.1) Q)
    (h : ∀ x, g (a x) = b (fun i => f i.1 (x i))) :
    (g.baseChange R).compMultilinearMap (extendOperation k M R a) =
      (extendOperation k N R b).compLinearMap (fun i => (f i.1).baseChange R) := by
  apply multilinear_ext_unit k M R (P := ModuleCat.of R (R ⊗[k] Q))
  intro x
  change g.baseChange R (extendOperation k M R a (fun i => (1 : R) ⊗ₜ[k] x i)) =
    extendOperation k N R b (fun i => (f i.1).baseChange R ((1 : R) ⊗ₜ[k] x i))
  rw [extendOperation_unit, LinearMap.baseChange_tmul, h x]
  have e : (fun i : TensorPosition Γ => (f i.1).baseChange R ((1 : R) ⊗ₜ[k] x i)) =
      fun i => (1 : R) ⊗ₜ[k] f i.1 (x i) :=
    funext fun i => LinearMap.baseChange_tmul _ _ _
  rw [e, extendOperation_unit]

/-- Extend a structure-preserving linear family to the new coefficients. -/
def extendStructureMap (R : Type u) [CommRing R] [Algebra k R]
    {A B : TensorStructure k sig} (f : TensorStructure.Hom A B) :
    TensorStructure.Hom (extendStructure k R A) (extendStructure k R B) where
  onSort s := (f.onSort s).baseChange R
  preservesTotal op x := MultilinearMap.congr_fun
    (extendOperation_natural f.onSort (f.onSort _) (A.total op) (B.total op)
      (f.preservesTotal op)) x
  preservesQuantity q x := MultilinearMap.congr_fun
    (extendOperation_natural f.onSort (f.onSort _) (A.quantity q) (B.quantity q)
      (f.preservesQuantity q)) x

/-- Changing coefficients is functorial on all structured arrows. -/
def extendStructureFunctor (k R : Type u) [CommRing k] [CommRing R] [Algebra k R]
    (sig : Signature.{u}) : TensorStructure k sig ⥤ TensorStructure R sig where
  obj := extendStructure k R
  map := extendStructureMap R
  map_id _ := TensorStructure.Hom.ext (funext fun _ => LinearMap.baseChange_id (A := R))
  map_comp f g := TensorStructure.Hom.ext (funext fun s =>
    LinearMap.baseChange_comp (A := R) (f.onSort s) (g.onSort s))

/-- Read the carrier map of a changed structure arrow as mathlib scalar extension at that sort. -/
@[simp]
theorem extendStructureMap_onSort {A B : TensorStructure k sig} (f : A ⟶ B) (s : sig.SortType) :
    (extendStructureMap R f).onSort s = (f.onSort s).baseChange R := rfl

/-- Reduce the object action of the scalar extension functor to the extended structure. -/
@[simp]
theorem extendStructureFunctor_obj (A : TensorStructure k sig) :
    (extendStructureFunctor k R sig).obj A = extendStructure k R A := rfl

/-- Reduce the arrow action of the scalar extension functor to the extended structure arrow. -/
@[simp]
theorem extendStructureFunctor_map {A B : TensorStructure k sig} (f : A ⟶ B) :
    (extendStructureFunctor k R sig).map f = extendStructureMap R f := rfl

end SHIGURE.TensorRealization
