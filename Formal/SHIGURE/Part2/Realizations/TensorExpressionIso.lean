import Formal.SHIGURE.Part2.Realizations.TensorInputs
import Formal.SHIGURE.Part2.Realizations.TensorExpressions

/-! # Tensor shapes and structural transport along an actual realization isomorphism -/

namespace SHIGURE.TensorRealization

open CategoryTheory TensorProduct PiTensorProduct
open scoped TensorProduct

noncomputable section

universe u

variable {R : Type u} [CommRing R] {sig : Signature.{u}} {A B : TensorStructure R sig}

private def carrierFunctor (s : sig.SortType) : TensorStructure R sig ⥤ ModuleCat.{u} R where
  obj A := A.carrier s
  map f := ModuleCat.ofHom (f.onSort s)

variable (e : A ≅ B)

/-- An isomorphism of tensor realizations gives a linear equivalence on each carrier. -/
def structureCarrierEquiv (s : sig.SortType) : A.carrier s ≃ₗ[R] B.carrier s :=
  ((carrierFunctor s).mapIso e).toLinearEquiv

/-- Transport the actual module of each written tensor shape along the structure isomorphism. -/
def tensorShapeEquiv : (U : TensorShape sig.SortType) → U.module A ≃ₗ[R] U.module B
  | .unit => LinearEquiv.refl R R
  | .sort s => structureCarrierEquiv e s
  | .arguments Γ => PiTensorProduct.congr (fun i : TensorPosition Γ => structureCarrierEquiv e i.1)
  | .tensor U V => TensorProduct.congr (tensorShapeEquiv U) (tensorShapeEquiv V)

private theorem tensorShapeEquiv_tmul (U V : TensorShape sig.SortType) (x : U.module A) (y : V.module A) :
    tensorShapeEquiv e (.tensor U V) (x ⊗ₜ[R] y) =
      tensorShapeEquiv e U x ⊗ₜ[R] tensorShapeEquiv e V y :=
  TensorProduct.congr_tmul _ _ _ _

private theorem tensorShapeEquiv_tprod {Γ : List sig.SortType} (x : ∀ i : TensorPosition Γ, A.carrier i.1) :
    tensorShapeEquiv e (.arguments Γ) (tprod R x) = tprod R (fun i => structureCarrierEquiv e i.1 (x i)) :=
  PiTensorProduct.congr_tprod _ _

variable {U V : TensorShape sig.SortType}

/-- The equation for comparing maps of tensor shapes under structural transport. -/
abbrev ShapeMapsCommute (fA : U.module A →ₗ[R] V.module A) (fB : U.module B →ₗ[R] V.module B) : Prop :=
  (tensorShapeEquiv e V).toLinearMap.comp fA = fB.comp (tensorShapeEquiv e U).toLinearMap

private theorem total_natural (i : sig.Total) :
    ShapeMapsCommute e (U := .arguments (sig.totalArity i).inputs) (V := .sort (sig.totalArity i).output)
      (lift (A.total i)) (lift (B.total i)) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change structureCarrierEquiv e _ (lift (A.total i) (tprod R x)) =
    lift (B.total i) (tensorShapeEquiv e (.arguments (sig.totalArity i).inputs) (tprod R x))
  rw [lift.tprod, tensorShapeEquiv_tprod, lift.tprod]
  exact e.hom.preservesTotal i x

private theorem quantity_natural (q : sig.Quantity) :
    ShapeMapsCommute e (U := .arguments (sig.quantityArity q).inputs) (V := .sort (sig.quantityArity q).output)
      (lift (A.quantity q)) (lift (B.quantity q)) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change structureCarrierEquiv e _ (lift (A.quantity q) (tprod R x)) =
    lift (B.quantity q) (tensorShapeEquiv e (.arguments (sig.quantityArity q).inputs) (tprod R x))
  rw [lift.tprod, tensorShapeEquiv_tprod, lift.tprod]
  exact e.hom.preservesQuantity q x

private theorem swap_natural (X Y : TensorShape sig.SortType) :
    ShapeMapsCommute e (U := .tensor X Y) (V := .tensor Y X)
      (TensorProduct.comm R (X.module A) (Y.module A)).toLinearMap
      (TensorProduct.comm R (X.module B) (Y.module B)).toLinearMap := by
  apply TensorProduct.ext'
  intro x y
  change tensorShapeEquiv e (.tensor Y X) (y ⊗ₜ[R] x) =
    TensorProduct.comm R (X.module B) (Y.module B) (tensorShapeEquiv e (.tensor X Y) (x ⊗ₜ[R] y))
  rw [tensorShapeEquiv_tmul, tensorShapeEquiv_tmul]
  rfl

private theorem assoc_natural (X Y Z : TensorShape sig.SortType) :
    ShapeMapsCommute e (U := .tensor (.tensor X Y) Z) (V := .tensor X (.tensor Y Z))
      (TensorProduct.assoc R (X.module A) (Y.module A) (Z.module A)).toLinearMap
      (TensorProduct.assoc R (X.module B) (Y.module B) (Z.module B)).toLinearMap := by
  apply TensorProduct.ext'
  intro xy z
  induction xy using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    change tensorShapeEquiv e (.tensor X (.tensor Y Z)) (x ⊗ₜ[R] (y ⊗ₜ[R] z)) =
      TensorProduct.assoc R (X.module B) (Y.module B) (Z.module B)
        (tensorShapeEquiv e (.tensor (.tensor X Y) Z) ((x ⊗ₜ[R] y) ⊗ₜ[R] z))
    simp only [tensorShapeEquiv_tmul]
    rfl
  | add x y hx hy => simp only [add_tmul, map_add, hx, hy]

private theorem shapeMapsCommute_apply {X Y : TensorShape sig.SortType}
    {f : X.module A →ₗ[R] Y.module A} {g : X.module B →ₗ[R] Y.module B}
    (h : ShapeMapsCommute e (U := X) (V := Y) f g) (x : X.module A) :
    tensorShapeEquiv e Y (f x) = g (tensorShapeEquiv e X x) :=
  LinearMap.congr_fun h x

private theorem shapeMapsCommute_symm {X Y : TensorShape sig.SortType}
    (f : X.module A ≃ₗ[R] Y.module A) (g : X.module B ≃ₗ[R] Y.module B)
    (h : ShapeMapsCommute e (U := X) (V := Y) f.toLinearMap g.toLinearMap) :
    ShapeMapsCommute e (U := Y) (V := X) f.symm.toLinearMap g.symm.toLinearMap := by
  apply LinearMap.ext
  intro x
  change tensorShapeEquiv e X (f.symm x) = g.symm (tensorShapeEquiv e Y x)
  apply g.injective
  have hw := shapeMapsCommute_apply e h (f.symm x)
  change tensorShapeEquiv e Y (f (f.symm x)) = g (tensorShapeEquiv e X (f.symm x)) at hw
  rw [LinearEquiv.apply_symm_apply] at hw ⊢
  exact hw.symm

private theorem leftUnit_natural (X : TensorShape sig.SortType) :
    ShapeMapsCommute e (U := .tensor .unit X) (V := X)
      (TensorProduct.lid R (X.module A)).toLinearMap (TensorProduct.lid R (X.module B)).toLinearMap := by
  apply TensorProduct.ext'
  intro r x
  change tensorShapeEquiv e X (r • x) = TensorProduct.lid R (X.module B)
    (tensorShapeEquiv e (.tensor .unit X) (r ⊗ₜ[R] x))
  rw [tensorShapeEquiv_tmul, map_smul]
  rfl

private theorem rightUnit_natural (X : TensorShape sig.SortType) :
    ShapeMapsCommute e (U := .tensor X .unit) (V := X)
      (TensorProduct.rid R (X.module A)).toLinearMap (TensorProduct.rid R (X.module B)).toLinearMap := by
  apply TensorProduct.ext'
  intro x r
  change tensorShapeEquiv e X (r • x) = TensorProduct.rid R (X.module B)
    (tensorShapeEquiv e (.tensor X .unit) (x ⊗ₜ[R] r))
  rw [tensorShapeEquiv_tmul, map_smul]
  rfl

private theorem emptyArguments_natural :
    ShapeMapsCommute e (U := .arguments []) (V := .unit)
      (inputTensorUnit R A.carrier).toLinearMap (inputTensorUnit R B.carrier).toLinearMap := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change inputTensorUnit R A.carrier (tprod R x) =
    inputTensorUnit R B.carrier (tensorShapeEquiv e (.arguments []) (tprod R x))
  rw [tensorShapeEquiv_tprod, inputTensorUnit_tprod, inputTensorUnit_tprod]

private theorem singleArgument_natural (s : sig.SortType) :
    ShapeMapsCommute e (U := .arguments [s]) (V := .sort s)
      (singleArgumentEquiv A.carrier s).toLinearMap (singleArgumentEquiv B.carrier s).toLinearMap := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change structureCarrierEquiv e s (singleArgumentEquiv A.carrier s (tprod R x)) =
    singleArgumentEquiv B.carrier s (tensorShapeEquiv e (.arguments [s]) (tprod R x))
  rw [tensorShapeEquiv_tprod, singleArgumentEquiv_tprod, singleArgumentEquiv_tprod]

private theorem shapeMapsCommute_tensor {X X' Y Y' : TensorShape sig.SortType}
    {aA : X.module A →ₗ[R] X'.module A} {aB : X.module B →ₗ[R] X'.module B}
    {bA : Y.module A →ₗ[R] Y'.module A} {bB : Y.module B →ₗ[R] Y'.module B}
    (ha : ShapeMapsCommute e (U := X) (V := X') aA aB)
    (hb : ShapeMapsCommute e (U := Y) (V := Y') bA bB) :
    ShapeMapsCommute e (U := .tensor X Y) (V := .tensor X' Y')
      (TensorProduct.map aA bA) (TensorProduct.map aB bB) := by
  apply TensorProduct.ext'
  intro x y
  change tensorShapeEquiv e (.tensor X' Y') (TensorProduct.map aA bA (x ⊗ₜ[R] y)) =
    TensorProduct.map aB bB (tensorShapeEquiv e (.tensor X Y) (x ⊗ₜ[R] y))
  rw [TensorProduct.map_tmul, tensorShapeEquiv_tmul, tensorShapeEquiv_tmul, TensorProduct.map_tmul]
  rw [shapeMapsCommute_apply e ha x, shapeMapsCommute_apply e hb y]

private theorem structureCarrierEquiv_cast {s t : sig.SortType} (same : s = t) (x : A.carrier s) :
    structureCarrierEquiv e t (cast (congrArg (fun s => (A.carrier s : Type u)) same) x) =
      cast (congrArg (fun s => (B.carrier s : Type u)) same) (structureCarrierEquiv e s x) := by
  subst t
  rfl

private theorem permuteArguments_natural {Γ Δ : List sig.SortType}
    (p : TensorPosition Γ ≃ TensorPosition Δ) (sorts : ∀ i, i.1 = (p i).1) :
    ShapeMapsCommute e (U := .arguments Γ) (V := .arguments Δ)
      ((TensorExpression.permuteArguments p sorts).eval A)
      ((TensorExpression.permuteArguments p sorts).eval B) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change tensorShapeEquiv e (.arguments Δ)
      ((TensorExpression.permuteArguments p sorts).eval A (tprod R x)) =
    (TensorExpression.permuteArguments p sorts).eval B
      (tensorShapeEquiv e (.arguments Γ) (tprod R x))
  rw [TensorExpression.eval_permuteArguments_tprod, tensorShapeEquiv_tprod, tensorShapeEquiv_tprod,
    TensorExpression.eval_permuteArguments_tprod]
  congr 1
  funext j
  exact structureCarrierEquiv_cast e
    ((sorts (p.symm j)).trans (congrArg Sigma.fst (p.apply_symm_apply j))) (x (p.symm j))

private theorem on_tensor_blocks {Γ Δ : List sig.SortType}
    {N : Type u} [AddCommGroup N] [Module R N]
    {l r : ((TensorShape.arguments Γ).module A ⊗[R] (TensorShape.arguments Δ).module A) →ₗ[R] N}
    (same : ∀ (x : ∀ i : TensorPosition Γ, A.carrier i.1) (y : ∀ i : TensorPosition Δ, A.carrier i.1),
      l (tprod R x ⊗ₜ[R] tprod R y) = r (tprod R x ⊗ₜ[R] tprod R y)) :
    l = r := by
  apply TensorProduct.ext'
  intro x y
  induction x using PiTensorProduct.induction_on with
  | add a b ha hb => simp only [add_tmul, map_add, ha, hb]
  | smul_tprod a x =>
    rw [← TensorProduct.smul_tmul', map_smul, map_smul]
    congr 1
    induction y using PiTensorProduct.induction_on with
    | add a b ha hb => simp only [tmul_add, map_add, ha, hb]
    | smul_tprod b y => rw [TensorProduct.tmul_smul, map_smul, map_smul, same]

private theorem combineArguments_natural {Γ Δ Θ : List sig.SortType}
    (p : TensorPosition Γ ⊕ TensorPosition Δ ≃ TensorPosition Θ)
    (sorts : ∀ i, Sum.elim Sigma.fst Sigma.fst i = (p i).1) :
    ShapeMapsCommute e (U := .tensor (.arguments Γ) (.arguments Δ)) (V := .arguments Θ)
      (combineArgumentsEquiv A p sorts).toLinearMap (combineArgumentsEquiv B p sorts).toLinearMap := by
  apply on_tensor_blocks
  intro x y
  change tensorShapeEquiv e (.arguments Θ) (combineArgumentsEquiv A p sorts (tprod R x ⊗ₜ[R] tprod R y)) =
    combineArgumentsEquiv B p sorts
      (tensorShapeEquiv e (.tensor (.arguments Γ) (.arguments Δ)) (tprod R x ⊗ₜ[R] tprod R y))
  rw [combineArgumentsEquiv_tprod, tensorShapeEquiv_tprod, tensorShapeEquiv_tmul,
    tensorShapeEquiv_tprod, tensorShapeEquiv_tprod, combineArgumentsEquiv_tprod]
  congr 1
  funext j
  let k := p.symm j
  have pair :
      Sum.rec (motive := fun i => B.carrier (Sum.elim Sigma.fst Sigma.fst i))
        (fun i => structureCarrierEquiv e i.1 (x i)) (fun i => structureCarrierEquiv e i.1 (y i)) k =
      structureCarrierEquiv e (Sum.elim Sigma.fst Sigma.fst k)
        (Sum.rec (motive := fun i => A.carrier (Sum.elim Sigma.fst Sigma.fst i)) x y k) := by
    dsimp only [k]
    generalize p.symm j = z
    cases z <;> rfl
  let equalSort : Sum.elim Sigma.fst Sigma.fst k = j.1 :=
    (sorts k).trans (congrArg Sigma.fst (p.apply_symm_apply j))
  let element := Sum.rec (motive := fun i => A.carrier (Sum.elim Sigma.fst Sigma.fst i)) x y k
  exact (structureCarrierEquiv_cast e equalSort element).trans
    (congrArg (cast (congrArg (fun s => (B.carrier s : Type u)) equalSort)) pair.symm)

/-- Every original tensor expression commutes with actual realization isomorphisms. -/
theorem tensorExpression_natural (w : TensorExpression R sig U V) :
    ShapeMapsCommute e (U := U) (V := V) (w.eval A) (w.eval B) := by
  induction w with
  | id => simp [ShapeMapsCommute, TensorExpression.eval]
  | zero => simp [ShapeMapsCommute, TensorExpression.eval]
  | total f => exact total_natural e f
  | quantity q => exact quantity_natural e q
  | swap X Y => exact swap_natural e X Y
  | assoc X Y Z => exact assoc_natural e X Y Z
  | assocInv X Y Z => exact shapeMapsCommute_symm e _ _ (assoc_natural e X Y Z)
  | leftUnit X => exact leftUnit_natural e X
  | leftUnitInv X => exact shapeMapsCommute_symm e _ _ (leftUnit_natural e X)
  | rightUnit X => exact rightUnit_natural e X
  | rightUnitInv X => exact shapeMapsCommute_symm e _ _ (rightUnit_natural e X)
  | emptyArguments => exact shapeMapsCommute_symm e _ _ (emptyArguments_natural e)
  | emptyArgumentsInv => exact emptyArguments_natural e
  | singleArgument s => exact shapeMapsCommute_symm e _ _ (singleArgument_natural e s)
  | singleArgumentInv s => exact singleArgument_natural e s
  | permuteArguments p sorts => exact permuteArguments_natural e p sorts
  | combineArguments p sorts => exact combineArguments_natural e p sorts
  | splitArguments p sorts => exact shapeMapsCommute_symm e _ _ (combineArguments_natural e p sorts)
  | comp l r hl hr =>
    apply LinearMap.ext
    intro x
    exact (shapeMapsCommute_apply e hr (l.eval A x)).trans
      (congrArg (r.eval B) (shapeMapsCommute_apply e hl x))
  | tensor l r hl hr => exact shapeMapsCommute_tensor e hl hr
  | add l r hl hr =>
    apply LinearMap.ext
    intro x
    change tensorShapeEquiv e _ (l.eval A x + r.eval A x) =
      l.eval B (tensorShapeEquiv e _ x) + r.eval B (tensorShapeEquiv e _ x)
    rw [map_add, shapeMapsCommute_apply e hl, shapeMapsCommute_apply e hr]
  | smul a l hl =>
    apply LinearMap.ext
    intro x
    change tensorShapeEquiv e _ (a • l.eval A x) = a • l.eval B (tensorShapeEquiv e _ x)
    rw [map_smul, shapeMapsCommute_apply e hl]

include e in
/-- Satisfaction of a written tensor Law is invariant under an actual isomorphism. -/
theorem tensorLaw_holds_iff_of_iso (law : TensorLaw R sig) :
    law.holds A ↔ law.holds B := by
  have left := shapeMapsCommute_apply e (tensorExpression_natural e law.left)
  have right := shapeMapsCommute_apply e (tensorExpression_natural e law.right)
  constructor
  · intro h
    change law.left.eval A = law.right.eval A at h
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := (tensorShapeEquiv e law.source).surjective y
    rw [← left, ← right, h]
  · intro h
    change law.left.eval B = law.right.eval B at h
    apply LinearMap.ext
    intro x
    apply (tensorShapeEquiv e law.target).injective
    rw [left, right, h]

end

end SHIGURE.TensorRealization
