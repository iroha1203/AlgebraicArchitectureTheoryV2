import Formal.SHIGURE.Part2.Realizations.TensorInputs

/-! # Naturality of typed tensor expressions

A family preserving the primitive operations also preserves every
written expression. The same shape comparison is used on both sides
of an equation.
-/

namespace SHIGURE

open TensorProduct PiTensorProduct TensorRealization
open scoped TensorProduct

universe u

noncomputable section

variable {R : Type u} [CommRing R] {sig : Signature.{u}}
variable {U V : TensorStructure R sig}

/-- The map of a written tensor shape induced by a linear family on sorts. -/
def TensorShape.mapSorts (f : ∀ s, U.carrier s →ₗ[R] V.carrier s) :
    (X : TensorShape sig.SortType) → (X.module U →ₗ[R] X.module V)
  | .unit => LinearMap.id
  | .sort s => f s
  | .arguments Γ => PiTensorProduct.map (fun i : TensorPosition Γ => f i.1)
  | .tensor X Y => TensorProduct.map (mapSorts f X) (mapSorts f Y)

/-- A sortwise equivalence induces an equivalence of the actual shape modules. -/
def TensorShape.equivSorts (e : ∀ s, U.carrier s ≃ₗ[R] V.carrier s) :
    (X : TensorShape sig.SortType) → (X.module U ≃ₗ[R] X.module V)
  | .unit => LinearEquiv.refl R _
  | .sort s => e s
  | .arguments Γ => PiTensorProduct.congr (fun i : TensorPosition Γ => e i.1)
  | .tensor X Y => TensorProduct.congr (equivSorts e X) (equivSorts e Y)

/-- The map induced by a family of equivalences is the underlying equivalence of shape modules. -/
theorem TensorShape.equivSorts_toLinearMap (e : ∀ s, U.carrier s ≃ₗ[R] V.carrier s)
    (X : TensorShape sig.SortType) : (X.equivSorts e).toLinearMap = X.mapSorts (fun s => (e s).toLinearMap) := by
  induction X with
  | unit => rfl
  | sort s => rfl
  | arguments Γ =>
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    exact (PiTensorProduct.congr_tprod (fun i : TensorPosition Γ => e i.1) x).trans
      (PiTensorProduct.map_tprod (fun i : TensorPosition Γ => (e i.1).toLinearMap) x).symm
  | tensor X Y hx hy =>
    apply TensorProduct.ext'
    intro x y
    change equivSorts e X x ⊗ₜ[R] equivSorts e Y y =
      mapSorts (fun s => (e s).toLinearMap) X x ⊗ₜ[R] mapSorts (fun s => (e s).toLinearMap) Y y
    exact congrArg₂ (TensorProduct.tmul R) (LinearMap.congr_fun hx x) (LinearMap.congr_fun hy y)

private theorem natural_inverse {P Q P' Q' : Type u}
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    [AddCommGroup P'] [Module R P'] [AddCommGroup Q'] [Module R Q']
    (e : P ≃ₗ[R] Q) (e' : P' ≃ₗ[R] Q')
    (f : P →ₗ[R] P') (g : Q →ₗ[R] Q')
    (square : g.comp e.toLinearMap = e'.toLinearMap.comp f) :
    f.comp e.symm.toLinearMap = e'.symm.toLinearMap.comp g := by
  ext x
  change f (e.symm x) = e'.symm (g x)
  apply e'.injective
  have atInput := LinearMap.congr_fun square (e.symm x)
  simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using atInput.symm

private theorem onSort_cast (f : TensorStructure.Hom U V) {s t : sig.SortType} (h : s = t)
    (x : U.carrier s) :
    f.onSort t (cast (congrArg (fun a => (U.carrier a : Type u)) h) x) =
      cast (congrArg (fun a => (V.carrier a : Type u)) h) (f.onSort s x) := by
  cases h
  rfl

private theorem input_unit_natural (f : TensorStructure.Hom U V) :
    (TensorShape.unit.mapSorts f.onSort).comp (inputTensorUnit R U.carrier).toLinearMap =
      (inputTensorUnit R V.carrier).toLinearMap.comp ((TensorShape.arguments []).mapSorts f.onSort) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  let y (i : TensorPosition ([] : List sig.SortType)) : V.carrier i.1 := f.onSort i.1 (x i)
  change inputTensorUnit R U.carrier (tprod R x) =
    inputTensorUnit R V.carrier (PiTensorProduct.map (fun i : TensorPosition [] => f.onSort i.1) (tprod R x))
  rw [PiTensorProduct.map_tprod]
  exact (inputTensorUnit_tprod R U.carrier x).trans (inputTensorUnit_tprod R V.carrier y).symm

private theorem input_single_natural (f : TensorStructure.Hom U V) (s : sig.SortType) :
    (f.onSort s).comp (singleArgumentEquiv U.carrier s).toLinearMap =
      (singleArgumentEquiv V.carrier s).toLinearMap.comp ((TensorShape.arguments [s]).mapSorts f.onSort) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  change f.onSort s (singleArgumentEquiv U.carrier s (tprod R x)) =
    singleArgumentEquiv V.carrier s (PiTensorProduct.map (fun i : TensorPosition [s] => f.onSort i.1) (tprod R x))
  rw [PiTensorProduct.map_tprod]
  exact (congrArg (f.onSort s) (singleArgumentEquiv_tprod U.carrier s x)).trans
    (singleArgumentEquiv_tprod V.carrier s (fun i => f.onSort i.1 (x i))).symm

private theorem input_combine_natural (f : TensorStructure.Hom U V) {Γ Δ Θ : List sig.SortType}
    (e : TensorPosition Γ ⊕ TensorPosition Δ ≃ TensorPosition Θ)
    (sorts : ∀ i, Sum.elim Sigma.fst Sigma.fst i = (e i).1) :
    ((TensorShape.arguments Θ).mapSorts f.onSort).comp (combineArgumentsEquiv U e sorts).toLinearMap =
      (combineArgumentsEquiv V e sorts).toLinearMap.comp
        ((TensorShape.tensor (.arguments Γ) (.arguments Δ)).mapSorts f.onSort) := by
  let leftMap := ((TensorShape.arguments Θ).mapSorts f.onSort).comp (combineArgumentsEquiv U e sorts).toLinearMap
  let rightMap := (combineArgumentsEquiv V e sorts).toLinearMap.comp
    ((TensorShape.tensor (.arguments Γ) (.arguments Δ)).mapSorts f.onSort)
  change leftMap = rightMap
  have generators (x : ∀ i : TensorPosition Γ, U.carrier i.1) (y : ∀ i : TensorPosition Δ, U.carrier i.1) :
      leftMap (tprod R x ⊗ₜ[R] tprod R y) = rightMap (tprod R x ⊗ₜ[R] tprod R y) := by
    change (PiTensorProduct.map (fun i : TensorPosition Θ => f.onSort i.1))
        (combineArgumentsEquiv U e sorts (tprod R x ⊗ₜ[R] tprod R y)) =
      combineArgumentsEquiv V e sorts (TensorProduct.map
        (PiTensorProduct.map (fun i : TensorPosition Γ => f.onSort i.1))
        (PiTensorProduct.map (fun i : TensorPosition Δ => f.onSort i.1)) (tprod R x ⊗ₜ[R] tprod R y))
    rw [TensorProduct.map_tmul, PiTensorProduct.map_tprod, PiTensorProduct.map_tprod,
      combineArgumentsEquiv_tprod, combineArgumentsEquiv_tprod, PiTensorProduct.map_tprod]
    apply congrArg (tprod R)
    funext j
    let ex := e.symm j
    let eq := (sorts ex).trans (congrArg Sigma.fst (e.apply_symm_apply j))
    rw [onSort_cast f eq]
    apply congrArg (cast (congrArg (fun a => (V.carrier a : Type u)) eq))
    change f.onSort (Sum.elim Sigma.fst Sigma.fst ex)
        (Sum.rec (motive := fun i => U.carrier (Sum.elim Sigma.fst Sigma.fst i)) x y ex) =
      Sum.rec (motive := fun i => V.carrier (Sum.elim Sigma.fst Sigma.fst i))
        (fun i => f.onSort i.1 (x i)) (fun i => f.onSort i.1 (y i)) ex
    cases ex <;> rfl
  apply TensorProduct.ext'
  intro x y
  induction x using PiTensorProduct.induction_on with
  | add x x' hx hx' => rw [add_tmul, map_add, map_add, hx, hx']
  | smul_tprod a x =>
    rw [← smul_tmul', map_smul, map_smul]
    induction y using PiTensorProduct.induction_on with
    | add y y' hy hy' =>
      simp only [tmul_add, map_add, smul_add]
      exact congrArg₂ (· + ·) hy hy'
    | smul_tprod b y =>
      rw [tmul_smul, map_smul, map_smul, generators]
      rfl

set_option maxHeartbeats 850000 in
/-- Evaluating any typed tensor expression commutes with every structure-preserving map. -/
theorem TensorExpression.eval_natural (f : TensorStructure.Hom U V) {X Y : TensorShape sig.SortType}
    (term : TensorExpression R sig X Y) :
    (Y.mapSorts f.onSort).comp (term.eval U) = (term.eval V).comp (X.mapSorts f.onSort) := by
  induction term with
  | id X => rw [TensorExpression.eval, TensorExpression.eval, LinearMap.comp_id, LinearMap.id_comp]
  | zero X Y => simp only [TensorExpression.eval, LinearMap.comp_zero, LinearMap.zero_comp]
  | total op =>
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    change f.onSort _ (PiTensorProduct.lift (U.total op) (tprod R x)) =
      PiTensorProduct.lift (V.total op) (PiTensorProduct.map
        (fun i : TensorPosition (sig.totalArity op).inputs => f.onSort i.1) (tprod R x))
    rw [PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod]
    exact f.preservesTotal op x
  | quantity q =>
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    change f.onSort _ (PiTensorProduct.lift (U.quantity q) (tprod R x)) =
      PiTensorProduct.lift (V.quantity q) (PiTensorProduct.map
        (fun i : TensorPosition (sig.quantityArity q).inputs => f.onSort i.1) (tprod R x))
    rw [PiTensorProduct.map_tprod, PiTensorProduct.lift.tprod, PiTensorProduct.lift.tprod]
    exact f.preservesQuantity q x
  | swap X Y =>
    apply TensorProduct.ext'
    intro x y
    rfl
  | assoc X Y Z =>
    apply TensorProduct.ext_threefold
    intro x y z
    rfl
  | assocInv X Y Z =>
    apply TensorProduct.ext_threefold'
    intro x y z
    rfl
  | leftUnit X =>
    apply TensorProduct.ext'
    intro r x
    change X.mapSorts f.onSort ((r : R) • x) = r • X.mapSorts f.onSort x
    exact map_smul _ _ _
  | rightUnit X =>
    apply TensorProduct.ext'
    intro x r
    change X.mapSorts f.onSort ((r : R) • x) = r • X.mapSorts f.onSort x
    exact map_smul _ _ _
  | leftUnitInv X =>
    apply LinearMap.ext
    intro x
    rfl
  | rightUnitInv X =>
    apply LinearMap.ext
    intro x
    rfl
  | emptyArgumentsInv =>
    exact input_unit_natural f
  | emptyArguments =>
    exact natural_inverse (inputTensorUnit R U.carrier) (inputTensorUnit R V.carrier)
      _ _ (input_unit_natural f)
  | singleArgumentInv s =>
    exact input_single_natural f s
  | singleArgument s =>
    exact natural_inverse (singleArgumentEquiv U.carrier s) (singleArgumentEquiv V.carrier s)
      _ _ (input_single_natural f s)
  | @permuteArguments Γ Δ e sorts =>
    apply PiTensorProduct.ext
    apply MultilinearMap.ext
    intro x
    change (PiTensorProduct.map (fun i : TensorPosition Δ => f.onSort i.1))
        ((TensorExpression.permuteArguments e sorts).eval U (tprod R x)) =
      (TensorExpression.permuteArguments e sorts).eval V
        ((PiTensorProduct.map (fun i : TensorPosition Γ => f.onSort i.1)) (tprod R x))
    rw [PiTensorProduct.map_tprod, eval_permuteArguments_tprod, eval_permuteArguments_tprod, PiTensorProduct.map_tprod]
    apply congrArg (tprod R)
    funext j
    exact onSort_cast f ((sorts (e.symm j)).trans (congrArg Sigma.fst (e.apply_symm_apply j))) _
  | combineArguments e sorts =>
    exact input_combine_natural f e sorts
  | splitArguments e sorts =>
    exact natural_inverse (combineArgumentsEquiv U e sorts) (combineArgumentsEquiv V e sorts)
      _ _ (input_combine_natural f e sorts)
  | comp p q hp hq =>
    apply LinearMap.ext
    intro x
    exact (LinearMap.congr_fun hq (p.eval U x)).trans
      (congrArg (q.eval V) (LinearMap.congr_fun hp x))
  | tensor p q hp hq =>
    apply TensorProduct.ext'
    intro x y
    simp only [TensorExpression.eval, TensorShape.mapSorts, LinearMap.comp_apply]
    exact congrArg₂ (TensorProduct.tmul R) (LinearMap.congr_fun hp x) (LinearMap.congr_fun hq y)
  | add p q hp hq =>
    simp only [TensorExpression.eval, LinearMap.comp_add, LinearMap.add_comp, hp, hq]
  | smul r p hp =>
    rw [TensorExpression.eval, TensorExpression.eval, LinearMap.comp_smul, LinearMap.smul_comp, hp]

end

end SHIGURE
