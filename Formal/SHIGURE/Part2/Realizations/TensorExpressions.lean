import Formal.SHIGURE.Part2.Realizations.TensorStructures
import Mathlib.LinearAlgebra.PiTensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Typed expressions in the tensor realization scheme

A tensor Law compares two fixed expressions with the same input and output
tensor shapes. Their evaluation uses the primitive multilinear operations and
mathlib's linear maps, tensor products and comparison isomorphisms.

## Implementation notes

The shapes support both the input tuples of primitive operations and binary
products of arbitrary shapes. A single-output arity would lose expressions
with tensor outputs, and an arbitrary function of the interpretation would
lose the fixed expression defining the Law.
-/

open CategoryTheory
open scoped TensorProduct

universe u

noncomputable section

namespace SHIGURE

/-- The typed positions indexing the tensor product of a context. -/
abbrev TensorPosition {S : Type u} (Γ : List S) :=
  (s : S) × Var Γ s

/-- Types of tensor expressions in the tensor scheme. -/
inductive TensorShape (S : Type u)
  | unit
  | sort (s : S)
  | arguments (Γ : List S)
  | tensor (X Y : TensorShape S)

variable {R : Type u} [CommRing R] {sig : Signature.{u}}

/-- Interpret a tensor shape by an actual mathlib module and tensor products. -/
def TensorShape.module (A : TensorStructure R sig) : TensorShape sig.SortType → ModuleCat.{u} R
  | .unit => ModuleCat.of R R
  | .sort s => A.carrier s
  | .arguments Γ => ModuleCat.of R (⨂[R] i : TensorPosition Γ, A.carrier i.1)
  | .tensor X Y => ModuleCat.of R (TensorShape.module A X ⊗[R] TensorShape.module A Y)

/-- A tensor expression is built from the written primitive operations and structural
linear maps, with composition, tensor product, addition and scalar multiplication. -/
inductive TensorExpression (R : Type u) (sig : Signature.{u}) :
    TensorShape sig.SortType → TensorShape sig.SortType → Type u
  | id (X) : TensorExpression R sig X X
  | zero (X Y) : TensorExpression R sig X Y
  | total (f : sig.Total) :
      TensorExpression R sig (.arguments (sig.totalArity f).inputs) (.sort (sig.totalArity f).output)
  | quantity (q : sig.Quantity) :
      TensorExpression R sig (.arguments (sig.quantityArity q).inputs) (.sort (sig.quantityArity q).output)
  | swap (X Y) : TensorExpression R sig (.tensor X Y) (.tensor Y X)
  | assoc (X Y Z) : TensorExpression R sig (.tensor (.tensor X Y) Z) (.tensor X (.tensor Y Z))
  | assocInv (X Y Z) : TensorExpression R sig (.tensor X (.tensor Y Z)) (.tensor (.tensor X Y) Z)
  | leftUnit (X) : TensorExpression R sig (.tensor .unit X) X
  | leftUnitInv (X) : TensorExpression R sig X (.tensor .unit X)
  | rightUnit (X) : TensorExpression R sig (.tensor X .unit) X
  | rightUnitInv (X) : TensorExpression R sig X (.tensor X .unit)
  | emptyArguments : TensorExpression R sig .unit (.arguments [])
  | emptyArgumentsInv : TensorExpression R sig (.arguments []) .unit
  | singleArgument (s) : TensorExpression R sig (.sort s) (.arguments [s])
  | singleArgumentInv (s) : TensorExpression R sig (.arguments [s]) (.sort s)
  | permuteArguments {Γ Δ : List sig.SortType} (e : TensorPosition Γ ≃ TensorPosition Δ)
      (sorts : ∀ i, i.1 = (e i).1) : TensorExpression R sig (.arguments Γ) (.arguments Δ)
  | combineArguments {Γ Δ Θ : List sig.SortType}
      (e : TensorPosition Γ ⊕ TensorPosition Δ ≃ TensorPosition Θ)
      (sorts : ∀ i, Sum.elim Sigma.fst Sigma.fst i = (e i).1) :
      TensorExpression R sig (.tensor (.arguments Γ) (.arguments Δ)) (.arguments Θ)
  | splitArguments {Γ Δ Θ : List sig.SortType}
      (e : TensorPosition Γ ⊕ TensorPosition Δ ≃ TensorPosition Θ)
      (sorts : ∀ i, Sum.elim Sigma.fst Sigma.fst i = (e i).1) :
      TensorExpression R sig (.arguments Θ) (.tensor (.arguments Γ) (.arguments Δ))
  | comp {X Y Z} : TensorExpression R sig X Y → TensorExpression R sig Y Z → TensorExpression R sig X Z
  | tensor {X X' Y Y'} : TensorExpression R sig X X' → TensorExpression R sig Y Y' →
      TensorExpression R sig (.tensor X Y) (.tensor X' Y')
  | add {X Y} : TensorExpression R sig X Y → TensorExpression R sig X Y → TensorExpression R sig X Y
  | smul {X Y} : R → TensorExpression R sig X Y → TensorExpression R sig X Y

/-- Carrier modules for equal sorts are linearly isomorphic by transport. -/
private def carrierSortEquiv (A : TensorStructure R sig) {s t : sig.SortType} (h : s = t) :
    A.carrier s ≃ₗ[R] A.carrier t := by
  subst t
  exact LinearEquiv.refl R _

/-- A type-preserving change of positions induces the tensor comparison of the same factors. -/
private def reindexTensor (A : TensorStructure R sig) {I J : Type u}
    (s : I → sig.SortType) (t : J → sig.SortType)
    (e : I ≃ J) (sorts : ∀ i, s i = t (e i)) :
    (⨂[R] i, A.carrier (s i)) ≃ₗ[R] ⨂[R] j, A.carrier (t j) :=
  (PiTensorProduct.reindex (R := R) (s := fun i => A.carrier (s i)) e).trans
    (PiTensorProduct.congr fun j => carrierSortEquiv A
      ((sorts (e.symm j)).trans (congrArg t (e.apply_symm_apply j))))

/-- The tensor product of the single type of variable is its carrier module. -/
def singleArgumentEquiv {K : Type u} (M : K → ModuleCat.{u} R) (s : K) :
    (⨂[R] i : TensorPosition [s], M i.1) ≃ₗ[R] M s := by
  let e : TensorPosition [s] ≃ PUnit.{1} :=
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => ⟨s, .here⟩
      left_inv := by
        rintro ⟨_, i⟩
        cases i with
        | here => rfl
        | there i => exact nomatch i
      right_inv _ := rfl }
  haveI : Subsingleton (TensorPosition [s]) :=
    ⟨fun i j => e.injective (Subsingleton.elim (e i) (e j))⟩
  exact PiTensorProduct.subsingletonEquiv (R := R) (s := fun i : TensorPosition [s] => M i.1)
    (⟨s, Var.here⟩ : TensorPosition [s])

/-- The single input comparison evaluates the one remaining entry. -/
theorem singleArgumentEquiv_tprod {K : Type u} (M : K → ModuleCat.{u} R) (s : K)
    (x : ∀ i : TensorPosition [s], M i.1) :
    singleArgumentEquiv M s (PiTensorProduct.tprod R x) = x ⟨s, Var.here⟩ := by
  have he (i : TensorPosition [s]) : i = ⟨s, Var.here⟩ := by
    obtain ⟨_, j⟩ := i
    cases j with
    | here => rfl
    | there i => exact nomatch i
  letI : Subsingleton (TensorPosition [s]) := ⟨fun i j => (he i).trans (he j).symm⟩
  exact PiTensorProduct.subsingletonEquiv_apply_tprod _ x

/-- The universal tensor comparison combines two finite blocks of typed input variables. -/
def combineArgumentsEquiv (A : TensorStructure R sig) {Γ Δ Θ : List sig.SortType}
    (e : TensorPosition Γ ⊕ TensorPosition Δ ≃ TensorPosition Θ)
    (sorts : ∀ i, Sum.elim Sigma.fst Sigma.fst i = (e i).1) :
    ((TensorShape.arguments Γ).module A ⊗[R] (TensorShape.arguments Δ).module A) ≃ₗ[R]
      (TensorShape.arguments Θ).module A :=
  (PiTensorProduct.tmulEquivDep R (fun i => A.carrier (Sum.elim Sigma.fst Sigma.fst i))).trans
    (reindexTensor A (Sum.elim Sigma.fst Sigma.fst) Sigma.fst e sorts)

/-- Evaluate a fixed typed expression as the corresponding linear map. -/
def TensorExpression.eval (A : TensorStructure R sig) {X Y : TensorShape sig.SortType} :
    TensorExpression R sig X Y → (X.module A →ₗ[R] Y.module A)
  | .id _ => LinearMap.id
  | .zero _ _ => 0
  | .total f => PiTensorProduct.lift (A.total f)
  | .quantity q => PiTensorProduct.lift (A.quantity q)
  | .swap X Y => (TensorProduct.comm R (X.module A) (Y.module A)).toLinearMap
  | .assoc X Y Z => (TensorProduct.assoc R (X.module A) (Y.module A) (Z.module A)).toLinearMap
  | .assocInv X Y Z => (TensorProduct.assoc R (X.module A) (Y.module A) (Z.module A)).symm.toLinearMap
  | .leftUnit X => (TensorProduct.lid R (X.module A)).toLinearMap
  | .leftUnitInv X => (TensorProduct.lid R (X.module A)).symm.toLinearMap
  | .rightUnit X => (TensorProduct.rid R (X.module A)).toLinearMap
  | .rightUnitInv X => (TensorProduct.rid R (X.module A)).symm.toLinearMap
  | .emptyArguments =>
      letI : IsEmpty ((s : sig.SortType) × Var [] s) := ⟨fun a => nomatch a.2⟩
      (PiTensorProduct.isEmptyEquiv ((s : sig.SortType) × Var [] s)).symm.toLinearMap
  | .emptyArgumentsInv =>
      letI : IsEmpty ((s : sig.SortType) × Var [] s) := ⟨fun a => nomatch a.2⟩
      (PiTensorProduct.isEmptyEquiv ((s : sig.SortType) × Var [] s)).toLinearMap
  | .singleArgument s => (singleArgumentEquiv A.carrier s).symm.toLinearMap
  | .singleArgumentInv s => (singleArgumentEquiv A.carrier s).toLinearMap
  | .permuteArguments e sorts => (reindexTensor A Sigma.fst Sigma.fst e sorts).toLinearMap
  | .combineArguments e sorts => (combineArgumentsEquiv A e sorts).toLinearMap
  | .splitArguments e sorts => (combineArgumentsEquiv A e sorts).symm.toLinearMap
  | .comp f g => (eval A g).comp (eval A f)
  | .tensor f g => TensorProduct.map (eval A f) (eval A g)
  | .add f g => eval A f + eval A g
  | .smul r f => r • eval A f

/-- The two comparisons between the empty input and the scalar unit are inverse. -/
theorem TensorExpression.emptyArguments_roundtrip (A : TensorStructure R sig) :
    (TensorExpression.comp .emptyArguments .emptyArgumentsInv).eval A = LinearMap.id := by
  letI : IsEmpty (TensorPosition ([] : List sig.SortType)) := ⟨fun i => nomatch i.2⟩
  exact (PiTensorProduct.isEmptyEquiv (TensorPosition ([] : List sig.SortType))).comp_symm

/-- Change the scalar literals of a tensor expression while keeping its typed syntax. -/
def TensorExpression.mapScalars {S : Type u} [CommRing S] (g : R →+* S)
    {X Y : TensorShape sig.SortType} : TensorExpression R sig X Y → TensorExpression S sig X Y
  | .id X => .id X
  | .zero X Y => .zero X Y
  | .total f => .total f
  | .quantity q => .quantity q
  | .swap X Y => .swap X Y
  | .assoc X Y Z => .assoc X Y Z
  | .assocInv X Y Z => .assocInv X Y Z
  | .leftUnit X => .leftUnit X
  | .leftUnitInv X => .leftUnitInv X
  | .rightUnit X => .rightUnit X
  | .rightUnitInv X => .rightUnitInv X
  | .emptyArguments => .emptyArguments
  | .emptyArgumentsInv => .emptyArgumentsInv
  | .singleArgument s => .singleArgument s
  | .singleArgumentInv s => .singleArgumentInv s
  | .permuteArguments e sorts => .permuteArguments e sorts
  | .combineArguments e sorts => .combineArguments e sorts
  | .splitArguments e sorts => .splitArguments e sorts
  | .comp f h => .comp (mapScalars g f) (mapScalars g h)
  | .tensor f h => .tensor (mapScalars g f) (mapScalars g h)
  | .add f h => .add (mapScalars g f) (mapScalars g h)
  | .smul r f => .smul (g r) (mapScalars g f)

/-- An equation compares two fixed tensor expressions with the same shapes. -/
structure TensorLaw (R : Type u) (sig : Signature.{u}) where
  /-- The common input shape. -/
  source : TensorShape sig.SortType
  /-- The common output shape. -/
  target : TensorShape sig.SortType
  /-- The written expression on the left. -/
  left : TensorExpression R sig source target
  /-- The written expression on the right. -/
  right : TensorExpression R sig source target

/-- A tensor Law holds exactly when its two interpretations are the same linear map. -/
def TensorLaw.holds (law : TensorLaw R sig) (A : TensorStructure R sig) : Prop :=
  law.left.eval A = law.right.eval A

/-- Interpret the same required equation over a new ring by mapping its scalars. -/
def TensorLaw.mapScalars {S : Type u} [CommRing S] (g : R →+* S) (law : TensorLaw R sig) :
    TensorLaw S sig :=
  ⟨law.source, law.target, law.left.mapScalars g, law.right.mapScalars g⟩

/-- The full-domain tensor mode applies to signatures without separately specified
relations or partial operations. -/
structure FullDomainTensorSignature (sig : Signature.{u}) : Prop where
  /-- Relations belong to the separately interpreted structure. -/
  noRelations : IsEmpty sig.Rel
  /-- Partial domains belong to the separately interpreted structure. -/
  noPartial : IsEmpty sig.Partial

section TensorExpressionGenerators

variable {R : Type u} [CommRing R] {sig : Signature.{u}}

/-- Transport of an entry acts by the equality of its carrier types. -/
private theorem carrierSortEquiv_apply (A : TensorStructure R sig) {s t : sig.SortType} (h : s = t)
    (x : A.carrier s) : carrierSortEquiv A h x = cast (congrArg (fun a => (A.carrier a : Type u)) h) x := by
  cases h
  rfl

/-- Reindexing a pure input tensor permutes its entries and transports each entry to its declared sort. -/
private theorem reindexTensor_tprod (A : TensorStructure R sig) {I J : Type u}
    (s : I → sig.SortType) (t : J → sig.SortType) (e : I ≃ J)
    (sorts : ∀ i, s i = t (e i)) (x : ∀ i, A.carrier (s i)) :
    reindexTensor A s t e sorts (PiTensorProduct.tprod R x) = PiTensorProduct.tprod R (fun j =>
      cast (congrArg (fun a => (A.carrier a : Type u))
        ((sorts (e.symm j)).trans (congrArg t (e.apply_symm_apply j)))) (x (e.symm j))) := by
  rw [reindexTensor, LinearEquiv.trans_apply, PiTensorProduct.reindex_tprod, PiTensorProduct.congr_tprod]
  congr 1
  funext j
  exact carrierSortEquiv_apply A _ _

/-- The permutation primitive evaluates pure inputs by the declared position equivalence. -/
theorem TensorExpression.eval_permuteArguments_tprod (A : TensorStructure R sig)
    {Γ Δ : List sig.SortType} (e : TensorPosition Γ ≃ TensorPosition Δ)
    (sorts : ∀ i, i.1 = (e i).1) (x : ∀ i : TensorPosition Γ, A.carrier i.1) :
    (TensorExpression.permuteArguments e sorts).eval A (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R (fun j => cast (congrArg (fun a => (A.carrier a : Type u))
        ((sorts (e.symm j)).trans (congrArg Sigma.fst (e.apply_symm_apply j)))) (x (e.symm j))) :=
  reindexTensor_tprod A Sigma.fst Sigma.fst e sorts x

/-- Combining two blocks of pure inputs takes each entry from its declared block and position. -/
theorem combineArgumentsEquiv_tprod (A : TensorStructure R sig) {Γ Δ Θ : List sig.SortType}
    (e : TensorPosition Γ ⊕ TensorPosition Δ ≃ TensorPosition Θ)
    (sorts : ∀ i, Sum.elim Sigma.fst Sigma.fst i = (e i).1)
    (x : ∀ i : TensorPosition Γ, A.carrier i.1) (y : ∀ i : TensorPosition Δ, A.carrier i.1) :
    combineArgumentsEquiv A e sorts (PiTensorProduct.tprod R x ⊗ₜ[R] PiTensorProduct.tprod R y) =
      PiTensorProduct.tprod R (fun j => cast (congrArg (fun a => (A.carrier a : Type u))
        ((sorts (e.symm j)).trans (congrArg Sigma.fst (e.apply_symm_apply j))))
        (Sum.rec (motive := fun i => A.carrier (Sum.elim Sigma.fst Sigma.fst i)) x y (e.symm j))) := by
  rw [combineArgumentsEquiv, LinearEquiv.trans_apply]
  have h := PiTensorProduct.tmulEquivDep_apply (R := R)
    (N := fun i => (A.carrier (Sum.elim Sigma.fst Sigma.fst i) : Type u)) x y
  exact (congrArg (reindexTensor A (Sum.elim Sigma.fst Sigma.fst) Sigma.fst e sorts) h).trans
    (reindexTensor_tprod A (Sum.elim Sigma.fst Sigma.fst) Sigma.fst e sorts _)

end TensorExpressionGenerators

end SHIGURE
