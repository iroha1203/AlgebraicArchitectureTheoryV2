import Formal.SHIGURE.Part2.Descent.Equalizer
import Mathlib.RingTheory.TensorProduct.Maps

/-! # The two coefficients and the triple overlap

The two scalar actions define the overlap in (B.1). The triple cocycle
produces the two identities for the coaction in (B.3).

## Implementation notes

The tensor product of the two scalar actions uses
`Module.endTensorEndAlgHom` and records the position of each copy of the
same algebra. The instance is local. A construction of a custom overlap
can use `attribute [local instance] doubleModule` to select these actions.
The three moves are compared as underlying `A`-linear maps, so the cocycle
tests equality on the entire triple tensor using its actual factor order.
-/

namespace SHIGURE.CoefficientDescent

open TensorProduct

noncomputable section

universe u

variable {A B X Y : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup X] [Module A X] [Module B X] [IsScalarTower A B X]
variable [AddCommGroup Y] [Module A Y] [Module B Y] [IsScalarTower A B Y]

/-- The two algebra factors act by the tensor product of their scalar actions. -/
def doubleAction : B ⊗[A] B →ₐ[A] Module.End A (X ⊗[A] Y) :=
  (Module.endTensorEndAlgHom (R := A) (S := A) (A := A) (M := X) (N := Y)).comp
    (Algebra.TensorProduct.map (Algebra.lsmul A A X : B →ₐ[A] Module.End A X)
      (Algebra.lsmul A A Y : B →ₐ[A] Module.End A Y))

/-- A pure coefficient tensor acts at the matching module positions. -/
@[simp] theorem doubleAction_tmul (b c : B) (x : X) (y : Y) :
    doubleAction (b ⊗ₜ[A] c) (x ⊗ₜ[A] y) = (b • x) ⊗ₜ[A] (c • y) := by
  rw [doubleAction, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, Module.endTensorEndAlgHom_apply]
  rfl

/-- The descent tensors carry the two actions at distinct tensor positions. -/
def doubleModule : Module (B ⊗[A] B) (X ⊗[A] Y) :=
  Module.compHom _ (doubleAction (A := A) (B := B) (X := X) (Y := Y)).toRingHom

attribute [local instance] doubleModule

/-- Compute the double scalar action on each factor of a pure tensor. -/
theorem double_smul (b c : B) (x : X) (y : Y) :
    (b ⊗ₜ[A] c) • (x ⊗ₜ[A] y) = (b • x) ⊗ₜ[A] (c • y) :=
  doubleAction_tmul b c x y

/-- Scalar restriction of the double action recovers the original base action. -/
instance doubleTower : IsScalarTower A (B ⊗[A] B) (X ⊗[A] Y) :=
  IsScalarTower.of_algebraMap_smul (fun a m => by
    change doubleAction (algebraMap A (B ⊗[A] B) a) m = a • m
    rw [AlgHom.commutes]
    rfl)

end

end SHIGURE.CoefficientDescent

namespace SHIGURE.CoefficientDescent

open TensorProduct

noncomputable section

universe u

variable {A B N : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

attribute [local instance] doubleModule

/-- The overlap is linear over the tensor algebra with its two separate actions. -/
abbrev OverlapIso (A B N : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] :=
  (N ⊗[A] B) ≃ₗ[B ⊗[A] B] (B ⊗[A] N)

variable (θ : OverlapIso A B N)

/-- Move the module across the first two positions of the triple tensor. -/
def move01 : ((N ⊗[A] B) ⊗[A] B) →ₗ[A] ((B ⊗[A] N) ⊗[A] B) :=
  (θ.restrictScalars A).toLinearMap.rTensor B

/-- Move the module across the second and third positions. -/
def move12 : ((B ⊗[A] N) ⊗[A] B) →ₗ[A] (B ⊗[A] (B ⊗[A] N)) :=
  ((θ.restrictScalars A).toLinearMap.lTensor B).comp (TensorProduct.assoc A B N B).toLinearMap

/-- Move the module directly from the first position to the third. -/
def move02 : ((N ⊗[A] B) ⊗[A] B) →ₗ[A] (B ⊗[A] (B ⊗[A] N)) :=
  ((TensorProduct.comm A N B).toLinearMap.lTensor B).comp
    ((TensorProduct.assoc A B N B).toLinearMap.comp ((move01 θ).comp
      ((TensorProduct.assoc A N B B).symm.toLinearMap.comp
        (((TensorProduct.comm A B B).toLinearMap.lTensor N).comp
          (TensorProduct.assoc A N B B).toLinearMap))))

/-- The actual descent datum across the two embeddings into the tensor algebra. -/
structure Datum (A B N : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] where
  overlap : OverlapIso A B N
  cocycle : (move12 overlap).comp (move01 overlap) = move02 overlap

namespace Datum

variable (D : Datum A B N)

/-- The actual overlap evaluated on the unit coefficient. -/
def coactionMap : N →ₗ[B] B ⊗[A] N where
  toFun n := D.overlap (n ⊗ₜ[A] (1 : B))
  map_add' n m := by rw [add_tmul, map_add]
  map_smul' b n := by
    have held := D.overlap.map_smul (b ⊗ₜ[A] (1 : B)) (n ⊗ₜ[A] (1 : B))
    rw [double_smul, one_smul] at held
    change D.overlap ((b • n) ⊗ₜ[A] (1 : B)) = b • D.overlap (n ⊗ₜ[A] (1 : B))
    rw [held]
    clear held
    induction D.overlap (n ⊗ₜ[A] (1 : B)) with
    | zero => simp
    | tmul c m => rw [double_smul, one_smul, smul_tmul']
    | add x y hx hy => rw [smul_add, smul_add, hx, hy]

/-- The coaction evaluates the overlap with unit in the second coefficient. -/
theorem coactionMap_apply (n : N) : D.coactionMap n = D.overlap (n ⊗ₜ[A] (1 : B)) := rfl

private def appendUnit : (B ⊗[A] N) →ₗ[A] ((B ⊗[A] N) ⊗[A] B) :=
  (TensorProduct.mk A (B ⊗[A] N) B).flip 1

private theorem move12_appendUnit (z : B ⊗[A] N) :
    move12 D.overlap (appendUnit z) = ((D.coactionMap.restrictScalars A).baseChange B) z := by
  suffices (move12 D.overlap).comp appendUnit =
      ((D.coactionMap.restrictScalars A).baseChange B).restrictScalars A from LinearMap.congr_fun this z
  apply TensorProduct.ext'
  intro b n
  rfl

omit [Module B N] [IsScalarTower A B N] in
private theorem insertMiddleUnit (z : B ⊗[A] N) :
    (TensorProduct.comm A N B).toLinearMap.lTensor B
      ((TensorProduct.assoc A B N B) (appendUnit z)) = ((insertUnit (A := A) (B := B)).baseChange B) z := by
  suffices ((TensorProduct.comm A N B).toLinearMap.lTensor B).comp
      ((TensorProduct.assoc A B N B).toLinearMap.comp appendUnit) =
      ((insertUnit (A := A) (B := B)).baseChange B).restrictScalars A from LinearMap.congr_fun this z
  apply TensorProduct.ext'
  intro b n
  rfl

/-- Evaluate the given triple cocycle on a vector with two unit coefficients. -/
theorem coaction_coassoc (n : N) :
    ((D.coactionMap.restrictScalars A).baseChange B) (D.coactionMap n) =
      ((insertUnit (A := A) (B := B)).baseChange B) (D.coactionMap n) := by
  have compare := LinearMap.congr_fun D.cocycle
    ((n ⊗ₜ[A] (1 : B)) ⊗ₜ[A] (1 : B))
  change move12 D.overlap (appendUnit (D.coactionMap n)) =
    (TensorProduct.comm A N B).toLinearMap.lTensor B
      ((TensorProduct.assoc A B N B) (appendUnit (D.coactionMap n))) at compare
  rwa [D.move12_appendUnit, insertMiddleUnit] at compare

/-- Multiplication applied to the overlap along the diagonal. -/
def diagonal : N →ₗ[B] N := multiply.comp D.coactionMap

private theorem baseChange_diagonal_coaction (n : N) :
    ((D.diagonal.restrictScalars A).baseChange B) (D.coactionMap n) = D.coactionMap n := by
  have same := congrArg (((multiply (A := A) (B := B) (N := N)).restrictScalars A).baseChange B)
    (D.coaction_coassoc n)
  have left : ((multiply (A := A) (B := B) (N := N)).restrictScalars A).baseChange B ∘ₗ
      ((D.coactionMap.restrictScalars A).baseChange B) = ((D.diagonal.restrictScalars A).baseChange B) := by
    apply AlgebraTensorModule.ext
    intro b n
    rfl
  have right : ((multiply (A := A) (B := B) (N := N)).restrictScalars A).baseChange B ∘ₗ
      ((insertUnit (A := A) (B := B)).baseChange B) = LinearMap.id := by
    apply AlgebraTensorModule.ext
    intro b n
    simp
  exact (LinearMap.congr_fun left (D.coactionMap n)).symm.trans
    (same.trans (LinearMap.congr_fun right (D.coactionMap n)))

private theorem diagonal_idempotent (n : N) : D.diagonal (D.diagonal n) = D.diagonal n := by
  have commute : D.diagonal.comp (multiply (A := A) (B := B) (N := N)) =
      (multiply (A := A) (B := B) (N := N)).comp ((D.diagonal.restrictScalars A).baseChange B) := by
    apply AlgebraTensorModule.ext
    intro b n
    simp
  exact (LinearMap.congr_fun commute (D.coactionMap n)).trans
    (congrArg (multiply (A := A) (B := B) (N := N)) (D.baseChange_diagonal_coaction n))

private theorem multiply_rightTensor (b : B) (x : B ⊗[A] N) :
    multiply (A := A) (((1 : B) ⊗ₜ[A] b) • x) = b • (multiply (A := A) x) := by
  induction x with
  | zero => simp
  | tmul c n =>
    rw [double_smul, one_smul, multiply_tmul, multiply_tmul, smul_comm c b]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

private theorem diagonal_overlap (z : N ⊗[A] B) :
    (multiply (A := A) (B := B)) (D.overlap z) =
      D.diagonal (multiply (A := A) ((TensorProduct.comm A N B) z)) := by
  suffices (multiply (A := A) (B := B) (N := N)).restrictScalars A ∘ₗ
      (D.overlap.restrictScalars A).toLinearMap =
      (D.diagonal.restrictScalars A).comp ((multiply (A := A) (B := B) (N := N)).restrictScalars A ∘ₗ
        (TensorProduct.comm A N B).toLinearMap) from LinearMap.congr_fun this z
  apply TensorProduct.ext'
  intro n b
  have factor := D.overlap.map_smul ((1 : B) ⊗ₜ[A] b) (n ⊗ₜ[A] (1 : B))
  rw [double_smul, one_smul, smul_eq_mul, mul_one] at factor
  change (multiply (A := A) (B := B)) (D.overlap (n ⊗ₜ[A] b)) =
    D.diagonal (multiply (A := A) (b ⊗ₜ[A] n))
  rw [factor, multiply_rightTensor, multiply_tmul, map_smul]
  rfl

/-- Invertibility of the overlap makes the diagonal map surjective. -/
theorem diagonal_surjective : Function.Surjective D.diagonal := by
  intro n
  obtain ⟨z, hz⟩ := D.overlap.surjective ((1 : B) ⊗ₜ[A] n)
  refine ⟨multiply (A := A) ((TensorProduct.comm A N B) z), ?_⟩
  rw [← D.diagonal_overlap, hz, multiply_tmul, one_smul]

/-- The diagonal is the identity, by surjectivity and the identity from the cocycle. -/
theorem coaction_counit (n : N) : multiply (A := A) (D.coactionMap n) = n := by
  obtain ⟨m, hm⟩ := D.diagonal_surjective n
  change D.diagonal n = n
  rw [← hm, D.diagonal_idempotent]

/-- The two identities (B.3) follow from the given overlap isomorphism and cocycle. -/
def toCoaction : Coaction A B N :=
  ⟨D.coactionMap, D.coaction_counit, D.coaction_coassoc⟩

/-- The descended vectors are the equalizer of the two actual readings in (B.2). -/
theorem mem_descended_iff (n : N) :
    n ∈ D.toCoaction.descended ↔ D.overlap (n ⊗ₜ[A] (1 : B)) = (1 : B) ⊗ₜ[A] n :=
  Iff.rfl

/-- The comparison of the actual descent datum multiplies the coefficient into the fixed vector. -/
theorem comparisonEquiv_tmul [Module.Flat A B] (b : B) (n : D.toCoaction.descended) :
    D.toCoaction.comparisonEquiv (b ⊗ₜ[A] n) = b • (n.val : N) :=
  rfl

end Datum

end

end SHIGURE.CoefficientDescent
