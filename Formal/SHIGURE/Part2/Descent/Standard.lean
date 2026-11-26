import Formal.SHIGURE.Part2.Descent.Overlap
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # Standard overlaps and compatible maps

Scalar extension puts the two coefficients in their prescribed positions.
The unit compares the original module with its fixed vectors, and maps
commuting with the overlap restrict to the two equalizers.

## Implementation notes

The standard unit becomes an isomorphism after tensoring: its composite
with the equalizer comparison is the identity. Faithful flatness then
reflects bijectivity to the unit itself. This reuses the comparison
already constructed from the coaction and gives the unit map directly.
-/

namespace SHIGURE.CoefficientDescent

open TensorProduct

noncomputable section

universe u

variable {A B M : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup M] [Module A M]

attribute [local instance] doubleModule

/-- The standard overlap moves the module past the untouched coefficient. -/
def standardLinearIso :
    ((B ⊗[A] M) ⊗[A] B) ≃ₗ[A] (B ⊗[A] (B ⊗[A] M)) :=
  (TensorProduct.assoc A B M B).trans
    (TensorProduct.congr (LinearEquiv.refl A B) (TensorProduct.comm A M B))

/-- The underlying reassociation moves the module past the second coefficient. -/
@[simp] theorem standardLinearIso_tmul (a b : B) (x : M) :
    standardLinearIso (((a ⊗ₜ[A] x) ⊗ₜ[A] b)) = a ⊗ₜ[A] (b ⊗ₜ[A] x) := rfl

private theorem standardAction (d : B ⊗[A] B) (z : (B ⊗[A] M) ⊗[A] B) :
    standardLinearIso (d • z) = d • (standardLinearIso z) := by
  induction d with
  | zero => simp
  | tmul b c =>
    suffices (standardLinearIso (A := A) (B := B) (M := M)).toLinearMap.comp (doubleAction (b ⊗ₜ[A] c)) =
        (doubleAction (b ⊗ₜ[A] c)).comp standardLinearIso.toLinearMap from LinearMap.congr_fun this z
    apply TensorProduct.ext_threefold
    intro a m y
    change standardLinearIso ((b ⊗ₜ[A] c) • ((a ⊗ₜ[A] m) ⊗ₜ[A] y)) =
        (b ⊗ₜ[A] c) • standardLinearIso ((a ⊗ₜ[A] m) ⊗ₜ[A] y)
    rw [double_smul, smul_tmul', standardLinearIso_tmul, standardLinearIso_tmul, double_smul, smul_tmul']
  | add x y hx hy => rw [add_smul, map_add, hx, hy, add_smul]

/-- The standard scalar extension carries a genuine double-linear overlap. -/
def standardOverlap : OverlapIso A B (B ⊗[A] M) :=
  { standardLinearIso.toAddEquiv with
    map_smul' := standardAction }

/-- Compute the standard double-linear overlap on pure tensors. -/
@[simp] theorem standardOverlap_tmul (a b : B) (x : M) :
    standardOverlap (((a ⊗ₜ[A] x) ⊗ₜ[A] b)) = a ⊗ₜ[A] (b ⊗ₜ[A] x) := rfl

/-- The scalar extension satisfies the triple condition. -/
def standardDatum : Datum A B (B ⊗[A] M) where
  overlap := standardOverlap
  cocycle := by
    ext a m b c
    rfl

/-- The original module maps into the fixed vectors of its standard overlap. -/
def standardUnit : M →ₗ[A] (standardDatum (A := A) (B := B) (M := M)).toCoaction.descended where
  toFun m := ⟨(1 : B) ⊗ₜ[A] m, rfl⟩
  map_add' _ _ := Subtype.ext (tmul_add _ _ _)
  map_smul' _ _ := Subtype.ext (tmul_smul _ _ _)

variable [Module.FaithfullyFlat A B]

omit [Module.FaithfullyFlat A B] in
/-- The comparison after the base-changed standard unit is the identity on the tensor. -/
theorem comparison_after_standardUnit :
    (standardDatum (A := A) (B := B) (M := M)).toCoaction.comparison ∘ₗ
        (standardUnit (A := A) (B := B) (M := M)).baseChange B = LinearMap.id := by
  apply AlgebraTensorModule.ext
  intro a m
  change a • ((1 : B) ⊗ₜ[A] m) = a ⊗ₜ[A] m
  rw [smul_tmul', smul_eq_mul, mul_one]

private theorem bijective_of_baseChange_comp_eq_id {N : Type u} [AddCommGroup N] [Module A N]
    (f : M →ₗ[A] N) (e : (B ⊗[A] N) ≃ₗ[B] (B ⊗[A] M))
    (h : e.toLinearMap.comp (f.baseChange B) = LinearMap.id) : Function.Bijective f := by
  have left (x : B ⊗[A] M) : e (f.baseChange B x) = x := LinearMap.congr_fun h x
  have bijective : Function.Bijective (f.lTensor B) :=
    ⟨(show Function.LeftInverse e (f.lTensor B) from left).injective,
      fun y => ⟨e y, e.injective (left (e y))⟩⟩
  exact (Module.FaithfullyFlat.lTensor_bijective_iff_bijective A B f).mp bijective

/-- Faithfully flat base change reflects the standard unit isomorphism. -/
theorem standardUnit_bijective :
    Function.Bijective (standardUnit (A := A) (B := B) (M := M)) := by
  let datum := standardDatum (A := A) (B := B) (M := M)
  let N : Submodule A (B ⊗[A] M) := datum.toCoaction.descended
  let unit : M →ₗ[A] N := standardUnit (A := A) (B := B) (M := M)
  let comparison : B ⊗[A] N ≃ₗ[B] B ⊗[A] M := datum.toCoaction.comparisonEquiv
  have triangle : comparison.toLinearMap.comp (unit.baseChange B) = LinearMap.id :=
    comparison_after_standardUnit (A := A) (B := B) (M := M)
  change Function.Bijective unit
  let addGroupN : AddCommGroup ↥N := inferInstance
  let moduleN : Module A ↥N := inferInstance
  exact @bijective_of_baseChange_comp_eq_id A B M
    ‹CommRing A› ‹CommRing B› ‹Algebra A B› ‹AddCommGroup M› ‹Module A M› ‹Module.FaithfullyFlat A B›
    ↥N addGroupN moduleN unit comparison triangle

/-- A module is the equalizer of the two standard pullback readings. -/
def standardUnitEquiv : M ≃ₗ[A] (standardDatum (A := A) (B := B) (M := M)).toCoaction.descended :=
  LinearEquiv.ofBijective standardUnit standardUnit_bijective

/-- The equivalence uses the unit insertion map on vectors. -/
theorem standardUnitEquiv_apply (m : M) :
    standardUnitEquiv (A := A) (B := B) (M := M) m =
      standardUnit (A := A) (B := B) (M := M) m :=
  rfl

end

end SHIGURE.CoefficientDescent

namespace SHIGURE.CoefficientDescent

open TensorProduct

noncomputable section

universe u

variable {A B N N' N'' : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
variable [AddCommGroup N'] [Module A N'] [Module B N'] [IsScalarTower A B N']
variable [AddCommGroup N''] [Module A N''] [Module B N''] [IsScalarTower A B N'']

attribute [local instance] doubleModule

namespace Datum

variable (D : Datum A B N) (D' : Datum A B N') (D'' : Datum A B N'')

/-- A linear map respects the actual two-factor overlap isomorphisms. -/
def Compatible (f : N →ₗ[B] N') : Prop :=
  ∀ z : N ⊗[A] B, (f.restrictScalars A).lTensor B (D.overlap z) =
    D'.overlap ((f.restrictScalars A).rTensor B z)

/-- Recover the entire overlap from the coaction and the second coefficient action. -/
theorem overlap_tmul (n : N) (b : B) :
    D.overlap (n ⊗ₜ[A] b) = ((1 : B) ⊗ₜ[A] b) • D.coactionMap n := by
  have h := D.overlap.map_smul ((1 : B) ⊗ₜ[A] b) (n ⊗ₜ[A] (1 : B))
  rwa [double_smul, one_smul, smul_eq_mul, mul_one] at h

private theorem lTensor_right_action (f : N →ₗ[B] N') (b : B) (z : B ⊗[A] N) :
    (f.restrictScalars A).lTensor B (((1 : B) ⊗ₜ[A] b) • z) =
      ((1 : B) ⊗ₜ[A] b) • (f.restrictScalars A).lTensor B z := by
  induction z with
  | zero => simp
  | tmul a n =>
    simp only [double_smul, one_smul, LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply, map_smul]
  | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]

/-- Compatibility may be read on the unit coefficient because the second factor acts linearly. -/
theorem compatible_iff_coaction (f : N →ₗ[B] N') :
    D.Compatible D' f ↔ ∀ n, (f.restrictScalars A).baseChange B (D.coactionMap n) = D'.coactionMap (f n) := by
  constructor
  · intro compatible n
    exact compatible (n ⊗ₜ[A] (1 : B))
  · intro coaction
    suffices (f.restrictScalars A).lTensor B ∘ₗ (D.overlap.restrictScalars A).toLinearMap =
        (D'.overlap.restrictScalars A).toLinearMap ∘ₗ (f.restrictScalars A).rTensor B from
      LinearMap.congr_fun this
    apply TensorProduct.ext'
    intro n b
    change (f.restrictScalars A).lTensor B (D.overlap (n ⊗ₜ[A] b)) =
      D'.overlap (f n ⊗ₜ[A] b)
    rw [D.overlap_tmul, D'.overlap_tmul, lTensor_right_action]
    exact congrArg (fun z : B ⊗[A] N' => ((1 : B) ⊗ₜ[A] b) • z) (coaction n)

set_option maxHeartbeats 500000 in
/-- The inverse of a compatible linear equivalence respects the actual overlap. -/
theorem compatible_symm (e : N ≃ₗ[B] N')
    (compatible : D.Compatible D' e.toLinearMap) : D'.Compatible D e.symm.toLinearMap := by
  apply (D'.compatible_iff_coaction D e.symm.toLinearMap).2
  intro x
  have held := (D.compatible_iff_coaction D' e.toLinearMap).1 compatible (e.symm x)
  change (e.toLinearMap.restrictScalars A).baseChange B (D.coactionMap (e.symm x)) =
    D'.coactionMap (e (e.symm x)) at held
  rw [e.apply_symm_apply] at held
  rw [← held]
  change ((e.restrictScalars A).symm.baseChange A B _ _) (((e.restrictScalars A).baseChange A B _ _) (D.coactionMap (e.symm x))) = _
  exact ((e.restrictScalars A).baseChange A B _ _).symm_apply_apply _

/-- The identity is compatible with the overlap. -/
theorem compatible_id : D.Compatible D LinearMap.id := by
  intro z
  simp

/-- Composition preserves compatibility with overlaps. -/
theorem compatible_comp {f : N →ₗ[B] N'} {g : N' →ₗ[B] N''}
    (hf : D.Compatible D' f) (hg : D'.Compatible D'' g) :
    D.Compatible D'' (g.comp f) := by
  intro z
  change ((g.restrictScalars A).comp (f.restrictScalars A)).lTensor B (D.overlap z) =
    D''.overlap (((g.restrictScalars A).comp (f.restrictScalars A)).rTensor B z)
  rw [LinearMap.lTensor_comp, LinearMap.rTensor_comp, LinearMap.comp_apply, LinearMap.comp_apply, hf, hg]

/-- Compatible linear maps restrict to the equalizers of the two readings. -/
def descendMap (f : N →ₗ[B] N') (compatible : D.Compatible D' f) :
    D.toCoaction.descended →ₗ[A] D'.toCoaction.descended :=
  ((f.restrictScalars A).comp D.toCoaction.descended.subtype).codRestrict _ fun n => by
    change D'.coactionMap (f n.val) = 1 ⊗ₜ[A] (f n.val)
    have held : D.coactionMap n.val = 1 ⊗ₜ[A] n.val := (D.toCoaction.descended_iff n.val).1 n.property
    rw [← (D.compatible_iff_coaction D' f).1 compatible, held,
      LinearMap.baseChange_tmul, LinearMap.restrictScalars_apply]

/-- The descended map has the original value on each fixed vector. -/
theorem descendMap_apply (f : N →ₗ[B] N') (compatible : D.Compatible D' f)
    (n : D.toCoaction.descended) : (D.descendMap D' f compatible n).val = f n.val := rfl

/-- The comparison is natural for every compatible linear map. -/
theorem comparison_natural (f : N →ₗ[B] N') (compatible : D.Compatible D' f) :
    f.comp D.toCoaction.comparison =
      D'.toCoaction.comparison.comp ((D.descendMap D' f compatible).baseChange B) := by
  apply AlgebraTensorModule.ext
  intro b n
  change f (b • n.val) = b • f n.val
  exact map_smul _ _ _

end Datum

end

end SHIGURE.CoefficientDescent
