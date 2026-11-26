import Formal.SHIGURE.Part2.Descent.ModuleEquivalence
import Formal.SHIGURE.Part2.AffineBaseChange

/-! # Tensor products and compatible maps in coefficient descent

Lemma B.5 uses the comparison of B.4 on each factor. The transported
standard overlap satisfies the triple cocycle, and on every pure tensor
it is the tensor of the two original overlap isomorphisms.

## Implementation notes

The tensor product uses the tensor comparison of Lemma B.3 and the
two multiplication comparisons of Lemma B.4. Transport proves the
threefold condition while preserving the two native coefficient positions.
The explicit pairing on overlap modules connects this construction to
the actual tensor over the double coefficient algebra.
-/

namespace SHIGURE.CoefficientDescent

open TensorProduct CategoryTheory

noncomputable section

universe u

variable {A B X X' Y Y' : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup X] [Module A X] [Module B X] [IsScalarTower A B X]
variable [AddCommGroup X'] [Module A X'] [Module B X'] [IsScalarTower A B X']
variable [AddCommGroup Y] [Module A Y] [Module B Y] [IsScalarTower A B Y]
variable [AddCommGroup Y'] [Module A Y'] [Module B Y'] [IsScalarTower A B Y']

attribute [local instance] doubleModule

/-- A pair of coefficient-linear isomorphisms acts on its two overlap positions. -/
def doubleCongr (e : X ≃ₗ[B] X') (f : Y ≃ₗ[B] Y') :
    X ⊗[A] Y ≃ₗ[B ⊗[A] B] X' ⊗[A] Y' := by
  let base := TensorProduct.congr (e.restrictScalars A) (f.restrictScalars A)
  exact {
    base.toAddEquiv with
    map_smul' := fun r z => by
      change base (r • z) = r • base z
      induction r with
      | zero => simp
      | tmul b c =>
        induction z with
        | zero => simp
        | tmul x y =>
          simp only [base, double_smul, TensorProduct.congr_tmul, LinearEquiv.restrictScalars_apply, map_smul]
        | add x y hx hy =>
          simp only [smul_add, map_add, hx, hy]
      | add r s hr hs =>
        simp only [add_smul, map_add, hr, hs] }

@[simp] theorem doubleCongr_tmul (e : X ≃ₗ[B] X') (f : Y ≃ₗ[B] Y') (x : X) (y : Y) :
    doubleCongr e f (x ⊗ₜ[A] y) = e x ⊗ₜ[A] f y := rfl

private def transportOverlap (e : X ≃ₗ[B] X') (θ : OverlapIso A B X) : OverlapIso A B X' :=
  (doubleCongr e.symm (.refl B B)).trans (θ.trans (doubleCongr (.refl B B) e))

private theorem overlap_at (e : X ≃ₗ[B] X') (θ : OverlapIso A B X) (x : X') (b : B) :
    transportOverlap e θ (x ⊗ₜ[A] b) =
      (e.restrictScalars A).toLinearMap.lTensor B (θ (e.symm x ⊗ₜ[A] b)) := by
  change doubleCongr (.refl B B) e (θ (e.symm x ⊗ₜ[A] b)) = _
  generalize θ (e.symm x ⊗ₜ[A] b) = z
  induction z with
  | zero => simp
  | tmul c y => rfl
  | add z w hz hw => simp only [map_add, hz, hw]

private def mapFirst (e : X ≃ₗ[B] X') :
    ((X ⊗[A] B) ⊗[A] B) →ₗ[A] ((X' ⊗[A] B) ⊗[A] B) :=
  ((e.restrictScalars A).toLinearMap.rTensor B).rTensor B

private def mapMiddle (e : X ≃ₗ[B] X') :
    ((B ⊗[A] X) ⊗[A] B) →ₗ[A] ((B ⊗[A] X') ⊗[A] B) :=
  ((e.restrictScalars A).toLinearMap.lTensor B).rTensor B

private def mapLast (e : X ≃ₗ[B] X') :
    (B ⊗[A] (B ⊗[A] X)) →ₗ[A] (B ⊗[A] (B ⊗[A] X')) :=
  ((e.restrictScalars A).toLinearMap.lTensor B).lTensor B

private theorem move01_transport (e : X ≃ₗ[B] X') (θ : OverlapIso A B X) :
    (move01 (transportOverlap e θ)).comp (mapFirst e) = (mapMiddle e).comp (move01 θ) := by
  apply TensorProduct.ext_threefold
  intro x b c
  change transportOverlap e θ (e x ⊗ₜ[A] b) ⊗ₜ[A] c =
    ((e.restrictScalars A).toLinearMap.lTensor B (θ (x ⊗ₜ[A] b))) ⊗ₜ[A] c
  rw [overlap_at, e.symm_apply_apply]

private theorem move12_transport (e : X ≃ₗ[B] X') (θ : OverlapIso A B X) :
    (move12 (transportOverlap e θ)).comp (mapMiddle e) = (mapLast e).comp (move12 θ) := by
  apply TensorProduct.ext_threefold
  intro b x c
  change b ⊗ₜ[A] transportOverlap e θ (e x ⊗ₜ[A] c) =
    b ⊗ₜ[A] ((e.restrictScalars A).toLinearMap.lTensor B (θ (x ⊗ₜ[A] c)))
  rw [overlap_at, e.symm_apply_apply]

private def insertMiddle (b : B) : (B ⊗[A] X) →ₗ[A] B ⊗[A] (B ⊗[A] X) :=
  (TensorProduct.mk A B X b).lTensor B

private theorem move02_pure (θ : OverlapIso A B X) (x : X) (b c : B) :
    move02 θ ((x ⊗ₜ[A] b) ⊗ₜ[A] c) = insertMiddle b (θ (x ⊗ₜ[A] c)) := by
  unfold move02
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, TensorProduct.assoc_tmul,
    TensorProduct.assoc_symm_tmul, LinearMap.lTensor_tmul, TensorProduct.comm_tmul]
  change ((TensorProduct.comm A X B).toLinearMap.lTensor B)
      (TensorProduct.assoc A B X B ((θ (x ⊗ₜ[A] c)) ⊗ₜ[A] b)) = _
  generalize θ (x ⊗ₜ[A] c) = z
  induction z with
  | zero => simp
  | tmul d y => rfl
  | add z w hz hw => simp only [add_tmul, map_add, hz, hw]

private theorem insertMiddle_comp (e : X ≃ₗ[B] X') (b : B) (z : B ⊗[A] X) :
    (insertMiddle b) ((e.restrictScalars A).toLinearMap.lTensor B z) =
      mapLast e (insertMiddle b z) := by
  suffices (insertMiddle b).comp ((e.restrictScalars A).toLinearMap.lTensor B) =
      (mapLast e).comp (insertMiddle b) from LinearMap.congr_fun this z
  apply TensorProduct.ext'
  intro c x
  rfl

private theorem move02_transport (e : X ≃ₗ[B] X') (θ : OverlapIso A B X) :
    (move02 (transportOverlap e θ)).comp (mapFirst e) = (mapLast e).comp (move02 θ) := by
  apply TensorProduct.ext_threefold
  intro x b c
  change move02 (transportOverlap e θ) ((e x ⊗ₜ[A] b) ⊗ₜ[A] c) =
    mapLast e (move02 θ ((x ⊗ₜ[A] b) ⊗ₜ[A] c))
  rw [move02_pure, move02_pure, overlap_at, e.symm_apply_apply, insertMiddle_comp]

/-- Transport a descent datum along an isomorphism over the cover algebra. -/
def Datum.transport (D : Datum A B X) (e : X ≃ₗ[B] X') : Datum A B X' where
  overlap := transportOverlap e D.overlap
  cocycle := by
    let θ := D.overlap
    let τ := transportOverlap e θ
    have transported : ((move12 τ).comp (move01 τ)).comp (mapFirst e) = (move02 τ).comp (mapFirst e) := by
      rw [LinearMap.comp_assoc, move01_transport, ← LinearMap.comp_assoc, move12_transport,
        LinearMap.comp_assoc, D.cocycle, move02_transport]
    apply TensorProduct.ext_threefold
    intro x b c
    have atPure := LinearMap.congr_fun transported (((e.symm x) ⊗ₜ[A] b) ⊗ₜ[A] c)
    change (move12 τ).comp (move01 τ) (((e (e.symm x)) ⊗ₜ[A] b) ⊗ₜ[A] c) =
      move02 τ (((e (e.symm x)) ⊗ₜ[A] b) ⊗ₜ[A] c) at atPure
    simpa only [e.apply_symm_apply] using atPure

/-- Transport takes a pure source tensor through the inverse and forward module isomorphism. -/
theorem Datum.transport_overlap_tmul (D : Datum A B X) (e : X ≃ₗ[B] X') (x : X') (b : B) :
    (D.transport e).overlap (x ⊗ₜ[A] b) =
      (e.restrictScalars A).toLinearMap.lTensor B (D.overlap (e.symm x ⊗ₜ[A] b)) :=
  overlap_at e D.overlap x b

/-- The transport isomorphism respects the actual two-factor overlaps. -/
theorem Datum.transport_compatible (D : Datum A B X) (e : X ≃ₗ[B] X') :
    D.Compatible (D.transport e) e.toLinearMap := by
  suffices ((e.restrictScalars A).toLinearMap.lTensor B).comp
      (D.overlap.restrictScalars A).toLinearMap =
      ((D.transport e).overlap.restrictScalars A).toLinearMap.comp ((e.restrictScalars A).toLinearMap.rTensor B) from
    LinearMap.congr_fun this
  apply TensorProduct.ext'
  intro x b
  change _ = transportOverlap e D.overlap (e x ⊗ₜ[A] b)
  rw [overlap_at, e.symm_apply_apply]
  rfl

set_option maxHeartbeats 500000 in
/-- The inverse of a compatible linear equivalence respects the actual overlap. -/
theorem Datum.compatible_symm (D : Datum A B X) (E : Datum A B X') (e : X ≃ₗ[B] X')
    (compatible : D.Compatible E e.toLinearMap) : E.Compatible D e.symm.toLinearMap := by
  apply (E.compatible_iff_coaction D e.symm.toLinearMap).2
  intro x
  have held := (D.compatible_iff_coaction E e.toLinearMap).1 compatible (e.symm x)
  change (e.toLinearMap.restrictScalars A).baseChange B (D.coactionMap (e.symm x)) =
    E.coactionMap (e (e.symm x)) at held
  rw [e.apply_symm_apply] at held
  rw [← held]
  change ((e.restrictScalars A).symm.baseChange A B _ _) (((e.restrictScalars A).baseChange A B _ _) (D.coactionMap (e.symm x))) = _
  exact ((e.restrictScalars A).baseChange A B _ _).symm_apply_apply _

/-- Conjugating a compatible map along transport gives a compatible map. -/
theorem Datum.transport_map_compatible (D : Datum A B X) (E : Datum A B Y)
    (e : X ≃ₗ[B] X') (e' : Y ≃ₗ[B] Y') (f : X →ₗ[B] Y) (hf : D.Compatible E f) :
    (D.transport e).Compatible (E.transport e') (e'.toLinearMap.comp (f.comp e.symm.toLinearMap)) :=
  (D.transport e).compatible_comp E (E.transport e')
    ((D.transport e).compatible_comp D E (D.compatible_symm _ e (D.transport_compatible e)) hf)
    (E.transport_compatible e')

/-- From a compatible isomorphism, descend both directions to the fixed-vector modules. -/
def Datum.descendEquiv (D : Datum A B X) (E : Datum A B X') (e : X ≃ₗ[B] X')
    (compatible : D.Compatible E e.toLinearMap) : D.toCoaction.descended ≃ₗ[A] E.toCoaction.descended :=
  LinearEquiv.ofLinear (D.descendMap E e.toLinearMap compatible)
    (E.descendMap D e.symm.toLinearMap (D.compatible_symm E e compatible))
    (by ext x; exact e.apply_symm_apply x.val)
    (by ext x; exact e.symm_apply_apply x.val)

/-- The descended isomorphism has the same value in the original module. -/
theorem Datum.descendEquiv_apply_val (D : Datum A B X) (E : Datum A B X') (e : X ≃ₗ[B] X')
    (compatible : D.Compatible E e.toLinearMap) (x : D.toCoaction.descended) :
    (D.descendEquiv E e compatible x).val = e x.val := rfl

variable [Module.FaithfullyFlat A B]

/-- Apply the tensor base-change isomorphism and both actual counits of B.4. -/
def Datum.tensorModelIso (D : Datum A B X) (E : Datum A B Y) :
    B ⊗[A] (D.toCoaction.descended ⊗[A] E.toCoaction.descended) ≃ₗ[B] X ⊗[B] Y :=
  SHIGURE.baseChangeTensor B ≪≫ₗ
    TensorProduct.congr D.toCoaction.comparisonEquiv E.toCoaction.comparisonEquiv

/-- The original pair of fixed vectors maps to the actual tensor of their images. -/
@[simp]
theorem Datum.tensorModelIso_tmul (D : Datum A B X) (E : Datum A B Y)
    (b : B) (x : D.toCoaction.descended) (y : E.toCoaction.descended) :
    D.tensorModelIso E (b ⊗ₜ[A] (x ⊗ₜ[A] y)) = (b • x.val) ⊗ₜ[B] y.val := by
  change TensorProduct.congr D.toCoaction.comparisonEquiv E.toCoaction.comparisonEquiv
    (SHIGURE.baseChangeTensor B (b ⊗ₜ[A] (x ⊗ₜ[A] y))) = _
  rw [SHIGURE.baseChangeTensor_tmul, TensorProduct.congr_tmul, D.comparisonEquiv_tmul,
    E.comparisonEquiv_tmul, one_smul]

/-- Put a descent datum on the actual tensor module using the comparison of B.4. -/
def Datum.tensor (D : Datum A B X) (E : Datum A B Y) : Datum A B (X ⊗[B] Y) :=
  (standardDatum (A := A) (B := B) (M := D.toCoaction.descended ⊗[A] E.toCoaction.descended)).transport
    (D.tensorModelIso E)

/-- The descended tensor module is the tensor product of the two descended modules. -/
def Datum.tensorDescendedEquiv (D : Datum A B X) (E : Datum A B Y) :
    D.toCoaction.descended ⊗[A] E.toCoaction.descended ≃ₗ[A] (D.tensor E).toCoaction.descended :=
  (standardUnitEquiv (A := A) (B := B) (M := D.toCoaction.descended ⊗[A] E.toCoaction.descended)).trans
    (Datum.descendEquiv _ _ (D.tensorModelIso E) (Datum.transport_compatible _ _))

/-- Pair the images on the target side of the two overlaps. The coefficient factors multiply. -/
def pairOutput (z : B ⊗[A] X) (w : B ⊗[A] Y) : B ⊗[A] (X ⊗[B] Y) :=
  (TensorProduct.mapOfCompatibleSMul B A X Y).baseChange B
    ((SHIGURE.baseChangeTensor B).symm (z ⊗ₜ[B] w))

omit [Module.FaithfullyFlat A B] in
/-- On pure overlap elements, pairing multiplies the first coefficients. -/
theorem pairOutput_tmul (a b : B) (x : X) (y : Y) :
    pairOutput (a ⊗ₜ[A] x) (b ⊗ₜ[A] y) = (b * a) ⊗ₜ[A] (x ⊗ₜ[B] y) :=
  rfl

omit [Module.FaithfullyFlat A B] in
private theorem pairOutput_add_left (z z' : B ⊗[A] X) (w : B ⊗[A] Y) :
    pairOutput (z + z') w = pairOutput z w + pairOutput z' w := by
  simp only [pairOutput, add_tmul, map_add]

omit [Module.FaithfullyFlat A B] in
private theorem pairOutput_add_right (z : B ⊗[A] X) (w w' : B ⊗[A] Y) :
    pairOutput z (w + w') = pairOutput z w + pairOutput z w' := by
  simp only [pairOutput, tmul_add, map_add]

omit [Module.FaithfullyFlat A B] in
private theorem pairOutput_smul_left (r : B ⊗[A] B) (z : B ⊗[A] X) (w : B ⊗[A] Y) :
    pairOutput (r • z) w = r • pairOutput z w := by
  induction r with
  | zero => simp [pairOutput]
  | tmul a b =>
    induction z with
    | zero => simp [pairOutput]
    | tmul c x =>
      induction w with
      | zero => simp [pairOutput]
      | tmul d y =>
        simp only [double_smul, pairOutput_tmul, smul_eq_mul, TensorProduct.smul_tmul']
        rw [mul_left_comm]
      | add w w' hw hw' => simp only [pairOutput_add_right, hw, hw', smul_add]
    | add z z' hz hz' => simp only [smul_add, pairOutput_add_left, hz, hz']
  | add r r' hr hr' => simp only [add_smul, pairOutput_add_left, hr, hr']

omit [Module.FaithfullyFlat A B] in
private theorem pairOutput_smul_right (r : B ⊗[A] B) (z : B ⊗[A] X) (w : B ⊗[A] Y) :
    pairOutput z (r • w) = r • pairOutput z w := by
  induction r with
  | zero => simp [pairOutput]
  | tmul a b =>
    induction z with
    | zero => simp [pairOutput]
    | tmul c x =>
      induction w with
      | zero => simp [pairOutput]
      | tmul d y =>
        simp only [double_smul, pairOutput_tmul, smul_eq_mul, TensorProduct.tmul_smul]
        rw [mul_assoc]
      | add w w' hw hw' => simp only [smul_add, pairOutput_add_right, hw, hw']
    | add z z' hz hz' => simp only [pairOutput_add_left, hz, hz', smul_add]
  | add r r' hr hr' => simp only [add_smul, pairOutput_add_right, hr, hr']

/-- Pair the two target modules over the actual double coefficient algebra. -/
def pairOutputTensor :
    (B ⊗[A] X) ⊗[B ⊗[A] B] (B ⊗[A] Y) →ₗ[B ⊗[A] B] B ⊗[A] (X ⊗[B] Y) :=
  TensorProduct.lift
    { toFun := fun z =>
        { toFun := pairOutput z
          map_add' := pairOutput_add_right z
          map_smul' := fun r w => pairOutput_smul_right r z w }
      map_add' := fun z z' => LinearMap.ext fun w => pairOutput_add_left z z' w
      map_smul' := fun r z => LinearMap.ext fun w => pairOutput_smul_left r z w }

omit [Module.FaithfullyFlat A B] in
/-- The tensor pairing evaluates the two aligned overlap images. -/
@[simp] theorem pairOutputTensor_tmul (z : B ⊗[A] X) (w : B ⊗[A] Y) :
    pairOutputTensor (z ⊗ₜ[B ⊗[A] B] w) = pairOutput z w := rfl

omit [Module.FaithfullyFlat A B] in
private theorem overlap_fixed (D : Datum A B X) (x : D.toCoaction.descended) (a b : B) :
    D.overlap ((a • x.val) ⊗ₜ[A] b) = a ⊗ₜ[A] (b • x.val) := by
  have fixed := (D.mem_descended_iff x.val).1 x.property
  have act := D.overlap.map_smul (a ⊗ₜ[A] b) (x.val ⊗ₜ[A] (1 : B))
  rw [double_smul, smul_eq_mul, mul_one, fixed, double_smul, smul_eq_mul, mul_one] at act
  exact act

private theorem tensor_overlap_fixed (D : Datum A B X) (E : Datum A B Y)
    (a c b : B) (x : D.toCoaction.descended) (y : E.toCoaction.descended) :
    (D.tensor E).overlap (((a • x.val) ⊗ₜ[B] (c • y.val)) ⊗ₜ[A] b) =
      pairOutput (D.overlap ((a • x.val) ⊗ₜ[A] (1 : B))) (E.overlap ((c • y.val) ⊗ₜ[A] b)) := by
  have same : (a • x.val) ⊗ₜ[B] (c • y.val) =
      D.tensorModelIso E ((c * a) ⊗ₜ[A] (x ⊗ₜ[A] y)) := by
    rw [D.tensorModelIso_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_smul]
  conv_lhs => rw [same]
  change transportOverlap (D.tensorModelIso E) standardOverlap
      (D.tensorModelIso E ((c * a) ⊗ₜ[A] (x ⊗ₜ[A] y)) ⊗ₜ[A] b) = _
  rw [overlap_at, LinearEquiv.symm_apply_apply, standardOverlap_tmul,
    LinearMap.lTensor_tmul, LinearEquiv.coe_coe, LinearEquiv.restrictScalars_apply, D.tensorModelIso_tmul,
    overlap_fixed, overlap_fixed, one_smul, pairOutput_tmul, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']

/-- The overlap on the tensor module tensors the two actual overlaps with the coefficient positions aligned. -/
theorem Datum.tensor_overlap_tmul (D : Datum A B X) (E : Datum A B Y) (a : X) (c : Y) (b : B) :
    (D.tensor E).overlap ((a ⊗ₜ[B] c) ⊗ₜ[A] b) =
      pairOutput (D.overlap (a ⊗ₜ[A] (1 : B))) (E.overlap (c ⊗ₜ[A] b)) := by
  obtain ⟨x, rfl⟩ := D.toCoaction.comparisonEquiv.surjective a
  obtain ⟨y, rfl⟩ := E.toCoaction.comparisonEquiv.surjective c
  induction x with
  | zero => simp [pairOutput]
  | tmul a x =>
    rw [D.comparisonEquiv_tmul]
    induction y with
    | zero => simp [pairOutput]
    | tmul c y => rw [E.comparisonEquiv_tmul]; exact tensor_overlap_fixed D E a c b x y
    | add y z hy hz => simp only [map_add, tmul_add, add_tmul, pairOutput, hy, hz] at *
  | add x z hx hz => simp only [map_add, add_tmul, pairOutput, hx, hz] at *

/-- On generators the transition applies the actual tensor of the two overlap isomorphisms. -/
theorem Datum.tensor_overlap_eq_tensorCongr (D : Datum A B X) (E : Datum A B Y)
    (a : X) (c : Y) (b : B) :
    (D.tensor E).overlap ((a ⊗ₜ[B] c) ⊗ₜ[A] b) =
      pairOutputTensor
        (TensorProduct.congr D.overlap E.overlap ((a ⊗ₜ[A] (1 : B)) ⊗ₜ[B ⊗[A] B] (c ⊗ₜ[A] b))) := by
  rw [TensorProduct.congr_tmul, pairOutputTensor_tmul, D.tensor_overlap_tmul]

/-- The equality of descended maps is exactly the equality of the original compatible maps. -/
theorem Datum.descendMap_eq_iff (D : Datum A B X) (E : Datum A B Y) {f g : X →ₗ[B] Y}
    (fCompatible : D.Compatible E f) (gCompatible : D.Compatible E g) :
    D.descendMap E f fCompatible = D.descendMap E g gCompatible ↔ f = g := by
  constructor
  · intro equal
    apply LinearMap.ext
    intro x
    obtain ⟨z, rfl⟩ := D.toCoaction.comparisonEquiv.surjective x
    have fReads := LinearMap.congr_fun (D.comparison_natural E f fCompatible) z
    have gReads := LinearMap.congr_fun (D.comparison_natural E g gCompatible) z
    rw [equal] at fReads
    exact fReads.trans gReads.symm
  · rintro rfl
    rfl

omit [Module.FaithfullyFlat A B] in
/-- The equalizer construction preserves the actual composite of compatible maps. -/
theorem Datum.descendMap_comp (D : Datum A B X) (E : Datum A B Y) (F : Datum A B Y')
    {f : X →ₗ[B] Y} {g : Y →ₗ[B] Y'} (fCompatible : D.Compatible E f) (gCompatible : E.Compatible F g) :
    D.descendMap F (g.comp f) (D.compatible_comp E F fCompatible gCompatible) =
      (E.descendMap F g gCompatible).comp (D.descendMap E f fCompatible) := by
  apply LinearMap.ext
  intro x
  rfl

/-- Surjectivity of any compatible map is equivalent to surjectivity of its descended map. -/
theorem Datum.descendMap_surjective_iff (D : Datum A B X) (E : Datum A B Y) (f : X →ₗ[B] Y)
    (compatible : D.Compatible E f) :
    Function.Surjective (D.descendMap E f compatible) ↔ Function.Surjective f := by
  let h := D.descendMap E f compatible
  let eD := D.toCoaction.comparisonEquiv
  let eE := E.toCoaction.comparisonEquiv
  have square (z) : eE (h.baseChange B z) = f (eD z) :=
    (LinearMap.congr_fun (D.comparison_natural E f compatible) z).symm
  change Function.Surjective h ↔ _
  rw [← Module.FaithfullyFlat.lTensor_surjective_iff_surjective A B h]
  constructor
  · intro surj y
    obtain ⟨z, hz⟩ := surj (eE.symm y)
    change h.baseChange B z = eE.symm y at hz
    exact ⟨eD z, (square z).symm.trans (by rw [hz, eE.apply_symm_apply])⟩
  · intro surj y
    obtain ⟨x, hx⟩ := surj (eE y)
    obtain ⟨z, rfl⟩ := eD.surjective x
    exact ⟨z, eE.injective ((square z).trans hx)⟩

/-- The descended linear maps are all linear maps between the fixed-vector modules. -/
def Datum.descendMapEquiv (D : Datum A B X) (E : Datum A B Y) :
    { f : X →ₗ[B] Y // D.Compatible E f } ≃
      (D.toCoaction.descended →ₗ[A] E.toCoaction.descended) := by
  let DX := DescentModule.ofDatum D
  let EY := DescentModule.ofDatum E
  let mapEquiv : (DX ⟶ EY) ≃
      ((DescentModule.descend (A := A) (B := B)).obj DX ⟶ (DescentModule.descend (A := A) (B := B)).obj EY) :=
    (DescentModule.equivalence (A := A) (B := B)).fullyFaithfulInverse.homEquiv
  let bundled : { f : X →ₗ[B] Y // D.Compatible E f } ≃ (DX ⟶ EY) :=
    ⟨fun f => ⟨f.val, f.property⟩, fun f => ⟨f.hom, f.compatible⟩, fun _ => rfl, fun _ => rfl⟩
  let underlying : ((DescentModule.descend (A := A) (B := B)).obj DX ⟶
      (DescentModule.descend (A := A) (B := B)).obj EY) ≃
        (D.toCoaction.descended →ₗ[A] E.toCoaction.descended) :=
    ⟨ModuleCat.Hom.hom, ModuleCat.ofHom, fun _ => rfl, fun _ => rfl⟩
  exact bundled.trans (mapEquiv.trans underlying)

/-- The equivalence sends a compatible map to its actual restriction to fixed vectors. -/
theorem Datum.descendMapEquiv_apply (D : Datum A B X) (E : Datum A B Y) (f : X →ₗ[B] Y)
    (compatible : D.Compatible E f) :
    D.descendMapEquiv E ⟨f, compatible⟩ = D.descendMap E f compatible := rfl

/-- The native tensor coaction is obtained by pairing the two native coactions. -/
theorem Datum.tensor_coaction_tmul (D : Datum A B X) (E : Datum A B Y) (x : X) (y : Y) :
    (D.tensor E).coactionMap (x ⊗ₜ[B] y) = pairOutput (D.coactionMap x) (E.coactionMap y) :=
  D.tensor_overlap_tmul E x y 1

omit [Module.FaithfullyFlat A B] in
/-- The tensor pairing commutes with maps on the two module factors. -/
theorem pairOutput_natural (f : X →ₗ[B] X') (g : Y →ₗ[B] Y') (z : B ⊗[A] X) (w : B ⊗[A] Y) :
    ((TensorProduct.map f g).restrictScalars A).baseChange B (pairOutput z w) =
      pairOutput ((f.restrictScalars A).baseChange B z) ((g.restrictScalars A).baseChange B w) := by
  induction z with
  | zero => simp [pairOutput]
  | tmul a x =>
    induction w with
    | zero => simp [pairOutput]
    | tmul b y =>
      simp only [LinearMap.baseChange_tmul, pairOutput_tmul, LinearMap.restrictScalars_apply, TensorProduct.map_tmul]
    | add w w' hw hw' => simp only [map_add, pairOutput_add_right, hw, hw']
  | add z z' hz hz' => simp only [map_add, pairOutput_add_left, hz, hz']

/-- The tensor of two compatible native maps is compatible with the tensor overlap. -/
theorem Datum.tensor_map_compatible (D : Datum A B X) (E : Datum A B Y)
    (D' : Datum A B X') (E' : Datum A B Y') (f : X →ₗ[B] X') (g : Y →ₗ[B] Y')
    (hf : D.Compatible D' f) (hg : E.Compatible E' g) :
    (D.tensor E).Compatible (D'.tensor E') (TensorProduct.map f g) := by
  apply ((D.tensor E).compatible_iff_coaction (D'.tensor E') _).2
  suffices ((TensorProduct.map f g).restrictScalars A).baseChange B ∘ₗ (D.tensor E).coactionMap =
      (D'.tensor E').coactionMap ∘ₗ TensorProduct.map f g from LinearMap.congr_fun this
  apply TensorProduct.ext'
  intro x y
  rw [LinearMap.comp_apply, LinearMap.comp_apply, TensorProduct.map_tmul, D.tensor_coaction_tmul,
    D'.tensor_coaction_tmul, pairOutput_natural,
    (D.compatible_iff_coaction D' f).1 hf x, (E.compatible_iff_coaction E' g).1 hg y]

/-- The comparison with the tensor of fixed-vector modules lifts pure tensors by inclusion. -/
theorem Datum.tensorDescendedEquiv_tmul (D : Datum A B X) (E : Datum A B Y)
    (x : D.toCoaction.descended) (y : E.toCoaction.descended) :
    (D.tensorDescendedEquiv E (x ⊗ₜ[A] y)).val = x.val ⊗ₜ[B] y.val := by
  change D.tensorModelIso E ((1 : B) ⊗ₜ[A] (x ⊗ₜ[A] y)) = _
  rw [D.tensorModelIso_tmul, one_smul]

/-- Descending the tensor of native maps agrees with tensoring the descended maps. -/
theorem Datum.tensor_map_natural (D : Datum A B X) (E : Datum A B Y)
    (D' : Datum A B X') (E' : Datum A B Y') (f : X →ₗ[B] X') (g : Y →ₗ[B] Y')
    (hf : D.Compatible D' f) (hg : E.Compatible E' g) :
    (D'.tensorDescendedEquiv E').toLinearMap.comp (TensorProduct.map (D.descendMap D' f hf) (E.descendMap E' g hg)) =
      ((D.tensor E).descendMap (D'.tensor E') (TensorProduct.map f g) (D.tensor_map_compatible E D' E' f g hf hg)).comp
        (D.tensorDescendedEquiv E).toLinearMap := by
  apply TensorProduct.ext'
  intro x y
  apply Subtype.ext
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearEquiv.coe_coe,
    Datum.tensorDescendedEquiv_tmul, Datum.descendMap_apply]

/-- A structure-preserving square of compatible maps commutes exactly when its descent does. -/
theorem Datum.descend_square_iff (D : Datum A B X) (D' : Datum A B X')
    (E : Datum A B Y) (E' : Datum A B Y')
    (op : X →ₗ[B] Y) (op' : X' →ₗ[B] Y') (f : X →ₗ[B] X') (g : Y →ₗ[B] Y')
    (hOp : D.Compatible E op) (hOp' : D'.Compatible E' op')
    (hf : D.Compatible D' f) (hg : E.Compatible E' g) :
    (E.descendMap E' g hg).comp (D.descendMap E op hOp) =
      (D'.descendMap E' op' hOp').comp (D.descendMap D' f hf) ↔ g.comp op = op'.comp f := by
  rw [← D.descendMap_comp E E' hOp hg, ← D.descendMap_comp D' E' hf hOp']
  exact D.descendMap_eq_iff E' (D.compatible_comp E E' hOp hg) (D.compatible_comp D' E' hf hOp')

end

end SHIGURE.CoefficientDescent
