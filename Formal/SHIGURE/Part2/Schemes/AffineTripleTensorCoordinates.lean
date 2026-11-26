import Formal.SHIGURE.Part2.Schemes.AffineScalarCocycle
import Formal.SHIGURE.Part2.Schemes.AffineOverlapRingDiagram
import Formal.SHIGURE.Part2.Descent.ScalarIteration
import Formal.SHIGURE.Part2.Descent.OrderedOverlapInsertion

/-! # Right-associated tensor coordinates for affine triple overlaps

## Implementation notes

The three geometric projections of Appendix B.3 use the ring
`B ⊗[A] (B ⊗[A] B)`. Nesting the two extensions on the right gives the
middle and last charts directly and identifies the three unit insertions
in the order of the cocycle in Lemma B.4. A left-associated tensor
presentation would require an additional associator on every projection.
The first chart uses the swap of the first two positions and the transported
scalar action, so the three coefficient expressions use one ring.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory ModuleCat TensorProduct
open SHIGURE.CoefficientDescent

noncomputable section

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "D₂" => B ⊗[A] B
local notation "D₃" => B ⊗[A] (B ⊗[A] B)
/-- The ring map of the indexed projection of the affine triple overlap in B.3. -/
private abbrev tripleProjectionRing (i : Fin 3) : B →+* D₃ :=
  (affineTripleRingHom A B i).hom

attribute [local instance] doubleModule

variable (M : ModuleCat.{u} B) [Module A M] [IsScalarTower A B M]

/-- The B.4 double tensor module with its original module in the first slot. -/
private abbrev middleDouble : ModuleCat.{u} D₂ := ModuleCat.of D₂ (M ⊗[A] B)
/-- The B.4 double tensor module with its original module in the last slot. -/
private abbrev lastDouble : ModuleCat.{u} D₂ := ModuleCat.of D₂ (B ⊗[A] M)

private instance : Module A (middleDouble (A := A) M) :=
  inferInstanceAs (Module A (M ⊗[A] B))

private instance : Module A (lastDouble (A := A) M) :=
  inferInstanceAs (Module A (B ⊗[A] M))

private instance : IsScalarTower A D₂ (middleDouble (A := A) M) :=
  inferInstanceAs (IsScalarTower A D₂ (M ⊗[A] B))

private instance : IsScalarTower A D₂ (lastDouble (A := A) M) :=
  inferInstanceAs (IsScalarTower A D₂ (B ⊗[A] M))

/-- Give the nested tensor chart its module structure over the B.3 triple coefficient ring. -/
private def rightTriple (U : ModuleCat.{u} D₂) [Module A U] [IsScalarTower A D₂ U] : ModuleCat.{u} D₃ :=
  letI : Module D₃ (B ⊗[A] U) :=
    tensorProductModule (A := A) (B := B) (C := D₂) (X := B) (Y := U)
  ModuleCat.of D₃ (B ⊗[A] U)

/-- The coordinate module with the original module in the middle factor. -/
abbrev affineMiddleTensor : ModuleCat.{u} D₃ := rightTriple (A := A) (middleDouble (A := A) M)

/-- The coordinate module with the original module in the last factor. -/
abbrev affineLastTensor : ModuleCat.{u} D₃ := rightTriple (A := A) (lastDouble (A := A) M)

variable {M}

/-- The geometric middle projection extends scalars into the middle tensor factor. -/
def affineMiddleTensorIso :
    (extendScalars (R := B) (S := D₃) (tripleProjectionRing (A := A) (B := B) 1)).obj M ≅ affineMiddleTensor (A := A) M :=
  mixedRightCompIso (A := A) (B := B) (C := D₂)
    (M := M) (U := middleDouble (A := A) M) (firstScalarEmbedding A B)
    (leftOverlapExtensionIso (A := A) (B := B) (N := M))

/-- The geometric last projection extends scalars into the last tensor factor. -/
def affineLastTensorIso :
    (extendScalars (R := B) (S := D₃) (tripleProjectionRing (A := A) (B := B) 2)).obj M ≅ affineLastTensor (A := A) M :=
  mixedRightCompIso (A := A) (B := B) (C := D₂)
    (M := M) (U := lastDouble (A := A) M) (secondScalarEmbedding A B)
    (rightOverlapExtensionIso (A := A) (B := B) (N := M))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 750000 in
/-- The unit of the middle extension is the pure tensor with the two outer coefficients one. -/
theorem affineMiddleTensorIso_unit (x : M) :
    (affineMiddleTensorIso (A := A) (M := M)).hom
      ((extendRestrictScalarsAdj (R := B) (S := D₃) (tripleProjectionRing (A := A) (B := B) 1)).unit.app M x) =
      (1 : B) ⊗ₜ[A] (x ⊗ₜ[A] (1 : B)) :=
  (mixedRightCompIso_unit (A := A) (B := B) (C := D₂) (M := M) (U := middleDouble (A := A) M)
    (firstScalarEmbedding A B) (leftOverlapExtensionIso (A := A) (B := B) (N := M)) x).trans
    (congrArg (fun y : M ⊗[A] B => (1 : B) ⊗ₜ[A] y) (leftOverlapExtensionIso_unit (A := A) (B := B) x))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 750000 in
/-- The unit of the last extension is the pure tensor with the two coefficient factors one. -/
theorem affineLastTensorIso_unit (x : M) :
    (affineLastTensorIso (A := A) (M := M)).hom
      ((extendRestrictScalarsAdj (R := B) (S := D₃) (tripleProjectionRing (A := A) (B := B) 2)).unit.app M x) =
      (1 : B) ⊗ₜ[A] ((1 : B) ⊗ₜ[A] x) :=
  (mixedRightCompIso_unit (A := A) (B := B) (C := D₂) (M := M) (U := lastDouble (A := A) M)
    (secondScalarEmbedding A B) (rightOverlapExtensionIso (A := A) (B := B) (N := M)) x).trans
    (congrArg (fun y : B ⊗[A] M => (1 : B) ⊗ₜ[A] y) (rightOverlapExtensionIso_unit (A := A) (B := B) x))

/-- The ring map from the B.3 double overlap into an ordered pair of the triple overlap. -/
private abbrev pairRing (i j : Fin 3) : D₂ →+* D₃ :=
  (affinePairRingHom A B i j).hom

/-- The right-associated triple tensor ring of Appendix B.3. -/
private abbrev tripleRing (i : Fin 3) : B →+* D₃ :=
  (affineTripleRingHom A B i).hom

/-- The double tensor ring of the affine overlap in Appendix B.3. -/
private abbrev doubleRing (j : Fin 2) : B →+* D₂ :=
  (affineDoubleRingHom A B j).hom

/-- Identify the second projection of a pair in the B.3 triple overlap. -/
private theorem pair_right (i j : Fin 3) :
    @RingHom.comp B D₂ D₃ _ _ _ (pairRing (A := A) (B := B) i j) (doubleRing (A := A) (B := B) 1) =
      tripleRing (A := A) (B := B) j :=
  congrArg
    (fun k : CommRingCat.of B ⟶ CommRingCat.of D₃ => k.hom)
    (affinePairRingHom_comp_right A B i j)

/-- Identify the first projection of a pair in the B.3 triple overlap. -/
private theorem pair_left (i j : Fin 3) :
    @RingHom.comp B D₂ D₃ _ _ _ (pairRing (A := A) (B := B) i j) (doubleRing (A := A) (B := B) 0) =
      tripleRing (A := A) (B := B) i :=
  congrArg
    (fun k : CommRingCat.of B ⟶ CommRingCat.of D₃ => k.hom)
    (affinePairRingHom_comp_left A B i j)

/-- Compute the action of a pair embedding on the first scalar generator of the B.4 chart. -/
private theorem pair_apply_first (i j : Fin 3) (b : B) :
    pairRing (A := A) (B := B) i j (b ⊗ₜ[A] (1 : B)) =
      tripleRing (A := A) (B := B) i b :=
  congrArg (fun k : B →+* D₃ => k b) (pair_left (A := A) (B := B) i j)

/-- The scalar extension along one of the three geometric projections. -/
abbrev affineTripleScalarModule (M : ModuleCat.{u} B) (i : Fin 3) : ModuleCat.{u} D₃ :=
  (extendScalars (R := B) (S := D₃) (tripleRing (A := A) (B := B) i)).obj M

/-- The unit vector of the extension along a geometric projection. -/
abbrev affineTripleScalarUnit (M : ModuleCat.{u} B) (i : Fin 3) (x : M) :
    affineTripleScalarModule (A := A) M i :=
  (extendRestrictScalarsAdj (R := B) (S := D₃) (tripleRing (A := A) (B := B) i)).unit.app M x

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
/-- Insert into the coordinate module along an actual pair projection. -/
abbrev affineTripleOverlapInsertion (i j : Fin 3) :=
  @orderedOverlapInsertion A B D₃ _ _ _ _ M _ _
    (pairRing (A := A) (B := B) i j) (tripleRing (A := A) (B := B) j)
    (pair_right (A := A) (B := B) i j)


set_option maxRecDepth 2048 in
set_option maxHeartbeats 700000 in
/-- Compare extension of the double tensor chart with the insertion formula used by (B.1). -/
private theorem affineInsertion_formula (i j : Fin 3) {V : ModuleCat.{u} D₃}
    (chart : affineTripleScalarModule (A := A) M j ≅ V) (L : (B ⊗[A] M) →+ V)
    (pure_tensor : ∀ b : B, ∀ x : M,
      tripleRing (A := A) (B := B) i b • chart.hom (affineTripleScalarUnit (A := A) M j x) = L (b ⊗ₜ[A] x))
    (z : B ⊗[A] M) :
    affineTripleOverlapInsertion (A := A) (M := M) i j chart z = L z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul b x =>
    have first := @orderedOverlapInsertion_tmul A B D₃
      (inferInstance : CommRing A) (inferInstance : CommRing B) (inferInstance : CommRing D₃)
      (inferInstance : Algebra A B) M (inferInstance : Module A M)
      (inferInstance : IsScalarTower A B M) (pairRing (A := A) (B := B) i j)
      (tripleRing (A := A) (B := B) j) (pair_right (A := A) (B := B) i j) V chart b x
    have middle := congrArg (fun c : D₃ => c • chart.hom (affineTripleScalarUnit (A := A) M j x))
      (pair_apply_first (A := A) (B := B) i j b)
    exact first.trans (middle.trans (pure_tensor b x))

/-- The B.4 ordered insertion placing the unit in the final coefficient position. -/
private def insertLast : (B ⊗[A] M) →ₗ[A] B ⊗[A] (M ⊗[A] B) :=
  (TensorProduct.assoc A B M B).toLinearMap.comp
    ((TensorProduct.mk A (B ⊗[A] M) B).flip (1 : B))

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
/-- In positions zero and one, insertion adds the unit in the final position. -/
theorem affineTripleOverlapInsertion_01 (z : B ⊗[A] M) :
    affineTripleOverlapInsertion (A := A) 0 1 (affineMiddleTensorIso (A := A) (M := M)) z =
      TensorProduct.assoc A B M B (z ⊗ₜ[A] (1 : B)) := by
  change _ = insertLast z
  refine affineInsertion_formula (A := A) (M := M) 0 1 (affineMiddleTensorIso (A := A) (M := M))
    (insertLast (A := A) (M := M)).toAddMonoidHom ?_ z
  intro b x
  have unit := affineMiddleTensorIso_unit (A := A) x
  change tripleRing (A := A) (B := B) 0 b •
    (affineMiddleTensorIso (A := A) (M := M)).hom (affineTripleScalarUnit (A := A) M 1 x) =
    insertLast (b ⊗ₜ[A] x)
  rw [unit]
  let y : middleDouble (A := A) M := x ⊗ₜ[A] (1 : B)
  change (b • (1 : B)) ⊗ₜ[A] ((1 : D₂) • y) = insertLast (b ⊗ₜ[A] x)
  rw [smul_eq_mul, mul_one, one_smul]
  rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
/-- In positions zero and two, insertion adds the unit in the middle position. -/
theorem affineTripleOverlapInsertion_02 (z : B ⊗[A] M) :
    affineTripleOverlapInsertion (A := A) 0 2 (affineLastTensorIso (A := A) (M := M)) z =
      ((TensorProduct.mk A B M (1 : B)).lTensor B) z := by
  refine affineInsertion_formula (A := A) (M := M) 0 2 (affineLastTensorIso (A := A) (M := M))
    ((TensorProduct.mk A B M (1 : B)).lTensor B).toAddMonoidHom ?_ z
  intro b x
  have unit := affineLastTensorIso_unit (A := A) x
  change tripleRing (A := A) (B := B) 0 b •
    (affineLastTensorIso (A := A) (M := M)).hom (affineTripleScalarUnit (A := A) M 2 x) =
    ((TensorProduct.mk A B M (1 : B)).lTensor B) (b ⊗ₜ[A] x)
  rw [unit]
  let y : lastDouble (A := A) M := (1 : B) ⊗ₜ[A] x
  change (b • (1 : B)) ⊗ₜ[A] ((1 : D₂) • y) = _
  rw [smul_eq_mul, mul_one, one_smul]
  rfl

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
/-- In positions one and two, insertion adds the unit in the first position. -/
theorem affineTripleOverlapInsertion_12 (z : B ⊗[A] M) :
    affineTripleOverlapInsertion (A := A) 1 2 (affineLastTensorIso (A := A) (M := M)) z =
      (1 : B) ⊗ₜ[A] z := by
  refine affineInsertion_formula (A := A) (M := M) 1 2 (affineLastTensorIso (A := A) (M := M))
    (TensorProduct.mk A B (B ⊗[A] M) (1 : B)).toAddMonoidHom ?_ z
  intro b x
  have unit := affineLastTensorIso_unit (A := A) x
  change tripleRing (A := A) (B := B) 1 b •
    (affineLastTensorIso (A := A) (M := M)).hom (affineTripleScalarUnit (A := A) M 2 x) =
    (1 : B) ⊗ₜ[A] (b ⊗ₜ[A] x)
  rw [unit]
  let y : lastDouble (A := A) M := (1 : B) ⊗ₜ[A] x
  change ((1 : B) • (1 : B)) ⊗ₜ[A] ((b ⊗ₜ[A] (1 : B)) • y) = _
  have step : (b ⊗ₜ[A] (1 : B)) • y = (b ⊗ₜ[A] x : B ⊗[A] M) := by
    change (b ⊗ₜ[A] (1 : B)) • ((1 : B) ⊗ₜ[A] x) = b ⊗ₜ[A] x
    rw [double_smul, smul_eq_mul, mul_one, one_smul]
  rw [one_smul, step]

section GeometricDatum

variable (D : AffineSingletonDescentData A B)

local notation "ℳ" => affineDescentCoefficientModule D
local notation "θ" => affineDescentCoefficientOverlap D

local instance : Module A ℳ := Module.compHom _ (algebraMap A B)
local instance : IsScalarTower A B ℳ := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

set_option maxRecDepth 2048 in
set_option maxHeartbeats 720000 in
/-- The geometric comparison on generators is the original overlap followed by insertion. -/
theorem affineDescentPairScalarHom_unit (i j : Fin 3) {V : ModuleCat.{u} D₃}
    (chart : affineTripleScalarModule (A := A) ℳ j ≅ V) (x : ℳ) :
    chart.hom (affineDescentPairScalarHom D i j (affineTripleScalarUnit (A := A) ℳ i x)) =
      affineTripleOverlapInsertion (A := A) (M := ℳ) i j chart (θ (x ⊗ₜ[A] (1 : B))) := by
  let g : D₂ →+* D₃ := pairRing (A := A) (B := B) i j
  let r : B →+* D₃ := tripleRing (A := A) (B := B) j
  let r₀ : B →+* D₃ := tripleRing (A := A) (B := B) i
  let δ : (extendScalars (firstScalarEmbedding A B)).obj ℳ ≅
      (extendScalars (secondScalarEmbedding A B)).obj ℳ := affineDescentScalarExtensionIso D
  have e : @RingHom.comp B D₂ D₃ _ _ _ g (secondScalarEmbedding A B) = r :=
    pair_right (A := A) (B := B) i j
  have e₀ : @RingHom.comp B D₂ D₃ _ _ _ g (firstScalarEmbedding A B) = r₀ :=
    pair_left (A := A) (B := B) i j
  have formula := @scalarOverlapPullHomAt_unit A B D₃
    (inferInstance : CommRing A) (inferInstance : CommRing B) (inferInstance : CommRing D₃)
    (inferInstance : Algebra A B) ℳ (inferInstance : Module A ℳ)
    (inferInstance : IsScalarTower A B ℳ) g r e V chart r₀ e₀ δ x
  let comparison : affineTripleScalarModule (A := A) ℳ i ⟶ affineTripleScalarModule (A := A) ℳ j :=
    scalarExtensionPullHomAt (firstScalarEmbedding A B) (secondScalarEmbedding A B) g e₀ e δ.hom
  have compare : affineDescentPairScalarHom D i j = comparison := rfl
  rw [compare]
  exact formula

/-- Apply the original ordered overlap to the last two tensor positions. -/
def affineTripleCoordinateMap :
    affineMiddleTensor (A := A) ℳ ⟶ affineLastTensor (A := A) ℳ := by
  let U := middleDouble (A := A) ℳ
  let V := lastDouble (A := A) ℳ
  let f : U →ₗ[D₂] V := (θ).toLinearMap
  exact ConcreteCategory.ofHom (C := ModuleCat.{u} D₃)
    (X := affineMiddleTensor (A := A) ℳ) (Y := affineLastTensor (A := A) ℳ)
    (tensorProductModuleMap (A := A) (B := B) (C := D₂)
      (LinearMap.id (R := B) (M := B)) f)

/-- The induced map acts by tensoring the original overlap on the right. -/
theorem affineTripleCoordinateMap_apply (z : B ⊗[A] (ℳ ⊗[A] B)) :
    affineTripleCoordinateMap D z = (((θ).restrictScalars A).toLinearMap.lTensor B) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add z w hz hw => simp only [map_add, hz, hw]
  | tmul b x => rfl


end GeometricDatum

end

end SHIGURE.SchemeDescent
