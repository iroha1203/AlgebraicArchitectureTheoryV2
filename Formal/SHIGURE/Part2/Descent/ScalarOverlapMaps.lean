import Formal.SHIGURE.Part2.Descent.ScalarOverlap

/-! # The coefficient overlap and its maps in ordered tensor coordinates -/

namespace SHIGURE.CoefficientDescent

open CategoryTheory ModuleCat TensorProduct

noncomputable section

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
  {M N : ModuleCat.{u} B} [Module A M] [Module A N] [IsScalarTower A B M] [IsScalarTower A B N]

attribute [local instance] doubleModule

local notation "F" => extendScalars (firstScalarEmbedding A B)
local notation "G" => extendScalars (secondScalarEmbedding A B)

/-- The given scalar comparison expressed in the two ordered double-overlap modules. -/
def scalarOverlapIso (δ : (F).obj M ≅ (G).obj M) : OverlapIso A B M :=
  ((leftOverlapExtensionIso (A := A) (B := B) (N := M)).symm ≪≫ δ ≪≫
    rightOverlapExtensionIso (A := A) (B := B) (N := M)).toLinearEquiv

private theorem transported_square {C : Type*} [Category C] {X Y U V X' Y' U' V' : C}
    (a : X ≅ X') (b : Y ≅ Y') (c : U ≅ U') (d : V ≅ V')
    (x : X ⟶ U) (y : Y ⟶ V) (x' : X' ⟶ U') (y' : Y' ⟶ V') (s : X ⟶ Y) (t : U ⟶ V)
    (left : x ≫ c.hom = a.hom ≫ x') (right : y ≫ d.hom = b.hom ≫ y')
    (comm : x ≫ t = s ≫ y) :
    x' ≫ (c.inv ≫ t ≫ d.hom) = (a.inv ≫ s ≫ b.hom) ≫ y' := by
  have left' : x' ≫ c.inv = a.inv ≫ x := by
    apply (cancel_epi a.hom).1
    rw [← Category.assoc a.hom, ← left, Category.assoc, c.hom_inv_id, Category.comp_id, a.hom_inv_id_assoc]
  simp only [Category.assoc]
  rw [← Category.assoc x', left', Category.assoc, ← Category.assoc x, comm, Category.assoc s, right]

set_option maxHeartbeats 600000 in
/-- A square commuting for the two scalar extensions also commutes in the
ordered overlap modules used for coefficient descent. -/
theorem scalarOverlapIso_comm (δ : (F).obj M ≅ (G).obj M) (ε : (F).obj N ≅ (G).obj N)
    (h : M ⟶ N) (comm : (F).map h ≫ ε.hom = δ.hom ≫ (G).map h) (x : M ⊗[A] B) :
    (h.hom.restrictScalars A).lTensor B (scalarOverlapIso (A := A) δ x) =
      scalarOverlapIso (A := A) ε ((h.hom.restrictScalars A).rTensor B x) := by
  let a := leftOverlapExtensionIso (A := A) (B := B) (N := M)
  let b := rightOverlapExtensionIso (A := A) (B := B) (N := M)
  let c := leftOverlapExtensionIso (A := A) (B := B) (N := N)
  let d := rightOverlapExtensionIso (A := A) (B := B) (N := N)
  let s := ModuleCat.ofHom (tensorProductModuleMap (A := A) (B := B) (C := B)
    h.hom (LinearMap.id (R := B) (M := B)))
  let t := ModuleCat.ofHom (tensorProductModuleMap (A := A) (B := B) (C := B)
    (LinearMap.id (R := B) (M := B)) h.hom)
  have first : (F).map h ≫ c.hom = a.hom ≫ s := mixedLeftExtensionIso_natural h
  have second : (G).map h ≫ d.hom = b.hom ≫ t := mixedRightExtensionIso_natural h
  have step : s ≫ (c.inv ≫ ε.hom ≫ d.hom) = (a.inv ≫ δ.hom ≫ b.hom) ≫ t :=
    transported_square a b c d ((F).map h) ((G).map h) s t δ.hom ε.hom first second comm
  have l : ∀ y : M ⊗[A] B, s y = (h.hom.restrictScalars A).rTensor B y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul y z => rfl
  have r : ∀ y : B ⊗[A] M, t y = (h.hom.restrictScalars A).lTensor B y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add y z hy hz => simp only [map_add, hy, hz]
    | tmul y z => rfl
  have fiber := congrArg (fun m : ModuleCat.of (B ⊗[A] B) (M ⊗[A] B) ⟶
    ModuleCat.of (B ⊗[A] B) (B ⊗[A] N) => m x) step
  change scalarOverlapIso (A := A) ε (s x) = t (scalarOverlapIso (A := A) δ x) at fiber
  rw [l, r] at fiber
  exact fiber.symm

section UnitValue

/-- Evaluating the coefficient overlap on a unit in the second slot uses
the left extension unit followed by the given scalar comparison. -/
theorem scalarOverlapIso_unit (δ : (extendScalars (firstScalarEmbedding A B)).obj M ≅
    (extendScalars (secondScalarEmbedding A B)).obj M) (x : M) :
    scalarOverlapIso (A := A) δ (x ⊗ₜ[A] (1 : B)) =
    (rightOverlapExtensionIso (A := A) (B := B) (N := M)).hom
      (δ.hom ((extendRestrictScalarsAdj (firstScalarEmbedding A B)).unit.app M x)) := by
  let a := leftOverlapExtensionIso (A := A) (B := B) (N := M)
  let b := rightOverlapExtensionIso (A := A) (B := B) (N := M)
  let y := (extendRestrictScalarsAdj (firstScalarEmbedding A B)).unit.app M x
  have first : a.hom y = x ⊗ₜ[A] (1 : B) := leftOverlapExtensionIso_unit (A := A) (B := B) x
  have inverse : a.inv (x ⊗ₜ[A] (1 : B)) = y := by
    rw [← first]
    exact congrArg (fun m : (extendScalars (firstScalarEmbedding A B)).obj M ⟶
      (extendScalars (firstScalarEmbedding A B)).obj M => m y) a.hom_inv_id
  change b.hom (δ.hom (a.inv (x ⊗ₜ[A] (1 : B)))) = b.hom (δ.hom y)
  rw [inverse]
set_option maxHeartbeats 800000 in
/-- Compatibility on unit tensors in the ordered modules reflects the actual scalar extension square. -/
theorem scalarOverlapIso_reflect_comm (δ : (F).obj M ≅ (G).obj M) (ε : (F).obj N ≅ (G).obj N)
    (h : M ⟶ N)
    (comm : ∀ x : M, (h.hom.restrictScalars A).lTensor B
      (scalarOverlapIso (A := A) δ (x ⊗ₜ[A] (1 : B))) =
      scalarOverlapIso (A := A) ε (h x ⊗ₜ[A] (1 : B))) :
    (F).map h ≫ ε.hom = δ.hom ≫ (G).map h := by
  let a := rightOverlapExtensionIso (A := A) (B := B) (N := M)
  let b := rightOverlapExtensionIso (A := A) (B := B) (N := N)
  let η := (extendRestrictScalarsAdj (firstScalarEmbedding A B)).unit
  let w := ModuleCat.ofHom (tensorProductModuleMap (A := A) (B := B) (C := B)
    (LinearMap.id (R := B) (M := B)) h.hom)
  have compat : (G).map h ≫ b.hom = a.hom ≫ w := mixedRightExtensionIso_natural h
  have eval : ∀ z : B ⊗[A] M, w z = (h.hom.restrictScalars A).lTensor B z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul x y => rfl
  apply ExtendScalars.hom_ext
  intro n
  let x := η.app M n
  change ε.hom ((F).map h x) = (G).map h (δ.hom x)
  have first : (F).map h x = η.app N (h n) := rfl
  apply b.toLinearEquiv.injective
  change b.hom (ε.hom ((F).map h x)) = b.hom ((G).map h (δ.hom x))
  have right := congrArg (fun m : (G).obj M ⟶ ModuleCat.of (B ⊗[A] B) (B ⊗[A] N) => m (δ.hom x)) compat
  change b.hom ((G).map h (δ.hom x)) = w (a.hom (δ.hom x)) at right
  rw [first, right, eval]
  rw [← scalarOverlapIso_unit (A := A) ε (h n), ← scalarOverlapIso_unit (A := A) δ n]
  exact (comm n).symm



end UnitValue

end

end SHIGURE.CoefficientDescent
