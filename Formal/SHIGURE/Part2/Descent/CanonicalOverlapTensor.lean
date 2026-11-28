import Formal.SHIGURE.Part2.Descent.CanonicalScalarComparison
import Formal.SHIGURE.Part2.Descent.ExtensionAlgebraTensor
import Formal.SHIGURE.Part2.Descent.ScalarOverlapMaps
import Formal.SHIGURE.Part2.Descent.StandardOverlapUnits

/-! # Canonical comparison in the tensor presentations of coefficient descent -/

namespace SHIGURE.CoefficientDescent

open CategoryTheory ModuleCat TensorProduct

noncomputable section

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] (M : ModuleCat.{u} A)

private theorem canonicalDoubleSquare :
    (firstScalarEmbedding A B).comp (algebraMap A B) = (secondScalarEmbedding A B).comp (algebraMap A B) := by
  ext a
  exact ((Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).commutes a).trans
    ((Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).commutes a).symm

private abbrev firstExtension (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    ModuleCat.{u} B ⥤ ModuleCat.{u} (B ⊗[A] B) := extendScalars (firstScalarEmbedding A B)
private abbrev secondExtension (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    ModuleCat.{u} B ⥤ ModuleCat.{u} (B ⊗[A] B) := extendScalars (secondScalarEmbedding A B)
private abbrev canonicalModule {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (M : ModuleCat.{u} A) : ModuleCat.{u} B := (extendScalars (algebraMap A B)).obj M

local notation "F₀" => firstExtension A B
local notation "F₁" => secondExtension A B
local notation "M₀" => canonicalModule (B := B) M
local notation "M₁" => ModuleCat.of B (B ⊗[A] M)

/-- Express the canonical scalar comparison on the ordinary base-change tensor module. -/
def canonicalScalarComparisonOnTensor (e : M₀ ≅ M₁) : (F₀).obj M₁ ≅ (F₁).obj M₁ :=
  ((F₀).mapIso e).symm ≪≫ canonicalScalarComparison (algebraMap A B) (firstScalarEmbedding A B)
    (secondScalarEmbedding A B) (canonicalDoubleSquare (A := A) (B := B)) M ≪≫ (F₁).mapIso e

set_option maxHeartbeats 750000 in
set_option maxRecDepth 2048 in
/-- The canonical scalar comparison has exactly the overlap of the coefficient
extension functor, through an identification preserving the unit tensors. -/
theorem canonicalScalarComparisonOnTensor_eq_standard (e : M₀ ≅ M₁)
    (unit : ∀ m : M, e.hom ((extendRestrictScalarsAdj (algebraMap A B)).unit.app M m) = (1 : B) ⊗ₜ[A] m) :
    scalarOverlapIso (A := A) (B := B) (M := M₁) (canonicalScalarComparisonOnTensor M e) = standardOverlap (A := A) (B := B) (M := M) := by
  let P : ModuleCat.{u} B := M₀
  letI : Module A P := Module.compHom _ (algebraMap A B)
  letI : IsScalarTower A B P := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let L := F₀
  let R := F₁
  let c := canonicalScalarComparison (algebraMap A B) (firstScalarEmbedding A B)
    (secondScalarEmbedding A B) (canonicalDoubleSquare (A := A) (B := B)) M
  let d := canonicalScalarComparisonOnTensor M e
  let h := e.hom
  have common : L.map h ≫ d.hom = c.hom ≫ R.map h := by
    let a := L.mapIso e
    change a.hom ≫ (a.inv ≫ c.hom ≫ R.map h) = c.hom ≫ R.map h
    rw [a.hom_inv_id_assoc]
  apply standardOverlap_eq_of_units
  intro x
  let n : P := (extendRestrictScalarsAdj (algebraMap A B)).unit.app M x
  have first : h n = (1 : B) ⊗ₜ[A] x := unit x
  have oldOverlap : scalarOverlapIso (A := A) c (n ⊗ₜ[A] (1 : B)) = (1 : B) ⊗ₜ[A] n := by
    let t := (rightOverlapExtensionIso (A := A) (B := B) (N := P)).hom
    have value := canonicalScalarComparison_unit (algebraMap A B) (firstScalarEmbedding A B)
      (secondScalarEmbedding A B) (canonicalDoubleSquare (A := A) (B := B)) M x
    have second := congrArg (fun v : R.obj P => t v) value
    have last := rightOverlapExtensionIso_unit (A := A) (B := B) (N := P) n
    exact (scalarOverlapIso_unit (A := A) c n).trans (second.trans last)
  let k := h.hom.restrictScalars A
  have leftTensor : k.rTensor B (n ⊗ₜ[A] (1 : B)) = (h n) ⊗ₜ[A] (1 : B) := rfl
  have rightTensor : k.lTensor B ((1 : B) ⊗ₜ[A] n) = (1 : B) ⊗ₜ[A] h n := rfl
  have chart : scalarOverlapIso (A := A) d (k.rTensor B (n ⊗ₜ[A] (1 : B))) =
      k.lTensor B (scalarOverlapIso (A := A) c (n ⊗ₜ[A] (1 : B))) :=
    (scalarOverlapIso_comm (A := A) c d h common (n ⊗ₜ[A] (1 : B))).symm
  rw [leftTensor, oldOverlap, rightTensor, first] at chart
  exact chart

/-- With the canonical tensor presentation, the comparison on a base-changed
module is the standard overlap used by faithful-flat module descent. -/
theorem canonicalScalarComparisonOnTensor_standard :
    scalarOverlapIso (A := A) (B := B) (M := M₁)
      (canonicalScalarComparisonOnTensor M (extendScalarsTensorIso (B := B) M)) =
        standardOverlap (A := A) (B := B) (M := M) :=
  canonicalScalarComparisonOnTensor_eq_standard M (extendScalarsTensorIso (B := B) M)
    (extendScalarsTensorIso_unit (B := B) M)

end

end SHIGURE.CoefficientDescent
