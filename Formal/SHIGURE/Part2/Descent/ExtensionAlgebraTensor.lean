import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Extension of scalars as the coefficient tensor module -/

namespace SHIGURE.CoefficientDescent

open CategoryTheory ModuleCat TensorProduct
open scoped ChangeOfRings

noncomputable section

universe u

variable {A B : Type u} [CommRing A] [CommRing B]

/-- The tensor target of coefficient extension in B.4, with its algebra
structure explicit so that it can be transported along equality. -/
private def tensorModuleOfAlgebra (a : Algebra A B) (M : ModuleCat.{u} A) : ModuleCat.{u} B :=
  letI := a
  ModuleCat.of B (B ⊗[A] M)

/-- Transport the tensor presentation of scalar extension to an equal
algebra structure on the target ring. -/
private def extendScalarsTensorIsoOf (f : A →+* B) (a : Algebra A B) (e : f.toAlgebra = a)
    (M : ModuleCat.{u} A) : (extendScalars f).obj M ≅ tensorModuleOfAlgebra a M :=
  eqToIso (congrArg (fun algebraStructure => tensorModuleOfAlgebra algebraStructure M) e)

/-- The comparison of tensor presentations carries the extension unit
to the pure tensor of the coefficient unit with the original element. -/
private theorem extendScalarsTensorIsoOf_unit (f : A →+* B) (a : Algebra A B) (e : f.toAlgebra = a)
    (M : ModuleCat.{u} A) (m : M) :
    (extendScalarsTensorIsoOf f a e M).hom ((extendRestrictScalarsAdj f).unit.app M m) =
      (letI := a; (1 : B) ⊗ₜ[A] m) := by
  subst a
  rfl

variable [algebraStructure : Algebra A B] (M : ModuleCat.{u} A)

/-- Compare the actual extension of scalars with the coefficient module used
in the standard overlap and the faithful-flat equalizer. -/
def extendScalarsTensorIso :
    (extendScalars (algebraMap A B)).obj M ≅ ModuleCat.of B (B ⊗[A] M) := by
  let f := algebraMap A B
  have e : f.toAlgebra = algebraStructure := toAlgebra_algebraMap
  change (extendScalars f).obj M ≅ tensorModuleOfAlgebra algebraStructure M
  exact extendScalarsTensorIsoOf f algebraStructure e M

/-- The distinguished generators agree on the two presentations. -/
theorem extendScalarsTensorIso_unit (m : M) :
    (extendScalarsTensorIso (B := B) M).hom
      ((extendRestrictScalarsAdj (algebraMap A B)).unit.app M m) = (1 : B) ⊗ₜ[A] m := by
  let f := algebraMap A B
  have e : f.toAlgebra = algebraStructure := toAlgebra_algebraMap
  exact extendScalarsTensorIsoOf_unit f algebraStructure e M m

/-- The canonical tensor presentation carries scalar extension of a module
map to the usual base-change map. -/
theorem extendScalarsTensorIso_natural {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    (extendScalars (algebraMap A B)).map f ≫ (extendScalarsTensorIso (B := B) N).hom =
      (extendScalarsTensorIso (B := B) M).hom ≫ ModuleCat.ofHom (f.hom.baseChange B) := by
  let a := algebraMap A B
  let E : ModuleCat.{u} A ⥤ ModuleCat.{u} B := extendScalars a
  let η := (extendRestrictScalarsAdj a).unit
  apply ExtendScalars.hom_ext
  intro x
  change (extendScalarsTensorIso (B := B) N).hom (E.map f (η.app M x)) =
    f.hom.baseChange B ((extendScalarsTensorIso (B := B) M).hom (η.app M x))
  have mapUnit : E.map f (η.app M x) = η.app N (f x) := rfl
  rw [mapUnit, extendScalarsTensorIso_unit, extendScalarsTensorIso_unit, LinearMap.baseChange_tmul]

end

end SHIGURE.CoefficientDescent
