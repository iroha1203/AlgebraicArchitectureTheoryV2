import Formal.SHIGURE.Part2.Descent.ScalarOverlap
import Formal.SHIGURE.Part2.Descent.ScalarCocycle

/-! # Iterated scalar extension in a tensor coordinate -/

namespace SHIGURE.CoefficientDescent

open CategoryTheory TensorProduct ModuleCat

noncomputable section

universe u

variable {A B C R : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing R]
  [Algebra A B] [Algebra A C]

attribute [local instance] tensorProductModule

section Right

variable {M : ModuleCat.{u} R} {U : ModuleCat.{u} C} [Module A U] [IsScalarTower A C U]

local notation "g" => secondMixedEmbedding A B C

/-- Extend through the second tensor coordinate and use the given comparison
for the inner extension. -/
def mixedRightCompIso (f : R →+* C) (e : (extendScalars f).obj M ≅ U) :
    (extendScalars (RingHom.comp g f)).obj M ≅ ModuleCat.of (B ⊗[A] C) (B ⊗[A] U) :=
  (extendScalarsComp f g).app M ≪≫ (extendScalars g).mapIso e ≪≫
    mixedRightExtensionIso (A := A) (B := B) (C := C) (N := U)

set_option maxHeartbeats 475000 in
/-- A unit for a composition of extensions gives the successive units in the tensor coordinate. -/
theorem mixedRightCompIso_unit (f : R →+* C) (e : (extendScalars f).obj M ≅ U) (x : M) :
    (mixedRightCompIso (A := A) (B := B) f e).hom
      ((extendRestrictScalarsAdj (RingHom.comp g f)).unit.app M x) =
    (1 : B) ⊗ₜ[A] e.hom ((extendRestrictScalarsAdj f).unit.app M x) := by
  let r := mixedRightExtensionIso (A := A) (B := B) (C := C) (N := U)
  change r.hom ((extendScalars g).map e.hom
      ((extendScalarsComp f g).hom.app M ((extendRestrictScalarsAdj (RingHom.comp g f)).unit.app M x))) = _
  rw [scalarExtensionComp_map_unit]
  exact mixedRightExtensionIso_unit _

end Right

end

end SHIGURE.CoefficientDescent
