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

variable {M N : ModuleCat.{u} R} {U V : ModuleCat.{u} C}
  [Module A U] [Module A V] [IsScalarTower A C U] [IsScalarTower A C V]

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

set_option maxHeartbeats 475000 in
/-- Pulling back a comparison through the second coordinate applies the comparison
in that slot of the tensor. -/
theorem mixedRightCompIso_pullHom (f₁ f₂ : R →+* C)
    (δ : (extendScalars f₁).obj M ⟶ (extendScalars f₂).obj N)
    (e₁ : (extendScalars f₁).obj M ≅ U) (e₂ : (extendScalars f₂).obj N ≅ V) :
    scalarExtensionPullHom f₁ f₂ g δ ≫ (mixedRightCompIso (A := A) (B := B) f₂ e₂).hom =
    (mixedRightCompIso (A := A) (B := B) f₁ e₁).hom ≫
      ModuleCat.ofHom (tensorProductModuleMap (A := A) (B := B) (C := C)
        (LinearMap.id (R := B) (M := B)) (e₁.inv ≫ δ ≫ e₂.hom).hom) := by
  let E := extendScalars g
  let l := (extendScalarsComp f₁ g).app M ≪≫ E.mapIso e₁
  let r := (extendScalarsComp f₂ g).app N ≪≫ E.mapIso e₂
  let t := mixedRightExtensionIso (A := A) (B := B) (C := C) (N := U)
  let s := mixedRightExtensionIso (A := A) (B := B) (C := C) (N := V)
  let d := e₁.inv ≫ δ ≫ e₂.hom
  let k := ModuleCat.ofHom (tensorProductModuleMap (A := A) (B := B) (C := C)
    (LinearMap.id (R := B) (M := B)) d.hom)
  change scalarExtensionPullHom f₁ f₂ g δ ≫ r.hom ≫ s.hom = (l.hom ≫ t.hom) ≫ k
  have step : scalarExtensionPullHom f₁ f₂ g δ ≫ r.hom = l.hom ≫ E.map d :=
    scalarExtensionPullHom_rechart f₁ f₂ g δ e₁ e₂
  have slot : E.map d ≫ s.hom = t.hom ≫ k := mixedRightExtensionIso_natural d
  rw [← Category.assoc _ r.hom, step, Category.assoc l.hom, slot, Category.assoc]


end Right

section Left

variable {M N : ModuleCat.{u} R} {U V : ModuleCat.{u} B}
  [Module A U] [Module A V] [IsScalarTower A B U] [IsScalarTower A B V]

local notation "g" => firstMixedEmbedding A B C

/-- Extend through the first tensor coordinate and use the given comparison
for the inner extension. -/
def mixedLeftCompIso (f : R →+* B) (e : (extendScalars f).obj M ≅ U) :
    (extendScalars (RingHom.comp g f)).obj M ≅ ModuleCat.of (B ⊗[A] C) (U ⊗[A] C) :=
  (extendScalarsComp f g).app M ≪≫ (extendScalars g).mapIso e ≪≫
    mixedLeftExtensionIso (A := A) (B := B) (C := C) (N := U)

set_option maxHeartbeats 475000 in
/-- A unit for a composition of extensions gives the successive units in the tensor coordinate. -/
theorem mixedLeftCompIso_unit (f : R →+* B) (e : (extendScalars f).obj M ≅ U) (x : M) :
    (mixedLeftCompIso (A := A) (B := B) f e).hom
      ((extendRestrictScalarsAdj (RingHom.comp g f)).unit.app M x) =
    e.hom ((extendRestrictScalarsAdj f).unit.app M x) ⊗ₜ[A] (1 : C) := by
  let r := mixedLeftExtensionIso (A := A) (B := B) (C := C) (N := U)
  change r.hom ((extendScalars g).map e.hom
      ((extendScalarsComp f g).hom.app M ((extendRestrictScalarsAdj (RingHom.comp g f)).unit.app M x))) = _
  rw [scalarExtensionComp_map_unit]
  exact mixedLeftExtensionIso_unit _

set_option maxHeartbeats 475000 in
/-- Pulling back a comparison through the first coordinate applies the comparison
in that slot of the tensor. -/
theorem mixedLeftCompIso_pullHom (f₁ f₂ : R →+* B)
    (δ : (extendScalars f₁).obj M ⟶ (extendScalars f₂).obj N)
    (e₁ : (extendScalars f₁).obj M ≅ U) (e₂ : (extendScalars f₂).obj N ≅ V) :
    scalarExtensionPullHom f₁ f₂ g δ ≫ (mixedLeftCompIso (A := A) (B := B) f₂ e₂).hom =
    (mixedLeftCompIso (A := A) (B := B) f₁ e₁).hom ≫
      ModuleCat.ofHom (tensorProductModuleMap (A := A) (B := B) (C := C)
        (e₁.inv ≫ δ ≫ e₂.hom).hom (LinearMap.id (R := C) (M := C))) := by
  let E := extendScalars g
  let l := (extendScalarsComp f₁ g).app M ≪≫ E.mapIso e₁
  let r := (extendScalarsComp f₂ g).app N ≪≫ E.mapIso e₂
  let t := mixedLeftExtensionIso (A := A) (B := B) (C := C) (N := U)
  let s := mixedLeftExtensionIso (A := A) (B := B) (C := C) (N := V)
  let d := e₁.inv ≫ δ ≫ e₂.hom
  let k := ModuleCat.ofHom (tensorProductModuleMap (A := A) (B := B) (C := C)
    d.hom (LinearMap.id (R := C) (M := C)))
  change scalarExtensionPullHom f₁ f₂ g δ ≫ r.hom ≫ s.hom = (l.hom ≫ t.hom) ≫ k
  have step : scalarExtensionPullHom f₁ f₂ g δ ≫ r.hom = l.hom ≫ E.map d :=
    scalarExtensionPullHom_rechart f₁ f₂ g δ e₁ e₂
  have slot : E.map d ≫ s.hom = t.hom ≫ k := mixedLeftExtensionIso_natural d
  rw [← Category.assoc _ r.hom, step, Category.assoc l.hom, slot, Category.assoc]


end Left

end

end SHIGURE.CoefficientDescent
