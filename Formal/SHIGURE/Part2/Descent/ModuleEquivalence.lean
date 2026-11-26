import Formal.SHIGURE.Part2.Descent.Standard
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.CategoryTheory.Equivalence

/-! # Effective descent of modules

Scalar extension and the fixed-vector equalizer define inverse functors
for the actual overlap data and all compatible linear maps.
-/

namespace SHIGURE.CoefficientDescent

open TensorProduct CategoryTheory

noncomputable section

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- A module over the large algebra equipped with descent across the two scalar embeddings. -/
structure DescentModule (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] where
  carrier : Type u
  [addGroup : AddCommGroup carrier]
  [moduleA : Module A carrier]
  [moduleB : Module B carrier]
  [tower : IsScalarTower A B carrier]
  datum : Datum A B carrier

attribute [instance] DescentModule.addGroup DescentModule.moduleA DescentModule.moduleB DescentModule.tower

namespace DescentModule

variable {X Y Z : DescentModule A B}

/-- Bundle an actual descent datum. -/
def ofDatum {N : Type u} [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    (D : Datum A B N) : DescentModule A B := ⟨N, D⟩

/-- Morphisms are all large-algebra-linear maps commuting with the overlap. -/
structure Hom (X Y : DescentModule A B) where
  hom : X.carrier →ₗ[B] Y.carrier
  compatible : X.datum.Compatible Y.datum hom

@[ext] theorem Hom.ext {f g : Hom X Y} (same : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases same
  rfl

instance : Category (DescentModule A B) where
  Hom := Hom
  id X := ⟨LinearMap.id, X.datum.compatible_id⟩
  comp {X Y Z} f g := ⟨g.hom.comp f.hom, X.datum.compatible_comp Y.datum Z.datum f.compatible g.compatible⟩

@[simp] theorem id_hom (X : DescentModule A B) : (𝟙 X : X ⟶ X).hom = LinearMap.id := rfl

@[simp] theorem comp_hom (f : X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).hom = g.hom.comp f.hom := rfl

/-- Descent is the fixed-vector equalizer on objects and restriction on maps. -/
def descend : DescentModule A B ⥤ ModuleCat.{u} A where
  obj X := ModuleCat.of A X.datum.toCoaction.descended
  map {X Y} f := ModuleCat.ofHom (X.datum.descendMap Y.datum f.hom f.compatible)
  map_id X := by ext x; rfl
  map_comp f g := by ext x; rfl

private theorem standardCompatible {M M' : ModuleCat.{u} A} (f : M ⟶ M') :
    (standardDatum (A := A) (B := B) (M := M)).Compatible
      (standardDatum (A := A) (B := B) (M := M')) (f.hom.baseChange B) := by
  apply (Datum.compatible_iff_coaction _ _ _).2
  suffices ((f.hom.baseChange B).restrictScalars A).baseChange B ∘ₗ
      (standardDatum (A := A) (B := B) (M := M)).coactionMap =
      (standardDatum (A := A) (B := B) (M := M')).coactionMap ∘ₗ (f.hom.baseChange B) from
    LinearMap.congr_fun this
  apply AlgebraTensorModule.ext
  intro b m
  rfl

/-- Scalar extension equips the tensor module with the standard triple cocycle. -/
def extend : ModuleCat.{u} A ⥤ DescentModule A B where
  obj M := ofDatum (standardDatum (A := A) (B := B) (M := M))
  map f := ⟨f.hom.baseChange B, standardCompatible f⟩
  map_id M := by
    apply Hom.ext
    apply AlgebraTensorModule.ext
    intro b m
    rfl
  map_comp f g := by
    apply Hom.ext
    apply AlgebraTensorModule.ext
    intro b m
    rfl

variable [Module.FaithfullyFlat A B]

omit [Module.FaithfullyFlat A B] in
private theorem comparisonCompatible (X : DescentModule A B) :
    ((extend (A := A) (B := B)).obj ((descend (A := A) (B := B)).obj X)).datum.Compatible X.datum
      X.datum.toCoaction.comparison := by
  apply (Datum.compatible_iff_coaction _ _ _).2
  suffices (X.datum.toCoaction.comparison.restrictScalars A).baseChange B ∘ₗ
        ((extend (A := A) (B := B)).obj ((descend (A := A) (B := B)).obj X)).datum.coactionMap =
      X.datum.coactionMap ∘ₗ X.datum.toCoaction.comparison from LinearMap.congr_fun this
  apply AlgebraTensorModule.ext
  intro b m
  change (X.datum.toCoaction.comparison.restrictScalars A).baseChange B
      (b ⊗ₜ[A] ((1 : B) ⊗ₜ[A] m)) = X.datum.coactionMap (b • m.val)
  have fixed : X.datum.coactionMap m.val = (1 : B) ⊗ₜ[A] m.val :=
    (X.datum.toCoaction.descended_iff m.val).1 m.property
  rw [LinearMap.baseChange_tmul, LinearMap.restrictScalars_apply, Coaction.comparison_tmul,
    one_smul, map_smul, fixed, smul_tmul', smul_eq_mul, mul_one]

omit [Module.FaithfullyFlat A B] in
private theorem compatible_inverse (e : X.carrier ≃ₗ[B] Y.carrier)
    (compatible : X.datum.Compatible Y.datum e.toLinearMap) :
    Y.datum.Compatible X.datum e.symm.toLinearMap := by
  apply (Datum.compatible_iff_coaction _ _ _).2
  intro y
  let lifted := LinearEquiv.baseChange A B X.carrier Y.carrier (e.restrictScalars A)
  apply lifted.injective
  have coherent := (X.datum.compatible_iff_coaction Y.datum e.toLinearMap).1 compatible (e.symm y)
  change lifted (LinearEquiv.baseChange A B Y.carrier X.carrier (e.symm.restrictScalars A)
        (Y.datum.coactionMap y)) = lifted (X.datum.coactionMap (e.symm y))
  have inverseLift :
      LinearEquiv.baseChange A B Y.carrier X.carrier (e.symm.restrictScalars A) = lifted.symm := by
    apply LinearEquiv.toLinearMap_injective
    apply AlgebraTensorModule.ext
    intro b n
    rfl
  rw [inverseLift, lifted.apply_symm_apply]
  exact (congrArg Y.datum.coactionMap (e.apply_symm_apply y)).symm.trans coherent.symm

private def comparisonIso (X : DescentModule A B) :
    ((descend (A := A) (B := B)) ⋙ (extend (A := A) (B := B))).obj X ≅ X where
  hom := ⟨X.datum.toCoaction.comparisonEquiv.toLinearMap, comparisonCompatible X⟩
  inv := ⟨X.datum.toCoaction.comparisonEquiv.symm.toLinearMap,
    compatible_inverse (X := (extend (A := A) (B := B)).obj ((descend (A := A) (B := B)).obj X))
      (Y := X) X.datum.toCoaction.comparisonEquiv (comparisonCompatible X)⟩
  hom_inv_id := by
    apply Hom.ext
    exact LinearMap.ext X.datum.toCoaction.fromModule_comparison
  inv_hom_id := by
    apply Hom.ext
    exact LinearMap.ext X.datum.toCoaction.comparison_fromModule

/-- The multiplication comparisons assemble into the natural counit. -/
def counitIso : descend (A := A) (B := B) ⋙ extend ≅ 𝟭 (DescentModule A B) :=
  NatIso.ofComponents comparisonIso (by
    intro X Y f
    apply Hom.ext
    exact (X.datum.comparison_natural Y.datum f.hom f.compatible).symm)

/-- Unit insertion identifies the original module with the equalizer after scalar extension. -/
def unitIso : 𝟭 (ModuleCat.{u} A) ≅ extend (A := A) (B := B) ⋙ descend :=
  NatIso.ofComponents (fun (M : ModuleCat.{u} A) =>
    (standardUnitEquiv (A := A) (B := B) (M := M)).toModuleIso) (by
    intro M M' f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    apply Subtype.ext
    change (standardUnitEquiv (A := A) (B := B) (M := M') (f.hom m)).val =
      f.hom.baseChange B (standardUnitEquiv (A := A) (B := B) (M := M) m).val
    rw [standardUnitEquiv_apply, standardUnitEquiv_apply]
    exact (LinearMap.baseChange_tmul (A := B) f.hom (1 : B) m).symm)

/-- Effective faithfully flat descent for modules and all their compatible maps. -/
def equivalence : ModuleCat.{u} A ≌ DescentModule A B where
  functor := extend
  inverse := descend
  unitIso := unitIso
  counitIso := counitIso
  functor_unitIso_comp X := by
    apply Hom.ext
    apply AlgebraTensorModule.ext
    intro b m
    change b • (standardUnitEquiv (A := A) (B := B) (M := X) m).val = b ⊗ₜ[A] m
    rw [standardUnitEquiv_apply]
    change b • ((1 : B) ⊗ₜ[A] m) = b ⊗ₜ[A] m
    rw [smul_tmul', smul_eq_mul, mul_one]

end DescentModule

end

end SHIGURE.CoefficientDescent
