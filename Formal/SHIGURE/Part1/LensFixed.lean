import Formal.SHIGURE.Part1.FixedModels
import Formal.SHIGURE.Part1.Lens
import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.CategoryTheory.Types.Basic

/-! # Lenses with a specified view type

The fixed-view part of Theorem 2.9 uses mathlib's fiber of the view functor.
The semantic side is the fixed-reduct category of Definition 2.2 for the
subsignature containing the view sort alone.

## Implementation notes

The fiber keeps the view type with an equality to the specified type, so its
arrows lie over the identity even when the carriers need transport. Requiring
objects to be stored with the specified view type definitionally would require
rebuilding a lens across that equality. The fiber uses the same underlying
lens and translates that transport to the existing fixed-model arrow condition.
-/

universe u

namespace SHIGURE.Lens

open CategoryTheory

/-- Forget a lens's state and retain its view type and its arrows' view maps. -/
def viewFunctor : Lens.{u} ⥤ Type u where
  obj := View
  map f := f.view
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor retains the view type. -/
@[simp] theorem viewFunctor_obj (L : Lens.{u}) : viewFunctor.obj L = L.View := rfl

/-- The functor takes the view component of each arrow. -/
@[simp] theorem viewFunctor_map {L M : Lens.{u}} (f : L ⟶ M) : viewFunctor.map f = f.view := rfl

/-- Lenses with the specified view type, with arrows over the identity of that type. -/
abbrev Fixed (V : Type u) := viewFunctor.Fiber V

namespace Fixed

/-- The signature of the fixed view sort has no operations or relations. -/
def viewSignature : Signature.{u} where
  SortType := PUnit
  Total := PEmpty
  Rel := PEmpty
  Partial := PEmpty
  Quantity := PEmpty
  totalArity f := nomatch f
  relInputs r := nomatch r
  partialArity p := nomatch p
  quantityArity q := nomatch q

/-- Include the only fixed sort as the view sort of the lens theory. -/
def viewInclusion : Subsignature viewSignature.{u} Chapter1.Lens.signature.{u} := by
  let names : SignatureNames viewSignature.{u} Chapter1.Lens.signature.{u} :=
    { onSort := fun _ => .view
      onTotal := fun f => nomatch f
      onRel := fun r => nomatch r
      onPartial := fun p => nomatch p
      onQuantity := fun q => nomatch q
      totalArity := fun f => nomatch f
      relInputs := fun r => nomatch r
      partialArity := fun p => nomatch p
      quantityArity := fun q => nomatch q }
  refine ⟨names, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b _
    exact Subsingleton.elim (α := PUnit) a b
  · intro f _ _
    exact nomatch f
  · intro r _ _
    exact nomatch r
  · intro p _ _
    exact nomatch p
  · intro q _ _
    exact nomatch q

/-- The fixed structure assigns the prescribed type to the only sort. -/
def viewData (V : Type u) : Structure viewSignature.{u} where
  carrier _ := V
  total f := nomatch f
  relation r := nomatch r
  partialDomain p := nomatch p
  partialValue p := nomatch p
  quantity q := nomatch q

/-- The right-hand side of the fixed-view isomorphism of Theorem 2.9. -/
abbrev Semantic (V : Type u) := FixedModel Chapter1.Lens.theory.{u} viewInclusion (viewData V)

/-- The reduct agrees with the prescribed view structure precisely when that carrier agrees. -/
theorem reduct_eq_iff (A : Structure Chapter1.Lens.signature.{u}) (V : Type u) :
    viewInclusion.val.restrict A = viewData V ↔ A.carrier .view = V := by
  constructor
  · intro same
    exact congrArg (fun B : Structure viewSignature => B.carrier PUnit.unit) same
  · intro same
    subst V
    have domains : (viewInclusion.val.restrict A).partialDomain =
        (viewData (A.carrier .view)).partialDomain := by
      funext p
      exact nomatch p
    refine Structure.ext rfl ?_ ?_ (heq_of_eq domains) ?_ ?_
    · exact heq_of_eq (funext fun f => nomatch f)
    · exact heq_of_eq (funext fun r => nomatch r)
    · exact Structure.partialValue_heq domains _ _ (fun p => nomatch p)
    · exact heq_of_eq (funext fun q => nomatch q)

/-- Equality in the category of types acts by transport on elements. -/
private theorem types_eqToHom_apply {X Y : Type u} (same : X = Y) (x : X) :
    (eqToHom same : X ⟶ Y) x = cast same x := by
  subst Y
  rfl

variable {V : Type u}

/-- The fiber arrow condition says exactly that the view component is the transported identity. -/
theorem view_lift_iff {A B : Fixed V} (f : A.val ⟶ B.val) :
    viewFunctor.IsHomLift (𝟙 V) f ↔ ∀ v, f.view v = cast (A.property.trans B.property.symm) v := by
  constructor
  · intro lifted v
    letI : viewFunctor.IsHomLift (𝟙 V) f := lifted
    have factors := congrFun (IsHomLift.fac' viewFunctor (𝟙 V) f) v
    simpa only [viewFunctor_map, types_comp_apply, types_id_apply, types_eqToHom_apply, cast_cast] using factors
  · intro fixes
    apply IsHomLift.of_fac' viewFunctor (𝟙 V) f A.property B.property
    funext v
    simpa only [viewFunctor_map, types_comp_apply, types_id_apply, types_eqToHom_apply, cast_cast] using fixes v

/-- A lens in the view fiber gives a model with the specified reduct. -/
def toFixedModel (A : Fixed V) : Semantic V :=
  ⟨A.val.toModel, (reduct_eq_iff A.val.toStructure V).2 A.property⟩

/-- A model with the specified reduct gives a lens in the view fiber. -/
def ofFixedModel (A : Semantic V) : Fixed V :=
  ⟨Lens.ofModel A.model, (reduct_eq_iff A.model.obj V).1 A.fixed⟩

/-- Encoding and reading a fixed lens recovers the same fiber object. -/
@[simp] theorem ofFixedModel_toFixedModel (A : Fixed V) : ofFixedModel (toFixedModel A) = A :=
  Subtype.ext (Lens.ofModel_toModel A.val)

/-- Two fixed lens models with the same underlying model coincide. -/
private theorem fixedModel_ext {A B : Semantic V} (same : A.model = B.model) : A = B := by
  cases A
  cases B
  cases same
  rfl

/-- Reading and encoding a fixed model recovers the same fixed model. -/
@[simp] theorem toFixedModel_ofFixedModel (A : Semantic V) : toFixedModel (ofFixedModel A) = A :=
  fixedModel_ext (Lens.toModel_ofModel A.model)

/-- The fiber arrow condition supplies the fixed-carrier proof for the model arrow. -/
def toFixedHom {A B : Fixed V} (f : A ⟶ B) : toFixedModel A ⟶ toFixedModel B :=
  let underlying := Functor.Fiber.fiberInclusion.map f
  FixedModel.Hom.mk (Lens.toModelHom underlying)
    (fun _ v => (view_lift_iff (A := A) (B := B) underlying).1 f.property v)

/-- A map fixing the view reduct gives a lens map over the identity view arrow. -/
def ofFixedHom {A B : Semantic V} (f : FixedModel.Hom A B) : ofFixedModel A ⟶ ofFixedModel B :=
  let underlying := Lens.ofModelHom (FixedModel.Hom.modelHom f)
  ⟨underlying, (view_lift_iff (A := ofFixedModel A) (B := ofFixedModel B) underlying).2
    fun v => FixedModel.Hom.fixes f PUnit.unit v⟩

/-- Encoding a fiber arrow uses the model map of the original lens arrow. -/
theorem toFixedHom_modelHom {A B : Fixed V} (f : A ⟶ B) :
    FixedModel.Hom.modelHom (toFixedHom f) = Lens.toModelHom (Functor.Fiber.fiberInclusion.map f) := rfl

/-- Reading a fixed-model arrow uses the lens map of the original model arrow. -/
theorem ofFixedHom_fiberInclusion {A B : Semantic V} (f : FixedModel.Hom A B) :
    Functor.Fiber.fiberInclusion.map (ofFixedHom f) = Lens.ofModelHom (FixedModel.Hom.modelHom f) := rfl

/-- Encode the fixed lens category into the fixed semantic category. -/
def toModels (V : Type u) : Fixed V ⥤ Semantic V where
  obj := toFixedModel
  map := toFixedHom
  map_id _ := FixedModel.Hom.ext (Model.hom_ext fun s _ => by cases s <;> rfl)
  map_comp _ _ := FixedModel.Hom.ext (Model.hom_ext fun s _ => by cases s <;> rfl)

/-- Recover fixed lens objects and arrows from the fixed semantic category. -/
def ofModels (V : Type u) : Semantic V ⥤ Fixed V where
  obj := ofFixedModel
  map := ofFixedHom
  map_id _ := Functor.Fiber.hom_ext (Lens.hom_ext (fun _ => rfl) (fun _ => rfl))
  map_comp _ _ := Functor.Fiber.hom_ext (Lens.hom_ext (fun _ => rfl) (fun _ => rfl))

/-- The fixed lens functors compose to the identity on fixed lenses. -/
theorem toModels_comp_ofModels (V : Type u) : toModels V ⋙ ofModels V = 𝟭 (Fixed V) := by
  have objects (A : Fixed V) : (toModels V ⋙ ofModels V).obj A = (𝟭 (Fixed V)).obj A := by
    change ofFixedModel (toFixedModel A) = A
    exact ofFixedModel_toFixedModel A
  refine Functor.ext objects ?_
  intro A B f
  apply Functor.Fiber.hom_ext
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  apply Lens.hom_ext
  · intro a
    simp only [Lens.comp_state, Lens.eqToHom_state, Function.comp_apply, cast_eq]
    change (Functor.Fiber.fiberInclusion.map (ofFixedHom (toFixedHom f))).state a = _
    rw [ofFixedHom_fiberInclusion, toFixedHom_modelHom,
      Lens.ofModelHom_state_apply, Lens.toModelHom_source_apply]
    rfl
  · intro v
    simp only [Lens.comp_view, Lens.eqToHom_view, Function.comp_apply, cast_eq]
    change (Functor.Fiber.fiberInclusion.map (ofFixedHom (toFixedHom f))).view v = _
    rw [ofFixedHom_fiberInclusion, toFixedHom_modelHom,
      Lens.ofModelHom_view_apply, Lens.toModelHom_view_apply]
    rfl

/-- The fixed lens functors compose to the identity on fixed semantic models. -/
theorem ofModels_comp_toModels (V : Type u) : ofModels V ⋙ toModels V = 𝟭 (Semantic V) := by
  have objects (A : Semantic V) : (ofModels V ⋙ toModels V).obj A = (𝟭 (Semantic V)).obj A := by
    change toFixedModel (ofFixedModel A) = A
    exact toFixedModel_ofFixedModel A
  refine Functor.ext objects ?_
  intro A B f
  apply FixedModel.Hom.ext
  let forget : Semantic V ⥤ Model Chapter1.Lens.theory.{u} := FixedModel.forget
  change forget.map ((ofModels V ⋙ toModels V).map f) =
    forget.map (eqToHom (objects A) ≫ f ≫ eqToHom (objects B).symm)
  rw [Functor.map_comp, Functor.map_comp, eqToHom_map, eqToHom_map]
  apply Model.hom_ext
  intro s x
  rw [Model.comp_apply, Model.comp_apply, Model.eqToHom_apply, Model.eqToHom_apply]
  change (FixedModel.Hom.modelHom (toFixedHom (ofFixedHom f))).hom.onSort s x = _
  rw [toFixedHom_modelHom, ofFixedHom_fiberInclusion]
  cases s with
  | source =>
    exact (Lens.toModelHom_source_apply (Lens.ofModelHom (FixedModel.Hom.modelHom f)) x).trans
      (Lens.ofModelHom_state_apply (FixedModel.Hom.modelHom f) x)
  | view =>
    exact (Lens.toModelHom_view_apply (Lens.ofModelHom (FixedModel.Hom.modelHom f)) x).trans
      (Lens.ofModelHom_view_apply (FixedModel.Hom.modelHom f) x)

/-- Theorem 2.9 with a fixed view, as a strict isomorphism of categories. -/
def modelIso (V : Type u) : Cat.of (Fixed V) ≅ Cat.of (Semantic V) where
  hom := (toModels V).toCatHom
  inv := (ofModels V).toCatHom
  hom_inv_id := congrArg Functor.toCatHom (toModels_comp_ofModels V)
  inv_hom_id := congrArg Functor.toCatHom (ofModels_comp_toModels V)

/-- The fixed-view object constructions give a bijection. -/
def modelObjectEquiv (V : Type u) : Fixed V ≃ Semantic V :=
  ⟨toFixedModel, ofFixedModel, ofFixedModel_toFixedModel, toFixedModel_ofFixedModel⟩

/-- The fixed-view model isomorphism recovers all arrows fixing the prescribed type. -/
def modelHomEquiv (A B : Fixed V) : (A ⟶ B) ≃ (toFixedModel A ⟶ toFixedModel B) :=
  (Cat.equivOfIso (modelIso V)).fullyFaithfulFunctor.homEquiv

/-- The fixed-view hom-set bijection uses the underlying model arrow. -/
theorem modelHomEquiv_apply {A B : Fixed V} (f : A ⟶ B) : modelHomEquiv A B f = toFixedHom f := rfl

end Fixed
end SHIGURE.Lens
