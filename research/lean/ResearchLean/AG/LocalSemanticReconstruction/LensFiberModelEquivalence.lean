import ResearchLean.AG.LocalSemanticReconstruction.CSFiniteLocalReading
import Formal.Util.AssertStandardAxioms

/-!
# Reconstruction of lenses from finite reference fibers

For a fixed lens input, the local model is its finite reference fiber.  The
accepted restriction map reads every named-get/put package morphism on that
fiber.  Conversely, `LensRealization.ext` assembles every local map into the
complete state map using the original `put` operations.

The local object contains only the finite fiber.  Its semantic realization is
constructed as the product lens over the parameter-owned view type; no
completed realization, extension certificate, or decoder membership is stored
in the local value.  The accepted `res_ext` and `ext_res` laws prove full
faithfulness, while `productFiberEquiv` proves object assembly.  Hence the
primitive fiber reading is a category equivalence retaining every
get/put-preserving morphism, including noninvertible ones.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory
open AAT.AG.RealizationReconstruction

universe u

/-- Read an independently specified semantic lens on its finite reference
fiber.  Morphisms are the accepted restrictions of complete state maps. -/
noncomputable def lensSemanticFiberReading (input : LensFamilyInput.{u}) :
    LensRealization input.View input.reference ⥤ FintypeCat.{u} where
  obj X := finiteLocalValue X.Fiber
  map f := FintypeCat.homMk (LensRealization.res f)
  map_id X := by
    apply FintypeCat.hom_ext
    intro state
    rfl
  map_comp f g := by
    apply FintypeCat.hom_ext
    intro state
    rfl

/-- No-unfold object API: the semantic reading is exactly the accepted finite
reference fiber. -/
@[simp] theorem lensSemanticFiberReading_obj
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    (lensSemanticFiberReading input).obj X = finiteLocalValue X.Fiber :=
  rfl

/-- No-unfold map API: the semantic reading is exactly `LensRealization.res`. -/
@[simp] theorem lensSemanticFiberReading_map_apply
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : X ⟶ Y) (state : X.Fiber) :
    (lensSemanticFiberReading input).map f state =
      LensRealization.res f state :=
  rfl

/-- Every finite local map assembles to a complete semantic lens morphism via
the source and target `put` operations. -/
noncomputable def lensSemanticFiberReadingFull
    (input : LensFamilyInput.{u}) :
    (lensSemanticFiberReading input).Full where
  map_surjective := by
    intro X Y localMap
    refine ⟨LensRealization.ext (fun state ↦ localMap state), ?_⟩
    apply FintypeCat.hom_ext
    intro state
    exact congrFun (LensRealization.res_ext
      (fun state ↦ localMap state)) state

/-- Finite reference-fiber readings distinguish every complete semantic lens
morphism by the accepted `ext_res` inverse law. -/
noncomputable def lensSemanticFiberReadingFaithful
    (input : LensFamilyInput.{u}) :
    (lensSemanticFiberReading input).Faithful where
  map_injective := by
    intro X Y first second equality
    apply (LensRealization.homEquivFiberMap X Y).injective
    apply funext
    intro state
    exact congrArg (fun localMap => localMap state) equality

/-- Assemble a finite local object as the product lens whose complement is the
supplied fiber.  Its `get` and `put` operations are constructed from the fixed
view parameter and are not fields of the local object. -/
noncomputable def lensFiberModelRealization
    (input : LensFamilyInput.{u}) (fiber : FintypeCat.{u}) :
    LensRealization input.View input.reference :=
  LensRealization.product input.View fiber input.reference

/-- The assembled local model reads its view by the product projection. -/
@[simp] theorem lensFiberModelRealization_get
    (input : LensFamilyInput.{u}) (fiber : FintypeCat.{u})
    (state : input.View × fiber) :
    (lensFiberModelRealization input fiber).get state = state.1 :=
  rfl

/-- The assembled local model implements update by replacing the visible view
and retaining the supplied finite-fiber coordinate. -/
@[simp] theorem lensFiberModelRealization_put
    (input : LensFamilyInput.{u}) (fiber : FintypeCat.{u})
    (state : input.View × fiber) (view : input.View) :
    (lensFiberModelRealization input fiber).put state view =
      (view, state.2) :=
  rfl

/-- Reading the assembled product lens recovers the supplied finite local
object through the canonical product-fiber equivalence. -/
noncomputable def lensFiberModelRealizationIso
    (input : LensFamilyInput.{u}) (fiber : FintypeCat.{u}) :
    (lensSemanticFiberReading input).obj
        (lensFiberModelRealization input fiber) ≅ fiber :=
  FintypeCat.equivEquivIso
    (LensRealization.productFiberEquiv
      input.View fiber input.reference)

/-- Every finite local object is the reference-fiber reading of an explicitly
constructed product lens. -/
noncomputable def lensSemanticFiberReadingEssSurj
    (input : LensFamilyInput.{u}) :
    (lensSemanticFiberReading input).EssSurj :=
  Functor.EssSurj.mk fun fiber =>
    ⟨lensFiberModelRealization input fiber,
      ⟨lensFiberModelRealizationIso input fiber⟩⟩

/-- Semantic total lenses and finite reference-fiber local models are
equivalent through the primitive restriction reading. -/
noncomputable def lensSemanticFiberEquivalence
    (input : LensFamilyInput.{u}) :
    LensRealization input.View input.reference ≌ FintypeCat.{u} := by
  letI : (lensSemanticFiberReading input).Faithful :=
    lensSemanticFiberReadingFaithful input
  letI : (lensSemanticFiberReading input).Full :=
    lensSemanticFiberReadingFull input
  letI : (lensSemanticFiberReading input).EssSurj :=
    lensSemanticFiberReadingEssSurj input
  letI : (lensSemanticFiberReading input).IsEquivalence := {}
  exact (lensSemanticFiberReading input).asEquivalence

/-- The forward functor of the semantic equivalence is definitionally the
primitive finite-fiber reading. -/
@[simp] theorem lensSemanticFiberEquivalence_functor
    (input : LensFamilyInput.{u}) :
    (lensSemanticFiberEquivalence input).functor =
      lensSemanticFiberReading input :=
  rfl

/-- The accepted closed-family finite-fiber reading is faithful because
operation-package readback and semantic fiber restriction are both faithful. -/
noncomputable def lensFiberValueReadingFaithful
    (input : LensFamilyInput.{u}) :
    (lensFiberValueReading input).Faithful where
  map_injective := by
    intro X Y first second equality
    cases X with
    | lens source =>
      cases Y with
      | lens target =>
        have semanticEquality :
            first.down.toSemanticHom = second.down.toSemanticHom := by
          apply (lensSemanticFiberReadingFaithful input).map_injective
          exact equality
        apply ULift.ext
        calc
          first.down = LensAATIndependentGeneratedPackageHom.ofSemanticHom
              first.down.toSemanticHom :=
            (LensAATIndependentGeneratedPackageHom.ofSemanticHom_toSemanticHom
              first.down).symm
          _ = LensAATIndependentGeneratedPackageHom.ofSemanticHom
              second.down.toSemanticHom := congrArg _ semanticEquality
          _ = second.down :=
            LensAATIndependentGeneratedPackageHom.ofSemanticHom_toSemanticHom
              second.down

/-- Every finite local map assembles through `LensRealization.ext` and enters
the closed-family category through the accepted operation-package round trip. -/
noncomputable def lensFiberValueReadingFull
    (input : LensFamilyInput.{u}) :
    (lensFiberValueReading input).Full where
  map_surjective := by
    intro X Y localMap
    cases X with
    | lens source =>
      cases Y with
      | lens target =>
        refine ⟨closedFamilyLensHom
          (LensRealization.ext (fun state ↦ localMap state)), ?_⟩
        apply FintypeCat.hom_ext
        intro state
        exact congrFun (LensRealization.res_ext
          (fun state ↦ localMap state)) state

/-- Every finite local object is read from the explicitly assembled product
lens in the closed-family category. -/
noncomputable def lensFiberValueReadingEssSurj
    (input : LensFamilyInput.{u}) :
    (lensFiberValueReading input).EssSurj :=
  Functor.EssSurj.mk fun fiber =>
    ⟨FamilyRealization.lens (lensFiberModelRealization input fiber),
      ⟨lensFiberModelRealizationIso input fiber⟩⟩

/-- The closed-family lens fiber is equivalent to finite reference-fiber local
models, with the accepted primitive reading as its forward functor. -/
noncomputable def lensClosedFamilyFiberEquivalence
    (input : LensFamilyInput.{u}) :
    FamilyRealization.{u, u} (.lens input) ≌ FintypeCat.{u} := by
  letI : (lensFiberValueReading input).Faithful :=
    lensFiberValueReadingFaithful input
  letI : (lensFiberValueReading input).Full :=
    lensFiberValueReadingFull input
  letI : (lensFiberValueReading input).EssSurj :=
    lensFiberValueReadingEssSurj input
  letI : (lensFiberValueReading input).IsEquivalence := {}
  exact (lensFiberValueReading input).asEquivalence

/-- The forward functor of the closed-family equivalence is exactly the Cycle
20 primitive finite-fiber reading. -/
@[simp] theorem lensClosedFamilyFiberEquivalence_functor
    (input : LensFamilyInput.{u}) :
    (lensClosedFamilyFiberEquivalence input).functor =
      lensFiberValueReading input :=
  rfl

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction

end AAT.AG.LocalSemanticReconstruction
