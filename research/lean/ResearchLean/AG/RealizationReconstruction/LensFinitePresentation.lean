import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Idempotents.Basic
import ResearchLean.AG.RealizationReconstruction.LensSemantics

/-!
# Finite presentation and reconstruction of total lenses

This module implements G-123(A,B,E) for the lens input family.  Presentation
objects are natural numbers and presentation morphisms are finite tables
`Fin n → Fin m`.  The decoder constructs product lenses.  Its fullness,
faithfulness, essential surjectivity, idempotent completeness of the semantic
category, and retract generation are proved from the lens laws and finiteness
of the reference fiber.

## Implementation notes

The semantic category is imported from `LensSemantics`; it was defined before
and independently of this syntax.  A presentation morphism is literally its
finite table, so syntactic equality is function extensionality on entries.
The evaluation equivalence `J` is therefore the identity equivalence on table
data, while the nontrivial `res`/`ext` inverse laws connect that table to every
state of the decoded lens.  Completed state maps are never presentation
constants.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

/-- A finite lens presentation records the cardinality of its complement table. -/
@[ext]
structure LensPresentation where
  /-- Number of complement entries. -/
  card : ℕ

namespace LensPresentation

/-- Presentation morphisms are finite tables between complements. -/
instance : Category LensPresentation where
  Hom P Q := Fin P.card → Fin Q.card
  id _ := id
  comp f g := g ∘ f
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

/-- Construct the presentation with `n` complement entries. -/
def ofNat (n : ℕ) : LensPresentation := ⟨n⟩

/-- The finite generator-map data between two presentations. -/
abbrev GeneratorMap (P Q : LensPresentation) := Fin P.card → Fin Q.card

/-- Syntax evaluation is a bijection onto finite generator maps. -/
def evaluationEquiv (P Q : LensPresentation) :
    (P ⟶ Q) ≃ GeneratorMap P Q :=
  Equiv.refl _

end LensPresentation

namespace LensRealization

variable (V : Type u) (v₀ : V)

/-- Decode a finite complement table as the corresponding product lens. -/
def lensDecoder : LensPresentation ⥤ LensRealization V v₀ where
  obj P := product V (ULift.{u} (Fin P.card)) v₀
  map {P Q} f :=
    { toFun := fun c => (c.1, ULift.up (f c.2.down))
      get_naturality := fun _ => rfl
      put_naturality := fun _ _ => rfl }
  map_id P := by
    apply Hom.ext
    funext c
    cases c
    rfl
  map_comp f g := by
    apply Hom.ext
    funext c
    cases c
    rfl

variable {V v₀}

/-- Restrict a decoded complete morphism to its finite complement table. -/
def displayedRes {P Q : LensPresentation}
    (h : (lensDecoder V v₀).obj P ⟶ (lensDecoder V v₀).obj Q) :
    LensPresentation.GeneratorMap P Q :=
  fun k => (h (v₀, ULift.up k)).2.down

/-- Extend a finite table to all states of the two decoded product lenses. -/
def displayedExt {P Q : LensPresentation}
    (t : LensPresentation.GeneratorMap P Q) :
    (lensDecoder V v₀).obj P ⟶ (lensDecoder V v₀).obj Q :=
  { toFun := fun c => (c.1, ULift.up (t c.2.down))
    get_naturality := fun _ => rfl
    put_naturality := fun _ _ => rfl }

/-- Restriction after extension recovers every finite table entry. -/
@[simp]
theorem displayedRes_displayedExt {P Q : LensPresentation}
    (t : LensPresentation.GeneratorMap P Q) :
    displayedRes (displayedExt (V := V) (v₀ := v₀) t) = t := by
  funext k
  rfl

/-- Extension after restriction recovers every state value of a decoded morphism. -/
@[simp]
theorem displayedExt_displayedRes {P Q : LensPresentation}
    (h : (lensDecoder V v₀).obj P ⟶ (lensDecoder V v₀).obj Q) :
    displayedExt (displayedRes h) = h := by
  apply Hom.ext
  funext c
  change V × ULift.{u} (Fin P.card) at c
  cases c with
  | mk v k =>
    have hput := (h.put_naturality (v₀, k) v).symm
    simpa only [displayedExt, displayedRes, lensDecoder, product, productData,
      ULift.up_down] using hput

/-- `res` and `ext` give the B0 bijection at every displayed pair of endpoints. -/
def displayedHomEquivGeneratorMap (P Q : LensPresentation) :
    ((lensDecoder V v₀).obj P ⟶ (lensDecoder V v₀).obj Q) ≃
      LensPresentation.GeneratorMap P Q where
  toFun := displayedRes
  invFun := displayedExt
  left_inv := displayedExt_displayedRes
  right_inv := displayedRes_displayedExt

/-- Decoder evaluation is extension of the generator-map evaluation `J`. -/
theorem lensDecoder_map_eq_displayedExt_evaluation
    {P Q : LensPresentation} (f : P ⟶ Q) :
    (lensDecoder V v₀).map f =
      displayedExt ((LensPresentation.evaluationEquiv P Q) f) := by
  apply Hom.ext
  funext c
  change V × ULift.{u} (Fin P.card) at c
  cases c
  rfl

/-- The finite lens decoder is faithful: equality is reflected entry by entry. -/
instance lensDecoder_faithful : (lensDecoder V v₀).Faithful where
  map_injective {P Q} f g h := by
    funext k
    have := congrArg (fun hom => displayedRes hom k) h
    simpa only [displayedRes, lensDecoder, product, productData, ULift.up_down] using this

/-- The finite lens decoder is full: restriction supplies the representing table. -/
instance lensDecoder_full : (lensDecoder V v₀).Full where
  map_surjective {P Q} h :=
    ⟨displayedRes h, by
      rw [lensDecoder_map_eq_displayedExt_evaluation]
      exact displayedExt_displayedRes h⟩

/-- A finite enumeration of the reference fiber of a semantic lens. -/
noncomputable def fiberEquivFin (L : LensRealization V v₀) :
    L.Fiber ≃ Fin (by letI := Fintype.ofFinite L.Fiber; exact Fintype.card L.Fiber) := by
  letI := Fintype.ofFinite L.Fiber
  exact Fintype.equivFin L.Fiber

/-- The presentation cardinal attached to an arbitrary semantic lens. -/
noncomputable def presentationOf (L : LensRealization V v₀) : LensPresentation where
  card := by
    letI := Fintype.ofFinite L.Fiber
    exact Fintype.card L.Fiber

/-- The decoded reference fiber is equivalent to the original reference fiber. -/
noncomputable def normalFormFiberEquiv (L : LensRealization V v₀) :
    ((lensDecoder V v₀).obj (presentationOf L)).Fiber ≃ L.Fiber :=
  ((productFiberEquiv V (ULift.{u} (Fin (presentationOf L).card)) v₀).trans
    Equiv.ulift).trans (fiberEquivFin L).symm

/-- Every semantic lens is isomorphic to the product lens decoded from its finite fiber. -/
noncomputable def normalFormIso (L : LensRealization V v₀) :
    (lensDecoder V v₀).obj (presentationOf L) ≅ L where
  hom := ext (normalFormFiberEquiv L)
  inv := ext (normalFormFiberEquiv L).symm
  hom_inv_id := by
    apply (homEquivFiberMap _ _).injective
    change res (ext (normalFormFiberEquiv L) ≫ ext (normalFormFiberEquiv L).symm) =
      res (𝟙 _)
    rw [res_comp, res_ext, res_ext, res_id]
    funext c
    exact (normalFormFiberEquiv L).symm_apply_apply c
  inv_hom_id := by
    apply (homEquivFiberMap _ _).injective
    change res (ext (normalFormFiberEquiv L).symm ≫ ext (normalFormFiberEquiv L)) =
      res (𝟙 _)
    rw [res_comp, res_ext, res_ext, res_id]
    funext c
    exact (normalFormFiberEquiv L).apply_symm_apply c

/-- Essential surjectivity is constructed by finite enumeration and the lens laws. -/
noncomputable instance lensDecoder_essSurj : (lensDecoder V v₀).EssSurj :=
  Functor.EssSurj.mk fun L =>
    ⟨presentationOf L, ⟨normalFormIso L⟩⟩

/-- The decoder satisfies the categorical equivalence criterion. -/
noncomputable instance lensDecoder_isEquivalence : (lensDecoder V v₀).IsEquivalence where

/-- The finite presentation category reconstructs the independent semantic lens category. -/
noncomputable def lensPresentationEquivalence :
    LensPresentation ≌ LensRealization V v₀ :=
  (lensDecoder V v₀).asEquivalence

/-- Explicit retract generation using the finite presentation selected from the reference fiber. -/
theorem exists_decoder_retract (L : LensRealization V v₀) :
    ∃ (P : LensPresentation)
      (i : L ⟶ (lensDecoder V v₀).obj P)
      (r : (lensDecoder V v₀).obj P ⟶ L),
      i ≫ r = 𝟙 L := by
  exact ⟨presentationOf L, (normalFormIso L).inv, (normalFormIso L).hom,
    (normalFormIso L).inv_hom_id⟩

/-- The fixed-point carrier of an idempotent semantic lens morphism. -/
def fixedPointData (L : LensRealization V v₀) (e : L ⟶ L) : LensData V where
  Carrier := {c : L.Carrier // e c = c}
  get := fun c => L.get c
  put := fun c v =>
    ⟨L.put c v, by
      rw [e.put_naturality, c.property]⟩

/-- The fixed-point construction inherits the lens laws and finite reference fiber. -/
def fixedPointCondition (L : LensRealization V v₀) (e : L ⟶ L) :
    IsTotalLens v₀ (fixedPointData L e) where
  put_get c := by
    apply Subtype.ext
    exact L.condition.put_get c.1
  get_put c v := L.condition.get_put c.1 v
  put_put c v w := by
    apply Subtype.ext
    exact L.condition.put_put c.1 v w
  finite_fiber := by
    let embed : {c : (fixedPointData L e).Carrier //
        (fixedPointData L e).get c = v₀} → L.Fiber :=
      fun c => ⟨c.1.1, c.property⟩
    exact Finite.of_injective embed (by
      intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : L.Fiber => z.1) hab)

/-- The semantic lens carried by the fixed points of an idempotent. -/
def fixedPointLens (L : LensRealization V v₀) (e : L ⟶ L) : LensRealization V v₀ where
  toLensData := fixedPointData L e
  condition := fixedPointCondition L e

/-- Inclusion of the fixed-point lens into the original semantic lens. -/
def fixedPointInclusion (L : LensRealization V v₀) (e : L ⟶ L) :
    fixedPointLens L e ⟶ L where
  toFun := Subtype.val
  get_naturality _ := rfl
  put_naturality _ _ := rfl

/-- An idempotent retracts the original lens onto its fixed-point lens. -/
def fixedPointRetraction (L : LensRealization V v₀) (e : L ⟶ L)
    (he : e ≫ e = e) : L ⟶ fixedPointLens L e where
  toFun c :=
    ⟨e c, by
      have hfun := congrArg Hom.toFun he
      exact congrFun hfun c⟩
  get_naturality c := e.get_naturality c
  put_naturality c v := by
    apply Subtype.ext
    exact e.put_naturality c v

/-- The fixed-point inclusion followed by retraction is the identity. -/
theorem fixedPoint_split_id
    (L : LensRealization V v₀) (e : L ⟶ L) (he : e ≫ e = e) :
    fixedPointInclusion L e ≫ fixedPointRetraction L e he = 𝟙 _ := by
  apply Hom.ext
  funext c
  apply Subtype.ext
  exact c.property

/-- The fixed-point retraction followed by inclusion is the original idempotent. -/
theorem fixedPoint_split_e
    (L : LensRealization V v₀) (e : L ⟶ L) (he : e ≫ e = e) :
    fixedPointRetraction L e he ≫ fixedPointInclusion L e = e := by
  apply Hom.ext
  funext c
  rfl

/-- The semantic lens category is idempotent complete by the fixed-point construction. -/
instance lensRealization_isIdempotentComplete :
    IsIdempotentComplete (LensRealization V v₀) where
  idempotents_split L e he :=
    ⟨fixedPointLens L e, fixedPointInclusion L e, fixedPointRetraction L e he,
      fixedPoint_split_id L e he, fixedPoint_split_e L e he⟩

end LensRealization

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
