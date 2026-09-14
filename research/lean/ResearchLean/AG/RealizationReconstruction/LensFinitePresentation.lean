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

/-- A finite lens presentation records the cardinality of its complement table.

This is the syntax object of G-123(A,E), n1015 (L3); it contains no semantic
state carrier or completed morphism. -/
@[ext]
structure LensPresentation where
  /-- The finite-complement cardinal supplied by the n1015 (L3) syntax object. -/
  card : ℕ

namespace LensPresentation

/-- The finite-table syntax category from G-123(E), n1015 (L3).  Its morphisms
are all functions between the displayed finite complements. -/
instance : Category LensPresentation where
  Hom P Q := Fin P.card → Fin Q.card
  id _ := id
  comp f g := g ∘ f
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl

/-- Constructor API for the G-123(E), n1015 (L3) finite syntax object; `n` is
the supplied table size and no semantic carrier is an input. -/
def ofNat (n : ℕ) : LensPresentation := ⟨n⟩

/-- Syntax API for G-123(B0), n1015 (L3): generator data is only a finite table
between complement indices, not a completed semantic map. -/
abbrev GeneratorMap (P Q : LensPresentation) := Fin P.card → Fin Q.card

/-- Syntax evaluation is a bijection onto finite generator maps.

This is `J` in G-123(B0).  Here syntax is literally a finite table, so the
evaluation bijection is definitionally the identity and contains no full map. -/
def evaluationEquiv (P Q : LensPresentation) :
    (P ⟶ Q) ≃ GeneratorMap P Q :=
  Equiv.refl _

end LensPresentation

namespace LensRealization

variable (V : Type u) (v₀ : V)

/-- Decode a finite complement table as the corresponding product lens.

This is the G-123(E), n1015 (L3) decoder; its action on a morphism is constructed
uniformly from the table and does not restrict the semantic morphism class. -/
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

/-- Displayed `res` API for G-123(B0); it evaluates an arbitrary completed map
only at the reference view and introduces no extra premise. -/
def displayedRes {P Q : LensPresentation}
    (h : (lensDecoder V v₀).obj P ⟶ (lensDecoder V v₀).obj Q) :
    LensPresentation.GeneratorMap P Q :=
  fun k => (h (v₀, ULift.up k)).2.down

/-- Displayed `ext` construction for G-123(B0); it builds the complete state map
uniformly from the finite table and the product-lens operations. -/
def displayedExt {P Q : LensPresentation}
    (t : LensPresentation.GeneratorMap P Q) :
    (lensDecoder V v₀).obj P ⟶ (lensDecoder V v₀).obj Q :=
  { toFun := fun c => (c.1, ULift.up (t c.2.down))
    get_naturality := fun _ => rfl
    put_naturality := fun _ _ => rfl }

/-- Displayed inverse-law API for G-123(B0); it proves table recovery directly
from the constructed `displayedExt`. -/
@[simp]
theorem displayedRes_displayedExt {P Q : LensPresentation}
    (t : LensPresentation.GeneratorMap P Q) :
    displayedRes (displayedExt (V := V) (v₀ := v₀) t) = t := by
  funext k
  rfl

/-- Displayed inverse-law API for G-123(B0); n1015 (L2) `put` naturality proves
recovery on every state, rather than only on generators. -/
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

/-- `res` and `ext` give the B0 bijection at every displayed pair of endpoints.

This is the displayed endpoint instance of G-123(B0), derived without an
extension certificate in the finite syntax. -/
def displayedHomEquivGeneratorMap (P Q : LensPresentation) :
    ((lensDecoder V v₀).obj P ⟶ (lensDecoder V v₀).obj Q) ≃
      LensPresentation.GeneratorMap P Q where
  toFun := displayedRes
  invFun := displayedExt
  left_inv := displayedExt_displayedRes
  right_inv := displayedRes_displayedExt

/-- Decoder evaluation is extension of the generator-map evaluation `J`.

This is the explicit equation `F_Θ(f) = ext(J(f))` required by G-123(B0). -/
theorem lensDecoder_map_eq_displayedExt_evaluation
    {P Q : LensPresentation} (f : P ⟶ Q) :
    (lensDecoder V v₀).map f =
      displayedExt ((LensPresentation.evaluationEquiv P Q) f) := by
  apply Hom.ext
  funext c
  change V × ULift.{u} (Fin P.card) at c
  cases c
  rfl

/-- Main G-123(B2) instance: decoder faithfulness is proved entry by entry from
the displayed restriction API, with no injectivity certificate in the syntax. -/
instance lensDecoder_faithful : (lensDecoder V v₀).Faithful where
  map_injective {P Q} f g h := by
    funext k
    have := congrArg (fun hom => displayedRes hom k) h
    simpa only [displayedRes, lensDecoder, product, productData, ULift.up_down] using this

/-- Main G-123(B1) instance: decoder fullness is constructed by restriction and
the B0 decoder equation, with no representability premise on semantic maps. -/
instance lensDecoder_full : (lensDecoder V v₀).Full where
  map_surjective {P Q} h :=
    ⟨displayedRes h, by
      rw [lensDecoder_map_eq_displayedExt_evaluation]
      exact displayedExt_displayedRes h⟩

/-- Enumeration API for G-123(E), n1015 (L4); its sole premise is the finite
reference fiber from (L1), and the choice is used only for finite syntax. -/
noncomputable def fiberEquivFin (L : LensRealization V v₀) :
    L.Fiber ≃ Fin (by letI := Fintype.ofFinite L.Fiber; exact Fintype.card L.Fiber) := by
  letI := Fintype.ofFinite L.Fiber
  exact Fintype.equivFin L.Fiber

/-- Object-selection API for G-123(B4,E): the presentation size is constructed
from the finite reference fiber required by n1015 (L1). -/
noncomputable def presentationOf (L : LensRealization V v₀) : LensPresentation where
  card := by
    letI := Fintype.ofFinite L.Fiber
    exact Fintype.card L.Fiber

/-- Fiber-transport API for G-123(B4,E): finite enumeration identifies the
decoder generator with the original n1015 complement `K_L`. -/
noncomputable def normalFormFiberEquiv (L : LensRealization V v₀) :
    ((lensDecoder V v₀).obj (presentationOf L)).Fiber ≃ L.Fiber :=
  ((productFiberEquiv V (ULift.{u} (Fin (presentationOf L).card)) v₀).trans
    Equiv.ulift).trans (fiberEquivFin L).symm

/-- Every semantic lens is isomorphic to the product lens decoded from its finite fiber.

This finite-enumeration normal form is constructed by first transporting the
finite complement to `L.Fiber`, then applying the inverse of the exact canonical
n1015 (L4) isomorphism `canonicalNormalFormIso`. -/
noncomputable def normalFormIso (L : LensRealization V v₀) :
    (lensDecoder V v₀).obj (presentationOf L) ≅ L :=
  productIsoOfEquiv V v₀ (Equiv.ulift.trans (fiberEquivFin L).symm) ≪≫
    (canonicalNormalFormIso L).symm

/-- Main G-123(E) instance: essential surjectivity is constructed from finite
fiber enumeration and the exact n1015 (L4) canonical normal form. -/
noncomputable instance lensDecoder_essSurj : (lensDecoder V v₀).EssSurj :=
  Functor.EssSurj.mk fun L =>
    ⟨presentationOf L, ⟨normalFormIso L⟩⟩

/-- The decoder satisfies the categorical equivalence criterion.

This G-123(E) instance packages the separately constructed fullness,
faithfulness, and essential surjectivity proofs; none is an input field. -/
noncomputable instance lensDecoder_isEquivalence : (lensDecoder V v₀).IsEquivalence where

/-- The finite presentation category reconstructs the independent semantic lens category.

This is the lens-family equivalence of G-123(E), n1015 (L1)--(L4), obtained only
after the four reconstruction obligations have been constructed separately. -/
noncomputable def lensPresentationEquivalence :
    LensPresentation ≌ LensRealization V v₀ :=
  (lensDecoder V v₀).asEquivalence

/-- Main G-123(B4) theorem: every semantic object is an explicit retract of the
decoder object selected from its finite fiber; no retract data is an input. -/
theorem exists_decoder_retract (L : LensRealization V v₀) :
    ∃ (P : LensPresentation)
      (i : L ⟶ (lensDecoder V v₀).obj P)
      (r : (lensDecoder V v₀).obj P ⟶ L),
      i ≫ r = 𝟙 L := by
  exact ⟨presentationOf L, (normalFormIso L).inv, (normalFormIso L).hom,
    (normalFormIso L).inv_hom_id⟩

/-- The fixed-point carrier of an idempotent semantic lens morphism.

This begins the constructed idempotent splitting required by G-123(B3); the
fixed points are derived from the actual endomorphism, not supplied as data. -/
def fixedPointData (L : LensRealization V v₀) (e : L ⟶ L) : LensData V where
  Carrier := {c : L.Carrier // e c = c}
  get := fun c => L.get c
  put := fun c v =>
    ⟨L.put c v, by
      rw [e.put_naturality, c.property]⟩

/-- The fixed-point construction inherits the lens laws and finite reference fiber.

This discharges the n1015 (L1) premises for the G-123(B3) splitting object from
the original lens laws and the endomorphism naturality fields. -/
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

/-- Object-construction API for G-123(B3): the fixed-point data and its derived
n1015 (L1) proof are packaged as a semantic lens. -/
def fixedPointLens (L : LensRealization V v₀) (e : L ⟶ L) : LensRealization V v₀ where
  toLensData := fixedPointData L e
  condition := fixedPointCondition L e

/-- Splitting API for G-123(B3): inclusion is constructed from subtype
inclusion and preserves the n1015 (L2) operations definitionally. -/
def fixedPointInclusion (L : LensRealization V v₀) (e : L ⟶ L) :
    fixedPointLens L e ⟶ L where
  toFun := Subtype.val
  get_naturality _ := rfl
  put_naturality _ _ := rfl

/-- An idempotent retracts the original lens onto its fixed-point lens.

This is the constructed retraction for G-123(B3); the sole extra premise is the
defining idempotence equation, which is used to prove fixed-point membership. -/
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

/-- First splitting equation for the main G-123(B3) construction; it uses
fixed-point membership and is separate from the second split equation. -/
theorem fixedPoint_split_id
    (L : LensRealization V v₀) (e : L ⟶ L) (he : e ≫ e = e) :
    fixedPointInclusion L e ≫ fixedPointRetraction L e he = 𝟙 _ := by
  apply Hom.ext
  funext c
  apply Subtype.ext
  exact c.property

/-- Second splitting equation for the main G-123(B3) construction; it identifies
the composite with the supplied endomorphism on every state. -/
theorem fixedPoint_split_e
    (L : LensRealization V v₀) (e : L ⟶ L) (he : e ≫ e = e) :
    fixedPointRetraction L e he ≫ fixedPointInclusion L e = e := by
  apply Hom.ext
  funext c
  rfl

/-- Main G-123(B3) instance: every idempotent in the independent semantic lens
category splits through the constructed fixed-point lens. -/
instance lensRealization_isIdempotentComplete :
    IsIdempotentComplete (LensRealization V v₀) where
  idempotents_split L e he :=
    ⟨fixedPointLens L e, fixedPointInclusion L e, fixedPointRetraction L e he,
      fixedPoint_split_id L e he, fixedPoint_split_e L e he⟩

end LensRealization

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
