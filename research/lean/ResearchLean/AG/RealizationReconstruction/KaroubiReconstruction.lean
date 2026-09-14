import Mathlib.CategoryTheory.Idempotents.FunctorExtension
import Formal.Util.AssertStandardAxioms

/-!
# Karoubi reconstruction from finite presentation data

This module proves the categorical reconstruction principle required by
G-123(B1).  For a decoder `F : P ⥤ R`, the four hypotheses remain distinct:
fullness, faithfulness, idempotent completeness of the independently defined
semantic category `R`, and generation of every semantic object as a retract of
a decoded object.  The proof constructs the induced functor on Karoubi
completions, proves its three equivalence properties, and only then removes the
Karoubi completion on `R` using its separately supplied splitting theorem.

No presentation or semantic object is redefined as an image of the decoder.
The final section also records the extension isomorphism and the unique,
coherent comparison between any two extensions with the same restriction.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory
open CategoryTheory.Idempotents

universe uP uR vP vR

variable {P : Type uP} {R : Type uR}
  [Category.{vP} P] [Category.{vR} R]

/-- G-123(B4): every independently defined semantic object is a retract of a
decoded presentation object.  This is a proposition to be proved for each
fixed input family, not a field of the syntax or semantic category. -/
def RetractGeneratedBy (F : P ⥤ R) : Prop :=
  ∀ X : R, ∃ (p : P) (i : X ⟶ F.obj p) (r : F.obj p ⟶ X), i ≫ r = 𝟙 X

/-- The functor induced by a decoder on Karoubi completions. -/
noncomputable def karoubiMap (F : P ⥤ R) : Karoubi P ⥤ Karoubi R :=
  (functorExtension₂ P R).obj F

/-- Computation of the induced Karoubi functor on the underlying morphism. -/
@[simp]
theorem karoubiMap_map_f (F : P ⥤ R) {X Y : Karoubi P} (f : X ⟶ Y) :
    ((karoubiMap F).map f).f = F.map f.f := rfl

/-- G-123(B3): faithfulness of the decoder implies faithfulness after Karoubi
completion.  The proof reflects equality of the underlying semantic arrows. -/
noncomputable def karoubiMapFaithful (F : P ⥤ R) (hfaithful : F.Faithful) :
    (karoubiMap F).Faithful := by
  letI : F.Faithful := hfaithful
  exact
    { map_injective := fun {X Y} f g h ↦ by
        apply Karoubi.Hom.ext
        apply F.map_injective
        exact congrArg Karoubi.Hom.f h }

/-- G-123(B2): fullness and faithfulness of the decoder construct every
Karoubi morphism from its underlying semantic arrow. -/
noncomputable def karoubiMapFull (F : P ⥤ R) (hfull : F.Full)
    (hfaithful : F.Faithful) : (karoubiMap F).Full := by
  letI : F.Full := hfull
  letI : F.Faithful := hfaithful
  exact
    { map_surjective := fun {X Y} h ↦ by
        let f : X.X ⟶ Y.X := F.preimage h.f
        have hf : F.map f = h.f := F.map_preimage h.f
        have comm : X.p ≫ f ≫ Y.p = f := by
          apply F.map_injective
          simpa only [F.map_comp, hf] using h.comm
        refine ⟨⟨f, comm⟩, ?_⟩
        apply Karoubi.Hom.ext
        exact hf }

/-- Lift a retract of a decoded object to an object of `Karoubi P` by taking
the preimage of the induced idempotent. -/
noncomputable def karoubiObjectOfRetract (F : P ⥤ R) (hfull : F.Full)
    (hfaithful : F.Faithful) (Y : Karoubi R) (p : P)
    (i : Y.X ⟶ F.obj p) (r : F.obj p ⟶ Y.X) (hir : i ≫ r = 𝟙 Y.X) :
    Karoubi P := by
  letI : F.Full := hfull
  letI : F.Faithful := hfaithful
  exact
    { X := p
      p := F.preimage (r ≫ Y.p ≫ i)
      idem := by
        apply F.map_injective
        rw [F.map_comp, F.map_preimage]
        simp only [Category.assoc]
        rw [← Category.assoc i r, hir, Category.id_comp]
        simp only [← Category.assoc, Y.idem] }

/-- The lifted retract object decodes to the original Karoubi object. -/
noncomputable def karoubiObjectOfRetractIso (F : P ⥤ R) (hfull : F.Full)
    (hfaithful : F.Faithful) (Y : Karoubi R) (p : P)
    (i : Y.X ⟶ F.obj p) (r : F.obj p ⟶ Y.X) (hir : i ≫ r = 𝟙 Y.X) :
    (karoubiMap F).obj (karoubiObjectOfRetract F hfull hfaithful Y p i r hir) ≅ Y := by
  letI : F.Full := hfull
  letI : F.Faithful := hfaithful
  exact
    { hom :=
        { f := r ≫ Y.p
          comm := by
            change F.map (F.preimage (r ≫ Y.p ≫ i)) ≫ (r ≫ Y.p) ≫ Y.p = r ≫ Y.p
            rw [F.map_preimage]
            simp only [Category.assoc]
            rw [← Category.assoc i r, hir, Category.id_comp, Y.idem, Y.idem] }
      inv :=
        { f := Y.p ≫ i
          comm := by
            change Y.p ≫ (Y.p ≫ i) ≫ F.map (F.preimage (r ≫ Y.p ≫ i)) = Y.p ≫ i
            rw [F.map_preimage]
            simp only [Category.assoc]
            rw [← Category.assoc i r, hir, Category.id_comp]
            simp only [← Category.assoc, Y.idem] }
      hom_inv_id := by
        apply Karoubi.Hom.ext
        change (r ≫ Y.p) ≫ Y.p ≫ i = F.map (F.preimage (r ≫ Y.p ≫ i))
        rw [F.map_preimage]
        simp
      inv_hom_id := by
        apply Karoubi.Hom.ext
        change (Y.p ≫ i) ≫ r ≫ Y.p = Y.p
        simp only [Category.assoc]
        rw [← Category.assoc i r, hir, Category.id_comp, Y.idem] }

/-- G-123(B4): retract generation supplies essential surjectivity of the
induced functor on Karoubi completions. -/
noncomputable def karoubiMapEssSurj (F : P ⥤ R) (hfull : F.Full)
    (hfaithful : F.Faithful) (hgen : RetractGeneratedBy F) :
    (karoubiMap F).EssSurj := by
  exact Functor.EssSurj.mk fun Y ↦ by
    rcases hgen Y.X with ⟨p, i, r, hir⟩
    exact ⟨karoubiObjectOfRetract F hfull hfaithful Y p i r hir,
      ⟨karoubiObjectOfRetractIso F hfull hfaithful Y p i r hir⟩⟩

/-- Fullness, faithfulness, and retract generation reconstruct the Karoubi
completion of the independent semantic category. -/
noncomputable def karoubiCompletionEquivalence (F : P ⥤ R)
    (hfull : F.Full) (hfaithful : F.Faithful) (hgen : RetractGeneratedBy F) :
    Karoubi P ≌ Karoubi R := by
  letI : (karoubiMap F).Full := karoubiMapFull F hfull hfaithful
  letI : (karoubiMap F).Faithful := karoubiMapFaithful F hfaithful
  letI : (karoubiMap F).EssSurj := karoubiMapEssSurj F hfull hfaithful hgen
  letI : (karoubiMap F).IsEquivalence := {}
  exact (karoubiMap F).asEquivalence

/-- G-123(B1): the four separately supplied and application-side discharged
properties reconstruct the independent semantic category itself. -/
noncomputable def karoubiReconstructionEquivalence (F : P ⥤ R)
    (hfull : F.Full) (hfaithful : F.Faithful)
    (hcomplete : IsIdempotentComplete R) (hgen : RetractGeneratedBy F) :
    Karoubi P ≌ R := by
  letI : IsIdempotentComplete R := hcomplete
  exact (karoubiCompletionEquivalence F hfull hfaithful hgen).trans
    (toKaroubiEquivalence R).symm

/-- The reconstruction functor is Mathlib's explicit extension of `F` across
the Karoubi completion; this exposes the constructed functor, not only the
existence of an equivalence. -/
theorem karoubiReconstructionEquivalence_functor (F : P ⥤ R)
    (hfull : F.Full) (hfaithful : F.Faithful)
    (hcomplete : IsIdempotentComplete R) (hgen : RetractGeneratedBy F) :
    (karoubiReconstructionEquivalence F hfull hfaithful hcomplete hgen).functor =
      (functorExtension P R).obj F := rfl

/-- G-123(B1) extension equation: restricting the reconstructed functor to
the original presentation category recovers the decoder up to canonical
natural isomorphism. -/
noncomputable def karoubiReconstructionRestrictionIso (F : P ⥤ R)
    (hfull : F.Full) (hfaithful : F.Faithful)
    (hcomplete : IsIdempotentComplete R) (hgen : RetractGeneratedBy F) :
    toKaroubi P ⋙ (karoubiReconstructionEquivalence F hfull hfaithful hcomplete hgen).functor ≅ F := by
  letI : IsIdempotentComplete R := hcomplete
  let T := toKaroubiEquivalence R
  let α : toKaroubi P ⋙ karoubiMap F ≅ F ⋙ toKaroubi R :=
    (functorExtension₂CompWhiskeringLeftToKaroubiIso P R).app F
  exact
    (Functor.associator (toKaroubi P) (karoubiMap F) T.inverse).symm |>.trans
      ((Functor.isoWhiskerRight α T.inverse).trans
        ((Functor.associator F T.functor T.inverse).trans
          ((Functor.isoWhiskerLeft F T.unitIso.symm).trans
            (Functor.rightUnitor F))))

/-- G-123(B1) uniqueness: two functors out of `Karoubi P` equipped with
isomorphic restrictions to the same decoder have a canonically constructed
comparison isomorphism. -/
noncomputable def karoubiExtensionComparison (F : P ⥤ R)
    (G H : Karoubi P ⥤ R) (eG : toKaroubi P ⋙ G ≅ F)
    (eH : toKaroubi P ⋙ H ≅ F) : G ≅ H :=
  whiskeringLeftObjToKaroubiFullyFaithful.preimageIso (eG.trans eH.symm)

/-- Restriction of the comparison's forward map is exactly the comparison
prescribed by the two extension witnesses. -/
@[simp]
theorem karoubiExtensionComparison_restrict_hom (F : P ⥤ R)
    (G H : Karoubi P ⥤ R) (eG : toKaroubi P ⋙ G ≅ F)
    (eH : toKaroubi P ⋙ H ≅ F) :
    ((Functor.whiskeringLeft P (Karoubi P) R).obj (toKaroubi P)).map
        (karoubiExtensionComparison F G H eG eH).hom = eG.hom ≫ eH.inv := by
  exact whiskeringLeftObjToKaroubiFullyFaithful.map_preimage _

/-- Restriction of the comparison's inverse is the reverse comparison. -/
@[simp]
theorem karoubiExtensionComparison_restrict_inv (F : P ⥤ R)
    (G H : Karoubi P ⥤ R) (eG : toKaroubi P ⋙ G ≅ F)
    (eH : toKaroubi P ⋙ H ≅ F) :
    ((Functor.whiskeringLeft P (Karoubi P) R).obj (toKaroubi P)).map
        (karoubiExtensionComparison F G H eG eH).inv = eH.hom ≫ eG.inv := by
  exact whiskeringLeftObjToKaroubiFullyFaithful.map_preimage _

/-- The restriction equation characterizes the canonical comparison uniquely;
there is no additional choice on retract objects hidden after restriction. -/
theorem karoubiExtensionComparison_unique (F : P ⥤ R)
    (G H : Karoubi P ⥤ R) (eG : toKaroubi P ⋙ G ≅ F)
    (eH : toKaroubi P ⋙ H ≅ F) (e : G ≅ H)
    (he : ((Functor.whiskeringLeft P (Karoubi P) R).obj (toKaroubi P)).map e.hom =
      eG.hom ≫ eH.inv) :
    e = karoubiExtensionComparison F G H eG eH := by
  apply Iso.ext
  apply whiskeringLeftObjToKaroubiFullyFaithful.map_injective
  rw [he, karoubiExtensionComparison_restrict_hom]

/-- The canonical comparison of an extension with itself is the identity. -/
theorem karoubiExtensionComparison_self (F : P ⥤ R) (G : Karoubi P ⥤ R)
    (eG : toKaroubi P ⋙ G ≅ F) :
    karoubiExtensionComparison F G G eG eG = Iso.refl G := by
  apply Iso.ext
  apply whiskeringLeftObjToKaroubiFullyFaithful.map_injective
  rw [karoubiExtensionComparison_restrict_hom]
  simp

/-- Canonical comparisons compose coherently through a third extension. -/
theorem karoubiExtensionComparison_trans (F : P ⥤ R)
    (G H K : Karoubi P ⥤ R) (eG : toKaroubi P ⋙ G ≅ F)
    (eH : toKaroubi P ⋙ H ≅ F) (eK : toKaroubi P ⋙ K ≅ F) :
    (karoubiExtensionComparison F G H eG eH).trans
        (karoubiExtensionComparison F H K eH eK) =
      karoubiExtensionComparison F G K eG eK := by
  apply Iso.ext
  apply whiskeringLeftObjToKaroubiFullyFaithful.map_injective
  change ((Functor.whiskeringLeft P (Karoubi P) R).obj (toKaroubi P)).map
      ((karoubiExtensionComparison F G H eG eH).hom ≫
        (karoubiExtensionComparison F H K eH eK).hom) = _
  rw [Functor.map_comp, karoubiExtensionComparison_restrict_hom,
    karoubiExtensionComparison_restrict_hom,
    karoubiExtensionComparison_restrict_hom]
  simp

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
