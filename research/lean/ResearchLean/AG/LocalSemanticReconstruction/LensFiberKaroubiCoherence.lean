import ResearchLean.AG.LocalSemanticReconstruction.LensFiberModelEquivalence
import ResearchLean.AG.RealizationReconstruction.CSKaroubiReconstruction
import Formal.Util.AssertStandardAxioms

/-!
# Lens finite-fiber and Karoubi coherence

The accepted finite lens decoder is read in the independent finite-fiber local
category constructed in Cycle 25.  Its object and morphism APIs expose the
original finite complement and generator table through the canonical product
fiber equivalence.

The accepted Karoubi reconstruction, its restriction isomorphism, explicit
retract generation, and its Arrow equivalence are then transported to the same
local category.  Arbitrary finite-fiber maps are retained; no decoder
membership, retract certificate, or completed realization is stored in a local
object.  This module does not assert effectiveness or the final four-family
local reconstruction.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory
open CategoryTheory.Idempotents
open AAT.AG.RealizationReconstruction

universe u

/-- Decode a finite lens presentation and read its actual finite reference
fiber in the independent local-model category. -/
noncomputable def lensFiberFiniteDecoder (input : LensFamilyInput.{u}) :
    LensPresentation ⥤ FintypeCat.{u} :=
  LensRealization.lensDecoder input.View input.reference ⋙
    lensSemanticFiberReading input

/-- The local object decoded from a presentation is canonically its displayed
finite complement.  The isomorphism is the actual product-fiber equivalence. -/
noncomputable def lensFiberFiniteDecoderObjectIso
    (input : LensFamilyInput.{u}) (P : LensPresentation) :
    (lensFiberFiniteDecoder input).obj P ≅
      finiteLocalValue (ULift.{u} (Fin P.card)) :=
  FintypeCat.equivEquivIso
    (LensRealization.productFiberEquiv input.View
      (ULift.{u} (Fin P.card)) input.reference)

/-- The object comparison reads a product-fiber state as its actual finite
complement coordinate. -/
@[simp] theorem lensFiberFiniteDecoderObjectIso_hom_apply
    (input : LensFamilyInput.{u}) (P : LensPresentation)
    (state : ((LensRealization.lensDecoder input.View input.reference).obj P).Fiber) :
    (lensFiberFiniteDecoderObjectIso input P).hom state = state.1.2 :=
  rfl

/-- Under the canonical object comparisons, a decoded local morphism is
exactly the original finite generator table. -/
@[simp] theorem lensFiberFiniteDecoder_map_under_object_iso
    (input : LensFamilyInput.{u}) {P Q : LensPresentation}
    (f : P ⟶ Q)
    (state : ((LensRealization.lensDecoder input.View input.reference).obj P).Fiber) :
    (lensFiberFiniteDecoderObjectIso input Q).hom
        ((lensFiberFiniteDecoder input).map f state) =
      ULift.up
        (f ((lensFiberFiniteDecoderObjectIso input P).hom state).down) :=
  rfl

/-- The accepted lens Karoubi reconstruction transported to the independent
finite-fiber local category. -/
noncomputable def lensKaroubiFiberEquivalence
    (input : LensFamilyInput.{u}) :
    Karoubi LensPresentation ≌ FintypeCat.{u} :=
  LensRealization.lensKaroubiReconstructionEquivalence.trans
    (lensSemanticFiberEquivalence input)

/-- Restricting the transported Karoubi reconstruction to finite
presentations recovers the finite-fiber decoder. -/
noncomputable def lensKaroubiFiberRestrictionIso
    (input : LensFamilyInput.{u}) :
    toKaroubi LensPresentation ⋙
        (lensKaroubiFiberEquivalence input).functor ≅
      lensFiberFiniteDecoder input :=
  (Functor.associator
      (toKaroubi LensPresentation)
      LensRealization.lensKaroubiReconstructionEquivalence.functor
      (lensSemanticFiberEquivalence input).functor).symm.trans
    (Functor.isoWhiskerRight
      LensRealization.lensKaroubiReconstructionRestrictionIso
      (lensSemanticFiberEquivalence input).functor)

/-- Every finite-fiber local model is a retract of the local reading of a
decoded finite presentation.  The witness is transported from the accepted
semantic retract through the explicit Cycle 25 product-lens assembler and
readback isomorphism. -/
theorem lensFiberFiniteDecoder_retractGeneratedBy
    (input : LensFamilyInput.{u}) :
    RetractGeneratedBy (lensFiberFiniteDecoder input) := by
  intro Z
  let X := lensFiberModelRealization input Z
  rcases LensRealization.lensRetractGeneratedBy X with
    ⟨P, insertion, retraction, retract⟩
  let localIso := lensFiberModelRealizationIso input Z
  let F := (lensSemanticFiberEquivalence input).functor
  have mappedRetract :
      F.map insertion ≫ F.map retraction =
        𝟙 ((lensSemanticFiberReading input).obj X) := by
    simpa only [F.map_comp, F.map_id] using congrArg F.map retract
  refine ⟨P,
    localIso.inv ≫ F.map insertion,
    F.map retraction ≫ localIso.hom, ?_⟩
  calc
    localIso.inv ≫ F.map insertion ≫ F.map retraction ≫ localIso.hom =
        localIso.inv ≫ (F.map insertion ≫ F.map retraction) ≫
          localIso.hom := by simp only [Category.assoc]
    _ = 𝟙 Z := by
      rw [mappedRetract]
      simpa only [Category.comp_id] using localIso.inv_hom_id

/-- Arrow-level Karoubi reconstruction transported to finite-fiber local
models.  It retains arbitrary local maps, not only isomorphisms. -/
noncomputable def lensKaroubiFiberArrowEquivalence
    (input : LensFamilyInput.{u}) :
    Karoubi (Arrow LensPresentation) ≌ Arrow FintypeCat.{u} :=
  LensRealization.lensKaroubiArrowReconstructionEquivalence.trans
    (Functor.mapArrowEquivalence (lensSemanticFiberEquivalence input))

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction

end AAT.AG.LocalSemanticReconstruction
