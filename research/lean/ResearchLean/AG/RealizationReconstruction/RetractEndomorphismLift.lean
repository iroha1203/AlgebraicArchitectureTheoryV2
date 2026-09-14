import ResearchLean.AG.RealizationReconstruction.KaroubiReconstruction
import Formal.Util.AssertStandardAxioms

/-!
# Endomorphism lifting through a decoded retract

This module isolates the categorical transfer needed to connect the finite
reference obstruction to G-123(B).  If `X` is exhibited as a retract of one
decoded presentation object and the decoder is full, every endomorphism of
`X` is obtained by decoding an endomorphism of that same presentation object.

Fullness and retract generation remain distinct hypotheses.  The theorem does
not construct the G-123 presentation or semantic category, prove either
hypothesis for the fixed input family, or place the mandatory-C source-choice
endomorphisms in the future semantic hom-set.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe uP uR vP vR

variable {P : Type uP} {R : Type uR}
  [Category.{vP} P] [Category.{vR} R]

/-- G-123(B) transfer API for one displayed retract: decode a presentation
endomorphism and restrict it along the supplied retraction.  The functor and
retract arrows are explicit inputs; fullness is not stored in this map. -/
def retractEndomorphismMap (F : P ⥤ R) {X : R} {p : P}
    (i : X ⟶ F.obj p) (r : F.obj p ⟶ X) : (p ⟶ p) → (X ⟶ X) :=
  fun f => i ≫ F.map f ≫ r

/-- G-123(B) local transfer theorem: decoder fullness makes
`retractEndomorphismMap` surjective whenever the displayed arrows satisfy the
retract equation.  Fullness is the B-property-1 premise, and `i ≫ r = 𝟙 X` is
the concrete B-property-4 witness; both are used to lift and simplify an
arbitrary semantic endomorphism. -/
theorem retractEndomorphismMap_surjective_of_full (F : P ⥤ R)
    (hfull : F.Full) {X : R} {p : P}
    (i : X ⟶ F.obj p) (r : F.obj p ⟶ X) (hir : i ≫ r = 𝟙 X) :
    Function.Surjective (retractEndomorphismMap F i r) := by
  letI : F.Full := hfull
  intro h
  obtain ⟨f, hf⟩ := F.map_surjective (r ≫ h ≫ i)
  refine ⟨f, ?_⟩
  simp only [retractEndomorphismMap, hf, Category.assoc]
  rw [← Category.assoc i r, hir, Category.id_comp]
  simp only [Category.comp_id]

/-- G-123(B) global transfer theorem: separately supplied fullness and
`RetractGeneratedBy F` construct, for every semantic object, one presentation
object and explicit retract arrows whose endomorphism decoder is surjective.
This consumes the two B premises but does not claim they follow from the fixed
AAT input; that discharge remains application-side work. -/
theorem exists_retractEndomorphismMap_surjective
    (F : P ⥤ R) (hfull : F.Full) (hgen : RetractGeneratedBy F) (X : R) :
    ∃ (p : P) (i : X ⟶ F.obj p) (r : F.obj p ⟶ X),
      i ≫ r = 𝟙 X ∧ Function.Surjective (retractEndomorphismMap F i r) := by
  obtain ⟨p, i, r, hir⟩ := hgen X
  exact ⟨p, i, r, hir, retractEndomorphismMap_surjective_of_full F hfull i r hir⟩

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
