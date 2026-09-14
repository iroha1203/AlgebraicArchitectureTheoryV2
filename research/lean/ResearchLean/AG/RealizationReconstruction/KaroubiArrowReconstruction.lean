import ResearchLean.AG.RealizationComparisonIdempotents.KaroubiArrowEquivalence
import ResearchLean.AG.RealizationReconstruction.KaroubiReconstruction

/-!
# Arrow-level Karoubi reconstruction

G-123(B1) requires reconstruction to preserve change, not merely objects.  This
module transports the independently proved G-119 equivalence
`Kar(Arrow P) ≌ Arrow(Kar P)` through the G-123 reconstruction equivalence.
Thus every presentation arrow, including non-invertible arrows, remains an
object of the reconstructed arrow category.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory
open CategoryTheory.Idempotents

universe uP uR vP vR

variable {P : Type uP} {R : Type uR}
  [Category.{vP} P] [Category.{vR} R]

/-- G-123(B1): Karoubi reconstruction commutes with passage to the category of
arrows, using the same four hypotheses as object-level reconstruction. -/
noncomputable def karoubiArrowReconstructionEquivalence (F : P ⥤ R)
    (hfull : F.Full) (hfaithful : F.Faithful)
    (hcomplete : IsIdempotentComplete R) (hgen : RetractGeneratedBy F) :
    Karoubi (Arrow P) ≌ Arrow R :=
  (AAT.AG.RealizationComparisonIdempotents.karoubiArrowEquivalence (E := P)).trans
    (Functor.mapArrowEquivalence
      (karoubiReconstructionEquivalence F hfull hfaithful hcomplete hgen))

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
