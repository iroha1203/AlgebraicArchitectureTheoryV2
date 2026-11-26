import Formal.SHIGURE.Part2.Schemes.AffineAlgebraPresentations
import Formal.SHIGURE.Part2.Schemes.QuasiCoherentComparison
import Formal.SHIGURE.Part2.Schemes.QuasiCoherentSheafAlgebras
import Formal.SHIGURE.Part2.Schemes.RelativeSpecExamples

/-! # Quasi-coherent and non-quasi-coherent sheaf examples -/

namespace SHIGURE.SchemeDescent.QuasiCoherentExamples

open AlgebraicGeometry CategoryTheory

noncomputable section

private abbrev base := CommRingCat.of ℤ
private abbrev X := Spec base

private abbrev structureAlgebra : Under X.sheaf := Under.mk (𝟙 X.sheaf)

/-- The structure sheaf on the spectrum of the integers is quasi-coherent.
This is a positive example of the affine cover criterion in the opening of Appendix B.
It uses the structure module on the integer spectrum. -/
theorem structureAlgebra_quasiCoherent : IsQuasiCoherentSheafAlgebra structureAlgebra := by
  apply isQuasiCoherentModule_of_tilde
  refine ⟨ModuleCat.of base base, ⟨?_⟩⟩
  exact tildeSelf (R := base)

/-- The affine-site construction uses the same actual structure sheaf.
This illustrates the algebra reconstruction comparison used in Lemma B.7.
The proof uses quasi-coherence of the structure algebra on the integer spectrum. -/
def structureAlgebra_reconstructed :
    (QuasiCoherentAlgebra.ofSheaf structureAlgebra structureAlgebra_quasiCoherent).algebraSheaf ≅
      structureAlgebra :=
  QuasiCoherentAlgebra.ofSheaf_algebraSheafIso structureAlgebra structureAlgebra_quasiCoherent

/-- The skyscraper algebra with value ℚ at the prime (2) cannot have a
tilde presentation on any affine open cover.
This is a negative example of the affine cover criterion in the opening of Appendix B.
The computed restriction to the principal open at 2 gives the obstruction. -/
theorem skyscraper_not_affineCover :
    ¬ HasAffineTildeCover (algebraUnderlyingModule RelativeSpecExamples.skyscraperAlgebraAtTwo) := by
  intro localCover
  have qc : IsQuasiCoherentSheafAlgebra RelativeSpecExamples.skyscraperAlgebraAtTwo :=
    (isQuasiCoherentSheafAlgebra_iff_affineCover _).2 localCover
  exact RelativeSpecExamples.skyscraperAlgebraAtTwo_not_localization
    (sheafAlgebra_localizes _ qc (isAffineOpen_top X) (2 : Γ(X, ⊤)))

example : (algebraUnderlyingModule structureAlgebra).IsQuasicoherent :=
  (isQuasiCoherentModule_iff_mathlib _).mp structureAlgebra_quasiCoherent

example : ¬ (algebraUnderlyingModule RelativeSpecExamples.skyscraperAlgebraAtTwo).IsQuasicoherent :=
  fun qc => skyscraper_not_affineCover
    ((isQuasiCoherentModule_iff_affineCover _).mp ((isQuasiCoherentModule_iff_mathlib _).mpr qc))

private abbrev skyscraperModule :=
  algebraUnderlyingModule RelativeSpecExamples.skyscraperAlgebraAtTwo

example : IsQuasiCoherentModule (algebraUnderlyingModule structureAlgebra) :=
  structureAlgebra_quasiCoherent

example : ¬ IsQuasiCoherentModule skyscraperModule :=
  fun coherent => skyscraper_not_affineCover
    ((isQuasiCoherentModule_iff_affineCover skyscraperModule).mp coherent)

example : HasAffineTildeCover (algebraUnderlyingModule structureAlgebra) :=
  (isQuasiCoherentSheafAlgebra_iff_affineCover _).mp structureAlgebra_quasiCoherent

example : ¬ IsQuasiCoherentSheafAlgebra RelativeSpecExamples.skyscraperAlgebraAtTwo :=
  fun coherent => skyscraper_not_affineCover ((isQuasiCoherentSheafAlgebra_iff_affineCover _).mp coherent)

example : PrincipalLocalizations (algebraUnderlyingModule structureAlgebra) :=
  (principalLocalizations_iff_tilde _).2 ⟨ModuleCat.of base base, ⟨tildeSelf (R := base)⟩⟩

example : ¬ PrincipalLocalizations skyscraperModule := by
  intro localizes
  apply skyscraper_not_affineCover
  exact (isQuasiCoherentModule_iff_affineCover _).mp
    (isQuasiCoherentModule_of_tilde _ ((principalLocalizations_iff_tilde _).mp localizes))

example : HasTildeOn (algebraUnderlyingModule structureAlgebra) (isAffineOpen_top X) :=
  structureAlgebra_quasiCoherent ⟨⊤, isAffineOpen_top X⟩

example : ¬ HasTildeOn skyscraperModule (isAffineOpen_top X) := by
  intro localTilde
  apply skyscraper_not_affineCover
  exact ⟨Unit, fun _ => ⟨⊤, isAffineOpen_top X⟩, by simp, fun _ => localTilde⟩

example : HasAffineAlgebraTildeCover structureAlgebra :=
  (isQuasiCoherentSheafAlgebra_iff_affineAlgebraTildeCover _).mp structureAlgebra_quasiCoherent

example : ¬ HasAffineAlgebraTildeCover RelativeSpecExamples.skyscraperAlgebraAtTwo := by
  intro localTilde
  apply skyscraper_not_affineCover
  exact (isQuasiCoherentSheafAlgebra_iff_affineCover _).mp
    ((isQuasiCoherentSheafAlgebra_iff_affineAlgebraTildeCover _).mpr localTilde)

example : HasAlgebraTildeOn structureAlgebra (isAffineOpen_top X) :=
  (isQuasiCoherentSheafAlgebra_iff_eachAlgebraPresentation _).mp
    structureAlgebra_quasiCoherent ⟨⊤, isAffineOpen_top X⟩

example : ¬ HasAlgebraTildeOn RelativeSpecExamples.skyscraperAlgebraAtTwo (isAffineOpen_top X) := by
  intro localTilde
  apply skyscraper_not_affineCover
  have cover : HasAffineAlgebraTildeCover RelativeSpecExamples.skyscraperAlgebraAtTwo :=
    ⟨Unit, fun _ => ⟨⊤, isAffineOpen_top X⟩, by simp, fun _ => localTilde⟩
  exact (isQuasiCoherentSheafAlgebra_iff_affineCover _).mp
    ((isQuasiCoherentSheafAlgebra_iff_affineAlgebraTildeCover _).mpr cover)

end

end SHIGURE.SchemeDescent.QuasiCoherentExamples
