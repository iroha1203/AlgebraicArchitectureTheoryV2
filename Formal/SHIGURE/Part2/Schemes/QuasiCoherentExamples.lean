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

/-- The structure sheaf on the spectrum of the integers is quasi-coherent. -/
theorem structureAlgebra_quasiCoherent : IsQuasiCoherentSheafAlgebra structureAlgebra := by
  apply isQuasiCoherentModule_of_tilde
  refine ⟨ModuleCat.of base base, ⟨?_⟩⟩
  exact tildeSelf (R := base)

/-- The affine-site construction uses the same actual structure sheaf. -/
def structureAlgebra_reconstructed :
    (QuasiCoherentAlgebra.ofSheaf structureAlgebra structureAlgebra_quasiCoherent).algebraSheaf ≅
      structureAlgebra :=
  QuasiCoherentAlgebra.ofSheaf_algebraSheafIso structureAlgebra structureAlgebra_quasiCoherent

/-- The skyscraper algebra with value ℚ at the prime (2) cannot have a
tilde presentation on any affine open cover. -/
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

end

end SHIGURE.SchemeDescent.QuasiCoherentExamples
