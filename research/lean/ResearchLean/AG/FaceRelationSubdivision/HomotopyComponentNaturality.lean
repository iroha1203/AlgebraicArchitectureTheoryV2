import ResearchLean.AG.FaceRelationSubdivision.ThreeHomotopy

/-!
# 実三成分射と標準補正の全整数次数自然性

## Implementation notes

二つの実線形補正の自然性を標準Homotopyの1→0、2→1へ渡し、
他の全整数次数は同じ零成分で検査する。非標準homotopy型で代替しない。
-/
noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AAT.AG.FaceRelationSubdivision
open TwoPhase AtlasDefectComposition
universe u
variable {CA CB DA DB : ThreeCochainComplex.{0,u} ℚ}

/-- 二実補正が可換なら標準Homotopyの全成分も同じ実射と可換。 -/
theorem homotopyComponent_natural
    (f : ThreeCochainComplex.Hom CB CA) (g : ThreeCochainComplex.Hom DB DA)
    (h0A : CA.C1 →ₗ[ℚ] DA.C0) (h1A : CA.C2 →ₗ[ℚ] DA.C1)
    (h0B : CB.C1 →ₗ[ℚ] DB.C0) (h1B : CB.C2 →ₗ[ℚ] DB.C1)
    (hn0 : g.f0.comp h0B = h0A.comp f.f1) (hn1 : g.f1.comp h1B = h1A.comp f.f2)
    (i j : ℤ) : homotopyComponent h0B h1B i j ≫ (zeroExtensionMap g).f j =
      (zeroExtensionMap f).f i ≫ homotopyComponent h0A h1A i j := by
  by_cases hi1 : i = 1
  · by_cases hj0 : j = 0
    · subst i; subst j
      rw [homotopyComponent_10, homotopyComponent_10]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
        zeroExtensionMap_f0_apply, zeroExtensionMap_f1_apply] using LinearMap.congr_fun hn0 x
    · have h10 : ¬ (i = 1 ∧ j = 0) := fun h => hj0 h.2
      have h21 : ¬ (i = 2 ∧ j = 1) := by omega
      rw [homotopyComponent_zero_of_ne _ _ _ _ h10 h21, homotopyComponent_zero_of_ne _ _ _ _ h10 h21]
      simp only [zero_comp, comp_zero]
  · by_cases hi2 : i = 2
    · by_cases hj1 : j = 1
      · subst i; subst j
        rw [homotopyComponent_21, homotopyComponent_21]
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
          zeroExtensionMap_f1_apply, zeroExtensionMap_f2_apply] using LinearMap.congr_fun hn1 x
      · have h10 : ¬ (i = 1 ∧ j = 0) := by omega
        have h21 : ¬ (i = 2 ∧ j = 1) := fun h => hj1 h.2
        rw [homotopyComponent_zero_of_ne _ _ _ _ h10 h21, homotopyComponent_zero_of_ne _ _ _ _ h10 h21]
        simp only [zero_comp, comp_zero]
    · have h10 : ¬ (i = 1 ∧ j = 0) := fun h => hi1 h.1
      have h21 : ¬ (i = 2 ∧ j = 1) := fun h => hi2 h.1
      rw [homotopyComponent_zero_of_ne _ _ _ _ h10 h21, homotopyComponent_zero_of_ne _ _ _ _ h10 h21]
      simp only [zero_comp, comp_zero]

end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
