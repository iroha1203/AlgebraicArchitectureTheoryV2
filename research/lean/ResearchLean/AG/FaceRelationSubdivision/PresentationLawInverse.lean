import ResearchLean.AG.FaceRelationSubdivision.FiniteHomComposition
import ResearchLean.AG.FaceRelationSubdivision.PresentationInverse
import ResearchLean.AG.FaceRelationSubdivision.LawPresentation

/-!
# 同じreadingの原始表示逆と実Law逆射

## Implementation notes

全セル名の原始全単射から両比較を生成し、合成を全三成分で恒等へ同定する。
Law同型の逆射を保存結論から選ばず、同じ原始逆表示との等号を証明する。
-/
noncomputable section
open CategoryTheory
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u
variable {Source : Type u} {q : Reading Source} {N M : TargetSupportedNerve.{u,u} q}
namespace CellPresentationEquiv
variable (E : CellPresentationEquiv q q (Reading.coarserThan_refl q) N M)

/-- 原始順表示と逆表示の合成は全セル計算成分で恒等。 -/
theorem comparison_comp_symmSelf : IncidenceSupportedComparison.comp E.comparison
    E.symmSelf.comparison = IncidenceSupportedComparison.identity q N := by
  apply IncidenceSupportedComparison.ext
  · funext v
    simp only [IncidenceSupportedComparison.comp_chartMap, comparison_chart, symmSelf_chart,
      Equiv.apply_symm_apply, IncidenceSupportedComparison.identity_chartMap]
  · funext a
    simp only [IncidenceSupportedComparison.comp_edgeMap, comparison_edge, Option.bind_some,
      symmSelf_edge, Equiv.apply_symm_apply, IncidenceSupportedComparison.identity_edgeMap]
  · funext F
    simp only [IncidenceSupportedComparison.comp_faceMap, comparison_face, Option.bind_some,
      symmSelf_face, Equiv.apply_symm_apply, IncidenceSupportedComparison.identity_faceMap]

/-- 原始逆表示と順表示の合成も全セル成分で恒等。 -/
theorem symmSelf_comparison_comp : IncidenceSupportedComparison.comp E.symmSelf.comparison
    E.comparison = IncidenceSupportedComparison.identity q M := by
  apply IncidenceSupportedComparison.ext
  · funext v
    simp only [IncidenceSupportedComparison.comp_chartMap, comparison_chart, symmSelf_chart,
      Equiv.symm_apply_apply, IncidenceSupportedComparison.identity_chartMap]
  · funext a
    simp only [IncidenceSupportedComparison.comp_edgeMap, comparison_edge, Option.bind_some,
      symmSelf_edge, Equiv.symm_apply_apply, IncidenceSupportedComparison.identity_edgeMap]
  · funext F
    simp only [IncidenceSupportedComparison.comp_faceMap, comparison_face, Option.bind_some,
      symmSelf_face, Equiv.symm_apply_apply, IncidenceSupportedComparison.identity_faceMap]

/-- 同じ原始逆表示から生成した実Law Homは標準表示同型の逆そのもの。 -/
theorem lawZeroExtensionIso_inv [Fintype Source] (laws : FiniteLawFamily Source) (ha : laws.Adequate q) :
    (E.lawZeroExtensionIso laws ha).inv =
      zeroExtensionMap (E.symmSelf.comparison.generatedComparisonHom laws ha ha) := by
  apply (cancel_mono (E.lawZeroExtensionIso laws ha).hom).mp
  rw [Iso.inv_hom_id, lawZeroExtensionIso_hom, ← zeroExtensionMap_comp,
    ← generatedComparisonHom_comp, symmSelf_comparison_comp,
    identity_generatedComparisonHom, zeroExtensionMap_id]

end CellPresentationEquiv

variable {O : TargetSupportedNerve.{u,u} q}
variable (E : CellPresentationEquiv q q (Reading.coarserThan_refl q) N M)
variable (s0 : SupportedBasisMap O.chartSupport M.chartSupport)
variable (s1 : SupportedBasisMap O.edgeSupport M.edgeSupport)
variable (s2 : SupportedBasisMap O.faceSupport M.faceSupport)
variable (hs0 : (TargetSupportedNerve.rawD1 M).raw.comp s1.raw = s0.raw.comp (TargetSupportedNerve.rawD1 O).raw)
variable (hs1 : (TargetSupportedNerve.rawD2 M).raw.comp s2.raw = s1.raw.comp (TargetSupportedNerve.rawD2 O).raw)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q)

/-- sectionの原始有限和を表示の原始基底表と直接合成してLaw射を生成する。 -/
def presentationLawSection [Fintype Source] :=
  lawFiniteHom (s0.comp E.comparison.basis0) (s1.comp E.comparison.basis1)
    (s2.comp E.comparison.basis2)
    (finiteComp_comm01 _ _ _ _ E.comparison.basis_comm01 hs0)
    (finiteComp_comm12 _ _ _ _ E.comparison.basis_comm12 hs1) laws ha

/-- 表示sectionの原始有限和からの直接構成式。 -/
@[simp] theorem presentationLawSection_eq_finite [Fintype Source] :
    presentationLawSection E s0 s1 s2 hs0 hs1 laws ha =
      lawFiniteHom (s0.comp E.comparison.basis0) (s1.comp E.comparison.basis1)
        (s2.comp E.comparison.basis2)
        (finiteComp_comm01 _ _ _ _ E.comparison.basis_comm01 hs0)
        (finiteComp_comm12 _ _ _ _ E.comparison.basis_comm12 hs1) laws ha := rfl

/- presentationLawSectionの同じ作業単位に属する原始有限和評価API。 -/
/-- 表示されたsectionの次数0有限和。 -/
@[simp] theorem presentationLawSection_f0 [Fintype Source] :
    (presentationLawSection E s0 s1 s2 hs0 hs1 laws ha).f0 =
      (s0.comp E.comparison.basis0).lawDual laws ha := rfl
/-- 表示されたsectionの次数1有限和。 -/
@[simp] theorem presentationLawSection_f1 [Fintype Source] :
    (presentationLawSection E s0 s1 s2 hs0 hs1 laws ha).f1 =
      (s1.comp E.comparison.basis1).lawDual laws ha := rfl
/-- 表示されたsectionの次数2有限和。 -/
@[simp] theorem presentationLawSection_f2 [Fintype Source] :
    (presentationLawSection E s0 s1 s2 hs0 hs1 laws ha).f2 =
      (s2.comp E.comparison.basis2).lawDual laws ha := rfl

/-- 直接生成したsection Law射は同じ表示射とsection射の合成。 -/
theorem presentationLawSection_eq [Fintype Source] :
    presentationLawSection E s0 s1 s2 hs0 hs1 laws ha =
      cochainComp (E.comparison.generatedComparisonHom laws ha ha)
        (lawFiniteHom s0 s1 s2 hs0 hs1 laws ha) := by
  rw [← E.comparison.basisLawHom_eq_generated laws ha
    E.comparison.basis_comm01 E.comparison.basis_comm12]
  apply cochain_ext
  · apply LinearMap.ext; intro z
    rw [presentationLawSection_f0, cochainComp_f0, lawFiniteHom_f0, lawFiniteHom_f0,
      SupportedBasisMap.lawDual_comp]
    rfl
  · apply LinearMap.ext; intro z
    rw [presentationLawSection_f1, cochainComp_f1, lawFiniteHom_f1, lawFiniteHom_f1,
      SupportedBasisMap.lawDual_comp]
    rfl
  · apply LinearMap.ext; intro z
    rw [presentationLawSection_f2, cochainComp_f2, lawFiniteHom_f2, lawFiniteHom_f2,
      SupportedBasisMap.lawDual_comp]
    rfl

end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
