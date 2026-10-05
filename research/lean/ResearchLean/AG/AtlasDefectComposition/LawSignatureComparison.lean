import ResearchLean.AG.AtlasDefectComposition.SelectedFamilyCanonicalComparison
import ResearchLean.AG.AtlasDefectComposition.LawSignatureRestoration
import Formal.Util.AssertStandardAxioms
/-! # 実全 Law 比較から多重度付き署名の全比較へ

Implementation notes: D の全次数 Law 同型と同じ粗 fiber・逆像の自然性を用いる。
元の発生ラベルを残し、両側で同じ canonical 再添字を適用する。
-/
noncomputable section
open CategoryTheory CochainComplex
namespace AAT.AG.AtlasDefectComposition
open CanonicalResolution ResolutionInvariance TwoPhase SelectedFamilies
universe u
variable {Source : Type u} [Fintype Source] {q r : Reading Source} {h : q.CoarserThan r}
variable (N : TargetSupportedNerve.{u,u} q) (E : TargetSupportedNerve.{u,u} r)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate q) (hr : laws.Adequate r)
/-- 全 Law coarse 複体を元の粗 fiber の selected 族へ送る同型。 -/
def lawSelectedCoarseIso : zeroExtension (N.lawGeneratedComplex laws ha) ≅
    SelectedFamilyComplex.coarse N E h (lawSelectedFamily (h:=h) N E laws ha) :=
  lawZeroExtensionIso N laws ha ≪≫ FiniteComplexFamily.iso _ _ (lawBlockFiberZeroExtensionIso N laws ha)
/-- 全 Law fine 複体を同じ粗 fiber の canonical 逆像族へ送る同型。 -/
def lawSelectedFineIso : zeroExtension (E.lawGeneratedComplex laws hr) ≅
    SelectedFamilyComplex.fine N E h (lawSelectedFamily (h:=h) N E laws ha) :=
  lawZeroExtensionIso E laws hr ≪≫ FiniteComplexFamily.iso _ _ (fun l =>
    lawBlockSelectedSubsetZeroExtensionIso E laws hr l _ (labelValueFiber_eq_preimage laws q r ha hr h l))
variable (M : TargetSupportedNerveMorphism q r h N E)
/-- 全 Law 同型は同じ粗 fiber と逆像の実比較を保持する。 -/
theorem lawSelected_square : zeroExtensionMap (M.generatedComparisonHom laws ha hr) ≫ (lawSelectedFineIso N E laws ha hr).hom =
    (lawSelectedCoarseIso N E laws ha).hom ≫ SelectedFamilyComplex.comparison N E h (lawSelectedFamily (h:=h) N E laws ha) M := by
  dsimp only [lawSelectedFineIso,lawSelectedCoarseIso,Iso.trans_hom]
  rw [← Category.assoc,lawZeroExtensionIso_natural,Category.assoc]
  have hh : FiniteComplexFamily.map _ _ (fun l => zeroExtensionMap (M.generatedBlockComparisonHom laws ha hr l)) ≫
      (FiniteComplexFamily.iso _ _ (fun l => lawBlockSelectedSubsetZeroExtensionIso E laws hr l _
        (labelValueFiber_eq_preimage laws q r ha hr h l))).hom =
    (FiniteComplexFamily.iso _ _ (lawBlockFiberZeroExtensionIso N laws ha)).hom ≫
      SelectedFamilyComplex.comparison N E h (lawSelectedFamily (h:=h) N E laws ha) M := by
    change FiniteComplexFamily.map _ _ _ ≫ FiniteComplexFamily.map _ _ _ = FiniteComplexFamily.map _ _ _ ≫ FiniteComplexFamily.map _ _ _
    rw [← FiniteComplexFamily.map_comp,← FiniteComplexFamily.map_comp]
    congr 1
    funext l
    exact lawBlockSelectedSubsetZeroExtensionIso_natural N E laws ha M hr l _ _ rfl
      (labelValueFiber_eq_preimage laws q r ha hr h l) (fun _ ht => ht)
  simpa only [Category.assoc] using congrArg (fun f => (lawZeroExtensionIso N laws ha).hom ≫ f) hh
/-- 実全 Law coarse 複体の重複度付き canonical 族への指定同型。 -/
def lawMultiplicityCoarseIso := lawSelectedCoarseIso (h:=h) N E laws ha ≪≫
  SelectedFamilyComplex.canonicalCoarseIso N E h (lawSelectedFamily (h:=h) N E laws ha)
/-- 同じ多重度と添字全単射を使う実全 Law fine 複体の指定同型。 -/
def lawMultiplicityFineIso := lawSelectedFineIso N E laws ha hr ≪≫
  SelectedFamilyComplex.canonicalFineIso N E h (lawSelectedFamily (h:=h) N E laws ha)
/-- 全実 Law の生成比較は重複度付き全署名から指定同型の下で復元する。 -/
theorem lawMultiplicity_square : zeroExtensionMap (M.generatedComparisonHom laws ha hr) ≫ (lawMultiplicityFineIso N E laws ha hr).hom =
    (lawMultiplicityCoarseIso N E laws ha).hom ≫ SelectedFamilyComplex.comparison N E h
      (canonicalFamily (SupportSignature.family N E h) (multiplicity (SupportSignature.family N E h) (lawSelectedFamily (h:=h) N E laws ha))) M := by
  dsimp only [lawMultiplicityFineIso,lawMultiplicityCoarseIso,Iso.trans_hom]
  rw [← Category.assoc,lawSelected_square N E laws ha hr M,Category.assoc,SelectedFamilyComplex.canonical_square]
  simp only [Category.assoc]
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
