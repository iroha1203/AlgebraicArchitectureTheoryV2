import ResearchLean.AG.FaceRelationSubdivision.WitnessOneCokernel
import ResearchLean.AG.FaceRelationSubdivision.FullSupportSubsetComparison
import ResearchLean.AG.AtlasDefectComposition.EmptySubset
import Formal.Util.AssertStandardAxioms
/-!
# W1 の全 subset と空 subset の同じ実比較

## Implementation notes

非空 A の一点を canonical 因子の全射性で持ち上げ、実 subset を全台表へ同定する。
空 A では選択セルが空であることから零複体の同型を作り、同じ生成比較と一致させる。
一ラベルの証明だけで全 A を代用する方式は採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision.WitnessOne
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
/-- 実 canonical 因子の A 逆像。 -/
def fineSubset (A : Set Bool) : Set Source := comparisonFactor qc qf coarser ⁻¹' A
/-- 非空 A の canonical 逆像も非空。 -/
theorem fineSubset_nonempty (A : Set Bool) (hA : A.Nonempty) : (fineSubset A).Nonempty := by
  obtain ⟨a,ha⟩ := hA
  obtain ⟨s,hs⟩ := comparisonFactor_surjective qc qf coarser a
  exact ⟨s,by change comparisonFactor qc qf coarser s ∈ A; rw [hs]; exact ha⟩
/-- 同じ原始 subset 比較の台写像条件。 -/
theorem subset_compatible (A : Set Bool) : ∀ t, t∈fineSubset A → comparisonFactor qc qf coarser t∈A := fun _ ht => ht
/-- rplus から独立に生成する全 A の実 subset 射。 -/
abbrev plusSubsetHom (A : Set Bool) := rPlus.targetSubsetComparisonHom A (fineSubset A) (subset_compatible A)
/-- rminus から独立に生成する全 A の実 subset 射。 -/
abbrev minusSubsetHom (A : Set Bool) := rMinus.targetSubsetComparisonHom A (fineSubset A) (subset_compatible A)
/-- j の同じ subset 台適合は reading 恒等因子から得る。 -/
theorem j_subset_compatible (A : Set Bool) : ∀ t, t∈fineSubset A →
    comparisonFactor qf qf (Reading.coarserThan_refl qf) t∈fineSubset A := by
  intro t ht
  rw [TriangleAddition.self_factor]
  exact ht
/-- 全 A でも同じ独立実 subset 射は uminus=jstar uplus。 -/
theorem subset_composition (A : Set Bool) : minusSubsetHom A=cochainComp (plusSubsetHom A)
    (j.targetSubsetComparisonHom (fineSubset A) (fineSubset A) (j_subset_compatible A)) :=
  AAT.AG.FaceRelationSubdivision.targetSubsetComparisonHom_comp rPlus j A (fineSubset A) (fineSubset A)
    (subset_compatible A) (j_subset_compatible A)
/-- 粗全非空 A を同じ名付き複体へ移す。 -/
def oldSubsetEquiv (A : Set Bool) (hA : A.Nonempty) := fullSubsetNamedEquiv N chart_full A hA
/-- plus 全非空逆像を同じ名付き複体へ移す。 -/
def plusSubsetEquiv (A : Set Bool) (hA : A.Nonempty) := fullSubsetNamedEquiv plus plus_chart_full (fineSubset A) (fineSubset_nonempty A hA)
/-- minus 全非空逆像を同じ名付き複体へ移す。 -/
def minusSubsetEquiv (A : Set Bool) (hA : A.Nonempty) := fullSubsetNamedEquiv minus minus_chart_full (fineSubset A) (fineSubset_nonempty A hA)
/-- 全非空 A の plus 独立実比較と名付き比較の全三成分正方形。 -/
theorem plus_subset_square (A : Set Bool) (hA : A.Nonempty) :
    cochainComp (plusSubsetHom A) (plusSubsetEquiv A hA).toHom = cochainComp (oldSubsetEquiv A hA).toHom plusNamedHom :=
  fullSubsetNamed_square rPlus chart_full plus_chart_full A (fineSubset A) hA (fineSubset_nonempty A hA) (subset_compatible A)
/-- 全非空 A の minus 独立実比較と名付き比較の全三成分正方形。 -/
theorem minus_subset_square (A : Set Bool) (hA : A.Nonempty) :
    cochainComp (minusSubsetHom A) (minusSubsetEquiv A hA).toHom = cochainComp (oldSubsetEquiv A hA).toHom minusNamedHom :=
  fullSubsetNamed_square rMinus chart_full minus_chart_full A (fineSubset A) hA (fineSubset_nonempty A hA) (subset_compatible A)
/-- 粗全非空 A の実 H¹ を k period へ移す。 -/
def oldSubsetPeriod (A : Set Bool) (hA : A.Nonempty) := (oldSubsetEquiv A hA).h1Equiv.trans oldH1Period
/-- plus 全非空 A の実 H¹ を k period へ移す。 -/
def plusSubsetPeriod (A : Set Bool) (hA : A.Nonempty) := (plusSubsetEquiv A hA).h1Equiv.trans plusH1Period
/-- minus 全非空 A の実 H¹ を二 period へ移す。 -/
def minusSubsetPeriod (A : Set Bool) (hA : A.Nonempty) := (minusSubsetEquiv A hA).h1Equiv.trans minusH1Period
/-- 元粗代表を同じ subset 同型の逆で移すと、元の period を読む。 -/
@[simp] theorem oldSubsetPeriod_mk (A : Set Bool) (hA : A.Nonempty) (z) :
    oldSubsetPeriod A hA ((oldSubsetEquiv A hA).h1Equiv.symm
      ((LinearMap.range (namedComplex N).boundaryToCycles).mkQ z)) = oldPeriod z := by
  dsimp only [oldSubsetPeriod, LinearEquiv.trans_apply]
  rw [LinearEquiv.apply_symm_apply, oldH1Period_mk]
/-- 元 minus 代表を同じ subset 同型の逆で移すと、元の二 period を読む。 -/
@[simp] theorem minusSubsetPeriod_mk (A : Set Bool) (hA : A.Nonempty) (z) :
    minusSubsetPeriod A hA ((minusSubsetEquiv A hA).h1Equiv.symm
      ((LinearMap.range (namedComplex minus).boundaryToCycles).mkQ z)) = minusPeriod z := by
  dsimp only [minusSubsetPeriod, LinearEquiv.trans_apply]
  rw [LinearEquiv.apply_symm_apply, minusH1Period_mk]
/-- 全非空 A の同じ実 plus 射は x→x。 -/
theorem plus_subset_identity (A : Set Bool) (hA : A.Nonempty) (x : (N.targetSubsetComplex A).H1) :
    plusSubsetPeriod A hA ((plusSubsetHom A).h1Map x)=oldSubsetPeriod A hA x := by
  have hn : ∀ z, (plusSubsetEquiv A hA).e1 ((plusSubsetHom A).f1 z)=plusNamedHom.f1 ((oldSubsetEquiv A hA).e1 z) := by
    intro z
    exact congrArg (fun f => f.f1 z) (plus_subset_square A hA)
  have hh := ThreeCochainComplex.CochainEquiv.h1Equiv_naturality_apply (oldSubsetEquiv A hA)
    (plusSubsetEquiv A hA) (plusSubsetHom A) plusNamedHom hn x
  exact (congrArg plusH1Period hh).trans (plus_named_identity _)
/-- 全非空 A の同じ実 minus 射は x→(x,0)。 -/
theorem minus_subset_injection (A : Set Bool) (hA : A.Nonempty) (x : (N.targetSubsetComplex A).H1) :
    minusSubsetPeriod A hA ((minusSubsetHom A).h1Map x)=(oldSubsetPeriod A hA x,0) := by
  have hn : ∀ z, (minusSubsetEquiv A hA).e1 ((minusSubsetHom A).f1 z)=minusNamedHom.f1 ((oldSubsetEquiv A hA).e1 z) := by
    intro z
    exact congrArg (fun f => f.f1 z) (minus_subset_square A hA)
  have hh := ThreeCochainComplex.CochainEquiv.h1Equiv_naturality_apply (oldSubsetEquiv A hA)
    (minusSubsetEquiv A hA) (minusSubsetHom A) minusNamedHom hn x
  exact (congrArg minusH1Period hh).trans (minus_named_injection _)
/-- 全非空 A の同じ実 minus 余核を追加 period で読む。 -/
def minusSubsetCokernel (A : Set Bool) (hA : A.Nonempty) :
    ((minus.targetSubsetComplex (fineSubset A)).H1 ⧸ LinearMap.range (minusSubsetHom A).h1Map) ≃ₗ[ℚ] ℚ :=
  (LinearConjugation.cokernelEquiv (minusSubsetHom A).h1Map periodInjection (oldSubsetPeriod A hA)
    (minusSubsetPeriod A hA) (minus_subset_injection A hA)).trans injectionCokernel
/-- 全非空 A の実 plus 比較は単射・全射。 -/
theorem plus_subset_bijective (A : Set Bool) (hA : A.Nonempty) : Function.Bijective (plusSubsetHom A).h1Map := by
  apply (LinearConjugation.bijective_iff (plusSubsetHom A).h1Map (LinearMap.id : ℚ →ₗ[ℚ] ℚ)
    (oldSubsetPeriod A hA) (plusSubsetPeriod A hA) (plus_subset_identity A hA)).mpr
  exact Function.bijective_id
/-- 全非空 A の実 minus 比較は単射。 -/
theorem minus_subset_injective (A : Set Bool) (hA : A.Nonempty) : Function.Injective (minusSubsetHom A).h1Map := by
  intro x y h
  apply (oldSubsetPeriod A hA).injective
  exact congrArg Prod.fst ((minus_subset_injection A hA x).symm.trans
    ((congrArg (minusSubsetPeriod A hA) h).trans (minus_subset_injection A hA y)))
/-- 空 A の canonical 逆像は空。 -/
@[simp] theorem fineSubset_empty : fineSubset ∅=∅ := rfl
/-- 空 subset の零複体同型を全三次数で構成する共通出力。 -/
def emptySubsetEquiv (E : TargetSupportedNerve qf) : ThreeCochainComplex.CochainEquiv
    (N.targetSubsetComplex ∅) (E.targetSubsetComplex ∅) := by
  letI : Subsingleton (N.targetSubsetComplex ∅).C0 := emptySubsetC0Subsingleton N
  letI : Subsingleton (N.targetSubsetComplex ∅).C1 := emptySubsetC1Subsingleton N
  letI : Subsingleton (N.targetSubsetComplex ∅).C2 := emptySubsetC2Subsingleton N
  letI : Subsingleton (E.targetSubsetComplex ∅).C0 := emptySubsetC0Subsingleton E
  letI : Subsingleton (E.targetSubsetComplex ∅).C1 := emptySubsetC1Subsingleton E
  letI : Subsingleton (E.targetSubsetComplex ∅).C2 := emptySubsetC2Subsingleton E
  exact {
    e0 := LinearEquiv.ofSubsingleton _ _
    e1 := LinearEquiv.ofSubsingleton _ _
    e2 := LinearEquiv.ofSubsingleton _ _
    comm0 _ := Subsingleton.elim _ _
    comm1 _ := Subsingleton.elim _ _ }

/-- 空 A の plus 実生成射は零複体の唯一の恒等同定と一致する。 -/
theorem plus_empty_identity : plusSubsetHom ∅=(emptySubsetEquiv plus).toHom := by
  letI : Subsingleton (plus.targetSubsetComplex (fineSubset ∅)).C0 := emptySubsetC0Subsingleton plus
  letI : Subsingleton (plus.targetSubsetComplex (fineSubset ∅)).C1 := emptySubsetC1Subsingleton plus
  letI : Subsingleton (plus.targetSubsetComplex (fineSubset ∅)).C2 := emptySubsetC2Subsingleton plus
  apply cochain_ext <;> apply LinearMap.ext <;> intro x <;> exact Subsingleton.elim _ _
/-- 空 A の minus 実生成射も零複体の唯一の恒等同定と一致する。 -/
theorem minus_empty_identity : minusSubsetHom ∅=(emptySubsetEquiv minus).toHom := by
  letI : Subsingleton (minus.targetSubsetComplex (fineSubset ∅)).C0 := emptySubsetC0Subsingleton minus
  letI : Subsingleton (minus.targetSubsetComplex (fineSubset ∅)).C1 := emptySubsetC1Subsingleton minus
  letI : Subsingleton (minus.targetSubsetComplex (fineSubset ∅)).C2 := emptySubsetC2Subsingleton minus
  apply cochain_ext <;> apply LinearMap.ext <;> intro x <;> exact Subsingleton.elim _ _
end AAT.AG.FaceRelationSubdivision.WitnessOne
#print axioms AAT.AG.FaceRelationSubdivision.WitnessOne.oldSubsetPeriod_mk
#print axioms AAT.AG.FaceRelationSubdivision.WitnessOne.minusSubsetPeriod_mk
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision.WitnessOne
