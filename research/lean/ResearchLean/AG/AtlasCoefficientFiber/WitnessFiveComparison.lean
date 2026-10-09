import ResearchLean.AG.AtlasCoefficientFiber.WitnessFiveInput
import ResearchLean.AG.AtlasCoefficientFiber.WitnessThreeComparison
import ResearchLean.AG.AtlasCoefficientFiber.WitnessOneEvaluation

/-!
# G-135 W5：原e/hの全H¹商と実比較

## Implementation notes

細側cycleのk値は原m微分で零に強制される。e/h periodの核と実d0像を両包含で
同定して全商を構成する。次元一致だけでH¹射を恒等と呼ぶ方法は採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessFive
open CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision AtlasDefectComposition
open WitnessCommon WitnessFullSupport

/-- 粗loopの原d0は同端点差から零。 -/
theorem coarse_d0_zero : (namedComplex Nc).d0 = 0 := by
  apply LinearMap.ext; intro z; funext e
  rw [namedComplex_d0_apply]; exact sub_self _
/-- 原粗面なしによるd1零。 -/
theorem coarse_d1_zero : (namedComplex Nc).d1 = 0 := by
  apply LinearMap.ext; intro z; funext f; exact Empty.elim f
/-- 細loopの同端点差から原d0零。 -/
theorem fine_d0_zero : (namedComplex Nf).d0 = 0 := by
  apply LinearMap.ext; intro z; funext e
  rw [namedComplex_d0_apply]; exact sub_self _
/-- 原m=(k,e,e)の微分はk値そのもの。 -/
theorem fine_d1_apply (z : Fin 3 → ℚ) (f : Unit) : (namedComplex Nf).d1 z f = z 2 := by
  rw [namedComplex_d1_apply]
  change z 2 - z 0 + z 0 = z 2
  ring
/-- 同細cycle条件はk値零と必要十分。 -/
theorem fine_cycle_iff (z : Fin 3 → ℚ) : z ∈ LinearMap.ker (namedComplex Nf).d1 ↔ z 2 = 0 := by
  constructor
  · intro hz
    have h := congrFun hz ()
    simpa only [fine_d1_apply,Pi.zero_apply] using h
  · intro hz
    rw [LinearMap.mem_ker]
    funext f
    change (namedComplex Nf).d1 z f = (0 : ℚ)
    exact (fine_d1_apply z f).trans hz
/-- 指定kだけ1の原cochainは閉でない。 -/
theorem k_only_not_cycle : ![0,0,(1:ℚ)] ∉ LinearMap.ker (namedComplex Nf).d1 := by
  rw [fine_cycle_iff]
  exact one_ne_zero
/-- 原粗H¹全商のe/h両逆座標。 -/
def coarseNamedCoordinates : (namedComplex Nc).H1 ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  zeroDifferentialH1Equiv _ coarse_d0_zero coarse_d1_zero
/-- 同細閉cochainの原e/h period。 -/
def finePeriod : LinearMap.ker (namedComplex Nf).d1 →ₗ[ℚ] (Fin 2 → ℚ) where
  toFun z i := z.1 (Fin.castLE (by decide) i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- e/h period核は同じ原d0像の全range。 -/
theorem finePeriod_kernel : LinearMap.ker finePeriod = LinearMap.range (namedComplex Nf).boundaryToCycles := by
  ext z
  constructor
  · intro hz
    have he : z.1 0 = 0 := congrFun hz 0
    have hh : z.1 1 = 0 := congrFun hz 1
    have hk : z.1 2 = 0 := (fine_cycle_iff z.1).mp z.2
    refine ⟨0,?_⟩
    apply Subtype.ext
    rw [map_zero]
    funext e
    change (0 : ℚ) = z.1 e
    fin_cases e
    · exact he.symm
    · exact hh.symm
    · exact hk.symm
  · rintro ⟨z,rfl⟩
    funext i
    change (namedComplex Nf).d0 z (Fin.castLE (by decide) i) = 0
    rw [fine_d0_zero]; rfl
/-- 任意e/h値はk零の原閉cochainから生成する。 -/
theorem finePeriod_surjective : Function.Surjective finePeriod := by
  intro z
  refine ⟨⟨![z 0,z 1,0],(fine_cycle_iff _).mpr rfl⟩,?_⟩
  funext i; fin_cases i <;> rfl
/-- 同原細H¹全商をe/hへ全両逆で同定。 -/
def fineNamedCoordinates : (namedComplex Nf).H1 ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  WitnessThree.periodQuotientEquiv _ finePeriod finePeriod_kernel finePeriod_surjective
/-- 全商同型は同じ閉代表のe/h値を読む。 -/
@[simp] theorem fineNamedCoordinates_mk (z : LinearMap.ker (namedComplex Nf).d1) :
    fineNamedCoordinates ((LinearMap.range (namedComplex Nf).boundaryToCycles).mkQ z) = finePeriod z :=
  WitnessThree.periodQuotientEquiv_mk _ finePeriod finePeriod_kernel finePeriod_surjective z
/-- 原named比較は全元でe/hを恒等に送る。 -/
theorem named_map (x : (namedComplex Nc).H1) :
    fineNamedCoordinates ((incidenceNamedHom M).h1Map x) = coarseNamedCoordinates x := by
  obtain ⟨z,rfl⟩ := (LinearMap.range (namedComplex Nc).boundaryToCycles).mkQ_surjective x
  rw [ThreeCochainComplex.Hom.h1Map_mk,fineNamedCoordinates_mk]
  funext i; fin_cases i <;> rfl
/-- 同原粗subset全H¹のe/h座標。 -/
def coarseCoordinates (A : Set Bool) (hA : A.Nonempty) :
    (Nc.targetSubsetComplex A).H1 ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).h1Equiv.trans coarseNamedCoordinates
/-- 同原細subset全H¹のe/h座標。 -/
def fineCoordinates (A : Set Bool) (hA : A.Nonempty) :
    (Nf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).H1 ≃ₗ[ℚ] (Fin 2 → ℚ) :=
  (fullSubsetNamedEquiv Nf (fun _ => rfl) _ (fine_nonempty A hA)).h1Equiv.trans fineNamedCoordinates
/-- 独立原uの全三次数named比較との可換square。 -/
theorem subset_square (A : Set Bool) (hA : A.Nonempty) :
    cochainComp (M.aSubnerveComparisonHom A)
      (fullSubsetNamedEquiv Nf (fun _ => rfl) _ (fine_nonempty A hA)).toHom =
    cochainComp (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).toHom (incidenceNamedHom M) :=
  fullSubsetNamed_square M (fun _ => rfl) (fun _ => rfl) A _ hA
    (fine_nonempty A hA) (fun _ ht => ht)
/-- 同実uのH¹射は全e/h値で恒等。 -/
theorem subset_map (A : Set Bool) (hA : A.Nonempty) (x : (Nc.targetSubsetComplex A).H1) :
    fineCoordinates A hA ((M.aSubnerveComparisonHom A).h1Map x) = coarseCoordinates A hA x := by
  have hn := fun z => congrArg (fun f => f.f1 z) (subset_square A hA)
  have hh := ThreeCochainComplex.CochainEquiv.h1Equiv_naturality_apply
    (fullSubsetNamedEquiv Nc (fun _ => rfl) A hA)
    (fullSubsetNamedEquiv Nf (fun _ => rfl) _ (fine_nonempty A hA))
    (M.aSubnerveComparisonHom A) (incidenceNamedHom M) hn x
  exact (congrArg fineNamedCoordinates hh).trans (named_map _)
/-- 非空全Aの同実H¹比較は単射かつ全射。 -/
theorem comparison_bijective (A : Set Bool) (hA : A.Nonempty) :
    Function.Bijective (M.aSubnerveComparisonHom A).h1Map := by
  constructor
  · intro x y h
    apply (coarseCoordinates A hA).injective
    exact (subset_map A hA x).symm.trans ((congrArg (fineCoordinates A hA) h).trans (subset_map A hA y))
  · intro y
    refine ⟨(coarseCoordinates A hA).symm (fineCoordinates A hA y),?_⟩
    apply (fineCoordinates A hA).injective
    rw [subset_map,LinearEquiv.apply_symm_apply]
/-- 空Aも同じ原商からH¹比較の両逆を生成。 -/
theorem empty_comparison_bijective : Function.Bijective (M.aSubnerveComparisonHom ∅).h1Map := by
  letI := WitnessOne.empty_H1_subsingleton qc Nc
  letI : Subsingleton (Nf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' ∅)).H1 := by
    simpa only [Set.preimage_empty] using WitnessOne.empty_H1_subsingleton qf Nf
  exact ⟨fun _ _ _ => Subsingleton.elim _ _,fun y => ⟨0,Subsingleton.elim _ _⟩⟩
/-- 同原比較は空Aを含む全Aで可逆。 -/
theorem allA_comparison_bijective (A : Set Bool) : Function.Bijective (M.aSubnerveComparisonHom A).h1Map := by
  by_cases hA : A.Nonempty
  · exact comparison_bijective A hA
  · have ha : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    subst A; exact empty_comparison_bijective
/-- 全Aの同実診断は零。 -/
theorem defect (A : Set Bool) : blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0) :=
  (blockDefect_eq_zero_iff_bijective _).mpr (allA_comparison_bijective A)

/-- 原粗subset座標の公開評価は同原named商へ移した値。 -/
theorem coarseCoordinates_apply (A : Set Bool) (hA : A.Nonempty) (x : (Nc.targetSubsetComplex A).H1) :
    coarseCoordinates A hA x = coarseNamedCoordinates ((fullSubsetNamedEquiv Nc (fun _ => rfl) A hA).h1Equiv x) := rfl
/-- 原細subset座標の公開評価は同原named商へ移した値。 -/
theorem fineCoordinates_apply (A : Set Bool) (hA : A.Nonempty)
    (x : (Nf.targetSubsetComplex (comparisonFactor qc qf coarser ⁻¹' A)).H1) :
    fineCoordinates A hA x = fineNamedCoordinates ((fullSubsetNamedEquiv Nf (fun _ => rfl) _ (fine_nonempty A hA)).h1Equiv x) := rfl

end AAT.AG.AtlasCoefficientFiber.WitnessFive
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.coarse_d0_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.coarse_d1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.fine_d0_zero
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.fine_d1_apply
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.fine_cycle_iff
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.k_only_not_cycle
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.coarseNamedCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.finePeriod
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.finePeriod_kernel
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.finePeriod_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.fineNamedCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.fineNamedCoordinates_mk
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.named_map
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.coarseCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.fineCoordinates
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.subset_square
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.subset_map
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.comparison_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.empty_comparison_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.allA_comparison_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.defect
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.coarseCoordinates_apply
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFive.fineCoordinates_apply
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessFive
