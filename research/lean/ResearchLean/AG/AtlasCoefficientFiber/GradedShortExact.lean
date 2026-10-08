import ResearchLean.AG.AtlasCoefficientFiber.FilteredComplexes

/-!
# G-135 B：原filtrationの実graded商と短完全列

## Implementation notes

F⁰/F¹を原carrier≤0鎖部分複体の双対へ同定する。
射は原辺・面への制限であり、商全射性は原包含の単射性から得る。
完全性やgradedの期待homologyを新しい入力にする案は採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 原垂直微分を双対化した同じgr⁰。 -/
abbrev firstGradedComplex : ThreeCochainComplex ℚ :=
  chainDualComplex (verticalEdgeBoundary M A) (verticalBoundary M A)
    (verticalEdgeBoundary_comp_verticalBoundary M A)

/-- 原chart/垂直辺制限は第一微分と可換。 -/
theorem verticalRestriction_comm0
    (z : (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).C0) :
    verticalRestriction1 M A ((Nf.targetSubsetComplex _).d0 z) =
      (verticalEdgeBoundary M A).dualMap (freeDualEquiv _ z) := by
  apply LinearMap.ext
  intro x
  rw [verticalRestriction1_apply, LinearMap.dualMap_apply, verticalEdgeBoundary_apply]
  exact (chainD1_dual Nf _ z (verticalEdgeInclusion M A x)).symm

/-- F⁰から原gr⁰への実評価射影。 -/
def firstGradedProjection : ThreeCochainComplex.Hom
    (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)) (firstGradedComplex M A) where
  f0 := (freeDualEquiv _).toLinearMap
  f1 := verticalRestriction1 M A
  f2 := verticalRestriction2 M A
  comm0 := verticalRestriction_comm0 M A
  comm1 := verticalRestriction_comm1 M A

/-- 射影0次は元chart自由chain双対同型。 -/
@[simp] theorem firstGradedProjection_f0 :
    (firstGradedProjection M A).f0 = (freeDualEquiv _).toLinearMap := rfl

/-- 射影1次は原垂直辺制限。 -/
@[simp] theorem firstGradedProjection_f1 : (firstGradedProjection M A).f1 = verticalRestriction1 M A := rfl

/-- 射影2次は原垂直面制限。 -/
@[simp] theorem firstGradedProjection_f2 : (firstGradedProjection M A).f2 = verticalRestriction2 M A := rfl

/-- 原辺包含の単射性が制限の全射性を生成する。 -/
theorem verticalRestriction1_surjective : Function.Surjective (verticalRestriction1 M A) :=
  (LinearMap.dualMap_surjective_of_injective (verticalEdgeInclusion_injective M A)).comp
    (freeDualEquiv _).surjective

/-- 原面包含の単射性が制限の全射性を生成する。 -/
theorem verticalRestriction2_surjective : Function.Surjective (verticalRestriction2 M A) :=
  (LinearMap.dualMap_surjective_of_injective (verticalFaceInclusion_injective M A)).comp
    (freeDualEquiv _).surjective

/-- F¹包含とgr⁰射影の標準零延長合成は零。 -/
theorem firstGraded_standard_zero :
    zeroExtensionMap (firstFiltrationInclusion M A) ≫ zeroExtensionMap (firstGradedProjection M A) = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  change degreeMap (firstFiltrationInclusion M A) n ≫ degreeMap (firstGradedProjection M A) n = 0
  by_cases h0 : n = 0
  · subst n
    apply ModuleCat.hom_ext
    exact LinearMap.ext fun x => map_zero _
  · by_cases h1 : n = 1
    · subst n
      apply ModuleCat.hom_ext
      exact LinearMap.ext fun x => x.2
    · by_cases h2 : n = 2
      · subst n
        apply ModuleCat.hom_ext
        exact LinearMap.ext fun x => x.2
      · rw [degreeMap_out (firstFiltrationInclusion M A) n h0 h1 h2]
        simp

/-- 原F¹→F⁰→gr⁰の同じ二射。 -/
def firstGradedShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℤ) :=
  ShortComplex.mk (zeroExtensionMap (firstFiltrationInclusion M A))
    (zeroExtensionMap (firstGradedProjection M A)) (firstGraded_standard_zero M A)

/-- 原F¹像が制限核に等しく全制限が全射なので、全整数次数で短完全。 -/
theorem firstGraded_degreewise_shortExact (n : ℤ) :
    ((firstGradedShortComplex M A).map
      (HomologicalComplex.eval (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) n)).ShortExact := by
  by_cases h0 : n = 0
  · subst n
    apply moduleShortExact_of_range_eq_ker
    · rw [firstFiltrationInclusion_f0, LinearMap.comp_zero]
    · rw [firstFiltrationInclusion_f0, firstGradedProjection_f0, LinearMap.range_zero]
      exact (LinearMap.ker_eq_bot.mpr (freeDualEquiv _).injective).symm
    · intro x y _
      exact Subsingleton.elim x y
    · exact (freeDualEquiv _).surjective
  · by_cases h1 : n = 1
    · subst n
      apply moduleShortExact_of_range_eq_ker
      · exact LinearMap.ext fun x => x.2
      · exact Submodule.range_subtype _
      · exact Submodule.injective_subtype _
      · exact verticalRestriction1_surjective M A
    · by_cases h2 : n = 2
      · subst n
        apply moduleShortExact_of_range_eq_ker
        · exact LinearMap.ext fun x => x.2
        · exact Submodule.range_subtype _
        · exact Submodule.injective_subtype _
        · exact verticalRestriction2_surjective M A
      · exact {
          exact := ShortComplex.exact_of_isZero_X₂ _ (degreeObject_isZero (Nf.targetSubsetComplex _) n h0 h1 h2)
          mono_f := (degreeObject_isZero (firstFiltrationComplex M A) n h0 h1 h2).mono _
          epi_g := (degreeObject_isZero (firstGradedComplex M A) n h0 h1 h2).epi _ }

/-- 実原filtrationが生成する第一graded短完全列。 -/
theorem firstGraded_shortExact : (firstGradedShortComplex M A).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ (firstGraded_degreewise_shortExact M A)

/-- 第一gradedは同じfiltration包含の標準cokernelそのものと同型。 -/
def firstGradedCokernelIso : cokernel (zeroExtensionMap (firstFiltrationInclusion M A)) ≅
    zeroExtension (firstGradedComplex M A) :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso (firstGraded_shortExact M A).gIsCokernel

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.firstGradedComplex
#print axioms AAT.AG.AtlasCoefficientFiber.verticalRestriction_comm0
#print axioms AAT.AG.AtlasCoefficientFiber.firstGradedProjection
#print axioms AAT.AG.AtlasCoefficientFiber.firstGradedProjection_f0
#print axioms AAT.AG.AtlasCoefficientFiber.firstGradedProjection_f1
#print axioms AAT.AG.AtlasCoefficientFiber.firstGradedProjection_f2
#print axioms AAT.AG.AtlasCoefficientFiber.verticalRestriction1_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.verticalRestriction2_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.firstGraded_standard_zero
#print axioms AAT.AG.AtlasCoefficientFiber.firstGradedShortComplex
#print axioms AAT.AG.AtlasCoefficientFiber.firstGraded_degreewise_shortExact
#print axioms AAT.AG.AtlasCoefficientFiber.firstGraded_shortExact
#print axioms AAT.AG.AtlasCoefficientFiber.firstGradedCokernelIso
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
