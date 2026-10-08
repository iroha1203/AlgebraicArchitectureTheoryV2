import ResearchLean.AG.AtlasCoefficientFiber.GradedShortExact

/-!
# G-135 B：原混在面のgraded複体

## Implementation notes

F¹/F²の1次は水平辺双対、2次は混在面双対、微分は原Bの双対である。
原分解の射影を使って全射の原像を生成する。任意の水平・混在行列で代替する
案は同じ原微分への同定を失うため採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- F¹辺cochainの原水平辺への実制限。 -/
def horizontalRestriction1 : (firstFiltrationComplex M A).C1 →ₗ[ℚ]
    Module.Dual ℚ (HorizontalEdge M A →₀ ℚ) :=
  (horizontalEdgeInclusion M A).dualMap.comp
    ((freeDualEquiv _).toLinearMap.comp (LinearMap.ker (verticalRestriction1 M A)).subtype)

/-- F¹面cochainの原混在面への実制限。 -/
def mixedRestriction2 : (firstFiltrationComplex M A).C2 →ₗ[ℚ]
    Module.Dual ℚ (MixedFace M A →₀ ℚ) :=
  (mixedFaceInclusion M A).dualMap.comp
    ((freeDualEquiv _).toLinearMap.comp (LinearMap.ker (verticalRestriction2 M A)).subtype)

/-- 水平制限は同じ原chain包含を評価。 -/
@[simp] theorem horizontalRestriction1_apply (z : (firstFiltrationComplex M A).C1)
    (x : HorizontalEdge M A →₀ ℚ) :
    horizontalRestriction1 M A z x = freeDualEquiv _ z.1 (horizontalEdgeInclusion M A x) := rfl

/-- 混在制限は同じ原chain包含を評価。 -/
@[simp] theorem mixedRestriction2_apply (z : (firstFiltrationComplex M A).C2)
    (x : MixedFace M A →₀ ℚ) :
    mixedRestriction2 M A z x = freeDualEquiv _ z.1 (mixedFaceInclusion M A x) := rfl

/-- 原F¹微分を混在面で読むと同じB双対になる。 -/
theorem mixedRestriction_comm1 (z : (firstFiltrationComplex M A).C1) :
    mixedRestriction2 M A ((firstFiltrationComplex M A).d1 z) =
      (mixedHorizontalBoundary M A).dualMap (horizontalRestriction1 M A z) := by
  apply LinearMap.ext
  intro y
  rw [mixedRestriction2_apply, firstFiltrationDifferential_val,
    LinearMap.dualMap_apply, horizontalRestriction1_apply]
  erw [← chainD2_dual]
  have he := mixedBoundary_recombination M A y
  rw [← he, map_add]
  have hz := LinearMap.congr_fun z.2 (mixedVerticalBoundary M A y)
  change freeDualEquiv _ z.1 (verticalEdgeInclusion M A (mixedVerticalBoundary M A y)) = 0 at hz
  rw [hz, zero_add]

/-- 原混在面関係だけを保持する同じgr¹。 -/
abbrev secondGradedComplex : ThreeCochainComplex ℚ where
  C0 := PUnit.{u+1}
  C1 := Module.Dual ℚ (HorizontalEdge M A →₀ ℚ)
  C2 := Module.Dual ℚ (MixedFace M A →₀ ℚ)
  d0 := 0
  d1 := (mixedHorizontalBoundary M A).dualMap
  d1_comp_d0 := by intro z; simp

/-- F¹からgr¹への実水平辺・混在面射影。 -/
def secondGradedProjection : ThreeCochainComplex.Hom (firstFiltrationComplex M A) (secondGradedComplex M A) where
  f0 := 0
  f1 := horizontalRestriction1 M A
  f2 := mixedRestriction2 M A
  comm0 := by intro z; simp
  comm1 := mixedRestriction_comm1 M A

/-- 水平汎関数を原辺射影で延長したF¹原像。 -/
def horizontalCochainLift (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ)) :
    (firstFiltrationComplex M A).C1 :=
  ⟨(freeDualEquiv _).symm (β.comp (horizontalEdgeProjection M A)), by
    apply LinearMap.ext
    intro x
    rw [verticalRestriction1_apply, LinearEquiv.apply_symm_apply, LinearMap.comp_apply,
      horizontalEdgeProjection_vertical, map_zero]
    rfl⟩

/-- 水平延長の自由双対値は同じ原辺射影との合成。 -/
@[simp] theorem horizontalCochainLift_dual (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ)) :
    freeDualEquiv _ (horizontalCochainLift M A β).1 =
      β.comp (horizontalEdgeProjection M A) :=
  LinearEquiv.apply_symm_apply _ _

/-- 水平延長は同じ原水平制限を戻す。 -/
@[simp] theorem horizontalCochainLift_spec (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ)) :
    horizontalRestriction1 M A (horizontalCochainLift M A β) = β := by
  apply LinearMap.ext
  intro x
  rw [horizontalRestriction1_apply]
  change freeDualEquiv _ ((freeDualEquiv _).symm (β.comp (horizontalEdgeProjection M A))) _ = _
  rw [LinearEquiv.apply_symm_apply, LinearMap.comp_apply, horizontalEdgeProjection_inclusion]

/-- 水平制限の全射性は原射影延長から生成する。 -/
theorem horizontalRestriction1_surjective : Function.Surjective (horizontalRestriction1 M A) :=
  fun β => ⟨horizontalCochainLift M A β, horizontalCochainLift_spec M A β⟩

/-- 水平・垂直原辺分解により水平制限はF¹上単射。 -/
theorem horizontalRestriction1_injective : Function.Injective (horizontalRestriction1 M A) := by
  apply LinearMap.ker_eq_bot.mp
  apply bot_unique
  intro z hz
  apply Subtype.ext
  apply (freeDualEquiv _).injective
  apply LinearMap.ext
  intro x
  simp only [Submodule.coe_zero, map_zero, LinearMap.zero_apply]
  have he := edgeBlock_recombination M A x
  rw [← he, map_add]
  have hv := LinearMap.congr_fun z.2 (verticalEdgeProjection M A x)
  have hh := LinearMap.congr_fun hz (horizontalEdgeProjection M A x)
  change freeDualEquiv _ z.1 (verticalEdgeInclusion M A (verticalEdgeProjection M A x)) = 0 at hv
  change freeDualEquiv _ z.1 (horizontalEdgeInclusion M A (horizontalEdgeProjection M A x)) = 0 at hh
  rw [hv, hh, add_zero]

/-- 混在汎関数を原三面射影で延長したF¹原像。 -/
def mixedCochainLift (γ : Module.Dual ℚ (MixedFace M A →₀ ℚ)) :
    (firstFiltrationComplex M A).C2 :=
  ⟨(freeDualEquiv _).symm (γ.comp (mixedFaceProjection M A)), by
    apply LinearMap.ext
    intro x
    rw [verticalRestriction2_apply, LinearEquiv.apply_symm_apply, LinearMap.comp_apply,
      mixedFaceProjection_vertical, map_zero]
    rfl⟩

/-- 混在延長は同じ原混在制限を戻す。 -/
@[simp] theorem mixedCochainLift_spec (γ : Module.Dual ℚ (MixedFace M A →₀ ℚ)) :
    mixedRestriction2 M A (mixedCochainLift M A γ) = γ := by
  apply LinearMap.ext
  intro x
  rw [mixedRestriction2_apply]
  change freeDualEquiv _ ((freeDualEquiv _).symm (γ.comp (mixedFaceProjection M A))) _ = _
  rw [LinearEquiv.apply_symm_apply, LinearMap.comp_apply, mixedFaceProjection_inclusion]

/-- 混在制限の全射性は原射影延長から生成する。 -/
theorem mixedRestriction2_surjective : Function.Surjective (mixedRestriction2 M A) :=
  fun γ => ⟨mixedCochainLift M A γ, mixedCochainLift_spec M A γ⟩

/-- F²の元は混在面への制限で零となる。 -/
theorem mixedRestriction2_second (z : (secondFiltrationComplex M A).C2) :
    mixedRestriction2 M A ((secondFiltrationInclusion M A).f2 z) = 0 := by
  apply LinearMap.ext
  intro x
  rw [mixedRestriction2_apply, secondFiltrationInclusion_f2_val]
  have hx : mixedFaceInclusion M A x ∈ degenerateL2 M A :=
    mixedFaceInclusion_range_le_degenerate M A ⟨x, rfl⟩
  exact LinearMap.congr_fun z.2 (⟨mixedFaceInclusion M A x, hx⟩ : degenerateL2 M A)

/-- 混在・垂直面の原分解から、射影核はF²像と一致。 -/
theorem mixedRestriction2_kernel :
    LinearMap.range (secondFiltrationInclusion M A).f2 = LinearMap.ker (mixedRestriction2 M A) := by
  ext z
  constructor
  · rintro ⟨z, rfl⟩
    exact mixedRestriction2_second M A z
  · intro hz
    have hd : restriction2 M A z.1 = 0 := by
      apply LinearMap.ext
      intro x
      rw [restriction2_apply]
      have he := degenerateFace_recombination M A x
      rw [← he, map_add]
      have hv := LinearMap.congr_fun z.2 (verticalFaceProjection M A x.1)
      have hm := LinearMap.congr_fun hz (mixedFaceProjection M A x.1)
      change freeDualEquiv _ z.1 (verticalFaceInclusion M A (verticalFaceProjection M A x.1)) = 0 at hv
      change freeDualEquiv _ z.1 (mixedFaceInclusion M A (mixedFaceProjection M A x.1)) = 0 at hm
      rw [hv, hm, add_zero, LinearMap.zero_apply]
    exact ⟨⟨z.1, hd⟩, Subtype.ext rfl⟩

/-- F²の原包含は元cochain値を保つので単射。 -/
theorem secondFiltrationInclusion_f2_injective : Function.Injective (secondFiltrationInclusion M A).f2 := by
  intro x y hh
  apply Subtype.ext
  have he := congrArg (fun z : (firstFiltrationComplex M A).C2 => z.1) hh
  simpa only [secondFiltrationInclusion_f2_val] using he

/-- 第二graded射影の0次は零射。 -/
@[simp] theorem secondGradedProjection_f0 : (secondGradedProjection M A).f0 = 0 := rfl

/-- 第二graded射影の1次は同じ水平制限。 -/
@[simp] theorem secondGradedProjection_f1 : (secondGradedProjection M A).f1 = horizontalRestriction1 M A := rfl

/-- 第二graded射影の2次は同じ混在制限。 -/
@[simp] theorem secondGradedProjection_f2 : (secondGradedProjection M A).f2 = mixedRestriction2 M A := rfl

/-- 第二gradedの原二射は全整数次数で合成零。 -/
theorem secondGraded_standard_zero :
    zeroExtensionMap (secondFiltrationInclusion M A) ≫ zeroExtensionMap (secondGradedProjection M A) = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  change degreeMap (secondFiltrationInclusion M A) n ≫ degreeMap (secondGradedProjection M A) n = 0
  by_cases h0 : n = 0
  · subst n
    apply ModuleCat.hom_ext
    change (secondGradedProjection M A).f0.comp (secondFiltrationInclusion M A).f0 = 0
    rw [secondGradedProjection_f0, LinearMap.zero_comp]
  · by_cases h1 : n = 1
    · subst n
      apply ModuleCat.hom_ext
      change (secondGradedProjection M A).f1.comp (secondFiltrationInclusion M A).f1 = 0
      rw [secondFiltrationInclusion_f1, LinearMap.comp_zero]
    · by_cases h2 : n = 2
      · subst n
        apply ModuleCat.hom_ext
        exact LinearMap.ext (mixedRestriction2_second M A)
      · rw [degreeMap_out (secondFiltrationInclusion M A) n h0 h1 h2]
        simp

/-- 原F²→F¹→gr¹の同じ二射。 -/
def secondGradedShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℤ) :=
  ShortComplex.mk (zeroExtensionMap (secondFiltrationInclusion M A))
    (zeroExtensionMap (secondGradedProjection M A)) (secondGraded_standard_zero M A)

/-- 同じ原分解の核/全射計算が全整数次数の短完全性を生成する。 -/
theorem secondGraded_degreewise_shortExact (n : ℤ) :
    ((secondGradedShortComplex M A).map
      (HomologicalComplex.eval (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) n)).ShortExact := by
  by_cases h0 : n = 0
  · subst n
    apply moduleShortExact_of_range_eq_ker
    · rw [secondGradedProjection_f0, LinearMap.zero_comp]
    · rw [secondFiltrationInclusion_f0, secondGradedProjection_f0, LinearMap.range_id, LinearMap.ker_zero]
    · exact Function.injective_id
    · intro x
      exact ⟨0, Subsingleton.elim _ _⟩
  · by_cases h1 : n = 1
    · subst n
      apply moduleShortExact_of_range_eq_ker
      · rw [secondFiltrationInclusion_f1, LinearMap.comp_zero]
      · rw [secondFiltrationInclusion_f1, secondGradedProjection_f1, LinearMap.range_zero]
        exact (LinearMap.ker_eq_bot.mpr (horizontalRestriction1_injective M A)).symm
      · intro x y _
        exact Subsingleton.elim x y
      · exact horizontalRestriction1_surjective M A
    · by_cases h2 : n = 2
      · subst n
        apply moduleShortExact_of_range_eq_ker
        · exact LinearMap.ext (mixedRestriction2_second M A)
        · exact mixedRestriction2_kernel M A
        · exact secondFiltrationInclusion_f2_injective M A
        · exact mixedRestriction2_surjective M A
      · exact {
          exact := ShortComplex.exact_of_isZero_X₂ _ (degreeObject_isZero (firstFiltrationComplex M A) n h0 h1 h2)
          mono_f := (degreeObject_isZero (secondFiltrationComplex M A) n h0 h1 h2).mono _
          epi_g := (degreeObject_isZero (secondGradedComplex M A) n h0 h1 h2).epi _ }

/-- 原F²→F¹→gr¹の標準短完全列。 -/
theorem secondGraded_shortExact : (secondGradedShortComplex M A).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ (secondGraded_degreewise_shortExact M A)

/-- 第二gradedも同じ包含の標準cokernelそのものと同型。 -/
def secondGradedCokernelIso : cokernel (zeroExtensionMap (secondFiltrationInclusion M A)) ≅
    zeroExtension (secondGradedComplex M A) :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso (secondGraded_shortExact M A).gIsCokernel

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.horizontalRestriction1
#print axioms AAT.AG.AtlasCoefficientFiber.mixedRestriction2
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalRestriction1_apply
#print axioms AAT.AG.AtlasCoefficientFiber.mixedRestriction2_apply
#print axioms AAT.AG.AtlasCoefficientFiber.mixedRestriction_comm1
#print axioms AAT.AG.AtlasCoefficientFiber.secondGradedComplex
#print axioms AAT.AG.AtlasCoefficientFiber.secondGradedProjection
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalCochainLift
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalCochainLift_dual
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalCochainLift_spec
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalRestriction1_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalRestriction1_injective
#print axioms AAT.AG.AtlasCoefficientFiber.mixedCochainLift
#print axioms AAT.AG.AtlasCoefficientFiber.mixedCochainLift_spec
#print axioms AAT.AG.AtlasCoefficientFiber.mixedRestriction2_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.mixedRestriction2_second
#print axioms AAT.AG.AtlasCoefficientFiber.mixedRestriction2_kernel
#print axioms AAT.AG.AtlasCoefficientFiber.secondFiltrationInclusion_f2_injective
#print axioms AAT.AG.AtlasCoefficientFiber.secondGradedProjection_f0
#print axioms AAT.AG.AtlasCoefficientFiber.secondGradedProjection_f1
#print axioms AAT.AG.AtlasCoefficientFiber.secondGradedProjection_f2
#print axioms AAT.AG.AtlasCoefficientFiber.secondGraded_standard_zero
#print axioms AAT.AG.AtlasCoefficientFiber.secondGradedShortComplex
#print axioms AAT.AG.AtlasCoefficientFiber.secondGraded_degreewise_shortExact
#print axioms AAT.AG.AtlasCoefficientFiber.secondGraded_shortExact
#print axioms AAT.AG.AtlasCoefficientFiber.secondGradedCokernelIso
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
