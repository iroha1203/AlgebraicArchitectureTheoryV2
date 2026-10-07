import ResearchLean.AG.AtlasCoefficientFiber.EvaluationAnnihilator
import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# G-135 A §4：実εと同じL双対制限の標準短完全列

Implementation notes: Pは実Kan係数から独立に作られた複体。
同じ評価εと制限をG-133の零延長へ渡し、全ℤ次数の完全性を証明する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits CanonicalResolution ResolutionInvariance FaceRelationSubdivision
open AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u, u} qc} {Nf : TargetSupportedNerve.{u, u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 標準零延長Homの次数外計算API。零対象の既存公開性質から得る。 -/
theorem degreeMap_out {C D : TwoPhase.ThreeCochainComplex.{0,u} ℚ}
    (f : TwoPhase.ThreeCochainComplex.Hom C D) (n : ℤ)
    (h0 : n ≠ 0) (h1 : n ≠ 1) (h2 : n ≠ 2) : degreeMap f n = 0 :=
  (degreeObject_isZero C n h0 h1 h2).eq_of_src _ _

/-- 独立Pから細複体、指定L双対への二射の全ℤ次数での合成零性。 -/
theorem evaluation_restriction_standard_zero :
    zeroExtensionMap (evaluationHom M A) ≫ zeroExtensionMap (restrictionHom M A) = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  change degreeMap (evaluationHom M A) n ≫ degreeMap (restrictionHom M A) n = 0
  by_cases h0 : n = 0
  · subst n
    apply ModuleCat.hom_ext
    exact LinearMap.ext (restriction0_evaluation0 M A)
  · by_cases h1 : n = 1
    · subst n
      apply ModuleCat.hom_ext
      exact LinearMap.ext (restriction1_evaluation1 M A)
    · by_cases h2 : n = 2
      · subst n
        apply ModuleCat.hom_ext
        exact LinearMap.ext (restriction2_evaluation2 M A)
      · rw [degreeMap_out (evaluationHom M A) n h0 h1 h2]
        simp

/-- 独立P、細実複体、指定Qを同じ二射で結ぶ標準short complex。 -/
def evaluationRestrictionShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℤ) :=
  ShortComplex.mk (zeroExtensionMap (evaluationHom M A))
    (zeroExtensionMap (restrictionHom M A)) (evaluation_restriction_standard_zero M A)

/-- 生成short complexの左射は同じεの標準零延長。 -/
@[simp] theorem evaluationRestrictionShortComplex_f :
    (evaluationRestrictionShortComplex M A).f = zeroExtensionMap (evaluationHom M A) := rfl
/-- 生成short complexの右射は同じL双対制限の標準零延長。 -/
@[simp] theorem evaluationRestrictionShortComplex_g :
    (evaluationRestrictionShortComplex M A).g = zeroExtensionMap (restrictionHom M A) := rfl

/-- 加群short complexを実関数の完全性と単射・全射性から短完全とする補助API。 -/
theorem moduleShortExact_of_range_eq_ker {V W Z : Type u}
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    [AddCommGroup Z] [Module ℚ Z] (f : V →ₗ[ℚ] W) (g : W →ₗ[ℚ] Z)
    (hz : g.comp f = 0) (he : LinearMap.range f = LinearMap.ker g)
    (hi : Function.Injective f) (hs : Function.Surjective g) :
    (ShortComplex.moduleCatMk f g hz).ShortExact where
  exact := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
    (LinearMap.exact_iff.mpr he.symm)
  mono_f := (ModuleCat.mono_iff_injective _).mpr hi
  epi_g := (ModuleCat.epi_iff_surjective _).mpr hs

/-- 指定二射の全ℤ次数のshort exact性。次数外も明示零加群で放電する。 -/
theorem evaluationRestriction_degreewise_shortExact (n : ℤ) :
    ((evaluationRestrictionShortComplex M A).map
      (HomologicalComplex.eval (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) n)).ShortExact := by
  by_cases h0 : n = 0
  · subst n
    apply moduleShortExact_of_range_eq_ker
    · exact LinearMap.ext (restriction0_evaluation0 M A)
    · exact evaluation0_range_eq_ker M A
    · exact evaluation0_injective M A
    · exact restriction0_surjective M A
  · by_cases h1 : n = 1
    · subst n
      apply moduleShortExact_of_range_eq_ker
      · exact LinearMap.ext (restriction1_evaluation1 M A)
      · exact evaluation1_range_eq_ker M A
      · exact evaluation1_injective M A
      · exact restriction1_surjective M A
    · by_cases h2 : n = 2
      · subst n
        apply moduleShortExact_of_range_eq_ker
        · exact LinearMap.ext (restriction2_evaluation2 M A)
        · exact evaluation2_range_eq_ker M A
        · exact evaluation2_injective M A
        · exact restriction2_surjective M A
      · have hout (C : TwoPhase.ThreeCochainComplex.{0,u} ℚ) : Limits.IsZero (degreeObject C n) :=
          degreeObject_isZero C n h0 h1 h2
        exact {
          exact := ShortComplex.exact_of_isZero_X₂ _ (hout (Nf.targetSubsetComplex _))
          mono_f := (hout (pushforwardComplex M A)).mono _
          epi_g := (hout (restrictionComplex M A)).epi _
        }

/-- 実Kan順像Pと原始L双対Qを結ぶ標準ℤ複体の短完全列。 -/
theorem evaluationRestriction_shortExact : (evaluationRestrictionShortComplex M A).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _
    (evaluationRestriction_degreewise_shortExact M A)

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.degreeMap_out
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation_restriction_standard_zero
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationRestrictionShortComplex
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationRestrictionShortComplex_f
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationRestrictionShortComplex_g
#print axioms AAT.AG.AtlasCoefficientFiber.moduleShortExact_of_range_eq_ker
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationRestriction_degreewise_shortExact
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationRestriction_shortExact
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
