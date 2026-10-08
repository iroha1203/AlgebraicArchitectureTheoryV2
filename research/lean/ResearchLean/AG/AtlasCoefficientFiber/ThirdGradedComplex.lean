import ResearchLean.AG.AtlasCoefficientFiber.FilteredSpectralObject

/-!
# G-135 B：第三gradedの原F³商

## Implementation notes

F³は原carrier≤2のannihilatorで零となる。隣接商F²/F³を、同じ零包含と恒等射の
短完全列から構成する。F²を商の照合なしに第三gradedと呼ぶ案は採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 原F²/F³を読む第三gradedの具体的三項複体。 -/
abbrev thirdGradedComplex := secondFiltrationComplex M A

/-- 第三graded射影は同じ原F²元を返す。 -/
def thirdGradedProjection : ThreeCochainComplex.Hom (secondFiltrationComplex M A) (thirdGradedComplex M A) :=
  { f0 := LinearMap.id, f1 := LinearMap.id, f2 := LinearMap.id,
    comm0 := fun _ => rfl, comm1 := fun _ => rfl }

/-- 原F³包含の後の第三射影は零。 -/
theorem thirdGraded_standard_zero : zeroExtensionMap (zeroFiltrationInclusion M A) ≫
    zeroExtensionMap (thirdGradedProjection M A) = 0 := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  by_cases h0 : n = 0
  · subst n; rfl
  · by_cases h1 : n = 1
    · subst n; rfl
    · by_cases h2 : n = 2
      · subst n; rfl
      · haveI : Subsingleton ((zeroExtension (thirdGradedComplex M A)).X n) :=
          ModuleCat.subsingleton_of_isZero (degreeObject_isZero (thirdGradedComplex M A) n h0 h1 h2)
        exact Subsingleton.elim _ _

/-- 同じ原零包含・射影の第三graded短複体。 -/
def thirdGradedShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} ℚ) ℤ) :=
  ShortComplex.mk (zeroExtensionMap (zeroFiltrationInclusion M A))
    (zeroExtensionMap (thirdGradedProjection M A)) (thirdGraded_standard_zero M A)

/-- 原第三graded列は全次数で短完全。 -/
theorem thirdGraded_degreewise_shortExact (n : ℤ) :
    ((HomologicalComplex.eval (ModuleCat.{u} ℚ) (ComplexShape.up ℤ) n).mapShortComplex.obj
      (thirdGradedShortComplex M A)).ShortExact := by
  by_cases h0 : n = 0
  · subst n
    apply moduleShortExact_of_range_eq_ker
    · exact LinearMap.comp_zero _
    · change LinearMap.range (0 : PUnit.{u+1} →ₗ[ℚ] _) = LinearMap.ker LinearMap.id
      simp only [LinearMap.range_zero, LinearMap.ker_id]
    · intro x y _; exact Subsingleton.elim x y
    · exact Function.surjective_id
  · by_cases h1 : n = 1
    · subst n
      apply moduleShortExact_of_range_eq_ker
      · exact LinearMap.comp_zero _
      · change LinearMap.range (0 : PUnit.{u+1} →ₗ[ℚ] _) = LinearMap.ker LinearMap.id
        simp only [LinearMap.range_zero, LinearMap.ker_id]
      · intro x y _; exact Subsingleton.elim x y
      · exact Function.surjective_id
    · by_cases h2 : n = 2
      · subst n
        apply moduleShortExact_of_range_eq_ker
        · exact LinearMap.comp_zero _
        · change LinearMap.range (0 : PUnit.{u+1} →ₗ[ℚ] _) = LinearMap.ker LinearMap.id
          simp only [LinearMap.range_zero, LinearMap.ker_id]
        · intro x y _; exact Subsingleton.elim x y
        · exact Function.surjective_id
      · exact {
          exact := ShortComplex.exact_of_isZero_X₂ _ (degreeObject_isZero (secondFiltrationComplex M A) n h0 h1 h2)
          mono_f := (degreeObject_isZero zeroFiltrationComplex n h0 h1 h2).mono _
          epi_g := (degreeObject_isZero (thirdGradedComplex M A) n h0 h1 h2).epi _ }

/-- 原F³零包含から生成される第三graded短完全列。 -/
theorem thirdGraded_shortExact : (thirdGradedShortComplex M A).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ (thirdGraded_degreewise_shortExact M A)

/-- 第三gradedは同じ原F³包含の標準cokernelと同型。 -/
def thirdGradedCokernelIso : cokernel (zeroExtensionMap (zeroFiltrationInclusion M A)) ≅
    zeroExtension (thirdGradedComplex M A) :=
  (cokernelIsCokernel _).coconePointUniqueUpToIso (thirdGraded_shortExact M A).gIsCokernel

/-- 第三gradedへの標準cone商評価。 -/
def thirdGradedConeDesc : CochainComplex.mappingCone (zeroExtensionMap (zeroFiltrationInclusion M A)) ⟶
    zeroExtension (thirdGradedComplex M A) :=
  CochainComplex.mappingCone.descShortComplex (thirdGradedShortComplex M A)

/-- 第三graded cone評価は原短完全性から擬同型。 -/
instance thirdGradedConeDesc_quasiIso : QuasiIso (thirdGradedConeDesc M A) :=
  CochainComplex.mappingCone.quasiIso_descShortComplex (thirdGraded_shortExact M A)

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.thirdGradedComplex
#print axioms AAT.AG.AtlasCoefficientFiber.thirdGradedProjection
#print axioms AAT.AG.AtlasCoefficientFiber.thirdGraded_standard_zero
#print axioms AAT.AG.AtlasCoefficientFiber.thirdGradedShortComplex
#print axioms AAT.AG.AtlasCoefficientFiber.thirdGraded_degreewise_shortExact
#print axioms AAT.AG.AtlasCoefficientFiber.thirdGraded_shortExact
#print axioms AAT.AG.AtlasCoefficientFiber.thirdGradedCokernelIso
#print axioms AAT.AG.AtlasCoefficientFiber.thirdGradedConeDesc
#print axioms AAT.AG.AtlasCoefficientFiber.thirdGradedConeDesc_quasiIso
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
