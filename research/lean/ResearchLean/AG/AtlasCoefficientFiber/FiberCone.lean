import ResearchLean.AG.AtlasCoefficientFiber.CoefficientCones
import ResearchLean.AG.AtlasCoefficientFiber.FiveTermSequence
import ResearchLean.AG.AtlasDefectComposition.ConeExactSequence

/-!
# G-135 C：原εの錐と原L双対Qの全次数同定

## Implementation notes

原evaluationRestrictionShortComplexの標準descを使い、実(y,x)を同じL制限yへ送る。
擬同型は生成済み原短完全性から得る。全次数の標準連結射を同じδへ同定してから、
次数1を原R座標と原τへ移す。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits CanonicalResolution ResolutionInvariance FaceRelationSubdivision
open AtlasDefectComposition CochainComplex HomologicalComplex
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 同じ原εの錐から原Qへ送る標準商評価。 -/
def fiberConeDesc : fiberCone M A ⟶ zeroExtension (restrictionComplex M A) :=
  mappingCone.descShortComplex (evaluationRestrictionShortComplex M A)

/-- 原Qへの評価を標準short complexのdescとして読む所有API。 -/
theorem fiberConeDesc_eq : fiberConeDesc M A =
    mappingCone.descShortComplex (evaluationRestrictionShortComplex M A) := rfl

/-- 原ε錐のtarget包含を原Q評価へ送る次数別公開式。 -/
theorem fiberConeDesc_inr_apply (n : ℤ)
    (y : (zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).X n) :
    (fiberConeDesc M A).f n
      ((mappingCone.inr (zeroExtensionMap (evaluationHom M A))).f n y) =
      (zeroExtensionMap (restrictionHom M A)).f n y := by
  have hz := congrArg (fun t : ((zeroExtension
      (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).X n ⟶
        (zeroExtension (restrictionComplex M A)).X n) => t y)
    (mappingCone.inr_f_descShortComplex_f (evaluationRestrictionShortComplex M A) n)
  simpa only [ModuleCat.comp_apply] using hz

/-- 原ε錐のshifted source包含は原Q評価で零となる。 -/
theorem fiberConeDesc_inl_apply (n : ℤ)
    (x : (zeroExtension (pushforwardComplex M A)).X (n+1)) :
    (fiberConeDesc M A).f n
      ((mappingCone.inl (zeroExtensionMap (evaluationHom M A))).v (n+1) n (by simp) x) = 0 := by
  have hz := congrArg (fun t : ((zeroExtension (pushforwardComplex M A)).X (n+1) ⟶
      (zeroExtension (restrictionComplex M A)).X n) => t x)
    (mappingCone.inl_v_descShortComplex_f (evaluationRestrictionShortComplex M A)
      (n+1) n (by simp))
  simpa only [ModuleCat.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply] using hz

/-- 全次数で実錐座標(y,x)を同じ原Lの制限yへ送る。 -/
theorem fiberConeDesc_symm_apply (n : ℤ)
    (p : (zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).X n ×
      (zeroExtension (pushforwardComplex M A)).X (n+1)) :
    (fiberConeDesc M A).f n
      ((coneCoordinateEquiv (zeroExtensionMap (evaluationHom M A)) n).symm p) =
        (zeroExtensionMap (restrictionHom M A)).f n p.1 := by
  rw [coneCoordinateEquiv_symm_eq, map_add, fiberConeDesc_inr_apply,
    fiberConeDesc_inl_apply, add_zero]

/-- 実錐の全元に対する原L制限評価式。 -/
theorem fiberConeDesc_apply (n : ℤ) (z : (fiberCone M A).X n) :
    (fiberConeDesc M A).f n z = (zeroExtensionMap (restrictionHom M A)).f n
      (coneCoordinateEquiv (zeroExtensionMap (evaluationHom M A)) n z).1 := by
  simpa only [LinearEquiv.symm_apply_apply] using
    fiberConeDesc_symm_apply M A n (coneCoordinateEquiv _ n z)

/-- 原ε錐への包含の後に評価すると、原L制限そのものになる。 -/
theorem fiberCone_inr_desc : mappingCone.inr (zeroExtensionMap (evaluationHom M A)) ≫
    fiberConeDesc M A = zeroExtensionMap (restrictionHom M A) :=
  mappingCone.inr_descShortComplex (evaluationRestrictionShortComplex M A)

/-- 原短完全性が同じ実評価を全整数次数の擬同型にする。 -/
instance fiberConeDesc_quasiIso : QuasiIso (fiberConeDesc M A) :=
  mappingCone.quasiIso_descShortComplex (evaluationRestriction_shortExact M A)

/-- 原Qへの評価の全homology射は標準圏で同型である。 -/
instance fiberConeDesc_homology_isIso (n : ℤ) :
    IsIso (HomologicalComplex.homologyMap (fiberConeDesc M A) n) :=
  (quasiIsoAt_iff_isIso_homologyMap _ n).mp inferInstance

/-- 原ε錐と原Qの全次数homologyを同じ評価で両方向同定する。 -/
def fiberConeHomologyEquiv (n : ℤ) : (fiberCone M A).homology n ≃ₗ[ℚ]
    (zeroExtension (restrictionComplex M A)).homology n :=
  (asIso (HomologicalComplex.homologyMap (fiberConeDesc M A) n)).toLinearEquiv

/-- 全次数homology同型の順写像は同じ実評価のhomology射である。 -/
@[simp] theorem fiberConeHomologyEquiv_apply (n : ℤ) (z : (fiberCone M A).homology n) :
    fiberConeHomologyEquiv M A n z = HomologicalComplex.homologyMap (fiberConeDesc M A) n z := rfl

/-- 全次数homology同型の逆元は同じ評価で元のQ類へ戻る。 -/
@[simp] theorem fiberConeHomologyEquiv_symm_evaluation (n : ℤ)
    (z : (zeroExtension (restrictionComplex M A)).homology n) :
    HomologicalComplex.homologyMap (fiberConeDesc M A) n
      ((fiberConeHomologyEquiv M A n).symm z) = z :=
  (fiberConeHomologyEquiv M A n).apply_symm_apply z

/-- 錐包含と原L制限のhomology図式は全整数次数で可換である。 -/
theorem fiberConeHomologyEquiv_inr (n : ℤ)
    (z : (zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology n) :
    fiberConeHomologyEquiv M A n
      (HomologicalComplex.homologyMap (mappingCone.inr (zeroExtensionMap (evaluationHom M A))) n z) =
      HomologicalComplex.homologyMap (zeroExtensionMap (restrictionHom M A)) n z := by
  rw [fiberConeHomologyEquiv_apply, ← ModuleCat.comp_apply,
    ← HomologicalComplex.homologyMap_comp, fiberCone_inr_desc]

/-- 原ε錐の連結射は全次数で原Q評価の後に同じ標準SESδを作用させる。 -/
theorem fiberCone_connecting (n : ℤ) : coneConnecting (zeroExtensionMap (evaluationHom M A)) n =
    HomologicalComplex.homologyMap (fiberConeDesc M A) n ≫
      (evaluationRestriction_shortExact M A).δ n (n+1) rfl :=
  coneConnecting_shortExact (evaluationRestrictionShortComplex M A)
    (evaluationRestriction_shortExact M A) n

/-- 次数1の同じfiber錐を、原Q座標の後に原κ*核Rへ同定する。 -/
def fiberConeH1REquiv : (fiberCone M A).homology (1 : ℤ) ≃ₗ[ℚ] R M A :=
  (fiberConeHomologyEquiv M A 1).trans (restrictionStandardHomologyREquiv M A)

/-- 原R同型の順写像は同じ原評価とR座標の合成である。 -/
@[simp] theorem fiberConeH1REquiv_apply (z : (fiberCone M A).homology (1 : ℤ)) :
    fiberConeH1REquiv M A z = restrictionStandardHomologyREquiv M A
      (fiberConeHomologyEquiv M A 1 z) := rfl

/-- 次数1の錐包含は同じ五項列の原fiber制限射へ送られる。 -/
theorem fiberConeH1REquiv_inr
    (z : (zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology (1 : ℤ)) :
    fiberConeH1REquiv M A
      (HomologicalComplex.homologyMap (mappingCone.inr (zeroExtensionMap (evaluationHom M A))) 1 z) =
        fiberRestrictionH1 M A z := by
  rw [fiberConeH1REquiv_apply, fiberConeHomologyEquiv_inr, fiberRestrictionH1_apply]

/-- 原τは同じ錐連結射と符号まで一致し、任意の錐homology元で成り立つ。 -/
theorem fiberConeH1REquiv_tau (z : (fiberCone M A).homology (1 : ℤ)) :
    connectingTau M A (fiberConeH1REquiv M A z) =
      coneConnecting (zeroExtensionMap (evaluationHom M A)) 1 z := by
  rw [fiberConeH1REquiv_apply, connectingTau_restrictionStandardHomologyREquiv,
    fiberCone_connecting, ModuleCat.comp_apply, fiberConeHomologyEquiv_apply]
  rfl

/-- 原Rへの同定の下で錐核射影の値は同じτである。 -/
theorem fiberConeKernelProjection_tau (z : (fiberCone M A).homology (1 : ℤ)) :
    (coneKernelProjection (zeroExtensionMap (evaluationHom M A)) 1 z).1 =
      connectingTau M A (fiberConeH1REquiv M A z) := by
  rw [coneKernelProjection_val, fiberConeH1REquiv_tau]

/-- 原H⁰Q零性を同じ実評価の両方向同型で原ε錐へ移す。 -/
theorem fiberCone_H0_isZero : IsZero ((fiberCone M A).homology (0 : ℤ)) := by
  letI : Subsingleton ((zeroExtension (restrictionComplex M A)).homology (0 : ℤ)) :=
    ModuleCat.subsingleton_of_isZero (restrictionComplex_H0_isZero M A)
  letI : Subsingleton ((fiberCone M A).homology (0 : ℤ)) :=
    (fiberConeHomologyEquiv M A 0).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.fiberConeDesc
#print axioms AAT.AG.AtlasCoefficientFiber.fiberConeDesc_eq
#print axioms AAT.AG.AtlasCoefficientFiber.fiberConeDesc_inr_apply
#print axioms AAT.AG.AtlasCoefficientFiber.fiberConeDesc_inl_apply
#print axioms AAT.AG.AtlasCoefficientFiber.fiberConeDesc_symm_apply
#print axioms AAT.AG.AtlasCoefficientFiber.fiberConeDesc_apply
#print axioms AAT.AG.AtlasCoefficientFiber.fiberCone_inr_desc
#print axioms AAT.AG.AtlasCoefficientFiber.fiberConeDesc_quasiIso
#print axioms AAT.AG.AtlasCoefficientFiber.fiberConeDesc_homology_isIso
#print axioms AAT.AG.AtlasCoefficientFiber.fiberConeHomologyEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.fiberConeHomologyEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.fiberConeHomologyEquiv_symm_evaluation
#print axioms AAT.AG.AtlasCoefficientFiber.fiberConeHomologyEquiv_inr
#print axioms AAT.AG.AtlasCoefficientFiber.fiberCone_connecting
#print axioms AAT.AG.AtlasCoefficientFiber.fiberConeH1REquiv
#print axioms AAT.AG.AtlasCoefficientFiber.fiberConeH1REquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.fiberConeH1REquiv_inr
#print axioms AAT.AG.AtlasCoefficientFiber.fiberConeH1REquiv_tau
#print axioms AAT.AG.AtlasCoefficientFiber.fiberConeKernelProjection_tau
#print axioms AAT.AG.AtlasCoefficientFiber.fiberCone_H0_isZero
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
