import ResearchLean.AG.AtlasCoefficientFiber.EvaluationAnnihilator

/-!
# G-135 A §4：独立順像Pと原支持chain商の双対

Implementation notes: 商の二境界は指定Lによる元のchain微分の商である。
Pを商から定義せず、実εの像の両包含を使って両方向線形同型を作る。
同型は全chain代表元で同じεを評価し、二微分とも可換とする。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits CanonicalResolution ResolutionInvariance FaceRelationSubdivision
open AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u, u} qc} {Nf : TargetSupportedNerve.{u, u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 元の第一chain境界を指定Lによる実商へ降ろす。 -/
def quotientBoundary1 :
    (K1 Nf (comparisonFactor qc qf h ⁻¹' A) ⧸ degenerateL1 M A) →ₗ[ℚ]
      (K0 Nf (comparisonFactor qc qf h ⁻¹' A) ⧸ degenerateL0 M A) :=
  Submodule.mapQ _ _ (chainD1 Nf _) (fun x hx =>
    (degenerateL1_boundary_eq M A).le ⟨x, hx, rfl⟩)

/-- 元の第二chain境界を指定Lによる実商へ降ろす。 -/
def quotientBoundary2 :
    (K2 Nf (comparisonFactor qc qf h ⁻¹' A) ⧸ degenerateL2 M A) →ₗ[ℚ]
      (K1 Nf (comparisonFactor qc qf h ⁻¹' A) ⧸ degenerateL1 M A) :=
  Submodule.mapQ _ _ (chainD2 Nf _) (fun x hx => degenerateL2_boundary_le M A ⟨x, hx, rfl⟩)

/-- 商の第一境界は全元で元の同じchain境界を読む。 -/
@[simp] theorem quotientBoundary1_mk (x : K1 Nf (comparisonFactor qc qf h ⁻¹' A)) :
    quotientBoundary1 M A ((degenerateL1 M A).mkQ x) =
      (degenerateL0 M A).mkQ (chainD1 Nf _ x) := rfl
/-- 商の第二境界は全元で元の同じchain境界を読む。 -/
@[simp] theorem quotientBoundary2_mk (x : K2 Nf (comparisonFactor qc qf h ⁻¹' A)) :
    quotientBoundary2 M A ((degenerateL2 M A).mkQ x) =
      (degenerateL1 M A).mkQ (chainD2 Nf _ x) := rfl

/-- 元のsquare-zeroにより実商の境界もsquare-zero。 -/
theorem quotientBoundary_square : (quotientBoundary1 M A).comp (quotientBoundary2 M A) = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := (degenerateL2 M A).mkQ_surjective x
  rw [LinearMap.comp_apply, quotientBoundary2_mk, quotientBoundary1_mk]
  have hy := LinearMap.congr_fun (chainD1_comp_chainD2 Nf (comparisonFactor qc qf h ⁻¹' A)) y
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hy
  rw [hy, map_zero, LinearMap.zero_apply]

/-- 元のchain商のsquare-zeroを双対化する。 -/
theorem quotientDualDifferential_square
    (z : Module.Dual ℚ (K0 Nf (comparisonFactor qc qf h ⁻¹' A) ⧸ degenerateL0 M A)) :
    (quotientBoundary2 M A).dualMap ((quotientBoundary1 M A).dualMap z) = 0 := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.dualMap_apply, LinearMap.dualMap_apply]
  have hx := LinearMap.congr_fun (quotientBoundary_square M A) x
  simp only [LinearMap.comp_apply, LinearMap.zero_apply] at hx
  rw [hx, map_zero, LinearMap.zero_apply]

/-- 指定Lによる元の支持chain商の同じ境界を双対化した複体。 -/
abbrev quotientDualComplex : TwoPhase.ThreeCochainComplex ℚ where
  C0 := Module.Dual ℚ (K0 Nf (comparisonFactor qc qf h ⁻¹' A) ⧸ degenerateL0 M A)
  C1 := Module.Dual ℚ (K1 Nf (comparisonFactor qc qf h ⁻¹' A) ⧸ degenerateL1 M A)
  C2 := Module.Dual ℚ (K2 Nf (comparisonFactor qc qf h ⁻¹' A) ⧸ degenerateL2 M A)
  d0 := (quotientBoundary1 M A).dualMap
  d1 := (quotientBoundary2 M A).dualMap
  d1_comp_d0 := quotientDualDifferential_square M A

/-- 商双対の第一微分は同じ商境界で評価する。 -/
@[simp] theorem quotientDualComplex_d0_apply (z : (quotientDualComplex M A).C0)
    (x : K1 Nf (comparisonFactor qc qf h ⁻¹' A) ⧸ degenerateL1 M A) :
    (quotientDualComplex M A).d0 z x = z (quotientBoundary1 M A x) := rfl
/-- 商双対の第二微分は同じ商境界で評価する。 -/
@[simp] theorem quotientDualComplex_d1_apply (z : (quotientDualComplex M A).C1)
    (x : K2 Nf (comparisonFactor qc qf h ⁻¹' A) ⧸ degenerateL2 M A) :
    (quotientDualComplex M A).d1 z x = z (quotientBoundary2 M A x) := rfl

/-- 自由chain双対の実像完全性から商双対同型を作る補助API。 -/
def quotientDualEquivOfRestriction {I P : Type u} [AddCommGroup P] [Module ℚ P]
    (W : Submodule ℚ (I →₀ ℚ)) (e : P →ₗ[ℚ] (I → ℚ)) (hi : Function.Injective e)
    (hz : ∀ p, W.dualRestrict (freeDualEquiv I (e p)) = 0)
    (hs : ∀ z, W.dualRestrict (freeDualEquiv I z) = 0 → ∃ p, e p = z) :
    P ≃ₗ[ℚ] Module.Dual ℚ ((I →₀ ℚ) ⧸ W) :=
  (LinearEquiv.ofBijective
    (((freeDualEquiv I).toLinearMap.comp e).codRestrict W.dualAnnihilator hz)
    ⟨by
      intro x y he
      apply hi
      apply (freeDualEquiv I).injective
      exact congrArg Subtype.val he,
    by
      intro z
      let w := (freeDualEquiv I).symm z.1
      have hw : W.dualRestrict (freeDualEquiv I w) = 0 := by
        rw [(freeDualEquiv I).apply_symm_apply]; exact z.2
      obtain ⟨p, hp⟩ := hs w hw
      refine ⟨p, Subtype.ext ?_⟩
      change freeDualEquiv I (e p) = z.1
      rw [hp, (freeDualEquiv I).apply_symm_apply]⟩).trans
    W.dualQuotEquivDualAnnihilator.symm

/-- 補助同型の商代表元評価は元の同じ自由chain双対評価。 -/
@[simp] theorem quotientDualEquivOfRestriction_mk {I P : Type u} [AddCommGroup P] [Module ℚ P]
    (W : Submodule ℚ (I →₀ ℚ)) (e : P →ₗ[ℚ] (I → ℚ)) (hi : Function.Injective e)
    (hz : ∀ p, W.dualRestrict (freeDualEquiv I (e p)) = 0)
    (hs : ∀ z, W.dualRestrict (freeDualEquiv I z) = 0 → ∃ p, e p = z)
    (p : P) (x : I →₀ ℚ) :
    quotientDualEquivOfRestriction W e hi hz hs p (W.mkQ x) = freeDualEquiv I (e p) x := rfl

/-- 実ε次数0から生成する独立Pと商双対の両方向同型。 -/
def evaluationQuotientDual0 : (pushforwardComplex M A).C0 ≃ₗ[ℚ] (quotientDualComplex M A).C0 :=
  quotientDualEquivOfRestriction _ (evaluation0 M A) (evaluation0_injective M A)
    (restriction0_evaluation0 M A) (evaluation0_preimage_of_restriction_zero M A)
/-- 実ε次数1から生成する独立Pと商双対の両方向同型。 -/
def evaluationQuotientDual1 : (pushforwardComplex M A).C1 ≃ₗ[ℚ] (quotientDualComplex M A).C1 :=
  quotientDualEquivOfRestriction _ (evaluation1 M A) (evaluation1_injective M A)
    (restriction1_evaluation1 M A) (evaluation1_preimage_of_restriction_zero M A)
/-- 実ε次数2から生成する独立Pと商双対の両方向同型。 -/
def evaluationQuotientDual2 : (pushforwardComplex M A).C2 ≃ₗ[ℚ] (quotientDualComplex M A).C2 :=
  quotientDualEquivOfRestriction _ (evaluation2 M A) (evaluation2_injective M A)
    (restriction2_evaluation2 M A) (evaluation2_preimage_of_restriction_zero M A)

/-- 次数0同型は全代表元で同じεを読む。 -/
@[simp] theorem evaluationQuotientDual0_mk (z : (pushforwardComplex M A).C0)
    (x : K0 Nf (comparisonFactor qc qf h ⁻¹' A)) :
    evaluationQuotientDual0 M A z ((degenerateL0 M A).mkQ x) =
      freeDualEquiv _ (evaluation0 M A z) x := rfl
/-- 次数1同型は全代表元で同じεを読む。 -/
@[simp] theorem evaluationQuotientDual1_mk (z : (pushforwardComplex M A).C1)
    (x : K1 Nf (comparisonFactor qc qf h ⁻¹' A)) :
    evaluationQuotientDual1 M A z ((degenerateL1 M A).mkQ x) =
      freeDualEquiv _ (evaluation1 M A z) x := rfl
/-- 次数2同型は全代表元で同じεを読む。 -/
@[simp] theorem evaluationQuotientDual2_mk (z : (pushforwardComplex M A).C2)
    (x : K2 Nf (comparisonFactor qc qf h ⁻¹' A)) :
    evaluationQuotientDual2 M A z ((degenerateL2 M A).mkQ x) =
      freeDualEquiv _ (evaluation2 M A z) x := rfl

/-- 次数別同型は同じ実εのcochain条件により第一微分と可換。 -/
theorem evaluationQuotientDual_comm0 (z : (pushforwardComplex M A).C0) :
    evaluationQuotientDual1 M A ((pushforwardComplex M A).d0 z) =
      (quotientDualComplex M A).d0 (evaluationQuotientDual0 M A z) := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := (degenerateL1 M A).mkQ_surjective x
  rw [evaluationQuotientDual1_mk, quotientDualComplex_d0_apply,
    quotientBoundary1_mk, evaluationQuotientDual0_mk, chainD1_dual]
  exact congrArg (fun w => freeDualEquiv _ w y) (evaluation_comm0 M A z)

/-- 次数別同型は同じ実εのcochain条件により第二微分と可換。 -/
theorem evaluationQuotientDual_comm1 (z : (pushforwardComplex M A).C1) :
    evaluationQuotientDual2 M A ((pushforwardComplex M A).d1 z) =
      (quotientDualComplex M A).d1 (evaluationQuotientDual1 M A z) := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, rfl⟩ := (degenerateL2 M A).mkQ_surjective x
  rw [evaluationQuotientDual2_mk, quotientDualComplex_d1_apply,
    quotientBoundary2_mk, evaluationQuotientDual1_mk, chainD2_dual]
  exact congrArg (fun w => freeDualEquiv _ w y) (evaluation_comm1 M A z)

/-- 三次数同型と両微分の可換式で作る独立Pから商双対への実Hom。 -/
def evaluationQuotientDualHom : TwoPhase.ThreeCochainComplex.Hom
    (pushforwardComplex M A) (quotientDualComplex M A) where
  f0 := (evaluationQuotientDual0 M A).toLinearMap
  f1 := (evaluationQuotientDual1 M A).toLinearMap
  f2 := (evaluationQuotientDual2 M A).toLinearMap
  comm0 := evaluationQuotientDual_comm0 M A
  comm1 := evaluationQuotientDual_comm1 M A

/-- 商双対への射の次数0成分。 -/
@[simp] theorem evaluationQuotientDualHom_f0 :
    (evaluationQuotientDualHom M A).f0 = (evaluationQuotientDual0 M A).toLinearMap := rfl
/-- 商双対への射の次数1成分。 -/
@[simp] theorem evaluationQuotientDualHom_f1 :
    (evaluationQuotientDualHom M A).f1 = (evaluationQuotientDual1 M A).toLinearMap := rfl
/-- 商双対への射の次数2成分。 -/
@[simp] theorem evaluationQuotientDualHom_f2 :
    (evaluationQuotientDualHom M A).f2 = (evaluationQuotientDual2 M A).toLinearMap := rfl

/-- 実商双対へのHomは標準ℤ cochain圏の同型である。 -/
instance evaluationQuotientDualHom_standard_isIso :
    IsIso (zeroExtensionMap (evaluationQuotientDualHom M A)) := by
  have hc (n : ℤ) : IsIso ((zeroExtensionMap (evaluationQuotientDualHom M A)).f n) := by
    change IsIso (degreeMap (evaluationQuotientDualHom M A) n)
    by_cases h0 : n = 0
    · subst n
      exact (ConcreteCategory.isIso_iff_bijective _).mpr (evaluationQuotientDual0 M A).bijective
    · by_cases h1 : n = 1
      · subst n
        exact (ConcreteCategory.isIso_iff_bijective _).mpr (evaluationQuotientDual1 M A).bijective
      · by_cases h2 : n = 2
        · subst n
          exact (ConcreteCategory.isIso_iff_bijective _).mpr (evaluationQuotientDual2 M A).bijective
        · have hout (C : TwoPhase.ThreeCochainComplex.{0,u} ℚ) : IsZero (degreeObject C n) := by
            have he : degreeObject C n = ModuleCat.of ℚ PUnit.{u+1} := by
              simp [degreeObject, h0, h1, h2]
            rw [he]
            exact ModuleCat.isZero_of_subsingleton _
          have he : degreeMap (evaluationQuotientDualHom M A) n =
              (IsZero.iso (hout (pushforwardComplex M A)) (hout (quotientDualComplex M A))).hom :=
            (hout (pushforwardComplex M A)).eq_of_src _ _
          rw [he]
          infer_instance
  letI := hc
  exact HomologicalComplex.Hom.isIso_of_components _

/-- 独立した実Kan順像Pと元のchain商双対の標準複体同型。 -/
def evaluationQuotientDualStandardIso :
    zeroExtension (pushforwardComplex M A) ≅ zeroExtension (quotientDualComplex M A) :=
  asIso (zeroExtensionMap (evaluationQuotientDualHom M A))

/-- 標準同型の順方向は三次数で同じ実εを評価する生成Hom。 -/
@[simp] theorem evaluationQuotientDualStandardIso_hom :
    (evaluationQuotientDualStandardIso M A).hom =
      zeroExtensionMap (evaluationQuotientDualHom M A) := rfl

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.quotientBoundary1
#print axioms AAT.AG.AtlasCoefficientFiber.quotientBoundary2
#print axioms AAT.AG.AtlasCoefficientFiber.quotientBoundary1_mk
#print axioms AAT.AG.AtlasCoefficientFiber.quotientBoundary2_mk
#print axioms AAT.AG.AtlasCoefficientFiber.quotientBoundary_square
#print axioms AAT.AG.AtlasCoefficientFiber.quotientDualDifferential_square
#print axioms AAT.AG.AtlasCoefficientFiber.quotientDualComplex
#print axioms AAT.AG.AtlasCoefficientFiber.quotientDualComplex_d0_apply
#print axioms AAT.AG.AtlasCoefficientFiber.quotientDualComplex_d1_apply
#print axioms AAT.AG.AtlasCoefficientFiber.quotientDualEquivOfRestriction
#print axioms AAT.AG.AtlasCoefficientFiber.quotientDualEquivOfRestriction_mk
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationQuotientDual0
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationQuotientDual1
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationQuotientDual2
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationQuotientDual0_mk
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationQuotientDual1_mk
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationQuotientDual2_mk
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationQuotientDual_comm0
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationQuotientDual_comm1
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationQuotientDualHom
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationQuotientDualHom_f0
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationQuotientDualHom_f1
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationQuotientDualHom_f2
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationQuotientDualHom_standard_isIso
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationQuotientDualStandardIso
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationQuotientDualStandardIso_hom
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
