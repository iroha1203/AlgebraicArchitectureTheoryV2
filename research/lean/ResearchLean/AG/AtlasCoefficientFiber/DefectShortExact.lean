import ResearchLean.AG.AtlasCoefficientFiber.DefectMaps

/-!
# G-135 C：実余核短完全列と相殺零

G-133の同じ二射の第四・第五射を独立Tの余核へ等号輸送する。
最後の余核は原制限によるkerτ同型へ送り、全代表と完全性を保つ。

## Implementation notes

同次元の対象を選んで写像を作る案は採らない。各商は同じ実射のrange quotient、
輸送は証明済みT因子化だけを使う。相殺の始域はkerH¹εでありRではない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 同じ実εの一次核は零部分空間。 -/
theorem evaluationH1_kernel : LinearMap.ker (evaluationH1 M A) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (evaluationH1_injective M A)

/-- G-133相殺は同じ二射において始域零から零となる。 -/
theorem coefficientCancellation_zero : DefectSequence.cancellation (unitH1 M A) (evaluationH1 M A) = 0 := by
  apply LinearMap.ext
  intro x
  have hx : x = 0 := Subtype.ext (evaluationH1_injective M A (x.2.trans (map_zero _).symm))
  rw [hx, map_zero, LinearMap.zero_apply]

/-- 実因子化の等号による合成余核から独立直接余核への同型。 -/
def compositeDirectCokernelEquiv :
    ((zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology (1 : ℤ) ⧸
      LinearMap.range ((evaluationH1 M A).comp (unitH1 M A))) ≃ₗ[ℚ]
    ((zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology (1 : ℤ) ⧸
      LinearMap.range (directH1 M A)) :=
  Submodule.quotEquivOfEq _ _ (congrArg LinearMap.range (directH1_factor M A)).symm

/-- 合成余核の同定は全原代表を保つ。 -/
@[simp] theorem compositeDirectCokernelEquiv_mk
    (x : (zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology (1 : ℤ)) :
    compositeDirectCokernelEquiv M A (Submodule.Quotient.mk x) = Submodule.Quotient.mk x :=
  Submodule.quotEquivOfEq_mk _ _ _ _

/-- 逆余核同定も同じ原代表を保つ。 -/
@[simp] theorem compositeDirectCokernelEquiv_symm_mk
    (x : (zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology (1 : ℤ)) :
    (compositeDirectCokernelEquiv M A).symm (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := by
  apply (compositeDirectCokernelEquiv M A).injective
  rw [LinearEquiv.apply_symm_apply, compositeDirectCokernelEquiv_mk]

/-- 原係数差の余核を同じ独立Tの余核へ入れるG-133第四射。 -/
def coefficientCokernelInclusion :
    ((zeroExtension (pushforwardComplex M A)).homology (1 : ℤ) ⧸ LinearMap.range (unitH1 M A)) →ₗ[ℚ]
    ((zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology (1 : ℤ) ⧸
      LinearMap.range (directH1 M A)) :=
  (compositeDirectCokernelEquiv M A).toLinearMap.comp
    (DefectSequence.fourth (unitH1 M A) (evaluationH1 M A))

/-- 余核包含の所有評価API。 -/
@[simp] theorem coefficientCokernelInclusion_apply
    (x : (zeroExtension (pushforwardComplex M A)).homology (1 : ℤ) ⧸ LinearMap.range (unitH1 M A)) :
    coefficientCokernelInclusion M A x = compositeDirectCokernelEquiv M A
      (DefectSequence.fourth (unitH1 M A) (evaluationH1 M A) x) := rfl

/-- 全係数余核代表は同じ実εの像の直接余核類へ入る。 -/
@[simp] theorem coefficientCokernelInclusion_mk
    (x : (zeroExtension (pushforwardComplex M A)).homology (1 : ℤ)) :
    coefficientCokernelInclusion M A (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (evaluationH1 M A x) := by
  change compositeDirectCokernelEquiv M A
    (DefectSequence.fourth _ _ ((LinearMap.range (unitH1 M A)).mkQ x)) = _
  rw [DefectSequence.fourth_mk, Submodule.mkQ_apply, compositeDirectCokernelEquiv_mk]

/-- 同じ独立直接余核をG-133第五射と原制限でkerτへ送る。 -/
def totalCokernelFiberProjection :
    ((zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology (1 : ℤ) ⧸
      LinearMap.range (directH1 M A)) →ₗ[ℚ] LinearMap.ker (connectingTau M A) :=
  (evaluationCokernelTauKernelEquiv M A).toLinearMap.comp
    ((DefectSequence.fifth (unitH1 M A) (evaluationH1 M A)).comp
      (compositeDirectCokernelEquiv M A).symm.toLinearMap)

/-- fiber余核射の所有評価API。 -/
@[simp] theorem totalCokernelFiberProjection_apply
    (x : (zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology (1 : ℤ) ⧸
      LinearMap.range (directH1 M A)) :
    totalCokernelFiberProjection M A x = evaluationCokernelTauKernelEquiv M A
      (DefectSequence.fifth (unitH1 M A) (evaluationH1 M A) ((compositeDirectCokernelEquiv M A).symm x)) := rfl

/-- 全直接余核代表は同じ原fiber制限の値を返す。 -/
@[simp] theorem totalCokernelFiberProjection_mk_val
    (x : (zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology (1 : ℤ)) :
    (totalCokernelFiberProjection M A (Submodule.Quotient.mk x)).1 = fiberRestrictionH1 M A x := by
  change (evaluationCokernelTauKernelEquiv M A
    (DefectSequence.fifth _ _ ((compositeDirectCokernelEquiv M A).symm (Submodule.Quotient.mk x)))).1 = _
  rw [compositeDirectCokernelEquiv_symm_mk]
  rw [show (Submodule.Quotient.mk x : _ ⧸ LinearMap.range ((evaluationH1 M A).comp (unitH1 M A))) =
    (LinearMap.range ((evaluationH1 M A).comp (unitH1 M A))).mkQ x from rfl,
    DefectSequence.fifth_mk, Submodule.mkQ_apply, evaluationCokernelTauKernelEquiv_mk_val]

/-- 同じG-133第四射は原相殺零により単射。 -/
theorem coefficientFourth_injective :
    Function.Injective (DefectSequence.fourth (unitH1 M A) (evaluationH1 M A)) := by
  intro x y hxy
  have hz : DefectSequence.fourth (unitH1 M A) (evaluationH1 M A) (x-y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨z, hz⟩ := (DefectSequence.exact_cancellation_fourth (unitH1 M A) (evaluationH1 M A) (x-y)).mp hz
  rw [coefficientCancellation_zero, LinearMap.zero_apply] at hz
  exact sub_eq_zero.mp hz.symm

/-- 係数余核から実直接余核への射は単射。 -/
theorem coefficientCokernelInclusion_injective : Function.Injective (coefficientCokernelInclusion M A) :=
  (compositeDirectCokernelEquiv M A).injective.comp (coefficientFourth_injective M A)

/-- 同じkerτへの実射は全射。 -/
theorem totalCokernelFiberProjection_surjective : Function.Surjective (totalCokernelFiberProjection M A) :=
  (evaluationCokernelTauKernelEquiv M A).surjective.comp
    ((DefectSequence.fifth_surjective (unitH1 M A) (evaluationH1 M A)).comp
      (compositeDirectCokernelEquiv M A).symm.surjective)

/-- 指定余核短完全列の実二射は同じ直接余核で完全。 -/
theorem coefficientCokernel_exact : Function.Exact (coefficientCokernelInclusion M A)
    (totalCokernelFiberProjection M A) := by
  intro x
  rw [totalCokernelFiberProjection_apply]
  rw [← (evaluationCokernelTauKernelEquiv M A).map_zero,
    (evaluationCokernelTauKernelEquiv M A).injective.eq_iff]
  rw [DefectSequence.exact_fourth_fifth]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [coefficientCokernelInclusion_apply]
    rw [hy, LinearEquiv.apply_symm_apply]
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply (compositeDirectCokernelEquiv M A).injective
    rw [LinearEquiv.apply_symm_apply, ← coefficientCokernelInclusion_apply]
    exact hy

/-- 指定余核SESの両端と全中間完全性。 -/
theorem coefficientCokernel_shortExact :
    Function.Injective (coefficientCokernelInclusion M A) ∧
    Function.Exact (coefficientCokernelInclusion M A) (totalCokernelFiberProjection M A) ∧
    Function.Surjective (totalCokernelFiberProjection M A) :=
  ⟨coefficientCokernelInclusion_injective M A, coefficientCokernel_exact M A,
    totalCokernelFiberProjection_surjective M A⟩

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.evaluationH1_kernel
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCancellation_zero
#print axioms AAT.AG.AtlasCoefficientFiber.compositeDirectCokernelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.compositeDirectCokernelEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.compositeDirectCokernelEquiv_symm_mk
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCokernelInclusion
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCokernelInclusion_apply
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCokernelInclusion_mk
#print axioms AAT.AG.AtlasCoefficientFiber.totalCokernelFiberProjection
#print axioms AAT.AG.AtlasCoefficientFiber.totalCokernelFiberProjection_apply
#print axioms AAT.AG.AtlasCoefficientFiber.totalCokernelFiberProjection_mk_val
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientFourth_injective
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCokernelInclusion_injective
#print axioms AAT.AG.AtlasCoefficientFiber.totalCokernelFiberProjection_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCokernel_exact
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientCokernel_shortExact
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
