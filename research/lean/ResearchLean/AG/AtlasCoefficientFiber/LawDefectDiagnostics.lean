import ResearchLean.AG.AtlasCoefficientFiber.LawHomologyCoordinates
import ResearchLean.AG.AtlasCoefficientFiber.DefectDiagnostics

/-!
# G-135 D：同じLaw H¹比較の実余核列

## Implementation notes

独立生成Law Tと原Law aを同じH¹上に保つ。
G133の第四・第五射を同じLaw因子化へ適用し、原Law制限でkerτへ送る。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open AtlasDefectComposition
universe u
variable {Source : Type u} [Fintype Source]
variable {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)
variable (laws : FiniteLawFamily Source) (ha : laws.Adequate qc)

/-- 原ε単射性により、同じcoarseH¹内の核は部分空間として等しい。 -/
theorem lawDirectH1_kernel : LinearMap.ker (lawDirectH1 M laws ha) = LinearMap.ker (lawUnitH1 M laws ha) := by
  ext x
  change lawDirectH1 M laws ha x = 0 ↔ lawUnitH1 M laws ha x = 0
  rw [lawDirectH1_factor, LinearMap.comp_apply]
  constructor
  · intro hx
    exact lawEvaluationH1_injective M laws ha (hx.trans (map_zero _).symm)
  · intro hx
    rw [hx, map_zero]

/-- 指定kerT≃keraは同じcoarseH¹の元を保つ。 -/
def lawDirectKernelUnitEquiv : LinearMap.ker (lawDirectH1 M laws ha) ≃ₗ[ℚ] LinearMap.ker (lawUnitH1 M laws ha) :=
  sameSubmoduleEquiv _ _ (lawDirectH1_kernel M laws ha)

/-- 核同型の原始元は恒等である。 -/
@[simp] theorem lawDirectKernelUnitEquiv_val (x : LinearMap.ker (lawDirectH1 M laws ha)) :
    (lawDirectKernelUnitEquiv M laws ha x).1 = x.1 := rfl

/-- 原五項列により同じfiber制限の核は実εの像。 -/
theorem lawFiberRestriction_kernel : LinearMap.ker (lawFiberRestrictionH1 M laws ha) =
    LinearMap.range (lawEvaluationH1 M laws ha) :=
  LinearMap.exact_iff.mp (lawFiveTerm_exact_at_fineH1 M laws ha)

/-- 原五項列により同じfiber制限の像は実τの核。 -/
theorem lawFiberRestriction_range : LinearMap.range (lawFiberRestrictionH1 M laws ha) =
    LinearMap.ker (lawConnectingTau M laws ha) :=
  (LinearMap.exact_iff.mp (lawFiveTerm_exact_at_fiber M laws ha)).symm

/-- 実εの余核から実τの核への原制限による同型。 -/
def lawEvaluationCokernelTauKernelEquiv :
    ((zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).homology (1 : ℤ) ⧸
      LinearMap.range (lawEvaluationH1 M laws ha)) ≃ₗ[ℚ] LinearMap.ker (lawConnectingTau M laws ha) :=
  (Submodule.quotEquivOfEq _ _ (lawFiberRestriction_kernel M laws ha).symm).trans
    ((lawFiberRestrictionH1 M laws ha).quotKerEquivRange.trans
      (sameSubmoduleEquiv _ _ (lawFiberRestriction_range M laws ha)))

/-- 後段余核同型は同じ原制限の全商代表を保存する。 -/
@[simp] theorem lawEvaluationCokernelTauKernelEquiv_mk_val
    (x : (zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).homology (1 : ℤ)) :
    (lawEvaluationCokernelTauKernelEquiv M laws ha (Submodule.Quotient.mk x)).1 = lawFiberRestrictionH1 M laws ha x := by
  simp only [lawEvaluationCokernelTauKernelEquiv, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, sameSubmoduleEquiv_val, LinearMap.quotKerEquivRange_apply_mk]

/-- 同じ実εの一次核は零部分空間。 -/
theorem lawEvaluationH1_kernel : LinearMap.ker (lawEvaluationH1 M laws ha) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (lawEvaluationH1_injective M laws ha)

/-- G-133相殺は同じ二射において始域零から零となる。 -/
theorem lawCoefficientCancellation_zero : DefectSequence.cancellation (lawUnitH1 M laws ha) (lawEvaluationH1 M laws ha) = 0 := by
  apply LinearMap.ext
  intro x
  have hx : x = 0 := Subtype.ext (lawEvaluationH1_injective M laws ha (x.2.trans (map_zero _).symm))
  rw [hx, map_zero, LinearMap.zero_apply]

/-- 実因子化の等号による合成余核から独立直接余核への同型。 -/
def lawCompositeDirectCokernelEquiv :
    ((zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).homology (1 : ℤ) ⧸
      LinearMap.range ((lawEvaluationH1 M laws ha).comp (lawUnitH1 M laws ha))) ≃ₗ[ℚ]
    ((zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).homology (1 : ℤ) ⧸
      LinearMap.range (lawDirectH1 M laws ha)) :=
  Submodule.quotEquivOfEq _ _ (congrArg LinearMap.range (lawDirectH1_factor M laws ha)).symm

/-- 合成余核の同定は全原代表を保つ。 -/
@[simp] theorem lawCompositeDirectCokernelEquiv_mk
    (x : (zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).homology (1 : ℤ)) :
    lawCompositeDirectCokernelEquiv M laws ha (Submodule.Quotient.mk x) = Submodule.Quotient.mk x :=
  Submodule.quotEquivOfEq_mk _ _ _ _

/-- 逆余核同定も同じ原代表を保つ。 -/
@[simp] theorem lawCompositeDirectCokernelEquiv_symm_mk
    (x : (zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).homology (1 : ℤ)) :
    (lawCompositeDirectCokernelEquiv M laws ha).symm (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := by
  apply (lawCompositeDirectCokernelEquiv M laws ha).injective
  rw [LinearEquiv.apply_symm_apply, lawCompositeDirectCokernelEquiv_mk]

/-- 原係数差の余核を同じ独立Tの余核へ入れるG-133第四射。 -/
def lawCoefficientCokernelInclusion :
    ((zeroExtension (lawPushforwardComplex M laws ha)).homology (1 : ℤ) ⧸ LinearMap.range (lawUnitH1 M laws ha)) →ₗ[ℚ]
    ((zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).homology (1 : ℤ) ⧸
      LinearMap.range (lawDirectH1 M laws ha)) :=
  (lawCompositeDirectCokernelEquiv M laws ha).toLinearMap.comp
    (DefectSequence.fourth (lawUnitH1 M laws ha) (lawEvaluationH1 M laws ha))

/-- 余核包含の所有評価API。 -/
@[simp] theorem lawCoefficientCokernelInclusion_apply
    (x : (zeroExtension (lawPushforwardComplex M laws ha)).homology (1 : ℤ) ⧸ LinearMap.range (lawUnitH1 M laws ha)) :
    lawCoefficientCokernelInclusion M laws ha x = lawCompositeDirectCokernelEquiv M laws ha
      (DefectSequence.fourth (lawUnitH1 M laws ha) (lawEvaluationH1 M laws ha) x) := rfl

/-- 全係数余核代表は同じ実εの像の直接余核類へ入る。 -/
@[simp] theorem lawCoefficientCokernelInclusion_mk
    (x : (zeroExtension (lawPushforwardComplex M laws ha)).homology (1 : ℤ)) :
    lawCoefficientCokernelInclusion M laws ha (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (lawEvaluationH1 M laws ha x) := by
  change lawCompositeDirectCokernelEquiv M laws ha
    (DefectSequence.fourth _ _ ((LinearMap.range (lawUnitH1 M laws ha)).mkQ x)) = _
  rw [DefectSequence.fourth_mk, Submodule.mkQ_apply, lawCompositeDirectCokernelEquiv_mk]

/-- 同じ独立直接余核をG-133第五射と原制限でkerτへ送る。 -/
def lawTotalCokernelFiberProjection :
    ((zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).homology (1 : ℤ) ⧸
      LinearMap.range (lawDirectH1 M laws ha)) →ₗ[ℚ] LinearMap.ker (lawConnectingTau M laws ha) :=
  (lawEvaluationCokernelTauKernelEquiv M laws ha).toLinearMap.comp
    ((DefectSequence.fifth (lawUnitH1 M laws ha) (lawEvaluationH1 M laws ha)).comp
      (lawCompositeDirectCokernelEquiv M laws ha).symm.toLinearMap)

/-- fiber余核射の所有評価API。 -/
@[simp] theorem lawTotalCokernelFiberProjection_apply
    (x : (zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).homology (1 : ℤ) ⧸
      LinearMap.range (lawDirectH1 M laws ha)) :
    lawTotalCokernelFiberProjection M laws ha x = lawEvaluationCokernelTauKernelEquiv M laws ha
      (DefectSequence.fifth (lawUnitH1 M laws ha) (lawEvaluationH1 M laws ha) ((lawCompositeDirectCokernelEquiv M laws ha).symm x)) := rfl

/-- 全直接余核代表は同じ原fiber制限の値を返す。 -/
@[simp] theorem lawTotalCokernelFiberProjection_mk_val
    (x : (zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).homology (1 : ℤ)) :
    (lawTotalCokernelFiberProjection M laws ha (Submodule.Quotient.mk x)).1 = lawFiberRestrictionH1 M laws ha x := by
  change (lawEvaluationCokernelTauKernelEquiv M laws ha
    (DefectSequence.fifth _ _ ((lawCompositeDirectCokernelEquiv M laws ha).symm (Submodule.Quotient.mk x)))).1 = _
  rw [lawCompositeDirectCokernelEquiv_symm_mk]
  rw [show (Submodule.Quotient.mk x : _ ⧸ LinearMap.range ((lawEvaluationH1 M laws ha).comp (lawUnitH1 M laws ha))) =
    (LinearMap.range ((lawEvaluationH1 M laws ha).comp (lawUnitH1 M laws ha))).mkQ x from rfl,
    DefectSequence.fifth_mk, Submodule.mkQ_apply, lawEvaluationCokernelTauKernelEquiv_mk_val]

/-- 同じG-133第四射は原相殺零により単射。 -/
theorem lawCoefficientFourth_injective :
    Function.Injective (DefectSequence.fourth (lawUnitH1 M laws ha) (lawEvaluationH1 M laws ha)) := by
  intro x y hxy
  have hz : DefectSequence.fourth (lawUnitH1 M laws ha) (lawEvaluationH1 M laws ha) (x-y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨z, hz⟩ := (DefectSequence.exact_cancellation_fourth (lawUnitH1 M laws ha) (lawEvaluationH1 M laws ha) (x-y)).mp hz
  rw [lawCoefficientCancellation_zero, LinearMap.zero_apply] at hz
  exact sub_eq_zero.mp hz.symm

/-- 係数余核から実直接余核への射は単射。 -/
theorem lawCoefficientCokernelInclusion_injective : Function.Injective (lawCoefficientCokernelInclusion M laws ha) :=
  (lawCompositeDirectCokernelEquiv M laws ha).injective.comp (lawCoefficientFourth_injective M laws ha)

/-- 同じkerτへの実射は全射。 -/
theorem lawTotalCokernelFiberProjection_surjective : Function.Surjective (lawTotalCokernelFiberProjection M laws ha) :=
  (lawEvaluationCokernelTauKernelEquiv M laws ha).surjective.comp
    ((DefectSequence.fifth_surjective (lawUnitH1 M laws ha) (lawEvaluationH1 M laws ha)).comp
      (lawCompositeDirectCokernelEquiv M laws ha).symm.surjective)

/-- 指定余核短完全列の実二射は同じ直接余核で完全。 -/
theorem lawCoefficientCokernel_exact : Function.Exact (lawCoefficientCokernelInclusion M laws ha)
    (lawTotalCokernelFiberProjection M laws ha) := by
  intro x
  rw [lawTotalCokernelFiberProjection_apply]
  rw [← (lawEvaluationCokernelTauKernelEquiv M laws ha).map_zero,
    (lawEvaluationCokernelTauKernelEquiv M laws ha).injective.eq_iff]
  rw [DefectSequence.exact_fourth_fifth]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    rw [lawCoefficientCokernelInclusion_apply]
    rw [hy, LinearEquiv.apply_symm_apply]
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply (lawCompositeDirectCokernelEquiv M laws ha).injective
    rw [LinearEquiv.apply_symm_apply, ← lawCoefficientCokernelInclusion_apply]
    exact hy

/-- 指定余核SESの両端と全中間完全性。 -/
theorem lawCoefficientCokernel_shortExact :
    Function.Injective (lawCoefficientCokernelInclusion M laws ha) ∧
    Function.Exact (lawCoefficientCokernelInclusion M laws ha) (lawTotalCokernelFiberProjection M laws ha) ∧
    Function.Surjective (lawTotalCokernelFiberProjection M laws ha) :=
  ⟨lawCoefficientCokernelInclusion_injective M laws ha, lawCoefficientCokernel_exact M laws ha,
    lawTotalCokernelFiberProjection_surjective M laws ha⟩


/-- 同じ旧Law比較核から同じ原Law a核への元を保つ両方向同型。 -/
def lawOldKernelUnitEquiv : LinearMap.ker
    (M.generatedComparisonH1Map laws ha (lawFineAdequate (h := h) laws ha)) ≃ₗ[ℚ]
      LinearMap.ker (lawUnitH1 M laws ha) :=
  (LinearConjugation.kernelEquiv _ _ (lawOldCoarseH1Equiv (Nc := Nc) laws ha)
    (lawOldFineH1Equiv (Nf := Nf) (h := h) laws ha)
    (fun x => (lawDirectH1_old M laws ha x).symm)).trans (lawDirectKernelUnitEquiv M laws ha)

/-- 旧Law核同型は同じ旧coarse類の標準類を読む。 -/
theorem lawOldKernelUnitEquiv_val
    (x : LinearMap.ker (M.generatedComparisonH1Map laws ha (lawFineAdequate (h := h) laws ha))) :
    (lawOldKernelUnitEquiv M laws ha x).val = lawOldCoarseH1Equiv (Nc := Nc) laws ha x.val := rfl

/-- 同じ旧Law比較余核と同じ独立標準T余核の実両方向同型。 -/
def lawOldCokernelStandardEquiv :
    ((Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha)).H1 ⧸
      LinearMap.range (M.generatedComparisonH1Map laws ha (lawFineAdequate (h := h) laws ha))) ≃ₗ[ℚ]
    ((zeroExtension (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha))).homology (1 : ℤ) ⧸
      LinearMap.range (lawDirectH1 M laws ha)) :=
  LinearConjugation.cokernelEquiv _ _ (lawOldCoarseH1Equiv (Nc := Nc) laws ha)
    (lawOldFineH1Equiv (Nf := Nf) (h := h) laws ha)
    (fun x => (lawDirectH1_old M laws ha x).symm)

/-- 旧Law余核同型は全代表元を同じfine標準類へ送る。 -/
theorem lawOldCokernelStandardEquiv_mk
    (x : (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha)).H1) :
    lawOldCokernelStandardEquiv M laws ha (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (lawOldFineH1Equiv (Nf := Nf) (h := h) laws ha x) := rfl

/-- 原Law係数余核から同じ旧Law比較余核への実包含。 -/
def lawOldCoefficientCokernelInclusion :
    ((zeroExtension (lawPushforwardComplex M laws ha)).homology (1 : ℤ) ⧸ LinearMap.range (lawUnitH1 M laws ha)) →ₗ[ℚ]
    ((Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha)).H1 ⧸
      LinearMap.range (M.generatedComparisonH1Map laws ha (lawFineAdequate (h := h) laws ha))) :=
  (lawOldCokernelStandardEquiv M laws ha).symm.toLinearMap.comp (lawCoefficientCokernelInclusion M laws ha)

/-- 同じ旧Law比較余核から原Law kerτへの実射。 -/
def lawOldTotalCokernelFiberProjection :
    ((Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha)).H1 ⧸
      LinearMap.range (M.generatedComparisonH1Map laws ha (lawFineAdequate (h := h) laws ha))) →ₗ[ℚ]
      LinearMap.ker (lawConnectingTau M laws ha) :=
  (lawTotalCokernelFiberProjection M laws ha).comp (lawOldCokernelStandardEquiv M laws ha).toLinearMap

/-- 旧Law実包含は全P標準代表を同じ旧fine類へ送る。 -/
theorem lawOldCoefficientCokernelInclusion_mk
    (x : (zeroExtension (lawPushforwardComplex M laws ha)).homology (1 : ℤ)) :
    lawOldCoefficientCokernelInclusion M laws ha (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((lawOldFineH1Equiv (Nf := Nf) (h := h) laws ha).symm
        (lawEvaluationH1 M laws ha x)) := by
  apply (lawOldCokernelStandardEquiv M laws ha).injective
  change lawOldCokernelStandardEquiv M laws ha
    ((lawOldCokernelStandardEquiv M laws ha).symm (lawCoefficientCokernelInclusion M laws ha _)) = _
  rw [LinearEquiv.apply_symm_apply, lawCoefficientCokernelInclusion_mk,
    lawOldCokernelStandardEquiv_mk, LinearEquiv.apply_symm_apply]

/-- 旧Law実fiber余核射は全旧fine代表の同じ原制限値を返す。 -/
theorem lawOldTotalCokernelFiberProjection_mk_val
    (x : (Nf.lawGeneratedComplex laws (lawFineAdequate (h := h) laws ha)).H1) :
    (lawOldTotalCokernelFiberProjection M laws ha (Submodule.Quotient.mk x)).val =
      lawFiberRestrictionH1 M laws ha (lawOldFineH1Equiv (Nf := Nf) (h := h) laws ha x) := by
  change (lawTotalCokernelFiberProjection M laws ha
    (lawOldCokernelStandardEquiv M laws ha (Submodule.Quotient.mk x))).val = _
  rw [lawOldCokernelStandardEquiv_mk, lawTotalCokernelFiberProjection_mk_val]

/-- 同じ旧Law余核列の包含は単射。 -/
theorem lawOldCoefficientCokernelInclusion_injective : Function.Injective (lawOldCoefficientCokernelInclusion M laws ha) :=
  (lawOldCokernelStandardEquiv M laws ha).symm.injective.comp (lawCoefficientCokernelInclusion_injective M laws ha)

/-- 同じ旧Law余核列の原kerτ射は全射。 -/
theorem lawOldTotalCokernelFiberProjection_surjective : Function.Surjective (lawOldTotalCokernelFiberProjection M laws ha) :=
  (lawTotalCokernelFiberProjection_surjective M laws ha).comp (lawOldCokernelStandardEquiv M laws ha).surjective

/-- 同じ旧Law余核列は全中間元で完全。 -/
theorem lawOldCoefficientCokernel_exact : Function.Exact (lawOldCoefficientCokernelInclusion M laws ha)
    (lawOldTotalCokernelFiberProjection M laws ha) := by
  intro x
  change lawTotalCokernelFiberProjection M laws ha (lawOldCokernelStandardEquiv M laws ha x) = 0 ↔ _
  rw [lawCoefficientCokernel_exact]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    change (lawOldCokernelStandardEquiv M laws ha).symm (lawCoefficientCokernelInclusion M laws ha y) = x
    rw [hy, LinearEquiv.symm_apply_apply]
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply (lawOldCokernelStandardEquiv M laws ha).symm.injective
    rw [LinearEquiv.symm_apply_apply]
    exact hy

/-- 同じ旧Law比較余核と原Law係数・fiberの短完全列。 -/
theorem lawOldCoefficientCokernel_shortExact :
    Function.Injective (lawOldCoefficientCokernelInclusion M laws ha) ∧
    Function.Exact (lawOldCoefficientCokernelInclusion M laws ha) (lawOldTotalCokernelFiberProjection M laws ha) ∧
    Function.Surjective (lawOldTotalCokernelFiberProjection M laws ha) :=
  ⟨lawOldCoefficientCokernelInclusion_injective M laws ha, lawOldCoefficientCokernel_exact M laws ha,
    lawOldTotalCokernelFiberProjection_surjective M laws ha⟩

omit [Fintype Source] in
/-- 原各ラベル余核の二寄与は同じ原a余核と原τ核である。 -/
theorem coefficient_cokernel_sum (A : Set qc.Target) :
    (blockDefect (M.aSubnerveComparisonHom A).h1Map).2 =
    Module.finrank ℚ ((zeroExtension (pushforwardComplex M A)).homology (1 : ℤ) ⧸ LinearMap.range (unitH1 M A)) +
      Module.finrank ℚ (LinearMap.ker (connectingTau M A)) := by
  rw [← directH1_defect, blockDefect_cokernel_dimension,
    coefficientSixTerm_cokernel_dimension, (evaluationCokernelTauKernelEquiv M A).finrank_eq]

/-- 同じ旧Law blockDefectの両成分は全発生ラベルの原係数・fiber寄与の和。 -/
theorem lawCoefficientBlockDefect_sum :
    blockDefect (M.generatedComparisonH1Map laws ha (lawFineAdequate (h := h) laws ha)) =
    (∑ l : LawValueLabel laws, Module.finrank ℚ (LinearMap.ker (unitH1 M (labelValueFiber laws qc ha l))),
      ∑ l : LawValueLabel laws,
        (Module.finrank ℚ ((zeroExtension (pushforwardComplex M (labelValueFiber laws qc ha l))).homology (1 : ℤ) ⧸
          LinearMap.range (unitH1 M (labelValueFiber laws qc ha l))) +
        Module.finrank ℚ (LinearMap.ker (connectingTau M (labelValueFiber laws qc ha l))))) := by
  rw [AAT.AG.FaceRelationSubdivision.lawH1Defect_subset_sum]
  simp only [coefficient_kernel_dimension, coefficient_cokernel_sum]

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.lawDirectH1_kernel
#print axioms AAT.AG.AtlasCoefficientFiber.lawDirectKernelUnitEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.lawDirectKernelUnitEquiv_val
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberRestriction_kernel
#print axioms AAT.AG.AtlasCoefficientFiber.lawFiberRestriction_range
#print axioms AAT.AG.AtlasCoefficientFiber.lawEvaluationCokernelTauKernelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.lawEvaluationCokernelTauKernelEquiv_mk_val
#print axioms AAT.AG.AtlasCoefficientFiber.lawEvaluationH1_kernel
#print axioms AAT.AG.AtlasCoefficientFiber.lawCoefficientCancellation_zero
#print axioms AAT.AG.AtlasCoefficientFiber.lawCompositeDirectCokernelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.lawCompositeDirectCokernelEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.lawCompositeDirectCokernelEquiv_symm_mk
#print axioms AAT.AG.AtlasCoefficientFiber.lawCoefficientCokernelInclusion
#print axioms AAT.AG.AtlasCoefficientFiber.lawCoefficientCokernelInclusion_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawCoefficientCokernelInclusion_mk
#print axioms AAT.AG.AtlasCoefficientFiber.lawTotalCokernelFiberProjection
#print axioms AAT.AG.AtlasCoefficientFiber.lawTotalCokernelFiberProjection_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lawTotalCokernelFiberProjection_mk_val
#print axioms AAT.AG.AtlasCoefficientFiber.lawCoefficientFourth_injective
#print axioms AAT.AG.AtlasCoefficientFiber.lawCoefficientCokernelInclusion_injective
#print axioms AAT.AG.AtlasCoefficientFiber.lawTotalCokernelFiberProjection_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.lawCoefficientCokernel_exact
#print axioms AAT.AG.AtlasCoefficientFiber.lawCoefficientCokernel_shortExact
#print axioms AAT.AG.AtlasCoefficientFiber.lawOldKernelUnitEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.lawOldKernelUnitEquiv_val
#print axioms AAT.AG.AtlasCoefficientFiber.lawOldCokernelStandardEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.lawOldCokernelStandardEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.lawOldCoefficientCokernelInclusion
#print axioms AAT.AG.AtlasCoefficientFiber.lawOldTotalCokernelFiberProjection
#print axioms AAT.AG.AtlasCoefficientFiber.lawOldCoefficientCokernelInclusion_mk
#print axioms AAT.AG.AtlasCoefficientFiber.lawOldTotalCokernelFiberProjection_mk_val
#print axioms AAT.AG.AtlasCoefficientFiber.lawOldCoefficientCokernelInclusion_injective
#print axioms AAT.AG.AtlasCoefficientFiber.lawOldTotalCokernelFiberProjection_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.lawOldCoefficientCokernel_exact
#print axioms AAT.AG.AtlasCoefficientFiber.lawOldCoefficientCokernel_shortExact
#print axioms AAT.AG.AtlasCoefficientFiber.coefficient_cokernel_sum
#print axioms AAT.AG.AtlasCoefficientFiber.lawCoefficientBlockDefect_sum
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
