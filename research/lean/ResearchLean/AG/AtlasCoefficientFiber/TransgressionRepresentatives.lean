import ResearchLean.AG.AtlasCoefficientFiber.FiveTermSequence
import ResearchLean.AG.AtlasCoefficientFiber.CochainRepresentatives
import ResearchLean.AG.AtlasCoefficientFiber.HomologyRepresentatives
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# G-135 B：実短完全列の連結射と原補正代表

標準δの代表射公式へ原ε・制限・補正cochainを渡す。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits CanonicalResolution ResolutionInvariance FaceRelationSubdivision
open AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 原補正cochainの微分を同じL₂へ制限すると零になる。 -/
theorem correctedEdgeCochain_d1_restriction_zero (z : VerticalCocycles M A)
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
    (hβ : (mixedHorizontalBoundary M A).dualMap β = -(mixedVerticalBoundary M A).dualMap z.1) :
    restriction2 M A ((Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).d1
      (correctedEdgeCochain M A z.1 β)) = 0 := by
  apply LinearMap.ext
  intro x
  rw [restriction2_apply, LinearMap.zero_apply]
  exact correctedEdgeCochain_d1_degenerate M A z β hβ x

/-- 原補正cochainの制限は同じQの閉代表になる。 -/
def correctedRestrictionCycle (z : VerticalCocycles M A)
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
    (hβ : (mixedHorizontalBoundary M A).dualMap β = -(mixedVerticalBoundary M A).dualMap z.1) :
    LinearMap.ker (restrictionComplex M A).d1 :=
  ⟨restriction1 M A (correctedEdgeCochain M A z.1 β), by
    rw [LinearMap.mem_ker, ← restriction_comm1]
    exact correctedEdgeCochain_d1_restriction_zero M A z β hβ⟩

/-- 原Q閉代表は同じ補正cochainの制限。 -/
@[simp] theorem correctedRestrictionCycle_val (z : VerticalCocycles M A)
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
    (hβ : (mixedHorizontalBoundary M A).dualMap β = -(mixedVerticalBoundary M A).dualMap z.1) :
    (correctedRestrictionCycle M A z β hβ).1 = restriction1 M A
      (correctedEdgeCochain M A z.1 β) := rfl

/-- 原短完全列のε全射性が補正微分のP₂原像を生成する。 -/
theorem correctedPushforwardCochain_exists (z : VerticalCocycles M A)
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
    (hβ : (mixedHorizontalBoundary M A).dualMap β = -(mixedVerticalBoundary M A).dualMap z.1) :
    ∃ p : (pushforwardComplex M A).C2, evaluation2 M A p =
      (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).d1
        (correctedEdgeCochain M A z.1 β) :=
  evaluation2_preimage_of_restriction_zero M A _
    (correctedEdgeCochain_d1_restriction_zero M A z β hβ)

/-- 元P₂の補正微分原像。 -/
def correctedPushforwardCochain (z : VerticalCocycles M A)
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
    (hβ : (mixedHorizontalBoundary M A).dualMap β = -(mixedVerticalBoundary M A).dualMap z.1) :
    (pushforwardComplex M A).C2 := Classical.choose (correctedPushforwardCochain_exists M A z β hβ)

/-- 選ばれたP₂原像をεで戻すと実補正微分である。 -/
theorem correctedPushforwardCochain_spec (z : VerticalCocycles M A)
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
    (hβ : (mixedHorizontalBoundary M A).dualMap β = -(mixedVerticalBoundary M A).dualMap z.1) :
    evaluation2 M A (correctedPushforwardCochain M A z β hβ) =
      (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).d1
        (correctedEdgeCochain M A z.1 β) :=
  Classical.choose_spec (correctedPushforwardCochain_exists M A z β hβ)

/-- 元の三項代表を使って、同じ実短完全列の標準δを計算する。 -/
theorem evaluationRestriction_connecting_representative
    (q : LinearMap.ker (restrictionComplex M A).d1)
    (w : (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).C1)
    (p : (pushforwardComplex M A).C2)
    (hq : restriction1 M A w = q.1)
    (hp : evaluation2 M A p =
      (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).d1 w) :
    (evaluationRestriction_shortExact M A).δ (1 : ℤ) 2 (by rfl)
      (oldH1Equiv (restrictionComplex M A) (Submodule.Quotient.mk q)) =
        oldH2Equiv (pushforwardComplex M A) (Submodule.Quotient.mk p) := by
  let x₃ : ModuleCat.of ℚ (ULift.{u} ℚ) ⟶ (zeroExtension (restrictionComplex M A)).X (1 : ℤ) :=
    elementArrow q.1
  let x₂ : ModuleCat.of ℚ (ULift.{u} ℚ) ⟶
      (zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).X (1 : ℤ) :=
    elementArrow w
  let x₁ : ModuleCat.of ℚ (ULift.{u} ℚ) ⟶ (zeroExtension (pushforwardComplex M A)).X (2 : ℤ) :=
    elementArrow p
  have hx₃ : x₃ ≫ (zeroExtension (restrictionComplex M A)).d 1 2 = 0 := by
    rw [show x₃ = elementArrow q.1 from rfl, elementArrow_comp]
    have hz : (zeroExtension (restrictionComplex M A)).d 1 2 q.1 = 0 := q.2
    rw [hz, elementArrow_zero]
  have hx₂ : x₂ ≫ (evaluationRestrictionShortComplex M A).g.f 1 = x₃ := by
    change elementArrow w ≫ (zeroExtensionMap (restrictionHom M A)).f 1 = elementArrow q.1
    rw [elementArrow_comp]
    exact congrArg (elementArrow (X := (zeroExtension (restrictionComplex M A)).X 1)) hq
  have hx₁ : x₁ ≫ (evaluationRestrictionShortComplex M A).f.f 2 =
      x₂ ≫ (zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).d 1 2 := by
    rw [show x₁ = elementArrow p from rfl, show x₂ = elementArrow w from rfl,
      elementArrow_comp, elementArrow_comp]
    exact congrArg (elementArrow (X := (zeroExtension
      (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).X 2)) hp
  have hh := (evaluationRestriction_shortExact M A).δ_eq (1 : ℤ) 2 (by rfl)
    x₃ hx₃ x₂ hx₂ x₁ hx₁ 3 (by simp)
  have he := congrArg (fun f => f (ULift.up (1 : ℚ))) hh
  have hxp : x₁ ≫ (zeroExtension (pushforwardComplex M A)).d 2 3 = 0 := by
    have hz := zeroExtension_d_zero (pushforwardComplex M A) 2 (by decide) (by decide)
    have hz' : (zeroExtension (pushforwardComplex M A)).d 2 3 = 0 := by simpa using hz
    rw [hz']
    simp only [comp_zero]
  change (evaluationRestriction_shortExact M A).δ (1 : ℤ) 2 (by rfl)
    ((zeroExtension (restrictionComplex M A)).homologyπ 1
      ((zeroExtension (restrictionComplex M A)).liftCycles x₃ 2 (by simp) hx₃
        (ULift.up (1 : ℚ)))) =
    (zeroExtension (pushforwardComplex M A)).homologyπ 2
      ((zeroExtension (pushforwardComplex M A)).liftCycles x₁ 3 (by simp) hxp
        (ULift.up (1 : ℚ))) at he
  rw [zeroExtension_liftCycles_H1_apply, zeroExtension_liftCycles_H2_apply] at he
  have hq1 : (ConcreteCategory.hom x₃) (ULift.up (1 : ℚ)) = q.1 := elementArrow_one _
  have hp1 : (ConcreteCategory.hom x₁) (ULift.up (1 : ℚ)) = p := elementArrow_one _
  simpa only [hq1, hp1] using he

/-- 実Q閉代表の原R座標は同じ補正付き垂直代表である。 -/
theorem correctedRestrictionCycle_fiberClass (z : VerticalCocycles M A)
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
    (hβ : (mixedHorizontalBoundary M A).dualMap β = -(mixedVerticalBoundary M A).dualMap z.1) :
    restrictionStandardHomologyREquiv M A
      (oldH1Equiv (restrictionComplex M A)
        (Submodule.Quotient.mk (correctedRestrictionCycle M A z β hβ))) =
      correctedFiberClass M A z β hβ := by
  apply (fiberRRawEquiv M A).injective
  rw [restrictionStandardHomologyREquiv_raw]
  apply Subtype.ext
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    rw [restrictionStandardHomologyRawREquiv_mk, correctedFiberClass_raw,
      verticalCocycleClass_mk, correctedRestrictionCycle_val, restriction1_apply,
      correctedEdgeCochain_dual, verticalCycleInclusion_val,
      correctedEdgeFunctional_vertical]

/-- 指定R上の実τは、原補正微分から生成されたP₂の同じ商類。 -/
theorem connectingTau_correctedFiberClass (z : VerticalCocycles M A)
    (β : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
    (hβ : (mixedHorizontalBoundary M A).dualMap β = -(mixedVerticalBoundary M A).dualMap z.1) :
    connectingTau M A (correctedFiberClass M A z β hβ) =
      oldH2Equiv (pushforwardComplex M A)
        (Submodule.Quotient.mk (correctedPushforwardCochain M A z β hβ)) := by
  rw [← correctedRestrictionCycle_fiberClass M A z β hβ,
    connectingTau_restrictionStandardHomologyREquiv]
  exact evaluationRestriction_connecting_representative M A _ _ _ rfl
    (correctedPushforwardCochain_spec M A z β hβ)

/-- 水平補正を選び直しても、実Rの類は同じ。 -/
theorem correctedFiberClass_independent_correction (z : VerticalCocycles M A)
    (β β' : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
    (hβ : (mixedHorizontalBoundary M A).dualMap β = -(mixedVerticalBoundary M A).dualMap z.1)
    (hβ' : (mixedHorizontalBoundary M A).dualMap β' = -(mixedVerticalBoundary M A).dualMap z.1) :
    correctedFiberClass M A z β hβ = correctedFiberClass M A z β' hβ' := by
  apply (fiberRRawEquiv M A).injective
  apply Subtype.ext
  rw [correctedFiberClass_raw, correctedFiberClass_raw]

/-- 水平補正を選び直しても、補正微分が定めるP₂商類は同じ。 -/
theorem correctedPushforwardCochain_independent_correction (z : VerticalCocycles M A)
    (β β' : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
    (hβ : (mixedHorizontalBoundary M A).dualMap β = -(mixedVerticalBoundary M A).dualMap z.1)
    (hβ' : (mixedHorizontalBoundary M A).dualMap β' = -(mixedVerticalBoundary M A).dualMap z.1) :
    (Submodule.Quotient.mk (correctedPushforwardCochain M A z β hβ) :
      (pushforwardComplex M A).C2 ⧸ LinearMap.range (pushforwardComplex M A).d1) =
        Submodule.Quotient.mk (correctedPushforwardCochain M A z β' hβ') := by
  apply (oldH2Equiv (pushforwardComplex M A)).injective
  rw [← connectingTau_correctedFiberClass, ← connectingTau_correctedFiberClass,
    correctedFiberClass_independent_correction M A z β β' hβ hβ']

/-- 垂直代表を原aのcoboundaryで変えても同じ垂直homology汎関数。 -/
theorem verticalCocycleClass_coboundary (z z' : VerticalCocycles M A)
    (γ : Module.Dual ℚ (K0 Nf (comparisonFactor qc qf h ⁻¹' A)))
    (hz : z'.1 = z.1 + (verticalEdgeBoundary M A).dualMap γ) :
    verticalCocycleClass M A z' = verticalCocycleClass M A z := by
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    rw [verticalCocycleClass_mk, verticalCocycleClass_mk, hz,
      LinearMap.add_apply, LinearMap.dualMap_apply,
      show verticalEdgeBoundary M A x.1 = 0 from x.2, map_zero, add_zero]

/-- 原coboundary変更と各水平補正を通して指定R類は同じ。 -/
theorem correctedFiberClass_coboundary (z z' : VerticalCocycles M A)
    (β β' : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
    (hβ : (mixedHorizontalBoundary M A).dualMap β = -(mixedVerticalBoundary M A).dualMap z.1)
    (hβ' : (mixedHorizontalBoundary M A).dualMap β' = -(mixedVerticalBoundary M A).dualMap z'.1)
    (γ : Module.Dual ℚ (K0 Nf (comparisonFactor qc qf h ⁻¹' A)))
    (hz : z'.1 = z.1 + (verticalEdgeBoundary M A).dualMap γ) :
    correctedFiberClass M A z' β' hβ' = correctedFiberClass M A z β hβ := by
  apply (fiberRRawEquiv M A).injective
  apply Subtype.ext
  rw [correctedFiberClass_raw, correctedFiberClass_raw, verticalCocycleClass_coboundary M A z z' γ hz]

/-- 原coboundary変更によって生成するP二次商類も同じ。 -/
theorem correctedPushforwardCochain_coboundary (z z' : VerticalCocycles M A)
    (β β' : Module.Dual ℚ (HorizontalEdge M A →₀ ℚ))
    (hβ : (mixedHorizontalBoundary M A).dualMap β = -(mixedVerticalBoundary M A).dualMap z.1)
    (hβ' : (mixedHorizontalBoundary M A).dualMap β' = -(mixedVerticalBoundary M A).dualMap z'.1)
    (γ : Module.Dual ℚ (K0 Nf (comparisonFactor qc qf h ⁻¹' A)))
    (hz : z'.1 = z.1 + (verticalEdgeBoundary M A).dualMap γ) :
    (Submodule.Quotient.mk (correctedPushforwardCochain M A z' β' hβ') :
      (pushforwardComplex M A).C2 ⧸ LinearMap.range (pushforwardComplex M A).d1) =
        Submodule.Quotient.mk (correctedPushforwardCochain M A z β hβ) := by
  apply (oldH2Equiv (pushforwardComplex M A)).injective
  rw [← connectingTau_correctedFiberClass, ← connectingTau_correctedFiberClass,
    correctedFiberClass_coboundary M A z z' β β' hβ hβ' γ hz]

/-- 任意の有限基底でτを行列評価し戻すと、同じ標準homology類になる。 -/
theorem connectingTau_basis_independent {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (bR : Module.Basis ι ℚ (R M A))
    (bP : Module.Basis κ ℚ ((zeroExtension (pushforwardComplex M A)).homology (2 : ℤ)))
    (r : R M A) :
    bP.equivFun.symm ((LinearMap.toMatrix bR bP (connectingTau M A)).mulVec (bR.equivFun r)) =
      connectingTau M A r := by
  rw [Module.Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr,
    ← Module.Basis.equivFun_apply, LinearEquiv.symm_apply_apply]

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.correctedEdgeCochain_d1_restriction_zero
#print axioms AAT.AG.AtlasCoefficientFiber.correctedRestrictionCycle
#print axioms AAT.AG.AtlasCoefficientFiber.correctedRestrictionCycle_val
#print axioms AAT.AG.AtlasCoefficientFiber.correctedPushforwardCochain_exists
#print axioms AAT.AG.AtlasCoefficientFiber.correctedPushforwardCochain
#print axioms AAT.AG.AtlasCoefficientFiber.correctedPushforwardCochain_spec
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationRestriction_connecting_representative
#print axioms AAT.AG.AtlasCoefficientFiber.correctedRestrictionCycle_fiberClass
#print axioms AAT.AG.AtlasCoefficientFiber.connectingTau_correctedFiberClass
#print axioms AAT.AG.AtlasCoefficientFiber.correctedFiberClass_independent_correction
#print axioms AAT.AG.AtlasCoefficientFiber.correctedPushforwardCochain_independent_correction
#print axioms AAT.AG.AtlasCoefficientFiber.verticalCocycleClass_coboundary
#print axioms AAT.AG.AtlasCoefficientFiber.correctedFiberClass_coboundary
#print axioms AAT.AG.AtlasCoefficientFiber.correctedPushforwardCochain_coboundary
#print axioms AAT.AG.AtlasCoefficientFiber.connectingTau_basis_independent
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
