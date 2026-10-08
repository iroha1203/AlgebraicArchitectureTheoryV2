import ResearchLean.AG.AtlasCoefficientFiber.FiveTermSequence
import ResearchLean.AG.AtlasCoefficientFiber.PushforwardEvaluation
import ResearchLean.AG.AtlasDefectComposition.ComparisonHomology
import ResearchLean.AG.AtlasDefectComposition.DefectSequence

/-!
# G-135 C：同じ実H¹射の核と後段余核

原ηと独立uから標準H¹射を作る。実εの単射性と原五項列の完全性を使い、
元を保つ核同型と原制限による余核同型を構成する。

## Implementation notes

実直接射を合成から定義する案は採らず、原uの標準homology射として先に生成する。
商同型は同じ実制限の核・像を通し、次元の一致だけで代替しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 同じ原ηの標準一次homology射a。 -/
def unitH1 : (zeroExtension (Nc.targetSubsetComplex A)).homology (1 : ℤ) →ₗ[ℚ]
    (zeroExtension (pushforwardComplex M A)).homology (1 : ℤ) :=
  (HomologicalComplex.homologyMap (zeroExtensionMap (unitHom M A)) 1).hom

/-- 独立な原uの標準一次homology射T。 -/
def directH1 : (zeroExtension (Nc.targetSubsetComplex A)).homology (1 : ℤ) →ₗ[ℚ]
    (zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology (1 : ℤ) :=
  (HomologicalComplex.homologyMap (zeroExtensionMap (M.aSubnerveComparisonHom A)) 1).hom

/-- aの所有評価API。 -/
@[simp] theorem unitH1_apply (x : (zeroExtension (Nc.targetSubsetComplex A)).homology (1 : ℤ)) :
    unitH1 M A x = HomologicalComplex.homologyMap (zeroExtensionMap (unitHom M A)) 1 x := rfl

/-- Tの所有評価API。 -/
@[simp] theorem directH1_apply (x : (zeroExtension (Nc.targetSubsetComplex A)).homology (1 : ℤ)) :
    directH1 M A x = HomologicalComplex.homologyMap
      (zeroExtensionMap (M.aSubnerveComparisonHom A)) 1 x := rfl

/-- aを標準homology mapとして読む所有等式API。 -/
theorem unitH1_eq_standard : unitH1 M A =
    (HomologicalComplex.homologyMap (zeroExtensionMap (unitHom M A)) 1).hom := rfl

/-- Tを標準homology mapとして読む所有等式API。 -/
theorem directH1_eq_standard : directH1 M A =
    (HomologicalComplex.homologyMap (zeroExtensionMap (M.aSubnerveComparisonHom A)) 1).hom := rfl

/-- 同じ独立uの全Hom因子化は標準一次homologyでT=H¹ε∘aとなる。 -/
theorem directH1_factor : directH1 M A = (evaluationH1 M A).comp (unitH1 M A) := by
  apply LinearMap.ext
  intro x
  rw [directH1_apply, aSubnerveComparisonHom_factorization M A, zeroExtensionMap_comp,
    HomologicalComplex.homologyMap_comp]
  rfl

/-- 同じ旧一次商の実比較と独立標準Tは可換に一致する。 -/
theorem directH1_old (x : (Nc.targetSubsetComplex A).H1) :
    directH1 M A (oldH1Equiv (Nc.targetSubsetComplex A) x) =
      oldH1Equiv (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))
        ((M.aSubnerveComparisonHom A).h1Map x) :=
  (oldH1Equiv_natural (M.aSubnerveComparisonHom A) x).symm

/-- 原ε単射性により、同じcoarseH¹内の核は部分空間として等しい。 -/
theorem directH1_kernel : LinearMap.ker (directH1 M A) = LinearMap.ker (unitH1 M A) := by
  ext x
  change directH1 M A x = 0 ↔ unitH1 M A x = 0
  rw [directH1_factor, LinearMap.comp_apply]
  constructor
  · intro hx
    exact evaluationH1_injective M A (hx.trans (map_zero _).symm)
  · intro hx
    rw [hx, map_zero]

section SameSubmodule
variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- 同じ部分空間の等号は元を保つ両方向線形同型を与える。 -/
def sameSubmoduleEquiv (p q : Submodule ℚ V) (hpq : p = q) : p ≃ₗ[ℚ] q :=
  LinearEquiv.ofEq p q hpq

/-- 部分空間同型は同じ原始元を読む。 -/
@[simp] theorem sameSubmoduleEquiv_val (p q : Submodule ℚ V) (hpq : p = q) (x : p) :
    (sameSubmoduleEquiv p q hpq x).1 = x.1 :=
  LinearEquiv.coe_ofEq_apply hpq x
end SameSubmodule

/-- 指定kerT≃keraは同じcoarseH¹の元を保つ。 -/
def directKernelUnitEquiv : LinearMap.ker (directH1 M A) ≃ₗ[ℚ] LinearMap.ker (unitH1 M A) :=
  sameSubmoduleEquiv _ _ (directH1_kernel M A)

/-- 核同型の原始元は恒等である。 -/
@[simp] theorem directKernelUnitEquiv_val (x : LinearMap.ker (directH1 M A)) :
    (directKernelUnitEquiv M A x).1 = x.1 := rfl

/-- 原五項列により同じfiber制限の核は実εの像。 -/
theorem fiberRestriction_kernel : LinearMap.ker (fiberRestrictionH1 M A) =
    LinearMap.range (evaluationH1 M A) :=
  LinearMap.exact_iff.mp (fiveTerm_exact_at_fineH1 M A)

/-- 原五項列により同じfiber制限の像は実τの核。 -/
theorem fiberRestriction_range : LinearMap.range (fiberRestrictionH1 M A) =
    LinearMap.ker (connectingTau M A) :=
  (LinearMap.exact_iff.mp (fiveTerm_exact_at_fiber M A)).symm

/-- 実εの余核から実τの核への原制限による同型。 -/
def evaluationCokernelTauKernelEquiv :
    ((zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology (1 : ℤ) ⧸
      LinearMap.range (evaluationH1 M A)) ≃ₗ[ℚ] LinearMap.ker (connectingTau M A) :=
  (Submodule.quotEquivOfEq _ _ (fiberRestriction_kernel M A).symm).trans
    ((fiberRestrictionH1 M A).quotKerEquivRange.trans
      (sameSubmoduleEquiv _ _ (fiberRestriction_range M A)))

/-- 後段余核同型は同じ原制限の全商代表を保存する。 -/
@[simp] theorem evaluationCokernelTauKernelEquiv_mk_val
    (x : (zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology (1 : ℤ)) :
    (evaluationCokernelTauKernelEquiv M A (Submodule.Quotient.mk x)).1 = fiberRestrictionH1 M A x := by
  simp only [evaluationCokernelTauKernelEquiv, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, sameSubmoduleEquiv_val, LinearMap.quotKerEquivRange_apply_mk]

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.unitH1
#print axioms AAT.AG.AtlasCoefficientFiber.directH1
#print axioms AAT.AG.AtlasCoefficientFiber.unitH1_apply
#print axioms AAT.AG.AtlasCoefficientFiber.directH1_apply
#print axioms AAT.AG.AtlasCoefficientFiber.unitH1_eq_standard
#print axioms AAT.AG.AtlasCoefficientFiber.directH1_eq_standard
#print axioms AAT.AG.AtlasCoefficientFiber.directH1_factor
#print axioms AAT.AG.AtlasCoefficientFiber.directH1_old
#print axioms AAT.AG.AtlasCoefficientFiber.directH1_kernel
#print axioms AAT.AG.AtlasCoefficientFiber.sameSubmoduleEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.sameSubmoduleEquiv_val
#print axioms AAT.AG.AtlasCoefficientFiber.directKernelUnitEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.directKernelUnitEquiv_val
#print axioms AAT.AG.AtlasCoefficientFiber.fiberRestriction_kernel
#print axioms AAT.AG.AtlasCoefficientFiber.fiberRestriction_range
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationCokernelTauKernelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.evaluationCokernelTauKernelEquiv_mk_val
#print axioms AAT.AG.AtlasCoefficientFiber.sameSubmoduleEquiv.congr_simp
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
