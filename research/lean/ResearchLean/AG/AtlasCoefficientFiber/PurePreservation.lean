import ResearchLean.AG.AtlasCoefficientFiber.PureComparison
import ResearchLean.AG.AtlasCoefficientFiber.DefectDiagnostics
import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# G-135 C：pure保存の必要十分条件と全AのC3′

## Implementation notes

原混在面が空という幾何条件からκ・τ零を生成し、Rを標準ofTopで全Φへ移す。
混在入力のRを全Φと読み替えず、pure条件の下でのみ両方向を証明する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 宣言上の垂直辺が空なら、原Φの一次cochainとその実H¹商は零になる。 -/
theorem phiH1_subsingleton_of_edges_isEmpty (c : Nc.ChartInTargetSubset A)
    [IsEmpty (PhiEdge M A c)] : Subsingleton (phiComplex M A c).H1 := by
  letI := phiComplex_C1_subsingleton M A c
  infer_instance

/-- 全Φ積の零性は各実Φ H¹の零性と必要十分で、空chart域も含む。 -/
theorem allPhiH1_subsingleton_iff :
    Subsingleton ((c : Nc.ChartInTargetSubset A) → (phiComplex M A c).H1) ↔
      ∀ c : Nc.ChartInTargetSubset A, Subsingleton (phiComplex M A c).H1 := by
  constructor
  · intro hp c
    letI := hp
    exact (Function.surjective_eval (β := fun c : Nc.ChartInTargetSubset A =>
      (phiComplex M A c).H1) c).subsingleton
  · intro hz
    letI : ∀ c : Nc.ChartInTargetSubset A, Subsingleton (phiComplex M A c).H1 := hz
    infer_instance

variable [IsEmpty (MixedFace M A)]

/-- 原mixed面が空なら、同じκ*は零である。 -/
theorem pure_kappaStar_zero : kappaStar M A = 0 := by
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro y
  rw [kappaStar_apply, LinearMap.congr_fun (kappa_zero_of_mixed_isEmpty A M)]
  simp only [LinearMap.zero_apply, map_zero]

/-- pure原入力から実Rは全Φ空間の全体となる。 -/
theorem pure_fiberR_eq_top : R M A = ⊤ := by
  rw [fiberR_eq_ker, pure_kappaStar_zero, LinearMap.ker_zero]

/-- pure Rと全Φ H¹積を、元を保持して標準部分空間同型で同定する。 -/
def pureFiberREquiv : R M A ≃ₗ[ℚ]
    ((c : Nc.ChartInTargetSubset A) → (phiComplex M A c).H1) :=
  LinearEquiv.ofTop (R M A) (pure_fiberR_eq_top M A)

/-- pure R同型の順写像は同じ全Φの値である。 -/
@[simp] theorem pureFiberREquiv_apply (z : R M A) :
    pureFiberREquiv M A z = z.1 := LinearEquiv.ofTop_apply _ _

/-- pure R同型の逆写像も同じ全Φの値を保つ。 -/
@[simp] theorem pureFiberREquiv_symm_val
    (z : (c : Nc.ChartInTargetSubset A) → (phiComplex M A c).H1) :
    ((pureFiberREquiv M A).symm z).1 = z := LinearEquiv.coe_ofTop_symm_apply _ _

/-- pure τは零なので、その単射性は全実Φ H¹零と必要十分である。 -/
theorem pure_connectingTau_injective_iff : Function.Injective (connectingTau M A) ↔
    ∀ c : Nc.ChartInTargetSubset A, Subsingleton (phiComplex M A c).H1 := by
  rw [← allPhiH1_subsingleton_iff, ← (pureFiberREquiv M A).toEquiv.subsingleton_congr]
  constructor
  · intro hi
    refine ⟨fun x y => hi ?_⟩
    rw [connectingTau_zero_of_mixed_isEmpty A M]
    rfl
  · intro hz
    letI := hz
    exact Function.injective_of_subsingleton _

/-- pure J零 iff 原a同型かつ全Φ H¹零、同じ旧比較の両方向である。 -/
theorem pure_zeroDefect_iff : blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0) ↔
    Function.Bijective (unitH1 M A) ∧
      ∀ c : Nc.ChartInTargetSubset A, Subsingleton (phiComplex M A c).H1 := by
  rw [coefficient_zeroDefect_iff, pure_connectingTau_injective_iff]

/-- 有限ℚ係数でのpure保存条件を、各Φの実finrank零としても読む。 -/
theorem pure_zeroDefect_finrank_iff :
    blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0) ↔
    Function.Bijective (unitH1 M A) ∧
      ∀ c : Nc.ChartInTargetSubset A, Module.finrank ℚ (phiComplex M A c).H1 = 0 := by
  simpa only [Module.finrank_zero_iff] using pure_zeroDefect_iff M A

omit [IsEmpty (MixedFace M A)] in
/-- 全Aへ量化したpure C3′と係数保存は、同じ全A旧診断零に必要十分である。 -/
theorem pure_allA_zeroDefect_iff (hPure : ∀ A : Set qc.Target, IsEmpty (MixedFace M A)) :
    (∀ A : Set qc.Target, blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0)) ↔
    (∀ A : Set qc.Target, Function.Bijective (unitH1 M A) ∧
      ∀ c : Nc.ChartInTargetSubset A, Subsingleton (phiComplex M A c).H1) := by
  apply forall_congr'
  intro A
  letI := hPure A
  exact pure_zeroDefect_iff M A

omit [IsEmpty (MixedFace M A)] in
/-- 全A保存から、非空Aとその全粗chartで新C3′の実H¹零を導く。 -/
theorem pure_C3prime_of_allA_zeroDefect
    (hPure : ∀ A : Set qc.Target, IsEmpty (MixedFace M A))
    (hJ : ∀ A : Set qc.Target, blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0)) :
    ∀ A : Set qc.Target, A.Nonempty →
      ∀ c : Nc.ChartInTargetSubset A, Subsingleton (phiComplex M A c).H1 := by
  intro A _
  exact ((pure_allA_zeroDefect_iff M hPure).mp hJ A).2

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.phiH1_subsingleton_of_edges_isEmpty
#print axioms AAT.AG.AtlasCoefficientFiber.allPhiH1_subsingleton_iff
#print axioms AAT.AG.AtlasCoefficientFiber.pure_kappaStar_zero
#print axioms AAT.AG.AtlasCoefficientFiber.pure_fiberR_eq_top
#print axioms AAT.AG.AtlasCoefficientFiber.pureFiberREquiv
#print axioms AAT.AG.AtlasCoefficientFiber.pureFiberREquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.pureFiberREquiv_symm_val
#print axioms AAT.AG.AtlasCoefficientFiber.pure_connectingTau_injective_iff
#print axioms AAT.AG.AtlasCoefficientFiber.pure_zeroDefect_iff
#print axioms AAT.AG.AtlasCoefficientFiber.pure_zeroDefect_finrank_iff
#print axioms AAT.AG.AtlasCoefficientFiber.pure_allA_zeroDefect_iff
#print axioms AAT.AG.AtlasCoefficientFiber.pure_C3prime_of_allA_zeroDefect
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
