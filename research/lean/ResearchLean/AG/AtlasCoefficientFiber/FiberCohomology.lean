import ResearchLean.AG.AtlasCoefficientFiber.FiberHomology
import ResearchLean.AG.UniformInvariance.UniformityReduction

/-!
# G-135 B §1：同じΦ cochain H¹上のfiber適合

有限直和双対はLinearMap.lsum、各Φのhomology双対は同じ原微分から構成する。

## Implementation notes

有限な粗chart添字では有限直和をPiで表示し、mathlibのlsumでその双対を移す。
Rは独立に生成したκの双対の核とし、全Φ空間そのものを一般のfiber項にする案は
混在関係を失うため採用しない。
-/
noncomputable section
open scoped Classical
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 原Φ cochainは、同じ原Φ chain微分の有限双対と可換に同型。 -/
def phiDualCochainEquiv (c : Nc.ChartInTargetSubset A) : ThreeCochainComplex.CochainEquiv
    (phiComplex M A c)
    (chainDualComplex (phiBoundary1 M A c) (phiBoundary2 M A c)
      (phiBoundary1_comp_phiBoundary2 M A c)) where
  e0 := freeDualEquiv _
  e1 := freeDualEquiv _
  e2 := freeDualEquiv _
  comm0 z := by
    apply LinearMap.ext
    intro x
    exact (phiBoundary1_dual M A c z x).symm
  comm1 z := by
    apply LinearMap.ext
    intro x
    exact (phiBoundary2_dual M A c z x).symm

/-- 原Φの実H¹商と同じchain H₁双対の両方向同型。 -/
def phiHomologyDualEquiv (c : Nc.ChartInTargetSubset A) :
    (phiComplex M A c).H1 ≃ₗ[ℚ] Module.Dual ℚ (PhiHomology M A c) :=
  (phiDualCochainEquiv M A c).h1Equiv.trans
    (chainHomologyDualEquiv (phiBoundary1 M A c) (phiBoundary2 M A c)
      (phiBoundary1_comp_phiBoundary2 M A c))

/-- 原Φの双対同定は同じ閉cochainと閉chainの代表を評価する。 -/
@[simp] theorem phiHomologyDualEquiv_mk (c : Nc.ChartInTargetSubset A)
    (z : LinearMap.ker (phiComplex M A c).d1) (x : phiCycles M A c) :
    phiHomologyDualEquiv M A c (Submodule.Quotient.mk z) (Submodule.Quotient.mk x) =
      freeDualEquiv _ z.1 x.1 := rfl

/-- 全ΦのH¹の有限直和を、同じ全Φ chain H₁の双対へ移す。 -/
def allPhiHomologyDualEquiv :
    ((c : Nc.ChartInTargetSubset A) → (phiComplex M A c).H1) ≃ₗ[ℚ]
      Module.Dual ℚ ((c : Nc.ChartInTargetSubset A) → PhiHomology M A c) := by
  classical
  letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
  exact (LinearEquiv.piCongrRight (phiHomologyDualEquiv M A)).trans
    (LinearMap.lsum ℚ _ ℚ)

/-- 全Φ双対の値は同じ有限添字上の成分評価の和。 -/
theorem allPhiHomologyDualEquiv_apply
    (z : (c : Nc.ChartInTargetSubset A) → (phiComplex M A c).H1)
    (x : (c : Nc.ChartInTargetSubset A) → PhiHomology M A c) :
    letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
    allPhiHomologyDualEquiv M A z x =
      ∑ c : Nc.ChartInTargetSubset A, phiHomologyDualEquiv M A c (z c) (x c) := by
  classical
  letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
  simp only [allPhiHomologyDualEquiv, LinearEquiv.trans_apply,
    LinearEquiv.piCongrRight_apply, LinearMap.lsum_apply,
    LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]

/-- 全Φ双対は元の一つのfiber類でその成分だけを評価する。 -/
theorem allPhiHomologyDualEquiv_single
    (z : (c : Nc.ChartInTargetSubset A) → (phiComplex M A c).H1)
    (c : Nc.ChartInTargetSubset A) (x : PhiHomology M A c) :
    allPhiHomologyDualEquiv M A z (Pi.single c x) = phiHomologyDualEquiv M A c (z c) x := by
  classical
  letI := Fintype.ofFinite (Nc.ChartInTargetSubset A)
  simp only [allPhiHomologyDualEquiv, LinearEquiv.trans_apply]
  exact LinearMap.lsum_piSingle ℚ _ ℚ _ c x

/-- 同じ全ΦのH¹と原垂直H₁双対の両方向同型。 -/
def phiCohomologyVerticalDualEquiv :
    ((c : Nc.ChartInTargetSubset A) → (phiComplex M A c).H1) ≃ₗ[ℚ]
      Module.Dual ℚ (VerticalHomology M A) :=
  (allPhiHomologyDualEquiv M A).trans (verticalHomologyPhiEquiv M A).dualMap

/-- 原垂直双対座標は同じ全Φ H₁座標で評価する。 -/
theorem phiCohomologyVerticalDualEquiv_apply
    (z : (c : Nc.ChartInTargetSubset A) → (phiComplex M A c).H1)
    (x : VerticalHomology M A) :
    phiCohomologyVerticalDualEquiv M A z x =
      allPhiHomologyDualEquiv M A z (verticalHomologyPhiEquiv M A x) := rfl

/-- 設計のκ*。実κの双対を同じΦ cochain H¹表示へ移す。 -/
def kappaStar : ((c : Nc.ChartInTargetSubset A) → (phiComplex M A c).H1) →ₗ[ℚ]
    Module.Dual ℚ (mixedCycles M A) :=
  (kappa M A).dualMap.comp (allPhiHomologyDualEquiv M A).toLinearMap

/-- κ*は同じ混在閉路Dy上の全Φ代表評価である。 -/
@[simp] theorem kappaStar_apply (z : (c : Nc.ChartInTargetSubset A) → (phiComplex M A c).H1)
    (y : mixedCycles M A) :
    kappaStar M A z y = allPhiHomologyDualEquiv M A z (kappa M A y) := rfl

/-- 全Φ表示と垂直表示のκ双対は、独立に生成された同じκから一致する。 -/
theorem kappaStar_raw : kappaStar M A = (rawKappa M A).dualMap.comp
    (phiCohomologyVerticalDualEquiv M A).toLinearMap := rfl

/-- 設計のRは同じ全Φ cochain H¹の中の実κ*核。 -/
abbrev R := LinearMap.ker (kappaStar M A)

/-- Rの公開核同定。下流では実κ*をこのAPIで使用する。 -/
theorem fiberR_eq_ker : R M A = LinearMap.ker (kappaStar M A) := rfl

section KernelTransport
variable {X Y Z : Type u} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]
variable [Module ℚ X] [Module ℚ Y] [Module ℚ Z]

/-- 可逆座標同定による核の両方向移送。同じfのkernelを保つ。 -/
def kernelEquivOfEquiv (e : X ≃ₗ[ℚ] Y) (f : Y →ₗ[ℚ] Z) :
    LinearMap.ker (f.comp e.toLinearMap) ≃ₗ[ℚ] LinearMap.ker f where
  toFun x := ⟨e x.1, x.2⟩
  invFun y := ⟨e.symm y.1, by
    change f (e (e.symm y.1)) = 0
    rw [e.apply_symm_apply]
    exact y.2⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)
  map_add' x y := Subtype.ext (e.map_add x.1 y.1)
  map_smul' r x := Subtype.ext (e.map_smul r x.1)
end KernelTransport

/-- 全Φ上の同じκ*核は、原垂直表示のκ双対核へ両方向に移る。 -/
def fiberRRawEquiv : R M A ≃ₗ[ℚ] LinearMap.ker (rawKappa M A).dualMap :=
  kernelEquivOfEquiv (phiCohomologyVerticalDualEquiv M A) (rawKappa M A).dualMap

/-- Rの同定は、同じ垂直閉路の代表評価を使う。 -/
@[simp] theorem fiberRRawEquiv_val (z : R M A) :
    (fiberRRawEquiv M A z).1 = phiCohomologyVerticalDualEquiv M A z.1 := rfl

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.phiDualCochainEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.phiHomologyDualEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.phiHomologyDualEquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.allPhiHomologyDualEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.allPhiHomologyDualEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.allPhiHomologyDualEquiv_single
#print axioms AAT.AG.AtlasCoefficientFiber.phiCohomologyVerticalDualEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.phiCohomologyVerticalDualEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.kappaStar
#print axioms AAT.AG.AtlasCoefficientFiber.kappaStar_apply
#print axioms AAT.AG.AtlasCoefficientFiber.kappaStar_raw
#print axioms AAT.AG.AtlasCoefficientFiber.R
#print axioms AAT.AG.AtlasCoefficientFiber.fiberR_eq_ker
#print axioms AAT.AG.AtlasCoefficientFiber.kernelEquivOfEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.fiberRRawEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.fiberRRawEquiv_val
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
