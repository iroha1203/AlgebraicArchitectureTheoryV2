import ResearchLean.AG.AtlasCoefficientFiber.DegenerateHomology
import ResearchLean.AG.AtlasCoefficientFiber.ChainHomologyDual
import ResearchLean.AG.AtlasCoefficientFiber.FiberCohomology

/-!
# G-135 B §1：実Qの標準H¹と原始κ双対の核

Φの直和との同定前の垂直homology表示を使い、同じL・Q・κを接続する。

## Implementation notes

原Lのchain homology双対、実cokerκの双対、実κ*の核を標準同型で合成する。
Rを期待次元から構成する案は、同じ写像への接続を与えないため採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
open AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 同じ原始κの双対核。全Φ表示への同定前の実部分空間。 -/
abbrev RawR := LinearMap.ker (rawKappa M A).dualMap

/-- κ像をannihilateする汎関数とκ双対核を同じ値で同定する。 -/
def rawKappaAnnihilatorEquiv : (LinearMap.range (rawKappa M A)).dualAnnihilator ≃ₗ[ℚ] RawR M A where
  toFun z := ⟨z.1, by
    change z.1 ∈ LinearMap.ker (rawKappa M A).dualMap
    rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range]
    exact z.2⟩
  invFun z := ⟨z.1, by
    rw [← LinearMap.ker_dualMap_eq_dualAnnihilator_range]
    exact z.2⟩
  left_inv z := rfl
  right_inv z := rfl
  map_add' x y := rfl
  map_smul' r x := rfl

/-- κ余核の双対を同じκ双対の核へ両方向に移す。 -/
def rawKappaCokernelDualEquiv :
    Module.Dual ℚ (VerticalHomology M A ⧸ LinearMap.range (rawKappa M A)) ≃ₗ[ℚ] RawR M A :=
  (LinearMap.range (rawKappa M A)).dualQuotEquivDualAnnihilator.trans
    (rawKappaAnnihilatorEquiv M A)

/-- 同型は垂直homology代表の商類での評価を読む。 -/
@[simp] theorem rawKappaCokernelDualEquiv_apply (z : Module.Dual ℚ
    (VerticalHomology M A ⧸ LinearMap.range (rawKappa M A))) (x : VerticalHomology M A) :
    (rawKappaCokernelDualEquiv M A z).1 x = z (Submodule.Quotient.mk x) := rfl

/-- 同じ実Lの一次homologyと、独立構成QのH¹の双対同定。 -/
def restrictionHomologyDualEquiv : (restrictionComplex M A).H1 ≃ₗ[ℚ]
    Module.Dual ℚ (DegenerateHomology M A) :=
  chainHomologyDualEquiv (degenerateBoundary1 M A) (degenerateBoundary2 M A)
    (degenerateBoundary_square M A)

/-- 原垂直包含によるH₁L≅coker κから、同じ標準H¹Q≅ker κ*を得る。 -/
def restrictionStandardHomologyRawREquiv :
    (zeroExtension (restrictionComplex M A)).homology (1 : ℤ) ≃ₗ[ℚ] RawR M A :=
  (oldH1Equiv (restrictionComplex M A)).symm.trans
    ((restrictionHomologyDualEquiv M A).trans
      ((rawKappaCokernelHomologyEquiv M A).dualMap.trans (rawKappaCokernelDualEquiv M A)))

/-- 指定Rは全Φ cochain H¹上のκ*核であり、実標準H¹Qに両方向同型。 -/
def restrictionStandardHomologyREquiv :
    (zeroExtension (restrictionComplex M A)).homology (1 : ℤ) ≃ₗ[ℚ] R M A :=
  (restrictionStandardHomologyRawREquiv M A).trans (fiberRRawEquiv M A).symm

/-- 標準H¹Qから原Rへの同定は同じ原垂直閉路で評価する。 -/
@[simp] theorem restrictionStandardHomologyRawREquiv_mk
    (z : LinearMap.ker (restrictionComplex M A).d1) (x : verticalCycles M A) :
    (restrictionStandardHomologyRawREquiv M A
      (oldH1Equiv (restrictionComplex M A) (Submodule.Quotient.mk z))).1
      (Submodule.Quotient.mk x) = z.1 (verticalCycleInclusion M A x).1 := by
  simp only [restrictionStandardHomologyRawREquiv, LinearEquiv.trans_apply,
    LinearEquiv.symm_apply_apply]
  rw [rawKappaCokernelDualEquiv_apply]
  change restrictionHomologyDualEquiv M A (Submodule.Quotient.mk z)
    (rawKappaCokernelHomologyEquiv M A
      (Submodule.Quotient.mk (Submodule.Quotient.mk x))) = _
  rw [rawKappaCokernelHomologyEquiv_mk]
  exact chainHomologyDualEquiv_mk _ _ _ z (verticalCycleInclusion M A x)

/-- 指定全Φ座標を原垂直座標へ戻すと同じ実R同型である。 -/
@[simp] theorem restrictionStandardHomologyREquiv_raw
    (z : (zeroExtension (restrictionComplex M A)).homology (1 : ℤ)) :
    fiberRRawEquiv M A (restrictionStandardHomologyREquiv M A z) =
      restrictionStandardHomologyRawREquiv M A z := by
  change fiberRRawEquiv M A ((fiberRRawEquiv M A).symm
    (restrictionStandardHomologyRawREquiv M A z)) = _
  exact (fiberRRawEquiv M A).apply_symm_apply _

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.RawR
#print axioms AAT.AG.AtlasCoefficientFiber.rawKappaAnnihilatorEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.rawKappaCokernelDualEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.rawKappaCokernelDualEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.restrictionHomologyDualEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.restrictionStandardHomologyRawREquiv
#print axioms AAT.AG.AtlasCoefficientFiber.restrictionStandardHomologyREquiv
#print axioms AAT.AG.AtlasCoefficientFiber.restrictionStandardHomologyRawREquiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.restrictionStandardHomologyREquiv_raw
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
