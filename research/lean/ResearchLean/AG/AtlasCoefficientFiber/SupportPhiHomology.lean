import ResearchLean.AG.AtlasCoefficientFiber.SupportPhiRestriction
import ResearchLean.AG.AtlasCoefficientFiber.SupportVerticalHomology

/-!
# G-135 D：同じ原Φ閉路商の台包含

## Implementation notes

同じ原Φ chain包含を原閉路と微分像へ制限して実商写像を作る。
局所双対の自然性は両側の同じ閉cochain・閉chain代表で検証する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) {A B : Set qc.Target} (hab : A ⊆ B)
variable (c : Nc.ChartInTargetSubset A)

/-- 原Φ閉路を同じ自由辺chain包含で含める。 -/
def supportPhiCycles : phiCycles M A c →ₗ[ℚ]
    phiCycles M B (supportCellInclude Nc.chartSupport hab c) :=
  ((supportPhiChain1 M hab c).comp (phiCycles M A c).subtype).codRestrict _ (fun x => by
    change phiBoundary1 M B _ (supportPhiChain1 M hab c x.1) = 0
    have hh := LinearMap.congr_fun (supportPhiChain_boundary1 M hab c) x.1
    change supportPhiChain0 M hab c (phiBoundary1 M A c x.1) = _ at hh
    exact hh.symm.trans (by rw [show phiBoundary1 M A c x.1 = 0 from x.2, map_zero]))

/-- 原Φ閉路包含の値は同じ原chain包含。 -/
@[simp] theorem supportPhiCycles_val (x : phiCycles M A c) :
    (supportPhiCycles M hab c x).1 = supportPhiChain1 M hab c x.1 := rfl

/-- 原Φ第二微分の実像を同じ原面chain包含で保つ。 -/
theorem supportPhiBoundaryToCycles (x : PhiFace M A c →₀ ℚ) :
    supportPhiCycles M hab c (phiBoundaryToCycles M A c x) =
      phiBoundaryToCycles M B (supportCellInclude Nc.chartSupport hab c) (supportPhiChain2 M hab c x) := by
  apply Subtype.ext
  exact LinearMap.congr_fun (supportPhiChain_boundary2 M hab c) x

/-- 原Φ閉路包含を同じ一次homology商へ降ろす。 -/
def supportPhiHomology : PhiHomology M A c →ₗ[ℚ]
    PhiHomology M B (supportCellInclude Nc.chartSupport hab c) :=
  Submodule.mapQ _ _ (supportPhiCycles M hab c) (fun x hx => by
    obtain ⟨t, rfl⟩ := hx
    exact ⟨supportPhiChain2 M hab c t, (supportPhiBoundaryToCycles M hab c t).symm⟩)

/-- 同じ原Φ一次homology包含の全代表式。 -/
@[simp] theorem supportPhiHomology_mk (x : phiCycles M A c) :
    supportPhiHomology M hab c (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (supportPhiCycles M hab c x) := Submodule.mapQ_apply _ _ _ x

/-- 元のΦ cochain H¹とchain H₁の双対は同じ代表包含・制限に対して自然。 -/
theorem supportPhiHomologyDual
    (z : (phiComplex M B (supportCellInclude Nc.chartSupport hab c)).H1)
    (x : PhiHomology M A c) :
    phiHomologyDualEquiv M A c ((supportPhiHom M hab c).h1Map z) x =
      phiHomologyDualEquiv M B (supportCellInclude Nc.chartSupport hab c) z
        (supportPhiHomology M hab c x) := by
  induction z using Submodule.Quotient.induction_on with
  | _ z =>
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      rw [supportPhiH1_mk, supportPhiHomology_mk, phiHomologyDualEquiv_mk, phiHomologyDualEquiv_mk]
      rw [TwoPhase.ThreeCochainComplex.Hom.cyclesMap_apply, supportPhiHom_f1]
      change freeDualEquiv _ (supportPhi1 M hab c z.1) x.1 =
        freeDualEquiv _ z.1 (supportPhiChain1 M hab c x.1)
      exact supportPhi1_dual M hab c z.1 x.1

/-- 全原Φ一次homologyの台包含は同じ原垂直H₁包含の両方向座標を読む。 -/
def supportAllPhiHomology :
    ((c : Nc.ChartInTargetSubset A) → PhiHomology M A c) →ₗ[ℚ]
      ((c : Nc.ChartInTargetSubset B) → PhiHomology M B c) :=
  (verticalHomologyPhiEquiv M B).toLinearMap.comp
    ((supportVerticalHomology M hab).comp (verticalHomologyPhiEquiv M A).symm.toLinearMap)

/-- 全原Φ一次homology包含の一般値は同じ原垂直H₁包含の両方向座標。 -/
theorem supportAllPhiHomology_apply
    (x : (c : Nc.ChartInTargetSubset A) → PhiHomology M A c) :
    supportAllPhiHomology M hab x = verticalHomologyPhiEquiv M B
      (supportVerticalHomology M hab ((verticalHomologyPhiEquiv M A).symm x)) := rfl

/-- 全原Φ一次homology包含は元の垂直閉路の全代表を含める。 -/
theorem supportAllPhiHomology_mk (x : verticalCycles M A) :
    supportAllPhiHomology M hab (verticalHomologyPhiEquiv M A (Submodule.Quotient.mk x)) =
      verticalHomologyPhiEquiv M B (Submodule.Quotient.mk (supportVerticalCyclesInclude M hab x)) := by
  change verticalHomologyPhiEquiv M B
    (supportVerticalHomology M hab ((verticalHomologyPhiEquiv M A).symm
      (verticalHomologyPhiEquiv M A (Submodule.Quotient.mk x)))) = _
  rw [LinearEquiv.symm_apply_apply, supportVerticalHomology_mk]

/-- 実κは同じ全原Φ H₁の包含と原混在閉路包含に対して自然。 -/
theorem supportKappa (x : mixedCycles M A) :
    supportAllPhiHomology M hab (kappa M A x) =
      kappa M B (supportMixedCyclesInclude M hab x) := by
  rw [kappa_apply, supportAllPhiHomology_mk, kappa_apply, supportMixedCycleToVertical]

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiCycles
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiCycles_val
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiBoundaryToCycles
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiHomology
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiHomology_mk
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiHomologyDual
#print axioms AAT.AG.AtlasCoefficientFiber.supportAllPhiHomology
#print axioms AAT.AG.AtlasCoefficientFiber.supportAllPhiHomology_apply
#print axioms AAT.AG.AtlasCoefficientFiber.supportAllPhiHomology_mk
#print axioms AAT.AG.AtlasCoefficientFiber.supportKappa
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
