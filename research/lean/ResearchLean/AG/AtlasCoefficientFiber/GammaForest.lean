import ResearchLean.AG.AtlasCoefficientFiber.GammaChains
import ResearchLean.AG.AtlasCoefficientFiber.NamedForest
import ResearchLean.AG.AtlasCoefficientFiber.RestrictionHomology

/-!
# G-135 B §1：原Γ forestからの全fiber H¹特殊化

Γの全非交和を同じmapped辺名・混在面名で表示する。
forest条件は非空有限辺部分集合のleaf条件であり、線形閉路の零性を入力にしない。

## Implementation notes

同じΓの非交和を元の辺名で表示し、各有限辺集合のleaf条件を適用する。
SimpleGraphへの変換はloopと平行辺を失うため採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
open AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 原Γ全体の無向多重グラフ。元mapped辺・混在面を名前のまま使用。 -/
abbrev gammaUndirectedGraph := namedUndirectedGraph (mixedGraphSource M A) (mixedGraphTarget M A)

/-- loop・平行辺を残した原Γ全体の無向forest条件。 -/
abbrev GammaForest := NamedForest (mixedGraphSource M A) (mixedGraphTarget M A)

/-- forestなら原Γ incidence Bの核が零。結論は原グラフから導く。 -/
theorem mixedHorizontalBoundary_ker_eq_bot (hF : GammaForest M A) :
    LinearMap.ker (mixedHorizontalBoundary M A) = ⊥ := by
  ext x
  change mixedHorizontalBoundary M A x = 0 ↔ x = 0
  rw [mixedHorizontalBoundary_eq_incidence]
  exact namedIncidence_eq_zero_iff (mixedGraphSource M A) (mixedGraphTarget M A) hF x

/-- 原Γ forestでは全混在閉路は零である。 -/
theorem mixedCycle_eq_zero (hF : GammaForest M A) (y : mixedCycles M A) : y = 0 := by
  apply Subtype.ext
  have hy : y.1 ∈ LinearMap.ker (mixedHorizontalBoundary M A) := y.2
  rw [mixedHorizontalBoundary_ker_eq_bot M A hF] at hy
  exact hy

/-- forestの実κは始域の原閉路零性から零。 -/
theorem rawKappa_eq_zero_of_forest (hF : GammaForest M A) : rawKappa M A = 0 := by
  apply LinearMap.ext
  intro y
  rw [mixedCycle_eq_zero M A hF y, map_zero, LinearMap.zero_apply]

/-- 全Φ表示へ移した同じκも零。 -/
theorem kappa_eq_zero_of_forest (hF : GammaForest M A) : kappa M A = 0 := by
  apply LinearMap.ext
  intro y
  rw [mixedCycle_eq_zero M A hF y, map_zero, LinearMap.zero_apply]

/-- 原Γ forestでは、同じ実κ*が零。 -/
theorem kappaStar_eq_zero_of_forest (hF : GammaForest M A) : kappaStar M A = 0 := by
  apply LinearMap.ext
  intro z
  apply LinearMap.ext
  intro y
  rw [kappaStar_apply, LinearMap.congr_fun (kappa_eq_zero_of_forest M A hF)]
  simp only [LinearMap.zero_apply, map_zero]

/-- Rは原Γ forestの場合に全Φ cochain H¹空間そのものとなる。 -/
theorem fiberR_eq_top_of_forest (hF : GammaForest M A) : R M A = ⊤ := by
  rw [fiberR_eq_ker, kappaStar_eq_zero_of_forest M A hF, LinearMap.ker_zero]

/-- 原Γ forestから、同じRと全Φ H¹有限直和の両方向同型。 -/
def forestFiberREquiv (hF : GammaForest M A) : R M A ≃ₗ[ℚ]
    ((c : Nc.ChartInTargetSubset A) → (phiComplex M A c).H1) :=
  LinearEquiv.ofBijective (R M A).subtype ⟨(R M A).injective_subtype, fun z =>
    ⟨⟨z, by rw [fiberR_eq_top_of_forest M A hF]; trivial⟩, rfl⟩⟩

/-- 同型は同じ全Φ cochain H¹の値を保つ。 -/
@[simp] theorem forestFiberREquiv_apply (hF : GammaForest M A) (z : R M A) :
    forestFiberREquiv M A hF z = z.1 := rfl

/-- 指定Qの標準H¹を、原Γ forestの全Φ cochain H¹へ両方向に同定。 -/
def forestRestrictionHomologyEquiv (hF : GammaForest M A) :
    (zeroExtension (restrictionComplex M A)).homology (1 : ℤ) ≃ₗ[ℚ]
      ((c : Nc.ChartInTargetSubset A) → (phiComplex M A c).H1) :=
  (restrictionStandardHomologyREquiv M A).trans (forestFiberREquiv M A hF)

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.gammaUndirectedGraph
#print axioms AAT.AG.AtlasCoefficientFiber.GammaForest
#print axioms AAT.AG.AtlasCoefficientFiber.mixedHorizontalBoundary_ker_eq_bot
#print axioms AAT.AG.AtlasCoefficientFiber.mixedCycle_eq_zero
#print axioms AAT.AG.AtlasCoefficientFiber.rawKappa_eq_zero_of_forest
#print axioms AAT.AG.AtlasCoefficientFiber.kappa_eq_zero_of_forest
#print axioms AAT.AG.AtlasCoefficientFiber.kappaStar_eq_zero_of_forest
#print axioms AAT.AG.AtlasCoefficientFiber.fiberR_eq_top_of_forest
#print axioms AAT.AG.AtlasCoefficientFiber.forestFiberREquiv
#print axioms AAT.AG.AtlasCoefficientFiber.forestFiberREquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.forestRestrictionHomologyEquiv
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
