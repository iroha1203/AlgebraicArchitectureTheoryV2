import ResearchLean.AG.AtlasCoefficientFiber.TauDuality

/-!
# G-135 B：原始行列によるτ消滅の必要十分条件

標準τの同じ原鎖連結写像との双対同定を使い、原By=Hxの像包含へ戻す。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 原始行列のBy=Hxに対するD像包含条件。 -/
def PrimitiveTransgressionVanishing : Prop :=
  ∀ (x : HorizontalFace M A →₀ ℚ) (y : MixedFace M A →₀ ℚ),
    mixedHorizontalBoundary M A y = horizontalFaceBoundary M A x →
      ∃ (v : VerticalFace M A →₀ ℚ) (t : mixedCycles M A),
        verticalBoundary M A v + mixedVerticalBoundary M A t.1 = mixedVerticalBoundary M A y

/-- 同じ原鎖連結写像の零性を、原始像包含と両方向に同定する。 -/
theorem horizontalChainConnecting_zero_iff_primitive :
    horizontalChainConnecting M A = 0 ↔ PrimitiveTransgressionVanishing M A := by
  rw [horizontalChainConnecting_eq_zero_iff]
  constructor
  · intro hh x y hy
    obtain ⟨v, t, he⟩ := (mem_verticalRelations M A _).mp (hh x y hy)
    refine ⟨-v, -t, ?_⟩
    have he' : verticalBoundary M A v + mixedVerticalBoundary M A t.1 =
        -mixedVerticalBoundary M A y := he
    simp only [map_neg, Submodule.coe_neg]
    have hn := congrArg Neg.neg he'
    simpa only [neg_add, neg_neg] using hn
  · intro hh x y hy
    obtain ⟨v, t, he⟩ := hh x y hy
    apply (mem_verticalRelations M A _).mpr
    refine ⟨-v, -t, ?_⟩
    simp only [map_neg, Submodule.coe_neg, horizontalLiftCycle_val]
    simpa only [neg_add] using congrArg Neg.neg he

/-- 標準τの零性と同じ原鎖連結写像の零性が同値。 -/
theorem connectingTau_zero_iff_chain :
    connectingTau M A = 0 ↔ horizontalChainConnecting M A = 0 := by
  constructor
  · intro hh
    apply LinearMap.ext
    intro x
    apply (Module.forall_dual_apply_eq_zero_iff ℚ _).mp
    intro ψ
    obtain ⟨r, hr⟩ := (fiberRelationsDualEquiv M A).surjective ψ
    have he := congrArg (fun f => f x) (connectingTau_chain_duality M A r)
    rw [hh, LinearMap.zero_apply, map_zero] at he
    simpa only [LinearMap.dualMap_apply, hr, LinearMap.zero_apply] using he.symm
  · intro hh
    apply LinearMap.ext
    intro r
    apply (pushforwardStandardH2HorizontalDualEquiv M A).injective
    rw [LinearMap.zero_apply, map_zero, connectingTau_chain_duality]
    apply LinearMap.ext
    intro x
    rw [LinearMap.dualMap_apply, hh, LinearMap.zero_apply, map_zero, LinearMap.zero_apply]

/-- 固定Aのτ消滅は原By=HxのD像包含と必要十分。 -/
theorem connectingTau_zero_iff_primitive :
    connectingTau M A = 0 ↔ PrimitiveTransgressionVanishing M A :=
  (connectingTau_zero_iff_chain M A).trans (horizontalChainConnecting_zero_iff_primitive M A)

/-- 全支持Aでのτ消滅も同じ原始行列条件の全A検査と必要十分。 -/
theorem connectingTau_allA_zero_iff_primitive :
    (∀ A : Set qc.Target, connectingTau M A = 0) ↔
      ∀ A : Set qc.Target, PrimitiveTransgressionVanishing M A := by
  exact forall_congr' (fun A => connectingTau_zero_iff_primitive M A)

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.PrimitiveTransgressionVanishing
#print axioms AAT.AG.AtlasCoefficientFiber.horizontalChainConnecting_zero_iff_primitive
#print axioms AAT.AG.AtlasCoefficientFiber.connectingTau_zero_iff_chain
#print axioms AAT.AG.AtlasCoefficientFiber.connectingTau_zero_iff_primitive
#print axioms AAT.AG.AtlasCoefficientFiber.connectingTau_allA_zero_iff_primitive
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
