import ResearchLean.AG.AtlasCoefficientFiber.SupportPhiHomology

/-!
# G-135 D：一つの原Φ閉路を同じ垂直閉路へ含める

## Implementation notes

元Φ辺の名前を垂直辺に戻して自由chainへ延長し、全Φ表示の単一成分と照合する。
この包含と台包含の可換性は全辺基底で証明する。
-/
noncomputable section
open scoped Classical
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)

/-- 原Φ自由辺chainを同じ原垂直辺へ含める。 -/
def supportPhiVerticalEmbed (A : Set qc.Target) (c : Nc.ChartInTargetSubset A) :
    (PhiEdge M A c →₀ ℚ) →ₗ[ℚ] (VerticalEdge M A →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (fun e => ⟨e.1, e.2.1⟩)

/-- 原Φ辺包含の全基底値。 -/
@[simp] theorem supportPhiVerticalEmbed_single (A : Set qc.Target) (c : Nc.ChartInTargetSubset A)
    (e : PhiEdge M A c) (r : ℚ) :
    supportPhiVerticalEmbed M A c (Finsupp.single e r) = Finsupp.single ⟨e.1, e.2.1⟩ r :=
  Finsupp.mapDomain_single

/-- 原Φ辺包含は全Φ表示の同じ単一成分に一致する。 -/
theorem supportPhiVerticalEmbed_coordinates (A : Set qc.Target) (c : Nc.ChartInTargetSubset A)
    (x : PhiEdge M A c →₀ ℚ) :
    phiChainEquiv1 M A (supportPhiVerticalEmbed M A c x) = Pi.single c x := by
  classical
  have hh : (phiChainEquiv1 M A).toLinearMap.comp (supportPhiVerticalEmbed M A c) =
      LinearMap.single ℚ (fun d => PhiEdge M A d →₀ ℚ) c := by
    apply Finsupp.lhom_ext
    intro e r
    change phiChainEquiv1 M A (supportPhiVerticalEmbed M A c (Finsupp.single e r)) =
      Pi.single c (Finsupp.single e r)
    rw [supportPhiVerticalEmbed_single]
    funext d
    by_cases hd : d = c
    · subst d
      rw [phiChainEquiv1_single_same, Pi.single_eq_same]
    · rw [phiChainEquiv1_single_other M A _ r d (fun he => hd (he.symm.trans e.2.2)),
        Pi.single_eq_of_ne hd]
  exact LinearMap.congr_fun hh x

/-- 原Φ閉路を同じ全Φ閉路座標の単一成分から垂直閉路へ戻す。 -/
def supportPhiVerticalCycles (A : Set qc.Target) (c : Nc.ChartInTargetSubset A) :
    phiCycles M A c →ₗ[ℚ] verticalCycles M A :=
  (phiVerticalCyclesEquiv M A).symm.toLinearMap.comp
    (LinearMap.single ℚ (fun d => phiCycles M A d) c)

/-- 原Φ閉路包含の値は同じ自由辺chain包含。 -/
@[simp] theorem supportPhiVerticalCycles_val (A : Set qc.Target) (c : Nc.ChartInTargetSubset A)
    (x : phiCycles M A c) :
    (supportPhiVerticalCycles M A c x).1 = supportPhiVerticalEmbed M A c x.1 := by
  classical
  apply (phiChainEquiv1 M A).injective
  rw [supportPhiVerticalEmbed_coordinates]
  funext d
  have hh := congrFun ((phiVerticalCyclesEquiv M A).apply_symm_apply (Pi.single c x)) d
  have hv := congrArg Subtype.val hh
  rw [phiVerticalCyclesEquiv_val] at hv
  change phiChainEquiv1 M A (supportPhiVerticalCycles M A c x).1 d = (((Pi.single c x : (d : Nc.ChartInTargetSubset A) → phiCycles M A d) d)).1 at hv
  refine hv.trans ?_
  by_cases hd : d = c
  · subst d
    simp
  · simp [hd]

/-- 原Φの単一homology類を全Φ表示から戻すと同じ垂直閉路の類になる。 -/
theorem supportPhiVerticalHomology_mk (A : Set qc.Target) (c : Nc.ChartInTargetSubset A)
    (x : phiCycles M A c) :
    (verticalHomologyPhiEquiv M A).symm (Pi.single c (Submodule.Quotient.mk x)) =
      Submodule.Quotient.mk (supportPhiVerticalCycles M A c x) := by
  classical
  apply (verticalHomologyPhiEquiv M A).injective
  rw [LinearEquiv.apply_symm_apply]
  funext d
  rw [verticalHomologyPhiEquiv_mk]
  have hh := congrFun ((phiVerticalCyclesEquiv M A).apply_symm_apply (Pi.single c x)) d
  change phiVerticalCyclesEquiv M A (supportPhiVerticalCycles M A c x) d = ((Pi.single c x : (d : Nc.ChartInTargetSubset A) → phiCycles M A d) d) at hh
  rw [hh]
  by_cases hd : d = c
  · subst d
    simp
  · simp [hd]

variable {A B : Set qc.Target} (hab : A ⊆ B) (c : Nc.ChartInTargetSubset A)

/-- 同じ原Φ自由辺包含は台包含と全基底で可換。 -/
theorem supportPhiVerticalEmbed_include (x : PhiEdge M A c →₀ ℚ) :
    supportVerticalEdgeChainInclude M hab (supportPhiVerticalEmbed M A c x) =
      supportPhiVerticalEmbed M B (supportCellInclude Nc.chartSupport hab c) (supportPhiChain1 M hab c x) := by
  have hh : (supportVerticalEdgeChainInclude M hab).comp (supportPhiVerticalEmbed M A c) =
      (supportPhiVerticalEmbed M B (supportCellInclude Nc.chartSupport hab c)).comp (supportPhiChain1 M hab c) := by
    apply Finsupp.lhom_ext
    intro e r
    change supportVerticalEdgeChainInclude M hab (supportPhiVerticalEmbed M A c (Finsupp.single e r)) =
      supportPhiVerticalEmbed M B (supportCellInclude Nc.chartSupport hab c)
        (supportPhiChain1 M hab c (Finsupp.single e r))
    rw [supportPhiVerticalEmbed_single, supportVerticalEdgeChainInclude_single,
      supportPhiChain1_single, supportPhiVerticalEmbed_single]
    rfl
  exact LinearMap.congr_fun hh x

/-- 同じ原Φ閉路包含は台包含と全閉路代表で可換。 -/
theorem supportPhiVerticalCycles_include (x : phiCycles M A c) :
    supportVerticalCyclesInclude M hab (supportPhiVerticalCycles M A c x) =
      supportPhiVerticalCycles M B (supportCellInclude Nc.chartSupport hab c) (supportPhiCycles M hab c x) := by
  apply Subtype.ext
  rw [supportVerticalCyclesInclude_val, supportPhiVerticalCycles_val,
    supportPhiVerticalCycles_val, supportPhiCycles_val, supportPhiVerticalEmbed_include]

/-- 全Φ H₁台包含は元の各fiber類を同じfiberの台包含へ送る。 -/
theorem supportAllPhiHomology_single (x : PhiHomology M A c) :
    supportAllPhiHomology M hab (Pi.single c x) =
      Pi.single (supportCellInclude Nc.chartSupport hab c) (supportPhiHomology M hab c x) := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    rw [supportAllPhiHomology_apply]
    rw [supportPhiVerticalHomology_mk, supportVerticalHomology_mk,
      supportPhiVerticalCycles_include, supportPhiHomology_mk]
    have hh := congrArg (verticalHomologyPhiEquiv M B)
      (supportPhiVerticalHomology_mk M B (supportCellInclude Nc.chartSupport hab c)
        (supportPhiCycles M hab c x))
    simpa only [LinearEquiv.apply_symm_apply] using hh.symm


end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiVerticalEmbed
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiVerticalEmbed_single
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiVerticalEmbed_coordinates
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiVerticalCycles
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiVerticalCycles_val
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiVerticalHomology_mk
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiVerticalEmbed_include
#print axioms AAT.AG.AtlasCoefficientFiber.supportPhiVerticalCycles_include
#print axioms AAT.AG.AtlasCoefficientFiber.supportAllPhiHomology_single
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
