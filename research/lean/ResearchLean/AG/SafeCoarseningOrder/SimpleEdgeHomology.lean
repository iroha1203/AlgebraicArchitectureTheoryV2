import ResearchLean.AG.SafeCoarseningOrder.UniformSafety
import ResearchLean.AG.AtlasCoefficientFiber.PhiInterval

/-!
# 一辺以下の原始入力と安全性の正例

W0を同じSafeへ適用するため、異端点で一辺以下のK1支持nerveの実d0全射性を示す。
各Aを扱い、原始辺の全射部分像から全商でも一辺以下であることを導出する。
-/

noncomputable section
namespace AAT.AG.SafeCoarseningOrder
open CanonicalResolution ResolutionInvariance TwoPhase AtlasCoefficientFiber

/-- 一辺以下で各辺の端点が異なる支持nerveでは全Aの実d0が全射。 -/
theorem subset_d0_surjective_of_single_edge {S : Type} {q : Reading S}
    (N : TargetSupportedNerve q) [Subsingleton N.nerve.EdgeComponent]
    (hne : ∀ e, N.nerve.edgeLeft e ≠ N.nerve.edgeRight e) (A : Set q.Target) :
    Function.Surjective (N.targetSubsetComplex A).d0 := by
  classical
  intro z
  by_cases hex : Nonempty (N.EdgeInTargetSubset A)
  · let e := Classical.choice hex
    let x : N.ChartInTargetSubset A → ℚ := fun v =>
      if v.1 = N.nerve.edgeRight e.1 then z e else 0
    refine ⟨x, ?_⟩
    funext f
    have hfe : f = e := Subtype.ext (Subsingleton.elim _ _)
    subst f
    rw [N.targetSubsetComplex_d0_apply]
    simp [x, hne e.1]
  · letI : IsEmpty (N.EdgeInTargetSubset A) := not_nonempty_iff.mp hex
    refine ⟨0, ?_⟩
    funext f
    exact isEmptyElim f

/-- 部分商像が全商辺を尽くすため、一辺以下という性質は全商で保存。 -/
theorem quotient_edges_subsingleton {S T V : Type} (M : PrimitiveInput S T V)
    [Subsingleton M.Edge] (R : Coarsening T V) : Subsingleton (M.QuotientEdge R) := by
  constructor
  intro f g
  obtain ⟨v, w, he, hv, hw⟩ := f.2.2
  obtain ⟨v', w', he', hv', hw'⟩ := g.2.2
  let e : M.Edge := ⟨(v,w),he⟩
  let e' : M.Edge := ⟨(v',w'),he'⟩
  have hf : M.quotientEdgeMap R e = some f := (M.quotientEdgeMap_eq_some R e f).mpr ⟨hv,hw⟩
  have hg : M.quotientEdgeMap R e' = some g := (M.quotientEdgeMap_eq_some R e' g).mpr ⟨hv',hw'⟩
  have heq : e = e' := Subsingleton.elim _ _
  exact Option.some.inj (hf.symm.trans (by rw [heq]; exact hg))

/-- 一辺以下のT0原始表の全粗化は同じ実比較について安全。 -/
theorem safe_of_single_edge {S T V : Type} [Fintype V] (M : PrimitiveInput S T V)
    [Subsingleton M.Edge] (R : Coarsening T V) : M.Safe R := by
  intro A
  letI : Subsingleton (M.quotientSupported R).nerve.EdgeComponent := quotient_edges_subsingleton M R
  letI := h1_subsingleton_of_d0_surjective _
    (subset_d0_surjective_of_single_edge (M.quotientSupported R) (fun e => e.2.1) A)
  letI : Subsingleton M.supported.nerve.EdgeComponent := inferInstanceAs (Subsingleton M.Edge)
  letI := h1_subsingleton_of_d0_surjective _
    (subset_d0_surjective_of_single_edge M.supported M.edge_endpoints_ne
      (comparisonFactor (M.quotientReading R) M.reading (M.quotient_coarser R) ⁻¹' A))
  constructor
  · exact Function.injective_of_subsingleton _
  · intro y
    exact ⟨0, Subsingleton.elim _ _⟩

end AAT.AG.SafeCoarseningOrder
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
