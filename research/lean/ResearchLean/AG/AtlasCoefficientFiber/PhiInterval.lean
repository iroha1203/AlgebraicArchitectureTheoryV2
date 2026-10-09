import ResearchLean.AG.AtlasCoefficientFiber.LocalPreservation

/-!
# 原Φの一点・一区間における H¹ 零性

Implementation notes: 原Option選択の辺が高々一つで、存在する辺の二端点が
異なる場合、原微分の全射を頂点potentialから構成する。期待rankは入力しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
universe u v

/-- 原次数0微分が全射なら、実cocycle商の全元は零となる。 -/
theorem h1_subsingleton_of_d0_surjective {k : Type u} [Field k]
    (C : ThreeCochainComplex.{u,v} k) (hd : Function.Surjective C.d0) :
    Subsingleton C.H1 := by
  have hb : Function.Surjective C.boundaryToCycles := by
    intro z
    obtain ⟨x, hx⟩ := hd z.1
    exact ⟨x, Subtype.ext hx⟩
  exact Submodule.Quotient.subsingleton_iff.mpr (LinearMap.range_eq_top.mpr hb)

variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 高々一つの原退化辺について、二端点差の任意指定値をpotentialで実現する。 -/
theorem phiD0_surjective_of_interval (c : Nc.ChartInTargetSubset A)
    [Subsingleton (PhiEdge M A c)]
    (hne : ∀ e : PhiEdge M A c, phiEndpoint M A e true ≠ phiEndpoint M A e false) :
    Function.Surjective (phiD0 M A c) := by
  classical
  intro z
  by_cases he : Nonempty (PhiEdge M A c)
  · let e : PhiEdge M A c := Classical.choice he
    refine ⟨fun v => if v = phiEndpoint M A e true then z e else 0, ?_⟩
    funext a
    have ha : a = e := Subsingleton.elim _ _
    subst a
    simp [Ne.symm (hne e)]
  · letI : IsEmpty (PhiEdge M A c) := ⟨fun e => he ⟨e⟩⟩
    exact ⟨0, Subsingleton.elim _ _⟩

/-- 同じ原Φの一区間または点からH¹零性を放電する。 -/
theorem phiH1_subsingleton_of_interval (c : Nc.ChartInTargetSubset A)
    [Subsingleton (PhiEdge M A c)]
    (hne : ∀ e : PhiEdge M A c, phiEndpoint M A e true ≠ phiEndpoint M A e false) :
    Subsingleton (phiComplex M A c).H1 :=
  h1_subsingleton_of_d0_surjective _ (phiD0_surjective_of_interval M A c hne)

/-- 同じ有限Φ cochain H¹の零性を原chain H₁へ両方向双対同定で移す。 -/
theorem phiHomology_subsingleton_of_h1_zero (c : Nc.ChartInTargetSubset A)
    (hz : Subsingleton (phiComplex M A c).H1) : Subsingleton (PhiHomology M A c) := by
  letI := hz
  letI : Subsingleton (Module.Dual ℚ (PhiHomology M A c)) :=
    (phiHomologyDualEquiv M A c).symm.toEquiv.subsingleton
  have hf : Module.finrank ℚ (Module.Dual ℚ (PhiHomology M A c)) = 0 :=
    Module.finrank_zero_of_subsingleton
  rw [Subspace.dual_finrank_eq] at hf
  exact Module.finrank_zero_iff.mp hf

/-- 全Φの実H¹零から、独立に構成した同じκの全値は零。 -/
theorem kappa_zero_of_phiH1_zero
    (hz : ∀ c : Nc.ChartInTargetSubset A, Subsingleton (phiComplex M A c).H1) :
    kappa M A = 0 := by
  letI (c : Nc.ChartInTargetSubset A) := phiHomology_subsingleton_of_h1_zero M A c (hz c)
  exact LinearMap.ext fun x => Subsingleton.elim _ _

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.h1_subsingleton_of_d0_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.phiD0_surjective_of_interval
#print axioms AAT.AG.AtlasCoefficientFiber.phiH1_subsingleton_of_interval
#print axioms AAT.AG.AtlasCoefficientFiber.phiHomology_subsingleton_of_h1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.kappa_zero_of_phiH1_zero
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
