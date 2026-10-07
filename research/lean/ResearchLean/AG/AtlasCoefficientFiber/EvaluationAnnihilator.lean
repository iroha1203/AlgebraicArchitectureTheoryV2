import ResearchLean.AG.AtlasCoefficientFiber.PrimitiveDescent
import ResearchLean.AG.AtlasCoefficientFiber.DualRestriction
import ResearchLean.AG.AtlasCoefficientFiber.LocalEvaluation

/-!
# G-135 A §4：実counit像と指定Lのannihilator

原始閉条件からΦ・Γ成分値とΛ値を生成し、独立した実Kan係数へ戻す。
像の逆包含をcertificateとして受け取らない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u, u} qc} {Nf : TargetSupportedNerve.{u, u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 線形制限が零であることの元空間上の評価式。 -/
theorem dualRestriction_eq_zero_iff {V : Type u} [AddCommGroup V] [Module ℚ V]
    (W : Submodule ℚ V) (z : Module.Dual ℚ V) :
    W.dualRestrict z = 0 ↔ ∀ x ∈ W, z x = 0 := by
  constructor
  · intro hz x hx
    exact LinearMap.congr_fun hz ⟨x, hx⟩
  · intro hz
    exact LinearMap.ext fun x => hz x.1 x.2

/-- Q次数0への零制限は、同じ原始垂直辺の端点閉条件。 -/
theorem restriction0_zero_iff
    (z : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :
    restriction0 M A z = 0 ↔ ∀ e : VerticalEdge M A,
      z (edgeEndpoint Nf _ e.1 true) = z (edgeEndpoint Nf _ e.1 false) := by
  change (degenerateL0 M A).dualRestrict (freeDualEquiv _ z) = 0 ↔ _
  rw [dualRestriction_eq_zero_iff]
  change (∀ x ∈ LinearMap.range ((chainD1 Nf _).comp (verticalEdgeInclusion M A)),
      freeDualEquiv _ z x = 0) ↔ _
  rw [annihilates_freeRange_iff]
  simp only [LinearMap.comp_apply, verticalEdgeInclusion_single, chainD1_single,
    one_smul, map_sub, freeDualEquiv_single, one_mul, sub_eq_zero]
  rfl

/-- Q次数1への零制限は垂直辺で零、混在面の全境界で零という原始閉条件。 -/
theorem restriction1_zero_iff
    (z : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :
    restriction1 M A z = 0 ↔
      (∀ e : VerticalEdge M A, z e.1 = 0) ∧
      (∀ f : MixedFace M A, (Nf.targetSubsetComplex _).d1 z f.1 = 0) := by
  change (degenerateL1 M A).dualRestrict (freeDualEquiv _ z) = 0 ↔ _
  rw [dualRestriction_eq_zero_iff]
  constructor
  · intro hz
    constructor
    · intro e
      have he := hz _ (verticalEdge_range_le_L1 M A ⟨Finsupp.single e 1, rfl⟩)
      simpa only [verticalEdgeInclusion_single, freeDualEquiv_single, one_mul] using he
    · intro f
      have hf := hz _ (mixedBoundary_range_le_L1 M A ⟨Finsupp.single f 1, rfl⟩)
      simpa only [LinearMap.comp_apply, mixedFaceInclusion_single, chainD2_dual,
        freeDualEquiv_single, one_mul] using hf
  · rintro ⟨hv, hm⟩ x hx
    obtain ⟨v, m, rfl⟩ := (mem_degenerateL1 M A x).mp hx
    have he : ∀ x ∈ LinearMap.range (verticalEdgeInclusion M A), freeDualEquiv _ z x = 0 :=
      (annihilates_freeRange_iff _ _).mpr (by
        intro e; simpa only [verticalEdgeInclusion_single, freeDualEquiv_single, one_mul] using hv e)
    have hf : ∀ x ∈ LinearMap.range ((chainD2 Nf _).comp (mixedFaceInclusion M A)),
        freeDualEquiv _ z x = 0 := (annihilates_freeRange_iff _ _).mpr (by
      intro f
      simpa only [LinearMap.comp_apply, mixedFaceInclusion_single, chainD2_dual,
        freeDualEquiv_single, one_mul] using hm f)
    have hm0 := hf _ ⟨m, rfl⟩
    simp only [LinearMap.comp_apply] at hm0
    rw [map_add, he _ ⟨v, rfl⟩, hm0, zero_add]

/-- Q次数2への零制限は同じ原始退化面での零評価。 -/
theorem restriction2_zero_iff
    (z : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ) :
    restriction2 M A z = 0 ↔ ∀ f : DegenerateFace M A, z f.1 = 0 := by
  change (degenerateL2 M A).dualRestrict (freeDualEquiv _ z) = 0 ↔ _
  rw [dualRestriction_eq_zero_iff]
  change (∀ x ∈ LinearMap.range (degenerateFaceInclusion M A), freeDualEquiv _ z x = 0) ↔ _
  rw [annihilates_freeRange_iff]
  simp only [degenerateFaceInclusion_single, freeDualEquiv_single, one_mul]

/-- 実ε次数0は指定L₀で消える。 -/
theorem restriction0_evaluation0 (w : (pushforwardComplex M A).C0) :
    restriction0 M A (evaluation0 M A w) = 0 := by
  apply (restriction0_zero_iff M A _).mpr
  intro e
  have he := congrFun (evaluation_comm0 M A w) e.1
  rw [evaluation1_of_none M A _ e.1 e.2, Nf.targetSubsetComplex_d0_apply] at he
  exact sub_eq_zero.mp he.symm

/-- 実ε次数1は指定L₁で消える。混在面の境界も含める。 -/
theorem restriction1_evaluation1 (w : (pushforwardComplex M A).C1) :
    restriction1 M A (evaluation1 M A w) = 0 := by
  apply (restriction1_zero_iff M A _).mpr
  constructor
  · intro e; exact evaluation1_of_none M A w e.1 e.2
  · intro f
    have hf := congrFun (evaluation_comm1 M A w) f.1
    rw [evaluation2_of_none M A _ f.1 f.2.1] at hf
    exact hf.symm

/-- 実ε次数2は指定L₂で消える。 -/
theorem restriction2_evaluation2 (w : (pushforwardComplex M A).C2) :
    restriction2 M A (evaluation2 M A w) = 0 :=
  (restriction2_zero_iff M A _).mpr fun f => evaluation2_of_none M A w f.1 f.2

/-- 原始垂直閉条件から、独立した実Kan係数の次数0を生成する。 -/
theorem evaluation0_preimage_of_restriction_zero
    (z : Nf.ChartInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ)
    (hz : restriction0 M A z = 0) : ∃ w, evaluation0 M A w = z := by
  let hv := (restriction0_zero_iff M A z).mp hz
  let w : (pushforwardComplex M A).C0 := fun c =>
    (phiCoefficientEquiv M A c).symm (phiDescendedValues M A c z hv)
  refine ⟨w, ?_⟩
  funext v
  let c := Carrier.chart M A _ (fun _ ht => ht) v
  rw [evaluation0_phi M A w c ⟨v, rfl⟩]
  exact congrFun ((phiCoefficientEquiv M A c).apply_symm_apply
    (phiDescendedValues M A c z hv)) _

/-- 原始L₁閉条件は各混在Γ関係の二端点での値の一致を含む。 -/
theorem gamma_closed_of_restriction_zero
    (z : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ)
    (hz : restriction1 M A z = 0) (e : Nc.EdgeInTargetSubset A) (f : GammaEdge M A e) :
    z (gammaSource M A f).1 = z (gammaTarget M A f).1 := by
  obtain ⟨hv, hm⟩ := (restriction1_zero_iff M A z).mp hz
  have hf := hm ⟨f.1, f.2.1, by
    rcases f.2.2 with hl | hr
    · exact ⟨e.1, hl.2.1⟩
    · exact ⟨e.1, hr.2.1⟩⟩
  rw [Nf.targetSubsetComplex_d1_apply] at hf
  rw [gammaSource_val]
  rcases f.2.2 with hl | hr
  · rw [gammaTarget_val_of_left M A f hl.1]
    have h0 := hv ⟨Nf.targetSubsetFaceEdge0 _ f.1, hl.1⟩
    rw [h0] at hf
    linarith
  · rw [gammaTarget_val_of_right M A f hr.1]
    have h2 := hv ⟨Nf.targetSubsetFaceEdge2 _ f.1, hr.2.2⟩
    rw [h2] at hf
    linarith

/-- 原始L₁閉条件から、独立した実Kan係数の次数1を生成する。 -/
theorem evaluation1_preimage_of_restriction_zero
    (z : Nf.EdgeInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ)
    (hz : restriction1 M A z = 0) : ∃ w, evaluation1 M A w = z := by
  let hg := gamma_closed_of_restriction_zero M A z hz
  let w : (pushforwardComplex M A).C1 := fun e =>
    (gammaCoefficientEquiv M A e).symm (gammaDescendedValues M A e z (hg e))
  refine ⟨w, ?_⟩
  funext v
  cases he : M.edgeMap v.1 with
  | none =>
    rw [evaluation1_of_none M A w v he]
    exact ((restriction1_zero_iff M A z).mp hz).1 ⟨v, he⟩ |>.symm
  | some a =>
    let e := M.targetSubsetEdgeMap A _ (fun _ ht => ht) v a he
    rw [evaluation1_gamma M A w e ⟨v, he⟩]
    exact congrFun ((gammaCoefficientEquiv M A e).apply_symm_apply
      (gammaDescendedValues M A e z (hg e))) _

/-- 原始L₂閉条件から、独立した実Kan係数の次数2を生成する。 -/
theorem evaluation2_preimage_of_restriction_zero
    (z : Nf.FaceInTargetSubset (comparisonFactor qc qf h ⁻¹' A) → ℚ)
    (hz : restriction2 M A z = 0) : ∃ w, evaluation2 M A w = z := by
  let w : (pushforwardComplex M A).C2 := fun F =>
    (lambdaCoefficientEquiv M A F).symm (fun f => z f.1)
  refine ⟨w, ?_⟩
  funext f
  cases hf : M.faceMap f.1 with
  | none =>
    rw [evaluation2_of_none M A w f hf]
    exact ((restriction2_zero_iff M A z).mp hz ⟨f, hf⟩).symm
  | some a =>
    let F := M.targetSubsetFaceMap A _ (fun _ ht => ht) f a hf
    rw [evaluation2_lambda M A w F ⟨f, hf⟩]
    exact congrFun ((lambdaCoefficientEquiv M A F).apply_symm_apply (fun f => z f.1)) _

/-- 実ε次数0の像は、指定L₀のannihilatorと同じ制限核。 -/
theorem evaluation0_range_eq_ker :
    LinearMap.range (evaluation0 M A) = LinearMap.ker (restriction0 M A) := by
  ext z
  exact ⟨by rintro ⟨w, rfl⟩; exact restriction0_evaluation0 M A w,
    evaluation0_preimage_of_restriction_zero M A z⟩
/-- 実ε次数1の像は、混在境界を含む指定L₁のannihilator。 -/
theorem evaluation1_range_eq_ker :
    LinearMap.range (evaluation1 M A) = LinearMap.ker (restriction1 M A) := by
  ext z
  exact ⟨by rintro ⟨w, rfl⟩; exact restriction1_evaluation1 M A w,
    evaluation1_preimage_of_restriction_zero M A z⟩
/-- 実ε次数2の像は、指定L₂のannihilator。 -/
theorem evaluation2_range_eq_ker :
    LinearMap.range (evaluation2 M A) = LinearMap.ker (restriction2 M A) := by
  ext z
  exact ⟨by rintro ⟨w, rfl⟩; exact restriction2_evaluation2 M A w,
    evaluation2_preimage_of_restriction_zero M A z⟩

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.dualRestriction_eq_zero_iff
#print axioms AAT.AG.AtlasCoefficientFiber.restriction0_zero_iff
#print axioms AAT.AG.AtlasCoefficientFiber.restriction1_zero_iff
#print axioms AAT.AG.AtlasCoefficientFiber.restriction2_zero_iff
#print axioms AAT.AG.AtlasCoefficientFiber.restriction0_evaluation0
#print axioms AAT.AG.AtlasCoefficientFiber.restriction1_evaluation1
#print axioms AAT.AG.AtlasCoefficientFiber.restriction2_evaluation2
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation0_preimage_of_restriction_zero
#print axioms AAT.AG.AtlasCoefficientFiber.gamma_closed_of_restriction_zero
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation1_preimage_of_restriction_zero
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation2_preimage_of_restriction_zero
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation0_range_eq_ker
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation1_range_eq_ker
#print axioms AAT.AG.AtlasCoefficientFiber.evaluation2_range_eq_ker
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
