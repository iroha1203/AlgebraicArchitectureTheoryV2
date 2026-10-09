import ResearchLean.AG.AtlasCoefficientFiber.WitnessCommon
import ResearchLean.AG.FaceRelationSubdivision.FullSupportSubsetComparison
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# G-135 全台指定例の原商と実発生ラベル

## Implementation notes

原H¹は変更せず、その元cyclesから全cochainへの写像の核を証明して商同値を作る。
零微分は一般補題の方向仮定であり、各原始例で放電する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.WitnessFullSupport
open CanonicalResolution ResolutionInvariance TwoPhase FaceRelationSubdivision WitnessCommon

/-- 原H¹が零微分の場合、全原degree-one座標を読む両方向同値。 -/
def zeroDifferentialH1Equiv (C : ThreeCochainComplex ℚ)
    (h0 : C.d0 = 0) (h1 : C.d1 = 0) : C.H1 ≃ₗ[ℚ] C.C1 := by
  let f : LinearMap.ker C.d1 →ₗ[ℚ] C.C1 := (LinearMap.ker C.d1).subtype
  have hk : LinearMap.ker f = LinearMap.range C.boundaryToCycles := by
    ext z
    constructor
    · intro hz
      refine ⟨0, ?_⟩
      apply Subtype.ext
      exact (map_zero C.d0).trans hz.symm
    · rintro ⟨x,rfl⟩
      change C.d0 x = 0
      rw [h0, LinearMap.zero_apply]
  have hs : Function.Surjective f := by
    intro z
    exact ⟨⟨z, by rw [LinearMap.mem_ker, h1, LinearMap.zero_apply]⟩,rfl⟩
  exact (Submodule.quotEquivOfEq _ _ hk.symm).trans (f.quotKerEquivOfSurjective hs)

/-- 同じ商同値は全原cocycle代表を読む。 -/
theorem zeroDifferentialH1Equiv_mk (C : ThreeCochainComplex ℚ)
    (h0 : C.d0 = 0) (h1 : C.d1 = 0) (z : LinearMap.ker C.d1) :
    zeroDifferentialH1Equiv C h0 h1
      ((LinearMap.range C.boundaryToCycles).mkQ z) = z.1 := rfl

/-- 同一Sourceの指定全射から非空Aのfine逆像も非空。 -/
theorem fine_nonempty (A : Set qc.Target) (hA : A.Nonempty) :
    (comparisonFactor qc qf coarser ⁻¹' A).Nonempty := by
  obtain ⟨a,ha⟩ := hA
  obtain ⟨s,hs⟩ := comparisonFactor_surjective qc qf coarser a
  exact ⟨s,by change comparisonFactor qc qf coarser s ∈ A; rw [hs]; exact ha⟩

/-- 指定Lawの実発生label全体は二Boolと両逆で一致する。 -/
def labelEquiv : LawValueLabel laws ≃ Bool where
  toFun l := l.value
  invFun := label
  left_inv l := by
    apply LawValueLabel.ext laws
    · change () = l.law
      cases l.law
      rfl
    · rfl
  right_inv _ := rfl

/-- 全発生labelは同じ指定Sourceから生成されたもの。 -/
theorem labelEquiv_symm (b : Bool) : labelEquiv.symm b = label b := rfl

/-- 同台でも二つの実発生labelは二summandとして残る。 -/
theorem labels_card : Fintype.card (LawValueLabel laws) = 2 :=
  (Fintype.card_congr labelEquiv).trans (by decide)

end AAT.AG.AtlasCoefficientFiber.WitnessFullSupport
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFullSupport.zeroDifferentialH1Equiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFullSupport.zeroDifferentialH1Equiv_mk
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFullSupport.fine_nonempty
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFullSupport.labelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFullSupport.labelEquiv_symm
#print axioms AAT.AG.AtlasCoefficientFiber.WitnessFullSupport.labels_card
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.WitnessFullSupport
