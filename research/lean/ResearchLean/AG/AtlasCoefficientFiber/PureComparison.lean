import ResearchLean.AG.AtlasCoefficientFiber.TransgressionVanishing

/-!
# G-135 B：旧hereditary入力でのpure特殊化

旧面退化条件から同じ原混在面基底の空性を導き、κと標準τの零性へ接続する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (H : TargetSupportedNerveMorphism qc qf h Nc Nf) (A : Set qc.Target)

/-- 旧hereditaryの実面退化条件から、原混在面基底は空になる。 -/
theorem hereditary_mixedFace_isEmpty :
    IsEmpty (MixedFace (IncidenceSupportedComparison.ofHereditary H) A) := by
  refine ⟨fun f => ?_⟩
  obtain ⟨e, he⟩ := f.2.2
  have hf : H.faceMap f.1.1 = none := f.2.1
  have hn := H.face_none_edge1 f.1.1 hf
  change H.edgeMap (Nf.nerve.faceEdge1 f.1.1) = some e at he
  rw [hn] at he
  cases he

/-- 原混在面基底の空性からκは零。 -/
theorem kappa_zero_of_mixed_isEmpty
    (M : IncidenceSupportedComparison qc qf h Nc Nf) [IsEmpty (MixedFace M A)] :
    kappa M A = 0 := by
  apply LinearMap.ext
  intro y
  have hy : y = 0 := Subsingleton.elim _ _
  rw [hy, map_zero, LinearMap.zero_apply]

/-- 原混在面が空なら、D像包含条件は同じ原微分の零値から従う。 -/
theorem primitiveVanishing_of_mixed_isEmpty
    (M : IncidenceSupportedComparison qc qf h Nc Nf) [IsEmpty (MixedFace M A)] :
    PrimitiveTransgressionVanishing M A := by
  intro x y _
  have hy : y = 0 := Subsingleton.elim _ _
  refine ⟨0, 0, ?_⟩
  rw [hy]
  simp only [Submodule.coe_zero, map_zero, add_zero]

/-- 原混在面が空なら標準短完全列の同じτは零。 -/
theorem connectingTau_zero_of_mixed_isEmpty
    (M : IncidenceSupportedComparison qc qf h Nc Nf) [IsEmpty (MixedFace M A)] :
    connectingTau M A = 0 :=
  (connectingTau_zero_iff_primitive M A).mpr (primitiveVanishing_of_mixed_isEmpty A M)

/-- 旧hereditary入力は同じ原κを零にする。 -/
theorem hereditary_kappa_zero : kappa (IncidenceSupportedComparison.ofHereditary H) A = 0 := by
  letI := hereditary_mixedFace_isEmpty H A
  exact kappa_zero_of_mixed_isEmpty A _

/-- 旧hereditary入力は同じ標準τを零にする。 -/
theorem hereditary_connectingTau_zero :
    connectingTau (IncidenceSupportedComparison.ofHereditary H) A = 0 := by
  letI := hereditary_mixedFace_isEmpty H A
  exact connectingTau_zero_of_mixed_isEmpty A _

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.hereditary_mixedFace_isEmpty
#print axioms AAT.AG.AtlasCoefficientFiber.kappa_zero_of_mixed_isEmpty
#print axioms AAT.AG.AtlasCoefficientFiber.primitiveVanishing_of_mixed_isEmpty
#print axioms AAT.AG.AtlasCoefficientFiber.connectingTau_zero_of_mixed_isEmpty
#print axioms AAT.AG.AtlasCoefficientFiber.hereditary_kappa_zero
#print axioms AAT.AG.AtlasCoefficientFiber.hereditary_connectingTau_zero
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
