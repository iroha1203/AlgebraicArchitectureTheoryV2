import ResearchLean.AG.AtlasCoefficientFiber.PurePreservation
import ResearchLean.AG.FaceRelationSubdivision.HereditarySpecialization
import ResearchLean.AG.UniformInvariance.ConditionC3NonnecessityWitness

/-!
# G-135 C：同じG-107原始表で新C3′と旧C3の失敗

## Implementation notes

既存R1ConditionC3Witness.presentation.toGeometryをそのまま原入力へ埋め込む。
原edgeMapは全てsomeであり、粗loopへのmapped辺を宣言上の垂直辺へ入れない。
旧比較の全A保存・実非零H¹を再利用し、新Φの計算を同じ表から導く。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.G107DeclaredFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open AtlasDefectComposition

/-- G107の同じproper reading・支持・三辺・一面を持つ原比較。 -/
abbrev M := IncidenceSupportedComparison.ofHereditary
  R1ConditionC3Witness.presentation.toGeometry

/-- 同じ原始表では全細辺が同名の粗辺へmappedである。 -/
theorem edgeMap_some (e : R1ConditionC3Witness.presentation.fineSupportedNerve.nerve.EdgeComponent) :
    M.edgeMap e = some e := rfl

/-- 全A・全粗chartで宣言上の退化辺は空である。 -/
theorem phiEdge_isEmpty (A : Set (Fin 2))
    (c : R1ConditionC3Witness.presentation.coarseSupportedNerve.ChartInTargetSubset A) :
    IsEmpty (PhiEdge M A c) := by
  refine ⟨fun e => ?_⟩
  have he := e.2.1
  rw [edgeMap_some] at he
  cases he

/-- 全Aの同じ実Φ H¹は零で、mappedloopの旧fiber H¹とは異なる。 -/
theorem phiH1_zero (A : Set (Fin 2))
    (c : R1ConditionC3Witness.presentation.coarseSupportedNerve.ChartInTargetSubset A) :
    Subsingleton (phiComplex M A c).H1 := by
  letI := phiEdge_isEmpty A c
  exact phiH1_subsingleton_of_edges_isEmpty M A c

/-- 同じG107既受理比較の全finset保存を任意Set Aへ輸送する。 -/
theorem comparisonH1_bijective (A : Set (Fin 2)) :
    Function.Bijective (M.aSubnerveComparisonHom A).h1Map := by
  classical
  rw [ofHereditary_aSubnerveComparisonHom_h1Map]
  have hs := R1ConditionC3Witness.aSubnerveComparisonHom_h1Map_bijective
    A.toFinite.toFinset
  rw [A.toFinite.coe_toFinset] at hs
  exact hs

/-- 新旧の同じ比較に対するblockDefectは全Aで零となる。 -/
theorem zeroDefect (A : Set (Fin 2)) :
    blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0) :=
  (blockDefect_eq_zero_iff_bijective _).mpr (comparisonH1_bijective A)

/-- 同じ原ηの標準H¹写像も全Aで同型になる。 -/
theorem unitH1_bijective (A : Set (Fin 2)) : Function.Bijective (unitH1 M A) :=
  ((coefficient_zeroDefect_iff M A).mp (zeroDefect A)).1

/-- 同じpure原入力で、全A保存必要十分の新C3′側が成立する。 -/
theorem C3prime_allA : ∀ A : Set (Fin 2), Function.Bijective (unitH1 M A) ∧
    ∀ c : R1ConditionC3Witness.presentation.coarseSupportedNerve.ChartInTargetSubset A,
      Subsingleton (phiComplex M A c).H1 := by
  apply (pure_allA_zeroDefect_iff M
    (hereditary_mixedFace_isEmpty R1ConditionC3Witness.presentation.toGeometry)).mp
  exact zeroDefect

/-- 同じ非空旧C3失敗blockで新C3′が成立し、両側の元H¹は非零である。 -/
theorem newC3prime_and_oldC3_failure :
    (∀ A : Set (Fin 2), blockDefect (M.aSubnerveComparisonHom A).h1Map = (0,0)) ∧
    (∀ A : Set (Fin 2), ∀ c :
      R1ConditionC3Witness.presentation.coarseSupportedNerve.ChartInTargetSubset A,
        Subsingleton (phiComplex M A c).H1) ∧
    (∀ A : Set (Fin 2), Function.Bijective (unitH1 M A)) ∧
    ¬ R1ConditionC3Witness.presentation.toGeometry.ConditionC3AtTargetSubset
      (↑R1ConditionC3Witness.targetZero : Set (Fin 2)) ∧
    0 < Module.finrank ℚ R1ConditionC3Witness.coarseTargetZeroComplex.H1 ∧
    0 < Module.finrank ℚ R1ConditionC3Witness.fineTargetZeroComplex.H1 :=
  ⟨zeroDefect, phiH1_zero, unitH1_bijective,
    R1ConditionC3Witness.not_conditionC3AtTargetSubset,
    R1ConditionC3Witness.targetZero_both_h1_pos⟩

end AAT.AG.AtlasCoefficientFiber.G107DeclaredFiber

#print axioms AAT.AG.AtlasCoefficientFiber.G107DeclaredFiber.M
#print axioms AAT.AG.AtlasCoefficientFiber.G107DeclaredFiber.edgeMap_some
#print axioms AAT.AG.AtlasCoefficientFiber.G107DeclaredFiber.phiEdge_isEmpty
#print axioms AAT.AG.AtlasCoefficientFiber.G107DeclaredFiber.phiH1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.G107DeclaredFiber.comparisonH1_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.G107DeclaredFiber.zeroDefect
#print axioms AAT.AG.AtlasCoefficientFiber.G107DeclaredFiber.unitH1_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.G107DeclaredFiber.C3prime_allA
#print axioms AAT.AG.AtlasCoefficientFiber.G107DeclaredFiber.newC3prime_and_oldC3_failure
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
