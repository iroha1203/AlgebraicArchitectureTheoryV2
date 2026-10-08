import ResearchLean.AG.AtlasCoefficientFiber.EvaluationAnnihilator
import ResearchLean.AG.AtlasCoefficientFiber.PurePreservation
import ResearchLean.AG.AtlasCoefficientFiber.FiberCone
import ResearchLean.AG.FaceRelationSubdivision.HomotopyDiagnostics

/-!
# G-135 D：全mappedセルからの実評価同型

## Implementation notes

原Option辺面にnoneがないことから、指定Lの生成子を消去する。
独立した右KanのPは保持し、同じ実εの単射性と原始像定理から逆を構成する。
H¹保存はここで仮定せず、任意のmapped比較の係数とfiberを扱う。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits HomologicalComplex CochainComplex
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase AtlasDefectComposition
universe u
namespace MappedCells
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)
variable (he : ∀ e, M.edgeMap e ≠ none) (hf : ∀ f, M.faceMap f ≠ none)

include he in
/-- 原Option表から選択垂直辺は空となる。 -/
theorem verticalEdge_isEmpty : IsEmpty (VerticalEdge M A) :=
  ⟨fun e => he e.1.1 e.2⟩
include hf in
/-- 原Option表から選択混在面は空となる。 -/
theorem mixedFace_isEmpty : IsEmpty (MixedFace M A) :=
  ⟨fun f => hf f.1.1 f.2.1⟩
include hf in
/-- 原Option表から選択退化面は空となる。 -/
theorem degenerateFace_isEmpty : IsEmpty (DegenerateFace M A) :=
  ⟨fun f => hf f.1.1 f.2⟩

include he in
/-- 垂直辺がないため原L₀は零部分空間。 -/
theorem L0_eq_bot : degenerateL0 M A = ⊥ := by
  letI := verticalEdge_isEmpty M A he
  ext x
  rw [mem_degenerateL0, Submodule.mem_bot]
  constructor
  · rintro ⟨v, rfl⟩
    rw [Subsingleton.elim v 0, map_zero, map_zero]
  · rintro rfl
    exact ⟨0, by rw [map_zero, map_zero]⟩
include he hf in
/-- 垂直辺と混在面がないため原L₁は零部分空間。 -/
theorem L1_eq_bot : degenerateL1 M A = ⊥ := by
  letI := verticalEdge_isEmpty M A he
  letI := mixedFace_isEmpty M A hf
  ext x
  rw [mem_degenerateL1, Submodule.mem_bot]
  constructor
  · rintro ⟨v, m, rfl⟩
    rw [Subsingleton.elim v 0, Subsingleton.elim m 0, map_zero, map_zero,
      map_zero, zero_add]
  · rintro rfl
    exact ⟨0, 0, by rw [map_zero, map_zero, map_zero, zero_add]⟩
include hf in
/-- 退化面がないため原L₂は零部分空間。 -/
theorem L2_eq_bot : degenerateL2 M A = ⊥ := by
  letI := degenerateFace_isEmpty M A hf
  ext x
  rw [mem_degenerateL2, Submodule.mem_bot]
  constructor
  · rintro ⟨f, rfl⟩
    rw [Subsingleton.elim f 0, map_zero]
  · rintro rfl
    exact ⟨0, map_zero _⟩

include he in
/-- 原始垂直閉条件が空なので細次数0の全cochainは原制限で零。 -/
theorem restriction0_zero (z) : restriction0 M A z = 0 :=
  (restriction0_zero_iff M A z).mpr fun e => (he e.1.1 e.2).elim
include he hf in
/-- 原始垂直辺・混在面条件が空なので細次数1の全cochainは原制限で零。 -/
theorem restriction1_zero (z) : restriction1 M A z = 0 :=
  (restriction1_zero_iff M A z).mpr
    ⟨fun e => (he e.1.1 e.2).elim, fun f => (hf f.1.1 f.2.1).elim⟩
include hf in
/-- 原始退化面条件が空なので細次数2の全cochainは原制限で零。 -/
theorem restriction2_zero (z) : restriction2 M A z = 0 :=
  (restriction2_zero_iff M A z).mpr fun f => (hf f.1.1 f.2).elim

include he in
/-- 実ε次数0の順写像を保持する両方向線形同型。 -/
def evaluation0Equiv : (pushforwardComplex M A).C0 ≃ₗ[ℚ]
    (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).C0 :=
  LinearEquiv.ofBijective (evaluation0 M A)
    ⟨evaluation0_injective M A, fun z =>
      evaluation0_preimage_of_restriction_zero M A z (restriction0_zero M A he z)⟩
include he hf in
/-- 実ε次数1の順写像を保持する両方向線形同型。 -/
def evaluation1Equiv : (pushforwardComplex M A).C1 ≃ₗ[ℚ]
    (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).C1 :=
  LinearEquiv.ofBijective (evaluation1 M A)
    ⟨evaluation1_injective M A, fun z =>
      evaluation1_preimage_of_restriction_zero M A z (restriction1_zero M A he hf z)⟩
include hf in
/-- 実ε次数2の順写像を保持する両方向線形同型。 -/
def evaluation2Equiv : (pushforwardComplex M A).C2 ≃ₗ[ℚ]
    (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)).C2 :=
  LinearEquiv.ofBijective (evaluation2 M A)
    ⟨evaluation2_injective M A, fun z =>
      evaluation2_preimage_of_restriction_zero M A z (restriction2_zero M A hf z)⟩
include he in
/-- 次数0同型は同じ元εを読む。 -/
@[simp] theorem evaluation0Equiv_apply (z) : evaluation0Equiv M A he z = evaluation0 M A z := rfl
include he hf in
/-- 次数1同型は同じ元εを読む。 -/
@[simp] theorem evaluation1Equiv_apply (z) : evaluation1Equiv M A he hf z = evaluation1 M A z := rfl
include hf in
/-- 次数2同型は同じ元εを読む。 -/
@[simp] theorem evaluation2Equiv_apply (z) : evaluation2Equiv M A hf z = evaluation2 M A z := rfl

include he hf in
/-- 全三次数評価と次数外零から元εの標準複体同型性を導く。 -/
theorem evaluation_standard_isIso : IsIso (zeroExtensionMap (evaluationHom M A)) := by
  have hc (n : ℤ) : IsIso ((zeroExtensionMap (evaluationHom M A)).f n) := by
    change IsIso (degreeMap (evaluationHom M A) n)
    by_cases h0 : n = 0
    · subst n
      exact (ConcreteCategory.isIso_iff_bijective _).mpr (evaluation0Equiv M A he).bijective
    · by_cases h1 : n = 1
      · subst n
        exact (ConcreteCategory.isIso_iff_bijective _).mpr (evaluation1Equiv M A he hf).bijective
      · by_cases h2 : n = 2
        · subst n
          exact (ConcreteCategory.isIso_iff_bijective _).mpr (evaluation2Equiv M A hf).bijective
        · have hs := degreeObject_isZero (pushforwardComplex M A) n h0 h1 h2
          have ht := degreeObject_isZero
            (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)) n h0 h1 h2
          have hh : degreeMap (evaluationHom M A) n = (IsZero.iso hs ht).hom := hs.eq_of_src _ _
          rw [hh]
          infer_instance
  letI := hc
  exact HomologicalComplex.Hom.isIso_of_components _
include he hf in
/-- 独立Pと同じ細cochainの全整数次数同型を、実εから生成する。 -/
def evaluationStandardIso : zeroExtension (pushforwardComplex M A) ≅
    zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A)) :=
  letI := evaluation_standard_isIso M A he hf
  asIso (zeroExtensionMap (evaluationHom M A))
include he hf in
/-- 標準同型の順方向は同じ原始counit評価。 -/
@[simp] theorem evaluationStandardIso_hom : (evaluationStandardIso M A he hf).hom =
    zeroExtensionMap (evaluationHom M A) := rfl
include he hf in
/-- 全整数次数のhomology同型も同じεを保持する。 -/
def evaluationHomologyEquiv (n : ℤ) : (zeroExtension (pushforwardComplex M A)).homology n ≃ₗ[ℚ]
    (zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology n :=
  (homologyMapIso (evaluationStandardIso M A he hf) n).toLinearEquiv
include he hf in
/-- homology順写像は同じεの実homology射。 -/
@[simp] theorem evaluationHomologyEquiv_apply (n : ℤ) (z) :
    evaluationHomologyEquiv M A he hf n z =
      homologyMap (zeroExtensionMap (evaluationHom M A)) n z := rfl
include he hf in
/-- 同じ原ε錐は全整数次数で零homologyを持つ。 -/
theorem fiberCone_isZero (n : ℤ) : IsZero ((fiberCone M A).homology n) := by
  apply cone_homology_isZero_of_bijective
  intro m
  exact (evaluationHomologyEquiv M A he hf m).bijective

include he in
/-- 垂直辺がない原ΦのH¹は全粗chartで零。 -/
theorem phiH1_subsingleton (c : Nc.ChartInTargetSubset A) : Subsingleton (phiComplex M A c).H1 := by
  letI : IsEmpty (PhiEdge M A c) := ⟨fun e => he e.1.1 e.2.1⟩
  exact phiH1_subsingleton_of_edges_isEmpty M A c
include he in
/-- literal κ*核Rは原Φ H¹が零なので零空間となる。 -/
theorem R_subsingleton : Subsingleton (R M A) := by
  letI : ∀ c : Nc.ChartInTargetSubset A, Subsingleton (phiComplex M A c).H1 :=
    phiH1_subsingleton M A he
  infer_instance
include he in
/-- 同じ原τは零のliteral Rから出る零射。 -/
theorem tau_zero : connectingTau M A = 0 := by
  letI := R_subsingleton M A he
  ext z
  rw [Subsingleton.elim z 0, map_zero, LinearMap.zero_apply]

end MappedCells
end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.MappedCells.verticalEdge_isEmpty
#print axioms AAT.AG.AtlasCoefficientFiber.MappedCells.mixedFace_isEmpty
#print axioms AAT.AG.AtlasCoefficientFiber.MappedCells.degenerateFace_isEmpty
#print axioms AAT.AG.AtlasCoefficientFiber.MappedCells.L0_eq_bot
#print axioms AAT.AG.AtlasCoefficientFiber.MappedCells.L1_eq_bot
#print axioms AAT.AG.AtlasCoefficientFiber.MappedCells.L2_eq_bot
#print axioms AAT.AG.AtlasCoefficientFiber.MappedCells.restriction0_zero
#print axioms AAT.AG.AtlasCoefficientFiber.MappedCells.restriction1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.MappedCells.restriction2_zero
#print axioms AAT.AG.AtlasCoefficientFiber.MappedCells.evaluation0Equiv
#print axioms AAT.AG.AtlasCoefficientFiber.MappedCells.evaluation1Equiv
#print axioms AAT.AG.AtlasCoefficientFiber.MappedCells.evaluation2Equiv
#print axioms AAT.AG.AtlasCoefficientFiber.MappedCells.evaluation0Equiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.MappedCells.evaluation1Equiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.MappedCells.evaluation2Equiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.MappedCells.evaluation_standard_isIso
#print axioms AAT.AG.AtlasCoefficientFiber.MappedCells.evaluationStandardIso
#print axioms AAT.AG.AtlasCoefficientFiber.MappedCells.evaluationStandardIso_hom
#print axioms AAT.AG.AtlasCoefficientFiber.MappedCells.evaluationHomologyEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.MappedCells.evaluationHomologyEquiv_apply
#print axioms AAT.AG.AtlasCoefficientFiber.MappedCells.fiberCone_isZero
#print axioms AAT.AG.AtlasCoefficientFiber.MappedCells.phiH1_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.MappedCells.R_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.MappedCells.tau_zero
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
