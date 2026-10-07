import ResearchLean.AG.FaceRelationSubdivision.WitnessOnePeriods
import ResearchLean.AG.FaceRelationSubdivision.LawComparisonDefect
import Formal.Util.AssertStandardAxioms
/-!
# W1 の同じ実比較の period 行列

## Implementation notes

全三成分正方形から既存 H¹ 商への自然性を使う。
座標行列は生成射の評価の結果であり、比較を行列から定義しない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision.WitnessOne
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
/-- plus の同じ原始射は旧辺値を保持する。 -/
@[simp] theorem plusNamed_old (z : Fin 2 → ℚ) (e : Fin 2) : plusNamedHom.f1 z (.inl e)=z e := by
  rw [incidenceNamedHom_f1,rPlus_edge_old]; rfl
/-- plus の同じ原始射は c 値を零にする。 -/
@[simp] theorem plusNamed_c (z : Fin 2 → ℚ) : plusNamedHom.f1 z (.inr false)=0 := by
  rw [incidenceNamedHom_f1,rPlus_edge_c]; rfl
/-- plus の同じ原始射は e2 に e1 の値を読む。 -/
@[simp] theorem plusNamed_e2 (z : Fin 2 → ℚ) : plusNamedHom.f1 z (.inr true)=z (0 : Fin 2) := by
  rw [incidenceNamedHom_f1,rPlus_edge_e2]; rfl
/-- minus の同じ原始射は旧辺値を保持する。 -/
@[simp] theorem minusNamed_old (z : Fin 2 → ℚ) (e : Fin 2) : minusNamedHom.f1 z (.inl e)=z e := by
  rw [incidenceNamedHom_f1,rMinus_edge,rPlus_edge_old]; rfl
/-- minus の同じ原始射は c 値を零にする。 -/
@[simp] theorem minusNamed_c (z : Fin 2 → ℚ) : minusNamedHom.f1 z (.inr false)=0 := by
  rw [incidenceNamedHom_f1,rMinus_edge,rPlus_edge_c]; rfl
/-- minus の同じ原始射は e2 に e1 の値を読む。 -/
@[simp] theorem minusNamed_e2 (z : Fin 2 → ℚ) : minusNamedHom.f1 z (.inr true)=z (0 : Fin 2) := by
  rw [incidenceNamedHom_f1,rMinus_edge,rPlus_edge_e2]; rfl
/-- plus の同じ H¹ 比較は x→x と評価される。 -/
theorem plus_named_identity (x : (namedComplex N).H1) : plusH1Period (plusNamedHom.h1Map x)=oldH1Period x := by
  obtain ⟨z,rfl⟩ := (LinearMap.range (namedComplex N).boundaryToCycles).mkQ_surjective x
  rw [ThreeCochainComplex.Hom.h1Map_mk,plusH1Period_mk,oldH1Period_mk,plusPeriod_apply,oldPeriod_apply,
    ThreeCochainComplex.Hom.cyclesMap_apply,plusNamed_old]
/-- minus の同じ H¹ 比較は x→(x,0) と評価される。 -/
theorem minus_named_injection (x : (namedComplex N).H1) : minusH1Period (minusNamedHom.h1Map x)=(oldH1Period x,0) := by
  obtain ⟨z,rfl⟩ := (LinearMap.range (namedComplex N).boundaryToCycles).mkQ_surjective x
  rw [ThreeCochainComplex.Hom.h1Map_mk,minusH1Period_mk,oldH1Period_mk,minusPeriod_apply,oldPeriod_apply]
  apply Prod.ext
  · rw [ThreeCochainComplex.Hom.cyclesMap_apply,minusNamed_old]
  · simp only [ThreeCochainComplex.Hom.cyclesMap_apply,minusNamed_c,minusNamed_old,minusNamed_e2]
    ring
/-- 旧実 block H¹ の同じ period。 -/
def oldBlockPeriod (l : LawValueLabel laws) := (blockEquiv l).h1Equiv.trans oldH1Period
/-- plus 実 block H¹ の同じ period。 -/
def plusBlockPeriod (l : LawValueLabel laws) := (plusBlockEquiv l).h1Equiv.trans plusH1Period
/-- minus 実 block H¹ の同じ二 period。 -/
def minusBlockPeriod (l : LawValueLabel laws) := (minusBlockEquiv l).h1Equiv.trans minusH1Period
/-- 独立実 plus 比較は各ラベルで period 恒等。 -/
theorem plus_block_identity (l : LawValueLabel laws) (x : (N.lawValueBlockComplex laws coarseAdequate l).H1) :
    plusBlockPeriod l ((plusBlockHom l).h1Map x)=oldBlockPeriod l x := by
  have hn : ∀ z, (plusBlockEquiv l).e1 ((plusBlockHom l).f1 z)=plusNamedHom.f1 ((blockEquiv l).e1 z) := by
    intro z
    exact congrArg (fun f => f.f1 z) (plus_named_square l)
  have hh := ThreeCochainComplex.CochainEquiv.h1Equiv_naturality_apply (blockEquiv l)
    (plusBlockEquiv l) (plusBlockHom l) plusNamedHom hn x
  exact (congrArg plusH1Period hh).trans (plus_named_identity _)
/-- 独立実 minus 比較は各ラベルで x→(x,0)。 -/
theorem minus_block_injection (l : LawValueLabel laws) (x : (N.lawValueBlockComplex laws coarseAdequate l).H1) :
    minusBlockPeriod l ((minusBlockHom l).h1Map x)=(oldBlockPeriod l x,0) := by
  have hn : ∀ z, (minusBlockEquiv l).e1 ((minusBlockHom l).f1 z)=minusNamedHom.f1 ((blockEquiv l).e1 z) := by
    intro z
    exact congrArg (fun f => f.f1 z) (minus_named_square l)
  have hh := ThreeCochainComplex.CochainEquiv.h1Equiv_naturality_apply (blockEquiv l)
    (minusBlockEquiv l) (minusBlockHom l) minusNamedHom hn x
  exact (congrArg minusH1Period hh).trans (minus_named_injection _)
/-- 同じ粗 loop 単独1の実 block 類。 -/
def oldBlockLoop (l : LawValueLabel laws) := (blockEquiv l).h1Equiv.symm
  ((LinearMap.range (namedComplex N).boundaryToCycles).mkQ (oldLoopOnly 1))
/-- 同じ plus loop 単独1の実 block 類。 -/
def plusBlockLoop (l : LawValueLabel laws) := (plusBlockEquiv l).h1Equiv.symm
  ((LinearMap.range (namedComplex plus).boundaryToCycles).mkQ (plusLoopOnly 1))
/-- 同じ minus loop 単独1の実 block 類。 -/
def minusBlockLoop (l : LawValueLabel laws) := (minusBlockEquiv l).h1Equiv.symm
  ((LinearMap.range (namedComplex minus).boundaryToCycles).mkQ (minusSection (1,0)))
/-- 同じ e2 単独1の minus 実 block 類。 -/
def minusBlockExtra (l : LawValueLabel laws) := (minusBlockEquiv l).h1Equiv.symm
  ((LinearMap.range (namedComplex minus).boundaryToCycles).mkQ (minusSection (0,1)))
/-- 粗 loop の実 period は1。 -/
@[simp] theorem oldBlockLoop_period (l : LawValueLabel laws) : oldBlockPeriod l (oldBlockLoop l)=1 := by
  simp only [oldBlockPeriod,oldBlockLoop,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,oldH1Period_mk,oldPeriod_loop]
/-- plus loop の実 period は1。 -/
@[simp] theorem plusBlockLoop_period (l : LawValueLabel laws) : plusBlockPeriod l (plusBlockLoop l)=1 := by
  simp only [plusBlockPeriod,plusBlockLoop,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,plusH1Period_mk,plusPeriod_loop]
/-- minus loop の実 period は(1,0)。 -/
@[simp] theorem minusBlockLoop_period (l : LawValueLabel laws) : minusBlockPeriod l (minusBlockLoop l)=(1,0) := by
  simp only [minusBlockPeriod,minusBlockLoop,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,minusH1Period_mk,minusPeriod_section]
/-- minus e2 の実 period は(0,1)。 -/
@[simp] theorem minusBlockExtra_period (l : LawValueLabel laws) : minusBlockPeriod l (minusBlockExtra l)=(0,1) := by
  simp only [minusBlockPeriod,minusBlockExtra,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,minusH1Period_mk,minusPeriod_section]
/-- 同じ実 plus 比較は loop 単独類を同じ loop 単独類へ送る。 -/
theorem plus_maps_loop (l : LawValueLabel laws) : (plusBlockHom l).h1Map (oldBlockLoop l)=plusBlockLoop l := by
  apply (plusBlockPeriod l).injective
  rw [plus_block_identity,oldBlockLoop_period,plusBlockLoop_period]
/-- 同じ実 minus 比較も loop 単独類を同じ loop 単独類へ送る。 -/
theorem minus_maps_loop (l : LawValueLabel laws) : (minusBlockHom l).h1Map (oldBlockLoop l)=minusBlockLoop l := by
  apply (minusBlockPeriod l).injective
  rw [minus_block_injection,oldBlockLoop_period,minusBlockLoop_period]
/-- 粗 loop 単独類は実 block でも非零。 -/
theorem old_loop_nonzero (l : LawValueLabel laws) : oldBlockLoop l ≠ 0 := by
  intro hz
  have he := congrArg (oldBlockPeriod l) hz
  rw [oldBlockLoop_period,map_zero] at he
  exact one_ne_zero he
/-- plus loop 単独類は実 block でも非零。 -/
theorem plus_loop_nonzero (l : LawValueLabel laws) : plusBlockLoop l ≠ 0 := by
  intro hz
  have he := congrArg (plusBlockPeriod l) hz
  rw [plusBlockLoop_period,map_zero] at he
  exact one_ne_zero he
/-- minus loop 単独類は実 block でも非零。 -/
theorem minus_loop_nonzero (l : LawValueLabel laws) : minusBlockLoop l ≠ 0 := by
  intro hz
  have he := congrArg (minusBlockPeriod l) hz
  rw [minusBlockLoop_period,map_zero] at he
  exact one_ne_zero (congrArg Prod.fst he)
end AAT.AG.FaceRelationSubdivision.WitnessOne
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision.WitnessOne
