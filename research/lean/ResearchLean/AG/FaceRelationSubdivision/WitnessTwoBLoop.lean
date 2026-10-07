import ResearchLean.AG.FaceRelationSubdivision.WitnessTwoBPeriods
import ResearchLean.AG.FaceRelationSubdivision.LoopSubdivisionPeriod
import Formal.Util.AssertStandardAxioms

/-!
# W2b の実保持 k 類と同じ比較

## Implementation notes

細 period を同じ原始 s と実 cochain 代表の保持辺値に同定する。
loop 類は生成 r が送った実代表を使い、各細セル上の k 単独値を別途証明する。
期待の H¹ 値だけを細 period の定義として証拠にする方式は採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision.WitnessTwoB
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
open ConnectedFaceWitness (q laws adequate label)
/-- 細分後の同じ実 k 座標。 -/
def fineK (l) := retainedBlockCoordinate N false laws adequate l (oldK l) (oldK_retained l)
/-- 細 period も同じ実代表の保持 k 座標を読む。 -/
@[simp] theorem fineBlockPeriod_mk (l)
    (z : LinearMap.ker (fine.lawValueBlockComplex laws adequate l).d1) :
    fineBlockPeriod l ((LinearMap.range (fine.lawValueBlockComplex laws adequate l).boundaryToCycles).mkQ z)=z.val (fineK l) :=
  subdivisionFinePeriod_mk N false laws adequate l (oldBlockPeriod l) (oldK l)
    (oldK_retained l) (oldBlockPeriod_mk l) z
/-- 粗実 block の k 単独 cochain。 -/
def oldLoopCycle (l) : LinearMap.ker (N.lawValueBlockComplex laws adequate l).d1 :=
  (blockEquiv l).symm.toHom.cyclesMap (loopOnly 1)
/-- 粗実 cocycle はすべての生成座標で k 単独値を持つ。 -/
theorem oldLoopCycle_apply (l) (x : N.EdgeBlockCoordinate laws adequate l) :
    (oldLoopCycle l).val x=(loopOnly 1).val x.val.cell := by
  have he := congrFun ((blockEquiv l).e1.apply_symm_apply (loopOnly 1).val) x.val.cell
  have hv := fullBlockNamedEquivalence_e1 N laws adequate chart_full
    (fullSupport_edge N chart_full) (fullSupport_face N chart_full) l
    ((blockEquiv l).e1.symm (loopOnly 1).val) x.val.cell
  have hx : (fullBlockCoordinateEquiv laws q adequate N.edgeSupport
      (fullSupport_edge N chart_full) l).symm x.val.cell=x :=
    CellCoordinate.block_cell_injective laws q adequate _ _ l
      (fullBlockCoordinateEquiv_symm_cell _ _ _ _ _ _ _)
  rw [hx] at hv
  exact hv.symm.trans he
/-- 粗実 k 単独類。 -/
def oldLoopClass (l) := (LinearMap.range (N.lawValueBlockComplex laws adequate l).boundaryToCycles).mkQ (oldLoopCycle l)
/-- 同じ生成 r を同じ粗実 k 単独代表に作用させた細 cocycle。 -/
def fineLoopCycle (l) := (EdgeSubdivision.blockR N false laws adequate l).cyclesMap (oldLoopCycle l)
/-- 細実 cocycle の全生成座標は、保持 k だけに旧値を持つ。 -/
theorem fineLoopCycle_apply (l) (x : fine.EdgeBlockCoordinate laws adequate l) :
    (fineLoopCycle l).val x=match x.val.cell with
      | .inl a => (loopOnly 1).val a.val
      | .inr _ => 0 := by
  rw [fineLoopCycle,ThreeCochainComplex.Hom.cyclesMap_apply,EdgeSubdivision.blockR_f1]
  cases hx : x.val.cell with
  | inl a =>
    have hb : (EdgeSubdivision.r1 N false).basisImage x.val.cell=Finsupp.single a.val 1 := by
      rw [hx,EdgeSubdivision.r1_basis,EdgeSubdivision.edgeImage_old,rationalOptionCell_some]
    have hv := (EdgeSubdivision.r1 N false).lawBlockDual_apply_single laws adequate l
      (oldLoopCycle l).val x a.val hb
    exact hv.trans ((oldLoopCycle_apply l _).trans
      (congrArg (loopOnly 1).val ((EdgeSubdivision.r1 N false).lawBlockCoordinate_cell laws adequate l x a.val _)))
  | inr a =>
    cases a with
    | inl b =>
      cases b
      · exact SupportedBasisMap.lawBlockDual_apply_zero laws adequate _ l _ x (by
          rw [hx,EdgeSubdivision.r1_basis,EdgeSubdivision.edgeImage_c,rationalOptionCell_none])
      · have hb : (EdgeSubdivision.r1 N false).basisImage x.val.cell=Finsupp.single false 1 := by
          rw [hx,EdgeSubdivision.r1_basis,EdgeSubdivision.edgeImage_b,rationalOptionCell_some]
        have hv := (EdgeSubdivision.r1 N false).lawBlockDual_apply_single laws adequate l
          (oldLoopCycle l).val x false hb
        exact hv.trans ((oldLoopCycle_apply l _).trans
          (congrArg (loopOnly 1).val ((EdgeSubdivision.r1 N false).lawBlockCoordinate_cell laws adequate l x false _)))
    | inr o =>
      have hb : (EdgeSubdivision.r1 N false).basisImage x.val.cell=Finsupp.single false 1 := by
        rw [hx,EdgeSubdivision.r1_basis,EdgeSubdivision.edgeImage_diagonal,rationalOptionCell_some]
      have hv := (EdgeSubdivision.r1 N false).lawBlockDual_apply_single laws adequate l
        (oldLoopCycle l).val x false hb
      exact hv.trans ((oldLoopCycle_apply l _).trans
        (congrArg (loopOnly 1).val ((EdgeSubdivision.r1 N false).lawBlockCoordinate_cell laws adequate l x false _)))
/-- 同じ fine 実代表の類。 -/
def fineLoopClass (l) := (LinearMap.range (fine.lawValueBlockComplex laws adequate l).boundaryToCycles).mkQ (fineLoopCycle l)
/-- 粗 period は同じ k 単独代表で1。 -/
@[simp] theorem oldLoopClass_period (l) : oldBlockPeriod l (oldLoopClass l)=1 := by
  rw [oldLoopClass,oldBlockPeriod_mk]
  have he := (blockEquiv l).e1.apply_symm_apply (loopOnly 1).val
  have hk := congrFun he true
  have hv := fullBlockNamedEquivalence_e1 N laws adequate chart_full
    (fullSupport_edge N chart_full) (fullSupport_face N chart_full) l
    ((blockEquiv l).e1.symm (loopOnly 1).val) true
  exact hv.symm.trans hk
/-- 同じ実比較は同じ k 類を送る。 -/
theorem comparison_maps_loop (l) : (EdgeSubdivision.blockR N false laws adequate l).h1Map (oldLoopClass l)=fineLoopClass l :=
  ThreeCochainComplex.Hom.h1Map_mk _ _
/-- 細 k period は同じ保持類で1。 -/
@[simp] theorem fineLoopClass_period (l) : fineBlockPeriod l (fineLoopClass l)=1 := by
  rw [← comparison_maps_loop,block_period_identity,oldLoopClass_period]
/-- 粗実 k 単独類は非零。 -/
theorem old_loop_nonzero (l) : oldLoopClass l≠0 := by
  intro h
  have he := congrArg (oldBlockPeriod l) h
  rw [oldLoopClass_period,map_zero] at he
  exact one_ne_zero he
/-- 同じ細実保持 k 類も非零。 -/
theorem fine_loop_nonzero (l) : fineLoopClass l≠0 := by
  intro h
  have he := congrArg (fineBlockPeriod l) h
  rw [fineLoopClass_period,map_zero] at he
  exact one_ne_zero he
end AAT.AG.FaceRelationSubdivision.WitnessTwoB
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision.WitnessTwoB
