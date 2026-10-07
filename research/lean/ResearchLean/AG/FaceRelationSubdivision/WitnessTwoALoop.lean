import ResearchLean.AG.FaceRelationSubdivision.WitnessTwoAPeriods
import ResearchLean.AG.FaceRelationSubdivision.LoopSubdivisionPeriod
import Formal.Util.AssertStandardAxioms

/-!
# W2a の元ラベルを保持する実 k 類

## Implementation notes

singleton の実 cocycle 商を元の Law block の三成分同型で移す。
細側は同じ原始 r を実代表に作用させ、その H¹ 写像が非零類を保つことを検証する。
支持の異なる二ラベルを同一全台の入力へ置き換える方式は採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision.WitnessTwoA
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
open ConnectedFaceWitness (q laws adequate label label_fiber)
/-- alpha の k 単独 cochain を同じ実 singleton 複体へ読む。 -/
def alphaLoopCycle : LinearMap.ker (N.targetSubsetComplex {false}).d1 :=
  alphaEquiv.symm.toHom.cyclesMap (WitnessThree.loopOnly 1)
/-- alpha の実代表は全選択辺で同じ原始 k 単独 cochain を読む。 -/
theorem alphaLoopCycle_apply (e : N.EdgeInTargetSubset {false}) :
    alphaLoopCycle.val e=(WitnessThree.loopOnly 1).val e.val :=
  pointSubsetNamedEquiv_symm_e1 N false alpha_common (WitnessThree.loopOnly 1).val e
/-- alpha の period は同じ k 単独類で1。 -/
theorem alpha_loop_period : alphaPeriod
    ((LinearMap.range (N.targetSubsetComplex {false}).boundaryToCycles).mkQ alphaLoopCycle)=1 := by
  rw [alphaPeriod_mk]
  have he := congrFun (alphaEquiv.e1.apply_symm_apply (WitnessThree.loopOnly 1).val) (3 : Fin 4)
  have hv := pointSubsetNamedEquiv_e1 N false alpha_common
    (alphaEquiv.e1.symm (WitnessThree.loopOnly 1).val) (3 : Fin 4)
  exact hv.symm.trans he
/-- 各 singleton の実 H¹ period。同じ支持選択を保つ。 -/
def subsetPeriod (a : Bool) : (N.targetSubsetComplex {a}).H1 ≃ₗ[ℚ] ℚ := by
  cases a
  · exact alphaPeriod
  · exact betaPeriod
/-- 各 singleton の実 k 単独 cocycle。 -/
def subsetLoopCycle (a : Bool) : LinearMap.ker (N.targetSubsetComplex {a}).d1 := by
  cases a
  · exact alphaLoopCycle
  · exact betaLoopOnly 1
/-- 指定二支持の実 period は k 単独 cocycle で1。 -/
theorem subset_loop_period (a : Bool) : subsetPeriod a
    ((LinearMap.range (N.targetSubsetComplex {a}).boundaryToCycles).mkQ (subsetLoopCycle a))=1 := by
  cases a
  · exact alpha_loop_period
  · exact betaLoopPeriod_loopOnly 1
/-- 同じ元発生ラベル block とその実 singleton 複体の全三成分同定。 -/
def blockEquiv (a : Bool) : ThreeCochainComplex.CochainEquiv
    (N.lawValueBlockComplex laws adequate (label a)) (N.targetSubsetComplex {a}) :=
  N.lawValueBlockSubsetEquivOfEq laws adequate (label a) {a} (label_fiber a)
/-- 元ラベルの独立実旧 block H¹ の period。 -/
def oldBlockPeriod (a : Bool) := (blockEquiv a).h1Equiv.trans (subsetPeriod a)
/-- 同じ原始 k の実 singleton 座標。 -/
def subsetK (a : Bool) : N.EdgeInTargetSubset {a} := by
  cases a
  · exact alphaK
  · exact betaK
/-- 両側支持の同じ旧 period は同じ実 k 値を読む。 -/
theorem subsetPeriod_mk (a : Bool) (z : LinearMap.ker (N.targetSubsetComplex {a}).d1) :
    subsetPeriod a ((LinearMap.range (N.targetSubsetComplex {a}).boundaryToCycles).mkQ z)=z.val (subsetK a) := by
  cases a
  · exact alphaPeriod_mk z
  · exact betaPeriod_mk z
/-- 元ラベルから生成した実旧 k 座標。 -/
def oldK (a : Bool) := N.labelFiberEdgeOfEq laws adequate (label a) {a} (label_fiber a) (subsetK a)
/-- 旧 k 座標の原始辺名。 -/
@[simp] theorem oldK_cell (a : Bool) : (oldK a).val.cell=(3 : Fin 4) := by
  rw [oldK,N.labelFiberEdgeOfEq_cell]
  cases a <;> rfl
/-- k は e と別名の保持辺である。 -/
theorem oldK_retained (a : Bool) : (oldK a).val.cell≠(0 : Fin 4) := by
  rw [oldK_cell]
  decide
/-- 同じ実旧 block period は実代表の k 値を読む。 -/
theorem oldBlockPeriod_mk (a : Bool) (z : LinearMap.ker (N.lawValueBlockComplex laws adequate (label a)).d1) :
    oldBlockPeriod a ((LinearMap.range (N.lawValueBlockComplex laws adequate (label a)).boundaryToCycles).mkQ z)=z.val (oldK a) := by
  rw [oldBlockPeriod,LinearEquiv.trans_apply,ThreeCochainComplex.CochainEquiv.h1Equiv_apply,
    ThreeCochainComplex.Hom.h1Map_mk,subsetPeriod_mk,ThreeCochainComplex.Hom.cyclesMap_apply]
  exact N.lawValueBlockSubsetEquivOfEq_e1 laws adequate (label a) {a} (label_fiber a) z.val (subsetK a)
/-- 同じ独立実細比較の逆から得る fine period。 -/
def fineBlockPeriod (a : Bool) := subdivisionFinePeriod N (0 : Fin 4) laws adequate (label a) (oldBlockPeriod a)
/-- 細側の同じ保持 k の実座標。 -/
def fineK (a : Bool) := retainedBlockCoordinate N (0 : Fin 4) laws adequate (label a) (oldK a) (oldK_retained a)
/-- 細側 period は同じ実代表の保持 k 値を読む。 -/
theorem fineBlockPeriod_mk (a : Bool) (z : LinearMap.ker (fine.lawValueBlockComplex laws adequate (label a)).d1) :
    fineBlockPeriod a ((LinearMap.range (fine.lawValueBlockComplex laws adequate (label a)).boundaryToCycles).mkQ z)=z.val (fineK a) :=
  subdivisionFinePeriod_mk N (0 : Fin 4) laws adequate (label a) (oldBlockPeriod a) (oldK a)
    (oldK_retained a) (oldBlockPeriod_mk a) z
/-- 同じ原始旧 k 単独 cocycle を実 block に移す。 -/
def oldLoopCycle (a : Bool) := (blockEquiv a).symm.toHom.cyclesMap (subsetLoopCycle a)
/-- 両 singleton の実代表は同じ k 単独値を持つ。 -/
theorem subsetLoopCycle_apply (a : Bool) (e : N.EdgeInTargetSubset {a}) :
    (subsetLoopCycle a).val e=if e.val=(3 : Fin 4) then 1 else 0 := by
  cases a
  · rw [subsetLoopCycle,alphaLoopCycle_apply]
    rcases e with ⟨e,he⟩
    fin_cases e <;> rfl
  · rfl
/-- 粗実 cocycle はすべての生成座標で k 単独値を持つ。 -/
theorem oldLoopCycle_apply (a : Bool) (x : N.EdgeBlockCoordinate laws adequate (label a)) :
    (oldLoopCycle a).val x=if x.val.cell=(3 : Fin 4) then 1 else 0 := by
  obtain ⟨e,rfl⟩ := N.labelFiberEdgeOfEq_surjective laws adequate (label a) {a} (label_fiber a) x
  rw [oldLoopCycle,ThreeCochainComplex.Hom.cyclesMap_apply]
  have he := N.lawValueBlockSubsetEquivOfEq_symm_e1 laws adequate (label a) {a}
    (label_fiber a) (subsetLoopCycle a).val e
  exact he.trans ((subsetLoopCycle_apply a e).trans
    (congrArg (fun k : Fin 4 => if k=3 then (1 : ℚ) else 0)
      (N.labelFiberEdgeOfEq_cell laws adequate (label a) {a} (label_fiber a) e).symm))
/-- 同じ実粗 k 単独類。 -/
def oldLoopClass (a : Bool) :=
  (LinearMap.range (N.lawValueBlockComplex laws adequate (label a)).boundaryToCycles).mkQ (oldLoopCycle a)
/-- 同じ生成 r が送る実細 cocycle。 -/
def fineLoopCycle (a : Bool) := (EdgeSubdivision.blockR N (0 : Fin 4) laws adequate (label a)).cyclesMap (oldLoopCycle a)
/-- 細実 cocycle の全生成座標は、保持 k だけに旧値を持つ。 -/
theorem fineLoopCycle_apply (a : Bool) (x : fine.EdgeBlockCoordinate laws adequate (label a)) :
    (fineLoopCycle a).val x=match x.val.cell with
      | .inl k => if k.val=(3 : Fin 4) then 1 else 0
      | .inr _ => 0 := by
  rw [fineLoopCycle,ThreeCochainComplex.Hom.cyclesMap_apply,EdgeSubdivision.blockR_f1]
  cases hx : x.val.cell with
  | inl k =>
    have hb : (EdgeSubdivision.r1 N (0 : Fin 4)).basisImage x.val.cell=Finsupp.single k.val 1 := by
      rw [hx,EdgeSubdivision.r1_basis,EdgeSubdivision.edgeImage_old,rationalOptionCell_some]
    have hv := (EdgeSubdivision.r1 N (0 : Fin 4)).lawBlockDual_apply_single laws adequate (label a)
      (oldLoopCycle a).val x k.val hb
    rw [oldLoopCycle_apply,SupportedBasisMap.lawBlockCoordinate_cell] at hv
    exact hv
  | inr k =>
    cases k with
    | inl b =>
      cases b
      · exact SupportedBasisMap.lawBlockDual_apply_zero laws adequate _ (label a) _ x (by
          rw [hx,EdgeSubdivision.r1_basis,EdgeSubdivision.edgeImage_c,rationalOptionCell_none])
      · have hb : (EdgeSubdivision.r1 N (0 : Fin 4)).basisImage x.val.cell=Finsupp.single (0 : Fin 4) 1 := by
          rw [hx,EdgeSubdivision.r1_basis,EdgeSubdivision.edgeImage_b,rationalOptionCell_some]
        have hv := (EdgeSubdivision.r1 N (0 : Fin 4)).lawBlockDual_apply_single laws adequate (label a)
          (oldLoopCycle a).val x (0 : Fin 4) hb
        rw [oldLoopCycle_apply,SupportedBasisMap.lawBlockCoordinate_cell] at hv
        exact hv.trans (if_neg (by decide))
    | inr o =>
      have hb : (EdgeSubdivision.r1 N (0 : Fin 4)).basisImage x.val.cell=Finsupp.single (0 : Fin 4) 1 := by
        rw [hx,EdgeSubdivision.r1_basis,EdgeSubdivision.edgeImage_diagonal,rationalOptionCell_some]
      have hv := (EdgeSubdivision.r1 N (0 : Fin 4)).lawBlockDual_apply_single laws adequate (label a)
        (oldLoopCycle a).val x (0 : Fin 4) hb
      rw [oldLoopCycle_apply,SupportedBasisMap.lawBlockCoordinate_cell] at hv
      exact hv.trans (if_neg (by decide))
/-- 同じ実細 k 類。 -/
def fineLoopClass (a : Bool) :=
  (LinearMap.range (fine.lawValueBlockComplex laws adequate (label a)).boundaryToCycles).mkQ (fineLoopCycle a)
/-- 同じ旧 block period は k 単独実類で1。 -/
@[simp] theorem oldLoopClass_period (a : Bool) : oldBlockPeriod a (oldLoopClass a)=1 := by
  have he := (blockEquiv a).toHom_h1Map_symm_h1Map
    ((LinearMap.range (N.targetSubsetComplex {a}).boundaryToCycles).mkQ (subsetLoopCycle a))
  have hp := congrArg (subsetPeriod a) he
  rw [ThreeCochainComplex.Hom.h1Map_mk] at hp
  exact hp.trans (subset_loop_period a)
/-- 同じ実比較は period 座標で恒等になる。 -/
theorem block_period_identity (a : Bool) (x : (N.lawValueBlockComplex laws adequate (label a)).H1) :
    fineBlockPeriod a ((EdgeSubdivision.blockR N (0 : Fin 4) laws adequate (label a)).h1Map x)=oldBlockPeriod a x := by
  have h : (EdgeSubdivision.blockOldH1Iso N (0 : Fin 4) laws adequate (label a)).toLinearEquiv x=
      (EdgeSubdivision.blockR N (0 : Fin 4) laws adequate (label a)).h1Map x := by
    rw [CategoryTheory.Iso.toLinearEquiv_apply,EdgeSubdivision.blockOldH1Iso_hom]
    rfl
  rw [← h]
  exact congrArg (oldBlockPeriod a)
    ((EdgeSubdivision.blockOldH1Iso N (0 : Fin 4) laws adequate (label a)).toLinearEquiv.symm_apply_apply x)
/-- 同じ独立実比較は k 単独類を同じ fine 実類へ送る。 -/
theorem comparison_maps_loop (a : Bool) :
    (EdgeSubdivision.blockR N (0 : Fin 4) laws adequate (label a)).h1Map (oldLoopClass a)=fineLoopClass a :=
  ThreeCochainComplex.Hom.h1Map_mk _ _
/-- 細 period は同じ保持 k 類で1。 -/
@[simp] theorem fineLoopClass_period (a : Bool) : fineBlockPeriod a (fineLoopClass a)=1 := by
  rw [← comparison_maps_loop,block_period_identity,oldLoopClass_period]
/-- 異なる二支持のそれぞれで旧 k 類は非零。 -/
theorem old_loop_nonzero (a : Bool) : oldLoopClass a≠0 := by
  intro h
  have he := congrArg (oldBlockPeriod a) h
  rw [oldLoopClass_period,map_zero] at he
  exact one_ne_zero he
/-- 同じ原始比較が保持する細 k 類も両ラベルで非零。 -/
theorem fine_loop_nonzero (a : Bool) : fineLoopClass a≠0 := by
  intro h
  have he := congrArg (fineBlockPeriod a) h
  rw [fineLoopClass_period,map_zero] at he
  exact one_ne_zero he
end AAT.AG.FaceRelationSubdivision.WitnessTwoA
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision.WitnessTwoA
