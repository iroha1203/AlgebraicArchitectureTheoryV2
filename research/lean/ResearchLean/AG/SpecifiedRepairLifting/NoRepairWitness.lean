import ResearchLean.AG.SpecifiedRepairLifting.FreeWitnesses

/-! # 固定W4の元修復不能と標準錐

Implementation notes: 元のC⁰=0,C¹=ZとD=0を有限表示から生成する。
標準錐のcycleと標準homologyを実際に同定し、独自の障害群による代替を避ける。
-/
namespace AAT.AG.SpecifiedRepairLifting.NoRepairWitness
open CategoryTheory Matrix IntegerElimination PresentedGroups PresentedComplex FiniteLifting FreeWitnesses CochainComplex
/-- W4の元複体。 -/
def w4C : ComplexData := ⟨freePresentation 0,freePresentation 1,freePresentation 0,0,0⟩
/-- W4の診断複体は零。 -/
def w4D : ComplexData := ⟨freePresentation 0,freePresentation 0,freePresentation 0,0,0⟩
/-- W4の原始比較は零。 -/
def w4Comparison : ComparisonData w4C w4D := ⟨0,0,0⟩
/-- 元補正の存在なしに固定入力条件を生成する。 -/
theorem w4_input_valid : InputValid w4C w4D w4Comparison ![1] 0 := by decide
/-- 同じ実比較。 -/
def w4Map := comparison w4_input_valid.1 w4_input_valid.2.1 w4Comparison w4_input_valid.2.2.1
/-- 元のC⁰の各元は零。 -/
theorem w4_source_zero (a : (native w4C w4_input_valid.1).X 0) : a = 0 := by
  apply (freeEquiv 0).injective
  exact Subsingleton.elim _ _
/-- 診断D⁰の各元も零。 -/
theorem w4_target_zero (a : (native w4D w4_input_valid.2.1).X 0) : a = 0 := by
  apply (freeEquiv 0).injective
  exact Subsingleton.elim _ _
/-- W4の任意の元の微分は零。 -/
theorem w4_d_zero (a : (native w4C w4_input_valid.1).X 0) :
    (native w4C w4_input_valid.1).d 0 1 a = 0 := by rw [w4_source_zero a,map_zero]
/-- 固定元z=1は元群で非零。 -/
theorem w4_z_ne_zero : quotientClass (freePresentation 1) ![1] ≠ 0 := by
  intro h
  have he := congrArg (freeEquiv 1) h
  rw [freeEquiv_class,map_zero] at he
  exact Int.one_ne_zero (congrFun he 0)
/-- W4は指定補正以前に元の修復自体が存在しない。 -/
theorem w4_no_repair : ¬ ∃ a : (native w4C w4_input_valid.1).X 0,
    (native w4C w4_input_valid.1).d 0 1 a = quotientClass (freePresentation 1) ![1] := by
  rintro ⟨a,ha⟩
  rw [w4_d_zero] at ha
  exact w4_z_ne_zero ha.symm
/-- W4の同じ実Liftは空。 -/
theorem w4_no_lift : ¬ Nonempty (NonnegativeLift w4Map (quotientClass (freePresentation 1) ![1])
    (quotientClass (freePresentation 0) 0)) := by
  rintro ⟨a⟩
  exact w4_no_repair ⟨a.val,a.property.1⟩
/-- W4の同じ標準錐。 -/
noncomputable abbrev W4Cone := mappingCone (zeroExtensionMap _ _ w4Map)
/-- 標準錐の実零次cycle。 -/
noncomputable abbrev W4Cycles := LinearMap.ker (W4Cone.sc 0).g.hom
/-- W4の錐cycleの整数source座標。 -/
noncomputable def w4CycleCoordinate : W4Cycles →+ ℤ where
  toFun c := (freeEquiv 1 (nonnegativeConeCoordinateEquiv w4Map c.val).2) 0
  map_zero' := by simp
  map_add' a b := by simp
/-- 錐cycleの座標評価。 -/
theorem w4CycleCoordinate_apply (c : W4Cycles) :
    w4CycleCoordinate c = (freeEquiv 1 (nonnegativeConeCoordinateEquiv w4Map c.val).2) 0 := rfl
/-- W4のcycle座標は単射。 -/
theorem w4CycleCoordinate_injective : Function.Injective w4CycleCoordinate := by
  apply (injective_iff_map_eq_zero _).mpr
  intro c hc
  apply Subtype.ext
  apply (nonnegativeConeCoordinateEquiv w4Map).injective
  change nonnegativeConeCoordinateEquiv w4Map c.val = nonnegativeConeCoordinateEquiv w4Map 0
  rw [map_zero]
  apply Prod.ext
  · exact w4_target_zero _
  · apply (freeEquiv 1).injective
    change freeEquiv 1 (nonnegativeConeCoordinateEquiv w4Map c.val).2 = freeEquiv 1 0
    rw [map_zero]
    ext i
    fin_cases i
    exact hc
/-- W4の任意の一次cochainは閉じている。 -/
theorem w4_closed (z : (native w4C w4_input_valid.1).X 1) :
    (native w4C w4_input_valid.1).d 1 2 z = 0 := by
  apply (freeEquiv 0).injective
  exact Subsingleton.elim _ _
/-- W4の零診断は任意の一次cochainに適合する。 -/
theorem w4_compatible (z : (native w4C w4_input_valid.1).X 1) :
    (native w4D w4_input_valid.2.1).d 0 1 0 = w4Map.f 1 z := by
  apply (freeEquiv 0).injective
  exact Subsingleton.elim _ _
/-- W4のcycle整数座標は全射。 -/
theorem w4CycleCoordinate_surjective : Function.Surjective w4CycleCoordinate := by
  intro n
  refine ⟨nonnegativeSpecifiedCycle w4Map (-(quotientClass (freePresentation 1) ![n])) 0
    (w4_closed _) (w4_compatible _),?_⟩
  rw [w4CycleCoordinate_apply,nonnegativeSpecifiedCycle_coordinates]
  simp only [neg_neg,freeEquiv_class]
  rfl
/-- W4ではcycleから標準homologyへの写像も単射。 -/
theorem w4_class_injective : Function.Injective (moduleCycleClass (W4Cone.sc 0)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro c hc
  obtain ⟨a,_,ha⟩ := (coneCycleClass_zero_iff w4Map c).mp hc
  apply w4CycleCoordinate_injective
  rw [map_zero,w4CycleCoordinate_apply]
  rw [w4_d_zero,neg_zero] at ha
  rw [← ha,map_zero]
  rfl
/-- 標準H⁰錐と同じ整数座標の群同型。 -/
noncomputable def w4ConeEquiv : W4Cone.homology 0 ≃+ ℤ :=
  (AddEquiv.ofBijective (moduleCycleClass (W4Cone.sc 0))
    ⟨w4_class_injective,moduleCycleClass_surjective _⟩).symm.trans
    (AddEquiv.ofBijective w4CycleCoordinate ⟨w4CycleCoordinate_injective,w4CycleCoordinate_surjective⟩)
/-- 標準類の整数座標はcycleの同じ座標。 -/
theorem w4ConeEquiv_class (c : W4Cycles) :
    w4ConeEquiv (moduleCycleClass (W4Cone.sc 0) c) = w4CycleCoordinate c :=
  congrArg w4CycleCoordinate ((AddEquiv.ofBijective (moduleCycleClass (W4Cone.sc 0))
    ⟨w4_class_injective,moduleCycleClass_surjective _⟩).symm_apply_apply c)

/-- 固定W4の同じ標準障害。 -/
noncomputable def w4Obstruction : W4Cone.homology 0 :=
  nonnegativeObstruction w4Map (quotientClass (freePresentation 1) ![1]) 0
    (w4_closed _) (w4_compatible _)
/-- W4障害は同じ指定cycleの標準類。 -/
theorem w4Obstruction_class : w4Obstruction = moduleCycleClass (W4Cone.sc 0)
    (nonnegativeSpecifiedCycle w4Map (quotientClass (freePresentation 1) ![1]) 0
      (w4_closed _) (w4_compatible _)) := rfl
/-- W4の標準障害の整数座標は符号を含めて-1。 -/
theorem w4_obstruction_coordinates : w4ConeEquiv w4Obstruction = -1 := by
  rw [w4Obstruction_class,w4ConeEquiv_class,w4CycleCoordinate_apply,nonnegativeSpecifiedCycle_coordinates]
  simp only [map_neg,freeEquiv_class]
  rfl
/-- W4の標準錐障害は非零。 -/
theorem w4_obstruction_ne_zero : w4Obstruction ≠ 0 := by
  intro h
  have he := w4_obstruction_coordinates
  rw [h,map_zero] at he
  norm_num at he
/-- 元のz=1の標準H¹類も非零。 -/
theorem w4_oneClass_ne_zero : oneClass (quotientClass (freePresentation 1) ![1])
    (w4_closed _) ≠ 0 := by
  intro h
  have hc : moduleCycleClass ((native w4C w4_input_valid.1).sc 1)
      (oneCycle (quotientClass (freePresentation 1) ![1]) (w4_closed _)) = 0 := h
  obtain ⟨a,ha⟩ := (oneCycleClass_zero_iff _).mp hc
  exact w4_no_repair ⟨a,ha⟩
/-- 同じBのpはW4の障害を元の-[z]へ送る。 -/
theorem w4_projection_obstruction : coneProjection w4Map w4Obstruction =
    -oneClass (quotientClass (freePresentation 1) ![1]) (w4_closed _) :=
  coneProjection_obstruction w4Map _ _ _ _
/-- W4ではp(o)も非零。 -/
theorem w4_projection_ne_zero : coneProjection w4Map w4Obstruction ≠ 0 := by
  rw [w4_projection_obstruction,neg_ne_zero]
  exact w4_oneClass_ne_zero
/-- 原始算法が選ぶ不能行。 -/
def w4FailureRow : Fin (PresentedProduct.product w4C.P1 w4D.P0).generators := ⟨0,by decide⟩
/-- 同じEの実行結果は不能行0を返す。 -/
theorem w4_solver_failure : finiteSolve w4C w4D w4Comparison ![1] 0 = .inr w4FailureRow := by decide
/-- W4の不能証拠は実際に零行への非零右辺である。 -/
theorem w4_zero_row_certificate :
    let M := equationMatrix w4C.P0 (PresentedProduct.product w4C.P1 w4D.P0) (jointMatrix w4C w4D w4Comparison)
    (produce M).diagonal w4FailureRow = 0 ∧
      transformed (produce M) (jointValue w4C w4D ![1] 0) w4FailureRow ≠ 0 := by decide
#eval checkInput w4C w4D w4Comparison ![1] 0
#eval !(finiteSolve w4C w4D w4Comparison ![1] 0).isLeft
#eval !(finiteUnique w4C w4D w4Comparison ![1] 0)

end AAT.AG.SpecifiedRepairLifting.NoRepairWitness

#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4C
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4D
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4Comparison
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4_input_valid
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4Map
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4_source_zero
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4_target_zero
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4_d_zero
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4_z_ne_zero
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4_no_repair
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4_no_lift
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.W4Cone
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.W4Cycles
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4CycleCoordinate
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4CycleCoordinate_apply
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4CycleCoordinate_injective
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4_closed
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4_compatible
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4CycleCoordinate_surjective
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4_class_injective
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4ConeEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4ConeEquiv_class
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4Obstruction
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4Obstruction_class
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4_obstruction_coordinates
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4_obstruction_ne_zero
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4_oneClass_ne_zero
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4_projection_obstruction
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4_projection_ne_zero
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4FailureRow
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4_solver_failure
#print axioms AAT.AG.SpecifiedRepairLifting.NoRepairWitness.w4_zero_row_certificate
#assert_standard_axioms_only AAT.AG.SpecifiedRepairLifting.NoRepairWitness
