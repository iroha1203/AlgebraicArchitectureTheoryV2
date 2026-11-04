import ResearchLean.AG.SpecifiedRepairLifting.FreeWitnesses
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-! # 固定W3のtorsionと同じ有限整数入力

Implementation notes: 関係行列[4]の元商をZMod 4へ同定する。
有限集合での評価はこの両方向群同型を通して実Liftと実核へ戻す。
有理化やrankへの置換は使わず、原始関係を保持する。
-/
namespace AAT.AG.SpecifiedRepairLifting.TorsionWitness
open CategoryTheory Matrix IntegerElimination PresentedGroups PresentedComplex FiniteLifting FreeWitnesses
/-- 一生成元一関係の巡回整数表示。 -/
def cyclicPresentation (n : ℕ) : Presentation := ⟨1,1,!![(n : ℤ)]⟩
/-- 元整数座標を剰余へ送る線形射。 -/
def residueLinear (n : ℕ) : Vec 1 →ₗ[ℤ] ZMod n :=
  (Int.castAddHom (ZMod n)).toIntLinearMap.comp (LinearMap.proj 0)
/-- 剰余射は唯一の座標の整数cast。 -/
theorem residueLinear_apply (n : ℕ) (x : Vec 1) : residueLinear n x = (x 0 : ZMod n) := rfl
/-- 剰余射の実核は原始関係行列の像と一致する。 -/
theorem cyclic_relations (n : ℕ) : relationSpace (cyclicPresentation n) = LinearMap.ker (residueLinear n) := by
  ext x
  change (∃ u : Vec 1, (!![(n : ℤ)] : Mat 1 1) *ᵥ u = x) ↔ residueLinear n x = 0
  rw [residueLinear_apply,ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · rintro ⟨u,hu⟩
    refine ⟨u 0,?_⟩
    have h := congrFun hu 0
    simpa [mulVec,dotProduct] using h.symm
  · rintro ⟨k,hk⟩
    refine ⟨![k],?_⟩
    change (!![(n : ℤ)] : Mat 1 1) *ᵥ ![k] = x
    ext i
    fin_cases i
    simpa [mulVec,dotProduct] using hk.symm
/-- 原始商から剰余への同じ写像。 -/
def cyclicMap (n : ℕ) : PresentedGroups.Group (cyclicPresentation n) →ₗ[ℤ] ZMod n :=
  (relationSpace (cyclicPresentation n)).liftQ (residueLinear n) (le_of_eq (cyclic_relations n))
/-- 原始代表に対する商写像の値。 -/
theorem cyclicMap_class (n : ℕ) (x : Vec 1) :
    cyclicMap n (quotientClass (cyclicPresentation n) x) = (x 0 : ZMod n) := rfl
/-- 原始商から剰余への写像は単射。 -/
theorem cyclicMap_injective (n : ℕ) : Function.Injective (cyclicMap n) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  obtain ⟨x,rfl⟩ := class_surjective (cyclicPresentation n) a
  apply (class_zero_iff _ _).mpr
  have hx : x ∈ LinearMap.ker (residueLinear n) := ha
  rw [← cyclic_relations] at hx
  exact hx
/-- 剰余の全元が原始整数代表から来る。 -/
theorem cyclicMap_surjective (n : ℕ) : Function.Surjective (cyclicMap n) := by
  intro a
  obtain ⟨x,hx⟩ := ZMod.intCast_surjective a
  refine ⟨quotientClass (cyclicPresentation n) ![x],?_⟩
  rw [cyclicMap_class]
  exact hx
/-- 同じ原始巡回商とZModの群同型。 -/
noncomputable def cyclicEquiv (n : ℕ) : PresentedGroups.Group (cyclicPresentation n) ≃+ ZMod n :=
  (LinearEquiv.ofBijective (cyclicMap n) ⟨cyclicMap_injective n,cyclicMap_surjective n⟩).toAddEquiv
/-- 同型は同じ整数剰余を取る。 -/
theorem cyclicEquiv_class (n : ℕ) (x : Vec 1) :
    cyclicEquiv n (quotientClass (cyclicPresentation n) x) = (x 0 : ZMod n) := rfl

/-- W3の元複体は零次Z/4で正次数は零。 -/
def w3C : ComplexData := ⟨cyclicPresentation 4,freePresentation 0,freePresentation 0,0,0⟩
/-- W3の比較は原始整数行列[2]。 -/
def w3Comparison : ComparisonData w3C w3C := ⟨!![2],0,0⟩
/-- b=1の全入力条件。 -/
theorem w3_input_one : InputValid w3C w3C w3Comparison 0 ![1] := by decide
/-- b=2の全入力条件。 -/
theorem w3_input_two : InputValid w3C w3C w3Comparison 0 ![2] := by decide
/-- 同じ実比較。 -/
def w3Map := comparison w3_input_one.1 w3_input_one.2.1 w3Comparison w3_input_one.2.2.1
/-- 元の零次群上での指定Lift。 -/
abbrev W3Lift (b : ℤ) := NonnegativeLift w3Map
  (quotientClass (freePresentation 0) 0) (quotientClass (cyclicPresentation 4) ![b])
/-- W3の微分は同じ元群上で零。 -/
theorem w3_d_apply (a : PresentedGroups.Group (cyclicPresentation 4)) :
    (native w3C w3_input_one.1).d 0 1 a = quotientClass (freePresentation 0) 0 := by
  apply (freeEquiv 0).injective
  exact Subsingleton.elim _ _
/-- W3の実比較を同じ剰余座標で評価する。 -/
theorem w3_map_coordinates (a : PresentedGroups.Group (cyclicPresentation 4)) :
    cyclicEquiv 4 (w3Map.f 0 a) = 2 * cyclicEquiv 4 a := by
  obtain ⟨x,rfl⟩ := class_surjective (cyclicPresentation 4) a
  change cyclicEquiv 4 ((comparison w3_input_one.1 w3_input_one.2.1 w3Comparison w3_input_one.2.2.1).f 0
    (quotientClass w3C.P0 x)) = _
  rw [comparison_apply0]
  change cyclicEquiv 4 (quotientClass (cyclicPresentation 4) ((!![2] : Mat 1 1) *ᵥ x)) = _
  rw [cyclicEquiv_class,cyclicEquiv_class]
  simp [mulVec,dotProduct]
/-- 二つの元群の補正式は同じZ/4での2a=bに一致する。 -/
theorem w3_lift_iff (b : ℤ) (a : PresentedGroups.Group (cyclicPresentation 4)) :
    ((native w3C w3_input_one.1).d 0 1 a = quotientClass (freePresentation 0) 0 ∧
      w3Map.f 0 a = quotientClass (cyclicPresentation 4) ![b]) ↔
      2 * cyclicEquiv 4 a = (b : ZMod 4) := by
  rw [and_iff_right (w3_d_apply a),← (cyclicEquiv 4).injective.eq_iff,w3_map_coordinates,cyclicEquiv_class]
  rfl
/-- 固定b=1には実Liftが存在しない。 -/
theorem w3_one_no_lift : ¬ Nonempty (W3Lift 1) := by
  rintro ⟨a⟩
  have h := (w3_lift_iff 1 a.val).mp a.property
  have hn : ∀ x : ZMod 4, 2*x ≠ 1 := by decide
  exact hn _ h
/-- 固定b=2を実現する補正1。 -/
def w3LiftOne : W3Lift 2 := ⟨quotientClass (cyclicPresentation 4) ![1],by
  apply (w3_lift_iff 2 _).mpr
  rw [cyclicEquiv_class]
  decide⟩
/-- 同じ固定b=2を実現する補正3。 -/
def w3LiftThree : W3Lift 2 := ⟨quotientClass (cyclicPresentation 4) ![3],by
  apply (w3_lift_iff 2 _).mpr
  rw [cyclicEquiv_class]
  decide⟩
/-- 補正1と3は元商群でも異なる。 -/
theorem w3_lifts_distinct : w3LiftOne ≠ w3LiftThree := by
  intro h
  have he := congrArg (fun a : W3Lift 2 => cyclicEquiv 4 a.val) h
  change (1 : ZMod 4) = 3 at he
  contradiction
/-- 固定b=2の実Liftは1と3で尽くされる。 -/
theorem w3_all_lifts (a : W3Lift 2) : a = w3LiftOne ∨ a = w3LiftThree := by
  have h := (w3_lift_iff 2 a.val).mp a.property
  have hall : ∀ x : ZMod 4, 2*x = 2 → x = 1 ∨ x = 3 := by decide
  rcases hall _ h with he | he
  · left
    apply Subtype.ext
    apply (cyclicEquiv 4).injective
    exact he
  · right
    apply Subtype.ext
    apply (cyclicEquiv 4).injective
    exact he

#eval !(finiteSolve w3C w3C w3Comparison 0 ![1]).isLeft
#eval (finiteSolve w3C w3C w3Comparison 0 ![2]).isLeft
#eval !(finiteUnique w3C w3C w3Comparison 0 ![2])

/-- W3の微分は零写像。 -/
theorem w3_d_zero (a : PresentedGroups.Group (cyclicPresentation 4)) :
    (native w3C w3_input_one.1).d 0 1 a = 0 := by
  rw [w3_d_apply,map_zero]
/-- W3の零次cycle全体と元のZ/4の群同型。 -/
noncomputable def w3CyclesEquiv : zeroCycles (native w3C w3_input_one.1) ≃+ ZMod 4 where
  toFun a := cyclicEquiv 4 a.val
  invFun x := ⟨(cyclicEquiv 4).symm x,w3_d_zero _⟩
  left_inv a := Subtype.ext ((cyclicEquiv 4).symm_apply_apply a.val)
  right_inv x := (cyclicEquiv 4).apply_symm_apply x
  map_add' a b := map_add (cyclicEquiv 4) a.val b.val
/-- cycle同型の元群での評価。 -/
theorem w3CyclesEquiv_apply (a : zeroCycles (native w3C w3_input_one.1)) :
    w3CyclesEquiv a = cyclicEquiv 4 a.val := rfl
/-- cycle同型の逆は元群の同じ剰余を持つ。 -/
theorem w3CyclesEquiv_symm_coordinates (x : ZMod 4) :
    cyclicEquiv 4 (w3CyclesEquiv.symm x).val = x := (cyclicEquiv 4).apply_symm_apply x
/-- 実kの値を剰余で評価すると2倍になる。 -/
theorem w3_cycle_comparison (a : zeroCycles (native w3C w3_input_one.1)) :
    w3CyclesEquiv (cycleComparison w3Map a) = 2 * w3CyclesEquiv a :=
  w3_map_coordinates a.val
/-- Z/2をZ/4の偶数部分へ送る準同型。 -/
def evenEmbed : ZMod 2 →+ ZMod 4 where
  toFun x := if x = 0 then 0 else 2
  map_zero' := by decide
  map_add' := by decide
/-- 偶数部分への埋め込みは単射。 -/
theorem evenEmbed_injective : Function.Injective evenEmbed := by decide
/-- 偶数部分は2倍射の実核そのもの。 -/
theorem evenEmbed_range (x : ZMod 4) : (∃ t : ZMod 2, evenEmbed t = x) ↔ 2*x = 0 := by
  revert x
  decide
/-- Z/2から実CorrectionKernelへの群射。 -/
noncomputable def w3KernelHom : ZMod 2 →+ CorrectionKernel w3Map where
  toFun t := ⟨w3CyclesEquiv.symm (evenEmbed t),by
    apply w3CyclesEquiv.injective
    rw [map_zero,w3_cycle_comparison,w3CyclesEquiv.apply_symm_apply]
    exact (evenEmbed_range _).mp ⟨t,rfl⟩⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' t u := by
    apply Subtype.ext
    simp
/-- 実核射は同じ偶数剰余を取る。 -/
theorem w3KernelHom_coordinates (t : ZMod 2) :
    w3CyclesEquiv (w3KernelHom t).val = evenEmbed t := w3CyclesEquiv.apply_symm_apply _
/-- 実核射は単射。 -/
theorem w3KernelHom_injective : Function.Injective w3KernelHom := by
  intro t u h
  apply evenEmbed_injective
  simpa only [w3KernelHom_coordinates] using congrArg (fun k : CorrectionKernel w3Map => w3CyclesEquiv k.val) h
/-- 実核の全元がZ/2から来る。 -/
theorem w3KernelHom_surjective : Function.Surjective w3KernelHom := by
  intro h
  have hh : 2*w3CyclesEquiv h.val = 0 := by
    rw [← w3_cycle_comparison]
    have he : cycleComparison w3Map h.val = 0 := h.property
    rw [he,map_zero]
  obtain ⟨t,ht⟩ := (evenEmbed_range _).mpr hh
  refine ⟨t,?_⟩
  apply Subtype.ext
  apply w3CyclesEquiv.injective
  rw [w3KernelHom_coordinates]
  exact ht
/-- W3の実核{0,2}はZ/2と群同型。 -/
noncomputable def w3KernelEquiv : ZMod 2 ≃+ CorrectionKernel w3Map :=
  AddEquiv.ofBijective w3KernelHom ⟨w3KernelHom_injective,w3KernelHom_surjective⟩
/-- 実核同型の元群座標。 -/
theorem w3KernelEquiv_coordinates (t : ZMod 2) :
    cyclicEquiv 4 (w3KernelEquiv t).val.val = evenEmbed t := w3KernelHom_coordinates t
/-- W3の非零核元は補正1を補正3へ移す。 -/
theorem w3_action_one : addKernel w3Map (w3KernelEquiv 1) w3LiftOne = w3LiftThree := by
  apply Subtype.ext
  apply (cyclicEquiv 4).injective
  rw [addKernel_val,map_add,w3KernelEquiv_coordinates]
  change (1 : ZMod 4) + evenEmbed 1 = 3
  decide
/-- W3の全解は実核の自由推移作用で分類される。 -/
noncomputable def w3AllSolutions : ZMod 2 ≃ W3Lift 2 :=
  w3KernelEquiv.toEquiv.trans (kernelEquivLift w3Map w3LiftOne)

/-- 剰余4から剰余2への自然な射。 -/
def parity4 : ZMod 4 →+ ZMod 2 := (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)).toAddMonoidHom
/-- parityの零性は実2倍射の像への所属と同値。 -/
theorem parity4_zero_iff (x : ZMod 4) : parity4 x = 0 ↔ ∃ y : ZMod 4, 2*y = x := by
  revert x
  decide
/-- parityは全射。 -/
theorem parity4_surjective : Function.Surjective parity4 := by decide
/-- 実零次cycle上のparity。 -/
noncomputable def w3Parity : zeroCycles (native w3C w3_input_one.1) →+ ZMod 2 :=
  parity4.comp w3CyclesEquiv.toAddMonoidHom
/-- 実cycle上でのparityの評価。 -/
theorem w3Parity_apply (a : zeroCycles (native w3C w3_input_one.1)) :
    w3Parity a = parity4 (w3CyclesEquiv a) := rfl
/-- 実kの像はparityの実核そのもの。 -/
theorem w3_comparison_range : (cycleComparison w3Map).range = w3Parity.ker := by
  ext a
  change (∃ x, cycleComparison w3Map x = a) ↔ w3Parity a = 0
  rw [w3Parity_apply,parity4_zero_iff]
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨w3CyclesEquiv x,(w3_cycle_comparison x).symm⟩
  · rintro ⟨y,hy⟩
    refine ⟨w3CyclesEquiv.symm y,?_⟩
    apply w3CyclesEquiv.injective
    rw [w3_cycle_comparison,w3CyclesEquiv.apply_symm_apply]
    exact hy
/-- 実cycle上のparityも全射。 -/
theorem w3Parity_surjective : Function.Surjective w3Parity := by
  intro x
  obtain ⟨y,hy⟩ := parity4_surjective x
  refine ⟨w3CyclesEquiv.symm y,?_⟩
  rw [w3Parity_apply,w3CyclesEquiv.apply_symm_apply]
  exact hy
/-- W3の同じBの余核はZ/2と群同型。 -/
noncomputable def w3CokernelEquiv : CorrectionCokernel w3Map ≃+ ZMod 2 :=
  (QuotientAddGroup.quotientAddEquivOfEq w3_comparison_range).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective w3Parity w3Parity_surjective)
/-- 余核同型は同じcycleのparityを返す。 -/
theorem w3CokernelEquiv_class (a : zeroCycles (native w3C w3_input_one.1)) :
    w3CokernelEquiv (QuotientAddGroup.mk a) = parity4 (w3CyclesEquiv a) := rfl
/-- b=1の同じAの標準錐障害は非零。 -/
theorem w3_obstruction_one_ne_zero : nonnegativeObstruction w3Map
    (quotientClass (freePresentation 0) 0) (quotientClass (cyclicPresentation 4) ![1])
    (input_closed w3C w3C w3Comparison 0 ![1] w3_input_one)
    (input_compatible w3C w3C w3Comparison 0 ![1] w3_input_one) ≠ 0 := by
  intro h
  exact w3_one_no_lift ((nonnegativeObstruction_zero_iff_lift _ _ _ _ _).mp h)
/-- b=2の同じAの標準錐障害は零。 -/
theorem w3_obstruction_two_zero : nonnegativeObstruction w3Map
    (quotientClass (freePresentation 0) 0) (quotientClass (cyclicPresentation 4) ![2])
    (input_closed w3C w3C w3Comparison 0 ![2] w3_input_two)
    (input_compatible w3C w3C w3Comparison 0 ![2] w3_input_two) = 0 :=
  (nonnegativeObstruction_zero_iff_lift _ _ _ _ _).mpr ⟨w3LiftOne⟩

/-- 同じ余核同型は元補正0に対する残差をparityで評価する。 -/
theorem w3CokernelEquiv_residual (b : PresentedGroups.Group (cyclicPresentation 4))
    (hb : (native w3C w3_input_one.2.1).d 0 1 b =
      w3Map.f 1 (quotientClass (freePresentation 0) 0)) :
    w3CokernelEquiv (residualClass w3Map (quotientClass (freePresentation 0) 0) b 0
      (w3_d_apply 0) hb) = parity4 (cyclicEquiv 4 (b - (show PresentedGroups.Group (cyclicPresentation 4) from w3Map.f 0 0))) := rfl
/-- b=1の同じ余核残差はZ/2の非零元1。 -/
theorem w3_residual_one_coordinates :
    w3CokernelEquiv (residualClass w3Map (quotientClass (freePresentation 0) 0)
      (quotientClass (cyclicPresentation 4) ![1]) 0 (w3_d_apply 0)
      (input_compatible w3C w3C w3Comparison 0 ![1] w3_input_one)) = 1 := by
  rw [w3CokernelEquiv_residual,map_zero,sub_zero,cyclicEquiv_class]
  decide
/-- b=1の余核障害は実際に非零。 -/
theorem w3_residual_one_ne_zero :
    residualClass w3Map (quotientClass (freePresentation 0) 0)
      (quotientClass (cyclicPresentation 4) ![1]) 0 (w3_d_apply 0)
      (input_compatible w3C w3C w3Comparison 0 ![1] w3_input_one) ≠ 0 := by
  intro h
  have he := w3_residual_one_coordinates
  rw [h,map_zero] at he
  exact zero_ne_one he
/-- b=2の同じ余核残差は零。 -/
theorem w3_residual_two_zero :
    residualClass w3Map (quotientClass (freePresentation 0) 0)
      (quotientClass (cyclicPresentation 4) ![2]) 0 (w3_d_apply 0)
      (input_compatible w3C w3C w3Comparison 0 ![2] w3_input_two) = 0 :=
  (residualClass_zero_iff_lift _ _ _ _ _ _).mpr ⟨w3LiftOne⟩
/-- W3の元群は4倍で消えるtorsion群。 -/
theorem w3_four_smul (a : PresentedGroups.Group (cyclicPresentation 4)) : (4 : ℕ) • a = 0 := by
  apply (cyclicEquiv 4).injective
  rw [map_nsmul,map_zero]
  have h : ∀ x : ZMod 4, (4 : ℕ) • x = 0 := by decide
  exact h _
/-- W3の元群から有理加法群へのどの射も全元を零へ送る。 -/
theorem w3_rational_map_zero (g : PresentedGroups.Group (cyclicPresentation 4) →+ ℚ) : g = 0 := by
  ext a
  have h := congrArg g (w3_four_smul a)
  rw [map_nsmul,map_zero] at h
  norm_num [nsmul_eq_mul] at h ⊢
  exact h
/-- 同じ群・比較でも指定bだけでEの可解性は異なる。 -/
theorem w3_algorithm_distinguishes :
    (finiteSolve w3C w3C w3Comparison 0 ![1]).isLeft = false ∧
    (finiteSolve w3C w3C w3Comparison 0 ![2]).isLeft = true := by decide
/-- b=2に対するE特解は同じ二つの実補正のいずれか。 -/
theorem w3_decoded_two (x : Vec w3C.P0.generators)
    (hx : finiteSolve w3C w3C w3Comparison 0 ![2] = .inl x) :
    decodedSolution w3C w3C w3Comparison 0 ![2] w3_input_two x hx = w3LiftOne ∨
    decodedSolution w3C w3C w3Comparison 0 ![2] w3_input_two x hx = w3LiftThree :=
  w3_all_lifts _
/-- Eの計算核表示も同じZ/2の実核と群同型。 -/
noncomputable def w3ComputedKernelEquiv :
    PresentedGroups.Group (correctionPresentation w3C w3C w3Comparison) ≃+ ZMod 2 :=
  (computedKernelEquiv w3C w3C w3Comparison w3_input_one.1 w3_input_one.2.1 w3_input_one.2.2.1).trans
    w3KernelEquiv.symm

/-- W3の元群の整数rankは零。 -/
theorem w3_rank_zero : Module.rank ℤ (PresentedGroups.Group (cyclicPresentation 4)) = 0 := by
  apply (rank_eq_zero_iff_isTorsion (R := ℤ)).mpr
  intro a
  refine ⟨⟨4,by simp⟩,?_⟩
  exact_mod_cast w3_four_smul a
/-- W3の実有理化の各元は零。 -/
theorem w3_rationalization_zero
    (x : TensorProduct ℤ ℚ (PresentedGroups.Group (cyclicPresentation 4))) : x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => rfl
  | tmul q a =>
    have hq : (4 : ℤ) • (q/4) = q := by simp only [zsmul_eq_mul]; ring
    have ha : (4 : ℤ) • a = 0 := by exact_mod_cast w3_four_smul a
    calc
      TensorProduct.tmul ℤ q a = TensorProduct.tmul ℤ ((4 : ℤ) • (q/4)) a := by rw [hq]
      _ = TensorProduct.tmul ℤ (q/4) ((4 : ℤ) • a) := TensorProduct.smul_tmul _ _ _
      _ = 0 := by rw [ha,TensorProduct.tmul_zero]
  | add x y hx hy => rw [hx,hy,add_zero]
/-- b=1とb=2はどの有理診断でも区別されないが、Liftの有無は異なる。 -/
theorem w3_rational_diagnostic_loses_decision
    (g : PresentedGroups.Group (cyclicPresentation 4) →+ ℚ) :
    g (quotientClass (cyclicPresentation 4) ![1]) = g (quotientClass (cyclicPresentation 4) ![2]) ∧
      ¬ Nonempty (W3Lift 1) ∧ Nonempty (W3Lift 2) := by
  rw [w3_rational_map_zero g]
  exact ⟨rfl,w3_one_no_lift,⟨w3LiftOne⟩⟩
/-- 計算核表示を経由しても作用は同じ実核の加算。 -/
theorem w3_computed_action
    (t : PresentedGroups.Group (correctionPresentation w3C w3C w3Comparison)) (a : W3Lift 2) :
    addKernel w3Map
      (computedKernelEquiv w3C w3C w3Comparison w3_input_one.1 w3_input_one.2.1 w3_input_one.2.2.1 t) a =
    addKernel w3Map (w3KernelEquiv (w3ComputedKernelEquiv t)) a := by
  have h : w3KernelEquiv (w3ComputedKernelEquiv t) =
      computedKernelEquiv w3C w3C w3Comparison w3_input_one.1 w3_input_one.2.1 w3_input_one.2.2.1 t :=
    w3KernelEquiv.apply_symm_apply _
  rw [h]

/-- W3の全実核元の元群座標は0または2。 -/
theorem w3_kernel_coordinates (h : CorrectionKernel w3Map) :
    cyclicEquiv 4 h.val.val = 0 ∨ cyclicEquiv 4 h.val.val = 2 := by
  obtain ⟨t,rfl⟩ := w3KernelEquiv.surjective h
  rw [w3KernelEquiv_coordinates]
  have hall : ∀ t : ZMod 2, evenEmbed t = 0 ∨ evenEmbed t = 2 := by decide
  exact hall t
/-- 全解同値はBの同じ作用を用いる。 -/
theorem w3AllSolutions_apply (t : ZMod 2) :
    w3AllSolutions t = addKernel w3Map (w3KernelEquiv t) w3LiftOne := rfl
/-- 全解同値の零元は補正1。 -/
theorem w3AllSolutions_zero : w3AllSolutions 0 = w3LiftOne := by
  rw [w3AllSolutions_apply,map_zero w3KernelEquiv]
  apply Subtype.ext
  simp only [addKernel_val]
  exact add_zero _
/-- 全解同値の非零元は補正3。 -/
theorem w3AllSolutions_one : w3AllSolutions 1 = w3LiftThree := by
  rw [w3AllSolutions_apply]
  exact w3_action_one
/-- b=1の原始不能行。 -/
def w3FailureRow : Fin (PresentedProduct.product w3C.P1 w3C.P0).generators := ⟨0,by decide⟩
/-- b=1のEは不能行を実際に返す。 -/
theorem w3_solver_failure : finiteSolve w3C w3C w3Comparison 0 ![1] = .inr w3FailureRow := by decide
/-- b=1の不能証拠は非零対角への整除違反。 -/
theorem w3_divisibility_certificate :
    let M := equationMatrix w3C.P0 (PresentedProduct.product w3C.P1 w3C.P0) (jointMatrix w3C w3C w3Comparison)
    (produce M).diagonal w3FailureRow ≠ 0 ∧
      ¬ (produce M).diagonal w3FailureRow ∣ transformed (produce M) (jointValue w3C w3C 0 ![1]) w3FailureRow := by decide

end AAT.AG.SpecifiedRepairLifting.TorsionWitness

#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.cyclicPresentation
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.residueLinear
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.residueLinear_apply
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.cyclic_relations
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.cyclicMap
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.cyclicMap_class
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.cyclicMap_injective
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.cyclicMap_surjective
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.cyclicEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.cyclicEquiv_class
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3C
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3Comparison
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_input_one
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_input_two
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3Map
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.W3Lift
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_d_apply
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_map_coordinates
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_lift_iff
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_one_no_lift
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3LiftOne
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3LiftThree
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_lifts_distinct
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_all_lifts
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_d_zero
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3CyclesEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3CyclesEquiv_apply
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3CyclesEquiv_symm_coordinates
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_cycle_comparison
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.evenEmbed
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.evenEmbed_injective
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.evenEmbed_range
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3KernelHom
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3KernelHom_coordinates
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3KernelHom_injective
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3KernelHom_surjective
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3KernelEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3KernelEquiv_coordinates
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_action_one
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3AllSolutions
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.parity4
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.parity4_zero_iff
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.parity4_surjective
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3Parity
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3Parity_apply
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_comparison_range
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3Parity_surjective
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3CokernelEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3CokernelEquiv_class
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_obstruction_one_ne_zero
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_obstruction_two_zero
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3CokernelEquiv_residual
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_residual_one_coordinates
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_residual_one_ne_zero
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_residual_two_zero
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_four_smul
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_rational_map_zero
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_algorithm_distinguishes
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_decoded_two
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3ComputedKernelEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_rank_zero
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_rationalization_zero
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_rational_diagnostic_loses_decision
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_computed_action
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_kernel_coordinates
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3AllSolutions_apply
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3AllSolutions_zero
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3AllSolutions_one
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3FailureRow
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_solver_failure
#print axioms AAT.AG.SpecifiedRepairLifting.TorsionWitness.w3_divisibility_certificate
#assert_standard_axioms_only AAT.AG.SpecifiedRepairLifting.TorsionWitness
