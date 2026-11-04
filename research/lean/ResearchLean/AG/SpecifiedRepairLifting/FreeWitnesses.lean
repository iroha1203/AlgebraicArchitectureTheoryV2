import ResearchLean.AG.SpecifiedRepairLifting.FiniteRepresentation

/-! # 固定された自由整数入力W2・W5・W6

Implementation notes: 原始整数表示をEの同じ入口へ渡し、関係なしの商を
元の整数座標へ同定して全解を評価する。実行例だけで全解証明を代替しない。
補正と非単射パラメータのfiberは別の数学対象として構成する。
-/
namespace AAT.AG.SpecifiedRepairLifting.FreeWitnesses
open CategoryTheory Matrix IntegerElimination PresentedGroups PresentedComplex PresentedProduct FiniteLifting
/-- 関係を持たない自由整数表示。 -/
def freePresentation (n : ℕ) : Presentation := ⟨n,0,0⟩
/-- 関係なし表示の関係像は零部分加群。 -/
theorem free_relations (n : ℕ) : relationSpace (freePresentation n) = ⊥ := by
  ext x
  constructor
  · rintro ⟨u,rfl⟩
    change (0 : Mat n 0) *ᵥ u = 0
    exact zero_mulVec u
  · intro hx
    have he : x = 0 := hx
    subst x
    exact ⟨0,by change (0 : Mat n 0) *ᵥ 0 = 0; exact mulVec_zero _⟩
/-- 関係なし商と元の整数座標の同型。 -/
noncomputable def freeEquiv (n : ℕ) : PresentedGroups.Group (freePresentation n) ≃ₗ[ℤ] Vec n :=
  (relationSpace (freePresentation n)).quotEquivOfEqBot (free_relations n)
/-- 自由表示の代表は同じ整数ベクトルへ復元される。 -/
theorem freeEquiv_class (n : ℕ) (x : Vec n) : freeEquiv n (quotientClass (freePresentation n) x) = x :=
  Submodule.quotEquivOfEqBot_apply_mk _ _ _
/-- 自由表示では元群等号が同じ整数座標の等号と一致する。 -/
theorem free_class_eq_iff (n : ℕ) (x y : Vec n) :
    quotientClass (freePresentation n) x = quotientClass (freePresentation n) y ↔ x = y := by
  rw [← (freeEquiv n).injective.eq_iff,freeEquiv_class,freeEquiv_class]
/-- W2の元複体、第三座標は微分に現れない。 -/
def w2C : ComplexData := ⟨freePresentation 3,freePresentation 1,freePresentation 0,!![-1,1,0],0⟩
/-- W2の診断複体。 -/
def w2D : ComplexData := ⟨freePresentation 2,freePresentation 1,freePresentation 0,!![-1,1],0⟩
/-- W2の指定比較は最初の二座標の射影と一次恒等。 -/
def w2Comparison : ComparisonData w2C w2D := ⟨!![1,0,0;0,1,0],!![1],0⟩
/-- 固定W2の全関係・複体・cochain・T0を原始入力から検査する。 -/
theorem w2_input_valid : InputValid w2C w2D w2Comparison ![1] ![0,1] := by decide
/-- W2の同じ実cochain比較。 -/
def w2Map := comparison w2_input_valid.1 w2_input_valid.2.1 w2Comparison w2_input_valid.2.2.1
/-- 固定W2の同じ実Lift。 -/
abbrev W2Lift := NonnegativeLift w2Map (quotientClass (freePresentation 1) ![1])
  (quotientClass (freePresentation 2) ![0,1])
/-- 各整数wから固定W2の実補正(0,1,w)を構成する。 -/
def w2Lift (w : ℤ) : W2Lift := ⟨quotientClass (freePresentation 3) ![0,1,w],by
  constructor
  · change (native w2C w2_input_valid.1).d 0 1 (quotientClass w2C.P0 ![0,1,w]) = _
    rw [native_d0_class]
    apply congrArg (quotientClass (freePresentation 1))
    change (!![-1,1,0] : Mat 1 3) *ᵥ ![0,1,w] = ![1]
    ext i
    fin_cases i
    simp [mulVec,dotProduct,Fin.sum_univ_succ]
  · change (comparison w2_input_valid.1 w2_input_valid.2.1 w2Comparison w2_input_valid.2.2.1).f 0 (quotientClass w2C.P0 ![0,1,w]) = _
    rw [comparison_apply0]
    apply congrArg (quotientClass (freePresentation 2))
    change (!![1,0,0;0,1,0] : Mat 2 3) *ᵥ ![0,1,w] = ![0,1]
    ext i
    fin_cases i <;> simp [mulVec,dotProduct,Fin.sum_univ_succ]⟩
/-- 構成したW2補正の元整数座標。 -/
theorem w2Lift_coordinates (w : ℤ) : freeEquiv 3 (w2Lift w).val = ![0,1,w] := freeEquiv_class _ _
/-- W2の任意の実補正は最初の二座標が厳密に(0,1)。 -/
theorem w2_lift_coordinates (a : W2Lift) :
    freeEquiv 3 a.val = ![0,1,(freeEquiv 3 a.val) 2] := by
  obtain ⟨x,hx⟩ := class_surjective (freePresentation 3) a.val
  have hf := a.property.2
  change (comparison w2_input_valid.1 w2_input_valid.2.1 w2Comparison w2_input_valid.2.2.1).f 0 a.val = _ at hf
  rw [← hx] at hf
  change (comparison w2_input_valid.1 w2_input_valid.2.1 w2Comparison w2_input_valid.2.2.1).f 0 (quotientClass w2C.P0 x) = _ at hf
  rw [comparison_apply0] at hf
  have he := (free_class_eq_iff 2 _ _).mp hf
  change (!![1,0,0;0,1,0] : Mat 2 3) *ᵥ x = ![0,1] at he
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  simp [mulVec,dotProduct,Fin.sum_univ_succ] at h0 h1
  rw [← hx,freeEquiv_class]
  change x = (![0,1,(show Vec 3 from x) 2] : Vec 3)
  ext i
  fin_cases i
  · simpa using h0
  · simpa using h1
  · rfl
/-- W2の全Liftと全整数wの両方向同値。 -/
noncomputable def w2LiftEquiv : ℤ ≃ W2Lift where
  toFun := w2Lift
  invFun a := (freeEquiv 3 a.val) 2
  left_inv w := by simp only [w2Lift_coordinates]; rfl
  right_inv a := by
    apply Subtype.ext
    apply (freeEquiv 3).injective
    rw [w2Lift_coordinates]
    exact (w2_lift_coordinates a).symm
/-- W2には同じ指定補正を実現する異なる二解がある。 -/
theorem w2_distinct : w2Lift 0 ≠ w2Lift 1 := by
  intro h
  have he := w2LiftEquiv.injective h
  exact Int.zero_ne_one he

/-- W2の整数と実核の同値は同じ基点からの実差で与える。 -/
noncomputable def w2KernelEquiv : ℤ ≃+ CorrectionKernel w2Map :=
  { w2LiftEquiv.trans (kernelEquivLift w2Map (w2Lift 0)).symm with
    map_add' := by
      intro u v
      apply Subtype.ext
      apply Subtype.ext
      apply (freeEquiv 3).injective
      change freeEquiv 3 ((w2Lift (u+v)).val - (w2Lift 0).val) =
        freeEquiv 3 (((w2Lift u).val - (w2Lift 0).val) + ((w2Lift v).val - (w2Lift 0).val))
      simp only [map_add,map_sub,w2Lift_coordinates]
      ext i
      fin_cases i <;> simp }
/-- 実核の座標は(0,0,w)。 -/
theorem w2KernelEquiv_coordinates (w : ℤ) :
    freeEquiv 3 (w2KernelEquiv w).val.val = ![0,0,w] := by
  change freeEquiv 3 ((w2Lift w).val - (w2Lift 0).val) = _
  simp only [map_sub,w2Lift_coordinates]
  ext i
  fin_cases i <;> simp
/-- W2のBの作用は自由な第三整数座標の加算そのもの。 -/
theorem w2_action (w t : ℤ) : addKernel w2Map (w2KernelEquiv t) (w2Lift w) = w2Lift (w+t) := by
  apply Subtype.ext
  apply (freeEquiv 3).injective
  simp only [addKernel_val,map_add,w2Lift_coordinates,w2KernelEquiv_coordinates]
  ext i
  fin_cases i <;> simp

/-- W2では同じBの余核残差が零である。 -/
theorem w2_residual_zero :
    residualClass w2Map (quotientClass (freePresentation 1) ![1])
      (quotientClass (freePresentation 2) ![0,1]) (w2Lift 0).val (w2Lift 0).property.1
      (input_compatible w2C w2D w2Comparison ![1] ![0,1] w2_input_valid) = 0 :=
  (residualClass_zero_iff_lift _ _ _ _ _ _).mpr ⟨w2Lift 0⟩
/-- Eが返す特解は同じ全解分類の(0,1,w)に入る。 -/
theorem w2_decoded_coordinates (x : Vec w2C.P0.generators)
    (hx : finiteSolve w2C w2D w2Comparison ![1] ![0,1] = .inl x) :
    freeEquiv 3 (decodedSolution w2C w2D w2Comparison ![1] ![0,1] w2_input_valid x hx).val =
      ![0,1,(freeEquiv 3 (decodedSolution w2C w2D w2Comparison ![1] ![0,1] w2_input_valid x hx).val) 2] :=
  w2_lift_coordinates _
/-- Eが生成した有限表示の核も同じ整数wの群である。 -/
noncomputable def w2ComputedKernelEquiv :
    PresentedGroups.Group (correctionPresentation w2C w2D w2Comparison) ≃+ ℤ :=
  (computedKernelEquiv w2C w2D w2Comparison w2_input_valid.1 w2_input_valid.2.1 w2_input_valid.2.2.1).trans
    w2KernelEquiv.symm

#eval checkInput w2C w2D w2Comparison ![1] ![0,1]
#eval (finiteSolve w2C w2D w2Comparison ![1] ![0,1]).isLeft
#eval !(finiteUnique w2C w2D w2Comparison ![1] ![0,1])

/-- W5の二つの非零微分を持つ複体。 -/
def w5C : ComplexData := ⟨freePresentation 1,freePresentation 2,freePresentation 1,!![1;0],!![0,1]⟩
/-- W5の比較は全三次数の恒等。 -/
def w5Comparison : ComparisonData w5C w5C := ⟨!![1],!![1,0;0,1],!![1]⟩
/-- 固定W5の入力条件は原始整数検査から成立する。 -/
theorem w5_input_valid : InputValid w5C w5C w5Comparison ![1,0] ![1] := by decide
/-- W5の同じ実比較。 -/
def w5Map := comparison w5_input_valid.1 w5_input_valid.2.1 w5Comparison w5_input_valid.2.2.1
/-- 固定W5の実Lift。 -/
abbrev W5Lift := NonnegativeLift w5Map (quotientClass (freePresentation 2) ![1,0])
  (quotientClass (freePresentation 1) ![1])
/-- W5の零次比較は元群上の恒等。 -/
theorem w5_map_apply (a : PresentedGroups.Group (freePresentation 1)) : w5Map.f 0 a = a := by
  obtain ⟨x,rfl⟩ := class_surjective (freePresentation 1) a
  change (comparison w5_input_valid.1 w5_input_valid.2.1 w5Comparison w5_input_valid.2.2.1).f 0
    (quotientClass w5C.P0 x) = _
  rw [comparison_apply0]
  apply congrArg (quotientClass (freePresentation 1))
  change (!![1] : Mat 1 1) *ᵥ x = x
  ext i
  fin_cases i
  simp [mulVec,dotProduct]
/-- W5の指定補正は元群の1で実現する。 -/
def w5Lift : W5Lift := ⟨quotientClass (freePresentation 1) ![1],by
  constructor
  · change (native w5C w5_input_valid.1).d 0 1 (quotientClass w5C.P0 ![1]) = _
    rw [native_d0_class]
    apply congrArg (quotientClass (freePresentation 2))
    change (!![1;0] : Mat 2 1) *ᵥ ![1] = ![1,0]
    ext i
    fin_cases i <;> simp [mulVec,dotProduct]
  · exact w5_map_apply _⟩
/-- W5では実補正自体が一意。 -/
theorem w5_unique (a : W5Lift) : a = w5Lift := by
  apply Subtype.ext
  have h := a.property.2
  rw [w5_map_apply] at h
  exact h
/-- W5の(0,1)は閉じておらず、次微分を捨てると受理対象が変わる。 -/
theorem w5_not_closed :
    (native w5C w5_input_valid.1).d 1 2 (quotientClass w5C.P1 ![0,1]) ≠ 0 := by
  rw [native_d1_class]
  have hm : w5C.d1 *ᵥ ![0,1] = ![1] := by
    change (!![0,1] : Mat 1 2) *ᵥ ![0,1] = ![1]
    ext i
    fin_cases i
    simp [mulVec,dotProduct,Fin.sum_univ_succ]
  rw [hm]
  intro h
  have he := congrArg (freeEquiv 1) h
  change freeEquiv 1 (quotientClass (freePresentation 1) ![1]) = freeEquiv 1 0 at he
  rw [freeEquiv_class,map_zero] at he
  exact Int.one_ne_zero (congrFun he 0)
/-- W5の次微分は非零。 -/
theorem w5_d1_ne_zero : (native w5C w5_input_valid.1).d 1 2 ≠ 0 := by
  intro h
  apply w5_not_closed
  rw [h]
  rfl
#eval checkInput w5C w5C w5Comparison ![1,0] ![1]
#eval !(checkInput w5C w5C w5Comparison ![0,1] ![1])
#eval (finiteSolve w5C w5C w5Comparison ![1,0] ![1]).isLeft
#eval finiteUnique w5C w5C w5Comparison ![1,0] ![1]

/-- W5の同じ標準錐障害は零。 -/
theorem w5_obstruction_zero : nonnegativeObstruction w5Map
    (quotientClass (freePresentation 2) ![1,0]) (quotientClass (freePresentation 1) ![1])
    (input_closed w5C w5C w5Comparison ![1,0] ![1] w5_input_valid)
    (input_compatible w5C w5C w5Comparison ![1,0] ![1] w5_input_valid) = 0 :=
  (nonnegativeObstruction_zero_iff_lift _ _ _ _ _).mpr ⟨w5Lift⟩
/-- W6の同じ整数恒等微分。 -/
def w6C : ComplexData := ⟨freePresentation 1,freePresentation 1,freePresentation 0,!![1],0⟩
/-- W6の比較は恒等。 -/
def w6Comparison : ComparisonData w6C w6C := ⟨!![1],!![1],0⟩
/-- W6の固定入力条件。 -/
theorem w6_input_valid : InputValid w6C w6C w6Comparison ![1] ![1] := by decide
/-- W6の同じ実比較。 -/
def w6Map := comparison w6_input_valid.1 w6_input_valid.2.1 w6Comparison w6_input_valid.2.2.1
/-- W6の実Lift。 -/
abbrev W6Lift := NonnegativeLift w6Map (quotientClass (freePresentation 1) ![1])
  (quotientClass (freePresentation 1) ![1])
/-- W6の零次比較は元群上の恒等。 -/
theorem w6_map_apply (a : PresentedGroups.Group (freePresentation 1)) : w6Map.f 0 a = a := by
  obtain ⟨x,rfl⟩ := class_surjective (freePresentation 1) a
  change (comparison w6_input_valid.1 w6_input_valid.2.1 w6Comparison w6_input_valid.2.2.1).f 0
    (quotientClass w6C.P0 x) = _
  rw [comparison_apply0]
  apply congrArg (quotientClass (freePresentation 1))
  change (!![1] : Mat 1 1) *ᵥ x = x
  ext i
  fin_cases i
  simp [mulVec,dotProduct]
/-- W6の実補正1。 -/
def w6Lift : W6Lift := ⟨quotientClass (freePresentation 1) ![1],by
  constructor
  · change (native w6C w6_input_valid.1).d 0 1 (quotientClass w6C.P0 ![1]) = _
    rw [native_d0_class]
    apply congrArg (quotientClass (freePresentation 1))
    change (!![1] : Mat 1 1) *ᵥ ![1] = ![1]
    ext i
    fin_cases i
    simp [mulVec,dotProduct]
  · exact w6_map_apply _⟩
/-- W6の実補正自体は一意。 -/
theorem w6_unique (a : W6Lift) : a = w6Lift := by
  apply Subtype.ext
  have h := a.property.2
  rw [w6_map_apply] at h
  exact h
/-- W6の非単射パラメータ射は二座標の和。 -/
def w6Rho : Vec 2 →+ ℤ where
  toFun x := x 0 + x 1
  map_zero' := by simp
  map_add' x y := by simp; abel
/-- パラメータ射の公開評価。 -/
theorem w6Rho_apply (x : Vec 2) : w6Rho x = x 0 + x 1 := rfl
/-- 実補正1を表示するパラメータfiber。 -/
abbrev W6Parameters := {x : Vec 2 // w6Rho x = 1}
/-- 任意整数nは同じ補正の表示(n,1-n)を与える。 -/
def w6Parameter (n : ℤ) : W6Parameters := ⟨![n,1-n],by rw [w6Rho_apply]; simp⟩
/-- パラメータの座標評価。 -/
theorem w6Parameter_val (n : ℤ) : (w6Parameter n).val = ![n,1-n] := rfl
/-- fiberは全整数と両方向に対応し、表示の多重性を保持する。 -/
def w6ParameterEquiv : ℤ ≃ W6Parameters where
  toFun := w6Parameter
  invFun x := x.val 0
  left_inv n := rfl
  right_inv x := by
    apply Subtype.ext
    have hx := x.property
    rw [w6Rho_apply] at hx
    ext i
    fin_cases i
    · rfl
    · change 1 - x.val 0 = x.val 1
      omega
/-- (0,1)と(1,0)は異なるが同じ補正を表示する。 -/
theorem w6_parameters_distinct : w6Parameter 0 ≠ w6Parameter 1 := by
  intro h
  exact Int.zero_ne_one (w6ParameterEquiv.injective h)
/-- パラメータ射の実核は整数群と同型。 -/
def w6ParameterKernelEquiv : ℤ ≃+ w6Rho.ker where
  toFun n := ⟨![n,-n],by change w6Rho ![n,-n] = 0; rw [w6Rho_apply]; simp⟩
  invFun x := x.val 0
  left_inv n := rfl
  right_inv x := by
    apply Subtype.ext
    have hx : w6Rho x.val = 0 := x.property
    rw [w6Rho_apply] at hx
    ext i
    fin_cases i
    · rfl
    · change -x.val 0 = x.val 1
      omega
  map_add' u v := by
    apply Subtype.ext
    ext i
    fin_cases i
    · rfl
    · change -(u+v) = -u + -v
      omega
/-- W6のパラメータ射は単射でない。 -/
theorem w6_rho_not_injective : ¬ Function.Injective w6Rho := by
  intro h
  have he := h ((w6Parameter 0).property.trans (w6Parameter 1).property.symm)
  exact w6_parameters_distinct (Subtype.ext he)

/-- 一整数座標と元の自由商群との群同型。 -/
noncomputable def integerClassEquiv : ℤ ≃+ PresentedGroups.Group (freePresentation 1) where
  toFun n := quotientClass (freePresentation 1) ![n]
  invFun a := (freeEquiv 1 a) 0
  left_inv n := by
    change freeEquiv 1 (quotientClass (freePresentation 1) ![n]) 0 = n
    rw [freeEquiv_class]
    rfl
  right_inv a := by
    apply (freeEquiv 1).injective
    rw [freeEquiv_class]
    ext i
    fin_cases i
    rfl
  map_add' n m := by
    rw [← map_add]
    apply congrArg (quotientClass (freePresentation 1))
    ext i
    fin_cases i
    rfl
/-- 整数同型は元商の同じ代表を返す。 -/
theorem integerClassEquiv_apply (n : ℤ) :
    integerClassEquiv n = quotientClass (freePresentation 1) ![n] := rfl
/-- W6の実C⁰を値域とするパラメータ射。 -/
noncomputable def w6CorrectionRho : Vec 2 →+ (native w6C w6_input_valid.1).X 0 :=
  integerClassEquiv.toAddMonoidHom.comp w6Rho
/-- 実C⁰への射は和の同じ商代表を取る。 -/
theorem w6CorrectionRho_apply (x : Vec 2) : w6CorrectionRho x = integerClassEquiv (w6Rho x) := rfl
/-- 同じ実補正1の逆像と整数座標fiberは一致する。 -/
theorem w6_parameter_iff (x : Vec 2) : w6CorrectionRho x = w6Lift.val ↔ w6Rho x = 1 := by
  rw [w6CorrectionRho_apply]
  change integerClassEquiv (w6Rho x) = integerClassEquiv 1 ↔ _
  exact integerClassEquiv.injective.eq_iff
/-- 元C⁰への実パラメータ射のfiber全体を整数で分類する。 -/
noncomputable def w6ActualParameterEquiv : ℤ ≃ {x : Vec 2 // w6CorrectionRho x = w6Lift.val} :=
  w6ParameterEquiv.trans
    { toFun := fun x => ⟨x.val,(w6_parameter_iff x.val).mpr x.property⟩
      invFun := fun x => ⟨x.val,(w6_parameter_iff x.val).mp x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
/-- 実C⁰を値域とした射でも同じ整数群が核を全て分類する。 -/
noncomputable def w6ActualKernelEquiv : ℤ ≃+ w6CorrectionRho.ker :=
  w6ParameterKernelEquiv.trans
    { toFun := fun x => ⟨x.val,by
        change w6CorrectionRho x.val = 0
        rw [w6CorrectionRho_apply]
        have h : w6Rho x.val = 0 := x.property
        rw [h,map_zero]⟩
      invFun := fun x => ⟨x.val,by
        change w6Rho x.val = 0
        apply integerClassEquiv.injective
        rw [map_zero]
        exact x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
/-- 計算されたW2核を整数へ復元しても同じBの作用になる。 -/
theorem w2_computed_action
    (t : PresentedGroups.Group (correctionPresentation w2C w2D w2Comparison)) (w : ℤ) :
    addKernel w2Map
      (computedKernelEquiv w2C w2D w2Comparison w2_input_valid.1 w2_input_valid.2.1 w2_input_valid.2.2.1 t)
      (w2Lift w) = w2Lift (w + w2ComputedKernelEquiv t) := by
  have h : w2KernelEquiv (w2ComputedKernelEquiv t) =
      computedKernelEquiv w2C w2D w2Comparison w2_input_valid.1 w2_input_valid.2.1 w2_input_valid.2.2.1 t :=
    w2KernelEquiv.apply_symm_apply _
  rw [← h]
  exact w2_action _ _

/-- W2の同じ標準錐障害も零。 -/
theorem w2_obstruction_zero : nonnegativeObstruction w2Map
    (quotientClass (freePresentation 1) ![1]) (quotientClass (freePresentation 2) ![0,1])
    (input_closed w2C w2D w2Comparison ![1] ![0,1] w2_input_valid)
    (input_compatible w2C w2D w2Comparison ![1] ![0,1] w2_input_valid) = 0 :=
  (nonnegativeObstruction_zero_iff_lift _ _ _ _ _).mpr ⟨w2Lift 0⟩
/-- W5の同じBの余核残差も零。 -/
theorem w5_residual_zero : residualClass w5Map
    (quotientClass (freePresentation 2) ![1,0]) (quotientClass (freePresentation 1) ![1])
    w5Lift.val w5Lift.property.1
    (input_compatible w5C w5C w5Comparison ![1,0] ![1] w5_input_valid) = 0 :=
  (residualClass_zero_iff_lift _ _ _ _ _ _).mpr ⟨w5Lift⟩
/-- W6の同じ標準錐障害は零。 -/
theorem w6_obstruction_zero : nonnegativeObstruction w6Map
    (quotientClass (freePresentation 1) ![1]) (quotientClass (freePresentation 1) ![1])
    (input_closed w6C w6C w6Comparison ![1] ![1] w6_input_valid)
    (input_compatible w6C w6C w6Comparison ![1] ![1] w6_input_valid) = 0 :=
  (nonnegativeObstruction_zero_iff_lift _ _ _ _ _).mpr ⟨w6Lift⟩
/-- W6の同じBの余核残差も零。 -/
theorem w6_residual_zero : residualClass w6Map
    (quotientClass (freePresentation 1) ![1]) (quotientClass (freePresentation 1) ![1])
    w6Lift.val w6Lift.property.1
    (input_compatible w6C w6C w6Comparison ![1] ![1] w6_input_valid) = 0 :=
  (residualClass_zero_iff_lift _ _ _ _ _ _).mpr ⟨w6Lift⟩
/-- W6のBが分類する実Liftの作用核は零。パラメータ核とは異なる。 -/
theorem w6_correction_kernel_zero : (cycleComparison w6Map).ker = ⊥ := by
  apply (nonempty_lift_unique_iff_kernel_zero w6Map w6Lift).mp
  exact ⟨fun a b => (w6_unique a).trans (w6_unique b).symm⟩
/-- W5の同じBの作用核も零。 -/
theorem w5_correction_kernel_zero : (cycleComparison w5Map).ker = ⊥ := by
  apply (nonempty_lift_unique_iff_kernel_zero w5Map w5Lift).mp
  exact ⟨fun a b => (w5_unique a).trans (w5_unique b).symm⟩
/-- W6の実fiber同値も指定した(n,1-n)を返す。 -/
theorem w6ActualParameterEquiv_val (n : ℤ) : (w6ActualParameterEquiv n).val = ![n,1-n] := rfl
/-- W6の実パラメータ核の同型は(n,-n)を返す。 -/
theorem w6ActualKernelEquiv_val (n : ℤ) : (w6ActualKernelEquiv n).val = ![n,-n] := rfl
/-- 実C⁰の同じ補正を表示する二つの異なる元。 -/
theorem w6_actual_parameters_distinct : w6ActualParameterEquiv 0 ≠ w6ActualParameterEquiv 1 := by
  intro h
  exact Int.zero_ne_one (w6ActualParameterEquiv.injective h)

/-- W5のE出力も同じ唯一の実補正1に一致する。 -/
theorem w5_decoded_eq (x : Vec w5C.P0.generators)
    (hx : finiteSolve w5C w5C w5Comparison ![1,0] ![1] = .inl x) :
    decodedSolution w5C w5C w5Comparison ![1,0] ![1] w5_input_valid x hx = w5Lift :=
  w5_unique _
/-- W5の非cocycle入力はEの実行入口でも拒否される。 -/
theorem w5_checked_reject : checkedSolve w5C w5C w5Comparison ![0,1] ![1] = none := by decide

end AAT.AG.SpecifiedRepairLifting.FreeWitnesses

#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.freePresentation
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.free_relations
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.freeEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.freeEquiv_class
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.free_class_eq_iff
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w2C
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w2D
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w2Comparison
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w2_input_valid
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w2Map
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.W2Lift
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w2Lift
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w2Lift_coordinates
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w2_lift_coordinates
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w2LiftEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w2_distinct
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w2KernelEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w2KernelEquiv_coordinates
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w2_action
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w2_residual_zero
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w2_decoded_coordinates
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w2ComputedKernelEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w5C
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w5Comparison
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w5_input_valid
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w5Map
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.W5Lift
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w5_map_apply
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w5Lift
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w5_unique
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w5_not_closed
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w5_d1_ne_zero
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w5_obstruction_zero
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w6C
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w6Comparison
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w6_input_valid
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w6Map
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.W6Lift
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w6_map_apply
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w6Lift
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w6_unique
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w6Rho
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w6Rho_apply
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.W6Parameters
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w6Parameter
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w6Parameter_val
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w6ParameterEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w6_parameters_distinct
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w6ParameterKernelEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w6_rho_not_injective
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.integerClassEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.integerClassEquiv_apply
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w6CorrectionRho
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w6CorrectionRho_apply
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w6_parameter_iff
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w6ActualParameterEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w6ActualKernelEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w2_computed_action
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w2_obstruction_zero
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w5_residual_zero
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w6_obstruction_zero
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w6_residual_zero
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w6_correction_kernel_zero
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w5_correction_kernel_zero
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w6ActualParameterEquiv_val
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w6ActualKernelEquiv_val
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w6_actual_parameters_distinct
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w5_decoded_eq
#print axioms AAT.AG.SpecifiedRepairLifting.FreeWitnesses.w5_checked_reject
#assert_standard_axioms_only AAT.AG.SpecifiedRepairLifting.FreeWitnesses
