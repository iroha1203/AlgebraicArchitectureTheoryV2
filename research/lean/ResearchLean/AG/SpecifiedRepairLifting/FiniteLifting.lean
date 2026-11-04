import ResearchLean.AG.SpecifiedRepairLifting.PresentedComplex
import ResearchLean.AG.SpecifiedRepairLifting.PresentedProduct

/-! # 原始有限表示の算法と同じ指定持ち上げの接続

Implementation notes: 二つの補正式は元C¹とD⁰の直積への射として束ねる。
直積表示の同型により指定z,bとの同時一致を元商群の等号として保持する。
生成したkernel表示をBの実CorrectionKernelへ同定して作用を接続する。
単なる整数系の解や補助変数の核を実Liftと定義する方法は採らない。
-/
namespace AAT.AG.SpecifiedRepairLifting.FiniteLifting
open CategoryTheory Matrix IntegerElimination PresentedGroups PresentedComplex PresentedProduct

variable (C D : ComplexData) (f : ComparisonData C D)
/-- 同じ二つの補正式を束ねる原始行列。 -/
def jointMatrix : Mat (C.P1.generators+D.P0.generators) C.P0.generators := above C.d0 f.f0
/-- 同じ二つの指定代表の連結。 -/
def jointValue (z : Vec C.P1.generators) (b : Vec D.P0.generators) := join z b
/-- 同じ原始入力の関係保存から束ねた射の関係保存を生成。 -/
theorem jointValid (hc : ComplexValid C) (hf : ComparisonValid f) :
    MapValid C.P0 (product C.P1 D.P0) (jointMatrix C D f) :=
  above_valid _ _ _ _ _ hc.1 hf.1
/-- 束ねた商射の等号は元の二つの厳密補正式そのもの。 -/
theorem jointEquation (hc : ComplexValid C) (hd : ComplexValid D) (hf : ComparisonValid f)
    (z : Vec C.P1.generators) (b : Vec D.P0.generators) (a : PresentedGroups.Group C.P0) :
    PresentedGroups.map C.P0 (product C.P1 D.P0) (jointMatrix C D f) (jointValid C D f hc hf) a =
      quotientClass (product C.P1 D.P0) (jointValue C D z b) ↔
    (native C hc).d 0 1 a = quotientClass C.P1 z ∧
      (comparison hc hd f hf).f 0 a = quotientClass D.P0 b := by
  rw [← (productEquiv C.P1 D.P0).injective.eq_iff]
  change productEquiv C.P1 D.P0
    (PresentedGroups.map C.P0 (product C.P1 D.P0) (above C.d0 f.f0) (above_valid _ _ _ _ _ hc.1 hf.1) a) =
    productEquiv C.P1 D.P0 (quotientClass (product C.P1 D.P0) (join z b)) ↔ _
  rw [above_map C.P0 C.P1 D.P0 C.d0 f.f0 hc.1 hf.1 a,productEquiv_class,first_join,second_join,Prod.mk.injEq,native_d,comparison_f]
  rfl
/-- 同じ実Liftと原始直積表示のFiberの両方向同値。 -/
def liftFiberEquiv (hc : ComplexValid C) (hd : ComplexValid D) (hf : ComparisonValid f)
    (z : Vec C.P1.generators) (b : Vec D.P0.generators) :
    NonnegativeLift (comparison hc hd f hf) (quotientClass C.P1 z) (quotientClass D.P0 b) ≃
      Fiber C.P0 (product C.P1 D.P0) (jointMatrix C D f) (jointValid C D f hc hf) (jointValue C D z b) where
  toFun a := ⟨a.val,(jointEquation C D f hc hd hf z b a.val).mpr a.property⟩
  invFun a := ⟨a.val,(jointEquation C D f hc hd hf z b a.val).mp a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
/-- 上の同値は元C⁰の補正を変更しない。 -/
theorem liftFiberEquiv_val (hc : ComplexValid C) (hd : ComplexValid D) (hf : ComparisonValid f)
    (z : Vec C.P1.generators) (b : Vec D.P0.generators)
    (a : NonnegativeLift (comparison hc hd f hf) (quotientClass C.P1 z) (quotientClass D.P0 b)) :
    (liftFiberEquiv C D f hc hd hf z b a).val = a.val := rfl
/-- 束ねた射の零性は元微分と元比較の同時零性。 -/
theorem jointZero (hc : ComplexValid C) (hd : ComplexValid D) (hf : ComparisonValid f)
    (a : PresentedGroups.Group C.P0) :
    PresentedGroups.map C.P0 (product C.P1 D.P0) (jointMatrix C D f) (jointValid C D f hc hf) a = 0 ↔
      (native C hc).d 0 1 a = 0 ∧ (comparison hc hd f hf).f 0 a = 0 := by
  have he := jointEquation C D f hc hd hf 0 0 a
  have hj : jointValue C D (0 : Vec C.P1.generators) (0 : Vec D.P0.generators) = 0 := by
    ext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [jointValue,join]
  simpa only [hj,map_zero] using he
/-- 束ねた元商射の実kernelはBの同じCorrectionKernel。 -/
def jointKernelEquiv (hc : ComplexValid C) (hd : ComplexValid D) (hf : ComparisonValid f) :
    LinearMap.ker (PresentedGroups.map C.P0 (product C.P1 D.P0) (jointMatrix C D f) (jointValid C D f hc hf)) ≃+
      CorrectionKernel (comparison hc hd f hf) where
  toFun x := ⟨⟨x.val,((jointZero C D f hc hd hf x.val).mp x.property).1⟩,
    Subtype.ext (((jointZero C D f hc hd hf x.val).mp x.property).2)⟩
  invFun x := ⟨x.val.val,(jointZero C D f hc hd hf x.val.val).mpr
    ⟨correctionKernel_d _ x,correctionKernel_f _ x⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
/-- 実kernel同定は元C⁰の値を保持する。 -/
theorem jointKernelEquiv_val (hc : ComplexValid C) (hd : ComplexValid D) (hf : ComparisonValid f)
    (x : LinearMap.ker (PresentedGroups.map C.P0 (product C.P1 D.P0) (jointMatrix C D f) (jointValid C D f hc hf))) :
    (jointKernelEquiv C D f hc hd hf x).val.val = x.val := rfl
/-- 原始入力から計算した実補正kernelの有限表示。 -/
def correctionPresentation : Presentation :=
  kernelPresentation C.P0 (product C.P1 D.P0) (jointMatrix C D f)
/-- 生成した有限表示をBの同じ実CorrectionKernelへ同定する。 -/
noncomputable def computedKernelEquiv (hc : ComplexValid C) (hd : ComplexValid D) (hf : ComparisonValid f) :
    PresentedGroups.Group (correctionPresentation C D f) ≃+ CorrectionKernel (comparison hc hd f hf) :=
  (PresentedGroups.kernelEquiv _ _ _ (jointValid C D f hc hf)).toAddEquiv.trans (jointKernelEquiv C D f hc hd hf)
/-- 生成核表示の代表の元C⁰への復元は計算した同じ行列。 -/
theorem computedKernelEquiv_class (hc : ComplexValid C) (hd : ComplexValid D) (hf : ComparisonValid f)
    (t : Vec (C.P0.generators+(product C.P1 D.P0).relations)) :
    (computedKernelEquiv C D f hc hd hf (quotientClass (correctionPresentation C D f) t)).val.val =
      quotientClass C.P0 (generatorMatrix C.P0 (product C.P1 D.P0) (jointMatrix C D f) *ᵥ t) := rfl
/-- 原始六群入力の指定補正に対する実行可能なsolver。 -/
def finiteSolve (z : Vec C.P1.generators) (b : Vec D.P0.generators) :=
  solvePresented C.P0 (product C.P1 D.P0) (jointMatrix C D f) (jointValue C D z b)
/-- solver成功時の同じ元C⁰補正から実Liftを生成する。 -/
def decodedSolution (z : Vec C.P1.generators) (b : Vec D.P0.generators) (h : InputValid C D f z b)
    (x : Vec C.P0.generators) (hx : finiteSolve C D f z b = .inl x) :
    NonnegativeLift (comparison h.1 h.2.1 f h.2.2.1) (quotientClass C.P1 z) (quotientClass D.P0 b) :=
  ⟨quotientClass C.P0 x,(jointEquation C D f h.1 h.2.1 h.2.2.1 z b _).mp
    (solvePresented_solution _ _ _ (jointValid C D f h.1 h.2.2.1) _ x hx)⟩
/-- 特解復元はsolverの元代表をそのまま元群へ送る。 -/
theorem decodedSolution_val (z : Vec C.P1.generators) (b : Vec D.P0.generators) (h : InputValid C D f z b)
    (x : Vec C.P0.generators) (hx : finiteSolve C D f z b = .inl x) :
    (decodedSolution C D f z b h x hx).val = quotientClass C.P0 x := rfl
/-- 全入力でsolver成功と同じ実Liftの非空性が一致する。 -/
theorem finiteSolve_complete (z : Vec C.P1.generators) (b : Vec D.P0.generators) (h : InputValid C D f z b) :
    (∃ x, finiteSolve C D f z b = .inl x) ↔
      Nonempty (NonnegativeLift (comparison h.1 h.2.1 f h.2.2.1) (quotientClass C.P1 z) (quotientClass D.P0 b)) := by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨decodedSolution C D f z b h x hx⟩
  · rintro ⟨a⟩
    apply (solvePresented_complete _ _ _ (jointValid C D f h.1 h.2.2.1) _).mpr
    exact ⟨a.val,(jointEquation C D f h.1 h.2.1 h.2.2.1 z b _).mpr a.property⟩
/-- 同じ標準錐障害の零性と原始入力の判定が一致する。 -/
theorem finiteSolve_obstruction (z : Vec C.P1.generators) (b : Vec D.P0.generators) (h : InputValid C D f z b) :
    (∃ x, finiteSolve C D f z b = .inl x) ↔
      nonnegativeObstruction (comparison h.1 h.2.1 f h.2.2.1) (quotientClass C.P1 z) (quotientClass D.P0 b)
        (input_closed C D f z b h) (input_compatible C D f z b h) = 0 := by
  rw [nonnegativeObstruction_zero_iff_lift,finiteSolve_complete C D f z b h]
/-- 生成した有限表示の全類を、元の実LiftへBの同じ作用で送る同値。 -/
noncomputable def computedLiftEquiv (z : Vec C.P1.generators) (b : Vec D.P0.generators) (h : InputValid C D f z b)
    (a : NonnegativeLift (comparison h.1 h.2.1 f h.2.2.1) (quotientClass C.P1 z) (quotientClass D.P0 b)) :
    PresentedGroups.Group (correctionPresentation C D f) ≃
      NonnegativeLift (comparison h.1 h.2.1 f h.2.2.1) (quotientClass C.P1 z) (quotientClass D.P0 b) :=
  (computedKernelEquiv C D f h.1 h.2.1 h.2.2.1).toEquiv.trans (kernelEquivLift _ a)
/-- 全解復元は元C⁰のa*+[Gt]であり、補助未知数の加法ではない。 -/
theorem computedLiftEquiv_class (z : Vec C.P1.generators) (b : Vec D.P0.generators) (h : InputValid C D f z b)
    (a : NonnegativeLift (comparison h.1 h.2.1 f h.2.2.1) (quotientClass C.P1 z) (quotientClass D.P0 b))
    (t : Vec (C.P0.generators+(product C.P1 D.P0).relations)) :
    (computedLiftEquiv C D f z b h a (quotientClass (correctionPresentation C D f) t)).val =
      (show PresentedGroups.Group C.P0 from a.val) + quotientClass C.P0 (generatorMatrix C.P0 (product C.P1 D.P0) (jointMatrix C D f) *ᵥ t) := rfl
/-- 原始入力の元補正の存在一意性判定。 -/
def finiteUnique (z : Vec C.P1.generators) (b : Vec D.P0.generators) : Bool :=
  uniquePresented C.P0 (product C.P1 D.P0) (jointMatrix C D f) (jointValue C D z b)
/-- 一意性判定は元の二つの厳密補正式に対する存在一意性。 -/
theorem finiteUnique_correct (z : Vec C.P1.generators) (b : Vec D.P0.generators) (h : InputValid C D f z b) :
    finiteUnique C D f z b = true ↔ ∃! a : (native C h.1).X 0,
      (native C h.1).d 0 1 a = quotientClass C.P1 z ∧
        (comparison h.1 h.2.1 f h.2.2.1).f 0 a = quotientClass D.P0 b := by
  rw [finiteUnique,uniquePresented_correct _ _ _ (jointValid C D f h.1 h.2.2.1)]
  simp only [jointEquation C D f h.1 h.2.1 h.2.2.1 z b]
  rfl


/-- 不能時には同じ実Liftが空である。 -/
theorem finiteSolve_no_solution (z : Vec C.P1.generators) (b : Vec D.P0.generators) (h : InputValid C D f z b)
    (i : Fin (product C.P1 D.P0).generators) (hi : finiteSolve C D f z b = .inr i) :
    ¬ Nonempty (NonnegativeLift (comparison h.1 h.2.1 f h.2.2.1) (quotientClass C.P1 z) (quotientClass D.P0 b)) := by
  rw [← finiteSolve_complete C D f z b h]
  rintro ⟨x,hx⟩
  rw [hi] at hx
  contradiction
/-- 不能行の証拠は同じ原始整数系の整除違反または零行矛盾。 -/
theorem finiteSolve_failure_kind (z : Vec C.P1.generators) (b : Vec D.P0.generators)
    (i : Fin (product C.P1 D.P0).generators) (hi : finiteSolve C D f z b = .inr i) :
    let M := equationMatrix C.P0 (product C.P1 D.P0) (jointMatrix C D f)
    ((produce M).diagonal i = 0 ∧ transformed (produce M) (jointValue C D z b) i ≠ 0) ∨
    ((produce M).diagonal i ≠ 0 ∧ ¬ (produce M).diagonal i ∣ transformed (produce M) (jointValue C D z b) i) :=
  solvePresented_failure_kind _ _ _ _ i hi
/-- 一意性判定はBの実Liftの非空かつ高々一元という条件と同じ。 -/
theorem finiteUnique_lift (z : Vec C.P1.generators) (b : Vec D.P0.generators) (h : InputValid C D f z b) :
    finiteUnique C D f z b = true ↔
      Nonempty (NonnegativeLift (comparison h.1 h.2.1 f h.2.2.1) (quotientClass C.P1 z) (quotientClass D.P0 b)) ∧
      Subsingleton (NonnegativeLift (comparison h.1 h.2.1 f h.2.2.1) (quotientClass C.P1 z) (quotientClass D.P0 b)) := by
  rw [finiteUnique_correct C D f z b h]
  constructor
  · rintro ⟨a,ha,hu⟩
    refine ⟨⟨⟨a,ha⟩⟩,⟨?_⟩⟩
    intro x y
    exact Subtype.ext ((hu x.val x.property).trans (hu y.val y.property).symm)
  · rintro ⟨⟨a⟩,hs⟩
    refine ⟨a.val,a.property,?_⟩
    intro x hx
    exact congrArg Subtype.val (@Subsingleton.elim _ hs ⟨x,hx⟩ a)
/-- 非空時の判定はBの同じ実kernelの零性と一致する。 -/
theorem finiteUnique_kernel (z : Vec C.P1.generators) (b : Vec D.P0.generators) (h : InputValid C D f z b)
    (a : NonnegativeLift (comparison h.1 h.2.1 f h.2.2.1) (quotientClass C.P1 z) (quotientClass D.P0 b)) :
    finiteUnique C D f z b = true ↔ (cycleComparison (comparison h.1 h.2.1 f h.2.2.1)).ker = ⊥ := by
  rw [finiteUnique_lift C D f z b h, and_iff_right ⟨a⟩, nonempty_lift_unique_iff_kernel_zero _ a]
/-- 拡大整数系の前半は固定設計のd_C x−R_C u。 -/
theorem finiteEquation_first (v : Vec (C.P0.generators+(product C.P1 D.P0).relations)) :
    first (equationMatrix C.P0 (product C.P1 D.P0) (jointMatrix C D f) *ᵥ v) =
      C.d0 *ᵥ first v - C.P1.matrix *ᵥ first (second v) := by
  rw [equationMatrix_mulVec]
  change first (above C.d0 f.f0 *ᵥ first v) -
    first (blockMatrix C.P1.matrix D.P0.matrix *ᵥ second v) = _
  rw [above_first,blockMatrix_first]
/-- 拡大整数系の後半は固定設計のφ⁰x−R_D v。 -/
theorem finiteEquation_second (v : Vec (C.P0.generators+(product C.P1 D.P0).relations)) :
    second (equationMatrix C.P0 (product C.P1 D.P0) (jointMatrix C D f) *ᵥ v) =
      f.f0 *ᵥ first v - D.P0.matrix *ᵥ second (second v) := by
  rw [equationMatrix_mulVec]
  change second (above C.d0 f.f0 *ᵥ first v) -
    second (blockMatrix C.P1.matrix D.P0.matrix *ᵥ second v) = _
  rw [above_second,blockMatrix_second]

/-- 全有限検査を先に実行し、不適合入力を拒否する原始入力インターフェース。 -/
def checkedSolve (z : Vec C.P1.generators) (b : Vec D.P0.generators) :=
  if checkInput C D f z b then some (finiteSolve C D f z b) else none
/-- 適合入力で返す結果は同じ原始solverの結果。 -/
theorem checkedSolve_valid (z : Vec C.P1.generators) (b : Vec D.P0.generators) (h : InputValid C D f z b) :
    checkedSolve C D f z b = some (finiteSolve C D f z b) := by
  simp only [checkedSolve,(checkInput_correct _ _ _ _ _).mpr h,↓reduceIte]
/-- 不適合な関係・複体・比較・指定入力のいずれも明示的に拒否する。 -/
theorem checkedSolve_reject_iff (z : Vec C.P1.generators) (b : Vec D.P0.generators) :
    checkedSolve C D f z b = none ↔ ¬ InputValid C D f z b := by
  simp only [checkedSolve,ite_eq_right_iff,Option.some_ne_none,imp_false,checkInput_correct]
/-- 受理した入力には全構造条件があり、その同じsolver出力を返す。 -/
theorem checkedSolve_some_iff (z : Vec C.P1.generators) (b : Vec D.P0.generators)
    (r : Sum (Vec C.P0.generators) (Fin (product C.P1 D.P0).generators)) :
    checkedSolve C D f z b = some r ↔ InputValid C D f z b ∧ finiteSolve C D f z b = r := by
  simp only [checkedSolve,ite_eq_iff,Option.some.injEq,checkInput_correct]
  tauto

/-- 元補正がある場合、同じBの余核残差の零性とも計算判定が一致する。 -/
theorem finiteSolve_residual (z : Vec C.P1.generators) (b : Vec D.P0.generators) (h : InputValid C D f z b)
    (a₀ : (native C h.1).X 0) (ha₀ : (native C h.1).d 0 1 a₀ = quotientClass C.P1 z) :
    (∃ x, finiteSolve C D f z b = .inl x) ↔
      residualClass (comparison h.1 h.2.1 f h.2.2.1) (quotientClass C.P1 z) (quotientClass D.P0 b)
        a₀ ha₀ (input_compatible C D f z b h) = 0 := by
  rw [residualClass_zero_iff_lift,finiteSolve_complete C D f z b h]

end AAT.AG.SpecifiedRepairLifting.FiniteLifting

#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.jointMatrix
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.jointValue
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.jointValid
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.jointEquation
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.liftFiberEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.liftFiberEquiv_val
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.jointZero
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.jointKernelEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.jointKernelEquiv_val
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.correctionPresentation
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.computedKernelEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.computedKernelEquiv_class
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.finiteSolve
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.decodedSolution
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.decodedSolution_val
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.finiteSolve_complete
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.finiteSolve_obstruction
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.computedLiftEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.computedLiftEquiv_class
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.finiteUnique
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.finiteUnique_correct
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.finiteSolve_no_solution
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.finiteSolve_failure_kind
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.finiteUnique_lift
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.finiteUnique_kernel
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.finiteEquation_first
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.finiteEquation_second
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.checkedSolve
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.checkedSolve_valid
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.checkedSolve_reject_iff
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.checkedSolve_some_iff
#print axioms AAT.AG.SpecifiedRepairLifting.FiniteLifting.finiteSolve_residual
#assert_standard_axioms_only AAT.AG.SpecifiedRepairLifting.FiniteLifting
