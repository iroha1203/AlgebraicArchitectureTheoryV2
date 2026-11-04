import ResearchLean.AG.SpecifiedRepairLifting.AdditiveCone
import Mathlib.Algebra.AddTorsor.Basic
/-! # 指定補正の全解と零次比較の核

G-138 Bの全解分類。元の非負複体と厳密なNonnegativeLiftを用いる。
Implementation notes: kは実φ⁰のcycleへの制限で、作用は元C⁰の加法、差は元C⁰の差。
解を新しいパラメータ型から定義せず、非空な実LiftにだけAddTorsorを与える。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.SpecifiedRepairLifting
universe w
variable {C D : CochainComplex (ModuleCat.{w} ℤ) ℕ} (f : C ⟶ D)
/-- BのZ⁰は元のd⁰の実kernelである。 -/
abbrev zeroCycles (C : CochainComplex (ModuleCat.{w} ℤ) ℕ) :=
  (C.d 0 1).hom.toAddMonoidHom.ker
/-- Bのkφは実φ⁰の零次cycleへの制限から生成する。 -/
def cycleComparison : zeroCycles C →+ zeroCycles D where
  toFun a := ⟨f.f 0 a.val, by
    change D.d 0 1 (f.f 0 a.val) = 0
    have ha : C.d 0 1 a.val = 0 := a.property
    have h := congrArg (fun g : C.X 0 ⟶ D.X 1 => g a.val) (f.comm 0 1)
    simpa only [ModuleCat.comp_apply, ha, map_zero] using h⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' a a' := Subtype.ext (map_add _ a.val a'.val)
/-- kφの値は元の比較成分そのものである。 -/
@[simp] theorem cycleComparison_apply (a : zeroCycles C) :
    (cycleComparison f a).val = f.f 0 a.val := rfl
/-- Bの全解に作用する群はkφの実kernel。 -/
abbrev CorrectionKernel := (cycleComparison f).ker
/-- 核の元の元cochainでの微分は零。 -/
theorem correctionKernel_d (h : CorrectionKernel f) : C.d 0 1 h.val.val = 0 :=
  h.val.property
/-- 核の元の元cochainでの比較像は零。 -/
theorem correctionKernel_f (h : CorrectionKernel f) : f.f 0 h.val.val = 0 :=
  congrArg Subtype.val h.property
/-- 実Liftへ核の元を加える構成。両等式を元の射の加法性から証明する。 -/
def addKernel {z : C.X 1} {b : D.X 0}
    (h : CorrectionKernel f) (a : NonnegativeLift f z b) : NonnegativeLift f z b :=
  ⟨a.val + h.val.val, by
    constructor
    · rw [map_add, a.property.1, correctionKernel_d, add_zero]
    · rw [map_add, a.property.2, correctionKernel_f, add_zero]⟩
/-- 核の作用を元C⁰で評価するAPI。 -/
@[simp] theorem addKernel_val {z : C.X 1} {b : D.X 0}
    (h : CorrectionKernel f) (a : NonnegativeLift f z b) :
    (addKernel f h a).val = a.val + h.val.val := rfl
/-- 任意二解の差から作用群の元を生成する。 -/
def liftDifference {z : C.X 1} {b : D.X 0}
    (a a' : NonnegativeLift f z b) : CorrectionKernel f :=
  ⟨⟨a.val - a'.val, by
    change C.d 0 1 (a.val - a'.val) = 0
    rw [map_sub, a.property.1, a'.property.1, sub_self]⟩, by
    apply Subtype.ext
    change f.f 0 (a.val - a'.val) = 0
    rw [map_sub, a.property.2, a'.property.2, sub_self]⟩
/-- 解の差の元C⁰での評価。 -/
@[simp] theorem liftDifference_val {z : C.X 1} {b : D.X 0}
    (a a' : NonnegativeLift f z b) :
    (liftDifference f a a').val.val = a.val - a'.val := rfl
/-- 解の差を第二解へ加えると第一解を厳密に復元する。 -/
theorem addKernel_difference {z : C.X 1} {b : D.X 0}
    (a a' : NonnegativeLift f z b) : addKernel f (liftDifference f a a') a' = a := by
  apply Subtype.ext
  simp only [addKernel_val, liftDifference_val]
  abel
/-- 核の作用後の差から同じ作用元を復元する。 -/
theorem difference_addKernel {z : C.X 1} {b : D.X 0}
    (h : CorrectionKernel f) (a : NonnegativeLift f z b) :
    liftDifference f (addKernel f h a) a = h := by
  apply Subtype.ext
  apply Subtype.ext
  simp only [liftDifference_val, addKernel_val]
  abel
/-- Bの実解集合は、非空のときだけ核によるAddTorsorになる。 -/
instance liftAddTorsor (z : C.X 1) (b : D.X 0) [Nonempty (NonnegativeLift f z b)] :
    AddTorsor (CorrectionKernel f) (NonnegativeLift f z b) where
  vadd := addKernel f
  zero_vadd a := by apply Subtype.ext; exact add_zero a.val
  add_vadd h h' a := by
    apply Subtype.ext
    change a.val + (h.val.val + h'.val.val) = (a.val + h'.val.val) + h.val.val
    abel
  vsub := liftDifference f
  vsub_vadd' := addKernel_difference f
  vadd_vsub' := difference_addKernel f
/-- 基点を一つ与えたとき、核と実Liftの全解を両逆で対応させる。 -/
def kernelEquivLift {z : C.X 1} {b : D.X 0} (a : NonnegativeLift f z b) :
    CorrectionKernel f ≃ NonnegativeLift f z b where
  toFun h := addKernel f h a
  invFun a' := liftDifference f a' a
  left_inv h := difference_addKernel f h a
  right_inv a' := addKernel_difference f a' a
/-- 全解同値の値は固定targetのa*+hそのもの。 -/
@[simp] theorem kernelEquivLift_val {z : C.X 1} {b : D.X 0}
    (a : NonnegativeLift f z b) (h : CorrectionKernel f) :
    (kernelEquivLift f a h).val = a.val + h.val.val := rfl
/-- 任意二解を移す作用元は、実差から一意に回収される。 -/
theorem existsUnique_addKernel {z : C.X 1} {b : D.X 0}
    (a a' : NonnegativeLift f z b) : ∃! h : CorrectionKernel f, addKernel f h a = a' := by
  refine ⟨liftDifference f a' a, addKernel_difference f a' a, ?_⟩
  intro h hh
  exact (difference_addKernel f h a).symm.trans
    (congrArg (fun x => liftDifference f x a) hh)
/-- Bの任意の元補正から、指定bとの差をZ⁰Dへ生成する。 -/
def residualCycle (z : C.X 1) (b : D.X 0) (a₀ : C.X 0)
    (ha₀ : C.d 0 1 a₀ = z) (hb : D.d 0 1 b = f.f 1 z) : zeroCycles D :=
  ⟨b - f.f 0 a₀, by
    change D.d 0 1 (b - f.f 0 a₀) = 0
    have hf : D.d 0 1 (f.f 0 a₀) = f.f 1 (C.d 0 1 a₀) :=
      congrArg (fun g : C.X 0 ⟶ D.X 1 => g a₀) (f.comm 0 1)
    rw [map_sub, hb, hf, ha₀, sub_self]⟩
/-- 残差cycleの値は同じ実比較によるb−φa₀。 -/
@[simp] theorem residualCycle_val (z : C.X 1) (b : D.X 0) (a₀ : C.X 0)
    (ha₀ : C.d 0 1 a₀ = z) (hb : D.d 0 1 b = f.f 1 z) :
    (residualCycle f z b a₀ ha₀ hb).val = b - f.f 0 a₀ := rfl
/-- kφの全射性から全ての元補正存在・適合bについて厳密Liftを構成する。 -/
theorem lift_of_cycleComparison_surjective (hs : Function.Surjective (cycleComparison f))
    (z : C.X 1) (b : D.X 0) (a₀ : C.X 0)
    (ha₀ : C.d 0 1 a₀ = z) (hb : D.d 0 1 b = f.f 1 z) :
    Nonempty (NonnegativeLift f z b) := by
  obtain ⟨h,hh⟩ := hs (residualCycle f z b a₀ ha₀ hb)
  have hh' : f.f 0 h.val = b - f.f 0 a₀ := congrArg Subtype.val hh
  refine ⟨⟨a₀ + h.val, ?_, ?_⟩⟩
  · have hd : C.d 0 1 h.val = 0 := h.property
    rw [map_add, ha₀, hd, add_zero]
  · rw [map_add, hh']
    abel
/-- Bの全射性条件を全量化で証明する。元の補正の存在はこの条件付き主張だけで使う。
閉性は元補正から従うが、固定targetの量化域を明示するためzの閉性も記載する。 -/
theorem cycleComparison_surjective_iff :
    Function.Surjective (cycleComparison f) ↔
      ∀ (z : C.X 1), C.d 1 2 z = 0 → (∃ a₀ : C.X 0, C.d 0 1 a₀ = z) →
        ∀ (b : D.X 0), D.d 0 1 b = f.f 1 z → Nonempty (NonnegativeLift f z b) := by
  constructor
  · intro hs z _ ⟨a₀,ha₀⟩ b hb
    exact lift_of_cycleComparison_surjective f hs z b a₀ ha₀ hb
  · intro hall b
    have hb : D.d 0 1 b.val = f.f 1 (0 : C.X 1) := by
      rw [map_zero]
      exact b.property
    obtain ⟨a⟩ := hall 0 (map_zero _) ⟨0,map_zero _⟩ b.val hb
    exact ⟨⟨a.val,a.property.1⟩, Subtype.ext a.property.2⟩
/-- kφが単射なら各実fiberは高々一元。適合条件の追加を必要としない補助定理。 -/
theorem lift_subsingleton_of_injective (hi : Function.Injective (cycleComparison f))
    (z : C.X 1) (b : D.X 0) : Subsingleton (NonnegativeLift f z b) := by
  constructor
  intro a a'
  let h := liftDifference f a a'
  have hc : h.val = 0 := hi (by simpa only [map_zero] using h.property)
  apply Subtype.ext
  apply sub_eq_zero.mp
  exact congrArg Subtype.val hc
/-- Bの単射性と全適合fiberの高々一元性を全量化で同値にする。 -/
theorem cycleComparison_injective_iff :
    Function.Injective (cycleComparison f) ↔
      ∀ (z : C.X 1), C.d 1 2 z = 0 → ∀ (b : D.X 0),
        D.d 0 1 b = f.f 1 z → Subsingleton (NonnegativeLift f z b) := by
  constructor
  · intro hi z _ b _
    exact lift_subsingleton_of_injective f hi z b
  · intro hall c c' he
    have hb : D.d 0 1 (f.f 0 c.val) = f.f 1 (0 : C.X 1) := by
      rw [map_zero]
      exact (cycleComparison f c).property
    let a : NonnegativeLift f 0 (f.f 0 c.val) := ⟨c.val,c.property,rfl⟩
    let a' : NonnegativeLift f 0 (f.f 0 c.val) :=
      ⟨c'.val,c'.property,(congrArg Subtype.val he).symm⟩
    have h := @Subsingleton.elim _ (hall 0 (map_zero _) _ hb) a a'
    have hv : a.val = a'.val := congrArg
      (fun x : NonnegativeLift f 0 (f.f 0 c.val) => x.val) h
    exact Subtype.ext hv
/-- 核が零群であることを、実kernel subgroupが⊥である等式へ同定する。 -/
theorem correctionKernel_subsingleton_iff :
    Subsingleton (CorrectionKernel f) ↔ (cycleComparison f).ker = ⊥ := by
  constructor
  · intro hs
    apply (AddSubgroup.eq_bot_iff_forall _).mpr
    intro x hx
    exact congrArg Subtype.val (@Subsingleton.elim _ hs ⟨x,hx⟩ 0)
  · intro hk
    constructor
    intro x y
    apply Subtype.ext
    have hx := (AddSubgroup.eq_bot_iff_forall _).mp hk x.val x.property
    have hy := (AddSubgroup.eq_bot_iff_forall _).mp hk y.val y.property
    exact hx.trans hy.symm
/-- Bの非空fiberの一意性とker kφ=0。実解a*を基点として全解同値から導く。 -/
theorem nonempty_lift_unique_iff_kernel_zero {z : C.X 1} {b : D.X 0}
    (a : NonnegativeLift f z b) :
    Subsingleton (NonnegativeLift f z b) ↔ (cycleComparison f).ker = ⊥ :=
  (kernelEquivLift f a).subsingleton_congr.symm.trans (correctionKernel_subsingleton_iff f)

/-- AddTorsorの公開加法は元C⁰の同じ加法で評価できる。 -/
@[simp] theorem lift_vadd_val {z : C.X 1} {b : D.X 0}
    [Nonempty (NonnegativeLift f z b)] (h : CorrectionKernel f) (a : NonnegativeLift f z b) :
    (h +ᵥ a).val = a.val + h.val.val := rfl
/-- AddTorsorの公開差は元C⁰の同じ差で評価できる。 -/
@[simp] theorem lift_vsub_val {z : C.X 1} {b : D.X 0}
    [Nonempty (NonnegativeLift f z b)] (a a' : NonnegativeLift f z b) :
    (a -ᵥ a' : CorrectionKernel f).val.val = a.val - a'.val := rfl
/-- 全非負次数零微分例で、零比較の実解へ任意整数を入れる。
非空虚性の補助例であり、固定W2の代替には数えない。 -/
def integerZeroLift (n : ℤ) :
    NonnegativeLift (0 : integerZeroDifferential ⟶ integerZeroDifferential) 0 0 :=
  ⟨n, by rw [integerZeroDifferential_d]; rfl, rfl⟩
/-- 上の実解の元cochainへの評価。 -/
@[simp] theorem integerZeroLift_val (n : ℤ) : (integerZeroLift n).val = n := rfl
/-- 整数の非零な差が実作用を変えることを同じ解で検証する。 -/
theorem integer_difference_action :
    addKernel (0 : integerZeroDifferential ⟶ integerZeroDifferential)
      (liftDifference 0 (integerZeroLift 1) (integerZeroLift 0)) (integerZeroLift 0) =
      integerZeroLift 1 := addKernel_difference _ _ _
/-- 同じfiberの異なる二解。非一意性を実cochainで検証する。 -/
theorem integer_two_lifts_ne : integerZeroLift 0 ≠ integerZeroLift 1 := by
  intro h
  have hv : (0 : ℤ) = 1 := congrArg Subtype.val h
  exact zero_ne_one hv
/-- 同じ整数例の核の作用元は非零である。 -/
theorem integer_difference_ne_zero :
    liftDifference (0 : integerZeroDifferential ⟶ integerZeroDifferential)
      (integerZeroLift 1) (integerZeroLift 0) ≠ 0 := by
  intro h
  have hv : (1 : ℤ) - 0 = 0 := congrArg (fun x : CorrectionKernel
    (0 : integerZeroDifferential ⟶ integerZeroDifferential) => x.val.val) h
  exact one_ne_zero (by simpa only [sub_zero] using hv)
/-- 恒等整数比較の零次cycle写像は単射。 -/
theorem integer_identity_cycle_injective :
    Function.Injective (cycleComparison (𝟙 integerZeroDifferential)) := by
  intro a a' h
  apply Subtype.ext
  exact congrArg Subtype.val h
/-- 同じ整数複体の恒等比較では指定補正3のfiberが高々一元。 -/
theorem integer_identity_unique :
    Subsingleton (NonnegativeLift (𝟙 integerZeroDifferential) 0 (3 : ℤ)) :=
  lift_subsingleton_of_injective _ integer_identity_cycle_injective _ _

end AAT.AG.SpecifiedRepairLifting
#print axioms AAT.AG.SpecifiedRepairLifting.zeroCycles
#print axioms AAT.AG.SpecifiedRepairLifting.cycleComparison
#print axioms AAT.AG.SpecifiedRepairLifting.cycleComparison_apply
#print axioms AAT.AG.SpecifiedRepairLifting.CorrectionKernel
#print axioms AAT.AG.SpecifiedRepairLifting.correctionKernel_d
#print axioms AAT.AG.SpecifiedRepairLifting.correctionKernel_f
#print axioms AAT.AG.SpecifiedRepairLifting.addKernel
#print axioms AAT.AG.SpecifiedRepairLifting.addKernel_val
#print axioms AAT.AG.SpecifiedRepairLifting.liftDifference
#print axioms AAT.AG.SpecifiedRepairLifting.liftDifference_val
#print axioms AAT.AG.SpecifiedRepairLifting.addKernel_difference
#print axioms AAT.AG.SpecifiedRepairLifting.difference_addKernel
#print axioms AAT.AG.SpecifiedRepairLifting.liftAddTorsor
#print axioms AAT.AG.SpecifiedRepairLifting.kernelEquivLift
#print axioms AAT.AG.SpecifiedRepairLifting.kernelEquivLift_val
#print axioms AAT.AG.SpecifiedRepairLifting.existsUnique_addKernel
#print axioms AAT.AG.SpecifiedRepairLifting.residualCycle
#print axioms AAT.AG.SpecifiedRepairLifting.residualCycle_val
#print axioms AAT.AG.SpecifiedRepairLifting.lift_of_cycleComparison_surjective
#print axioms AAT.AG.SpecifiedRepairLifting.cycleComparison_surjective_iff
#print axioms AAT.AG.SpecifiedRepairLifting.lift_subsingleton_of_injective
#print axioms AAT.AG.SpecifiedRepairLifting.cycleComparison_injective_iff
#print axioms AAT.AG.SpecifiedRepairLifting.correctionKernel_subsingleton_iff
#print axioms AAT.AG.SpecifiedRepairLifting.nonempty_lift_unique_iff_kernel_zero
#print axioms AAT.AG.SpecifiedRepairLifting.lift_vadd_val
#print axioms AAT.AG.SpecifiedRepairLifting.lift_vsub_val
#print axioms AAT.AG.SpecifiedRepairLifting.integerZeroLift
#print axioms AAT.AG.SpecifiedRepairLifting.integerZeroLift_val
#print axioms AAT.AG.SpecifiedRepairLifting.integer_difference_action
#print axioms AAT.AG.SpecifiedRepairLifting.integer_two_lifts_ne
#print axioms AAT.AG.SpecifiedRepairLifting.integer_difference_ne_zero
#print axioms AAT.AG.SpecifiedRepairLifting.integer_identity_cycle_injective
#print axioms AAT.AG.SpecifiedRepairLifting.integer_identity_unique
#assert_standard_axioms_only AAT.AG.SpecifiedRepairLifting
