import ResearchLean.AG.SafeCoarseningOrder.W1Classification
import ResearchLean.AG.SafeCoarseningOrder.FixedMaximalDecision
import Mathlib.Logic.Equiv.Bool

/-! # W1 全原始自己同型と全固定極大元

## Implementation notes

有向辺保存から任意chart自己同型の一段差を1へ強制し、全自己同型を
Bool全単射と元巡回translationで尽くす。固定分割は元Rそのものについて評価する。
無向D₄を自己同型とする代替は有向辺保存を満たさないため用いない。
-/
set_option maxHeartbeats 2400000
noncomputable section
namespace AAT.AG.SafeCoarseningOrder.W1
/-- 元Bool全単射と巡回translationから全原始保存条件を放電する。 -/
def automorphism (p : Bool ≃ Bool) (k : ZMod 4) : PrimitiveIso input input where
  source := p
  target := p
  chart := Equiv.addRight k
  read_comm s := rfl
  edge_iff v w := by
    rw [input_edge_iff,input_edge_iff]
    change w=v+1 ↔ w+k=(v+k)+1
    have he : (v+k)+1=(v+1)+k := by abel
    rw [he]
    constructor
    · intro h; exact congrArg (fun x => x+k) h
    · intro h; exact add_right_cancel h
  support_iff _ _ := ⟨fun _ => True.intro,fun _ => True.intro⟩
/-- 原始生成自己同型のsourceを保持する基本API。 -/
@[simp] theorem automorphism_source (p : Bool ≃ Bool) (k : ZMod 4) :
    (automorphism p k).source=p := rfl
/-- 原始生成自己同型のtargetを保持する基本API。 -/
@[simp] theorem automorphism_target (p : Bool ≃ Bool) (k : ZMod 4) :
    (automorphism p k).target=p := rfl
/-- 原始生成自己同型のchart評価API。 -/
@[simp] theorem automorphism_chart_apply (p : Bool ≃ Bool) (k v : ZMod 4) :
    (automorphism p k).chart v=v+k := rfl
/-- q=idの元可換性により任意自己同型のsource/target表は一致する。 -/
theorem aut_source_eq_target (a : PrimitiveIso input input) : a.source=a.target := by
  apply Equiv.ext
  intro s
  simpa only [Cycle.input_read] using a.read_comm s
/-- 原始有向辺保存により任意chart自己同型は巡回一段差を保つ。 -/
theorem aut_chart_step (a : PrimitiveIso input input) (v : ZMod 4) :
    a.chart (v+1)=a.chart v+1 :=
  (input_edge_iff _ _).mp ((a.edge_iff v (v+1)).mp ((input_edge_iff _ _).mpr rfl))
/-- 全元chartで任意自己同型は元chart0のtranslationとなる。 -/
theorem aut_chart_apply (a : PrimitiveIso input input) (v : ZMod 4) :
    a.chart v=v+a.chart 0 := by
  have h1 : a.chart 1=a.chart 0+1 := by simpa only [zero_add] using aut_chart_step a 0
  have h2 : a.chart 2=a.chart 1+1 := aut_chart_step a 1
  have h3 : a.chart 3=a.chart 2+1 := aut_chart_step a 2
  fin_cases v
  · change a.chart 0=0+a.chart 0
    rw [zero_add]
  · change a.chart 1=1+a.chart 0
    rw [h1]; abel
  · change a.chart 2=2+a.chart 0
    rw [h2,h1]; abel
  · change a.chart 3=3+a.chart 0
    rw [h3,h2,h1]; abel
/-- 全S/T/V原始自己同型をBool全単射×四translationで尽くす。 -/
theorem aut_classification (a : PrimitiveIso input input) :
    a=automorphism a.target (a.chart 0) := by
  apply PrimitiveIso.ext
  · exact aut_source_eq_target a
  · rfl
  · ext v
    exact aut_chart_apply a v
/-- 指定一段回転は元source/targetを恒等に保つ。 -/
def rotation : PrimitiveIso input input := automorphism (Equiv.refl Bool) 1
/-- 指定Bool交換はchartを元恒等に保つ。 -/
def boolSwap : PrimitiveIso input input := automorphism Equiv.boolNot 0
/-- 指定回転の元chart評価API。 -/
@[simp] theorem rotation_chart_apply (v : ZMod 4) : rotation.chart v=v+1 := rfl
/-- 全translationの逆chart評価は元差である。 -/
@[simp] theorem automorphism_chart_symm_apply (p : Bool ≃ Bool) (k v : ZMod 4) :
    (automorphism p k).chart.symm v=v-k := by
  apply (automorphism p k).chart.injective
  rw [Equiv.apply_symm_apply,automorphism_chart_apply,sub_add_cancel]
/-- 指定回転の逆chart評価API。 -/
@[simp] theorem rotation_chart_symm_apply (v : ZMod 4) : rotation.chart.symm v=v-1 :=
  automorphism_chart_symm_apply (Equiv.refl Bool) 1 v
/-- 全原始translationは全七Maxのうち交互二block分割6を固定する。 -/
theorem alternating_fixed (a : PrimitiveIso input input) :
    a.coarseningOrderIso (candidate ⊤ 6)=candidate ⊤ 6 := by
  rw [aut_classification a]
  apply Prod.ext
  · apply Setoid.ext; intro s t
    rw [PrimitiveIso.coarseningOrderIso_target_rel]
  · apply Setoid.ext; intro v w
    rw [PrimitiveIso.coarseningOrderIso_chart_rel,candidate_chart_iff,candidate_chart_iff,
      automorphism_chart_symm_apply,automorphism_chart_symm_apply]
    generalize hk : a.chart 0=k
    fin_cases k <;> fin_cases v <;> fin_cases w <;> decide +kernel

/-- Bool全単射の全二表を元二点の単射性から分類する。 -/
theorem bool_equiv_cases (p : Bool ≃ Bool) : p=Equiv.refl Bool ∨ p=Equiv.boolNot := by
  cases hf : p false <;> cases ht : p true
  · exact (Bool.false_ne_true (p.injective (hf.trans ht.symm))).elim
  · left; apply Equiv.ext; intro b; cases b <;> assumption
  · right; apply Equiv.ext; intro b; cases b <;> assumption
  · exact (Bool.false_ne_true (p.injective (hf.trans ht.symm))).elim
/-- 原始一段回転が二block候補を固定するのは交互分割6だけ。 -/
theorem rotation_fixed_binary_iff (i : Fin 15) (hi : numClasses i=2) :
    rotation.coarseningOrderIso (candidate ⊤ i)=candidate ⊤ i ↔ i=6 := by
  fin_cases i
  · exact ((by decide +kernel : numClasses 0≠2) hi).elim
  · apply iff_of_false ?_ (by decide +kernel)
    intro h
    change rotation.coarseningOrderIso (candidate ⊤ 1)=candidate ⊤ 1 at h
    have he : (rotation.coarseningOrderIso (candidate ⊤ 1)).2.r 0 1 ↔
        (candidate ⊤ 1).2.r 0 1 := by rw [h]
    rw [PrimitiveIso.coarseningOrderIso_chart_rel,candidate_chart_iff,candidate_chart_iff,
      rotation_chart_symm_apply,rotation_chart_symm_apply] at he
    exact (by decide +kernel : ¬ (partitionMap 1 (0-1)=partitionMap 1 (1-1) ↔
      partitionMap 1 0=partitionMap 1 1)) he
  · apply iff_of_false ?_ (by decide +kernel)
    intro h
    change rotation.coarseningOrderIso (candidate ⊤ 2)=candidate ⊤ 2 at h
    have he : (rotation.coarseningOrderIso (candidate ⊤ 2)).2.r 0 2 ↔
        (candidate ⊤ 2).2.r 0 2 := by rw [h]
    rw [PrimitiveIso.coarseningOrderIso_chart_rel,candidate_chart_iff,candidate_chart_iff,
      rotation_chart_symm_apply,rotation_chart_symm_apply] at he
    exact (by decide +kernel : ¬ (partitionMap 2 (0-1)=partitionMap 2 (2-1) ↔
      partitionMap 2 0=partitionMap 2 2)) he
  · apply iff_of_false ?_ (by decide +kernel)
    intro h
    change rotation.coarseningOrderIso (candidate ⊤ 3)=candidate ⊤ 3 at h
    have he : (rotation.coarseningOrderIso (candidate ⊤ 3)).2.r 0 1 ↔
        (candidate ⊤ 3).2.r 0 1 := by rw [h]
    rw [PrimitiveIso.coarseningOrderIso_chart_rel,candidate_chart_iff,candidate_chart_iff,
      rotation_chart_symm_apply,rotation_chart_symm_apply] at he
    exact (by decide +kernel : ¬ (partitionMap 3 (0-1)=partitionMap 3 (1-1) ↔
      partitionMap 3 0=partitionMap 3 1)) he
  · exact ((by decide +kernel : numClasses 4≠2) hi).elim
  · apply iff_of_false ?_ (by decide +kernel)
    intro h
    change rotation.coarseningOrderIso (candidate ⊤ 5)=candidate ⊤ 5 at h
    have he : (rotation.coarseningOrderIso (candidate ⊤ 5)).2.r 0 1 ↔
        (candidate ⊤ 5).2.r 0 1 := by rw [h]
    rw [PrimitiveIso.coarseningOrderIso_chart_rel,candidate_chart_iff,candidate_chart_iff,
      rotation_chart_symm_apply,rotation_chart_symm_apply] at he
    exact (by decide +kernel : ¬ (partitionMap 5 (0-1)=partitionMap 5 (1-1) ↔
      partitionMap 5 0=partitionMap 5 1)) he
  · exact iff_of_true (alternating_fixed rotation) rfl
  · exact ((by decide +kernel : numClasses 7≠2) hi).elim
  · apply iff_of_false ?_ (by decide +kernel)
    intro h
    change rotation.coarseningOrderIso (candidate ⊤ 8)=candidate ⊤ 8 at h
    have he : (rotation.coarseningOrderIso (candidate ⊤ 8)).2.r 0 1 ↔
        (candidate ⊤ 8).2.r 0 1 := by rw [h]
    rw [PrimitiveIso.coarseningOrderIso_chart_rel,candidate_chart_iff,candidate_chart_iff,
      rotation_chart_symm_apply,rotation_chart_symm_apply] at he
    exact (by decide +kernel : ¬ (partitionMap 8 (0-1)=partitionMap 8 (1-1) ↔
      partitionMap 8 0=partitionMap 8 1)) he
  · apply iff_of_false ?_ (by decide +kernel)
    intro h
    change rotation.coarseningOrderIso (candidate ⊤ 9)=candidate ⊤ 9 at h
    have he : (rotation.coarseningOrderIso (candidate ⊤ 9)).2.r 0 2 ↔
        (candidate ⊤ 9).2.r 0 2 := by rw [h]
    rw [PrimitiveIso.coarseningOrderIso_chart_rel,candidate_chart_iff,candidate_chart_iff,
      rotation_chart_symm_apply,rotation_chart_symm_apply] at he
    exact (by decide +kernel : ¬ (partitionMap 9 (0-1)=partitionMap 9 (2-1) ↔
      partitionMap 9 0=partitionMap 9 2)) he
  · exact ((by decide +kernel : numClasses 10≠2) hi).elim
  · exact ((by decide +kernel : numClasses 11≠2) hi).elim
  · exact ((by decide +kernel : numClasses 12≠2) hi).elim
  · exact ((by decide +kernel : numClasses 13≠2) hi).elim
  · exact ((by decide +kernel : numClasses 14≠2) hi).elim
/-- 全極大元と全原始Autを評価したFixMaxは交互分割だけ。 -/
theorem fixed_maximal_iff (R : Coarsening Bool (ZMod 4)) :
    (Maximal input.Safe R ∧ ∀ a : PrimitiveIso input input, a.coarseningOrderIso R=R) ↔
      R=candidate ⊤ 6 := by
  constructor
  · rintro ⟨hm,hf⟩
    obtain ⟨i,hi,rfl⟩ := (maximal_iff_binary R).mp hm
    have h6 := (rotation_fixed_binary_iff i hi).mp (hf rotation)
    subst i
    rfl
  · rintro rfl
    exact ⟨binary_maximal 6 (by decide +kernel),alternating_fixed⟩
/-- 元回転のtargetは恒等で、元target分割を変えない。 -/
@[simp] theorem rotation_target_symm_apply (b : Bool) : rotation.target.symm b=b := rfl
/-- 元回転の全chart分割への作用を原始色表から生成する。 -/
def rotationIndex (i : Fin 15) : Fin 15 := ![0,9,1,8,10,2,6,12,3,5,13,4,7,11,14] i
/-- 回転は元全15分割にこの実作用を与える。 -/
theorem rotation_candidate (P : Setoid Bool) (i : Fin 15) :
    rotation.coarseningOrderIso (candidate P i)=candidate P (rotationIndex i) := by
  apply Prod.ext
  · apply Setoid.ext; intro s t
    rw [PrimitiveIso.coarseningOrderIso_target_rel,candidate_target_iff,
      rotation_target_symm_apply,rotation_target_symm_apply]
  · apply Setoid.ext; intro v w
    rw [PrimitiveIso.coarseningOrderIso_chart_rel,candidate_chart_iff,candidate_chart_iff,
      rotation_chart_symm_apply,rotation_chart_symm_apply]
    fin_cases i <;> fin_cases v <;> fin_cases w <;> decide +kernel
/-- 指定Bool交換は元chartを恒等に保つ。 -/
@[simp] theorem boolSwap_chart_symm_apply (v : ZMod 4) : boolSwap.chart.symm v=v := by
  change (automorphism Equiv.boolNot 0).chart.symm v=v
  rw [automorphism_chart_symm_apply,sub_zero]
/-- 指定Bool交換の元target逆写像は同じBool交換。 -/
@[simp] theorem boolSwap_target_symm_apply (b : Bool) : boolSwap.target.symm b=(!b) := rfl
/-- Bool交換は両target分割と全chart分割候補を固定する。 -/
theorem boolSwap_candidate (P : Setoid Bool) (i : Fin 15) :
    boolSwap.coarseningOrderIso (candidate P i)=candidate P i := by
  apply Prod.ext
  · apply Setoid.ext; intro s t
    rw [PrimitiveIso.coarseningOrderIso_target_rel,candidate_target_iff,
      boolSwap_target_symm_apply,boolSwap_target_symm_apply]
    rcases classify_target P with rfl|rfl
    · exact Equiv.boolNot.injective.eq_iff
    · exact Iff.rfl
  · apply Setoid.ext; intro v w
    rw [PrimitiveIso.coarseningOrderIso_chart_rel,candidate_chart_iff,
      boolSwap_chart_symm_apply,boolSwap_chart_symm_apply]
    exact Iff.rfl
open scoped Classical
/-- Bの同じ全固定極大有限表は元交互分割のsingleton。 -/
theorem fixedMaximalCoarsenings_eq : input.fixedMaximalCoarsenings={candidate ⊤ 6} := by
  ext R
  rw [input.mem_fixedMaximalCoarsenings,fixed_maximal_iff,Finset.mem_singleton]
/-- 全固定有限判定は正の結果を返す。 -/
theorem fixedMaximalDecision_true : input.fixedMaximalDecision=true := by
  apply input.fixedMaximalDecision_eq_true.mpr
  rw [fixedMaximalCoarsenings_eq]
  exact Finset.singleton_nonempty _
/-- 元全Max/全Autから構成した指定固定極大正出力。 -/
def specifiedFixedOutput : input.FixedMaximalWitness where
  coarsening := candidate ⊤ 6
  maximal := binary_maximal 6 (by decide +kernel)
  fixed := alternating_fixed
/-- 同じtrueからBの一般固定極大producerを発火させる。 -/
def generatedFixedOutput : input.FixedMaximalWitness := input.fixedMaximalWitness fixedMaximalDecision_true
/-- 生成出力は軌道でなく元交互分割そのもの。 -/
theorem generatedFixedOutput_eq : generatedFixedOutput.coarsening=candidate ⊤ 6 :=
  fixed_maximal_iff _ |>.mp ⟨generatedFixedOutput.maximal,generatedFixedOutput.fixed⟩
end AAT.AG.SafeCoarseningOrder.W1


#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
