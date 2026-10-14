import ResearchLean.AG.SafeCoarseningOrder.FiniteDecisionInstances
import Mathlib.Tactic.FinCases

/-!
# 原始三角形の二chart粗化と実比較

三辺の一つを内部化する粗化を元表から生成する。残る逆向き二辺は別セルに保ち、
同じ実比較の全単射性を元cochainとpotentialの正逆liftから示す。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition FailureCertificate
namespace Triangle
/-- 三角形の元有向辺表の評価API。 -/
theorem input_edge_iff (v w : Fin 3) : input.edge v w ↔ w = v+1 := Iff.rfl
/-- iとi+1を合併しi+2を別chartにする原始chart写像。 -/
def cutMap (i v : Fin 3) : Bool := decide (v = i+2)
/-- 合併側の二元はfalse、残りの元はtrue。 -/
theorem cutMap_values (i : Fin 3) : cutMap i i = false ∧
    cutMap i (i+1) = false ∧ cutMap i (i+2) = true := by
  fin_cases i <;> decide +kernel
/-- targetは恒等分割、chartは原始cutMapの核。 -/
def cut (i : Fin 3) : Coarsening Unit (Fin 3) := (⊥,Setoid.ker (cutMap i))
/-- 元chartから指定商chartへの写像。 -/
def cutChart (i v : Fin 3) : Quotient (cut i).2 := Quotient.mk _ v
/-- 異なるcutMap値を持つ原始chartは商でも異なる。 -/
theorem cutChart_ne (i v w : Fin 3) (h : cutMap i v ≠ cutMap i w) :
    cutChart i v ≠ cutChart i w := by
  intro he
  exact h (Quotient.exact he)
/-- 同じcutMap値を持つ原始chartは商で同じ。 -/
theorem cutChart_eq (i v w : Fin 3) (h : cutMap i v = cutMap i w) :
    cutChart i v = cutChart i w := Quotient.sound h
/-- 元i→i+1辺は指定粗化で内部化される。 -/
theorem cut_internal (i : Fin 3) : cutChart i i = cutChart i (i+1) :=
  cutChart_eq i i (i+1) ((cutMap_values i).1.trans (cutMap_values i).2.1.symm)
/-- false→trueの残存商辺。 -/
def cutEdge0 (i : Fin 3) : input.QuotientEdge (cut i) :=
  ⟨(cutChart i (i+1),cutChart i (i+2)),
    cutChart_ne i (i+1) (i+2) (by rw [(cutMap_values i).2.1,(cutMap_values i).2.2]; decide),
    i+1,i+2,((input_edge_iff _ _).mpr (by fin_cases i <;> decide +kernel)),rfl,rfl⟩
/-- true→falseの残存商辺。逆向きは同一視しない。 -/
def cutEdge1 (i : Fin 3) : input.QuotientEdge (cut i) :=
  ⟨(cutChart i (i+2),cutChart i i),
    cutChart_ne i (i+2) i (by rw [(cutMap_values i).2.2,(cutMap_values i).1]; decide),
    i+2,i,((input_edge_iff _ _).mpr (by fin_cases i <;> decide +kernel)),rfl,rfl⟩
/-- 全target領域で選択したfalse→true辺。 -/
def cutFullEdge0 (i : Fin 3) : (input.quotientSupported (cut i)).EdgeInTargetSubset Set.univ :=
  ⟨cutEdge0 i,Quotient.mk (cut i).1 (),
    ⟨input.quotientSupport_mk (cut i) (i+1) True.intro,
      input.quotientSupport_mk (cut i) (i+2) True.intro⟩,True.intro⟩
/-- 全target領域で選択したtrue→false辺。 -/
def cutFullEdge1 (i : Fin 3) : (input.quotientSupported (cut i)).EdgeInTargetSubset Set.univ :=
  ⟨cutEdge1 i,Quotient.mk (cut i).1 (),
    ⟨input.quotientSupport_mk (cut i) (i+2) True.intro,
      input.quotientSupport_mk (cut i) i True.intro⟩,True.intro⟩
/-- 全領域の同じ元生成比較Hom。 -/
def cutHom (i : Fin 3) : ThreeCochainComplex.Hom
    ((input.quotientSupported (cut i)).targetSubsetComplex Set.univ) fullComplex :=
  transportHom (congrArg input.supported.targetSubsetComplex Set.preimage_univ)
    ((input.quotientComparison (cut i)).aSubnerveComparisonHom Set.univ)
/-- canonical全領域逆像の等号transportを同じ旧比較の全Homへ戻す。 -/
theorem cutHom_eq_old (i : Fin 3) : cutHom i =
    (input.quotientMorphism (cut i)).targetSubsetComparisonHom Set.univ Set.univ
      (fun _ _ => True.intro) := by
  rw [cutHom,input.quotient_actualHom_old]
  exact targetSubsetComparisonHom_transport (input.quotientMorphism (cut i)) Set.univ _
    Set.univ Set.preimage_univ (fun _ h => h) (fun _ _ => True.intro)
/-- 元内部辺の実次数1引き戻しは零。 -/
theorem cutHom_internal (i : Fin 3) (x : (input.quotientSupported (cut i)).targetSubsetComplex Set.univ |>.C1) :
    (cutHom i).f1 x (fullEdge i) = 0 := by
  have hm : (input.quotientMorphism (cut i)).edgeMap (fullEdge i).1 = none := by
    apply (input.quotientEdgeMap_eq_none _ _).mpr
    exact (cutMap_values i).1.trans (cutMap_values i).2.1.symm
  rw [cutHom_eq_old]
  change (input.quotientMorphism (cut i)).targetSubsetPullback1 _ _ _ x (fullEdge i) = 0
  rw [TargetSupportedNerveMorphism.targetSubsetPullback1_apply,
    TargetSupportedNerveMorphism.targetSubsetEdgeMapOption_eq_none _ _ _ _ _ hm]
  rfl
/-- false→true原辺の実引き戻しは同じ残存商辺の評価。 -/
theorem cutHom_edge0 (i : Fin 3) (x : (input.quotientSupported (cut i)).targetSubsetComplex Set.univ |>.C1) :
    (cutHom i).f1 x (fullEdge (i+1)) = x (cutFullEdge0 i) := by
  have hm : (input.quotientMorphism (cut i)).edgeMap (fullEdge (i+1)).1 = some (cutEdge0 i) :=
    (input.quotientEdgeMap_eq_some _ _ _).mpr
      ⟨rfl,congrArg (cutChart i) (by fin_cases i <;> decide +kernel)⟩
  rw [cutHom_eq_old]
  change (input.quotientMorphism (cut i)).targetSubsetPullback1 _ _ _ x (fullEdge (i+1)) = _
  rw [TargetSupportedNerveMorphism.targetSubsetPullback1_apply,
    TargetSupportedNerveMorphism.targetSubsetEdgeMapOption_eq_some _ _ _ _ _ _ hm,Option.elim_some]
  congr 1
/-- true→false原辺の実引き戻しは同じ逆向き残存商辺の評価。 -/
theorem cutHom_edge1 (i : Fin 3) (x : (input.quotientSupported (cut i)).targetSubsetComplex Set.univ |>.C1) :
    (cutHom i).f1 x (fullEdge (i+2)) = x (cutFullEdge1 i) := by
  have hm : (input.quotientMorphism (cut i)).edgeMap (fullEdge (i+2)).1 = some (cutEdge1 i) := by
    apply (input.quotientEdgeMap_eq_some _ _ _).mpr
    exact ⟨rfl,congrArg (cutChart i) (by fin_cases i <;> decide +kernel)⟩
  rw [cutHom_eq_old]
  change (input.quotientMorphism (cut i)).targetSubsetPullback1 _ _ _ x (fullEdge (i+2)) = _
  rw [TargetSupportedNerveMorphism.targetSubsetPullback1_apply,
    TargetSupportedNerveMorphism.targetSubsetEdgeMapOption_eq_some _ _ _ _ _ _ hm,Option.elim_some]
  congr 1

/-- 循環添字の三つの元を尽くす。 -/
theorem index_trichotomy (i v : Fin 3) : v = i ∨ v = i+1 ∨ v = i+2 := by
  fin_cases i <;> fin_cases v <;> decide +kernel
/-- 元の選択有向辺は左端添字で尽くされる。 -/
theorem fullEdge_surjective : Function.Surjective fullEdge := by
  intro e
  refine ⟨e.1.1.1,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact ((input_edge_iff _ _).mp e.1.2).symm
/-- 選択元辺の左端の原始添字。 -/
theorem fullEdge_left (v : Fin 3) : input.supported.nerve.edgeLeft (fullEdge v).1 = v := rfl
/-- 選択元辺の右端の原始添字。 -/
theorem fullEdge_right (v : Fin 3) : input.supported.nerve.edgeRight (fullEdge v).1 = v+1 := rfl
/-- 全商辺は指定した二つの向きを尽くす。 -/
theorem cutEdge_cases (i : Fin 3) (e : input.QuotientEdge (cut i)) :
    e = cutEdge0 i ∨ e = cutEdge1 i := by
  obtain ⟨hne,v,w,he,hv,hw⟩ := e.2
  have hwv := (input_edge_iff v w).mp he
  subst w
  obtain h | h | h := index_trichotomy i v
  · subst v
    exact (hne (hv.symm.trans ((cut_internal i).trans hw))).elim
  · subst v
    apply Or.inl
    apply Subtype.ext
    apply Prod.ext
    · exact hv.symm
    · exact hw.symm.trans (congrArg (cutChart i) (by fin_cases i <;> decide +kernel))
  · subst v
    apply Or.inr
    apply Subtype.ext
    apply Prod.ext
    · exact hv.symm
    · exact hw.symm.trans (congrArg (cutChart i) (by fin_cases i <;> decide +kernel))
/-- 同じ全target領域の選択辺も二つの向きを尽くす。 -/
theorem cutFullEdge_cases (i : Fin 3)
    (e : (input.quotientSupported (cut i)).EdgeInTargetSubset Set.univ) :
    e = cutFullEdge0 i ∨ e = cutFullEdge1 i := by
  obtain h | h := cutEdge_cases i e.1
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)
/-- 残存する逆向き二辺は異なる実セル。 -/
theorem cutFullEdges_ne (i : Fin 3) : cutFullEdge1 i ≠ cutFullEdge0 i := by
  intro h
  have he := congrArg (fun e => e.1.1.1) h
  exact (cutEdge0 i).2.1 he.symm
/-- 元cochainの二辺和と第三辺から粗cochainを生成する。 -/
def cutLift (i : Fin 3) (z : fullComplex.C1) :
    ((input.quotientSupported (cut i)).targetSubsetComplex Set.univ).C1 := by
  classical
  exact fun e => if e = cutFullEdge0 i then z (fullEdge i)+z (fullEdge (i+1)) else z (fullEdge (i+2))
/-- 生成粗cochainの二つの実辺評価。 -/
theorem cutLift_values (i : Fin 3) (z : fullComplex.C1) :
    cutLift i z (cutFullEdge0 i) = z (fullEdge i)+z (fullEdge (i+1)) ∧
    cutLift i z (cutFullEdge1 i) = z (fullEdge (i+2)) := by
  simp [cutLift,cutFullEdges_ne]
/-- 元cochainと粗比較像の差を生成する細potential。 -/
def cutPotential (i : Fin 3) (z : fullComplex.C1) : fullComplex.C0 := by
  classical
  exact fun v => if v.1 = i+1 then z (fullEdge i) else 0
/-- 生成potentialの実d0を三つの元辺で評価する。 -/
theorem cutPotential_d0 (i : Fin 3) (z : fullComplex.C1) :
    fullComplex.d0 (cutPotential i z) (fullEdge i) = z (fullEdge i) ∧
    fullComplex.d0 (cutPotential i z) (fullEdge (i+1)) = -z (fullEdge i) ∧
    fullComplex.d0 (cutPotential i z) (fullEdge (i+2)) = 0 := by
  change (input.supported.targetSubsetComplex Set.univ).d0 _ _ = _ ∧ _ = _ ∧ _ = _
  simp only [input.supported.targetSubsetComplex_d0_apply,cutPotential,
    TargetSupportedNerve.targetSubsetEdgeRight_val,TargetSupportedNerve.targetSubsetEdgeLeft_val,
    fullEdge_left,fullEdge_right]
  have h0 : i ≠ i+1 := by fin_cases i <;> decide +kernel
  have h1 : (i+1)+1 ≠ i+1 := by fin_cases i <;> decide +kernel
  have h2 : (i+2)+1 ≠ i+1 := by fin_cases i <;> decide +kernel
  have h3 : i+2 ≠ i+1 := by fin_cases i <;> decide +kernel
  simp [h0,h1,h2,h3]
/-- 任意の細cochainは実粗比較像に細d0像を加えたもの。 -/
theorem cut_surjective_representatives (i : Fin 3) (z : LinearMap.ker fullComplex.d1) :
    ∃ x : LinearMap.ker ((input.quotientSupported (cut i)).targetSubsetComplex Set.univ).d1,
    ∃ y, z.1 - (cutHom i).f1 x.1 = fullComplex.d0 y := by
  let x := cutLift i z.1
  refine ⟨⟨x,by funext f; exact f.1.elim⟩,cutPotential i z.1,?_⟩
  funext e
  obtain ⟨v,rfl⟩ := fullEdge_surjective e
  obtain h | h | h := index_trichotomy i v
  · subst v
    change z.1 (fullEdge i) - (cutHom i).f1 x (fullEdge i) = _
    rw [cutHom_internal,(cutPotential_d0 i z.1).1,sub_zero]
  · subst v
    change z.1 (fullEdge (i+1)) - (cutHom i).f1 x (fullEdge (i+1)) = _
    rw [cutHom_edge0,(cutPotential_d0 i z.1).2.1]
    change z.1 (fullEdge (i+1)) - cutLift i z.1 (cutFullEdge0 i) = _
    rw [(cutLift_values i z.1).1]
    ring
  · subst v
    change z.1 (fullEdge (i+2)) - (cutHom i).f1 x (fullEdge (i+2)) = _
    rw [cutHom_edge1,(cutPotential_d0 i z.1).2.2]
    change z.1 (fullEdge (i+2)) - cutLift i z.1 (cutFullEdge1 i) = _
    rw [(cutLift_values i z.1).2,sub_self]


/-- 元の実d0評価を指定chartに戻す。 -/
theorem full_d0_apply (y : fullComplex.C0) (v : Fin 3) :
    fullComplex.d0 y (fullEdge v) = y (fullChart (v+1))-y (fullChart v) := by
  rw [input.supported.targetSubsetComplex_d0_apply]
  rfl
/-- 三辺添字の二歩目。 -/
theorem step_two (i : Fin 3) : (i+1)+1 = i+2 := by
  fin_cases i <;> decide +kernel
/-- 三辺添字の三歩目。 -/
theorem step_three (i : Fin 3) : (i+2)+1 = i := by
  fin_cases i <;> decide +kernel
/-- 残存false→true辺の元商chart端点。 -/
theorem cutFullEdge0_left (i : Fin 3) :
    (input.quotientSupported (cut i)).nerve.edgeLeft (cutFullEdge0 i).1 = cutChart i (i+1) := rfl
/-- 残存false→true辺の右端。 -/
theorem cutFullEdge0_right (i : Fin 3) :
    (input.quotientSupported (cut i)).nerve.edgeRight (cutFullEdge0 i).1 = cutChart i (i+2) := rfl
/-- 残存true→false辺の左端。 -/
theorem cutFullEdge1_left (i : Fin 3) :
    (input.quotientSupported (cut i)).nerve.edgeLeft (cutFullEdge1 i).1 = cutChart i (i+2) := rfl
/-- 残存true→false辺の右端。 -/
theorem cutFullEdge1_right (i : Fin 3) :
    (input.quotientSupported (cut i)).nerve.edgeRight (cutFullEdge1 i).1 = cutChart i i := rfl
/-- 内部辺で等しいfine potentialから商potentialを生成する。 -/
def cutCoarsePotential (i : Fin 3) (y : fullComplex.C0) :
    ((input.quotientSupported (cut i)).targetSubsetComplex Set.univ).C0 := by
  classical
  exact fun v => if v.1 = cutChart i (i+2) then y (fullChart (i+2)) else y (fullChart i)
/-- 商potentialの実d0を二つの残存辺で評価する。 -/
theorem cutCoarsePotential_d0 (i : Fin 3) (y : fullComplex.C0) :
    ((input.quotientSupported (cut i)).targetSubsetComplex Set.univ).d0
      (cutCoarsePotential i y) (cutFullEdge0 i) = y (fullChart (i+2))-y (fullChart i) ∧
    ((input.quotientSupported (cut i)).targetSubsetComplex Set.univ).d0
      (cutCoarsePotential i y) (cutFullEdge1 i) = y (fullChart i)-y (fullChart (i+2)) := by
  have h0 : cutChart i (i+1) ≠ cutChart i (i+2) := (cutEdge0 i).2.1
  have h1 : cutChart i i ≠ cutChart i (i+2) := (cutEdge1 i).2.1.symm
  simp only [(input.quotientSupported (cut i)).targetSubsetComplex_d0_apply,cutCoarsePotential,
    TargetSupportedNerve.targetSubsetEdgeRight_val,TargetSupportedNerve.targetSubsetEdgeLeft_val,
    cutFullEdge0_left,cutFullEdge0_right,cutFullEdge1_left,cutFullEdge1_right]
  simp [h0,h1]
/-- 粗cycleの実比較像がexactなら元の粗cycleもexact。 -/
theorem cut_injective_representatives (i : Fin 3)
    (z : LinearMap.ker ((input.quotientSupported (cut i)).targetSubsetComplex Set.univ).d1)
    (hy : ∃ y, fullComplex.d0 y = (cutHom i).f1 z.1) :
    ∃ b, ((input.quotientSupported (cut i)).targetSubsetComplex Set.univ).d0 b = z.1 := by
  obtain ⟨y,hy⟩ := hy
  have hInt := congrFun hy (fullEdge i)
  rw [full_d0_apply,cutHom_internal] at hInt
  have hYi := sub_eq_zero.mp hInt
  refine ⟨cutCoarsePotential i y,?_⟩
  funext e
  obtain h | h := cutFullEdge_cases i e
  · subst e
    rw [(cutCoarsePotential_d0 i y).1]
    have h := congrFun hy (fullEdge (i+1))
    rw [full_d0_apply,cutHom_edge0,step_two,hYi] at h
    exact h
  · subst e
    rw [(cutCoarsePotential_d0 i y).2]
    have h := congrFun hy (fullEdge (i+2))
    rw [full_d0_apply,cutHom_edge1,step_three] at h
    exact h
/-- 三角形の任意一辺縮約は、同じ全領域実H¹比較で全単射。 -/
theorem cutHom_bijective (i : Fin 3) : Function.Bijective (cutHom i).h1Map :=
  bijective_of_representatives (cutHom i) (cut_injective_representatives i)
    (cut_surjective_representatives i)


/-- 任意一辺縮約の全領域比較は、canonical逆像を保った元の実比較でも全単射。 -/
theorem cut_full_bijective (i : Fin 3) : Function.Bijective
    ((input.quotientComparison (cut i)).aSubnerveComparisonHom Set.univ).h1Map := by
  have htransport : ∀ {C D E : ThreeCochainComplex ℚ} (h : D = E)
      (f : ThreeCochainComplex.Hom C D),
      Function.Bijective (transportHom h f).h1Map ↔ Function.Bijective f.h1Map := by
    intro C D E h f; cases h; rfl
  exact (htransport _ _).mp (cutHom_bijective i)
/-- 元商targetは一点なので空/全領域を尽くし、任意一辺縮約はSafe。 -/
theorem cut_safe (i : Fin 3) : input.Safe (cut i) := by
  classical
  intro A
  by_cases h : ∃ x, x ∈ A
  · obtain ⟨x,hx⟩ := h
    have hA : A = Set.univ := by
      apply Set.eq_univ_iff_forall.mpr
      intro y
      exact Subsingleton.elim x y ▸ hx
    subst A
    exact cut_full_bijective i
  · have hA : A = ∅ := by
      ext x
      exact ⟨fun hx => (h ⟨x,hx⟩).elim,fun hx => hx.elim⟩
    subst A
    rw [input.quotient_actualHom_old]
    exact PrimitiveInput.empty_comparison_bijective (input.quotientMorphism (cut i))

end Triangle
end AAT.AG.SafeCoarseningOrder
#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
