import ResearchLean.AG.SafeCoarseningOrder.UniformSafety
import ResearchLean.AG.AtlasGluingWidth.WidthIntegration

/-! # 元有向閉路のperiodと実H¹

## Implementation notes

元i→i+1辺値を旧交互閉路a辺へ零延長し、受理累積積分から同じ実d0の原始関数を生成する。period商射の単射/全射と指定spike非零を実代表で証明する。
同次元H¹間の別の同型は元periodと指定spikeを保持しないため用いない。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder.Cycle
open CanonicalResolution ResolutionInvariance TwoPhase AtlasGluingWidth
variable (n : ℕ) [NeZero n] (hn : 2 ≤ n)
/-- Bool/id、全台、i→i+1の元有向閉路。n≥2から非対角性を生成する。 -/
def input : PrimitiveInput Bool Bool (ZMod n) where
  read := id
  read_surjective := Function.surjective_id
  edge v w := w = v+1
  edge_ne v w h := by
    subst w
    intro he
    have hz : (1 : ZMod n) = 0 := add_left_cancel (he.symm.trans (add_zero v).symm)
    have := ZMod.one_eq_zero_iff.mp hz
    omega
  support _ := Set.univ
  support_nonempty _ := Set.univ_nonempty
omit [NeZero n] in
/-- 指定有向辺表の基本評価API。 -/
@[simp] theorem input_edge_iff (v w : ZMod n) : (input n hn).edge v w ↔ w=v+1 := Iff.rfl
omit [NeZero n] in
/-- 指定chart台の基本評価API。 -/
@[simp] theorem input_support (v : ZMod n) : (input n hn).support v=Set.univ := rfl
omit [NeZero n] in
/-- 指定元readingの基本評価API。 -/
@[simp] theorem input_read (s : Bool) : (input n hn).read s=s := rfl
/-- 元閉路を全target領域で選択した同じ支持複体。 -/
abbrev fullComplex := (input n hn).supported.targetSubsetComplex Set.univ
/-- 元chartの全領域セル。 -/
def fullChart (v : ZMod n) : (input n hn).supported.ChartInTargetSubset Set.univ :=
  ⟨v,false,True.intro,True.intro⟩
/-- 元i→i+1辺の全領域セル。 -/
def fullEdge (v : ZMod n) : (input n hn).supported.EdgeInTargetSubset Set.univ :=
  ⟨⟨(v,v+1),rfl⟩,false,⟨True.intro,True.intro⟩,True.intro⟩
/-- 元選択辺の左端indexを保持する基本API。 -/
@[simp] theorem fullEdge_index (i : ZMod n) : (fullEdge n hn i).1.1.1=i := rfl
/-- 選択元辺はその左端添字から全て復元される。 -/
theorem full_edge_complete (e : (input n hn).supported.EdgeInTargetSubset Set.univ) :
    fullEdge n hn e.1.1.1 = e := by
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext rfl e.1.2.symm
/-- 元実微分は右端値と左端値の差である。 -/
theorem edge_d0 (x : (fullComplex n hn).C0) (v : ZMod n) :
    (fullComplex n hn).d0 x (fullEdge n hn v) =
      x (fullChart n hn (v+1)) - x (fullChart n hn v) := by
  rw [TargetSupportedNerve.targetSubsetComplex_d0_apply]
  rfl
/-- 全元有向辺値の和。期待H¹次元から構成しない。 -/
def period : (fullComplex n hn).C1 →ₗ[ℚ] ℚ where
  toFun z := ∑ i : ZMod n,z (fullEdge n hn i)
  map_add' x y := by
    change (∑ i, (x (fullEdge n hn i)+y (fullEdge n hn i))) = _
    exact Finset.sum_add_distrib
  map_smul' a x := by
    change (∑ i,a*x (fullEdge n hn i)) = a*(∑ i,x (fullEdge n hn i))
    rw [Finset.mul_sum]
/-- periodの元辺値和を返す基本評価API。 -/
@[simp] theorem period_apply (z : (fullComplex n hn).C1) :
    period n hn z=∑ i : ZMod n,z (fullEdge n hn i) := rfl
/-- 添字の巡回全単射により実d0像のperiodは零になる。 -/
theorem period_boundary (x : (fullComplex n hn).C0) : period n hn ((fullComplex n hn).d0 x) = 0 := by
  rw [period_apply]
  simp_rw [edge_d0]
  have hs : (∑ i : ZMod n,x (fullChart n hn (i+1))) = ∑ i : ZMod n,x (fullChart n hn i) :=
    Equiv.sum_comp (Equiv.addRight (1 : ZMod n)) (fun i => x (fullChart n hn i))
  rw [Finset.sum_sub_distrib,hs,sub_self]
/-- 各元辺値を旧a辺へ、旧b辺へ零を置く交互閉路cochain。 -/
def extended (z : (fullComplex n hn).C1) : Width.Cochain n :=
  fun e => if e.2 then 0 else z (fullEdge n hn e.1)
/-- 零延長の元辺評価を公開する基本API。 -/
theorem extended_apply (z : (fullComplex n hn).C1) (e : ZMod n × Bool) :
    extended n hn z e = if e.2 then 0 else z (fullEdge n hn e.1) := rfl
/-- 交互閉路への零延長は元periodを保持する。 -/
theorem extended_period (z : (fullComplex n hn).C1) : Width.period n (extended n hn z) = period n hn z := by
  simp only [Width.period_apply,extended,Bool.false_eq_true,if_false,if_true,add_zero]
  rfl
/-- 受理G136累積積分から元chartへ制限した原始関数。 -/
def potential (z : (fullComplex n hn).C1) : (fullComplex n hn).C0 :=
  fun v => Width.potential n (extended n hn z) (v.1,false)
/-- 元chartへの原始関数の制限を評価する基本API。 -/
theorem potential_apply (z : (fullComplex n hn).C1) (v : ZMod n) :
    potential n hn z (fullChart n hn v) = Width.potential n (extended n hn z) (v,false) := rfl
/-- period零の全元cochainは同じ実d0で積分される。 -/
theorem differential_potential (z : (fullComplex n hn).C1) (hz : period n hn z = 0) :
    (fullComplex n hn).d0 (potential n hn z) = z := by
  have ho := Width.difference_potential n (extended n hn z) ((extended_period n hn z).trans hz)
  funext e
  rw [← full_edge_complete n hn e,edge_d0]
  have ha := congrFun ho (e.1.1.1,false)
  have hb := congrFun ho (e.1.1.1,true)
  rw [Width.difference_apply] at ha hb
  simp only [Width.left_apply,Width.right_apply,extended_apply,
    Bool.false_eq_true,if_false,if_true] at ha hb
  rw [potential_apply,potential_apply]
  linarith
/-- 空面から任意元cochainを同じ実cocycleへ入れる。 -/
def cycle (z : (fullComplex n hn).C1) : LinearMap.ker (fullComplex n hn).d1 :=
  ⟨z,by funext f; exact f.1.elim⟩
/-- 同じ実d0像による商への元cochain類。 -/
def classOf (z : (fullComplex n hn).C1) : (fullComplex n hn).H1 :=
  (LinearMap.range (fullComplex n hn).boundaryToCycles).mkQ (cycle n hn z)
/-- 実d0像を消すperiodを元H¹商へ降ろした線形射。 -/
def periodH1 : (fullComplex n hn).H1 →ₗ[ℚ] ℚ :=
  (LinearMap.range (fullComplex n hn).boundaryToCycles).liftQ
    ((period n hn).comp (LinearMap.ker (fullComplex n hn).d1).subtype) (by
      rintro z ⟨x,rfl⟩
      exact period_boundary n hn x)
/-- H¹上のperiodは同じcochainの辺値和を返す。 -/
@[simp] theorem periodH1_classOf (z : (fullComplex n hn).C1) :
    periodH1 n hn (classOf n hn z) = period n hn z := rfl
/-- 元辺0→1だけ1、他の元辺は0である指定cochain。 -/
def spike : (fullComplex n hn).C1 := fun e => if e.1.1.1 = 0 then 1 else 0
/-- 元spikeの辺値を評価する基本API。 -/
@[simp] theorem spike_apply (e : (input n hn).supported.EdgeInTargetSubset Set.univ) :
    spike n hn e=if e.1.1.1=0 then 1 else 0 := rfl
/-- 指定spikeのperiodは1である。 -/
theorem period_spike : period n hn (spike n hn) = 1 := by
  rw [period_apply]
  simp only [spike_apply,fullEdge_index]
  simp
/-- period零の元H¹類は生成potentialにより零となる。 -/
theorem class_zero_of_period_zero (c : (fullComplex n hn).H1) (hc : periodH1 n hn c = 0) :
    c = 0 := by
  obtain ⟨z,rfl⟩ := (LinearMap.range (fullComplex n hn).boundaryToCycles).mkQ_surjective c
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨potential n hn z.1,?_⟩
  apply Subtype.ext
  exact differential_potential n hn z.1 hc
/-- 同じperiodの単射性とspikeによる全射性を証明する。 -/
theorem periodH1_bijective : Function.Bijective (periodH1 n hn) := by
  constructor
  · intro a b hab
    have h : periodH1 n hn (a-b) = 0 := by rw [map_sub,hab,sub_self]
    exact sub_eq_zero.mp (class_zero_of_period_zero n hn (a-b) h)
  · intro a
    refine ⟨a • classOf n hn (spike n hn),?_⟩
    rw [map_smul,periodH1_classOf,period_spike]
    simp
/-- 同じ元periodから生成した実H¹とℚの両方向同型。 -/
def fullH1Equiv : (fullComplex n hn).H1 ≃ₗ[ℚ] ℚ :=
  LinearEquiv.ofBijective (periodH1 n hn) (periodH1_bijective n hn)
/-- 指定cochain類はperiod1により同じ元H¹で非零である。 -/
theorem spike_nonzero : classOf n hn (spike n hn) ≠ 0 := by
  intro h
  have hh := congrArg (periodH1 n hn) h
  rw [periodH1_classOf,period_spike,map_zero] at hh
  exact one_ne_zero hh


/-- 実period同型の後で元H¹次元を導く。 -/
theorem full_H1_dimension : Module.finrank ℚ (fullComplex n hn).H1 = 1 :=
  (fullH1Equiv n hn).finrank_eq.trans (Module.finrank_self ℚ)
end AAT.AG.SafeCoarseningOrder.Cycle

#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
