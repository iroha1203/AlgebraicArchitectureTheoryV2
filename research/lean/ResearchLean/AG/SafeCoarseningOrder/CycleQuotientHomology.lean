import ResearchLean.AG.SafeCoarseningOrder.CycleHomology

/-! # 全商閉路の実比較とrank

## Implementation notes

商d0核を元閉路から定数関数へ同定する。異なる商有向辺のspikeを同じ部分辺像で引き戻し、正periodから実全射liftを構成する。セル数は実rankの証明後にJへ使う。
同次元だけの射同定は用いず、元部分辺像と実全射liftを先に証明する。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder.Cycle
open CanonicalResolution ResolutionInvariance TwoPhase AtlasGluingWidth
variable (n : ℕ) [NeZero n] (hn : 2 ≤ n)
variable (R : Coarsening Bool (ZMod n))
/-- 任意の独立分割対から生成した商の全領域支持複体。 -/
abbrev coarseComplex := ((input n hn).quotientSupported R).targetSubsetComplex Set.univ
omit [NeZero n] in
/-- 元全台と商mk全射から任意商chartの台を全targetへ生成する。 -/
theorem quotient_support_all (c : Quotient R.2) (t : Quotient R.1) :
    t ∈ (input n hn).quotientSupport R c := by
  induction c using Quotient.inductionOn with | _ v =>
    induction t using Quotient.inductionOn with | _ s =>
      exact (input n hn).quotientSupport_mk R v True.intro
/-- 元商chartの全領域セル。 -/
def coarseChart (c : Quotient R.2) :
    ((input n hn).quotientSupported R).ChartInTargetSubset Set.univ :=
  ⟨c,Quotient.mk R.1 false,quotient_support_all n hn R c _,True.intro⟩
/-- 異端点の元商有向辺を同じK1全領域セルへ入れる。 -/
def coarseEdge (e : (input n hn).QuotientEdge R) :
    ((input n hn).quotientSupported R).EdgeInTargetSubset Set.univ :=
  ⟨e,Quotient.mk R.1 false,
    ⟨quotient_support_all n hn R e.1.1 _,quotient_support_all n hn R e.1.2 _⟩,True.intro⟩
/-- 元商実微分の両端評価式。 -/
theorem coarse_edge_d0 (x : (coarseComplex n hn R).C0) (e : (input n hn).QuotientEdge R) :
    (coarseComplex n hn R).d0 x (coarseEdge n hn R e) =
      x (coarseChart n hn R e.1.2)-x (coarseChart n hn R e.1.1) := by
  rw [TargetSupportedNerve.targetSubsetComplex_d0_apply]
  rfl
/-- i→i+1で値が不変なら、元有限閉路の全点で同じ値を取る。 -/
theorem periodic_constant (f : ZMod n → ℚ) (hf : ∀ i, f (i+1)=f i) : ∀ i, f i=f 0 := by
  intro i
  have hnat (m : ℕ) : f (m : ZMod n)=f 0 := by
    induction m with
    | zero => simp only [Nat.cast_zero]
    | succ m ih => rw [Nat.cast_succ,hf,ih]
  simpa only [ZMod.natCast_zmod_val] using hnat i.val
/-- 商実d0核の元は、元閉路を通じ全商chartで定数となる。 -/
theorem coarse_d0_zero_constant (x : (coarseComplex n hn R).C0)
    (hx : (coarseComplex n hn R).d0 x = 0) :
    ∀ c, x c=x (coarseChart n hn R (Quotient.mk R.2 0)) := by
  let f : ZMod n → ℚ := fun v => x (coarseChart n hn R (Quotient.mk R.2 v))
  have hf : ∀ i, f (i+1)=f i := by
    intro i
    by_cases h : Quotient.mk R.2 i = Quotient.mk R.2 (i+1)
    · exact congrArg (fun c => x (coarseChart n hn R c)) h.symm
    · let e : (input n hn).QuotientEdge R :=
        ⟨(Quotient.mk R.2 i,Quotient.mk R.2 (i+1)),h,i,i+1,rfl,rfl,rfl⟩
      have he := congrFun hx (coarseEdge n hn R e)
      rw [coarse_edge_d0] at he
      exact sub_eq_zero.mp he
  intro c
  have hc : coarseChart n hn R c.1 = c := Subtype.ext rfl
  rw [← hc]
  induction c.1 using Quotient.inductionOn with | _ v =>
    exact periodic_constant n f hf v
/-- 商実d0核を元chart0評価と定数関数でℚへ両方向同定する。 -/
def coarseKernelEquiv : LinearMap.ker (coarseComplex n hn R).d0 ≃ₗ[ℚ] ℚ where
  toFun x := x.1 (coarseChart n hn R (Quotient.mk R.2 0))
  invFun a := ⟨fun _ => a,by funext e; rw [TargetSupportedNerve.targetSubsetComplex_d0_apply]; change a-a=0; exact sub_self a⟩
  left_inv x := by
    apply Subtype.ext
    funext c
    exact (coarse_d0_zero_constant n hn R x.1 x.2 c).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 商chartと実選択chartの全単射。 -/
def coarseChartEquiv : Quotient R.2 ≃
    ((input n hn).quotientSupported R).ChartInTargetSubset Set.univ where
  toFun := coarseChart n hn R
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl
/-- 商有向辺と実選択K1辺の全単射。 -/
def coarseEdgeEquiv : (input n hn).QuotientEdge R ≃
    ((input n hn).quotientSupported R).EdgeInTargetSubset Set.univ where
  toFun := coarseEdge n hn R
  invFun := Subtype.val
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl
/-- 原始有限chartから商chartの有限一覧instanceを生成する。 -/
instance quotientChartFintype (Q : Setoid (ZMod n)) : Fintype (Quotient Q) := Fintype.ofFinite _
/-- 商chart順序対subtypeから有向商辺の有限一覧instanceを生成する。 -/
instance quotientEdgeFintype : Fintype ((input n hn).QuotientEdge R) := Fintype.ofFinite _
/-- 商chart全単射から元次数0の次元を数える。 -/
theorem coarse_C0_dimension : Module.finrank ℚ (coarseComplex n hn R).C0 =
    Fintype.card (Quotient R.2) := by
  classical
  let eqv := LinearEquiv.funCongrLeft ℚ ℚ (coarseChartEquiv n hn R)
  exact eqv.finrank_eq.trans (Module.finrank_pi ℚ)
/-- 逆向きセルを保持する商辺全単射から元次数1を数える。 -/
theorem coarse_C1_dimension : Module.finrank ℚ (coarseComplex n hn R).C1 =
    Fintype.card ((input n hn).QuotientEdge R) := by
  classical
  let eqv := LinearEquiv.funCongrLeft ℚ ℚ (coarseEdgeEquiv n hn R)
  exact eqv.finrank_eq.trans (Module.finrank_pi ℚ)
/-- 実d0核の定数関数同型から次元1を導く。 -/
theorem coarse_d0_kernel_dimension : Module.finrank ℚ (LinearMap.ker (coarseComplex n hn R).d0) = 1 :=
  (coarseKernelEquiv n hn R).finrank_eq.trans (Module.finrank_self ℚ)
/-- 元Empty面から全次数1がcocycleであることを導く。 -/
theorem coarse_d1_kernel_dimension : Module.finrank ℚ (LinearMap.ker (coarseComplex n hn R).d1) =
    Fintype.card ((input n hn).QuotientEdge R) := by
  classical
  have h : (coarseComplex n hn R).d1=0 := by
    apply LinearMap.ext
    intro z
    funext f
    exact f.1.elim
  rw [h,LinearMap.ker_zero,finrank_top]
  exact coarse_C1_dimension n hn R
/-- cocycleへの実d0射は同じd0核を持つ。 -/
theorem coarse_boundary_kernel : LinearMap.ker (coarseComplex n hn R).boundaryToCycles =
    LinearMap.ker (coarseComplex n hn R).d0 := by
  ext x
  simp only [LinearMap.mem_ker,Subtype.ext_iff,ThreeCochainComplex.boundaryToCycles_apply,
    ZeroMemClass.coe_zero]
/-- 商実d0核の構成とrank-nullityからH¹・chart・有向辺数を結ぶ。 -/
theorem coarse_H1_euler : Module.finrank ℚ (coarseComplex n hn R).H1 +
    Fintype.card (Quotient R.2) = Fintype.card ((input n hn).QuotientEdge R) + 1 := by
  classical
  have hq := (LinearMap.range (coarseComplex n hn R).boundaryToCycles).finrank_quotient_add_finrank
  have hb := (coarseComplex n hn R).boundaryToCycles.finrank_range_add_finrank_ker
  rw [coarse_d1_kernel_dimension] at hq
  rw [coarse_boundary_kernel,coarse_d0_kernel_dimension,coarse_C0_dimension] at hb
  change Module.finrank ℚ (coarseComplex n hn R).H1 + _ = _ at hq
  omega

open AtlasDefectComposition
/-- canonical全領域逆像を等号transportした同じ実商比較Hom。 -/
def fullHom : ThreeCochainComplex.Hom (coarseComplex n hn R) (fullComplex n hn) :=
  transportHom (congrArg (input n hn).supported.targetSubsetComplex Set.preimage_univ)
    (((input n hn).quotientComparison R).aSubnerveComparisonHom Set.univ)
/-- 同じ全Homを元hereditary比較の全領域射へ戻す。 -/
theorem fullHom_eq_old : fullHom n hn R =
    ((input n hn).quotientMorphism R).targetSubsetComparisonHom Set.univ Set.univ
      (fun _ _ => True.intro) := by
  rw [fullHom,PrimitiveInput.quotient_actualHom_old]
  exact targetSubsetComparisonHom_transport ((input n hn).quotientMorphism R) Set.univ _
    Set.univ Set.preimage_univ (fun _ h => h) (fun _ _ => True.intro)
/-- 内部化した元辺の実次数1引き戻しは零になる。 -/
theorem fullHom_edge_none (v : ZMod n) (z : (coarseComplex n hn R).C1)
    (he : (input n hn).quotientEdgeMap R (fullEdge n hn v).1=none) :
    (fullHom n hn R).f1 z (fullEdge n hn v)=0 := by
  rw [fullHom_eq_old]
  rw [TargetSupportedNerveMorphism.targetSubsetComparisonHom_f1_apply,
    TargetSupportedNerveMorphism.targetSubsetEdgeMapOption_eq_none _ _ _ _ _ he]
  rfl
/-- 残る元辺の実引き戻しは同じ有向商辺の評価である。 -/
theorem fullHom_edge_some (v : ZMod n) (e : (input n hn).QuotientEdge R)
    (z : (coarseComplex n hn R).C1)
    (he : (input n hn).quotientEdgeMap R (fullEdge n hn v).1=some e) :
    (fullHom n hn R).f1 z (fullEdge n hn v)=z (coarseEdge n hn R e) := by
  rw [fullHom_eq_old]
  rw [TargetSupportedNerveMorphism.targetSubsetComparisonHom_f1_apply,
    TargetSupportedNerveMorphism.targetSubsetEdgeMapOption_eq_some _ _ _ _ _ _ he,Option.elim_some]
  congr 1
/-- 指定有向商辺だけ1とする元商cochain。 -/
def coarseSpike (e : (input n hn).QuotientEdge R) : (coarseComplex n hn R).C1 :=
  by classical exact fun f => if f.1=e then 1 else 0
/-- 元商spikeの指定セル評価は1である。 -/
theorem coarseSpike_self (e : (input n hn).QuotientEdge R) :
    coarseSpike n hn R e (coarseEdge n hn R e)=1 := by
  classical
  simp [coarseSpike,coarseEdge]
/-- 元商spikeの全実セル評価は非負である。 -/
theorem coarseSpike_nonneg (e f : (input n hn).QuotientEdge R) :
    0 ≤ coarseSpike n hn R e (coarseEdge n hn R f) := by
  classical
  dsimp only [coarseSpike]
  split <;> norm_num
/-- 全商辺は同じ部分辺像に現れる元i→i+1辺を持つ。 -/
theorem coarse_edge_has_original (e : (input n hn).QuotientEdge R) :
    ∃ v, (input n hn).quotientEdgeMap R (fullEdge n hn v).1=some e := by
  obtain ⟨_,v,w,he,hv,hw⟩ := e.2
  rw [input_edge_iff] at he
  subst w
  exact ⟨v,((input n hn).quotientEdgeMap_eq_some _ _ _).mpr ⟨hv,hw⟩⟩
/-- 実部分辺像の全引き戻し値は非負である。 -/
theorem fullHom_spike_nonneg (e : (input n hn).QuotientEdge R) (v : ZMod n) :
    0 ≤ (fullHom n hn R).f1 (coarseSpike n hn R e) (fullEdge n hn v) := by
  cases he : (input n hn).quotientEdgeMap R (fullEdge n hn v).1 with
  | none => rw [fullHom_edge_none n hn R v _ he]
  | some f => rw [fullHom_edge_some n hn R v f _ he]; exact coarseSpike_nonneg n hn R e f
/-- 同じ商spikeの実pullback periodは元の残存辺により正となる。 -/
theorem period_coarseSpike_pos (e : (input n hn).QuotientEdge R) :
    0 < period n hn ((fullHom n hn R).f1 (coarseSpike n hn R e)) := by
  obtain ⟨v,hv⟩ := coarse_edge_has_original n hn R e
  rw [period_apply]
  apply Finset.sum_pos'
  · intro i _
    exact fullHom_spike_nonneg n hn R e i
  · refine ⟨v,Finset.mem_univ v,?_⟩
    rw [fullHom_edge_some n hn R v e _ hv,coarseSpike_self]
    norm_num
/-- 元Empty面から全商cochainを同じ実cocycleへ入れる。 -/
def coarseCycle (z : (coarseComplex n hn R).C1) : LinearMap.ker (coarseComplex n hn R).d1 :=
  ⟨z,by funext f; exact f.1.elim⟩
/-- 元商cochainを同じ実d0像によるH¹商へ入れる。 -/
def coarseClassOf (z : (coarseComplex n hn R).C1) : (coarseComplex n hn R).H1 :=
  (LinearMap.range (coarseComplex n hn R).boundaryToCycles).mkQ (coarseCycle n hn R z)
/-- 同じ実H¹比較の像を元pullback cochainのperiodで評価する。 -/
theorem period_image_class (z : (coarseComplex n hn R).C1) :
    periodH1 n hn ((fullHom n hn R).h1Map (coarseClassOf n hn R z)) =
      period n hn ((fullHom n hn R).f1 z) := by
  rw [coarseClassOf,ThreeCochainComplex.Hom.h1Map_mk]
  rfl
/-- 実pullbackの正periodと元period同型から実H¹比較の全射liftを構成する。 -/
theorem fullHom_h1_surjective (e : (input n hn).QuotientEdge R) :
    Function.Surjective (fullHom n hn R).h1Map := by
  intro y
  let b := period n hn ((fullHom n hn R).f1 (coarseSpike n hn R e))
  have hb : b ≠ 0 := ne_of_gt (period_coarseSpike_pos n hn R e)
  refine ⟨(periodH1 n hn y/b) • coarseClassOf n hn R (coarseSpike n hn R e),?_⟩
  apply (periodH1_bijective n hn).1
  rw [map_smul,map_smul,period_image_class]
  change periodH1 n hn y/b*b=periodH1 n hn y
  exact div_mul_cancel₀ _ hb

/-- 同じ実比較の全射性を証明した後でrank1を導く。 -/
theorem fullHom_h1_rank (e : (input n hn).QuotientEdge R) :
    Module.finrank ℚ (LinearMap.range (fullHom n hn R).h1Map)=1 := by
  rw [LinearMap.range_eq_top.mpr (fullHom_h1_surjective n hn R e),finrank_top]
  exact full_H1_dimension n hn
/-- 実rank証明と商d0構成の後で実核・余核の二欠損を評価する。 -/
theorem fullHom_defect (e : (input n hn).QuotientEdge R) :
    blockDefect (fullHom n hn R).h1Map =
      (Fintype.card ((input n hn).QuotientEdge R)-Fintype.card (Quotient R.2),0) := by
  rw [blockDefect_eq_finrank_sub_range,fullHom_h1_rank n hn R e,full_H1_dimension n hn]
  have hd := coarse_H1_euler n hn R
  have hr := (fullHom n hn R).h1Map.finrank_range_add_finrank_ker
  rw [fullHom_h1_rank n hn R e] at hr
  congr 1
  omega
/-- 等号transportを戻してcanonical同じ実比較の全領域Jを評価する。 -/
theorem actual_full_defect (e : (input n hn).QuotientEdge R) :
    blockDefect (((input n hn).quotientComparison R).aSubnerveComparisonHom Set.univ).h1Map =
      (Fintype.card ((input n hn).QuotientEdge R)-Fintype.card (Quotient R.2),0) := by
  rw [← transportHom_defect (congrArg (input n hn).supported.targetSubsetComplex Set.preimage_univ)]
  exact fullHom_defect n hn R e

end AAT.AG.SafeCoarseningOrder.Cycle

#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
