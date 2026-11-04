import ResearchLean.AG.SpecifiedRepairLifting.IntegerElimination

/-! # 有限表示整数群の射と逆像

Implementation notes: 群は原始関係行列の像による商として保持する。
関係保存と商等号は同じ原始整数solverで有限検査する。
整数系の補助変数を元群の自由度と数えないため、射影のkernelも
二つ目の整数系で生成し、全解のパラメータをその関係で割る。
有理化や整数核の零性による商解の一意性の代用は採らない。
-/
namespace AAT.AG.SpecifiedRepairLifting.PresentedGroups
open Matrix
open IntegerElimination

/-- 二つの自由座標を連結する。 -/
def join {n r : ℕ} (x : Vec n) (u : Vec r) : Vec (n+r) := Fin.addCases x u
/-- 連結座標の前半。 -/
def first {n r : ℕ} (v : Vec (n+r)) : Vec n := fun i => v (Fin.castAdd r i)
/-- 連結座標の後半。 -/
def second {n r : ℕ} (v : Vec (n+r)) : Vec r := fun i => v (Fin.natAdd n i)
/-- 連結の前半は元の前半座標。 -/
@[simp] theorem first_join {n r : ℕ} (x : Vec n) (u : Vec r) : first (join x u) = x := by
  ext i
  simp [first,join]
/-- 連結の後半は元の後半座標。 -/
@[simp] theorem second_join {n r : ℕ} (x : Vec n) (u : Vec r) : second (join x u) = u := by
  ext i
  simp [second,join]
/-- 全自由座標を前半と後半から復元する。 -/
@[simp] theorem join_parts {n r : ℕ} (v : Vec (n+r)) : join (first v) (second v) = v := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [join,first,second]
/-- 二行列を横に並べた原始行列。 -/
def beside {m n r : ℕ} (A : Mat m n) (B : Mat m r) : Mat m (n+r) :=
  fun i => Fin.addCases (A i) (B i)
/-- 横連結行列の元整数ベクトル上の評価。 -/
theorem beside_mulVec {m n r : ℕ} (A : Mat m n) (B : Mat m r) (v : Vec (n+r)) :
    beside A B *ᵥ v = A *ᵥ first v + B *ᵥ second v := by
  ext i
  simp [mulVec,dotProduct,beside,first,second,Fin.sum_univ_add]
/-- 自由座標の前半への整数線形射。 -/
def firstMap (n r : ℕ) : Vec (n+r) →ₗ[ℤ] Vec n where
  toFun := first
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- 任意の有限整数生成元と関係を持つ表示。 -/
structure Presentation where
  generators : ℕ
  relations : ℕ
  matrix : Mat generators relations
/-- 元の関係像。 -/
def relationSpace (P : Presentation) : Submodule ℤ (Vec P.generators) :=
  LinearMap.range (Matrix.toLin' P.matrix)
/-- torsionを含む元の有限表示群。 -/
abbrev Group (P : Presentation) := Vec P.generators ⧸ relationSpace P
/-- 原始代表を元の商群へ送る。 -/
def quotientClass (P : Presentation) : Vec P.generators →ₗ[ℤ] Group P := (relationSpace P).mkQ
/-- 原始商の全元に整数代表がある。 -/
theorem class_surjective (P : Presentation) : Function.Surjective (quotientClass P) :=
  Submodule.mkQ_surjective _
/-- 原始代表の零性は元関係の整数証人と同値。 -/
theorem class_zero_iff (P : Presentation) (x : Vec P.generators) :
    quotientClass P x = 0 ↔ ∃ u : Vec P.relations, P.matrix *ᵥ u = x := by
  change (Submodule.Quotient.mk x : Group P) = 0 ↔ x ∈ relationSpace P
  exact Submodule.Quotient.mk_eq_zero (relationSpace P)
/-- 同じ商元であることは元関係を法とする厳密等号。 -/
theorem class_eq_iff (P : Presentation) (x y : Vec P.generators) :
    quotientClass P x = quotientClass P y ↔ ∃ u : Vec P.relations, P.matrix *ᵥ u = x-y := by
  rw [← sub_eq_zero, ← map_sub, class_zero_iff]
/-- 零性の有限判定。 -/
def isZero (P : Presentation) (x : Vec P.generators) : Bool :=
  decide (Divisible (produce P.matrix) x)
/-- 零性判定と同じ商群の零性が一致する。 -/
theorem isZero_correct (P : Presentation) (x : Vec P.generators) :
    isZero P x = true ↔ quotientClass P x = 0 := by
  rw [isZero,decide_eq_true_eq,divisible_iff_solution _ (produce_valid _),class_zero_iff]
/-- 原始行列の関係保存は関係の全列について有限判定する。 -/
def MapValid (P Q : Presentation) (A : Mat Q.generators P.generators) : Prop :=
  ∀ j : Fin P.relations, Divisible (produce Q.matrix) ((A * P.matrix).col j)
/-- 関係保存の検査は有限個の整数整除で決定可能。 -/
instance mapValidDecidable (P Q : Presentation) (A : Mat Q.generators P.generators) :
    Decidable (MapValid P Q A) := by unfold MapValid; infer_instance
/-- 関係保存の有限検査から元商上の射の条件を生成する。 -/
theorem relation_preserved (P Q : Presentation) (A : Mat Q.generators P.generators)
    (h : MapValid P Q A) : relationSpace P ≤ LinearMap.ker ((quotientClass Q).comp (Matrix.toLin' A)) := by
  rintro x ⟨u,rfl⟩
  change quotientClass Q (A *ᵥ (P.matrix *ᵥ u)) = 0
  rw [mulVec_mulVec]
  have hc : ∀ j, quotientClass Q ((A * P.matrix).col j) = 0 := by
    intro j
    exact (class_zero_iff Q _).mpr ((divisible_iff_solution _ (produce_valid _) _).mp (h j))
  have he : (A * P.matrix) *ᵥ u = ∑ j, u j • (A * P.matrix).col j := by
    ext i
    simp [mulVec,dotProduct,mul_comm]
  rw [he,map_sum]
  simp only [map_smul, hc, smul_zero, Finset.sum_const_zero]
/-- 有限検査を通った原始行列から同じ元商上の射を構成する。 -/
def map (P Q : Presentation) (A : Mat Q.generators P.generators) (h : MapValid P Q A) :
    Group P →ₗ[ℤ] Group Q :=
  (relationSpace P).liftQ ((quotientClass Q).comp (Matrix.toLin' A)) (relation_preserved P Q A h)
/-- 商射は原始行列の同じ代表を送る。 -/
@[simp] theorem map_class (P Q : Presentation) (A : Mat Q.generators P.generators)
    (h : MapValid P Q A) (x : Vec P.generators) : map P Q A h (quotientClass P x) = quotientClass Q (A *ᵥ x) := rfl
/-- 商上の逆像方程式に関係証人を加えた原始整数行列。 -/
def equationMatrix (P Q : Presentation) (A : Mat Q.generators P.generators) :
    Mat Q.generators (P.generators+Q.relations) := beside A (-Q.matrix)
/-- 拡大整数系の評価は元像から関係証人を引く。 -/
theorem equationMatrix_mulVec (P Q : Presentation) (A : Mat Q.generators P.generators)
    (v : Vec (P.generators+Q.relations)) :
    equationMatrix P Q A *ᵥ v = A *ᵥ first v - Q.matrix *ᵥ second v := by
  rw [equationMatrix,beside_mulVec,neg_mulVec,sub_eq_add_neg]
/-- 同じ商射の指定逆像と関係証人の存在が両方向に一致する。 -/
theorem map_class_eq_iff (P Q : Presentation) (A : Mat Q.generators P.generators)
    (h : MapValid P Q A) (x : Vec P.generators) (b : Vec Q.generators) :
    map P Q A h (quotientClass P x) = quotientClass Q b ↔
      ∃ u : Vec Q.relations, equationMatrix P Q A *ᵥ join x u = b := by
  rw [map_class,class_eq_iff]
  constructor <;> rintro ⟨u,hu⟩ <;> refine ⟨u,?_⟩
  · rw [equationMatrix_mulVec,first_join,second_join,hu]
    abel
  · rw [equationMatrix_mulVec,first_join,second_join] at hu
    exact (eq_sub_iff_add_eq).mpr (by rw [add_comm, ← sub_eq_iff_eq_add.mp hu])


/-- 全商元の逆像存在は同じ拡大整数系の可解性と同値。 -/
theorem fiber_nonempty_iff (P Q : Presentation) (A : Mat Q.generators P.generators)
    (h : MapValid P Q A) (b : Vec Q.generators) :
    (∃ x : Group P, map P Q A h x = quotientClass Q b) ↔
      ∃ v, equationMatrix P Q A *ᵥ v = b := by
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨a,rfl⟩ := class_surjective P x
    obtain ⟨u,hu⟩ := (map_class_eq_iff P Q A h a b).mp hx
    exact ⟨join a u,hu⟩
  · rintro ⟨v,hv⟩
    refine ⟨quotientClass P (first v), (map_class_eq_iff P Q A h _ _).mpr ⟨second v,?_⟩⟩
    simpa only [join_parts] using hv
/-- 原始表示から特解の代表または元整数系の矛盾行を返す。 -/
def solvePresented (P Q : Presentation) (A : Mat Q.generators P.generators)
    (b : Vec Q.generators) : Sum (Vec P.generators) (Fin Q.generators) :=
  (solve (equationMatrix P Q A) b).map first id
/-- 返却した代表は同じ商射の厳密な指定逆像。 -/
theorem solvePresented_solution (P Q : Presentation) (A : Mat Q.generators P.generators)
    (h : MapValid P Q A) (b : Vec Q.generators) (x : Vec P.generators)
    (hx : solvePresented P Q A b = .inl x) :
    map P Q A h (quotientClass P x) = quotientClass Q b := by
  unfold solvePresented at hx
  cases hs : solve (equationMatrix P Q A) b with
  | inl v =>
    simp only [hs,Sum.map_inl,Sum.inl.injEq] at hx
    subst x
    apply (map_class_eq_iff P Q A h _ _).mpr
    exact ⟨second v, by simpa only [join_parts] using solve_solution _ b v hs⟩
  | inr i => simp [hs] at hx
/-- 返却した矛盾行は元拡大系の不整除を示す。 -/
theorem solvePresented_failure (P Q : Presentation) (A : Mat Q.generators P.generators)
    (b : Vec Q.generators) (i : Fin Q.generators) (hi : solvePresented P Q A b = .inr i) :
    solve (equationMatrix P Q A) b = .inr i := by
  unfold solvePresented at hi
  cases hs : solve (equationMatrix P Q A) b with
  | inl v => simp [hs] at hi
  | inr j => simpa only [hs,Sum.map_inr,Sum.inr.injEq,id_eq] using hi
/-- 矛盾行が返れば同じ商群の指定逆像は存在しない。 -/
theorem solvePresented_no_solution (P Q : Presentation) (A : Mat Q.generators P.generators)
    (h : MapValid P Q A) (b : Vec Q.generators) (i : Fin Q.generators)
    (hi : solvePresented P Q A b = .inr i) :
    ¬ ∃ x : Group P, map P Q A h x = quotientClass Q b := by
  rw [fiber_nonempty_iff]
  exact solve_no_solution _ b i (solvePresented_failure P Q A b i hi)
/-- 商上の全逆像について判定の完全性を保持する。 -/
theorem solvePresented_complete (P Q : Presentation) (A : Mat Q.generators P.generators)
    (h : MapValid P Q A) (b : Vec Q.generators) :
    (∃ x, solvePresented P Q A b = .inl x) ↔
      ∃ x : Group P, map P Q A h x = quotientClass Q b := by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨quotientClass P x,solvePresented_solution P Q A h b x hx⟩
  · intro he
    cases hs : solvePresented P Q A b with
    | inl x => exact ⟨x,rfl⟩
    | inr i => exact (solvePresented_no_solution P Q A h b i hs he).elim
/-- 行列の前半の行を抜き出す。 -/
def topRows {n r k : ℕ} (M : Mat (n+r) k) : Mat n k := fun i j => M (Fin.castAdd r i) j
/-- 前半の行の行列積は自由座標の前半と一致する。 -/
theorem topRows_mulVec {n r k : ℕ} (M : Mat (n+r) k) (v : Vec k) :
    topRows M *ᵥ v = first (M *ᵥ v) := rfl
/-- 拡大系の整数核を元生成元へ射影した計算可能な生成行列。 -/
def generatorMatrix (P Q : Presentation) (A : Mat Q.generators P.generators) :
    Mat P.generators (P.generators+Q.relations) :=
  topRows (kernelMatrix (produce (equationMatrix P Q A)))
/-- 生成行列は元商射のkernelに値を持つ。 -/
theorem generatorMatrix_killed (P Q : Presentation) (A : Mat Q.generators P.generators)
    (h : MapValid P Q A) (t : Vec (P.generators+Q.relations)) :
    map P Q A h (quotientClass P (generatorMatrix P Q A *ᵥ t)) = 0 := by
  have hk : equationMatrix P Q A *ᵥ (kernelMatrix (produce (equationMatrix P Q A)) *ᵥ t) = 0 := by
    rw [mulVec_mulVec,kernelMatrix_killed _ (produce_valid _),zero_mulVec]
  change map P Q A h (quotientClass P (first (kernelMatrix (produce (equationMatrix P Q A)) *ᵥ t))) = 0
  rw [← map_zero (quotientClass Q)]
  apply (map_class_eq_iff P Q A h _ _).mpr
  exact ⟨second (kernelMatrix (produce (equationMatrix P Q A)) *ᵥ t), by simpa only [join_parts] using hk⟩
/-- 原始生成行列は元商射の全kernelを尽くす。 -/
theorem generatorMatrix_surjective (P Q : Presentation) (A : Mat Q.generators P.generators)
    (h : MapValid P Q A) (x : Group P) (hx : map P Q A h x = 0) :
    ∃ t, quotientClass P (generatorMatrix P Q A *ᵥ t) = x := by
  obtain ⟨a,rfl⟩ := class_surjective P x
  have ha : map P Q A h (quotientClass P a) = quotientClass Q 0 := by simpa using hx
  obtain ⟨u,hu⟩ := (map_class_eq_iff P Q A h a 0).mp ha
  refine ⟨join a u,?_⟩
  change quotientClass P (first (kernelMatrix (produce (equationMatrix P Q A)) *ᵥ join a u)) = _
  rw [kernelMatrix_fixed _ (produce_valid _) _ hu,first_join]
/-- 自由座標から元商射の実kernelへの線形パラメータ。 -/
def kernelParam (P Q : Presentation) (A : Mat Q.generators P.generators) (h : MapValid P Q A) :
    Vec (P.generators+Q.relations) →ₗ[ℤ] LinearMap.ker (map P Q A h) :=
  ((quotientClass P).comp (Matrix.toLin' (generatorMatrix P Q A))).codRestrict _
    (generatorMatrix_killed P Q A h)
/-- 実kernelへのパラメータは同じ元商の代表を送る。 -/
@[simp] theorem kernelParam_val (P Q : Presentation) (A : Mat Q.generators P.generators)
    (h : MapValid P Q A) (t : Vec (P.generators+Q.relations)) :
    (kernelParam P Q A h t).val = quotientClass P (generatorMatrix P Q A *ᵥ t) := rfl
/-- 実kernelへのパラメータは全射。 -/
theorem kernelParam_surjective (P Q : Presentation) (A : Mat Q.generators P.generators)
    (h : MapValid P Q A) : Function.Surjective (kernelParam P Q A h) := by
  intro x
  obtain ⟨t,ht⟩ := generatorMatrix_surjective P Q A h x.val x.property
  exact ⟨t,Subtype.ext ht⟩


/-- 自由パラメータの同じ商元を与える全関係を整数系から生成する。 -/
def relationMatrix (P : Presentation) {k : ℕ} (G : Mat P.generators k) : Mat k (k+P.relations) :=
  topRows (kernelMatrix (produce (beside G (-P.matrix))))
/-- 計算した関係行列の像は、元商へのパラメータのkernelと厳密に一致する。 -/
theorem relationMatrix_range (P : Presentation) {k : ℕ} (G : Mat P.generators k) (t : Vec k) :
    (∃ v, relationMatrix P G *ᵥ v = t) ↔ quotientClass P (G *ᵥ t) = 0 := by
  constructor
  · rintro ⟨v,rfl⟩
    let M := beside G (-P.matrix)
    let w := kernelMatrix (produce M) *ᵥ v
    have hw : M *ᵥ w = 0 := by
      dsimp [w]
      rw [mulVec_mulVec,kernelMatrix_killed _ (produce_valid _),zero_mulVec]
    have he : G *ᵥ first w - P.matrix *ᵥ second w = 0 := by
      simpa only [M,beside_mulVec,neg_mulVec,← sub_eq_add_neg] using hw
    apply (class_zero_iff P _).mpr
    exact ⟨second w,(sub_eq_zero.mp he).symm⟩
  · intro ht
    obtain ⟨u,hu⟩ := (class_zero_iff P _).mp ht
    have hw : beside G (-P.matrix) *ᵥ join t u = 0 := by
      rw [beside_mulVec,first_join,second_join,neg_mulVec,hu,add_neg_cancel]
    refine ⟨join t u,?_⟩
    change first (kernelMatrix (produce (beside G (-P.matrix))) *ᵥ join t u) = t
    rw [kernelMatrix_fixed _ (produce_valid _) _ hw,first_join]
/-- 計算した実kernelの生成元と関係を一つの原始表示として返す。 -/
def kernelPresentation (P Q : Presentation) (A : Mat Q.generators P.generators) : Presentation :=
  ⟨P.generators+Q.relations,(P.generators+Q.relations)+P.relations,
    relationMatrix P (generatorMatrix P Q A)⟩
/-- 元商射のkernelパラメータの全関係は生成した関係像。 -/
theorem kernelParam_ker (P Q : Presentation) (A : Mat Q.generators P.generators)
    (h : MapValid P Q A) :
    LinearMap.ker (kernelParam P Q A h) = relationSpace (kernelPresentation P Q A) := by
  ext t
  change kernelParam P Q A h t = 0 ↔ ∃ v, relationMatrix P (generatorMatrix P Q A) *ᵥ v = t
  rw [relationMatrix_range]
  constructor
  · intro ht
    exact congrArg Subtype.val ht
  · intro ht
    exact Subtype.ext ht
/-- 原始入力から生成した有限表示と元商射の実kernelの同型。 -/
noncomputable def kernelEquiv (P Q : Presentation) (A : Mat Q.generators P.generators)
    (h : MapValid P Q A) : Group (kernelPresentation P Q A) ≃ₗ[ℤ] LinearMap.ker (map P Q A h) :=
  (Submodule.quotEquivOfEq _ _ (kernelParam_ker P Q A h).symm).trans
    ((kernelParam P Q A h).quotKerEquivOfSurjective (kernelParam_surjective P Q A h))
/-- 生成表示の代表の復元値は元C⁰の同じ商元。 -/
theorem kernelEquiv_class (P Q : Presentation) (A : Mat Q.generators P.generators)
    (h : MapValid P Q A) (t : Vec (P.generators+Q.relations)) :
    (kernelEquiv P Q A h (quotientClass (kernelPresentation P Q A) t)).val =
      quotientClass P (generatorMatrix P Q A *ᵥ t) := rfl
/-- 特解と計算した実商kernelが同じ全商解を尽くす。 -/
theorem all_solutions (P Q : Presentation) (A : Mat Q.generators P.generators)
    (h : MapValid P Q A) (b : Vec Q.generators) (a : Group P)
    (ha : map P Q A h a = quotientClass Q b) (x : Group P) :
    map P Q A h x = quotientClass Q b ↔
      ∃ t, x = a + quotientClass P (generatorMatrix P Q A *ᵥ t) := by
  constructor
  · intro hx
    have hk : map P Q A h (x-a) = 0 := by rw [map_sub,hx,ha,sub_self]
    obtain ⟨t,ht⟩ := generatorMatrix_surjective P Q A h (x-a) hk
    exact ⟨t,by rw [ht]; abel⟩
  · rintro ⟨t,rfl⟩
    rw [map_add,ha,generatorMatrix_killed,add_zero]
/-- 実kernel零性を全生成列の元関係membershipで有限検査する。 -/
def kernelZero (P Q : Presentation) (A : Mat Q.generators P.generators) : Bool :=
  decide (∀ j, Divisible (produce P.matrix) ((generatorMatrix P Q A).col j))
/-- 生成列零性の検査は実商kernel全体の零性に一致する。 -/
theorem kernelZero_correct (P Q : Presentation) (A : Mat Q.generators P.generators)
    (h : MapValid P Q A) : kernelZero P Q A = true ↔ ∀ x, map P Q A h x = 0 → x = 0 := by
  rw [kernelZero,decide_eq_true_eq]
  constructor
  · intro hj x hx
    obtain ⟨t,rfl⟩ := generatorMatrix_surjective P Q A h x hx
    have hc : ∀ j, quotientClass P ((generatorMatrix P Q A).col j) = 0 := by
      intro j
      exact (class_zero_iff P _).mpr ((divisible_iff_solution _ (produce_valid _) _).mp (hj j))
    have he : generatorMatrix P Q A *ᵥ t = ∑ j, t j • (generatorMatrix P Q A).col j := by
      ext i
      simp [mulVec,dotProduct,mul_comm]
    rw [he,map_sum]
    simp only [map_smul,hc,smul_zero,Finset.sum_const_zero]
  · intro hz j
    apply (divisible_iff_solution _ (produce_valid _) _).mpr
    apply (class_zero_iff P _).mp
    have hk := generatorMatrix_killed P Q A h (Pi.single j 1)
    rw [mulVec_single_one] at hk
    exact hz _ hk


/-- 元商群における指定逆像全体。 -/
abbrev Fiber (P Q : Presentation) (A : Mat Q.generators P.generators)
    (h : MapValid P Q A) (b : Vec Q.generators) :=
  {x : Group P // map P Q A h x = quotientClass Q b}
/-- 特解を固定すると、生成した有限表示から元の全商解への両方向同値が得られる。 -/
noncomputable def fiberEquiv (P Q : Presentation) (A : Mat Q.generators P.generators)
    (h : MapValid P Q A) (b : Vec Q.generators) (a : Fiber P Q A h b) :
    Group (kernelPresentation P Q A) ≃ Fiber P Q A h b where
  toFun t := ⟨a.val + (kernelEquiv P Q A h t).val, by
    rw [map_add,a.property,(kernelEquiv P Q A h t).property,add_zero]⟩
  invFun x := (kernelEquiv P Q A h).symm ⟨x.val-a.val, by
    change map P Q A h (x.val-a.val) = 0
    rw [map_sub,x.property,a.property,sub_self]⟩
  left_inv t := by
    apply (kernelEquiv P Q A h).injective
    rw [LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    dsimp only
    abel
  right_inv x := by
    apply Subtype.ext
    simp only [LinearEquiv.apply_symm_apply]
    abel
/-- 全解同値の代表評価は同じ商群上の加法作用。 -/
theorem fiberEquiv_class (P Q : Presentation) (A : Mat Q.generators P.generators)
    (h : MapValid P Q A) (b : Vec Q.generators) (a : Fiber P Q A h b)
    (t : Vec (P.generators+Q.relations)) :
    (fiberEquiv P Q A h b a (quotientClass (kernelPresentation P Q A) t)).val =
      a.val + quotientClass P (generatorMatrix P Q A *ᵥ t) := rfl
/-- 商上の一意解は可解性と実商kernel零性に一致する。 -/
theorem unique_fiber_iff (P Q : Presentation) (A : Mat Q.generators P.generators)
    (h : MapValid P Q A) (b : Vec Q.generators) :
    (∃! x : Group P, map P Q A h x = quotientClass Q b) ↔
      Divisible (produce (equationMatrix P Q A)) b ∧ kernelZero P Q A = true := by
  rw [divisible_iff_solution _ (produce_valid _),← fiber_nonempty_iff P Q A h,
    kernelZero_correct P Q A h]
  constructor
  · rintro ⟨a,ha,hu⟩
    refine ⟨⟨a,ha⟩,?_⟩
    intro x hx
    have he : map P Q A h (a+x) = quotientClass Q b := by rw [map_add,ha,hx,add_zero]
    have hu' := hu (a+x) he
    exact add_left_cancel (by simpa only [add_zero] using hu' : a+x = a+0)
  · rintro ⟨⟨a,ha⟩,hk⟩
    refine ⟨a,ha,?_⟩
    intro x hx
    have he : map P Q A h (x-a) = 0 := by rw [map_sub,hx,ha,sub_self]
    exact sub_eq_zero.mp (hk _ he)
/-- 原始表示から、補助変数を除いた元商解の一意性を判定する。 -/
def uniquePresented (P Q : Presentation) (A : Mat Q.generators P.generators)
    (b : Vec Q.generators) : Bool :=
  decide (Divisible (produce (equationMatrix P Q A)) b) && kernelZero P Q A
/-- 有限一意性判定は同じ商群上の存在一意性に一致する。 -/
theorem uniquePresented_correct (P Q : Presentation) (A : Mat Q.generators P.generators)
    (h : MapValid P Q A) (b : Vec Q.generators) :
    uniquePresented P Q A b = true ↔ ∃! x : Group P, map P Q A h x = quotientClass Q b := by
  rw [uniquePresented,Bool.and_eq_true,decide_eq_true_eq,unique_fiber_iff]
/-- 不成立時の証拠は拡大系の零行矛盾または非零整数の不整除。 -/
theorem solvePresented_failure_kind (P Q : Presentation) (A : Mat Q.generators P.generators)
    (b : Vec Q.generators) (i : Fin Q.generators) (hi : solvePresented P Q A b = .inr i) :
    ((produce (equationMatrix P Q A)).diagonal i = 0 ∧
      transformed (produce (equationMatrix P Q A)) b i ≠ 0) ∨
    ((produce (equationMatrix P Q A)).diagonal i ≠ 0 ∧
      ¬ (produce (equationMatrix P Q A)).diagonal i ∣ transformed (produce (equationMatrix P Q A)) b i) :=
  solve_failure_kind _ b i (solvePresented_failure P Q A b i hi)
/-- 関係保存の有限検査は商射条件の必要性も満たす。 -/
theorem mapValid_iff (P Q : Presentation) (A : Mat Q.generators P.generators) :
    MapValid P Q A ↔ relationSpace P ≤ LinearMap.ker ((quotientClass Q).comp (Matrix.toLin' A)) := by
  constructor
  · exact relation_preserved P Q A
  · intro h j
    apply (divisible_iff_solution _ (produce_valid _) _).mpr
    apply (class_zero_iff Q _).mp
    have hj : P.matrix.col j ∈ relationSpace P := ⟨Pi.single j 1,by exact Matrix.mulVec_single_one P.matrix j⟩
    have he := h hj
    change quotientClass Q (A *ᵥ P.matrix.col j) = 0 at he
    rw [← mulVec_single_one P.matrix j,mulVec_mulVec,mulVec_single_one] at he
    exact he

/-- 同じ終域商元の代表変更は可解性判定を変えない。 -/
theorem solvePresented_rep_independent (P Q : Presentation) (A : Mat Q.generators P.generators)
    (h : MapValid P Q A) (b b' : Vec Q.generators) (hb : quotientClass Q b = quotientClass Q b') :
    (∃ x, solvePresented P Q A b = .inl x) ↔ (∃ x, solvePresented P Q A b' = .inl x) := by
  rw [solvePresented_complete P Q A h,solvePresented_complete P Q A h,hb]
/-- 同じ終域商元の代表変更は元商解の一意性を変えない。 -/
theorem uniquePresented_rep_independent (P Q : Presentation) (A : Mat Q.generators P.generators)
    (h : MapValid P Q A) (b b' : Vec Q.generators) (hb : quotientClass Q b = quotientClass Q b') :
    uniquePresented P Q A b = uniquePresented P Q A b' := by
  apply Bool.eq_iff_iff.mpr
  rw [uniquePresented_correct P Q A h,uniquePresented_correct P Q A h,hb]

-- 原始有限表示での実行。指定Wの全要件をこれだけで満たしたとはしない。
#eval let P : Presentation := ⟨1,1,!![4]⟩
      let Q : Presentation := ⟨1,1,!![2]⟩
      decide (MapValid P Q !![1])
#eval let P : Presentation := ⟨1,1,!![2]⟩
      let Q : Presentation := ⟨1,1,!![4]⟩
      decide (¬ MapValid P Q !![1])
#eval let P : Presentation := ⟨1,1,!![4]⟩
      isZero P ![4] && !(isZero P ![1])
#eval let P : Presentation := ⟨1,1,!![4]⟩
      match solvePresented P P !![2] ![1] with
      | .inl _ => false
      | .inr _ => true
#eval let P : Presentation := ⟨1,1,!![4]⟩
      match solvePresented P P !![2] ![2] with
      | .inl x => (2*x 0) % 4 == 2
      | .inr _ => false
#eval let P : Presentation := ⟨1,1,!![4]⟩
      !(uniquePresented P P !![2] ![2])
#eval let P : Presentation := ⟨1,1,!![4]⟩
      uniquePresented P P !![1] ![2]
#eval let P : Presentation := ⟨0,0,0⟩
      uniquePresented P P 0 0
#eval let P : Presentation := ⟨1,0,0⟩
      let Q : Presentation := ⟨1,1,!![4]⟩
      !(uniquePresented P Q !![0] ![0])

end AAT.AG.SpecifiedRepairLifting.PresentedGroups

#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.join
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.first
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.second
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.first_join
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.second_join
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.join_parts
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.beside
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.beside_mulVec
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.firstMap
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.Presentation
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.relationSpace
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.Group
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.quotientClass
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.class_surjective
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.class_zero_iff
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.class_eq_iff
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.isZero
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.isZero_correct
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.MapValid
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.mapValidDecidable
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.relation_preserved
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.map
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.map_class
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.equationMatrix
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.equationMatrix_mulVec
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.map_class_eq_iff
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.fiber_nonempty_iff
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.solvePresented
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.solvePresented_solution
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.solvePresented_failure
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.solvePresented_no_solution
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.solvePresented_complete
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.topRows
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.topRows_mulVec
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.generatorMatrix
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.generatorMatrix_killed
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.generatorMatrix_surjective
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.kernelParam
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.kernelParam_val
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.kernelParam_surjective
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.relationMatrix
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.relationMatrix_range
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.kernelPresentation
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.kernelParam_ker
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.kernelEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.kernelEquiv_class
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.all_solutions
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.kernelZero
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.kernelZero_correct
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.Fiber
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.fiberEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.fiberEquiv_class
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.unique_fiber_iff
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.uniquePresented
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.uniquePresented_correct
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.solvePresented_failure_kind
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.mapValid_iff
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.solvePresented_rep_independent
#print axioms AAT.AG.SpecifiedRepairLifting.PresentedGroups.uniquePresented_rep_independent
#assert_standard_axioms_only AAT.AG.SpecifiedRepairLifting.PresentedGroups
