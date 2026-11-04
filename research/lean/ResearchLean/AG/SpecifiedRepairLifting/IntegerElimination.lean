import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Logic.Encodable.Pi
import Mathlib.LinearAlgebra.Isomorphisms
import Formal.Util.AssertStandardAxioms

/-! # 原始整数行列の像の対角表示

Implementation notes: 整数像の基底を周囲の自由群の基底に対角に置く。
全解は像基底への座標とその原像から得られる kernel 射影で復元する。
有理消去では整数の整除障害を失うため用いない。
producer は直接対角候補、有限燃料のEuclid型候補、符号化された有限整数表の
構成的探索の順に進む。各候補は原始入力に対する Valid の有限検査を通す。
最後の探索の停止は全整数行列の像のSmith基底の存在から証明する。
この存在証明は実行時入力ではなく消去される停止根拠であり、
外部からSmith形や変換行列を受け取らない。有限燃料の候補単体には
完全性を主張しない。単なる証明付き外部certificate検査では原始入力からの
生成を満たさないため、この全域producerを採用した。
商の同型だけは非計算的で、solve・unique・生成行列は計算可能である。
このファイル内の変換検査補題は producer の正当性を支える補助APIである。
-/
namespace AAT.AG.SpecifiedRepairLifting.IntegerElimination
open Matrix

/-- 固定有限個の整数生成元の座標。 -/
abbrev Vec (n : ℕ) := Fin n → ℤ
/-- 原始整数行列。零行・零列も許す。 -/
abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℤ
/-- 行列の全成分を有限関数として符号化する。 -/
instance matrixEncodable (m n : ℕ) : Encodable (Mat m n) :=
  inferInstanceAs (Encodable (Fin m → Fin n → ℤ))
/-- 像の対角座標と、その元の生成元からの復元データ。 -/
structure Data (m n : ℕ) where
  left : Mat m m
  right : Mat m m
  diagonal : Vec m
  lift : Mat n m
  coordinates : Mat m n
/-- 変換データは有限整数表の直積と計算的に同値。 -/
def dataEquiv (m n : ℕ) : Data m n ≃ (Mat m m × Mat m m × Vec m × Mat n m × Mat m n) where
  toFun c := ⟨c.left,c.right,c.diagonal,c.lift,c.coordinates⟩
  invFun t := ⟨t.1,t.2.1,t.2.2.1,t.2.2.2.1,t.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
/-- 有限整数表の計算可能な符号化。 -/
instance dataEncodable (m n : ℕ) : Encodable (Data m n) :=
  Encodable.ofEquiv _ (dataEquiv m n)
/-- 全ての条件は原始行列との有限整数等式で検査する。 -/
def Valid {m n : ℕ} (A : Mat m n) (c : Data m n) : Prop :=
  c.left * c.right = 1 ∧ c.right * c.left = 1 ∧
  c.left * A = Matrix.diagonal c.diagonal * c.coordinates ∧
  A * c.lift = c.right * Matrix.diagonal c.diagonal ∧
  ∀ i, c.diagonal i = 0 → ∀ j, c.coordinates i j = 0
/-- 検査は有限行列の決定可能等号だけで実行される。 -/
instance validDecidable {m n : ℕ} (A : Mat m n) (c : Data m n) : Decidable (Valid A c) := by
  unfold Valid
  infer_instance

variable {m n : ℕ} {A : Mat m n} (c : Data m n)
/-- 元の右辺を同じ整数同型の座標へ送る。 -/
def transformed (b : Vec m) : Vec m := c.left *ᵥ b
/-- 対角系の可解性を有限個の整数整除として表す。 -/
def Divisible (b : Vec m) : Prop := ∀ i, c.diagonal i ∣ transformed c b i
/-- 整除判定も整数の有限検査。 -/
instance divisibleDecidable (b : Vec m) : Decidable (Divisible c b) := by
  unfold Divisible
  infer_instance
/-- 整除成立時に用いる実整数の特解候補。 -/
def particular (b : Vec m) : Vec n := c.lift *ᵥ (fun i => transformed c b i / c.diagonal i)
/-- 任意の解は同じ対角整除条件を満たす。 -/
theorem solution_divisible (h : Valid A c) (x : Vec n) (b : Vec m) (hx : A *ᵥ x = b) :
    Divisible c b := by
  intro i
  have he : c.left *ᵥ b = Matrix.diagonal c.diagonal *ᵥ (c.coordinates *ᵥ x) := by
    rw [← hx, mulVec_mulVec, h.2.2.1, ← mulVec_mulVec]
  unfold transformed
  rw [he]
  simp only [mulVec_diagonal]
  exact dvd_mul_right _ _
/-- 有限整除条件から原始行列の特解を復元する。 -/
theorem particular_correct (h : Valid A c) (b : Vec m) (hb : Divisible c b) :
    A *ᵥ particular c b = b := by
  have hd : Matrix.diagonal c.diagonal *ᵥ (fun i => transformed c b i / c.diagonal i) =
      transformed c b := by
    ext i
    simp only [mulVec_diagonal]
    exact Int.mul_ediv_cancel' (hb i)
  unfold particular
  rw [mulVec_mulVec, h.2.2.2.1, ← mulVec_mulVec, hd]
  unfold transformed
  rw [mulVec_mulVec, h.2.1, one_mulVec]
/-- 全原始右辺について整除判定と実整数解の存在が同値。 -/
theorem divisible_iff_solution (h : Valid A c) (b : Vec m) :
    Divisible c b ↔ ∃ x : Vec n, A *ᵥ x = b :=
  ⟨fun hb => ⟨particular c b, particular_correct c h b hb⟩,
    fun ⟨x,hx⟩ => solution_divisible c h x b hx⟩
/-- 対角整除の失敗は元の整数解の不存在を証明する。 -/
theorem no_solution_of_not_dvd (h : Valid A c) (b : Vec m) (i : Fin m)
    (hi : ¬ c.diagonal i ∣ transformed c b i) : ¬ ∃ x : Vec n, A *ᵥ x = b := by
  rintro ⟨x,hx⟩
  exact hi (solution_divisible c h x b hx i)
/-- 実整数 kernel へ戻す計算可能な射影行列。 -/
def kernelMatrix : Mat n n := 1 - c.lift * c.coordinates
/-- kernel 射影の像は原始行列で零になる。 -/
theorem kernelMatrix_killed (h : Valid A c) : A * kernelMatrix c = 0 := by
  unfold kernelMatrix
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h.2.2.2.1, Matrix.mul_assoc,
    ← h.2.2.1, ← Matrix.mul_assoc, h.2.1, Matrix.one_mul, sub_self]
/-- 任意の元kernelベクトルは同じ射影でそのまま復元される。 -/
theorem kernelMatrix_fixed (h : Valid A c) (x : Vec n) (hx : A *ᵥ x = 0) :
    kernelMatrix c *ᵥ x = x := by
  have hv : c.coordinates *ᵥ x = 0 := by
    have hd : Matrix.diagonal c.diagonal *ᵥ (c.coordinates *ᵥ x) = 0 := by
      rw [mulVec_mulVec, ← h.2.2.1, ← mulVec_mulVec, hx, mulVec_zero]
    ext i
    by_cases hi : c.diagonal i = 0
    · simp only [mulVec, dotProduct]
      simp [h.2.2.2.2 i hi]
    · have he := congrFun hd i
      simp only [mulVec_diagonal, Pi.zero_apply] at he
      exact (mul_eq_zero.mp he).resolve_left hi
  unfold kernelMatrix
  rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, hv, mulVec_zero, sub_zero]
/-- kernel 射影の値は元ベクトルから像座標の復元を引いたもの。 -/
theorem kernelMatrix_apply (x : Vec n) : kernelMatrix c *ᵥ x = x - (c.lift * c.coordinates) *ᵥ x := by
  rw [kernelMatrix, sub_mulVec, one_mulVec]
/-- 任意の自由パラメータを原始行列の実kernelへ送る。 -/
def kernelParam (h : Valid A c) : Vec n →ₗ[ℤ] LinearMap.ker (Matrix.toLin' A) :=
  (Matrix.toLin' (kernelMatrix c)).codRestrict _ (by
    intro x
    change A *ᵥ (kernelMatrix c *ᵥ x) = 0
    rw [mulVec_mulVec, kernelMatrix_killed c h, zero_mulVec])
/-- kernel パラメータの値は同じ計算可能な射影の値。 -/
@[simp] theorem kernelParam_val (h : Valid A c) (x : Vec n) :
    (kernelParam c h x).val = kernelMatrix c *ᵥ x := rfl
/-- 全ての原始kernel元を自由パラメータから復元する。 -/
theorem kernelParam_surjective (h : Valid A c) : Function.Surjective (kernelParam c h) := by
  intro x
  exact ⟨x.val, Subtype.ext (kernelMatrix_fixed c h x.val x.property)⟩
/-- 同じkernel元を表すパラメータの差は有限関係行列の像。 -/
theorem kernelParam_ker (h : Valid A c) :
    LinearMap.ker (kernelParam c h) = LinearMap.range (Matrix.toLin' (c.lift * c.coordinates)) := by
  ext x
  constructor
  · intro hx
    have hz : kernelMatrix c *ᵥ x = 0 := congrArg Subtype.val hx
    rw [kernelMatrix_apply, sub_eq_zero] at hz
    exact ⟨x,hz.symm⟩
  · rintro ⟨t,rfl⟩
    apply Subtype.ext
    change kernelMatrix c *ᵥ ((c.lift * c.coordinates) *ᵥ t) = 0
    have ht : (c.lift * c.coordinates) *ᵥ t = t - kernelMatrix c *ᵥ t := by
      rw [kernelMatrix_apply]
      abel
    rw [ht, mulVec_sub]
    have hk : A *ᵥ (kernelMatrix c *ᵥ t) = 0 := by
      rw [mulVec_mulVec, kernelMatrix_killed c h, zero_mulVec]
    rw [kernelMatrix_fixed c h _ hk, sub_self]
/-- 実kernelは計算した有限生成元・関係の商と同型。 -/
noncomputable def kernelPresentationEquiv (h : Valid A c) :
    (Vec n ⧸ LinearMap.range (Matrix.toLin' (c.lift * c.coordinates))) ≃ₗ[ℤ]
      LinearMap.ker (Matrix.toLin' A) :=
  (Submodule.quotEquivOfEq _ _ (kernelParam_ker c h).symm).trans
    ((kernelParam c h).quotKerEquivOfSurjective (kernelParam_surjective c h))
/-- 有限kernel表示の代表は同じ元ベクトルへ復元される。 -/
theorem kernelPresentationEquiv_mk (h : Valid A c) (x : Vec n) :
    (kernelPresentationEquiv c h (Submodule.Quotient.mk x)).val = kernelMatrix c *ᵥ x := rfl
/-- 特解と実kernelの加法が元の全整数解を尽くす。 -/
theorem all_solutions (h : Valid A c) (b : Vec m) (hb : Divisible c b) (x : Vec n) :
    A *ᵥ x = b ↔ ∃ t : Vec n, x = particular c b + kernelMatrix c *ᵥ t := by
  constructor
  · intro hx
    refine ⟨x - particular c b, ?_⟩
    have hk : A *ᵥ (x - particular c b) = 0 := by
      rw [mulVec_sub, hx, particular_correct c h b hb, sub_self]
    rw [kernelMatrix_fixed c h _ hk]
    abel
  · rintro ⟨t,rfl⟩
    rw [mulVec_add, particular_correct c h b hb, mulVec_mulVec,
      kernelMatrix_killed c h, zero_mulVec, add_zero]
/-- 全原始整数行列に有限検査を満たす変換データが存在する。
像のSmith基底は停止証明のためだけに使い、実行部への入力にはしない。 -/
theorem exists_valid (A : Mat m n) : ∃ c : Data m n, Valid A c := by
  classical
  let F := Matrix.toLin' A
  obtain ⟨r,s⟩ := F.range.smithNormalForm (Pi.basisFun ℤ (Fin m))
  choose t ht using (fun k : Fin r => (s.bN k).property)
  let U : Mat m m := LinearMap.toMatrix' s.bM.equivFun.toLinearMap
  let Ui : Mat m m := LinearMap.toMatrix' s.bM.equivFun.symm.toLinearMap
  let d : Vec m := Function.extend s.f s.a 0
  let B : Mat n m := fun j i => Function.extend s.f t 0 i j
  let col (j : Fin n) : F.range := ⟨A.col j, by
    exact ⟨Pi.single j 1, Matrix.mulVec_single_one A j⟩⟩
  let V : Mat m n := fun i j => Function.extend s.f (fun k => s.bN.repr (col j) k) 0 i
  refine ⟨⟨U,Ui,d,B,V⟩, ?_, ?_, ?_, ?_, ?_⟩
  · change U * Ui = 1
    have hi : s.bM.equivFun.toLinearMap.comp s.bM.equivFun.symm.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact s.bM.equivFun.apply_symm_apply x
    dsimp [U,Ui]
    rw [← LinearMap.toMatrix'_comp, hi, LinearMap.toMatrix'_id]
  · change Ui * U = 1
    have hi : s.bM.equivFun.symm.toLinearMap.comp s.bM.equivFun.toLinearMap = LinearMap.id := by
      apply LinearMap.ext
      intro x
      exact s.bM.equivFun.symm_apply_apply x
    dsimp [U,Ui]
    rw [← LinearMap.toMatrix'_comp, hi, LinearMap.toMatrix'_id]
  · change U * A = Matrix.diagonal d * V
    ext i j
    rw [Matrix.diagonal_mul]
    change (U *ᵥ A.col j) i = d i * V i j
    rw [LinearMap.toMatrix'_mulVec]
    by_cases hi : ∃ k, s.f k = i
    · obtain ⟨k,rfl⟩ := hi
      dsimp [d,V]
      rw [s.f.injective.extend_apply, s.f.injective.extend_apply]
      exact congrFun (s.repr_comp_embedding_eq_smul (col j)) k
    · dsimp [d,V]
      rw [Function.extend_apply' _ _ _ hi, Pi.zero_apply, zero_mul]
      exact s.repr_eq_zero_of_notMem_range (col j) hi
  · change A * B = Ui * Matrix.diagonal d
    ext i j
    rw [Matrix.mul_diagonal]
    change (A *ᵥ (fun k => B k j)) i = Ui i j * d j
    by_cases hj : ∃ k, s.f k = j
    · obtain ⟨k,rfl⟩ := hj
      have hb : s.bM.equivFun.symm (Pi.single (s.f k) 1) = s.bM (s.f k) := by
        apply s.bM.equivFun.injective
        ext i
        simp [Module.Basis.equivFun_self, Pi.single_apply, eq_comm]
      change (A *ᵥ (Function.extend s.f t 0 (s.f k))) i = Ui i (s.f k) * d (s.f k)
      rw [s.f.injective.extend_apply]
      have hk : A *ᵥ t k = (s.bN k).val := ht k
      rw [hk, s.snf]
      dsimp [Ui,d]
      rw [s.f.injective.extend_apply]
      change (s.a k • s.bM (s.f k)) i = (s.bM.equivFun.symm (Pi.single (s.f k) 1)) i * s.a k
      rw [hb]
      exact mul_comm _ _
    · change (A *ᵥ Function.extend s.f t 0 j) i = Ui i j * Function.extend s.f s.a 0 j
      rw [Function.extend_apply' _ _ _ hj, Function.extend_apply' _ _ _ hj,
        Pi.zero_apply, Pi.zero_apply, mulVec_zero, mul_zero]
      rfl
  · change ∀ i, d i = 0 → ∀ j, V i j = 0
    intro i hi j
    by_cases he : ∃ k, s.f k = i
    · obtain ⟨k,rfl⟩ := he
      have ha : s.a k ≠ 0 := by
        intro hk
        have hs := s.snf k
        rw [hk, zero_smul] at hs
        exact s.bN.ne_zero k (Subtype.ext hs)
      exact (ha (by simpa only [d, s.f.injective.extend_apply] using hi)).elim
    · exact Function.extend_apply' _ _ _ he

/-- 対角入力と零次元入力に対する直接計算候補。使用前に同じ有限検査を行う。 -/
def diagonalCandidate (A : Mat m n) : Data m n :=
  let d : Vec m := fun i => if h : i.val < n then A i ⟨i.val,h⟩ else 0
  ⟨1,1,d,(fun j i => if j.val = i.val ∧ d i ≠ 0 then 1 else 0),
    (fun i j => if i.val = j.val ∧ d i ≠ 0 then 1 else 0)⟩
/-- 有限燃料の整数消去候補の状態。正しさは最後のValid検査で判定する。 -/
structure State (m n : ℕ) where
  work : Mat m n
  left : Mat m m
  right : Mat m m
  domain : Mat n n
  domainInv : Mat n n
/-- 原始行列と恒等変換から候補生成を始める。 -/
def initialState (A : Mat m n) : State m n := ⟨A,1,1,1,1⟩
/-- 二行交換と記録した逆変換の二列交換。 -/
def swapRows (s : State m n) (i j : Fin m) : State m n :=
  let σ := Equiv.swap i j
  {s with work := fun a b => s.work (σ a) b
          left := fun a b => s.left (σ a) b
          right := fun a b => s.right a (σ b)}
/-- 二列交換と記録した逆変換の二行交換。 -/
def swapCols (s : State m n) (i j : Fin n) : State m n :=
  let σ := Equiv.swap i j
  {s with work := fun a b => s.work a (σ b)
          domain := fun a b => s.domain a (σ b)
          domainInv := fun a b => s.domainInv (σ a) b}
/-- 整数倍の行減算と逆変換の列加算。 -/
def reduceRow (s : State m n) (i j : Fin m) (q : ℤ) : State m n :=
  {s with work := fun a b => if a = i then s.work a b - q * s.work j b else s.work a b
          left := fun a b => if a = i then s.left a b - q * s.left j b else s.left a b
          right := fun a b => if b = j then s.right a b + q * s.right a i else s.right a b}
/-- 整数倍の列減算と逆変換の行加算。 -/
def reduceCol (s : State m n) (i j : Fin n) (q : ℤ) : State m n :=
  {s with work := fun a b => if b = i then s.work a b - q * s.work a j else s.work a b
          domain := fun a b => if b = i then s.domain a b - q * s.domain a j else s.domain a b
          domainInv := fun a b => if a = j then s.domainInv a b + q * s.domainInv i b else s.domainInv a b}
/-- 有限燃料でEuclid型の行列候補を生成する。燃料不足でも全探索へ進める。 -/
def diagonalize : ℕ → ℕ → State m n → State m n
  | 0, _, s => s
  | fuel+1, k, s =>
    if hm : k < m then
      if hn : k < n then
        let i : Fin m := ⟨k,hm⟩
        let j : Fin n := ⟨k,hn⟩
        if s.work i j = 0 then
          match ((List.finRange m).flatMap fun a => (List.finRange n).map fun b => (a,b)).find?
              (fun p => decide (k ≤ p.1.val ∧ k ≤ p.2.val ∧ s.work p.1 p.2 ≠ 0)) with
          | none => s
          | some (a,b) => diagonalize fuel k (swapCols (swapRows s i a) j b)
        else
          match (List.finRange m).find? (fun a => decide (k < a.val ∧ s.work a j ≠ 0)) with
          | some a =>
            let t := reduceRow s a i (s.work a j / s.work i j)
            diagonalize fuel k (if t.work a j = 0 then t else swapRows t i a)
          | none =>
            match (List.finRange n).find? (fun b => decide (k < b.val ∧ s.work i b ≠ 0)) with
            | some b =>
              let t := reduceCol s b j (s.work i b / s.work i j)
              diagonalize fuel k (if t.work i b = 0 then t else swapCols t j b)
            | none => diagonalize fuel (k+1) s
      else s
    else s
/-- 消去候補から像の対角座標と復元表を計算する。 -/
def stateCandidate (s : State m n) : Data m n :=
  let d : Vec m := fun i => if h : i.val < n then s.work i ⟨i.val,h⟩ else 0
  ⟨s.left,s.right,d,
    (fun j i => if h : i.val < n then if d i = 0 then 0 else s.domain j ⟨i.val,h⟩ else 0),
    (fun i j => if h : i.val < n then if d i = 0 then 0 else s.domainInv ⟨i.val,h⟩ j else 0)⟩
/-- 原始行列から有限手数で作る一般整数消去候補。 -/
def euclideanCandidate (A : Mat m n) : Data m n :=
  stateCandidate (diagonalize (10000 * (m+n+1)) 0 (initialState A))
/-- 原始行列から有限整数表を構成的に探索する停止producer。
直接候補が検査に通らない場合も、全入力で停止する構成的探索へ進む。 -/
def produce (A : Mat m n) : Data m n :=
  let c := diagonalCandidate A
  if Valid A c then c else
    let e := euclideanCandidate A
    if Valid A e then e else Encodable.choose (exists_valid A)
/-- producerが返した全変換条件は入力行列から生成される。 -/
theorem produce_valid (A : Mat m n) : Valid A (produce A) := by
  unfold produce
  dsimp only
  split
  · assumption
  · split
    · assumption
    · exact Encodable.choose_spec (exists_valid A)

/-- 整除失敗時は有限個の行の少なくとも一つが失敗する。 -/
theorem failingRows_nonempty (b : Vec m) (h : ¬ Divisible c b) :
    (Finset.univ.filter (fun i => ¬ c.diagonal i ∣ transformed c b i)).Nonempty := by
  classical
  by_contra hn
  apply h
  intro i
  by_contra hi
  exact hn ⟨i, by simp [hi]⟩
/-- 不整除の行を有限検査だけで選ぶ。 -/
def failureRow (b : Vec m) (h : ¬ Divisible c b) : Fin m :=
  (Finset.univ.filter (fun i => ¬ c.diagonal i ∣ transformed c b i)).min'
    (failingRows_nonempty c b h)
/-- 計算した行には実際に整数整除違反がある。 -/
theorem failureRow_spec (b : Vec m) (h : ¬ Divisible c b) :
    ¬ c.diagonal (failureRow c b h) ∣ transformed c b (failureRow c b h) := by
  exact (Finset.mem_filter.mp (Finset.min'_mem _ (failingRows_nonempty c b h))).2
/-- 原始行列と右辺から、特解または矛盾行を生成する。 -/
def solve (A : Mat m n) (b : Vec m) : Sum (Vec n) (Fin m) :=
  let c := produce A
  if h : Divisible c b then .inl (particular c b) else .inr (failureRow c b h)
/-- 出力が特解なら元の整数方程式を厳密に満たす。 -/
theorem solve_solution (A : Mat m n) (b : Vec m) (x : Vec n) (hx : solve A b = .inl x) :
    A *ᵥ x = b := by
  unfold solve at hx
  dsimp only at hx
  split at hx
  · cases hx
    exact particular_correct _ (produce_valid A) b (by assumption)
  · contradiction
/-- 出力が矛盾行なら生成した対角系の整除違反が検査できる。 -/
theorem solve_failure (A : Mat m n) (b : Vec m) (i : Fin m) (hi : solve A b = .inr i) :
    ¬ (produce A).diagonal i ∣ transformed (produce A) b i := by
  unfold solve at hi
  dsimp only at hi
  split at hi
  · contradiction
  · cases hi
    exact failureRow_spec _ _ _
/-- 矛盾行は元の全整数解の不存在を証明する。 -/
theorem solve_no_solution (A : Mat m n) (b : Vec m) (i : Fin m) (hi : solve A b = .inr i) :
    ¬ ∃ x : Vec n, A *ᵥ x = b :=
  no_solution_of_not_dvd _ (produce_valid A) b i (solve_failure A b i hi)
/-- 矛盾行を零行矛盾と非零整数の不整除へ区別する。 -/
theorem solve_failure_kind (A : Mat m n) (b : Vec m) (i : Fin m) (hi : solve A b = .inr i) :
    ((produce A).diagonal i = 0 ∧ transformed (produce A) b i ≠ 0) ∨
    ((produce A).diagonal i ≠ 0 ∧ ¬ (produce A).diagonal i ∣ transformed (produce A) b i) := by
  have hn := solve_failure A b i hi
  by_cases hd : (produce A).diagonal i = 0
  · refine Or.inl ⟨hd, ?_⟩
    intro hz
    exact hn (hz ▸ dvd_zero _)
  · exact Or.inr ⟨hd,hn⟩
/-- 全入力についてsolverの成功と元整数解の存在が同値。 -/
theorem solve_complete (A : Mat m n) (b : Vec m) :
    (∃ x : Vec n, solve A b = .inl x) ↔ ∃ x : Vec n, A *ᵥ x = b := by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨x,solve_solution A b x hx⟩
  · intro he
    cases hs : solve A b with
    | inl x => exact ⟨x,rfl⟩
    | inr i => exact (solve_no_solution A b i hs he).elim
/-- 原始入力から生成した関係行列による実kernelの有限表示。 -/
noncomputable def producedKernelEquiv (A : Mat m n) :
    (Vec n ⧸ LinearMap.range (Matrix.toLin' ((produce A).lift * (produce A).coordinates))) ≃ₗ[ℤ]
      LinearMap.ker (Matrix.toLin' A) :=
  kernelPresentationEquiv (produce A) (produce_valid A)
/-- 生成したkernel表示の全代表が同じ元ベクトルへ復元される。 -/
theorem producedKernelEquiv_mk (A : Mat m n) (t : Vec n) :
    (producedKernelEquiv A (Submodule.Quotient.mk t)).val = kernelMatrix (produce A) *ᵥ t :=
  kernelPresentationEquiv_mk _ _ t
/-- solverが返した特解と生成kernelから元の全整数解を復元する。 -/
theorem solve_all_solutions (A : Mat m n) (b : Vec m) (x : Vec n)
    (hx : solve A b = .inl x) (y : Vec n) :
    A *ᵥ y = b ↔ ∃ t : Vec n, y = x + kernelMatrix (produce A) *ᵥ t := by
  have hAx := solve_solution A b x hx
  constructor
  · intro hy
    refine ⟨y-x, ?_⟩
    have hk : A *ᵥ (y-x) = 0 := by rw [mulVec_sub,hy,hAx,sub_self]
    rw [kernelMatrix_fixed _ (produce_valid A) _ hk]
    abel
  · rintro ⟨t,rfl⟩
    rw [mulVec_add,hAx,mulVec_mulVec,kernelMatrix_killed _ (produce_valid A),zero_mulVec,add_zero]
/-- 実整数解の一意性は可解性と生成kernel行列の零性で有限判定できる。 -/
theorem unique_solution_iff (A : Mat m n) (b : Vec m) :
    (∃! x : Vec n, A *ᵥ x = b) ↔ Divisible (produce A) b ∧ kernelMatrix (produce A) = 0 := by
  constructor
  · rintro ⟨x,hx,hu⟩
    refine ⟨solution_divisible _ (produce_valid A) x b hx, ?_⟩
    ext i j
    have hk : A *ᵥ (kernelMatrix (produce A) *ᵥ Pi.single j 1) = 0 := by
      rw [mulVec_mulVec,kernelMatrix_killed _ (produce_valid A),zero_mulVec]
    have hy : A *ᵥ (x + kernelMatrix (produce A) *ᵥ Pi.single j 1) = b := by
      rw [mulVec_add,hx,hk,add_zero]
    have hz : kernelMatrix (produce A) *ᵥ Pi.single j 1 = 0 := by
      apply add_left_cancel (a := x)
      simpa only [add_zero] using hu _ hy
    simpa only [mulVec_single_one, Matrix.col_apply, Pi.zero_apply] using congrFun hz i
  · rintro ⟨hb,hk⟩
    refine ⟨particular (produce A) b, particular_correct _ (produce_valid A) b hb, ?_⟩
    intro y hy
    obtain ⟨t,ht⟩ := (all_solutions _ (produce_valid A) b hb y).mp hy
    simpa only [hk,zero_mulVec,add_zero] using ht
/-- 元整数解の一意性の実行可能な判定。 -/
def unique (A : Mat m n) (b : Vec m) : Bool :=
  decide (Divisible (produce A) b ∧ kernelMatrix (produce A) = 0)
/-- 一意性判定は元の全解に対する存在一意性と一致する。 -/
theorem unique_correct (A : Mat m n) (b : Vec m) :
    unique A b = true ↔ ∃! x : Vec n, A *ᵥ x = b := by
  rw [unique, decide_eq_true_eq, unique_solution_iff]

/-- 全零の変換表は一次元で逆行列条件を満たさない。 -/
theorem zero_data_not_valid : ¬ Valid (0 : Mat 1 1) (⟨0,0,0,0,0⟩ : Data 1 1) := by
  decide

-- Primitive-input executions; these are not the required W2–W5 evaluations.
#eval decide (Valid (0 : Mat 0 0) (produce 0))
#eval match solve (fun _ _ => (2 : ℤ) : Mat 1 1) (fun _ => 4) with
  | .inl x => x 0 == 2
  | .inr _ => false
#eval match solve (fun _ _ => (2 : ℤ) : Mat 1 1) (fun _ => 1) with
  | .inl _ => false
  | .inr i => i.val == 0
#eval decide (Valid (!![2, 3; 4, 6] : Mat 2 2) (produce !![2, 3; 4, 6]))
#eval match solve (!![2, 3; 4, 6] : Mat 2 2) ![1, 2] with
  | .inl x => decide ((!![2, 3; 4, 6] : Mat 2 2) *ᵥ x = ![1, 2])
  | .inr _ => false
#eval match solve (!![2, 3; 4, 6] : Mat 2 2) ![1, 3] with
  | .inl _ => false
  | .inr _ => true
#eval decide (Valid (0 : Mat 0 2) (produce 0))
#eval decide (Valid (0 : Mat 2 0) (produce 0))
#eval unique (fun _ _ => (-2 : ℤ) : Mat 1 1) (fun _ => 4)
#eval !(unique (!![2, 3; 4, 6] : Mat 2 2) ![1, 2])
end AAT.AG.SpecifiedRepairLifting.IntegerElimination

#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.Vec
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.Mat
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.matrixEncodable
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.Data
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.dataEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.dataEncodable
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.Valid
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.validDecidable
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.transformed
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.Divisible
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.divisibleDecidable
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.particular
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.solution_divisible
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.particular_correct
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.divisible_iff_solution
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.no_solution_of_not_dvd
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.kernelMatrix
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.kernelMatrix_killed
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.kernelMatrix_fixed
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.kernelMatrix_apply
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.kernelParam
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.kernelParam_val
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.kernelParam_surjective
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.kernelParam_ker
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.kernelPresentationEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.kernelPresentationEquiv_mk
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.all_solutions
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.exists_valid
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.diagonalCandidate
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.State
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.initialState
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.swapRows
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.swapCols
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.reduceRow
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.reduceCol
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.diagonalize
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.stateCandidate
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.euclideanCandidate
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.produce
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.produce_valid
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.failingRows_nonempty
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.failureRow
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.failureRow_spec
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.solve
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.solve_solution
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.solve_failure
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.solve_no_solution
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.solve_failure_kind
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.solve_complete
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.producedKernelEquiv
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.producedKernelEquiv_mk
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.solve_all_solutions
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.unique_solution_iff
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.unique
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.unique_correct
#print axioms AAT.AG.SpecifiedRepairLifting.IntegerElimination.zero_data_not_valid
#assert_standard_axioms_only AAT.AG.SpecifiedRepairLifting.IntegerElimination
