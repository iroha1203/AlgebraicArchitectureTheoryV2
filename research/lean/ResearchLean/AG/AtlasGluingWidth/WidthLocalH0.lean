import ResearchLean.AG.AtlasGluingWidth.WidthIntersection

/-! # 指定閉路の局所pathの実H⁰

GOAL E / witnesses §4。fine A/B は元辺の零微分から全chart値が一定と証明する。
H¹零から連結性を推論しない。

## Implementation notes

Aの二辺とBの自然数代表のpathを直接たどる。抽象的な成分数を入力として
H⁰同型を選ぶ案は、原始表からの連結性の放電を隠すため採らない。
-/
noncomputable section
namespace AAT.AG.AtlasGluingWidth.Width
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
variable (n : ℕ) [NeZero n]

/-- 指定領域の元chartを選択chartへ入れる。 -/
def localChart (X : Set (Concept n)) (v : Chart n)
    (hv : v.1 ∈ X ∨ (v.2 = true ∧ v.1 + 1 ∈ X)) : (selected n false X).Chart :=
  ⟨v, (chart_selected n false X v).mpr hv⟩
/-- 指定領域の元辺を選択辺へ入れる。 -/
def localEdge (X : Set (Concept n)) (e : Concept n × Bool)
    (he : (if e.2 then e.1 + 1 else e.1) ∈ X) : (selected n false X).Edge :=
  ⟨⟨e, by simp⟩, (edge_selected n false X _).mpr he⟩
/-- 零微分核の値は各実選択辺の両端で等しい。 -/
theorem local_zero_edge (X : Set (Concept n))
    (z : LinearMap.ker (selected n false X).complex.d0) (e : (selected n false X).Edge) :
    z.1 ((selected n false X).right e) = z.1 ((selected n false X).left e) := by
  have he := congrFun z.2 e
  rw [CellSelection.complex_d0_apply] at he
  exact sub_eq_zero.mp he
/-- Aの実chart v₀を根とする。 -/
def aRoot : (selected n false (regionA n)).Chart :=
  localChart n (regionA n) (0, false) (Or.inl rfl)
/-- Aで選択されるa₀。 -/
def aEdge : (selected n false (regionA n)).Edge :=
  localEdge n (regionA n) (0, false) rfl
/-- Aで選択されるb₋₁。 -/
def aBackEdge : (selected n false (regionA n)).Edge :=
  localEdge n (regionA n) (-1, true) (by simp [regionA])
/-- Aの二つの実辺は全選択chartの核値をv₀へ接続する。 -/
theorem a_zero_constant (z : LinearMap.ker (selected n false (regionA n)).complex.d0)
    (v : (selected n false (regionA n)).Chart) : z.1 v = z.1 (aRoot n) := by
  have ha := local_zero_edge n (regionA n) z (aEdge n)
  have hb := local_zero_edge n (regionA n) z (aBackEdge n)
  have hv := (chart_selected n false (regionA n) v.1).mp v.2
  rcases v with ⟨⟨i,b⟩, hp⟩
  cases b
  · have hi : i = 0 := by simpa [regionA] using hv
    subst i
    rfl
  · rcases hv with hi | ⟨_,hi⟩
    · have hi' : i = 0 := hi
      subst i
      exact ha
    · have hi' : i = -1 := add_eq_zero_iff_eq_neg.mp hi
      subst i
      simpa [aBackEdge, aRoot, localEdge, localChart, CellSelection.right,
        CellSelection.left, right, left] using hb.symm
omit [NeZero n] in
/-- n≥2なら全wᵢがBに選ばれる。 -/
theorem b_w_selected (hn : 2 ≤ n) (i : Concept n) :
    i ∈ regionB n ∨ (true = true ∧ i + 1 ∈ regionB n) := by
  by_cases hi : i = 0
  · subst i
    exact Or.inr ⟨rfl, by simpa [regionB,regionA] using one_ne_zero n hn⟩
  · exact Or.inl hi
/-- Bの全wᵢを同じ原chart名で選択する。 -/
def bW (hn : 2 ≤ n) (i : Concept n) : (selected n false (regionB n)).Chart :=
  localChart n (regionB n) (i,true) (b_w_selected n hn i)
/-- Bのi≠0のvᵢ。 -/
def bV (i : Concept n) (hi : i ≠ 0) : (selected n false (regionB n)).Chart :=
  localChart n (regionB n) (i,false) (Or.inl hi)
/-- Bのi≠0のaᵢ。 -/
def bAEdge (i : Concept n) (hi : i ≠ 0) : (selected n false (regionB n)).Edge :=
  localEdge n (regionB n) (i,false) hi
/-- Bのi+1≠0のbᵢ。 -/
def bBEdge (i : Concept n) (hi : i+1 ≠ 0) : (selected n false (regionB n)).Edge :=
  localEdge n (regionB n) (i,true) hi
/-- Bのa辺はvᵢとwᵢの核値を同じにする。 -/
theorem b_a_value (hn : 2 ≤ n) (z : LinearMap.ker (selected n false (regionB n)).complex.d0)
    (i : Concept n) (hi : i ≠ 0) : z.1 (bV n i hi) = z.1 (bW n hn i) :=
  (local_zero_edge n (regionB n) z (bAEdge n i hi)).symm
/-- Bのb辺はwᵢとvᵢ₊₁の核値を同じにする。 -/
theorem b_b_value (hn : 2 ≤ n) (z : LinearMap.ker (selected n false (regionB n)).complex.d0)
    (i : Concept n) (hi : i+1 ≠ 0) : z.1 (bV n (i+1) hi) = z.1 (bW n hn i) :=
  local_zero_edge n (regionB n) z (bBEdge n i hi)
omit [NeZero n] in
/-- n未満の正の代表は概念0ではない。 -/
theorem positive_cast_ne_zero (r : ℕ) (hr : 0 < r) (hn : r < n) : (r : Concept n) ≠ 0 := by
  intro h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt hn, ZMod.val_zero] at hv
  omega
/-- Bの自然数代表pathをたどって全w値をw₀へ接続する。 -/
theorem b_w_constant (hn : 2 ≤ n) (z : LinearMap.ker (selected n false (regionB n)).complex.d0)
    (i : Concept n) : z.1 (bW n hn i) = z.1 (bW n hn 0) := by
  have hi (r : ℕ) (hr : r < n) : z.1 (bW n hn (r : Concept n)) = z.1 (bW n hn 0) := by
    induction r with
    | zero => simp
    | succ r ih =>
      have hs : (r : Concept n)+1 ≠ 0 := by
        rw [← Nat.cast_one, ← Nat.cast_add]
        exact positive_cast_ne_zero n (r+1) (by omega) hr
      rw [Nat.cast_add, Nat.cast_one]
      exact (b_a_value n hn z _ hs).symm.trans ((b_b_value n hn z _ hs).trans (ih (by omega)))
  simpa only [ZMod.natCast_zmod_val] using hi i.val (ZMod.val_lt i)
/-- 原始Bの全選択chartは同じ核値を持つ。 -/
theorem b_zero_constant (hn : 2 ≤ n)
    (z : LinearMap.ker (selected n false (regionB n)).complex.d0)
    (v : (selected n false (regionB n)).Chart) : z.1 v = z.1 (bW n hn 0) := by
  have hv := (chart_selected n false (regionB n) v.1).mp v.2
  rcases v with ⟨⟨i,b⟩,hp⟩
  cases b
  · have hi : i ≠ 0 := by simpa [regionB,regionA] using hv
    exact (b_a_value n hn z i hi).trans (b_w_constant n hn z i)
  · exact b_w_constant n hn z i

/-- 実零微分核の全値が根へ接続するとき、根評価は定数関数と両方向同型。 -/
def constantKernelEquiv {T : Type} {q : Reading T} {D : TargetSupportedNerve q}
    (S : CellSelection D) (root : S.Chart)
    (hc : ∀ z : LinearMap.ker S.complex.d0, ∀ v, z.1 v = z.1 root) :
    LinearMap.ker S.complex.d0 ≃ₗ[ℚ] ℚ where
  toFun z := z.1 root
  invFun a := ⟨fun _ => a, by funext e; simp only [CellSelection.complex_d0_apply, sub_self]; rfl⟩
  left_inv z := by apply Subtype.ext; funext v; exact (hc z v).symm
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- 同じ根評価の公開式。 -/
@[simp] theorem constantKernelEquiv_apply {T : Type} {q : Reading T}
    {D : TargetSupportedNerve q} (S : CellSelection D) (root : S.Chart)
    (hc : ∀ z : LinearMap.ker S.complex.d0, ∀ v, z.1 v = z.1 root)
    (z : LinearMap.ker S.complex.d0) : constantKernelEquiv S root hc z = z.1 root := rfl
/-- 同じ逆同型は全chartで指定定数を返す。 -/
@[simp] theorem constantKernelEquiv_symm_apply {T : Type} {q : Reading T}
    {D : TargetSupportedNerve q} (S : CellSelection D) (root : S.Chart)
    (hc : ∀ z : LinearMap.ker S.complex.d0, ∀ v, z.1 v = z.1 root) (a : ℚ) (v : S.Chart) :
    ((constantKernelEquiv S root hc).symm a).1 v = a := rfl
/-- 原始AのH⁰核は根v₀の値でℚに同定される。 -/
def aH0Equiv : LinearMap.ker (selected n false (regionA n)).complex.d0 ≃ₗ[ℚ] ℚ :=
  constantKernelEquiv _ (aRoot n) (a_zero_constant n)
/-- 原始BのH⁰核は根w₀の値でℚに同定される。 -/
def bH0Equiv (hn : 2 ≤ n) : LinearMap.ker (selected n false (regionB n)).complex.d0 ≃ₗ[ℚ] ℚ :=
  constantKernelEquiv _ (bW n hn 0) (b_zero_constant n hn)
/-- 全閉路の選択H⁰核は元閉路の零微分を持つ。 -/
theorem full_zero_constant (z : LinearMap.ker (selected n false Set.univ).complex.d0)
    (v : (selected n false Set.univ).Chart) : z.1 v = z.1 (fullChart n (0,false)) := by
  let x : Chart n → ℚ := fun v => z.1 (fullChart n v)
  have hx : difference n x = 0 := by
    funext e
    exact congrFun z.2 (fullEdge n e)
  exact difference_zero_constant n x hx v.1
/-- 全閉路の実H⁰核は指定v₀評価でℚと両方向同型。 -/
def fullH0Equiv : LinearMap.ker (selected n false Set.univ).complex.d0 ≃ₗ[ℚ] ℚ :=
  constantKernelEquiv _ (fullChart n (0,false)) (full_zero_constant n)
/-- 同じ非空粗領域は唯一の元chartを選ぶ。 -/
def coarseRoot (X : Set (Concept n)) (hx : X.Nonempty) : (CellSelection.region (coarse n) X).Chart :=
  ⟨(), by obtain ⟨i,hi⟩ := hx; exact ⟨i, Set.mem_univ _, hi⟩⟩
/-- 元粗chartがUnitなので粗領域H⁰は根評価でℚと両方向同型。 -/
def coarseH0Equiv (X : Set (Concept n)) (hx : X.Nonempty) :
    LinearMap.ker (CellSelection.region (coarse n) X).complex.d0 ≃ₗ[ℚ] ℚ :=
  constantKernelEquiv _ (coarseRoot n X hx) (fun z _ => congrArg z.1 (Subsingleton.elim _ _))
omit [NeZero n] in
/-- n≥2でBは実際に1を含む。 -/
theorem regionB_nonempty (hn : 2 ≤ n) : (regionB n).Nonempty :=
  ⟨1, one_ne_zero n hn⟩
/-- 真の粗交差は同じ一つの元chartを両方の証拠点で選ぶ。 -/
def coarseIntersectionRoot (hn : 2 ≤ n) :
    ((CellSelection.region (coarse n) (regionA n)).inter
      (CellSelection.region (coarse n) (regionB n))).Chart :=
  ⟨(), (coarseRoot n (regionA n) ⟨0,rfl⟩).2,
    (coarseRoot n (regionB n) (regionB_nonempty n hn)).2⟩
/-- 真の粗交差H⁰核は同じ一chart評価でℚと両方向同型。 -/
def coarseIntersectionH0Equiv (hn : 2 ≤ n) :
    LinearMap.ker ((CellSelection.region (coarse n) (regionA n)).inter
      (CellSelection.region (coarse n) (regionB n))).complex.d0 ≃ₗ[ℚ] ℚ :=
  constantKernelEquiv _ (coarseIntersectionRoot n hn) (fun z _ => congrArg z.1 (Subsingleton.elim _ _))

end AAT.AG.AtlasGluingWidth.Width
#assert_standard_axioms_only AAT.AG.AtlasGluingWidth.Width
