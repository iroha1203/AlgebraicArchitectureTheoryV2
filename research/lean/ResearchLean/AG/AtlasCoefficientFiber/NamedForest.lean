import ResearchLean.AG.AtlasCoefficientFiber.RawBlocks
import Mathlib.Combinatorics.Graph.Basic

/-!
# G-135 B §1：名前付き無向多重forestのincidence単射性

finite forestのleaf特徴付けを、すべての非空有限辺部分集合に課す。
辺名を保持するため、loop一辺と平行二辺はこの条件を満たさない。
線形微分の核やrankをforestの定義へ置かない。

## Implementation notes

使用版mathlibのGraphにはBasicのみがあり、forest述語のAPIがないため、
無向多重forestの有限部分グラフleaf特徴付けを使用しnative GraphのIncへ同定する。
端点集合への辺の同一視は平行辺を失うため、辺型Eを保持する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open scoped Classical
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {E V : Type u} (s t : E → V)

/-- 同じ名前付き辺・二端点を持つmathlibの無向多重グラフ。 -/
def namedUndirectedGraph : _root_.Graph V E where
  vertexSet := Set.univ
  edgeSet := Set.univ
  IsLink e x y := (x = s e ∧ y = t e) ∨ (x = t e ∧ y = s e)
  isLink_symm := by
    intro e _ x y h
    rcases h with h | h
    · exact Or.inr ⟨h.2, h.1⟩
    · exact Or.inl ⟨h.2, h.1⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro e x y v w h h'
    rcases h with h | h <;> rcases h' with h' | h'
    · exact Or.inl (h.1.trans h'.1.symm)
    · exact Or.inr (h.1.trans h'.2.symm)
    · exact Or.inr (h.1.trans h'.2.symm)
    · exact Or.inl (h.1.trans h'.1.symm)
  edge_mem_iff_exists_isLink e := ⟨fun _ => ⟨s e, t e, Or.inl ⟨rfl, rfl⟩⟩, fun _ => trivial⟩
  left_mem_of_isLink := fun {_ _ _} _ => trivial

/-- native多重グラフのincidenceは、同じ原二端点の所属である。 -/
theorem namedUndirectedGraph_inc (e : E) (v : V) :
    (namedUndirectedGraph s t).Inc e v ↔ v = s e ∨ v = t e := by
  constructor
  · rintro ⟨w, h | h⟩
    · exact Or.inl h.1
    · exact Or.inr h.1
  · rintro (h | h)
    · exact ⟨t e, Or.inl ⟨h, rfl⟩⟩
    · exact ⟨s e, Or.inr ⟨h, rfl⟩⟩

/-- 無向forestの有限辺部分集合leaf条件。loop・平行辺を消さずに全部分集合を検査する。 -/
def NamedForest : Prop := ∀ F : Finset E, F.Nonempty →
  ∃ (v : V) (e : E), e ∈ F ∧ s e ≠ t e ∧ (v = s e ∨ v = t e) ∧
    ∀ f ∈ F, (v = s f ∨ v = t f) → f = e

/-- forestのleaf条件はnative多重グラフの全incidenceを使う同じ条件。 -/
theorem namedForest_graph_iff : NamedForest s t ↔
    ∀ F : Finset E, F.Nonempty → ∃ (v : V) (e : E), e ∈ F ∧ s e ≠ t e ∧
      (namedUndirectedGraph s t).Inc e v ∧
      ∀ f ∈ F, (namedUndirectedGraph s t).Inc f v → f = e := by
  simp only [NamedForest, namedUndirectedGraph_inc]

/-- 原名前付き端点差分による有向incidence。 -/
def namedIncidence : (E →₀ ℚ) →ₗ[ℚ] (V →₀ ℚ) :=
  freeMap fun e => Finsupp.single (t e) 1 - Finsupp.single (s e) 1

/-- 有向incidenceは原辺ごとの終点−始点を線形延長する。 -/
@[simp] theorem namedIncidence_single (e : E) (r : ℚ) :
    namedIncidence s t (Finsupp.single e r) = r • (Finsupp.single (t e) 1 - Finsupp.single (s e) 1) :=
  freeMap_single _ _ _

/-- leafでは他の全非零辺の寄与が消え、同じ一辺の係数だけが残る。 -/
theorem namedIncidence_leaf_value (x : E →₀ ℚ) (v : V) (e : E) (he : e ∈ x.support)
    (hl : ∀ f ∈ x.support, (v = s f ∨ v = t f) → f = e) :
    namedIncidence s t x v = x e *
      ((if t e = v then (1 : ℚ) else 0) - (if s e = v then (1 : ℚ) else 0)) := by
  classical
  rw [namedIncidence, freeMap_apply]
  simp only [Finsupp.sum, Finsupp.finset_sum_apply, Finsupp.smul_apply, Finsupp.sub_apply,
    Finsupp.single_apply, smul_eq_mul]
  apply Finset.sum_eq_single e
  · intro f hf hfe
    have hs : s f ≠ v := fun hh => hfe (hl f hf (Or.inl hh.symm))
    have ht : t f ≠ v := fun hh => hfe (hl f hf (Or.inr hh.symm))
    simp only [if_neg hs, if_neg ht, sub_self, mul_zero]
  · intro hn
    exact False.elim (hn he)

/-- forestの原incidenceには非零閉辺chainがない。核零性を入力にはしない。 -/
theorem namedIncidence_eq_zero_iff (hF : NamedForest s t) (x : E →₀ ℚ) :
    namedIncidence s t x = 0 ↔ x = 0 := by
  classical
  constructor
  · intro hx
    by_contra hn
    obtain ⟨v, e, he, hst, hv, hl⟩ := hF x.support (Finsupp.support_nonempty_iff.mpr hn)
    have hz := congrArg (fun y : V →₀ ℚ => y v) hx
    change namedIncidence s t x v = 0 at hz
    rw [namedIncidence_leaf_value s t x v e he hl] at hz
    have he0 : x e ≠ 0 := Finsupp.mem_support_iff.mp he
    rcases hv with hv | hv
    · have ht : t e ≠ v := fun hh => hst (hv.symm.trans hh.symm)
      simp only [if_pos hv.symm, if_neg ht, zero_sub, mul_neg, mul_one, neg_eq_zero] at hz
      exact he0 hz
    · have hs : s e ≠ v := fun hh => hst (hh.trans hv)
      simp only [if_pos hv.symm, if_neg hs, sub_zero, mul_one] at hz
      exact he0 hz
  · rintro rfl
    exact map_zero _

/-- 同じforest原incidenceは単射。 -/
theorem namedIncidence_injective (hF : NamedForest s t) : Function.Injective (namedIncidence s t) := by
  intro x y hxy
  have hz : namedIncidence s t (x - y) = 0 := by rw [map_sub, hxy, sub_self]
  exact sub_eq_zero.mp ((namedIncidence_eq_zero_iff s t hF (x - y)).mp hz)

/-- loopが一辺でもあれば、辺名を保ったforest条件は成立しない。 -/
theorem namedForest_no_loop (hF : NamedForest s t) (e : E) : s e ≠ t e := by
  classical
  obtain ⟨v, f, hf, hn, _⟩ := hF {e} (Finset.singleton_nonempty e)
  simpa only [Finset.mem_singleton.mp hf] using hn

/-- 異名の平行二辺もforestのleaf条件に反する。 -/
theorem namedForest_no_parallel (hF : NamedForest s t) (e f : E)
    (he : s e = s f) (ht : t e = t f) : e = f := by
  classical
  obtain ⟨v, g, hg, _, hv, hl⟩ := hF {e, f} (by simp)
  have hve : v = s e ∨ v = t e := by
    rcases Finset.mem_insert.mp hg with h | h
    · simpa only [h] using hv
    · have hgf := Finset.mem_singleton.mp h
      simpa only [hgf, he, ht] using hv
  have hvf : v = s f ∨ v = t f := by simpa only [he, ht] using hve
  exact (hl e (by simp) hve).trans (hl f (by simp) hvf).symm

/-- 空の原辺集合ではforest条件が入力から成立する。 -/
theorem namedForest_of_isEmpty [IsEmpty E] : NamedForest s t := by
  intro F hF
  obtain ⟨e, _⟩ := hF
  exact isEmptyElim e

/-- 異なる両端点を持つ一辺だけの原グラフはforest。孤立頂点も許す。 -/
theorem namedForest_of_subsingleton [Subsingleton E] (hn : ∀ e, s e ≠ t e) : NamedForest s t := by
  intro F hF
  obtain ⟨e, he⟩ := hF
  exact ⟨s e, e, he, hn e, Or.inl rfl, fun f _ _ => Subsingleton.elim f e⟩

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.namedUndirectedGraph
#print axioms AAT.AG.AtlasCoefficientFiber.namedUndirectedGraph_inc
#print axioms AAT.AG.AtlasCoefficientFiber.NamedForest
#print axioms AAT.AG.AtlasCoefficientFiber.namedForest_graph_iff
#print axioms AAT.AG.AtlasCoefficientFiber.namedIncidence
#print axioms AAT.AG.AtlasCoefficientFiber.namedIncidence_single
#print axioms AAT.AG.AtlasCoefficientFiber.namedIncidence_leaf_value
#print axioms AAT.AG.AtlasCoefficientFiber.namedIncidence_eq_zero_iff
#print axioms AAT.AG.AtlasCoefficientFiber.namedIncidence_injective
#print axioms AAT.AG.AtlasCoefficientFiber.namedForest_no_loop
#print axioms AAT.AG.AtlasCoefficientFiber.namedForest_no_parallel
#print axioms AAT.AG.AtlasCoefficientFiber.namedForest_of_isEmpty
#print axioms AAT.AG.AtlasCoefficientFiber.namedForest_of_subsingleton
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
