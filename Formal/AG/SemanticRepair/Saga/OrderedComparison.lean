import Formal.AG.SemanticRepair.Saga.CechThreeTerm

/-!
# Part X Lemma 2.1A: increasing vs full ordered-tuple Čech comparison

For a sitewide abelian presheaf `F` on the AAT site, a monomorphic ordered
cover `𝒰`, and the empty-overlap normalization (`F` vanishes on omitted
intersections), this module proves the Part X Lemma 2.1A comparison between

* the increasing three-term complex `incComplex (F.onIntersections 𝒰)`
  (Definition 2.1), and
* the full ordered-tuple three-term spine `ordComplex F 𝒰`, whose degree-one
  and degree-two cochains run over all ordered index pairs / triples
  (the degree ≤ 2 spine of the Part IV model).

The comparison is proved, not supplied: restriction is a chain map on the
nose (`restrictCochain1_ordDelta0` / `restrictCochain2_ordDelta1` are `rfl`),
the inverse is the antisymmetric extension `extend1`, and the `Z¹`-level
injectivity / surjectivity use the thin-model diagonal isomorphisms that the
mathematical text derives from the monomorphism hypothesis.  The permutation
argument of the text (cocycle equations at permuted tuples are signed images
of the increasing equation) is `ordDelta1_eq_zero_of_normalForm`.  The `H¹`
equivalence and its zero-class transfer are `ordToIncH1` / `incToOrdH1` with
their inverse and zero-preservation theorems.  The matching-family clause of
Lemma 2.1A is `matchingFamily_iff`.

The connection to the Part IV declarations `CoverRelativeCechComplex` /
`CoverRelativeHn` lives in `Formal.AG.SemanticRepair.Saga.PartIVBridge`.
-/

noncomputable section

namespace AAT.AG
namespace SemanticRepair
namespace Saga

open CategoryTheory

universe u w x

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : Site.AATSite A}

namespace SitePresheafData

variable (F : SitePresheafData.{u, w} S)

/-- thin site: 平行な射に沿った restriction は一致する。 -/
theorem restrict_hom_congr {X Y : S.category} (h h' : X ⟶ Y)
    (v : F.carrier Y) : F.restrict h v = F.restrict h' v := by
  rw [Subsingleton.elim h h']

/-- thin site: 2段 restriction は経路に依存しない。 -/
theorem restrict_restrict {X Y Y' Z : S.category}
    (h₁ : X ⟶ Y) (h₂ : Y ⟶ Z) (h₁' : X ⟶ Y') (h₂' : Y' ⟶ Z)
    (v : F.carrier Z) :
    F.restrict h₁ (F.restrict h₂ v) = F.restrict h₁' (F.restrict h₂' v) := by
  rw [← F.restrict_comp h₁ h₂ v, ← F.restrict_comp h₁' h₂' v,
    Subsingleton.elim (h₁ ≫ h₂) (h₁' ≫ h₂')]

/-- thin site: 双方向の射を持つ対象への restriction は値零を反映する。 -/
theorem eq_zero_of_restrict_eq_zero {X Y : S.category}
    (down : X ⟶ Y) (up : Y ⟶ X) {v : F.carrier Y}
    (h : F.restrict down v = 0) : v = 0 := by
  have hv : F.restrict up (F.restrict down v) = v := by
    rw [← F.restrict_comp up down v, Subsingleton.elim (up ≫ down) (𝟙 Y),
      F.restrict_id]
  rw [h, map_zero] at hv
  exact hv.symm

end SitePresheafData

namespace MonomorphicOrderedCover

variable {S : Site.AATSite A} (𝒰 : MonomorphicOrderedCover S)

/-- 逆順 overlap から昇順 overlap への canonical 射(pullback lift)。 -/
def swapHom (i j : 𝒰.Index) : 𝒰.pairCtx j i ⟶ 𝒰.pairCtx i j :=
  𝒰.pairLift (𝒰.pairSnd j i) (𝒰.pairFst j i)

end MonomorphicOrderedCover

variable {𝒰 : MonomorphicOrderedCover S}
variable (F : SitePresheafData.{u, w} S)

/-- 全 ordered pair 上の次数1 cochain(第IV部 model の次数1成分)。 -/
abbrev OrdCochain1 (𝒰 : MonomorphicOrderedCover S) : Type (max u w) :=
  ∀ q : 𝒰.Index × 𝒰.Index, F.carrier (𝒰.pairCtx q.1 q.2)

/-- 全 ordered triple 上の次数2 cochain。 -/
abbrev OrdCochain2 (𝒰 : MonomorphicOrderedCover S) : Type (max u w) :=
  ∀ t : 𝒰.Index × 𝒰.Index × 𝒰.Index, F.carrier (𝒰.tripleCtx t.1 t.2.1 t.2.2)

/-- 全 ordered tuple 複体の `δ⁰`。 -/
def ordDelta0 : Cochain0 (F.onIntersections 𝒰) →+ OrdCochain1 F 𝒰 :=
  AddMonoidHom.mk'
    (fun a q =>
      F.restrict (𝒰.pairSnd q.1 q.2) (a q.2) -
        F.restrict (𝒰.pairFst q.1 q.2) (a q.1))
    (by
      intro a b
      funext q
      simp only [Pi.add_apply, map_add]
      abel)

/-- 全 ordered tuple 複体の `δ¹`。 -/
def ordDelta1 : OrdCochain1 F 𝒰 →+ OrdCochain2 F 𝒰 :=
  AddMonoidHom.mk'
    (fun c t =>
      F.restrict (𝒰.tripleFaceJK t.1 t.2.1 t.2.2) (c (t.2.1, t.2.2)) -
        F.restrict (𝒰.tripleFaceIK t.1 t.2.1 t.2.2) (c (t.1, t.2.2)) +
        F.restrict (𝒰.tripleFaceIJ t.1 t.2.1 t.2.2) (c (t.1, t.2.1)))
    (by
      intro c d
      funext t
      simp only [Pi.add_apply, map_add]
      abel)

theorem ordDelta1_ordDelta0 (a : Cochain0 (F.onIntersections 𝒰)) :
    ordDelta1 F (ordDelta0 F a) = 0 := by
  funext t
  obtain ⟨i, j, k⟩ := t
  have key : ∀ x y z x' y' z' : F.carrier (𝒰.tripleCtx i j k),
      x = x' -> y = y' -> z = z' -> x - y - (x' - z) + (y' - z') = 0 := by
    intro x y z x' y' z' hx hy hz
    subst hx
    subst hy
    subst hz
    abel
  simp only [ordDelta1, ordDelta0, AddMonoidHom.mk'_apply, map_sub,
    Pi.zero_apply]
  exact key _ _ _ _ _ _
    (F.restrict_restrict _ _ _ _ (a k))
    (F.restrict_restrict _ _ _ _ (a j))
    (F.restrict_restrict _ _ _ _ (a i))

/-- 第IV部 model の次数 ≤ 2 スパイン(全 ordered tuple 三項複体)。 -/
def ordComplex (𝒰 : MonomorphicOrderedCover S) :
    Cohomology.AdditiveThreeTermComplex
      (Cochain0 (F.onIntersections 𝒰)) (OrdCochain1 F 𝒰) (OrdCochain2 F 𝒰) where
  d0 := ordDelta0 F
  d1 := ordDelta1 F
  d_comp := ordDelta1_ordDelta0 F

/-! ## 増加添字への restriction は chain map(on the nose) -/

/-- 次数1の増加添字 restriction。 -/
def restrictCochain1 : OrdCochain1 F 𝒰 →+ Cochain1 (F.onIntersections 𝒰) :=
  AddMonoidHom.mk' (fun c p => c (p.fst, p.snd)) (fun _ _ => rfl)

/-- 次数2の増加添字 restriction。 -/
def restrictCochain2 : OrdCochain2 F 𝒰 →+ Cochain2 (F.onIntersections 𝒰) :=
  AddMonoidHom.mk' (fun c t => c (t.fst, t.snd, t.trd)) (fun _ _ => rfl)

/-- 補題2.1A(`B̃¹ ≅ B¹`、restriction 方向): 増加 restriction は tuple
coboundary を増加 coboundary へ on the nose で送る。拡張方向は
`extend1_delta0`。 -/
theorem restrictCochain1_ordDelta0 (a : Cochain0 (F.onIntersections 𝒰)) :
    restrictCochain1 F (ordDelta0 F a) = delta0 (F.onIntersections 𝒰) a :=
  rfl

theorem restrictCochain2_ordDelta1 (c : OrdCochain1 F 𝒰) :
    restrictCochain2 F (ordDelta1 F c) =
      delta1 (F.onIntersections 𝒰) (restrictCochain1 F c) :=
  rfl

/-! ## 省略 overlap の正規化の transported 形 -/

/-- 省略昇順 pair の逆順 overlap 上でも `F` は零である(swap transport)。 -/
theorem pair_rev_zero
    (hpair : ∀ i j, 𝒰.omittedPair i j ->
      ∀ v : F.carrier (𝒰.pairCtx i j), v = 0)
    {i j : 𝒰.Index} (hk : 𝒰.omittedPair j i)
    (v : F.carrier (𝒰.pairCtx i j)) : v = 0 := by
  have hv : F.restrict (𝒰.swapHom j i) (F.restrict (𝒰.swapHom i j) v) = v := by
    rw [← F.restrict_comp (𝒰.swapHom j i) (𝒰.swapHom i j) v,
      Subsingleton.elim (𝒰.swapHom j i ≫ 𝒰.swapHom i j) (𝟙 (𝒰.pairCtx i j)),
      F.restrict_id]
  rw [hpair j i hk (F.restrict (𝒰.swapHom i j) v), map_zero] at hv
  exact hv.symm

/-! ## 補題2.1A: 単射性(cocycle は増加成分で決まる) -/

/-- 対角成分の消滅: tuple cocycle の `(i,i)` 成分は零である
(数学本文の mono による diagonal 同型の thin model 読み)。 -/
theorem cocycle_diag_eq_zero {c : OrdCochain1 F 𝒰}
    (hc : ordDelta1 F c = 0) (i : 𝒰.Index) : c (i, i) = 0 := by
  have h := congrFun hc (i, i, i)
  simp only [ordDelta1, AddMonoidHom.mk'_apply, Pi.zero_apply] at h
  rw [F.restrict_hom_congr (𝒰.tripleFaceJK i i i) (𝒰.tripleFaceIJ i i i),
    F.restrict_hom_congr (𝒰.tripleFaceIK i i i) (𝒰.tripleFaceIJ i i i)] at h
  have h' : F.restrict (𝒰.tripleFaceIJ i i i) (c (i, i)) = 0 := by
    calc F.restrict (𝒰.tripleFaceIJ i i i) (c (i, i)) =
        F.restrict (𝒰.tripleFaceIJ i i i) (c (i, i)) -
          F.restrict (𝒰.tripleFaceIJ i i i) (c (i, i)) +
          F.restrict (𝒰.tripleFaceIJ i i i) (c (i, i)) := by abel
      _ = 0 := h
  exact F.eq_zero_of_restrict_eq_zero (𝒰.tripleFaceIJ i i i)
    (𝒰.tripleLift (𝒰.pairFst i i) (𝒰.pairSnd i i) (𝒰.pairSnd i i)) h'

/--
補題2.1A 単射部: 増加成分が零で `F` が省略 overlap 上零なら、
tuple cocycle は全成分零である。
-/
theorem cocycle_eq_zero_of_restrict_eq_zero
    (hpair : ∀ i j, 𝒰.omittedPair i j ->
      ∀ v : F.carrier (𝒰.pairCtx i j), v = 0)
    {c : OrdCochain1 F 𝒰} (hc : ordDelta1 F c = 0)
    (h0 : restrictCochain1 F c = 0) : c = 0 := by
  letI := 𝒰.indexOrder
  have hinc : ∀ i j, 𝒰.indexOrder.lt i j -> c (i, j) = 0 := by
    intro i j hij
    by_cases hk : 𝒰.omittedPair i j
    · exact hpair i j hk (c (i, j))
    · exact congrFun h0 ⟨i, j, hij, hk⟩
  funext q
  obtain ⟨i, j⟩ := q
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact hinc i j hij
  · exact cocycle_diag_eq_zero F hc i
  · have h := congrFun hc (j, i, j)
    simp only [ordDelta1, AddMonoidHom.mk'_apply, Pi.zero_apply] at h
    rw [cocycle_diag_eq_zero F hc j, map_zero, hinc j i hji, map_zero] at h
    have h' : F.restrict (𝒰.tripleFaceJK j i j) (c (i, j)) = 0 := by
      calc F.restrict (𝒰.tripleFaceJK j i j) (c (i, j)) =
          F.restrict (𝒰.tripleFaceJK j i j) (c (i, j)) - 0 + 0 := by abel
        _ = 0 := h
    exact F.eq_zero_of_restrict_eq_zero (𝒰.tripleFaceJK j i j)
      (𝒰.tripleLift (𝒰.pairSnd i j) (𝒰.pairFst i j) (𝒰.pairSnd i j)) h'

/-! ## 補題2.1A: 反対称拡張(全射部の構成) -/

open Classical in
/-- 増加添字 cochain の反対称拡張: 対角は零、逆順は符号つき transport、
省略昇順成分は零。 -/
def extend1 : Cochain1 (F.onIntersections 𝒰) →+ OrdCochain1 F 𝒰 :=
  AddMonoidHom.mk'
    (fun z q =>
      if hlt : 𝒰.indexOrder.lt q.1 q.2 then
        (if hk : 𝒰.omittedPair q.1 q.2 then 0 else z ⟨q.1, q.2, hlt, hk⟩)
      else if hgt : 𝒰.indexOrder.lt q.2 q.1 then
        (if hk : 𝒰.omittedPair q.2 q.1 then 0
         else - F.restrict (𝒰.swapHom q.2 q.1) (z ⟨q.2, q.1, hgt, hk⟩))
      else 0)
    (by
      intro z z'
      funext q
      by_cases hlt : 𝒰.indexOrder.lt q.1 q.2
      · by_cases hk : 𝒰.omittedPair q.1 q.2
        · simp [hlt, hk]
        · simp [hlt, hk]
      · by_cases hgt : 𝒰.indexOrder.lt q.2 q.1
        · by_cases hk : 𝒰.omittedPair q.2 q.1
          · simp [hlt, hgt, hk]
          · simp only [Pi.add_apply, dif_neg hlt, dif_pos hgt, dif_neg hk,
              map_add]
            abel
        · simp [hlt, hgt])

theorem extend1_kept (z : Cochain1 (F.onIntersections 𝒰)) (p : KeptPair 𝒰) :
    extend1 F z (p.fst, p.snd) = z p := by
  simp only [extend1, AddMonoidHom.mk'_apply, dif_pos p.lt, dif_neg p.kept]

theorem extend1_diag (z : Cochain1 (F.onIntersections 𝒰)) (i : 𝒰.Index) :
    extend1 F z (i, i) = 0 := by
  letI := 𝒰.indexOrder
  have hirr : ¬ 𝒰.indexOrder.lt i i := lt_irrefl i
  simp only [extend1, AddMonoidHom.mk'_apply, dif_neg hirr]

theorem extend1_omitted (z : Cochain1 (F.onIntersections 𝒰)) {i j : 𝒰.Index}
    (hij : 𝒰.indexOrder.lt i j) (hk : 𝒰.omittedPair i j) :
    extend1 F z (i, j) = 0 := by
  simp only [extend1, AddMonoidHom.mk'_apply, dif_pos hij, dif_pos hk]

theorem extend1_rev (z : Cochain1 (F.onIntersections 𝒰)) {i j : 𝒰.Index}
    (hij : 𝒰.indexOrder.lt i j) :
    extend1 F z (j, i) =
      - F.restrict (𝒰.swapHom i j) (extend1 F z (i, j)) := by
  letI := 𝒰.indexOrder
  have hnlt : ¬ 𝒰.indexOrder.lt j i := lt_asymm hij
  by_cases hk : 𝒰.omittedPair i j
  · simp only [extend1, AddMonoidHom.mk'_apply, dif_neg hnlt, dif_pos hij,
      dif_pos hk, map_zero, neg_zero]
  · simp only [extend1, AddMonoidHom.mk'_apply, dif_neg hnlt, dif_pos hij,
      dif_neg hk]

/-- 反対称性の全添字版: `n (j,i) = - swap-transport (n (i,j))`。 -/
theorem extend1_antisym (z : Cochain1 (F.onIntersections 𝒰)) (i j : 𝒰.Index) :
    extend1 F z (j, i) =
      - F.restrict (𝒰.swapHom i j) (extend1 F z (i, j)) := by
  letI := 𝒰.indexOrder
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact extend1_rev F z hij
  · rw [extend1_diag, map_zero, neg_zero]
  · rw [extend1_rev F z hji]
    have hcollapse :
        F.restrict (𝒰.swapHom i j)
            (- F.restrict (𝒰.swapHom j i) (extend1 F z (j, i))) =
          - extend1 F z (j, i) := by
      rw [map_neg]
      congr 1
      rw [← F.restrict_comp (𝒰.swapHom i j) (𝒰.swapHom j i),
        Subsingleton.elim (𝒰.swapHom i j ≫ 𝒰.swapHom j i)
          (𝟙 (𝒰.pairCtx j i)),
        F.restrict_id]
    rw [hcollapse, neg_neg]

/-! ## 補題2.1A: 拡張の cocycle 性(数学本文の符号付き像の議論) -/

/--
master lemma: 対角零・反対称・昇順 cocycle 恒等式を満たす全添字 cochain は
tuple cocycle である。数学本文の「permutation に対する cocycle equation は
昇順 equation の符号付き像」の Lean 実体。
-/
theorem ordDelta1_eq_zero_of_normalForm (n : OrdCochain1 F 𝒰)
    (hdiag : ∀ i, n (i, i) = 0)
    (hanti : ∀ i j, n (j, i) = - F.restrict (𝒰.swapHom i j) (n (i, j)))
    (hinc : ∀ i j k, 𝒰.indexOrder.lt i j -> 𝒰.indexOrder.lt j k ->
      F.restrict (𝒰.tripleFaceJK i j k) (n (j, k)) -
        F.restrict (𝒰.tripleFaceIK i j k) (n (i, k)) +
        F.restrict (𝒰.tripleFaceIJ i j k) (n (i, j)) = 0) :
    ordDelta1 F n = 0 := by
  letI := 𝒰.indexOrder
  funext t
  obtain ⟨a, b, c⟩ := t
  simp only [ordDelta1, AddMonoidHom.mk'_apply, Pi.zero_apply]
  have ha : 𝒰.tripleCtx a b c ⟶ 𝒰.chart a :=
    𝒰.tripleFaceIJ a b c ≫ 𝒰.pairFst a b
  have hb : 𝒰.tripleCtx a b c ⟶ 𝒰.chart b :=
    𝒰.tripleFaceIJ a b c ≫ 𝒰.pairSnd a b
  have hc : 𝒰.tripleCtx a b c ⟶ 𝒰.chart c :=
    𝒰.tripleFaceIK a b c ≫ 𝒰.pairSnd a c
  -- 一様 restriction。
  set P : ∀ (x y : 𝒰.Index), (𝒰.tripleCtx a b c ⟶ 𝒰.chart x) ->
      (𝒰.tripleCtx a b c ⟶ 𝒰.chart y) ->
      F.carrier (𝒰.pairCtx x y) -> F.carrier (𝒰.tripleCtx a b c) :=
    fun _ _ hx hy v => F.restrict (𝒰.pairLift hx hy) v with hP
  -- E の3項を P 形へ collapse。
  have e₁ : F.restrict (𝒰.tripleFaceJK a b c) (n (b, c)) =
      P b c hb hc (n (b, c)) := F.restrict_hom_congr _ _ _
  have e₂ : F.restrict (𝒰.tripleFaceIK a b c) (n (a, c)) =
      P a c ha hc (n (a, c)) := F.restrict_hom_congr _ _ _
  have e₃ : F.restrict (𝒰.tripleFaceIJ a b c) (n (a, b)) =
      P a b ha hb (n (a, b)) := F.restrict_hom_congr _ _ _
  rw [e₁, e₂, e₃]
  -- 反対称の P 版。
  have flip : ∀ (x y : 𝒰.Index) (hx : 𝒰.tripleCtx a b c ⟶ 𝒰.chart x)
      (hy : 𝒰.tripleCtx a b c ⟶ 𝒰.chart y),
      P y x hy hx (n (y, x)) = - P x y hx hy (n (x, y)) := by
    intro x y hx hy
    rw [hP]
    show F.restrict (𝒰.pairLift hy hx) (n (y, x)) =
      - F.restrict (𝒰.pairLift hx hy) (n (x, y))
    rw [hanti x y, map_neg]
    congr 1
    rw [← F.restrict_comp (𝒰.pairLift hy hx) (𝒰.swapHom x y) (n (x, y))]
    exact F.restrict_hom_congr _ _ _
  -- 平行射の P 一致。
  have congrP : ∀ (x y : 𝒰.Index)
      (hx hx' : 𝒰.tripleCtx a b c ⟶ 𝒰.chart x)
      (hy hy' : 𝒰.tripleCtx a b c ⟶ 𝒰.chart y)
      (v : F.carrier (𝒰.pairCtx x y)), P x y hx hy v = P x y hx' hy' v := by
    intro x y hx hx' hy hy' v
    rw [hP]
    exact F.restrict_hom_congr _ _ _
  -- 対角の P 版。
  have diagP : ∀ (x : 𝒰.Index) (hx hx' : 𝒰.tripleCtx a b c ⟶ 𝒰.chart x),
      P x x hx hx' (n (x, x)) = 0 := by
    intro x hx hx'
    show F.restrict (𝒰.pairLift hx hx') (n (x, x)) = 0
    rw [hdiag x, map_zero]
  -- 昇順恒等式の P 版。
  have sorted : ∀ (i j k : 𝒰.Index)
      (hi : 𝒰.tripleCtx a b c ⟶ 𝒰.chart i)
      (hj : 𝒰.tripleCtx a b c ⟶ 𝒰.chart j)
      (hk : 𝒰.tripleCtx a b c ⟶ 𝒰.chart k),
      𝒰.indexOrder.lt i j -> 𝒰.indexOrder.lt j k ->
      P j k hj hk (n (j, k)) - P i k hi hk (n (i, k)) +
        P i j hi hj (n (i, j)) = 0 := by
    intro i j k hi hj hk hij hjk
    have hT : 𝒰.tripleCtx a b c ⟶ 𝒰.tripleCtx i j k := 𝒰.tripleLift hi hj hk
    have key := congrArg (F.restrict hT) (hinc i j k hij hjk)
    rw [map_zero, map_add, map_sub] at key
    have c₁ : F.restrict hT (F.restrict (𝒰.tripleFaceJK i j k) (n (j, k))) =
        P j k hj hk (n (j, k)) := by
      show F.restrict hT (F.restrict (𝒰.tripleFaceJK i j k) (n (j, k))) =
        F.restrict (𝒰.pairLift hj hk) (n (j, k))
      rw [F.restrict_restrict hT (𝒰.tripleFaceJK i j k)
          (𝒰.pairLift hj hk) (𝟙 (𝒰.pairCtx j k)) (n (j, k)), F.restrict_id]
    have c₂ : F.restrict hT (F.restrict (𝒰.tripleFaceIK i j k) (n (i, k))) =
        P i k hi hk (n (i, k)) := by
      show F.restrict hT (F.restrict (𝒰.tripleFaceIK i j k) (n (i, k))) =
        F.restrict (𝒰.pairLift hi hk) (n (i, k))
      rw [F.restrict_restrict hT (𝒰.tripleFaceIK i j k)
          (𝒰.pairLift hi hk) (𝟙 (𝒰.pairCtx i k)) (n (i, k)), F.restrict_id]
    have c₃ : F.restrict hT (F.restrict (𝒰.tripleFaceIJ i j k) (n (i, j))) =
        P i j hi hj (n (i, j)) := by
      show F.restrict hT (F.restrict (𝒰.tripleFaceIJ i j k) (n (i, j))) =
        F.restrict (𝒰.pairLift hi hj) (n (i, j))
      rw [F.restrict_restrict hT (𝒰.tripleFaceIJ i j k)
          (𝒰.pairLift hi hj) (𝟙 (𝒰.pairCtx i j)) (n (i, j)), F.restrict_id]
    rw [c₁, c₂, c₃] at key
    exact key
  clear e₁ e₂ e₃
  -- 3添字の順序で場合分け。
  rcases lt_trichotomy a b with hab | rfl | hba
  · rcases lt_trichotomy b c with hbc | rfl | hcb
    · exact sorted a b c ha hb hc hab hbc
    · rw [diagP b hb hc, congrP a b ha ha hc hb (n (a, b))]
      abel
    · rcases lt_trichotomy a c with hac | rfl | hca
      · -- a < c < b
        rw [flip c b hc hb]
        have h := sorted a c b ha hc hb hac hcb
        have hrw : - P c b hc hb (n (c, b)) - P a c ha hc (n (a, c)) +
            P a b ha hb (n (a, b)) =
            - (P c b hc hb (n (c, b)) - P a b ha hb (n (a, b)) +
              P a c ha hc (n (a, c))) := by abel
        rw [hrw, h, neg_zero]
      · -- c = a < b: tuple (a, b, a)
        rw [diagP a ha hc, flip a b hc hb,
          congrP a b hc ha hb hb (n (a, b))]
        abel
      · -- c < a < b
        rw [flip c b hc hb, flip c a hc ha]
        have h := sorted c a b hc ha hb hca hab
        have hrw : - P c b hc hb (n (c, b)) - - P c a hc ha (n (c, a)) +
            P a b ha hb (n (a, b)) =
            P a b ha hb (n (a, b)) - P c b hc hb (n (c, b)) +
              P c a hc ha (n (c, a)) := by abel
        rw [hrw]
        exact h
  · rw [diagP a ha hb, congrP a c hb ha hc hc (n (a, c))]
    abel
  · rcases lt_trichotomy a c with hac | rfl | hca
    · -- b < a < c
      rw [flip b a hb ha]
      have h := sorted b a c hb ha hc hba hac
      have hrw : P b c hb hc (n (b, c)) - P a c ha hc (n (a, c)) +
          - P b a hb ha (n (b, a)) =
          - (P a c ha hc (n (a, c)) - P b c hb hc (n (b, c)) +
            P b a hb ha (n (b, a))) := by abel
      rw [hrw, h, neg_zero]
    · -- b < a = c: tuple (a, b, a)
      rw [diagP a ha hc, flip b a hb ha,
        congrP b a hb hb hc ha (n (b, a))]
      abel
    · rcases lt_trichotomy b c with hbc | rfl | hcb
      · -- b < c < a
        rw [flip c a hc ha, flip b a hb ha]
        have h := sorted b c a hb hc ha hbc hca
        have hrw : P b c hb hc (n (b, c)) - - P c a hc ha (n (c, a)) +
            - P b a hb ha (n (b, a)) =
            P c a hc ha (n (c, a)) - P b a hb ha (n (b, a)) +
              P b c hb hc (n (b, c)) := by abel
        rw [hrw]
        exact h
      · -- c = b < a: tuple (a, b, b)
        rw [diagP b hb hc, congrP a b ha ha hc hb (n (a, b))]
        abel
      · -- c < b < a
        rw [flip c b hc hb, flip c a hc ha, flip b a hb ha]
        have h := sorted c b a hc hb ha hcb hba
        have hrw : - P c b hc hb (n (c, b)) - - P c a hc ha (n (c, a)) +
            - P b a hb ha (n (b, a)) =
            - (P b a hb ha (n (b, a)) - P c a hc ha (n (c, a)) +
              P c b hc hb (n (c, b))) := by abel
        rw [hrw, h, neg_zero]

/--
補題2.1A 全射部: 増加添字 cocycle の反対称拡張は tuple cocycle である。
昇順恒等式は kept triple では入力 cocycle 性から、omitted triple では
normalization から従う。
-/
theorem extend1_cocycle
    (htriple : ∀ i j k, 𝒰.omittedTriple i j k ->
      ∀ v : F.carrier (𝒰.tripleCtx i j k), v = 0)
    {z : Cochain1 (F.onIntersections 𝒰)}
    (hz : delta1 (F.onIntersections 𝒰) z = 0) :
    ordDelta1 F (extend1 F z) = 0 := by
  refine ordDelta1_eq_zero_of_normalForm F (extend1 F z) (extend1_diag F z)
    (extend1_antisym F z) ?_
  intro i j k hij hjk
  by_cases hkt : 𝒰.omittedTriple i j k
  · exact htriple i j k hkt _
  · set t : KeptTriple 𝒰 := ⟨i, j, k, hij, hjk, hkt⟩ with ht
    have h := congrFun hz t
    simp only [delta1, AddMonoidHom.mk'_apply, Pi.zero_apply] at h
    have e₁ : extend1 F z (j, k) = z t.pairJK := extend1_kept F z t.pairJK
    have e₂ : extend1 F z (i, k) = z t.pairIK := extend1_kept F z t.pairIK
    have e₃ : extend1 F z (i, j) = z t.pairIJ := extend1_kept F z t.pairIJ
    rw [e₁, e₂, e₃]
    exact h

/-- 補題2.1A(`B̃¹ ≅ B¹`、拡張方向): 反対称拡張は増加 coboundary を
tuple coboundary に送る。restriction 方向は `restrictCochain1_ordDelta0`。
両方向で `B̃¹` と `B¹` が対応する。 -/
theorem extend1_delta0
    (hpair : ∀ i j, 𝒰.omittedPair i j ->
      ∀ v : F.carrier (𝒰.pairCtx i j), v = 0)
    (b : Cochain0 (F.onIntersections 𝒰)) :
    extend1 F (delta0 (F.onIntersections 𝒰) b) = ordDelta0 F b := by
  letI := 𝒰.indexOrder
  funext q
  obtain ⟨i, j⟩ := q
  rcases lt_trichotomy i j with hij | rfl | hji
  · by_cases hk : 𝒰.omittedPair i j
    · rw [extend1_omitted F _ hij hk]
      exact (hpair i j hk _).symm
    · exact extend1_kept F (delta0 (F.onIntersections 𝒰) b) ⟨i, j, hij, hk⟩
  · rw [extend1_diag]
    show (0 : F.carrier (𝒰.pairCtx i i)) =
      F.restrict (𝒰.pairSnd i i) (b i) - F.restrict (𝒰.pairFst i i) (b i)
    rw [F.restrict_hom_congr (𝒰.pairSnd i i) (𝒰.pairFst i i) (b i), sub_self]
  · rw [extend1_rev F _ hji]
    by_cases hk : 𝒰.omittedPair j i
    · rw [extend1_omitted F _ hji hk, map_zero, neg_zero]
      exact (pair_rev_zero F hpair hk _).symm
    · have hval : extend1 F (delta0 (F.onIntersections 𝒰) b) (j, i) =
          F.restrict (𝒰.pairSnd j i) (b i) - F.restrict (𝒰.pairFst j i) (b j) :=
        extend1_kept F (delta0 (F.onIntersections 𝒰) b) ⟨j, i, hji, hk⟩
      rw [hval, map_sub, neg_sub]
      show F.restrict (𝒰.swapHom j i) (F.restrict (𝒰.pairFst j i) (b j)) -
          F.restrict (𝒰.swapHom j i) (F.restrict (𝒰.pairSnd j i) (b i)) =
        F.restrict (𝒰.pairSnd i j) (b j) - F.restrict (𝒰.pairFst i j) (b i)
      rw [F.restrict_restrict (𝒰.swapHom j i) (𝒰.pairFst j i)
          (𝒰.pairSnd i j) (𝟙 (𝒰.chart j)) (b j), F.restrict_id,
        F.restrict_restrict (𝒰.swapHom j i) (𝒰.pairSnd j i)
          (𝒰.pairFst i j) (𝟙 (𝒰.chart i)) (b i), F.restrict_id]

/-- restriction は拡張の左逆(cochain 水準)。 -/
theorem restrictCochain1_extend1 (z : Cochain1 (F.onIntersections 𝒰)) :
    restrictCochain1 F (extend1 F z) = z := by
  funext p
  exact extend1_kept F z p

/-- cocycle 水準では拡張は restriction の右逆でもある(単射部の帰結)。 -/
theorem extend1_restrictCochain1
    (hpair : ∀ i j, 𝒰.omittedPair i j ->
      ∀ v : F.carrier (𝒰.pairCtx i j), v = 0)
    (htriple : ∀ i j k, 𝒰.omittedTriple i j k ->
      ∀ v : F.carrier (𝒰.tripleCtx i j k), v = 0)
    {c : OrdCochain1 F 𝒰} (hc : ordDelta1 F c = 0) :
    extend1 F (restrictCochain1 F c) = c := by
  have hz : delta1 (F.onIntersections 𝒰) (restrictCochain1 F c) = 0 := by
    rw [← restrictCochain2_ordDelta1, hc, map_zero]
  have hdiff : ordDelta1 F (extend1 F (restrictCochain1 F c) - c) = 0 := by
    rw [map_sub, extend1_cocycle F htriple hz, hc, sub_zero]
  have h0 : restrictCochain1 F (extend1 F (restrictCochain1 F c) - c) = 0 := by
    rw [map_sub, restrictCochain1_extend1, sub_self]
  exact sub_eq_zero.mp (cocycle_eq_zero_of_restrict_eq_zero F hpair hdiff h0)

/-! ## 補題2.1A: `H¹` 同値と零類移送 -/

section H1

variable (hpair : ∀ i j, 𝒰.omittedPair i j ->
    ∀ v : F.carrier (𝒰.pairCtx i j), v = 0)
variable (htriple : ∀ i j k, 𝒰.omittedTriple i j k ->
    ∀ v : F.carrier (𝒰.tripleCtx i j k), v = 0)

/-- tuple cocycle の増加 restriction は増加 cocycle。 -/
def restrictCocycle (c : (ordComplex F 𝒰).H1Cocycle) :
    (incComplex (F.onIntersections 𝒰)).H1Cocycle :=
  ⟨restrictCochain1 F c.1, by
    have hc : ordDelta1 F c.1 = 0 := c.2
    show delta1 (F.onIntersections 𝒰) (restrictCochain1 F c.1) = 0
    rw [← restrictCochain2_ordDelta1, hc, map_zero]⟩

/-- 増加 cocycle の反対称拡張は tuple cocycle。 -/
def extendCocycle (z : (incComplex (F.onIntersections 𝒰)).H1Cocycle) :
    (ordComplex F 𝒰).H1Cocycle :=
  ⟨extend1 F z.1, extend1_cocycle F htriple z.2⟩

/-- 補題2.1A: `Ȟ¹_ord → Ȟ¹`(restriction の誘導)。 -/
def ordToIncH1 : (ordComplex F 𝒰).H1 -> IncH1 (F.onIntersections 𝒰) :=
  Quotient.lift
    (fun c => Quotient.mk
      (incComplex (F.onIntersections 𝒰)).H1CoboundarySetoid
      (restrictCocycle F c))
    (by
      intro x y hxy
      rcases hxy with ⟨b, hb⟩
      have hb' : x.1 - y.1 = ordDelta0 F b := hb
      apply Quotient.sound
      refine ⟨b, ?_⟩
      show restrictCochain1 F x.1 - restrictCochain1 F y.1 =
        delta0 (F.onIntersections 𝒰) b
      rw [← map_sub, hb', restrictCochain1_ordDelta0])

/-- 補題2.1A: `Ȟ¹ → Ȟ¹_ord`(反対称拡張の誘導)。 -/
def incToOrdH1 : IncH1 (F.onIntersections 𝒰) -> (ordComplex F 𝒰).H1 :=
  Quotient.lift
    (fun z => Quotient.mk (ordComplex F 𝒰).H1CoboundarySetoid
      (extendCocycle F htriple z))
    (by
      intro x y hxy
      rcases hxy with ⟨b, hb⟩
      have hb' : x.1 - y.1 = delta0 (F.onIntersections 𝒰) b := hb
      apply Quotient.sound
      refine ⟨b, ?_⟩
      show extend1 F x.1 - extend1 F y.1 = ordDelta0 F b
      rw [← map_sub, hb', extend1_delta0 F hpair])

/-- 補題2.1A: 両誘導写像は互いに逆(tuple 側)。 -/
theorem incToOrd_ordToInc (h : (ordComplex F 𝒰).H1) :
    incToOrdH1 F hpair htriple (ordToIncH1 F h) = h := by
  refine Quotient.inductionOn h ?_
  intro c
  apply Quotient.sound
  refine ⟨0, ?_⟩
  show extend1 F (restrictCochain1 F c.1) - c.1 = ordDelta0 F 0
  rw [extend1_restrictCochain1 F hpair htriple c.2, sub_self, map_zero]

/-- 補題2.1A: 両誘導写像は互いに逆(増加側)。 -/
theorem ordToInc_incToOrd (h : IncH1 (F.onIntersections 𝒰)) :
    ordToIncH1 F (incToOrdH1 F hpair htriple h) = h := by
  refine Quotient.inductionOn h ?_
  intro z
  apply Quotient.sound
  refine ⟨0, ?_⟩
  show restrictCochain1 F (extend1 F z.1) - z.1 =
    delta0 (F.onIntersections 𝒰) 0
  rw [restrictCochain1_extend1, sub_self, map_zero]

/-- restriction の誘導写像は零類を零類へ送る。 -/
theorem ordToIncH1_zero :
    ordToIncH1 F ((ordComplex F 𝒰).H1ZeroClass) =
      (incComplex (F.onIntersections 𝒰)).H1ZeroClass := by
  apply Quotient.sound
  refine ⟨0, ?_⟩
  show restrictCochain1 F (0 : OrdCochain1 F 𝒰) - 0 =
    delta0 (F.onIntersections 𝒰) 0
  simp only [map_zero, sub_zero]

/-- 拡張の誘導写像は零類を零類へ送る。 -/
theorem incToOrdH1_zero :
    incToOrdH1 F hpair htriple
        ((incComplex (F.onIntersections 𝒰)).H1ZeroClass) =
      (ordComplex F 𝒰).H1ZeroClass := by
  apply Quotient.sound
  refine ⟨0, ?_⟩
  show extend1 F (0 : Cochain1 (F.onIntersections 𝒰)) - 0 = ordDelta0 F 0
  simp only [map_zero, sub_zero]

include hpair htriple in
/-- 補題2.1A: 零類の保存と反映。 -/
theorem ordToIncH1_zero_iff (h : (ordComplex F 𝒰).H1) :
    (incComplex (F.onIntersections 𝒰)).H1IsZero (ordToIncH1 F h) ↔
      (ordComplex F 𝒰).H1IsZero h := by
  constructor
  · intro hh
    have hstep := congrArg (incToOrdH1 F hpair htriple) hh
    rw [incToOrd_ordToInc F hpair htriple] at hstep
    rw [Cohomology.AdditiveThreeTermComplex.H1IsZero, hstep]
    exact incToOrdH1_zero F hpair htriple
  · intro hh
    rw [Cohomology.AdditiveThreeTermComplex.H1IsZero] at hh
    rw [Cohomology.AdditiveThreeTermComplex.H1IsZero, hh]
    exact ordToIncH1_zero F

end H1

/-! ## 補題2.1A: matching family の同値(set-valued clause) -/

/-- site 全域の Type 値 state presheaf データ(matching family clause の担体)。 -/
structure SiteStateData (S : Site.AATSite A) where
  State : S.category -> Type x
  restrictState : ∀ {V' V : S.category}, (V' ⟶ V) -> State V -> State V'
  restrictState_id : ∀ (V : S.category) (p : State V), restrictState (𝟙 V) p = p
  restrictState_comp :
      ∀ {V'' V' V : S.category} (f : V'' ⟶ V') (g : V' ⟶ V) (p : State V),
        restrictState (f ≫ g) p = restrictState f (restrictState g p)

namespace SiteStateData

variable (T : SiteStateData.{u, x} S)

/-- thin site: 平行な射に沿った state restriction は一致する。 -/
theorem restrictState_hom_congr {X Y : S.category} (h h' : X ⟶ Y)
    (p : T.State Y) : T.restrictState h p = T.restrictState h' p := by
  rw [Subsingleton.elim h h']

/-- 省略昇順 pair の subsingleton 性は逆順 overlap にも移送される。 -/
theorem rev_subsingleton {𝒰 : MonomorphicOrderedCover S}
    (hsub : ∀ i j, 𝒰.omittedPair i j -> Subsingleton (T.State (𝒰.pairCtx i j)))
    {i j : 𝒰.Index} (hk : 𝒰.omittedPair j i) :
    Subsingleton (T.State (𝒰.pairCtx i j)) := by
  constructor
  intro p q
  haveI := hsub j i hk
  have hp : T.restrictState (𝒰.swapHom j i)
      (T.restrictState (𝒰.swapHom i j) p) = p := by
    rw [← T.restrictState_comp (𝒰.swapHom j i) (𝒰.swapHom i j) p,
      Subsingleton.elim (𝒰.swapHom j i ≫ 𝒰.swapHom i j) (𝟙 (𝒰.pairCtx i j)),
      T.restrictState_id]
  have hq : T.restrictState (𝒰.swapHom j i)
      (T.restrictState (𝒰.swapHom i j) q) = q := by
    rw [← T.restrictState_comp (𝒰.swapHom j i) (𝒰.swapHom i j) q,
      Subsingleton.elim (𝒰.swapHom j i ≫ 𝒰.swapHom i j) (𝟙 (𝒰.pairCtx i j)),
      T.restrictState_id]
  rw [← hp, ← hq,
    Subsingleton.elim (T.restrictState (𝒰.swapHom i j) p)
      (T.restrictState (𝒰.swapHom i j) q)]

/--
X.補題2.1A(matching family clause): 省略 overlap 上 subsingleton な
state presheaf の chart family について、全 ordered overlap 上の一致と
増加・非省略 overlap 上の一致は同値である。
-/
theorem matchingFamily_iff {𝒰 : MonomorphicOrderedCover S}
    (hsub : ∀ i j, 𝒰.omittedPair i j -> Subsingleton (T.State (𝒰.pairCtx i j)))
    (p : ∀ i : 𝒰.Index, T.State (𝒰.chart i)) :
    (∀ i j : 𝒰.Index,
        T.restrictState (𝒰.pairFst i j) (p i) =
          T.restrictState (𝒰.pairSnd i j) (p j)) ↔
      (∀ q : KeptPair 𝒰,
        T.restrictState (𝒰.pairFst q.fst q.snd) (p q.fst) =
          T.restrictState (𝒰.pairSnd q.fst q.snd) (p q.snd)) := by
  constructor
  · intro h q
    exact h q.fst q.snd
  · intro h i j
    letI := 𝒰.indexOrder
    rcases lt_trichotomy i j with hij | rfl | hji
    · by_cases hk : 𝒰.omittedPair i j
      · haveI := hsub i j hk
        exact Subsingleton.elim _ _
      · exact h ⟨i, j, hij, hk⟩
    · exact T.restrictState_hom_congr (𝒰.pairFst i i) (𝒰.pairSnd i i) (p i)
    · by_cases hk : 𝒰.omittedPair j i
      · haveI := T.rev_subsingleton hsub hk
        exact Subsingleton.elim _ _
      · have hkept := h ⟨j, i, hji, hk⟩
        have := congrArg (T.restrictState (𝒰.swapHom j i)) hkept
        rw [← T.restrictState_comp (𝒰.swapHom j i) (𝒰.pairFst j i) (p j),
          ← T.restrictState_comp (𝒰.swapHom j i) (𝒰.pairSnd j i) (p i)] at this
        rw [T.restrictState_hom_congr (𝒰.pairFst i j)
            (𝒰.swapHom j i ≫ 𝒰.pairSnd j i) (p i),
          T.restrictState_hom_congr (𝒰.pairSnd i j)
            (𝒰.swapHom j i ≫ 𝒰.pairFst j i) (p j)]
        exact this.symm

end SiteStateData

end Saga
end SemanticRepair
end AAT.AG
