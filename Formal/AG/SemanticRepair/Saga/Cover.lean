import Formal.AG.Site.Geometry
import Mathlib.Tactic

/-!
# Part X §1–§2: monomorphic ordered AAT cover and its intersection diagram

This module fixes the cover-side inputs of Part X Theorem 1.1 following the R0
design note (`docs/note/aat_saga_part10_lean_r0_input_structure_design.md`).

* `MonomorphicOrderedCover`: a linearly ordered monomorphic AAT cover with
  selected pairwise / triple overlaps, pullback lifts, and a selected
  designation of the empty intersections that Part X §1 removes from the Čech
  products.  The designation carries the monotonicity law that keeps every
  face of a kept triple constructible.
* `IntersectionIndex` / `Face`: the objects and generating morphisms of the
  intersection diagram `Int_{≤2}(𝒰)` used by the comparison core.
* `TopologicalMonomorphicCover`: the Part X Definition 8.1 extension whose
  cover sieve belongs to the generated AAT topology (consumed by C5).
* `MonomorphicOrderedCover.ofOverlapPackage`: canonical constructor from the
  site's selected `ContextOverlapPullback`; on this thin context model every
  morphism is a monomorphism (Part II Proposition 4.2 reading), which is
  recorded by `mono_of_contextHom`.

The increasing three-term Čech complex over this diagram lives in
`Formal.AG.SemanticRepair.Saga.CechThreeTerm`.
-/

noncomputable section

namespace AAT.AG
namespace SemanticRepair
namespace Saga

open CategoryTheory

universe u

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}

/--
II.命題4.2 の読み: 現行 site model の context category は thin であり、
すべての射は monomorphism である。定理1.1 の明示前提 `inclusion_mono` は
このモデル上で自動的に放電される。
-/
theorem mono_of_contextHom {S : Site.AATSite A} {X Y : S.category} (f : X ⟶ Y) :
    Mono f :=
  ⟨fun _ _ _ => Subsingleton.elim _ _⟩

/--
X.§1: 全順序添字つき monomorphic AAT cover。

overlap は selected data として持ち、pullback 性は lift field で持つ
(thin category なので可換条件と一意性は自動)。`omittedPair` / `omittedTriple`
は積から除く empty intersection の selected 指定であり、`omittedTriple_mono` は
本文の `U_ijk = U_i ×_W U_j ×_W U_k ⊆ U_ij`(非空 triple の pairwise overlap は
非空)を selected 指定へ忠実に写す。省略側の値の固定は定理1.1 入力8
(empty-overlap normalization)が供給する。
-/
structure MonomorphicOrderedCover (S : Site.AATSite A) where
  /-- 中心定理の base context `W`。 -/
  base : S.category
  /-- 添字集合 `I`。有限性は comparison core の入力にしない(本文 §1)。 -/
  Index : Type u
  /-- 添字の selected 全順序。 -/
  indexOrder : LinearOrder Index
  /-- chart `U_i`。 -/
  chart : Index -> S.category
  /-- 被覆射 `u_i : U_i → W`。 -/
  inclusion : ∀ i : Index, chart i ⟶ base
  /-- 定理1.1 の明示前提: 各 `u_i` は monomorphism。 -/
  inclusion_mono : ∀ i : Index, Mono (inclusion i)
  /-- pairwise overlap `U_ij`(全 pair 分を保持。複体は増加・非省略成分のみ消費)。 -/
  pairCtx : Index -> Index -> S.category
  /-- `U_ij → U_i`。 -/
  pairFst : ∀ i j, pairCtx i j ⟶ chart i
  /-- `U_ij → U_j`。 -/
  pairSnd : ∀ i j, pairCtx i j ⟶ chart j
  /-- pullback lift(thin category なので図式可換と一意性は自動)。 -/
  pairLift : ∀ {i j} {X : S.category},
      (X ⟶ chart i) -> (X ⟶ chart j) -> (X ⟶ pairCtx i j)
  /-- triple overlap `U_ijk`。 -/
  tripleCtx : Index -> Index -> Index -> S.category
  /-- `U_ijk → U_ij`。 -/
  tripleFaceIJ : ∀ i j k, tripleCtx i j k ⟶ pairCtx i j
  /-- `U_ijk → U_ik`。 -/
  tripleFaceIK : ∀ i j k, tripleCtx i j k ⟶ pairCtx i k
  /-- `U_ijk → U_jk`。 -/
  tripleFaceJK : ∀ i j k, tripleCtx i j k ⟶ pairCtx j k
  /-- triple pullback lift。 -/
  tripleLift : ∀ {i j k} {X : S.category},
      (X ⟶ chart i) -> (X ⟶ chart j) -> (X ⟶ chart k) -> (X ⟶ tripleCtx i j k)
  /-- 積から除く empty `U_ij` の selected 指定(`i < j` で読む)。 -/
  omittedPair : Index -> Index -> Prop
  /-- 積から除く empty `U_ijk` の selected 指定(`i < j < k` で読む)。 -/
  omittedTriple : Index -> Index -> Index -> Prop
  /-- 本文 `U_ijk ⊆ U_ij` の selected 指定への写し:
  非省略 triple の3つの pairwise overlap は非省略である。 -/
  omittedTriple_mono :
      ∀ i j k, indexOrder.lt i j -> indexOrder.lt j k -> ¬ omittedTriple i j k ->
        ¬ omittedPair i j ∧ ¬ omittedPair i k ∧ ¬ omittedPair j k

namespace MonomorphicOrderedCover

variable {S : Site.AATSite A}

/-- 増加・非省略の pairwise intersection の添字。 -/
structure KeptPair (𝒰 : MonomorphicOrderedCover S) : Type u where
  fst : 𝒰.Index
  snd : 𝒰.Index
  lt : 𝒰.indexOrder.lt fst snd
  kept : ¬ 𝒰.omittedPair fst snd

/-- 増加・非省略の triple intersection の添字。 -/
structure KeptTriple (𝒰 : MonomorphicOrderedCover S) : Type u where
  fst : 𝒰.Index
  snd : 𝒰.Index
  trd : 𝒰.Index
  lt₁ : 𝒰.indexOrder.lt fst snd
  lt₂ : 𝒰.indexOrder.lt snd trd
  kept : ¬ 𝒰.omittedTriple fst snd trd

variable {𝒰 : MonomorphicOrderedCover S}

/-- kept triple の第1・第2添字の kept pair(`omittedTriple_mono` で放電)。 -/
def KeptTriple.pairIJ (t : KeptTriple 𝒰) : KeptPair 𝒰 :=
  ⟨t.fst, t.snd, t.lt₁,
    (𝒰.omittedTriple_mono t.fst t.snd t.trd t.lt₁ t.lt₂ t.kept).1⟩

/-- kept triple の第1・第3添字の kept pair。増加性は明示 `lt_trans` term で供給する
(`indexOrder` は field なので dot-notation の `lt_trans` は解決されない)。 -/
def KeptTriple.pairIK (t : KeptTriple 𝒰) : KeptPair 𝒰 :=
  ⟨t.fst, t.trd,
    @lt_trans _ 𝒰.indexOrder.toPartialOrder.toPreorder _ _ _ t.lt₁ t.lt₂,
    (𝒰.omittedTriple_mono t.fst t.snd t.trd t.lt₁ t.lt₂ t.kept).2.1⟩

/-- kept triple の第2・第3添字の kept pair。 -/
def KeptTriple.pairJK (t : KeptTriple 𝒰) : KeptPair 𝒰 :=
  ⟨t.snd, t.trd, t.lt₂,
    (𝒰.omittedTriple_mono t.fst t.snd t.trd t.lt₁ t.lt₂ t.kept).2.2⟩

@[simp]
theorem KeptTriple.pairIJ_fst (t : KeptTriple 𝒰) : t.pairIJ.fst = t.fst := rfl

@[simp]
theorem KeptTriple.pairIJ_snd (t : KeptTriple 𝒰) : t.pairIJ.snd = t.snd := rfl

@[simp]
theorem KeptTriple.pairIK_fst (t : KeptTriple 𝒰) : t.pairIK.fst = t.fst := rfl

@[simp]
theorem KeptTriple.pairIK_snd (t : KeptTriple 𝒰) : t.pairIK.snd = t.trd := rfl

@[simp]
theorem KeptTriple.pairJK_fst (t : KeptTriple 𝒰) : t.pairJK.fst = t.snd := rfl

@[simp]
theorem KeptTriple.pairJK_snd (t : KeptTriple 𝒰) : t.pairJK.snd = t.trd := rfl

end MonomorphicOrderedCover

export MonomorphicOrderedCover (KeptPair KeptTriple)

variable {S : Site.AATSite A}

/--
X.定義3.1 注記の `Int_{≤2}(𝒰)` の対象: chart、非省略 pairwise overlap、
非省略 triple overlap。
-/
inductive IntersectionIndex (𝒰 : MonomorphicOrderedCover S) : Type u where
  | chart (i : 𝒰.Index)
  | pair (p : KeptPair 𝒰)
  | triple (t : KeptTriple 𝒰)

namespace IntersectionIndex

variable {𝒰 : MonomorphicOrderedCover S}

/-- 各 intersection index の実 context。 -/
def ctx : IntersectionIndex 𝒰 -> S.category
  | .chart i => 𝒰.chart i
  | .pair p => 𝒰.pairCtx p.fst p.snd
  | .triple t => 𝒰.tripleCtx t.fst t.snd t.trd

end IntersectionIndex

/--
`Int_{≤2}(𝒰)` の生成射(face)。comparison core の restriction は
これに沿ってだけ要求する。triple の face の kept-pair 性は
`omittedTriple_mono` から取る。
-/
inductive Face (𝒰 : MonomorphicOrderedCover S) :
    IntersectionIndex 𝒰 -> IntersectionIndex 𝒰 -> Type u where
  | pairLeft (p : KeptPair 𝒰) : Face 𝒰 (.pair p) (.chart p.fst)
  | pairRight (p : KeptPair 𝒰) : Face 𝒰 (.pair p) (.chart p.snd)
  | tripleIJ (t : KeptTriple 𝒰) : Face 𝒰 (.triple t) (.pair t.pairIJ)
  | tripleIK (t : KeptTriple 𝒰) : Face 𝒰 (.triple t) (.pair t.pairIK)
  | tripleJK (t : KeptTriple 𝒰) : Face 𝒰 (.triple t) (.pair t.pairJK)

namespace Face

variable {𝒰 : MonomorphicOrderedCover S}

/-- face の実 site 射。 -/
def hom : {σ τ : IntersectionIndex 𝒰} -> Face 𝒰 σ τ -> (σ.ctx ⟶ τ.ctx)
  | _, _, .pairLeft p => 𝒰.pairFst p.fst p.snd
  | _, _, .pairRight p => 𝒰.pairSnd p.fst p.snd
  | _, _, .tripleIJ t => 𝒰.tripleFaceIJ t.fst t.snd t.trd
  | _, _, .tripleIK t => 𝒰.tripleFaceIK t.fst t.snd t.trd
  | _, _, .tripleJK t => 𝒰.tripleFaceJK t.fst t.snd t.trd

end Face

/-- `V` が `Int_{≤2}(𝒰)` の context であること(torsor 律などの量化域)。 -/
def IsIntersectionCtx (𝒰 : MonomorphicOrderedCover S) (V : S.category) : Prop :=
  ∃ σ : IntersectionIndex 𝒰, σ.ctx = V

/--
X.定義8.1 条件3: 生成 topology に属する monomorphic AAT cover。
comparison core(定理6.3–7.6)はこの extension を受け取らない。
定理8.2・系8.3(C5)だけが受け取る。
-/
structure TopologicalMonomorphicCover (S : Site.AATSite A) extends
    MonomorphicOrderedCover S where
  mem_topology :
    Sieve.generate (Presieve.ofArrows toMonomorphicOrderedCover.chart
        toMonomorphicOrderedCover.inclusion) ∈
      S.topology toMonomorphicOrderedCover.base

namespace MonomorphicOrderedCover

variable {S : Site.AATSite A}

/--
canonical constructor: site の selected `ContextOverlapPullback` から
pair / triple overlap と lift を生成する。triple overlap は左結合の
iterated overlap。`omittedTriple` は pair 省略の和 + `omittedTripleExtra` で
生成するため、`omittedTriple_mono` は De Morgan で構成的に成立する。
省略指定と実際の空性の結び付けは constructor の仮定にせず、
定理1.1 入力8 normalization の証明義務として供給される。
-/
def ofOverlapPackage (base : S.category) (Index : Type u)
    (indexOrder : LinearOrder Index) (chart : Index -> S.category)
    (inclusion : ∀ i, chart i ⟶ base)
    (inclusion_mono : ∀ i, Mono (inclusion i))
    (omittedPair : Index -> Index -> Prop)
    (omittedTripleExtra : Index -> Index -> Index -> Prop) :
    MonomorphicOrderedCover S where
  base := base
  Index := Index
  indexOrder := indexOrder
  chart := chart
  inclusion := inclusion
  inclusion_mono := inclusion_mono
  pairCtx i j :=
    Site.ContextCategoryObject.of S.contextPreorder
      (S.overlap.overlap base.ctx (chart i).ctx (chart j).ctx)
  pairFst i j :=
    homOfLE (S.overlap.overlap_le_left (leOfHom (inclusion i))
      (leOfHom (inclusion j)))
  pairSnd i j :=
    homOfLE (S.overlap.overlap_le_right (leOfHom (inclusion i))
      (leOfHom (inclusion j)))
  pairLift {i j _X} fi fj :=
    homOfLE (S.overlap.overlap_lift (leOfHom (inclusion i))
      (leOfHom (inclusion j)) (leOfHom fi) (leOfHom fj))
  tripleCtx i j k :=
    Site.ContextCategoryObject.of S.contextPreorder
      (S.overlap.overlap base.ctx
        (S.overlap.overlap base.ctx (chart i).ctx (chart j).ctx)
        (chart k).ctx)
  tripleFaceIJ i j k :=
    homOfLE (S.overlap.overlap_le_left
      (S.overlap.overlap_le_base (leOfHom (inclusion i)) (leOfHom (inclusion j)))
      (leOfHom (inclusion k)))
  tripleFaceIK i j k :=
    homOfLE (S.overlap.overlap_lift (leOfHom (inclusion i))
      (leOfHom (inclusion k))
      (S.contextPreorder.trans
        (S.overlap.overlap_le_left
          (S.overlap.overlap_le_base (leOfHom (inclusion i))
            (leOfHom (inclusion j)))
          (leOfHom (inclusion k)))
        (S.overlap.overlap_le_left (leOfHom (inclusion i))
          (leOfHom (inclusion j))))
      (S.overlap.overlap_le_right
        (S.overlap.overlap_le_base (leOfHom (inclusion i)) (leOfHom (inclusion j)))
        (leOfHom (inclusion k))))
  tripleFaceJK i j k :=
    homOfLE (S.overlap.overlap_lift (leOfHom (inclusion j))
      (leOfHom (inclusion k))
      (S.contextPreorder.trans
        (S.overlap.overlap_le_left
          (S.overlap.overlap_le_base (leOfHom (inclusion i))
            (leOfHom (inclusion j)))
          (leOfHom (inclusion k)))
        (S.overlap.overlap_le_right (leOfHom (inclusion i))
          (leOfHom (inclusion j))))
      (S.overlap.overlap_le_right
        (S.overlap.overlap_le_base (leOfHom (inclusion i)) (leOfHom (inclusion j)))
        (leOfHom (inclusion k))))
  tripleLift {i j k _X} fi fj fk :=
    homOfLE (S.overlap.overlap_lift
      (S.overlap.overlap_le_base (leOfHom (inclusion i)) (leOfHom (inclusion j)))
      (leOfHom (inclusion k))
      (S.overlap.overlap_lift (leOfHom (inclusion i)) (leOfHom (inclusion j))
        (leOfHom fi) (leOfHom fj))
      (leOfHom fk))
  omittedPair := omittedPair
  omittedTriple i j k :=
    omittedPair i j ∨ omittedPair i k ∨ omittedPair j k ∨
      omittedTripleExtra i j k
  omittedTriple_mono _i _j _k _ _ h :=
    ⟨fun ha => h (Or.inl ha), fun hb => h (Or.inr (Or.inl hb)),
      fun hc => h (Or.inr (Or.inr (Or.inl hc)))⟩

end MonomorphicOrderedCover

end Saga
end SemanticRepair
end AAT.AG
