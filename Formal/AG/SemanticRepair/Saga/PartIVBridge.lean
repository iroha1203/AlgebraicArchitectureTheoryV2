import Formal.AG.SemanticRepair.Saga.OrderedComparison

/-!
# Part X Lemma 2.1A: connection to the Part IV declarations

This module connects the ordered-tuple comparison of
`Formal.AG.SemanticRepair.Saga.OrderedComparison` to the actual Part IV
surface `Cohomology.CoverRelativeCechCover` / `CoverRelativeCechComplex` /
`CoverRelativeHn` of `Formal/AG/Cohomology/CechComplex.lean`.

* `SitePresheafData.ofObstructionSheaf`: read a Part IV obstruction
  coefficient sheaf as sitewide abelian presheaf data.
* `MonomorphicOrderedCover.toTupleCechCover`: the ordered-tuple cover-relative
  Čech cover generated from `𝒰` (tuples in degrees ≤ 2, empty simplex data
  above; the degree-one cohomology of the Part IV structure only consumes
  degrees ≤ 2).
* `MonomorphicOrderedCover.toTupleCechComplex`: a genuine
  `CoverRelativeCechComplex` instance over that cover whose differentials are
  the ordered-tuple differentials; `d ∘ d = 0` is proved, not selected.
* `degreeOneThreeTerm_toTupleCechComplex`: the degree ≤ 2 spine of that
  Part IV complex is definitionally the ordered comparison complex.
* `incToCoverRelativeH1` / `coverRelativeToIncH1` with inverse and zero-class
  theorems: Lemma 2.1A read against `CoverRelativeHn 1`.

Instantiating the sitewide presheaf at `mSemPresheaf` gives the `C_sem`
comparison of Part X Definition 3.4 against the Part IV model.
-/

noncomputable section

namespace AAT.AG
namespace SemanticRepair
namespace Saga

open CategoryTheory
open Opposite

universe u

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : Site.AATSite A}

namespace SitePresheafData

/-- Part IV の obstruction coefficient sheaf を site 全域 presheaf データとして読む。 -/
def ofObstructionSheaf (Ob : Cohomology.ObstructionSheaf S) :
    SitePresheafData.{u, u} S where
  carrier V := Ob.carrier.toPresheaf.obj (op V)
  addCommGroup V := Ob.addCommGroup V
  restrict {V' V} f :=
    AddMonoidHom.mk' (Ob.carrier.toPresheaf.map f.op) (Ob.map_add f)
  restrict_id V x := by
    show Ob.carrier.toPresheaf.map (𝟙 V).op x = x
    rw [op_id, Ob.carrier.toPresheaf.map_id]
    rfl
  restrict_comp {V'' V' V} f g x := by
    show Ob.carrier.toPresheaf.map (f ≫ g).op x = _
    rw [op_comp, Ob.carrier.toPresheaf.map_comp]
    rfl

end SitePresheafData

namespace MonomorphicOrderedCover

variable (𝒰 : MonomorphicOrderedCover S)

/-- 次数 `n` の tuple simplex(次数 ≤ 2 のみ実データ)。 -/
def tupleSimplex : Nat -> Type u
  | 0 => 𝒰.Index
  | 1 => 𝒰.Index × 𝒰.Index
  | 2 => 𝒰.Index × 𝒰.Index × 𝒰.Index
  | _ + 3 => PEmpty

/-- 次数 `n` の tuple overlap。 -/
def tupleOverlap : ∀ n : Nat, 𝒰.tupleSimplex n -> S.category
  | 0, i => 𝒰.chart i
  | 1, q => 𝒰.pairCtx q.1 q.2
  | 2, t => 𝒰.tripleCtx t.1 t.2.1 t.2.2
  | _ + 3, e => e.elim

/-- tuple face map(`l` 番目の添字を除く)。 -/
def tupleFace : ∀ (n : Nat), Fin (n + 2) -> 𝒰.tupleSimplex (n + 1) ->
    𝒰.tupleSimplex n
  | 0, ⟨0, _⟩, q => q.2
  | 0, ⟨1, _⟩, q => q.1
  | 1, ⟨0, _⟩, t => (t.2.1, t.2.2)
  | 1, ⟨1, _⟩, t => (t.1, t.2.2)
  | 1, ⟨2, _⟩, t => (t.1, t.2.1)
  | _ + 2, _, e => e.elim

/-- tuple face restriction(selected overlap 射を読む)。 -/
def tupleFaceRestriction : ∀ (n : Nat) (l : Fin (n + 2))
    (σ : 𝒰.tupleSimplex (n + 1)),
    𝒰.tupleOverlap (n + 1) σ ⟶ 𝒰.tupleOverlap n (𝒰.tupleFace n l σ)
  | 0, ⟨0, _⟩, q => 𝒰.pairSnd q.1 q.2
  | 0, ⟨1, _⟩, q => 𝒰.pairFst q.1 q.2
  | 1, ⟨0, _⟩, t => 𝒰.tripleFaceJK t.1 t.2.1 t.2.2
  | 1, ⟨1, _⟩, t => 𝒰.tripleFaceIK t.1 t.2.1 t.2.2
  | 1, ⟨2, _⟩, t => 𝒰.tripleFaceIJ t.1 t.2.1 t.2.2
  | _ + 2, _, e => e.elim

/-- `𝒰` から生成する第IV部 cover-relative Čech cover(全 ordered tuple、次数 ≤ 2)。 -/
def toTupleCechCover : Cohomology.CoverRelativeCechCover S where
  base := 𝒰.base
  Index := 𝒰.Index
  chart := 𝒰.chart
  inclusion := 𝒰.inclusion
  simplex := 𝒰.tupleSimplex
  overlap := 𝒰.tupleOverlap
  face := 𝒰.tupleFace
  faceRestriction := 𝒰.tupleFaceRestriction

variable (Ob : Cohomology.ObstructionSheaf S)

/-- tuple cochain の可換群構造。 -/
instance tupleCochainAddCommGroup (n : Nat) :
    AddCommGroup (Cohomology.CoverRelativeCechCochain 𝒰.toTupleCechCover Ob n) :=
  Pi.addCommGroup

/--
`𝒰` から生成する第IV部 cover-relative Čech complex。微分は全 ordered tuple の
交代和であり、`δ¹δ⁰ = 0` は `ordDelta1_ordDelta0` で証明される(selected
witness の supply ではなく proved)。次数 ≥ 2 の cochain は空 simplex 上の
自明群である。
-/
def toTupleCechComplex :
    Cohomology.CoverRelativeCechComplex 𝒰.toTupleCechCover Ob where
  cochainAddCommGroup n := tupleCochainAddCommGroup 𝒰 Ob n
  alternatingFaceCombination
    | 0 => fun g σ => g σ 0 - g σ 1
    | 1 => fun g σ => g σ 0 - g σ 1 + g σ 2
    | _ + 2 => fun _ σ => σ.elim
  differential
    | 0 => ordDelta0 (SitePresheafData.ofObstructionSheaf Ob)
    | 1 => ordDelta1 (SitePresheafData.ofObstructionSheaf Ob)
    | _ + 2 => 0
  differential_eq_alternatingFaceCombination
    | 0, c => rfl
    | 1, c => rfl
    | _ + 2, c => by
        funext σ
        exact σ.elim
  differential_comp
    | 0, c =>
        ordDelta1_ordDelta0 (SitePresheafData.ofObstructionSheaf Ob) c
    | _ + 1, c => by
        funext σ
        exact σ.elim

/--
第IV部複体の次数 ≤ 2 スパインは ordered comparison 複体そのものである
(定義的一致)。
-/
theorem degreeOneThreeTerm_toTupleCechComplex :
    (𝒰.toTupleCechComplex Ob).degreeOneThreeTerm =
      ordComplex (SitePresheafData.ofObstructionSheaf Ob) 𝒰 :=
  rfl

section H1

variable {𝒰}
variable (hpair : ∀ i j, 𝒰.omittedPair i j ->
    ∀ v : (SitePresheafData.ofObstructionSheaf Ob).carrier (𝒰.pairCtx i j),
      v = 0)
variable (htriple : ∀ i j k, 𝒰.omittedTriple i j k ->
    ∀ v : (SitePresheafData.ofObstructionSheaf Ob).carrier (𝒰.tripleCtx i j k),
      v = 0)

/--
補題2.1A(第IV部接続、順方向): 増加三項複体の `H¹` から
第IV部 `CoverRelativeHn 1` への写像。
-/
def incToCoverRelativeH1 :
    IncH1 ((SitePresheafData.ofObstructionSheaf Ob).onIntersections 𝒰) ->
      (𝒰.toTupleCechComplex Ob).CoverRelativeHn 1 :=
  incToOrdH1 (SitePresheafData.ofObstructionSheaf Ob) hpair htriple

/--
補題2.1A(第IV部接続、逆方向): 第IV部 `CoverRelativeHn 1` から
増加三項複体の `H¹` への写像。
-/
def coverRelativeToIncH1 :
    (𝒰.toTupleCechComplex Ob).CoverRelativeHn 1 ->
      IncH1 ((SitePresheafData.ofObstructionSheaf Ob).onIntersections 𝒰) :=
  ordToIncH1 (SitePresheafData.ofObstructionSheaf Ob)

/-- 補題2.1A(第IV部接続): 両写像は互いに逆(第IV部側)。 -/
theorem incToCoverRelative_coverRelativeToInc
    (h : (𝒰.toTupleCechComplex Ob).CoverRelativeHn 1) :
    incToCoverRelativeH1 Ob hpair htriple (coverRelativeToIncH1 Ob h) = h :=
  incToOrd_ordToInc (SitePresheafData.ofObstructionSheaf Ob) hpair htriple h

/-- 補題2.1A(第IV部接続): 両写像は互いに逆(増加側)。 -/
theorem coverRelativeToInc_incToCoverRelative
    (h : IncH1 ((SitePresheafData.ofObstructionSheaf Ob).onIntersections 𝒰)) :
    coverRelativeToIncH1 Ob (incToCoverRelativeH1 Ob hpair htriple h) = h :=
  ordToInc_incToOrd (SitePresheafData.ofObstructionSheaf Ob) hpair htriple h

include hpair htriple in
/-- 補題2.1A(第IV部接続): 零類の保存と反映。 -/
theorem coverRelativeToIncH1_zero_iff
    (h : (𝒰.toTupleCechComplex Ob).CoverRelativeHn 1) :
    (incComplex ((SitePresheafData.ofObstructionSheaf Ob).onIntersections 𝒰)).H1IsZero
        (coverRelativeToIncH1 Ob h) ↔
      (𝒰.toTupleCechComplex Ob).degreeOneThreeTerm.H1IsZero h :=
  ordToIncH1_zero_iff (SitePresheafData.ofObstructionSheaf Ob) hpair htriple h

end H1

end MonomorphicOrderedCover

end Saga
end SemanticRepair
end AAT.AG
