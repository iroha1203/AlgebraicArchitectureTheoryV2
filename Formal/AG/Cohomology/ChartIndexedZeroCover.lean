import Formal.AG.Cohomology.CechComplex

noncomputable section

namespace AAT.AG
namespace Cohomology

universe u

open CategoryTheory

/--
X.R1(d): explicit incidence between zero-simplices and cover charts.

This is intentionally additional data.  A plain `CoverRelativeCechCover`
records an arbitrary selected type of zero-simplices; it does not by itself
claim that zero-simplices are exactly the chart indices.
-/
structure CoverRelativeCechZeroSimplexChartIncidence {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A}
    (𝒰 : CoverRelativeCechCover S) where
  chartOfZeroSimplex : 𝒰.simplex 0 -> 𝒰.Index
  zeroSimplexOfChart : 𝒰.Index -> 𝒰.simplex 0
  chartOf_zeroSimplexOfChart :
    ∀ i : 𝒰.Index, chartOfZeroSimplex (zeroSimplexOfChart i) = i
  zeroSimplexOfChart_chartOf :
    ∀ σ : 𝒰.simplex 0, zeroSimplexOfChart (chartOfZeroSimplex σ) = σ
  overlap_zeroSimplexOfChart_eq_chart :
    ∀ i : 𝒰.Index, 𝒰.overlap 0 (zeroSimplexOfChart i) = 𝒰.chart i

namespace CoverRelativeCechZeroSimplexChartIncidence

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A} {𝒰 : CoverRelativeCechCover S}

/-- X.R1(d): incidence data gives an equivalence between charts and zero-simplices. -/
def zeroSimplexEquiv (I : CoverRelativeCechZeroSimplexChartIncidence 𝒰) :
    𝒰.simplex 0 ≃ 𝒰.Index where
  toFun := I.chartOfZeroSimplex
  invFun := I.zeroSimplexOfChart
  left_inv := I.zeroSimplexOfChart_chartOf
  right_inv := I.chartOf_zeroSimplexOfChart

/-- X.R1(d): the selected zero-simplex for a chart has that chart as overlap. -/
theorem overlap_zeroSimplex_eq_chart
    (I : CoverRelativeCechZeroSimplexChartIncidence 𝒰) (i : 𝒰.Index) :
    𝒰.overlap 0 (I.zeroSimplexOfChart i) = 𝒰.chart i :=
  I.overlap_zeroSimplexOfChart_eq_chart i

/--
X.R1(d): if the selected zero-simplex type is too small to distinguish two
charts, no chart-incidence data can exist.
-/
theorem no_incidence_of_subsingleton_zeroSimplex
    [Subsingleton (𝒰.simplex 0)] {i j : 𝒰.Index} (hij : i ≠ j) :
    ¬ Nonempty (CoverRelativeCechZeroSimplexChartIncidence 𝒰) := by
  rintro ⟨I⟩
  apply hij
  calc
    i = I.chartOfZeroSimplex (I.zeroSimplexOfChart i) := by
      exact (I.chartOf_zeroSimplexOfChart i).symm
    _ = I.chartOfZeroSimplex (I.zeroSimplexOfChart j) := by
      rw [Subsingleton.elim (I.zeroSimplexOfChart i) (I.zeroSimplexOfChart j)]
    _ = j := I.chartOf_zeroSimplexOfChart j

end CoverRelativeCechZeroSimplexChartIncidence

/--
X.R1(d): a representative no-go packet for plain covers.

The packet records a plain cover whose selected zero-simplices cannot separate
two chart indices.  The theorem below turns this witness into the statement
that chart incidence is not derivable from the plain cover surface.
-/
structure CoverRelativeCechPlainZeroIncidenceNoGo {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} {S : Site.AATSite A} where
  cover : CoverRelativeCechCover S
  zeroSimplexSubsingleton : Subsingleton (cover.simplex 0)
  leftChart : cover.Index
  rightChart : cover.Index
  left_ne_right : leftChart ≠ rightChart

namespace CoverRelativeCechPlainZeroIncidenceNoGo

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}

/--
X.R1(d): no-go representative for deriving chart incidence from a plain cover.
-/
theorem no_incidence (N : CoverRelativeCechPlainZeroIncidenceNoGo (S := S)) :
    ¬ Nonempty (CoverRelativeCechZeroSimplexChartIncidence N.cover) := by
  letI := N.zeroSimplexSubsingleton
  exact CoverRelativeCechZeroSimplexChartIncidence.no_incidence_of_subsingleton_zeroSimplex
    N.left_ne_right

end CoverRelativeCechPlainZeroIncidenceNoGo

/--
X.R1(d): cover-relative Cech cover data whose zero-simplices are definitionally
the chart indices.

Higher simplices remain selected data.  The split fields keep the `0`-face
maps explicit, because faces from 1-simplices land in chart indices while
higher faces land in the selected higher simplex types.
-/
structure CoverRelativeCechChartIndexedZeroCover {U : AtomCarrier.{u}}
    {A : ArchitectureObject U} (S : Site.AATSite A) where
  base : S.category
  Index : Type u
  chart : Index -> S.category
  inclusion : ∀ i : Index, chart i ⟶ base
  higherSimplex : Nat -> Type u
  higherOverlap : ∀ n : Nat, higherSimplex n -> S.category
  faceZero : Fin 2 -> higherSimplex 0 -> Index
  faceSucc :
    ∀ n : Nat, Fin (n + 3) -> higherSimplex (n + 1) -> higherSimplex n
  faceRestrictionZero :
    ∀ (i : Fin 2) (σ : higherSimplex 0),
      higherOverlap 0 σ ⟶ chart (faceZero i σ)
  faceRestrictionSucc :
    ∀ (n : Nat) (i : Fin (n + 3)) (σ : higherSimplex (n + 1)),
      higherOverlap (n + 1) σ ⟶ higherOverlap n (faceSucc n i σ)

namespace CoverRelativeCechChartIndexedZeroCover

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}

/-- X.R1(d): simplex family with degree zero definitionally equal to charts. -/
def simplex (𝒱 : CoverRelativeCechChartIndexedZeroCover S) : Nat -> Type u
  | 0 => 𝒱.Index
  | n + 1 => 𝒱.higherSimplex n

/-- X.R1(d): overlap family with degree zero definitionally equal to charts. -/
def overlap (𝒱 : CoverRelativeCechChartIndexedZeroCover S) :
    ∀ n : Nat, 𝒱.simplex n -> S.category
  | 0, i => 𝒱.chart i
  | n + 1, σ => 𝒱.higherOverlap n σ

/-- X.R1(d): face maps for the chart-indexed zero cover. -/
def face (𝒱 : CoverRelativeCechChartIndexedZeroCover S) :
    ∀ n : Nat, Fin (n + 2) -> 𝒱.simplex (n + 1) -> 𝒱.simplex n
  | 0, i, σ => 𝒱.faceZero i σ
  | n + 1, i, σ => 𝒱.faceSucc n i σ

/-- X.R1(d): face restriction maps for the chart-indexed zero cover. -/
def faceRestriction (𝒱 : CoverRelativeCechChartIndexedZeroCover S) :
    ∀ (n : Nat) (i : Fin (n + 2)) (σ : 𝒱.simplex (n + 1)),
      𝒱.overlap (n + 1) σ ⟶ 𝒱.overlap n (𝒱.face n i σ)
  | 0, i, σ => 𝒱.faceRestrictionZero i σ
  | n + 1, i, σ => 𝒱.faceRestrictionSucc n i σ

/-- X.R1(d): forget to the existing plain cover-relative Cech cover surface. -/
def toCoverRelativeCechCover (𝒱 : CoverRelativeCechChartIndexedZeroCover S) :
    CoverRelativeCechCover S where
  base := 𝒱.base
  Index := 𝒱.Index
  chart := 𝒱.chart
  inclusion := 𝒱.inclusion
  simplex := 𝒱.simplex
  overlap := 𝒱.overlap
  face := 𝒱.face
  faceRestriction := 𝒱.faceRestriction

/-- X.R1(d): degree-zero simplices are definitionally the chart indices. -/
theorem toCoverRelativeCechCover_simplex_zero
    (𝒱 : CoverRelativeCechChartIndexedZeroCover S) :
    (𝒱.toCoverRelativeCechCover).simplex 0 = 𝒱.Index :=
  rfl

/-- X.R1(d): degree-zero overlaps are definitionally chart objects. -/
theorem toCoverRelativeCechCover_overlap_zero
    (𝒱 : CoverRelativeCechChartIndexedZeroCover S) (i : 𝒱.Index) :
    (𝒱.toCoverRelativeCechCover).overlap 0 i = 𝒱.chart i :=
  rfl

/-- X.R1(d): the chart-indexed cover carries canonical zero-simplex incidence. -/
def zeroSimplexChartIncidence (𝒱 : CoverRelativeCechChartIndexedZeroCover S) :
    CoverRelativeCechZeroSimplexChartIncidence 𝒱.toCoverRelativeCechCover where
  chartOfZeroSimplex := id
  zeroSimplexOfChart := id
  chartOf_zeroSimplexOfChart := fun _ => rfl
  zeroSimplexOfChart_chartOf := fun _ => rfl
  overlap_zeroSimplexOfChart_eq_chart := fun _ => rfl

/--
X.R1(d): canonical incidence on a chart-indexed zero cover identifies the
selected zero-simplex of a chart with that chart.
-/
theorem zeroSimplexChartIncidence_chart
    (𝒱 : CoverRelativeCechChartIndexedZeroCover S) (i : 𝒱.Index) :
    (𝒱.zeroSimplexChartIncidence).chartOfZeroSimplex
      ((𝒱.zeroSimplexChartIncidence).zeroSimplexOfChart i) = i :=
  rfl

end CoverRelativeCechChartIndexedZeroCover

end Cohomology
end AAT.AG
