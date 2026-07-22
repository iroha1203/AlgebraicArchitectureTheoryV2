import Formal.AG.Cohomology.ChartIndexedZeroCover
import Formal.AG.SemanticRepair.AdditiveH1

noncomputable section

namespace AAT.AG
namespace SemanticRepair

open CategoryTheory
open Opposite

universe u v w x r

/-! ## X.§6 atom-generated site and cover-relative Cech bridge -/

/--
X.定理6.1: an atom-generated admissible coverage family generates a cover in
the selected `J_U` Grothendieck topology.
-/
theorem atomGeneratedCoverage_generates_AATGrothendieckTopology
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A}
    {E : ArchitecturalEquationSystem C}
    {Sig : ArchitectureSignature U}
    {R : Site.CoverageRequirements A E Sig}
    {P : Site.ContextOverlapPullback C}
    {base : Site.ContextCategoryObject C}
    (family : Site.AATCoverageFamily R P base) :
    Sieve.generate family.presieve ∈
      Site.AATGrothendieckTopology R P base :=
  Site.AATGrothendieckTopology.generate_mem family

/--
X.定理6.1: the selected topology of an `AATSite` is exactly the generated
atom-coverage topology `J_U`.
-/
theorem selectedAATSiteTopology_eq_atomGeneratedGrothendieckTopology
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    (S : Site.AATSite A) :
    S.topology =
      Site.AATGrothendieckTopology S.requirements S.overlap :=
  Site.AATSite.topology_eq S

/--
X.定義6.3: provenance bridge from a semantic repair cover to the general
cover-relative Cech cover surface.

The fields map selected semantic charts, overlaps, and triple-overlaps into
the selected 0-, 1-, and 2-simplices of the general cover.  The bridge stores
only incidence provenance; it does not store cohomology, zero-class, boundary,
descent, or gluing conclusions.
-/
structure SemanticRepairCoverRelativeCoverBridge
    {P : SemanticAtomProjection.{u, v}}
    (cover : SemanticRepairCover.{u, v, w, x} P)
    {U : AtomCarrier.{r}} {A : ArchitectureObject U}
    (S : Site.AATSite A) where
  coverRelative : Cohomology.CoverRelativeCechCover S
  chartSimplex : cover.CoverChart -> coverRelative.simplex 0
  overlapSimplex :
    (Sigma fun pair : cover.CoverChart × cover.CoverChart =>
      cover.Overlap pair.1 pair.2) -> coverRelative.simplex 1
  tripleSimplex :
    (Sigma fun triple : cover.CoverChart × cover.CoverChart × cover.CoverChart =>
      cover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
        coverRelative.simplex 2

namespace SemanticRepairCover

/-- X.定義6.3: forget the semantic provenance bridge to its selected Cech cover. -/
def toCoverRelativeCechCover
    {P : SemanticAtomProjection.{u, v}}
    {cover : SemanticRepairCover.{u, v, w, x} P}
    {U : AtomCarrier.{r}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    (bridge : SemanticRepairCoverRelativeCoverBridge cover S) :
    Cohomology.CoverRelativeCechCover S :=
  bridge.coverRelative

end SemanticRepairCover

/--
X.定理6.4 negative half: a plain cover with a selected zero-simplex but empty
chart index cannot carry zero-simplex/chart incidence.

This is the representative counterexample packet showing that incidence is
data, not a consequence of the bare `CoverRelativeCechCover` API.
-/
structure EmptyIndexZeroSimplexIncidenceNoGo
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} where
  cover : Cohomology.CoverRelativeCechCover S
  zeroSimplex : cover.simplex 0
  indexEmpty : IsEmpty cover.Index

namespace EmptyIndexZeroSimplexIncidenceNoGo

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}

/--
X.定理6.4 negative half: the empty-index witness refutes existence of
zero-simplex/chart incidence for the selected plain cover.
-/
theorem no_incidence (N : EmptyIndexZeroSimplexIncidenceNoGo (S := S)) :
    ¬ Nonempty (Cohomology.CoverRelativeCechZeroSimplexChartIncidence N.cover) := by
  rintro ⟨I⟩
  exact N.indexEmpty.false (I.chartOfZeroSimplex N.zeroSimplex)

end EmptyIndexZeroSimplexIncidenceNoGo

/--
X.定理6.4 negative half: a bridge-only constructor would also be impossible
when the target cover has empty chart index but the semantic cover has a chart.
-/
theorem no_constructor_from_coverBridge_without_zeroSimplexChartIncidence
    {P : SemanticAtomProjection.{u, v}}
    {semanticCover : SemanticRepairCover.{u, v, w, x} P}
    {U : AtomCarrier.{r}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    (bridge : SemanticRepairCoverRelativeCoverBridge semanticCover S)
    (chart : semanticCover.CoverChart)
    (hIndex :
      IsEmpty (SemanticRepairCover.toCoverRelativeCechCover bridge).Index)
    (zeroSimplexChartIncidenceConstructor :
      (bridgeInput : SemanticRepairCoverRelativeCoverBridge semanticCover S) ->
        Cohomology.CoverRelativeCechZeroSimplexChartIncidence
          (SemanticRepairCover.toCoverRelativeCechCover bridgeInput)) :
    False := by
  let incidence := zeroSimplexChartIncidenceConstructor bridge
  exact hIndex.false (incidence.chartOfZeroSimplex (bridge.chartSimplex chart))

/--
X.定理6.4 positive half: chart-indexed zero covers generate the missing
zero-simplex/chart incidence data.
-/
theorem chartIndexedZeroCover_constructs_zeroSimplexChartIncidence
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    (charted : Cohomology.CoverRelativeCechChartIndexedZeroCover S) :
    Nonempty
      (Cohomology.CoverRelativeCechZeroSimplexChartIncidence
        charted.toCoverRelativeCechCover) :=
  ⟨charted.zeroSimplexChartIncidence⟩

/--
X.定理6.5: the semantic repair cover nerve is a typed restatement of the
selected pairwise-overlap and triple-overlap provenance.
-/
theorem coverNerve_typedComponent_adequacy
    {P : SemanticAtomProjection.{u, v}}
    (cover : SemanticRepairCover.{u, v, w, x} P) :
    (forall edge : (cover.toCoverNerve).EdgeComponent,
      exists pair : cover.CoverChart × cover.CoverChart,
      exists overlap : cover.Overlap pair.1 pair.2,
        edge = Sigma.mk pair overlap /\
          (cover.toCoverNerve).edgeLeft edge = pair.1 /\
          (cover.toCoverNerve).edgeRight edge = pair.2) /\
      (forall face : (cover.toCoverNerve).FaceComponent,
        exists tripleIndex : cover.CoverChart × cover.CoverChart × cover.CoverChart,
        exists triple :
          cover.TripleOverlap tripleIndex.1 tripleIndex.2.1 tripleIndex.2.2,
          face = Sigma.mk tripleIndex triple /\
            (cover.toCoverNerve).faceEdge0 face =
              Sigma.mk (tripleIndex.1, tripleIndex.2.1)
                (cover.tripleEdge01 triple) /\
            (cover.toCoverNerve).faceEdge1 face =
              Sigma.mk (tripleIndex.2.1, tripleIndex.2.2)
                (cover.tripleEdge12 triple) /\
            (cover.toCoverNerve).faceEdge2 face =
              Sigma.mk (tripleIndex.1, tripleIndex.2.2)
                (cover.tripleEdge02 triple)) := by
  constructor
  · intro edge
    rcases edge with ⟨⟨left, right⟩, overlap⟩
    exact ⟨(left, right), overlap, rfl, rfl, rfl⟩
  · intro face
    rcases face with ⟨⟨i, j, k⟩, triple⟩
    exact ⟨(i, j, k), triple, rfl, rfl, rfl, rfl⟩

/--
X.定理6.6: a sheaf condition plus selected cover membership derives the
per-cover sheaf condition, descent, and unique global gluing section.
-/
theorem aatSheafCondition_coverMembership_descent_effectiveGluing
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {F : Site.AATPresheaf S}
    (hSheaf : Site.AATSheafCondition S F)
    {base : S.category} (cover : Sieve base)
    (hcover : cover ∈ S.topology base)
    (data : Site.AATGluingData S F cover) :
    Site.AATSheafConditionFor S F cover /\
      Site.AATDescent S F cover /\
      ∃! globalSection : F.obj (op base),
        Site.AATGlobalSectionRealizes data globalSection := by
  let hFor := Site.AATSheafCondition.cover hSheaf cover hcover
  let hDescent := Site.AATSheafConditionFor.descent hFor
  exact ⟨hFor, hDescent, hDescent data⟩

end SemanticRepair
end AAT.AG
