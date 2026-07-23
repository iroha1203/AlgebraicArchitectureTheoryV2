import Formal.AG.Cohomology.FinitePosetStandardComplex
import Formal.AG.SemanticRepair.SagaComparison

noncomputable section

namespace AAT.AG
namespace SemanticRepair

open CategoryTheory
open Opposite

universe u v w x y z r q t

/-!
This module is reserved for the body-side distillation of the generated-pair
law-equation route.  Research-loop declarations must be distilled into body
definitions before they can become theorem-7.5 evidence on the canonical AG
surface.
-/

/-! ## Body-side translation of the Research complete support -/

/--
Body-side translation of the Research `completeRepairSupport`.

In the Research loop the successful faithfulness-discharge route uses the
complete refined repair support.  The AG body version is the same mathematical
content in the abstract `SemanticAtomProjection` vocabulary: every semantic atom
of the selected projection is supported.
-/
def lawEquationCompleteRepairSupport
    (P : SemanticAtomProjection.{u, v}) : P.Support :=
  fun _atom => True

/--
Complete support semantically closes every residual atom.  This is the AG-body
counterpart of the Research complete-support closure theorem; the general
form over an arbitrary full support is `semanticRepairClosed_top` in
`GluingComplex.lean`.
-/
theorem lawEquationCompleteRepairSupport_semanticRepairClosed
    (P : SemanticAtomProjection.{u, v})
    (cover : FiniteSemanticRepairCoverDatum.{v, w, x} P.Component) :
    SemanticRepairClosed P cover (lawEquationCompleteRepairSupport P) := by
  intro _atom _hresidual
  trivial

/--
Complete support decomposes into residual-component coverage and residual
faithfulness, using the same closure decomposition theorem as the Research
route.
-/
theorem lawEquationCompleteRepairSupport_componentCoverage_and_faithfulness
    (P : SemanticAtomProjection.{u, v})
    (cover : FiniteSemanticRepairCoverDatum.{v, w, x} P.Component) :
    ResidualComponentCoveredSupport P cover
        (lawEquationCompleteRepairSupport P) /\
      ResidualComponentFaithfulSupport P cover
        (lawEquationCompleteRepairSupport P) :=
  (semanticRepairClosed_iff_residualComponentCovered_and_faithful).mp
    (lawEquationCompleteRepairSupport_semanticRepairClosed P cover)

/-- Body-side cover bridge for the law-equation generated-pair route. -/
def lawEquationCoverBridge
    {P : SemanticAtomProjection.{u, v}}
    (semanticCover : SemanticRepairCover.{u, v, w, x} P)
    {U : AtomCarrier.{r}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    (coverRel : Cohomology.CoverRelativeCechCover S)
    (chartSimplex : semanticCover.CoverChart -> coverRel.simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) -> coverRel.simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          coverRel.simplex 2) :
    SemanticRepairCoverRelativeCoverBridge semanticCover S where
  coverRelative := coverRel
  chartSimplex := chartSimplex
  overlapSimplex := overlapSimplex
  tripleSimplex := tripleSimplex

/--
Body-side current input surface for the generated-pair route.

At the AG-body level this is the existing theorem-6 cover bridge typed over the
selected law-equation cover-relative Cech cover.  It deliberately returns the
existing body bridge type instead of importing the research-only G-06 surface.

Role split: this thin `def` only re-types the cover bridge; it carries no
sheaf-descent data.  The rich input surface that the theorem-7.5 routes
consume is the structure `LawEquationGeneratedCurrentG06InputSurface`, which
additionally records the selected cover, its membership, the sheaf condition,
and the descent object.
-/
def lawEquationCurrentG06InputSurface
    {P : SemanticAtomProjection.{u, v}}
    (semanticCover : SemanticRepairCover.{u, v, w, x} P)
    {U : AtomCarrier.{r}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    (coverRel : Cohomology.CoverRelativeCechCover S)
    (chartSimplex : semanticCover.CoverChart -> coverRel.simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) -> coverRel.simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          coverRel.simplex 2) :
    SemanticRepairCoverRelativeCoverBridge semanticCover S :=
  lawEquationCoverBridge semanticCover coverRel chartSimplex overlapSimplex
    tripleSimplex

/-! ## Cover-relative generated additive surface -/

/--
Build the bounded semantic Cech data directly from a cover-relative Cech
complex.  The degree objects and differentials are not supplied independently:
`C0`, `C1`, `C2`, `delta0`, and `delta1` are exactly `K.Cn 0`, `K.Cn 1`,
`K.Cn 2`, `K.d 0`, and `K.d 1`.

Scaffolding: this builder requires `Fintype (K.Cn 0)` / `Fintype (K.Cn 1)`,
premises absent from theorem 7.5.  It supports the bounded `from*` routes
only; the canonical theorem-7.5 entry-point is the finite-free
`lawEquation_constructs_groundedComparisonPacket_finiteFree`.
-/
def coverRelativeCechDataOfComplex
    {P : SemanticAtomProjection.{u, v}}
    (semanticCover : SemanticRepairCover.{u, v, w, x} P)
    {U : AtomCarrier.{x}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    (K : Cohomology.CoverRelativeCechComplex coverRel Ob)
    (c0Finite : Fintype (K.Cn 0)) (c1Finite : Fintype (K.Cn 1))
    (zero1 residual : K.Cn 1)
    (hzero1 : letI := K.cochainAddCommGroup 2; K.d 1 zero1 = 0)
    (hresidual : letI := K.cochainAddCommGroup 2; K.d 1 residual = 0) :
    SemanticRepairCoverCechData.{u, v, w, x, x, x} semanticCover where
  C0 := K.Cn 0
  C1 := K.Cn 1
  C2 := K.Cn 2
  c0Finite := c0Finite
  c1Finite := c1Finite
  zero1 := zero1
  zero2 := by
    letI := K.cochainAddCommGroup 2
    exact 0
  delta0 := K.d 0
  delta1 := K.d 1
  residual := residual
  zero1_cocycle := hzero1
  delta1_delta0_eq_zero := by
    intro primitive
    exact K.differential_comp 0 primitive
  residual_cocycle := hresidual

/--
Additive laws for the bounded Cech data generated from a cover-relative
complex.  The additive structure and differential laws come from `K`.

Scaffolding: inherits the `Fintype` premises of
`coverRelativeCechDataOfComplex`, which are absent from theorem 7.5; the
canonical theorem-7.5 entry-point is the finite-free
`lawEquation_constructs_groundedComparisonPacket_finiteFree`.
-/
def coverRelativeAdditiveCechDataOfComplex
    {P : SemanticAtomProjection.{u, v}}
    (semanticCover : SemanticRepairCover.{u, v, w, x} P)
    {U : AtomCarrier.{x}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    (K : Cohomology.CoverRelativeCechComplex coverRel Ob)
    (c0Finite : Fintype (K.Cn 0)) (c1Finite : Fintype (K.Cn 1))
    (zero1 residual : K.Cn 1)
    (hzero1 : letI := K.cochainAddCommGroup 2; K.d 1 zero1 = 0)
    (hresidual : letI := K.cochainAddCommGroup 2; K.d 1 residual = 0)
    (hzero1_eq_zero : letI := K.cochainAddCommGroup 1; zero1 = 0) :
    SemanticRepairAdditiveCechH1Data
      (coverRelativeCechDataOfComplex semanticCover K c0Finite c1Finite
        zero1 residual hzero1 hresidual) where
  c0AddCommGroup := K.cochainAddCommGroup 0
  c1AddCommGroup := K.cochainAddCommGroup 1
  zero1_eq_zero := hzero1_eq_zero
  delta0_zero := by
    letI := K.cochainAddCommGroup 0
    letI := K.cochainAddCommGroup 1
    exact (K.d 0).map_zero
  delta0_add := by
    letI := K.cochainAddCommGroup 0
    letI := K.cochainAddCommGroup 1
    intro left right
    exact (K.d 0).map_add left right
  delta0_neg := by
    letI := K.cochainAddCommGroup 0
    letI := K.cochainAddCommGroup 1
    intro primitive
    exact (K.d 0).map_neg primitive

/--
Generated boundary-relation data whose Cech degrees and differentials are
read from the selected cover-relative complex.

Scaffolding: inherits the `Fintype` premises of
`coverRelativeCechDataOfComplex`, which are absent from theorem 7.5; the
canonical theorem-7.5 entry-point is the finite-free
`lawEquation_constructs_groundedComparisonPacket_finiteFree`.
-/
def coverRelativeBoundaryAdditiveDataOfComplex
    {P : SemanticAtomProjection.{u, v}}
    (semanticCover : SemanticRepairCover.{u, v, w, x} P)
    {U : AtomCarrier.{x}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    (K : Cohomology.CoverRelativeCechComplex coverRel Ob)
    (c0Finite : Fintype (K.Cn 0)) (c1Finite : Fintype (K.Cn 1))
    (zero1 residual : K.Cn 1)
    (hzero1 : letI := K.cochainAddCommGroup 2; K.d 1 zero1 = 0)
    (hresidual : letI := K.cochainAddCommGroup 2; K.d 1 residual = 0)
    (hzero1_eq_zero : letI := K.cochainAddCommGroup 1; zero1 = 0)
    (supportOf : K.Cn 0 -> P.Support)
    (component_covered_of_boundary :
      forall primitive,
        K.d 0 primitive = residual ->
          ResidualComponentCoveredSupport P semanticCover.baseCover
            (supportOf primitive))
    (component_faithful_of_boundary :
      forall primitive,
        K.d 0 primitive = residual ->
          ResidualComponentFaithfulSupport P semanticCover.baseCover
            (supportOf primitive)) :
    SemanticRepairCoverH1BoundaryRelationAdditiveData P where
  boundaryRelation :=
    { cover := semanticCover
      cech :=
        coverRelativeCechDataOfComplex semanticCover K c0Finite c1Finite
          zero1 residual hzero1 hresidual
      supportOf := supportOf
      component_covered_of_boundary := component_covered_of_boundary
      component_faithful_of_boundary := component_faithful_of_boundary }
  additive :=
    coverRelativeAdditiveCechDataOfComplex semanticCover K c0Finite c1Finite
      zero1 residual hzero1 hresidual hzero1_eq_zero

/--
When the selected residual is generated as an actual cover-relative
coboundary `K.d 0 primitive`, the bounded additive H1 class is zero.  This is
the body-side form of the research route's generated residual boundary
witness; no H1-zero certificate is accepted as an input.

Scaffolding: carries the `Fintype` cochain premises of the bounded surface,
absent from theorem 7.5.
-/
theorem coverRelativeGeneratedBoundary_additiveH1ZeroOfPrimitive
    {P : SemanticAtomProjection.{u, v}}
    (semanticCover : SemanticRepairCover.{u, v, w, x} P)
    {U : AtomCarrier.{x}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    (K : Cohomology.CoverRelativeCechComplex coverRel Ob)
    (c0Finite : Fintype (K.Cn 0)) (c1Finite : Fintype (K.Cn 1))
    (zero1 : K.Cn 1)
    (primitive : K.Cn 0)
    (hzero1 : letI := K.cochainAddCommGroup 2; K.d 1 zero1 = 0)
    (hzero1_eq_zero : letI := K.cochainAddCommGroup 1; zero1 = 0)
    (supportOf : K.Cn 0 -> P.Support)
    (component_covered_of_boundary :
      forall boundaryPrimitive,
        K.d 0 boundaryPrimitive = K.d 0 primitive ->
          ResidualComponentCoveredSupport P semanticCover.baseCover
            (supportOf boundaryPrimitive))
    (component_faithful_of_boundary :
      forall boundaryPrimitive,
        K.d 0 boundaryPrimitive = K.d 0 primitive ->
          ResidualComponentFaithfulSupport P semanticCover.baseCover
            (supportOf boundaryPrimitive)) :
    (coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
      zero1 (K.d 0 primitive) hzero1 (K.differential_comp 0 primitive)
      hzero1_eq_zero supportOf component_covered_of_boundary
      component_faithful_of_boundary).toAdditiveCechH1Data.H1Zero := by
  let data :=
    coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
      zero1 (K.d 0 primitive) hzero1 (K.differential_comp 0 primitive)
      hzero1_eq_zero supportOf component_covered_of_boundary
      component_faithful_of_boundary
  exact
    (semanticRepairAdditiveH1Zero_iff_boundary
      data.toAdditiveCechH1Data).2 ⟨primitive, rfl⟩

/--
The same generated boundary witness, read on the theorem-7.2 finite-free H1
surface.

Scaffolding: carries the `Fintype` cochain premises of the bounded surface,
absent from theorem 7.5.
-/
theorem coverRelativeGeneratedBoundary_surfaceH1ZeroOfPrimitive
    {P : SemanticAtomProjection.{u, v}}
    (semanticCover : SemanticRepairCover.{u, v, w, x} P)
    {U : AtomCarrier.{x}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    (K : Cohomology.CoverRelativeCechComplex coverRel Ob)
    (c0Finite : Fintype (K.Cn 0)) (c1Finite : Fintype (K.Cn 1))
    (zero1 : K.Cn 1)
    (primitive : K.Cn 0)
    (hzero1 : letI := K.cochainAddCommGroup 2; K.d 1 zero1 = 0)
    (hzero1_eq_zero : letI := K.cochainAddCommGroup 1; zero1 = 0)
    (supportOf : K.Cn 0 -> P.Support)
    (component_covered_of_boundary :
      forall boundaryPrimitive,
        K.d 0 boundaryPrimitive = K.d 0 primitive ->
          ResidualComponentCoveredSupport P semanticCover.baseCover
            (supportOf boundaryPrimitive))
    (component_faithful_of_boundary :
      forall boundaryPrimitive,
        K.d 0 boundaryPrimitive = K.d 0 primitive ->
          ResidualComponentFaithfulSupport P semanticCover.baseCover
            (supportOf boundaryPrimitive)) :
    (coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
      zero1 (K.d 0 primitive) hzero1 (K.differential_comp 0 primitive)
      hzero1_eq_zero supportOf component_covered_of_boundary
      component_faithful_of_boundary).toAdditiveH1Surface.H1Zero := by
  let data :=
    coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
      zero1 (K.d 0 primitive) hzero1 (K.differential_comp 0 primitive)
      hzero1_eq_zero supportOf component_covered_of_boundary
      component_faithful_of_boundary
  exact
    (boundedAdditiveH1Zero_iff_surfaceH1Zero data).1
      (coverRelativeGeneratedBoundary_additiveH1ZeroOfPrimitive
        semanticCover K c0Finite c1Finite zero1 primitive hzero1
        hzero1_eq_zero supportOf component_covered_of_boundary
        component_faithful_of_boundary)

/--
Identity cochain realization for boundary-additive data generated from the
same cover-relative complex.  This constructs the comparison supply from
`K.Cn` and `K.d`; it is not an externally supplied realization packet.

Scaffolding: inherits the `Fintype` premises of
`coverRelativeCechDataOfComplex`, which are absent from theorem 7.5.
-/
def coverRelativeIdentityCochainRealizationOfComplex
    {P : SemanticAtomProjection.{u, v}}
    (semanticCover : SemanticRepairCover.{u, v, w, x} P)
    {U : AtomCarrier.{x}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    (K : Cohomology.CoverRelativeCechComplex coverRel Ob)
    (c0Finite : Fintype (K.Cn 0)) (c1Finite : Fintype (K.Cn 1))
    (zero1 residual : K.Cn 1)
    (hzero1 : letI := K.cochainAddCommGroup 2; K.d 1 zero1 = 0)
    (hresidual : letI := K.cochainAddCommGroup 2; K.d 1 residual = 0)
    (hzero1_eq_zero : letI := K.cochainAddCommGroup 1; zero1 = 0)
    (supportOf : K.Cn 0 -> P.Support)
    (component_covered_of_boundary :
      forall primitive,
        K.d 0 primitive = residual ->
          ResidualComponentCoveredSupport P semanticCover.baseCover
            (supportOf primitive))
    (component_faithful_of_boundary :
      forall primitive,
        K.d 0 primitive = residual ->
          ResidualComponentFaithfulSupport P semanticCover.baseCover
            (supportOf primitive)) :
    SemanticRepairCoverRelativeCochainRealization
      (coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
        zero1 residual hzero1 hresidual hzero1_eq_zero supportOf
        component_covered_of_boundary component_faithful_of_boundary).toAdditiveH1Surface
      K where
  c0Equiv := AddEquiv.refl (K.Cn 0)
  c1Equiv := AddEquiv.refl (K.Cn 1)
  c2Equiv := Equiv.refl (K.Cn 2)
  c2Equiv_zero := rfl
  c2Equiv_symm_zero := rfl
  d0_to := by
    intro primitive
    rfl
  d0_from := by
    intro primitive
    rfl
  d1_to := by
    intro cochain
    rfl
  d1_from := by
    intro cochain
    rfl

/-! ## Research-conjunct-preserving AG body packets -/

/--
AG-body translation of the Research `CurrentG06InputSurface`.

Unlike the older body bridge, this surface retains the generated
cover-relative complex, generated coefficient presheaf, selected cover,
selected cover membership, sheaf condition, and descent object.

Role split: this structure is the rich input surface consumed by the
theorem-7.5 routes.  The thin `lawEquationCurrentG06InputSurface` `def` above
only re-types the cover bridge; it remains in use as an internal cover-bridge
component of builders and route proofs, but it is not an alternative
theorem-7.5 input surface.
-/
structure LawEquationGeneratedCurrentG06InputSurface
    {P : SemanticAtomProjection.{u, v}}
    (semanticCover : SemanticRepairCover.{u, v, w, x} P)
    {U : AtomCarrier.{r}} {A : ArchitectureObject U}
    (S : Site.AATSite A)
    (F : Site.AATPresheaf S)
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    (K : Cohomology.CoverRelativeCechComplex coverRel Ob) where
  /-- Bridge from semantic charts to the generated cover-relative simplices. -/
  coverBridge : SemanticRepairCoverRelativeCoverBridge semanticCover S
  /-- Base object on which the selected cover is generated. -/
  coverBase : S.category
  /-- Cover selected for sheaf descent. -/
  selectedCover : Sieve coverBase
  selectedCover_mem : selectedCover ∈ S.topology coverBase
  sheafCondition : Site.AATSheafCondition S F
  descent : Site.AATDescent S F selectedCover

/-- Construct the AG-body current G-06 surface from the selected cover data. -/
def lawEquationGeneratedCurrentG06InputSurface
    {P : SemanticAtomProjection.{u, v}}
    (semanticCover : SemanticRepairCover.{u, v, w, x} P)
    {U : AtomCarrier.{r}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {F : Site.AATPresheaf S}
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    (K : Cohomology.CoverRelativeCechComplex coverRel Ob)
    (chartSimplex : semanticCover.CoverChart -> coverRel.simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) -> coverRel.simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          coverRel.simplex 2)
    {base : S.category}
    (cover : Sieve base)
    (sheafCondition : Site.AATSheafCondition S F)
    (cover_mem : cover ∈ S.topology base) :
    LawEquationGeneratedCurrentG06InputSurface semanticCover S F K where
  coverBridge :=
    lawEquationCurrentG06InputSurface semanticCover coverRel chartSimplex
      overlapSimplex tripleSimplex
  coverBase := base
  selectedCover := cover
  selectedCover_mem := cover_mem
  sheafCondition := sheafCondition
  descent :=
    Site.AATSheafConditionFor.descent
      (Site.AATSheafCondition.cover sheafCondition cover cover_mem)

/--
Finite-poset generated-cover form of the AG-body current G-06 surface.

This is the body translation of the Research surface fields
`coverBase`, `selectedCover`, and `selectedCover_mem`: the selected cover is
not supplied as an arbitrary sieve, but generated from the finite-poset cover
family.
-/
def lawEquationGeneratedCurrentG06InputSurfaceOfFinitePosetGeometry
    {P : SemanticAtomProjection.{u, v}}
    (semanticCover : SemanticRepairCover.{u, v, w, x} P)
    {U : AtomCarrier.{r}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {F : Site.AATPresheaf S}
    (geometry : Site.FinitePosetCoverGeometry S)
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    (K : Cohomology.CoverRelativeCechComplex coverRel Ob)
    (chartSimplex : semanticCover.CoverChart -> coverRel.simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) -> coverRel.simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          coverRel.simplex 2)
    (sheafCondition : Site.AATSheafCondition S F) :
    LawEquationGeneratedCurrentG06InputSurface semanticCover S F K :=
  lawEquationGeneratedCurrentG06InputSurface semanticCover K
    chartSimplex overlapSimplex tripleSimplex
    (Sieve.generate geometry.cover.presieve) sheafCondition
    (Site.AATGrothendieckTopology.generate_mem geometry.cover)

theorem lawEquationGeneratedCurrentG06InputSurfaceOfFinitePosetGeometry_selectedCover
    {P : SemanticAtomProjection.{u, v}}
    (semanticCover : SemanticRepairCover.{u, v, w, x} P)
    {U : AtomCarrier.{r}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {F : Site.AATPresheaf S}
    (geometry : Site.FinitePosetCoverGeometry S)
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    (K : Cohomology.CoverRelativeCechComplex coverRel Ob)
    (chartSimplex : semanticCover.CoverChart -> coverRel.simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) -> coverRel.simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          coverRel.simplex 2)
    (sheafCondition : Site.AATSheafCondition S F) :
    (lawEquationGeneratedCurrentG06InputSurfaceOfFinitePosetGeometry
      semanticCover geometry K chartSimplex overlapSimplex tripleSimplex
      sheafCondition).selectedCover =
      Sieve.generate geometry.cover.presieve :=
  rfl

/--
AG-body source data corresponding to the Research
`toCoverRelativeBaseRestrictionSource` lower geometry.

The structure records which displayed law-equation chart is read by each
degree-`0` Cech simplex, the map from the simplex overlap to the selected cover
base, and the restriction map from the same overlap to that chart.  It stores
no source section, realization equality, evaluator, arrow-compatibility law,
`sourceC0CechZero`, residual statement, or H1 conclusion.
-/
structure LawEquationBodyCechSource
    {U : AtomCarrier.{u}}
    {A : ArchitectureObject U}
    {S : Site.AATSite.{u} A}
    {E : ArchitecturalEquationSystem S.contextPreorder}
    (D : LawAlgebra.LawEquationDefectSource.{u} E)
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    (_K : Cohomology.CoverRelativeCechComplex coverRel Ob) where
  /-- Displayed law-equation chart read by a degree-zero simplex. -/
  chartOf : coverRel.simplex 0 -> D.Chart
  /-- Map from the displayed chart to the selected cover base. -/
  chartToBase :
    (sigma : coverRel.simplex 0) ->
      D.chart (chartOf sigma) ⟶ coverRel.base
  /-- Restriction from the simplex overlap to its displayed chart. -/
  restriction :
    forall sigma : coverRel.simplex 0,
      coverRel.overlap 0 sigma ⟶ D.chart (chartOf sigma)

namespace LawEquationBodyCechSource

variable {U : AtomCarrier.{u}}
variable {A : ArchitectureObject U}
variable {S : Site.AATSite.{u} A}
variable {E : ArchitecturalEquationSystem S.contextPreorder}
variable {D : LawAlgebra.LawEquationDefectSource.{u} E}
variable {coverRel : Cohomology.CoverRelativeCechCover S}
variable {sheafCondition :
  Site.AATSheafCondition S E.obstructionQuotientPresheaf}
variable {K : Cohomology.CoverRelativeCechComplex coverRel
  (Cohomology.ObstructionSheaf.ofAddCommGrpValued
    E.obstructionQuotientCoefficient sheafCondition)}

/-!
The base-restriction source is kept separate from the displayed source.  This
prevents the degree-`0` primitive from being defined as the displayed
interpretation that it is later required to realize.
-/
/-- Independent section over the cover base used to generate a Cech source. -/
structure LawEquationBodyBaseRestrictionSource
    (source : LawEquationBodyCechSource D K) where
  /-- Section restricted along the body source maps. -/
  sourceSection :
    E.ObstructionQuotient coverRel.base

namespace LawEquationBodyBaseRestrictionSource

/-- Restrict the independently supplied base section to every selected overlap. -/
def toPrimitive
    {source : LawEquationBodyCechSource D K}
    (baseSource : LawEquationBodyBaseRestrictionSource source) : K.Cn 0 :=
  fun sigma =>
    E.obstructionQuotientPresheaf.map
      (source.restriction sigma ≫ source.chartToBase sigma).op
      baseSource.sourceSection

end LawEquationBodyBaseRestrictionSource

/-- The overlap-to-base map factors through its displayed chart. -/
def zeroSimplexToBase
    (source : LawEquationBodyCechSource D K)
    (sigma : coverRel.simplex 0) :
    coverRel.overlap 0 sigma ⟶ coverRel.base :=
  source.restriction sigma ≫ source.chartToBase sigma

/-- The law-equation constructor selects the zero base section. -/
def toBaseRestrictionSource
    (source : LawEquationBodyCechSource D K) :
    LawEquationBodyBaseRestrictionSource source where
  sourceSection := (0 : E.ObstructionQuotient coverRel.base)

/--
The body source primitive generated by restricting the zero base section.

This is intentionally independent of `D.interpret`: agreement with the
displayed interpretations is a theorem below, not a definitional equality.
-/
def toPrimitive (source : LawEquationBodyCechSource D K) : K.Cn 0 :=
  source.toBaseRestrictionSource.toPrimitive

/-- The displayed interpretation restricted to a selected degree-`0` overlap. -/
def restrictedDisplayedInterpretation
    (source : LawEquationBodyCechSource D K)
    (sigma : coverRel.simplex 0) :=
  E.obstructionQuotientPresheaf.map
    (source.restriction sigma).op
    (D.interpret (source.chartOf sigma))

/-- Canonical displayed source-C0 cochain used by the actual Cech-zero claim. -/
def displayedSourceC0 (source : LawEquationBodyCechSource D K) : K.Cn 0 :=
  fun sigma => source.restrictedDisplayedInterpretation sigma

/-- Research conjunct 1 at the selected degree-`0` overlaps. -/
def DisplayedInterpretationRealization
    (source : LawEquationBodyCechSource D K) : Prop :=
  forall sigma : coverRel.simplex 0,
    source.toPrimitive sigma = source.displayedSourceC0 sigma

/--
Body translation of Research
`baseRestrictionSourcePreservesDisplayedInterpretation` for a selected
base-restriction source.
-/
def BaseRestrictionSourcePreservesDisplayedInterpretation
    (source : LawEquationBodyCechSource D K)
    (baseSource : LawEquationBodyBaseRestrictionSource source) : Prop :=
  forall sigma : coverRel.simplex 0,
    E.obstructionQuotientPresheaf.map
        (source.chartToBase sigma).op baseSource.sourceSection =
      D.interpret (source.chartOf sigma)

/--
Body translation of Research `commonRestrictionRealization`: some independent
base-restriction source realizes all displayed chart sections.
-/
def CommonRestrictionRealization
    (source : LawEquationBodyCechSource D K) : Prop :=
  Exists fun baseSource : LawEquationBodyBaseRestrictionSource source =>
    source.BaseRestrictionSourcePreservesDisplayedInterpretation baseSource

/-- Body translation of Research `arrowCompatibilityLaw` on common refinements. -/
def ArrowCompatibilityLaw
    (source : LawEquationBodyCechSource D K) : Prop :=
  CategoryTheory.Presieve.Arrows.Compatible
    E.obstructionQuotientPresheaf source.chartToBase
      (fun sigma => D.interpret (source.chartOf sigma))

/--
Body translation of the Research restriction-level law evaluator.

For every pair of displayed charts and every common refinement, supported
required laws that hold on the two local readings evaluate to equality of the
two restricted obstruction sections.
-/
def DisplayedRequiredLawRestrictionEvaluator
    (source : LawEquationBodyCechSource D K) : Prop :=
  forall (sigma tau : coverRel.simplex 0) {Z : S.category}
      (gSigma : Z ⟶ D.chart (source.chartOf sigma))
      (gTau : Z ⟶ D.chart (source.chartOf tau)),
    gSigma ≫ source.chartToBase sigma =
        gTau ≫ source.chartToBase tau ->
      forall (lawIndexSigma lawIndexTau : E.Index),
        lawIndexSigma ∈
            D.lawSupport (source.chartOf sigma)
              (D.input (source.chartOf sigma)) ->
          lawIndexTau ∈
              D.lawSupport (source.chartOf tau)
                (D.input (source.chartOf tau)) ->
            E.Required lawIndexSigma ->
              E.Required lawIndexTau ->
                E.EquationHolds lawIndexSigma
                    (D.objectOfLocalInput (source.chartOf sigma)
                      (D.input (source.chartOf sigma))) ->
                  E.EquationHolds lawIndexTau
                      (D.objectOfLocalInput (source.chartOf tau)
                        (D.input (source.chartOf tau))) ->
                    E.obstructionQuotientPresheaf.map gSigma.op
                        (D.interpret (source.chartOf sigma)) =
                      E.obstructionQuotientPresheaf.map gTau.op
                        (D.interpret (source.chartOf tau))

  /-- Pointwise law reading below the actual Cech differential-zero claim. -/
  def SourceC0PointwiseZero
    (source : LawEquationBodyCechSource D K) : Prop :=
  source.DisplayedInterpretationRealization ∧
    GeneratedSourceC0PointwiseZero D

  /-- Body translation of Research `sourceC0CechZero`: actual differential zero. -/
  def SourceC0CechZero
      (source : LawEquationBodyCechSource D K) : Prop :=
    letI := K.cochainAddCommGroup 1
    K.d 0 source.displayedSourceC0 = 0

  /-- Combined pointwise and actual differential-zero package for generated Cech routes. -/
  def SourceC0GeneratedCechZero
      (source : LawEquationBodyCechSource D K) : Prop :=
    source.SourceC0PointwiseZero ∧ source.SourceC0CechZero

theorem displayedRequiredLawsHoldOn_constructs_baseRestrictionSourcePreservesDisplayedInterpretation
    (source : LawEquationBodyCechSource D K)
    (hholds : D.DisplayedRequiredLawsHoldOn) :
    source.BaseRestrictionSourcePreservesDisplayedInterpretation
      source.toBaseRestrictionSource := by
  intro sigma
  dsimp [toBaseRestrictionSource]
  rw [D.displayedRequiredLawsHoldOn_constructs_interpret_eq_zero hholds
    (source.chartOf sigma)]
  exact
    (E.obstructionQuotientCoefficient.map
      (source.chartToBase sigma).op).hom.map_zero

theorem baseRestrictionSourcePreservesDisplayedInterpretation_constructs_commonRestrictionRealization
    (source : LawEquationBodyCechSource D K)
    (hpreserves :
      source.BaseRestrictionSourcePreservesDisplayedInterpretation
        source.toBaseRestrictionSource) :
    source.CommonRestrictionRealization :=
  ⟨source.toBaseRestrictionSource, hpreserves⟩

theorem commonRestrictionRealization_constructs_arrowCompatibilityLaw
    (source : LawEquationBodyCechSource D K)
    (hrealized : source.CommonRestrictionRealization) :
    source.ArrowCompatibilityLaw := by
  rcases hrealized with ⟨baseSource, hpreserves⟩
  have hcompatible :=
    (CategoryTheory.Presieve.Arrows.toCompatible
      E.obstructionQuotientPresheaf
      source.chartToBase baseSource.sourceSection).property
  intro sigma tau Z gSigma gTau hcomm
  change
    E.obstructionQuotientPresheaf.map gSigma.op
        (D.interpret (source.chartOf sigma)) =
      E.obstructionQuotientPresheaf.map gTau.op
        (D.interpret (source.chartOf tau))
  rw [← hpreserves sigma, ← hpreserves tau]
  exact hcompatible sigma tau Z gSigma gTau hcomm

/-- A common base-section realization constructs the restriction-level evaluator. -/
theorem commonRestrictionRealization_constructs_displayedRequiredLawRestrictionEvaluator
    (source : LawEquationBodyCechSource D K)
    (hrealized : source.CommonRestrictionRealization) :
    source.DisplayedRequiredLawRestrictionEvaluator := by
  rcases hrealized with ⟨baseSource, hpreserves⟩
  have hcompatible :=
    (CategoryTheory.Presieve.Arrows.toCompatible
      E.obstructionQuotientPresheaf
      source.chartToBase baseSource.sourceSection).property
  intro sigma tau Z gSigma gTau hcomm
    _lawIndexSigma _lawIndexTau _hmemSigma _hmemTau
    _hrequiredSigma _hrequiredTau _hholdsSigma _hholdsTau
  rw [← hpreserves sigma, ← hpreserves tau]
  exact hcompatible sigma tau Z gSigma gTau hcomm

theorem displayedRequiredLawsHoldOn_constructs_commonRestrictionRealization
    (source : LawEquationBodyCechSource D K)
    (hholds : D.DisplayedRequiredLawsHoldOn) :
    source.CommonRestrictionRealization :=
  source.baseRestrictionSourcePreservesDisplayedInterpretation_constructs_commonRestrictionRealization
    (source.displayedRequiredLawsHoldOn_constructs_baseRestrictionSourcePreservesDisplayedInterpretation
      hholds)

/-- Displayed law fulfillment constructs the restriction-level evaluator through R1. -/
theorem displayedRequiredLawsHoldOn_constructs_displayedRequiredLawRestrictionEvaluator
    (source : LawEquationBodyCechSource D K)
    (hholds : D.DisplayedRequiredLawsHoldOn) :
    source.DisplayedRequiredLawRestrictionEvaluator :=
  source.commonRestrictionRealization_constructs_displayedRequiredLawRestrictionEvaluator
    (source.displayedRequiredLawsHoldOn_constructs_commonRestrictionRealization
      hholds)

/-- The evaluator and displayed law fulfillment recover the bare arrow law. -/
theorem displayedRequiredLawsHoldOn_and_restrictionEvaluator_constructs_arrowCompatibilityLaw
    (source : LawEquationBodyCechSource D K)
    (hholds : D.DisplayedRequiredLawsHoldOn)
    (evaluator : source.DisplayedRequiredLawRestrictionEvaluator) :
    source.ArrowCompatibilityLaw := by
  intro sigma tau Z gSigma gTau hcomm
  obtain ⟨lawIndexSigma, hmemSigma⟩ :=
    D.lawSupport_nonempty (source.chartOf sigma)
  obtain ⟨lawIndexTau, hmemTau⟩ :=
    D.lawSupport_nonempty (source.chartOf tau)
  have hrequiredSigma :=
    D.lawSupport_required (source.chartOf sigma) lawIndexSigma hmemSigma
  have hrequiredTau :=
    D.lawSupport_required (source.chartOf tau) lawIndexTau hmemTau
  exact
    evaluator sigma tau gSigma gTau hcomm lawIndexSigma lawIndexTau
      hmemSigma hmemTau hrequiredSigma hrequiredTau
      (by
        have heq : lawIndexSigma = (D.equationIndex (source.chartOf sigma)).1 := by
          simpa using hmemSigma
        subst lawIndexSigma
        exact hholds (source.chartOf sigma))
      (by
        have heq : lawIndexTau = (D.equationIndex (source.chartOf tau)).1 := by
          simpa using hmemTau
        subst lawIndexTau
        exact hholds (source.chartOf tau))

/-- Without arrow compatibility, displayed law fulfillment cannot yield the evaluator. -/
theorem no_displayedRequiredLawRestrictionEvaluator_without_arrowCompatibilityLaw
    (source : LawEquationBodyCechSource D K)
    (hholds : D.DisplayedRequiredLawsHoldOn)
    (hmissing : ¬ source.ArrowCompatibilityLaw) :
    ¬ source.DisplayedRequiredLawRestrictionEvaluator := by
  intro evaluator
  exact hmissing
    (source.displayedRequiredLawsHoldOn_and_restrictionEvaluator_constructs_arrowCompatibilityLaw
      hholds evaluator)

theorem displayedRequiredLawsHoldOn_constructs_arrowCompatibilityLaw
    (source : LawEquationBodyCechSource D K)
    (hholds : D.DisplayedRequiredLawsHoldOn) :
    source.ArrowCompatibilityLaw :=
  source.commonRestrictionRealization_constructs_arrowCompatibilityLaw
    (source.displayedRequiredLawsHoldOn_constructs_commonRestrictionRealization
      hholds)

theorem displayedRequiredLawsHoldOn_constructs_displayedInterpretationRealization
    (source : LawEquationBodyCechSource D K)
    (hholds : D.DisplayedRequiredLawsHoldOn) :
    source.DisplayedInterpretationRealization := by
  intro sigma
  dsimp [toPrimitive, toBaseRestrictionSource,
    LawEquationBodyBaseRestrictionSource.toPrimitive,
    displayedSourceC0, restrictedDisplayedInterpretation]
  rw [D.displayedRequiredLawsHoldOn_constructs_interpret_eq_zero hholds
    (source.chartOf sigma)]
  exact
    ((E.obstructionQuotientCoefficient.map
      (source.zeroSimplexToBase sigma).op).hom.map_zero).trans
      ((E.obstructionQuotientCoefficient.map
        (source.restriction sigma).op).hom.map_zero).symm

theorem no_commonRestrictionRealization_without_arrowCompatibilityLaw
    (source : LawEquationBodyCechSource D K)
    (hmissing : ¬ source.ArrowCompatibilityLaw) :
    ¬ source.CommonRestrictionRealization := by
  intro hrealized
  exact hmissing
    (source.commonRestrictionRealization_constructs_arrowCompatibilityLaw
      hrealized)

theorem restrictedDisplayedInterpretation_ne_zero_prevents_displayedInterpretationRealization
    (source : LawEquationBodyCechSource D K)
    (sigma : coverRel.simplex 0)
    (hne : source.restrictedDisplayedInterpretation sigma ≠
      (0 : E.ObstructionQuotient (coverRel.overlap 0 sigma))) :
    ¬ source.DisplayedInterpretationRealization := by
  intro hrealized
  apply hne
  calc
    source.restrictedDisplayedInterpretation sigma =
        source.toPrimitive sigma :=
      (hrealized sigma).symm
    _ = (0 : E.ObstructionQuotient (coverRel.overlap 0 sigma)) := by
      dsimp [toPrimitive, toBaseRestrictionSource,
        LawEquationBodyBaseRestrictionSource.toPrimitive]
      exact
        (E.obstructionQuotientCoefficient.map
          (source.zeroSimplexToBase sigma).op).hom.map_zero

theorem displayedRequiredLawsHoldOn_constructs_sourceC0PointwiseZero
    (source : LawEquationBodyCechSource D K)
    (hholds : D.DisplayedRequiredLawsHoldOn) :
    source.SourceC0PointwiseZero :=
  ⟨source.displayedRequiredLawsHoldOn_constructs_displayedInterpretationRealization
      hholds,
    D.displayedRequiredLawsHoldOn_constructs_interpret_eq_zero hholds⟩

end LawEquationBodyCechSource

/--
AG-body translation of Research
`DegreewiseCarrierDataAndExplicitFaceRestrictionEquations`.

It is an explicit existential Prop over the degree-wise carrier equivalences
and the four face/differential equations, matching the Research conjunct shape.
-/
def DegreewiseCarrierDataAndExplicitFaceRestrictionEquationsBody
    (additive : SemanticRepairAdditiveH1Surface.{y, x, z})
    {U : AtomCarrier.{r}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    (K : Cohomology.CoverRelativeCechComplex coverRel Ob) : Prop :=
  Exists fun c0Equiv :
    letI := additive.c0AddCommGroup
    letI := K.cochainAddCommGroup 0
    additive.C0 ≃+ K.Cn 0 =>
  Exists fun c1Equiv :
    letI := additive.c1AddCommGroup
    letI := K.cochainAddCommGroup 1
    additive.C1 ≃+ K.Cn 1 =>
  Exists fun c2Equiv : additive.C2 ≃ K.Cn 2 =>
  Exists fun _c2Equiv_zero :
    letI := K.cochainAddCommGroup 2
    c2Equiv additive.zero2 = 0 =>
  Exists fun _c2Equiv_symm_zero :
    letI := K.cochainAddCommGroup 2
    c2Equiv.symm 0 = additive.zero2 =>
    (letI := additive.c0AddCommGroup
     letI := additive.c1AddCommGroup
     letI := K.cochainAddCommGroup 0
     letI := K.cochainAddCommGroup 1
     forall primitive : additive.C0,
        K.d 0 (c0Equiv primitive) = c1Equiv (additive.delta0 primitive)) /\
    (letI := additive.c0AddCommGroup
     letI := additive.c1AddCommGroup
     letI := K.cochainAddCommGroup 0
     letI := K.cochainAddCommGroup 1
     forall primitive : K.Cn 0,
        additive.delta0 (c0Equiv.symm primitive) =
          c1Equiv.symm (K.d 0 primitive)) /\
    (letI := additive.c1AddCommGroup
     letI := K.cochainAddCommGroup 1
     forall cochain : additive.C1,
        K.d 1 (c1Equiv cochain) = c2Equiv (additive.delta1 cochain)) /\
    (letI := additive.c1AddCommGroup
     letI := K.cochainAddCommGroup 1
     forall cochain : K.Cn 1,
        additive.delta1 (c1Equiv.symm cochain) =
          c2Equiv.symm (K.d 1 cochain))

/-- Extract the explicit degree-wise carrier/face equations from a cochain realization. -/
theorem cochainRealization_constructs_degreewiseCarrierFaceEquationsBody
    {additive : SemanticRepairAdditiveH1Surface.{y, x, z}}
    {U : AtomCarrier.{r}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    {K : Cohomology.CoverRelativeCechComplex coverRel Ob}
    (realization : SemanticRepairCoverRelativeCochainRealization additive K) :
    DegreewiseCarrierDataAndExplicitFaceRestrictionEquationsBody additive K := by
  exact
    ⟨realization.c0Equiv, realization.c1Equiv, realization.c2Equiv,
      realization.c2Equiv_zero, realization.c2Equiv_symm_zero,
      realization.d0_to, realization.d0_from, realization.d1_to,
      realization.d1_from⟩

/--
AG-body translation of the Research selected semantic coefficient realization
layer.
-/
structure SelectedSemanticCoefficientDirectRealizationLayerBody
    {P : SemanticAtomProjection.{u, v}}
    {semanticCover : SemanticRepairCover.{u, v, w, x} P}
    {U : AtomCarrier.{r}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {F : Site.AATPresheaf S}
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    {K : Cohomology.CoverRelativeCechComplex coverRel Ob}
    (surface :
      LawEquationGeneratedCurrentG06InputSurface semanticCover S F K)
    (data : SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    Type (max (r + 1) (max u (max v (max w (max x (max y z)))))) where
  /-- Coverage family whose generated sieve is the selected cover. -/
  family :
    Site.AATCoverageFamily S.requirements S.overlap surface.coverBase
  cover_eq : surface.selectedCover = Sieve.generate family.presieve
  directLower :
    DegreewiseCarrierDataAndExplicitFaceRestrictionEquationsBody
      data.toAdditiveH1Surface K

/-- A generated coverage family and cochain realization construct the selected layer body. -/
def cochainRealization_constructs_selectedRealizationLayerBody
    {P : SemanticAtomProjection.{u, v}}
    {semanticCover : SemanticRepairCover.{u, v, w, x} P}
    {U : AtomCarrier.{r}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {F : Site.AATPresheaf S}
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    {K : Cohomology.CoverRelativeCechComplex coverRel Ob}
    (surface :
      LawEquationGeneratedCurrentG06InputSurface semanticCover S F K)
    (data : SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (family :
      Site.AATCoverageFamily S.requirements S.overlap surface.coverBase)
    (cover_eq : surface.selectedCover = Sieve.generate family.presieve)
    (realization :
      SemanticRepairCoverRelativeCochainRealization data.toAdditiveH1Surface K) :
    SelectedSemanticCoefficientDirectRealizationLayerBody surface data :=
  { family := family
    cover_eq := cover_eq
    directLower :=
      cochainRealization_constructs_degreewiseCarrierFaceEquationsBody
        realization }

/-- The selected realization layer exposes the generated-cover equation. -/
theorem SelectedSemanticCoefficientDirectRealizationLayerBody.cover_is_generated
    {P : SemanticAtomProjection.{u, v}}
    {semanticCover : SemanticRepairCover.{u, v, w, x} P}
    {U : AtomCarrier.{r}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {F : Site.AATPresheaf S}
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    {K : Cohomology.CoverRelativeCechComplex coverRel Ob}
    {surface :
      LawEquationGeneratedCurrentG06InputSurface semanticCover S F K}
    {data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P}
    (layer : SelectedSemanticCoefficientDirectRealizationLayerBody surface data) :
    surface.selectedCover = Sieve.generate layer.family.presieve :=
  layer.cover_eq

/-- A surface with no generated-family presentation cannot carry the selected layer. -/
theorem no_selectedRealizationLayer_without_generatedCover
    {P : SemanticAtomProjection.{u, v}}
    {semanticCover : SemanticRepairCover.{u, v, w, x} P}
    {U : AtomCarrier.{r}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {F : Site.AATPresheaf S}
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    {K : Cohomology.CoverRelativeCechComplex coverRel Ob}
    {surface :
      LawEquationGeneratedCurrentG06InputSurface semanticCover S F K}
    {data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P}
    (hnotGenerated :
      forall family :
        Site.AATCoverageFamily S.requirements S.overlap surface.coverBase,
        surface.selectedCover ≠ Sieve.generate family.presieve) :
    ¬ Nonempty
      (SelectedSemanticCoefficientDirectRealizationLayerBody surface data) := by
  rintro ⟨layer⟩
  exact hnotGenerated layer.family layer.cover_eq

/-!
The final generated law-equation route is finite-free.  Its coefficient
surface is the cover-relative complex itself, so no finiteness of the section
groups is required.

Implementation notes:

- `coverRelativeGeneratedBoundaryAdditiveH1Surface` uses the selected
  cover-relative complex itself as the degreewise carrier and defines the
  residual as `K.d 0 primitive`.  This is the body presentation of theorem
  8.2: conclusions 4--10 arise from a generated boundary independently of
  displayed-law fulfillment.
- The identity cochain realization is chosen because both sides are the same
  generated complex.  A separately supplied equivalence was rejected because
  it would move conclusion 6 into an input certificate.
- The earlier bounded presentation requiring `Fintype (K.Cn 0)` and
  `Fintype (K.Cn 1)` was rejected for the final route because those hypotheses
  are absent from the Research source theorem and are unnecessary for the
  degreewise identity realization.
- The rich semantic input, witness geometry, and finite-poset defect source
  remain separate structures so atom trace provenance, the generally supplied
  quotient sheaf condition, and local law data cannot be replaced by a single
  conclusion-carrying certificate.
-/

/-- Finite-free additive H1 surface generated by a cover-relative primitive. -/
def coverRelativeGeneratedBoundaryAdditiveH1Surface
    {U : AtomCarrier.{r}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    (K : Cohomology.CoverRelativeCechComplex coverRel Ob)
    (primitive : K.Cn 0) : SemanticRepairAdditiveH1Surface := by
  letI := K.cochainAddCommGroup 0
  letI := K.cochainAddCommGroup 1
  letI := K.cochainAddCommGroup 2
  exact
    { C0 := K.Cn 0
      C1 := K.Cn 1
      C2 := K.Cn 2
      zero1 := 0
      zero2 := 0
      delta0 := K.d 0
      delta1 := K.d 1
      residual := K.d 0 primitive
      zero1_eq_zero := rfl
      delta0_zero := (K.d 0).map_zero
      delta0_add := (K.d 0).map_add
      delta0_neg := (K.d 0).map_neg
      zero1_cocycle := (K.d 1).map_zero
      delta1_delta0_eq_zero := K.differential_comp 0
      residual_cocycle := K.differential_comp 0 primitive }

/-- Identity cochain realization of the finite-free generated boundary surface. -/
def coverRelativeGeneratedBoundaryCochainRealization
    {U : AtomCarrier.{r}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    (K : Cohomology.CoverRelativeCechComplex coverRel Ob)
    (primitive : K.Cn 0) :
    SemanticRepairCoverRelativeCochainRealization
      (coverRelativeGeneratedBoundaryAdditiveH1Surface K primitive) K := by
  letI := K.cochainAddCommGroup 0
  letI := K.cochainAddCommGroup 1
  letI := K.cochainAddCommGroup 2
  exact
    { c0Equiv := AddEquiv.refl _
      c1Equiv := AddEquiv.refl _
      c2Equiv := Equiv.refl _
      c2Equiv_zero := rfl
      c2Equiv_symm_zero := rfl
      d0_to := fun _ => rfl
      d0_from := fun _ => rfl
      d1_to := fun _ => rfl
      d1_from := fun _ => rfl }

/-- Finite-free selected generated-cover layer. -/
structure SelectedSemanticCoefficientFiniteFreeRealizationLayerBody
    {P : SemanticAtomProjection.{u, v}}
    {semanticCover : SemanticRepairCover.{u, v, w, x} P}
    {U : AtomCarrier.{r}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {F : Site.AATPresheaf S}
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    {K : Cohomology.CoverRelativeCechComplex coverRel Ob}
    (surface : LawEquationGeneratedCurrentG06InputSurface semanticCover S F K)
    (additive : SemanticRepairAdditiveH1Surface.{q, t, z}) :
    Type (max (r + 1) (max u (max v (max w (max x (max q (max t z))))))) where
  /-- Coverage family whose generated sieve is the selected cover. -/
  family : Site.AATCoverageFamily S.requirements S.overlap surface.coverBase
  cover_eq : surface.selectedCover = Sieve.generate family.presieve
  directLower :
    DegreewiseCarrierDataAndExplicitFaceRestrictionEquationsBody additive K

/-- A generated family and finite-free realization construct the selected layer. -/
def cochainRealization_constructs_finiteFreeSelectedRealizationLayerBody
    {P : SemanticAtomProjection.{u, v}}
    {semanticCover : SemanticRepairCover.{u, v, w, x} P}
    {U : AtomCarrier.{r}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {F : Site.AATPresheaf S}
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    {K : Cohomology.CoverRelativeCechComplex coverRel Ob}
    (surface : LawEquationGeneratedCurrentG06InputSurface semanticCover S F K)
    (additive : SemanticRepairAdditiveH1Surface.{q, t, z})
    (family : Site.AATCoverageFamily S.requirements S.overlap surface.coverBase)
    (cover_eq : surface.selectedCover = Sieve.generate family.presieve)
    (realization : SemanticRepairCoverRelativeCochainRealization additive K) :
    SelectedSemanticCoefficientFiniteFreeRealizationLayerBody surface additive :=
  { family := family
    cover_eq := cover_eq
    directLower :=
      cochainRealization_constructs_degreewiseCarrierFaceEquationsBody realization }

/-- The bounded R4 layer forgets only bounded carrier bookkeeping. -/
def SelectedSemanticCoefficientDirectRealizationLayerBody.toFiniteFree
    {P : SemanticAtomProjection.{u, v}}
    {semanticCover : SemanticRepairCover.{u, v, w, x} P}
    {U : AtomCarrier.{r}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {F : Site.AATPresheaf S}
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    {K : Cohomology.CoverRelativeCechComplex coverRel Ob}
    {surface : LawEquationGeneratedCurrentG06InputSurface semanticCover S F K}
    {data : SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P}
    (layer : SelectedSemanticCoefficientDirectRealizationLayerBody surface data) :
    SelectedSemanticCoefficientFiniteFreeRealizationLayerBody
      surface data.toAdditiveH1Surface :=
  { family := layer.family
    cover_eq := layer.cover_eq
    directLower := layer.directLower }

/-- A finite-free R4 layer specializes back to the bounded carrier presentation. -/
def SelectedSemanticCoefficientFiniteFreeRealizationLayerBody.toBounded
    {P : SemanticAtomProjection.{u, v}}
    {semanticCover : SemanticRepairCover.{u, v, w, x} P}
    {U : AtomCarrier.{r}} {A : ArchitectureObject U}
    {S : Site.AATSite A} {F : Site.AATPresheaf S}
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    {K : Cohomology.CoverRelativeCechComplex coverRel Ob}
    {surface : LawEquationGeneratedCurrentG06InputSurface semanticCover S F K}
    {data : SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P}
    (layer : SelectedSemanticCoefficientFiniteFreeRealizationLayerBody
      surface data.toAdditiveH1Surface) :
    SelectedSemanticCoefficientDirectRealizationLayerBody surface data :=
  { family := layer.family
    cover_eq := layer.cover_eq
    directLower := layer.directLower }

/-- Generated residual is an actual additive coboundary. -/
def GeneratedResidualBoundarySurfaceBody
    (additive : SemanticRepairAdditiveH1Surface) : Prop :=
  Exists fun primitive : additive.C0 =>
    additive.delta0 primitive = additive.residual

/-- Generated residual and zero cocycles are in the same semantic class. -/
def GeneratedSemanticH1ZeroBody
    (additive : SemanticRepairAdditiveH1Surface) : Prop :=
  additive.delta1 additive.residual = additive.zero2 /\
    additive.Cohomologous
      ⟨additive.residual, additive.residual_cocycle⟩
      ⟨additive.zero1, additive.zero1_cocycle⟩

/-- The generated primitive supplies the finite-free residual witness. -/
theorem generatedBoundarySurface_constructs_residualBoundaryBody
    {additive : SemanticRepairAdditiveH1Surface}
    (primitive : additive.C0)
    (hprimitive : additive.delta0 primitive = additive.residual) :
    GeneratedResidualBoundarySurfaceBody additive :=
  ⟨primitive, hprimitive⟩

/-- A generated residual boundary supplies the semantic same-class witness. -/
theorem residualBoundaryBody_constructs_semanticH1ZeroBody
    {additive : SemanticRepairAdditiveH1Surface}
    (hboundary : GeneratedResidualBoundarySurfaceBody additive) :
    GeneratedSemanticH1ZeroBody additive := by
  rcases hboundary with ⟨primitive, hprimitive⟩
  refine ⟨additive.residual_cocycle, primitive, ?_⟩
  letI := additive.c1AddCommGroup
  change additive.residual - additive.zero1 = additive.delta0 primitive
  rw [additive.zero1_eq_zero, sub_zero, hprimitive]

/-- Semantic same-class zero supplies the quotient-level additive H1 zero. -/
theorem semanticH1ZeroBody_constructs_additiveH1Zero
    {additive : SemanticRepairAdditiveH1Surface}
    (hzero : GeneratedSemanticH1ZeroBody additive) :
    additive.H1Zero :=
  Quotient.sound hzero.2

/-- The semantic zero body cannot hold without an actual residual primitive. -/
theorem semanticH1ZeroBody_constructs_residualBoundaryBody
    {additive : SemanticRepairAdditiveH1Surface}
    (hzero : GeneratedSemanticH1ZeroBody additive) :
    GeneratedResidualBoundarySurfaceBody additive := by
  rcases hzero.2 with ⟨primitive, hprimitive⟩
  refine ⟨primitive, ?_⟩
  letI := additive.c1AddCommGroup
  change additive.residual - additive.zero1 = additive.delta0 primitive at hprimitive
  rw [additive.zero1_eq_zero, sub_zero] at hprimitive
  exact hprimitive.symm

/-- Absence of a residual primitive rules out the generated semantic zero body. -/
theorem no_generatedSemanticH1ZeroBody_without_residualBoundary
    {additive : SemanticRepairAdditiveH1Surface}
    (hmissing : ¬ GeneratedResidualBoundarySurfaceBody additive) :
    ¬ GeneratedSemanticH1ZeroBody additive :=
  fun hzero => hmissing (semanticH1ZeroBody_constructs_residualBoundaryBody hzero)

/-- The semantic zero body is exactly residual-boundary generation. -/
theorem generatedSemanticH1ZeroBody_iff_residualBoundarySurfaceBody
    (additive : SemanticRepairAdditiveH1Surface) :
    GeneratedSemanticH1ZeroBody additive <->
      GeneratedResidualBoundarySurfaceBody additive :=
  ⟨semanticH1ZeroBody_constructs_residualBoundaryBody,
    residualBoundaryBody_constructs_semanticH1ZeroBody⟩

/-- AG-body translation of the Research residual-boundary conjunct. -/
def GeneratedResidualBoundaryBody
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    Prop :=
  CechB1 data.boundaryRelation.cech data.boundaryRelation.cech.residual

/-- The bounded R4 residual predicate and finite-free predicate are identical. -/
theorem generatedResidualBoundaryBody_iff_surfaceBody
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    GeneratedResidualBoundaryBody data <->
      GeneratedResidualBoundarySurfaceBody data.toAdditiveH1Surface :=
  Iff.rfl

/-- The generated primitive gives the residual-boundary conjunct. -/
theorem generatedBoundary_constructs_residualBoundaryBody
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (primitive : data.boundaryRelation.cech.C0)
    (hprimitive :
      data.boundaryRelation.cech.delta0 primitive =
        data.boundaryRelation.cech.residual) :
    GeneratedResidualBoundaryBody data :=
  ⟨primitive, hprimitive⟩

/--
AG-body translated law-independent tuple for the Research
`lawEquation_groundedRoute_isLawIndependent` theorem.
-/
structure LawEquationGroundedRouteLawIndependentConjunctsBody
    {P : SemanticAtomProjection.{u, v}}
    {semanticCover : SemanticRepairCover.{u, v, w, x} P}
    {Ulaw : AtomCarrier.{u}}
    {Alaw : ArchitectureObject Ulaw}
    {Slaw : Site.AATSite.{u} Alaw}
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    {coverRel : Cohomology.CoverRelativeCechCover Slaw}
    {Ob : Cohomology.ObstructionSheaf Slaw}
    {K : Cohomology.CoverRelativeCechComplex coverRel Ob}
    (surface :
      LawEquationGeneratedCurrentG06InputSurface
        semanticCover Slaw E.obstructionQuotientPresheaf K)
    (data : SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (comparison :
      SemanticRepairCoverRelativeH1Comparison data.toAdditiveH1Surface K) :
    Type (max (u + 1) (max v (max w (max x (max y z))))) where
  selectedRealizationLayer :
    Nonempty (SelectedSemanticCoefficientDirectRealizationLayerBody surface data)
  degreewiseCarrierFaceEquations :
    DegreewiseCarrierDataAndExplicitFaceRestrictionEquationsBody
      data.toAdditiveH1Surface K
  cochainRealization :
    Nonempty (SemanticRepairCoverRelativeCochainRealization data.toAdditiveH1Surface K)
  h1ComparisonPackage :
    Nonempty
      (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
        comparison)
  residualBoundary : GeneratedResidualBoundaryBody data
  semanticH1Zero : data.toAdditiveH1Surface.H1Zero
  additiveH1Zero : data.toAdditiveCechH1Data.H1Zero

/--
Lower pointwise tuple used before the standard Cech differential is fixed.
-/
structure LawEquationGroundedComparisonPointwiseConjunctsBody
    {P : SemanticAtomProjection.{u, v}}
    {semanticCover : SemanticRepairCover.{u, v, w, x} P}
    {Ulaw : AtomCarrier.{u}}
    {Alaw : ArchitectureObject Ulaw}
    {Slaw : Site.AATSite.{u} Alaw}
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    (D : LawAlgebra.LawEquationDefectSource.{u} E)
    {coverRel : Cohomology.CoverRelativeCechCover Slaw}
    {sheafCondition :
      Site.AATSheafCondition Slaw E.obstructionQuotientPresheaf}
    {K : Cohomology.CoverRelativeCechComplex coverRel
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        E.obstructionQuotientCoefficient sheafCondition)}
    (surface :
      LawEquationGeneratedCurrentG06InputSurface
        semanticCover Slaw E.obstructionQuotientPresheaf K)
    (source : LawEquationBodyCechSource D K)
    (data : SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (comparison :
      SemanticRepairCoverRelativeH1Comparison data.toAdditiveH1Surface K) :
    Type (max (u + 1) (max v (max w (max x (max y z))))) where
  displayedInterpretationRealization :
    source.DisplayedInterpretationRealization
  commonRestrictionRealization : source.CommonRestrictionRealization
  baseRestrictionSourcePreservesDisplayedInterpretation :
    source.BaseRestrictionSourcePreservesDisplayedInterpretation
      source.toBaseRestrictionSource
  arrowCompatibilityLaw : source.ArrowCompatibilityLaw
  displayedRequiredLawRestrictionEvaluator :
    source.DisplayedRequiredLawRestrictionEvaluator
  sourceC0PointwiseZero : source.SourceC0PointwiseZero
  selectedRealizationLayer :
    Nonempty (SelectedSemanticCoefficientDirectRealizationLayerBody surface data)
  degreewiseCarrierFaceEquations :
    DegreewiseCarrierDataAndExplicitFaceRestrictionEquationsBody
      data.toAdditiveH1Surface K
  cochainRealization :
    Nonempty (SemanticRepairCoverRelativeCochainRealization data.toAdditiveH1Surface K)
  h1ComparisonPackage :
    Nonempty
      (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
        comparison)
  residualBoundary : GeneratedResidualBoundaryBody data
  semanticH1Zero : data.toAdditiveH1Surface.H1Zero
  additiveH1Zero : data.toAdditiveCechH1Data.H1Zero

/-- Research theorem-7.5 tuple with actual source-C0 Cech differential zero. -/
structure LawEquationGroundedComparisonConjunctsBody
    {P : SemanticAtomProjection.{u, v}}
    {semanticCover : SemanticRepairCover.{u, v, w, x} P}
    {Ulaw : AtomCarrier.{u}}
    {Alaw : ArchitectureObject Ulaw}
    {Slaw : Site.AATSite.{u} Alaw}
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    (D : LawAlgebra.LawEquationDefectSource.{u} E)
    {coverRel : Cohomology.CoverRelativeCechCover Slaw}
    {sheafCondition :
      Site.AATSheafCondition Slaw E.obstructionQuotientPresheaf}
    {K : Cohomology.CoverRelativeCechComplex coverRel
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        E.obstructionQuotientCoefficient sheafCondition)}
    (surface :
      LawEquationGeneratedCurrentG06InputSurface
        semanticCover Slaw E.obstructionQuotientPresheaf K)
    (source : LawEquationBodyCechSource D K)
    (data : SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (comparison :
      SemanticRepairCoverRelativeH1Comparison data.toAdditiveH1Surface K) :
    Type (max (u + 1) (max v (max w (max x (max y z)))))
    extends LawEquationGroundedComparisonPointwiseConjunctsBody
      D surface source data comparison where
  sourceC0CechZero : source.SourceC0CechZero

/-- The packet transports displayed source-C0 zero back to the independent primitive. -/
theorem LawEquationGroundedComparisonConjunctsBody.sourcePrimitiveC0CechZero
    {P : SemanticAtomProjection.{u, v}}
    {semanticCover : SemanticRepairCover.{u, v, w, x} P}
    {Ulaw : AtomCarrier.{u}}
    {Alaw : ArchitectureObject Ulaw}
    {Slaw : Site.AATSite.{u} Alaw}
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    {D : LawAlgebra.LawEquationDefectSource.{u} E}
    {coverRel : Cohomology.CoverRelativeCechCover Slaw}
    {sheafCondition :
      Site.AATSheafCondition Slaw E.obstructionQuotientPresheaf}
    {K : Cohomology.CoverRelativeCechComplex coverRel
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        E.obstructionQuotientCoefficient sheafCondition)}
    {surface :
      LawEquationGeneratedCurrentG06InputSurface
        semanticCover Slaw E.obstructionQuotientPresheaf K}
    {source : LawEquationBodyCechSource D K}
    {data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P}
    {comparison :
      SemanticRepairCoverRelativeH1Comparison data.toAdditiveH1Surface K}
    (packet :
      LawEquationGroundedComparisonConjunctsBody
        D surface source data comparison) :
    letI := K.cochainAddCommGroup 1
    K.d 0 source.toPrimitive = 0 := by
  have heq : source.toPrimitive = source.displayedSourceC0 :=
    funext packet.displayedInterpretationRealization
  rw [heq]
  exact packet.sourceC0CechZero

/-- Repackage the generated interpretation equality under its pointwise-zero name. -/
theorem toGeneratedInterpretationPointwiseZero
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite.{u} A}
    {E : ArchitecturalEquationSystem S.contextPreorder}
    (D : LawAlgebra.LawEquationDefectSource.{u} E)
    (hpointwise : forall i : D.Chart, D.interpret i = 0) :
    D.GeneratedInterpretationPointwiseZero :=
  hpointwise

/--
Displayed required-law fulfillment constructs the body-side primitive
realization used by the generated-pair route.
-/
theorem displayedRequiredLawsHoldOn_constructs_primitive_realizes_displayedInterpretations
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite.{u} A}
    {E : ArchitecturalEquationSystem S.contextPreorder}
    (D : LawAlgebra.LawEquationDefectSource.{u} E)
    (hholds : D.DisplayedRequiredLawsHoldOn) :
    forall i : D.Chart, D.interpret i = 0 :=
  D.displayedRequiredLawsHoldOn_constructs_interpret_eq_zero hholds

/--
X.定理7.5 generated-pair body route.

The theorem constructs the cover bridge, the H1 comparison, and the 7.5 packet
from AG-body data only.  It does not import or wrap research declarations, and
it does not call the native-input wrapper.

Scaffolding: this route consumes the section-4 bounded Cech data, whose
`c0Finite` / `c1Finite` fields carry `Fintype` premises absent from theorem
7.5.  The canonical theorem-7.5 entry-point is the finite-free
`lawEquation_constructs_groundedComparisonPacket_finiteFree`.
-/
theorem lawEquation_constructs_generatedPair_groundedComparisonPacket
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    {Ulaw : AtomCarrier.{u}}
    {Alaw : ArchitectureObject Ulaw}
    {Slaw : Site.AATSite.{u} Alaw}
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    (D : LawAlgebra.LawEquationDefectSource.{u} E)
    (hDisplayedRequiredLaws : D.DisplayedRequiredLawsHoldOn)
    (semanticCover : SemanticRepairCover.{u, v, w, x} P)
    {coverRel : Cohomology.CoverRelativeCechCover Slaw}
    (chartSimplex : semanticCover.CoverChart -> coverRel.simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) -> coverRel.simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          coverRel.simplex 2)
    {base : Slaw.category}
    (cover : Sieve base)
    (certificate :
      data.TrueSheafConditionCertificate Slaw E.obstructionQuotientPresheaf cover)
    (gluingData :
      Site.AATGluingData Slaw E.obstructionQuotientPresheaf cover)
    {K : Cohomology.CoverRelativeCechComplex coverRel
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        E.obstructionQuotientCoefficient certificate.sheafCondition)}
    (realization :
      SemanticRepairCoverRelativeCochainRealization data.toAdditiveH1Surface K) :
    Nonempty
      (Sigma fun _bridge : SemanticRepairCoverRelativeCoverBridge semanticCover Slaw =>
        Sigma fun comparison :
          SemanticRepairCoverRelativeH1Comparison data.toAdditiveH1Surface K =>
            SemanticRepairGeneratedEndToEndSAGAPacket
              data D Slaw E.obstructionQuotientPresheaf cover gluingData
              comparison) := by
  let bridge :=
    lawEquationCurrentG06InputSurface semanticCover coverRel chartSimplex
      overlapSimplex tripleSimplex
  let comparison := realization.toH1Comparison
  have hInterpretZero :
      forall i : D.Chart, D.interpret i = 0 :=
    displayedRequiredLawsHoldOn_constructs_primitive_realizes_displayedInterpretations
      D hDisplayedRequiredLaws
  have hPointwiseZero : D.GeneratedInterpretationPointwiseZero :=
    toGeneratedInterpretationPointwiseZero D hInterpretZero
  rcases
    displayedRequiredLawsHoldOn_constructs_generatedSourceC0_zeroPackage
      D hDisplayedRequiredLaws with
    ⟨hZeroPackage⟩
  rcases
    trueSheafBoundaryRelationAdditive_coverRelativeH1Zero_effectiveGluing_package
      data Slaw E.obstructionQuotientPresheaf cover certificate gluingData
      comparison with
    ⟨package73⟩
  refine ⟨⟨bridge, comparison, ?_⟩⟩
  exact
    { lawDependentConclusions :=
        { generatedSourceC0ZeroPackage := hZeroPackage
          generatedInterpretationZero := hInterpretZero
          generatedInterpretationPointwiseZero := hPointwiseZero
          generatedInterpretationZero_iff_defect_mem_obstructionIdeal :=
            D.interpret_eq_zero_iff_defect_mem_obstructionIdeal
          nonzeroInterpretationDetectsDisplayedLawFailure :=
            fun i hne =>
              D.interpret_ne_zero_detects_displayed_required_law_failure i hne }
      lawIndependentConclusions :=
        { groundedGlobalGluingPackage := ⟨package73⟩
          sheafConditionFor := package73.sheafConditionFor
          descent := package73.descent
          uniqueGlobalSection := package73.uniqueGlobalSection
          globalCoherent_iff_coverRelativeH1Zero :=
            package73.globalCoherent_iff_coverRelativeH1Zero
          boundedAdditiveH1Zero_iff_coverRelativeH1Zero :=
            package73.boundedAdditiveH1Zero_iff_coverRelativeH1Zero
          torsorTrivialization := package73.torsorTrivialization_of_h1Zero } }

/--
Generated-complex form of theorem 7.5 for the body route.

The comparison supply is generated inside the theorem from the selected
cover-relative complex `K`: the bounded additive Cech data uses `K.Cn` and
`K.d`, and the cochain realization is the identity realization constructed
from that generated surface.

Scaffolding: this bounded route assumes `Fintype` on the degree-0/1 cochain
groups, premises absent from theorem 7.5.  The canonical theorem-7.5
entry-point is the finite-free
`lawEquation_constructs_groundedComparisonPacket_finiteFree`.
-/
theorem lawEquation_constructs_generatedPair_groundedComparisonPacket_fromCoverRelativeComplex
    {P : SemanticAtomProjection.{x, v}}
    (semanticCover : SemanticRepairCover.{x, v, w, x} P)
    {Ulaw : AtomCarrier.{x}}
    {Alaw : ArchitectureObject Ulaw}
    {Slaw : Site.AATSite.{x} Alaw}
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    (D : LawAlgebra.LawEquationDefectSource.{x} E)
    (hDisplayedRequiredLaws : D.DisplayedRequiredLawsHoldOn)
    {coverRel : Cohomology.CoverRelativeCechCover Slaw}
    (chartSimplex : semanticCover.CoverChart -> coverRel.simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) -> coverRel.simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          coverRel.simplex 2)
    {base : Slaw.category}
    (cover : Sieve base)
    (sheafCondition :
      Site.AATSheafCondition Slaw E.obstructionQuotientPresheaf)
    (K : Cohomology.CoverRelativeCechComplex coverRel
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        E.obstructionQuotientCoefficient sheafCondition))
    (c0Finite : Fintype (K.Cn 0)) (c1Finite : Fintype (K.Cn 1))
    (zero1 residual : K.Cn 1)
    (hzero1 : letI := K.cochainAddCommGroup 2; K.d 1 zero1 = 0)
    (hresidual : letI := K.cochainAddCommGroup 2; K.d 1 residual = 0)
    (hzero1_eq_zero : letI := K.cochainAddCommGroup 1; zero1 = 0)
    (supportOf : K.Cn 0 -> P.Support)
    (component_covered_of_boundary :
      forall primitive,
        K.d 0 primitive = residual ->
          ResidualComponentCoveredSupport P semanticCover.baseCover
            (supportOf primitive))
    (component_faithful_of_boundary :
      forall primitive,
        K.d 0 primitive = residual ->
          ResidualComponentFaithfulSupport P semanticCover.baseCover
            (supportOf primitive))
    (cover_mem : cover ∈ Slaw.topology base)
    (gluingData :
      Site.AATGluingData Slaw E.obstructionQuotientPresheaf cover) :
    Nonempty
      (Sigma fun _bridge : SemanticRepairCoverRelativeCoverBridge semanticCover Slaw =>
        Sigma fun comparison :
          SemanticRepairCoverRelativeH1Comparison
            (coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
              zero1 residual hzero1 hresidual hzero1_eq_zero supportOf component_covered_of_boundary
              component_faithful_of_boundary).toAdditiveH1Surface
            K =>
            SemanticRepairGeneratedEndToEndSAGAPacket
              (coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
                zero1 residual hzero1 hresidual hzero1_eq_zero supportOf component_covered_of_boundary
                component_faithful_of_boundary)
              D Slaw E.obstructionQuotientPresheaf cover gluingData comparison) := by
  let data :=
    coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
      zero1 residual hzero1 hresidual hzero1_eq_zero supportOf component_covered_of_boundary
      component_faithful_of_boundary
  let certificate : data.TrueSheafConditionCertificate
      Slaw E.obstructionQuotientPresheaf cover :=
    { cover_mem := cover_mem
      sheafCondition := sheafCondition }
  let realization :=
    coverRelativeIdentityCochainRealizationOfComplex semanticCover K c0Finite c1Finite
      zero1 residual hzero1 hresidual hzero1_eq_zero supportOf component_covered_of_boundary
      component_faithful_of_boundary
  exact
    lawEquation_constructs_generatedPair_groundedComparisonPacket
      data D hDisplayedRequiredLaws semanticCover chartSimplex overlapSimplex
      tripleSimplex cover certificate gluingData realization

/--
Generated-boundary theorem-7.5 law-independent layer.

This is the body-side counterpart of the research-loop
`lawEquation_groundedRoute_isLawIndependent`: once the residual is generated as
`K.d 0 primitive`, the H1 comparison, theorem-7.3 conclusion group, residual
boundary reading, and semantic/additive H1-zero readings are constructed
without any displayed-law premise.  The law premise is used only when this
surface is later combined with the law-dependent degree-zero conclusions.

Scaffolding: this bounded route assumes `Fintype` on the degree-0/1 cochain
groups, premises absent from theorem 7.5.  The canonical theorem-7.5
entry-point is the finite-free
`lawEquation_constructs_groundedComparisonPacket_finiteFree`.
-/
theorem lawEquation_generatedBoundary_lawIndependentConclusions_fromPrimitive
    {P : SemanticAtomProjection.{x, v}}
    (semanticCover : SemanticRepairCover.{x, v, w, x} P)
    {Ulaw : AtomCarrier.{x}}
    {Alaw : ArchitectureObject Ulaw}
    {Slaw : Site.AATSite.{x} Alaw}
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    {coverRel : Cohomology.CoverRelativeCechCover Slaw}
    (chartSimplex : semanticCover.CoverChart -> coverRel.simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) -> coverRel.simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          coverRel.simplex 2)
    {base : Slaw.category}
    (cover : Sieve base)
    (sheafCondition :
      Site.AATSheafCondition Slaw E.obstructionQuotientPresheaf)
    (K : Cohomology.CoverRelativeCechComplex coverRel
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        E.obstructionQuotientCoefficient sheafCondition))
    (c0Finite : Fintype (K.Cn 0)) (c1Finite : Fintype (K.Cn 1))
    (zero1 : K.Cn 1)
    (primitive : K.Cn 0)
    (hzero1 : letI := K.cochainAddCommGroup 2; K.d 1 zero1 = 0)
    (hzero1_eq_zero : letI := K.cochainAddCommGroup 1; zero1 = 0)
    (supportOf : K.Cn 0 -> P.Support)
    (component_covered_of_boundary :
      forall boundaryPrimitive,
        K.d 0 boundaryPrimitive = K.d 0 primitive ->
          ResidualComponentCoveredSupport P semanticCover.baseCover
            (supportOf boundaryPrimitive))
    (component_faithful_of_boundary :
      forall boundaryPrimitive,
        K.d 0 boundaryPrimitive = K.d 0 primitive ->
          ResidualComponentFaithfulSupport P semanticCover.baseCover
            (supportOf boundaryPrimitive))
    (cover_mem : cover ∈ Slaw.topology base)
    (gluingData :
      Site.AATGluingData Slaw E.obstructionQuotientPresheaf cover) :
    Nonempty
      (Sigma fun _bridge : SemanticRepairCoverRelativeCoverBridge semanticCover Slaw =>
        Sigma fun comparison :
          SemanticRepairCoverRelativeH1Comparison
            (coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
              zero1 (K.d 0 primitive) hzero1 (K.differential_comp 0 primitive)
              hzero1_eq_zero supportOf component_covered_of_boundary
              component_faithful_of_boundary).toAdditiveH1Surface
            K =>
            Subtype (fun _lawIndependent :
              SemanticRepairGeneratedLawIndependentConclusions
                (coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
                  zero1 (K.d 0 primitive) hzero1 (K.differential_comp 0 primitive)
                  hzero1_eq_zero supportOf component_covered_of_boundary
                  component_faithful_of_boundary)
                Slaw E.obstructionQuotientPresheaf cover gluingData comparison =>
            (coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
              zero1 (K.d 0 primitive) hzero1 (K.differential_comp 0 primitive)
              hzero1_eq_zero supportOf component_covered_of_boundary
              component_faithful_of_boundary).toAdditiveCechH1Data.H1Zero ∧
            (coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
              zero1 (K.d 0 primitive) hzero1 (K.differential_comp 0 primitive)
              hzero1_eq_zero supportOf component_covered_of_boundary
              component_faithful_of_boundary).toAdditiveH1Surface.H1Zero ∧
            comparison.CoverRelativeResidualH1Zero)) := by
  let data :=
    coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
      zero1 (K.d 0 primitive) hzero1 (K.differential_comp 0 primitive)
      hzero1_eq_zero supportOf component_covered_of_boundary
      component_faithful_of_boundary
  let bridge :=
    lawEquationCurrentG06InputSurface semanticCover coverRel chartSimplex
      overlapSimplex tripleSimplex
  let certificate : data.TrueSheafConditionCertificate
      Slaw E.obstructionQuotientPresheaf cover :=
    { cover_mem := cover_mem
      sheafCondition := sheafCondition }
  let realization :=
    coverRelativeIdentityCochainRealizationOfComplex semanticCover K c0Finite c1Finite
      zero1 (K.d 0 primitive) hzero1 (K.differential_comp 0 primitive)
      hzero1_eq_zero supportOf component_covered_of_boundary
      component_faithful_of_boundary
  let comparison := realization.toH1Comparison
  rcases
    trueSheafBoundaryRelationAdditive_coverRelativeH1Zero_effectiveGluing_package
      data Slaw E.obstructionQuotientPresheaf cover certificate gluingData
      comparison with
    ⟨package73⟩
  have hBounded : data.toAdditiveCechH1Data.H1Zero :=
    coverRelativeGeneratedBoundary_additiveH1ZeroOfPrimitive
      semanticCover K c0Finite c1Finite zero1 primitive hzero1
      hzero1_eq_zero supportOf component_covered_of_boundary
      component_faithful_of_boundary
  have hSurface : data.toAdditiveH1Surface.H1Zero :=
    (boundedAdditiveH1Zero_iff_surfaceH1Zero data).1 hBounded
  have hCover : comparison.CoverRelativeResidualH1Zero :=
    (comparison.semanticRepairAdditiveH1Zero_iff_coverRelativeH1Zero).1
      hSurface
  let lawIndependent :
      SemanticRepairGeneratedLawIndependentConclusions
        data Slaw E.obstructionQuotientPresheaf cover gluingData
        comparison :=
    { groundedGlobalGluingPackage := ⟨package73⟩
      sheafConditionFor := package73.sheafConditionFor
      descent := package73.descent
      uniqueGlobalSection := package73.uniqueGlobalSection
      globalCoherent_iff_coverRelativeH1Zero :=
        package73.globalCoherent_iff_coverRelativeH1Zero
      boundedAdditiveH1Zero_iff_coverRelativeH1Zero :=
        package73.boundedAdditiveH1Zero_iff_coverRelativeH1Zero
      torsorTrivialization := package73.torsorTrivialization_of_h1Zero }
  refine ⟨⟨bridge, comparison, ?_⟩⟩
  exact ⟨lawIndependent, hBounded, hSurface, hCover⟩

/--
Generated-boundary law-independent route with the Research visible conjuncts
preserved as AG-body fields.

Scaffolding: this bounded route assumes `Fintype` on the degree-0/1 cochain
groups, premises absent from theorem 7.5.  The canonical theorem-7.5
entry-point is the finite-free
`lawEquation_constructs_groundedComparisonPacket_finiteFree`.
-/
theorem lawEquation_generatedBoundary_lawIndependentResearchConjuncts_fromPrimitive
    {P : SemanticAtomProjection.{x, v}}
    (semanticCover : SemanticRepairCover.{x, v, w, x} P)
    {Ulaw : AtomCarrier.{x}}
    {Alaw : ArchitectureObject Ulaw}
    {Slaw : Site.AATSite.{x} Alaw}
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    {coverRel : Cohomology.CoverRelativeCechCover Slaw}
    (chartSimplex : semanticCover.CoverChart -> coverRel.simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) -> coverRel.simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          coverRel.simplex 2)
    {base : Slaw.category}
    (family :
      Site.AATCoverageFamily Slaw.requirements Slaw.overlap base)
    (sheafCondition :
      Site.AATSheafCondition Slaw E.obstructionQuotientPresheaf)
    (K : Cohomology.CoverRelativeCechComplex coverRel
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        E.obstructionQuotientCoefficient sheafCondition))
    (c0Finite : Fintype (K.Cn 0)) (c1Finite : Fintype (K.Cn 1))
    (zero1 : K.Cn 1)
    (primitive : K.Cn 0)
    (hzero1 : letI := K.cochainAddCommGroup 2; K.d 1 zero1 = 0)
    (hzero1_eq_zero : letI := K.cochainAddCommGroup 1; zero1 = 0)
    (supportOf : K.Cn 0 -> P.Support)
    (component_covered_of_boundary :
      forall boundaryPrimitive,
        K.d 0 boundaryPrimitive = K.d 0 primitive ->
          ResidualComponentCoveredSupport P semanticCover.baseCover
            (supportOf boundaryPrimitive))
    (component_faithful_of_boundary :
      forall boundaryPrimitive,
        K.d 0 boundaryPrimitive = K.d 0 primitive ->
          ResidualComponentFaithfulSupport P semanticCover.baseCover
            (supportOf boundaryPrimitive)) :
    Nonempty
      (Sigma fun surface :
        LawEquationGeneratedCurrentG06InputSurface
          semanticCover Slaw E.obstructionQuotientPresheaf K =>
        Sigma fun comparison :
          SemanticRepairCoverRelativeH1Comparison
            (coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
              zero1 (K.d 0 primitive) hzero1 (K.differential_comp 0 primitive)
              hzero1_eq_zero supportOf component_covered_of_boundary
              component_faithful_of_boundary).toAdditiveH1Surface
            K =>
          LawEquationGroundedRouteLawIndependentConjunctsBody
            surface
            (coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
              zero1 (K.d 0 primitive) hzero1 (K.differential_comp 0 primitive)
              hzero1_eq_zero supportOf component_covered_of_boundary
              component_faithful_of_boundary)
            comparison) := by
  let data :=
    coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
      zero1 (K.d 0 primitive) hzero1 (K.differential_comp 0 primitive)
      hzero1_eq_zero supportOf component_covered_of_boundary
      component_faithful_of_boundary
  let surface :=
    lawEquationGeneratedCurrentG06InputSurface
      (semanticCover := semanticCover) K chartSimplex overlapSimplex
      tripleSimplex (Sieve.generate family.presieve) sheafCondition
      (Site.AATGrothendieckTopology.generate_mem family)
  let realization :=
    coverRelativeIdentityCochainRealizationOfComplex semanticCover K c0Finite c1Finite
      zero1 (K.d 0 primitive) hzero1 (K.differential_comp 0 primitive)
      hzero1_eq_zero supportOf component_covered_of_boundary
      component_faithful_of_boundary
  let comparison := realization.toH1Comparison
  have hDegree :
      DegreewiseCarrierDataAndExplicitFaceRestrictionEquationsBody
        data.toAdditiveH1Surface K :=
    cochainRealization_constructs_degreewiseCarrierFaceEquationsBody
      realization
  have hLayer :
      SelectedSemanticCoefficientDirectRealizationLayerBody surface data :=
    cochainRealization_constructs_selectedRealizationLayerBody
      surface data family rfl realization
  have hBoundary : GeneratedResidualBoundaryBody data :=
    generatedBoundary_constructs_residualBoundaryBody data primitive rfl
  have hAdditive : data.toAdditiveCechH1Data.H1Zero :=
    coverRelativeGeneratedBoundary_additiveH1ZeroOfPrimitive
      semanticCover K c0Finite c1Finite zero1 primitive hzero1
      hzero1_eq_zero supportOf component_covered_of_boundary
      component_faithful_of_boundary
  have hSemantic : data.toAdditiveH1Surface.H1Zero :=
    (boundedAdditiveH1Zero_iff_surfaceH1Zero data).1 hAdditive
  refine ⟨⟨surface, comparison, ?_⟩⟩
  exact
    { selectedRealizationLayer := ⟨hLayer⟩
      degreewiseCarrierFaceEquations := hDegree
      cochainRealization := ⟨realization⟩
      h1ComparisonPackage :=
        comparison.semanticRepairAdditiveH1_coverRelativeH1_comparison_package
      residualBoundary := hBoundary
      semanticH1Zero := hSemantic
      additiveH1Zero := hAdditive }

/--
Generated-boundary law-independent route tied to the law-equation body source.

This is the Research-preserving form used by the final theorem-7.5 route: the
generated residual is not selected independently, but is exactly
`K.d 0 source.toPrimitive`.

Scaffolding: this bounded route assumes `Fintype` on the degree-0/1 cochain
groups, premises absent from theorem 7.5.  The canonical theorem-7.5
entry-point is the finite-free
`lawEquation_constructs_groundedComparisonPacket_finiteFree`.
-/
theorem lawEquation_generatedBoundary_lawIndependentResearchConjuncts_fromSource
    {P : SemanticAtomProjection.{x, v}}
    (semanticCover : SemanticRepairCover.{x, v, w, x} P)
    {Ulaw : AtomCarrier.{x}}
    {Alaw : ArchitectureObject Ulaw}
    {Slaw : Site.AATSite.{x} Alaw}
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    (D : LawAlgebra.LawEquationDefectSource.{x} E)
    {coverRel : Cohomology.CoverRelativeCechCover Slaw}
    (chartSimplex : semanticCover.CoverChart -> coverRel.simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) -> coverRel.simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          coverRel.simplex 2)
    {base : Slaw.category}
    (family :
      Site.AATCoverageFamily Slaw.requirements Slaw.overlap base)
    (sheafCondition :
      Site.AATSheafCondition Slaw E.obstructionQuotientPresheaf)
    (K : Cohomology.CoverRelativeCechComplex coverRel
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        E.obstructionQuotientCoefficient sheafCondition))
    (source : LawEquationBodyCechSource D K)
    (c0Finite : Fintype (K.Cn 0)) (c1Finite : Fintype (K.Cn 1))
    (zero1 : K.Cn 1)
    (hzero1 : letI := K.cochainAddCommGroup 2; K.d 1 zero1 = 0)
    (hzero1_eq_zero : letI := K.cochainAddCommGroup 1; zero1 = 0)
    (supportOf : K.Cn 0 -> P.Support)
    (component_covered_of_boundary :
      forall boundaryPrimitive,
        K.d 0 boundaryPrimitive = K.d 0 source.toPrimitive ->
          ResidualComponentCoveredSupport P semanticCover.baseCover
            (supportOf boundaryPrimitive))
    (component_faithful_of_boundary :
      forall boundaryPrimitive,
        K.d 0 boundaryPrimitive = K.d 0 source.toPrimitive ->
          ResidualComponentFaithfulSupport P semanticCover.baseCover
            (supportOf boundaryPrimitive)) :
    Nonempty
      (Sigma fun surface :
        LawEquationGeneratedCurrentG06InputSurface
          semanticCover Slaw E.obstructionQuotientPresheaf K =>
        Sigma fun comparison :
          SemanticRepairCoverRelativeH1Comparison
            (coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
              zero1 (K.d 0 source.toPrimitive) hzero1
              (K.differential_comp 0 source.toPrimitive)
              hzero1_eq_zero supportOf component_covered_of_boundary
              component_faithful_of_boundary).toAdditiveH1Surface
            K =>
          LawEquationGroundedRouteLawIndependentConjunctsBody
            surface
            (coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
              zero1 (K.d 0 source.toPrimitive) hzero1
              (K.differential_comp 0 source.toPrimitive)
              hzero1_eq_zero supportOf component_covered_of_boundary
              component_faithful_of_boundary)
            comparison) :=
  lawEquation_generatedBoundary_lawIndependentResearchConjuncts_fromPrimitive
    semanticCover chartSimplex overlapSimplex tripleSimplex family
    sheafCondition K c0Finite c1Finite zero1 source.toPrimitive hzero1
    hzero1_eq_zero supportOf component_covered_of_boundary
    component_faithful_of_boundary

/--
Data packet returned by the generated-boundary theorem-7.5 constructors.

Implementation notes: the nested sigma type keeps the generated cover bridge
and H1 comparison visible while the subtype records the three vanishing
conclusions attached to the end-to-end packet.
-/
def LawEquationGeneratedBoundaryGroundedComparisonPacket
    {P : SemanticAtomProjection.{x, v}}
    (semanticCover : SemanticRepairCover.{x, v, w, x} P)
    {Ulaw : AtomCarrier.{x}}
    {Alaw : ArchitectureObject Ulaw}
    {Slaw : Site.AATSite.{x} Alaw}
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    (D : LawAlgebra.LawEquationDefectSource.{x} E)
    {base : Slaw.category}
    (cover : Sieve base)
    (gluingData :
      Site.AATGluingData Slaw E.obstructionQuotientPresheaf cover)
    {coverRel : Cohomology.CoverRelativeCechCover Slaw}
    {sheafCondition :
      Site.AATSheafCondition Slaw E.obstructionQuotientPresheaf}
    (K : Cohomology.CoverRelativeCechComplex coverRel
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        E.obstructionQuotientCoefficient sheafCondition))
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{x, v, w, x, y, z} P) :=
  Sigma fun _bridge : SemanticRepairCoverRelativeCoverBridge semanticCover Slaw =>
    Sigma fun comparison :
      SemanticRepairCoverRelativeH1Comparison data.toAdditiveH1Surface K =>
      Subtype (fun _ :
        SemanticRepairGeneratedEndToEndSAGAPacket.{x, v, w, x, y, z, x, x, x, x}
          (K := K)
          data D Slaw E.obstructionQuotientPresheaf cover gluingData comparison =>
        data.toAdditiveCechH1Data.H1Zero /\
          data.toAdditiveH1Surface.H1Zero /\
            comparison.CoverRelativeResidualH1Zero)

/--
Generated-boundary form of theorem 7.5.

This route does not accept a residual cocycle or H1-zero statement.  The
residual is `K.d 0 primitive`, so the residual cocycle is generated by
`d ∘ d = 0`, the bounded and finite-free H1-zero statements are generated
inside the theorem, and the cover-relative zero statement is obtained through
the generated H1 comparison.

Scaffolding: this bounded route assumes `Fintype` on the degree-0/1 cochain
groups, premises absent from theorem 7.5.  The canonical theorem-7.5
entry-point is the finite-free
`lawEquation_constructs_groundedComparisonPacket_finiteFree`.
-/
theorem lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromPrimitive
    {P : SemanticAtomProjection.{x, v}}
    (semanticCover : SemanticRepairCover.{x, v, w, x} P)
    {Ulaw : AtomCarrier.{x}}
    {Alaw : ArchitectureObject Ulaw}
    {Slaw : Site.AATSite.{x} Alaw}
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    (D : LawAlgebra.LawEquationDefectSource.{x} E)
    (hDisplayedRequiredLaws : D.DisplayedRequiredLawsHoldOn)
    {coverRel : Cohomology.CoverRelativeCechCover Slaw}
    (chartSimplex : semanticCover.CoverChart -> coverRel.simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) -> coverRel.simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          coverRel.simplex 2)
    {base : Slaw.category}
    (cover : Sieve base)
    (sheafCondition :
      Site.AATSheafCondition Slaw E.obstructionQuotientPresheaf)
    (K : Cohomology.CoverRelativeCechComplex coverRel
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        E.obstructionQuotientCoefficient sheafCondition))
    (c0Finite : Fintype (K.Cn 0)) (c1Finite : Fintype (K.Cn 1))
    (zero1 : K.Cn 1)
    (primitive : K.Cn 0)
    (hzero1 : letI := K.cochainAddCommGroup 2; K.d 1 zero1 = 0)
    (hzero1_eq_zero : letI := K.cochainAddCommGroup 1; zero1 = 0)
    (supportOf : K.Cn 0 -> P.Support)
    (component_covered_of_boundary :
      forall boundaryPrimitive,
        K.d 0 boundaryPrimitive = K.d 0 primitive ->
          ResidualComponentCoveredSupport P semanticCover.baseCover
            (supportOf boundaryPrimitive))
    (component_faithful_of_boundary :
      forall boundaryPrimitive,
        K.d 0 boundaryPrimitive = K.d 0 primitive ->
          ResidualComponentFaithfulSupport P semanticCover.baseCover
            (supportOf boundaryPrimitive))
    (cover_mem : cover ∈ Slaw.topology base)
    (gluingData :
      Site.AATGluingData Slaw E.obstructionQuotientPresheaf cover) :
    Nonempty
      (LawEquationGeneratedBoundaryGroundedComparisonPacket
        semanticCover D cover gluingData K
        (coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
          zero1 (K.d 0 primitive) hzero1 (K.differential_comp 0 primitive)
          hzero1_eq_zero supportOf component_covered_of_boundary
          component_faithful_of_boundary)) := by
  let data :=
    coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
      zero1 (K.d 0 primitive) hzero1 (K.differential_comp 0 primitive)
      hzero1_eq_zero supportOf component_covered_of_boundary
      component_faithful_of_boundary
  have hindependent :=
    lawEquation_generatedBoundary_lawIndependentConclusions_fromPrimitive
      semanticCover chartSimplex overlapSimplex tripleSimplex cover
      sheafCondition K c0Finite c1Finite zero1 primitive hzero1
      hzero1_eq_zero supportOf component_covered_of_boundary
      component_faithful_of_boundary cover_mem gluingData
  rcases hindependent with
    ⟨bridge, packetComparison, ⟨lawIndependent, hBounded, hSurface, hCover⟩⟩
  rcases
    LawAlgebra.LawEquationDefectSource.lawEquation_grounding_packet
      D hDisplayedRequiredLaws with
    ⟨hInterpretZero, hPointwiseZero, hDefectIff, hFailureDetection⟩
  rcases
    displayedRequiredLawsHoldOn_constructs_generatedSourceC0_zeroPackage
      D hDisplayedRequiredLaws with
    ⟨hZeroPackage⟩
  let packet :
      SemanticRepairGeneratedEndToEndSAGAPacket
        data D Slaw E.obstructionQuotientPresheaf cover gluingData
        packetComparison :=
    { lawDependentConclusions :=
        { generatedSourceC0ZeroPackage := hZeroPackage
          generatedInterpretationZero := hInterpretZero
          generatedInterpretationPointwiseZero := hPointwiseZero
          generatedInterpretationZero_iff_defect_mem_obstructionIdeal :=
            hDefectIff
          nonzeroInterpretationDetectsDisplayedLawFailure := hFailureDetection }
      lawIndependentConclusions := lawIndependent }
  exact ⟨⟨bridge, packetComparison, packet, hBounded, hSurface, hCover⟩⟩

/--
Lower generated-boundary tuple retaining pointwise source-C0 data only.

Scaffolding: this bounded route assumes `Fintype` on the degree-0/1 cochain
groups, premises absent from theorem 7.5.  The canonical theorem-7.5
entry-point is the finite-free
`lawEquation_constructs_groundedComparisonPacket_finiteFree`.
-/
theorem lawEquation_constructs_groundedPointwiseResearchConjuncts_fromPrimitive
    {P : SemanticAtomProjection.{x, v}}
    (semanticCover : SemanticRepairCover.{x, v, w, x} P)
    {Ulaw : AtomCarrier.{x}}
    {Alaw : ArchitectureObject Ulaw}
    {Slaw : Site.AATSite.{x} Alaw}
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    (D : LawAlgebra.LawEquationDefectSource.{x} E)
    (hDisplayedRequiredLaws : D.DisplayedRequiredLawsHoldOn)
    {coverRel : Cohomology.CoverRelativeCechCover Slaw}
    (chartSimplex : semanticCover.CoverChart -> coverRel.simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) -> coverRel.simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          coverRel.simplex 2)
    {base : Slaw.category}
    (family :
      Site.AATCoverageFamily Slaw.requirements Slaw.overlap base)
    (sheafCondition :
      Site.AATSheafCondition Slaw E.obstructionQuotientPresheaf)
    (K : Cohomology.CoverRelativeCechComplex coverRel
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        E.obstructionQuotientCoefficient sheafCondition))
    (c0Finite : Fintype (K.Cn 0)) (c1Finite : Fintype (K.Cn 1))
    (zero1 : K.Cn 1)
    (primitive : K.Cn 0)
    (hzero1 : letI := K.cochainAddCommGroup 2; K.d 1 zero1 = 0)
    (hzero1_eq_zero : letI := K.cochainAddCommGroup 1; zero1 = 0)
    (supportOf : K.Cn 0 -> P.Support)
    (component_covered_of_boundary :
      forall boundaryPrimitive,
        K.d 0 boundaryPrimitive = K.d 0 primitive ->
          ResidualComponentCoveredSupport P semanticCover.baseCover
            (supportOf boundaryPrimitive))
    (component_faithful_of_boundary :
      forall boundaryPrimitive,
        K.d 0 boundaryPrimitive = K.d 0 primitive ->
          ResidualComponentFaithfulSupport P semanticCover.baseCover
            (supportOf boundaryPrimitive))
    (source : LawEquationBodyCechSource D K) :
    Nonempty
      (Sigma fun surface :
        LawEquationGeneratedCurrentG06InputSurface
          semanticCover Slaw E.obstructionQuotientPresheaf K =>
        Sigma fun comparison :
          SemanticRepairCoverRelativeH1Comparison
            (coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
              zero1 (K.d 0 primitive) hzero1 (K.differential_comp 0 primitive)
              hzero1_eq_zero supportOf component_covered_of_boundary
              component_faithful_of_boundary).toAdditiveH1Surface
            K =>
          LawEquationGroundedComparisonPointwiseConjunctsBody D surface source
            (coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
              zero1 (K.d 0 primitive) hzero1 (K.differential_comp 0 primitive)
              hzero1_eq_zero supportOf component_covered_of_boundary
              component_faithful_of_boundary)
            comparison) := by
  let data :=
    coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
      zero1 (K.d 0 primitive) hzero1 (K.differential_comp 0 primitive)
      hzero1_eq_zero supportOf component_covered_of_boundary
      component_faithful_of_boundary
  rcases
    lawEquation_generatedBoundary_lawIndependentResearchConjuncts_fromPrimitive
      semanticCover chartSimplex overlapSimplex tripleSimplex family
      sheafCondition K c0Finite c1Finite zero1 primitive hzero1
      hzero1_eq_zero supportOf component_covered_of_boundary
      component_faithful_of_boundary with
    ⟨⟨surface, comparison, hindependent⟩⟩
  rcases
    LawAlgebra.LawEquationDefectSource.lawEquation_grounding_packet
      D hDisplayedRequiredLaws with
    ⟨_hInterpretZero, _hPointwiseZero, _hDefectIff, _hFailureDetection⟩
  refine ⟨⟨surface, comparison, ?_⟩⟩
  exact
    { displayedInterpretationRealization :=
        source.displayedRequiredLawsHoldOn_constructs_displayedInterpretationRealization
          hDisplayedRequiredLaws
      commonRestrictionRealization :=
        source.displayedRequiredLawsHoldOn_constructs_commonRestrictionRealization
          hDisplayedRequiredLaws
      baseRestrictionSourcePreservesDisplayedInterpretation :=
        source.displayedRequiredLawsHoldOn_constructs_baseRestrictionSourcePreservesDisplayedInterpretation
          hDisplayedRequiredLaws
      arrowCompatibilityLaw :=
        source.displayedRequiredLawsHoldOn_constructs_arrowCompatibilityLaw
          hDisplayedRequiredLaws
      displayedRequiredLawRestrictionEvaluator :=
        source.displayedRequiredLawsHoldOn_constructs_displayedRequiredLawRestrictionEvaluator
          hDisplayedRequiredLaws
      sourceC0PointwiseZero :=
        source.displayedRequiredLawsHoldOn_constructs_sourceC0PointwiseZero
          hDisplayedRequiredLaws
      selectedRealizationLayer := hindependent.selectedRealizationLayer
      degreewiseCarrierFaceEquations :=
        hindependent.degreewiseCarrierFaceEquations
      cochainRealization := hindependent.cochainRealization
      h1ComparisonPackage := hindependent.h1ComparisonPackage
      residualBoundary := hindependent.residualBoundary
      semanticH1Zero := hindependent.semanticH1Zero
      additiveH1Zero := hindependent.additiveH1Zero }

/--
Generated-boundary theorem-7.5 route whose generated residual is tied to the
law-equation body source primitive.

Unlike the primitive-parametrized helper, this lower theorem ties the
pointwise source-C0 reading and generated residual to `source.toPrimitive`.
It is not the theorem-7.5 completion packet because it contains no actual
source-C0 differential-zero proof.

Scaffolding: this bounded route assumes `Fintype` on the degree-0/1 cochain
groups, premises absent from theorem 7.5.  The canonical theorem-7.5
entry-point is the finite-free
`lawEquation_constructs_groundedComparisonPacket_finiteFree`.
-/
theorem lawEquation_constructs_groundedPointwiseResearchConjuncts_fromSource
    {P : SemanticAtomProjection.{x, v}}
    (semanticCover : SemanticRepairCover.{x, v, w, x} P)
    {Ulaw : AtomCarrier.{x}}
    {Alaw : ArchitectureObject Ulaw}
    {Slaw : Site.AATSite.{x} Alaw}
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    (D : LawAlgebra.LawEquationDefectSource.{x} E)
    (hDisplayedRequiredLaws : D.DisplayedRequiredLawsHoldOn)
    {coverRel : Cohomology.CoverRelativeCechCover Slaw}
    (chartSimplex : semanticCover.CoverChart -> coverRel.simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) -> coverRel.simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          coverRel.simplex 2)
    {base : Slaw.category}
    (family :
      Site.AATCoverageFamily Slaw.requirements Slaw.overlap base)
    (sheafCondition :
      Site.AATSheafCondition Slaw E.obstructionQuotientPresheaf)
    (K : Cohomology.CoverRelativeCechComplex coverRel
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        E.obstructionQuotientCoefficient sheafCondition))
    (source : LawEquationBodyCechSource D K)
    (c0Finite : Fintype (K.Cn 0)) (c1Finite : Fintype (K.Cn 1))
    (zero1 : K.Cn 1)
    (hzero1 : letI := K.cochainAddCommGroup 2; K.d 1 zero1 = 0)
    (hzero1_eq_zero : letI := K.cochainAddCommGroup 1; zero1 = 0)
    (supportOf : K.Cn 0 -> P.Support)
    (component_covered_of_boundary :
      forall boundaryPrimitive,
        K.d 0 boundaryPrimitive = K.d 0 source.toPrimitive ->
          ResidualComponentCoveredSupport P semanticCover.baseCover
            (supportOf boundaryPrimitive))
    (component_faithful_of_boundary :
      forall boundaryPrimitive,
        K.d 0 boundaryPrimitive = K.d 0 source.toPrimitive ->
          ResidualComponentFaithfulSupport P semanticCover.baseCover
            (supportOf boundaryPrimitive)) :
    Nonempty
      (Sigma fun surface :
        LawEquationGeneratedCurrentG06InputSurface
          semanticCover Slaw E.obstructionQuotientPresheaf K =>
        Sigma fun comparison :
          SemanticRepairCoverRelativeH1Comparison
            (coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
              zero1 (K.d 0 source.toPrimitive) hzero1
              (K.differential_comp 0 source.toPrimitive)
              hzero1_eq_zero supportOf component_covered_of_boundary
              component_faithful_of_boundary).toAdditiveH1Surface
            K =>
          LawEquationGroundedComparisonPointwiseConjunctsBody D surface source
            (coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
              zero1 (K.d 0 source.toPrimitive) hzero1
              (K.differential_comp 0 source.toPrimitive)
              hzero1_eq_zero supportOf component_covered_of_boundary
              component_faithful_of_boundary)
            comparison) := by
  rcases
    lawEquation_generatedBoundary_lawIndependentResearchConjuncts_fromSource
      semanticCover D chartSimplex overlapSimplex tripleSimplex family
      sheafCondition K source c0Finite c1Finite zero1 hzero1
      hzero1_eq_zero supportOf component_covered_of_boundary
      component_faithful_of_boundary with
    ⟨⟨surface, comparison, hindependent⟩⟩
  rcases
    LawAlgebra.LawEquationDefectSource.lawEquation_grounding_packet
      D hDisplayedRequiredLaws with
    ⟨_hInterpretZero, _hPointwiseZero, _hDefectIff, _hFailureDetection⟩
  refine ⟨⟨surface, comparison, ?_⟩⟩
  exact
    { displayedInterpretationRealization :=
        source.displayedRequiredLawsHoldOn_constructs_displayedInterpretationRealization
          hDisplayedRequiredLaws
      commonRestrictionRealization :=
        source.displayedRequiredLawsHoldOn_constructs_commonRestrictionRealization
          hDisplayedRequiredLaws
      baseRestrictionSourcePreservesDisplayedInterpretation :=
        source.displayedRequiredLawsHoldOn_constructs_baseRestrictionSourcePreservesDisplayedInterpretation
          hDisplayedRequiredLaws
      arrowCompatibilityLaw :=
        source.displayedRequiredLawsHoldOn_constructs_arrowCompatibilityLaw
          hDisplayedRequiredLaws
      displayedRequiredLawRestrictionEvaluator :=
        source.displayedRequiredLawsHoldOn_constructs_displayedRequiredLawRestrictionEvaluator
          hDisplayedRequiredLaws
      sourceC0PointwiseZero :=
        source.displayedRequiredLawsHoldOn_constructs_sourceC0PointwiseZero
          hDisplayedRequiredLaws
      selectedRealizationLayer := hindependent.selectedRealizationLayer
      degreewiseCarrierFaceEquations :=
        hindependent.degreewiseCarrierFaceEquations
      cochainRealization := hindependent.cochainRealization
      h1ComparisonPackage := hindependent.h1ComparisonPackage
      residualBoundary := hindependent.residualBoundary
      semanticH1Zero := hindependent.semanticH1Zero
      additiveH1Zero := hindependent.additiveH1Zero }

/--
Finite-poset generated-boundary form of theorem 7.5.

This construction removes the hand-selected cover-relative complex, zero
one-cochain, and semantic support witnesses from the theorem input.  The
cover-relative complex is `comparisonData.generalComplex`, the selected zero
one-cochain is `0`, and the support witnesses are generated by the full
semantic support.  The remaining finite data is the finite-poset comparison
surface and the selected primitive whose coboundary is the generated residual.

Scaffolding: this bounded route assumes `Fintype` on the degree-0/1 cochain
groups, premises absent from theorem 7.5.  The canonical theorem-7.5
entry-point is the finite-free
`lawEquation_constructs_groundedComparisonPacket_finiteFree`.
-/
theorem lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromFinitePosetComparisonPrimitive
    {P : SemanticAtomProjection.{x, v}}
    (semanticCover : SemanticRepairCover.{x, v, w, x} P)
    {Ulaw : AtomCarrier.{x}}
    {Alaw : ArchitectureObject Ulaw}
    {Slaw : Site.AATSite.{x} Alaw}
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    (D : LawAlgebra.LawEquationDefectSource.{x} E)
    (hDisplayedRequiredLaws : D.DisplayedRequiredLawsHoldOn)
    {Kfp : Site.FinitePosetAATSiteRegime Slaw}
    {C : Site.FinitePosetCechComplex Kfp}
    {base : Slaw.category}
    (cover : Sieve base)
    (sheafCondition :
      Site.AATSheafCondition Slaw E.obstructionQuotientPresheaf)
    (comparisonData :
      Cohomology.FinitePosetCechComparisonData C
        (Cohomology.ObstructionSheaf.ofAddCommGrpValued
          E.obstructionQuotientCoefficient sheafCondition))
    (chartSimplex :
      semanticCover.CoverChart ->
        (Cohomology.finitePosetCoverRelativeCover C).simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) ->
          (Cohomology.finitePosetCoverRelativeCover C).simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          (Cohomology.finitePosetCoverRelativeCover C).simplex 2)
    (c0Finite : Fintype (comparisonData.generalComplex.Cn 0))
    (c1Finite : Fintype (comparisonData.generalComplex.Cn 1))
    (primitive : comparisonData.generalComplex.Cn 0)
    (cover_mem : cover ∈ Slaw.topology base)
    (gluingData :
      Site.AATGluingData Slaw E.obstructionQuotientPresheaf cover) :
    Nonempty
      (LawEquationGeneratedBoundaryGroundedComparisonPacket
        semanticCover D cover gluingData comparisonData.generalComplex
        (coverRelativeBoundaryAdditiveDataOfComplex semanticCover
          comparisonData.generalComplex c0Finite c1Finite
          (0 : comparisonData.generalComplex.Cn 1)
          (comparisonData.generalComplex.d 0 primitive)
          (by
            letI := comparisonData.generalComplex.cochainAddCommGroup 1
            letI := comparisonData.generalComplex.cochainAddCommGroup 2
            exact (comparisonData.generalComplex.d 1).map_zero)
          (comparisonData.generalComplex.differential_comp 0 primitive) rfl
          (fun _ => lawEquationCompleteRepairSupport P)
          (fun _ _ =>
            (lawEquationCompleteRepairSupport_componentCoverage_and_faithfulness
              P semanticCover.baseCover).1)
          (fun _ _ =>
            (lawEquationCompleteRepairSupport_componentCoverage_and_faithfulness
              P semanticCover.baseCover).2))) :=
  lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromPrimitive
    semanticCover D hDisplayedRequiredLaws chartSimplex overlapSimplex
    tripleSimplex cover sheafCondition comparisonData.generalComplex
    c0Finite c1Finite (0 : comparisonData.generalComplex.Cn 1) primitive
      (by
        letI := comparisonData.generalComplex.cochainAddCommGroup 1
        letI := comparisonData.generalComplex.cochainAddCommGroup 2
        exact (comparisonData.generalComplex.d 1).map_zero)
      rfl
      (fun _ => lawEquationCompleteRepairSupport P)
      (fun _ _ =>
        (lawEquationCompleteRepairSupport_componentCoverage_and_faithfulness
          P semanticCover.baseCover).1)
      (fun _ _ =>
        (lawEquationCompleteRepairSupport_componentCoverage_and_faithfulness
          P semanticCover.baseCover).2)
      cover_mem gluingData

namespace StandardFinitePosetGeneratedBoundary

open Cohomology
open Cohomology.StandardFinitePosetCech

variable {Ulaw : AtomCarrier.{x}}
variable {Alaw : ArchitectureObject Ulaw}
variable {Slaw : Site.AATSite.{x} Alaw}

/-- Standard finite-poset differential is additive on obstruction coefficients. -/
theorem standardDifferential_add
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    {Ob : Cohomology.ObstructionSheaf Slaw}
    {faces :
      Site.FinitePosetCechFaceData
        (geometry.toObstructionCoefficientRegime Ob)}
    (n : Nat)
    (left right :
      Site.FinitePosetCechCochain
        (geometry.toObstructionCoefficientRegime Ob) n) :
    standardDifferential faces n (left + right) =
      standardDifferential faces n left + standardDifferential faces n right := by
  classical
  funext simplex
  let W :=
    Site.FinitePosetCechOverlapObject
      (geometry.toObstructionCoefficientRegime Ob) (n + 1) simplex
  letI := Ob.addCommGroup W
  dsimp [standardDifferential, standardAdditiveData,
    obstructionSheafStandardAlternatingCombination,
    Site.FinitePosetCechFaceRestriction]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  by_cases h : Even i.val
  · simp [h]
    exact
      Ob.map_add (homOfLE (faces.faceOverlap_le n simplex i))
        (left (faces.face n simplex i)) (right (faces.face n simplex i))
  · simp [h]
    change
      -(Ob.carrier.toPresheaf.map
          (homOfLE (faces.faceOverlap_le n simplex i)).op
          (left (faces.face n simplex i) + right (faces.face n simplex i))) =
        -(Ob.carrier.toPresheaf.map
          (homOfLE (faces.faceOverlap_le n simplex i)).op
          (left (faces.face n simplex i))) +
          -(Ob.carrier.toPresheaf.map
          (homOfLE (faces.faceOverlap_le n simplex i)).op
          (right (faces.face n simplex i)))
    rw [Ob.map_add (homOfLE (faces.faceOverlap_le n simplex i))
        (left (faces.face n simplex i)) (right (faces.face n simplex i))]
    abel

/--
Generate the cover-relative complex directly from the standard finite-poset
Čech complex.  This is the AG-body analogue of the research route's standard
finite-poset `K`: the cover is `finitePosetCoverRelativeCover`, the cochains
are the obstruction-sheaf section families, and the differential is the
standard finite-poset differential viewed as an additive homomorphism.
-/
def coverRelativeComplexOfStandardFinitePosetLaw
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    {Ob : Cohomology.ObstructionSheaf Slaw}
    {faces :
      Site.FinitePosetCechFaceData
        (geometry.toObstructionCoefficientRegime Ob)}
    (law : StandardDifferentialCompLaw geometry Ob faces) :
    Cohomology.CoverRelativeCechComplex
      (Cohomology.finitePosetCoverRelativeCover
        (standardFinitePosetCechComplex law)) Ob where
  cochainAddCommGroup := by
    intro n
    change AddCommGroup
      (Site.FinitePosetCechCochain
        (geometry.toObstructionCoefficientRegime Ob) n)
    infer_instance
  alternatingFaceCombination := by
    intro n terms simplex
    exact
      obstructionSheafStandardAlternatingCombination Ob
        (Site.FinitePosetCechOverlapObject
          (geometry.toObstructionCoefficientRegime Ob) (n + 1) simplex)
        (n + 2) (terms simplex)
  differential := by
    intro n
    letI : AddCommGroup
        (Site.FinitePosetCechCochain
          (geometry.toObstructionCoefficientRegime Ob) n) := by infer_instance
    letI : AddCommGroup
        (Site.FinitePosetCechCochain
          (geometry.toObstructionCoefficientRegime Ob) (n + 1)) := by infer_instance
    change
      Site.FinitePosetCechCochain
          (geometry.toObstructionCoefficientRegime Ob) n →+
        Site.FinitePosetCechCochain
          (geometry.toObstructionCoefficientRegime Ob) (n + 1)
    exact {
      toFun := standardDifferential faces n
      map_zero' := standardDifferential_zero faces n
      map_add' := standardDifferential_add n
    }
  differential_eq_alternatingFaceCombination := by
    intro n c
    rfl
  differential_comp := by
    intro n c
    exact law.differential_comp_zero n c

/--
For the standard generated finite-poset complex, displayed law fulfillment makes
the body source C0 cochain Cech-zero in the actual differential sense.

This proof is intentionally standard-complex specific: arbitrary
`CoverRelativeCechComplex` values may choose a non-pointwise cochain group zero,
so the differential-zero conclusion cannot be distilled at that level.
-/
theorem displayedRequiredLawsHoldOn_constructs_standardSourceC0CechZero
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    (D : LawAlgebra.LawEquationDefectSource.{x} E)
    (sheafCondition :
      Site.AATSheafCondition Slaw E.obstructionQuotientPresheaf)
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    {faces :
      Site.FinitePosetCechFaceData
        (geometry.toObstructionCoefficientRegime
          (Cohomology.ObstructionSheaf.ofAddCommGrpValued
            E.obstructionQuotientCoefficient sheafCondition))}
    (law : StandardDifferentialCompLaw geometry
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        E.obstructionQuotientCoefficient sheafCondition) faces)
    (source :
      LawEquationBodyCechSource D
        (coverRelativeComplexOfStandardFinitePosetLaw law))
    (hholds : D.DisplayedRequiredLawsHoldOn) :
    source.SourceC0CechZero := by
  let K := coverRelativeComplexOfStandardFinitePosetLaw law
  let Ob :=
    Cohomology.ObstructionSheaf.ofAddCommGrpValued
      E.obstructionQuotientCoefficient sheafCondition
  have hevaluator :=
    source.displayedRequiredLawsHoldOn_constructs_displayedRequiredLawRestrictionEvaluator
      hholds
  have harrow :=
    source.displayedRequiredLawsHoldOn_and_restrictionEvaluator_constructs_arrowCompatibilityLaw
      hholds hevaluator
  letI := K.cochainAddCommGroup 1
  change K.d 0 source.displayedSourceC0 = 0
  funext simplex
  apply
    (standardDifferential_degreeZero_eq_zero_iff_faceRestrictions_eq
      faces source.displayedSourceC0 simplex).2
  let sigma0 := faces.face 0 simplex (0 : Fin 2)
  let sigma1 := faces.face 0 simplex (1 : Fin 2)
  let f0 :
      Site.FinitePosetCechOverlapObject
          (geometry.toObstructionCoefficientRegime Ob) 1 simplex ⟶
        Site.FinitePosetCechOverlapObject
          (geometry.toObstructionCoefficientRegime Ob) 0 sigma0 :=
    homOfLE (faces.faceOverlap_le 0 simplex (0 : Fin 2))
  let f1 :
      Site.FinitePosetCechOverlapObject
          (geometry.toObstructionCoefficientRegime Ob) 1 simplex ⟶
        Site.FinitePosetCechOverlapObject
          (geometry.toObstructionCoefficientRegime Ob) 0 sigma1 :=
    homOfLE (faces.faceOverlap_le 0 simplex (1 : Fin 2))
  let g0 := f0 ≫ source.restriction sigma0
  let g1 := f1 ≫ source.restriction sigma1
  have hrestricted :=
    harrow sigma0 sigma1
      (Site.FinitePosetCechOverlapObject
        (geometry.toObstructionCoefficientRegime Ob) 1 simplex)
      g0 g1 (Subsingleton.elim _ _)
  dsimp [Site.FinitePosetCechFaceRestriction]
  change
    E.obstructionQuotientPresheaf.map f0.op
        (E.obstructionQuotientPresheaf.map (source.restriction sigma0).op
          (D.interpret (source.chartOf sigma0))) =
      E.obstructionQuotientPresheaf.map f1.op
        (E.obstructionQuotientPresheaf.map (source.restriction sigma1).op
          (D.interpret (source.chartOf sigma1)))
  rw [← CategoryTheory.FunctorToTypes.map_comp_apply,
    ← CategoryTheory.FunctorToTypes.map_comp_apply]
  simpa [g0, g1] using hrestricted

/-- Unequal displayed face restrictions reject actual source-C0 Cech zero. -/
theorem displayedFaceRestriction_ne_prevents_standardSourceC0CechZero
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    (D : LawAlgebra.LawEquationDefectSource.{x} E)
    (sheafCondition :
      Site.AATSheafCondition Slaw E.obstructionQuotientPresheaf)
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    {faces :
      Site.FinitePosetCechFaceData
        (geometry.toObstructionCoefficientRegime
          (Cohomology.ObstructionSheaf.ofAddCommGrpValued
            E.obstructionQuotientCoefficient sheafCondition))}
    (law : StandardDifferentialCompLaw geometry
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        E.obstructionQuotientCoefficient sheafCondition) faces)
    (source :
      LawEquationBodyCechSource D
        (coverRelativeComplexOfStandardFinitePosetLaw law))
    (simplex :
      Site.FinitePosetCechSimplex
        (geometry.toObstructionCoefficientRegime
          (Cohomology.ObstructionSheaf.ofAddCommGrpValued
            E.obstructionQuotientCoefficient sheafCondition)) 1)
    (hne :
      Site.FinitePosetCechFaceRestriction faces source.displayedSourceC0
          simplex (0 : Fin 2) ≠
        Site.FinitePosetCechFaceRestriction faces source.displayedSourceC0
          simplex (1 : Fin 2)) :
    ¬ source.SourceC0CechZero := by
  intro hzero
  let K := coverRelativeComplexOfStandardFinitePosetLaw law
  letI := K.cochainAddCommGroup 1
  change K.d 0 source.displayedSourceC0 = 0 at hzero
  have hat := congrFun hzero simplex
  exact hne
    ((standardDifferential_degreeZero_eq_zero_iff_faceRestrictions_eq
      faces source.displayedSourceC0 simplex).1 hat)

/--
Standard finite-poset generated-boundary form of theorem 7.5.

This route no longer accepts `FinitePosetCechComparisonData`: the
cover-relative complex is generated directly from the standard finite-poset
law and face data.

Scaffolding: this bounded route assumes `Fintype` on the degree-0/1 cochain
groups, premises absent from theorem 7.5.  The canonical theorem-7.5
entry-point is the finite-free
`lawEquation_constructs_groundedComparisonPacket_finiteFree`.
-/
theorem lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromStandardFinitePosetPrimitive
    {P : SemanticAtomProjection.{x, v}}
    (semanticCover : SemanticRepairCover.{x, v, w, x} P)
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    (D : LawAlgebra.LawEquationDefectSource.{x} E)
    (hDisplayedRequiredLaws : D.DisplayedRequiredLawsHoldOn)
    {base : Slaw.category}
    (cover : Sieve base)
    (sheafCondition :
      Site.AATSheafCondition Slaw E.obstructionQuotientPresheaf)
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    {faces :
      Site.FinitePosetCechFaceData
        (geometry.toObstructionCoefficientRegime
          (Cohomology.ObstructionSheaf.ofAddCommGrpValued
            E.obstructionQuotientCoefficient sheafCondition))}
    (law : StandardDifferentialCompLaw geometry
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        E.obstructionQuotientCoefficient sheafCondition) faces)
    (chartSimplex :
      semanticCover.CoverChart ->
        (Cohomology.finitePosetCoverRelativeCover
          (standardFinitePosetCechComplex law)).simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) ->
          (Cohomology.finitePosetCoverRelativeCover
            (standardFinitePosetCechComplex law)).simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          (Cohomology.finitePosetCoverRelativeCover
            (standardFinitePosetCechComplex law)).simplex 2)
    (c0Finite :
      Fintype ((coverRelativeComplexOfStandardFinitePosetLaw law).Cn 0))
    (c1Finite :
      Fintype ((coverRelativeComplexOfStandardFinitePosetLaw law).Cn 1))
    (primitive : (coverRelativeComplexOfStandardFinitePosetLaw law).Cn 0)
    (cover_mem : cover ∈ Slaw.topology base)
    (gluingData :
      Site.AATGluingData Slaw E.obstructionQuotientPresheaf cover) :
    Nonempty
      (LawEquationGeneratedBoundaryGroundedComparisonPacket
        semanticCover D cover gluingData
        (coverRelativeComplexOfStandardFinitePosetLaw law)
        (coverRelativeBoundaryAdditiveDataOfComplex semanticCover
          (coverRelativeComplexOfStandardFinitePosetLaw law) c0Finite c1Finite
          (0 : (coverRelativeComplexOfStandardFinitePosetLaw law).Cn 1)
          ((coverRelativeComplexOfStandardFinitePosetLaw law).d 0 primitive)
          (by
            letI :=
              (coverRelativeComplexOfStandardFinitePosetLaw law).cochainAddCommGroup 1
            letI :=
              (coverRelativeComplexOfStandardFinitePosetLaw law).cochainAddCommGroup 2
            exact ((coverRelativeComplexOfStandardFinitePosetLaw law).d 1).map_zero)
          ((coverRelativeComplexOfStandardFinitePosetLaw law).differential_comp
            0 primitive) rfl
          (fun _ => lawEquationCompleteRepairSupport P)
          (fun _ _ =>
            (lawEquationCompleteRepairSupport_componentCoverage_and_faithfulness
              P semanticCover.baseCover).1)
          (fun _ _ =>
            (lawEquationCompleteRepairSupport_componentCoverage_and_faithfulness
              P semanticCover.baseCover).2))) :=
  lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromPrimitive
      semanticCover D hDisplayedRequiredLaws chartSimplex overlapSimplex
      tripleSimplex cover sheafCondition
      (coverRelativeComplexOfStandardFinitePosetLaw law)
      c0Finite c1Finite
      (0 : (coverRelativeComplexOfStandardFinitePosetLaw law).Cn 1)
      primitive
        (by
          letI := (coverRelativeComplexOfStandardFinitePosetLaw law).cochainAddCommGroup 1
          letI := (coverRelativeComplexOfStandardFinitePosetLaw law).cochainAddCommGroup 2
          exact ((coverRelativeComplexOfStandardFinitePosetLaw law).d 1).map_zero)
        rfl
        (fun _ => lawEquationCompleteRepairSupport P)
        (fun _ _ =>
          (lawEquationCompleteRepairSupport_componentCoverage_and_faithfulness
            P semanticCover.baseCover).1)
        (fun _ _ =>
          (lawEquationCompleteRepairSupport_componentCoverage_and_faithfulness
            P semanticCover.baseCover).2)
        cover_mem gluingData

/--
Standard finite-poset theorem-7.5 route tied to the body source primitive and
exposing the actual source C0 differential-zero conjunct.

Scaffolding: this bounded route assumes `Fintype` on the degree-0/1 cochain
groups, premises absent from theorem 7.5.  The canonical theorem-7.5
entry-point is the finite-free
`lawEquation_constructs_groundedComparisonPacket_finiteFree`.
-/
theorem lawEquation_constructs_groundedResearchConjuncts_fromStandardFinitePosetSource
    {P : SemanticAtomProjection.{x, v}}
    (semanticCover : SemanticRepairCover.{x, v, w, x} P)
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    (D : LawAlgebra.LawEquationDefectSource.{x} E)
    (hDisplayedRequiredLaws : D.DisplayedRequiredLawsHoldOn)
    (sheafCondition :
      Site.AATSheafCondition Slaw E.obstructionQuotientPresheaf)
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    {faces :
      Site.FinitePosetCechFaceData
        (geometry.toObstructionCoefficientRegime
          (Cohomology.ObstructionSheaf.ofAddCommGrpValued
            E.obstructionQuotientCoefficient sheafCondition))}
    (law : StandardDifferentialCompLaw geometry
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        E.obstructionQuotientCoefficient sheafCondition) faces)
    (chartSimplex :
      semanticCover.CoverChart ->
        (Cohomology.finitePosetCoverRelativeCover
          (standardFinitePosetCechComplex law)).simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) ->
          (Cohomology.finitePosetCoverRelativeCover
            (standardFinitePosetCechComplex law)).simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          (Cohomology.finitePosetCoverRelativeCover
            (standardFinitePosetCechComplex law)).simplex 2)
    (source :
      LawEquationBodyCechSource D
        (coverRelativeComplexOfStandardFinitePosetLaw law))
    (c0Finite :
      Fintype ((coverRelativeComplexOfStandardFinitePosetLaw law).Cn 0))
    (c1Finite :
      Fintype ((coverRelativeComplexOfStandardFinitePosetLaw law).Cn 1)) :
    Nonempty
      (Sigma fun surface :
        LawEquationGeneratedCurrentG06InputSurface
          semanticCover Slaw E.obstructionQuotientPresheaf
          (coverRelativeComplexOfStandardFinitePosetLaw law) =>
        Sigma fun comparison :
          SemanticRepairCoverRelativeH1Comparison
            (coverRelativeBoundaryAdditiveDataOfComplex semanticCover
              (coverRelativeComplexOfStandardFinitePosetLaw law) c0Finite c1Finite
              (0 : (coverRelativeComplexOfStandardFinitePosetLaw law).Cn 1)
              ((coverRelativeComplexOfStandardFinitePosetLaw law).d 0 source.toPrimitive)
              (by
                let K := coverRelativeComplexOfStandardFinitePosetLaw law
                letI := K.cochainAddCommGroup 1
                letI := K.cochainAddCommGroup 2
                exact (K.d 1).map_zero)
              ((coverRelativeComplexOfStandardFinitePosetLaw law).differential_comp
                0 source.toPrimitive)
              rfl
                (fun _ => lawEquationCompleteRepairSupport P)
                (fun _ _ =>
                  (lawEquationCompleteRepairSupport_componentCoverage_and_faithfulness
                    P semanticCover.baseCover).1)
                (fun _ _ =>
                  (lawEquationCompleteRepairSupport_componentCoverage_and_faithfulness
                    P semanticCover.baseCover).2)).toAdditiveH1Surface
            (coverRelativeComplexOfStandardFinitePosetLaw law) =>
          LawEquationGroundedComparisonConjunctsBody
            D surface source
            (coverRelativeBoundaryAdditiveDataOfComplex semanticCover
              (coverRelativeComplexOfStandardFinitePosetLaw law) c0Finite c1Finite
              (0 : (coverRelativeComplexOfStandardFinitePosetLaw law).Cn 1)
              ((coverRelativeComplexOfStandardFinitePosetLaw law).d 0 source.toPrimitive)
              (by
                let K := coverRelativeComplexOfStandardFinitePosetLaw law
                letI := K.cochainAddCommGroup 1
                letI := K.cochainAddCommGroup 2
                exact (K.d 1).map_zero)
              ((coverRelativeComplexOfStandardFinitePosetLaw law).differential_comp
                0 source.toPrimitive)
              rfl
                (fun _ => lawEquationCompleteRepairSupport P)
                (fun _ _ =>
                  (lawEquationCompleteRepairSupport_componentCoverage_and_faithfulness
                    P semanticCover.baseCover).1)
                (fun _ _ =>
                  (lawEquationCompleteRepairSupport_componentCoverage_and_faithfulness
                    P semanticCover.baseCover).2))
  comparison) := by
  let K := coverRelativeComplexOfStandardFinitePosetLaw law
  let supportOf : K.Cn 0 -> P.Support :=
    fun _ => lawEquationCompleteRepairSupport P
  have hzero1 : letI := K.cochainAddCommGroup 2; K.d 1 (0 : K.Cn 1) = 0 := by
    letI := K.cochainAddCommGroup 1
    letI := K.cochainAddCommGroup 2
    exact (K.d 1).map_zero
  have hsourceC0 : source.SourceC0CechZero :=
    displayedRequiredLawsHoldOn_constructs_standardSourceC0CechZero
      D sheafCondition law source hDisplayedRequiredLaws
  rcases
    lawEquation_constructs_groundedPointwiseResearchConjuncts_fromSource
        semanticCover D hDisplayedRequiredLaws chartSimplex overlapSimplex
        tripleSimplex geometry.cover sheafCondition K source c0Finite c1Finite
        (0 : K.Cn 1) hzero1 rfl supportOf
        (fun _ _ =>
          (lawEquationCompleteRepairSupport_componentCoverage_and_faithfulness
            P semanticCover.baseCover).1)
        (fun _ _ =>
          (lawEquationCompleteRepairSupport_componentCoverage_and_faithfulness
            P semanticCover.baseCover).2) with
    ⟨⟨surface, comparison, conjuncts⟩⟩
  exact ⟨⟨surface, comparison,
    { toLawEquationGroundedComparisonPointwiseConjunctsBody := conjuncts
      sourceC0CechZero := hsourceC0 }⟩⟩

/-- Native generated obstruction sheaf used by the canonical tuple route. -/
def canonicalTupleGeneratedBoundaryObstructionSheaf
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    (sheafCondition :
      Site.AATSheafCondition Slaw E.obstructionQuotientPresheaf) :
    Cohomology.ObstructionSheaf Slaw :=
  Cohomology.ObstructionSheaf.ofAddCommGrpValued
    E.obstructionQuotientCoefficient sheafCondition

/--
Canonical tuple geometry generates the standard finite-poset `d ∘ d = 0` law
used by the generated-boundary theorem 7.5 route.
-/
theorem canonicalTupleGeneratedBoundaryLaw
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    (sheafCondition :
      Site.AATSheafCondition Slaw E.obstructionQuotientPresheaf)
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (tupleGeometry : Site.FinitePosetCanonicalTupleCoverGeometry geometry) :
    StandardDifferentialCompLaw tupleGeometry.toCoverGeometry
      (canonicalTupleGeneratedBoundaryObstructionSheaf
        (E := E) sheafCondition)
      ((tupleGeometry.toSimplicialFaceAction
        (canonicalTupleGeneratedBoundaryObstructionSheaf
          (E := E) sheafCondition).carrier.toPresheaf).toFaceData) :=
  canonicalTupleStandardDifferentialCompLaw tupleGeometry
    (canonicalTupleGeneratedBoundaryObstructionSheaf
      (E := E) sheafCondition)

/--
Canonical tuple generated cover-relative complex for native law-equation
obstruction coefficients.
-/
def canonicalTupleGeneratedBoundaryComplex
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    (sheafCondition :
      Site.AATSheafCondition Slaw E.obstructionQuotientPresheaf)
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (tupleGeometry : Site.FinitePosetCanonicalTupleCoverGeometry geometry) :
    Cohomology.CoverRelativeCechComplex
      (Cohomology.finitePosetCoverRelativeCover
        (canonicalTupleStandardFinitePosetCechComplex tupleGeometry
          (canonicalTupleGeneratedBoundaryObstructionSheaf
            (E := E) sheafCondition)))
      (canonicalTupleGeneratedBoundaryObstructionSheaf
        (E := E) sheafCondition) :=
  coverRelativeComplexOfStandardFinitePosetLaw
    (canonicalTupleGeneratedBoundaryLaw
      (E := E) sheafCondition tupleGeometry)

/-! ## Law-equation generated spine distilled from the research loop -/

/--
Law-equation generated finite-poset regime.

This is the body-side counterpart of the research-loop `lawEquationRegime`:
the coefficient slot is the native law-equation quotient coefficient, and the
simplex/face surface is the canonical tuple geometry.
-/
abbrev lawEquationRegime
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    (sheafCondition :
      Site.AATSheafCondition Slaw E.obstructionQuotientPresheaf)
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (tupleGeometry : Site.FinitePosetCanonicalTupleCoverGeometry geometry) :
    Site.FinitePosetAATSiteRegime Slaw :=
  tupleGeometry.toCoverGeometry.toObstructionCoefficientRegime
    (canonicalTupleGeneratedBoundaryObstructionSheaf
      (E := E) sheafCondition)

/--
Law-equation generated standard finite-poset Cech complex.

This is the body-side counterpart of the research-loop
`lawEquationStandardComplex`.  The standard differential and `d ∘ d = 0` law
come from the canonical tuple face action, not from a supplied comparison
package.
-/
abbrev lawEquationStandardComplex
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    (sheafCondition :
      Site.AATSheafCondition Slaw E.obstructionQuotientPresheaf)
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (tupleGeometry : Site.FinitePosetCanonicalTupleCoverGeometry geometry) :
    Site.FinitePosetCechComplex
      (lawEquationRegime (E := E) sheafCondition tupleGeometry) :=
  canonicalTupleStandardFinitePosetCechComplex tupleGeometry
    (canonicalTupleGeneratedBoundaryObstructionSheaf
      (E := E) sheafCondition)

/--
Law-equation generated cover-relative Cech complex.

This is the body-side counterpart of the research-loop
`lawEquationCechComplex`.  It is generated from
`lawEquationStandardComplex`, hence from the native law-equation quotient
coefficient and canonical tuple face action.
-/
abbrev lawEquationCechComplex
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    (sheafCondition :
      Site.AATSheafCondition Slaw E.obstructionQuotientPresheaf)
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (tupleGeometry : Site.FinitePosetCanonicalTupleCoverGeometry geometry) :
    Cohomology.CoverRelativeCechComplex
      (Cohomology.finitePosetCoverRelativeCover
        (lawEquationStandardComplex
          (E := E) sheafCondition tupleGeometry))
      (canonicalTupleGeneratedBoundaryObstructionSheaf
        (E := E) sheafCondition) :=
  canonicalTupleGeneratedBoundaryComplex
    (E := E) sheafCondition tupleGeometry

/-- The cover-relative cover generated by the law-equation standard complex. -/
abbrev lawEquationCoverRelativeCover
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    (sheafCondition :
      Site.AATSheafCondition Slaw E.obstructionQuotientPresheaf)
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (tupleGeometry : Site.FinitePosetCanonicalTupleCoverGeometry geometry) :
    Cohomology.CoverRelativeCechCover Slaw :=
  Cohomology.finitePosetCoverRelativeCover
    (lawEquationStandardComplex
      (E := E) sheafCondition tupleGeometry)

/--
Canonical tuple generated-boundary form of theorem 7.5.

This route does not accept a prebuilt comparison-data package or a supplied
`d ∘ d = 0` law.  The finite-poset cover-relative complex is generated from
the canonical tuple geometry and the native law-equation quotient coefficient.

Scaffolding: this bounded route assumes `Fintype` on the degree-0/1 cochain
groups, premises absent from theorem 7.5.  The canonical theorem-7.5
entry-point is the finite-free
`lawEquation_constructs_groundedComparisonPacket_finiteFree`.
-/
theorem lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromCanonicalTuplePrimitive
    {P : SemanticAtomProjection.{x, v}}
    (semanticCover : SemanticRepairCover.{x, v, w, x} P)
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    (D : LawAlgebra.LawEquationDefectSource.{x} E)
    (hDisplayedRequiredLaws : D.DisplayedRequiredLawsHoldOn)
    {base : Slaw.category}
    (cover : Sieve base)
    (sheafCondition :
      Site.AATSheafCondition Slaw E.obstructionQuotientPresheaf)
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (tupleGeometry : Site.FinitePosetCanonicalTupleCoverGeometry geometry)
    (chartSimplex :
      semanticCover.CoverChart ->
        (Cohomology.finitePosetCoverRelativeCover
          (canonicalTupleStandardFinitePosetCechComplex tupleGeometry
            (canonicalTupleGeneratedBoundaryObstructionSheaf
              (E := E) sheafCondition))).simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) ->
          (Cohomology.finitePosetCoverRelativeCover
            (canonicalTupleStandardFinitePosetCechComplex tupleGeometry
              (canonicalTupleGeneratedBoundaryObstructionSheaf
                (E := E) sheafCondition))).simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          (Cohomology.finitePosetCoverRelativeCover
            (canonicalTupleStandardFinitePosetCechComplex tupleGeometry
              (canonicalTupleGeneratedBoundaryObstructionSheaf
                (E := E) sheafCondition))).simplex 2)
    (c0Finite :
      Fintype ((canonicalTupleGeneratedBoundaryComplex
        (E := E) sheafCondition tupleGeometry).Cn 0))
    (c1Finite :
      Fintype ((canonicalTupleGeneratedBoundaryComplex
        (E := E) sheafCondition tupleGeometry).Cn 1))
    (primitive :
      (canonicalTupleGeneratedBoundaryComplex
        (E := E) sheafCondition tupleGeometry).Cn 0)
    (cover_mem : cover ∈ Slaw.topology base)
    (gluingData :
      Site.AATGluingData Slaw E.obstructionQuotientPresheaf cover) :
    let K := canonicalTupleGeneratedBoundaryComplex
      (E := E) sheafCondition tupleGeometry
    Nonempty
      (LawEquationGeneratedBoundaryGroundedComparisonPacket
        semanticCover D cover gluingData K
        (coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
          (0 : K.Cn 1) (K.d 0 primitive)
          (by
            letI := K.cochainAddCommGroup 1
            letI := K.cochainAddCommGroup 2
            exact (K.d 1).map_zero)
          (K.differential_comp 0 primitive) rfl
          (fun _ => lawEquationCompleteRepairSupport P)
          (fun _ _ =>
            (lawEquationCompleteRepairSupport_componentCoverage_and_faithfulness
              P semanticCover.baseCover).1)
          (fun _ _ =>
            (lawEquationCompleteRepairSupport_componentCoverage_and_faithfulness
              P semanticCover.baseCover).2))) :=
  lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromStandardFinitePosetPrimitive
    semanticCover D hDisplayedRequiredLaws cover sheafCondition
    (canonicalTupleGeneratedBoundaryLaw
      (E := E) sheafCondition tupleGeometry)
    chartSimplex overlapSimplex tripleSimplex c0Finite c1Finite primitive
    cover_mem gluingData

/--
Law-equation-spine form of theorem 7.5.

This entrypoint is intentionally named after the research-loop spine:
`lawEquationRegime`, `lawEquationStandardComplex`, and
`lawEquationCechComplex` are the objects consumed here.  It is not a wrapper
around a research theorem; it calls the body-side canonical tuple route.

Scaffolding: this bounded route assumes `Fintype` on the degree-0/1 cochain
groups, premises absent from theorem 7.5.  The canonical theorem-7.5
entry-point is the finite-free
`lawEquation_constructs_groundedComparisonPacket_finiteFree`.
-/
theorem lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromLawEquationSpinePrimitive
    {P : SemanticAtomProjection.{x, v}}
    (semanticCover : SemanticRepairCover.{x, v, w, x} P)
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    (D : LawAlgebra.LawEquationDefectSource.{x} E)
    (hDisplayedRequiredLaws : D.DisplayedRequiredLawsHoldOn)
    {base : Slaw.category}
    (cover : Sieve base)
    (sheafCondition :
      Site.AATSheafCondition Slaw E.obstructionQuotientPresheaf)
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (tupleGeometry : Site.FinitePosetCanonicalTupleCoverGeometry geometry)
    (chartSimplex :
      semanticCover.CoverChart ->
        (lawEquationCoverRelativeCover
          (E := E) sheafCondition tupleGeometry).simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) ->
          (lawEquationCoverRelativeCover
            (E := E) sheafCondition tupleGeometry).simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          (lawEquationCoverRelativeCover
            (E := E) sheafCondition tupleGeometry).simplex 2)
    (c0Finite :
      Fintype ((lawEquationCechComplex
        (E := E) sheafCondition tupleGeometry).Cn 0))
    (c1Finite :
      Fintype ((lawEquationCechComplex
        (E := E) sheafCondition tupleGeometry).Cn 1))
    (primitive :
      (lawEquationCechComplex
        (E := E) sheafCondition tupleGeometry).Cn 0)
    (cover_mem : cover ∈ Slaw.topology base)
    (gluingData :
      Site.AATGluingData Slaw E.obstructionQuotientPresheaf cover) :
    let K := lawEquationCechComplex (E := E) sheafCondition tupleGeometry
    Nonempty
      (LawEquationGeneratedBoundaryGroundedComparisonPacket
        semanticCover D cover gluingData K
        (coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
          (0 : K.Cn 1) (K.d 0 primitive)
          (by
            letI := K.cochainAddCommGroup 1
            letI := K.cochainAddCommGroup 2
            exact (K.d 1).map_zero)
          (K.differential_comp 0 primitive) rfl
          (fun _ => lawEquationCompleteRepairSupport P)
          (fun _ _ =>
            (lawEquationCompleteRepairSupport_componentCoverage_and_faithfulness
              P semanticCover.baseCover).1)
          (fun _ _ =>
            (lawEquationCompleteRepairSupport_componentCoverage_and_faithfulness
              P semanticCover.baseCover).2))) :=
  lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromCanonicalTuplePrimitive
    semanticCover D hDisplayedRequiredLaws cover sheafCondition tupleGeometry
    chartSimplex overlapSimplex tripleSimplex c0Finite c1Finite primitive
    cover_mem gluingData

/--
Overlap-generated law-equation-spine form of theorem 7.5.

This is the distilled body-side analogue of the research-loop route that starts
with the law-equation regime and constructs the canonical tuple geometry from
the selected finite-poset cover and the site overlap operation.

Scaffolding: this bounded route assumes `Fintype` on the degree-0/1 cochain
groups, premises absent from theorem 7.5.  The canonical theorem-7.5
entry-point is the finite-free
`lawEquation_constructs_groundedComparisonPacket_finiteFree`.
-/
theorem lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromOverlapGeneratedSpinePrimitive
    {P : SemanticAtomProjection.{x, v}}
    (semanticCover : SemanticRepairCover.{x, v, w, x} P)
    {E : ArchitecturalEquationSystem Slaw.contextPreorder}
    (D : LawAlgebra.LawEquationDefectSource.{x} E)
    (hDisplayedRequiredLaws : D.DisplayedRequiredLawsHoldOn)
    {base : Slaw.category}
    (cover : Sieve base)
    (sheafCondition :
      Site.AATSheafCondition Slaw E.obstructionQuotientPresheaf)
    (geometry : Site.FinitePosetCoverGeometry Slaw)
    (chartSimplex :
      semanticCover.CoverChart ->
        (lawEquationCoverRelativeCover
          (E := E) sheafCondition
          geometry.canonicalTupleCoverGeometryFromOverlap).simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) ->
          (lawEquationCoverRelativeCover
            (E := E) sheafCondition
            geometry.canonicalTupleCoverGeometryFromOverlap).simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          (lawEquationCoverRelativeCover
            (E := E) sheafCondition
            geometry.canonicalTupleCoverGeometryFromOverlap).simplex 2)
    (c0Finite :
      Fintype ((lawEquationCechComplex
        (E := E) sheafCondition
        geometry.canonicalTupleCoverGeometryFromOverlap).Cn 0))
    (c1Finite :
      Fintype ((lawEquationCechComplex
        (E := E) sheafCondition
        geometry.canonicalTupleCoverGeometryFromOverlap).Cn 1))
    (primitive :
      (lawEquationCechComplex
        (E := E) sheafCondition
        geometry.canonicalTupleCoverGeometryFromOverlap).Cn 0)
    (cover_mem : cover ∈ Slaw.topology base)
    (gluingData :
      Site.AATGluingData Slaw E.obstructionQuotientPresheaf cover) :
    let K := lawEquationCechComplex (E := E) sheafCondition
      geometry.canonicalTupleCoverGeometryFromOverlap
    Nonempty
      (LawEquationGeneratedBoundaryGroundedComparisonPacket
        semanticCover D cover gluingData K
        (coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
          (0 : K.Cn 1) (K.d 0 primitive)
          (by
            letI := K.cochainAddCommGroup 1
            letI := K.cochainAddCommGroup 2
            exact (K.d 1).map_zero)
          (K.differential_comp 0 primitive) rfl
          (fun _ => lawEquationCompleteRepairSupport P)
          (fun _ _ =>
            (lawEquationCompleteRepairSupport_componentCoverage_and_faithfulness
              P semanticCover.baseCover).1)
          (fun _ _ =>
            (lawEquationCompleteRepairSupport_componentCoverage_and_faithfulness
              P semanticCover.baseCover).2))) :=
  lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromLawEquationSpinePrimitive
    semanticCover D hDisplayedRequiredLaws cover sheafCondition
    geometry.canonicalTupleCoverGeometryFromOverlap
    chartSimplex overlapSimplex tripleSimplex c0Finite c1Finite primitive
    cover_mem gluingData

/-! ## Finite-free final ten-conjunct route -/

/-- Semantic-atom input whose atom vocabulary is definitionally the law carrier. -/
structure LawEquationSemanticAtomInputBody (U : AtomCarrier.{x}) where
  /-- Semantic component type receiving each law-carrier atom. -/
  Component : Type v
  /-- Projection from law-carrier atoms to semantic components. -/
  project : U.Atom -> Component
  /-- Trace-visibility token attached to each source atom. -/
  sourceTraceToken : U.Atom -> Bool

namespace LawEquationSemanticAtomInputBody

/-- Forget the law-carrier tie only after fixing the semantic atom type. -/
def toSemanticAtomProjection
    {U : AtomCarrier.{x}} (input : LawEquationSemanticAtomInputBody.{v, x} U) :
    SemanticAtomProjection.{x, v} where
  SemanticAtom := U.Atom
  Component := input.Component
  project := input.project

end LawEquationSemanticAtomInputBody

/-- Production counterpart of the Research witness-ideal geometry input. -/
structure LawEquationWitnessIdealGeometryBody
    (semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw)
    (S : Site.AATSite.{x} Alaw) where
  /-- Displayed source atom whose provenance is visible in the semantic input. -/
  supportAtom : Ulaw.Atom
  supportAtom_traceVisible :
    semanticInput.sourceTraceToken supportAtom = true
  quotientIsSheaf :
    Site.AATSheafCondition S
      S.equationSystem.obstructionQuotientPresheaf

namespace LawEquationWitnessIdealGeometryBody

/-- The witness geometry always uses the equation system selected by its site. -/
abbrev equationSystem
    {semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw}
    {S : Site.AATSite.{x} Alaw}
    (_G : LawEquationWitnessIdealGeometryBody semanticInput S) :
    ArchitecturalEquationSystem S.contextPreorder :=
  S.equationSystem

end LawEquationWitnessIdealGeometryBody

/--
Cover-indexed displayed equation input on the selected finite-poset geometry.

Implementation notes: the cover fixes the chart index and chart object.  This
structure selects the local architecture object, one required equation, and
one support Atom.  Its law support, Atom support, displayed residual, witness
membership, and quotient class are generated by the APIs below rather than
accepted as independent fields.
-/
structure FinitePosetLawEquationDefectSourceBody
    (semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw)
    (G : LawEquationWitnessIdealGeometryBody semanticInput Slaw)
    (geometry : Site.FinitePosetCoverGeometry Slaw) where
  /-- Local input type indexed by a selected cover chart. -/
  LocalInput : geometry.cover.Index -> Type x
  /-- Selected local input for each cover chart. -/
  input : (i : geometry.cover.Index) -> LocalInput i
  /-- Architecture object presented by a local input. -/
  objectOfLocalInput :
    (i : geometry.cover.Index) -> LocalInput i -> ArchitectureObject Ulaw
  /-- Required equation selected at each cover chart. -/
  equationIndex :
    (i : geometry.cover.Index) -> G.equationSystem.RequiredIndex
  /-- Atom at which the selected equation residual is displayed. -/
  supportAtom : (i : geometry.cover.Index) -> Ulaw.Atom
  /-- The displayed support Atom has semantic source-trace provenance. -/
  supportAtom_traceVisible :
    forall i : geometry.cover.Index,
      semanticInput.sourceTraceToken (supportAtom i) = true

namespace FinitePosetLawEquationDefectSourceBody

/-- The compatibility Atom-support view is generated as the displayed singleton. -/
def atomSupport
    {semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw}
    {G : LawEquationWitnessIdealGeometryBody semanticInput Slaw}
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry)
    (i : geometry.cover.Index) (_localInput : D.LocalInput i) :
    List Ulaw.Atom :=
  [D.supportAtom i]

/-- Generated Atom support contains a trace-visible Atom at every local input. -/
theorem atomSupport_traceVisible
    {semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw}
    {G : LawEquationWitnessIdealGeometryBody semanticInput Slaw}
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry)
    (i : geometry.cover.Index) (localInput : D.LocalInput i) :
    exists atom : Ulaw.Atom,
      atom ∈ D.atomSupport i localInput /\
        semanticInput.sourceTraceToken atom = true :=
  ⟨D.supportAtom i, by simp [atomSupport], D.supportAtom_traceVisible i⟩

/-- The compatibility law-support view is generated as the selected singleton. -/
def lawSupport
    {semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw}
    {G : LawEquationWitnessIdealGeometryBody semanticInput Slaw}
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry)
    (i : geometry.cover.Index) (_localInput : D.LocalInput i) :
    List G.equationSystem.Index :=
  [(D.equationIndex i).1]

/-- Generated law support is inhabited at every finite-poset chart. -/
theorem lawSupport_nonempty
    {semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw}
    {G : LawEquationWitnessIdealGeometryBody semanticInput Slaw}
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry)
    (i : geometry.cover.Index) :
    exists lawIndex : G.equationSystem.Index,
      lawIndex ∈ D.lawSupport i (D.input i) :=
  ⟨(D.equationIndex i).1, by simp [lawSupport]⟩

/-- Every equation in generated finite-poset law support is required. -/
theorem lawSupport_required
    {semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw}
    {G : LawEquationWitnessIdealGeometryBody semanticInput Slaw}
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry)
    (i : geometry.cover.Index) (lawIndex : G.equationSystem.Index)
    (hmem : lawIndex ∈ D.lawSupport i (D.input i)) :
    G.equationSystem.Required lawIndex := by
  have heq : lawIndex = (D.equationIndex i).1 := by
    simpa [lawSupport] using hmem
  subst lawIndex
  exact (D.equationIndex i).2

/-- The finite-poset displayed residual is generated from the selected equation data. -/
def defect
    {semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw}
    {G : LawEquationWitnessIdealGeometryBody semanticInput Slaw}
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry)
    (i : geometry.cover.Index) (localInput : D.LocalInput i) :
    G.equationSystem.Observable
      (Site.ContextCategoryObject.of Slaw.contextPreorder
        (geometry.cover.patch i)) :=
  G.equationSystem.equationResidual
    (Site.ContextCategoryObject.of Slaw.contextPreorder
      (geometry.cover.patch i))
    (D.objectOfLocalInput i localInput)
    (D.equationIndex i).1 (D.supportAtom i)

/--
The finite-poset displayed defect is characterized by its selected equation
residual.  The simp direction exposes the canonical residual expression for
downstream equation APIs.
-/
@[simp] theorem defect_eq_equationResidual
    {semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw}
    {G : LawEquationWitnessIdealGeometryBody semanticInput Slaw}
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry)
    (i : geometry.cover.Index) (localInput : D.LocalInput i) :
    D.defect i localInput =
      G.equationSystem.equationResidual
        (Site.ContextCategoryObject.of Slaw.contextPreorder
          (geometry.cover.patch i))
        (D.objectOfLocalInput i localInput)
        (D.equationIndex i).1 (D.supportAtom i) :=
  rfl

/-- Forget only the finite-poset chart indexing, retaining all law data. -/
def toLawEquationDefectSource
    {semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw}
    {G : LawEquationWitnessIdealGeometryBody semanticInput Slaw}
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry) :
    LawAlgebra.LawEquationDefectSource G.equationSystem where
  Chart := geometry.cover.Index
  chart := fun i =>
    Site.ContextCategoryObject.of Slaw.contextPreorder (geometry.cover.patch i)
  LocalInput := D.LocalInput
  input := D.input
  objectOfLocalInput := D.objectOfLocalInput
  equationIndex := D.equationIndex
  supportAtom := D.supportAtom

/--
Projection to the generic displayed source uses the context selected by the
finite-poset cover.
-/
@[simp] theorem toLawEquationDefectSource_chart
    {semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw}
    {G : LawEquationWitnessIdealGeometryBody semanticInput Slaw}
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry)
    (i : geometry.cover.Index) :
    D.toLawEquationDefectSource.chart i =
      Site.ContextCategoryObject.of Slaw.contextPreorder
        (geometry.cover.patch i) :=
  rfl

/--
Projection to the generic displayed source preserves the selected local input.
-/
@[simp] theorem toLawEquationDefectSource_input
    {semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw}
    {G : LawEquationWitnessIdealGeometryBody semanticInput Slaw}
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry)
    (i : geometry.cover.Index) :
    D.toLawEquationDefectSource.input i = D.input i :=
  rfl

/--
Projection to the generic displayed source preserves the generated residual.
The simp direction rewrites the projected defect to the finite-poset source API
without exposing the projection's structure fields.
-/
@[simp] theorem toLawEquationDefectSource_defect
    {semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw}
    {G : LawEquationWitnessIdealGeometryBody semanticInput Slaw}
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry)
    (i : geometry.cover.Index) (localInput : D.LocalInput i) :
    D.toLawEquationDefectSource.defect i localInput =
      D.defect i localInput :=
  rfl

/-- Displayed-law fulfillment for the generated generic defect source. -/
abbrev DisplayedRequiredLawsHoldOn
    {semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw}
    {G : LawEquationWitnessIdealGeometryBody semanticInput Slaw}
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry) : Prop :=
  D.toLawEquationDefectSource.DisplayedRequiredLawsHoldOn

/-- Generate the body Cech source from finite-poset simplex provenance. -/
def toLawEquationBodyCechSource
    {semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw}
    {G : LawEquationWitnessIdealGeometryBody semanticInput Slaw}
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry) :
    LawEquationBodyCechSource D.toLawEquationDefectSource
      (lawEquationCechComplex (E := G.equationSystem) G.quotientIsSheaf
        geometry.canonicalTupleCoverGeometryFromOverlap) where
  chartOf := fun sigma => sigma 0
  chartToBase := fun sigma =>
    homOfLE
      (show Slaw.contextPreorder.le
          (geometry.cover.patch (sigma 0)) geometry.base.ctx from
        geometry.cover.inclusion (sigma 0))
  restriction := fun sigma =>
    homOfLE
      (show Slaw.contextPreorder.le
          (geometry.canonicalTupleOverlapFromOverlap 0 sigma)
          (geometry.cover.patch (sigma 0)) from
        geometry.canonicalTupleOverlapFromOverlap_le_patch 0 sigma 0)

/--
At degree zero, the canonical tuple overlap is the selected patch, so the
generated body source restricts a displayed interpretation along the identity.
This comparison keeps downstream consumers independent of both source
projection implementations.
-/
@[simp] theorem toLawEquationBodyCechSource_restrictedDisplayedInterpretation
    {semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw}
    {G : LawEquationWitnessIdealGeometryBody semanticInput Slaw}
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry)
    (sigma :
      Site.FinitePosetCechCanonicalTupleSimplex geometry.cover.Index 0) :
    D.toLawEquationBodyCechSource.restrictedDisplayedInterpretation sigma =
      D.toLawEquationDefectSource.interpret (sigma 0) := by
  simp [LawEquationBodyCechSource.restrictedDisplayedInterpretation,
    FinitePosetLawEquationDefectSourceBody.toLawEquationBodyCechSource]
  exact
    G.equationSystem.obstructionQuotientRestrict_id_apply _
      (D.toLawEquationDefectSource.interpret (sigma 0))

end FinitePosetLawEquationDefectSourceBody

/--
Semantic coefficient geometry generated from the same rich witness geometry
and defect input as the law-equation source.
-/
structure LawEquationGeneratedSemanticCoefficientGeometryBody
    {semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw}
    {G : LawEquationWitnessIdealGeometryBody semanticInput Slaw}
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry) where
  /-- Coefficient presheaf generated by the witness geometry. -/
  coefficient : Site.AATPresheaf Slaw
  coefficient_eq : coefficient = G.equationSystem.obstructionQuotientPresheaf
  isSheaf : Site.AATSheafCondition Slaw coefficient
  supportAtomTraceVisible :
    semanticInput.sourceTraceToken G.supportAtom = true
  localAtomSupportTraceVisible :
    forall (i : geometry.cover.Index) (localInput : D.LocalInput i),
      exists atom : Ulaw.Atom,
        atom ∈ D.atomSupport i localInput /\
          semanticInput.sourceTraceToken atom = true

/-- Generate semantic coefficient provenance without accepting a certificate. -/
def FinitePosetLawEquationDefectSourceBody.toGeneratedSemanticCoefficientGeometry
    {semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw}
    {G : LawEquationWitnessIdealGeometryBody semanticInput Slaw}
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry) :
    LawEquationGeneratedSemanticCoefficientGeometryBody D where
  coefficient := G.equationSystem.obstructionQuotientPresheaf
  coefficient_eq := rfl
  isSheaf := G.quotientIsSheaf
  supportAtomTraceVisible := G.supportAtom_traceVisible
  localAtomSupportTraceVisible := D.atomSupport_traceVisible

/-- Atom-supported source for the finite-free realization used by conjunct 4. -/
structure LawEquationAtomSupportedFiniteFreeRealizationSourceBody
    {semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw}
    {G : LawEquationWitnessIdealGeometryBody semanticInput Slaw}
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry)
    {coverRel : Cohomology.CoverRelativeCechCover Slaw}
    {Ob : Cohomology.ObstructionSheaf Slaw}
    {K : Cohomology.CoverRelativeCechComplex coverRel Ob}
    (source : LawEquationBodyCechSource D.toLawEquationDefectSource K)
    (additive : SemanticRepairAdditiveH1Surface) where
  /-- Atom support attached to each degree-zero simplex. -/
  supportAtSimplex : coverRel.simplex 0 -> List Ulaw.Atom
  supportAtSimplex_eq :
    forall sigma,
      supportAtSimplex sigma =
        D.atomSupport (source.chartOf sigma) (D.input (source.chartOf sigma))
  supportAtSimplex_traceVisible :
    forall sigma,
      exists atom : Ulaw.Atom,
        atom ∈ supportAtSimplex sigma /\
          semanticInput.sourceTraceToken atom = true
  /-- Coefficient geometry generated from the same defect input. -/
  coefficientGeometry : LawEquationGeneratedSemanticCoefficientGeometryBody D
  /-- Concrete cochain realization used for the H1 comparison. -/
  realization : SemanticRepairCoverRelativeCochainRealization additive K

/-- Generate the atom-supported realization source from D and the body source. -/
def FinitePosetLawEquationDefectSourceBody.toAtomSupportedFiniteFreeRealizationSource
    {semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw}
    {G : LawEquationWitnessIdealGeometryBody semanticInput Slaw}
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry)
    {coverRel : Cohomology.CoverRelativeCechCover Slaw}
    {Ob : Cohomology.ObstructionSheaf Slaw}
    {K : Cohomology.CoverRelativeCechComplex coverRel Ob}
    (source : LawEquationBodyCechSource D.toLawEquationDefectSource K)
    (additive : SemanticRepairAdditiveH1Surface)
    (realization : SemanticRepairCoverRelativeCochainRealization additive K) :
    LawEquationAtomSupportedFiniteFreeRealizationSourceBody
      D source additive where
  supportAtSimplex := fun sigma =>
    D.atomSupport (source.chartOf sigma) (D.input (source.chartOf sigma))
  supportAtSimplex_eq := fun _ => rfl
  supportAtSimplex_traceVisible := fun sigma =>
    D.atomSupport_traceVisible
      (source.chartOf sigma) (D.input (source.chartOf sigma))
  coefficientGeometry := D.toGeneratedSemanticCoefficientGeometry
  realization := realization

/--
Selected layer constructed from the atom-supported realization source rather
than pairing trace provenance with an independently built layer.
-/
structure LawEquationSelectedSemanticCoefficientFiniteFreeLayerBody
    {semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw}
    {semanticCover :
      SemanticRepairCover.{x, v, w, x} semanticInput.toSemanticAtomProjection}
    {G : LawEquationWitnessIdealGeometryBody semanticInput Slaw}
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry)
    {coverRel : Cohomology.CoverRelativeCechCover Slaw}
    {Ob : Cohomology.ObstructionSheaf Slaw}
    {K : Cohomology.CoverRelativeCechComplex coverRel Ob}
    (source : LawEquationBodyCechSource D.toLawEquationDefectSource K)
    (surface :
      LawEquationGeneratedCurrentG06InputSurface
        semanticCover Slaw G.equationSystem.obstructionQuotientPresheaf K)
    (additive : SemanticRepairAdditiveH1Surface) where
  /-- Atom-supported realization source underlying the selected layer. -/
  atomSupportedSource :
    LawEquationAtomSupportedFiniteFreeRealizationSourceBody D source additive
  /-- Coverage family whose generated sieve is the selected cover. -/
  family : Site.AATCoverageFamily Slaw.requirements Slaw.overlap surface.coverBase
  cover_eq : surface.selectedCover = Sieve.generate family.presieve

/-- The R4 layer is generated from the realization carried by the atom-supported source. -/
def LawEquationSelectedSemanticCoefficientFiniteFreeLayerBody.toFiniteFreeLayer
    {semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw}
    {semanticCover :
      SemanticRepairCover.{x, v, w, x} semanticInput.toSemanticAtomProjection}
    {G : LawEquationWitnessIdealGeometryBody semanticInput Slaw}
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    {D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry}
    {coverRel : Cohomology.CoverRelativeCechCover Slaw}
    {Ob : Cohomology.ObstructionSheaf Slaw}
    {K : Cohomology.CoverRelativeCechComplex coverRel Ob}
    {source : LawEquationBodyCechSource D.toLawEquationDefectSource K}
    {surface :
      LawEquationGeneratedCurrentG06InputSurface
        semanticCover Slaw G.equationSystem.obstructionQuotientPresheaf K}
    {additive : SemanticRepairAdditiveH1Surface}
    (layer : LawEquationSelectedSemanticCoefficientFiniteFreeLayerBody
      D source surface additive) :
    SelectedSemanticCoefficientFiniteFreeRealizationLayerBody surface additive :=
  cochainRealization_constructs_finiteFreeSelectedRealizationLayerBody
    surface additive layer.family layer.cover_eq
      layer.atomSupportedSource.realization

/--
The ten body conjuncts corresponding one-for-one to the Research theorem.
Fields 1--3 are law-dependent; fields 4--10 are generated from the selected
cover-relative primitive without using displayed-law fulfillment.
-/
structure LawEquationGroundedComparisonFiniteFreeConjunctsBody
    {semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw}
    {semanticCover :
      SemanticRepairCover.{x, v, w, x} semanticInput.toSemanticAtomProjection}
    {G : LawEquationWitnessIdealGeometryBody semanticInput Slaw}
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry)
    (surface :
      LawEquationGeneratedCurrentG06InputSurface
        semanticCover Slaw G.equationSystem.obstructionQuotientPresheaf
        (lawEquationCechComplex (E := G.equationSystem) G.quotientIsSheaf
          geometry.canonicalTupleCoverGeometryFromOverlap))
    (source :
      LawEquationBodyCechSource D.toLawEquationDefectSource
        (lawEquationCechComplex (E := G.equationSystem) G.quotientIsSheaf
          geometry.canonicalTupleCoverGeometryFromOverlap)) :
    Type (max (x + 1) (max v w)) where
  displayedInterpretationRealization :
    source.DisplayedInterpretationRealization
  displayedRequiredLawRestrictionEvaluator :
    source.DisplayedRequiredLawRestrictionEvaluator
  sourceC0CechZero : source.SourceC0CechZero
  selectedRealizationLayer :
    Nonempty
      (LawEquationSelectedSemanticCoefficientFiniteFreeLayerBody D source surface
        (coverRelativeGeneratedBoundaryAdditiveH1Surface
          (lawEquationCechComplex (E := G.equationSystem) G.quotientIsSheaf
            geometry.canonicalTupleCoverGeometryFromOverlap)
          source.toPrimitive))
  degreewiseCarrierFaceEquations :
    DegreewiseCarrierDataAndExplicitFaceRestrictionEquationsBody
      (coverRelativeGeneratedBoundaryAdditiveH1Surface
        (lawEquationCechComplex (E := G.equationSystem) G.quotientIsSheaf
          geometry.canonicalTupleCoverGeometryFromOverlap)
        source.toPrimitive)
      (lawEquationCechComplex (E := G.equationSystem) G.quotientIsSheaf
        geometry.canonicalTupleCoverGeometryFromOverlap)
  cochainRealization :
    Nonempty
      (SemanticRepairCoverRelativeCochainRealization
        (coverRelativeGeneratedBoundaryAdditiveH1Surface
          (lawEquationCechComplex (E := G.equationSystem) G.quotientIsSheaf
            geometry.canonicalTupleCoverGeometryFromOverlap)
          source.toPrimitive)
        (lawEquationCechComplex (E := G.equationSystem) G.quotientIsSheaf
          geometry.canonicalTupleCoverGeometryFromOverlap))
  h1ComparisonPackage :
    Nonempty
      (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
        (coverRelativeGeneratedBoundaryCochainRealization
          (lawEquationCechComplex (E := G.equationSystem) G.quotientIsSheaf
            geometry.canonicalTupleCoverGeometryFromOverlap)
          source.toPrimitive).toH1Comparison)
  residualBoundary :
    GeneratedResidualBoundarySurfaceBody
      (coverRelativeGeneratedBoundaryAdditiveH1Surface
        (lawEquationCechComplex (E := G.equationSystem) G.quotientIsSheaf
          geometry.canonicalTupleCoverGeometryFromOverlap)
        source.toPrimitive)
  semanticH1Zero :
    GeneratedSemanticH1ZeroBody
      (coverRelativeGeneratedBoundaryAdditiveH1Surface
        (lawEquationCechComplex (E := G.equationSystem) G.quotientIsSheaf
          geometry.canonicalTupleCoverGeometryFromOverlap)
        source.toPrimitive)
  additiveH1Zero :
    (coverRelativeGeneratedBoundaryAdditiveH1Surface
      (lawEquationCechComplex (E := G.equationSystem) G.quotientIsSheaf
        geometry.canonicalTupleCoverGeometryFromOverlap)
      source.toPrimitive).H1Zero

/-- Law-independent construction of final conjuncts 4--10. -/
theorem lawEquation_constructs_finiteFreeLawIndependentConjuncts
    (semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw)
    (semanticCover :
      SemanticRepairCover.{x, v, w, x} semanticInput.toSemanticAtomProjection)
    (G : LawEquationWitnessIdealGeometryBody semanticInput Slaw)
    (geometry : Site.FinitePosetCoverGeometry Slaw)
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry)
    (chartSimplex :
      semanticCover.CoverChart ->
        (lawEquationCoverRelativeCover (E := G.equationSystem) G.quotientIsSheaf
          geometry.canonicalTupleCoverGeometryFromOverlap).simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) ->
          (lawEquationCoverRelativeCover (E := G.equationSystem) G.quotientIsSheaf
            geometry.canonicalTupleCoverGeometryFromOverlap).simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          (lawEquationCoverRelativeCover (E := G.equationSystem) G.quotientIsSheaf
            geometry.canonicalTupleCoverGeometryFromOverlap).simplex 2) :
    let K := lawEquationCechComplex (E := G.equationSystem) G.quotientIsSheaf
      geometry.canonicalTupleCoverGeometryFromOverlap
    let source := D.toLawEquationBodyCechSource
    let surface := lawEquationGeneratedCurrentG06InputSurfaceOfFinitePosetGeometry
      semanticCover geometry K chartSimplex overlapSimplex tripleSimplex G.quotientIsSheaf
    let additive := coverRelativeGeneratedBoundaryAdditiveH1Surface K source.toPrimitive
    let realization := coverRelativeGeneratedBoundaryCochainRealization K source.toPrimitive
    Nonempty (LawEquationSelectedSemanticCoefficientFiniteFreeLayerBody
      D source surface additive) /\
      DegreewiseCarrierDataAndExplicitFaceRestrictionEquationsBody additive K /\
      Nonempty (SemanticRepairCoverRelativeCochainRealization additive K) /\
      Nonempty
        (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
          realization.toH1Comparison) /\
      GeneratedResidualBoundarySurfaceBody additive /\
      GeneratedSemanticH1ZeroBody additive /\
      additive.H1Zero := by
  dsimp
  let K := lawEquationCechComplex (E := G.equationSystem) G.quotientIsSheaf
    geometry.canonicalTupleCoverGeometryFromOverlap
  let source := D.toLawEquationBodyCechSource
  let surface := lawEquationGeneratedCurrentG06InputSurfaceOfFinitePosetGeometry
    semanticCover geometry K chartSimplex overlapSimplex tripleSimplex G.quotientIsSheaf
  let additive := coverRelativeGeneratedBoundaryAdditiveH1Surface K source.toPrimitive
  let realization := coverRelativeGeneratedBoundaryCochainRealization K source.toPrimitive
  have hlayer :
      Nonempty (LawEquationSelectedSemanticCoefficientFiniteFreeLayerBody
        D source surface additive) :=
    ⟨{ atomSupportedSource :=
        D.toAtomSupportedFiniteFreeRealizationSource source additive realization
       family := geometry.cover
       cover_eq := rfl }⟩
  have hface : DegreewiseCarrierDataAndExplicitFaceRestrictionEquationsBody additive K :=
    cochainRealization_constructs_degreewiseCarrierFaceEquationsBody realization
  have hcomparison :
      Nonempty
        (SemanticRepairCoverRelativeH1Comparison.SemanticRepairAdditiveH1CoverRelativeH1ComparisonPackage
          realization.toH1Comparison) :=
    ⟨realization.toH1Comparison.semanticRepairAdditiveH1_coverRelativeH1_comparison_packageData⟩
  have hboundary : GeneratedResidualBoundarySurfaceBody additive :=
    ⟨source.toPrimitive, rfl⟩
  have hsemantic := residualBoundaryBody_constructs_semanticH1ZeroBody hboundary
  have hadditive := semanticH1ZeroBody_constructs_additiveH1Zero hsemantic
  exact ⟨hlayer, hface, ⟨realization⟩, hcomparison,
    hboundary, hsemantic, hadditive⟩

/--
**Canonical theorem-7.5 witness.**  Final production theorem corresponding to
the Research ten-conjunct packet.

The standard law, cover-relative complex, selected generated cover, Cech
source, additive surface, realization, comparison, residual witness, and both
H1-zero conclusions are all generated internally.  No cochain finiteness is
assumed, matching the input specification of theorem 7.5 in the body text;
the bounded `from*` routes above are scaffolding with extra `Fintype`
premises.

Reading guard: the residual of this generated route is `K.d 0 primitive`, so
its H1 class is the zero class independently of displayed-law fulfillment
(theorem 8.2).  This theorem therefore demonstrates degree-zero vanishing on
the law-generated route, not a cancellation of a nonzero H1 class; the
nonzero-H1 instance is carried separately by example 9.2 (circle).
-/
theorem lawEquation_constructs_groundedComparisonPacket_finiteFree
    (semanticInput : LawEquationSemanticAtomInputBody.{v, x} Ulaw)
    (semanticCover :
      SemanticRepairCover.{x, v, w, x} semanticInput.toSemanticAtomProjection)
    (G : LawEquationWitnessIdealGeometryBody semanticInput Slaw)
    (geometry : Site.FinitePosetCoverGeometry Slaw)
    (D : FinitePosetLawEquationDefectSourceBody semanticInput G geometry)
    (chartSimplex :
      semanticCover.CoverChart ->
        (lawEquationCoverRelativeCover (E := G.equationSystem) G.quotientIsSheaf
          geometry.canonicalTupleCoverGeometryFromOverlap).simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) ->
          (lawEquationCoverRelativeCover (E := G.equationSystem) G.quotientIsSheaf
            geometry.canonicalTupleCoverGeometryFromOverlap).simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          (lawEquationCoverRelativeCover (E := G.equationSystem) G.quotientIsSheaf
            geometry.canonicalTupleCoverGeometryFromOverlap).simplex 2)
    (hholds : D.DisplayedRequiredLawsHoldOn) :
    let K := lawEquationCechComplex (E := G.equationSystem) G.quotientIsSheaf
      geometry.canonicalTupleCoverGeometryFromOverlap
    let source := D.toLawEquationBodyCechSource
    let surface := lawEquationGeneratedCurrentG06InputSurfaceOfFinitePosetGeometry
      semanticCover geometry K chartSimplex overlapSimplex tripleSimplex G.quotientIsSheaf
    Nonempty
      (LawEquationGroundedComparisonFiniteFreeConjunctsBody
        D surface source) := by
  dsimp
  let K := lawEquationCechComplex (E := G.equationSystem) G.quotientIsSheaf
    geometry.canonicalTupleCoverGeometryFromOverlap
  let source := D.toLawEquationBodyCechSource
  let surface := lawEquationGeneratedCurrentG06InputSurfaceOfFinitePosetGeometry
    semanticCover geometry K chartSimplex overlapSimplex tripleSimplex G.quotientIsSheaf
  rcases lawEquation_constructs_finiteFreeLawIndependentConjuncts
      semanticInput semanticCover G geometry D chartSimplex overlapSimplex tripleSimplex with
    ⟨hlayer, hface, hrealization, hcomparison, hboundary, hsemantic, hadditive⟩
  have hrealized :=
    source.displayedRequiredLawsHoldOn_constructs_displayedInterpretationRealization hholds
  have hevaluator :=
    source.displayedRequiredLawsHoldOn_constructs_displayedRequiredLawRestrictionEvaluator hholds
  have hsourceC0 :=
    displayedRequiredLawsHoldOn_constructs_standardSourceC0CechZero
      D.toLawEquationDefectSource G.quotientIsSheaf
      (canonicalTupleGeneratedBoundaryLaw (E := G.equationSystem) G.quotientIsSheaf
        geometry.canonicalTupleCoverGeometryFromOverlap)
      source hholds
  exact ⟨⟨hrealized, hevaluator, hsourceC0, hlayer, hface,
    hrealization, hcomparison, hboundary, hsemantic, hadditive⟩⟩

end StandardFinitePosetGeneratedBoundary

end SemanticRepair
end AAT.AG
