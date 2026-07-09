import Formal.AG.Cohomology.FinitePosetStandardComplex
import Formal.AG.SemanticRepair.SagaComparison

noncomputable section

namespace AAT.AG
namespace SemanticRepair

open CategoryTheory
open Opposite

universe u v w x y z r

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
The generated-boundary route assigns the complete support to every boundary
primitive, matching the Research `support_eq` field for complete-support
boundary complexes.
-/
def lawEquationCompleteSupportOf
    {P : SemanticAtomProjection.{u, v}}
    {U : AtomCarrier.{x}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    (K : Cohomology.CoverRelativeCechComplex coverRel Ob)
    (_primitive : K.Cn 0) : P.Support :=
  lawEquationCompleteRepairSupport P

/--
Complete support semantically closes every residual atom.  This is the AG-body
counterpart of the Research complete-support closure theorem.
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

/--
Generated-boundary component coverage supplied by the complete-support
translation, not by an external support certificate.
-/
theorem lawEquationCompleteSupport_componentCovered_of_boundary
    {P : SemanticAtomProjection.{u, v}}
    (semanticCover : SemanticRepairCover.{u, v, w, x} P)
    {U : AtomCarrier.{x}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    (K : Cohomology.CoverRelativeCechComplex coverRel Ob)
    (residual : K.Cn 1) :
    forall primitive,
      K.d 0 primitive = residual ->
        ResidualComponentCoveredSupport P semanticCover.baseCover
          (lawEquationCompleteSupportOf K primitive) := by
  intro _primitive _hboundary
  exact
    (lawEquationCompleteRepairSupport_componentCoverage_and_faithfulness
      P semanticCover.baseCover).1

/--
Generated-boundary residual faithfulness supplied by the complete-support
translation, not by an external support certificate.
-/
theorem lawEquationCompleteSupport_componentFaithful_of_boundary
    {P : SemanticAtomProjection.{u, v}}
    (semanticCover : SemanticRepairCover.{u, v, w, x} P)
    {U : AtomCarrier.{x}} {A : ArchitectureObject U}
    {S : Site.AATSite A}
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    (K : Cohomology.CoverRelativeCechComplex coverRel Ob)
    (residual : K.Cn 1) :
    forall primitive,
      K.d 0 primitive = residual ->
        ResidualComponentFaithfulSupport P semanticCover.baseCover
          (lawEquationCompleteSupportOf K primitive) := by
  intro _primitive _hboundary
  exact
    (lawEquationCompleteRepairSupport_componentCoverage_and_faithfulness
      P semanticCover.baseCover).2

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
  coverBridge : SemanticRepairCoverRelativeCoverBridge semanticCover S
  coverBase : S.category
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
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{u} S}
    (D : LawAlgebra.LawEquationDefectSource.{u} G)
    {coverRel : Cohomology.CoverRelativeCechCover S}
    {Ob : Cohomology.ObstructionSheaf S}
    (_K : Cohomology.CoverRelativeCechComplex coverRel Ob) where
  chartOf : coverRel.simplex 0 -> D.Chart
  chartToBase :
    (sigma : coverRel.simplex 0) ->
      D.chart (chartOf sigma) ⟶ coverRel.base
  restriction :
    forall sigma : coverRel.simplex 0,
      coverRel.overlap 0 sigma ⟶ D.chart (chartOf sigma)

namespace LawEquationBodyCechSource

variable {U : AtomCarrier.{u}}
variable {A : ArchitectureObject U}
variable {S : Site.AATSite.{u} A}
variable {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{u} S}
variable {D : LawAlgebra.LawEquationDefectSource.{u} G}
variable {coverRel : Cohomology.CoverRelativeCechCover S}
variable {sheafCondition :
  Site.AATSheafCondition S G.obstructionQuotientPresheaf}
variable {K : Cohomology.CoverRelativeCechComplex coverRel
  (Cohomology.ObstructionSheaf.ofAddCommGrpValued
    G.obstructionQuotientCoefficient sheafCondition)}

/-!
The base-restriction source is kept separate from the displayed source.  This
prevents the degree-`0` primitive from being defined as the displayed
interpretation that it is later required to realize.
-/
structure LawEquationBodyBaseRestrictionSource
    (source : LawEquationBodyCechSource D K) where
  sourceSection :
    G.ObstructionQuotient coverRel.base

namespace LawEquationBodyBaseRestrictionSource

/-- Restrict the independently supplied base section to every selected overlap. -/
def toPrimitive
    {source : LawEquationBodyCechSource D K}
    (baseSource : LawEquationBodyBaseRestrictionSource source) : K.Cn 0 :=
  fun sigma =>
    G.obstructionQuotientPresheaf.map
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
  sourceSection := (0 : G.ObstructionQuotient coverRel.base)

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
  G.obstructionQuotientPresheaf.map
    (source.restriction sigma).op
    (D.interpret (source.chartOf sigma))

/-- Research conjunct 1 at the selected degree-`0` overlaps. -/
def DisplayedInterpretationRealization
    (source : LawEquationBodyCechSource D K) : Prop :=
  forall sigma : coverRel.simplex 0,
    source.toPrimitive sigma =
      source.restrictedDisplayedInterpretation sigma

/--
Body translation of Research
`baseRestrictionSourcePreservesDisplayedInterpretation` for a selected
base-restriction source.
-/
def BaseRestrictionSourcePreservesDisplayedInterpretation
    (source : LawEquationBodyCechSource D K)
    (baseSource : LawEquationBodyBaseRestrictionSource source) : Prop :=
  forall sigma : coverRel.simplex 0,
    G.obstructionQuotientPresheaf.map
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
    G.obstructionQuotientPresheaf source.chartToBase
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
      forall (lawIndexSigma lawIndexTau : S.lawUniverse.Index),
        lawIndexSigma ∈
            D.lawSupport (source.chartOf sigma)
              (D.input (source.chartOf sigma)) ->
          lawIndexTau ∈
              D.lawSupport (source.chartOf tau)
                (D.input (source.chartOf tau)) ->
            S.lawUniverse.Required lawIndexSigma ->
              S.lawUniverse.Required lawIndexTau ->
                (S.lawUniverse.law lawIndexSigma).holds
                    (D.objectOfLocalInput (source.chartOf sigma)
                      (D.input (source.chartOf sigma))) ->
                  (S.lawUniverse.law lawIndexTau).holds
                      (D.objectOfLocalInput (source.chartOf tau)
                        (D.input (source.chartOf tau))) ->
                    G.obstructionQuotientPresheaf.map gSigma.op
                        (D.interpret (source.chartOf sigma)) =
                      G.obstructionQuotientPresheaf.map gTau.op
                        (D.interpret (source.chartOf tau))

  /-- Body translation of Research `sourceC0CechZero`. -/
  def SourceC0CechZero
    (source : LawEquationBodyCechSource D K) : Prop :=
  source.DisplayedInterpretationRealization ∧
    GeneratedSourceC0PointwiseZero D

  /--
  Body translation of Research generated-Cech `sourceC0CechZero` for a concrete
  Cech complex: the displayed source is realized, pointwise zero, and Cech-zero
  for the selected differential.
  -/
  def SourceC0GeneratedCechZero
      (source : LawEquationBodyCechSource D K) : Prop :=
    source.SourceC0CechZero ∧
      letI := K.cochainAddCommGroup 1
      K.d 0 source.toPrimitive = 0

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
    (G.obstructionQuotientCoefficient.map
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
      G.obstructionQuotientPresheaf
      source.chartToBase baseSource.sourceSection).property
  intro sigma tau Z gSigma gTau hcomm
  change
    G.obstructionQuotientPresheaf.map gSigma.op
        (D.interpret (source.chartOf sigma)) =
      G.obstructionQuotientPresheaf.map gTau.op
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
      G.obstructionQuotientPresheaf
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
      (hholds (source.chartOf sigma) lawIndexSigma hmemSigma hrequiredSigma)
      (hholds (source.chartOf tau) lawIndexTau hmemTau hrequiredTau)

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
    restrictedDisplayedInterpretation]
  rw [D.displayedRequiredLawsHoldOn_constructs_interpret_eq_zero hholds
    (source.chartOf sigma)]
  exact
    ((G.obstructionQuotientCoefficient.map
      (source.zeroSimplexToBase sigma).op).hom.map_zero).trans
      ((G.obstructionQuotientCoefficient.map
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
      (0 : G.ObstructionQuotient (coverRel.overlap 0 sigma))) :
    ¬ source.DisplayedInterpretationRealization := by
  intro hrealized
  apply hne
  calc
    source.restrictedDisplayedInterpretation sigma =
        source.toPrimitive sigma :=
      (hrealized sigma).symm
    _ = (0 : G.ObstructionQuotient (coverRel.overlap 0 sigma)) := by
      dsimp [toPrimitive, toBaseRestrictionSource,
        LawEquationBodyBaseRestrictionSource.toPrimitive]
      exact
        (G.obstructionQuotientCoefficient.map
          (source.zeroSimplexToBase sigma).op).hom.map_zero

theorem displayedRequiredLawsHoldOn_constructs_sourceC0CechZero
    (source : LawEquationBodyCechSource D K)
    (hholds : D.DisplayedRequiredLawsHoldOn) :
    source.SourceC0CechZero :=
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

/-- AG-body translation of the Research residual-boundary conjunct. -/
def GeneratedResidualBoundaryBody
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P) :
    Prop :=
  CechB1 data.boundaryRelation.cech data.boundaryRelation.cech.residual

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
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{u} Slaw}
    {coverRel : Cohomology.CoverRelativeCechCover Slaw}
    {Ob : Cohomology.ObstructionSheaf Slaw}
    {K : Cohomology.CoverRelativeCechComplex coverRel Ob}
    (surface :
      LawEquationGeneratedCurrentG06InputSurface
        semanticCover Slaw G.obstructionQuotientPresheaf K)
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
AG-body translated theorem-7.5 conjunct tuple preserving the Research packet's
visible conjuncts.
-/
structure LawEquationGroundedComparisonConjunctsBody
    {P : SemanticAtomProjection.{u, v}}
    {semanticCover : SemanticRepairCover.{u, v, w, x} P}
    {Ulaw : AtomCarrier.{u}}
    {Alaw : ArchitectureObject Ulaw}
    {Slaw : Site.AATSite.{u} Alaw}
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{u} Slaw}
    (D : LawAlgebra.LawEquationDefectSource.{u} G)
    {coverRel : Cohomology.CoverRelativeCechCover Slaw}
    {sheafCondition :
      Site.AATSheafCondition Slaw G.obstructionQuotientPresheaf}
    {K : Cohomology.CoverRelativeCechComplex coverRel
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        G.obstructionQuotientCoefficient sheafCondition)}
    (surface :
      LawEquationGeneratedCurrentG06InputSurface
        semanticCover Slaw G.obstructionQuotientPresheaf K)
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
  sourceC0CechZero : source.SourceC0CechZero
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
Stronger theorem-7.5 body tuple for generated/standard complexes: in addition
to the Research visible tuple translated by
`LawEquationGroundedComparisonConjunctsBody`, it exposes the actual Cech
differential-zero content of the source degree-0 cochain.
-/
structure LawEquationGroundedComparisonConjunctsBodyWithSourceC0DifferentialZero
    {P : SemanticAtomProjection.{u, v}}
    {semanticCover : SemanticRepairCover.{u, v, w, x} P}
    {Ulaw : AtomCarrier.{u}}
    {Alaw : ArchitectureObject Ulaw}
    {Slaw : Site.AATSite.{u} Alaw}
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{u} Slaw}
    (D : LawAlgebra.LawEquationDefectSource.{u} G)
    {coverRel : Cohomology.CoverRelativeCechCover Slaw}
    {sheafCondition :
      Site.AATSheafCondition Slaw G.obstructionQuotientPresheaf}
    {K : Cohomology.CoverRelativeCechComplex coverRel
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        G.obstructionQuotientCoefficient sheafCondition)}
    (surface :
      LawEquationGeneratedCurrentG06InputSurface
        semanticCover Slaw G.obstructionQuotientPresheaf K)
    (source : LawEquationBodyCechSource D K)
    (data : SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    (comparison :
      SemanticRepairCoverRelativeH1Comparison data.toAdditiveH1Surface K) :
    Type (max (u + 1) (max v (max w (max x (max y z))))) where
  conjuncts :
    LawEquationGroundedComparisonConjunctsBody D surface source data comparison
  sourceC0DifferentialZero :
    letI := K.cochainAddCommGroup 1
    K.d 0 source.toPrimitive = 0
  sourceC0GeneratedCechZero :
    source.SourceC0GeneratedCechZero

/-- Repackage the generated interpretation equality under its pointwise-zero name. -/
def toGeneratedInterpretationPointwiseZero
    {U : AtomCarrier.{u}} {A : ArchitectureObject U}
    {S : Site.AATSite.{u} A}
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{u} S}
    (D : LawAlgebra.LawEquationDefectSource.{u} G)
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
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{u} S}
    (D : LawAlgebra.LawEquationDefectSource.{u} G)
    (hholds : D.DisplayedRequiredLawsHoldOn) :
    forall i : D.Chart, D.interpret i = 0 :=
  D.displayedRequiredLawsHoldOn_constructs_interpret_eq_zero hholds

/--
X.定理7.5 generated-pair body route.

The theorem constructs the cover bridge, the H1 comparison, and the 7.5 packet
from AG-body data only.  It does not import or wrap research declarations, and
it does not call the native-input wrapper.
-/
theorem lawEquation_constructs_generatedPair_groundedComparisonPacket
    {P : SemanticAtomProjection.{u, v}}
    (data :
      SemanticRepairCoverH1BoundaryRelationAdditiveData.{u, v, w, x, y, z} P)
    {Ulaw : AtomCarrier.{u}}
    {Alaw : ArchitectureObject Ulaw}
    {Slaw : Site.AATSite.{u} Alaw}
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{u} Slaw}
    (D : LawAlgebra.LawEquationDefectSource.{u} G)
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
      data.TrueSheafConditionCertificate Slaw G.obstructionQuotientPresheaf cover)
    (gluingData :
      Site.AATGluingData Slaw G.obstructionQuotientPresheaf cover)
    {K : Cohomology.CoverRelativeCechComplex coverRel
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        G.obstructionQuotientCoefficient certificate.sheafCondition)}
    (realization :
      SemanticRepairCoverRelativeCochainRealization data.toAdditiveH1Surface K) :
    Nonempty
      (Sigma fun _bridge : SemanticRepairCoverRelativeCoverBridge semanticCover Slaw =>
        Sigma fun comparison :
          SemanticRepairCoverRelativeH1Comparison data.toAdditiveH1Surface K =>
            SemanticRepairGeneratedEndToEndSAGAPacket
              data D Slaw G.obstructionQuotientPresheaf cover gluingData
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
      data Slaw G.obstructionQuotientPresheaf cover certificate gluingData
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
          higherObstructionsVanish :=
            ⟨package73.nonabelianTorsorTrivial,
              package73.higherCoherenceVanishes,
              package73.stackEffectivelyVanishes⟩ } }

/--
Generated-complex form of theorem 7.5 for the body route.

The comparison supply is generated inside the theorem from the selected
cover-relative complex `K`: the bounded additive Cech data uses `K.Cn` and
`K.d`, and the cochain realization is the identity realization constructed
from that generated surface.
-/
theorem lawEquation_constructs_generatedPair_groundedComparisonPacket_fromCoverRelativeComplex
    {P : SemanticAtomProjection.{x, v}}
    (semanticCover : SemanticRepairCover.{x, v, w, x} P)
    {Ulaw : AtomCarrier.{x}}
    {Alaw : ArchitectureObject Ulaw}
    {Slaw : Site.AATSite.{x} Alaw}
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{x} Slaw}
    (D : LawAlgebra.LawEquationDefectSource.{x} G)
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
      Site.AATSheafCondition Slaw G.obstructionQuotientPresheaf)
    (K : Cohomology.CoverRelativeCechComplex coverRel
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        G.obstructionQuotientCoefficient sheafCondition))
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
      Site.AATGluingData Slaw G.obstructionQuotientPresheaf cover) :
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
              D Slaw G.obstructionQuotientPresheaf cover gluingData comparison) := by
  let data :=
    coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
      zero1 residual hzero1 hresidual hzero1_eq_zero supportOf component_covered_of_boundary
      component_faithful_of_boundary
  let certificate : data.TrueSheafConditionCertificate
      Slaw G.obstructionQuotientPresheaf cover :=
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
-/
theorem lawEquation_generatedBoundary_lawIndependentConclusions_fromPrimitive
    {P : SemanticAtomProjection.{x, v}}
    (semanticCover : SemanticRepairCover.{x, v, w, x} P)
    {Ulaw : AtomCarrier.{x}}
    {Alaw : ArchitectureObject Ulaw}
    {Slaw : Site.AATSite.{x} Alaw}
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{x} Slaw}
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
      Site.AATSheafCondition Slaw G.obstructionQuotientPresheaf)
    (K : Cohomology.CoverRelativeCechComplex coverRel
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        G.obstructionQuotientCoefficient sheafCondition))
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
      Site.AATGluingData Slaw G.obstructionQuotientPresheaf cover) :
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
                Slaw G.obstructionQuotientPresheaf cover gluingData comparison =>
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
      Slaw G.obstructionQuotientPresheaf cover :=
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
      data Slaw G.obstructionQuotientPresheaf cover certificate gluingData
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
        data Slaw G.obstructionQuotientPresheaf cover gluingData
        comparison :=
    { groundedGlobalGluingPackage := ⟨package73⟩
      sheafConditionFor := package73.sheafConditionFor
      descent := package73.descent
      uniqueGlobalSection := package73.uniqueGlobalSection
      globalCoherent_iff_coverRelativeH1Zero :=
        package73.globalCoherent_iff_coverRelativeH1Zero
      boundedAdditiveH1Zero_iff_coverRelativeH1Zero :=
        package73.boundedAdditiveH1Zero_iff_coverRelativeH1Zero
      higherObstructionsVanish :=
        ⟨package73.nonabelianTorsorTrivial,
          package73.higherCoherenceVanishes,
          package73.stackEffectivelyVanishes⟩ }
  refine ⟨⟨bridge, comparison, ?_⟩⟩
  exact ⟨lawIndependent, hBounded, hSurface, hCover⟩

/--
Generated-boundary law-independent route with the Research visible conjuncts
preserved as AG-body fields.
-/
theorem lawEquation_generatedBoundary_lawIndependentResearchConjuncts_fromPrimitive
    {P : SemanticAtomProjection.{x, v}}
    (semanticCover : SemanticRepairCover.{x, v, w, x} P)
    {Ulaw : AtomCarrier.{x}}
    {Alaw : ArchitectureObject Ulaw}
    {Slaw : Site.AATSite.{x} Alaw}
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{x} Slaw}
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
      Site.AATSheafCondition Slaw G.obstructionQuotientPresheaf)
    (K : Cohomology.CoverRelativeCechComplex coverRel
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        G.obstructionQuotientCoefficient sheafCondition))
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
          semanticCover Slaw G.obstructionQuotientPresheaf K =>
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
-/
theorem lawEquation_generatedBoundary_lawIndependentResearchConjuncts_fromSource
    {P : SemanticAtomProjection.{x, v}}
    (semanticCover : SemanticRepairCover.{x, v, w, x} P)
    {Ulaw : AtomCarrier.{x}}
    {Alaw : ArchitectureObject Ulaw}
    {Slaw : Site.AATSite.{x} Alaw}
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{x} Slaw}
    (D : LawAlgebra.LawEquationDefectSource.{x} G)
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
      Site.AATSheafCondition Slaw G.obstructionQuotientPresheaf)
    (K : Cohomology.CoverRelativeCechComplex coverRel
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        G.obstructionQuotientCoefficient sheafCondition))
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
          semanticCover Slaw G.obstructionQuotientPresheaf K =>
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
Generated-boundary form of theorem 7.5.

This route does not accept a residual cocycle or H1-zero statement.  The
residual is `K.d 0 primitive`, so the residual cocycle is generated by
`d ∘ d = 0`, the bounded and finite-free H1-zero statements are generated
inside the theorem, and the cover-relative zero statement is obtained through
the generated H1 comparison.
-/
theorem lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromPrimitive
    {P : SemanticAtomProjection.{x, v}}
    (semanticCover : SemanticRepairCover.{x, v, w, x} P)
    {Ulaw : AtomCarrier.{x}}
    {Alaw : ArchitectureObject Ulaw}
    {Slaw : Site.AATSite.{x} Alaw}
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{x} Slaw}
    (D : LawAlgebra.LawEquationDefectSource.{x} G)
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
      Site.AATSheafCondition Slaw G.obstructionQuotientPresheaf)
    (K : Cohomology.CoverRelativeCechComplex coverRel
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        G.obstructionQuotientCoefficient sheafCondition))
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
      Site.AATGluingData Slaw G.obstructionQuotientPresheaf cover) :
    Nonempty
      (Sigma fun _bridge : SemanticRepairCoverRelativeCoverBridge semanticCover Slaw =>
        Sigma fun comparison :
          SemanticRepairCoverRelativeH1Comparison
            (coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
              zero1 (K.d 0 primitive) hzero1 (K.differential_comp 0 primitive)
              hzero1_eq_zero supportOf component_covered_of_boundary
              component_faithful_of_boundary).toAdditiveH1Surface
            K =>
            Subtype (fun _ :
              SemanticRepairGeneratedEndToEndSAGAPacket
                (coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
                  zero1 (K.d 0 primitive) hzero1 (K.differential_comp 0 primitive)
                  hzero1_eq_zero supportOf component_covered_of_boundary
                  component_faithful_of_boundary)
                D Slaw G.obstructionQuotientPresheaf cover gluingData comparison =>
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
        data D Slaw G.obstructionQuotientPresheaf cover gluingData
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
Generated-boundary theorem-7.5 route with the Research visible 10-conjunct
packet preserved as AG-body fields.
-/
theorem lawEquation_constructs_groundedResearchConjuncts_fromPrimitive
    {P : SemanticAtomProjection.{x, v}}
    (semanticCover : SemanticRepairCover.{x, v, w, x} P)
    {Ulaw : AtomCarrier.{x}}
    {Alaw : ArchitectureObject Ulaw}
    {Slaw : Site.AATSite.{x} Alaw}
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{x} Slaw}
    (D : LawAlgebra.LawEquationDefectSource.{x} G)
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
      Site.AATSheafCondition Slaw G.obstructionQuotientPresheaf)
    (K : Cohomology.CoverRelativeCechComplex coverRel
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        G.obstructionQuotientCoefficient sheafCondition))
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
          semanticCover Slaw G.obstructionQuotientPresheaf K =>
        Sigma fun comparison :
          SemanticRepairCoverRelativeH1Comparison
            (coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
              zero1 (K.d 0 primitive) hzero1 (K.differential_comp 0 primitive)
              hzero1_eq_zero supportOf component_covered_of_boundary
              component_faithful_of_boundary).toAdditiveH1Surface
            K =>
          LawEquationGroundedComparisonConjunctsBody D surface source
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
      sourceC0CechZero :=
        source.displayedRequiredLawsHoldOn_constructs_sourceC0CechZero
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

Unlike the primitive-parametrized helper, this theorem returns the Research
visible conjunct tuple for the single source witness: the displayed
interpretation realization, the source C0 Cech-zero statement, the residual
boundary, and the H1-zero conclusions all refer to `source.toPrimitive`.
-/
theorem lawEquation_constructs_groundedResearchConjuncts_fromSource
    {P : SemanticAtomProjection.{x, v}}
    (semanticCover : SemanticRepairCover.{x, v, w, x} P)
    {Ulaw : AtomCarrier.{x}}
    {Alaw : ArchitectureObject Ulaw}
    {Slaw : Site.AATSite.{x} Alaw}
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{x} Slaw}
    (D : LawAlgebra.LawEquationDefectSource.{x} G)
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
      Site.AATSheafCondition Slaw G.obstructionQuotientPresheaf)
    (K : Cohomology.CoverRelativeCechComplex coverRel
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        G.obstructionQuotientCoefficient sheafCondition))
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
          semanticCover Slaw G.obstructionQuotientPresheaf K =>
        Sigma fun comparison :
          SemanticRepairCoverRelativeH1Comparison
            (coverRelativeBoundaryAdditiveDataOfComplex semanticCover K c0Finite c1Finite
              zero1 (K.d 0 source.toPrimitive) hzero1
              (K.differential_comp 0 source.toPrimitive)
              hzero1_eq_zero supportOf component_covered_of_boundary
              component_faithful_of_boundary).toAdditiveH1Surface
            K =>
          LawEquationGroundedComparisonConjunctsBody D surface source
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
      sourceC0CechZero :=
        source.displayedRequiredLawsHoldOn_constructs_sourceC0CechZero
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
-/
def lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromFinitePosetComparisonPrimitive
    {P : SemanticAtomProjection.{x, v}}
    (semanticCover : SemanticRepairCover.{x, v, w, x} P)
    {Ulaw : AtomCarrier.{x}}
    {Alaw : ArchitectureObject Ulaw}
    {Slaw : Site.AATSite.{x} Alaw}
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{x} Slaw}
    (D : LawAlgebra.LawEquationDefectSource.{x} G)
    (hDisplayedRequiredLaws : D.DisplayedRequiredLawsHoldOn)
    {Kfp : Site.FinitePosetAATSiteRegime Slaw}
    {C : Site.FinitePosetCechComplex Kfp}
    {base : Slaw.category}
    (cover : Sieve base)
    (sheafCondition :
      Site.AATSheafCondition Slaw G.obstructionQuotientPresheaf)
    (comparisonData :
      Cohomology.FinitePosetCechComparisonData C
        (Cohomology.ObstructionSheaf.ofAddCommGrpValued
          G.obstructionQuotientCoefficient sheafCondition))
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
      Site.AATGluingData Slaw G.obstructionQuotientPresheaf cover) :=
  lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromPrimitive
    semanticCover D hDisplayedRequiredLaws chartSimplex overlapSimplex
    tripleSimplex cover sheafCondition comparisonData.generalComplex
    c0Finite c1Finite (0 : comparisonData.generalComplex.Cn 1) primitive
      (by
        letI := comparisonData.generalComplex.cochainAddCommGroup 1
        letI := comparisonData.generalComplex.cochainAddCommGroup 2
        exact (comparisonData.generalComplex.d 1).map_zero)
      rfl
      (lawEquationCompleteSupportOf (P := P) comparisonData.generalComplex)
      (lawEquationCompleteSupport_componentCovered_of_boundary
        semanticCover comparisonData.generalComplex
        (comparisonData.generalComplex.d 0 primitive))
      (lawEquationCompleteSupport_componentFaithful_of_boundary
        semanticCover comparisonData.generalComplex
        (comparisonData.generalComplex.d 0 primitive))
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
theorem displayedRequiredLawsHoldOn_constructs_standardSourceC0DifferentialZero
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{x} Slaw}
    (D : LawAlgebra.LawEquationDefectSource.{x} G)
    (sheafCondition :
      Site.AATSheafCondition Slaw G.obstructionQuotientPresheaf)
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    {faces :
      Site.FinitePosetCechFaceData
        (geometry.toObstructionCoefficientRegime
          (Cohomology.ObstructionSheaf.ofAddCommGrpValued
            G.obstructionQuotientCoefficient sheafCondition))}
    (law : StandardDifferentialCompLaw geometry
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        G.obstructionQuotientCoefficient sheafCondition) faces)
    (source :
      LawEquationBodyCechSource D
        (coverRelativeComplexOfStandardFinitePosetLaw law))
    (hholds : D.DisplayedRequiredLawsHoldOn) :
    let K := coverRelativeComplexOfStandardFinitePosetLaw law
    letI := K.cochainAddCommGroup 1
    K.d 0 source.toPrimitive = 0 := by
  let K := coverRelativeComplexOfStandardFinitePosetLaw law
  have hsource : source.toPrimitive = (0 : K.Cn 0) := by
    have hrealized :=
      source.displayedRequiredLawsHoldOn_constructs_displayedInterpretationRealization
        hholds
    funext sigma
    rw [hrealized sigma]
    dsimp [LawEquationBodyCechSource.restrictedDisplayedInterpretation]
    rw [D.displayedRequiredLawsHoldOn_constructs_interpret_eq_zero hholds
      (source.chartOf sigma)]
    change
      (ConcreteCategory.hom
        (G.obstructionQuotientCoefficient.map
          (source.restriction sigma).op)) 0 = 0
    exact
      (G.obstructionQuotientCoefficient.map
        (source.restriction sigma).op).hom.map_zero
  letI := K.cochainAddCommGroup 0
  letI := K.cochainAddCommGroup 1
  rw [hsource]
  exact (K.d 0).map_zero

/--
Standard finite-poset generated-boundary form of theorem 7.5.

This route no longer accepts `FinitePosetCechComparisonData`: the
cover-relative complex is generated directly from the standard finite-poset
law and face data.
-/
def lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromStandardFinitePosetPrimitive
    {P : SemanticAtomProjection.{x, v}}
    (semanticCover : SemanticRepairCover.{x, v, w, x} P)
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{x} Slaw}
    (D : LawAlgebra.LawEquationDefectSource.{x} G)
    (hDisplayedRequiredLaws : D.DisplayedRequiredLawsHoldOn)
    {base : Slaw.category}
    (cover : Sieve base)
    (sheafCondition :
      Site.AATSheafCondition Slaw G.obstructionQuotientPresheaf)
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    {faces :
      Site.FinitePosetCechFaceData
        (geometry.toObstructionCoefficientRegime
          (Cohomology.ObstructionSheaf.ofAddCommGrpValued
            G.obstructionQuotientCoefficient sheafCondition))}
    (law : StandardDifferentialCompLaw geometry
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        G.obstructionQuotientCoefficient sheafCondition) faces)
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
      Site.AATGluingData Slaw G.obstructionQuotientPresheaf cover) :=
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
        (lawEquationCompleteSupportOf
          (P := P) (coverRelativeComplexOfStandardFinitePosetLaw law))
        (lawEquationCompleteSupport_componentCovered_of_boundary
          semanticCover (coverRelativeComplexOfStandardFinitePosetLaw law)
          ((coverRelativeComplexOfStandardFinitePosetLaw law).d 0 primitive))
        (lawEquationCompleteSupport_componentFaithful_of_boundary
          semanticCover (coverRelativeComplexOfStandardFinitePosetLaw law)
          ((coverRelativeComplexOfStandardFinitePosetLaw law).d 0 primitive))
        cover_mem gluingData

/--
Standard finite-poset theorem-7.5 route tied to the body source primitive and
exposing the actual source C0 differential-zero conjunct.
-/
theorem lawEquation_constructs_groundedResearchConjunctsWithSourceC0DifferentialZero_fromStandardFinitePosetSource
    {P : SemanticAtomProjection.{x, v}}
    (semanticCover : SemanticRepairCover.{x, v, w, x} P)
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{x} Slaw}
    (D : LawAlgebra.LawEquationDefectSource.{x} G)
    (hDisplayedRequiredLaws : D.DisplayedRequiredLawsHoldOn)
    (sheafCondition :
      Site.AATSheafCondition Slaw G.obstructionQuotientPresheaf)
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    {faces :
      Site.FinitePosetCechFaceData
        (geometry.toObstructionCoefficientRegime
          (Cohomology.ObstructionSheaf.ofAddCommGrpValued
            G.obstructionQuotientCoefficient sheafCondition))}
    (law : StandardDifferentialCompLaw geometry
      (Cohomology.ObstructionSheaf.ofAddCommGrpValued
        G.obstructionQuotientCoefficient sheafCondition) faces)
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
          semanticCover Slaw G.obstructionQuotientPresheaf
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
                (lawEquationCompleteSupportOf
                  (P := P) (coverRelativeComplexOfStandardFinitePosetLaw law))
                (lawEquationCompleteSupport_componentCovered_of_boundary
                  semanticCover (coverRelativeComplexOfStandardFinitePosetLaw law)
                  ((coverRelativeComplexOfStandardFinitePosetLaw law).d 0
                    source.toPrimitive))
                (lawEquationCompleteSupport_componentFaithful_of_boundary
                  semanticCover (coverRelativeComplexOfStandardFinitePosetLaw law)
                  ((coverRelativeComplexOfStandardFinitePosetLaw law).d 0
                    source.toPrimitive))).toAdditiveH1Surface
            (coverRelativeComplexOfStandardFinitePosetLaw law) =>
          LawEquationGroundedComparisonConjunctsBodyWithSourceC0DifferentialZero
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
                (lawEquationCompleteSupportOf
                  (P := P) (coverRelativeComplexOfStandardFinitePosetLaw law))
                (lawEquationCompleteSupport_componentCovered_of_boundary
                  semanticCover (coverRelativeComplexOfStandardFinitePosetLaw law)
                  ((coverRelativeComplexOfStandardFinitePosetLaw law).d 0
                    source.toPrimitive))
                (lawEquationCompleteSupport_componentFaithful_of_boundary
                  semanticCover (coverRelativeComplexOfStandardFinitePosetLaw law)
                  ((coverRelativeComplexOfStandardFinitePosetLaw law).d 0
                    source.toPrimitive)))
  comparison) := by
  let K := coverRelativeComplexOfStandardFinitePosetLaw law
  let supportOf : K.Cn 0 -> P.Support :=
    lawEquationCompleteSupportOf (P := P) K
  have hzero1 : letI := K.cochainAddCommGroup 2; K.d 1 (0 : K.Cn 1) = 0 := by
    letI := K.cochainAddCommGroup 1
    letI := K.cochainAddCommGroup 2
    exact (K.d 1).map_zero
  have hsourceC0 :
      letI := K.cochainAddCommGroup 1
      K.d 0 source.toPrimitive = 0 :=
    displayedRequiredLawsHoldOn_constructs_standardSourceC0DifferentialZero
      D sheafCondition law source hDisplayedRequiredLaws
  rcases
    lawEquation_constructs_groundedResearchConjuncts_fromSource
        semanticCover D hDisplayedRequiredLaws chartSimplex overlapSimplex
        tripleSimplex geometry.cover sheafCondition K source c0Finite c1Finite
        (0 : K.Cn 1) hzero1 rfl supportOf
        (lawEquationCompleteSupport_componentCovered_of_boundary
          semanticCover K (K.d 0 source.toPrimitive))
        (lawEquationCompleteSupport_componentFaithful_of_boundary
          semanticCover K (K.d 0 source.toPrimitive)) with
    ⟨⟨surface, comparison, conjuncts⟩⟩
  exact ⟨⟨surface, comparison,
    { conjuncts := conjuncts
      sourceC0DifferentialZero := hsourceC0
      sourceC0GeneratedCechZero :=
        ⟨conjuncts.sourceC0CechZero, hsourceC0⟩ }⟩⟩

/-- Native generated obstruction sheaf used by the canonical tuple route. -/
def canonicalTupleGeneratedBoundaryObstructionSheaf
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{x} Slaw}
    (sheafCondition :
      Site.AATSheafCondition Slaw G.obstructionQuotientPresheaf) :
    Cohomology.ObstructionSheaf Slaw :=
  Cohomology.ObstructionSheaf.ofAddCommGrpValued
    G.obstructionQuotientCoefficient sheafCondition

/--
Canonical tuple geometry generates the standard finite-poset `d ∘ d = 0` law
used by the generated-boundary theorem 7.5 route.
-/
def canonicalTupleGeneratedBoundaryLaw
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{x} Slaw}
    (sheafCondition :
      Site.AATSheafCondition Slaw G.obstructionQuotientPresheaf)
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (tupleGeometry : Site.FinitePosetCanonicalTupleCoverGeometry geometry) :
    StandardDifferentialCompLaw tupleGeometry.toCoverGeometry
      (canonicalTupleGeneratedBoundaryObstructionSheaf
        (G := G) sheafCondition)
      ((tupleGeometry.toSimplicialFaceAction
        (canonicalTupleGeneratedBoundaryObstructionSheaf
          (G := G) sheafCondition).carrier.toPresheaf).toFaceData) :=
  canonicalTupleStandardDifferentialCompLaw tupleGeometry
    (canonicalTupleGeneratedBoundaryObstructionSheaf
      (G := G) sheafCondition)

/--
Canonical tuple generated cover-relative complex for native law-equation
obstruction coefficients.
-/
def canonicalTupleGeneratedBoundaryComplex
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{x} Slaw}
    (sheafCondition :
      Site.AATSheafCondition Slaw G.obstructionQuotientPresheaf)
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (tupleGeometry : Site.FinitePosetCanonicalTupleCoverGeometry geometry) :
    Cohomology.CoverRelativeCechComplex
      (Cohomology.finitePosetCoverRelativeCover
        (canonicalTupleStandardFinitePosetCechComplex tupleGeometry
          (canonicalTupleGeneratedBoundaryObstructionSheaf
            (G := G) sheafCondition)))
      (canonicalTupleGeneratedBoundaryObstructionSheaf
        (G := G) sheafCondition) :=
  coverRelativeComplexOfStandardFinitePosetLaw
    (canonicalTupleGeneratedBoundaryLaw
      (G := G) sheafCondition tupleGeometry)

/-! ## Law-equation generated spine distilled from the research loop -/

/--
Law-equation generated finite-poset regime.

This is the body-side counterpart of the research-loop `lawEquationRegime`:
the coefficient slot is the native law-equation quotient coefficient, and the
simplex/face surface is the canonical tuple geometry.
-/
abbrev lawEquationRegime
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{x} Slaw}
    (sheafCondition :
      Site.AATSheafCondition Slaw G.obstructionQuotientPresheaf)
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (tupleGeometry : Site.FinitePosetCanonicalTupleCoverGeometry geometry) :
    Site.FinitePosetAATSiteRegime Slaw :=
  tupleGeometry.toCoverGeometry.toObstructionCoefficientRegime
    (canonicalTupleGeneratedBoundaryObstructionSheaf
      (G := G) sheafCondition)

/--
Law-equation generated standard finite-poset Cech complex.

This is the body-side counterpart of the research-loop
`lawEquationStandardComplex`.  The standard differential and `d ∘ d = 0` law
come from the canonical tuple face action, not from a supplied comparison
package.
-/
abbrev lawEquationStandardComplex
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{x} Slaw}
    (sheafCondition :
      Site.AATSheafCondition Slaw G.obstructionQuotientPresheaf)
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (tupleGeometry : Site.FinitePosetCanonicalTupleCoverGeometry geometry) :
    Site.FinitePosetCechComplex
      (lawEquationRegime (G := G) sheafCondition tupleGeometry) :=
  canonicalTupleStandardFinitePosetCechComplex tupleGeometry
    (canonicalTupleGeneratedBoundaryObstructionSheaf
      (G := G) sheafCondition)

/--
Law-equation generated cover-relative Cech complex.

This is the body-side counterpart of the research-loop
`lawEquationCechComplex`.  It is generated from
`lawEquationStandardComplex`, hence from the native law-equation quotient
coefficient and canonical tuple face action.
-/
abbrev lawEquationCechComplex
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{x} Slaw}
    (sheafCondition :
      Site.AATSheafCondition Slaw G.obstructionQuotientPresheaf)
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (tupleGeometry : Site.FinitePosetCanonicalTupleCoverGeometry geometry) :
    Cohomology.CoverRelativeCechComplex
      (Cohomology.finitePosetCoverRelativeCover
        (lawEquationStandardComplex
          (G := G) sheafCondition tupleGeometry))
      (canonicalTupleGeneratedBoundaryObstructionSheaf
        (G := G) sheafCondition) :=
  canonicalTupleGeneratedBoundaryComplex
    (G := G) sheafCondition tupleGeometry

/-- The cover-relative cover generated by the law-equation standard complex. -/
abbrev lawEquationCoverRelativeCover
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{x} Slaw}
    (sheafCondition :
      Site.AATSheafCondition Slaw G.obstructionQuotientPresheaf)
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (tupleGeometry : Site.FinitePosetCanonicalTupleCoverGeometry geometry) :
    Cohomology.CoverRelativeCechCover Slaw :=
  Cohomology.finitePosetCoverRelativeCover
    (lawEquationStandardComplex
      (G := G) sheafCondition tupleGeometry)

/--
Canonical tuple generated-boundary form of theorem 7.5.

This route does not accept a prebuilt comparison-data package or a supplied
`d ∘ d = 0` law.  The finite-poset cover-relative complex is generated from
the canonical tuple geometry and the native law-equation quotient coefficient.
-/
def lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromCanonicalTuplePrimitive
    {P : SemanticAtomProjection.{x, v}}
    (semanticCover : SemanticRepairCover.{x, v, w, x} P)
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{x} Slaw}
    (D : LawAlgebra.LawEquationDefectSource.{x} G)
    (hDisplayedRequiredLaws : D.DisplayedRequiredLawsHoldOn)
    {base : Slaw.category}
    (cover : Sieve base)
    (sheafCondition :
      Site.AATSheafCondition Slaw G.obstructionQuotientPresheaf)
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (tupleGeometry : Site.FinitePosetCanonicalTupleCoverGeometry geometry)
    (chartSimplex :
      semanticCover.CoverChart ->
        (Cohomology.finitePosetCoverRelativeCover
          (canonicalTupleStandardFinitePosetCechComplex tupleGeometry
            (canonicalTupleGeneratedBoundaryObstructionSheaf
              (G := G) sheafCondition))).simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) ->
          (Cohomology.finitePosetCoverRelativeCover
            (canonicalTupleStandardFinitePosetCechComplex tupleGeometry
              (canonicalTupleGeneratedBoundaryObstructionSheaf
                (G := G) sheafCondition))).simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          (Cohomology.finitePosetCoverRelativeCover
            (canonicalTupleStandardFinitePosetCechComplex tupleGeometry
              (canonicalTupleGeneratedBoundaryObstructionSheaf
                (G := G) sheafCondition))).simplex 2)
    (c0Finite :
      Fintype ((canonicalTupleGeneratedBoundaryComplex
        (G := G) sheafCondition tupleGeometry).Cn 0))
    (c1Finite :
      Fintype ((canonicalTupleGeneratedBoundaryComplex
        (G := G) sheafCondition tupleGeometry).Cn 1))
    (primitive :
      (canonicalTupleGeneratedBoundaryComplex
        (G := G) sheafCondition tupleGeometry).Cn 0)
    (cover_mem : cover ∈ Slaw.topology base)
    (gluingData :
      Site.AATGluingData Slaw G.obstructionQuotientPresheaf cover) :=
  lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromStandardFinitePosetPrimitive
    semanticCover D hDisplayedRequiredLaws cover sheafCondition
    (canonicalTupleGeneratedBoundaryLaw
      (G := G) sheafCondition tupleGeometry)
    chartSimplex overlapSimplex tripleSimplex c0Finite c1Finite primitive
    cover_mem gluingData

/--
Law-equation-spine form of theorem 7.5.

This entrypoint is intentionally named after the research-loop spine:
`lawEquationRegime`, `lawEquationStandardComplex`, and
`lawEquationCechComplex` are the objects consumed here.  It is not a wrapper
around a research theorem; it calls the body-side canonical tuple route.
-/
def lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromLawEquationSpinePrimitive
    {P : SemanticAtomProjection.{x, v}}
    (semanticCover : SemanticRepairCover.{x, v, w, x} P)
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{x} Slaw}
    (D : LawAlgebra.LawEquationDefectSource.{x} G)
    (hDisplayedRequiredLaws : D.DisplayedRequiredLawsHoldOn)
    {base : Slaw.category}
    (cover : Sieve base)
    (sheafCondition :
      Site.AATSheafCondition Slaw G.obstructionQuotientPresheaf)
    {geometry : Site.FinitePosetCoverGeometry Slaw}
    (tupleGeometry : Site.FinitePosetCanonicalTupleCoverGeometry geometry)
    (chartSimplex :
      semanticCover.CoverChart ->
        (lawEquationCoverRelativeCover
          (G := G) sheafCondition tupleGeometry).simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) ->
          (lawEquationCoverRelativeCover
            (G := G) sheafCondition tupleGeometry).simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          (lawEquationCoverRelativeCover
            (G := G) sheafCondition tupleGeometry).simplex 2)
    (c0Finite :
      Fintype ((lawEquationCechComplex
        (G := G) sheafCondition tupleGeometry).Cn 0))
    (c1Finite :
      Fintype ((lawEquationCechComplex
        (G := G) sheafCondition tupleGeometry).Cn 1))
    (primitive :
      (lawEquationCechComplex
        (G := G) sheafCondition tupleGeometry).Cn 0)
    (cover_mem : cover ∈ Slaw.topology base)
    (gluingData :
      Site.AATGluingData Slaw G.obstructionQuotientPresheaf cover) :=
  lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromCanonicalTuplePrimitive
    semanticCover D hDisplayedRequiredLaws cover sheafCondition tupleGeometry
    chartSimplex overlapSimplex tripleSimplex c0Finite c1Finite primitive
    cover_mem gluingData

/--
Overlap-generated law-equation-spine form of theorem 7.5.

This is the distilled body-side analogue of the research-loop route that starts
with the law-equation regime and constructs the canonical tuple geometry from
the selected finite-poset cover and the site overlap operation.
-/
def lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromOverlapGeneratedSpinePrimitive
    {P : SemanticAtomProjection.{x, v}}
    (semanticCover : SemanticRepairCover.{x, v, w, x} P)
    {G : LawAlgebra.SemanticLawEquationWitnessIdealCore.{x} Slaw}
    (D : LawAlgebra.LawEquationDefectSource.{x} G)
    (hDisplayedRequiredLaws : D.DisplayedRequiredLawsHoldOn)
    {base : Slaw.category}
    (cover : Sieve base)
    (sheafCondition :
      Site.AATSheafCondition Slaw G.obstructionQuotientPresheaf)
    (geometry : Site.FinitePosetCoverGeometry Slaw)
    (chartSimplex :
      semanticCover.CoverChart ->
        (lawEquationCoverRelativeCover
          (G := G) sheafCondition
          geometry.canonicalTupleCoverGeometryFromOverlap).simplex 0)
    (overlapSimplex :
      (Sigma fun pair : semanticCover.CoverChart × semanticCover.CoverChart =>
        semanticCover.Overlap pair.1 pair.2) ->
          (lawEquationCoverRelativeCover
            (G := G) sheafCondition
            geometry.canonicalTupleCoverGeometryFromOverlap).simplex 1)
    (tripleSimplex :
      (Sigma fun triple : semanticCover.CoverChart × semanticCover.CoverChart ×
        semanticCover.CoverChart =>
        semanticCover.TripleOverlap triple.1 triple.2.1 triple.2.2) ->
          (lawEquationCoverRelativeCover
            (G := G) sheafCondition
            geometry.canonicalTupleCoverGeometryFromOverlap).simplex 2)
    (c0Finite :
      Fintype ((lawEquationCechComplex
        (G := G) sheafCondition
        geometry.canonicalTupleCoverGeometryFromOverlap).Cn 0))
    (c1Finite :
      Fintype ((lawEquationCechComplex
        (G := G) sheafCondition
        geometry.canonicalTupleCoverGeometryFromOverlap).Cn 1))
    (primitive :
      (lawEquationCechComplex
        (G := G) sheafCondition
        geometry.canonicalTupleCoverGeometryFromOverlap).Cn 0)
    (cover_mem : cover ∈ Slaw.topology base)
    (gluingData :
      Site.AATGluingData Slaw G.obstructionQuotientPresheaf cover) :=
  lawEquation_constructs_generatedBoundary_groundedComparisonPacket_fromLawEquationSpinePrimitive
    semanticCover D hDisplayedRequiredLaws cover sheafCondition
    geometry.canonicalTupleCoverGeometryFromOverlap
    chartSimplex overlapSimplex tripleSimplex c0Finite c1Finite primitive
    cover_mem gluingData

end StandardFinitePosetGeneratedBoundary

end SemanticRepair
end AAT.AG
