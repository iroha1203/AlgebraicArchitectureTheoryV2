import ResearchLean.AG.FullGeometryNormalization.SemanticExactNormalizationNaturality
import ResearchLean.AG.FullGeometryNormalization.SemanticExactNormalizationPush
import ResearchLean.AG.FullGeometryNormalization.SemanticExactGeometryTransportAdjunction
import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedEndpointBridge
import ResearchLean.AG.FullGeometryNormalization.SemanticDerivedBarAlphaNormalizationNaturality
import ResearchLean.AG.DoctrineFiberProduct.IdempotentExchangeTransportIdentityClassification
import Mathlib.CategoryTheory.Idempotents.Karoubi
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Semantic exact comparison normalization classification

The selector and comparison in this module are constructed from a semantic
Beck--Chevalley square, its G-106 cochain, and the generated exact geometry
routes.  The endpoint normalizations are formed on the actual generated
complete geometries.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory CategoryTheory.Idempotents
open AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct TransportCoherence

set_option maxHeartbeats 3000000

/-- The literal G-106 cochain selector at a diagnostic face of the semantic
square.  The source core is the package at that face's target vertex. -/
def semanticExactBarSelectedAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (omega : DefectCochain interpretation.data) : Prop :=
  omega z ≠ 1 ∧
    CanonicalObjectNormalizationAdmissible
      (interpretation.data.lift.package (input.diagnostic.twoTarget z))

/-- The actual G-106 source core at the selected diagnostic face. -/
abbrev semanticExactBarSourceCoreAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell) : AATCorePackage U :=
  interpretation.data.lift.package (input.diagnostic.twoTarget z)

/-- The target projector is the image of the selected source normalization
through the literal bottom transport and right pullback route. -/
noncomputable def semanticExactBarDAt
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (omega : DefectCochain interpretation.data)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt
      (semanticExactBarSourceCoreAt input interpretation z) k)
    (endpoint_eq : packagePoint
      (semanticExactBarSourceCoreAt input interpretation z) =
        input.square.southwest) :
    semanticDerivedViaBaseGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq ⟶
      semanticDerivedViaBaseGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq := by
  classical
  by_cases selected : semanticExactBarSelectedAt input interpretation z omega
  · exact (semanticGeometryPullFunctor input.square.right).map
      ((geomFiberTransportFunctor input.square.bottom).map
        (canonicalGeometryFiberNormalization
          (semanticDerivedSouthwestGeometryFiber input
            (semanticExactBarSourceCoreAt input interpretation z)
            k g endpoint_eq) selected.2))
  · exact 𝟙 _

/-- On the selected branch the target projector is exactly the image of the
source canonical normalization along the generated via-base route. -/
theorem semanticExactBarDAt_eq_normalization_route
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (omega : DefectCochain interpretation.data)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt
      (semanticExactBarSourceCoreAt input interpretation z) k)
    (endpoint_eq : packagePoint
      (semanticExactBarSourceCoreAt input interpretation z) =
        input.square.southwest)
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    semanticExactBarDAt input interpretation z omega k g endpoint_eq =
      (semanticGeometryPullFunctor input.square.right).map
        ((geomFiberTransportFunctor input.square.bottom).map
          (canonicalGeometryFiberNormalization
            (semanticDerivedSouthwestGeometryFiber input
              (semanticExactBarSourceCoreAt input interpretation z)
              k g endpoint_eq) selected.2)) := by
  simp [semanticExactBarDAt, selected]

/-- Off the literal diagnostic selector, the generated target projector is
the identity. -/
theorem semanticExactBarDAt_eq_id
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (omega : DefectCochain interpretation.data)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt
      (semanticExactBarSourceCoreAt input interpretation z) k)
    (endpoint_eq : packagePoint
      (semanticExactBarSourceCoreAt input interpretation z) =
        input.square.southwest)
    (notSelected : ¬ semanticExactBarSelectedAt input interpretation z omega) :
    semanticExactBarDAt input interpretation z omega k g endpoint_eq = 𝟙 _ := by
  simp [semanticExactBarDAt, notSelected]

/-- The target projector is idempotent as the functorial image of the
canonical normalization idempotent. -/
theorem semanticExactBarDAt_idem
    {U : AtomCarrier.{u}}
    (input : BCSemanticInput U)
    (interpretation : BCDiagnosticInterpretation U input)
    (z : input.diagnostic.TwoCell)
    (omega : DefectCochain interpretation.data)
    (k : Type v) [CommRing k]
    (g : FixedCoefficientGeometryAt
      (semanticExactBarSourceCoreAt input interpretation z) k)
    (endpoint_eq : packagePoint
      (semanticExactBarSourceCoreAt input interpretation z) =
        input.square.southwest) :
    semanticExactBarDAt input interpretation z omega k g endpoint_eq ≫
        semanticExactBarDAt input interpretation z omega k g endpoint_eq =
      semanticExactBarDAt input interpretation z omega k g endpoint_eq := by
  classical
  by_cases selected : semanticExactBarSelectedAt input interpretation z omega
  · rw [semanticExactBarDAt_eq_normalization_route
        input interpretation z omega k g endpoint_eq selected,
      ← Functor.map_comp, ← Functor.map_comp]
    congr 2
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact canonicalGeometryNormalization_idem _ _
  · rw [semanticExactBarDAt_eq_id
      input interpretation z omega k g endpoint_eq selected]
    simp

/-- Semantic complete-geometry transport is faithful, using the generated
unit and counit isomorphisms of its pullback adjunction. -/
theorem semanticGeomFiberTransportFunctor_faithful
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (input : ExtInstHom X Y) :
    (geomFiberTransportFunctor.{u, v} input).Faithful := by
  let adj := semanticGeometryTransportPullAdjunction.{u, v} input
  letI (source : GeomFiber.{u, v} X) : IsIso (adj.unit.app source) := by
    change IsIso ((semanticGeometryTransportPullUnit input).app source)
    exact semanticGeometryTransportPullUnit_app_isIso input source
  letI (target : GeomFiber.{u, v} Y) : IsIso (adj.counit.app target) := by
    change IsIso ((semanticGeometryTransportPullCounit input).app target)
    exact semanticGeometryTransportPullCounit_app_isIso input target
  letI : (geomFiberTransportFunctor.{u, v} input).IsEquivalence :=
    adj.toEquivalence.isEquivalence_functor
  infer_instance

/-- Semantic exact complete-geometry pullback is faithful by the same
generated adjoint equivalence. -/
theorem semanticGeometryPullFunctor_faithful
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U} (input : ExtInstHom X Y) :
    (semanticGeometryPullFunctor.{u, v} input).Faithful := by
  let adj := semanticGeometryTransportPullAdjunction.{u, v} input
  letI (source : GeomFiber.{u, v} X) : IsIso (adj.unit.app source) := by
    change IsIso ((semanticGeometryTransportPullUnit input).app source)
    exact semanticGeometryTransportPullUnit_app_isIso input source
  letI (target : GeomFiber.{u, v} Y) : IsIso (adj.counit.app target) := by
    change IsIso ((semanticGeometryTransportPullCounit input).app target)
    exact semanticGeometryTransportPullCounit_app_isIso input target
  letI : (semanticGeometryPullFunctor.{u, v} input).IsEquivalence :=
    adj.toEquivalence.isEquivalence_inverse
  infer_instance

/-- Canonical complete-geometry normalization is noninvertible: its projection
is the canonical core normalization, whose object map is noninjective. -/
theorem canonicalGeometryFiberNormalization_not_isIso
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G : GeomFiber.{u, v} X)
    (admissible : CanonicalObjectNormalizationAdmissible G.1.core) :
    ¬ IsIso (canonicalGeometryFiberNormalization G admissible) := by
  intro h
  letI : IsIso (canonicalGeometryFiberNormalization G admissible) := h
  letI : IsIso ((geometryFiberProjection X).map
      (canonicalGeometryFiberNormalization G admissible)) := by
    infer_instance
  have hCore : IsIso
      (show G.1.core ⟶ G.1.core from
        canonicalObjectNormalizationTotal G.1.core admissible) := by
    change IsIso
      (CategoryTheory.Functor.Fiber.fiberInclusion.map
        ((geometryFiberProjection X).map
          (canonicalGeometryFiberNormalization G admissible)))
    infer_instance
  exact canonicalObjectNormalizationTotal_not_isIso G.1.core admissible
    (canonicalObjectNormalization_not_injective G.1.core) hCore

/-- Canonical complete-geometry normalization cannot be the identity. -/
theorem canonicalGeometryFiberNormalization_ne_id
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G : GeomFiber.{u, v} X)
    (admissible : CanonicalObjectNormalizationAdmissible G.1.core) :
    canonicalGeometryFiberNormalization G admissible ≠ 𝟙 G := by
  intro h
  apply canonicalGeometryFiberNormalization_not_isIso G admissible
  rw [h]
  infer_instance

/-- The semantic bottom-transport/right-pull route retains the nontrivial
normalization endomorphism of its source geometry. -/
theorem semanticGeometryViaRoute_map_normalization_ne_id
    {U : AtomCarrier.{u}}
    {X Y Z : ExtractionInstance U}
    (bottom : ExtInstHom X Z) (right : ExtInstHom Y Z)
    (G : GeomFiber.{u, v} X)
    (admissible : CanonicalObjectNormalizationAdmissible G.1.core) :
    (geomFiberTransportFunctor bottom ⋙
        semanticGeometryPullFunctor right).map
          (canonicalGeometryFiberNormalization G admissible) ≠ 𝟙 _ := by
  letI : (geomFiberTransportFunctor.{u, v} bottom).Faithful :=
    semanticGeomFiberTransportFunctor_faithful bottom
  letI : (semanticGeometryPullFunctor.{u, v} right).Faithful :=
    semanticGeometryPullFunctor_faithful right
  let route := geomFiberTransportFunctor bottom ⋙
    semanticGeometryPullFunctor right
  letI : route.Faithful := by infer_instance
  intro h
  exact canonicalGeometryFiberNormalization_ne_id G admissible
    ((functor_map_eq_id_iff_of_faithful route
      (canonicalGeometryFiberNormalization G admissible)).1 h)


section Comparison

variable {U : AtomCarrier.{u}}
variable (input : BCSemanticInput U)
variable (interpretation : BCDiagnosticInterpretation U input)
variable (z : input.diagnostic.TwoCell)
variable (omega : DefectCochain interpretation.data)
variable (k : Type v) [CommRing k]
variable (g : FixedCoefficientGeometryAt
  (semanticExactBarSourceCoreAt input interpretation z) k)
variable (endpoint_eq : packagePoint
  (semanticExactBarSourceCoreAt input interpretation z) =
    input.square.southwest)
variable (square_isPullback : IsPullback input.square.left input.square.top
  input.square.bottom input.square.right)

/-- Admissibility of the generated via-base complete geometry, derived from
the one southwest source core. -/
theorem semanticExactViaBaseGeometryAt_admissible
    (admissible : CanonicalObjectNormalizationAdmissible
      (semanticExactBarSourceCoreAt input interpretation z)) :
    CanonicalObjectNormalizationAdmissible
      (semanticDerivedViaBaseGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq).1.core :=
  canonicalGeometryNormalizationAdmissible_semanticExactPull
    input.square.right
    (semanticDerivedTargetGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z)
      k g endpoint_eq)
    (canonicalGeometryNormalizationAdmissible_semanticExactTransport
      input.square.bottom
      (semanticDerivedSouthwestGeometryFiber input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq) admissible)

/-- Admissibility of the generated direct complete geometry, derived from
the same southwest source core. -/
theorem semanticExactDirectGeometryAt_admissible
    (admissible : CanonicalObjectNormalizationAdmissible
      (semanticExactBarSourceCoreAt input interpretation z)) :
    CanonicalObjectNormalizationAdmissible
      (semanticDerivedDirectGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq).1.core :=
  canonicalGeometryNormalizationAdmissible_semanticExactTransport
    input.square.top
    (semanticDerivedLeftPulledGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z)
      k g endpoint_eq)
    (canonicalGeometryNormalizationAdmissible_semanticExactPull
      input.square.left
      (semanticDerivedSouthwestGeometryFiber input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq) admissible)

/-- Admissibility at the northwest endpoint of the left then bottom pull
route. -/
theorem semanticExactBGeometryAt_admissible
    (admissible : CanonicalObjectNormalizationAdmissible
      (semanticExactBarSourceCoreAt input interpretation z)) :
    CanonicalObjectNormalizationAdmissible
      (semanticDerivedBGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq).1.core :=
  canonicalGeometryNormalizationAdmissible_semanticExactPull
    input.square.left
    (semanticDerivedBottomPulledTargetGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z)
      k g endpoint_eq)
    (canonicalGeometryNormalizationAdmissible_semanticExactPull
      input.square.bottom
      (semanticDerivedTargetGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq)
      (canonicalGeometryNormalizationAdmissible_semanticExactTransport
        input.square.bottom
        (semanticDerivedSouthwestGeometryFiber input
          (semanticExactBarSourceCoreAt input interpretation z)
          k g endpoint_eq) admissible))

/-- Admissibility at the northwest endpoint of the top then right pull
route. -/
theorem semanticExactTGeometryAt_admissible
    (admissible : CanonicalObjectNormalizationAdmissible
      (semanticExactBarSourceCoreAt input interpretation z)) :
    CanonicalObjectNormalizationAdmissible
      (semanticDerivedTGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq).1.core :=
  canonicalGeometryNormalizationAdmissible_semanticExactPull
    input.square.top
    (semanticDerivedViaBaseGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z)
      k g endpoint_eq)
    (semanticExactViaBaseGeometryAt_admissible
      input interpretation z k g endpoint_eq admissible)

/-- When the literal cochain selector fires, both complete-geometry endpoint
cores satisfy canonical normalization admissibility. -/
theorem semanticExactBarEndpoints_admissible
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    CanonicalObjectNormalizationAdmissible
        (semanticDerivedDirectGeometryAt input
          (semanticExactBarSourceCoreAt input interpretation z)
          k g endpoint_eq).1.core ∧
      CanonicalObjectNormalizationAdmissible
        (semanticDerivedViaBaseGeometryAt input
          (semanticExactBarSourceCoreAt input interpretation z)
          k g endpoint_eq).1.core :=
  ⟨semanticExactDirectGeometryAt_admissible
      input interpretation z k g endpoint_eq selected.2,
    semanticExactViaBaseGeometryAt_admissible
      input interpretation z k g endpoint_eq selected.2⟩

/-- On the selected branch, the target projector is the normalization of
the literal via-base endpoint. -/
theorem semanticExactBarDAt_eq_endpoint_normalization
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    semanticExactBarDAt input interpretation z omega k g endpoint_eq =
      canonicalGeometryFiberNormalization
        (semanticDerivedViaBaseGeometryAt input
          (semanticExactBarSourceCoreAt input interpretation z)
          k g endpoint_eq)
        (semanticExactViaBaseGeometryAt_admissible
          input interpretation z k g endpoint_eq selected.2) := by
  rw [semanticExactBarDAt_eq_normalization_route
    input interpretation z omega k g endpoint_eq selected]
  rw [semanticGeomFiberTransportFunctor_map_normalization]
  exact semanticGeometryPullFunctor_map_normalization
    input.square.right
    (semanticDerivedTargetGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z)
      k g endpoint_eq)
    (canonicalGeometryNormalizationAdmissible_semanticExactTransport
      input.square.bottom
      (semanticDerivedSouthwestGeometryFiber input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq) selected.2)

/-- Source projector obtained by conjugating the generated target projector
along the complete semantic comparison isomorphism. -/
noncomputable def semanticExactBarEAt :
    semanticDerivedDirectGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq ⟶
      semanticDerivedDirectGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq :=
  (semanticDerivedBarAlphaIsoAt input
    (semanticExactBarSourceCoreAt input interpretation z)
    k g endpoint_eq square_isPullback).hom ≫
      semanticExactBarDAt input interpretation z omega k g endpoint_eq ≫
        (semanticDerivedBarAlphaIsoAt input
          (semanticExactBarSourceCoreAt input interpretation z)
          k g endpoint_eq square_isPullback).inv

/-- The selected complete-geometry comparison is the generated comparison
followed by the target projector. -/
noncomputable def semanticExactBarBetaAt :
    semanticDerivedDirectGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq ⟶
      semanticDerivedViaBaseGeometryAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq :=
  (semanticDerivedBarAlphaIsoAt input
    (semanticExactBarSourceCoreAt input interpretation z)
    k g endpoint_eq square_isPullback).hom ≫
      semanticExactBarDAt input interpretation z omega k g endpoint_eq

/-- The conjugate source projector is idempotent. -/
theorem semanticExactBarEAt_idem :
    semanticExactBarEAt input interpretation z omega k g endpoint_eq
        square_isPullback ≫
      semanticExactBarEAt input interpretation z omega k g endpoint_eq
        square_isPullback =
      semanticExactBarEAt input interpretation z omega k g endpoint_eq
        square_isPullback := by
  simp only [semanticExactBarEAt, Category.assoc,
    Iso.inv_hom_id_assoc]
  rw [← Category.assoc
      (semanticExactBarDAt input interpretation z omega k g endpoint_eq)
      (semanticExactBarDAt input interpretation z omega k g endpoint_eq)
      (semanticDerivedBarAlphaIsoAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq square_isPullback).inv,
    semanticExactBarDAt_idem]

/-- The selected comparison is absorbed by its source projector. -/
theorem semanticExactBarBetaAt_source_factorization :
    semanticExactBarEAt input interpretation z omega k g endpoint_eq
        square_isPullback ≫
      semanticExactBarBetaAt input interpretation z omega k g endpoint_eq
        square_isPullback =
      semanticExactBarBetaAt input interpretation z omega k g endpoint_eq
        square_isPullback := by
  simp [semanticExactBarEAt, semanticExactBarBetaAt,
    Category.assoc, semanticExactBarDAt_idem]

/-- The selected comparison is absorbed by its target projector. -/
theorem semanticExactBarBetaAt_target_factorization :
    semanticExactBarBetaAt input interpretation z omega k g endpoint_eq
        square_isPullback ≫
      semanticExactBarDAt input interpretation z omega k g endpoint_eq =
      semanticExactBarBetaAt input interpretation z omega k g endpoint_eq
        square_isPullback := by
  simp [semanticExactBarBetaAt, Category.assoc,
    semanticExactBarDAt_idem]

/-- Karoubi image selected by the source projector. -/
noncomputable def semanticExactBarESourceKaroubiAt :
    Karoubi (GeomFiber input.square.northeast) where
  X := semanticDerivedDirectGeometryAt input
    (semanticExactBarSourceCoreAt input interpretation z)
    k g endpoint_eq
  p := semanticExactBarEAt input interpretation z omega k g endpoint_eq
    square_isPullback
  idem := semanticExactBarEAt_idem input interpretation z omega k g
    endpoint_eq square_isPullback

/-- Karoubi image selected by the target projector. -/
noncomputable def semanticExactBarDTargetKaroubiAt :
    Karoubi (GeomFiber input.square.northeast) where
  X := semanticDerivedViaBaseGeometryAt input
    (semanticExactBarSourceCoreAt input interpretation z)
    k g endpoint_eq
  p := semanticExactBarDAt input interpretation z omega k g endpoint_eq
  idem := semanticExactBarDAt_idem input interpretation z omega k g endpoint_eq

/-- The generated selected comparison induces an isomorphism of its two
Karoubi images, with inverse underlying map `barD ≫ barAlpha⁻¹`. -/
noncomputable def semanticExactBarBetaKaroubiIsoAt :
    semanticExactBarESourceKaroubiAt input interpretation z omega k g
        endpoint_eq square_isPullback ≅
      semanticExactBarDTargetKaroubiAt input interpretation z omega k g
        endpoint_eq where
  hom :=
    { f := semanticExactBarBetaAt input interpretation z omega k g endpoint_eq
        square_isPullback
      comm := by
        change semanticExactBarEAt input interpretation z omega k g endpoint_eq
            square_isPullback ≫
          semanticExactBarBetaAt input interpretation z omega k g endpoint_eq
            square_isPullback ≫
          semanticExactBarDAt input interpretation z omega k g endpoint_eq =
          semanticExactBarBetaAt input interpretation z omega k g endpoint_eq
            square_isPullback
        rw [semanticExactBarBetaAt_target_factorization,
          semanticExactBarBetaAt_source_factorization] }
  inv :=
    { f := semanticExactBarDAt input interpretation z omega k g endpoint_eq ≫
        (semanticDerivedBarAlphaIsoAt input
          (semanticExactBarSourceCoreAt input interpretation z)
          k g endpoint_eq square_isPullback).inv
      comm := by
        change semanticExactBarDAt input interpretation z omega k g endpoint_eq ≫
            (semanticExactBarDAt input interpretation z omega k g endpoint_eq ≫
              (semanticDerivedBarAlphaIsoAt input
                (semanticExactBarSourceCoreAt input interpretation z)
                k g endpoint_eq square_isPullback).inv) ≫
              semanticExactBarEAt input interpretation z omega k g endpoint_eq
                square_isPullback =
          semanticExactBarDAt input interpretation z omega k g endpoint_eq ≫
            (semanticDerivedBarAlphaIsoAt input
              (semanticExactBarSourceCoreAt input interpretation z)
              k g endpoint_eq square_isPullback).inv
        simp only [semanticExactBarEAt, Category.assoc,
          Iso.inv_hom_id_assoc]
        rw [← Category.assoc
            (semanticExactBarDAt input interpretation z omega k g endpoint_eq)
            (semanticExactBarDAt input interpretation z omega k g endpoint_eq)
            (semanticDerivedBarAlphaIsoAt input
              (semanticExactBarSourceCoreAt input interpretation z)
              k g endpoint_eq square_isPullback).inv,
          semanticExactBarDAt_idem,
          ← Category.assoc
            (semanticExactBarDAt input interpretation z omega k g endpoint_eq)
            (semanticExactBarDAt input interpretation z omega k g endpoint_eq)
            (semanticDerivedBarAlphaIsoAt input
              (semanticExactBarSourceCoreAt input interpretation z)
              k g endpoint_eq square_isPullback).inv,
          semanticExactBarDAt_idem] }
  hom_inv_id := by
    apply Karoubi.Hom.ext
    change semanticExactBarBetaAt input interpretation z omega k g endpoint_eq
        square_isPullback ≫
      (semanticExactBarDAt input interpretation z omega k g endpoint_eq ≫
        (semanticDerivedBarAlphaIsoAt input
          (semanticExactBarSourceCoreAt input interpretation z)
          k g endpoint_eq square_isPullback).inv) =
      semanticExactBarEAt input interpretation z omega k g endpoint_eq
        square_isPullback
    simp only [semanticExactBarBetaAt, semanticExactBarEAt,
      Category.assoc]
    rw [← Category.assoc
        (semanticExactBarDAt input interpretation z omega k g endpoint_eq)
        (semanticExactBarDAt input interpretation z omega k g endpoint_eq)
        (semanticDerivedBarAlphaIsoAt input
          (semanticExactBarSourceCoreAt input interpretation z)
          k g endpoint_eq square_isPullback).inv,
      semanticExactBarDAt_idem]
  inv_hom_id := by
    apply Karoubi.Hom.ext
    change (semanticExactBarDAt input interpretation z omega k g endpoint_eq ≫
        (semanticDerivedBarAlphaIsoAt input
          (semanticExactBarSourceCoreAt input interpretation z)
          k g endpoint_eq square_isPullback).inv) ≫
      semanticExactBarBetaAt input interpretation z omega k g endpoint_eq
        square_isPullback =
      semanticExactBarDAt input interpretation z omega k g endpoint_eq
    simp only [semanticExactBarBetaAt, Category.assoc,
      Iso.inv_hom_id_assoc]
    rw [semanticExactBarDAt_idem]

/-- On the selected branch, the conjugate source projector agrees with the
canonical normalization of the literal direct endpoint. -/
theorem semanticExactBarEAt_eq_endpoint_normalization
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    semanticExactBarEAt input interpretation z omega k g endpoint_eq
        square_isPullback =
      canonicalGeometryFiberNormalization
        (semanticDerivedDirectGeometryAt input
          (semanticExactBarSourceCoreAt input interpretation z)
          k g endpoint_eq)
        (semanticExactDirectGeometryAt_admissible
          input interpretation z k g endpoint_eq selected.2) := by
  let alpha := semanticDerivedBarAlphaIsoAt input
    (semanticExactBarSourceCoreAt input interpretation z)
    k g endpoint_eq square_isPullback
  let nDirect := canonicalGeometryFiberNormalization
    (semanticDerivedDirectGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z)
      k g endpoint_eq)
    (semanticExactDirectGeometryAt_admissible
      input interpretation z k g endpoint_eq selected.2)
  let nVia := canonicalGeometryFiberNormalization
    (semanticDerivedViaBaseGeometryAt input
      (semanticExactBarSourceCoreAt input interpretation z)
      k g endpoint_eq)
    (semanticExactViaBaseGeometryAt_admissible
      input interpretation z k g endpoint_eq selected.2)
  have naturality : nDirect ≫ alpha.hom = alpha.hom ≫ nVia := by
    simpa only [alpha, nDirect, nVia] using
      (semanticDerivedBarAlphaIsoAt_normalization_natural
        input (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq square_isPullback selected.2)
  have hD : semanticExactBarDAt input interpretation z omega k g endpoint_eq =
      nVia := by
    exact semanticExactBarDAt_eq_endpoint_normalization
      input interpretation z omega k g endpoint_eq selected
  apply (cancel_mono alpha.hom).1
  calc
    semanticExactBarEAt input interpretation z omega k g endpoint_eq
        square_isPullback ≫ alpha.hom =
      alpha.hom ≫ semanticExactBarDAt input interpretation z omega k g
        endpoint_eq := by
      simp [semanticExactBarEAt, alpha, Category.assoc]
    _ = alpha.hom ≫ nVia := by rw [hD]
    _ = nDirect ≫ alpha.hom := naturality.symm

/-- The two selected endpoint projectors are exactly the canonical
normalizations of their respective literal geometry endpoints. -/
theorem semanticExactBarProjectorsAt_eq_endpoint_normalizations
    (selected : semanticExactBarSelectedAt input interpretation z omega) :
    semanticExactBarEAt input interpretation z omega k g endpoint_eq
        square_isPullback =
        canonicalGeometryFiberNormalization
          (semanticDerivedDirectGeometryAt input
            (semanticExactBarSourceCoreAt input interpretation z)
            k g endpoint_eq)
          (semanticExactDirectGeometryAt_admissible
            input interpretation z k g endpoint_eq selected.2) ∧
      semanticExactBarDAt input interpretation z omega k g endpoint_eq =
        canonicalGeometryFiberNormalization
          (semanticDerivedViaBaseGeometryAt input
            (semanticExactBarSourceCoreAt input interpretation z)
            k g endpoint_eq)
          (semanticExactViaBaseGeometryAt_admissible
            input interpretation z k g endpoint_eq selected.2) :=
  ⟨semanticExactBarEAt_eq_endpoint_normalization
      input interpretation z omega k g endpoint_eq square_isPullback selected,
    semanticExactBarDAt_eq_endpoint_normalization
      input interpretation z omega k g endpoint_eq selected⟩

/-- The target projector is the identity exactly when the literal cochain
selector does not fire. -/
theorem semanticExactBarDAt_eq_id_iff :
    semanticExactBarDAt input interpretation z omega k g endpoint_eq = 𝟙 _ ↔
      ¬ semanticExactBarSelectedAt input interpretation z omega := by
  constructor
  · intro h selected
    rw [semanticExactBarDAt_eq_normalization_route
      input interpretation z omega k g endpoint_eq selected] at h
    exact semanticGeometryViaRoute_map_normalization_ne_id
      input.square.bottom input.square.right
      (semanticDerivedSouthwestGeometryFiber input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq) selected.2 h
  · exact semanticExactBarDAt_eq_id
      input interpretation z omega k g endpoint_eq

/-- An invertible idempotent endomorphism is the identity. -/
private theorem semanticIsIso_iff_eq_id_of_idempotent
    {C : Type u} [Category.{v} C] {Z : C} (e : Z ⟶ Z)
    (idem : e ≫ e = e) : IsIso e ↔ e = 𝟙 Z := by
  constructor
  · intro isIso
    letI : IsIso e := isIso
    exact (cancel_epi_id e).1 idem
  · rintro rfl
    infer_instance

/-- The generated selected comparison is invertible precisely when its target
projector is the identity. -/
theorem semanticExactBarBetaAt_isIso_iff_barDAt_eq_id :
    IsIso (semanticExactBarBetaAt input interpretation z omega k g endpoint_eq
      square_isPullback) ↔
      semanticExactBarDAt input interpretation z omega k g endpoint_eq = 𝟙 _ := by
  change IsIso
      ((semanticDerivedBarAlphaIsoAt input
        (semanticExactBarSourceCoreAt input interpretation z)
        k g endpoint_eq square_isPullback).hom ≫
          semanticExactBarDAt input interpretation z omega k g endpoint_eq) ↔ _
  exact (isIso_comp_left_iff _ _).trans
    (semanticIsIso_iff_eq_id_of_idempotent
      (semanticExactBarDAt input interpretation z omega k g endpoint_eq)
      (semanticExactBarDAt_idem input interpretation z omega k g endpoint_eq))

/-- Full nonisomorphism classification against the actual G-106 selector. -/
theorem semanticExactBarBetaAt_isIso_iff_not_selected :
    IsIso (semanticExactBarBetaAt input interpretation z omega k g endpoint_eq
      square_isPullback) ↔
      ¬ semanticExactBarSelectedAt input interpretation z omega :=
  (semanticExactBarBetaAt_isIso_iff_barDAt_eq_id
    input interpretation z omega k g endpoint_eq square_isPullback).trans
    (semanticExactBarDAt_eq_id_iff
      input interpretation z omega k g endpoint_eq)

/-- Off the selector both endpoint projectors are identities. -/
theorem semanticExactBarProjectorsAt_eq_id
    (notSelected : ¬ semanticExactBarSelectedAt input interpretation z omega) :
    semanticExactBarEAt input interpretation z omega k g endpoint_eq
        square_isPullback = 𝟙 _ ∧
      semanticExactBarDAt input interpretation z omega k g endpoint_eq =
        𝟙 _ := by
  have hD := semanticExactBarDAt_eq_id
    input interpretation z omega k g endpoint_eq notSelected
  constructor
  · simp [semanticExactBarEAt, hD]
  · exact hD

end Comparison

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
