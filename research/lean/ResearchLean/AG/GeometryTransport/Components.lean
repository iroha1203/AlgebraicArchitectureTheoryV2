import ResearchLean.AG.GeometryTransport.LiftUniqueness
import Mathlib.CategoryTheory.Sites.Equivalence

/-!
# Standalone geometry-transport components and topology

This module exposes the site, coefficient, and raw-system computations made by
the single canonical geometry transport.  It also transports admissible cover
families across the canonical context equivalence, which is the generator-level
input for the covering-sieve comparison.
-/

namespace AAT.AG.GeometryTransport

universe u v

open CategoryTheory
open AtomFoundation

/-! ## Standalone component computations -/

/-- Canonical geometry transport uses the freely pushed selected geometry. -/
@[simp] theorem geomTransportAlong_geometry_eq {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E) :
    (geomTransportAlong G sigma).geometry =
      pushSelectedGeometry G (transportAlongHom G.core sigma) :=
  rfl

/-- G-108 (ii)/(iv) exactness provenance for the canonical geometry target:
its transported source commutes with doctrine normalization.  Unlike the Atom
family equations, this standalone component law uses `sigma.normalize_eq`
through the reviewed G-101 transport API. -/
theorem geomTransportAlong_normalize_source_eq {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E) :
    (geomTransportAlong G sigma).core.reading.doctrine.normalize
        (geomTransportAlong G sigma).core.reading.source =
      sigma.sourceMap
        (G.core.reading.doctrine.normalize G.core.reading.source) := by
  exact transportAlong_normalize_source_eq G.core sigma

/-- The transported requirements are exactly the free forward coverage predicates. -/
@[simp] theorem geomTransportAlong_requirements_eq {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E) :
    (geomTransportAlong G sigma).geometry.requirements =
      pushCoverage G (transportAlongHom G.core sigma) :=
  rfl

/-- The transported overlap package is exactly inverse-context reindexing. -/
@[simp] theorem geomTransportAlong_overlap_eq {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E) :
    (geomTransportAlong G sigma).geometry.overlap =
      pushOverlap G (transportAlongHom G.core sigma) :=
  rfl

/-- Canonical geometry transport retains the coefficient type. -/
@[simp] theorem geomTransportAlong_coefficient_eq {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E) :
    (geomTransportAlong G sigma).Coefficient = G.Coefficient :=
  rfl

/-- The canonical raw system is identity base change followed by context reindexing. -/
@[simp] theorem geomTransportAlong_raw_eq {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E) :
    (geomTransportAlong G sigma).raw =
      rawReindexCore G.geometry
        (pushSelectedGeometry G (transportAlongHom G.core sigma))
        (transportAlongHom G.core sigma)
        (G.raw.baseChange (RingHom.id G.Coefficient)) :=
  rfl

/-- Objectwise canonical transport copies the inverse-indexed coordinate family. -/
@[simp] theorem geomTransportAlong_coordinateFamily_eq {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    (W : (geomTransportAlong G sigma).site.category) :
    (geomTransportAlong G sigma).raw.coordFamily W =
      copyCoordinateFamily (V := W.ctx)
        ((G.raw.baseChange (RingHom.id G.Coefficient)).coordFamily
          ((contextInverse (transportAlongHom G.core sigma)).obj W)) :=
  rfl

/-- Objectwise canonical transport copies the inverse-indexed relation family. -/
@[simp] theorem geomTransportAlong_relationFamily_eq {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    (W : (geomTransportAlong G sigma).site.category) :
    (geomTransportAlong G sigma).raw.relationFamily W =
      copyRelationFamily (V := W.ctx)
        ((G.raw.baseChange (RingHom.id G.Coefficient)).relationFamily
          ((contextInverse (transportAlongHom G.core sigma)).obj W)) :=
  rfl

/-! ## Canonical context cancellation at raw-context level -/

/-- Inverse-after-forward canonical transport fixes each raw source context. -/
theorem canonicalContextBackwardMap_forward {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    (W : Site.ArchCtx G.core.object) :
    contextBackwardMap (G := G) (H := geomTransportAlong G sigma)
        (transportAlongHom G.core sigma)
        (contextMap (G := G) (H := geomTransportAlong G sigma)
          (transportAlongHom G.core sigma) W) = W := by
  exact congrArg (fun X => X.ctx)
    (canonicalContextRetraction_eq G sigma ⟨W⟩)

/-- Core-level inverse-after-forward transport fixes each raw source context. -/
theorem canonicalCoreContextBackwardMap_forward {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    (W : Site.ArchCtx G.core.object) :
    coreContextBackwardMap
        (P := G.core) (Q := (geomTransportAlong G sigma).core)
        (transportAlongHom G.core sigma)
        (coreContextMap
          (P := G.core) (Q := (geomTransportAlong G sigma).core)
          (transportAlongHom G.core sigma) W) = W := by
  exact congrArg (fun X => X.ctx)
    (canonicalContextRetraction_eq G sigma ⟨W⟩)

/-- Forward-after-inverse canonical transport fixes each raw target context. -/
theorem canonicalContextForwardMap_backward {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    (W : Site.ArchCtx (geomTransportAlong G sigma).core.object) :
    contextMap (G := G) (H := geomTransportAlong G sigma)
        (transportAlongHom G.core sigma)
        (contextBackwardMap (G := G) (H := geomTransportAlong G sigma)
          (transportAlongHom G.core sigma) W) = W := by
  exact congrArg (fun X => X.ctx)
    (canonicalContextSection_eq G sigma ⟨W⟩)

/-- Core-level forward-after-inverse transport fixes each raw target context. -/
theorem canonicalCoreContextForwardMap_backward {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    (W : Site.ArchCtx (geomTransportAlong G sigma).core.object) :
    coreContextMap
        (P := G.core) (Q := (geomTransportAlong G sigma).core)
        (transportAlongHom G.core sigma)
        (coreContextBackwardMap
          (P := G.core) (Q := (geomTransportAlong G sigma).core)
          (transportAlongHom G.core sigma) W) = W := by
  exact congrArg (fun X => X.ctx)
    (canonicalContextSection_eq G sigma ⟨W⟩)

/-- Canonical overlap reindexing sends a source overlap to the overlap of the
three corresponding target contexts. -/
theorem canonical_pushOverlap_forward {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    (base left right : Site.ArchCtx G.core.object) :
    (pushOverlap G (transportAlongHom G.core sigma)).overlap
        (contextMap (G := G) (H := geomTransportAlong G sigma)
          (transportAlongHom G.core sigma) base)
        (contextMap (G := G) (H := geomTransportAlong G sigma)
          (transportAlongHom G.core sigma) left)
        (contextMap (G := G) (H := geomTransportAlong G sigma)
          (transportAlongHom G.core sigma) right) =
      contextMap (G := G) (H := geomTransportAlong G sigma)
        (transportAlongHom G.core sigma)
        (G.geometry.overlap.overlap base left right) := by
  simp only [pushOverlap]
  change coreContextMap (transportAlongHom G.core sigma)
      (G.geometry.overlap.overlap
        (coreContextBackwardMap (transportAlongHom G.core sigma)
          (coreContextMap (transportAlongHom G.core sigma) base))
        (coreContextBackwardMap (transportAlongHom G.core sigma)
          (coreContextMap (transportAlongHom G.core sigma) left))
        (coreContextBackwardMap (transportAlongHom G.core sigma)
          (coreContextMap (transportAlongHom G.core sigma) right))) =
    coreContextMap (transportAlongHom G.core sigma)
      (G.geometry.overlap.overlap base left right)
  rw [canonicalCoreContextBackwardMap_forward,
    canonicalCoreContextBackwardMap_forward,
    canonicalCoreContextBackwardMap_forward]

/-! ## Forward transport of admissible cover generators -/

/-- A source admissible family transported by the canonical context functor. -/
noncomputable def pushAATCoverageFamily {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {base : G.site.category}
    (family : Site.AATCoverageFamily G.geometry.requirements
      G.geometry.overlap base) :
    Site.AATCoverageFamily
      (geomTransportAlong G sigma).geometry.requirements
      (geomTransportAlong G sigma).geometry.overlap
      ((contextFunctor (G := G) (H := geomTransportAlong G sigma)
        (transportAlongHom G.core sigma)).obj base) where
  Index := family.Index
  patch i := ((contextFunctor (G := G) (H := geomTransportAlong G sigma)
    (transportAlongHom G.core sigma)).obj ⟨family.patch i⟩).ctx
  inclusion i :=
    ((contextFunctor (G := G) (H := geomTransportAlong G sigma)
      (transportAlongHom G.core sigma)).map
      (homOfLE (family.inclusion i))).le
  admissible := by
    let f := transportAlongHom G.core sigma
    constructor
    · intro atom hrequired
      rcases hrequired with ⟨source, hsource, rfl⟩
      rcases family.admissible.atomSupportCoverage source hsource with ⟨i, hi⟩
      exact ⟨i, family.patch i, source, hi, rfl, rfl⟩
    · intro coordinate hrequired
      rcases hrequired with ⟨source, hsource, rfl⟩
      rcases family.admissible.equationCoordinateCoverage source hsource with
        hpatch | hoverlap
      · left
        rcases hpatch with ⟨i, hi⟩
        exact ⟨i, family.patch i, source, hi, rfl, rfl⟩
      · right
        rcases hoverlap with ⟨i, j, hij⟩
        refine ⟨i, j, G.geometry.overlap.overlap base.ctx
          (family.patch i) (family.patch j), source, hij, ?_, rfl⟩
        exact (canonical_pushOverlap_forward G sigma
          base.ctx (family.patch i) (family.patch j)).symm
    · intro coordinate hrequired
      rcases hrequired with ⟨source, hsource, rfl⟩
      rcases family.admissible.violationWitnessCoverage source hsource with
        hpatch | hoverlap
      · left
        rcases hpatch with ⟨i, hi⟩
        exact ⟨i, family.patch i, source, hi, rfl, rfl⟩
      · right
        rcases hoverlap with ⟨i, j, hij⟩
        refine ⟨i, j, G.geometry.overlap.overlap base.ctx
          (family.patch i) (family.patch j), source, hij, ?_, rfl⟩
        exact (canonical_pushOverlap_forward G sigma
          base.ctx (family.patch i) (family.patch j)).symm
    · intro axis hrequired
      rcases hrequired with ⟨source, hsource, rfl⟩
      rcases family.admissible.signatureAxisCoverage source hsource with ⟨i, hi⟩
      exact ⟨i, family.patch i, source, hi, rfl, rfl⟩
    · intro i j
      refine ⟨G.geometry.overlap.overlap base.ctx
        (family.patch i) (family.patch j), base.ctx,
        family.admissible.boundaryCoverage i j, ?_, rfl⟩
      exact (canonical_pushOverlap_forward G sigma
        base.ctx (family.patch i) (family.patch j)).symm
    · intro i
      exact Site.CoverageFamily.inclusion_nonGenerating _ i

/-- The transported family's presieve is exactly the image presieve, before
sieve generation. -/
theorem pushAATCoverageFamily_presieve {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {base : G.site.category}
    (family : Site.AATCoverageFamily G.geometry.requirements
      G.geometry.overlap base) :
    (pushAATCoverageFamily G sigma family).presieve =
      family.presieve.map
        (contextFunctor (G := G) (H := geomTransportAlong G sigma)
          (transportAlongHom G.core sigma)) := by
  rw [Site.AATCoverageFamily.presieve, Site.AATCoverageFamily.presieve,
    Presieve.map_ofArrows]
  apply le_antisymm
  · intro Y arrow h
    rcases h with ⟨i⟩
    exact Presieve.ofArrows.mk' i rfl (Subsingleton.elim _ _)
  · intro Y arrow h
    rcases h with ⟨i⟩
    exact Presieve.ofArrows.mk' i rfl (Subsingleton.elim _ _)

/-- Source covering sieves remain covering after canonical pushforward into
the topology generated by the transported requirements and overlap. -/
theorem geomSourceTopology_le_inducedTarget {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E) :
    G.site.topology ≤
      (contextFunctor (G := G) (H := geomTransportAlong G sigma)
        (transportAlongHom G.core sigma)).inducedTopology
        (geomTransportAlong G sigma).site.topology := by
  change (Site.admissiblePrecoverage G.geometry.requirements
      G.geometry.overlap).toGrothendieck ≤ _
  rw [Precoverage.toGrothendieck_eq_sInf]
  apply sInf_le
  intro base R hR
  rcases hR with ⟨family, rfl⟩
  change (Sieve.generate family.presieve).functorPushforward
      (contextFunctor (G := G) (H := geomTransportAlong G sigma)
        (transportAlongHom G.core sigma)) ∈
    (geomTransportAlong G sigma).site.topology _
  rw [← Sieve.generate_map_eq_functorPushforward]
  rw [← pushAATCoverageFamily_presieve G sigma family]
  exact Site.AATGrothendieckTopology.generate_mem
    (pushAATCoverageFamily G sigma family)

/-! ## Reverse transport of admissible cover generators -/

/-- The exact required-coordinate map is injective. -/
theorem requiredCoordinateMap_injective {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (f : PackageTotalHom G.core H.core) :
    Function.Injective (requiredCoordinateMap f) := by
  intro x y hxy
  apply Prod.ext
  · apply Subtype.ext
    exact f.upper.equationTransport.equationEquiv.injective
      (congrArg (fun z => z.1.1) hxy)
  · exact f.upper.atomEquiv.injective (congrArg Prod.snd hxy)

/-- The exact violation-coordinate map is injective. -/
theorem equationCoordinateMap_injective {U : AtomCarrier.{u}}
    {G H : GeometryPackage.{u, v} U}
    (f : PackageTotalHom G.core H.core) :
    Function.Injective (equationCoordinateMap f) := by
  intro x y hxy
  apply Prod.ext
  · exact f.upper.equationTransport.equationEquiv.injective
      (congrArg Prod.fst hxy)
  · exact f.upper.atomEquiv.injective (congrArg Prod.snd hxy)

/-- The canonical core context map is injective on actual context objects. -/
theorem canonicalCoreContextMap_injective {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E) :
    Function.Injective (coreContextMap
      (P := G.core) (Q := (geomTransportAlong G sigma).core)
      (transportAlongHom G.core sigma)) := by
  intro W V hWV
  calc
    W = coreContextBackwardMap (transportAlongHom G.core sigma)
        (coreContextMap (transportAlongHom G.core sigma) W) :=
      (canonicalCoreContextBackwardMap_forward G sigma W).symm
    _ = coreContextBackwardMap (transportAlongHom G.core sigma)
        (coreContextMap (transportAlongHom G.core sigma) V) :=
      congrArg (coreContextBackwardMap (transportAlongHom G.core sigma)) hWV
    _ = V := canonicalCoreContextBackwardMap_forward G sigma V

/-- A target generator pulled back by the inverse canonical context functor. -/
noncomputable def pullAATCoverageFamily {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {base : (geomTransportAlong G sigma).site.category}
    (family : Site.AATCoverageFamily
      (geomTransportAlong G sigma).geometry.requirements
      (geomTransportAlong G sigma).geometry.overlap base) :
    Site.AATCoverageFamily G.geometry.requirements G.geometry.overlap
      ((contextInverse (G := G) (H := geomTransportAlong G sigma)
        (transportAlongHom G.core sigma)).obj base) where
  Index := family.Index
  patch i := ((contextInverse (G := G) (H := geomTransportAlong G sigma)
    (transportAlongHom G.core sigma)).obj ⟨family.patch i⟩).ctx
  inclusion i :=
    ((contextInverse (G := G) (H := geomTransportAlong G sigma)
      (transportAlongHom G.core sigma)).map
      (homOfLE (family.inclusion i))).le
  admissible := by
    let f := transportAlongHom G.core sigma
    constructor
    · intro atom hrequired
      have htarget : (geomTransportAlong G sigma).geometry.requirements.requiredSupport
          (f.upper.atomEquiv atom) := ⟨atom, hrequired, rfl⟩
      rcases family.admissible.atomSupportCoverage _ htarget with ⟨i, hi⟩
      rcases hi with ⟨sourceW, sourceAtom, hvis, hW, hAtom⟩
      have hAtomEq : sourceAtom = atom := f.upper.atomEquiv.injective hAtom
      have hWEq : sourceW = contextBackwardMap f (family.patch i) := by
        apply canonicalCoreContextMap_injective G sigma
        exact hW.trans (canonicalCoreContextForwardMap_backward
          G sigma (family.patch i)).symm
      exact ⟨i, by simpa [hWEq, hAtomEq] using hvis⟩
    · intro coordinate hrequired
      have htarget := show
        (geomTransportAlong G sigma).geometry.requirements.requiredEquationCoordinate
          (requiredCoordinateMap f coordinate) from ⟨coordinate, hrequired, rfl⟩
      rcases family.admissible.equationCoordinateCoverage _ htarget with
        hpatch | hoverlap
      · left
        rcases hpatch with ⟨i, sourceW, sourceCoordinate, hvis, hW, hCoordinate⟩
        have hCoordinateEq : sourceCoordinate = coordinate :=
          requiredCoordinateMap_injective
            (G := G) (H := geomTransportAlong G sigma) f hCoordinate
        have hWEq : sourceW = contextBackwardMap f (family.patch i) := by
          apply canonicalCoreContextMap_injective G sigma
          exact hW.trans (canonicalCoreContextForwardMap_backward
            G sigma (family.patch i)).symm
        exact ⟨i, by simpa [hWEq, hCoordinateEq] using hvis⟩
      · right
        rcases hoverlap with
          ⟨i, j, sourceW, sourceCoordinate, hvis, hW, hCoordinate⟩
        have hCoordinateEq : sourceCoordinate = coordinate :=
          requiredCoordinateMap_injective
            (G := G) (H := geomTransportAlong G sigma) f hCoordinate
        have hWEq : sourceW = G.geometry.overlap.overlap
            (contextBackwardMap f base.ctx)
            (contextBackwardMap f (family.patch i))
            (contextBackwardMap f (family.patch j)) := by
          apply canonicalCoreContextMap_injective G sigma
          exact hW
        exact ⟨i, j, by simpa [hWEq, hCoordinateEq] using hvis⟩
    · intro coordinate hrequired
      have htarget := show
        (geomTransportAlong G sigma).geometry.requirements.selectedViolationWitness
          (equationCoordinateMap f coordinate) from ⟨coordinate, hrequired, rfl⟩
      rcases family.admissible.violationWitnessCoverage _ htarget with
        hpatch | hoverlap
      · left
        rcases hpatch with ⟨i, sourceW, sourceCoordinate, hvis, hW, hCoordinate⟩
        have hCoordinateEq : sourceCoordinate = coordinate :=
          equationCoordinateMap_injective
            (G := G) (H := geomTransportAlong G sigma) f hCoordinate
        have hWEq : sourceW = contextBackwardMap f (family.patch i) := by
          apply canonicalCoreContextMap_injective G sigma
          exact hW.trans (canonicalCoreContextForwardMap_backward
            G sigma (family.patch i)).symm
        exact ⟨i, by simpa [hWEq, hCoordinateEq] using hvis⟩
      · right
        rcases hoverlap with
          ⟨i, j, sourceW, sourceCoordinate, hvis, hW, hCoordinate⟩
        have hCoordinateEq : sourceCoordinate = coordinate :=
          equationCoordinateMap_injective
            (G := G) (H := geomTransportAlong G sigma) f hCoordinate
        have hWEq : sourceW = G.geometry.overlap.overlap
            (contextBackwardMap f base.ctx)
            (contextBackwardMap f (family.patch i))
            (contextBackwardMap f (family.patch j)) := by
          apply canonicalCoreContextMap_injective G sigma
          exact hW
        exact ⟨i, j, by simpa [hWEq, hCoordinateEq] using hvis⟩
    · intro axis hrequired
      have htarget := show
        (geomTransportAlong G sigma).geometry.requirements.requiredAxis
          (f.upper.axisMap axis) from ⟨axis, hrequired, rfl⟩
      rcases family.admissible.signatureAxisCoverage _ htarget with ⟨i, hi⟩
      rcases hi with ⟨sourceW, sourceAxis, hvis, hW, hAxis⟩
      have hAxisEq : sourceAxis = axis := by
        simpa [f, transportAlongHom, transportAlongUpper] using hAxis
      have hWEq : sourceW = contextBackwardMap f (family.patch i) := by
        apply canonicalCoreContextMap_injective G sigma
        exact hW.trans (canonicalCoreContextForwardMap_backward
          G sigma (family.patch i)).symm
      exact ⟨i, by simpa [hWEq, hAxisEq] using hvis⟩
    · intro i j
      rcases family.admissible.boundaryCoverage i j with
        ⟨sourceW, sourceV, hvis, hW, hV⟩
      have hWEq : sourceW = G.geometry.overlap.overlap
          (contextBackwardMap f base.ctx)
          (contextBackwardMap f (family.patch i))
          (contextBackwardMap f (family.patch j)) := by
        apply canonicalCoreContextMap_injective G sigma
        exact hW
      have hVEq : sourceV = contextBackwardMap f base.ctx := by
        apply canonicalCoreContextMap_injective G sigma
        exact hV.trans (canonicalCoreContextForwardMap_backward
          G sigma base.ctx).symm
      simpa [hWEq, hVEq] using hvis
    · intro i
      exact Site.CoverageFamily.inclusion_nonGenerating _ i

/-- The pulled family's presieve is exactly the image under the inverse
context functor. -/
theorem pullAATCoverageFamily_presieve {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    {base : (geomTransportAlong G sigma).site.category}
    (family : Site.AATCoverageFamily
      (geomTransportAlong G sigma).geometry.requirements
      (geomTransportAlong G sigma).geometry.overlap base) :
    (pullAATCoverageFamily G sigma family).presieve =
      family.presieve.map
        (contextInverse (G := G) (H := geomTransportAlong G sigma)
          (transportAlongHom G.core sigma)) := by
  rw [Site.AATCoverageFamily.presieve, Site.AATCoverageFamily.presieve,
    Presieve.map_ofArrows]
  apply le_antisymm
  · intro Y arrow h
    rcases h with ⟨i⟩
    exact Presieve.ofArrows.mk' i rfl (Subsingleton.elim _ _)
  · intro Y arrow h
    rcases h with ⟨i⟩
    exact Presieve.ofArrows.mk' i rfl (Subsingleton.elim _ _)

/-- Target covering sieves remain covering after pushforward by the inverse
canonical context functor. -/
theorem geomTargetTopology_le_inducedSource {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E) :
    (geomTransportAlong G sigma).site.topology ≤
      (contextInverse (G := G) (H := geomTransportAlong G sigma)
        (transportAlongHom G.core sigma)).inducedTopology G.site.topology := by
  change (Site.admissiblePrecoverage
      (geomTransportAlong G sigma).geometry.requirements
      (geomTransportAlong G sigma).geometry.overlap).toGrothendieck ≤ _
  rw [Precoverage.toGrothendieck_eq_sInf]
  apply sInf_le
  intro base R hR
  rcases hR with ⟨family, rfl⟩
  change (Sieve.generate family.presieve).functorPushforward
      (contextInverse (G := G) (H := geomTransportAlong G sigma)
        (transportAlongHom G.core sigma)) ∈ G.site.topology _
  rw [← Sieve.generate_map_eq_functorPushforward]
  rw [← pullAATCoverageFamily_presieve G sigma family]
  exact Site.AATGrothendieckTopology.generate_mem
    (pullAATCoverageFamily G sigma family)

/-- Canonical geometry transport preserves and reflects every covering sieve
of the generated AAT topologies.  The right-hand sieve is the actual Mathlib
functor pushforward, not an identity-index surrogate. -/
theorem geomTransportAlong_coveringSieve_iff {U : AtomCarrier.{u}}
    (G : GeometryPackage.{u, v} U) {E : ExtractionDoctrine U}
    (sigma : ExactDoctrineHom G.core.reading.doctrine E)
    (W : G.site.category) (S : Sieve W) :
    S ∈ G.site.topology W ↔
      S.functorPushforward
          (contextFunctor (G := G) (H := geomTransportAlong G sigma)
            (transportAlongHom G.core sigma)) ∈
        (geomTransportAlong G sigma).site.topology
          ((contextFunctor (G := G) (H := geomTransportAlong G sigma)
            (transportAlongHom G.core sigma)).obj W) := by
  constructor
  · intro hS
    exact geomSourceTopology_le_inducedTarget G sigma W hS
  · intro hS
    let e := (transportAlongHom G.core sigma).upper.equationTransport.contextEquivalence
    have hback := geomTargetTopology_le_inducedSource G sigma
      ((contextFunctor (G := G) (H := geomTransportAlong G sigma)
        (transportAlongHom G.core sigma)).obj W) hS
    change (S.functorPushforward e.functor).functorPushforward e.inverse ∈
      G.site.topology (e.inverse.obj (e.functor.obj W)) at hback
    rw [Sieve.functorPushforward_equivalence_eq_pullback e S] at hback
    exact (GrothendieckTopology.pullback_mem_iff_of_isIso
      (J := G.site.topology) (i := e.unitInv.app W)).mp hback

end AAT.AG.GeometryTransport

#assert_standard_axioms_only AAT.AG.GeometryTransport
