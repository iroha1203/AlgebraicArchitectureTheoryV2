import ResearchLean.AG.DoctrineFiberProduct.BCPresentationReplacement

/-!
# Provenance via-base route API

The provenance route is definitionally a two-stage composite.  This
lightweight theorem exposes that composition to downstream equivalence proofs
without requiring them to unfold the route definition or import a higher
G-116 classification module.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence TransportCoherence

/-- The provenance-indexed via-base route is the bottom transport followed by
selected reindexing along the right realization. -/
theorem bcProvenanceViaBaseRoute_eq
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    {input : BCSemanticInput U} (provenance : BCRealizationProvenance input) :
    bcProvenanceViaBaseRoute provenance =
      coreFiberTransportFunctor input.square.bottom ⋙
        selectedCoreFiberReindexFunctor
          provenance.rightProvenance.toRealizableHom :=
  rfl

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct

end AAT.AG.DoctrineFiberProduct
