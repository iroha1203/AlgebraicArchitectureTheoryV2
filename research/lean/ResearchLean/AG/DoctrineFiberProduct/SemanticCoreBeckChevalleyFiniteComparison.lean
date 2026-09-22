import ResearchLean.AG.DoctrineFiberProduct.SemanticCoreBeckChevalleyMate
import ResearchLean.AG.DoctrineFiberProduct.BCPresentationReplacement

/-! Comparison of semantic-global Beck--Chevalley data with decoded finite presentations. -/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

/-- The unrestricted reindexing agrees with the finite selected reindexing
after the canonical comparison of their cartesian lifts. -/
noncomputable def semanticFiniteReindexComparison
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U) :
    exact_bottom_semantic_global_reindex_functor input.semantic.hom ≅
      selectedCoreFiberReindexFunctor input := by
  exact coreFiberCleavageSelectedComparison input
    (exact_bottom_semantic_global_cartesian_cleavage input.semantic.hom)

/-- The bridge to the finite selected functor preserves the actual cartesian
lift, so it records a map law as well as an objectwise isomorphism. -/
theorem semanticFiniteReindexComparison_hom_fac
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (input : RealizableHom U)
    (targetPackage : CoreFiber input.semantic.target) :
    ((semanticFiniteReindexComparison input).hom.app targetPackage).1 ≫
      (selectedCoreFiberCartesianLift input targetPackage).hom =
    (exact_bottom_semantic_global_selected_lift input.semantic.hom
      targetPackage).hom := by
  exact coreFiberCleavageSelectedComparisonApp_hom_fac input
    (exact_bottom_semantic_global_cartesian_cleavage input.semantic.hom)
    targetPackage

/-- The semantic covariant comparison specializes to the finite square
comparison after decoding, including all four mapped base arrows. -/
theorem semanticCoreTransportSquareIso_decode
    {U : AtomCarrier.{u}} [DecidableEq U.Atom]
    (presentation : BCPresentation U) :
    semanticCoreTransportSquareIso (decodeBCSquare presentation) =
      bcCoreTransportSquareIso presentation := by
  have h := bcProvenanceCoreTransportSquareIso_eq_semantic
    (BCRealizationProvenance.mk presentation rfl :
      BCRealizationProvenance (toSemanticBC presentation))
  change bcCoreTransportSquareIso presentation =
    semanticCoreTransportSquareIso (decodeBCSquare presentation) at h
  exact h.symm

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
