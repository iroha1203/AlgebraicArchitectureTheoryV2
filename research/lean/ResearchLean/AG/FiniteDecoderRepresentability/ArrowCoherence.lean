import ResearchLean.AG.FiniteDecoderRepresentability.DiscreteCompactness
import Formal.Util.AssertStandardAxioms

/-!
# Coverage-presentation and finite-decoder arrow coherence

This module completes the arrow-coherence clause of G-121(B).  It exposes the
actual source map and Atom permutation read by `typedPresentationToSemantic`,
specializes those formulas to the presentation constructed by the G-112
coverage theorem, and identifies typed decoding with the morphism action of
`finiteCodeCartRealization`, including identity and composition.
-/

namespace AAT.AG.FiniteDecoderRepresentability

universe u

open CategoryTheory AtomFoundation DoctrineFiberProduct

variable {U : AtomCarrier.{u}}

/-- Typed decoding reads exactly the authored source-map field. -/
@[simp]
theorem typedPresentationToSemantic_sourceMap
    [DecidableEq U.Atom] {source target : FiniteInstanceCode U}
    (presentation : CartPresentationBetween source target) :
    (typedPresentationToSemantic presentation).doctrineHom.sourceMap =
      presentation.sourceMap :=
  rfl

/-- Typed decoding reads exactly the permutation decoded from the authored table. -/
@[simp]
theorem typedPresentationToSemantic_atomEquiv
    [DecidableEq U.Atom] {source target : FiniteInstanceCode U}
    (presentation : CartPresentationBetween source target) :
    (typedPresentationToSemantic presentation).doctrineHom.atomEquiv =
      presentation.atomEquiv.toEquiv :=
  rfl

/--
The G-112 coverage presentation's decoded source map is the semantic source map
transported across the generated finite endpoint enumerations.
-/
theorem endpointFiniteTargetCofinitePresentation_decoded_sourceMap_apply
    [DecidableEq U.Atom] (input : CartSemanticInput U)
    [Finite input.source.doctrine.Source]
    [Finite input.target.doctrine.Source]
    (htarget : AllExtractionsFiniteOrCofinite input.target)
    (source : (finiteCofiniteInstanceCodeOf input.source
      (allExtractionsFiniteOrCofinite_source_of_hom input.hom htarget)
      (Equiv.refl U.Atom)).doctrine.Source) :
    (typedPresentationToSemantic
      (endpointFiniteTargetCofinitePresentation input htarget)).doctrineHom.sourceMap
        source =
      (finiteSourceEquiv input.target.doctrine.Source).symm
        (input.hom.doctrineHom.sourceMap
          (finiteSourceEquiv input.source.doctrine.Source source)) :=
  rfl

/-- The G-112 coverage presentation itself decodes the identity Atom permutation. -/
theorem endpointFiniteTargetCofinitePresentation_decoded_atomEquiv
    [DecidableEq U.Atom] (input : CartSemanticInput U)
    [Finite input.source.doctrine.Source]
    [Finite input.target.doctrine.Source]
    (htarget : AllExtractionsFiniteOrCofinite input.target) :
    (typedPresentationToSemantic
      (endpointFiniteTargetCofinitePresentation input htarget)).doctrineHom.atomEquiv =
        Equiv.refl U.Atom := by
  exact AtomPermutationCode.toEquiv_refl

/--
The G-112 generated endpoint isomorphisms and the typed decoder form the actual
semantic square used by the coverage witness.
-/
theorem endpointFiniteTargetCofinitePresentation_typed_hom_comm
    [DecidableEq U.Atom] (input : CartSemanticInput U)
    [Finite input.source.doctrine.Source]
    [Finite input.target.doctrine.Source]
    (htarget : AllExtractionsFiniteOrCofinite input.target) :
    (finiteCofiniteInstanceCodeOfIso input.source
        (allExtractionsFiniteOrCofinite_source_of_hom input.hom htarget)
        (Equiv.refl U.Atom)).hom ≫ input.hom =
      typedPresentationToSemantic
          (endpointFiniteTargetCofinitePresentation input htarget) ≫
        (finiteCofiniteInstanceCodeOfIso input.target htarget
          input.hom.doctrineHom.atomEquiv).hom := by
  exact endpointFiniteTargetCofinitePresentation_hom_comm input htarget

/-- `D₀` maps a represented morphism to the same arrow as direct typed decoding. -/
@[simp]
theorem finiteCodeCartRealization_map_ofPresentation
    [DecidableEq U.Atom] {source target : FiniteInstanceCode U}
    (presentation : CartPresentationBetween source target) :
    finiteCodeCartRealization.map
        (FiniteCodeCartHom.ofPresentation presentation) =
      typedPresentationToSemantic presentation :=
  rfl

/-- The typed identity presentation and `D₀` both evaluate to semantic identity. -/
@[simp]
theorem typedPresentationToSemantic_id
    [DecidableEq U.Atom] (object : FiniteInstanceCode U) :
    typedPresentationToSemantic (idTypedPresentation object) =
      𝟙 object.toSemantic := by
  have h := finiteCodeCartRealization.map_id object
  change typedPresentationToSemantic (idTypedPresentation object) =
    𝟙 object.toSemantic at h
  exact h

/-- Typed composition and the compositional action of `D₀` have the same evaluation. -/
theorem typedPresentationToSemantic_comp
    [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target) :
    typedPresentationToSemantic (compPresentation first second) =
      typedPresentationToSemantic first ≫
        typedPresentationToSemantic second := by
  exact toSemanticCart_compPresentation_hom first second

#assert_standard_axioms_only AAT.AG.FiniteDecoderRepresentability

end AAT.AG.FiniteDecoderRepresentability
