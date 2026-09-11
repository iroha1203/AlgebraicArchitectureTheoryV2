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

/--
G-121(B3) decoder API: typed decoding reads exactly the authored source-map
field.  The `simp` direction normalizes the semantic component to source data.
-/
@[simp]
theorem typedPresentationToSemantic_sourceMap
    [DecidableEq U.Atom] {source target : FiniteInstanceCode U}
    (presentation : CartPresentationBetween source target) :
    (typedPresentationToSemantic presentation).doctrineHom.sourceMap =
      presentation.sourceMap :=
  rfl

/--
G-121(B3) decoder API: typed decoding reads `AtomPermutationCode.toEquiv` of
the authored table.  The `simp` direction normalizes semantics to code data.
-/
@[simp]
theorem typedPresentationToSemantic_atomEquiv
    [DecidableEq U.Atom] {source target : FiniteInstanceCode U}
    (presentation : CartPresentationBetween source target) :
    (typedPresentationToSemantic presentation).doctrineHom.atomEquiv =
      presentation.atomEquiv.toEquiv :=
  rfl

/--
G-121(B3) coverage specialization: the G-112 presentation's decoded source map
is the semantic source map transported across its finite endpoint enumerations.
The `Finite` instances and `htarget` are exactly the constructor's hypotheses.
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

/--
G-121(B3) coverage specialization: the G-112 presentation itself decodes the
identity Atom permutation.  The input permutation remains in the target anchor;
the `Finite` instances and `htarget` come from the G-112 constructor.
-/
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
G-121(B3) main coverage bridge: the G-112 generated endpoint isomorphisms and
the typed decoder form the actual semantic square used by the coverage witness.
Its finiteness and target-extraction hypotheses are those of that constructor.
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

/--
G-121(B3) decoder bridge: `D₀` maps an authored quotient representative to the
same arrow as direct typed decoding.  The `simp` direction exposes that decoder.
-/
@[simp]
theorem finiteCodeCartRealization_map_ofPresentation
    [DecidableEq U.Atom] {source target : FiniteInstanceCode U}
    (presentation : CartPresentationBetween source target) :
    finiteCodeCartRealization.map
        (FiniteCodeCartHom.ofPresentation presentation) =
      typedPresentationToSemantic presentation :=
  rfl

/--
G-121(B3) identity law: the existing typed identity presentation evaluates to
semantic identity by `D₀.map_id`.  The `simp` direction selects that identity.
-/
@[simp]
theorem typedPresentationToSemantic_id
    [DecidableEq U.Atom] (object : FiniteInstanceCode U) :
    typedPresentationToSemantic (idTypedPresentation object) =
      𝟙 object.toSemantic := by
  have h := finiteCodeCartRealization.map_id object
  change typedPresentationToSemantic (idTypedPresentation object) =
    𝟙 object.toSemantic at h
  exact h

/--
G-121(B3) composition law: `D₀` evaluates the quotient representative of the
existing `compPresentation` as the composite of the two represented arrows.
-/
theorem finiteCodeCartRealization_map_compPresentation
    [DecidableEq U.Atom]
    {source middle target : FiniteInstanceCode U}
    (first : CartPresentationBetween source middle)
    (second : CartPresentationBetween middle target) :
    finiteCodeCartRealization.map
        (FiniteCodeCartHom.ofPresentation (compPresentation first second)) =
      finiteCodeCartRealization.map
          (FiniteCodeCartHom.ofPresentation first) ≫
        finiteCodeCartRealization.map
          (FiniteCodeCartHom.ofPresentation second) := by
  rw [finiteCodeCartRealization_map_ofPresentation,
    finiteCodeCartRealization_map_ofPresentation,
    finiteCodeCartRealization_map_ofPresentation]
  exact toSemanticCart_compPresentation_hom first second

#assert_standard_axioms_only AAT.AG.FiniteDecoderRepresentability

end AAT.AG.FiniteDecoderRepresentability
