import ResearchLean.AG.LocalSemanticReconstruction.ProtocolObservedRestrictionModel
import Formal.Util.AssertStandardAxioms

/-!
# Reconstruction of protocol realizations from observed restrictions

An observation-aware finite restriction model already supplies a finite state
at every quotient execution, coherent restriction maps, and a natural
observation into the fixed parameter-owned observation diagram.  Transporting
that data across the double opposite constructs a protocol realization
directly.  No presentation, decoder membership, realizability witness, or
extension certificate is stored or assumed.

Reading the reconstructed realization returns the original observed model up
to a componentwise identity isomorphism.  An isomorphism, rather than strict
equality, is necessary because `finiteLocalValue` may choose a different
`Fintype` instance for the same underlying finite carrier.  Together with the
previously proved full faithfulness, this gives the protocol-branch category
equivalence.  This is reconstruction from the complete family of quotient-
execution restrictions; it makes no finite generator-table or effectiveness
claim.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory
open AAT.AG.RealizationReconstruction

universe u v

/-- Reconstruct a protocol realization from its complete observed finite
restriction family.  Every field comes from the local diagram or its primitive
observation map. -/
noncomputable def protocolObservedRestrictionRealization
    (input : ProtocolFamilyInput.{u})
    (Z : ProtocolObservedRestrictionModel input) :
    ProtocolRealization input.schema input.observation where
  toFunctor :=
    { obj := fun q => Z.stateDiagram.obj
          (Opposite.op (Opposite.op q))
      map := fun f => Z.stateDiagram.map f.op.op
      map_id := by
        intro q
        funext state
        simp
      map_comp := by
        intro q r s f g
        funext state
        simp }
  state_finite := fun vertex => by infer_instance
  observation :=
    { app := fun q => Z.observe.app (Opposite.op (Opposite.op q))
      naturality := by
        intro q r f
        funext state
        simpa [protocolFiniteDiagramUnderlying, protocolObservationDiagram] using
          congrFun (Z.observe.naturality f.op.op) state }

/-- The finite state diagram obtained by reading the reconstructed realization
is componentwise the original diagram.  The maps are identity functions on
the underlying carriers; the isomorphism ignores the possibly different
chosen finite enumerations. -/
noncomputable def protocolObservedRestrictionStateIso
    (input : ProtocolFamilyInput.{u})
    (Z : ProtocolObservedRestrictionModel input) :
    (protocolObservedRestrictionObject input
        (protocolObservedRestrictionRealization input Z)).stateDiagram ≅
      Z.stateDiagram :=
  NatIso.ofComponents
    (fun q => by
      cases q with
      | op q =>
        cases q with
        | op q => exact FintypeCat.equivEquivIso (Equiv.refl _))
    (by
      intro q r f
      apply FintypeCat.hom_ext
      intro state
      rfl)

/-- Reading a reconstructed realization is isomorphic to the supplied
observed local model.  Both directions are identity-on-carriers and preserve
the supplied observation map. -/
noncomputable def protocolObservedRestrictionRealizationIso
    (input : ProtocolFamilyInput.{u})
    (Z : ProtocolObservedRestrictionModel input) :
    protocolObservedRestrictionObject input
        (protocolObservedRestrictionRealization input Z) ≅ Z where
  hom :=
    { stateMap := (protocolObservedRestrictionStateIso input Z).hom
      observation_naturality := by
        apply NatTrans.ext
        funext q state
        simp [protocolObservedRestrictionStateIso,
          protocolObservedRestrictionRealization,
          protocolObservedRestrictionObject,
          protocolFiniteDiagramUnderlying]
        change Z.observe.app q state = Z.observe.app q state
        rfl }
  inv :=
    { stateMap := (protocolObservedRestrictionStateIso input Z).inv
      observation_naturality := by
        apply NatTrans.ext
        funext q state
        simp [protocolObservedRestrictionStateIso,
          protocolObservedRestrictionRealization,
          protocolObservedRestrictionObject,
          protocolFiniteDiagramUnderlying]
        change Z.observe.app q state = Z.observe.app q state
        rfl }
  hom_inv_id := by
    apply ProtocolObservedRestrictionHom.ext
    exact (protocolObservedRestrictionStateIso input Z).hom_inv_id
  inv_hom_id := by
    apply ProtocolObservedRestrictionHom.ext
    exact (protocolObservedRestrictionStateIso input Z).inv_hom_id

/-- Every observed finite restriction model is, up to its harmless choice of
finite enumerations, the reading of a reconstructed protocol realization. -/
noncomputable def protocolObservedRestrictionReadingEssSurj
    (input : ProtocolFamilyInput.{u}) :
    (protocolObservedRestrictionReading input).EssSurj :=
  Functor.EssSurj.mk fun Z =>
    ⟨FamilyRealization.protocol
        (protocolObservedRestrictionRealization input Z),
      ⟨protocolObservedRestrictionRealizationIso input Z⟩⟩

/-- The accepted protocol realization category is equivalent to the category
of complete observation-aware finite restriction families. -/
noncomputable def protocolObservedRestrictionEquivalence
    (input : ProtocolFamilyInput.{u}) :
    FamilyRealization.{u, v} (.protocol input) ≌
      ProtocolObservedRestrictionModel input := by
  letI : (protocolObservedRestrictionReading input).Faithful :=
    protocolObservedRestrictionReadingFaithful input
  letI : (protocolObservedRestrictionReading input).Full :=
    protocolObservedRestrictionReadingFull input
  letI : (protocolObservedRestrictionReading input).EssSurj :=
    protocolObservedRestrictionReadingEssSurj input
  letI : (protocolObservedRestrictionReading input).IsEquivalence := {}
  exact (protocolObservedRestrictionReading input).asEquivalence

/-- The forward functor of the protocol equivalence is definitionally the
primitive observation-aware restriction reading. -/
@[simp] theorem protocolObservedRestrictionEquivalence_functor
    (input : ProtocolFamilyInput.{u}) :
    (protocolObservedRestrictionEquivalence input).functor =
      protocolObservedRestrictionReading input :=
  rfl

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction

end AAT.AG.LocalSemanticReconstruction
