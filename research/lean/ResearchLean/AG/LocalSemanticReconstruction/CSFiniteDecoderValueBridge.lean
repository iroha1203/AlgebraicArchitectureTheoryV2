import ResearchLean.AG.LocalSemanticReconstruction.CSFiniteValueQueryBridge
import Formal.Util.AssertStandardAxioms
/-! Design IV-3: small finite value tables and their actual semantic extensions
are evaluated through the same primitive local Hom as the accepted finite
decoder, fiber/observed comparison, and Karoubi/Arrow routes. -/
namespace AAT.AG.LocalSemanticReconstruction
open CategoryTheory RealizationReconstruction IndependentAATPrimitiveReconstruction

open FiniteApplicationHomDecoders
namespace CSFiniteDecoderValueBridge
universe u

theorem lens_decoder_value_iff_main_point
    (input : LensFamilyInput.{u}) {p q : LensPresentation}
    (arrow : p ⟶ q)
    (state : ((LensRealization.lensDecoder input.View input.reference).obj p).Fiber)
    (output : ((LensRealization.lensDecoder input.View input.reference).obj q).Fiber) :
    LensSemanticFiniteDetermination.readLensHomAt
      ((LensRealization.lensDecoder input.View input.reference).obj p)
      ((LensRealization.lensDecoder input.View input.reference).obj q)
      ((LensRealization.lensDecoder input.View input.reference).map arrow) state = output ↔
      decodeLensPoint input
        (ULiftHom.objUp ((LensRealization.lensDecoder input.View input.reference).obj p))
        (ULiftHom.objUp ((LensRealization.lensDecoder input.View input.reference).obj q))
        state.1 output.1
        (localHomTable (.lens input) ((lensFiniteDecoder input).map arrow)) = true := by
  exact CSFiniteValueQueryBridge.lens_value_iff_primitive_point input
    ((LensRealization.lensDecoder input.View input.reference).obj p)
    ((LensRealization.lensDecoder input.View input.reference).obj q)
    ((LensRealization.lensDecoder input.View input.reference).map arrow) state output


theorem protocol_decoder_value_iff_main_point
    (input : ProtocolFamilyInput.{u})
    {p q : ProtocolPresentation input.schema input.observation}
    (arrow : p ⟶ q)
    (vertex : input.schema.Vertex)
    (state : ((ProtocolPresentation.decoder input.schema input.observation).obj p).State vertex)
    (output : ((ProtocolPresentation.decoder input.schema input.observation).obj q).State vertex) :
    ProtocolObservedFiniteDetermination.readProtocolHomAt
      ((ProtocolPresentation.decoder input.schema input.observation).obj p)
      ((ProtocolPresentation.decoder input.schema input.observation).obj q)
      ((ProtocolPresentation.decoder input.schema input.observation).map arrow)
        ⟨vertex,state⟩ = ⟨vertex,output⟩ ↔
      decodeProtocolPoint input
        (ULiftHom.objUp ((ProtocolPresentation.decoder input.schema input.observation).obj p))
        (ULiftHom.objUp ((ProtocolPresentation.decoder input.schema input.observation).obj q))
        vertex state output
        (localHomTable (.protocol input) ((protocolFiniteDecoder input).map arrow)) = true := by
  exact CSFiniteValueQueryBridge.protocol_value_iff_primitive_point input
    ((ProtocolPresentation.decoder input.schema input.observation).obj p)
    ((ProtocolPresentation.decoder input.schema input.observation).obj q)
    ((ProtocolPresentation.decoder input.schema input.observation).map arrow)
      vertex state output


/-- The accepted finite lens decoder comparison commutes on every presentation
arrow; the value table equation above is evaluated on this same arrow. -/
theorem lens_finite_decoder_fiber_square
    (input : LensFamilyInput.{0}) {p q : LensPresentation}
    (arrow : p ⟶ q) :
    ((lensFiniteDecoder input ⋙ lensLocalToFiber input).map arrow) ≫
      (lensFiniteDecoderFiberIso input).hom.app q =
      (lensFiniteDecoderFiberIso input).hom.app p ≫
        (lensFiberFiniteDecoder input).map arrow := by
  exact (lensFiniteDecoderFiberIso input).hom.naturality arrow

/-- The corresponding accepted protocol decoder comparison commutes on the
same finite presentation arrow whose values are read above. -/
theorem protocol_finite_decoder_observed_square
    (input : ProtocolFamilyInput.{0})
    {p q : ProtocolPresentation input.schema input.observation}
    (arrow : p ⟶ q) :
    ((protocolFiniteDecoder input ⋙ protocolLocalToObserved input).map arrow) ≫
      (protocolFiniteDecoderObservedIso input).hom.app q =
      (protocolFiniteDecoderObservedIso input).hom.app p ≫
        (protocolObservedFiniteDecoder input).map arrow := by
  exact (protocolFiniteDecoderObservedIso input).hom.naturality arrow


/-- The finite lens decoder's actual arrow is read by its original finite
fiber table at the same primitive query. -/
theorem lens_decoder_restricted_table_iff_main_point
    (input : LensFamilyInput.{u}) {p q : LensPresentation}
    (arrow : p ⟶ q)
    [Fintype ((LensRealization.lensDecoder input.View input.reference).obj p).Fiber]
    (state : ((LensRealization.lensDecoder input.View input.reference).obj p).Fiber)
    (output : ((LensRealization.lensDecoder input.View input.reference).obj q).Fiber) :
    decodeLensPoint input
      (ULiftHom.objUp ((LensRealization.lensDecoder input.View input.reference).obj p))
      (ULiftHom.objUp ((LensRealization.lensDecoder input.View input.reference).obj q))
      state.1 output.1
      (localHomTable (.lens input) ((lensFiniteDecoder input).map arrow)) = true ↔
    (FiniteReading.restrict
      (LensSemanticFiniteDetermination.readLensHomAt
        ((LensRealization.lensDecoder input.View input.reference).obj p)
        ((LensRealization.lensDecoder input.View input.reference).obj q))
      (LensSemanticFiniteDetermination.fullFiber
        ((LensRealization.lensDecoder input.View input.reference).obj p))
      ((LensRealization.lensDecoder input.View input.reference).map arrow))
        ⟨state, Finset.mem_univ _⟩ = output := by
  rw [← lens_decoder_value_iff_main_point]
  rfl

/-- The finite protocol decoder's actual arrow is read by its original
finite vertex table at the same primitive query. -/
theorem protocol_decoder_restricted_table_iff_main_point
    (input : ProtocolFamilyInput.{u})
    {p q : ProtocolPresentation input.schema input.observation}
    (arrow : p ⟶ q)
    [Fintype (ProtocolObservedFiniteDetermination.InputPoint
      ((ProtocolPresentation.decoder input.schema input.observation).obj p))]
    (vertex : input.schema.Vertex)
    (state : ((ProtocolPresentation.decoder input.schema input.observation).obj p).State vertex)
    (output : ((ProtocolPresentation.decoder input.schema input.observation).obj q).State vertex) :
    decodeProtocolPoint input
      (ULiftHom.objUp ((ProtocolPresentation.decoder input.schema input.observation).obj p))
      (ULiftHom.objUp ((ProtocolPresentation.decoder input.schema input.observation).obj q))
      vertex state output
      (localHomTable (.protocol input) ((protocolFiniteDecoder input).map arrow)) = true ↔
    (FiniteReading.restrict
      (ProtocolObservedFiniteDetermination.readProtocolHomAt
        ((ProtocolPresentation.decoder input.schema input.observation).obj p)
        ((ProtocolPresentation.decoder input.schema input.observation).obj q))
      (ProtocolObservedFiniteDetermination.fullInput
        ((ProtocolPresentation.decoder input.schema input.observation).obj p))
      ((ProtocolPresentation.decoder input.schema input.observation).map arrow))
        ⟨⟨vertex,state⟩, Finset.mem_univ _⟩ = ⟨vertex,output⟩ := by
  rw [← protocol_decoder_value_iff_main_point]
  rfl


/-- The actual extension from a small lens table commutes with the accepted
semantic-to-primitive finite-fiber comparison square. -/
theorem lens_assembled_table_fiber_square
    (input : LensFamilyInput.{u})
    (X Y : LensRealization input.View input.reference)
    [Fintype X.Fiber]
    (table : LensSemanticFiniteDetermination.RawTable X Y) :
    (((lensSemanticPrimitiveEquivalence input).functor ⋙ lensLocalToFiber input).map
        (LensSemanticFiniteDetermination.assembleTable X Y table)) ≫
      (lensSemanticPrimitiveFiberComparisonIso input).hom.app Y =
      (lensSemanticPrimitiveFiberComparisonIso input).hom.app X ≫
        (lensSemanticFiberReading input).map
          (LensSemanticFiniteDetermination.assembleTable X Y table) := by
  exact (lensSemanticPrimitiveFiberComparisonIso input).hom.naturality _

/-- The actual extension from a coherent protocol table commutes with the
accepted semantic-to-primitive observed comparison square. -/
theorem protocol_assembled_table_observed_square
    (input : ProtocolFamilyInput.{u})
    (P Q : ProtocolRealization input.schema input.observation)
    [Fintype (ProtocolObservedFiniteDetermination.InputPoint P)]
    [DecidableEq input.schema.Vertex]
    (table : ProtocolObservedFiniteDetermination.RawTable P Q)
    (coherent : ProtocolObservedFiniteDetermination.TableCoherent P Q table) :
    (((protocolSemanticPrimitiveEquivalence input).functor ⋙
        protocolLocalToObserved input).map
          (ProtocolObservedFiniteDetermination.assembleTable P Q table coherent)) ≫
      (protocolSemanticPrimitiveObservedComparisonIso input).hom.app Q =
      (protocolSemanticPrimitiveObservedComparisonIso input).hom.app P ≫
        (protocolSemanticObservedRestrictionEquivalence input).functor.map
          (ProtocolObservedFiniteDetermination.assembleTable P Q table coherent) := by
  exact (protocolSemanticPrimitiveObservedComparisonIso input).hom.naturality _


#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.CSFiniteDecoderValueBridge

end CSFiniteDecoderValueBridge
end AAT.AG.LocalSemanticReconstruction
