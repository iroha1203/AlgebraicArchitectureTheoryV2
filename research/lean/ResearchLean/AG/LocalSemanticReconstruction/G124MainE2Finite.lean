import ResearchLean.AG.LocalSemanticReconstruction.CSFiniteValueQueryBridge
import ResearchLean.AG.LocalSemanticReconstruction.CSFiniteDecoderValueBridge
import ResearchLean.AG.LocalSemanticReconstruction.CSFixedFFiberD
import Formal.Util.AssertStandardAxioms

/-! Design IV-4/E2: the separate general-Hom finite reading criteria are
exposed beside the exact common-main Hom obtained from every original value
table. The executable path retains its enumerated input contracts. -/
namespace AAT.AG.LocalSemanticReconstruction.G124MainTheorem
open CategoryTheory RealizationReconstruction IndependentAATPrimitiveReconstruction
universe u

/-- Every lens semantic Hom is separated by the complete reference fiber,
every raw table extends, and the original executable program applies; each
actual Hom is the same main-N image of its table extension. -/
theorem lens_general_finite_reading
    (input : LensFamilyInput.{u})
    (X Y : LensRealization input.View input.reference)
    [Fintype X.Fiber] :
    FiniteReading.Separates
      (LensSemanticFiniteDetermination.readLensHomAt X Y)
      (LensSemanticFiniteDetermination.fullFiber X) ∧
    FiniteReading.Extends
      (LensSemanticFiniteDetermination.readLensHomAt X Y)
      (LensSemanticFiniteDetermination.fullFiber X)
      (LensSemanticFiniteDetermination.TableAdmissible X Y) ∧
    FiniteReading.Effective
      (LensSemanticFiniteDetermination.readLensHomAt X Y)
      (LensSemanticFiniteDetermination.fullFiber X)
      (LensSemanticFiniteDetermination.TableAdmissible X Y) ∧
    (∀ f : X ⟶ Y,
      (reading (Parameter.lens input : Parameter.{u, u})).map (ULift.up f) =
        (reading (Parameter.lens input : Parameter.{u, u})).map
          (ULift.up (LensSemanticFiniteDetermination.assembleTable X Y
            (FiniteReading.restrict
              (LensSemanticFiniteDetermination.readLensHomAt X Y)
              (LensSemanticFiniteDetermination.fullFiber X) f)))) := by
  refine ⟨LensSemanticFiniteDetermination.fullFiber_separates X Y,
    LensSemanticFiniteDetermination.fullFiber_extends X Y,
    LensSemanticFiniteDetermination.fullFiber_effective X Y, ?_⟩
  intro f
  exact congrArg (fun g : X ⟶ Y =>
    (reading (Parameter.lens input : Parameter.{u, u})).map (ULift.up g))
    (CSFiniteValueQueryBridge.lens_assemble_restricted_values input X Y f).symm

/-- The general protocol table uses independent tag, named-edge and
observation equations; all coherent tables extend. Its assembled original
Hom is the one read by common N. -/
theorem protocol_general_finite_reading
    (input : ProtocolFamilyInput.{u})
    (P Q : ProtocolRealization input.schema input.observation)
    [Fintype (ProtocolObservedFiniteDetermination.InputPoint P)]
    [DecidableEq input.schema.Vertex] :
    FiniteReading.Separates
      (ProtocolObservedFiniteDetermination.readProtocolHomAt P Q)
      (ProtocolObservedFiniteDetermination.fullInput P) ∧
    FiniteReading.Extends
      (ProtocolObservedFiniteDetermination.readProtocolHomAt P Q)
      (ProtocolObservedFiniteDetermination.fullInput P)
      (ProtocolObservedFiniteDetermination.TableCoherent P Q) ∧
    (∀ f : P ⟶ Q,
      (reading (Parameter.protocol input : Parameter.{u, u})).map (ULift.up f) =
        (reading (Parameter.protocol input : Parameter.{u, u})).map
          (ULift.up (ProtocolObservedFiniteDetermination.assembleTable P Q
            (FiniteReading.restrict
              (ProtocolObservedFiniteDetermination.readProtocolHomAt P Q)
              (ProtocolObservedFiniteDetermination.fullInput P) f)
            (ProtocolObservedFiniteDetermination.read_table_coherent P Q f)))) := by
  refine ⟨ProtocolObservedFiniteDetermination.fullInput_separates P Q,
    ProtocolObservedFiniteDetermination.fullInput_extends P Q, ?_⟩
  intro f
  exact congrArg (fun g : P ⟶ Q =>
    (reading (Parameter.protocol input : Parameter.{u, u})).map (ULift.up g))
    (CSFiniteValueQueryBridge.protocol_assemble_restricted_values
      input P Q f).symm

/-- The original executable protocol general-Hom program applies when its
finite vertex, state, edge and tagged observation comparison inputs are
provided. No observation carrier is required to be finite. -/
theorem protocol_general_effective
    (input : ProtocolFamilyInput.{u})
    (P Q : ProtocolRealization input.schema input.observation)
    [Fintype input.schema.Vertex] [DecidableEq input.schema.Vertex]
    [∀ vertex, Fintype (P.State vertex)]
    [∀ vertex, DecidableEq (Q.State vertex)]
    [∀ source target, Fintype (input.schema.Edge source target)]
    [DecidableEq (ProtocolObservedFiniteDetermination.ObservationValue
      (S := input.schema) (O := input.observation))] :
    FiniteReading.Effective
      (ProtocolObservedFiniteDetermination.readProtocolHomAt P Q)
      (ProtocolObservedFiniteDetermination.fullInput P)
      (ProtocolObservedFiniteDetermination.TableCoherent P Q) :=
  ProtocolObservedFiniteDetermination.fullInput_effective P Q

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G124MainTheorem

end AAT.AG.LocalSemanticReconstruction.G124MainTheorem
