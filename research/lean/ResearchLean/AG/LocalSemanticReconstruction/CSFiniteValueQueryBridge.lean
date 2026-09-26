import ResearchLean.AG.LocalSemanticReconstruction.FiniteApplicationHomDecoders
import ResearchLean.AG.LocalSemanticReconstruction.LensSemanticFiniteDetermination
import ResearchLean.AG.LocalSemanticReconstruction.ProtocolObservedFiniteDetermination
import Formal.Util.AssertStandardAxioms

/-! Design IV-3: the finite lens and protocol value tables are read at actual
point graph cells of the common main local Hom. The finite query selections
are independent of the morphism being tested. -/
namespace AAT.AG.LocalSemanticReconstruction
open CategoryTheory RealizationReconstruction IndependentAATPrimitiveReconstruction
open FiniteApplicationHomDecoders
universe u
namespace CSFiniteValueQueryBridge
variable {V : Type u} {reference : V}
    (input : LensFamilyInput.{u})
    (X Y : LensRealization input.View input.reference)
theorem lens_value_iff_primitive_point (f : X ⟶ Y)
    (state : X.Fiber) (output : Y.Fiber) :
    LensSemanticFiniteDetermination.readLensHomAt X Y f state = output ↔
      decodeLensPoint input (ULiftHom.objUp X) (ULiftHom.objUp Y)
        state.1 output.1
        (localHomTable (.lens input)
          ((reading (.lens input)).map (ULift.up f))) = true := by
  rw [lensPoint_decode]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact h

variable {S : ProtocolSchema.{u}} {O : S.ExecutionCategory ⥤ Type u}
    (protocolInput : ProtocolFamilyInput.{u})
    (P Q : ProtocolRealization protocolInput.schema protocolInput.observation)
theorem protocol_value_iff_primitive_point (f : P ⟶ Q)
    (vertex : protocolInput.schema.Vertex) (state : P.State vertex)
    (output : Q.State vertex) :
    ProtocolObservedFiniteDetermination.readProtocolHomAt P Q f ⟨vertex,state⟩ =
        ⟨vertex,output⟩ ↔
      decodeProtocolPoint protocolInput (ULiftHom.objUp P) (ULiftHom.objUp Q)
        vertex state output
        (localHomTable (.protocol protocolInput)
          ((reading (.protocol protocolInput)).map (ULift.up f))) = true := by
  rw [protocolPoint_decode]
  constructor
  · intro h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  · intro h
    exact congrArg (Sigma.mk vertex) h

/-- All primitive graph cells for the finite source and target reference fibers. -/
noncomputable def lensFiniteQuerySet [Fintype X.Fiber] :
    Finset (HomQuery (Parameter.lens input : Parameter.{u, u})) := by
  classical
  letI : Fintype Y.Fiber := Fintype.ofFinite _
  exact Finset.univ.biUnion (fun state : X.Fiber =>
    Finset.univ.image (fun output : Y.Fiber =>
      lensPointQuery input (ULiftHom.objUp X) (ULiftHom.objUp Y)
        state.1 output.1))

/-- The complete finite fiber value table is recovered from its selected
primitive graph cells in the main local Hom. -/
theorem lens_finite_query_separates [Fintype X.Fiber]
    (f g : X ⟶ Y)
    (agree : ∀ query ∈ lensFiniteQuerySet input X Y,
      localHomTable (.lens input)
          ((reading (.lens input)).map (ULift.up f)) query =
        localHomTable (.lens input)
          ((reading (.lens input)).map (ULift.up g)) query) : f = g := by
  apply LensSemanticFiniteDetermination.fullFiber_separates X Y
  funext point
  let state : X.Fiber := point.1
  let output : Y.Fiber := LensSemanticFiniteDetermination.readLensHomAt X Y f state
  have hmem : lensPointQuery input (ULiftHom.objUp X) (ULiftHom.objUp Y)
      state.1 output.1 ∈ lensFiniteQuerySet input X Y := by
    classical
    unfold lensFiniteQuerySet
    letI : Fintype Y.Fiber := Fintype.ofFinite _
    apply Finset.mem_biUnion.mpr
    refine ⟨state, Finset.mem_univ _, ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨output, Finset.mem_univ _, rfl⟩
  have hf : decodeLensPoint input (ULiftHom.objUp X) (ULiftHom.objUp Y)
        state.1 output.1
        (localHomTable (.lens input)
          ((reading (.lens input)).map (ULift.up f))) = true :=
    (lens_value_iff_primitive_point input X Y f state output).mp rfl
  have hg : decodeLensPoint input (ULiftHom.objUp X) (ULiftHom.objUp Y)
        state.1 output.1
        (localHomTable (.lens input)
          ((reading (.lens input)).map (ULift.up g))) = true := by
    rw [← hf]
    exact (agree _ hmem).symm
  exact (lens_value_iff_primitive_point input X Y g state output).mpr hg |>.symm


/-- The common protocol graph cells selected by all finite input states and
the finite target state carrier at their respective vertices. -/
noncomputable def protocolFiniteQuerySet
    [Fintype (ProtocolObservedFiniteDetermination.InputPoint P)] :
    Finset (HomQuery (Parameter.protocol protocolInput : Parameter.{u, u})) := by
  classical
  exact Finset.univ.biUnion (fun point :
      ProtocolObservedFiniteDetermination.InputPoint P =>
    letI : Fintype (Q.State point.1) := Fintype.ofFinite _
    Finset.univ.image (fun output : Q.State point.1 =>
      protocolPointQuery protocolInput (ULiftHom.objUp P) (ULiftHom.objUp Q)
        point.1 point.2 output))

/-- Agreement on the selected finite common protocol graph cells separates
all actual observation-preserving protocol morphisms. -/
theorem protocol_finite_query_separates
    [Fintype (ProtocolObservedFiniteDetermination.InputPoint P)]
    (f g : P ⟶ Q)
    (agree : ∀ query ∈ protocolFiniteQuerySet protocolInput P Q,
      localHomTable (.protocol protocolInput)
          ((reading (.protocol protocolInput)).map (ULift.up f)) query =
        localHomTable (.protocol protocolInput)
          ((reading (.protocol protocolInput)).map (ULift.up g)) query) :
    f = g := by
  apply ProtocolObservedFiniteDetermination.fullInput_separates P Q
  funext point
  let vertex := point.1.1
  let state := point.1.2
  let output := (ProtocolObservedFiniteDetermination.readProtocolHomAt P Q f
    ⟨vertex, state⟩).2
  have hmem : protocolPointQuery protocolInput (ULiftHom.objUp P)
      (ULiftHom.objUp Q) vertex state output ∈
      protocolFiniteQuerySet protocolInput P Q := by
    classical
    unfold protocolFiniteQuerySet
    apply Finset.mem_biUnion.mpr
    refine ⟨⟨vertex,state⟩, Finset.mem_univ _, ?_⟩
    letI : Fintype (Q.State vertex) := Fintype.ofFinite _
    apply Finset.mem_image.mpr
    exact ⟨output, Finset.mem_univ _, rfl⟩
  have hf : decodeProtocolPoint protocolInput (ULiftHom.objUp P)
        (ULiftHom.objUp Q) vertex state output
        (localHomTable (.protocol protocolInput)
          ((reading (.protocol protocolInput)).map (ULift.up f))) = true :=
    (protocol_value_iff_primitive_point protocolInput P Q f vertex state output).mp rfl
  have hg : decodeProtocolPoint protocolInput (ULiftHom.objUp P)
        (ULiftHom.objUp Q) vertex state output
        (localHomTable (.protocol protocolInput)
          ((reading (.protocol protocolInput)).map (ULift.up g))) = true := by
    rw [← hf]
    exact (agree _ hmem).symm
  have hpoint := (protocol_value_iff_primitive_point protocolInput P Q g
    vertex state output).mpr hg
  -- The output tag is fixed by the source vertex in both readings.
  exact hpoint.symm


/-- The accepted total lens extension has exactly the supplied value at
every corresponding common primitive query. -/
theorem lens_assembled_table_primitive_point [Fintype X.Fiber]
    (table : LensSemanticFiniteDetermination.RawTable X Y)
    (state : X.Fiber) (output : Y.Fiber) :
    decodeLensPoint input (ULiftHom.objUp X) (ULiftHom.objUp Y)
        state.1 output.1
        (localHomTable (.lens input)
          ((reading (.lens input)).map
            (ULift.up (LensSemanticFiniteDetermination.assembleTable X Y table)))) = true ↔
      table ⟨state, Finset.mem_univ _⟩ = output := by
  rw [← lens_value_iff_primitive_point]
  have h := congrFun (LensSemanticFiniteDetermination.restrict_assembleTable X Y table)
    ⟨state, Finset.mem_univ _⟩
  simpa [FiniteReading.restrict] using h ▸ Iff.rfl

/-- The accepted coherent protocol extension has exactly the supplied tagged
value at the common primitive vertex query. -/
theorem protocol_assembled_table_primitive_point
    [Fintype (ProtocolObservedFiniteDetermination.InputPoint P)]
    [DecidableEq protocolInput.schema.Vertex]
    (table : ProtocolObservedFiniteDetermination.RawTable P Q)
    (coherent : ProtocolObservedFiniteDetermination.TableCoherent P Q table)
    (vertex : protocolInput.schema.Vertex) (state : P.State vertex)
    (output : Q.State vertex) :
    decodeProtocolPoint protocolInput (ULiftHom.objUp P) (ULiftHom.objUp Q)
        vertex state output
        (localHomTable (.protocol protocolInput)
          ((reading (.protocol protocolInput)).map
            (ULift.up (ProtocolObservedFiniteDetermination.assembleTable P Q table coherent)))) = true ↔
      table ⟨⟨vertex,state⟩, Finset.mem_univ _⟩ = ⟨vertex,output⟩ := by
  rw [← protocol_value_iff_primitive_point]
  have h := congrFun
    (ProtocolObservedFiniteDetermination.restrict_assembleTable P Q table coherent)
    ⟨⟨vertex,state⟩, Finset.mem_univ _⟩
  simpa [FiniteReading.restrict] using h ▸ Iff.rfl


#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.CSFiniteValueQueryBridge

end CSFiniteValueQueryBridge
end AAT.AG.LocalSemanticReconstruction
