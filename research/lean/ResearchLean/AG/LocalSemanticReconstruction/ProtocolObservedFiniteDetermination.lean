import ResearchLean.AG.LocalSemanticReconstruction.FiniteEffectiveness
import ResearchLean.AG.LocalSemanticReconstruction.ProtocolObservedRestrictionModel
import ResearchLean.AG.RealizationReconstruction.ProtocolReconstruction
import Formal.Util.AssertStandardAxioms

/-!
# Finite determination of observation-preserving protocol morphisms

For fixed actual protocol realizations `X` and `Y`, a morphism is read on the
finite family of all pairs `(vertex, source state)`.  Because the target state
type depends on the vertex, the common `FiniteReading` value is a tagged
dependent sum `(vertex, target state)`.  Coherence decodes matching tags into
typed components and asks only for successful decoding, named-edge squares,
and observation equations; it does not accept a completed component family as
a certificate.

The existing generator reconstruction extends those local equations to every
quotient execution.  Thus the full finite table separately satisfies
separation, extension, and effectiveness for the actual noninvertible
observation-preserving Hom.  The effectiveness boundary takes explicit
finite enumerations and equality decisions; it does not infer executability
from the semantic `Finite` premises or require observation carriers to be
finite.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory
open AAT.AG.RealizationReconstruction

universe u v

namespace ProtocolObservedFiniteDetermination

variable {S : ProtocolSchema.{u}} {O : S.ExecutionCategory ⥤ Type u}
  (X Y : ProtocolRealization S O)

/-- A finite-reading input is a named control vertex together with one actual
source state at that vertex. -/
abbrev InputPoint := Σ vertex : S.Vertex, X.State vertex

/-- A uniform reading value retains the target vertex tag together with the
corresponding actual target state. -/
abbrev OutputValue := Σ vertex : S.Vertex, Y.State vertex

/-- Observation equality is requested only on the tagged values that occur at
named vertices; their carriers need not be finite. -/
abbrev ObservationValue :=
  Σ vertex : S.Vertex, O.obj (S.vertexObject vertex)

/-- Read an actual observation-preserving protocol morphism at one tagged
source state. -/
def readProtocolHomAt (f : X ⟶ Y) (point : InputPoint X) : OutputValue Y :=
  ⟨point.1,
    ProtocolRealization.app f (S.vertexObject point.1) point.2⟩

/-- The explicit finite reading set contains every vertex/state input pair. -/
def fullInput [Fintype (InputPoint X)] : Finset (InputPoint X) :=
  Finset.univ

/-- A raw full table on the common finite-reading surface. -/
abbrev RawTable [Fintype (InputPoint X)] :=
  {point // point ∈ fullInput X} → OutputValue Y

/-- Decode one tagged raw output at its expected vertex.  A mismatched tag is
rejected as `none`; a matching tag transports the state along the witnessed
vertex equality. -/
def decodedAt [Fintype (InputPoint X)] [DecidableEq S.Vertex]
    (table : RawTable X Y) (vertex : S.Vertex) (state : X.State vertex) :
    Option (Y.State vertex) :=
  let output := table ⟨⟨vertex, state⟩, Finset.mem_univ _⟩
  if tagEquality : output.1 = vertex then
    some (cast (congrArg (fun namedVertex => Y.State namedVertex) tagEquality)
      output.2)
  else
    none

/-- G-124(D/E2) local coherence for a general protocol Hom.  It asks that
every tagged output decode, that decoded components commute with every named
edge, and that they preserve observation.  No completed Hom, component-family
certificate, or extension witness is stored. -/
def TableCoherent [Fintype (InputPoint X)] [DecidableEq S.Vertex]
    (table : RawTable X Y) : Prop :=
  (∀ (vertex : S.Vertex) (state : X.State vertex),
    (decodedAt X Y table vertex state).isSome) ∧
  (∀ {source target : S.Vertex} (edge : S.Edge source target)
    (state : X.State source),
    Option.map (Y.edgeAction edge) (decodedAt X Y table source state) =
      decodedAt X Y table target (X.edgeAction edge state)) ∧
  (∀ (vertex : S.Vertex) (state : X.State vertex),
    Option.map (fun targetState =>
        (⟨vertex, Y.observe vertex targetState⟩ :
          ObservationValue (S := S) (O := O)))
        (decodedAt X Y table vertex state) =
      some ⟨vertex, X.observe vertex state⟩)

/-- Successful decoding returns exactly the original tagged raw entry. -/
theorem table_eq_tagged_get [Fintype (InputPoint X)] [DecidableEq S.Vertex]
    (table : RawTable X Y) (vertex : S.Vertex) (state : X.State vertex)
    (success : (decodedAt X Y table vertex state).isSome) :
    table ⟨⟨vertex, state⟩, Finset.mem_univ _⟩ =
      ⟨vertex, (decodedAt X Y table vertex state).get success⟩ := by
  let output := table ⟨⟨vertex, state⟩, Finset.mem_univ _⟩
  change output = ⟨vertex, (decodedAt X Y table vertex state).get success⟩
  by_cases tagEquality : output.1 = vertex
  · have decodedEquality :
        decodedAt X Y table vertex state =
          some (cast
            (congrArg (fun namedVertex => Y.State namedVertex) tagEquality)
            output.2) := by
      simp [decodedAt, output, tagEquality]
    have stateEquality :
        (decodedAt X Y table vertex state).get success =
          cast (congrArg (fun namedVertex => Y.State namedVertex) tagEquality)
            output.2 :=
      Option.some.inj ((Option.some_get success).trans decodedEquality)
    calc
      output = ⟨vertex,
          cast (congrArg (fun namedVertex => Y.State namedVertex) tagEquality)
            output.2⟩ := by
        exact Sigma.ext tagEquality (cast_heq _ _).symm
      _ = ⟨vertex, (decodedAt X Y table vertex state).get success⟩ := by
        rw [stateEquality]
  · have impossible : ¬ (decodedAt X Y table vertex state).isSome := by
      simp [decodedAt, output, tagEquality]
    exact (impossible success).elim

/-- The full table read from every actual protocol Hom satisfies the
independent local coherence predicate. -/
theorem read_table_coherent [Fintype (InputPoint X)] [DecidableEq S.Vertex]
    (f : X ⟶ Y) :
    TableCoherent X Y
      (FiniteReading.restrict (readProtocolHomAt X Y) (fullInput X) f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro vertex state
    simp [decodedAt, FiniteReading.restrict, readProtocolHomAt]
  · intro source target edge state
    simpa [decodedAt, FiniteReading.restrict, readProtocolHomAt] using
      congrFun (ProtocolRealization.edge_naturality f edge) state |>.symm
  · intro vertex state
    simpa [decodedAt, FiniteReading.restrict, readProtocolHomAt] using
      congrArg (fun observed =>
        (⟨vertex, observed⟩ : ObservationValue (S := S) (O := O)))
        (congrFun (ProtocolRealization.observation_app f vertex) state)

/-- A raw table that changes a vertex tag is not coherent.  This supplies the
negative instance for the new predicate without adding a global object or an
extension witness. -/
theorem not_tableCoherent_of_tag_mismatch [Fintype (InputPoint X)]
    [DecidableEq S.Vertex]
    (table : RawTable X Y) (vertex : S.Vertex) (state : X.State vertex)
    (mismatch : (table ⟨⟨vertex, state⟩, Finset.mem_univ _⟩).1 ≠ vertex) :
    ¬ TableCoherent X Y table := by
  intro coherent
  have decoded := coherent.1 vertex state
  simp [decodedAt, mismatch] at decoded

/-- The full finite point table separates all actual observation-preserving
protocol morphisms. -/
theorem fullInput_separates [Fintype (InputPoint X)] :
    FiniteReading.Separates (readProtocolHomAt X Y) (fullInput X) := by
  intro first second tableEquality
  apply (ProtocolRealization.homEquivGeneratorMap X Y).injective
  apply ProtocolRealization.GeneratorMap.ext
  funext vertex state
  have pointEquality := congrFun tableEquality
    ⟨⟨vertex, state⟩, Finset.mem_univ _⟩
  exact sigma_mk_injective pointEquality

/-- Turn a coherent full raw table into the actual protocol Hom obtained by
the accepted generator-map extension. -/
def assembleTable [Fintype (InputPoint X)] [DecidableEq S.Vertex]
    (table : RawTable X Y) (coherent : TableCoherent X Y table) : X ⟶ Y :=
  ProtocolRealization.ext
    { component := fun vertex state =>
        (decodedAt X Y table vertex state).get (coherent.1 vertex state)
      edge_naturality := by
        intro source target edge
        funext state
        have edgeEquality := coherent.2.1 edge state
        have taggedEquality :
            some (Y.edgeAction edge
              ((decodedAt X Y table source state).get
                (coherent.1 source state))) =
              some ((decodedAt X Y table target
                (X.edgeAction edge state)).get
                  (coherent.1 target (X.edgeAction edge state))) := by
          calc
            _ = Option.map (Y.edgeAction edge)
                (decodedAt X Y table source state) := by
              change Option.map (Y.edgeAction edge)
                  (some ((decodedAt X Y table source state).get
                    (coherent.1 source state))) =
                Option.map (Y.edgeAction edge)
                  (decodedAt X Y table source state)
              exact congrArg (Option.map (Y.edgeAction edge))
                (Option.some_get (coherent.1 source state))
            _ = decodedAt X Y table target (X.edgeAction edge state) :=
              edgeEquality
            _ = _ := (Option.some_get
              (coherent.1 target (X.edgeAction edge state))).symm
        exact (Option.some.inj taggedEquality).symm
      observation_naturality := by
        intro vertex
        funext state
        have observedEquality := coherent.2.2 vertex state
        have taggedEquality :
            (⟨vertex,
              Y.observe vertex
                ((decodedAt X Y table vertex state).get
                  (coherent.1 vertex state))⟩ :
              ObservationValue (S := S) (O := O)) =
              ⟨vertex, X.observe vertex state⟩ := by
          apply Option.some.inj
          calc
            _ = Option.map (fun targetState =>
                (⟨vertex, Y.observe vertex targetState⟩ :
                  ObservationValue (S := S) (O := O)))
                (decodedAt X Y table vertex state) := by
              change Option.map (fun targetState =>
                    (⟨vertex, Y.observe vertex targetState⟩ :
                      ObservationValue (S := S) (O := O)))
                  (some ((decodedAt X Y table vertex state).get
                    (coherent.1 vertex state))) =
                Option.map (fun targetState =>
                    (⟨vertex, Y.observe vertex targetState⟩ :
                      ObservationValue (S := S) (O := O)))
                  (decodedAt X Y table vertex state)
              exact congrArg
                (Option.map (fun targetState =>
                  (⟨vertex, Y.observe vertex targetState⟩ :
                    ObservationValue (S := S) (O := O))))
                (Option.some_get (coherent.1 vertex state))
            _ = _ := observedEquality
        exact @sigma_mk_injective S.Vertex
          (fun namedVertex => O.obj (S.vertexObject namedVertex))
          vertex _ _ taggedEquality }

/-- Reading the assembled actual Hom recovers every entry of the coherent raw
table exactly. -/
@[simp] theorem restrict_assembleTable [Fintype (InputPoint X)]
    [DecidableEq S.Vertex]
    (table : RawTable X Y) (coherent : TableCoherent X Y table) :
    FiniteReading.restrict (readProtocolHomAt X Y) (fullInput X)
        (assembleTable X Y table coherent) = table := by
  funext point
  rcases point with ⟨⟨vertex, state⟩, membership⟩
  simpa [FiniteReading.restrict, readProtocolHomAt, assembleTable] using
    (table_eq_tagged_get X Y table vertex state
      (coherent.1 vertex state)).symm

/-- Every independently coherent full table extends to an actual general
protocol Hom. -/
theorem fullInput_extends [Fintype (InputPoint X)] [DecidableEq S.Vertex] :
    FiniteReading.Extends (readProtocolHomAt X Y) (fullInput X)
      (TableCoherent X Y) := by
  intro table coherent
  exact ⟨assembleTable X Y table coherent,
    restrict_assembleTable X Y table coherent⟩

/-- The full vertex/state table is a determining set for the actual general
observation-preserving protocol Hom. -/
theorem fullInput_determining [Fintype (InputPoint X)] [DecidableEq S.Vertex] :
    FiniteReading.Determining (readProtocolHomAt X Y) (fullInput X)
      (TableCoherent X Y) :=
  ⟨fullInput_separates X Y, fullInput_extends X Y⟩

section Effectiveness

variable [Fintype S.Vertex] [DecidableEq S.Vertex]
  [∀ vertex, Fintype (X.State vertex)]
  [∀ vertex, DecidableEq (Y.State vertex)]
  [∀ source target, Fintype (S.Edge source target)]
  [DecidableEq (ObservationValue (S := S) (O := O))]

/-- Under explicit finite enumerations and equality decisions, the raw local
coherence predicate is decidable without requiring finite observation
carriers. -/
instance tableCoherentDecidable (table : RawTable X Y) :
    Decidable (TableCoherent X Y table) := by
  unfold TableCoherent
  infer_instance

/-- Executable extension of general protocol Hom tables: decide the local
generator and observation equations, reject exactly incoherent input, and
return the actual quotient-execution Hom with exact readback. -/
def effectivenessProgram :
    FiniteReading.EffectivenessProgram
      (readProtocolHomAt X Y) (fullInput X) (TableCoherent X Y) where
  coherenceTest table := decide (TableCoherent X Y table)
  coherenceTest_eq_true_iff table := by simp
  extend? table :=
    if coherent : TableCoherent X Y table then
      some (assembleTable X Y table coherent)
    else
      none
  extend_eq_none_iff table := by
    split_ifs with coherent
    · simp [coherent]
    · simp [coherent]
  restrict_eq_of_extend_eq_some table global success := by
    split_ifs at success with coherent
    · cases success
      exact restrict_assembleTable X Y table coherent

/-- The explicit program supplies effectiveness independently of separation
and extension. -/
theorem fullInput_effective :
    FiniteReading.Effective
      (readProtocolHomAt X Y) (fullInput X) (TableCoherent X Y) :=
  ⟨effectivenessProgram X Y⟩

end Effectiveness

/-- The finite point reading is exactly the state component of the Cycle 22
observation-aware local Hom reading. -/
@[simp] theorem readProtocolHomAt_eq_observedRestrictionMap
    (input : ProtocolFamilyInput.{u})
    {source target : ProtocolRealization input.schema input.observation}
    (f : source ⟶ target)
    (point : InputPoint source) :
    readProtocolHomAt source target f point =
      ⟨point.1,
        (protocolObservedRestrictionMap input
          (closedFamilyProtocolHom f)).stateMap.app
          (Opposite.op (Opposite.op
            (input.schema.vertexObject point.1))) point.2⟩ := by
  rfl

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.ProtocolObservedFiniteDetermination

end ProtocolObservedFiniteDetermination

end AAT.AG.LocalSemanticReconstruction
