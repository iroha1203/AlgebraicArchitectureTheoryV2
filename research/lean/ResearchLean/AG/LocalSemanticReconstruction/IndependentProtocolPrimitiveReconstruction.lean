import ResearchLean.AG.LocalSemanticReconstruction.IndependentCarrierGraphReadings
import ResearchLean.AG.LocalSemanticReconstruction.IndependentFiniteFragments
import ResearchLean.AG.LocalSemanticReconstruction.IndependentFiniteGraphLawFormula
import ResearchLean.AG.LocalSemanticReconstruction.IndependentFiniteLawFormula
import ResearchLean.AG.LocalSemanticReconstruction.LocalReconstructionEquivalence
import ResearchLean.AG.LocalSemanticReconstruction.ProtocolObservedRestrictionModel
import ResearchLean.AG.RealizationReconstruction.CSAATLawSystems
import ResearchLean.AG.RealizationReconstruction.ProtocolFinitePresentation
import ResearchLean.AG.RealizationReconstruction.ProtocolReconstruction
import Formal.Util.AssertStandardAxioms

/-!
# Primitive reconstruction of finite-state protocols

For a fixed protocol input, this module declares one carrier cell at each
schema vertex, one candidate graph for every named edge, and one candidate
graph for every vertex observation.  Relation formulas recurse over the
existing `Quiver.Path` values.  Observation formulas use only named-edge and
observation graph cells.

The local object stores compatible finite fragments, closed graph-row
instances, pointwise relation and observation formulas, and list covers of
the selected state carriers.  The local Hom stores vertex-map graph fragments
and the finite named-edge and observation preservation formulas.  Completed
protocol realizations and completed semantic Homs occur only in reading and
assembly functions.

## Implementation notes

The construction reuses `Quiver.Path`, `ProtocolSchema.pathFunctorOfEdgeAction`,
`ProtocolRealization.ext`, the independent carrier-graph reader, and the general
reconstruction equivalence.  This keeps the primitive data to carrier and graph
cells while deriving carrier comparisons and all path equations from those cells.
A second path language and fields containing completed realizations were rejected:
the former would duplicate the accepted schema API, while the latter would place
the result being reconstructed inside the local data.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory
open AAT.AG.RealizationReconstruction
open LocalReconstructionEquivalence

noncomputable section

namespace IndependentProtocolPrimitiveReconstruction

universe u

/-- Candidate carrier graph queries specialized to the protocol universe. -/
abbrev GraphQuery := IndependentCarrierGraph.Query.{u, u}

/-- Boolean candidate carrier graph tables specialized to the protocol universe. -/
abbrev GraphTable := IndependentCarrierGraph.Table.{u, u}

/-- Primitive protocol object queries fixed before any state carrier is selected. -/
inductive ObjectQuery (input : ProtocolFamilyInput.{u}) where
  /-- The state-carrier declaration at one schema vertex. -/
  | stateCarrier (vertex : input.schema.Vertex)
  /-- One candidate graph cell for a named schema edge. -/
  | edge {source target : input.schema.Vertex}
      (edge : input.schema.Edge source target) (query : GraphQuery.{u})
  /-- One candidate graph cell for the observation at a schema vertex. -/
  | observe (vertex : input.schema.Vertex) (query : GraphQuery.{u})

/-- The dependent value type of each primitive protocol object query. -/
def ObjectValue {input : ProtocolFamilyInput.{u}} : ObjectQuery input → Type (u + 1)
  | .stateCarrier _ => Type u
  | .edge _ _ => ULift.{u + 1, 0} Bool
  | .observe _ _ => ULift.{u + 1, 0} Bool

/-- A dependent primitive protocol object table. -/
abbrev ObjectTable (input : ProtocolFamilyInput.{u}) :=
  (query : ObjectQuery input) → ObjectValue query

/-- Finite fragments of a primitive protocol object table. -/
abbrev ObjectFragment {input : ProtocolFamilyInput.{u}}
    (D : Finset (ObjectQuery input)) :=
  IndependentFiniteFragments.Fragment
    (fun query : ObjectQuery input => ObjectValue query) D

/-- A family of finite protocol object fragments. -/
abbrev ObjectFragmentFamily (input : ProtocolFamilyInput.{u}) :=
  IndependentFiniteFragments.FragmentFamily
    (fun query : ObjectQuery input => ObjectValue query)

/-- Compatibility of finite protocol object fragments. -/
abbrev ObjectCompatible {input : ProtocolFamilyInput.{u}}
    (family : ObjectFragmentFamily input) :=
  IndependentFiniteFragments.Compatible family

/-- Restrict a protocol object table to every finite query set. -/
def objectFragments {input : ProtocolFamilyInput.{u}} (table : ObjectTable input) :
    ObjectFragmentFamily input :=
  IndependentFiniteFragments.fragments table

/-- Glue compatible protocol object fragments through singleton cells. -/
def objectGlue {input : ProtocolFamilyInput.{u}} (family : ObjectFragmentFamily input) :
    ObjectTable input :=
  IndependentFiniteFragments.glue family

/-- Restrictions of a protocol object table are compatible. -/
theorem objectFragments_compatible {input : ProtocolFamilyInput.{u}}
    (table : ObjectTable input) : ObjectCompatible (objectFragments table) :=
  IndependentFiniteFragments.fragments_compatible table

/-- Gluing all restrictions recovers a protocol object table. -/
theorem objectGlue_fragments {input : ProtocolFamilyInput.{u}}
    (table : ObjectTable input) : objectGlue (objectFragments table) = table :=
  IndependentFiniteFragments.glue_fragments table

/-- Compatible protocol object fragments are recovered from their glued table. -/
theorem objectFragments_glue {input : ProtocolFamilyInput.{u}}
    (family : ObjectFragmentFamily input) (compatible : ObjectCompatible family) :
    objectFragments (objectGlue family) = family :=
  IndependentFiniteFragments.fragments_glue family compatible

/-- The state family selected by the primitive carrier cells. -/
def State {input : ProtocolFamilyInput.{u}} (table : ObjectTable input)
    (vertex : input.schema.Vertex) : Type u :=
  table (.stateCarrier vertex)

/-- Restrict an object table to one named-edge graph. -/
def edgeTable {input : ProtocolFamilyInput.{u}} (table : ObjectTable input)
    {source target : input.schema.Vertex}
    (edge : input.schema.Edge source target) : GraphTable.{u} :=
  fun query => (table (.edge edge query)).down

/-- Restrict an object table to one vertex-observation graph. -/
def observeTable {input : ProtocolFamilyInput.{u}} (table : ObjectTable input)
    (vertex : input.schema.Vertex) : GraphTable.{u} :=
  fun query => (table (.observe vertex query)).down

/-- Boolean law queries computed from the dependent primitive object table. -/
inductive ObjectLawQuery (input : ProtocolFamilyInput.{u}) where
  /-- Compare a candidate type with one declared vertex carrier. -/
  | carrierMatches (vertex : input.schema.Vertex) (candidate : Type u)
  /-- Read one named-edge graph cell. -/
  | edge {source target : input.schema.Vertex}
      (edge : input.schema.Edge source target) (query : GraphQuery.{u})
  /-- Read one vertex-observation graph cell. -/
  | observe (vertex : input.schema.Vertex) (query : GraphQuery.{u})

/-- Boolean table used only to evaluate derived protocol object formulas. -/
abbrev ObjectLawTable (input : ProtocolFamilyInput.{u}) := ObjectLawQuery input → Bool

/-- Derive law cells from the primitive carrier and graph cells. -/
def objectLawTable {input : ProtocolFamilyInput.{u}} (table : ObjectTable input) :
    ObjectLawTable input := by
  classical
  intro query
  cases query with
  | carrierMatches vertex candidate =>
      exact decide (candidate = table (.stateCarrier vertex))
  | edge edge query => exact (table (.edge edge query)).down
  | observe vertex query => exact (table (.observe vertex query)).down

/-- The selected carrier-reference cell as a closed Boolean formula. -/
def carrierFormula (input : ProtocolFamilyInput.{u})
    (vertex : input.schema.Vertex) (C : Type u) :
    IndependentFiniteLawFormula.BoolFormula.{u + 1, 0} (ObjectLawQuery input) :=
  .cell (.carrierMatches vertex C) true

/-- A derived carrier match is true exactly for the declared vertex carrier. -/
theorem objectLawTable_carrierMatches_iff {input : ProtocolFamilyInput.{u}}
    (table : ObjectTable input) (vertex : input.schema.Vertex) (C : Type u) :
    objectLawTable table (.carrierMatches vertex C) = true ↔ C = State table vertex := by
  classical
  simp [objectLawTable, State]

/-- Map each derived protocol law query to its determining primitive cell. -/
def objectLawQueryBase (input : ProtocolFamilyInput.{u}) :
    ObjectLawQuery input → ObjectQuery input
  | .carrierMatches vertex _ => .stateCarrier vertex
  | .edge edge query => .edge edge query
  | .observe vertex query => .observe vertex query

/-- Primitive cells needed by one finite protocol object formula. -/
def objectFormulaBaseSupport (input : ProtocolFamilyInput.{u})
    (formula : IndependentFiniteLawFormula.BoolFormula.{u + 1, 0}
      (ObjectLawQuery input)) : Finset (ObjectQuery input) := by
  classical
  exact formula.support.image (objectLawQueryBase input)

/-- Agreement on primitive support preserves a derived protocol formula. -/
theorem objectFormula_evaluate_iff_of_base_support
    (input : ProtocolFamilyInput.{u})
    (formula : IndependentFiniteLawFormula.BoolFormula.{u + 1, 0}
      (ObjectLawQuery input))
    (first second : ObjectTable input)
    (agree : ∀ query ∈ objectFormulaBaseSupport input formula,
      first query = second query) :
    formula.evaluate (objectLawTable first) ↔
      formula.evaluate (objectLawTable second) := by
  classical
  apply IndependentFiniteLawFormula.BoolFormula.evaluate_iff_of_support
  intro query member
  have baseMember : objectLawQueryBase input query ∈
      objectFormulaBaseSupport input formula := by
    classical
    exact Finset.mem_image.mpr ⟨query, member, rfl⟩
  cases query with
  | carrierMatches vertex candidate =>
      change decide (candidate = first (.stateCarrier vertex)) =
        decide (candidate = second (.stateCarrier vertex))
      exact congrArg (fun carrier => decide (candidate = carrier))
        (agree (.stateCarrier vertex) baseMember)
  | edge edge graphQuery =>
      exact congrArg ULift.down (agree (.edge edge graphQuery) baseMember)
  | observe vertex graphQuery =>
      exact congrArg ULift.down (agree (.observe vertex graphQuery) baseMember)

/-- Assemble all named-edge actions from lawful primitive graphs. -/
def assembleEdgeAction {input : ProtocolFamilyInput.{u}}
    (table : ObjectTable input)
    (lawful : ∀ {source target} (edge : input.schema.Edge source target),
      IndependentCarrierGraph.IsLawful (State table source) (State table target)
        (edgeTable table edge))
    {source target : input.schema.Vertex}
    (edge : input.schema.Edge source target) : State table source → State table target :=
  IndependentCarrierGraph.assemble _ _ (edgeTable table edge) (lawful edge)

/-- Assemble the observation at one vertex from its lawful primitive graph. -/
def assembleObserve {input : ProtocolFamilyInput.{u}}
    (table : ObjectTable input)
    (lawful : ∀ vertex,
      IndependentCarrierGraph.IsLawful (State table vertex)
        (input.observation.obj (input.schema.vertexObject vertex))
        (observeTable table vertex))
    (vertex : input.schema.Vertex) :
    State table vertex → input.observation.obj (input.schema.vertexObject vertex) :=
  IndependentCarrierGraph.assemble _ _ (observeTable table vertex) (lawful vertex)

/-- Finite conjunction of the actual graph cells traversed by an existing path. -/
def pathTraceFormula (input : ProtocolFamilyInput.{u})
    (table : ObjectTable input)
    (edgeLawful : ∀ {source target} (edge : input.schema.Edge source target),
      IndependentCarrierGraph.IsLawful (State table source) (State table target)
        (edgeTable table edge))
    {source target : input.schema.Vertex}
    (path : Quiver.Path source target) (state : State table source) :
    IndependentFiniteLawFormula.BoolFormula.{u + 1, 0} (ObjectLawQuery input) :=
  match path with
  | .nil => carrierFormula input source (State table source)
  | .cons pathHead edge =>
      .and (pathTraceFormula input table edgeLawful pathHead state)
        (.and (carrierFormula input target (State table target))
          (.cell (.edge edge (.edge _ _
            (input.schema.evaluatePath (assembleEdgeAction table edgeLawful) pathHead state)
            (assembleEdgeAction table edgeLawful edge
              (input.schema.evaluatePath (assembleEdgeAction table edgeLawful) pathHead state)))) true))

/-- Finite path formula whose last graph cell is required to end at a supplied state. -/
def pathToFormula (input : ProtocolFamilyInput.{u})
    (table : ObjectTable input)
    (edgeLawful : ∀ {source target} (edge : input.schema.Edge source target),
      IndependentCarrierGraph.IsLawful (State table source) (State table target)
        (edgeTable table edge))
    {source target : input.schema.Vertex}
    (path : Quiver.Path source target) (state : State table source)
    (endpoint : State table target) :
    IndependentFiniteLawFormula.BoolFormula.{u + 1, 0} (ObjectLawQuery input) := by
  classical
  cases path with
  | nil => exact (.and (carrierFormula input source (State table source))
      (if state = endpoint then .truth else .falsity))
  | cons pathHead edge =>
      exact .and (pathTraceFormula input table edgeLawful pathHead state)
        (.and (carrierFormula input target (State table target))
          (.cell (.edge edge (.edge _ _
            (input.schema.evaluatePath (assembleEdgeAction table edgeLawful) pathHead state)
            endpoint)) true))

/-- The relation instance uses both existing schema paths and their finite edge traces. -/
def relationFormula (input : ProtocolFamilyInput.{u})
    (table : ObjectTable input)
    (edgeLawful : ∀ {source target} (edge : input.schema.Edge source target),
      IndependentCarrierGraph.IsLawful (State table source) (State table target)
        (edgeTable table edge))
    (relation : input.schema.RelationIndex)
    (state : State table (input.schema.relationSource relation)) :
    IndependentFiniteLawFormula.BoolFormula.{u + 1, 0} (ObjectLawQuery input) :=
  .and
    (carrierFormula input (input.schema.relationSource relation)
      (State table (input.schema.relationSource relation)))
    (.and
      (pathTraceFormula input table edgeLawful
        (input.schema.relationLeft relation) state)
      (pathToFormula input table edgeLawful
        (input.schema.relationRight relation) state
        (input.schema.evaluatePath (assembleEdgeAction table edgeLawful)
          (input.schema.relationLeft relation) state)))

/-- One finite formula for the observation square of a named edge at one state. -/
def observationFormula (input : ProtocolFamilyInput.{u})
    (table : ObjectTable input)
    (edgeLawful : ∀ {source target} (edge : input.schema.Edge source target),
      IndependentCarrierGraph.IsLawful (State table source) (State table target)
        (edgeTable table edge))
    (observeLawful : ∀ vertex,
      IndependentCarrierGraph.IsLawful (State table vertex)
        (input.observation.obj (input.schema.vertexObject vertex))
        (observeTable table vertex))
    {source target : input.schema.Vertex}
    (edge : input.schema.Edge source target) (state : State table source) :
    IndependentFiniteLawFormula.BoolFormula.{u + 1, 0} (ObjectLawQuery input) :=
  let targetState := assembleEdgeAction table edgeLawful edge state
  let observed := assembleObserve table observeLawful source state
  .and (carrierFormula input source (State table source))
    (.and (carrierFormula input target (State table target))
      (.and
        (.cell (.edge edge (.edge _ _ state targetState)) true)
        (.and
          (.cell (.observe source (.edge _ _ state observed)) true)
          (.cell (.observe target (.edge _ _ targetState
            (input.observation.map (input.schema.edgeMorphism edge) observed))) true))))

/-- Every path-trace formula evaluates for a lawful family of edge graphs. -/
theorem pathTraceFormula_evaluate_raw {input : ProtocolFamilyInput.{u}}
    (table : ObjectTable input)
    (edgeLawful : ∀ {source target} (edge : input.schema.Edge source target),
      IndependentCarrierGraph.IsLawful (State table source) (State table target)
        (edgeTable table edge))
    {source target} (path : Quiver.Path source target) (state : State table source) :
    (pathTraceFormula input table edgeLawful path state).evaluate
      (objectLawTable table) := by
  induction path with
  | nil => exact (objectLawTable_carrierMatches_iff table _ _).mpr rfl
  | cons pathHead edge ih =>
      exact ⟨ih, (objectLawTable_carrierMatches_iff table _ _).mpr rfl,
        IndependentCarrierGraph.edge_assemble _ _ _ (edgeLawful edge) _⟩

/-- A raw path-to formula is equivalent to reaching its supplied endpoint. -/
theorem pathToFormula_evaluate_iff_raw {input : ProtocolFamilyInput.{u}}
    (table : ObjectTable input)
    (edgeLawful : ∀ {source target} (edge : input.schema.Edge source target),
      IndependentCarrierGraph.IsLawful (State table source) (State table target)
        (edgeTable table edge))
    {source target} (path : Quiver.Path source target) (state : State table source)
    (endpoint : State table target) :
    (pathToFormula input table edgeLawful path state endpoint).evaluate
        (objectLawTable table) ↔
      input.schema.evaluatePath (assembleEdgeAction table edgeLawful) path state = endpoint := by
  induction path with
  | nil =>
      classical
      have nilEvaluation :
          input.schema.evaluatePath (assembleEdgeAction table edgeLawful)
              (Quiver.Path.nil : Quiver.Path source source) state = state := by
        rfl
      by_cases h : state = endpoint
      · rw [nilEvaluation]
        simp [pathToFormula, carrierFormula,
          IndependentFiniteLawFormula.BoolFormula.evaluate,
          objectLawTable_carrierMatches_iff, h]
      · rw [nilEvaluation]
        simp [pathToFormula, carrierFormula,
          IndependentFiniteLawFormula.BoolFormula.evaluate,
          objectLawTable_carrierMatches_iff, h]
  | cons pathHead edge ih =>
      constructor
      · rintro ⟨_, _, edgeCell⟩
        change assembleEdgeAction table edgeLawful edge
            (input.schema.evaluatePath (assembleEdgeAction table edgeLawful) pathHead state) =
          endpoint
        exact IndependentCarrierGraph.assemble_eq_of_edge _ _ _
          (edgeLawful edge) edgeCell
      · intro equality
        refine ⟨pathTraceFormula_evaluate_raw table edgeLawful pathHead state,
          (objectLawTable_carrierMatches_iff table _ _).mpr rfl, ?_⟩
        rw [← equality]
        exact IndependentCarrierGraph.edge_assemble _ _ _ (edgeLawful edge) _

/-- A raw relation formula is equivalent to its pointwise path equation. -/
theorem relationFormula_evaluate_iff_raw {input : ProtocolFamilyInput.{u}}
    (table : ObjectTable input)
    (edgeLawful : ∀ {source target} (edge : input.schema.Edge source target),
      IndependentCarrierGraph.IsLawful (State table source) (State table target)
        (edgeTable table edge))
    (relation : input.schema.RelationIndex)
    (state : State table (input.schema.relationSource relation)) :
    (relationFormula input table edgeLawful relation state).evaluate
        (objectLawTable table) ↔
      input.schema.evaluatePath (assembleEdgeAction table edgeLawful)
          (input.schema.relationLeft relation) state =
        input.schema.evaluatePath (assembleEdgeAction table edgeLawful)
          (input.schema.relationRight relation) state := by
  constructor
  · rintro ⟨_, _, rightTrace⟩
    exact ((pathToFormula_evaluate_iff_raw table edgeLawful _ _ _).mp rightTrace).symm
  · intro equality
    refine ⟨(objectLawTable_carrierMatches_iff table _ _).mpr rfl,
      pathTraceFormula_evaluate_raw table edgeLawful _ state, ?_⟩
    exact (pathToFormula_evaluate_iff_raw table edgeLawful _ _ _).mpr equality.symm

/-- A raw observation formula is equivalent to its named-edge square. -/
theorem observationFormula_evaluate_iff_raw {input : ProtocolFamilyInput.{u}}
    (table : ObjectTable input)
    (edgeLawful : ∀ {source target} (edge : input.schema.Edge source target),
      IndependentCarrierGraph.IsLawful (State table source) (State table target)
        (edgeTable table edge))
    (observeLawful : ∀ vertex,
      IndependentCarrierGraph.IsLawful (State table vertex)
        (input.observation.obj (input.schema.vertexObject vertex))
        (observeTable table vertex))
    {source target} (edge : input.schema.Edge source target)
    (state : State table source) :
    (observationFormula input table edgeLawful observeLawful edge state).evaluate
        (objectLawTable table) ↔
      input.observation.map (input.schema.edgeMorphism edge)
          (assembleObserve table observeLawful source state) =
        assembleObserve table observeLawful target
          (assembleEdgeAction table edgeLawful edge state) := by
  constructor
  · rintro ⟨_, _, _, _, targetObservation⟩
    exact (IndependentCarrierGraph.assemble_eq_of_edge _ _ _
      (observeLawful target) targetObservation).symm
  · intro equality
    refine ⟨(objectLawTable_carrierMatches_iff table _ _).mpr rfl,
      (objectLawTable_carrierMatches_iff table _ _).mpr rfl,
      IndependentCarrierGraph.edge_assemble _ _ _ (edgeLawful edge) state,
      IndependentCarrierGraph.edge_assemble _ _ _ (observeLawful source) state, ?_⟩
    rw [equality]
    exact IndependentCarrierGraph.edge_assemble _ _ _
      (observeLawful target) (assembleEdgeAction table edgeLawful edge state)

/-- A finite list covers every state at one selected protocol vertex. -/
def StateCover {input : ProtocolFamilyInput.{u}} (table : ObjectTable input)
    (vertex : input.schema.Vertex) : Prop :=
  ∃ states : List (State table vertex), ∀ state, state ∈ states

/-- A state list cover is equivalent to the existing finite-carrier condition. -/
theorem stateCover_iff_finite {input : ProtocolFamilyInput.{u}}
    (table : ObjectTable input) (vertex : input.schema.Vertex) :
    StateCover table vertex ↔ Finite (State table vertex) := by
  constructor
  · rintro ⟨states, cover⟩
    classical
    letI : Fintype (State table vertex) :=
      ⟨states.toFinset, fun state => by simpa using cover state⟩
    exact Finite.of_fintype _
  · intro finite
    letI : Finite (State table vertex) := finite
    letI := Fintype.ofFinite (State table vertex)
    exact ⟨Finset.univ.toList, fun state => by simp⟩

/-- A primitive protocol object containing only finite fragments and point laws. -/
structure Object (input : ProtocolFamilyInput.{u}) where
  /-- Finite fragments containing all primitive object cells. -/
  family : ObjectFragmentFamily input
  /-- The finite fragments agree under inclusions. -/
  compatible : ObjectCompatible family
  /-- Closed graph-row instances for each named edge. -/
  edge_instances : ∀ {source target} (edge : input.schema.Edge source target),
    IndependentFiniteGraphLawFormula.CarrierRows.Instances
      (fun query => (objectGlue family (.edge edge query)).down) id
      (State (objectGlue family) source) (State (objectGlue family) target)
  /-- Closed graph-row instances for each vertex observation. -/
  observe_instances : ∀ vertex,
    IndependentFiniteGraphLawFormula.CarrierRows.Instances
      (fun query => (objectGlue family (.observe vertex query)).down) id
      (State (objectGlue family) vertex)
      (input.observation.obj (input.schema.vertexObject vertex))
  /-- Every fixed schema relation formula evaluates from the primitive cells. -/
  relation_formula : ∀ relation state,
    (relationFormula input (objectGlue family)
      (fun edge =>
        (IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances
          (fun query => (objectGlue family (.edge edge query)).down) id _ _).mpr
          (edge_instances edge)) relation state).evaluate
      (objectLawTable (objectGlue family))
  /-- Every named-edge observation formula evaluates from the primitive cells. -/
  observation_formula : ∀ {source target}
      (edge : input.schema.Edge source target) state,
    (observationFormula input (objectGlue family)
      (fun edge =>
        (IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances
          (fun query => (objectGlue family (.edge edge query)).down) id _ _).mpr
          (edge_instances edge))
      (fun vertex =>
        (IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances
          (fun query => (objectGlue family (.observe vertex query)).down) id _ _).mpr
          (observe_instances vertex)) edge state).evaluate
      (objectLawTable (objectGlue family))
  /-- A finite list covers the selected state carrier at every vertex. -/
  state_cover : ∀ vertex, StateCover (objectGlue family) vertex

namespace Object

variable {input : ProtocolFamilyInput.{u}}

/-- Primitive protocol objects are equal when their fragment families agree. -/
@[ext]
theorem ext {first second : Object input} (family : first.family = second.family) :
    first = second := by
  cases first
  cases second
  cases family
  rfl

/-- Glue the primitive object table from its finite fragments. -/
def table (object : Object input) : ObjectTable input := objectGlue object.family

/-- State carrier selected at one schema vertex. -/
def State (object : Object input) (vertex : input.schema.Vertex) : Type u :=
  IndependentProtocolPrimitiveReconstruction.State object.table vertex

/-- Every selected named-edge graph is lawful. -/
theorem edge_lawful (object : Object input) {source target}
    (edge : input.schema.Edge source target) :
    IndependentCarrierGraph.IsLawful (object.State source) (object.State target)
      (edgeTable object.table edge) :=
  (IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances
    (edgeTable object.table edge) id _ _).mpr (object.edge_instances edge)

/-- Every selected vertex-observation graph is lawful. -/
theorem observe_lawful (object : Object input) (vertex : input.schema.Vertex) :
    IndependentCarrierGraph.IsLawful (object.State vertex)
      (input.observation.obj (input.schema.vertexObject vertex))
      (observeTable object.table vertex) :=
  (IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances
    (observeTable object.table vertex) id _ _).mpr
      (object.observe_instances vertex)

/-- Every selected state carrier is finite through its list cover. -/
theorem state_finite (object : Object input) (vertex : input.schema.Vertex) :
    Finite (object.State vertex) :=
  (stateCover_iff_finite object.table vertex).mp (object.state_cover vertex)

/-- The selected carrier-match cell evaluates to true. -/
theorem carrier_selected (object : Object input) (vertex : input.schema.Vertex) :
    objectLawTable object.table (.carrierMatches vertex (object.State vertex)) = true :=
  (objectLawTable_carrierMatches_iff object.table vertex _).mpr rfl

end Object

/-- Named-edge action assembled from a primitive protocol object. -/
def assembleEdge {input : ProtocolFamilyInput.{u}} (object : Object input)
    {source target} (edge : input.schema.Edge source target) :
    object.State source → object.State target :=
  IndependentCarrierGraph.assemble _ _ (edgeTable object.table edge)
    (object.edge_lawful edge)

/-- Vertex observation assembled from a primitive protocol object. -/
def assembleObservation {input : ProtocolFamilyInput.{u}} (object : Object input)
    (vertex : input.schema.Vertex) :
    object.State vertex → input.observation.obj (input.schema.vertexObject vertex) :=
  IndependentCarrierGraph.assemble _ _ (observeTable object.table vertex)
    (object.observe_lawful vertex)

/-- Primitive edge cells are exactly the graph of the assembled named edge. -/
theorem edge_edge_iff {input : ProtocolFamilyInput.{u}} (object : Object input)
    {source target} (edge : input.schema.Edge source target)
    (state : object.State source) (image : object.State target) :
    (object.table (.edge edge (.edge _ _ state image))).down = true ↔
      assembleEdge object edge state = image := by
  constructor
  · exact IndependentCarrierGraph.assemble_eq_of_edge _ _ _ (object.edge_lawful edge)
  · intro equality
    rw [← equality]
    exact IndependentCarrierGraph.edge_assemble _ _ _ (object.edge_lawful edge) state

/-- Primitive observation cells are exactly the graph of the assembled observation. -/
theorem observe_edge_iff {input : ProtocolFamilyInput.{u}} (object : Object input)
    (vertex : input.schema.Vertex) (state : object.State vertex)
    (value : input.observation.obj (input.schema.vertexObject vertex)) :
    (object.table (.observe vertex (.edge _ _ state value))).down = true ↔
      assembleObservation object vertex state = value := by
  constructor
  · exact IndependentCarrierGraph.assemble_eq_of_edge _ _ _ (object.observe_lawful vertex)
  · intro equality
    rw [← equality]
    exact IndependentCarrierGraph.edge_assemble _ _ _ (object.observe_lawful vertex) state

/-- Every actual finite path trace formula evaluates to true. -/
theorem pathTraceFormula_evaluate {input : ProtocolFamilyInput.{u}}
    (object : Object input) {source target}
    (path : Quiver.Path source target) (state : object.State source) :
    (pathTraceFormula input object.table (fun edge => object.edge_lawful edge)
      path state).evaluate (objectLawTable object.table) :=
  pathTraceFormula_evaluate_raw object.table
    (fun edge => object.edge_lawful edge) path state

/-- A path-to formula evaluates exactly when path evaluation reaches its endpoint. -/
theorem pathToFormula_evaluate_iff {input : ProtocolFamilyInput.{u}}
    (object : Object input) {source target}
    (path : Quiver.Path source target) (state : object.State source)
    (endpoint : object.State target) :
    (pathToFormula input object.table (fun edge => object.edge_lawful edge)
      path state endpoint).evaluate (objectLawTable object.table) ↔
      input.schema.evaluatePath (assembleEdge object) path state = endpoint :=
  pathToFormula_evaluate_iff_raw object.table
    (fun edge => object.edge_lawful edge) path state endpoint

/-- Relation formulas are equivalent to the native pointwise path equations. -/
theorem relationFormula_evaluate_iff {input : ProtocolFamilyInput.{u}}
    (object : Object input) (relation : input.schema.RelationIndex)
    (state : object.State (input.schema.relationSource relation)) :
    (relationFormula input object.table (fun edge => object.edge_lawful edge)
      relation state).evaluate (objectLawTable object.table) ↔
      input.schema.evaluatePath (assembleEdge object)
          (input.schema.relationLeft relation) state =
        input.schema.evaluatePath (assembleEdge object)
          (input.schema.relationRight relation) state :=
  relationFormula_evaluate_iff_raw object.table
    (fun edge => object.edge_lawful edge) relation state

/-- Observation formulas are equivalent to the native named-edge square. -/
theorem observationFormula_evaluate_iff {input : ProtocolFamilyInput.{u}}
    (object : Object input) {source target}
    (edge : input.schema.Edge source target) (state : object.State source) :
    (observationFormula input object.table (fun edge => object.edge_lawful edge)
      (fun vertex => object.observe_lawful vertex) edge state).evaluate
        (objectLawTable object.table) ↔
      input.observation.map (input.schema.edgeMorphism edge)
          (assembleObservation object source state) =
        assembleObservation object target (assembleEdge object edge state) :=
  observationFormula_evaluate_iff_raw object.table
    (fun edge => object.edge_lawful edge)
    (fun vertex => object.observe_lawful vertex) edge state

/-- The free-path functor generated by the assembled primitive edge graphs. -/
def assembledPathFunctor {input : ProtocolFamilyInput.{u}} (object : Object input) :
    Paths input.schema.Vertex ⥤ Type u :=
  input.schema.pathFunctorOfEdgeAction object.State (assembleEdge object)

/-- Primitive relation formulas make the assembled path functor respect the schema relation. -/
theorem assembledPathFunctor_relation {input : ProtocolFamilyInput.{u}}
    (object : Object input) {source target : Paths input.schema.Vertex}
    (left right : source ⟶ target) (relation : input.schema.pathRelation left right) :
    (assembledPathFunctor object).map left = (assembledPathFunctor object).map right := by
  obtain ⟨index, sourceEq, targetEq, leftEq, rightEq⟩ := relation
  cases sourceEq
  cases targetEq
  subst left
  subst right
  funext state
  exact (relationFormula_evaluate_iff object index state).mp
    (object.relation_formula index state)

/-- The functor on the quotient execution category assembled from primitive graphs. -/
def assembledFunctor {input : ProtocolFamilyInput.{u}} (object : Object input) :
    input.schema.ExecutionCategory ⥤ Type u :=
  CategoryTheory.Quotient.lift input.schema.pathRelation (assembledPathFunctor object)
    (fun _ _ left right relation => assembledPathFunctor_relation object left right relation)

/-- Named-edge observation squares extend over every free path. -/
def assembledPathObservation {input : ProtocolFamilyInput.{u}} (object : Object input) :
    assembledPathFunctor object ⟶
      CategoryTheory.Quotient.functor input.schema.pathRelation ⋙ input.observation :=
  Paths.liftNatTrans (assembleObservation object) (fun edge => by
    funext state
    exact (observationFormula_evaluate_iff object edge state).mp
      (object.observation_formula edge state) |>.symm)

/-- The observation transformation assembled on the quotient execution category. -/
def assembledObservation {input : ProtocolFamilyInput.{u}} (object : Object input) :
    assembledFunctor object ⟶ input.observation where
  app execution := assembleObservation object execution.as
  naturality := by
    intro source target morphism
    apply CategoryTheory.Quotient.induction (r := input.schema.pathRelation)
      (P := fun {a b} path =>
        (assembledFunctor object).map path ≫ assembleObservation object b.as =
          assembleObservation object a.as ≫ input.observation.map path)
    intro source target path
    exact (assembledPathObservation object).naturality path

/-- Assemble a primitive protocol object into the existing semantic category. -/
def assembleObject {input : ProtocolFamilyInput.{u}} (object : Object input) :
    ProtocolRealization input.schema input.observation where
  toFunctor := assembledFunctor object
  state_finite := object.state_finite
  observation := assembledObservation object

/-- Read vertex carriers, named edges, and observations into one primitive table. -/
def readDataTable {input : ProtocolFamilyInput.{u}}
    (realization : ProtocolRealization input.schema input.observation) :
    ObjectTable input := by
  intro query
  cases query with
  | stateCarrier vertex => exact realization.State vertex
  | edge edge query =>
      exact ULift.up (IndependentCarrierGraph.read _ _
        (realization.edgeAction edge) query)
  | observe vertex query =>
      exact ULift.up (IndependentCarrierGraph.read _ _
        (realization.observe vertex) query)

/-- Edge-table restriction of a semantic protocol reading. -/
@[simp] theorem edgeTable_readDataTable {input : ProtocolFamilyInput.{u}}
    (realization : ProtocolRealization input.schema input.observation)
    {source target} (edge : input.schema.Edge source target) :
    edgeTable (readDataTable realization) edge =
      IndependentCarrierGraph.read _ _ (realization.edgeAction edge) := rfl

/-- Observation-table restriction of a semantic protocol reading. -/
@[simp] theorem observeTable_readDataTable {input : ProtocolFamilyInput.{u}}
    (realization : ProtocolRealization input.schema input.observation)
    (vertex : input.schema.Vertex) :
    observeTable (readDataTable realization) vertex =
      IndependentCarrierGraph.read _ _ (realization.observe vertex) := rfl

/-- Read an arbitrary semantic protocol realization into primitive fragments. -/
def readObject {input : ProtocolFamilyInput.{u}}
    (realization : ProtocolRealization input.schema input.observation) : Object input where
  family := objectFragments (readDataTable realization)
  compatible := objectFragments_compatible _
  edge_instances edge :=
    (IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances
      (IndependentCarrierGraph.read _ _ (realization.edgeAction edge)) id _ _).mp
      (IndependentCarrierGraph.read_isLawful _ _ (realization.edgeAction edge))
  observe_instances vertex :=
    (IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances
      (IndependentCarrierGraph.read _ _ (realization.observe vertex)) id _ _).mp
      (IndependentCarrierGraph.read_isLawful _ _ (realization.observe vertex))
  relation_formula relation state := by
    apply (relationFormula_evaluate_iff_raw (readDataTable realization)
      (fun edge => IndependentCarrierGraph.read_isLawful _ _
        (realization.edgeAction edge)) relation state).mpr
    change input.schema.evaluatePath
        (fun {source target} (edge : input.schema.Edge source target) =>
          IndependentCarrierGraph.assemble (realization.State source)
            (realization.State target)
            (IndependentCarrierGraph.read _ _ (realization.edgeAction edge))
            (IndependentCarrierGraph.read_isLawful _ _
              (realization.edgeAction edge)))
          (input.schema.relationLeft relation) state =
      input.schema.evaluatePath
        (fun {source target} (edge : input.schema.Edge source target) =>
          IndependentCarrierGraph.assemble (realization.State source)
            (realization.State target)
            (IndependentCarrierGraph.read _ _ (realization.edgeAction edge))
            (IndependentCarrierGraph.read_isLawful _ _
              (realization.edgeAction edge)))
          (input.schema.relationRight relation) state
    have assembled :
        (fun {source target} (edge : input.schema.Edge source target) =>
          IndependentCarrierGraph.assemble (realization.State source)
            (realization.State target)
            (IndependentCarrierGraph.read _ _ (realization.edgeAction edge))
            (IndependentCarrierGraph.read_isLawful _ _
              (realization.edgeAction edge))) =
        (fun {source target} (edge : input.schema.Edge source target) =>
          realization.edgeAction edge) := by
      funext source target edge state
      exact congrFun (IndependentCarrierGraph.assemble_read _ _
        (realization.edgeAction edge)) state
    rw [assembled]
    rw [protocolEvaluatePath_eq_pathAction, protocolEvaluatePath_eq_pathAction]
    have leftPath := congrArg realization.toFunctor.map
      (input.schema.relation_sound relation)
    exact congrFun leftPath state
  observation_formula edge state := by
    apply (observationFormula_evaluate_iff_raw (readDataTable realization)
      (fun edge => IndependentCarrierGraph.read_isLawful _ _
        (realization.edgeAction edge))
      (fun vertex => IndependentCarrierGraph.read_isLawful _ _
        (realization.observe vertex)) edge state).mpr
    change input.observation.map (input.schema.edgeMorphism edge)
        (IndependentCarrierGraph.assemble (realization.State _)
          (input.observation.obj (input.schema.vertexObject _))
          (IndependentCarrierGraph.read _ _ (realization.observe _))
          (IndependentCarrierGraph.read_isLawful _ _
            (realization.observe _)) state) =
      IndependentCarrierGraph.assemble (realization.State _)
        (input.observation.obj (input.schema.vertexObject _))
        (IndependentCarrierGraph.read _ _ (realization.observe _))
        (IndependentCarrierGraph.read_isLawful _ _
          (realization.observe _))
        (IndependentCarrierGraph.assemble (realization.State _)
          (realization.State _)
          (IndependentCarrierGraph.read _ _ (realization.edgeAction edge))
          (IndependentCarrierGraph.read_isLawful _ _
            (realization.edgeAction edge)) state)
    rw [congrFun (IndependentCarrierGraph.assemble_read _ _
      (realization.observe _)) state]
    rw [congrFun (IndependentCarrierGraph.assemble_read _ _
      (realization.edgeAction edge)) state]
    rw [congrFun (IndependentCarrierGraph.assemble_read _ _
      (realization.observe _)) (realization.edgeAction edge state)]
    exact congrFun (NatTrans.naturality realization.observation
      (input.schema.edgeMorphism edge)).symm state
  state_cover vertex := by
    apply (stateCover_iff_finite (readDataTable realization) vertex).mpr
    exact realization.state_finite vertex

/-- Reading after primitive object assembly recovers every primitive cell. -/
@[simp] theorem readObject_assembleObject {input : ProtocolFamilyInput.{u}}
    (object : Object input) : readObject (assembleObject object) = object := by
  apply Object.ext
  change objectFragments (readDataTable (assembleObject object)) = object.family
  rw [← objectFragments_glue object.family object.compatible]
  apply congrArg objectFragments
  funext query
  cases query with
  | stateCarrier vertex => rfl
  | edge edge query =>
      apply ULift.ext
      exact congrFun (IndependentCarrierGraph.read_assemble _ _
        (edgeTable object.table edge) (object.edge_lawful edge)) query
  | observe vertex query =>
      apply ULift.ext
      exact congrFun (IndependentCarrierGraph.read_assemble _ _
        (observeTable object.table vertex) (object.observe_lawful vertex)) query

/-- Semantic reading followed by primitive assembly is isomorphic to the source realization. -/
def assembleObjectReadIso {input : ProtocolFamilyInput.{u}}
    (realization : ProtocolRealization input.schema input.observation) :
    assembleObject (readObject realization) ≅ realization where
  hom := ProtocolRealization.ext
    { component := fun _ => id
      edge_naturality := fun edge => by
        funext state
        exact congrFun (IndependentCarrierGraph.assemble_read _ _
          (realization.edgeAction edge)) state
      observation_naturality := fun vertex => by
        funext state
        exact (congrFun (IndependentCarrierGraph.assemble_read _ _
          (realization.observe vertex)) state).symm }
  inv := ProtocolRealization.ext
    { component := fun _ => id
      edge_naturality := fun edge => by
        funext state
        exact (congrFun (IndependentCarrierGraph.assemble_read _ _
          (realization.edgeAction edge)) state).symm
      observation_naturality := fun vertex => by
        funext state
        exact congrFun (IndependentCarrierGraph.assemble_read _ _
          (realization.observe vertex)) state }
  hom_inv_id := by
    apply ProtocolRealization.Hom.ext
    ext execution state
    rfl
  inv_hom_id := by
    apply ProtocolRealization.Hom.ext
    ext execution state
    rfl

/-- Primitive vertex-map queries for a protocol Hom. -/
inductive HomTableQuery (input : ProtocolFamilyInput.{u}) where
  /-- One candidate graph cell at a fixed schema vertex. -/
  | map (vertex : input.schema.Vertex) (query : GraphQuery.{u})

/-- Every primitive Hom-table query has one Boolean value. -/
abbrev HomTableValue {input : ProtocolFamilyInput.{u}} (_ : HomTableQuery input) := Bool

/-- Dependent primitive table of vertex-map graph cells. -/
abbrev HomTable (input : ProtocolFamilyInput.{u}) := HomTableQuery input → Bool

/-- Finite fragments of a primitive protocol Hom table. -/
abbrev HomFragment {input : ProtocolFamilyInput.{u}}
    (D : Finset (HomTableQuery input)) :=
  IndependentFiniteFragments.Fragment
    (fun query : HomTableQuery input => HomTableValue query) D

/-- A family of finite primitive protocol Hom fragments. -/
abbrev HomFragmentFamily (input : ProtocolFamilyInput.{u}) :=
  IndependentFiniteFragments.FragmentFamily
    (fun query : HomTableQuery input => HomTableValue query)

/-- Compatibility of finite primitive protocol Hom fragments. -/
abbrev HomCompatible {input : ProtocolFamilyInput.{u}}
    (family : HomFragmentFamily input) :=
  IndependentFiniteFragments.Compatible family

/-- Restrict a primitive protocol Hom table to all finite query sets. -/
def homFragments {input : ProtocolFamilyInput.{u}} (table : HomTable input) :
    HomFragmentFamily input :=
  IndependentFiniteFragments.fragments table

/-- Glue compatible primitive protocol Hom fragments. -/
def homGlue {input : ProtocolFamilyInput.{u}} (family : HomFragmentFamily input) :
    HomTable input :=
  IndependentFiniteFragments.glue family

/-- Restrictions of a primitive protocol Hom table are compatible. -/
theorem homFragments_compatible {input : ProtocolFamilyInput.{u}}
    (table : HomTable input) : HomCompatible (homFragments table) :=
  IndependentFiniteFragments.fragments_compatible table

/-- Gluing all Hom restrictions recovers the table. -/
theorem homGlue_fragments {input : ProtocolFamilyInput.{u}} (table : HomTable input) :
    homGlue (homFragments table) = table :=
  IndependentFiniteFragments.glue_fragments table

/-- Compatible Hom fragments are recovered from their glued table. -/
theorem homFragments_glue {input : ProtocolFamilyInput.{u}}
    (family : HomFragmentFamily input) (compatible : HomCompatible family) :
    homFragments (homGlue family) = family :=
  IndependentFiniteFragments.fragments_glue family compatible

/-- Restrict a primitive Hom table to one vertex-map graph. -/
def vertexMapTable {input : ProtocolFamilyInput.{u}} (table : HomTable input)
    (vertex : input.schema.Vertex) : GraphTable.{u} :=
  fun query => table (.map vertex query)

/-- Derived protocol Hom-law queries tag both endpoints and the vertex maps. -/
inductive HomLawQuery (input : ProtocolFamilyInput.{u}) where
  /-- A source-object derived law cell. -/
  | source (query : ObjectLawQuery input)
  /-- A target-object derived law cell. -/
  | target (query : ObjectLawQuery input)
  /-- A vertex-map graph cell. -/
  | map (vertex : input.schema.Vertex) (query : GraphQuery.{u})

/-- Primitive Hom-law queries tag endpoint cells and vertex-map cells. -/
inductive HomPrimitiveQuery (input : ProtocolFamilyInput.{u}) where
  /-- One source-object primitive cell. -/
  | source (query : ObjectQuery input)
  /-- One target-object primitive cell. -/
  | target (query : ObjectQuery input)
  /-- One vertex-map primitive cell. -/
  | map (vertex : input.schema.Vertex) (query : GraphQuery.{u})

/-- Dependent value type of a primitive protocol Hom-law query. -/
def HomPrimitiveValue {input : ProtocolFamilyInput.{u}} :
    HomPrimitiveQuery input → Type (u + 1)
  | .source query => ObjectValue query
  | .target query => ObjectValue query
  | .map _ _ => ULift.{u + 1, 0} Bool

/-- A tagged dependent table containing both endpoints and all vertex maps. -/
abbrev HomPrimitiveTable (input : ProtocolFamilyInput.{u}) :=
  (query : HomPrimitiveQuery input) → HomPrimitiveValue query

/-- Combine two object tables and one vertex-map table. -/
def homPrimitiveTable {input : ProtocolFamilyInput.{u}}
    (source target : ObjectTable input) (maps : HomTable input) :
    HomPrimitiveTable input
  | .source query => source query
  | .target query => target query
  | .map vertex query => ULift.up (maps (.map vertex query))

/-- Derive the Boolean Hom-law table used by closed formulas. -/
def homLawTable {input : ProtocolFamilyInput.{u}}
    (source target : ObjectTable input) (maps : HomTable input) :
    HomLawQuery input → Bool
  | .source query => objectLawTable source query
  | .target query => objectLawTable target query
  | .map vertex query => maps (.map vertex query)

/-- Map each derived Hom-law query to its determining primitive cell. -/
def homLawQueryBase (input : ProtocolFamilyInput.{u}) :
    HomLawQuery input → HomPrimitiveQuery input
  | .source query => .source (objectLawQueryBase input query)
  | .target query => .target (objectLawQueryBase input query)
  | .map vertex query => .map vertex query

/-- Primitive cells needed to evaluate one finite protocol Hom formula. -/
def homFormulaBaseSupport (input : ProtocolFamilyInput.{u})
    (formula : IndependentFiniteLawFormula.BoolFormula.{u + 1, 0}
      (HomLawQuery input)) : Finset (HomPrimitiveQuery input) := by
  classical
  exact formula.support.image (homLawQueryBase input)

/-- Derive a Boolean Hom-law table from its dependent primitive table. -/
def homPrimitiveLawTable {input : ProtocolFamilyInput.{u}}
    (table : HomPrimitiveTable input) : HomLawQuery input → Bool := by
  classical
  intro query
  cases query with
  | source query =>
      cases query with
      | carrierMatches vertex candidate =>
          exact decide (candidate = table (.source (.stateCarrier vertex)))
      | edge edge graphQuery => exact (table (.source (.edge edge graphQuery))).down
      | observe vertex graphQuery =>
          exact (table (.source (.observe vertex graphQuery))).down
  | target query =>
      cases query with
      | carrierMatches vertex candidate =>
          exact decide (candidate = table (.target (.stateCarrier vertex)))
      | edge edge graphQuery => exact (table (.target (.edge edge graphQuery))).down
      | observe vertex graphQuery =>
          exact (table (.target (.observe vertex graphQuery))).down
  | map vertex graphQuery => exact (table (.map vertex graphQuery)).down

/-- Primitive Hom support agreement preserves derived formula evaluation. -/
theorem homFormula_evaluate_iff_of_base_support
    (input : ProtocolFamilyInput.{u})
    (formula : IndependentFiniteLawFormula.BoolFormula.{u + 1, 0}
      (HomLawQuery input))
    (first second : HomPrimitiveTable input)
    (agree : ∀ query ∈ homFormulaBaseSupport input formula,
      first query = second query) :
    formula.evaluate (homPrimitiveLawTable first) ↔
      formula.evaluate (homPrimitiveLawTable second) := by
  classical
  apply IndependentFiniteLawFormula.BoolFormula.evaluate_iff_of_support
  intro query member
  have baseMember : homLawQueryBase input query ∈ homFormulaBaseSupport input formula :=
    Finset.mem_image.mpr ⟨query, member, rfl⟩
  cases query with
  | source query =>
      cases query with
      | carrierMatches vertex candidate =>
          exact congrArg (fun carrier => decide (candidate = carrier))
            (agree (.source (.stateCarrier vertex)) baseMember)
      | edge edge graphQuery =>
          exact congrArg ULift.down (agree (.source (.edge edge graphQuery)) baseMember)
      | observe vertex graphQuery =>
          exact congrArg ULift.down
            (agree (.source (.observe vertex graphQuery)) baseMember)
  | target query =>
      cases query with
      | carrierMatches vertex candidate =>
          exact congrArg (fun carrier => decide (candidate = carrier))
            (agree (.target (.stateCarrier vertex)) baseMember)
      | edge edge graphQuery =>
          exact congrArg ULift.down (agree (.target (.edge edge graphQuery)) baseMember)
      | observe vertex graphQuery =>
          exact congrArg ULift.down
            (agree (.target (.observe vertex graphQuery)) baseMember)
  | map vertex graphQuery =>
      exact congrArg ULift.down (agree (.map vertex graphQuery) baseMember)

/-- Finite formula for preservation of one named edge at one point. -/
def edgePreservationFormula (input : ProtocolFamilyInput.{u})
    (sourceTable targetTable : ObjectTable input)
    {source target : input.schema.Vertex}
    (edge : input.schema.Edge source target)
    (state : State sourceTable source) (image : State targetTable source)
    (sourceNext : State sourceTable target) (targetNext : State targetTable target) :
    IndependentFiniteLawFormula.BoolFormula.{u + 1, 0} (HomLawQuery input) :=
  .and (.cell (.source (.carrierMatches source (State sourceTable source))) true)
    (.and (.cell (.target (.carrierMatches source (State targetTable source))) true)
      (.and (.cell (.source (.carrierMatches target (State sourceTable target))) true)
        (.and (.cell (.target (.carrierMatches target (State targetTable target))) true)
          (.implies
            (.and
              (.and
                (.cell (.map source (.edge _ _ state image)) true)
                (.cell (.source (.edge edge (.edge _ _ state sourceNext))) true))
              (.cell (.target (.edge edge (.edge _ _ image targetNext))) true))
            (.cell (.map target (.edge _ _ sourceNext targetNext)) true)))))

/-- Finite formula for preservation of one vertex observation at one point. -/
def observationPreservationFormula (input : ProtocolFamilyInput.{u})
    (sourceTable targetTable : ObjectTable input) (vertex : input.schema.Vertex)
    (state : State sourceTable vertex) (image : State targetTable vertex)
    (value : input.observation.obj (input.schema.vertexObject vertex)) :
    IndependentFiniteLawFormula.BoolFormula.{u + 1, 0} (HomLawQuery input) :=
  .and (.cell (.source (.carrierMatches vertex (State sourceTable vertex))) true)
    (.and (.cell (.target (.carrierMatches vertex (State targetTable vertex))) true)
      (.implies
        (.and
          (.cell (.map vertex (.edge _ _ state image)) true)
          (.cell (.source (.observe vertex (.edge _ _ state value))) true))
        (.cell (.target (.observe vertex (.edge _ _ image value))) true)))

/-- A primitive protocol Hom with vertex maps and generator preservation formulas. -/
structure Hom {input : ProtocolFamilyInput.{u}} (source target : Object input) where
  /-- Finite fragments containing all vertex-map graph cells. -/
  family : HomFragmentFamily input
  /-- The finite fragments agree under inclusions. -/
  compatible : HomCompatible family
  /-- Closed total graph rows at every schema vertex. -/
  map_instances : ∀ vertex,
    IndependentFiniteGraphLawFormula.CarrierRows.Instances
      (vertexMapTable (homGlue family) vertex) id
      (source.State vertex) (target.State vertex)
  /-- Every named-edge preservation formula evaluates. -/
  edge_formula : ∀ {v w} (edge : input.schema.Edge v w)
      (state : source.State v) (image : target.State v)
      (sourceNext : source.State w) (targetNext : target.State w),
    (edgePreservationFormula input source.table target.table edge
      state image sourceNext targetNext).evaluate
        (homLawTable source.table target.table (homGlue family))
  /-- Every observation preservation formula evaluates. -/
  observation_formula : ∀ vertex (state : source.State vertex)
      (image : target.State vertex)
      (value : input.observation.obj (input.schema.vertexObject vertex)),
    (observationPreservationFormula input source.table target.table vertex
      state image value).evaluate
        (homLawTable source.table target.table (homGlue family))

namespace Hom

variable {input : ProtocolFamilyInput.{u}} {source target : Object input}

/-- Glue the primitive vertex-map table. -/
def table (morphism : Hom source target) : HomTable input := homGlue morphism.family

/-- Every vertex-map graph is lawful. -/
theorem lawful (morphism : Hom source target) (vertex : input.schema.Vertex) :
    IndependentCarrierGraph.IsLawful (source.State vertex) (target.State vertex)
      (vertexMapTable morphism.table vertex) :=
  (IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances
    (vertexMapTable morphism.table vertex) id _ _).mpr (morphism.map_instances vertex)

/-- Primitive protocol Homs are equal when their fragment families agree. -/
@[ext]
theorem ext {first second : Hom source target} (family : first.family = second.family) :
    first = second := by
  cases first
  cases second
  cases family
  rfl

/-- Assemble the vertex map selected by a primitive Hom graph. -/
def component (morphism : Hom source target) (vertex : input.schema.Vertex) :
    source.State vertex → target.State vertex :=
  IndependentCarrierGraph.assemble _ _ (vertexMapTable morphism.table vertex)
    (morphism.lawful vertex)

/-- Primitive vertex-map cells are exactly the graph of the assembled component. -/
theorem edge_iff (morphism : Hom source target) (vertex : input.schema.Vertex)
    (state : source.State vertex) (image : target.State vertex) :
    morphism.table (.map vertex (.edge _ _ state image)) = true ↔
      morphism.component vertex state = image := by
  constructor
  · exact IndependentCarrierGraph.assemble_eq_of_edge _ _ _ (morphism.lawful vertex)
  · intro equality
    rw [← equality]
    exact IndependentCarrierGraph.edge_assemble _ _ _ (morphism.lawful vertex) state

end Hom

/-- Assemble a primitive protocol Hom through the existing generator extension. -/
def assembleHom {input : ProtocolFamilyInput.{u}} {source target : Object input}
    (morphism : Hom source target) : assembleObject source ⟶ assembleObject target :=
  ProtocolRealization.ext
    { component := morphism.component
      edge_naturality := fun {v w} edge => by
        funext state
        let image := morphism.component v state
        let sourceNext := assembleEdge source edge state
        let targetNext := assembleEdge target edge image
        apply (morphism.edge_iff w sourceNext targetNext).mp
        exact (morphism.edge_formula edge state image sourceNext targetNext).2.2.2.2
          ⟨⟨(morphism.edge_iff v state image).mpr rfl,
              (edge_edge_iff source edge state sourceNext).mpr rfl⟩,
            (edge_edge_iff target edge image targetNext).mpr rfl⟩
      observation_naturality := fun vertex => by
        funext state
        let image := morphism.component vertex state
        let value := assembleObservation source vertex state
        apply (observe_edge_iff target vertex image value).mp
        exact (morphism.observation_formula vertex state image value).2.2
          ⟨(morphism.edge_iff vertex state image).mpr rfl,
            (observe_edge_iff source vertex state value).mpr rfl⟩ }

/-- Read a semantic protocol Hom into vertex-map graphs and generator formulas. -/
def readHom {input : ProtocolFamilyInput.{u}}
    {source target : ProtocolRealization input.schema input.observation}
    (morphism : source ⟶ target) : Hom (readObject source) (readObject target) where
  family := homFragments (fun query => match query with
    | .map vertex graphQuery =>
        IndependentCarrierGraph.read _ _
          ((ProtocolRealization.res morphism).component vertex) graphQuery)
  compatible := homFragments_compatible _
  map_instances vertex :=
    (IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances
      (IndependentCarrierGraph.read _ _
        ((ProtocolRealization.res morphism).component vertex)) id _ _).mp
      (IndependentCarrierGraph.read_isLawful _ _
        ((ProtocolRealization.res morphism).component vertex))
  edge_formula {v} {w} edge state image sourceNext targetNext := by
    simp only [homGlue_fragments, edgePreservationFormula,
      IndependentFiniteLawFormula.BoolFormula.evaluate]
    refine ⟨(readObject source).carrier_selected _,
      (readObject target).carrier_selected _,
      (readObject source).carrier_selected _,
      (readObject target).carrier_selected _, ?_⟩
    change ((IndependentCarrierGraph.read (source.State v) (target.State v)
          ((ProtocolRealization.res morphism).component v)
            (.edge (source.State v) (target.State v) state image) = true ∧
        IndependentCarrierGraph.read (source.State v) (source.State w)
          (source.edgeAction edge)
            (.edge (source.State v) (source.State w) state sourceNext) = true) ∧
      IndependentCarrierGraph.read (target.State v) (target.State w)
        (target.edgeAction edge)
          (.edge (target.State v) (target.State w) image targetNext) = true) →
      IndependentCarrierGraph.read (source.State w) (target.State w)
        ((ProtocolRealization.res morphism).component w)
          (.edge (source.State w) (target.State w) sourceNext targetNext) = true
    rintro ⟨⟨mapCell, sourceCell⟩, targetCell⟩
    apply (IndependentCarrierGraph.read_edge _ _ _ _ _).mpr
    have mapEquality := (IndependentCarrierGraph.read_edge _ _ _ _ _).mp mapCell
    have sourceEquality := (IndependentCarrierGraph.read_edge _ _ _ _ _).mp sourceCell
    have targetEquality := (IndependentCarrierGraph.read_edge _ _ _ _ _).mp targetCell
    subst image
    subst sourceNext
    subst targetNext
    exact congrFun ((ProtocolRealization.res morphism).edge_naturality edge) state
  observation_formula vertex state image value := by
    simp only [homGlue_fragments, observationPreservationFormula,
      IndependentFiniteLawFormula.BoolFormula.evaluate]
    refine ⟨(readObject source).carrier_selected vertex,
      (readObject target).carrier_selected vertex, ?_⟩
    change (IndependentCarrierGraph.read (source.State vertex) (target.State vertex)
          ((ProtocolRealization.res morphism).component vertex)
            (.edge (source.State vertex) (target.State vertex) state image) = true ∧
        IndependentCarrierGraph.read (source.State vertex)
          (input.observation.obj (input.schema.vertexObject vertex))
          (source.observe vertex)
            (.edge (source.State vertex)
              (input.observation.obj (input.schema.vertexObject vertex)) state value) = true) →
      IndependentCarrierGraph.read (target.State vertex)
        (input.observation.obj (input.schema.vertexObject vertex))
        (target.observe vertex)
          (.edge (target.State vertex)
            (input.observation.obj (input.schema.vertexObject vertex)) image value) = true
    rintro ⟨mapCell, sourceCell⟩
    apply (IndependentCarrierGraph.read_edge _ _ _ _ _).mpr
    have mapEquality := (IndependentCarrierGraph.read_edge _ _ _ _ _).mp mapCell
    have sourceEquality := (IndependentCarrierGraph.read_edge _ _ _ _ _).mp sourceCell
    subst image
    subst value
    exact congrFun ((ProtocolRealization.res morphism).observation_naturality vertex) state

/-- Assemble a local Hom directly between its original semantic endpoints. -/
def assembleReadHom {input : ProtocolFamilyInput.{u}}
    {source target : ProtocolRealization input.schema input.observation}
    (morphism : Hom (readObject source) (readObject target)) : source ⟶ target :=
  ProtocolRealization.ext
    { component := morphism.component
      edge_naturality := fun {v w} edge => by
        funext state
        let image := morphism.component v state
        let sourceNext := source.edgeAction edge state
        let targetNext := target.edgeAction edge image
        apply (morphism.edge_iff w sourceNext targetNext).mp
        exact (morphism.edge_formula edge state image sourceNext targetNext).2.2.2.2
          ⟨⟨(morphism.edge_iff v state image).mpr rfl,
              (IndependentCarrierGraph.read_edge _ _ (source.edgeAction edge)
                state sourceNext).mpr rfl⟩,
            (IndependentCarrierGraph.read_edge _ _ (target.edgeAction edge)
              image targetNext).mpr rfl⟩
      observation_naturality := fun vertex => by
        funext state
        let image := morphism.component vertex state
        let value := source.observe vertex state
        apply (IndependentCarrierGraph.read_edge _ _ (target.observe vertex)
          image value).mp
        exact (morphism.observation_formula vertex state image value).2.2
          ⟨(morphism.edge_iff vertex state image).mpr rfl,
            (IndependentCarrierGraph.read_edge _ _ (source.observe vertex)
              state value).mpr rfl⟩ }

/-- Assembly after reading recovers every semantic protocol Hom. -/
@[simp] theorem assembleReadHom_readHom {input : ProtocolFamilyInput.{u}}
    {source target : ProtocolRealization input.schema input.observation}
    (morphism : source ⟶ target) :
    assembleReadHom (readHom morphism) = morphism := by
  apply ProtocolRealization.Hom.ext
  ext execution state
  exact congrFun (IndependentCarrierGraph.assemble_read _ _
    ((ProtocolRealization.res morphism).component execution.as)) state

/-- Reading after direct endpoint assembly recovers every primitive Hom. -/
@[simp] theorem readHom_assembleReadHom {input : ProtocolFamilyInput.{u}}
    {source target : ProtocolRealization input.schema input.observation}
    (morphism : Hom (readObject source) (readObject target)) :
    readHom (assembleReadHom morphism) = morphism := by
  apply Hom.ext
  change homFragments (fun query => match query with
    | .map vertex graphQuery => IndependentCarrierGraph.read _ _
        (morphism.component vertex) graphQuery) = morphism.family
  rw [← homFragments_glue morphism.family morphism.compatible]
  apply congrArg homFragments
  funext query
  cases query with
  | map vertex graphQuery =>
      exact congrFun (IndependentCarrierGraph.read_assemble _ _
        (vertexMapTable morphism.table vertex) (morphism.lawful vertex)) graphQuery

/-- Direct primitive identity uses the diagonal graph at every vertex. -/
def identityHom {input : ProtocolFamilyInput.{u}} (object : Object input) :
    Hom object object where
  family := homFragments (fun query => match query with
    | .map vertex graphQuery => IndependentCarrierGraph.identity (object.State vertex) graphQuery)
  compatible := homFragments_compatible _
  map_instances vertex :=
    (IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances
      (IndependentCarrierGraph.identity (object.State vertex)) id _ _).mp
      (IndependentCarrierGraph.identity_isLawful _)
  edge_formula {v} {w} edge state image sourceNext targetNext := by
    simp only [homGlue_fragments, edgePreservationFormula,
      IndependentFiniteLawFormula.BoolFormula.evaluate]
    refine ⟨object.carrier_selected _, object.carrier_selected _,
      object.carrier_selected _, object.carrier_selected _, ?_⟩
    rintro ⟨⟨mapCell, sourceCell⟩, targetCell⟩
    have imageEq := (IndependentCarrierGraph.identity_edge _ state image).mp mapCell
    subst image
    apply (IndependentCarrierGraph.identity_edge _ sourceNext targetNext).mpr
    exact (IndependentCarrierGraph.assemble_eq_of_edge _ _ _
      (object.edge_lawful edge) sourceCell).symm.trans
        (IndependentCarrierGraph.assemble_eq_of_edge _ _ _
          (object.edge_lawful edge) targetCell)
  observation_formula vertex state image value := by
    simp only [homGlue_fragments, observationPreservationFormula,
      IndependentFiniteLawFormula.BoolFormula.evaluate]
    refine ⟨object.carrier_selected vertex, object.carrier_selected vertex, ?_⟩
    rintro ⟨mapCell, sourceCell⟩
    have imageEq := (IndependentCarrierGraph.identity_edge _ state image).mp mapCell
    subst image
    exact sourceCell

/-- Direct primitive composition uses point composition of every vertex graph. -/
def composeHom {input : ProtocolFamilyInput.{u}}
    {source middle target : Object input}
    (first : Hom source middle) (second : Hom middle target) : Hom source target where
  family := homFragments (fun query => match query with
    | .map vertex graphQuery =>
        IndependentCarrierGraph.compose (source.State vertex) (middle.State vertex)
          (target.State vertex)
          (vertexMapTable first.table vertex) (first.lawful vertex)
          (vertexMapTable second.table vertex) graphQuery)
  compatible := homFragments_compatible _
  map_instances vertex :=
    (IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances
      (IndependentCarrierGraph.compose (source.State vertex) (middle.State vertex)
        (target.State vertex)
        (vertexMapTable first.table vertex) (first.lawful vertex)
        (vertexMapTable second.table vertex)) id _ _).mp
      (IndependentCarrierGraph.compose_isLawful (source.State vertex)
        (middle.State vertex) (target.State vertex)
        (vertexMapTable first.table vertex) (first.lawful vertex)
        (vertexMapTable second.table vertex) (second.lawful vertex))
  edge_formula {v} {w} edge state image sourceNext targetNext := by
    simp only [homGlue_fragments, edgePreservationFormula,
      IndependentFiniteLawFormula.BoolFormula.evaluate]
    refine ⟨source.carrier_selected _, target.carrier_selected _,
      source.carrier_selected _, target.carrier_selected _, ?_⟩
    rintro ⟨⟨compositeCell, sourceCell⟩, targetCell⟩
    let middleState := first.component _ state
    let middleNext := assembleEdge middle edge middleState
    change IndependentCarrierGraph.compose (source.State v) (middle.State v)
      (target.State v) (vertexMapTable first.table v) (first.lawful v)
        (vertexMapTable second.table v)
          (.edge (source.State v) (target.State v) state image) = true at compositeCell
    have firstCell : first.table (.map v (.edge _ _ state middleState)) = true :=
      (first.edge_iff v state middleState).mpr rfl
    have secondCell : second.table (.map v (.edge _ _ middleState image)) = true := by
      simpa [middleState, IndependentCarrierGraph.compose_edge] using compositeCell
    have firstNext : first.table (.map w (.edge _ _ sourceNext middleNext)) = true :=
      (first.edge_formula edge state middleState sourceNext middleNext).2.2.2.2
        ⟨⟨firstCell, sourceCell⟩,
          (edge_edge_iff middle edge middleState middleNext).mpr rfl⟩
    have middleNextEq : first.component w sourceNext = middleNext :=
      (first.edge_iff w sourceNext middleNext).mp firstNext
    change IndependentCarrierGraph.assemble (source.State w) (middle.State w)
      (vertexMapTable first.table w) (first.lawful w) sourceNext = middleNext at middleNextEq
    have secondNext : second.table (.map w (.edge _ _ middleNext targetNext)) = true :=
      (second.edge_formula edge middleState image middleNext targetNext).2.2.2.2
        ⟨⟨secondCell, (edge_edge_iff middle edge middleState middleNext).mpr rfl⟩,
          targetCell⟩
    change IndependentCarrierGraph.compose (source.State w) (middle.State w)
      (target.State w) (vertexMapTable first.table w) (first.lawful w)
        (vertexMapTable second.table w)
          (.edge (source.State w) (target.State w) sourceNext targetNext) = true
    rw [IndependentCarrierGraph.compose_edge, middleNextEq]
    exact secondNext
  observation_formula vertex state image value := by
    simp only [homGlue_fragments, observationPreservationFormula,
      IndependentFiniteLawFormula.BoolFormula.evaluate]
    refine ⟨source.carrier_selected vertex, target.carrier_selected vertex, ?_⟩
    rintro ⟨compositeCell, sourceCell⟩
    let middleState := first.component vertex state
    have firstCell : first.table (.map vertex (.edge _ _ state middleState)) = true :=
      (first.edge_iff vertex state middleState).mpr rfl
    change IndependentCarrierGraph.compose (source.State vertex)
      (middle.State vertex) (target.State vertex)
      (vertexMapTable first.table vertex) (first.lawful vertex)
      (vertexMapTable second.table vertex)
        (.edge (source.State vertex) (target.State vertex) state image) = true
      at compositeCell
    have secondCell : second.table (.map vertex (.edge _ _ middleState image)) = true := by
      simpa [middleState, IndependentCarrierGraph.compose_edge] using compositeCell
    have middleObservation :=
      (first.observation_formula vertex state middleState value).2.2
      ⟨firstCell, sourceCell⟩
    exact (second.observation_formula vertex middleState image value).2.2
      ⟨secondCell, middleObservation⟩

/-- Primitive protocol objects and direct graph Homs form a category. -/
instance {input : ProtocolFamilyInput.{u}} : Category.{u + 1} (Object input) where
  Hom := fun source target => IndependentProtocolPrimitiveReconstruction.Hom source target
  id := identityHom
  comp := composeHom
  id_comp := by
    intro source target morphism
    apply Hom.ext
    have tableEq : (fun query : HomTableQuery input => match query with
      | .map vertex graphQuery =>
          IndependentCarrierGraph.compose (source.State vertex)
            (source.State vertex) (target.State vertex)
            (IndependentCarrierGraph.identity (source.State vertex))
            (IndependentCarrierGraph.identity_isLawful (source.State vertex))
            (vertexMapTable morphism.table vertex) graphQuery) = morphism.table := by
      funext query
      cases query with
      | map vertex graphQuery =>
          exact congrFun (IndependentCarrierGraph.identity_compose _ _
            (vertexMapTable morphism.table vertex) (morphism.lawful vertex)) graphQuery
    rw [← homFragments_glue morphism.family morphism.compatible]
    simpa only [composeHom, identityHom] using congrArg homFragments tableEq
  comp_id := by
    intro source target morphism
    apply Hom.ext
    have tableEq : (fun query : HomTableQuery input => match query with
      | .map vertex graphQuery =>
          IndependentCarrierGraph.compose (source.State vertex)
            (target.State vertex) (target.State vertex)
            (vertexMapTable morphism.table vertex) (morphism.lawful vertex)
            (IndependentCarrierGraph.identity (target.State vertex)) graphQuery) =
        morphism.table := by
      funext query
      cases query with
      | map vertex graphQuery =>
          exact congrFun (IndependentCarrierGraph.compose_identity _ _
            (vertexMapTable morphism.table vertex) (morphism.lawful vertex)) graphQuery
    rw [← homFragments_glue morphism.family morphism.compatible]
    simpa only [composeHom, identityHom] using congrArg homFragments tableEq
  assoc := by
    intro firstObject secondObject thirdObject fourthObject first second third
    apply Hom.ext
    have tableEq : (fun query : HomTableQuery input => match query with
      | .map vertex graphQuery =>
          IndependentCarrierGraph.compose (firstObject.State vertex)
            (thirdObject.State vertex) (fourthObject.State vertex)
            (IndependentCarrierGraph.compose (firstObject.State vertex)
              (secondObject.State vertex) (thirdObject.State vertex)
              (vertexMapTable first.table vertex) (first.lawful vertex)
              (vertexMapTable second.table vertex))
            (IndependentCarrierGraph.compose_isLawful _ _ _ _ (first.lawful vertex)
              _ (second.lawful vertex))
            (vertexMapTable third.table vertex) graphQuery) =
      (fun query : HomTableQuery input => match query with
        | .map vertex graphQuery =>
            IndependentCarrierGraph.compose (firstObject.State vertex)
              (secondObject.State vertex) (fourthObject.State vertex)
              (vertexMapTable first.table vertex) (first.lawful vertex)
              (IndependentCarrierGraph.compose (secondObject.State vertex)
                (thirdObject.State vertex) (fourthObject.State vertex)
                (vertexMapTable second.table vertex) (second.lawful vertex)
                (vertexMapTable third.table vertex)) graphQuery) := by
      funext query
      cases query with
      | map vertex graphQuery =>
          exact congrFun (IndependentCarrierGraph.compose_assoc _ _ _ _
            (vertexMapTable first.table vertex) (first.lawful vertex)
            (vertexMapTable second.table vertex) (second.lawful vertex)
            (vertexMapTable third.table vertex) (third.lawful vertex)) graphQuery
    simpa only [composeHom] using congrArg homFragments tableEq

/-- Reading sends semantic identities to direct primitive diagonal graphs. -/
theorem readHom_id {input : ProtocolFamilyInput.{u}}
    (realization : ProtocolRealization input.schema input.observation) :
    readHom (𝟙 realization) = identityHom (readObject realization) := by
  apply Hom.ext
  have tableEq : (fun query : HomTableQuery input => match query with
    | .map vertex graphQuery =>
        IndependentCarrierGraph.read (realization.State vertex)
          (realization.State vertex) id graphQuery) =
      (fun query : HomTableQuery input => match query with
        | .map vertex graphQuery =>
            IndependentCarrierGraph.identity (realization.State vertex) graphQuery) := by
    funext query
    cases query with
    | map vertex graphQuery => rfl
  simpa only [readHom, identityHom] using congrArg homFragments tableEq

/-- Reading sends semantic composition to direct pointwise graph composition. -/
theorem readHom_comp {input : ProtocolFamilyInput.{u}}
    {source middle target : ProtocolRealization input.schema input.observation}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    readHom (first ≫ second) = composeHom (readHom first) (readHom second) := by
  apply Hom.ext
  have tableEq : (fun query : HomTableQuery input => match query with
    | .map vertex graphQuery => IndependentCarrierGraph.read
        (source.State vertex) (target.State vertex)
        (((ProtocolRealization.res second).component vertex) ∘
          ((ProtocolRealization.res first).component vertex)) graphQuery) =
      (fun query : HomTableQuery input => match query with
        | .map vertex graphQuery => IndependentCarrierGraph.compose
            (source.State vertex) (middle.State vertex) (target.State vertex)
            (IndependentCarrierGraph.read _ _
              ((ProtocolRealization.res first).component vertex))
            (IndependentCarrierGraph.read_isLawful _ _
              ((ProtocolRealization.res first).component vertex))
            (IndependentCarrierGraph.read _ _
              ((ProtocolRealization.res second).component vertex)) graphQuery) := by
    funext query
    cases query with
    | map vertex graphQuery =>
        exact congrFun (IndependentCarrierGraph.read_compose _ _ _
          ((ProtocolRealization.res first).component vertex)
          ((ProtocolRealization.res second).component vertex)) graphQuery
  simpa only [readHom, composeHom] using congrArg homFragments tableEq

/-- Fixed-input semantic protocol reading into the primitive local category. -/
def readingFunctor (input : ProtocolFamilyInput.{u}) :
    ProtocolRealization input.schema input.observation ⥤ Object input where
  obj := readObject
  map := readHom
  map_id := readHom_id
  map_comp := readHom_comp

/-- Primitive reading separates all semantic protocol Homs. -/
theorem homSeparation (input : ProtocolFamilyInput.{u}) :
    HomSeparation (readingFunctor input) where
  hom source target := ⟨by
    intro first second equality
    calc
      first = assembleReadHom (readHom first) := (assembleReadHom_readHom first).symm
      _ = assembleReadHom (readHom second) := congrArg assembleReadHom equality
      _ = second := assembleReadHom_readHom second⟩

/-- Every primitive Hom between read endpoints assembles and reads back. -/
def homAssembly (input : ProtocolFamilyInput.{u}) :
    HomAssembly (readingFunctor input) where
  assemble := assembleReadHom
  map_assemble := readHom_assembleReadHom

/-- Every primitive object is read from its directly assembled realization. -/
def objectAssembly (input : ProtocolFamilyInput.{u}) :
    ObjectAssembly (readingFunctor input) where
  assembleObject := assembleObject
  readAssembledIso object := eqToIso (readObject_assembleObject object)

/-- Primitive protocol separation and assembly satisfy the general reconstruction input. -/
def reconstructionData (input : ProtocolFamilyInput.{u}) :
    ReconstructionData (readingFunctor input) where
  separation := homSeparation input
  homAssembly := homAssembly input
  objectAssembly := objectAssembly input

/-- Reading and direct assembly are inverse on every semantic protocol Hom. -/
@[simp] theorem assemble_read {input : ProtocolFamilyInput.{u}}
    {source target : ProtocolRealization input.schema input.observation}
    (morphism : source ⟶ target) :
    (reconstructionData input).homAssembly.assemble
      ((readingFunctor input).map morphism) = morphism :=
  (reconstructionData input).assemble_map morphism

/-- Direct assembly and reading are inverse on every primitive protocol Hom. -/
@[simp] theorem read_assemble {input : ProtocolFamilyInput.{u}}
    {source target : ProtocolRealization input.schema input.observation}
    (morphism : (readingFunctor input).obj source ⟶
      (readingFunctor input).obj target) :
    (readingFunctor input).map
      ((reconstructionData input).homAssembly.assemble morphism) = morphism :=
  (reconstructionData input).homAssembly.map_assemble morphism

/-- Every primitive protocol Hom has exactly one semantic preimage. -/
theorem existsUnique_preimage {input : ProtocolFamilyInput.{u}}
    {source target : ProtocolRealization input.schema input.observation}
    (morphism : (readingFunctor input).obj source ⟶
      (readingFunctor input).obj target) :
    ∃! global : source ⟶ target, (readingFunctor input).map global = morphism :=
  (reconstructionData input).existsUnique_preimage morphism

/-- Primitive protocol objects are equivalent to all finite semantic realizations. -/
noncomputable def equivalence (input : ProtocolFamilyInput.{u}) :
    ProtocolRealization input.schema input.observation ≌ Object input :=
  (reconstructionData input).equivalence

/-- The forward functor of the protocol equivalence is the primitive reader. -/
@[simp] theorem equivalence_functor (input : ProtocolFamilyInput.{u}) :
    (equivalence input).functor = readingFunctor input := rfl

/-- Primitive state reading agrees with the accepted observed restriction at a vertex. -/
@[simp] theorem observedRestriction_state
    (input : ProtocolFamilyInput.{u})
    (realization : ProtocolRealization input.schema input.observation)
    (vertex : input.schema.Vertex) :
    (readObject realization).State vertex =
      (protocolObservedRestrictionObject input realization).stateDiagram.obj
        (Opposite.op (Opposite.op (input.schema.vertexObject vertex))) := rfl

/-- Primitive edge assembly agrees with the accepted observed restriction evaluation. -/
theorem observedRestriction_edge
    (input : ProtocolFamilyInput.{u})
    (realization : ProtocolRealization input.schema input.observation)
    {source target} (edge : input.schema.Edge source target)
    (state : realization.State source) :
    assembleEdge (readObject realization) edge state =
      (protocolObservedRestrictionObject input realization).stateDiagram.map
        (input.schema.edgeMorphism edge).op.op state := by
  exact congrFun (IndependentCarrierGraph.assemble_read _ _
    (realization.edgeAction edge)) state

/-- Primitive edge assembly along every existing path agrees with the observed restriction. -/
theorem observedRestriction_path
    (input : ProtocolFamilyInput.{u})
    (realization : ProtocolRealization input.schema input.observation)
    {source target} (path : Quiver.Path source target)
    (state : realization.State source) :
    input.schema.evaluatePath (assembleEdge (readObject realization)) path state =
      (protocolObservedRestrictionObject input realization).stateDiagram.map
        (input.schema.pathMorphism path).op.op state := by
  change input.schema.evaluatePath
      (fun {source target} (edge : input.schema.Edge source target) =>
        IndependentCarrierGraph.assemble (realization.State source)
          (realization.State target)
          (IndependentCarrierGraph.read _ _ (realization.edgeAction edge))
          (IndependentCarrierGraph.read_isLawful _ _
            (realization.edgeAction edge))) path state =
    (protocolObservedRestrictionObject input realization).stateDiagram.map
      (input.schema.pathMorphism path).op.op state
  have edgeAssembly :
      (fun {source target} (edge : input.schema.Edge source target) =>
        IndependentCarrierGraph.assemble (realization.State source)
          (realization.State target)
          (IndependentCarrierGraph.read _ _ (realization.edgeAction edge))
          (IndependentCarrierGraph.read_isLawful _ _
            (realization.edgeAction edge))) =
        (fun {source target} (edge : input.schema.Edge source target) =>
          realization.edgeAction edge) := by
    funext source target edge state
    exact congrFun (IndependentCarrierGraph.assemble_read _ _
      (realization.edgeAction edge)) state
  rw [edgeAssembly, protocolEvaluatePath_eq_pathAction]
  rfl

/-- Primitive observation assembly agrees with the accepted observed restriction map. -/
theorem observedRestriction_observation
    (input : ProtocolFamilyInput.{u})
    (realization : ProtocolRealization input.schema input.observation)
    (vertex : input.schema.Vertex) (state : realization.State vertex) :
    assembleObservation (readObject realization) vertex state =
      (protocolObservedRestrictionObject input realization).observe.app
        (Opposite.op (Opposite.op (input.schema.vertexObject vertex))) state := by
  exact congrFun (IndependentCarrierGraph.assemble_read _ _
    (realization.observe vertex)) state

/-- Primitive vertex-map assembly agrees with the accepted observed restriction map. -/
theorem observedRestriction_map
    (input : ProtocolFamilyInput.{u})
    {source target : ProtocolRealization input.schema input.observation}
    (morphism : source ⟶ target) (vertex : input.schema.Vertex)
    (state : source.State vertex) :
    (readHom morphism).component vertex state =
      (protocolObservedRestrictionMap input
        (closedFamilyProtocolHom morphism)).stateMap.app
          (Opposite.op (Opposite.op (input.schema.vertexObject vertex))) state := by
  exact congrFun (IndependentCarrierGraph.assemble_read _ _
    ((ProtocolRealization.res morphism).component vertex)) state

/-- Every protocol object formula has finite derived and primitive support. -/
theorem objectFormula_support_finite
    (input : ProtocolFamilyInput.{u})
    (formula : IndependentFiniteLawFormula.BoolFormula.{u + 1, 0}
      (ObjectLawQuery input)) :
    Finite formula.support ∧ Finite (objectFormulaBaseSupport input formula) :=
  ⟨IndependentFiniteLawFormula.BoolFormula.support_finite _, inferInstance⟩

/-- Every protocol Hom formula has finite derived and primitive support. -/
theorem homFormula_support_finite
    (input : ProtocolFamilyInput.{u})
    (formula : IndependentFiniteLawFormula.BoolFormula.{u + 1, 0}
      (HomLawQuery input)) :
    Finite formula.support ∧ Finite (homFormulaBaseSupport input formula) :=
  ⟨IndependentFiniteLawFormula.BoolFormula.support_finite _, inferInstance⟩

/-- Object relation formulas preserve evaluation from their exact primitive support. -/
theorem relationFormula_evaluate_iff_of_support
    {input : ProtocolFamilyInput.{u}} (object : Object input)
    (relation : input.schema.RelationIndex)
    (state : object.State (input.schema.relationSource relation))
    (second : ObjectTable input)
    (agree : ∀ query ∈ objectFormulaBaseSupport input
      (relationFormula input object.table (fun edge => object.edge_lawful edge)
        relation state), object.table query = second query) :
    (relationFormula input object.table (fun edge => object.edge_lawful edge)
      relation state).evaluate (objectLawTable object.table) ↔
    (relationFormula input object.table (fun edge => object.edge_lawful edge)
      relation state).evaluate (objectLawTable second) :=
  objectFormula_evaluate_iff_of_base_support input _ object.table second agree

/-- Object observation formulas preserve evaluation from their exact primitive support. -/
theorem observationFormula_evaluate_iff_of_support
    {input : ProtocolFamilyInput.{u}} (object : Object input)
    {source target} (edge : input.schema.Edge source target)
    (state : object.State source) (second : ObjectTable input)
    (agree : ∀ query ∈ objectFormulaBaseSupport input
      (observationFormula input object.table (fun edge => object.edge_lawful edge)
        (fun vertex => object.observe_lawful vertex) edge state),
        object.table query = second query) :
    (observationFormula input object.table (fun edge => object.edge_lawful edge)
      (fun vertex => object.observe_lawful vertex) edge state).evaluate
        (objectLawTable object.table) ↔
    (observationFormula input object.table (fun edge => object.edge_lawful edge)
      (fun vertex => object.observe_lawful vertex) edge state).evaluate
        (objectLawTable second) :=
  objectFormula_evaluate_iff_of_base_support input _ object.table second agree

/-- Edge-preservation formulas are equivalent to the assembled generator square at a point. -/
theorem edgePreservationFormula_evaluate_iff
    {input : ProtocolFamilyInput.{u}} {source target : Object input}
    (morphism : Hom source target) {v w} (edge : input.schema.Edge v w)
    (state : source.State v) (image : target.State v)
    (sourceNext : source.State w) (targetNext : target.State w) :
    (edgePreservationFormula input source.table target.table edge
      state image sourceNext targetNext).evaluate
        (homLawTable source.table target.table morphism.table) ↔
      ((morphism.table (.map v (.edge _ _ state image)) = true ∧
          (source.table (.edge edge (.edge _ _ state sourceNext))).down = true) ∧
        (target.table (.edge edge (.edge _ _ image targetNext))).down = true →
        morphism.component w sourceNext = targetNext) := by
  constructor
  · intro formula premise
    exact (morphism.edge_iff w sourceNext targetNext).mp
      (formula.2.2.2.2 premise)
  · intro rule
    exact ⟨source.carrier_selected v, target.carrier_selected v,
      source.carrier_selected w, target.carrier_selected w,
      fun premise =>
        (morphism.edge_iff w sourceNext targetNext).mpr (rule premise)⟩

/-- Observation-preservation formulas are equivalent to the assembled vertex square. -/
theorem observationPreservationFormula_evaluate_iff
    {input : ProtocolFamilyInput.{u}} {source target : Object input}
    (morphism : Hom source target) (vertex : input.schema.Vertex)
    (state : source.State vertex) (image : target.State vertex)
    (value : input.observation.obj (input.schema.vertexObject vertex)) :
    (observationPreservationFormula input source.table target.table vertex
      state image value).evaluate
        (homLawTable source.table target.table morphism.table) ↔
      (morphism.table (.map vertex (.edge _ _ state image)) = true ∧
        (source.table (.observe vertex (.edge _ _ state value))).down = true →
        assembleObservation target vertex image = value) := by
  constructor
  · intro formula premise
    exact (observe_edge_iff target vertex image value).mp (formula.2.2 premise)
  · intro rule
    exact ⟨source.carrier_selected vertex, target.carrier_selected vertex,
      fun premise =>
        (observe_edge_iff target vertex image value).mpr (rule premise)⟩

/-- Flipping the sole edge in the accepted negative fixture gives a lawful graph table. -/
def togglingObjectTable : ObjectTable togglingProtocolInput := by
  intro query
  cases query with
  | stateCarrier _ => exact Bool
  | edge _ query =>
      exact ULift.up (IndependentCarrierGraph.read Bool Bool (fun state => !state) query)
  | observe _ query =>
      exact ULift.up (IndependentCarrierGraph.read Bool PUnit
        (fun _ => PUnit.unit) query)

/-- The toggling fixture's named-edge graph is lawful independently of its path law. -/
theorem togglingEdgeLawful {source target}
    (edge : togglingProtocolInput.schema.Edge source target) :
    IndependentCarrierGraph.IsLawful
      (State togglingObjectTable source) (State togglingObjectTable target)
      (edgeTable togglingObjectTable edge) :=
  IndependentCarrierGraph.read_isLawful Bool Bool (fun state => !state)

/-- The existing toggling fixture is rejected by the primitive path-relation formula. -/
theorem togglingRelationFormula_rejected :
    ¬ (relationFormula togglingProtocolInput togglingObjectTable
      (fun edge => togglingEdgeLawful edge) PUnit.unit false).evaluate
        (objectLawTable togglingObjectTable) := by
  rw [relationFormula_evaluate_iff_raw]
  change ¬ (false = assembleEdgeAction togglingObjectTable
    (fun edge => togglingEdgeLawful edge)
    (show togglingProtocolInput.schema.Edge TogglingProtocolVertex.point
      TogglingProtocolVertex.point from PUnit.unit) false)
  intro equality
  have toggled : assembleEdgeAction togglingObjectTable
      (fun edge => togglingEdgeLawful edge)
      (show togglingProtocolInput.schema.Edge TogglingProtocolVertex.point
        TogglingProtocolVertex.point from PUnit.unit) false = true :=
    congrFun (IndependentCarrierGraph.assemble_read Bool Bool
      (fun state => !state)) false
  exact Bool.noConfusion (equality.trans toggled)

/-- Infinite-state raw protocol table whose edge and observation maps are identities or constants. -/
def infiniteProtocolTable : ObjectTable togglingProtocolInput := by
  intro query
  cases query with
  | stateCarrier _ => exact Nat
  | edge _ query =>
      exact ULift.up (IndependentCarrierGraph.read Nat Nat id query)
  | observe _ query =>
      exact ULift.up (IndependentCarrierGraph.read Nat PUnit
        (fun _ => PUnit.unit) query)

/-- The infinite fixture's edge graph is lawful. -/
theorem infiniteProtocolEdgeLawful {source target}
    (edge : togglingProtocolInput.schema.Edge source target) :
    IndependentCarrierGraph.IsLawful
      (State infiniteProtocolTable source) (State infiniteProtocolTable target)
      (edgeTable infiniteProtocolTable edge) :=
  IndependentCarrierGraph.read_isLawful Nat Nat id

/-- The infinite fixture's observation graph is lawful. -/
theorem infiniteProtocolObserveLawful (vertex : togglingProtocolInput.schema.Vertex) :
    IndependentCarrierGraph.IsLawful
      (State infiniteProtocolTable vertex)
      (togglingProtocolInput.observation.obj
        (togglingProtocolInput.schema.vertexObject vertex))
      (observeTable infiniteProtocolTable vertex) :=
  IndependentCarrierGraph.read_isLawful Nat PUnit (fun _ => PUnit.unit)

/-- The infinite fixture satisfies the path relation formula at every state. -/
theorem infiniteProtocol_relation_formula (state : Nat) :
    (relationFormula togglingProtocolInput infiniteProtocolTable
      (fun edge => infiniteProtocolEdgeLawful edge) PUnit.unit state).evaluate
        (objectLawTable infiniteProtocolTable) := by
  apply (relationFormula_evaluate_iff_raw infiniteProtocolTable
    (fun edge => infiniteProtocolEdgeLawful edge) PUnit.unit state).mpr
  change state = assembleEdgeAction infiniteProtocolTable
    (fun edge => infiniteProtocolEdgeLawful edge)
    (show togglingProtocolInput.schema.Edge TogglingProtocolVertex.point
      TogglingProtocolVertex.point from PUnit.unit) state
  exact (congrFun (IndependentCarrierGraph.assemble_read Nat Nat id) state).symm

/-- The infinite fixture satisfies every named-edge observation formula. -/
theorem infiniteProtocol_observation_formula
    {source target} (edge : togglingProtocolInput.schema.Edge source target)
    (state : State infiniteProtocolTable source) :
    (observationFormula togglingProtocolInput infiniteProtocolTable
      (fun edge => infiniteProtocolEdgeLawful edge)
      infiniteProtocolObserveLawful edge state).evaluate
        (objectLawTable infiniteProtocolTable) := by
  apply (observationFormula_evaluate_iff_raw infiniteProtocolTable
    (fun edge => infiniteProtocolEdgeLawful edge)
    infiniteProtocolObserveLawful edge state).mpr
  rfl

/-- The infinite fixture is rejected only by the vertex-state list-cover condition. -/
theorem infiniteProtocol_not_stateCover :
    ¬ StateCover infiniteProtocolTable TogglingProtocolVertex.point := by
  rw [stateCover_iff_finite]
  exact (Infinite.not_finite : ¬ Finite Nat)

/-- A false expected target-observation cell rejects the object observation square. -/
theorem observationFormula_rejected
    {input : ProtocolFamilyInput.{u}} (table : ObjectTable input)
    (edgeLawful : ∀ {source target} (edge : input.schema.Edge source target),
      IndependentCarrierGraph.IsLawful (State table source) (State table target)
        (edgeTable table edge))
    (observeLawful : ∀ vertex,
      IndependentCarrierGraph.IsLawful (State table vertex)
        (input.observation.obj (input.schema.vertexObject vertex))
        (observeTable table vertex))
    {source target} (edge : input.schema.Edge source target)
    (state : State table source)
    (targetFalse : observeTable table target
      (.edge _ _ (assembleEdgeAction table edgeLawful edge state)
        (input.observation.map (input.schema.edgeMorphism edge)
          (assembleObserve table observeLawful source state))) = false) :
    ¬ (observationFormula input table edgeLawful observeLawful edge state).evaluate
        (objectLawTable table) := by
  intro evaluation
  have targetTrue := evaluation.2.2.2.2
  exact Bool.noConfusion (targetFalse.symm.trans targetTrue)

/-- A false target-observation cell rejects an otherwise firing observation formula. -/
theorem observationPreservationFormula_rejected
    {input : ProtocolFamilyInput.{u}}
    (sourceTable targetTable : ObjectTable input) (maps : HomTable input)
    (vertex : input.schema.Vertex)
    (state : State sourceTable vertex) (image : State targetTable vertex)
    (value : input.observation.obj (input.schema.vertexObject vertex))
    (mapTrue : maps (.map vertex (.edge _ _ state image)) = true)
    (sourceTrue : (sourceTable (.observe vertex (.edge _ _ state value))).down = true)
    (targetFalse : (targetTable (.observe vertex (.edge _ _ image value))).down = false) :
    ¬ (observationPreservationFormula input sourceTable targetTable vertex
      state image value).evaluate (homLawTable sourceTable targetTable maps) := by
  intro evaluation
  have targetTrue := evaluation.2.2 ⟨mapTrue, sourceTrue⟩
  exact Bool.noConfusion (targetFalse.symm.trans targetTrue)

/-- A false target vertex-map cell rejects an otherwise firing edge formula. -/
theorem edgePreservationFormula_rejected
    {input : ProtocolFamilyInput.{u}}
    (sourceTable targetTable : ObjectTable input) (maps : HomTable input)
    {v w} (edge : input.schema.Edge v w)
    (state : State sourceTable v) (image : State targetTable v)
    (sourceNext : State sourceTable w) (targetNext : State targetTable w)
    (mapTrue : maps (.map v (.edge _ _ state image)) = true)
    (sourceEdgeTrue : (sourceTable (.edge edge (.edge _ _ state sourceNext))).down = true)
    (targetEdgeTrue : (targetTable (.edge edge (.edge _ _ image targetNext))).down = true)
    (nextFalse : maps (.map w (.edge _ _ sourceNext targetNext)) = false) :
    ¬ (edgePreservationFormula input sourceTable targetTable edge
      state image sourceNext targetNext).evaluate
        (homLawTable sourceTable targetTable maps) := by
  intro evaluation
  have nextTrue := evaluation.2.2.2.2
    ⟨⟨mapTrue, sourceEdgeTrue⟩, targetEdgeTrue⟩
  exact Bool.noConfusion (nextFalse.symm.trans nextTrue)

/-- Two-state presentation of the accepted toggling schema with identity edge action. -/
def twoStateProtocolPresentation :
    ProtocolPresentation togglingProtocolSchema togglingProtocolObservation where
  card _ := 2
  edgeTable _ := id
  relation_compatibility _ := by funext state; rfl
  observationValue _ _ := PUnit.unit
  observation_edge _ := by funext state; rfl

/-- One-state presentation of the same accepted toggling schema. -/
def oneStateProtocolPresentation :
    ProtocolPresentation togglingProtocolSchema togglingProtocolObservation where
  card _ := 1
  edgeTable _ := id
  relation_compatibility _ := by funext state; rfl
  observationValue _ _ := PUnit.unit
  observation_edge _ := by funext state; rfl

/-- A noninvertible generator map from two states to one state. -/
def twoToOnePresentationHom :
    twoStateProtocolPresentation ⟶ oneStateProtocolPresentation where
  component vertex _ := ⟨0, by cases vertex; decide⟩
  edge_naturality _ := by funext state; rfl
  observation_naturality _ := by funext state; rfl

/-- The accepted semantic Hom induced by the two-to-one generator map. -/
def twoToOneProtocolHom :
    ProtocolPresentation.decoderObject twoStateProtocolPresentation ⟶
      ProtocolPresentation.decoderObject oneStateProtocolPresentation :=
  ProtocolPresentation.decoderMap twoToOnePresentationHom

/-- The primitive reader contains the noninvertible Hom between distinct state types. -/
def twoToOnePrimitiveHom :
    Hom (readObject (input := togglingProtocolInput)
      (ProtocolPresentation.decoderObject twoStateProtocolPresentation))
      (readObject (input := togglingProtocolInput)
        (ProtocolPresentation.decoderObject oneStateProtocolPresentation)) :=
  readHom (input := togglingProtocolInput) twoToOneProtocolHom

/-- The two-to-one primitive Hom component is not injective. -/
theorem twoToOnePrimitiveHom_not_injective :
    ¬ Function.Injective
      (twoToOnePrimitiveHom.component TogglingProtocolVertex.point) := by
  intro injective
  have imageEquality : twoToOnePrimitiveHom.component TogglingProtocolVertex.point
      (ULift.up (0 : Fin 2)) =
      twoToOnePrimitiveHom.component TogglingProtocolVertex.point
        (ULift.up (1 : Fin 2)) := rfl
  exact (show ULift.up (0 : Fin 2) ≠ ULift.up (1 : Fin 2) by decide)
    (injective imageEquality)

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentProtocolPrimitiveReconstruction

end IndependentProtocolPrimitiveReconstruction

end


end AAT.AG.LocalSemanticReconstruction
