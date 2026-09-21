import ResearchLean.AG.LocalSemanticReconstruction.IndependentCarrierGraphReadings
import ResearchLean.AG.LocalSemanticReconstruction.IndependentFiniteFragments
import ResearchLean.AG.LocalSemanticReconstruction.IndependentFiniteGraphLawFormula
import ResearchLean.AG.LocalSemanticReconstruction.IndependentFiniteLawFormula
import ResearchLean.AG.LocalSemanticReconstruction.LensFiberModelEquivalence
import ResearchLean.AG.LocalSemanticReconstruction.LensSemanticFiniteDetermination
import ResearchLean.AG.LocalSemanticReconstruction.LocalReconstructionEquivalence
import Formal.Util.AssertStandardAxioms

/-!
# Primitive reconstruction of total lenses

For a fixed `LensFamilyInput`, this module declares the lens queries before a
state carrier is selected.  Compatible finite fragments contain the carrier
reference cell and the candidate graphs for `get` and every fixed-view `put`.
The three total-lens laws are closed `BoolFormula` instances at fixed points,
and the reference fiber is the subtype selected by the reference `get` edge.

Local Homs contain one candidate state-map graph and closed formulas for
`get` and `put` preservation.  Identity and composition use
`IndependentCarrierGraph.identity` and `IndependentCarrierGraph.compose`
directly.  Reading and assembly cover all semantic lens objects and all
get/put-preserving maps, including noninvertible maps.

## Implementation notes

The object and Hom records contain finite fragment families and their point laws; they
do not contain `LensRealization`, `LensRealization.Hom`, decoder membership, or
extension data.  Native objects and Homs occur only in the two reading and
assembly directions.  The fixed GOAL B equivalence is obtained by one use of
`LocalReconstructionEquivalence.ReconstructionData.equivalence` after Hom
separation, Hom assembly, and object assembly have been proved separately.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory
open AAT.AG.RealizationReconstruction
open LocalReconstructionEquivalence

noncomputable section

namespace IndependentLensPrimitiveReconstruction

universe u

/-- Candidate carrier graph queries specialized to one lens universe. -/
abbrev GraphQuery := IndependentCarrierGraph.Query.{u, u}

/-- Boolean candidate carrier graph tables specialized to one lens universe. -/
abbrev GraphTable := IndependentCarrierGraph.Table.{u, u}

/-- A fixed lens-object query tags a candidate graph cell by its semantic
role.  The query type depends only on the parameter-owned view type. -/
inductive ObjectQuery (input : LensFamilyInput.{u}) where
  /-- The unique state-carrier declaration cell. -/
  | stateCarrier
  /-- One candidate edge of the `get` graph. -/
  | get (query : GraphQuery.{u})
  /-- One candidate edge of the `put` graph at a fixed view. -/
  | put (view : input.View) (query : GraphQuery.{u})

/-- The dependent value type of each primitive object query. -/
def ObjectValue {input : LensFamilyInput.{u}} : ObjectQuery input → Type (u + 1)
  | .stateCarrier => Type u
  | .get _ => ULift.{u + 1, 0} Bool
  | .put _ _ => ULift.{u + 1, 0} Bool

/-- The dependent table containing the carrier declaration and graph cells. -/
abbrev ObjectTable (input : LensFamilyInput.{u}) :=
  (query : ObjectQuery input) → ObjectValue query

/-- Finite object-table fragments over the fixed query declaration. -/
abbrev ObjectFragment {input : LensFamilyInput.{u}} (D : Finset (ObjectQuery input)) :=
  IndependentFiniteFragments.Fragment (fun query : ObjectQuery input => ObjectValue query) D

/-- A family of finite object-table fragments. -/
abbrev ObjectFragmentFamily (input : LensFamilyInput.{u}) :=
  IndependentFiniteFragments.FragmentFamily
    (fun query : ObjectQuery input => ObjectValue query)

/-- Compatibility of finite object-table fragments. -/
abbrev ObjectCompatible {input : LensFamilyInput.{u}}
    (family : ObjectFragmentFamily input) :=
  IndependentFiniteFragments.Compatible family

/-- Restrict an object table to every finite query set. -/
def objectFragments {input : LensFamilyInput.{u}} (table : ObjectTable input) :
    ObjectFragmentFamily input :=
  IndependentFiniteFragments.fragments table

/-- Glue compatible object fragments through singleton cells. -/
def objectGlue {input : LensFamilyInput.{u}} (family : ObjectFragmentFamily input) :
    ObjectTable input :=
  IndependentFiniteFragments.glue family

/-- Object-table restrictions are compatible. -/
theorem objectFragments_compatible {input : LensFamilyInput.{u}} (table : ObjectTable input) :
    ObjectCompatible (objectFragments table) :=
  IndependentFiniteFragments.fragments_compatible table

/-- Gluing all restrictions recovers the object table. -/
theorem objectGlue_fragments {input : LensFamilyInput.{u}} (table : ObjectTable input) :
    objectGlue (objectFragments table) = table :=
  IndependentFiniteFragments.glue_fragments table

/-- Compatible object fragments are recovered from their glued table. -/
theorem objectFragments_glue {input : LensFamilyInput.{u}}
    (family : ObjectFragmentFamily input) (compatible : ObjectCompatible family) :
    objectFragments (objectGlue family) = family :=
  IndependentFiniteFragments.fragments_glue family compatible

/-- Restrict the tagged object table to the candidate `get` graph. -/
def getTable {input : LensFamilyInput.{u}} (table : ObjectTable input) : GraphTable.{u} :=
  fun query => (table (.get query)).down

/-- Restrict the tagged object table to the candidate `put` graph at one view. -/
def putTable {input : LensFamilyInput.{u}} (table : ObjectTable input)
    (view : input.View) : GraphTable.{u} :=
  fun query => (table (.put view query)).down

/-- Embed a carrier-graph query into the object `get` cells. -/
def getEmbed (input : LensFamilyInput.{u}) : GraphQuery.{u} → ObjectQuery input :=
  ObjectQuery.get

/-- Embed a carrier-graph query into one fixed-view object `put` row. -/
def putEmbed (input : LensFamilyInput.{u}) (view : input.View) :
    GraphQuery.{u} → ObjectQuery input :=
  ObjectQuery.put view

/-- Boolean law queries derived from the dependent primitive object table. -/
inductive ObjectLawQuery (input : LensFamilyInput.{u}) where
  /-- Compare one candidate type with the declared state carrier. -/
  | carrierMatches (candidate : Type u)
  /-- Read one candidate `get` edge. -/
  | get (query : GraphQuery.{u})
  /-- Read one fixed-view candidate `put` edge. -/
  | put (view : input.View) (query : GraphQuery.{u})

/-- Boolean table used only to evaluate derived object-law formulas. -/
abbrev ObjectLawTable (input : LensFamilyInput.{u}) := ObjectLawQuery input → Bool

/-- Derive law cells from the unique carrier declaration and the base graph cells. -/
def objectLawTable {input : LensFamilyInput.{u}} (table : ObjectTable input) :
    ObjectLawTable input := by
  classical
  intro query
  cases query with
  | carrierMatches candidate => exact decide (candidate = table .stateCarrier)
  | get graphQuery => exact (table (.get graphQuery)).down
  | put view graphQuery => exact (table (.put view graphQuery)).down

/-- The selected carrier-reference cell as a closed Boolean formula. -/
def carrierFormula (input : LensFamilyInput.{u}) (C : Type u) :
    IndependentFiniteLawFormula.BoolFormula.{u + 1, 0} (ObjectLawQuery input) :=
  .cell (.carrierMatches C) true

/-- Raw evaluation of the carrier-reference formula. -/
theorem carrierFormula_evaluate_raw (input : LensFamilyInput.{u}) (C : Type u)
    (table : ObjectLawTable input) :
    (carrierFormula input C).evaluate table ↔ table (.carrierMatches C) = true := Iff.rfl

/-- A derived match cell is true exactly for the declared carrier type. -/
theorem objectLawTable_carrierMatches_iff {input : LensFamilyInput.{u}}
    (table : ObjectTable input) (C : Type u) :
    objectLawTable table (.carrierMatches C) = true ↔ C = table .stateCarrier := by
  classical
  simp [objectLawTable]

/-- Carrier-match cells depend only on the single base carrier declaration. -/
theorem objectLawTable_carrierMatches_eq_of_stateCarrier_eq
    {input : LensFamilyInput.{u}} {first second : ObjectTable input}
    (equality : first .stateCarrier = second .stateCarrier) (C : Type u) :
    objectLawTable first (.carrierMatches C) =
      objectLawTable second (.carrierMatches C) := by
  simp only [objectLawTable]
  rw [equality]

/-- Map a derived object-law query to the primitive cell that determines it. -/
def objectLawQueryBase (input : LensFamilyInput.{u}) :
    ObjectLawQuery input → ObjectQuery input
  | .carrierMatches _ => .stateCarrier
  | .get query => .get query
  | .put view query => .put view query

/-- Primitive cells needed to evaluate one finite object-law formula. -/
def objectFormulaBaseSupport (input : LensFamilyInput.{u})
    (formula : IndependentFiniteLawFormula.BoolFormula.{u + 1, 0}
      (ObjectLawQuery input)) : Finset (ObjectQuery input) := by
  classical
  exact formula.support.image (objectLawQueryBase input)

/-- Agreement on the primitive object cells supporting a formula preserves
evaluation of its derived law table. -/
theorem objectFormula_evaluate_iff_of_base_support
    (input : LensFamilyInput.{u})
    (formula : IndependentFiniteLawFormula.BoolFormula.{u + 1, 0}
      (ObjectLawQuery input))
    (first second : ObjectTable input)
    (agree : ∀ query ∈ objectFormulaBaseSupport input formula,
      first query = second query) :
    formula.evaluate (objectLawTable first) ↔
      formula.evaluate (objectLawTable second) := by
  apply IndependentFiniteLawFormula.BoolFormula.evaluate_iff_of_support
  intro query member
  have baseMember : objectLawQueryBase input query ∈
      objectFormulaBaseSupport input formula := by
    classical
    exact Finset.mem_image.mpr ⟨query, member, rfl⟩
  cases query with
  | carrierMatches candidate =>
      exact objectLawTable_carrierMatches_eq_of_stateCarrier_eq
        (agree .stateCarrier baseMember) candidate
  | get graphQuery =>
      exact congrArg ULift.down (agree (.get graphQuery) baseMember)
  | put view graphQuery =>
      exact congrArg ULift.down (agree (.put view graphQuery) baseMember)

/-- The finite formula for `get(c) = v -> put_v(c) = c`. -/
def putGetFormula (input : LensFamilyInput.{u}) (C : Type u)
    (c : C) (view : input.View) :
    IndependentFiniteLawFormula.BoolFormula.{u + 1, 0} (ObjectLawQuery input) :=
  .and (carrierFormula input C)
    (.implies
      (.cell (.get (.edge C input.View c view)) true)
      (.cell (.put view (.edge C C c c)) true))

/-- The finite formula for `put_v(c) = d -> get(d) = v`. -/
def getPutFormula (input : LensFamilyInput.{u}) (C : Type u)
    (c d : C) (view : input.View) :
    IndependentFiniteLawFormula.BoolFormula.{u + 1, 0} (ObjectLawQuery input) :=
  .and (carrierFormula input C)
    (.implies
      (.cell (.put view (.edge C C c d)) true)
      (.cell (.get (.edge C input.View d view)) true))

/-- The finite formula for two consecutive updates to retain the last view. -/
def putPutFormula (input : LensFamilyInput.{u}) (C : Type u)
    (c d e : C) (first second : input.View) :
    IndependentFiniteLawFormula.BoolFormula.{u + 1, 0} (ObjectLawQuery input) :=
  .and (carrierFormula input C)
    (.implies
      (.and
        (.cell (.put first (.edge C C c d)) true)
        (.cell (.put second (.edge C C d e)) true))
      (.cell (.put second (.edge C C c e)) true))

/-- Raw-table evaluation of one put-get formula. -/
theorem putGetFormula_evaluate_raw (input : LensFamilyInput.{u}) (C : Type u)
    (c : C) (view : input.View) (table : ObjectLawTable input) :
    (putGetFormula input C c view).evaluate table ↔
      table (.carrierMatches C) = true ∧
        (table (.get (.edge C input.View c view)) = true →
          table (.put view (.edge C C c c)) = true) := Iff.rfl

/-- Raw-table evaluation of one get-put formula. -/
theorem getPutFormula_evaluate_raw (input : LensFamilyInput.{u}) (C : Type u)
    (c d : C) (view : input.View) (table : ObjectLawTable input) :
    (getPutFormula input C c d view).evaluate table ↔
      table (.carrierMatches C) = true ∧
        (table (.put view (.edge C C c d)) = true →
          table (.get (.edge C input.View d view)) = true) := Iff.rfl

/-- Raw-table evaluation of one put-put formula. -/
theorem putPutFormula_evaluate_raw (input : LensFamilyInput.{u}) (C : Type u)
    (c d e : C) (first second : input.View) (table : ObjectLawTable input) :
    (putPutFormula input C c d e first second).evaluate table ↔
      table (.carrierMatches C) = true ∧
        (table (.put first (.edge C C c d)) = true ∧
            table (.put second (.edge C C d e)) = true →
          table (.put second (.edge C C c e)) = true) := Iff.rfl

/-- The reference fiber selected directly by the primitive `get` graph. -/
abbrev PrimitiveFiber (input : LensFamilyInput.{u}) (C : Type u)
    (table : ObjectTable input) :=
  {c : C // (table (.get (.edge C input.View c input.reference))).down = true}

/-- A finite list covering every state in the primitive reference fiber. -/
def FiberCover (input : LensFamilyInput.{u}) (C : Type u)
    (table : ObjectTable input) : Prop :=
  ∃ states : List (PrimitiveFiber input C table), ∀ state, state ∈ states

/-- A list cover is equivalent to finiteness of the primitive reference fiber. -/
theorem fiberCover_iff_finite (input : LensFamilyInput.{u}) (C : Type u)
    (table : ObjectTable input) :
    FiberCover input C table ↔ Finite (PrimitiveFiber input C table) := by
  constructor
  · rintro ⟨states, cover⟩
    classical
    letI : Fintype (PrimitiveFiber input C table) :=
      ⟨states.toFinset, fun state => by simpa using cover state⟩
    exact Finite.of_fintype _
  · intro finite
    letI : Finite (PrimitiveFiber input C table) := finite
    letI := Fintype.ofFinite (PrimitiveFiber input C table)
    exact ⟨Finset.univ.toList, fun state => by simp⟩

/-- A fixed-GOAL A/B primitive lens object.  Its fields are exactly one state
carrier reference, compatible finite fragments, graph-row formula instances,
the three finite point formulas, and a list cover of the primitive fiber. -/
structure Object (input : LensFamilyInput.{u}) where
  /-- Finite fragments containing all primitive object cells. -/
  family : ObjectFragmentFamily input
  /-- The finite fragments agree under inclusions. -/
  compatible : ObjectCompatible family
  /-- Closed graph-row instances for the selected `get` graph. -/
  get_instances : IndependentFiniteGraphLawFormula.CarrierRows.Instances
    (fun query => (objectGlue family (.get query)).down) id
      (objectGlue family .stateCarrier) input.View
  /-- Closed graph-row instances for every fixed-view `put` graph. -/
  put_instances : ∀ view, IndependentFiniteGraphLawFormula.CarrierRows.Instances
    (fun query => (objectGlue family (.put view query)).down) id
      (objectGlue family .stateCarrier) (objectGlue family .stateCarrier)
  /-- Every fixed-point put-get formula evaluates from the primitive table. -/
  put_get_formula : ∀ c view,
    (putGetFormula input (objectGlue family .stateCarrier) c view).evaluate
      (objectLawTable (objectGlue family))
  /-- Every fixed-point get-put formula evaluates from the primitive table. -/
  get_put_formula : ∀ c d view,
    (getPutFormula input (objectGlue family .stateCarrier) c d view).evaluate
      (objectLawTable (objectGlue family))
  /-- Every fixed-point put-put formula evaluates from the primitive table. -/
  put_put_formula : ∀ c d e first second,
    (putPutFormula input (objectGlue family .stateCarrier) c d e first second).evaluate
      (objectLawTable (objectGlue family))
  /-- A finite list covers the primitive reference-edge subtype. -/
  fiber_cover : FiberCover input (objectGlue family .stateCarrier) (objectGlue family)

namespace Object

variable {input : LensFamilyInput.{u}}

/-- Primitive lens objects are equal when their dependent fragment families agree. -/
@[ext]
theorem ext {first second : Object input}
    (family : first.family = second.family) : first = second := by
  cases first
  cases second
  cases family
  rfl

/-- Glue the primitive object table from its compatible finite fragments. -/
def table (object : Object input) : ObjectTable input := objectGlue object.family

/-- The state carrier is read from the unique dependent declaration cell. -/
def Carrier (object : Object input) : Type u := object.table .stateCarrier

/-- The primitive reference fiber of a local object. -/
abbrev Fiber (object : Object input) :=
  PrimitiveFiber input object.Carrier object.table

/-- The selected carrier-reference cell is true. -/
theorem carrier_selected (object : Object input) :
    objectLawTable object.table (.carrierMatches object.Carrier) = true := by
  exact (objectLawTable_carrierMatches_iff object.table object.Carrier).mpr rfl

/-- Every mismatched carrier-reference candidate is false. -/
theorem carrier_mismatch (object : Object input) (C : Type u)
    (mismatch : C ≠ object.Carrier) :
    objectLawTable object.table (.carrierMatches C) = false := by
  classical
  change C ≠ object.table .stateCarrier at mismatch
  simp [objectLawTable, mismatch]

/-- Carrier-reference cells recognize exactly the selected carrier. -/
theorem carrier_cell_iff (object : Object input) (C : Type u) :
    objectLawTable object.table (.carrierMatches C) = true ↔ C = object.Carrier :=
  objectLawTable_carrierMatches_iff object.table C

/-- The selected `get` graph law follows from its finite row instances. -/
theorem get_lawful (object : Object input) :
    IndependentCarrierGraph.IsLawful object.Carrier input.View (getTable object.table) :=
  (IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances
    (getTable object.table) id object.Carrier input.View).mpr object.get_instances

/-- Each selected fixed-view `put` graph law follows from its finite row instances. -/
theorem put_lawful (object : Object input) (view : input.View) :
    IndependentCarrierGraph.IsLawful object.Carrier object.Carrier
      (putTable object.table view) :=
  (IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances
    (putTable object.table view) id object.Carrier object.Carrier).mpr
      (object.put_instances view)

/-- The stored list cover proves finiteness without adding a structure field or global instance. -/
theorem fiber_finite (object : Object input) : Finite object.Fiber :=
  (fiberCover_iff_finite input object.Carrier object.table).mp object.fiber_cover

end Object

/-- Assemble the primitive `get` graph of a local object. -/
def assembleGet {input : LensFamilyInput.{u}} (object : Object input) :
    object.Carrier → input.View :=
  IndependentCarrierGraph.assemble object.Carrier input.View
    (getTable object.table) object.get_lawful

/-- Assemble one fixed-view primitive `put` graph. -/
def assemblePut {input : LensFamilyInput.{u}} (object : Object input)
    (state : object.Carrier) (view : input.View) : object.Carrier :=
  IndependentCarrierGraph.assemble object.Carrier object.Carrier
    (putTable object.table view) (object.put_lawful view) state

/-- No-unfold API for a true primitive `get` edge. -/
theorem get_edge_iff {input : LensFamilyInput.{u}} (object : Object input)
    (state : object.Carrier) (view : input.View) :
    (object.table (.get (.edge object.Carrier input.View state view))).down = true ↔
      assembleGet object state = view := by
  constructor
  · exact IndependentCarrierGraph.assemble_eq_of_edge
      object.Carrier input.View (getTable object.table) object.get_lawful
  · intro equality
    rw [← equality]
    exact IndependentCarrierGraph.edge_assemble
      object.Carrier input.View (getTable object.table) object.get_lawful state

/-- No-unfold API for a true primitive `put` edge. -/
theorem put_edge_iff {input : LensFamilyInput.{u}} (object : Object input)
    (state target : object.Carrier) (view : input.View) :
    (object.table (.put view
      (.edge object.Carrier object.Carrier state target))).down = true ↔
      assemblePut object state view = target := by
  constructor
  · exact IndependentCarrierGraph.assemble_eq_of_edge
      object.Carrier object.Carrier (putTable object.table view)
        (object.put_lawful view)
  · intro equality
    rw [← equality]
    exact IndependentCarrierGraph.edge_assemble
      object.Carrier object.Carrier (putTable object.table view)
        (object.put_lawful view) state

/-- Assemble a primitive local object into the existing semantic lens type.
The three semantic laws are derived from the closed point formulas. -/
def assembleObject {input : LensFamilyInput.{u}} (object : Object input) :
    LensRealization input.View input.reference where
  toLensData :=
    { Carrier := object.Carrier
      get := assembleGet object
      put := assemblePut object }
  condition :=
    { put_get := fun state => by
        apply (put_edge_iff object state state (assembleGet object state)).mp
        exact ((putGetFormula_evaluate_raw input object.Carrier state
          (assembleGet object state) _).mp
            (object.put_get_formula state (assembleGet object state))).2
          (IndependentCarrierGraph.edge_assemble object.Carrier input.View
            (getTable object.table) object.get_lawful state)
      get_put := fun state view => by
        apply (get_edge_iff object (assemblePut object state view) view).mp
        exact ((getPutFormula_evaluate_raw input object.Carrier state
          (assemblePut object state view) view _).mp
            (object.get_put_formula state (assemblePut object state view) view)).2
          (IndependentCarrierGraph.edge_assemble object.Carrier object.Carrier
            (putTable object.table view) (object.put_lawful view) state)
      put_put := fun state first second => by
        symm
        apply (put_edge_iff object state (assemblePut object (assemblePut object state first) second)
          second).mp
        exact ((putPutFormula_evaluate_raw input object.Carrier state
          (assemblePut object state first)
          (assemblePut object (assemblePut object state first) second) first second _).mp
            (object.put_put_formula state (assemblePut object state first)
              (assemblePut object (assemblePut object state first) second) first second)).2
          ⟨IndependentCarrierGraph.edge_assemble object.Carrier object.Carrier
              (putTable object.table first) (object.put_lawful first) state,
            IndependentCarrierGraph.edge_assemble object.Carrier object.Carrier
              (putTable object.table second) (object.put_lawful second)
                (assemblePut object state first)⟩
      finite_fiber := by
        letI : Finite object.Fiber := object.fiber_finite
        let equivalence : object.Fiber ≃
            {state : object.Carrier // assembleGet object state = input.reference} :=
          { toFun := fun state =>
              ⟨state, (get_edge_iff object state input.reference).mp state.property⟩
            invFun := fun state =>
              ⟨state, (get_edge_iff object state input.reference).mpr state.property⟩
            left_inv := fun state => Subtype.ext rfl
            right_inv := fun state => Subtype.ext rfl }
        exact Finite.of_equiv object.Fiber equivalence }

/-- No-unfold API: assembled `get` is the graph assembly. -/
@[simp] theorem assembleObject_get {input : LensFamilyInput.{u}}
    (object : Object input) (state : object.Carrier) :
    (assembleObject object).get state = assembleGet object state := rfl

/-- No-unfold API: assembled `put` is the fixed-view graph assembly. -/
@[simp] theorem assembleObject_put {input : LensFamilyInput.{u}}
    (object : Object input) (state : object.Carrier) (view : input.View) :
    (assembleObject object).put state view = assemblePut object state view := rfl

/-- The primitive fiber is canonically the reference fiber of its assembled
semantic lens. -/
def primitiveFiberEquiv {input : LensFamilyInput.{u}} (object : Object input) :
    object.Fiber ≃ (assembleObject object).Fiber where
  toFun state :=
    ⟨state.val, (get_edge_iff object state.val input.reference).mp state.property⟩
  invFun state :=
    ⟨state.val, (get_edge_iff object state.val input.reference).mpr state.property⟩
  left_inv _state := Subtype.ext rfl
  right_inv _state := Subtype.ext rfl

/-- Read raw lens data into the fixed tagged object table. -/
def readDataTable {input : LensFamilyInput.{u}} (data : LensData input.View) :
    ObjectTable input := by
  intro query
  cases query with
  | stateCarrier => exact data.Carrier
  | get graphQuery =>
      exact ULift.up (IndependentCarrierGraph.read data.Carrier input.View data.get graphQuery)
  | put view graphQuery =>
      exact ULift.up (IndependentCarrierGraph.read data.Carrier data.Carrier
        (fun state => data.put state view) graphQuery)

/-- The read table restricts to the existing `get` graph reader. -/
@[simp] theorem getTable_readDataTable {input : LensFamilyInput.{u}}
    (data : LensData input.View) :
    getTable (readDataTable data) =
      IndependentCarrierGraph.read data.Carrier input.View data.get := rfl

/-- The read table restricts to the existing fixed-view `put` graph reader. -/
@[simp] theorem putTable_readDataTable {input : LensFamilyInput.{u}}
    (data : LensData input.View) (view : input.View) :
    putTable (readDataTable data) view =
      IndependentCarrierGraph.read data.Carrier data.Carrier
        (fun state => data.put state view) := rfl

/-- The reference edges read from a semantic lens are canonically its existing
`LensRealization.Fiber`. -/
def readFiberEquiv {input : LensFamilyInput.{u}}
    (lens : LensRealization input.View input.reference) :
    PrimitiveFiber input lens.Carrier (readDataTable lens.toLensData) ≃ lens.Fiber where
  toFun state :=
    ⟨state, (IndependentCarrierGraph.read_edge lens.Carrier input.View lens.get
      state input.reference).mp state.property⟩
  invFun state :=
    ⟨state, (IndependentCarrierGraph.read_edge lens.Carrier input.View lens.get
      state input.reference).mpr state.property⟩
  left_inv _state := Subtype.ext rfl
  right_inv _state := Subtype.ext rfl

/-- Read an arbitrary semantic lens into the primitive object declaration. -/
def readObject {input : LensFamilyInput.{u}}
    (lens : LensRealization input.View input.reference) : Object input where
  family := objectFragments (readDataTable lens.toLensData)
  compatible := objectFragments_compatible _
  get_instances :=
    (IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances
      (getTable (readDataTable lens.toLensData)) id lens.Carrier input.View).mp
      (IndependentCarrierGraph.read_isLawful _ _ lens.get)
  put_instances view :=
    (IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances
      (putTable (readDataTable lens.toLensData) view) id lens.Carrier lens.Carrier).mp
      (IndependentCarrierGraph.read_isLawful _ _ (fun state => lens.put state view))
  put_get_formula state view := by
    apply (putGetFormula_evaluate_raw input lens.Carrier state view _).mpr
    refine ⟨?_, ?_⟩
    · apply (objectLawTable_carrierMatches_iff _ lens.Carrier).mpr
      rw [objectGlue_fragments]
      rfl
    simp only [objectGlue_fragments]
    change IndependentCarrierGraph.read lens.Carrier input.View lens.get
          (.edge lens.Carrier input.View state view) = true →
        IndependentCarrierGraph.read lens.Carrier lens.Carrier
          (fun current => lens.put current view)
            (.edge lens.Carrier lens.Carrier state state) = true
    intro premise
    apply (IndependentCarrierGraph.read_edge _ _ _ _ _).mpr
    have getEquality :=
      (IndependentCarrierGraph.read_edge _ _ _ _ _).mp premise
    simpa [getEquality] using lens.condition.put_get state
  get_put_formula state target view := by
    apply (getPutFormula_evaluate_raw input lens.Carrier state target view _).mpr
    refine ⟨?_, ?_⟩
    · apply (objectLawTable_carrierMatches_iff _ lens.Carrier).mpr
      rw [objectGlue_fragments]
      rfl
    simp only [objectGlue_fragments]
    change IndependentCarrierGraph.read lens.Carrier lens.Carrier
          (fun current => lens.put current view)
            (.edge lens.Carrier lens.Carrier state target) = true →
        IndependentCarrierGraph.read lens.Carrier input.View lens.get
          (.edge lens.Carrier input.View target view) = true
    intro premise
    apply (IndependentCarrierGraph.read_edge _ _ _ _ _).mpr
    have putEquality :=
      (IndependentCarrierGraph.read_edge _ _ _ _ _).mp premise
    subst target
    exact lens.condition.get_put state view
  put_put_formula state middle target first second := by
    apply (putPutFormula_evaluate_raw input lens.Carrier state middle target first second _).mpr
    refine ⟨?_, ?_⟩
    · apply (objectLawTable_carrierMatches_iff _ lens.Carrier).mpr
      rw [objectGlue_fragments]
      rfl
    simp only [objectGlue_fragments]
    change (IndependentCarrierGraph.read lens.Carrier lens.Carrier
          (fun current => lens.put current first)
            (.edge lens.Carrier lens.Carrier state middle) = true ∧
        IndependentCarrierGraph.read lens.Carrier lens.Carrier
          (fun current => lens.put current second)
            (.edge lens.Carrier lens.Carrier middle target) = true) →
        IndependentCarrierGraph.read lens.Carrier lens.Carrier
          (fun current => lens.put current second)
            (.edge lens.Carrier lens.Carrier state target) = true
    rintro ⟨firstEdge, secondEdge⟩
    apply (IndependentCarrierGraph.read_edge _ _ _ _ _).mpr
    have firstEquality :=
      (IndependentCarrierGraph.read_edge _ _ _ _ _).mp firstEdge
    have secondEquality :=
      (IndependentCarrierGraph.read_edge _ _ _ _ _).mp secondEdge
    subst middle
    subst target
    exact (lens.condition.put_put state first second).symm
  fiber_cover := by
    apply (fiberCover_iff_finite input lens.Carrier _).mpr
    exact Finite.of_equiv lens.Fiber (readFiberEquiv lens).symm

/-- Reading after primitive object assembly recovers the whole tagged table. -/
@[simp] theorem readObject_assembleObject {input : LensFamilyInput.{u}}
    (object : Object input) :
    readObject (assembleObject object) = object := by
  apply Object.ext
  change objectFragments (readDataTable (assembleObject object).toLensData) = object.family
  rw [← objectFragments_glue object.family object.compatible]
  apply congrArg (objectFragments (input := input))
  funext query
  cases query with
  | stateCarrier => rfl
  | get query =>
      apply ULift.ext
      exact congrFun (IndependentCarrierGraph.read_assemble object.Carrier input.View
        (getTable object.table) object.get_lawful) query
  | put view query =>
      apply ULift.ext
      exact congrFun (IndependentCarrierGraph.read_assemble object.Carrier object.Carrier
        (putTable object.table view) (object.put_lawful view)) query

/-- Semantic reading followed by primitive assembly is canonically isomorphic
to the original lens.  Both maps use the identity state function; the graph
round trips discharge the two preservation laws. -/
def assembleObjectReadIso {input : LensFamilyInput.{u}}
    (lens : LensRealization input.View input.reference) :
    assembleObject (readObject lens) ≅ lens where
  hom :=
    { toFun := id
      get_naturality := fun state => by
        exact (congrFun
          (IndependentCarrierGraph.assemble_read lens.Carrier input.View lens.get) state).symm
      put_naturality := fun state view => by
        exact congrFun
          (IndependentCarrierGraph.assemble_read lens.Carrier lens.Carrier
            (fun current => lens.put current view)) state }
  inv :=
    { toFun := id
      get_naturality := fun state => by
        exact congrFun
          (IndependentCarrierGraph.assemble_read lens.Carrier input.View lens.get) state
      put_naturality := fun state view => by
        exact (congrFun
          (IndependentCarrierGraph.assemble_read lens.Carrier lens.Carrier
            (fun current => lens.put current view)) state).symm }
  hom_inv_id := by
    apply LensRealization.Hom.ext
    rfl
  inv_hom_id := by
    apply LensRealization.Hom.ext
    rfl

/-- A fixed Hom-law query tags source-object, target-object, and state-map
cells without storing either completed endpoint or a completed Hom. -/
inductive HomQuery (input : LensFamilyInput.{u}) where
  /-- A source-object derived law cell. -/
  | source (query : ObjectLawQuery input)
  /-- A target-object derived law cell. -/
  | target (query : ObjectLawQuery input)
  /-- A candidate state-map graph cell. -/
  | map (query : GraphQuery.{u})

/-- Primitive Hom queries tag source cells, target cells, and state-map cells. -/
inductive HomPrimitiveQuery (input : LensFamilyInput.{u}) where
  /-- One source-object primitive cell. -/
  | source (query : ObjectQuery input)
  /-- One target-object primitive cell. -/
  | target (query : ObjectQuery input)
  /-- One primitive state-map graph cell. -/
  | map (query : GraphQuery.{u})

/-- The dependent value type for primitive Hom queries. -/
def HomPrimitiveValue {input : LensFamilyInput.{u}} :
    HomPrimitiveQuery input → Type (u + 1)
  | .source query => ObjectValue query
  | .target query => ObjectValue query
  | .map _ => ULift.{u + 1, 0} Bool

/-- A dependent primitive Hom table contains both endpoint tables and one map table. -/
abbrev HomPrimitiveTable (input : LensFamilyInput.{u}) :=
  (query : HomPrimitiveQuery input) → HomPrimitiveValue query

/-- Combine two primitive object tables and a state-map graph table. -/
def homPrimitiveTable {input : LensFamilyInput.{u}}
    (source target : ObjectTable input) (table : GraphTable.{u}) :
    HomPrimitiveTable input
  | .source query => source query
  | .target query => target query
  | .map query => ULift.up (table query)

/-- Map a derived Hom-law query to the primitive cell that determines it. -/
def homLawQueryBase (input : LensFamilyInput.{u}) :
    HomQuery input → HomPrimitiveQuery input
  | .source query => .source (objectLawQueryBase input query)
  | .target query => .target (objectLawQueryBase input query)
  | .map query => .map query

/-- Primitive cells needed to evaluate one finite Hom-law formula. -/
def homFormulaBaseSupport (input : LensFamilyInput.{u})
    (formula : IndependentFiniteLawFormula.BoolFormula.{u + 1, 0}
      (HomQuery input)) : Finset (HomPrimitiveQuery input) := by
  classical
  exact formula.support.image (homLawQueryBase input)

/-- Derive a Boolean Hom-law table from its dependent primitive table. -/
def homPrimitiveLawTable {input : LensFamilyInput.{u}}
    (table : HomPrimitiveTable input) : HomQuery input → Bool := by
  classical
  intro query
  cases query with
  | source objectQuery =>
      cases objectQuery with
      | carrierMatches candidate =>
          exact decide (candidate = table (.source .stateCarrier))
      | get graphQuery => exact (table (.source (.get graphQuery))).down
      | put view graphQuery => exact (table (.source (.put view graphQuery))).down
  | target objectQuery =>
      cases objectQuery with
      | carrierMatches candidate =>
          exact decide (candidate = table (.target .stateCarrier))
      | get graphQuery => exact (table (.target (.get graphQuery))).down
      | put view graphQuery => exact (table (.target (.put view graphQuery))).down
  | map graphQuery => exact (table (.map graphQuery)).down

/-- Agreement on the primitive Hom cells supporting a formula preserves
evaluation of its derived law table. -/
theorem homFormula_evaluate_iff_of_base_support
    (input : LensFamilyInput.{u})
    (formula : IndependentFiniteLawFormula.BoolFormula.{u + 1, 0}
      (HomQuery input))
    (first second : HomPrimitiveTable input)
    (agree : ∀ query ∈ homFormulaBaseSupport input formula,
      first query = second query) :
    formula.evaluate (homPrimitiveLawTable first) ↔
      formula.evaluate (homPrimitiveLawTable second) := by
  classical
  apply IndependentFiniteLawFormula.BoolFormula.evaluate_iff_of_support
  intro query member
  have baseMember : homLawQueryBase input query ∈
      homFormulaBaseSupport input formula := by
    classical
    exact Finset.mem_image.mpr ⟨query, member, rfl⟩
  cases query with
  | source objectQuery =>
      cases objectQuery with
      | carrierMatches candidate =>
          change decide (candidate = first (.source .stateCarrier)) =
            decide (candidate = second (.source .stateCarrier))
          exact congrArg (fun carrier => decide (candidate = carrier))
            (agree (.source .stateCarrier) baseMember)
      | get graphQuery =>
          exact congrArg ULift.down (agree (.source (.get graphQuery)) baseMember)
      | put view graphQuery =>
          exact congrArg ULift.down
            (agree (.source (.put view graphQuery)) baseMember)
  | target objectQuery =>
      cases objectQuery with
      | carrierMatches candidate =>
          change decide (candidate = first (.target .stateCarrier)) =
            decide (candidate = second (.target .stateCarrier))
          exact congrArg (fun carrier => decide (candidate = carrier))
            (agree (.target .stateCarrier) baseMember)
      | get graphQuery =>
          exact congrArg ULift.down (agree (.target (.get graphQuery)) baseMember)
      | put view graphQuery =>
          exact congrArg ULift.down
            (agree (.target (.put view graphQuery)) baseMember)
  | map graphQuery =>
      exact congrArg ULift.down (agree (.map graphQuery) baseMember)

/-- Combine primitive endpoint tables and one candidate state-map table for
evaluation of the closed Hom-preservation formulas. -/
def homLawTableFromTables {input : LensFamilyInput.{u}}
    (source target : ObjectTable input) (table : GraphTable.{u}) :
    HomQuery input → Bool
  | .source query => objectLawTable source query
  | .target query => objectLawTable target query
  | .map query => table query

/-- The combined dependent primitive table derives the same Hom-law table as
the three component tables. -/
theorem homPrimitiveLawTable_homPrimitiveTable {input : LensFamilyInput.{u}}
    (source target : ObjectTable input) (table : GraphTable.{u}) :
    homPrimitiveLawTable (homPrimitiveTable source target table) =
      homLawTableFromTables source target table := by
  classical
  funext query
  cases query with
  | source objectQuery => cases objectQuery <;> rfl
  | target objectQuery => cases objectQuery <;> rfl
  | map graphQuery => rfl

/-- Combine fixed endpoint tables and one candidate state-map table solely for
evaluation of the closed Hom-preservation formulas. -/
def homLawTable {input : LensFamilyInput.{u}} (source target : Object input)
    (table : GraphTable.{u}) : HomQuery input → Bool :=
  homLawTableFromTables source.table target.table table

/-- Finite formula saying that one true state-map edge preserves one `get`
value. -/
def getPreservationFormula (input : LensFamilyInput.{u})
    (sourceCarrier targetCarrier : Type u)
    (source : sourceCarrier) (target : targetCarrier) (view : input.View) :
    IndependentFiniteLawFormula.BoolFormula.{u + 1, 0} (HomQuery input) :=
  .and (.cell (.source (.carrierMatches sourceCarrier)) true)
    (.and (.cell (.target (.carrierMatches targetCarrier)) true)
      (.implies
        (.and
          (.cell (.map (.edge sourceCarrier targetCarrier source target)) true)
          (.cell (.source (.get
            (.edge sourceCarrier input.View source view))) true))
        (.cell (.target (.get
          (.edge targetCarrier input.View target view))) true)))

/-- Finite formula saying that one state-map edge and the corresponding source
and target update edges determine the updated state-map edge. -/
def putPreservationFormula (input : LensFamilyInput.{u})
    (sourceCarrier targetCarrier : Type u)
    (source source' : sourceCarrier) (target target' : targetCarrier)
    (view : input.View) :
    IndependentFiniteLawFormula.BoolFormula.{u + 1, 0} (HomQuery input) :=
  .and (.cell (.source (.carrierMatches sourceCarrier)) true)
    (.and (.cell (.target (.carrierMatches targetCarrier)) true)
      (.implies
        (.and
          (.and
            (.cell (.map (.edge sourceCarrier targetCarrier source target)) true)
            (.cell (.source (.put view
              (.edge sourceCarrier sourceCarrier source source'))) true))
          (.cell (.target (.put view
            (.edge targetCarrier targetCarrier target target'))) true))
        (.cell (.map (.edge sourceCarrier targetCarrier source' target')) true)))

/-- Raw-table evaluation of one get-preservation formula. -/
theorem getPreservationFormula_evaluate_raw
    (input : LensFamilyInput.{u}) (sourceCarrier targetCarrier : Type u)
    (source : sourceCarrier) (target : targetCarrier) (view : input.View)
    (table : HomQuery input → Bool) :
    (getPreservationFormula input sourceCarrier targetCarrier source target view).evaluate table ↔
      table (.source (.carrierMatches sourceCarrier)) = true ∧
        table (.target (.carrierMatches targetCarrier)) = true ∧
          (table (.map (.edge sourceCarrier targetCarrier source target)) = true ∧
              table (.source (.get (.edge sourceCarrier input.View source view))) = true →
            table (.target (.get (.edge targetCarrier input.View target view))) = true) := Iff.rfl

/-- Raw-table evaluation of one put-preservation formula. -/
theorem putPreservationFormula_evaluate_raw
    (input : LensFamilyInput.{u}) (sourceCarrier targetCarrier : Type u)
    (source source' : sourceCarrier) (target target' : targetCarrier)
    (view : input.View) (table : HomQuery input → Bool) :
    (putPreservationFormula input sourceCarrier targetCarrier
      source source' target target' view).evaluate table ↔
      table (.source (.carrierMatches sourceCarrier)) = true ∧
        table (.target (.carrierMatches targetCarrier)) = true ∧
          ((table (.map (.edge sourceCarrier targetCarrier source target)) = true ∧
              table (.source (.put view
                (.edge sourceCarrier sourceCarrier source source'))) = true) ∧
            table (.target (.put view
              (.edge targetCarrier targetCarrier target target'))) = true →
            table (.map (.edge sourceCarrier targetCarrier source' target')) = true) := Iff.rfl

/-- Finite state-map graph fragments of a primitive Hom. -/
abbrev HomFragment (D : Finset GraphQuery.{u}) :=
  IndependentFiniteFragments.Fragment (fun _ : GraphQuery.{u} => Bool) D

/-- A family of finite state-map graph fragments. -/
abbrev HomFragmentFamily :=
  IndependentFiniteFragments.FragmentFamily (fun _ : GraphQuery.{u} => Bool)

/-- Compatibility of finite state-map fragments. -/
abbrev HomCompatible (family : HomFragmentFamily.{u}) :=
  IndependentFiniteFragments.Compatible family

/-- Restrict a state-map graph table to every finite query set. -/
def homFragments (table : GraphTable.{u}) : HomFragmentFamily.{u} :=
  IndependentFiniteFragments.fragments table

/-- Glue state-map graph fragments through singleton cells. -/
def homGlue (family : HomFragmentFamily.{u}) : GraphTable.{u} :=
  IndependentFiniteFragments.glue family

/-- State-map table restrictions are compatible. -/
theorem homFragments_compatible (table : GraphTable.{u}) :
    HomCompatible (homFragments table) :=
  IndependentFiniteFragments.fragments_compatible table

/-- Gluing all state-map restrictions recovers the table. -/
theorem homGlue_fragments (table : GraphTable.{u}) :
    homGlue (homFragments table) = table :=
  IndependentFiniteFragments.glue_fragments table

/-- Compatible state-map fragments are recovered from their glued table. -/
theorem homFragments_glue (family : HomFragmentFamily.{u})
    (compatible : HomCompatible family) :
    homFragments (homGlue family) = family :=
  IndependentFiniteFragments.fragments_glue family compatible

/-- A primitive local Hom is one lawful candidate state-map graph together
with the two finite preservation formula families. -/
structure Hom {input : LensFamilyInput.{u}} (source target : Object input) where
  /-- Finite fragments of the candidate state-map graph. -/
  family : HomFragmentFamily.{u}
  /-- The state-map fragments agree under inclusions. -/
  compatible : HomCompatible family
  /-- Closed graph-row instances for the selected state-map graph. -/
  map_instances : IndependentFiniteGraphLawFormula.CarrierRows.Instances
    (homGlue family) id source.Carrier target.Carrier
  /-- Every fixed-point `get` preservation formula evaluates. -/
  get_formula : ∀ sourceState targetState view,
    (getPreservationFormula input source.Carrier target.Carrier
      sourceState targetState view).evaluate (homLawTable source target (homGlue family))
  /-- Every fixed-point `put` preservation formula evaluates. -/
  put_formula : ∀ sourceState sourceState' targetState targetState' view,
    (putPreservationFormula input source.Carrier target.Carrier
      sourceState sourceState' targetState targetState' view).evaluate
        (homLawTable source target (homGlue family))

namespace Hom

variable {input : LensFamilyInput.{u}} {source target : Object input}

/-- Glue the candidate state-map table from its compatible finite fragments. -/
def table (morphism : Hom source target) : GraphTable.{u} := homGlue morphism.family

/-- The state-map graph law follows from its finite row instances. -/
theorem lawful (morphism : Hom source target) :
    IndependentCarrierGraph.IsLawful source.Carrier target.Carrier morphism.table :=
  (IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances
    morphism.table id source.Carrier target.Carrier).mpr morphism.map_instances

/-- Primitive Homs are equal when their finite state-map families agree. -/
@[ext]
theorem ext {first second : Hom source target}
    (family : first.family = second.family) : first = second := by
  cases first
  cases second
  cases family
  rfl

end Hom

/-- Extract the raw get-preservation implication from a primitive Hom formula. -/
theorem Hom.get_rule {input : LensFamilyInput.{u}} {source target : Object input}
    (morphism : Hom source target) (sourceState : source.Carrier)
    (targetState : target.Carrier) (view : input.View) :
    morphism.table (.edge source.Carrier target.Carrier sourceState targetState) = true ∧
        (source.table (.get
          (.edge source.Carrier input.View sourceState view))).down = true →
      (target.table (.get
        (.edge target.Carrier input.View targetState view))).down = true :=
  ((getPreservationFormula_evaluate_raw input source.Carrier target.Carrier
    sourceState targetState view _).mp (morphism.get_formula sourceState targetState view)).2.2

/-- Extract the raw put-preservation implication from a primitive Hom formula. -/
theorem Hom.put_rule {input : LensFamilyInput.{u}} {source target : Object input}
    (morphism : Hom source target)
    (sourceState sourceState' : source.Carrier)
    (targetState targetState' : target.Carrier) (view : input.View) :
    ((morphism.table (.edge source.Carrier target.Carrier sourceState targetState) = true ∧
        (source.table (.put view
          (.edge source.Carrier source.Carrier sourceState sourceState'))).down = true) ∧
      (target.table (.put view
        (.edge target.Carrier target.Carrier targetState targetState'))).down = true) →
      morphism.table (.edge source.Carrier target.Carrier sourceState' targetState') = true :=
  ((putPreservationFormula_evaluate_raw input source.Carrier target.Carrier
    sourceState sourceState' targetState targetState' view _).mp
      (morphism.put_formula sourceState sourceState' targetState targetState' view)).2.2

/-- Assemble the state-map graph carried by a primitive Hom. -/
def Hom.toFun {input : LensFamilyInput.{u}} {source target : Object input}
    (morphism : Hom source target) : source.Carrier → target.Carrier :=
  IndependentCarrierGraph.assemble source.Carrier target.Carrier
    morphism.table morphism.lawful

/-- Primitive Hom graph evaluation is exactly evaluation of its assembled
state map. -/
theorem Hom.edge_iff {input : LensFamilyInput.{u}} {source target : Object input}
    (morphism : Hom source target) (state : source.Carrier)
    (image : target.Carrier) :
    morphism.table (.edge source.Carrier target.Carrier state image) = true ↔
      morphism.toFun state = image := by
  constructor
  · exact IndependentCarrierGraph.assemble_eq_of_edge
      source.Carrier target.Carrier morphism.table morphism.lawful
  · intro equality
    rw [← equality]
    exact IndependentCarrierGraph.edge_assemble
      source.Carrier target.Carrier morphism.table morphism.lawful state

/-- Assemble a primitive Hom between assembled primitive endpoints.  Both
naturality laws are derived from the finite formulas. -/
def assembleHom {input : LensFamilyInput.{u}} {source target : Object input}
    (morphism : Hom source target) : assembleObject source ⟶ assembleObject target where
  toFun := morphism.toFun
  get_naturality state := by
    let image := morphism.toFun state
    let view := assembleGet source state
    apply (get_edge_iff target image view).mp
    exact morphism.get_rule state image view
      ⟨(morphism.edge_iff state image).mpr rfl,
        (get_edge_iff source state view).mpr rfl⟩
  put_naturality state view := by
    let image := morphism.toFun state
    let source' := assemblePut source state view
    let target' := assemblePut target image view
    apply (morphism.edge_iff source' target').mp
    exact morphism.put_rule state source' image target' view
      ⟨⟨(morphism.edge_iff state image).mpr rfl,
          (put_edge_iff source state source' view).mpr rfl⟩,
        (put_edge_iff target image target' view).mpr rfl⟩

/-- Read a semantic Hom into a primitive state-map graph and its finite
preservation formulas. -/
def readHom {input : LensFamilyInput.{u}}
    {source target : LensRealization input.View input.reference}
    (morphism : source ⟶ target) : Hom (readObject source) (readObject target) where
  family := homFragments
    (IndependentCarrierGraph.read source.Carrier target.Carrier morphism.toFun)
  compatible := homFragments_compatible _
  map_instances :=
    (IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances
      (IndependentCarrierGraph.read source.Carrier target.Carrier morphism.toFun)
      id source.Carrier target.Carrier).mp
      (IndependentCarrierGraph.read_isLawful _ _ morphism.toFun)
  get_formula sourceState targetState view := by
    apply (getPreservationFormula_evaluate_raw input source.Carrier target.Carrier
      sourceState targetState view _).mpr
    refine ⟨(readObject source).carrier_selected,
      (readObject target).carrier_selected, ?_⟩
    simp only [homGlue_fragments]
    change (IndependentCarrierGraph.read source.Carrier target.Carrier morphism.toFun
          (.edge source.Carrier target.Carrier sourceState targetState) = true ∧
        IndependentCarrierGraph.read source.Carrier input.View source.get
          (.edge source.Carrier input.View sourceState view) = true) →
        IndependentCarrierGraph.read target.Carrier input.View target.get
          (.edge target.Carrier input.View targetState view) = true
    rintro ⟨mapEdge, sourceEdge⟩
    apply (IndependentCarrierGraph.read_edge _ _ _ _ _).mpr
    have mapEquality := (IndependentCarrierGraph.read_edge _ _ _ _ _).mp mapEdge
    have sourceEquality := (IndependentCarrierGraph.read_edge _ _ _ _ _).mp sourceEdge
    subst targetState
    exact (morphism.get_naturality sourceState).trans sourceEquality
  put_formula sourceState sourceState' targetState targetState' view := by
    apply (putPreservationFormula_evaluate_raw input source.Carrier target.Carrier
      sourceState sourceState' targetState targetState' view _).mpr
    refine ⟨(readObject source).carrier_selected,
      (readObject target).carrier_selected, ?_⟩
    simp only [homGlue_fragments]
    change ((IndependentCarrierGraph.read source.Carrier target.Carrier morphism.toFun
          (.edge source.Carrier target.Carrier sourceState targetState) = true ∧
        IndependentCarrierGraph.read source.Carrier source.Carrier
          (fun current => source.put current view)
            (.edge source.Carrier source.Carrier sourceState sourceState') = true) ∧
        IndependentCarrierGraph.read target.Carrier target.Carrier
          (fun current => target.put current view)
            (.edge target.Carrier target.Carrier targetState targetState') = true) →
        IndependentCarrierGraph.read source.Carrier target.Carrier morphism.toFun
          (.edge source.Carrier target.Carrier sourceState' targetState') = true
    rintro ⟨⟨mapEdge, sourceEdge⟩, targetEdge⟩
    apply (IndependentCarrierGraph.read_edge _ _ _ _ _).mpr
    have mapEquality := (IndependentCarrierGraph.read_edge _ _ _ _ _).mp mapEdge
    have sourceEquality := (IndependentCarrierGraph.read_edge _ _ _ _ _).mp sourceEdge
    have targetEquality := (IndependentCarrierGraph.read_edge _ _ _ _ _).mp targetEdge
    subst targetState
    subst sourceState'
    subst targetState'
    exact morphism.put_naturality sourceState view

/-- Assemble a local Hom whose endpoints were read from fixed semantic
objects, directly back to those endpoints.  This is the Hom inverse used by
`ReconstructionData`; object assembly is not used here. -/
def assembleReadHom {input : LensFamilyInput.{u}}
    {source target : LensRealization input.View input.reference}
    (morphism : Hom (readObject source) (readObject target)) : source ⟶ target where
  toFun := morphism.toFun
  get_naturality state := by
    let image := morphism.toFun state
    let view := source.get state
    apply (IndependentCarrierGraph.read_edge target.Carrier input.View target.get
      image view).mp
    exact morphism.get_rule state image view
      ⟨(morphism.edge_iff state image).mpr rfl,
        (IndependentCarrierGraph.read_edge source.Carrier input.View source.get
          state view).mpr rfl⟩
  put_naturality state view := by
    let image := morphism.toFun state
    let source' := source.put state view
    let target' := target.put image view
    apply (morphism.edge_iff source' target').mp
    exact morphism.put_rule state source' image target' view
      ⟨⟨(morphism.edge_iff state image).mpr rfl,
          (IndependentCarrierGraph.read_edge source.Carrier source.Carrier
            (fun current => source.put current view) state source').mpr rfl⟩,
        (IndependentCarrierGraph.read_edge target.Carrier target.Carrier
          (fun current => target.put current view) image target').mpr rfl⟩

/-- Assembly after reading recovers every semantic Hom, including
noninvertible ones. -/
@[simp] theorem assembleReadHom_readHom {input : LensFamilyInput.{u}}
    {source target : LensRealization input.View input.reference}
    (morphism : source ⟶ target) :
    assembleReadHom (readHom morphism) = morphism := by
  apply LensRealization.Hom.ext
  exact IndependentCarrierGraph.assemble_read source.Carrier target.Carrier morphism.toFun

/-- Reading after direct endpoint assembly recovers every primitive local Hom. -/
@[simp] theorem readHom_assembleReadHom {input : LensFamilyInput.{u}}
    {source target : LensRealization input.View input.reference}
    (morphism : Hom (readObject source) (readObject target)) :
    readHom (assembleReadHom morphism) = morphism := by
  apply Hom.ext
  change homFragments (IndependentCarrierGraph.read source.Carrier target.Carrier
    morphism.toFun) = morphism.family
  rw [← homFragments_glue morphism.family morphism.compatible]
  apply congrArg homFragments
  exact IndependentCarrierGraph.read_assemble source.Carrier target.Carrier
    morphism.table morphism.lawful

/-- Direct primitive identity built from the carrier-graph diagonal. -/
def identityHom {input : LensFamilyInput.{u}} (object : Object input) :
    Hom object object where
  family := homFragments (IndependentCarrierGraph.identity object.Carrier)
  compatible := homFragments_compatible _
  map_instances :=
    (IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances
      (IndependentCarrierGraph.identity object.Carrier) id
      object.Carrier object.Carrier).mp
      (IndependentCarrierGraph.identity_isLawful object.Carrier)
  get_formula source target view := by
    apply (getPreservationFormula_evaluate_raw input object.Carrier object.Carrier
      source target view _).mpr
    refine ⟨object.carrier_selected, object.carrier_selected, ?_⟩
    simp only [homGlue_fragments]
    change (IndependentCarrierGraph.identity object.Carrier
          (.edge object.Carrier object.Carrier source target) = true ∧
        (object.table (.get (.edge object.Carrier input.View source view))).down = true) →
        (object.table (.get (.edge object.Carrier input.View target view))).down = true
    rintro ⟨identityEdge, sourceEdge⟩
    have equality :=
      (IndependentCarrierGraph.identity_edge object.Carrier source target).mp identityEdge
    subst target
    exact sourceEdge
  put_formula source source' target target' view := by
    apply (putPreservationFormula_evaluate_raw input object.Carrier object.Carrier
      source source' target target' view _).mpr
    refine ⟨object.carrier_selected, object.carrier_selected, ?_⟩
    simp only [homGlue_fragments]
    change ((IndependentCarrierGraph.identity object.Carrier
          (.edge object.Carrier object.Carrier source target) = true ∧
        (object.table (.put view
          (.edge object.Carrier object.Carrier source source'))).down = true) ∧
        (object.table (.put view
          (.edge object.Carrier object.Carrier target target'))).down = true) →
        IndependentCarrierGraph.identity object.Carrier
          (.edge object.Carrier object.Carrier source' target') = true
    rintro ⟨⟨identityEdge, sourceEdge⟩, targetEdge⟩
    have equality :=
      (IndependentCarrierGraph.identity_edge object.Carrier source target).mp identityEdge
    subst target
    apply (IndependentCarrierGraph.identity_edge object.Carrier source' target').mpr
    exact (IndependentCarrierGraph.assemble_eq_of_edge object.Carrier object.Carrier
      (putTable object.table view) (object.put_lawful view) sourceEdge).symm.trans
        (IndependentCarrierGraph.assemble_eq_of_edge object.Carrier object.Carrier
          (putTable object.table view) (object.put_lawful view) targetEdge)

/-- Direct primitive composition uses carrier-graph composition and proves the
two preservation formula families from those of its factors. -/
def composeHom {input : LensFamilyInput.{u}}
    {source middle target : Object input}
    (first : Hom source middle) (second : Hom middle target) :
    Hom source target where
  family := homFragments
    (IndependentCarrierGraph.compose source.Carrier middle.Carrier target.Carrier
      first.table first.lawful second.table)
  compatible := homFragments_compatible _
  map_instances :=
    (IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances
      (IndependentCarrierGraph.compose source.Carrier middle.Carrier target.Carrier
        first.table first.lawful second.table) id source.Carrier target.Carrier).mp
      (IndependentCarrierGraph.compose_isLawful
        source.Carrier middle.Carrier target.Carrier first.table first.lawful
          second.table second.lawful)
  get_formula sourceState targetState view := by
    apply (getPreservationFormula_evaluate_raw input source.Carrier target.Carrier
      sourceState targetState view _).mpr
    refine ⟨source.carrier_selected, target.carrier_selected, ?_⟩
    simp only [homGlue_fragments]
    change (IndependentCarrierGraph.compose source.Carrier middle.Carrier target.Carrier
          first.table first.lawful second.table
            (.edge source.Carrier target.Carrier sourceState targetState) = true ∧
        (source.table (.get
          (.edge source.Carrier input.View sourceState view))).down = true) →
        (target.table (.get
          (.edge target.Carrier input.View targetState view))).down = true
    rintro ⟨compositeEdge, sourceEdge⟩
    let middleState := first.toFun sourceState
    have secondEdge :
        second.table (.edge middle.Carrier target.Carrier middleState targetState) = true := by
      simpa [middleState, IndependentCarrierGraph.compose_edge] using compositeEdge
    have middleEdge :
        (middle.table (.get
          (.edge middle.Carrier input.View middleState view))).down = true :=
      first.get_rule sourceState middleState view
        ⟨(first.edge_iff sourceState middleState).mpr rfl, sourceEdge⟩
    exact second.get_rule middleState targetState view
      ⟨secondEdge, middleEdge⟩
  put_formula sourceState sourceState' targetState targetState' view := by
    apply (putPreservationFormula_evaluate_raw input source.Carrier target.Carrier
      sourceState sourceState' targetState targetState' view _).mpr
    refine ⟨source.carrier_selected, target.carrier_selected, ?_⟩
    simp only [homGlue_fragments]
    change ((IndependentCarrierGraph.compose source.Carrier middle.Carrier target.Carrier
          first.table first.lawful second.table
            (.edge source.Carrier target.Carrier sourceState targetState) = true ∧
        (source.table (.put view
          (.edge source.Carrier source.Carrier sourceState sourceState'))).down = true) ∧
        (target.table (.put view
          (.edge target.Carrier target.Carrier targetState targetState'))).down = true) →
        IndependentCarrierGraph.compose source.Carrier middle.Carrier target.Carrier
          first.table first.lawful second.table
            (.edge source.Carrier target.Carrier sourceState' targetState') = true
    rintro ⟨⟨compositeEdge, sourcePutEdge⟩, targetPutEdge⟩
    let middleState := first.toFun sourceState
    let middleState' := first.toFun sourceState'
    have firstEdge :
        first.table (.edge source.Carrier middle.Carrier sourceState middleState) = true :=
      (first.edge_iff sourceState middleState).mpr rfl
    have secondEdge :
        second.table (.edge middle.Carrier target.Carrier middleState targetState) = true := by
      simpa [middleState, IndependentCarrierGraph.compose_edge] using compositeEdge
    let targetMiddle := assemblePut middle middleState view
    have middlePutEdge :
        (middle.table (.put view
          (.edge middle.Carrier middle.Carrier middleState targetMiddle))).down = true :=
      IndependentCarrierGraph.edge_assemble middle.Carrier middle.Carrier
        (putTable middle.table view) (middle.put_lawful view) middleState
    have firstEdge' :
        first.table (.edge source.Carrier middle.Carrier sourceState' targetMiddle) = true :=
      first.put_rule sourceState sourceState' middleState targetMiddle view
        ⟨⟨firstEdge, sourcePutEdge⟩, middlePutEdge⟩
    have middleState'_eq : middleState' = targetMiddle :=
      (first.edge_iff sourceState' targetMiddle).mp firstEdge'
    have secondEdge' :
        second.table (.edge middle.Carrier target.Carrier targetMiddle targetState') = true :=
      second.put_rule middleState targetMiddle targetState targetState' view
        ⟨⟨secondEdge, middlePutEdge⟩, targetPutEdge⟩
    rw [IndependentCarrierGraph.compose_edge]
    change second.table (.edge middle.Carrier target.Carrier middleState' targetState') = true
    rw [middleState'_eq]
    exact secondEdge'

/-- Primitive lens objects and direct graph Homs form the fixed-input local
category required by the fixed GOAL B lens branch. -/
instance {input : LensFamilyInput.{u}} : Category.{u + 1} (Object input) where
  Hom := fun source target =>
    IndependentLensPrimitiveReconstruction.Hom source target
  id := identityHom
  comp := composeHom
  id_comp morphism := by
    apply Hom.ext
    rw [← homFragments_glue morphism.family morphism.compatible]
    simpa only [composeHom, identityHom] using congrArg homFragments
      (IndependentCarrierGraph.identity_compose _ _ morphism.table morphism.lawful)
  comp_id morphism := by
    apply Hom.ext
    rw [← homFragments_glue morphism.family morphism.compatible]
    simpa only [composeHom, identityHom] using congrArg homFragments
      (IndependentCarrierGraph.compose_identity _ _ morphism.table morphism.lawful)
  assoc first second third := by
    apply Hom.ext
    simpa only [composeHom] using congrArg homFragments
      (IndependentCarrierGraph.compose_assoc _ _ _ _
        first.table first.lawful second.table second.lawful third.table third.lawful)

/-- Reading sends the semantic identity to the direct primitive diagonal. -/
theorem readHom_id {input : LensFamilyInput.{u}}
    (lens : LensRealization input.View input.reference) :
    readHom (𝟙 lens) = identityHom (readObject lens) := by
  apply Hom.ext
  simpa only [readHom, identityHom] using congrArg homFragments
    (show IndependentCarrierGraph.read lens.Carrier lens.Carrier id =
      IndependentCarrierGraph.identity lens.Carrier by rfl)

/-- Reading sends semantic composition to direct primitive graph composition. -/
theorem readHom_comp {input : LensFamilyInput.{u}}
    {source middle target : LensRealization input.View input.reference}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    readHom (first ≫ second) = composeHom (readHom first) (readHom second) := by
  apply Hom.ext
  simpa only [readHom, composeHom] using congrArg homFragments
    (IndependentCarrierGraph.read_compose source.Carrier middle.Carrier target.Carrier
      first.toFun second.toFun)

/-- Fixed-input native lens reading into the independent primitive local
category. -/
def readingFunctor (input : LensFamilyInput.{u}) :
    LensRealization input.View input.reference ⥤ Object input where
  obj := readObject
  map := readHom
  map_id := readHom_id
  map_comp := readHom_comp

/-- No-unfold object API for the primitive lens reading functor. -/
@[simp] theorem readingFunctor_obj
    (input : LensFamilyInput.{u})
    (lens : LensRealization input.View input.reference) :
    (readingFunctor input).obj lens = readObject lens := rfl

/-- No-unfold map API for the primitive lens reading functor. -/
@[simp] theorem readingFunctor_map_table
    (input : LensFamilyInput.{u})
    {source target : LensRealization input.View input.reference}
    (morphism : source ⟶ target) (query : GraphQuery.{u}) :
    ((readingFunctor input).map morphism).table query =
      IndependentCarrierGraph.read source.Carrier target.Carrier
        morphism.toFun query :=
  congrFun (homGlue_fragments
    (IndependentCarrierGraph.read source.Carrier target.Carrier morphism.toFun)) query

/-- Equal primitive object readings determine isomorphic semantic lens
objects through their graph assemblies. -/
theorem readObject_separates_up_to_iso {input : LensFamilyInput.{u}}
    {first second : LensRealization input.View input.reference}
    (equality : readObject first = readObject second) : Nonempty (first ≅ second) := by
  refine ⟨(assembleObjectReadIso first).symm ≪≫ ?_ ≪≫ assembleObjectReadIso second⟩
  exact eqToIso (congrArg assembleObject equality)

/-- The primitive reader separates every semantic Hom type. -/
theorem homSeparation (input : LensFamilyInput.{u}) :
    HomSeparation (readingFunctor input) where
  hom source target := ⟨by
    intro first second equality
    calc
      first = assembleReadHom (readHom first) := (assembleReadHom_readHom first).symm
      _ = assembleReadHom (readHom second) := congrArg assembleReadHom equality
      _ = second := assembleReadHom_readHom second⟩

/-- Every primitive Hom between read endpoints assembles directly to those
native endpoints, and reading recovers it. -/
def homAssembly (input : LensFamilyInput.{u}) :
    HomAssembly (readingFunctor input) where
  assemble := assembleReadHom
  map_assemble := readHom_assembleReadHom

/-- Every primitive object is read from its graph-assembled semantic lens. -/
def objectAssembly (input : LensFamilyInput.{u}) :
    ObjectAssembly (readingFunctor input) where
  assembleObject := assembleObject
  readAssembledIso object := by
    change readObject (assembleObject object) ≅ object
    exact eqToIso (readObject_assembleObject object)

/-- Fixed GOAL B reconstruction data for primitive total lenses, with no
additional premise. -/
def reconstructionData (input : LensFamilyInput.{u}) :
    ReconstructionData (readingFunctor input) where
  separation := homSeparation input
  homAssembly := homAssembly input
  objectAssembly := objectAssembly input

/-- Every semantic Hom is recovered after primitive reading and direct
endpoint assembly. -/
@[simp] theorem assemble_read {input : LensFamilyInput.{u}}
    {source target : LensRealization input.View input.reference}
    (morphism : source ⟶ target) :
    (reconstructionData input).homAssembly.assemble
      ((readingFunctor input).map morphism) = morphism :=
  (reconstructionData input).assemble_map morphism

/-- Every primitive local Hom is recovered after direct endpoint assembly and
reading. -/
@[simp] theorem read_assemble {input : LensFamilyInput.{u}}
    {source target : LensRealization input.View input.reference}
    (morphism : (readingFunctor input).obj source ⟶
      (readingFunctor input).obj target) :
    (readingFunctor input).map
      ((reconstructionData input).homAssembly.assemble morphism) = morphism :=
  (reconstructionData input).homAssembly.map_assemble morphism

/-- Every primitive local Hom has exactly one semantic preimage. -/
theorem existsUnique_preimage {input : LensFamilyInput.{u}}
    {source target : LensRealization input.View input.reference}
    (morphism : (readingFunctor input).obj source ⟶
      (readingFunctor input).obj target) :
    ∃! global : source ⟶ target,
      (readingFunctor input).map global = morphism :=
  (reconstructionData input).existsUnique_preimage morphism

/-- Main fixed GOAL B theorem for the lens branch.  The general reconstruction
theorem is applied once to the concrete primitive separation and assembly
data. -/
noncomputable def equivalence (input : LensFamilyInput.{u}) :
    LensRealization input.View input.reference ≌ Object input :=
  (reconstructionData input).equivalence

/-- No-unfold API: the forward functor of the main lens equivalence is the
primitive graph reading functor. -/
@[simp] theorem equivalence_functor (input : LensFamilyInput.{u}) :
    (equivalence input).functor = readingFunctor input := rfl

/-- A primitive Hom acts on the primitive reference fibers by its assembled
state-map graph. -/
def primitiveFiberMap {input : LensFamilyInput.{u}}
    {source target : Object input} (morphism : Hom source target) :
    source.Fiber → target.Fiber := fun state => by
  let image := morphism.toFun state
  refine ⟨image, ?_⟩
  exact morphism.get_rule state image input.reference
    ⟨(morphism.edge_iff state image).mpr rfl, state.property⟩

/-- The primitive fiber action of a read Hom agrees pointwise with the
existing `LensRealization.res`. -/
theorem readFiberEquiv_primitiveFiberMap_readHom
    {input : LensFamilyInput.{u}}
    {source target : LensRealization input.View input.reference}
    (morphism : source ⟶ target) (state : (readObject source).Fiber) :
    readFiberEquiv target (primitiveFiberMap (readHom morphism) state) =
      LensRealization.res morphism (readFiberEquiv source state) := by
  apply Subtype.ext
  exact congrFun
    (IndependentCarrierGraph.assemble_read source.Carrier target.Carrier morphism.toFun)
    state.val

/-- Object-level comparison with the accepted semantic fiber reading. -/
noncomputable def readObjectFiberIso
    (input : LensFamilyInput.{u})
    (lens : LensRealization input.View input.reference) :
    (@finiteLocalValue (readObject lens).Fiber (readObject lens).fiber_finite) ≅
      (lensSemanticFiberReading input).obj lens :=
  by
    letI : Finite (readObject lens).Fiber := (readObject lens).fiber_finite
    exact FintypeCat.equivEquivIso (readFiberEquiv lens)

/-- No-unfold API for the object comparison: its forward map is exactly the
primitive-to-native reference-fiber equivalence. -/
@[simp] theorem readObjectFiberIso_hom_apply
    (input : LensFamilyInput.{u})
    (lens : LensRealization input.View input.reference)
    (state : (readObject lens).Fiber) :
    (readObjectFiberIso input lens).hom state = readFiberEquiv lens state := rfl

/-- Map-level comparison with `lensSemanticFiberReading`: the primitive fiber
action and the accepted `LensRealization.res` reading commute pointwise. -/
theorem readObjectFiberIso_naturality
    (input : LensFamilyInput.{u})
    {source target : LensRealization input.View input.reference}
    (morphism : source ⟶ target) (state : (readObject source).Fiber) :
    (readObjectFiberIso input target).hom
        (primitiveFiberMap (readHom morphism) state) =
      (lensSemanticFiberReading input).map morphism
        ((readObjectFiberIso input source).hom state) :=
  readFiberEquiv_primitiveFiberMap_readHom morphism state

/-- The primitive fiber action of any local Hom agrees with restriction of
its assembled semantic Hom under the primitive-to-native fiber equivalences. -/
theorem primitiveFiberEquiv_primitiveFiberMap
    {input : LensFamilyInput.{u}} {source target : Object input}
    (morphism : Hom source target) (state : source.Fiber) :
    primitiveFiberEquiv target (primitiveFiberMap morphism state) =
      LensRealization.res (assembleHom morphism) (primitiveFiberEquiv source state) := by
  apply Subtype.ext
  rfl

/-- The direct primitive assembly is the existing
`LensRealization.homEquivFiberMap` inverse applied to its primitive fiber
action. -/
theorem assembleHom_eq_homEquivFiberMap_symm
    {input : LensFamilyInput.{u}} {source target : Object input}
    (morphism : Hom source target) :
    assembleHom morphism =
      (LensRealization.homEquivFiberMap (assembleObject source)
        (assembleObject target)).symm
        (fun state => primitiveFiberEquiv target
          (primitiveFiberMap morphism ((primitiveFiberEquiv source).symm state))) := by
  rw [show (fun state => primitiveFiberEquiv target
      (primitiveFiberMap morphism ((primitiveFiberEquiv source).symm state))) =
      LensRealization.res (assembleHom morphism) by
    funext state
    apply Subtype.ext
    rfl]
  exact (LensRealization.ext_res (assembleHom morphism)).symm

/-- The support of each total-lens point formula is finite by the accepted
closed-formula support theorem. -/
theorem objectFormula_support_finite
    (input : LensFamilyInput.{u}) (C : Type u) (c d e : C)
    (first second : input.View) :
    Finite (putGetFormula input C c first).support ∧
      Finite (getPutFormula input C c d first).support ∧
      Finite (putPutFormula input C c d e first second).support :=
  ⟨IndependentFiniteLawFormula.BoolFormula.support_finite _,
    IndependentFiniteLawFormula.BoolFormula.support_finite _,
    IndependentFiniteLawFormula.BoolFormula.support_finite _⟩

/-- The supports of both Hom-preservation formulas are finite. -/
theorem homFormula_support_finite
    (input : LensFamilyInput.{u}) (C D : Type u)
    (c c' : C) (d d' : D) (view : input.View) :
    Finite (getPreservationFormula input C D c d view).support ∧
      Finite (putPreservationFormula input C D c c' d d' view).support :=
  ⟨IndependentFiniteLawFormula.BoolFormula.support_finite _,
    IndependentFiniteLawFormula.BoolFormula.support_finite _⟩

/-- Every object-law formula support contains its selected carrier cell. -/
theorem carrier_mem_objectFormula_support
    (input : LensFamilyInput.{u}) (C : Type u) (c d e : C)
    (first second : input.View) :
    ObjectLawQuery.carrierMatches C ∈ (putGetFormula input C c first).support ∧
      ObjectLawQuery.carrierMatches C ∈ (getPutFormula input C c d first).support ∧
      ObjectLawQuery.carrierMatches C ∈
        (putPutFormula input C c d e first second).support := by
  classical
  simp [putGetFormula, getPutFormula, putPutFormula, carrierFormula,
    IndependentFiniteLawFormula.BoolFormula.support]

/-- The put-get support contains the carrier cell and both graph cells it reads. -/
theorem putGetFormula_support_cells
    (input : LensFamilyInput.{u}) (C : Type u) (c : C) (view : input.View) :
    ObjectLawQuery.carrierMatches C ∈ (putGetFormula input C c view).support ∧
      ObjectLawQuery.get (.edge C input.View c view) ∈
        (putGetFormula input C c view).support ∧
      ObjectLawQuery.put view (.edge C C c c) ∈
        (putGetFormula input C c view).support := by
  classical
  simp [putGetFormula, carrierFormula, IndependentFiniteLawFormula.BoolFormula.support]

/-- The get-put support contains the carrier cell and both graph cells it reads. -/
theorem getPutFormula_support_cells
    (input : LensFamilyInput.{u}) (C : Type u) (c d : C) (view : input.View) :
    ObjectLawQuery.carrierMatches C ∈ (getPutFormula input C c d view).support ∧
      ObjectLawQuery.put view (.edge C C c d) ∈
        (getPutFormula input C c d view).support ∧
      ObjectLawQuery.get (.edge C input.View d view) ∈
        (getPutFormula input C c d view).support := by
  classical
  simp [getPutFormula, carrierFormula, IndependentFiniteLawFormula.BoolFormula.support]

/-- The put-put support contains the carrier cell and all three update graph cells. -/
theorem putPutFormula_support_cells
    (input : LensFamilyInput.{u}) (C : Type u) (c d e : C)
    (first second : input.View) :
    ObjectLawQuery.carrierMatches C ∈
        (putPutFormula input C c d e first second).support ∧
      ObjectLawQuery.put first (.edge C C c d) ∈
        (putPutFormula input C c d e first second).support ∧
      ObjectLawQuery.put second (.edge C C d e) ∈
        (putPutFormula input C c d e first second).support ∧
      ObjectLawQuery.put second (.edge C C c e) ∈
        (putPutFormula input C c d e first second).support := by
  classical
  simp [putPutFormula, carrierFormula, IndependentFiniteLawFormula.BoolFormula.support]

/-- Both Hom-law supports contain the source and target carrier cells. -/
theorem carrier_mem_homFormula_support
    (input : LensFamilyInput.{u}) (C D : Type u)
    (c c' : C) (d d' : D) (view : input.View) :
    (HomQuery.source (.carrierMatches C) ∈
        (getPreservationFormula input C D c d view).support ∧
      HomQuery.target (.carrierMatches D) ∈
        (getPreservationFormula input C D c d view).support) ∧
      (HomQuery.source (.carrierMatches C) ∈
          (putPreservationFormula input C D c c' d d' view).support ∧
        HomQuery.target (.carrierMatches D) ∈
          (putPreservationFormula input C D c c' d d' view).support) := by
  classical
  simp [getPreservationFormula, putPreservationFormula,
    IndependentFiniteLawFormula.BoolFormula.support]

/-- The get-preservation support contains both carrier cells and all three graph cells. -/
theorem getPreservationFormula_support_cells
    (input : LensFamilyInput.{u}) (C D : Type u)
    (c : C) (d : D) (view : input.View) :
    HomQuery.source (.carrierMatches C) ∈
        (getPreservationFormula input C D c d view).support ∧
      HomQuery.target (.carrierMatches D) ∈
        (getPreservationFormula input C D c d view).support ∧
      HomQuery.map (.edge C D c d) ∈
        (getPreservationFormula input C D c d view).support ∧
      HomQuery.source (.get (.edge C input.View c view)) ∈
        (getPreservationFormula input C D c d view).support ∧
      HomQuery.target (.get (.edge D input.View d view)) ∈
        (getPreservationFormula input C D c d view).support := by
  classical
  simp [getPreservationFormula, IndependentFiniteLawFormula.BoolFormula.support]

/-- The put-preservation support contains both carrier cells and every graph cell it reads. -/
theorem putPreservationFormula_support_cells
    (input : LensFamilyInput.{u}) (C D : Type u)
    (c c' : C) (d d' : D) (view : input.View) :
    HomQuery.source (.carrierMatches C) ∈
        (putPreservationFormula input C D c c' d d' view).support ∧
      HomQuery.target (.carrierMatches D) ∈
        (putPreservationFormula input C D c c' d d' view).support ∧
      HomQuery.map (.edge C D c d) ∈
        (putPreservationFormula input C D c c' d d' view).support ∧
      HomQuery.source (.put view (.edge C C c c')) ∈
        (putPreservationFormula input C D c c' d d' view).support ∧
      HomQuery.target (.put view (.edge D D d d')) ∈
        (putPreservationFormula input C D c c' d d' view).support ∧
      HomQuery.map (.edge C D c' d') ∈
        (putPreservationFormula input C D c c' d d' view).support := by
  classical
  simp [putPreservationFormula, IndependentFiniteLawFormula.BoolFormula.support]

/-- The `get` graph row instances are equivalent to native graph lawfulness. -/
theorem getLawful_iff_instances {input : LensFamilyInput.{u}}
    (table : ObjectTable input) (C : Type u) :
    IndependentCarrierGraph.IsLawful C input.View (getTable table) ↔
      IndependentFiniteGraphLawFormula.CarrierRows.Instances
        (getTable table) id C input.View :=
  IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances
    (getTable table) id C input.View

/-- One fixed-view `put` graph's row instances are equivalent to native lawfulness. -/
theorem putLawful_iff_instances {input : LensFamilyInput.{u}}
    (table : ObjectTable input) (C : Type u) (view : input.View) :
    IndependentCarrierGraph.IsLawful C C (putTable table view) ↔
      IndependentFiniteGraphLawFormula.CarrierRows.Instances
        (putTable table view) id C C :=
  IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances
    (putTable table view) id C C

/-- State-map graph row instances are equivalent to native graph lawfulness. -/
theorem homLawful_iff_instances (table : GraphTable.{u}) (C D : Type u) :
    IndependentCarrierGraph.IsLawful C D table ↔
      IndependentFiniteGraphLawFormula.CarrierRows.Instances table id C D :=
  IndependentFiniteGraphLawFormula.CarrierRows.lawful_iff_instances table id C D

/-- Agreement on the primitive cells supporting a put-get instance preserves
evaluation of the derived law table. -/
theorem putGetFormula_evaluate_iff_of_support
    (input : LensFamilyInput.{u}) (C : Type u) (c : C) (view : input.View)
    (first second : ObjectTable input)
    (agree : ∀ query ∈
      objectFormulaBaseSupport input (putGetFormula input C c view),
      first query = second query) :
    (putGetFormula input C c view).evaluate (objectLawTable first) ↔
      (putGetFormula input C c view).evaluate (objectLawTable second) :=
  objectFormula_evaluate_iff_of_base_support input _ first second agree

/-- Agreement on the primitive cells supporting a get-put instance preserves
evaluation of the derived law table. -/
theorem getPutFormula_evaluate_iff_of_support
    (input : LensFamilyInput.{u}) (C : Type u) (c d : C) (view : input.View)
    (first second : ObjectTable input)
    (agree : ∀ query ∈
      objectFormulaBaseSupport input (getPutFormula input C c d view),
      first query = second query) :
    (getPutFormula input C c d view).evaluate (objectLawTable first) ↔
      (getPutFormula input C c d view).evaluate (objectLawTable second) :=
  objectFormula_evaluate_iff_of_base_support input _ first second agree

/-- Agreement on the primitive cells supporting a put-put instance preserves
evaluation of the derived law table. -/
theorem putPutFormula_evaluate_iff_of_support
    (input : LensFamilyInput.{u}) (C : Type u) (c d e : C)
    (firstView secondView : input.View) (first second : ObjectTable input)
    (agree : ∀ query ∈
      objectFormulaBaseSupport input
        (putPutFormula input C c d e firstView secondView),
      first query = second query) :
    (putPutFormula input C c d e firstView secondView).evaluate
        (objectLawTable first) ↔
      (putPutFormula input C c d e firstView secondView).evaluate
        (objectLawTable second) :=
  objectFormula_evaluate_iff_of_base_support input _ first second agree

/-- Agreement on the primitive endpoint and map cells supporting a get
preservation instance preserves evaluation of the derived law table. -/
theorem getPreservationFormula_evaluate_iff_of_support
    (input : LensFamilyInput.{u}) (C D : Type u) (c : C) (d : D)
    (view : input.View)
    (firstSource firstTarget secondSource secondTarget : ObjectTable input)
    (firstMap secondMap : GraphTable.{u})
    (agree : ∀ query ∈
      homFormulaBaseSupport input (getPreservationFormula input C D c d view),
      homPrimitiveTable firstSource firstTarget firstMap query =
        homPrimitiveTable secondSource secondTarget secondMap query) :
    (getPreservationFormula input C D c d view).evaluate
        (homLawTableFromTables firstSource firstTarget firstMap) ↔
      (getPreservationFormula input C D c d view).evaluate
        (homLawTableFromTables secondSource secondTarget secondMap) := by
  rw [← homPrimitiveLawTable_homPrimitiveTable firstSource firstTarget firstMap,
    ← homPrimitiveLawTable_homPrimitiveTable secondSource secondTarget secondMap]
  exact homFormula_evaluate_iff_of_base_support input _ _ _ agree

/-- Agreement on the primitive endpoint and map cells supporting a put
preservation instance preserves evaluation of the derived law table. -/
theorem putPreservationFormula_evaluate_iff_of_support
    (input : LensFamilyInput.{u}) (C D : Type u)
    (c c' : C) (d d' : D) (view : input.View)
    (firstSource firstTarget secondSource secondTarget : ObjectTable input)
    (firstMap secondMap : GraphTable.{u})
    (agree : ∀ query ∈
      homFormulaBaseSupport input
        (putPreservationFormula input C D c c' d d' view),
      homPrimitiveTable firstSource firstTarget firstMap query =
        homPrimitiveTable secondSource secondTarget secondMap query) :
    (putPreservationFormula input C D c c' d d' view).evaluate
        (homLawTableFromTables firstSource firstTarget firstMap) ↔
      (putPreservationFormula input C D c c' d d' view).evaluate
        (homLawTableFromTables secondSource secondTarget secondMap) := by
  rw [← homPrimitiveLawTable_homPrimitiveTable firstSource firstTarget firstMap,
    ← homPrimitiveLawTable_homPrimitiveTable secondSource secondTarget secondMap]
  exact homFormula_evaluate_iff_of_base_support input _ _ _ agree

/-- A put-get formula evaluates exactly when the corresponding assembled
point implication holds. -/
theorem putGetFormula_evaluate_iff
    {input : LensFamilyInput.{u}} (object : Object input)
    (state : object.Carrier) (view : input.View) :
    (putGetFormula input object.Carrier state view).evaluate
        (objectLawTable object.table) ↔
      (assembleGet object state = view → assemblePut object state view = state) := by
  constructor
  · intro formula getEquality
    exact (put_edge_iff object state state view).mp
      (((putGetFormula_evaluate_raw input object.Carrier state view _).mp formula).2
        ((get_edge_iff object state view).mpr getEquality))
  · intro implication
    apply (putGetFormula_evaluate_raw input object.Carrier state view _).mpr
    exact ⟨object.carrier_selected, fun getEdge =>
      (put_edge_iff object state state view).mpr
        (implication ((get_edge_iff object state view).mp getEdge))⟩

/-- A get-put formula evaluates exactly when the corresponding assembled
point implication holds. -/
theorem getPutFormula_evaluate_iff
    {input : LensFamilyInput.{u}} (object : Object input)
    (state target : object.Carrier) (view : input.View) :
    (getPutFormula input object.Carrier state target view).evaluate
        (objectLawTable object.table) ↔
      (assemblePut object state view = target → assembleGet object target = view) := by
  constructor
  · intro formula putEquality
    exact (get_edge_iff object target view).mp
      (((getPutFormula_evaluate_raw input object.Carrier state target view _).mp formula).2
        ((put_edge_iff object state target view).mpr putEquality))
  · intro implication
    apply (getPutFormula_evaluate_raw input object.Carrier state target view _).mpr
    exact ⟨object.carrier_selected, fun putEdge =>
      (get_edge_iff object target view).mpr
        (implication ((put_edge_iff object state target view).mp putEdge))⟩

/-- A put-put formula evaluates exactly when the corresponding assembled
two-update point implication holds. -/
theorem putPutFormula_evaluate_iff
    {input : LensFamilyInput.{u}} (object : Object input)
    (state middle target : object.Carrier) (first second : input.View) :
    (putPutFormula input object.Carrier state middle target first second).evaluate
        (objectLawTable object.table) ↔
      (assemblePut object state first = middle →
        assemblePut object middle second = target →
        assemblePut object state second = target) := by
  constructor
  · intro formula firstEquality secondEquality
    exact (put_edge_iff object state target second).mp
      (((putPutFormula_evaluate_raw input object.Carrier state middle target first second _).mp
        formula).2
        ⟨(put_edge_iff object state middle first).mpr firstEquality,
          (put_edge_iff object middle target second).mpr secondEquality⟩)
  · intro implication
    apply (putPutFormula_evaluate_raw input object.Carrier state middle target first second _).mpr
    exact ⟨object.carrier_selected, fun edges =>
      (put_edge_iff object state target second).mpr
        (implication
          ((put_edge_iff object state middle first).mp edges.1)
          ((put_edge_iff object middle target second).mp edges.2))⟩

/-- A get-preservation formula evaluates exactly when the assembled map
preserves the chosen get-value implication. -/
theorem getPreservationFormula_evaluate_iff
    {input : LensFamilyInput.{u}} {source target : Object input}
    (morphism : Hom source target) (sourceState : source.Carrier)
    (targetState : target.Carrier) (view : input.View) :
    (getPreservationFormula input source.Carrier target.Carrier
      sourceState targetState view).evaluate
        (homLawTable source target morphism.table) ↔
      (morphism.toFun sourceState = targetState →
        assembleGet source sourceState = view →
        assembleGet target targetState = view) := by
  constructor
  · intro formula mapEquality sourceEquality
    exact (get_edge_iff target targetState view).mp
      (((getPreservationFormula_evaluate_raw input source.Carrier target.Carrier
        sourceState targetState view _).mp formula).2.2
        ⟨(morphism.edge_iff sourceState targetState).mpr mapEquality,
          (get_edge_iff source sourceState view).mpr sourceEquality⟩)
  · intro implication
    apply (getPreservationFormula_evaluate_raw input source.Carrier target.Carrier
      sourceState targetState view _).mpr
    exact ⟨source.carrier_selected, target.carrier_selected, fun edges =>
      (get_edge_iff target targetState view).mpr
        (implication
          ((morphism.edge_iff sourceState targetState).mp edges.1)
          ((get_edge_iff source sourceState view).mp edges.2))⟩

/-- A put-preservation formula evaluates exactly when the assembled map
preserves the chosen source and target update edges. -/
theorem putPreservationFormula_evaluate_iff
    {input : LensFamilyInput.{u}} {source target : Object input}
    (morphism : Hom source target)
    (sourceState sourceState' : source.Carrier)
    (targetState targetState' : target.Carrier) (view : input.View) :
    (putPreservationFormula input source.Carrier target.Carrier
      sourceState sourceState' targetState targetState' view).evaluate
        (homLawTable source target morphism.table) ↔
      (morphism.toFun sourceState = targetState →
        assemblePut source sourceState view = sourceState' →
        assemblePut target targetState view = targetState' →
        morphism.toFun sourceState' = targetState') := by
  constructor
  · intro formula mapEquality sourceEquality targetEquality
    exact (morphism.edge_iff sourceState' targetState').mp
      (((putPreservationFormula_evaluate_raw input source.Carrier target.Carrier
        sourceState sourceState' targetState targetState' view _).mp formula).2.2
        ⟨⟨(morphism.edge_iff sourceState targetState).mpr mapEquality,
            (put_edge_iff source sourceState sourceState' view).mpr sourceEquality⟩,
          (put_edge_iff target targetState targetState' view).mpr targetEquality⟩)
  · intro implication
    apply (putPreservationFormula_evaluate_raw input source.Carrier target.Carrier
      sourceState sourceState' targetState targetState' view _).mpr
    exact ⟨source.carrier_selected, target.carrier_selected, fun edges =>
      (morphism.edge_iff sourceState' targetState').mpr
        (implication
          ((morphism.edge_iff sourceState targetState).mp edges.1.1)
          ((put_edge_iff source sourceState sourceState' view).mp edges.1.2)
          ((put_edge_iff target targetState targetState' view).mp edges.2))⟩

/-! ### Concrete positive and rejection fixtures -/

/-- Raw ignored-update cells used to test that the finite get-put formula is
not vacuous. -/
def ignoredUpdateTable : ObjectTable ({ View := Bool, reference := false } : LensFamilyInput) :=
  readDataTable LensRealization.ignoredUpdateData

/-- The concrete ignored-update table fails the get-put formula at
`state = false`, `target = false`, and `view = true`. -/
theorem ignoredUpdateTable_rejected :
    ¬ (getPutFormula ({ View := Bool, reference := false } : LensFamilyInput)
      Bool false false true).evaluate (objectLawTable ignoredUpdateTable) := by
  intro formula
  have conclusion := ((getPutFormula_evaluate_raw
    ({ View := Bool, reference := false } : LensFamilyInput)
    Bool false false true (objectLawTable ignoredUpdateTable)).mp formula).2
    ((IndependentCarrierGraph.read_edge Bool Bool
      (fun state => LensRealization.ignoredUpdateData.put state true)
      false false).mpr rfl)
  have impossible :=
    (IndependentCarrierGraph.read_edge Bool Bool
      LensRealization.ignoredUpdateData.get false true).mp conclusion
  exact Bool.noConfusion impossible

/-- A product lens used to reject a state map that changes the visible value. -/
abbrev booleanViewUnitLens : LensRealization Bool false :=
  LensRealization.product Bool PUnit false

/-- Candidate state-map table that flips the visible Boolean component. -/
def flipVisibleTable : GraphTable :=
  IndependentCarrierGraph.read (Bool × PUnit) (Bool × PUnit)
    (fun state => (!state.1, state.2))

/-- Combined raw table for the invalid visible-flipping state map. -/
def flipVisibleHomLawTable :
    HomQuery ({ View := Bool, reference := false } : LensFamilyInput) → Bool :=
  homLawTable (readObject booleanViewUnitLens) (readObject booleanViewUnitLens)
    flipVisibleTable

/-- The visible-flipping candidate fails `get` preservation at a concrete point. -/
theorem flipVisibleTable_getPreservation_rejected :
    ¬ (getPreservationFormula
      ({ View := Bool, reference := false } : LensFamilyInput)
      (Bool × PUnit) (Bool × PUnit)
      (false, PUnit.unit) (true, PUnit.unit) false).evaluate
        flipVisibleHomLawTable := by
  intro formula
  have rule := ((getPreservationFormula_evaluate_raw
    ({ View := Bool, reference := false } : LensFamilyInput)
    (Bool × PUnit) (Bool × PUnit)
    (false, PUnit.unit) (true, PUnit.unit) false
    flipVisibleHomLawTable).mp formula).2.2
  have targetEdge := rule ⟨
    (IndependentCarrierGraph.read_edge (Bool × PUnit) (Bool × PUnit)
      (fun state => (!state.1, state.2))
      (false, PUnit.unit) (true, PUnit.unit)).mpr rfl,
    (IndependentCarrierGraph.read_edge (Bool × PUnit) Bool Prod.fst
      (false, PUnit.unit) false).mpr rfl⟩
  have impossible :=
    (IndependentCarrierGraph.read_edge (Bool × PUnit) Bool Prod.fst
      (true, PUnit.unit) false).mp targetEdge
  exact Bool.noConfusion impossible

/-- The fixed input with a unit view and its unique reference value. -/
def booleanFiberInput : LensFamilyInput where
  View := Unit
  reference := ()

/-- Raw unit-view lens data with natural-number states and identity updates. -/
def infiniteFiberData : LensData Unit where
  Carrier := Nat
  get := fun _ => ()
  put := fun state _ => state

/-- The infinite-fiber fixture satisfies all three pointwise lens equations. -/
theorem infiniteFiberData_point_laws :
    (∀ state, infiniteFiberData.put state (infiniteFiberData.get state) = state) ∧
      (∀ state view, infiniteFiberData.get
        (infiniteFiberData.put state view) = view) ∧
      (∀ state first second, infiniteFiberData.put
        (infiniteFiberData.put state first) second =
          infiniteFiberData.put state second) := by
  simp [infiniteFiberData]

/-- Primitive cells for the natural-number state fixture. -/
def infiniteFiberTable : ObjectTable booleanFiberInput :=
  readDataTable infiniteFiberData

/-- Every natural-number state lies in the primitive reference fiber. -/
def infinitePrimitiveFiberEquiv :
    PrimitiveFiber booleanFiberInput Nat infiniteFiberTable ≃ Nat where
  toFun state := state.val
  invFun state := ⟨state, by
    change IndependentCarrierGraph.read Nat Unit (fun _ => ())
      (.edge Nat Unit state ()) = true
    exact (IndependentCarrierGraph.read_edge Nat Unit (fun _ => ()) state ()).mpr rfl⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := rfl

/-- The natural-number fixture is rejected only by the finite reference-fiber
requirement: its raw get and put operations satisfy all three lens equations. -/
theorem infiniteFiberTable_not_fiberCover :
    ¬ FiberCover booleanFiberInput Nat infiniteFiberTable := by
  intro cover
  have finitePrimitive :
      Finite (PrimitiveFiber booleanFiberInput Nat infiniteFiberTable) :=
    (fiberCover_iff_finite booleanFiberInput Nat infiniteFiberTable).mp cover
  have finiteNat : Finite Nat := infinitePrimitiveFiberEquiv.finite_iff.mp finitePrimitive
  exact (Infinite.not_finite : ¬ Finite Nat) finiteNat

/-- A unit-complement lens whose carrier differs from the Boolean-complement fixture. -/
abbrev unitFiberLens : LensRealization Unit () :=
  LensRealization.product Unit PUnit ()

/-- A noninvertible Hom from the Boolean-complement carrier to the unit-complement carrier. -/
def booleanToUnitHom :
    LensSemanticFiniteDetermination.booleanFiberLens ⟶ unitFiberLens where
  toFun := fun state => (state.1, PUnit.unit)
  get_naturality := fun _ => rfl
  put_naturality := fun _ _ => rfl

/-- The cross-carrier fixture is noninvertible because its state map is not injective. -/
theorem booleanToUnitHom_not_injective :
    ¬ Function.Injective booleanToUnitHom.toFun := by
  intro injective
  have equality := injective (show
    booleanToUnitHom.toFun ((), false) = booleanToUnitHom.toFun ((), true) by rfl)
  exact Bool.noConfusion (congrArg Prod.snd equality)

/-- Primitive reading of the noninvertible Hom between distinct carrier types. -/
def booleanToUnitPrimitiveHom :
    Hom
      (readObject (input := booleanFiberInput)
        LensSemanticFiniteDetermination.booleanFiberLens)
      (readObject (input := booleanFiberInput) unitFiberLens) :=
  readHom (input := booleanFiberInput) booleanToUnitHom

/-- Reading the existing noninvertible fixture produces an admitted primitive
Hom at the explicit Boolean-fiber parameter. -/
def constantFalsePrimitiveHom :
    Hom
      (readObject (input := booleanFiberInput)
        LensSemanticFiniteDetermination.booleanFiberLens)
      (readObject (input := booleanFiberInput)
        LensSemanticFiniteDetermination.booleanFiberLens) :=
  readHom (input := booleanFiberInput)
    LensSemanticFiniteDetermination.constantFalseHom

/-- The primitive reading retains the existing fixture's noninjective fiber
action, so the local Hom range is not restricted to isomorphisms. -/
theorem constantFalsePrimitiveHom_fiber_not_injective :
    ¬ Function.Injective (primitiveFiberMap constantFalsePrimitiveHom) := by
  intro injective
  apply LensSemanticFiniteDetermination.constantFalseHom_res_not_injective
  intro first second equality
  let firstPrimitive :=
    (readFiberEquiv (input := booleanFiberInput)
      LensSemanticFiniteDetermination.booleanFiberLens).symm first
  let secondPrimitive :=
    (readFiberEquiv (input := booleanFiberInput)
      LensSemanticFiniteDetermination.booleanFiberLens).symm second
  have primitiveEquality : firstPrimitive = secondPrimitive := by
    apply injective
    apply (readFiberEquiv (input := booleanFiberInput)
      LensSemanticFiniteDetermination.booleanFiberLens).injective
    change
      readFiberEquiv (input := booleanFiberInput)
          LensSemanticFiniteDetermination.booleanFiberLens
          (primitiveFiberMap
            (readHom (input := booleanFiberInput)
              LensSemanticFiniteDetermination.constantFalseHom) firstPrimitive) =
        readFiberEquiv (input := booleanFiberInput)
          LensSemanticFiniteDetermination.booleanFiberLens
          (primitiveFiberMap
            (readHom (input := booleanFiberInput)
              LensSemanticFiniteDetermination.constantFalseHom) secondPrimitive)
    calc
      _ = LensRealization.res LensSemanticFiniteDetermination.constantFalseHom
          (readFiberEquiv (input := booleanFiberInput)
            LensSemanticFiniteDetermination.booleanFiberLens firstPrimitive) :=
        readFiberEquiv_primitiveFiberMap_readHom
          (input := booleanFiberInput)
          (source := LensSemanticFiniteDetermination.booleanFiberLens)
          (target := LensSemanticFiniteDetermination.booleanFiberLens)
          LensSemanticFiniteDetermination.constantFalseHom firstPrimitive
      _ = LensRealization.res LensSemanticFiniteDetermination.constantFalseHom first := by
        rw [show readFiberEquiv (input := booleanFiberInput)
          LensSemanticFiniteDetermination.booleanFiberLens firstPrimitive =
          first by simp [firstPrimitive]]
      _ = LensRealization.res LensSemanticFiniteDetermination.constantFalseHom second := equality
      _ = LensRealization.res LensSemanticFiniteDetermination.constantFalseHom
          (readFiberEquiv (input := booleanFiberInput)
            LensSemanticFiniteDetermination.booleanFiberLens secondPrimitive) := by
        rw [show readFiberEquiv (input := booleanFiberInput)
          LensSemanticFiniteDetermination.booleanFiberLens secondPrimitive =
          second by simp [secondPrimitive]]
      _ = _ := (readFiberEquiv_primitiveFiberMap_readHom
        (input := booleanFiberInput)
        (source := LensSemanticFiniteDetermination.booleanFiberLens)
        (target := LensSemanticFiniteDetermination.booleanFiberLens)
        LensSemanticFiniteDetermination.constantFalseHom secondPrimitive).symm
  have nativeEquality := congrArg
    (readFiberEquiv (input := booleanFiberInput)
      LensSemanticFiniteDetermination.booleanFiberLens) primitiveEquality
  simpa [firstPrimitive, secondPrimitive] using nativeEquality

end IndependentLensPrimitiveReconstruction

end

end AAT.AG.LocalSemanticReconstruction

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentLensPrimitiveReconstruction
