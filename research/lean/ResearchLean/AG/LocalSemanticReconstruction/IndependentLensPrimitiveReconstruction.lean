import ResearchLean.AG.LocalSemanticReconstruction.IndependentCarrierGraphReadings
import ResearchLean.AG.LocalSemanticReconstruction.IndependentFiniteLawFormula
import ResearchLean.AG.LocalSemanticReconstruction.LensFiberModelEquivalence
import ResearchLean.AG.LocalSemanticReconstruction.LensSemanticFiniteDetermination
import ResearchLean.AG.LocalSemanticReconstruction.LocalReconstructionEquivalence
import Formal.Util.AssertStandardAxioms

/-!
# Primitive reconstruction of total lenses

For a fixed `LensFamilyInput`, this module declares the lens queries before a
state carrier is selected.  One tagged Boolean table contains the candidate
graphs for `get` and every fixed-view `put`.  The three total-lens laws are
closed `BoolFormula` instances at fixed points, and the reference fiber is the
subtype selected by the reference `get` edge.

Local Homs contain one candidate state-map graph and closed formulas for
`get` and `put` preservation.  Identity and composition use
`IndependentCarrierGraph.identity` and `IndependentCarrierGraph.compose`
directly.  Reading and assembly cover all semantic lens objects and all
get/put-preserving maps, including noninvertible maps.

## Implementation notes

The object and Hom records contain primitive tables and their point laws; they
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
  /-- One candidate edge of the `get` graph. -/
  | get (query : GraphQuery.{u})
  /-- One candidate edge of the `put` graph at a fixed view. -/
  | put (view : input.View) (query : GraphQuery.{u})

/-- The single Boolean table containing all primitive lens-object cells. -/
abbrev ObjectTable (input : LensFamilyInput.{u}) := ObjectQuery input → Bool

/-- Restrict the tagged object table to the candidate `get` graph. -/
def getTable {input : LensFamilyInput.{u}} (table : ObjectTable input) : GraphTable.{u} :=
  fun query => table (.get query)

/-- Restrict the tagged object table to the candidate `put` graph at one view. -/
def putTable {input : LensFamilyInput.{u}} (table : ObjectTable input)
    (view : input.View) : GraphTable.{u} :=
  fun query => table (.put view query)

/-- The finite formula for `get(c) = v -> put_v(c) = c`. -/
def putGetFormula (input : LensFamilyInput.{u}) (C : Type u)
    (c : C) (view : input.View) :
    IndependentFiniteLawFormula.BoolFormula.{u + 1, 0} (ObjectQuery input) :=
  .implies
    (.cell (.get (.edge C input.View c view)) true)
    (.cell (.put view (.edge C C c c)) true)

/-- The finite formula for `put_v(c) = d -> get(d) = v`. -/
def getPutFormula (input : LensFamilyInput.{u}) (C : Type u)
    (c d : C) (view : input.View) :
    IndependentFiniteLawFormula.BoolFormula.{u + 1, 0} (ObjectQuery input) :=
  .implies
    (.cell (.put view (.edge C C c d)) true)
    (.cell (.get (.edge C input.View d view)) true)

/-- The finite formula for two consecutive updates to retain the last view. -/
def putPutFormula (input : LensFamilyInput.{u}) (C : Type u)
    (c d e : C) (first second : input.View) :
    IndependentFiniteLawFormula.BoolFormula.{u + 1, 0} (ObjectQuery input) :=
  .implies
    (.and
      (.cell (.put first (.edge C C c d)) true)
      (.cell (.put second (.edge C C d e)) true))
    (.cell (.put second (.edge C C c e)) true)

/-- The reference fiber selected directly by the primitive `get` graph. -/
abbrev PrimitiveFiber (input : LensFamilyInput.{u}) (C : Type u)
    (table : ObjectTable input) :=
  {c : C // table (.get (.edge C input.View c input.reference)) = true}

/-- A fixed-GOAL A/B primitive lens object.  Its fields are exactly one state
carrier reference, one tagged table, graph lawfulness, the three finite point
formulas, and finiteness of the primitive reference fiber. -/
structure Object (input : LensFamilyInput.{u}) where
  /-- The selected state carrier referenced by active graph queries. -/
  Carrier : Type u
  /-- The common tagged table for `get` and all fixed-view `put` graphs. -/
  table : ObjectTable input
  /-- The selected `get` graph is total and all mismatched carrier cells are false. -/
  get_lawful : IndependentCarrierGraph.IsLawful Carrier input.View (getTable table)
  /-- Every selected fixed-view `put` graph is total and typed. -/
  put_lawful : ∀ view, IndependentCarrierGraph.IsLawful Carrier Carrier (putTable table view)
  /-- Every fixed-point put-get formula evaluates from the primitive table. -/
  put_get_formula : ∀ c view,
    (putGetFormula input Carrier c view).evaluate table
  /-- Every fixed-point get-put formula evaluates from the primitive table. -/
  get_put_formula : ∀ c d view,
    (getPutFormula input Carrier c d view).evaluate table
  /-- Every fixed-point put-put formula evaluates from the primitive table. -/
  put_put_formula : ∀ c d e first second,
    (putPutFormula input Carrier c d e first second).evaluate table
  /-- The primitive reference-edge subtype is finite. -/
  fiber_finite : Finite (PrimitiveFiber input Carrier table)

namespace Object

variable {input : LensFamilyInput.{u}}

/-- Primitive lens objects are equal when their carrier reference and tagged
table agree; all remaining fields are propositions. -/
@[ext]
theorem ext {first second : Object input}
    (carrier : first.Carrier = second.Carrier)
    (table : first.table = second.table) : first = second := by
  cases first
  cases second
  cases carrier
  cases table
  rfl

/-- The primitive reference fiber of a local object. -/
abbrev Fiber (object : Object input) :=
  PrimitiveFiber input object.Carrier object.table

/-- Finiteness is supplied only for the primitive reference fiber. -/
instance (object : Object input) : Finite object.Fiber := object.fiber_finite

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
    object.table (.get (.edge object.Carrier input.View state view)) = true ↔
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
    object.table (.put view (.edge object.Carrier object.Carrier state target)) = true ↔
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
        exact object.put_get_formula state (assembleGet object state)
          (IndependentCarrierGraph.edge_assemble object.Carrier input.View
            (getTable object.table) object.get_lawful state)
      get_put := fun state view => by
        apply (get_edge_iff object (assemblePut object state view) view).mp
        exact object.get_put_formula state (assemblePut object state view) view
          (IndependentCarrierGraph.edge_assemble object.Carrier object.Carrier
            (putTable object.table view) (object.put_lawful view) state)
      put_put := fun state first second => by
        symm
        apply (put_edge_iff object state (assemblePut object (assemblePut object state first) second)
          second).mp
        exact object.put_put_formula state (assemblePut object state first)
          (assemblePut object (assemblePut object state first) second) first second
          ⟨IndependentCarrierGraph.edge_assemble object.Carrier object.Carrier
              (putTable object.table first) (object.put_lawful first) state,
            IndependentCarrierGraph.edge_assemble object.Carrier object.Carrier
              (putTable object.table second) (object.put_lawful second)
                (assemblePut object state first)⟩
      finite_fiber := by
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
    ObjectTable input
  | .get query => IndependentCarrierGraph.read data.Carrier input.View data.get query
  | .put view query =>
      IndependentCarrierGraph.read data.Carrier data.Carrier
        (fun state => data.put state view) query

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
  Carrier := lens.Carrier
  table := readDataTable lens.toLensData
  get_lawful := IndependentCarrierGraph.read_isLawful _ _ lens.get
  put_lawful view := IndependentCarrierGraph.read_isLawful _ _
    (fun state => lens.put state view)
  put_get_formula state view := by
    change
      IndependentCarrierGraph.read lens.Carrier input.View lens.get
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
    change
      IndependentCarrierGraph.read lens.Carrier lens.Carrier
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
    change
      (IndependentCarrierGraph.read lens.Carrier lens.Carrier
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
  fiber_finite :=
    Finite.of_equiv lens.Fiber (readFiberEquiv lens).symm

/-- Reading after primitive object assembly recovers the whole tagged table. -/
@[simp] theorem readObject_assembleObject {input : LensFamilyInput.{u}}
    (object : Object input) :
    readObject (assembleObject object) = object := by
  apply Object.ext
  · rfl
  funext query
  cases query with
  | get query =>
      exact congrFun (IndependentCarrierGraph.read_assemble object.Carrier input.View
        (getTable object.table) object.get_lawful) query
  | put view query =>
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
  /-- A source-object primitive cell. -/
  | source (query : ObjectQuery input)
  /-- A target-object primitive cell. -/
  | target (query : ObjectQuery input)
  /-- A candidate state-map graph cell. -/
  | map (query : GraphQuery.{u})

/-- Combine fixed endpoint tables and one candidate state-map table solely for
evaluation of the closed Hom-preservation formulas. -/
def homLawTable {input : LensFamilyInput.{u}} (source target : Object input)
    (table : GraphTable.{u}) : HomQuery input → Bool
  | .source query => source.table query
  | .target query => target.table query
  | .map query => table query

/-- Finite formula saying that one true state-map edge preserves one `get`
value. -/
def getPreservationFormula (input : LensFamilyInput.{u})
    (sourceCarrier targetCarrier : Type u)
    (source : sourceCarrier) (target : targetCarrier) (view : input.View) :
    IndependentFiniteLawFormula.BoolFormula.{u + 1, 0} (HomQuery input) :=
  .implies
    (.and
      (.cell (.map (.edge sourceCarrier targetCarrier source target)) true)
      (.cell (.source (.get
        (.edge sourceCarrier input.View source view))) true))
    (.cell (.target (.get
      (.edge targetCarrier input.View target view))) true)

/-- Finite formula saying that one state-map edge and the corresponding source
and target update edges determine the updated state-map edge. -/
def putPreservationFormula (input : LensFamilyInput.{u})
    (sourceCarrier targetCarrier : Type u)
    (source source' : sourceCarrier) (target target' : targetCarrier)
    (view : input.View) :
    IndependentFiniteLawFormula.BoolFormula.{u + 1, 0} (HomQuery input) :=
  .implies
    (.and
      (.and
        (.cell (.map (.edge sourceCarrier targetCarrier source target)) true)
        (.cell (.source (.put view
          (.edge sourceCarrier sourceCarrier source source'))) true))
      (.cell (.target (.put view
        (.edge targetCarrier targetCarrier target target'))) true))
    (.cell (.map (.edge sourceCarrier targetCarrier source' target')) true)

/-- A primitive local Hom is one lawful candidate state-map graph together
with the two finite preservation formula families. -/
@[ext]
structure Hom {input : LensFamilyInput.{u}} (source target : Object input) where
  /-- Candidate state-map graph table. -/
  table : GraphTable.{u}
  /-- The state-map graph is total and typed at the selected carriers. -/
  lawful : IndependentCarrierGraph.IsLawful source.Carrier target.Carrier table
  /-- Every fixed-point `get` preservation formula evaluates. -/
  get_formula : ∀ sourceState targetState view,
    (getPreservationFormula input source.Carrier target.Carrier
      sourceState targetState view).evaluate (homLawTable source target table)
  /-- Every fixed-point `put` preservation formula evaluates. -/
  put_formula : ∀ sourceState sourceState' targetState targetState' view,
    (putPreservationFormula input source.Carrier target.Carrier
      sourceState sourceState' targetState targetState' view).evaluate
        (homLawTable source target table)

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
    exact morphism.get_formula state image view
      ⟨(morphism.edge_iff state image).mpr rfl,
        (get_edge_iff source state view).mpr rfl⟩
  put_naturality state view := by
    let image := morphism.toFun state
    let source' := assemblePut source state view
    let target' := assemblePut target image view
    apply (morphism.edge_iff source' target').mp
    exact morphism.put_formula state source' image target' view
      ⟨⟨(morphism.edge_iff state image).mpr rfl,
          (put_edge_iff source state source' view).mpr rfl⟩,
        (put_edge_iff target image target' view).mpr rfl⟩

/-- Read a semantic Hom into a primitive state-map graph and its finite
preservation formulas. -/
def readHom {input : LensFamilyInput.{u}}
    {source target : LensRealization input.View input.reference}
    (morphism : source ⟶ target) : Hom (readObject source) (readObject target) where
  table := IndependentCarrierGraph.read source.Carrier target.Carrier morphism.toFun
  lawful := IndependentCarrierGraph.read_isLawful _ _ morphism.toFun
  get_formula sourceState targetState view := by
    change
      (IndependentCarrierGraph.read source.Carrier target.Carrier morphism.toFun
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
    change
      ((IndependentCarrierGraph.read source.Carrier target.Carrier morphism.toFun
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
    exact morphism.get_formula state image view
      ⟨(morphism.edge_iff state image).mpr rfl,
        (IndependentCarrierGraph.read_edge source.Carrier input.View source.get
          state view).mpr rfl⟩
  put_naturality state view := by
    let image := morphism.toFun state
    let source' := source.put state view
    let target' := target.put image view
    apply (morphism.edge_iff source' target').mp
    exact morphism.put_formula state source' image target' view
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
  exact IndependentCarrierGraph.read_assemble source.Carrier target.Carrier
    morphism.table morphism.lawful

/-- Direct primitive identity built from the carrier-graph diagonal. -/
def identityHom {input : LensFamilyInput.{u}} (object : Object input) :
    Hom object object where
  table := IndependentCarrierGraph.identity object.Carrier
  lawful := IndependentCarrierGraph.identity_isLawful object.Carrier
  get_formula source target view := by
    change
      (IndependentCarrierGraph.identity object.Carrier
          (.edge object.Carrier object.Carrier source target) = true ∧
        object.table (.get (.edge object.Carrier input.View source view)) = true) →
        object.table (.get (.edge object.Carrier input.View target view)) = true
    rintro ⟨identityEdge, sourceEdge⟩
    have equality :=
      (IndependentCarrierGraph.identity_edge object.Carrier source target).mp identityEdge
    subst target
    exact sourceEdge
  put_formula source source' target target' view := by
    change
      ((IndependentCarrierGraph.identity object.Carrier
          (.edge object.Carrier object.Carrier source target) = true ∧
        object.table (.put view
          (.edge object.Carrier object.Carrier source source')) = true) ∧
        object.table (.put view
          (.edge object.Carrier object.Carrier target target')) = true) →
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
  table := IndependentCarrierGraph.compose source.Carrier middle.Carrier target.Carrier
    first.table first.lawful second.table
  lawful := IndependentCarrierGraph.compose_isLawful
    source.Carrier middle.Carrier target.Carrier first.table first.lawful
      second.table second.lawful
  get_formula sourceState targetState view := by
    change
      (IndependentCarrierGraph.compose source.Carrier middle.Carrier target.Carrier
          first.table first.lawful second.table
            (.edge source.Carrier target.Carrier sourceState targetState) = true ∧
        source.table (.get
          (.edge source.Carrier input.View sourceState view)) = true) →
        target.table (.get
          (.edge target.Carrier input.View targetState view)) = true
    rintro ⟨compositeEdge, sourceEdge⟩
    let middleState := first.toFun sourceState
    have secondEdge :
        second.table (.edge middle.Carrier target.Carrier middleState targetState) = true := by
      simpa [middleState, IndependentCarrierGraph.compose_edge] using compositeEdge
    have middleEdge :
        middle.table (.get
          (.edge middle.Carrier input.View middleState view)) = true :=
      first.get_formula sourceState middleState view
        ⟨(first.edge_iff sourceState middleState).mpr rfl, sourceEdge⟩
    exact second.get_formula middleState targetState view
      ⟨secondEdge, middleEdge⟩
  put_formula sourceState sourceState' targetState targetState' view := by
    change
      ((IndependentCarrierGraph.compose source.Carrier middle.Carrier target.Carrier
          first.table first.lawful second.table
            (.edge source.Carrier target.Carrier sourceState targetState) = true ∧
        source.table (.put view
          (.edge source.Carrier source.Carrier sourceState sourceState')) = true) ∧
        target.table (.put view
          (.edge target.Carrier target.Carrier targetState targetState')) = true) →
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
        middle.table (.put view
          (.edge middle.Carrier middle.Carrier middleState targetMiddle)) = true :=
      IndependentCarrierGraph.edge_assemble middle.Carrier middle.Carrier
        (putTable middle.table view) (middle.put_lawful view) middleState
    have firstEdge' :
        first.table (.edge source.Carrier middle.Carrier sourceState' targetMiddle) = true :=
      first.put_formula sourceState sourceState' middleState targetMiddle view
        ⟨⟨firstEdge, sourcePutEdge⟩, middlePutEdge⟩
    have middleState'_eq : middleState' = targetMiddle :=
      (first.edge_iff sourceState' targetMiddle).mp firstEdge'
    have secondEdge' :
        second.table (.edge middle.Carrier target.Carrier targetMiddle targetState') = true :=
      second.put_formula middleState targetMiddle targetState targetState' view
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
    exact IndependentCarrierGraph.identity_compose _ _ morphism.table morphism.lawful
  comp_id morphism := by
    apply Hom.ext
    exact IndependentCarrierGraph.compose_identity _ _ morphism.table morphism.lawful
  assoc first second third := by
    apply Hom.ext
    exact IndependentCarrierGraph.compose_assoc _ _ _ _
      first.table first.lawful second.table second.lawful third.table third.lawful

/-- Reading sends the semantic identity to the direct primitive diagonal. -/
theorem readHom_id {input : LensFamilyInput.{u}}
    (lens : LensRealization input.View input.reference) :
    readHom (𝟙 lens) = identityHom (readObject lens) := by
  apply Hom.ext
  rfl

/-- Reading sends semantic composition to direct primitive graph composition. -/
theorem readHom_comp {input : LensFamilyInput.{u}}
    {source middle target : LensRealization input.View input.reference}
    (first : source ⟶ middle) (second : middle ⟶ target) :
    readHom (first ≫ second) = composeHom (readHom first) (readHom second) := by
  apply Hom.ext
  exact IndependentCarrierGraph.read_compose source.Carrier middle.Carrier target.Carrier
    first.toFun second.toFun

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
        morphism.toFun query := rfl

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
  exact morphism.get_formula state image input.reference
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
    finiteLocalValue (readObject lens).Fiber ≅
      (lensSemanticFiberReading input).obj lens :=
  FintypeCat.equivEquivIso (readFiberEquiv lens)

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

/-- Agreement on the finite support of a put-get instance preserves its
evaluation. -/
theorem putGetFormula_evaluate_iff_of_support
    (input : LensFamilyInput.{u}) (C : Type u) (c : C) (view : input.View)
    (first second : ObjectTable input)
    (agree : ∀ query ∈ (putGetFormula input C c view).support,
      first query = second query) :
    (putGetFormula input C c view).evaluate first ↔
      (putGetFormula input C c view).evaluate second :=
  IndependentFiniteLawFormula.BoolFormula.evaluate_iff_of_support
    first second _ agree

/-- Agreement on the finite support of a get-put instance preserves its
evaluation. -/
theorem getPutFormula_evaluate_iff_of_support
    (input : LensFamilyInput.{u}) (C : Type u) (c d : C) (view : input.View)
    (first second : ObjectTable input)
    (agree : ∀ query ∈ (getPutFormula input C c d view).support,
      first query = second query) :
    (getPutFormula input C c d view).evaluate first ↔
      (getPutFormula input C c d view).evaluate second :=
  IndependentFiniteLawFormula.BoolFormula.evaluate_iff_of_support
    first second _ agree

/-- Agreement on the finite support of a put-put instance preserves its
evaluation. -/
theorem putPutFormula_evaluate_iff_of_support
    (input : LensFamilyInput.{u}) (C : Type u) (c d e : C)
    (firstView secondView : input.View) (first second : ObjectTable input)
    (agree : ∀ query ∈
      (putPutFormula input C c d e firstView secondView).support,
      first query = second query) :
    (putPutFormula input C c d e firstView secondView).evaluate first ↔
      (putPutFormula input C c d e firstView secondView).evaluate second :=
  IndependentFiniteLawFormula.BoolFormula.evaluate_iff_of_support
    first second _ agree

/-- Agreement on the finite support of a get-preservation instance preserves
its evaluation. -/
theorem getPreservationFormula_evaluate_iff_of_support
    (input : LensFamilyInput.{u}) (C D : Type u) (c : C) (d : D)
    (view : input.View) (first second : HomQuery input → Bool)
    (agree : ∀ query ∈ (getPreservationFormula input C D c d view).support,
      first query = second query) :
    (getPreservationFormula input C D c d view).evaluate first ↔
      (getPreservationFormula input C D c d view).evaluate second :=
  IndependentFiniteLawFormula.BoolFormula.evaluate_iff_of_support
    first second _ agree

/-- Agreement on the finite support of a put-preservation instance preserves
its evaluation. -/
theorem putPreservationFormula_evaluate_iff_of_support
    (input : LensFamilyInput.{u}) (C D : Type u)
    (c c' : C) (d d' : D) (view : input.View)
    (first second : HomQuery input → Bool)
    (agree : ∀ query ∈
      (putPreservationFormula input C D c c' d d' view).support,
      first query = second query) :
    (putPreservationFormula input C D c c' d d' view).evaluate first ↔
      (putPreservationFormula input C D c c' d d' view).evaluate second :=
  IndependentFiniteLawFormula.BoolFormula.evaluate_iff_of_support
    first second _ agree

/-- A put-get formula evaluates exactly when the corresponding assembled
point implication holds. -/
theorem putGetFormula_evaluate_iff
    {input : LensFamilyInput.{u}} (object : Object input)
    (state : object.Carrier) (view : input.View) :
    (putGetFormula input object.Carrier state view).evaluate object.table ↔
      (assembleGet object state = view → assemblePut object state view = state) := by
  constructor
  · intro formula getEquality
    exact (put_edge_iff object state state view).mp
      (formula ((get_edge_iff object state view).mpr getEquality))
  · intro implication getEdge
    exact (put_edge_iff object state state view).mpr
      (implication ((get_edge_iff object state view).mp getEdge))

/-- A get-put formula evaluates exactly when the corresponding assembled
point implication holds. -/
theorem getPutFormula_evaluate_iff
    {input : LensFamilyInput.{u}} (object : Object input)
    (state target : object.Carrier) (view : input.View) :
    (getPutFormula input object.Carrier state target view).evaluate object.table ↔
      (assemblePut object state view = target → assembleGet object target = view) := by
  constructor
  · intro formula putEquality
    exact (get_edge_iff object target view).mp
      (formula ((put_edge_iff object state target view).mpr putEquality))
  · intro implication putEdge
    exact (get_edge_iff object target view).mpr
      (implication ((put_edge_iff object state target view).mp putEdge))

/-- A put-put formula evaluates exactly when the corresponding assembled
two-update point implication holds. -/
theorem putPutFormula_evaluate_iff
    {input : LensFamilyInput.{u}} (object : Object input)
    (state middle target : object.Carrier) (first second : input.View) :
    (putPutFormula input object.Carrier state middle target first second).evaluate
        object.table ↔
      (assemblePut object state first = middle →
        assemblePut object middle second = target →
        assemblePut object state second = target) := by
  constructor
  · intro formula firstEquality secondEquality
    exact (put_edge_iff object state target second).mp
      (formula
        ⟨(put_edge_iff object state middle first).mpr firstEquality,
          (put_edge_iff object middle target second).mpr secondEquality⟩)
  · intro implication edges
    exact (put_edge_iff object state target second).mpr
      (implication
        ((put_edge_iff object state middle first).mp edges.1)
        ((put_edge_iff object middle target second).mp edges.2))

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
      (formula
        ⟨(morphism.edge_iff sourceState targetState).mpr mapEquality,
          (get_edge_iff source sourceState view).mpr sourceEquality⟩)
  · intro implication edges
    exact (get_edge_iff target targetState view).mpr
      (implication
        ((morphism.edge_iff sourceState targetState).mp edges.1)
        ((get_edge_iff source sourceState view).mp edges.2))

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
      (formula
        ⟨⟨(morphism.edge_iff sourceState targetState).mpr mapEquality,
            (put_edge_iff source sourceState sourceState' view).mpr sourceEquality⟩,
          (put_edge_iff target targetState targetState' view).mpr targetEquality⟩)
  · intro implication edges
    exact (morphism.edge_iff sourceState' targetState').mpr
      (implication
        ((morphism.edge_iff sourceState targetState).mp edges.1.1)
        ((put_edge_iff source sourceState sourceState' view).mp edges.1.2)
        ((put_edge_iff target targetState targetState' view).mp edges.2))

/-! ### Concrete positive and rejection fixtures -/

/-- Raw ignored-update cells used to test that the finite get-put formula is
not vacuous. -/
def ignoredUpdateTable : ObjectTable ({ View := Bool, reference := false } : LensFamilyInput) :=
  readDataTable LensRealization.ignoredUpdateData

/-- The concrete ignored-update table fails the get-put formula at
`state = false`, `target = false`, and `view = true`. -/
theorem ignoredUpdateTable_rejected :
    ¬ (getPutFormula ({ View := Bool, reference := false } : LensFamilyInput)
      Bool false false true).evaluate ignoredUpdateTable := by
  intro formula
  have conclusion := formula
    ((IndependentCarrierGraph.read_edge Bool Bool
      (fun state => LensRealization.ignoredUpdateData.put state true)
      false false).mpr rfl)
  have impossible :=
    (IndependentCarrierGraph.read_edge Bool Bool
      LensRealization.ignoredUpdateData.get false true).mp conclusion
  exact Bool.noConfusion impossible

/-- Reading the existing noninvertible `constantFalseHom` produces an admitted
primitive Hom in the same local category used by the main equivalence. -/
def booleanFiberInput : LensFamilyInput where
  View := Unit
  reference := ()

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
