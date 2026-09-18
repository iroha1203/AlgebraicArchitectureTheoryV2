import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Types.Basic
import Formal.Util.AssertStandardAxioms

/-!
# Primitive Bool graphs for arbitrary functions

An arbitrary function is presented by one Bool value for every ordered
source-target pair.  Raw graph data are separated from the total-functional
law saying that each source has exactly one true target.  No completed function
is stored in either layer.

The unique target assembles a function, while pointwise equality reads a
function back to a graph.  Both inverse laws are proved.  Graph composition is
then defined by readback of ordinary function composition and identified with
relational composition.  Wrapping types as objects produces a category whose
comparison functor to `Type` is explicitly fully faithful.

## Implementation notes

This module uses a Bool relation rather than storing a function so that every
primitive value remains one finite local reading.  Existence and uniqueness of
a true target in every row are a separate predicate; they are not placed in raw
data.  Equality decisions are
chosen classically inside `read`, avoiding a public `DecidableEq` premise.
The diagonal graph and a constant-false graph give positive and negative
fixtures for the new predicate.
-/

namespace AAT.AG.LocalSemanticReconstruction

noncomputable section

open CategoryTheory

namespace PrimitiveFunctionGraph

universe u v w

/-- Independent point-pair Bool data for a possible function graph. -/
structure GraphData (α : Type u) (β : Type v) where
  /-- One finite local value for each source-target pair. -/
  edge : α → β → Bool

/-- The exact-one row law characterizing graphs of total functions. -/
structure IsTotalFunctional (graph : GraphData α β) : Prop where
  /-- Every source has exactly one true target. -/
  row_existsUnique : ∀ source, ∃! target, graph.edge source target = true

/-- A primitive function graph is raw Bool data satisfying the independent
total-functional law. -/
abbrev GraphCode (α : Type u) (β : Type v) :=
  { graph : GraphData α β // IsTotalFunctional graph }

namespace GraphData

/-- Raw function-graph data are determined by all point-pair readings. -/
@[ext]
theorem ext {first second : GraphData α β}
    (edge_eq : first.edge = second.edge) : first = second := by
  cases first
  cases second
  cases edge_eq
  rfl

/-- The diagonal relation is the positive total-functional fixture. -/
noncomputable def diagonal : GraphData α α := by
  classical
  exact ⟨fun source target => decide (source = target)⟩

/-- Every diagonal relation is total and functional. -/
theorem diagonal_isTotalFunctional :
    IsTotalFunctional (diagonal : GraphData α α) := by
  classical
  constructor
  intro source
  simp only [diagonal, decide_eq_true_eq]
  exact ⟨source, rfl, fun target equality => equality.symm⟩

/-- The constant-false Bool relation is the negative fixture. -/
def falseBool : GraphData Bool Bool :=
  ⟨fun _ _ => false⟩

/-- The constant-false relation is not total. -/
theorem falseBool_not_isTotalFunctional :
    ¬ IsTotalFunctional falseBool := by
  intro total
  rcases total.row_existsUnique false with ⟨target, edge, _⟩
  simp [falseBool] at edge

end GraphData

namespace GraphCode

/-- The Bool relation underlying a primitive function graph. -/
def edge (code : GraphCode α β) : α → β → Bool :=
  code.1.edge

/-- Every source of a primitive function graph has one unique target. -/
theorem row_existsUnique (code : GraphCode α β) (source : α) :
    ∃! target, code.edge source target = true :=
  code.2.row_existsUnique source

/-- Primitive function graphs are determined by their point-pair readings. -/
@[ext]
theorem ext {first second : GraphCode α β}
    (edge_eq : first.edge = second.edge) : first = second := by
  apply Subtype.ext
  exact GraphData.ext edge_eq

/-- The target selected by the unique true edge in one row. -/
def target (code : GraphCode α β) (source : α) : β :=
  Classical.choose (code.row_existsUnique source)

/-- The selected target is joined to its source. -/
theorem edge_target (code : GraphCode α β) (source : α) :
    code.edge source (code.target source) = true :=
  (Classical.choose_spec (code.row_existsUnique source)).1

/-- Every true edge has the selected target. -/
theorem target_eq_of_edge (code : GraphCode α β)
    {source : α} {target : β} (edge : code.edge source target = true) :
    code.target source = target :=
  ((Classical.choose_spec (code.row_existsUnique source)).2 target edge).symm

/-- A point-pair reading is true exactly at the selected target. -/
theorem edge_eq_true_iff_target_eq (code : GraphCode α β)
    (source : α) (target : β) :
    code.edge source target = true ↔ code.target source = target := by
  constructor
  · exact code.target_eq_of_edge
  · intro equality
    rw [← equality]
    exact code.edge_target source

/-- Assemble the unique row targets into an ordinary function. -/
def assemble (code : GraphCode α β) : α → β :=
  code.target

/-- Read an arbitrary function pointwise as a primitive Bool graph. -/
noncomputable def read (function : α → β) : GraphCode α β := by
  classical
  refine ⟨⟨fun source target => decide (function source = target)⟩, ?_⟩
  constructor
  intro source
  simp only [decide_eq_true_eq]
  exact ⟨function source, rfl, fun target equality => equality.symm⟩

/-- Reading exposes the ordinary graph equation. -/
@[simp]
theorem read_edge_eq_true_iff (function : α → β) (source : α) (target : β) :
    (read function).edge source target = true ↔ function source = target := by
  simp [read, edge]

/-- Assembly after reading recovers every arbitrary function. -/
@[simp]
theorem assemble_read (function : α → β) :
    assemble (read function) = function := by
  funext source
  exact (read function).target_eq_of_edge (by simp)

/-- Reading after assembly recovers every primitive local edge. -/
@[simp]
theorem read_assemble (code : GraphCode α β) :
    read (assemble code) = code := by
  apply GraphCode.ext
  funext source target
  apply Bool.eq_iff_iff.mpr
  simpa [read, edge, assemble] using
    (code.edge_eq_true_iff_target_eq source target).symm

/-- Primitive function graphs and arbitrary functions are explicitly
equivalent. -/
noncomputable def graphEquivFunction : GraphCode α β ≃ (α → β) where
  toFun := assemble
  invFun := read
  left_inv := read_assemble
  right_inv := assemble_read

/-- Assembly is injective because graph reading is its left inverse. -/
theorem assemble_injective :
    Function.Injective (assemble : GraphCode α β → (α → β)) :=
  graphEquivFunction.injective

/-- Identity graph on one type. -/
noncomputable def id : GraphCode α α :=
  read _root_.id

/-- Composition of primitive graphs, with the second graph applied after the
first. -/
noncomputable def comp (first : GraphCode α β) (second : GraphCode β γ) :
    GraphCode α γ :=
  read (assemble second ∘ assemble first)

/-- Identity graph assembles to the identity function. -/
@[simp]
theorem assemble_id : assemble (id : GraphCode α α) = _root_.id :=
  assemble_read _

/-- Graph composition assembles to ordinary function composition. -/
@[simp]
theorem assemble_comp (first : GraphCode α β) (second : GraphCode β γ) :
    assemble (comp first second) = assemble second ∘ assemble first :=
  assemble_read _

/-- The selected target of a composite is ordinary function composition. -/
theorem target_comp (first : GraphCode α β) (second : GraphCode β γ)
    (source : α) :
    (comp first second).target source =
      second.target (first.target source) := by
  have equality := congrFun (assemble_comp first second) source
  exact equality

/-- Composition of primitive function graphs is relational composition. -/
theorem comp_edge_eq_true_iff (first : GraphCode α β)
    (second : GraphCode β γ) (source : α) (target : γ) :
    (comp first second).edge source target = true ↔
      ∃ middle,
        first.edge source middle = true ∧
          second.edge middle target = true := by
  rw [edge_eq_true_iff_target_eq, target_comp]
  constructor
  · intro equality
    exact ⟨first.target source, first.edge_target source,
      (second.edge_eq_true_iff_target_eq _ _).mpr equality⟩
  · rintro ⟨middle, firstEdge, secondEdge⟩
    rw [first.target_eq_of_edge firstEdge]
    exact second.target_eq_of_edge secondEdge

/-- The identity graph is the diagonal relation. -/
theorem id_edge_eq_true_iff (source target : α) :
    (id : GraphCode α α).edge source target = true ↔ source = target := by
  simp [id]

end GraphCode

/-! ## The category of primitive function graphs -/

/-- A type regarded as an object whose morphisms are primitive Bool graphs. -/
structure Object where
  /-- Carrier of the graph object. -/
  Carrier : Type u

namespace Object

/-- Primitive function graphs form a category by relationally characterized
composition. -/
noncomputable instance : CategoryTheory.Category.{u} Object.{u} where
  Hom source target := GraphCode source.Carrier target.Carrier
  id object := GraphCode.id
  comp first second := GraphCode.comp first second
  id_comp morphism := by
    apply GraphCode.assemble_injective
    simp
  comp_id morphism := by
    apply GraphCode.assemble_injective
    simp
  assoc first second third := by
    apply GraphCode.assemble_injective
    simp [Function.comp_def]

/-- Forget graph syntax and assemble every morphism as a function. -/
noncomputable def toType : Object.{u} ⥤ Type u where
  obj object := object.Carrier
  map morphism := GraphCode.assemble morphism
  map_id _ := GraphCode.assemble_id
  map_comp first second := GraphCode.assemble_comp first second

/-- The comparison with ordinary functions is fully faithful, with graph
reading as the explicit Hom inverse. -/
noncomputable def toTypeFullyFaithful : toType.FullyFaithful where
  preimage function := GraphCode.read function
  map_preimage function := GraphCode.assemble_read function
  preimage_map graph := GraphCode.read_assemble graph

/-- Fullness of graph assembly. -/
noncomputable instance toType_full : toType.Full :=
  toTypeFullyFaithful.full

/-- Faithfulness of graph assembly. -/
noncomputable instance toType_faithful : toType.Faithful :=
  toTypeFullyFaithful.faithful

end Object

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.PrimitiveFunctionGraph

end PrimitiveFunctionGraph

end

end AAT.AG.LocalSemanticReconstruction
