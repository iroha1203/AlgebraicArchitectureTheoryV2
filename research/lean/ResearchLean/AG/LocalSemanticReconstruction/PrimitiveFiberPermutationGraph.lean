import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.Group.Subgroup.Basic
import Formal.Util.AssertStandardAxioms

/-!
# Primitive graph presentation of fiber-preserving permutations

For an arbitrary map `normalize : α → β`, a fiber-preserving permutation of
`α` is presented by its Bool-valued graph.  The presentation stores one finite
local value for each ordered pair of points, together with independent
row-existence, row-uniqueness, column-existence, column-uniqueness, and fiber
compatibility laws.  It does not store a function, equivalence, permutation,
or completed inverse.

The graph assembles to a permutation by the unique row witness.  The unique
column witness supplies the inverse, so read and assembly are mutually inverse.
Transporting the group law through these maps gives a multiplicative
equivalence with the full subgroup of fiber-preserving permutations.  A final
formula identifies the transported multiplication with relational graph
composition.

## Implementation notes

The group operations on graph codes are transported through the proved
read/assembly equivalence.  They are not additional fields of the code.  The
relational multiplication theorem exposes the resulting local rule and fixes
the order forced by Mathlib's permutation multiplication.
-/

namespace AAT.AG.LocalSemanticReconstruction

noncomputable section

namespace PrimitiveFiberPermutationGraph

universe u v

variable {α : Type u} {β : Type v}

/-- All permutations preserving the fibers of `normalize`. -/
def FiberPermutationSubgroup (normalize : α → β) :
    Subgroup (Equiv.Perm α) where
  carrier := {permutation | ∀ value, normalize (permutation value) = normalize value}
  one_mem' := by intro value; rfl
  mul_mem' := by
    intro first second first_mem second_mem value
    change normalize (first (second value)) = normalize value
    rw [first_mem, second_mem]
  inv_mem' := by
    intro permutation permutation_mem value
    have preserved := permutation_mem (permutation⁻¹ value)
    simpa using preserved.symm

/-- Independent Bool-valued local graph data for one fiber-preserving
permutation.  No completed map or inverse is retained. -/
structure GraphCode (normalize : α → β) where
  /-- One finite local value for each ordered pair. -/
  edge : α → α → Bool
  /-- Every source has exactly one outgoing true edge. -/
  row_existsUnique : ∀ source, ∃! target, edge source target = true
  /-- Every target has exactly one incoming true edge. -/
  column_existsUnique : ∀ target, ∃! source, edge source target = true
  /-- True edges remain inside one normalization fiber. -/
  fiber_eq : ∀ {source target}, edge source target = true →
    normalize target = normalize source

namespace GraphCode

variable {normalize : α → β}

/-- Graph codes are determined by their Bool-valued local readings. -/
@[ext]
theorem ext {first second : GraphCode normalize}
    (edge_eq : first.edge = second.edge) : first = second := by
  cases first
  cases second
  cases edge_eq
  rfl

/-- Target selected by the unique outgoing edge. -/
def target (code : GraphCode normalize) (source : α) : α :=
  Classical.choose (code.row_existsUnique source)

/-- The selected target is joined to its source. -/
theorem edge_target (code : GraphCode normalize) (source : α) :
    code.edge source (code.target source) = true :=
  (Classical.choose_spec (code.row_existsUnique source)).1

/-- Every true outgoing edge has the selected target. -/
theorem target_eq_of_edge (code : GraphCode normalize)
    {source target : α} (edge : code.edge source target = true) :
    code.target source = target :=
  ((Classical.choose_spec (code.row_existsUnique source)).2 target edge).symm

/-- A local edge is true exactly when its endpoint is the selected target. -/
theorem edge_eq_true_iff_target_eq (code : GraphCode normalize)
    (source target : α) :
    code.edge source target = true ↔ code.target source = target := by
  constructor
  · exact code.target_eq_of_edge
  · intro equality
    rw [← equality]
    exact code.edge_target source

/-- Source selected by the unique incoming edge. -/
def source (code : GraphCode normalize) (target : α) : α :=
  Classical.choose (code.column_existsUnique target)

/-- The selected source is joined to its target. -/
theorem edge_source (code : GraphCode normalize) (target : α) :
    code.edge (code.source target) target = true :=
  (Classical.choose_spec (code.column_existsUnique target)).1

/-- Every true incoming edge has the selected source. -/
theorem source_eq_of_edge (code : GraphCode normalize)
    {source target : α} (edge : code.edge source target = true) :
    code.source target = source :=
  ((Classical.choose_spec (code.column_existsUnique target)).2 source edge).symm

/-- The selected source followed by the selected target is identity. -/
theorem target_source (code : GraphCode normalize) (target : α) :
    code.target (code.source target) = target :=
  code.target_eq_of_edge (code.edge_source target)

/-- The selected target followed by the selected source is identity. -/
theorem source_target (code : GraphCode normalize) (source : α) :
    code.source (code.target source) = source :=
  code.source_eq_of_edge (code.edge_target source)

/-- Assemble the unique row and column witnesses into a permutation. -/
def targetEquiv (code : GraphCode normalize) : Equiv.Perm α where
  toFun := code.target
  invFun := code.source
  left_inv := code.source_target
  right_inv := code.target_source

/-- The assembled permutation preserves every normalization fiber. -/
theorem target_normalize (code : GraphCode normalize) (source : α) :
    normalize (code.target source) = normalize source :=
  code.fiber_eq (code.edge_target source)

/-- Assemble a primitive graph into the full fiber-preserving permutation
subgroup. -/
def assemble (code : GraphCode normalize) :
    FiberPermutationSubgroup normalize :=
  ⟨code.targetEquiv, by
    show ∀ source, normalize (code.targetEquiv source) = normalize source
    exact code.target_normalize⟩

variable [DecidableEq α]

/-- Read a fiber-preserving permutation pointwise as finite Bool graph data. -/
def read (permutation : FiberPermutationSubgroup normalize) :
    GraphCode normalize where
  edge source target := decide (permutation.1 source = target)
  row_existsUnique source := by
    simp only [decide_eq_true_eq]
    exact ⟨permutation.1 source, rfl, fun target equality => equality.symm⟩
  column_existsUnique target := by
    simp only [decide_eq_true_eq]
    refine ⟨permutation.1.symm target, permutation.1.apply_symm_apply target, ?_⟩
    intro source equality
    apply permutation.1.injective
    exact equality.trans (permutation.1.apply_symm_apply target).symm
  fiber_eq := by
    intro source target equality
    have target_eq : permutation.1 source = target :=
      of_decide_eq_true equality
    rw [← target_eq]
    have preserved : ∀ value,
        normalize (permutation.1 value) = normalize value :=
      permutation.property
    exact preserved source

/-- Reading exposes the ordinary graph equation. -/
@[simp]
theorem read_edge_eq_true_iff
    (permutation : FiberPermutationSubgroup normalize) (source target : α) :
    (read permutation).edge source target = true ↔
      permutation.1 source = target := by
  simp [read]

/-- Assembly after reading recovers the complete fiber-preserving
permutation. -/
@[simp]
theorem assemble_read (permutation : FiberPermutationSubgroup normalize) :
    assemble (read permutation) = permutation := by
  apply Subtype.ext
  apply Equiv.Perm.ext
  intro source
  exact (read permutation).target_eq_of_edge (by simp [read])

/-- Reading after assembly recovers every primitive local edge. -/
@[simp]
theorem read_assemble (code : GraphCode normalize) :
    read (assemble code) = code := by
  apply GraphCode.ext
  funext source target
  apply Bool.eq_iff_iff.mpr
  simpa [read] using (code.edge_eq_true_iff_target_eq source target).symm

/-- Primitive graph codes and all fiber-preserving permutations are
equivalent, with both inverse laws exposed above. -/
def graphEquivFiberPermutation :
    GraphCode normalize ≃ FiberPermutationSubgroup normalize where
  toFun := assemble
  invFun := read
  left_inv := read_assemble
  right_inv := assemble_read

/-- Assembly is injective because graph reading is its left inverse. -/
theorem assemble_injective : Function.Injective
    (assemble : GraphCode normalize → FiberPermutationSubgroup normalize) :=
  graphEquivFiberPermutation.injective

/-! ## Transported group law and its local relational formula -/

/-- Identity graph transported from the identity fiber permutation. -/
instance : One (GraphCode normalize) :=
  ⟨read 1⟩

/-- Graph product transported from composition of assembled permutations. -/
instance : Mul (GraphCode normalize) :=
  ⟨fun first second => read (assemble first * assemble second)⟩

/-- Graph inverse transported from the inverse assembled permutation. -/
instance : Inv (GraphCode normalize) :=
  ⟨fun code => read ((assemble code)⁻¹)⟩

@[simp]
theorem assemble_one : assemble (1 : GraphCode normalize) = 1 :=
  assemble_read 1

@[simp]
theorem assemble_mul (first second : GraphCode normalize) :
    assemble (first * second) = assemble first * assemble second :=
  assemble_read _

@[simp]
theorem assemble_inv (code : GraphCode normalize) :
    assemble code⁻¹ = (assemble code)⁻¹ :=
  assemble_read _

/-- The transported operations form a group because assembly is injective and
preserves all three operations. -/
instance : Group (GraphCode normalize) where
  mul_assoc first second third := by
    apply assemble_injective
    simp only [assemble_mul]
    exact mul_assoc _ _ _
  one_mul code := by
    apply assemble_injective
    simp only [assemble_mul, assemble_one, one_mul]
  mul_one code := by
    apply assemble_injective
    simp only [assemble_mul, assemble_one, mul_one]
  inv_mul_cancel code := by
    apply assemble_injective
    simp only [assemble_mul, assemble_inv, inv_mul_cancel, assemble_one]

/-- The read/assembly equivalence is multiplicative. -/
def graphMulEquivFiberPermutation :
    GraphCode normalize ≃* FiberPermutationSubgroup normalize where
  toFun := assemble
  invFun := read
  left_inv := read_assemble
  right_inv := assemble_read
  map_mul' := assemble_mul

/-- The selected target of a graph product is ordinary permutation
composition. -/
theorem target_mul (first second : GraphCode normalize) (source : α) :
    (first * second).target source =
      first.target (second.target source) := by
  have equality := congrArg
    (fun permutation : FiberPermutationSubgroup normalize =>
      permutation.1 source)
    (assemble_mul first second)
  simpa [assemble, targetEquiv] using equality

/-- Multiplication of graph codes is relational composition.  The second
graph is followed by the first, matching permutation multiplication. -/
theorem mul_edge_eq_true_iff (first second : GraphCode normalize)
    (source target : α) :
    (first * second).edge source target = true ↔
      ∃ middle,
        second.edge source middle = true ∧
          first.edge middle target = true := by
  rw [edge_eq_true_iff_target_eq]
  rw [target_mul]
  constructor
  · intro equality
    exact ⟨second.target source, second.edge_target source,
      (first.edge_eq_true_iff_target_eq _ _).mpr equality⟩
  · rintro ⟨middle, secondEdge, firstEdge⟩
    rw [second.target_eq_of_edge secondEdge]
    exact first.target_eq_of_edge firstEdge

/-- The identity graph is the diagonal relation. -/
theorem one_edge_eq_true_iff (source target : α) :
    (1 : GraphCode normalize).edge source target = true ↔ source = target := by
  rw [edge_eq_true_iff_target_eq]
  have equality := congrArg
    (fun permutation : FiberPermutationSubgroup normalize =>
      permutation.1 source) assemble_one
  change (1 : GraphCode normalize).target source = target ↔ source = target
  have target_eq : (1 : GraphCode normalize).target source = source := by
    simpa [assemble, targetEquiv] using equality
  rw [target_eq]

end GraphCode

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.PrimitiveFiberPermutationGraph

end PrimitiveFiberPermutationGraph

end

end AAT.AG.LocalSemanticReconstruction
