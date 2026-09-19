import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitiveDeclaration
import Formal.Util.AssertStandardAxioms

/-!
# Pointed and upper Atom equivalences from the common Hom cells

Both native Atom equivalences have their own primitive direction-tagged point
pairs. Exact-one rows and the two-cell inverse rule construct each equivalence.
Their native whole-equivalence equality is derived from forward point agreement;
it is not a local law field. These constructions use the common Hom declaration
and do not require selected source/target geometry objects.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Atom

noncomputable section

universe u v

variable {U : AtomCarrier.{u}}

/-- Direction-tagged point pairs on the primitive Atom carrier, common to all realizations. -/
abbrev PointTable (U : AtomCarrier.{u}) := Direction → U.Atom → U.Atom → Bool

/-- Primitive inverse conditions state only exact-one rows and one forward/backward point comparison. -/
structure IsLawful (p : PointTable U) : Prop where
  /-- Every source Atom has exactly one forward image. -/
  forward : ∀ a, ∃! b, p .forward a b = true
  /-- Every target Atom has exactly one backward image. -/
  backward : ∀ b, ∃! a, p .backward a b = true
  /-- The two direction-tagged point readings are inverse at this pair. -/
  inverse : ∀ a b, p .forward a b = true ↔ p .backward a b = true

/-- Each direction's exact-one rows construct an existing primitive total-function graph. -/
def graph (p : PointTable U) (h : IsLawful p) : Direction → PrimitiveFunctionGraph.GraphCode U.Atom U.Atom
  | .forward => ⟨⟨fun a b => p .forward a b⟩, ⟨h.forward⟩⟩
  | .backward => ⟨⟨fun b a => p .backward a b⟩, ⟨h.backward⟩⟩

/-- Construct the native Atom equivalence from its two point families and inverse point condition. -/
def assemble (p : PointTable U) (h : IsLawful p) : U.Atom ≃ U.Atom where
  toFun := (graph p h .forward).assemble
  invFun := (graph p h .backward).assemble
  left_inv a := (graph p h .backward).target_eq_of_edge
    ((h.inverse a _).1 ((graph p h .forward).edge_target a))
  right_inv b := (graph p h .forward).target_eq_of_edge
    ((h.inverse _ b).2 ((graph p h .backward).edge_target b))

/-- Read one native equivalence as two Boolean point families in fixed source/target order. -/
def read (e : U.Atom ≃ U.Atom) : PointTable U := by
  classical
  exact fun direction a b => match direction with
    | .forward => decide (e a = b)
    | .backward => decide (e.symm b = a)

/-- Every native Atom equivalence satisfies the pointwise row and inverse rules. -/
theorem read_isLawful (e : U.Atom ≃ U.Atom) : IsLawful (read e) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro a
    simp only [read, decide_eq_true_eq]
    exact ⟨e a, rfl, fun b hb => hb.symm⟩
  · intro b
    simp only [read, decide_eq_true_eq]
    exact ⟨e.symm b, rfl, fun a ha => ha.symm⟩
  · intro a b
    simp only [read, decide_eq_true_eq]
    constructor
    · intro h
      rw [← h]
      exact e.symm_apply_apply a
    · intro h
      rw [← h]
      exact e.apply_symm_apply b

/-- The actual forward image has a true primitive point reading. -/
theorem edge_assemble (p : PointTable U) (h : IsLawful p) (a : U.Atom) :
    p .forward a (assemble p h a) = true := (graph p h .forward).edge_target a

/-- Any true forward pair determines exactly the assembled Atom image. -/
theorem assemble_eq_of_edge (p : PointTable U) (h : IsLawful p) {a b : U.Atom}
    (hab : p .forward a b = true) : assemble p h a = b := (graph p h .forward).target_eq_of_edge hab

/-- The primitive Atom assembler restores the full original native equivalence. -/
theorem assemble_read (e : U.Atom ≃ U.Atom) : assemble (read e) (read_isLawful e) = e := by
  apply Equiv.ext
  intro a
  exact congrFun (PrimitiveFunctionGraph.GraphCode.assemble_read e) a

/-- Both direction-tagged point families are restored by native assembly and re-reading. -/
theorem read_assemble (p : PointTable U) (h : IsLawful p) : read (assemble p h) = p := by
  classical
  funext direction a b
  apply Bool.eq_iff_iff.mpr
  cases direction with
  | forward =>
      simp only [read, decide_eq_true_eq]
      exact ((graph p h .forward).edge_eq_true_iff_target_eq a b).symm
  | backward =>
      simp only [read, decide_eq_true_eq]
      exact ((graph p h .backward).edge_eq_true_iff_target_eq b a).symm

/-- All native Atom equivalences have exact primitive point presentations. -/
def readingEquiv : (U.Atom ≃ U.Atom) ≃ {p : PointTable U // IsLawful p} where
  toFun e := ⟨read e, read_isLawful e⟩
  invFun p := assemble p.val p.property
  left_inv := assemble_read
  right_inv p := Subtype.ext (read_assemble p.val p.property)

/-- Extract the lower pointed-Atom cells directly from the common Hom table. -/
def pointed {mode : Mode} (t : Table.{u, v} U mode) : PointTable U :=
  fun direction a b => t (.pointedAtom direction a b)

/-- Extract the upper Atom cells independently from the same common Hom table. -/
def upper {mode : Mode} (t : Table.{u, v} U mode) : PointTable U :=
  fun direction a b => t (.atom direction a b)

/-- The native pointed/upper agreement is imposed only as equality of individual forward cells. -/
structure IsCoherent {mode : Mode} (t : Table.{u, v} U mode) : Prop where
  /-- The lower pointed component obeys the primitive equivalence rules. -/
  pointed : IsLawful (Atom.pointed t)
  /-- The upper component separately obeys those rules. -/
  upper : IsLawful (Atom.upper t)
  /-- The two role-tagged forward point readings agree. -/
  agree : ∀ a b, t (.pointedAtom .forward a b) = t (.atom .forward a b)

/-- Derive the original whole-equivalence agreement from local primitive point agreement. -/
theorem pointed_eq_upper {mode : Mode} (t : Table.{u, v} U mode) (h : IsCoherent t) :
    assemble (pointed t) h.pointed = assemble (upper t) h.upper := by
  apply Equiv.ext
  intro a
  have hp := edge_assemble (pointed t) h.pointed a
  have hu : upper t .forward a (assemble (pointed t) h.pointed a) = true := by
    exact (h.agree a _).symm.trans hp
  exact (assemble_eq_of_edge (upper t) h.upper hu).symm

/-- A single pointed/upper point mismatch is rejected even when both roles separately describe equivalences. -/
theorem mismatch_rejected {mode : Mode} (t : Table.{u, v} U mode) (a b : U.Atom)
    (hne : t (.pointedAtom .forward a b) ≠ t (.atom .forward a b)) : ¬ IsCoherent t :=
  fun h => hne (h.agree a b)

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Atom

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Atom
