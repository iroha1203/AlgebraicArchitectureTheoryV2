import Formal.AG.Site.ContextCategory
import Formal.Util.AssertStandardAxioms

/-!
# Primitive context objects for independent local reconstruction

A context response is decomposed into three carrier roles, one primitive
extension value with its carrier, and individual predicate readings. The
architecture object appears in the support law, not in the query declaration.
No complete architecture context is retained as a table value.

## Implementation notes

The extension carrier and selected value are primitive native inputs, while
the three predicate families are collected from point responses. Overlap
values use these same context queries. Its four order laws are stated on the
constructed contexts, rather than supplied as a completed overlap package.
Connection of these dependent order instances to a common finite-query
declaration remains part of the later assembly obligation.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentContextObjectPrimitive

universe u

open Site

variable {U : AtomCarrier.{u}}

/-- The three different carrier roles of a minimal architecture context. -/
inductive CarrierRole where
  /-- Carrier of supports. -/
  | support
  /-- Carrier of axes. -/
  | axis
  /-- Carrier of observables. -/
  | observable

/-- One primitive extension value paired with its raw carrier reference. -/
abbrev ExtensionValue := (T : Type u) × T

/-- Context queries are declared before selecting the architecture object. -/
inductive Query (U : AtomCarrier.{u}) where
  /-- Read one of the three raw carrier references. -/
  | carrier (role : CarrierRole)
  /-- Read the primitive extension value and its type. -/
  | extension
  /-- Read support incidence at one candidate support and Atom. -/
  | support (K : Type u) (s : K) (a : U.Atom)
  /-- Read the axis predicate at one candidate axis. -/
  | axis (K : Type u) (a : K)
  /-- Read the observable predicate at one candidate observable. -/
  | observable (K : Type u) (x : K)

/-- Each response has the native primitive role of its query. -/
def Query.Value : Query U → Type (u + 1)
  | .carrier _ => Type u
  | .extension => ExtensionValue.{u}
  | .support _ _ _ => ULift.{u + 1} Prop
  | .axis _ _ => ULift.{u + 1} Prop
  | .observable _ _ => ULift.{u + 1} Prop

/-- Dependent primitive context table. -/
abbrev Table (U : AtomCarrier.{u}) := (q : Query U) → q.Value

/-- Read the carrier assigned to one context role. -/
abbrev carrier (t : Table U) (r : CarrierRole) : Type u := t (.carrier r)

/-- A predicate response can be true only at its role's selected carrier. -/
structure IsTyped (t : Table U) : Prop where
  /-- Inactive support candidates are uniformly false. -/
  support : ∀ K s a, K ≠ carrier t .support → ¬ (t (.support K s a)).down
  /-- Inactive axis candidates are uniformly false. -/
  axis : ∀ K a, K ≠ carrier t .axis → ¬ (t (.axis K a)).down
  /-- Inactive observable candidates are uniformly false. -/
  observable : ∀ K x, K ≠ carrier t .observable → ¬ (t (.observable K x)).down

/-- The primitive support law refers to the selected object's actual Atom family. -/
def IsLawful (A : ArchitectureObject U) (t : Table U) : Prop :=
  ∀ (s : carrier t .support) (a : U.Atom),
    (t (.support _ s a)).down → A.configuration.family.mem a

/-- Construct the native context from carriers, selected extension, and predicate points. -/
def assemble (A : ArchitectureObject U) (t : Table U) (hl : IsLawful A t) : ArchCtx A where
  minimal :=
    { Support := carrier t .support
      Axis := carrier t .axis
      Observable := carrier t .observable
      supportReads s a := (t (.support _ s a)).down
      supportReads_objectFamily := hl _ _
      axisReads a := (t (.axis _ a)).down
      observableReads x := (t (.observable _ x)).down }
  Extension := (t .extension).1
  extension := (t .extension).2

/-- Native contexts yield point responses with fixed inactive predicates. -/
noncomputable def read {A : ArchitectureObject U} (W : ArchCtx A) : Table U := by
  classical
  intro q
  cases q with
  | carrier r => cases r with
    | support => exact W.Support
    | axis => exact W.Axis
    | observable => exact W.Observable
  | extension => exact ⟨W.Extension, W.extension⟩
  | support K s a => exact ⟨if h : K = W.Support then W.minimal.supportReads (h ▸ s : W.Support) a else False⟩
  | axis K a => exact ⟨if h : K = W.Axis then W.minimal.axisReads (h ▸ a : W.Axis) else False⟩
  | observable K x => exact ⟨if h : K = W.Observable then W.minimal.observableReads (h ▸ x : W.Observable) else False⟩

/-- Native context readings use exactly the designated role carriers. -/
theorem read_isTyped {A : ArchitectureObject U} (W : ArchCtx A) : IsTyped (read W) where
  support K s a h := by
    change K ≠ W.Support at h
    simp [read, h]
  axis K a h := by
    change K ≠ W.Axis at h
    simp [read, h]
  observable K x h := by
    change K ≠ W.Observable at h
    simp [read, h]

/-- Native support incidence supplies the local family-membership law. -/
theorem read_isLawful {A : ArchitectureObject U} (W : ArchCtx A) : IsLawful A (read W) := by
  intro s a h
  exact W.minimal.supportReads_objectFamily (by simpa [read, carrier] using h)

/-- Every native context field is determined by its carrier and point families. -/
theorem minimal_ext {A : ArchitectureObject U} {M N : MinimalContext A}
    (hs : M.Support = N.Support) (ha : M.Axis = N.Axis) (ho : M.Observable = N.Observable)
    (hsp : HEq M.supportReads N.supportReads) (hap : HEq M.axisReads N.axisReads)
    (hop : HEq M.observableReads N.observableReads) : M = N := by
  cases M
  cases N
  cases hs
  cases ha
  cases ho
  cases hsp
  cases hap
  cases hop
  rfl

/-- The minimal context and primitive extension determine the full native context. -/
theorem context_ext {A : ArchitectureObject U} {W V : ArchCtx A}
    (hm : W.minimal = V.minimal) (he : W.Extension = V.Extension)
    (hv : HEq W.extension V.extension) : W = V := by
  cases W
  cases V
  cases hm
  cases he
  cases hv
  rfl

/-- Native assembly recovers every context carrier, predicate, and extension value. -/
theorem assemble_read {A : ArchitectureObject U} (W : ArchCtx A) :
    assemble A (read W) (read_isLawful W) = W := by
  apply context_ext (W := assemble A (read W) (read_isLawful W)) (V := W)
  · apply minimal_ext (M := (assemble A (read W) (read_isLawful W)).minimal) (N := W.minimal) rfl rfl rfl
    · apply heq_of_eq
      funext s a
      simp [assemble, read]
    · apply heq_of_eq
      funext a
      simp [assemble, read]
    · apply heq_of_eq
      funext x
      simp [assemble, read]
  · rfl
  · rfl

/-- Read-after-assemble restores active predicates and the unique inactive responses. -/
theorem read_assemble (A : ArchitectureObject U) (t : Table U) (ht : IsTyped t)
    (hl : IsLawful A t) : read (assemble A t hl) = t := by
  classical
  funext q
  cases q with
  | carrier r => cases r <;> rfl
  | extension => rfl
  | support K s a =>
    apply ULift.ext
    by_cases h : K = carrier t .support
    · subst K
      simp [read, assemble, ArchitectureContext.Support]
    · simp [read, assemble, ArchitectureContext.Support, h, ht.support K s a h]
  | axis K a =>
    apply ULift.ext
    by_cases h : K = carrier t .axis
    · subst K
      simp [read, assemble, ArchitectureContext.Axis]
    · simp [read, assemble, ArchitectureContext.Axis, h, ht.axis K a h]
  | observable K x =>
    apply ULift.ext
    by_cases h : K = carrier t .observable
    · subst K
      simp [read, assemble, ArchitectureContext.Observable]
    · simp [read, assemble, ArchitectureContext.Observable, h, ht.observable K x h]

/-- All native contexts have exact primitive presentations with no extra witness data. -/
noncomputable def readingEquiv (A : ArchitectureObject U) :
    ArchCtx A ≃ {t : Table U // IsTyped t ∧ IsLawful A t} where
  toFun W := ⟨read W, read_isTyped W, read_isLawful W⟩
  invFun t := assemble A t.val t.property.2
  left_inv := assemble_read
  right_inv t := Subtype.ext (read_assemble A t.val t.property.1 t.property.2)

/-- Primitive context readings distinguish every native context field. -/
theorem read_injective {A : ArchitectureObject U} : Function.Injective (read (A := A)) := by
  intro W V h
  apply (readingEquiv A).injective
  exact Subtype.ext h

namespace Overlap

/-- A selected overlap is read through one primitive context cell at a time. -/
inductive Query (A : ArchitectureObject U) where
  /-- Read one primitive of the context returned at a given triple. -/
  | context (base left right : ArchCtx A) (q : IndependentContextObjectPrimitive.Query U)

/-- The response retains the primitive value type of the underlying context query. -/
def Query.Value {A : ArchitectureObject U} : Query A → Type (u + 1)
  | .context _ _ _ q => q.Value

/-- Dependent table of overlap-context primitive responses. -/
abbrev Table (A : ArchitectureObject U) := (q : Query A) → q.Value

variable {A : ArchitectureObject U}

/-- Collect the primitive context table at one triple, before constructing a native context. -/
abbrev context (t : Table A) (base left right : ArchCtx A) :
    IndependentContextObjectPrimitive.Table U := fun q => t (.context base left right q)

/-- Every overlap context uses exactly its own role-specific carrier declarations. -/
def IsTyped (t : Table A) : Prop :=
  ∀ base left right, IndependentContextObjectPrimitive.IsTyped (context t base left right)

/-- Support incidence and the four independent overlap comparisons. -/
structure IsLawful (C : ContextPreorderCategory A) (t : Table A) : Prop where
  /-- Each overlap context reads only Atoms of the original architecture object. -/
  support : ∀ base left right,
    IndependentContextObjectPrimitive.IsLawful A (context t base left right)
  /-- The constructed overlap lies below the left input. -/
  left : ∀ base left right, C.le left base → C.le right base →
    C.le (IndependentContextObjectPrimitive.assemble A (context t base left right)
      (support base left right)) left
  /-- The constructed overlap lies below the right input. -/
  right : ∀ base left right, C.le left base → C.le right base →
    C.le (IndependentContextObjectPrimitive.assemble A (context t base left right)
      (support base left right)) right
  /-- The constructed overlap lies below the base. -/
  base : ∀ base left right, C.le left base → C.le right base →
    C.le (IndependentContextObjectPrimitive.assemble A (context t base left right)
      (support base left right)) base
  /-- Every common refinement lies below the constructed overlap. -/
  lift : ∀ base left right X, C.le left base → C.le right base → C.le X left → C.le X right →
    C.le X (IndependentContextObjectPrimitive.assemble A (context t base left right)
      (support base left right))

/-- Assemble a native overlap package after constructing each returned context from primitives. -/
def assemble (C : ContextPreorderCategory A) (t : Table A) (hl : IsLawful C t) :
    ContextOverlapPullback C where
  overlap base left right := IndependentContextObjectPrimitive.assemble A
    (context t base left right) (hl.support base left right)
  overlap_le_left := hl.left _ _ _
  overlap_le_right := hl.right _ _ _
  overlap_le_base := hl.base _ _ _
  overlap_lift := hl.lift _ _ _ _

/-- Read the primitive fields of each selected native overlap context. -/
noncomputable def read {C : ContextPreorderCategory A} (P : ContextOverlapPullback C) : Table A
  | .context base left right q => IndependentContextObjectPrimitive.read (P.overlap base left right) q

/-- Native overlap contexts satisfy exact primitive carrier activation. -/
theorem read_isTyped {C : ContextPreorderCategory A} (P : ContextOverlapPullback C) :
    IsTyped (read P) := fun base left right =>
  IndependentContextObjectPrimitive.read_isTyped (P.overlap base left right)

/-- Reconstructing a single overlap response returns its original native context. -/
theorem context_assemble_read {C : ContextPreorderCategory A} (P : ContextOverlapPullback C)
    (base left right : ArchCtx A)
    (hl : IndependentContextObjectPrimitive.IsLawful A (context (read P) base left right)) :
    IndependentContextObjectPrimitive.assemble A (context (read P) base left right) hl =
      P.overlap base left right :=
  IndependentContextObjectPrimitive.assemble_read (P.overlap base left right)

/-- The native overlap laws supply all four local order comparisons. -/
theorem read_isLawful {C : ContextPreorderCategory A} (P : ContextOverlapPullback C) :
    IsLawful C (read P) where
  support base left right := IndependentContextObjectPrimitive.read_isLawful (P.overlap base left right)
  left base left right hl hr := by
    simpa only [context_assemble_read] using P.overlap_le_left hl hr
  right base left right hl hr := by
    simpa only [context_assemble_read] using P.overlap_le_right hl hr
  base base left right hl hr := by
    simpa only [context_assemble_read] using P.overlap_le_base hl hr
  lift base left right X hl hr hXl hXr := by
    simpa only [context_assemble_read] using P.overlap_lift hl hr hXl hXr

/-- The selected context-valued function determines the native overlap package. -/
theorem overlap_ext {C : ContextPreorderCategory A} {P Q : ContextOverlapPullback C}
    (h : P.overlap = Q.overlap) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

/-- All native overlap data is recovered, without replacing equality by an isomorphism. -/
theorem assemble_read {C : ContextPreorderCategory A} (P : ContextOverlapPullback C) :
    assemble C (read P) (read_isLawful P) = P := by
  apply overlap_ext
  funext base left right
  exact context_assemble_read P base left right ((read_isLawful P).support base left right)

/-- Every overlap primitive cell is recovered after native assembly. -/
theorem read_assemble (C : ContextPreorderCategory A) (t : Table A) (ht : IsTyped t)
    (hl : IsLawful C t) : read (assemble C t hl) = t := by
  funext q
  cases q with
  | context base left right q =>
    exact congrFun (IndependentContextObjectPrimitive.read_assemble A (context t base left right)
      (ht base left right) (hl.support base left right)) q

/-- The primitive context tables recover all permitted native overlap selections. -/
noncomputable def readingEquiv (C : ContextPreorderCategory A) :
    ContextOverlapPullback C ≃ {t : Table A // IsTyped t ∧ IsLawful C t} where
  toFun P := ⟨read P, read_isTyped P, read_isLawful P⟩
  invFun t := assemble C t.val t.property.2
  left_inv := assemble_read
  right_inv t := Subtype.ext (read_assemble C t.val t.property.1 t.property.2)

end Overlap

end AAT.AG.LocalSemanticReconstruction.IndependentContextObjectPrimitive

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentContextObjectPrimitive
