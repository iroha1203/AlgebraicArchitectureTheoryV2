import ResearchLean.AG.LocalSemanticReconstruction.IndependentContextObjectPrimitiveReadings
import Formal.Util.AssertStandardAxioms

/-!
# Candidate result references for primitive overlap comparisons

A selected overlap is still given by primitive context-field cells. Additional
Boolean cells compare candidate context references with those primitive cells:
a positive comparison requires pointwise agreement, and a negative comparison
requires an actual differing point. These derived cells have no free choices.
The order requirements then refer to candidate contexts directly, so a single
order instance never constructs a context from an infinite predicate family.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentOverlapCandidate

noncomputable section

universe u

open Site

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}

namespace ContextMatch

/-- Candidate context references are compared by individual primitive field responses. -/
structure IsLawful (t : IndependentContextObjectPrimitive.Table U) (m : ArchCtx A → Bool) : Prop where
  /-- A matching reference agrees at every primitive point separately. -/
  yes : ∀ W, m W = true → ∀ q, t q = IndependentContextObjectPrimitive.read W q
  /-- A rejected reference must differ at a specific primitive point. -/
  no : ∀ W, m W = false → ∃ q, t q ≠ IndependentContextObjectPrimitive.read W q

/-- Local point matching derives exact equality to the assembled native context. -/
theorem matches_iff (t : IndependentContextObjectPrimitive.Table U)
    (ht : IndependentContextObjectPrimitive.IsTyped t) (hl : IndependentContextObjectPrimitive.IsLawful A t)
    (m : ArchCtx A → Bool) (hm : IsLawful t m) (W : ArchCtx A) :
    m W = true ↔ W = IndependentContextObjectPrimitive.assemble A t hl := by
  constructor
  · intro h
    apply IndependentContextObjectPrimitive.read_injective
    rw [IndependentContextObjectPrimitive.read_assemble A t ht hl]
    exact (funext (hm.yes W h)).symm
  · rintro rfl
    cases h : m (IndependentContextObjectPrimitive.assemble A t hl) with
    | true => rfl
    | false =>
      obtain ⟨q, hq⟩ := hm.no _ h
      exact False.elim (hq (congrFun (IndependentContextObjectPrimitive.read_assemble A t ht hl) q).symm)

/-- The native reader returns the derived match flag for each raw candidate reference. -/
def read (W : ArchCtx A) : ArchCtx A → Bool := by
  classical
  exact fun V => decide (V = W)

/-- Each native context supplies both positive point equations and negative point witnesses. -/
theorem read_isLawful (W : ArchCtx A) : IsLawful (IndependentContextObjectPrimitive.read W) (read W) := by
  classical
  constructor
  · intro V h q
    have hv : V = W := of_decide_eq_true h
    subst V
    rfl
  · intro V h
    have hv : V ≠ W := of_decide_eq_false h
    by_contra hn
    push_neg at hn
    exact hv (IndependentContextObjectPrimitive.read_injective (funext hn).symm)

/-- Derived match cells are unique for fixed primitive context rows. -/
theorem eq_read (t : IndependentContextObjectPrimitive.Table U)
    (ht : IndependentContextObjectPrimitive.IsTyped t) (hl : IndependentContextObjectPrimitive.IsLawful A t)
    (m : ArchCtx A → Bool) (hm : IsLawful t m) :
    m = read (IndependentContextObjectPrimitive.assemble A t hl) := by
  classical
  funext W
  apply Bool.eq_iff_iff.mpr
  simpa [read] using matches_iff t ht hl m hm W

end ContextMatch

/-- Context-field points and candidate-result flags are declared before the context preorder exists. -/
inductive Query (A : ArchitectureObject U) where
  /-- One primitive field of the context selected at a triple. -/
  | context (base left right : ArchCtx A) (q : IndependentContextObjectPrimitive.Query U)
  /-- One candidate-result matching flag at that triple. -/
  | matching (base left right result : ArchCtx A)

/-- Each cell contains one primitive context response or one Boolean. -/
def Query.Value : Query A → Type (u + 1)
  | .context _ _ _ q => q.Value
  | .matching _ _ _ _ => ULift.{u + 1} Bool

/-- Primitive dependent overlap table on candidate contexts. -/
abbrev Table (A : ArchitectureObject U) := (q : Query A) → q.Value

/-- Primitive context rows, with no completed overlap value in a cell. -/
def context (t : Table A) : IndependentContextObjectPrimitive.Overlap.Table A
  | .context base left right q => t (.context base left right q)

/-- Candidate-result match cells for a fixed triple. -/
def matching (t : Table A) (base left right : ArchCtx A) : ArchCtx A → Bool :=
  fun result => (t (.matching base left right result)).down

/-- Primitive context carriers have exactly their original role activation. -/
abbrev IsTyped (t : Table A) := IndependentContextObjectPrimitive.Overlap.IsTyped (context t)

/-- Independent point conditions for overlap, including its result-reference matching metadata. -/
structure IsLawful (C : ContextPreorderCategory A) (t : Table A) : Prop where
  /-- Every selected context reads only Atoms admitted by the architecture object. -/
  support : ∀ base left right, IndependentContextObjectPrimitive.IsLawful A
    (IndependentContextObjectPrimitive.Overlap.context (context t) base left right)
  /-- Candidate result flags agree with all primitive point fields, with a point witness on rejection. -/
  matching : ∀ base left right, ContextMatch.IsLawful
    (IndependentContextObjectPrimitive.Overlap.context (context t) base left right)
    (IndependentOverlapCandidate.matching t base left right)
  /-- One matching candidate result lies below the left input. -/
  left : ∀ base left right result, IndependentOverlapCandidate.matching t base left right result = true →
    C.le left base → C.le right base → C.le result left
  /-- One matching candidate result lies below the right input. -/
  right : ∀ base left right result, IndependentOverlapCandidate.matching t base left right result = true →
    C.le left base → C.le right base → C.le result right
  /-- One matching candidate result lies below the base. -/
  base : ∀ base left right result, IndependentOverlapCandidate.matching t base left right result = true →
    C.le left base → C.le right base → C.le result base
  /-- Any common refinement lies below the matching candidate result. -/
  lift : ∀ base left right result X, IndependentOverlapCandidate.matching t base left right result = true →
    C.le left base → C.le right base → C.le X left → C.le X right → C.le X result

variable (C : ContextPreorderCategory A)

/-- The primitively assembled context is forced to have a positive match flag. -/
theorem generated_match (t : Table A) (ht : IsTyped t) (hl : IsLawful C t) (base left right : ArchCtx A) :
    matching t base left right (IndependentContextObjectPrimitive.assemble A
      (IndependentContextObjectPrimitive.Overlap.context (context t) base left right)
      (hl.support base left right)) = true :=
  (ContextMatch.matches_iff _ (ht base left right) (hl.support base left right)
    _ (hl.matching base left right) _).2 rfl

/-- Derive the four original overlap requirements from candidate-result point instances. -/
def originalLaws (t : Table A) (ht : IsTyped t) (hl : IsLawful C t) :
    IndependentContextObjectPrimitive.Overlap.IsLawful C (context t) where
  support := hl.support
  left base left right hL hR := hl.left base left right _ (generated_match C t ht hl base left right) hL hR
  right base left right hL hR := hl.right base left right _ (generated_match C t ht hl base left right) hL hR
  base base left right hL hR := hl.base base left right _ (generated_match C t ht hl base left right) hL hR
  lift base left right X hL hR hXl hXr :=
    hl.lift base left right _ X (generated_match C t ht hl base left right) hL hR hXl hXr

/-- Construct the native overlap package from context points and the derived order laws. -/
def assemble (t : Table A) (ht : IsTyped t) (hl : IsLawful C t) : ContextOverlapPullback C :=
  IndependentContextObjectPrimitive.Overlap.assemble C (context t) (originalLaws C t ht hl)

/-- Read each native overlap value through primitive context points and derived match flags. -/
def read (P : ContextOverlapPullback C) : Table A
  | .context base left right q => IndependentContextObjectPrimitive.read (P.overlap base left right) q
  | .matching base left right result => ⟨ContextMatch.read (P.overlap base left right) result⟩

/-- Native overlap readings obey the same candidate context carrier activation. -/
theorem read_isTyped (P : ContextOverlapPullback C) : IsTyped (read C P) :=
  IndependentContextObjectPrimitive.Overlap.read_isTyped P

/-- Native overlap laws supply each primitive support, matching, and order condition. -/
theorem read_isLawful (P : ContextOverlapPullback C) : IsLawful C (read C P) where
  support base left right := IndependentContextObjectPrimitive.read_isLawful (P.overlap base left right)
  matching base left right := ContextMatch.read_isLawful (P.overlap base left right)
  left base left right result hm hL hR := by
    classical
    have hr : result = P.overlap base left right := of_decide_eq_true hm
    subst result
    exact P.overlap_le_left hL hR
  right base left right result hm hL hR := by
    classical
    have hr : result = P.overlap base left right := of_decide_eq_true hm
    subst result
    exact P.overlap_le_right hL hR
  base base left right result hm hL hR := by
    classical
    have hr : result = P.overlap base left right := of_decide_eq_true hm
    subst result
    exact P.overlap_le_base hL hR
  lift base left right result X hm hL hR hXl hXr := by
    classical
    have hr : result = P.overlap base left right := of_decide_eq_true hm
    subst result
    exact P.overlap_lift hL hR hXl hXr

/-- Primitive reconstruction restores every original overlap context and all four order laws. -/
theorem assemble_read (P : ContextOverlapPullback C) :
    assemble C (read C P) (read_isTyped C P) (read_isLawful C P) = P :=
  IndependentContextObjectPrimitive.Overlap.assemble_read P

/-- Re-reading restores the primitive context cells and all uniquely determined candidate-match flags. -/
theorem read_assemble (t : Table A) (ht : IsTyped t) (hl : IsLawful C t) :
    read C (assemble C t ht hl) = t := by
  funext q
  cases q with
  | context base left right q =>
    exact congrFun (IndependentContextObjectPrimitive.read_assemble A _ (ht base left right)
      (hl.support base left right)) q
  | matching base left right result =>
    exact congrArg ULift.up (congrFun (ContextMatch.eq_read _ (ht base left right)
      (hl.support base left right) _ (hl.matching base left right)) result).symm

/-- Native overlaps and the candidate-reference primitive tables have exact inverse readings. -/
def readingEquiv : ContextOverlapPullback C ≃ {t : Table A // IsTyped t ∧ IsLawful C t} where
  toFun P := ⟨read C P, read_isTyped C P, read_isLawful C P⟩
  invFun t := assemble C t.val t.property.1 t.property.2
  left_inv := assemble_read C
  right_inv t := Subtype.ext (read_assemble C t.val t.property.1 t.property.2)

end

end AAT.AG.LocalSemanticReconstruction.IndependentOverlapCandidate

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentOverlapCandidate
