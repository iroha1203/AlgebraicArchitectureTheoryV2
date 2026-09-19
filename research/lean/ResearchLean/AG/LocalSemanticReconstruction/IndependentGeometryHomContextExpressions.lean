import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomContextReadings
import Formal.Util.AssertStandardAxioms

/-!
# Finite common-query support for every context Hom law instance

The closed syntax reads only source/target refinement cells and Hom context
point cells. Its support is a triple of finite subsets of the already common
object/object/Hom declarations. Every expression is invariant under agreement
on that support, for arbitrary tables. The local monotonicity and both
unit/counit clauses are exactly quantified instances of this syntax.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ContextFinite

noncomputable section

universe u v

open Site

variable {U : AtomCarrier.{u}} {A B : ArchitectureObject U} {mode : Mode}

/-- Read the optional source/target context refinement point; an absent response cannot assert refinement. -/
def pointLe (t : IndependentGeometryPrimitive.Table.{u, v} U) (A : ArchitectureObject U)
    (W X : ArchCtx A) : Prop :=
  match t (.atObject A (.context (.le W X))) with
  | some x => x.down.down
  | none => False

/-- Active common rows give exactly the primitive context-order evaluation. -/
theorem pointLe_iff (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ht : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (ha : IndependentGeometryPrimitive.matching t (.object A) = true) (W X : ArchCtx A) :
    pointLe t A W X ↔ IndependentContextPrimitive.le
      (IndependentGeometryPrimitive.contextTable (IndependentGeometryPrimitive.dependent t ht A ha)) W X := by
  unfold pointLe
  rw [← IndependentGeometryPrimitive.some_dependent t ht A ha (.context (.le W X))]
  rfl

/-- Closed primitive context-Hom expressions; no arbitrary proposition or completed map is an argument. -/
inductive Expr (A B : ArchitectureObject U) where
  /-- Source refinement at one explicit context pair. -/
  | source (W X : ArchCtx A)
  /-- Target refinement at one explicit context pair. -/
  | target (V Y : ArchCtx B)
  /-- One direction-tagged context graph pair. -/
  | edge (direction : Direction) (W : ArchCtx A) (V : ArchCtx B)
  /-- Conjunction of finite expressions. -/
  | and (p q : Expr A B)
  /-- Implication between finite expressions. -/
  | implies (p q : Expr A B)

/-- Evaluate the fixed syntax through the three primitive common tables. -/
def evaluate (s t : IndependentGeometryPrimitive.Table.{u, v} U) (h : Table.{u, v} U mode) : Expr A B → Prop
  | .source W X => pointLe s A W X
  | .target V Y => pointLe t B V Y
  | .edge direction W V => h (.atObjects A B (.context direction W V)) = true
  | .and p q => evaluate s t h p ∧ evaluate s t h q
  | .implies p q => evaluate s t h p → evaluate s t h q

/-- Finite addresses in the two object tables and the Hom table. -/
abbrev Support (U : AtomCarrier.{u}) (mode : Mode) :=
  Finset (IndependentGeometryPrimitive.Query.{u, v} U) ×
    Finset (IndependentGeometryPrimitive.Query.{u, v} U) × Finset (Query.{u, v} U mode)

/-- Constructor-wise finite support on the common declarations, independent of table values. -/
def support : Expr A B → Support.{u, v} U mode
  | .source W X => ({.atObject A (.context (.le W X))}, ∅, ∅)
  | .target V Y => (∅, {.atObject B (.context (.le V Y))}, ∅)
  | .edge direction W V => (∅, ∅, {.atObjects A B (.context direction W V)})
  | .and p q => by
      classical
      exact ((support p).1 ∪ (support q).1,
        (support p).2.1 ∪ (support q).2.1,
        (support p).2.2 ∪ (support q).2.2)
  | .implies p q => by
      classical
      exact ((support p).1 ∪ (support q).1,
        (support p).2.1 ∪ (support q).2.1,
        (support p).2.2 ∪ (support q).2.2)

/-- Agreement on the finite support preserves evaluation even for arbitrary unvalidated tables. -/
theorem evaluate_iff_of_support (s t s' t' : IndependentGeometryPrimitive.Table.{u, v} U)
    (h h' : Table.{u, v} U mode) (e : Expr A B)
    (hs : ∀ q ∈ (support (mode := mode) e).1, s q = s' q)
    (ht : ∀ q ∈ (support (mode := mode) e).2.1, t q = t' q)
    (hh : ∀ q ∈ (support (mode := mode) e).2.2, h q = h' q) :
    evaluate s t h e ↔ evaluate s' t' h' e := by
  classical
  induction e with
  | source W X =>
      have he := hs (.atObject A (.context (.le W X))) (by simp [support])
      simp only [evaluate, pointLe, he]
  | target V Y =>
      have he := ht (.atObject B (.context (.le V Y))) (by simp [support])
      simp only [evaluate, pointLe, he]
  | edge direction W V =>
      have he := hh (.atObjects A B (.context direction W V)) (by simp [support])
      simp only [evaluate, he]
  | and p q hp hq =>
      exact and_congr
        (hp (fun r hr => hs r (by simp [support, hr])) (fun r hr => ht r (by simp [support, hr]))
          (fun r hr => hh r (by simp [support, hr])))
        (hq (fun r hr => hs r (by simp [support, hr])) (fun r hr => ht r (by simp [support, hr]))
          (fun r hr => hh r (by simp [support, hr])))
  | implies p q hp hq =>
      exact imp_congr
        (hp (fun r hr => hs r (by simp [support, hr])) (fun r hr => ht r (by simp [support, hr]))
          (fun r hr => hh r (by simp [support, hr])))
        (hq (fun r hr => hs r (by simp [support, hr])) (fun r hr => ht r (by simp [support, hr]))
          (fun r hr => hh r (by simp [support, hr])))

/-- Forward monotonicity as one finite implication. -/
def forwardRule (W X : ArchCtx A) (V Y : ArchCtx B) : Expr A B :=
  .implies (.and (.edge .forward W V) (.and (.edge .forward X Y) (.source W X))) (.target V Y)

/-- Backward monotonicity keeps its original arrow order. -/
def backwardRule (W X : ArchCtx A) (V Y : ArchCtx B) : Expr A B :=
  .implies (.and (.edge .backward W V) (.and (.edge .backward X Y) (.target V Y))) (.source W X)

/-- Both unit comparisons are retained without strengthening them to context equality. -/
def unitRule (W : ArchCtx A) (V : ArchCtx B) (X : ArchCtx A) : Expr A B :=
  .implies (.and (.edge .forward W V) (.edge .backward X V)) (.and (.source W X) (.source X W))

/-- Both counit comparisons are retained in the opposite composite order. -/
def counitRule (V : ArchCtx B) (W : ArchCtx A) (Y : ArchCtx B) : Expr A B :=
  .implies (.and (.edge .backward W V) (.edge .forward W Y)) (.and (.target Y V) (.target V Y))

/-- All context-Hom local laws are exact-one graph rows and instances of the closed finite syntax. -/
theorem lawful_iff_expressions (s t : IndependentGeometryPrimitive.Table.{u, v} U)
    (h : Table.{u, v} U mode) :
    Context.IsLawful (pointLe s A) (pointLe t B) (Context.points h A B) ↔
      (∀ W : ArchCtx A, ∃! V : ArchCtx B, evaluate s t h (.edge .forward W V)) ∧
      (∀ V : ArchCtx B, ∃! W : ArchCtx A, evaluate s t h (.edge .backward W V)) ∧
      (∀ (W X : ArchCtx A) (V Y : ArchCtx B), evaluate s t h (forwardRule W X V Y)) ∧
      (∀ (W X : ArchCtx A) (V Y : ArchCtx B), evaluate s t h (backwardRule W X V Y)) ∧
      (∀ (W : ArchCtx A) (V : ArchCtx B) (X : ArchCtx A), evaluate s t h (unitRule W V X)) ∧
      (∀ (V : ArchCtx B) (W : ArchCtx A) (Y : ArchCtx B), evaluate s t h (counitRule V W Y)) := by
  simp only [evaluate, forwardRule, backwardRule, unitRule, counitRule, and_imp]
  constructor
  · intro hl
    exact ⟨hl.forward, hl.backward, hl.forward_mono, hl.backward_mono, hl.unit, hl.counit⟩
  · rintro ⟨hf, hb, hm, hn, hu, hc⟩
    exact ⟨hf, hb, hm, hn, hu, hc⟩

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ContextFinite

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ContextFinite
