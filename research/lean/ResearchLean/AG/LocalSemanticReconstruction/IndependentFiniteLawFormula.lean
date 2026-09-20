import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitiveDeclaration
import Formal.Util.AssertStandardAxioms

/-!
# Closed finite formulas for independent geometry laws

This file supplies the support calculus used by the finite-law audit.  A
formula can inspect one source-object cell, one target-object cell, or one Hom
cell.  The only leaves without table support are explicit equalities or
inequalities between already supplied indices and values.  In particular,
there is no constructor accepting an arbitrary proposition or a completed
law certificate.

The preservation theorem compares all three primitive tables.  Endpoint
facts therefore cannot disappear into a Hom-only support calculation.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentFiniteLawFormula

noncomputable section

universe u v w x

open IndependentGeometryHomPrimitive

variable {U : AtomCarrier.{u}} {mode : Mode}

/-- A closed finite proposition over one Boolean table.  This small syntax is
used for total-function and inverse-row laws before those rows are embedded in
the complete common Hom declaration. -/
inductive BoolFormula (Q : Type v) where
  | cell (q : Q) (value : Bool)
  | equal {α : Type w} (left right : α)
  | notEqual {α : Type w} (left right : α)
  | truth
  | falsity
  | and (left right : BoolFormula Q)
  | or (left right : BoolFormula Q)
  | implies (premise conclusion : BoolFormula Q)
  | iff (left right : BoolFormula Q)

/-- Evaluate a closed Boolean-table formula. -/
def BoolFormula.evaluate {Q : Type v} (table : Q → Bool) : BoolFormula.{v, w} Q → Prop
  | .cell q value => table q = value
  | .equal left right => left = right
  | .notEqual left right => left ≠ right
  | .truth => True
  | .falsity => False
  | .and left right => left.evaluate table ∧ right.evaluate table
  | .or left right => left.evaluate table ∨ right.evaluate table
  | .implies premise conclusion => premise.evaluate table → conclusion.evaluate table
  | .iff left right => left.evaluate table ↔ right.evaluate table

/-- Exact Boolean cells read by the formula. -/
def BoolFormula.support {Q : Type v} : BoolFormula.{v, w} Q → Finset Q
  | .cell q _ => {q}
  | .equal _ _
  | .notEqual _ _
  | .truth
  | .falsity => ∅
  | .and left right
  | .or left right
  | .implies left right
  | .iff left right => by
      classical
      exact left.support ∪ right.support

/-- Agreement on the generated support preserves Boolean formula evaluation. -/
theorem BoolFormula.evaluate_iff_of_support {Q : Type v}
    (first second : Q → Bool) (formula : BoolFormula.{v, w} Q)
    (agree : ∀ q ∈ formula.support, first q = second q) :
    formula.evaluate first ↔ formula.evaluate second := by
  classical
  induction formula with
  | cell q value =>
      change first q = value ↔ second q = value
      rw [agree q (by simp [BoolFormula.support])]
  | equal left right => rfl
  | notEqual left right => rfl
  | truth => rfl
  | falsity => rfl
  | and left right ihLeft ihRight =>
      exact and_congr
        (ihLeft (fun q hq => agree q (by simp [BoolFormula.support, hq])))
        (ihRight (fun q hq => agree q (by simp [BoolFormula.support, hq])))
  | or left right ihLeft ihRight =>
      exact or_congr
        (ihLeft (fun q hq => agree q (by simp [BoolFormula.support, hq])))
        (ihRight (fun q hq => agree q (by simp [BoolFormula.support, hq])))
  | implies premise conclusion ihPremise ihConclusion =>
      exact imp_congr
        (ihPremise (fun q hq => agree q (by simp [BoolFormula.support, hq])))
        (ihConclusion (fun q hq => agree q (by simp [BoolFormula.support, hq])))
  | iff left right ihLeft ihRight =>
      exact iff_congr
        (ihLeft (fun q hq => agree q (by simp [BoolFormula.support, hq])))
        (ihRight (fun q hq => agree q (by simp [BoolFormula.support, hq])))

theorem BoolFormula.support_finite {Q : Type v} (formula : BoolFormula.{v, w} Q) :
    Finite formula.support := inferInstance

/-- A closed finite proposition over the single dependent object declaration. -/
inductive ObjectFormula (U : AtomCarrier.{u}) where
  | cell (q : IndependentGeometryPrimitive.Query.{u, v} U) (value : q.Value)
  | equal {α : Type w} (left right : α)
  | notEqual {α : Type w} (left right : α)
  | truth
  | falsity
  | and (left right : ObjectFormula U)
  | or (left right : ObjectFormula U)
  | implies (premise conclusion : ObjectFormula U)
  | iff (left right : ObjectFormula U)

/-- Finite conjunction of object formulas, with truth as its empty value. -/
def ObjectFormula.allList {α : Type x} (items : List α)
    (formula : α → ObjectFormula.{u, v, w} U) : ObjectFormula.{u, v, w} U :=
  match items with
  | [] => .truth
  | item :: rest => .and (formula item) (ObjectFormula.allList rest formula)

/-- Evaluate one closed object formula. -/
def ObjectFormula.evaluate (table : IndependentGeometryPrimitive.Table.{u, v} U) :
    ObjectFormula.{u, v, w} U → Prop
  | .cell q value => table q = value
  | .equal left right => left = right
  | .notEqual left right => left ≠ right
  | .truth => True
  | .falsity => False
  | .and left right => left.evaluate table ∧ right.evaluate table
  | .or left right => left.evaluate table ∨ right.evaluate table
  | .implies premise conclusion => premise.evaluate table → conclusion.evaluate table
  | .iff left right => left.evaluate table ↔ right.evaluate table

@[simp] theorem ObjectFormula.evaluate_allList {α : Type x}
    (table : IndependentGeometryPrimitive.Table.{u, v} U)
    (items : List α) (formula : α → ObjectFormula.{u, v, w} U) :
    (ObjectFormula.allList items formula).evaluate table ↔
      ∀ item ∈ items, (formula item).evaluate table := by
  induction items with
  | nil => simp [ObjectFormula.allList, ObjectFormula.evaluate]
  | cons item items ih => simp [ObjectFormula.allList, ObjectFormula.evaluate, ih]

/-- Exact primitive object cells read by one formula. -/
def ObjectFormula.support : ObjectFormula.{u, v, w} U →
    Finset (IndependentGeometryPrimitive.Query.{u, v} U)
  | .cell q _ => {q}
  | .equal _ _
  | .notEqual _ _
  | .truth
  | .falsity => ∅
  | .and left right
  | .or left right
  | .implies left right
  | .iff left right => by
      classical
      exact left.support ∪ right.support

/-- Primitive table agreement on the generated finite support preserves the
truth of one object-law instance. -/
theorem ObjectFormula.evaluate_iff_of_support
    (first second : IndependentGeometryPrimitive.Table.{u, v} U)
    (formula : ObjectFormula.{u, v, w} U)
    (agree : ∀ q ∈ formula.support, first q = second q) :
    formula.evaluate first ↔ formula.evaluate second := by
  classical
  induction formula with
  | cell q value =>
      change first q = value ↔ second q = value
      rw [agree q (by simp [ObjectFormula.support])]
  | equal left right => rfl
  | notEqual left right => rfl
  | truth => rfl
  | falsity => rfl
  | and left right ihLeft ihRight =>
      exact and_congr
        (ihLeft (fun q hq => agree q (by simp [ObjectFormula.support, hq])))
        (ihRight (fun q hq => agree q (by simp [ObjectFormula.support, hq])))
  | or left right ihLeft ihRight =>
      exact or_congr
        (ihLeft (fun q hq => agree q (by simp [ObjectFormula.support, hq])))
        (ihRight (fun q hq => agree q (by simp [ObjectFormula.support, hq])))
  | implies premise conclusion ihPremise ihConclusion =>
      exact imp_congr
        (ihPremise (fun q hq => agree q (by simp [ObjectFormula.support, hq])))
        (ihConclusion (fun q hq => agree q (by simp [ObjectFormula.support, hq])))
  | iff left right ihLeft ihRight =>
      exact iff_congr
        (ihLeft (fun q hq => agree q (by simp [ObjectFormula.support, hq])))
        (ihRight (fun q hq => agree q (by simp [ObjectFormula.support, hq])))

theorem ObjectFormula.support_finite (formula : ObjectFormula.{u, v, w} U) :
    Finite formula.support := inferInstance

/-- A closed finite proposition over the two primitive object tables and the
common Boolean Hom table.  Static leaves are restricted to equality and
inequality; arbitrary propositions are deliberately absent. -/
inductive Formula (U : AtomCarrier.{u}) (mode : Mode) where
  /-- One exact source-object response. -/
  | source (q : IndependentGeometryPrimitive.Query.{u, v} U) (value : q.Value)
  /-- One exact target-object response. -/
  | target (q : IndependentGeometryPrimitive.Query.{u, v} U) (value : q.Value)
  /-- One exact common-Hom response. -/
  | hom (q : IndependentGeometryHomPrimitive.Query.{u, v} U mode) (value : Bool)
  /-- Equality of two supplied indices or values. -/
  | equal {α : Type w} (left right : α)
  /-- Inequality of two supplied indices or values. -/
  | notEqual {α : Type w} (left right : α)
  /-- Truth, used as the neutral element of finite conjunctions. -/
  | truth
  /-- Falsity, used for closed refutation instances. -/
  | falsity
  /-- Finite conjunction. -/
  | and (left right : Formula U mode)
  /-- Finite disjunction. -/
  | or (left right : Formula U mode)
  /-- Finite implication. -/
  | implies (premise conclusion : Formula U mode)
  /-- Finite logical equivalence. -/
  | iff (left right : Formula U mode)

/-- Embed a closed formula over common Hom cells into the three-table syntax. -/
def Formula.ofHom :
    BoolFormula.{max (u + 1) (v + 1), w}
      (IndependentGeometryHomPrimitive.Query.{u, v} U mode) →
      Formula.{u, v, w} U mode
  | .cell q value => .hom q value
  | .equal left right => .equal left right
  | .notEqual left right => .notEqual left right
  | .truth => .truth
  | .falsity => .falsity
  | .and left right => .and (Formula.ofHom left) (Formula.ofHom right)
  | .or left right => .or (Formula.ofHom left) (Formula.ofHom right)
  | .implies premise conclusion =>
      .implies (Formula.ofHom premise) (Formula.ofHom conclusion)
  | .iff left right => .iff (Formula.ofHom left) (Formula.ofHom right)

/-- Finite conjunction, with truth as its empty value. -/
def Formula.allList {α : Type x} (items : List α)
    (formula : α → Formula.{u, v, w} U mode) : Formula.{u, v, w} U mode :=
  match items with
  | [] => .truth
  | item :: rest => .and (formula item) (Formula.allList rest formula)

/-- Finite disjunction, with falsity as its empty value. -/
def Formula.anyList {α : Type x} (items : List α)
    (formula : α → Formula.{u, v, w} U mode) : Formula.{u, v, w} U mode :=
  match items with
  | [] => .falsity
  | item :: rest => .or (formula item) (Formula.anyList rest formula)

/-- Evaluate a closed formula against the three primitive tables. -/
def Formula.evaluate
    (sourceTable targetTable : IndependentGeometryPrimitive.Table.{u, v} U)
    (homTable : IndependentGeometryHomPrimitive.Table.{u, v} U mode) :
    Formula.{u, v, w} U mode → Prop
  | .source q value => sourceTable q = value
  | .target q value => targetTable q = value
  | .hom q value => homTable q = value
  | .equal left right => left = right
  | .notEqual left right => left ≠ right
  | .truth => True
  | .falsity => False
  | .and left right => left.evaluate sourceTable targetTable homTable ∧
      right.evaluate sourceTable targetTable homTable
  | .or left right => left.evaluate sourceTable targetTable homTable ∨
      right.evaluate sourceTable targetTable homTable
  | .implies premise conclusion =>
      premise.evaluate sourceTable targetTable homTable →
        conclusion.evaluate sourceTable targetTable homTable
  | .iff left right => left.evaluate sourceTable targetTable homTable ↔
      right.evaluate sourceTable targetTable homTable

@[simp] theorem Formula.evaluate_ofHom
    (sourceTable targetTable : IndependentGeometryPrimitive.Table.{u, v} U)
    (homTable : IndependentGeometryHomPrimitive.Table.{u, v} U mode)
    (formula : BoolFormula.{max (u + 1) (v + 1), w}
      (IndependentGeometryHomPrimitive.Query.{u, v} U mode)) :
    (Formula.ofHom formula).evaluate sourceTable targetTable homTable ↔
      formula.evaluate homTable := by
  induction formula <;> simp_all [Formula.ofHom, Formula.evaluate, BoolFormula.evaluate]

@[simp] theorem Formula.evaluate_allList {α : Type x}
    (sourceTable targetTable : IndependentGeometryPrimitive.Table.{u, v} U)
    (homTable : IndependentGeometryHomPrimitive.Table.{u, v} U mode)
    (items : List α) (formula : α → Formula.{u, v, w} U mode) :
    (Formula.allList items formula).evaluate sourceTable targetTable homTable ↔
      ∀ item ∈ items, (formula item).evaluate sourceTable targetTable homTable := by
  induction items with
  | nil => simp [Formula.allList, Formula.evaluate]
  | cons item items ih => simp [Formula.allList, Formula.evaluate, ih]

@[simp] theorem Formula.evaluate_anyList {α : Type x}
    (sourceTable targetTable : IndependentGeometryPrimitive.Table.{u, v} U)
    (homTable : IndependentGeometryHomPrimitive.Table.{u, v} U mode)
    (items : List α) (formula : α → Formula.{u, v, w} U mode) :
    (Formula.anyList items formula).evaluate sourceTable targetTable homTable ↔
      ∃ item ∈ items, (formula item).evaluate sourceTable targetTable homTable := by
  induction items with
  | nil => simp [Formula.anyList, Formula.evaluate]
  | cons item items ih => simp [Formula.anyList, Formula.evaluate, ih]

/-- The three finite address sets read by a closed formula. -/
abbrev Support (U : AtomCarrier.{u}) (mode : Mode) :=
  Finset (IndependentGeometryPrimitive.Query.{u, v} U) ×
    Finset (IndependentGeometryPrimitive.Query.{u, v} U) ×
      Finset (IndependentGeometryHomPrimitive.Query.{u, v} U mode)

/-- Constructor-wise support contains every table cell used by evaluation. -/
def Formula.support : Formula.{u, v, w} U mode → Support.{u, v} U mode
  | .source q _ => ({q}, ∅, ∅)
  | .target q _ => (∅, {q}, ∅)
  | .hom q _ => (∅, ∅, {q})
  | .equal _ _
  | .notEqual _ _
  | .truth
  | .falsity => (∅, ∅, ∅)
  | .and left right
  | .or left right
  | .implies left right
  | .iff left right => by
      classical
      exact (left.support.1 ∪ right.support.1,
        left.support.2.1 ∪ right.support.2.1,
        left.support.2.2 ∪ right.support.2.2)

/-- Agreement on all three generated supports preserves formula evaluation
for arbitrary, possibly unlawful, comparison tables. -/
theorem Formula.evaluate_iff_of_support
    (sourceTable targetTable sourceTable' targetTable' :
      IndependentGeometryPrimitive.Table.{u, v} U)
    (homTable homTable' : IndependentGeometryHomPrimitive.Table.{u, v} U mode)
    (formula : Formula.{u, v, w} U mode)
    (sourceAgree : ∀ q ∈ formula.support.1, sourceTable q = sourceTable' q)
    (targetAgree : ∀ q ∈ formula.support.2.1, targetTable q = targetTable' q)
    (homAgree : ∀ q ∈ formula.support.2.2, homTable q = homTable' q) :
    formula.evaluate sourceTable targetTable homTable ↔
      formula.evaluate sourceTable' targetTable' homTable' := by
  classical
  induction formula with
  | source q value =>
      change sourceTable q = value ↔ sourceTable' q = value
      rw [sourceAgree q (by simp [Formula.support])]
  | target q value =>
      change targetTable q = value ↔ targetTable' q = value
      rw [targetAgree q (by simp [Formula.support])]
  | hom q value =>
      change homTable q = value ↔ homTable' q = value
      rw [homAgree q (by simp [Formula.support])]
  | equal left right => rfl
  | notEqual left right => rfl
  | truth => rfl
  | falsity => rfl
  | and left right ihLeft ihRight =>
      exact and_congr
        (ihLeft
          (fun q hq => sourceAgree q (by simp [Formula.support, hq]))
          (fun q hq => targetAgree q (by simp [Formula.support, hq]))
          (fun q hq => homAgree q (by simp [Formula.support, hq])))
        (ihRight
          (fun q hq => sourceAgree q (by simp [Formula.support, hq]))
          (fun q hq => targetAgree q (by simp [Formula.support, hq]))
          (fun q hq => homAgree q (by simp [Formula.support, hq])))
  | or left right ihLeft ihRight =>
      exact or_congr
        (ihLeft
          (fun q hq => sourceAgree q (by simp [Formula.support, hq]))
          (fun q hq => targetAgree q (by simp [Formula.support, hq]))
          (fun q hq => homAgree q (by simp [Formula.support, hq])))
        (ihRight
          (fun q hq => sourceAgree q (by simp [Formula.support, hq]))
          (fun q hq => targetAgree q (by simp [Formula.support, hq]))
          (fun q hq => homAgree q (by simp [Formula.support, hq])))
  | implies premise conclusion ihPremise ihConclusion =>
      exact imp_congr
        (ihPremise
          (fun q hq => sourceAgree q (by simp [Formula.support, hq]))
          (fun q hq => targetAgree q (by simp [Formula.support, hq]))
          (fun q hq => homAgree q (by simp [Formula.support, hq])))
        (ihConclusion
          (fun q hq => sourceAgree q (by simp [Formula.support, hq]))
          (fun q hq => targetAgree q (by simp [Formula.support, hq]))
          (fun q hq => homAgree q (by simp [Formula.support, hq])))
  | iff left right ihLeft ihRight =>
      exact iff_congr
        (ihLeft
          (fun q hq => sourceAgree q (by simp [Formula.support, hq]))
          (fun q hq => targetAgree q (by simp [Formula.support, hq]))
          (fun q hq => homAgree q (by simp [Formula.support, hq])))
        (ihRight
          (fun q hq => sourceAgree q (by simp [Formula.support, hq]))
          (fun q hq => targetAgree q (by simp [Formula.support, hq]))
          (fun q hq => homAgree q (by simp [Formula.support, hq])))

/-- Every generated support is finite without a finite carrier or finite query
universe assumption. -/
theorem Formula.support_finite (formula : Formula.{u, v, w} U mode) :
    Finite formula.support.1 ∧ Finite formula.support.2.1 ∧ Finite formula.support.2.2 :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end

end AAT.AG.LocalSemanticReconstruction.IndependentFiniteLawFormula

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentFiniteLawFormula
