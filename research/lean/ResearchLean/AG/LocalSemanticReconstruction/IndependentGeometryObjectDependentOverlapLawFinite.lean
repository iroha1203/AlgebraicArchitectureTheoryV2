import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryObjectDependentCoverageLawFinite
import ResearchLean.AG.LocalSemanticReconstruction.IndependentOverlapFiniteExpressions
import Formal.Util.AssertStandardAxioms

/-!
# Closed finite formulas for active-object overlap laws

Role-carrier typing is represented by exact object formulas.  Support,
positive and negative matching, and the four order clauses reuse the dedicated
closed finite overlap syntax and its exact lawfulness theorem.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectDependentFinite

noncomputable section

universe u v w

open Site IndependentFiniteLawFormula

variable {U : AtomCarrier.{u}}

namespace Overlap

abbrev overlapRows
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true) :=
  IndependentGeometryPrimitive.overlapTable (rows t ha A hA)

def overlapAnchor
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (q : IndependentOverlapCandidate.Query A)
    (body : ObjectFormula.{u, v, w} U) : ObjectFormula.{u, v, w} U :=
  .and (ObjectMatchingFinite.matchCell (.object A) true)
    (.and (.cell (.atObject A (.overlap q))
      (some ((rows t ha A hA) (.overlap q)))) body)

@[simp] theorem overlapAnchor_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (q : IndependentOverlapCandidate.Query A)
    (body : ObjectFormula.{u, v, w} U) :
    (overlapAnchor t ha A hA q body).evaluate t ↔ body.evaluate t := by
  simp only [overlapAnchor, ObjectFormula.evaluate,
    ObjectMatchingFinite.matchCell_evaluate, hA, true_and]
  exact and_iff_right
    (IndependentGeometryPrimitive.some_dependent t ha A hA (.overlap q)).symm

def supportTypedFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (base left right : ArchCtx A) (K : Type u) (s : K) (a : U.Atom) :
    ObjectFormula.{u, v, u + 1} U :=
  overlapAnchor t ha A hA (.context base left right (.carrier .support))
    (overlapAnchor t ha A hA (.context base left right (.support K s a))
      (.implies
        (.notEqual K (IndependentContextObjectPrimitive.carrier
          (IndependentContextObjectPrimitive.Overlap.context
            (IndependentOverlapCandidate.context (overlapRows t ha A hA))
            base left right) .support))
        (.equal
          (ULift.up ((overlapRows t ha A hA
            (.context base left right (.support K s a))).down) : ULift.{u + 1} Prop)
          (ULift.up False))))

def axisTypedFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (base left right : ArchCtx A) (K : Type u) (a : K) :
    ObjectFormula.{u, v, u + 1} U :=
  overlapAnchor t ha A hA (.context base left right (.carrier .axis))
    (overlapAnchor t ha A hA (.context base left right (.axis K a))
      (.implies
        (.notEqual K (IndependentContextObjectPrimitive.carrier
          (IndependentContextObjectPrimitive.Overlap.context
            (IndependentOverlapCandidate.context (overlapRows t ha A hA))
            base left right) .axis))
        (.equal
          (ULift.up ((overlapRows t ha A hA
            (.context base left right (.axis K a))).down) : ULift.{u + 1} Prop)
          (ULift.up False))))

def observableTypedFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (base left right : ArchCtx A) (K : Type u) (x : K) :
    ObjectFormula.{u, v, u + 1} U :=
  overlapAnchor t ha A hA (.context base left right (.carrier .observable))
    (overlapAnchor t ha A hA (.context base left right (.observable K x))
      (.implies
        (.notEqual K (IndependentContextObjectPrimitive.carrier
          (IndependentContextObjectPrimitive.Overlap.context
            (IndependentOverlapCandidate.context (overlapRows t ha A hA))
            base left right) .observable))
        (.equal
          (ULift.up ((overlapRows t ha A hA
            (.context base left right (.observable K x))).down) : ULift.{u + 1} Prop)
          (ULift.up False))))

structure TypedInstances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true) : Prop where
  support : ∀ base left right K s a,
    (supportTypedFormula t ha A hA base left right K s a).evaluate t
  axis : ∀ base left right K a,
    (axisTypedFormula t ha A hA base left right K a).evaluate t
  observable : ∀ base left right K x,
    (observableTypedFormula t ha A hA base left right K x).evaluate t

theorem typed_iff_instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true) :
    IndependentOverlapCandidate.IsTyped (overlapRows t ha A hA) ↔
      TypedInstances t ha A hA := by
  constructor
  · intro ht
    refine ⟨?_, ?_, ?_⟩
    · intro base left right K s a
      simp only [supportTypedFormula, overlapAnchor_evaluate, ObjectFormula.evaluate]
      intro hK
      apply ULift.ext
      exact propext (iff_false_intro ((ht base left right).support K s a hK))
    · intro base left right K a
      simp only [axisTypedFormula, overlapAnchor_evaluate, ObjectFormula.evaluate]
      intro hK
      apply ULift.ext
      exact propext (iff_false_intro ((ht base left right).axis K a hK))
    · intro base left right K x
      simp only [observableTypedFormula, overlapAnchor_evaluate, ObjectFormula.evaluate]
      intro hK
      apply ULift.ext
      exact propext (iff_false_intro ((ht base left right).observable K x hK))
  · intro hi base left right
    refine ⟨?_, ?_, ?_⟩
    · intro K s a hK hs
      have hp := hi.support base left right K s a
      simp only [supportTypedFormula, overlapAnchor_evaluate, ObjectFormula.evaluate] at hp
      have he := congrArg ULift.down (hp hK)
      change (overlapRows t ha A hA
        (.context base left right (.support K s a))).down at hs
      rw [he] at hs
      exact hs
    · intro K a hK hs
      have hp := hi.axis base left right K a
      simp only [axisTypedFormula, overlapAnchor_evaluate, ObjectFormula.evaluate] at hp
      have he := congrArg ULift.down (hp hK)
      change (overlapRows t ha A hA
        (.context base left right (.axis K a))).down at hs
      rw [he] at hs
      exact hs
    · intro K x hK hs
      have hp := hi.observable base left right K x
      simp only [observableTypedFormula, overlapAnchor_evaluate, ObjectFormula.evaluate] at hp
      have he := congrArg ULift.down (hp hK)
      change (overlapRows t ha A hA
        (.context base left right (.observable K x))).down at hs
      rw [he] at hs
      exact hs

abbrev LawInstances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true) : Prop :=
  (∀ b l r K (s : K) a,
    IndependentOverlapFinite.evaluate (rows t ha A hA)
      (.supportAdmission b l r K s a)) ∧
  (∀ b l r W q,
    IndependentOverlapFinite.evaluate (rows t ha A hA)
      (IndependentOverlapFinite.positiveMatchRule b l r W q)) ∧
  (∀ b l r W, IndependentOverlapCandidate.matching (overlapRows t ha A hA) b l r W = false →
    ∃ q, IndependentOverlapFinite.evaluate (rows t ha A hA)
      (IndependentOverlapFinite.negativeMatchWitness b l r W q)) ∧
  (∀ b l r W, IndependentOverlapFinite.evaluate (rows t ha A hA)
    (IndependentOverlapFinite.leftRule b l r W)) ∧
  (∀ b l r W, IndependentOverlapFinite.evaluate (rows t ha A hA)
    (IndependentOverlapFinite.rightRule b l r W)) ∧
  (∀ b l r W, IndependentOverlapFinite.evaluate (rows t ha A hA)
    (IndependentOverlapFinite.baseRule b l r W)) ∧
  ∀ b l r W X, IndependentOverlapFinite.evaluate (rows t ha A hA)
    (IndependentOverlapFinite.liftRule b l r W X)

theorem lawful_iff_instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA)) :
    IndependentOverlapCandidate.IsLawful (contextPreorder t ha A hA hc)
        (overlapRows t ha A hA) ↔ LawInstances t ha A hA := by
  exact IndependentOverlapFinite.lawful_iff_expressions (rows t ha A hA)
    hc.choose hc.choose_spec

structure Instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true) : Prop where
  typed : TypedInstances t ha A hA
  lawful : LawInstances t ha A hA

theorem overlapLaws_iff_instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA)) :
    IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc ↔
      Instances t ha A hA := by
  constructor
  · rintro ⟨ht, hl⟩
    exact ⟨(typed_iff_instances t ha A hA).1 ht,
      (lawful_iff_instances t ha A hA hc).1 hl⟩
  · rintro ⟨ht, hl⟩
    exact ⟨(typed_iff_instances t ha A hA).2 ht,
      (lawful_iff_instances t ha A hA hc).2 hl⟩

end Overlap

end


end AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectDependentFinite

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectDependentFinite
