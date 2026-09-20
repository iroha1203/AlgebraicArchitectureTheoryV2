import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryObjectDependentContextLawFinite
import Formal.Util.AssertStandardAxioms

/-!
# Closed finite formulas for active-object equation laws

Every type reference, operation value, restriction value, and coordinate used
by a formula is anchored to its primitive active-object row.  The formulas
therefore contain no completed ring, homomorphism, or law certificate.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectDependentFinite

noncomputable section

universe u v w

open Site CategoryTheory IndependentFiniteLawFormula

variable {U : AtomCarrier.{u}}

abbrev contextPreorder
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA)) :=
  IndependentCoreTableAssembly.context
    (IndependentGeometryPrimitive.contextData (rows t ha A hA) hc)

abbrev equationRows
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true) :=
  IndependentGeometryPrimitive.equationTable (rows t ha A hA)

def equationCell (A : ArchitectureObject U) (q : IndependentEquationPrimitive.Query A)
    (value : q.Value) : ObjectFormula.{u, v, w} U :=
  .cell (.atObject A (.equation q)) (some (ULift.up value))

@[simp] theorem equationCellEq_iff
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (q : IndependentEquationPrimitive.Query A) (value : q.Value) :
    t (.atObject A (.equation q)) = some (ULift.up value) ↔
      equationRows t ha A hA q = value := by
  rw [← IndependentGeometryPrimitive.some_dependent t ha A hA (.equation q)]
  constructor
  · intro h
    exact congrArg ULift.down (Option.some.inj h)
  · intro h
    apply congrArg some
    apply ULift.ext
    exact h

theorem equationCell_evaluate_iff
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (q : IndependentEquationPrimitive.Query A) (value : q.Value) :
    (equationCell A q value : ObjectFormula.{u, v, w} U).evaluate t ↔
      equationRows t ha A hA q = value :=
  equationCellEq_iff t ha A hA q value

def equationAnchor
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (q : IndependentEquationPrimitive.Query A)
    (body : ObjectFormula.{u, v, w} U) : ObjectFormula.{u, v,w} U :=
  .and (ObjectMatchingFinite.matchCell (.object A) true)
    (.and (.cell (.atObject A (.equation q))
      (some ((rows t ha A hA) (.equation q)))) body)

@[simp] theorem equationAnchor_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (q : IndependentEquationPrimitive.Query A)
    (body : ObjectFormula.{u, v, w} U) :
    (equationAnchor t ha A hA q body).evaluate t ↔ body.evaluate t := by
  simp only [equationAnchor, ObjectFormula.evaluate,
    ObjectMatchingFinite.matchCell_evaluate, hA, true_and]
  exact and_iff_right
    (IndependentGeometryPrimitive.some_dependent t ha A hA (.equation q)).symm

namespace Equation

/-! ## Exact activation formulas -/

def observableTypedFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (W : ArchCtx A) (K : Type u) (q : IndependentRingPrimitive.Query K)
    (value : Option K) :
    ObjectFormula.{u, v, 0} U :=
  equationAnchor t ha A hA (.observable W .carrier)
    (equationCell A (.observable W (.operation K q)) (ULift.up value))

def roleTypedFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (I : Type u) (i : I) (value : Option EquationRole) : ObjectFormula.{u, v, 0} U :=
  equationAnchor t ha A hA .index
    (equationCell A (.role I i) (ULift.up value))

def restrictionTypedFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (W V : ArchCtx A) (K L : Type u) (x : L) (value : Option K) :
    ObjectFormula.{u, v, 0} U :=
  contextAnchor t ha A hA (.le W V)
    (equationAnchor t ha A hA (.observable W .carrier)
      (equationAnchor t ha A hA (.observable V .carrier)
        (equationCell A (.restriction W V K L x) (ULift.up value))))

def violationTypedFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (W : ArchCtx A) (I K : Type u) (i : I) (a : U.Atom) (value : Option K) :
    ObjectFormula.{u, v, 0} U :=
  equationAnchor t ha A hA .index
    (equationAnchor t ha A hA (.observable W .carrier)
      (equationCell A (.violation W I K i a) (ULift.up value)))

def residualTypedFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (W : ArchCtx A) (B : ArchitectureObject U) (I K : Type u) (i : I) (a : U.Atom)
    (value : Option K) :
    ObjectFormula.{u, v, 0} U :=
  equationAnchor t ha A hA .index
    (equationAnchor t ha A hA (.observable W .carrier)
      (equationCell A (.residual W B I K i a) (ULift.up value)))

structure TypedInstances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true) : Prop where
  observableSome : ∀ W K q, K = IndependentEquationPrimitive.observableType
      (equationRows t ha A hA) W →
    ∃ y, (observableTypedFormula t ha A hA W K q (some y)).evaluate t
  observableNone : ∀ W K q, K ≠ IndependentEquationPrimitive.observableType
      (equationRows t ha A hA) W →
    (observableTypedFormula t ha A hA W K q none).evaluate t
  roleSome : ∀ I i, I = IndependentEquationPrimitive.index (equationRows t ha A hA) →
    ∃ y, (roleTypedFormula t ha A hA I i (some y)).evaluate t
  roleNone : ∀ I i, I ≠ IndependentEquationPrimitive.index (equationRows t ha A hA) →
    (roleTypedFormula t ha A hA I i none).evaluate t
  restrictionSome : ∀ W V K L x,
    IndependentContextPrimitive.le
        (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) W V ∧
      K = IndependentEquationPrimitive.observableType (equationRows t ha A hA) W ∧
      L = IndependentEquationPrimitive.observableType (equationRows t ha A hA) V →
    ∃ y, (restrictionTypedFormula t ha A hA W V K L x (some y)).evaluate t
  restrictionNone : ∀ W V K L x,
    ¬ (IndependentContextPrimitive.le
        (IndependentGeometryPrimitive.contextTable (rows t ha A hA)) W V ∧
      K = IndependentEquationPrimitive.observableType (equationRows t ha A hA) W ∧
      L = IndependentEquationPrimitive.observableType (equationRows t ha A hA) V) →
    (restrictionTypedFormula t ha A hA W V K L x none).evaluate t
  violationSome : ∀ W I K i a,
    I = IndependentEquationPrimitive.index (equationRows t ha A hA) ∧
      K = IndependentEquationPrimitive.observableType (equationRows t ha A hA) W →
    ∃ y, (violationTypedFormula t ha A hA W I K i a (some y)).evaluate t
  violationNone : ∀ W I K i a,
    ¬ (I = IndependentEquationPrimitive.index (equationRows t ha A hA) ∧
      K = IndependentEquationPrimitive.observableType (equationRows t ha A hA) W) →
    (violationTypedFormula t ha A hA W I K i a none).evaluate t
  residualSome : ∀ W B I K i a,
    I = IndependentEquationPrimitive.index (equationRows t ha A hA) ∧
      K = IndependentEquationPrimitive.observableType (equationRows t ha A hA) W →
    ∃ y, (residualTypedFormula t ha A hA W B I K i a (some y)).evaluate t
  residualNone : ∀ W B I K i a,
    ¬ (I = IndependentEquationPrimitive.index (equationRows t ha A hA) ∧
      K = IndependentEquationPrimitive.observableType (equationRows t ha A hA) W) →
    (residualTypedFormula t ha A hA W B I K i a none).evaluate t

theorem typed_iff_instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA)) :
    IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
        (equationRows t ha A hA) ↔ TypedInstances t ha A hA := by
  constructor
  · intro ht
    refine {
      observableSome := ?_
      observableNone := ?_
      roleSome := ?_
      roleNone := ?_
      restrictionSome := ?_
      restrictionNone := ?_
      violationSome := ?_
      violationNone := ?_
      residualSome := ?_
      residualNone := ?_ }
    · intro W K q hK
      have hs := (ht.observable W K q).2 hK
      cases hv : (equationRows t ha A hA (.observable W (.operation K q))).down with
      | none => simp [hv] at hs
      | some y =>
          refine ⟨y, ?_⟩
          simp only [observableTypedFormula, equationAnchor_evaluate]
          apply (equationCell_evaluate_iff t ha A hA _ _).2
          apply ULift.ext
          exact hv
    · intro W K q hK
      have hn := IndependentInvariantSignaturePrimitive.option_none _
        (mt (ht.observable W K q).1 hK)
      simp only [observableTypedFormula, equationAnchor_evaluate]
      apply (equationCell_evaluate_iff t ha A hA _ _).2
      apply ULift.ext
      exact hn
    · intro I i hI
      have hs := (ht.role I i).2 hI
      cases hv : (equationRows t ha A hA (.role I i)).down with
      | none => simp [hv] at hs
      | some y =>
          refine ⟨y, ?_⟩
          simp only [roleTypedFormula, equationAnchor_evaluate]
          apply (equationCell_evaluate_iff t ha A hA _ _).2
          apply ULift.ext
          exact hv
    · intro I i hI
      have hn := IndependentInvariantSignaturePrimitive.option_none _ (mt (ht.role I i).1 hI)
      simp only [roleTypedFormula, equationAnchor_evaluate]
      apply (equationCell_evaluate_iff t ha A hA _ _).2
      apply ULift.ext
      exact hn
    · intro W V K L x htyped
      have hs := (ht.restriction W V K L x).2 htyped
      cases hv : (equationRows t ha A hA (.restriction W V K L x)).down with
      | none => simp [hv] at hs
      | some y =>
          refine ⟨y, ?_⟩
          simp only [restrictionTypedFormula, contextAnchor_evaluate, equationAnchor_evaluate]
          apply (equationCell_evaluate_iff t ha A hA _ _).2
          apply ULift.ext
          exact hv
    · intro W V K L x htyped
      have hn := IndependentInvariantSignaturePrimitive.option_none _
        (mt (ht.restriction W V K L x).1 htyped)
      simp only [restrictionTypedFormula, contextAnchor_evaluate, equationAnchor_evaluate]
      apply (equationCell_evaluate_iff t ha A hA _ _).2
      apply ULift.ext
      exact hn
    · intro W I K i a htyped
      have hs := (ht.violation W I K i a).2 htyped
      cases hv : (equationRows t ha A hA (.violation W I K i a)).down with
      | none => simp [hv] at hs
      | some y =>
          refine ⟨y, ?_⟩
          simp only [violationTypedFormula, equationAnchor_evaluate]
          apply (equationCell_evaluate_iff t ha A hA _ _).2
          apply ULift.ext
          exact hv
    · intro W I K i a htyped
      have hn := IndependentInvariantSignaturePrimitive.option_none _
        (mt (ht.violation W I K i a).1 htyped)
      simp only [violationTypedFormula, equationAnchor_evaluate]
      apply (equationCell_evaluate_iff t ha A hA _ _).2
      apply ULift.ext
      exact hn
    · intro W B I K i a htyped
      have hs := (ht.residual W B I K i a).2 htyped
      cases hv : (equationRows t ha A hA (.residual W B I K i a)).down with
      | none => simp [hv] at hs
      | some y =>
          refine ⟨y, ?_⟩
          simp only [residualTypedFormula, equationAnchor_evaluate]
          apply (equationCell_evaluate_iff t ha A hA _ _).2
          apply ULift.ext
          exact hv
    · intro W B I K i a htyped
      have hn := IndependentInvariantSignaturePrimitive.option_none _
        (mt (ht.residual W B I K i a).1 htyped)
      simp only [residualTypedFormula, equationAnchor_evaluate]
      apply (equationCell_evaluate_iff t ha A hA _ _).2
      apply ULift.ext
      exact hn
  · intro hi
    refine {
      observable := ?_
      role := ?_
      restriction := ?_
      violation := ?_
      residual := ?_ }
    · intro W K q
      constructor
      · intro hs
        by_contra hK
        have hn := hi.observableNone W K q hK
        simp only [observableTypedFormula, equationAnchor_evaluate] at hn
        have he := congrArg ULift.down
          ((equationCell_evaluate_iff t ha A hA _ _).1 hn)
        rw [he] at hs
        exact Bool.noConfusion hs
      · intro hK
        obtain ⟨y, hy⟩ := hi.observableSome W K q hK
        simp only [observableTypedFormula, equationAnchor_evaluate] at hy
        have he := congrArg ULift.down
          ((equationCell_evaluate_iff t ha A hA _ _).1 hy)
        rw [he]
        rfl
    · intro I i
      constructor
      · intro hs
        by_contra hI
        have hn := hi.roleNone I i hI
        simp only [roleTypedFormula, equationAnchor_evaluate] at hn
        have he := congrArg ULift.down
          ((equationCell_evaluate_iff t ha A hA _ _).1 hn)
        rw [he] at hs
        exact Bool.noConfusion hs
      · intro hI
        obtain ⟨y, hy⟩ := hi.roleSome I i hI
        simp only [roleTypedFormula, equationAnchor_evaluate] at hy
        have he := congrArg ULift.down
          ((equationCell_evaluate_iff t ha A hA _ _).1 hy)
        rw [he]
        rfl
    · intro W V K L x
      constructor
      · intro hs
        by_contra htyped
        have hn := hi.restrictionNone W V K L x htyped
        simp only [restrictionTypedFormula, contextAnchor_evaluate, equationAnchor_evaluate] at hn
        have he := congrArg ULift.down
          ((equationCell_evaluate_iff t ha A hA _ _).1 hn)
        rw [he] at hs
        exact Bool.noConfusion hs
      · intro htyped
        obtain ⟨y, hy⟩ := hi.restrictionSome W V K L x htyped
        simp only [restrictionTypedFormula, contextAnchor_evaluate, equationAnchor_evaluate] at hy
        have he := congrArg ULift.down
          ((equationCell_evaluate_iff t ha A hA _ _).1 hy)
        rw [he]
        rfl
    · intro W I K i a
      constructor
      · intro hs
        by_contra htyped
        have hn := hi.violationNone W I K i a htyped
        simp only [violationTypedFormula, equationAnchor_evaluate] at hn
        have he := congrArg ULift.down
          ((equationCell_evaluate_iff t ha A hA _ _).1 hn)
        rw [he] at hs
        exact Bool.noConfusion hs
      · intro htyped
        obtain ⟨y, hy⟩ := hi.violationSome W I K i a htyped
        simp only [violationTypedFormula, equationAnchor_evaluate] at hy
        have he := congrArg ULift.down
          ((equationCell_evaluate_iff t ha A hA _ _).1 hy)
        rw [he]
        rfl
    · intro W B I K i a
      constructor
      · intro hs
        by_contra htyped
        have hn := hi.residualNone W B I K i a htyped
        simp only [residualTypedFormula, equationAnchor_evaluate] at hn
        have he := congrArg ULift.down
          ((equationCell_evaluate_iff t ha A hA _ _).1 hn)
        rw [he] at hs
        exact Bool.noConfusion hs
      · intro htyped
        obtain ⟨y, hy⟩ := hi.residualSome W B I K i a htyped
        simp only [residualTypedFormula, equationAnchor_evaluate] at hy
        have he := congrArg ULift.down
          ((equationCell_evaluate_iff t ha A hA _ _).1 hy)
        rw [he]
        rfl

/-! ## Observable-ring equations -/

abbrev observableActive
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W : ArchCtx A) :=
  IndependentRingPrimitive.Carrier.active
    (IndependentEquationPrimitive.observable (equationRows t ha A hA) W)
    (ht.observable W)

def observableActiveAnchor
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (_ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W : ArchCtx A)
    (q : IndependentRingPrimitive.Query
      (IndependentEquationPrimitive.observableType (equationRows t ha A hA) W))
    (body : ObjectFormula.{u, v, w} U) : ObjectFormula.{u, v, w} U :=
  equationAnchor t ha A hA (.observable W .carrier)
    (equationAnchor t ha A hA (.observable W (.operation _ q)) body)

@[simp] theorem observableActiveAnchor_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W : ArchCtx A)
    (q : IndependentRingPrimitive.Query
      (IndependentEquationPrimitive.observableType (equationRows t ha A hA) W))
    (body : ObjectFormula.{u, v, w} U) :
    (observableActiveAnchor t ha A hA hc ht W q body).evaluate t ↔ body.evaluate t := by
  simp [observableActiveAnchor]

def observableActiveAnchors
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W : ArchCtx A) :
    List (IndependentRingPrimitive.Query
      (IndependentEquationPrimitive.observableType (equationRows t ha A hA) W)) →
      ObjectFormula.{u, v, w} U → ObjectFormula.{u, v, w} U
  | [], body => body
  | q :: qs, body => observableActiveAnchor t ha A hA hc ht W q
      (observableActiveAnchors t ha A hA hc ht W qs body)

@[simp] theorem observableActiveAnchors_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W : ArchCtx A)
    (qs : List (IndependentRingPrimitive.Query
      (IndependentEquationPrimitive.observableType (equationRows t ha A hA) W)))
    (body : ObjectFormula.{u, v, w} U) :
    (observableActiveAnchors t ha A hA hc ht W qs body).evaluate t ↔
      body.evaluate t := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [observableActiveAnchors, ih]

def observableActiveValue
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (_ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W : ArchCtx A)
    (q : IndependentRingPrimitive.Query
      (IndependentEquationPrimitive.observableType (equationRows t ha A hA) W))
    (value : IndependentEquationPrimitive.observableType (equationRows t ha A hA) W) :
    ObjectFormula.{u, v, u} U :=
  equationAnchor t ha A hA (.observable W .carrier)
    (equationCell A (.observable W (.operation _ q)) (ULift.up (some value)))

@[simp] theorem observableActiveValue_evaluate_iff
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W : ArchCtx A)
    (q : IndependentRingPrimitive.Query
      (IndependentEquationPrimitive.observableType (equationRows t ha A hA) W))
    (value : IndependentEquationPrimitive.observableType (equationRows t ha A hA) W) :
    (observableActiveValue t ha A hA hc ht W q value).evaluate t ↔
      observableActive t ha A hA hc ht W q = value := by
  simp only [observableActiveValue, equationAnchor_evaluate]
  rw [equationCell_evaluate_iff t ha A hA]
  constructor
  · intro h
    have he := congrArg ULift.down h
    exact Option.some.inj ((Option.some_get _).trans he)
  · intro h
    apply ULift.ext
    exact (Option.some_get _).symm.trans (congrArg some h)

def ringAddAssoc
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W : ArchCtx A)
    (a b c : IndependentEquationPrimitive.observableType (equationRows t ha A hA) W) :
    ObjectFormula.{u, v, u} U :=
  observableActiveAnchors t ha A hA hc ht W
    [.add a b, .add (observableActive t ha A hA hc ht W (.add a b)) c,
      .add b c, .add a (observableActive t ha A hA hc ht W (.add b c))]
    (observableActiveValue t ha A hA hc ht W
      (.add (observableActive t ha A hA hc ht W (.add a b)) c)
      (observableActive t ha A hA hc ht W
        (.add a (observableActive t ha A hA hc ht W (.add b c)))))

def ringZeroAdd
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W : ArchCtx A)
    (a : IndependentEquationPrimitive.observableType (equationRows t ha A hA) W) :
    ObjectFormula.{u, v, u} U :=
  observableActiveAnchors t ha A hA hc ht W
    [.zero, .add (observableActive t ha A hA hc ht W .zero) a]
    (observableActiveValue t ha A hA hc ht W
      (.add (observableActive t ha A hA hc ht W .zero) a) a)

def ringNegAddCancel
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W : ArchCtx A)
    (a : IndependentEquationPrimitive.observableType (equationRows t ha A hA) W) :
    ObjectFormula.{u, v, u} U :=
  observableActiveAnchors t ha A hA hc ht W
    [.neg a, .add (observableActive t ha A hA hc ht W (.neg a)) a, .zero]
    (observableActiveValue t ha A hA hc ht W
      (.add (observableActive t ha A hA hc ht W (.neg a)) a)
      (observableActive t ha A hA hc ht W .zero))

def ringMulAssoc
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W : ArchCtx A)
    (a b c : IndependentEquationPrimitive.observableType (equationRows t ha A hA) W) :
    ObjectFormula.{u, v, u} U :=
  observableActiveAnchors t ha A hA hc ht W
    [.mul a b, .mul (observableActive t ha A hA hc ht W (.mul a b)) c,
      .mul b c, .mul a (observableActive t ha A hA hc ht W (.mul b c))]
    (observableActiveValue t ha A hA hc ht W
      (.mul (observableActive t ha A hA hc ht W (.mul a b)) c)
      (observableActive t ha A hA hc ht W
        (.mul a (observableActive t ha A hA hc ht W (.mul b c)))))

def ringMulComm
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W : ArchCtx A)
    (a b : IndependentEquationPrimitive.observableType (equationRows t ha A hA) W) :
    ObjectFormula.{u, v, u} U :=
  observableActiveAnchors t ha A hA hc ht W [.mul a b, .mul b a]
    (observableActiveValue t ha A hA hc ht W (.mul a b)
      (observableActive t ha A hA hc ht W (.mul b a)))

def ringOneMul
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W : ArchCtx A)
    (a : IndependentEquationPrimitive.observableType (equationRows t ha A hA) W) :
    ObjectFormula.{u, v, u} U :=
  observableActiveAnchors t ha A hA hc ht W
    [.one, .mul (observableActive t ha A hA hc ht W .one) a]
    (observableActiveValue t ha A hA hc ht W
      (.mul (observableActive t ha A hA hc ht W .one) a) a)

def ringLeftDistrib
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W : ArchCtx A)
    (a b c : IndependentEquationPrimitive.observableType (equationRows t ha A hA) W) :
    ObjectFormula.{u, v, u} U :=
  observableActiveAnchors t ha A hA hc ht W
    [.add b c, .mul a (observableActive t ha A hA hc ht W (.add b c)),
      .mul a b, .mul a c,
      .add (observableActive t ha A hA hc ht W (.mul a b))
        (observableActive t ha A hA hc ht W (.mul a c))]
    (observableActiveValue t ha A hA hc ht W
      (.mul a (observableActive t ha A hA hc ht W (.add b c)))
      (observableActive t ha A hA hc ht W
        (.add (observableActive t ha A hA hc ht W (.mul a b))
          (observableActive t ha A hA hc ht W (.mul a c)))))

structure RingInstances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W : ArchCtx A) : Prop where
  addAssoc : ∀ a b c, (ringAddAssoc t ha A hA hc ht W a b c).evaluate t
  zeroAdd : ∀ a, (ringZeroAdd t ha A hA hc ht W a).evaluate t
  negAddCancel : ∀ a, (ringNegAddCancel t ha A hA hc ht W a).evaluate t
  mulAssoc : ∀ a b c, (ringMulAssoc t ha A hA hc ht W a b c).evaluate t
  mulComm : ∀ a b, (ringMulComm t ha A hA hc ht W a b).evaluate t
  oneMul : ∀ a, (ringOneMul t ha A hA hc ht W a).evaluate t
  leftDistrib : ∀ a b c, (ringLeftDistrib t ha A hA hc ht W a b c).evaluate t

theorem ringLawful_iff_instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W : ArchCtx A) :
    IndependentRingPrimitive.Carrier.IsLawful
        (IndependentEquationPrimitive.observable (equationRows t ha A hA) W)
        (ht.observable W) ↔ RingInstances t ha A hA hc ht W := by
  unfold IndependentRingPrimitive.Carrier.IsLawful
  constructor
  · intro hl
    exact {
      addAssoc := fun a b c => by simpa [ringAddAssoc] using hl.add_assoc a b c
      zeroAdd := fun a => by simpa [ringZeroAdd] using hl.zero_add a
      negAddCancel := fun a => by simpa [ringNegAddCancel] using hl.neg_add_cancel a
      mulAssoc := fun a b c => by simpa [ringMulAssoc] using hl.mul_assoc a b c
      mulComm := fun a b => by simpa [ringMulComm] using hl.mul_comm a b
      oneMul := fun a => by simpa [ringOneMul] using hl.one_mul a
      leftDistrib := fun a b c => by simpa [ringLeftDistrib] using hl.left_distrib a b c }
  · intro hi
    exact {
      add_assoc := fun a b c => by simpa [ringAddAssoc] using hi.addAssoc a b c
      zero_add := fun a => by simpa [ringZeroAdd] using hi.zeroAdd a
      neg_add_cancel := fun a => by simpa [ringNegAddCancel] using hi.negAddCancel a
      mul_assoc := fun a b c => by simpa [ringMulAssoc] using hi.mulAssoc a b c
      mul_comm := fun a b => by simpa [ringMulComm] using hi.mulComm a b
      one_mul := fun a => by simpa [ringOneMul] using hi.oneMul a
      left_distrib := fun a b c => by simpa [ringLeftDistrib] using hi.leftDistrib a b c }

/-! ## Restriction homomorphism equations -/

abbrev restrictValue
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) {W V : ArchCtx A}
    (h : (contextPreorder t ha A hA hc).le W V)
    (x : IndependentEquationPrimitive.observableType (equationRows t ha A hA) V) :=
  IndependentEquationPrimitive.restrict (equationRows t ha A hA) ht h x

def restrictionAnchor
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (_ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) {W V : ArchCtx A}
    (_h : (contextPreorder t ha A hA hc).le W V)
    (x : IndependentEquationPrimitive.observableType (equationRows t ha A hA) V)
    (body : ObjectFormula.{u, v, w} U) : ObjectFormula.{u, v, w} U :=
  contextAnchor t ha A hA (.le W V)
    (equationAnchor t ha A hA (.observable W .carrier)
      (equationAnchor t ha A hA (.observable V .carrier)
        (equationAnchor t ha A hA (.restriction W V
          (IndependentEquationPrimitive.observableType (equationRows t ha A hA) W)
          (IndependentEquationPrimitive.observableType (equationRows t ha A hA) V) x) body)))

@[simp] theorem restrictionAnchor_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) {W V : ArchCtx A}
    (h : (contextPreorder t ha A hA hc).le W V)
    (x : IndependentEquationPrimitive.observableType (equationRows t ha A hA) V)
    (body : ObjectFormula.{u, v, w} U) :
    (restrictionAnchor t ha A hA hc ht h x body).evaluate t ↔ body.evaluate t := by
  simp [restrictionAnchor]

def restrictionValueFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (_ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) {W V : ArchCtx A}
    (_h : (contextPreorder t ha A hA hc).le W V)
    (x : IndependentEquationPrimitive.observableType (equationRows t ha A hA) V)
    (value : IndependentEquationPrimitive.observableType (equationRows t ha A hA) W) :
    ObjectFormula.{u, v, u} U :=
  contextAnchor t ha A hA (.le W V)
    (equationAnchor t ha A hA (.observable W .carrier)
      (equationAnchor t ha A hA (.observable V .carrier)
        (equationCell A (.restriction W V
          (IndependentEquationPrimitive.observableType (equationRows t ha A hA) W)
          (IndependentEquationPrimitive.observableType (equationRows t ha A hA) V) x)
          (ULift.up (some value)))))

@[simp] theorem restrictionValueFormula_evaluate_iff
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) {W V : ArchCtx A}
    (h : (contextPreorder t ha A hA hc).le W V)
    (x : IndependentEquationPrimitive.observableType (equationRows t ha A hA) V)
    (value : IndependentEquationPrimitive.observableType (equationRows t ha A hA) W) :
    (restrictionValueFormula t ha A hA hc ht h x value).evaluate t ↔
      restrictValue t ha A hA hc ht h x = value := by
  simp only [restrictionValueFormula, contextAnchor_evaluate, equationAnchor_evaluate]
  rw [equationCell_evaluate_iff t ha A hA]
  constructor
  · intro hvalue
    have he := congrArg ULift.down hvalue
    exact Option.some.inj ((Option.some_get _).trans he)
  · intro hvalue
    apply ULift.ext
    exact (Option.some_get _).symm.trans (congrArg some hvalue)

def restrictionZero
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W V : ArchCtx A)
    (h : (contextPreorder t ha A hA hc).le W V) : ObjectFormula.{u, v, u} U :=
  observableActiveAnchor t ha A hA hc ht V .zero
    (observableActiveAnchor t ha A hA hc ht W .zero
      (restrictionAnchor t ha A hA hc ht h
        (observableActive t ha A hA hc ht V .zero)
        (restrictionValueFormula t ha A hA hc ht h
          (observableActive t ha A hA hc ht V .zero)
          (observableActive t ha A hA hc ht W .zero))))

def restrictionOne
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W V : ArchCtx A)
    (h : (contextPreorder t ha A hA hc).le W V) : ObjectFormula.{u, v, u} U :=
  observableActiveAnchor t ha A hA hc ht V .one
    (observableActiveAnchor t ha A hA hc ht W .one
      (restrictionAnchor t ha A hA hc ht h
        (observableActive t ha A hA hc ht V .one)
        (restrictionValueFormula t ha A hA hc ht h
          (observableActive t ha A hA hc ht V .one)
          (observableActive t ha A hA hc ht W .one))))

def restrictionAdd
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W V : ArchCtx A)
    (h : (contextPreorder t ha A hA hc).le W V)
    (a b : IndependentEquationPrimitive.observableType (equationRows t ha A hA) V) :
    ObjectFormula.{u, v, u} U :=
  observableActiveAnchor t ha A hA hc ht V (.add a b)
    (restrictionAnchor t ha A hA hc ht h
      (observableActive t ha A hA hc ht V (.add a b))
      (restrictionAnchor t ha A hA hc ht h a
        (restrictionAnchor t ha A hA hc ht h b
          (observableActiveAnchor t ha A hA hc ht W
            (.add (restrictValue t ha A hA hc ht h a)
              (restrictValue t ha A hA hc ht h b))
            (restrictionValueFormula t ha A hA hc ht h
              (observableActive t ha A hA hc ht V (.add a b))
              (observableActive t ha A hA hc ht W
                (.add (restrictValue t ha A hA hc ht h a)
                  (restrictValue t ha A hA hc ht h b))))))))

def restrictionMul
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W V : ArchCtx A)
    (h : (contextPreorder t ha A hA hc).le W V)
    (a b : IndependentEquationPrimitive.observableType (equationRows t ha A hA) V) :
    ObjectFormula.{u, v, u} U :=
  observableActiveAnchor t ha A hA hc ht V (.mul a b)
    (restrictionAnchor t ha A hA hc ht h
      (observableActive t ha A hA hc ht V (.mul a b))
      (restrictionAnchor t ha A hA hc ht h a
        (restrictionAnchor t ha A hA hc ht h b
          (observableActiveAnchor t ha A hA hc ht W
            (.mul (restrictValue t ha A hA hc ht h a)
              (restrictValue t ha A hA hc ht h b))
            (restrictionValueFormula t ha A hA hc ht h
              (observableActive t ha A hA hc ht V (.mul a b))
              (observableActive t ha A hA hc ht W
                (.mul (restrictValue t ha A hA hc ht h a)
                  (restrictValue t ha A hA hc ht h b))))))))

structure RestrictionInstances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W V : ArchCtx A)
    (h : (contextPreorder t ha A hA hc).le W V) : Prop where
  zero : (restrictionZero t ha A hA hc ht W V h).evaluate t
  one : (restrictionOne t ha A hA hc ht W V h).evaluate t
  add : ∀ a b, (restrictionAdd t ha A hA hc ht W V h a b).evaluate t
  mul : ∀ a b, (restrictionMul t ha A hA hc ht W V h a b).evaluate t

theorem restrictionLawful_iff_instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA))
    (hr : ∀ W, IndependentRingPrimitive.Carrier.IsLawful
      (IndependentEquationPrimitive.observable (equationRows t ha A hA) W)
      (ht.observable W)) (W V : ArchCtx A)
    (h : (contextPreorder t ha A hA hc).le W V) :
    @IndependentRingPrimitive.Hom.IsLawful
      (IndependentEquationPrimitive.observableType (equationRows t ha A hA) V)
      (IndependentEquationPrimitive.observableType (equationRows t ha A hA) W)
      (IndependentEquationPrimitive.observableRing
        (equationRows t ha A hA) ht V (hr V))
      (IndependentEquationPrimitive.observableRing
        (equationRows t ha A hA) ht W (hr W))
      (restrictValue t ha A hA hc ht h) ↔
      RestrictionInstances t ha A hA hc ht W V h := by
  letI := IndependentEquationPrimitive.observableRing
    (equationRows t ha A hA) ht V (hr V)
  letI := IndependentEquationPrimitive.observableRing
    (equationRows t ha A hA) ht W (hr W)
  constructor
  · intro hl
    exact {
      zero := by
        simpa [restrictionZero, IndependentEquationPrimitive.observableRing,
          IndependentRingPrimitive.assemble] using hl.zero
      one := by
        simpa [restrictionOne, IndependentEquationPrimitive.observableRing,
          IndependentRingPrimitive.assemble] using hl.one
      add := fun a b => by
        simpa [restrictionAdd, IndependentEquationPrimitive.observableRing,
          IndependentRingPrimitive.assemble] using hl.add a b
      mul := fun a b => by
        simpa [restrictionMul, IndependentEquationPrimitive.observableRing,
          IndependentRingPrimitive.assemble] using hl.mul a b }
  · intro hi
    exact {
      zero := by
        simpa [restrictionZero, IndependentEquationPrimitive.observableRing,
          IndependentRingPrimitive.assemble] using hi.zero
      one := by
        simpa [restrictionOne, IndependentEquationPrimitive.observableRing,
          IndependentRingPrimitive.assemble] using hi.one
      add := fun a b => by
        simpa [restrictionAdd, IndependentEquationPrimitive.observableRing,
          IndependentRingPrimitive.assemble] using hi.add a b
      mul := fun a b => by
        simpa [restrictionMul, IndependentEquationPrimitive.observableRing,
          IndependentRingPrimitive.assemble] using hi.mul a b }

/-! ## Identity, composition, and coordinate compatibility -/

abbrev violationValue
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W : ArchCtx A)
    (i : IndependentEquationPrimitive.index (equationRows t ha A hA)) (a : U.Atom) :=
  IndependentEquationPrimitive.violation (equationRows t ha A hA) ht W i a

abbrev residualValue
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W : ArchCtx A) (B : ArchitectureObject U)
    (i : IndependentEquationPrimitive.index (equationRows t ha A hA)) (a : U.Atom) :=
  IndependentEquationPrimitive.residual (equationRows t ha A hA) ht W B i a

def violationAnchor
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (_ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W : ArchCtx A)
    (i : IndependentEquationPrimitive.index (equationRows t ha A hA)) (a : U.Atom)
    (body : ObjectFormula.{u, v, w} U) : ObjectFormula.{u, v, w} U :=
  equationAnchor t ha A hA .index
    (equationAnchor t ha A hA (.observable W .carrier)
      (equationAnchor t ha A hA (.violation W
        (IndependentEquationPrimitive.index (equationRows t ha A hA))
        (IndependentEquationPrimitive.observableType (equationRows t ha A hA) W) i a) body))

@[simp] theorem violationAnchor_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W : ArchCtx A)
    (i : IndependentEquationPrimitive.index (equationRows t ha A hA)) (a : U.Atom)
    (body : ObjectFormula.{u, v, w} U) :
    (violationAnchor t ha A hA hc ht W i a body).evaluate t ↔ body.evaluate t := by
  simp [violationAnchor]

def residualAnchor
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (_ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W : ArchCtx A) (B : ArchitectureObject U)
    (i : IndependentEquationPrimitive.index (equationRows t ha A hA)) (a : U.Atom)
    (body : ObjectFormula.{u, v,w} U) : ObjectFormula.{u, v, w} U :=
  equationAnchor t ha A hA .index
    (equationAnchor t ha A hA (.observable W .carrier)
      (equationAnchor t ha A hA (.residual W B
        (IndependentEquationPrimitive.index (equationRows t ha A hA))
        (IndependentEquationPrimitive.observableType (equationRows t ha A hA) W) i a) body))

@[simp] theorem residualAnchor_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W : ArchCtx A) (B : ArchitectureObject U)
    (i : IndependentEquationPrimitive.index (equationRows t ha A hA)) (a : U.Atom)
    (body : ObjectFormula.{u, v, w} U) :
    (residualAnchor t ha A hA hc ht W B i a body).evaluate t ↔ body.evaluate t := by
  simp [residualAnchor]

def identityFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W : ArchCtx A)
    (x : IndependentEquationPrimitive.observableType (equationRows t ha A hA) W) :
    ObjectFormula.{u, v, u} U :=
  restrictionAnchor t ha A hA hc ht ((contextPreorder t ha A hA hc).refl W) x
    (restrictionValueFormula t ha A hA hc ht
      ((contextPreorder t ha A hA hc).refl W) x x)

def compositionFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W V X : ArchCtx A)
    (h : (contextPreorder t ha A hA hc).le W V)
    (g : (contextPreorder t ha A hA hc).le V X)
    (x : IndependentEquationPrimitive.observableType (equationRows t ha A hA) X) :
    ObjectFormula.{u, v, u} U :=
  restrictionAnchor t ha A hA hc ht g x
    (restrictionAnchor t ha A hA hc ht h (restrictValue t ha A hA hc ht g x)
      (restrictionAnchor t ha A hA hc ht ((contextPreorder t ha A hA hc).trans h g) x
        (restrictionValueFormula t ha A hA hc ht
          ((contextPreorder t ha A hA hc).trans h g) x
          (restrictValue t ha A hA hc ht h (restrictValue t ha A hA hc ht g x)))))

def violationFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W V : ArchCtx A)
    (h : (contextPreorder t ha A hA hc).le W V)
    (i : IndependentEquationPrimitive.index (equationRows t ha A hA)) (a : U.Atom) :
    ObjectFormula.{u, v, u} U :=
  violationAnchor t ha A hA hc ht V i a
    (violationAnchor t ha A hA hc ht W i a
      (restrictionAnchor t ha A hA hc ht h (violationValue t ha A hA hc ht V i a)
        (restrictionValueFormula t ha A hA hc ht h
          (violationValue t ha A hA hc ht V i a)
          (violationValue t ha A hA hc ht W i a))))

def residualFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) (W V : ArchCtx A)
    (h : (contextPreorder t ha A hA hc).le W V) (B : ArchitectureObject U)
    (i : IndependentEquationPrimitive.index (equationRows t ha A hA)) (a : U.Atom) :
    ObjectFormula.{u, v, u} U :=
  residualAnchor t ha A hA hc ht V B i a
    (residualAnchor t ha A hA hc ht W B i a
      (restrictionAnchor t ha A hA hc ht h (residualValue t ha A hA hc ht V B i a)
        (restrictionValueFormula t ha A hA hc ht h
          (residualValue t ha A hA hc ht V B i a)
          (residualValue t ha A hA hc ht W B i a))))

structure LawInstances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) : Prop where
  ring : ∀ W, RingInstances t ha A hA hc ht W
  restriction : ∀ W V h, RestrictionInstances t ha A hA hc ht W V h
  identity : ∀ W x, (identityFormula t ha A hA hc ht W x).evaluate t
  composition : ∀ W V X h g x,
    (compositionFormula t ha A hA hc ht W V X h g x).evaluate t
  violation : ∀ W V h i a, (violationFormula t ha A hA hc ht W V h i a).evaluate t
  residual : ∀ W V h B i a, (residualFormula t ha A hA hc ht W V h B i a).evaluate t

theorem lawful_iff_instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (ht : IndependentEquationPrimitive.IsTyped (contextPreorder t ha A hA hc)
      (equationRows t ha A hA)) :
    IndependentEquationPrimitive.IsLawful (equationRows t ha A hA) ht ↔
      LawInstances t ha A hA hc ht := by
  constructor
  · intro hl
    refine {
      ring := ?_
      restriction := ?_
      identity := ?_
      composition := ?_
      violation := ?_
      residual := ?_ }
    · intro W
      exact (ringLawful_iff_instances t ha A hA hc ht W).1 (hl.ring W)
    · intro W V h
      exact (restrictionLawful_iff_instances t ha A hA hc ht hl.ring W V h).1
        (hl.restriction W V h)
    · intro W x
      simpa [identityFormula] using hl.identity W x
    · intro W V X h g x
      simpa [compositionFormula] using hl.composition W V X h g x
    · intro W V h i a
      simpa [violationFormula] using hl.violation W V h i a
    · intro W V h B i a
      simpa [residualFormula] using hl.residual W V h B i a
  · intro hi
    let hr : ∀ W, IndependentRingPrimitive.Carrier.IsLawful
        (IndependentEquationPrimitive.observable (equationRows t ha A hA) W)
        (ht.observable W) := fun W =>
      (ringLawful_iff_instances t ha A hA hc ht W).2 (hi.ring W)
    refine {
      ring := hr
      restriction := ?_
      identity := ?_
      composition := ?_
      violation := ?_
      residual := ?_ }
    · intro W V h
      exact (restrictionLawful_iff_instances t ha A hA hc ht hr W V h).2
        (hi.restriction W V h)
    · intro W x
      simpa [identityFormula] using hi.identity W x
    · intro W V X h g x
      simpa [compositionFormula] using hi.composition W V X h g x
    · intro W V h i a
      simpa [violationFormula] using hi.violation W V h i a
    · intro W V h B i a
      simpa [residualFormula] using hi.residual W V h B i a

structure Instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA)) : Prop where
  typed : TypedInstances t ha A hA
  lawful : LawInstances t ha A hA hc ((typed_iff_instances t ha A hA hc).2 typed)

theorem equationLaws_iff_instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA)) :
    IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc ↔
      Instances t ha A hA hc := by
  constructor
  · rintro ⟨ht, hl⟩
    let hi := (typed_iff_instances t ha A hA hc).1 ht
    refine ⟨hi, ?_⟩
    apply (lawful_iff_instances t ha A hA hc ((typed_iff_instances t ha A hA hc).2 hi)).1
    simpa only [Subsingleton.elim ht ((typed_iff_instances t ha A hA hc).2 hi)] using hl
  · rintro ⟨ht, hl⟩
    exact ⟨(typed_iff_instances t ha A hA hc).2 ht,
      (lawful_iff_instances t ha A hA hc _).2 hl⟩

end Equation

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectDependentFinite

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectDependentFinite
