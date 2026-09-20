import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryObjectDependentOverlapLawFinite
import Formal.Util.AssertStandardAxioms

/-!
# Closed finite formulas for active-object raw laws

Raw activation formulas name every coordinate, relation, context, coefficient
reference, and response row used by their condition.  Generator, identity, and
composition formulas below additionally name every finite polynomial and
variable-image row used by the corresponding point equation.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectDependentFinite

noncomputable section

universe u v w

open Site CategoryTheory LawAlgebra IndependentFiniteLawFormula

variable {U : AtomCarrier.{u}}

namespace Raw

abbrev rawRows
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true) :=
  IndependentGeometryPrimitive.rawTable (rows t ha A hA)

abbrev coefficientNative
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t) :=
  IndependentGeometryTableAssembly.coefficient
    (IndependentGeometryPrimitive.coefficientData t hf)

abbrev coefficientReference
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t) :
    IndependentRawCandidate.CoefficientRef.{v} :=
  @IndependentRawCandidate.coefficientRef _ (coefficientNative t hf).2.toZero

abbrev rawSite
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc) :=
  IndependentGeometryPrimitive.assembledSite t hf (rows t ha A hA) hc he hv ho

def rawAnchor
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (q : IndependentRawCandidate.Query.{u, v} A)
    (body : ObjectFormula.{u, v, w} U) : ObjectFormula.{u, v, w} U :=
  .and (ObjectMatchingFinite.matchCell (.object A) true)
    (.and (.cell (.atObject A (.raw q))
      (some ((rows t ha A hA) (.raw q)))) body)

@[simp] theorem rawAnchor_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (q : IndependentRawCandidate.Query.{u, v} A)
    (body : ObjectFormula.{u, v, w} U) :
    (rawAnchor t ha A hA q body).evaluate t ↔ body.evaluate t := by
  simp only [rawAnchor, ObjectFormula.evaluate,
    ObjectMatchingFinite.matchCell_evaluate, hA, true_and]
  exact and_iff_right
    (IndependentGeometryPrimitive.some_dependent t ha A hA (.raw q)).symm

def coefficientRefAnchor
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (body : ObjectFormula.{u, v, w} U) : ObjectFormula.{u, v, w} U :=
  .and (.cell (.coefficient .carrier) (t (.coefficient .carrier)))
    (.and (.cell (.coefficient (.operation (coefficientNative t hf).1 .zero))
      (t (.coefficient (.operation (coefficientNative t hf).1 .zero)))) body)

@[simp] theorem coefficientRefAnchor_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (body : ObjectFormula.{u, v, w} U) :
    (coefficientRefAnchor t hf body).evaluate t ↔ body.evaluate t := by
  simp [coefficientRefAnchor, ObjectFormula.evaluate]

def labelTypedFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (W : ArchCtx A) (C : Type u) (c : C) (value : CoordinateLabel) :
    ObjectFormula.{u, v, 0} U :=
  rawAnchor t ha A hA (.coordinate W)
    (.cell (.atObject A (.raw (.label W C c)))
      (some (ULift.up (some value))))

def localDataTypedFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (W : ArchCtx A) (C : Type u) (c : C) (value : Type u) :
    ObjectFormula.{u, v, 0} U :=
  rawAnchor t ha A hA (.coordinate W)
    (.cell (.atObject A (.raw (.localData W C c)))
      (some (ULift.up (some value))))

def polynomialTypedFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (W : ArchCtx A) (C J : Type u) (r : IndependentRawCandidate.CoefficientRef.{v})
    (j : J) (value : IndependentPolynomialExpressions.Sparse C r.1 r.2) :
    ObjectFormula.{u, v, 0} U :=
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  rawAnchor t ha A hA (.coordinate W)
    (rawAnchor t ha A hA (.relation W)
      (coefficientRefAnchor t hf
        (.cell (.atObject A (.raw (.polynomial W C J r j)))
          (some (ULift.up (some value))))))

def imageTypedFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (_hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (_ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (W V : ArchCtx A) (C D : Type u) (r : IndependentRawCandidate.CoefficientRef.{v})
    (d : D) (value : IndependentPolynomialExpressions.Sparse C r.1 r.2) :
    ObjectFormula.{u, v, 0} U :=
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  contextAnchor t ha A hA (.le W V)
    (rawAnchor t ha A hA (.coordinate W)
      (rawAnchor t ha A hA (.coordinate V)
        (coefficientRefAnchor t hf
          (.cell (.atObject A (.raw (.image W V C D r d)))
            (some (ULift.up (some value)))))))

@[simp] theorem labelTypedFormula_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (W : ArchCtx A) (C : Type u) (c : C) (value : CoordinateLabel) :
    (labelTypedFormula t ha A hA W C c value).evaluate t ↔
      (rawRows t ha A hA (.label W C c)).down = some value := by
  simp only [labelTypedFormula, rawAnchor_evaluate, ObjectFormula.evaluate]
  rw [← IndependentGeometryPrimitive.some_dependent t ha A hA (.raw (.label W C c))]
  constructor
  · intro h
    exact congrArg ULift.down (Option.some.inj h)
  · intro h
    congr 2
    exact ULift.ext _ _ h

@[simp] theorem localDataTypedFormula_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (W : ArchCtx A) (C : Type u) (c : C) (value : Type u) :
    (localDataTypedFormula t ha A hA W C c value).evaluate t ↔
      (rawRows t ha A hA (.localData W C c)).down = some value := by
  simp only [localDataTypedFormula, rawAnchor_evaluate, ObjectFormula.evaluate]
  rw [← IndependentGeometryPrimitive.some_dependent t ha A hA (.raw (.localData W C c))]
  constructor
  · intro h
    exact congrArg ULift.down (Option.some.inj h)
  · intro h
    congr 2
    exact ULift.ext _ _ h

@[simp] theorem polynomialTypedFormula_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (W : ArchCtx A) (C J : Type u) (r : IndependentRawCandidate.CoefficientRef.{v})
    (j : J) (value : IndependentPolynomialExpressions.Sparse C r.1 r.2) :
    (polynomialTypedFormula t ha A hA hf W C J r j value).evaluate t ↔
      (rawRows t ha A hA (.polynomial W C J r j)).down = some value := by
  simp only [polynomialTypedFormula, rawAnchor_evaluate,
    coefficientRefAnchor_evaluate, ObjectFormula.evaluate]
  rw [← IndependentGeometryPrimitive.some_dependent t ha A hA
    (.raw (.polynomial W C J r j))]
  constructor
  · intro h
    exact congrArg ULift.down (Option.some.inj h)
  · intro h
    congr 2
    exact ULift.ext _ _ h

@[simp] theorem imageTypedFormula_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (W V : ArchCtx A) (C D : Type u) (r : IndependentRawCandidate.CoefficientRef.{v})
    (d : D) (value : IndependentPolynomialExpressions.Sparse C r.1 r.2) :
    (imageTypedFormula t ha A hA hf hc he hv ho W V C D r d value).evaluate t ↔
      (rawRows t ha A hA (.image W V C D r d)).down = some value := by
  simp only [imageTypedFormula, contextAnchor_evaluate, rawAnchor_evaluate,
    coefficientRefAnchor_evaluate, ObjectFormula.evaluate]
  rw [← IndependentGeometryPrimitive.some_dependent t ha A hA
    (.raw (.image W V C D r d))]
  constructor
  · intro h
    exact congrArg ULift.down (Option.some.inj h)
  · intro h
    congr 2
    exact ULift.ext _ _ h

structure TypedInstances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc) : Prop where
  labelSome : ∀ W C c value,
    (labelTypedFormula t ha A hA W C c value).evaluate t →
      C = IndependentRawCandidate.coord (rawRows t ha A hA) W
  labelExists : ∀ W C c,
    C = IndependentRawCandidate.coord (rawRows t ha A hA) W →
      ∃ value, (labelTypedFormula t ha A hA W C c value).evaluate t
  localDataSome : ∀ W C c value,
    (localDataTypedFormula t ha A hA W C c value).evaluate t →
      C = IndependentRawCandidate.coord (rawRows t ha A hA) W
  localDataExists : ∀ W C c,
    C = IndependentRawCandidate.coord (rawRows t ha A hA) W →
      ∃ value, (localDataTypedFormula t ha A hA W C c value).evaluate t
  polynomialSome : ∀ W C J r j value,
    (polynomialTypedFormula t ha A hA hf W C J r j value).evaluate t →
      C = IndependentRawCandidate.coord (rawRows t ha A hA) W ∧
        J = IndependentRawCandidate.rel (rawRows t ha A hA) W ∧
        r = coefficientReference t hf
  polynomialExists : ∀ W C J r j,
    C = IndependentRawCandidate.coord (rawRows t ha A hA) W ∧
      J = IndependentRawCandidate.rel (rawRows t ha A hA) W ∧
      r = coefficientReference t hf →
        ∃ value, (polynomialTypedFormula t ha A hA hf W C J r j value).evaluate t
  imageSome : ∀ W V C D r d value,
    (imageTypedFormula t ha A hA hf hc he hv ho W V C D r d value).evaluate t →
      (rawSite t ha A hA hf hc he hv ho).contextPreorder.le W V ∧
        C = IndependentRawCandidate.coord (rawRows t ha A hA) W ∧
        D = IndependentRawCandidate.coord (rawRows t ha A hA) V ∧
        r = coefficientReference t hf
  imageExists : ∀ W V C D r d,
    (rawSite t ha A hA hf hc he hv ho).contextPreorder.le W V ∧
      C = IndependentRawCandidate.coord (rawRows t ha A hA) W ∧
      D = IndependentRawCandidate.coord (rawRows t ha A hA) V ∧
      r = coefficientReference t hf →
        ∃ value,
          (imageTypedFormula t ha A hA hf hc he hv ho W V C D r d value).evaluate t

theorem typed_iff_instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc) :
    (@IndependentRawCandidate.IsTyped _ _
      (rawSite t ha A hA hf hc he hv ho) (coefficientNative t hf).1
      (coefficientNative t hf).2 (rawRows t ha A hA)) ↔
      TypedInstances t ha A hA hf hc he hv ho := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  constructor
  · intro ht
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro W C c value hvalue
      exact (ht.label W C c).1 (by
        rw [(labelTypedFormula_evaluate t ha A hA W C c value).1 hvalue]
        rfl)
    · intro W C c hC
      have hp := (ht.label W C c).2 hC
      cases hvalue : (rawRows t ha A hA (.label W C c)).down with
      | none => simp [hvalue] at hp
      | some value =>
          exact ⟨value, (labelTypedFormula_evaluate t ha A hA W C c value).2 hvalue⟩
    · intro W C c value hvalue
      exact (ht.localData W C c).1 (by
        rw [(localDataTypedFormula_evaluate t ha A hA W C c value).1 hvalue]
        rfl)
    · intro W C c hC
      have hp := (ht.localData W C c).2 hC
      cases hvalue : (rawRows t ha A hA (.localData W C c)).down with
      | none => simp [hvalue] at hp
      | some value =>
          exact ⟨value,
            (localDataTypedFormula_evaluate t ha A hA W C c value).2 hvalue⟩
    · intro W C J r j value hvalue
      exact (ht.polynomial W C J r j).1 (by
        rw [(polynomialTypedFormula_evaluate t ha A hA hf W C J r j value).1 hvalue]
        rfl)
    · intro W C J r j hactive
      have hp := (ht.polynomial W C J r j).2 hactive
      cases hvalue : (rawRows t ha A hA (.polynomial W C J r j)).down with
      | none => simp [hvalue] at hp
      | some value =>
          exact ⟨value,
            (polynomialTypedFormula_evaluate t ha A hA hf W C J r j value).2 hvalue⟩
    · intro W V C D r d value hvalue
      exact (ht.image W V C D r d).1 (by
        rw [(imageTypedFormula_evaluate t ha A hA hf hc he hv ho
          W V C D r d value).1 hvalue]
        rfl)
    · intro W V C D r d hactive
      have hp := (ht.image W V C D r d).2 hactive
      cases hvalue : (rawRows t ha A hA (.image W V C D r d)).down with
      | none => simp [hvalue] at hp
      | some value =>
          exact ⟨value,
            (imageTypedFormula_evaluate t ha A hA hf hc he hv ho
              W V C D r d value).2 hvalue⟩
  · intro hi
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro W C c
      constructor
      · intro hp
        cases hvalue : (rawRows t ha A hA (.label W C c)).down with
        | none => simp [hvalue] at hp
        | some value =>
            exact hi.labelSome W C c value
              ((labelTypedFormula_evaluate t ha A hA W C c value).2 hvalue)
      · intro hC
        obtain ⟨value, hvalue⟩ := hi.labelExists W C c hC
        rw [(labelTypedFormula_evaluate t ha A hA W C c value).1 hvalue]
        rfl
    · intro W C c
      constructor
      · intro hp
        cases hvalue : (rawRows t ha A hA (.localData W C c)).down with
        | none => simp [hvalue] at hp
        | some value =>
            exact hi.localDataSome W C c value
              ((localDataTypedFormula_evaluate t ha A hA W C c value).2 hvalue)
      · intro hC
        obtain ⟨value, hvalue⟩ := hi.localDataExists W C c hC
        rw [(localDataTypedFormula_evaluate t ha A hA W C c value).1 hvalue]
        rfl
    · intro W C J r j
      constructor
      · intro hp
        cases hvalue : (rawRows t ha A hA (.polynomial W C J r j)).down with
        | none => simp [hvalue] at hp
        | some value =>
            exact hi.polynomialSome W C J r j value
              ((polynomialTypedFormula_evaluate t ha A hA hf W C J r j value).2 hvalue)
      · intro hactive
        obtain ⟨value, hvalue⟩ := hi.polynomialExists W C J r j hactive
        rw [(polynomialTypedFormula_evaluate t ha A hA hf W C J r j value).1 hvalue]
        rfl
    · intro W V C D r d
      constructor
      · intro hp
        cases hvalue : (rawRows t ha A hA (.image W V C D r d)).down with
        | none => simp [hvalue] at hp
        | some value =>
            exact hi.imageSome W V C D r d value
              ((imageTypedFormula_evaluate t ha A hA hf hc he hv ho
                W V C D r d value).2 hvalue)
      · intro hactive
        obtain ⟨value, hvalue⟩ := hi.imageExists W V C D r d hactive
        rw [(imageTypedFormula_evaluate t ha A hA hf hc he hv ho
          W V C D r d value).1 hvalue]
        rfl

abbrev CandidateTyped
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc) : Prop :=
  @IndependentRawCandidate.IsTyped _ _ (rawSite t ha A hA hf hc he hv ho)
    (coefficientNative t hf).1 (coefficientNative t hf).2 (rawRows t ha A hA)

abbrev localRows
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc) :=
  @IndependentRawCandidate.lower _ _ (rawSite t ha A hA hf hc he hv ho)
    (coefficientNative t hf).1 (coefficientNative t hf).2 (rawRows t ha A hA)

abbrev localTyped
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho) :=
  @IndependentRawCandidate.lower_isTyped _ _ (rawSite t ha A hA hf hc he hv ho)
    (coefficientNative t hf).1 (coefficientNative t hf).2 (rawRows t ha A hA) ht

/-- Anchor the exact primitive row used for one selected relation polynomial. -/
def selectedPolynomialAnchor
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (W : (rawSite t ha A hA hf hc he hv ho).category)
    (r : IndependentRawCandidate.rel (rawRows t ha A hA) W.ctx)
    (body : ObjectFormula.{u, v, w} U) : ObjectFormula.{u, v, w} U :=
  rawAnchor t ha A hA (.coordinate W.ctx)
    (rawAnchor t ha A hA (.relation W.ctx)
      (coefficientRefAnchor t hf
        (rawAnchor t ha A hA
          (.polynomial W.ctx
            (IndependentRawCandidate.coord (rawRows t ha A hA) W.ctx)
            (IndependentRawCandidate.rel (rawRows t ha A hA) W.ctx)
            (coefficientReference t hf) r)
          body)))

@[simp] theorem selectedPolynomialAnchor_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (W : (rawSite t ha A hA hf hc he hv ho).category)
    (r : IndependentRawCandidate.rel (rawRows t ha A hA) W.ctx)
    (body : ObjectFormula.{u, v, w} U) :
    (selectedPolynomialAnchor t ha A hA hf hc he hv ho W r body).evaluate t ↔
      body.evaluate t := by
  simp [selectedPolynomialAnchor]

/-- Anchor the exact primitive row used for one selected variable image. -/
def selectedImageAnchor
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    {X Y : (rawSite t ha A hA hf hc he hv ho).category} (_f : X ⟶ Y)
    (c : IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
    (body : ObjectFormula.{u, v, w} U) : ObjectFormula.{u, v, w} U :=
  contextAnchor t ha A hA (.le X.ctx Y.ctx)
    (rawAnchor t ha A hA (.coordinate X.ctx)
      (rawAnchor t ha A hA (.coordinate Y.ctx)
        (coefficientRefAnchor t hf
          (rawAnchor t ha A hA
            (.image X.ctx Y.ctx
              (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
              (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
              (coefficientReference t hf) c)
            body))))

@[simp] theorem selectedImageAnchor_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    {X Y : (rawSite t ha A hA hf hc he hv ho).category} (f : X ⟶ Y)
    (c : IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
    (body : ObjectFormula.{u, v, w} U) :
    (selectedImageAnchor t ha A hA hf hc he hv ho f c body).evaluate t ↔
      body.evaluate t := by
  simp [selectedImageAnchor]

abbrev relationPolynomial
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    (W : (rawSite t ha A hA hf hc he hv ho).category)
    (r : IndependentRawCandidate.rel (rawRows t ha A hA) W.ctx) :
    @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) W.ctx)
      (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact (IndependentRawLocal.relations (localRows t ha A hA hf hc he hv ho)
    (localTyped t ha A hA hf hc he hv ho ht) W).polynomial r

abbrev variableImage
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    {X Y : (rawSite t ha A hA hf hc he hv ho).category} (f : X ⟶ Y)
    (c : IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx) :
    @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
      (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact IndependentRawLocal.variableImage (localRows t ha A hA hf hc he hv ho)
    (localTyped t ha A hA hf hc he hv ho ht) f c

abbrev mappedPolynomial
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    {X Y : (rawSite t ha A hA hf hc he hv ho).category} (f : X ⟶ Y)
    (p : @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
      (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) :
    @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
      (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact (IndependentRawLocal.restriction (localRows t ha A hA hf hc he hv ho)
    (localTyped t ha A hA hf hc he hv ho ht) f).polynomialMap p

/-- Compile one native polynomial using the coefficient ring recovered from
the selected foundation rows. -/
noncomputable def polynomialExpression
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t) {C : Type u}
    (p : @MvPolynomial C (coefficientNative t hf).1
      (coefficientNative t hf).2.toCommSemiring) :
    IndependentPolynomialExpressions.Expr C (coefficientNative t hf).1 := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact IndependentPolynomialExpressions.compile p

/-- Evaluate one selected target polynomial through the finite expression compiler. -/
abbrev substitutionValue
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    {X Y : (rawSite t ha A hA hf hc he hv ho).category} (f : X ⟶ Y)
    (p : @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
      (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) :
    @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
      (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact IndependentPolynomialExpressions.evaluate
    (IndependentPolynomialExpressions.nativeTable MvPolynomial.C
      (variableImage t ha A hA hf hc he hv ho ht f))
    (polynomialExpression t hf p)

theorem substitutionValue_eq_mappedPolynomial
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    {X Y : (rawSite t ha A hA hf hc he hv ho).category} (f : X ⟶ Y)
    (p : @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
      (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) :
    substitutionValue t ha A hA hf hc he hv ho ht f p =
      mappedPolynomial t ha A hA hf hc he hv ho ht f p := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  simpa [substitutionValue, mappedPolynomial, IndependentRawLocal.restriction,
    TypedCoordinateRestriction.polynomialMap, polynomialExpression] using
    (IndependentPolynomialExpressions.evaluate_compile MvPolynomial.C
      (variableImage t ha A hA hf hc he hv ho ht f) p)

/-- Primitive polynomial table used to substitute the selected variable-image
cells of one raw restriction. -/
abbrev substitutionTable
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    {X Y : (rawSite t ha A hA hf hc he hv ho).category} (f : X ⟶ Y) := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact IndependentPolynomialExpressions.nativeTable MvPolynomial.C
    (variableImage t ha A hA hf hc he hv ho ht f)

/-- Closed cell formula for the compiled substitution of one native
polynomial.  Its support is the recursive six-role AST support. -/
noncomputable def substitutionCellFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    {X Y : (rawSite t ha A hA hf hc he hv ho).category} (f : X ⟶ Y)
    (p : @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
      (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)
    (expected : @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
      (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact IndependentPolynomialExpressions.expressionFormula
    (substitutionTable t ha A hA hf hc he hv ho ht f)
    (polynomialExpression t hf p) expected

/-- Anchor one coefficient-ring operation used by a synthetic polynomial
query.  The operation arguments remain the exact native coefficient values
appearing in that query. -/
def coefficientOperationAnchor
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (q : IndependentRingPrimitive.Query (coefficientNative t hf).1)
    (body : ObjectFormula.{u, v, w} U) : ObjectFormula.{u, v, w} U :=
  .and (.cell (.coefficient (.operation (coefficientNative t hf).1 q))
    (t (.coefficient (.operation (coefficientNative t hf).1 q)))) body

@[simp] theorem coefficientOperationAnchor_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (q : IndependentRingPrimitive.Query (coefficientNative t hf).1)
    (body : ObjectFormula.{u, v, w} U) :
    (coefficientOperationAnchor t hf q body).evaluate t ↔ body.evaluate t := by
  simp [coefficientOperationAnchor, ObjectFormula.evaluate]

/-- Anchor a finite list of coefficient-ring operation points. -/
def coefficientOperationAnchors
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t) :
    List (IndependentRingPrimitive.Query (coefficientNative t hf).1) →
      ObjectFormula.{u, v, w} U → ObjectFormula.{u, v, w} U
  | [], body => body
  | q :: qs, body => coefficientOperationAnchor t hf q
      (coefficientOperationAnchors t hf qs body)

@[simp] theorem coefficientOperationAnchors_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (qs : List (IndependentRingPrimitive.Query (coefficientNative t hf).1))
    (body : ObjectFormula.{u, v, w} U) :
    (coefficientOperationAnchors t hf qs body).evaluate t ↔ body.evaluate t := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [coefficientOperationAnchors, ih]

/-- Coefficient operations used pointwise by one native polynomial sum. -/
noncomputable def polynomialAddQueries
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t) {C : Type u}
    (p q : @MvPolynomial C (coefficientNative t hf).1
      (coefficientNative t hf).2.toCommSemiring) :
    List (IndependentRingPrimitive.Query (coefficientNative t hf).1) := by
  classical
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact .zero :: (p.support ∪ q.support).toList.map
    (fun m => .add (p.coeff m) (q.coeff m))

/-- Exact coefficient products that can contribute to one product monomial. -/
noncomputable def polynomialProductTerms
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t) {C : Type u}
    (p q : @MvPolynomial C (coefficientNative t hf).1
      (coefficientNative t hf).2.toCommSemiring) (m : C →₀ ℕ) :
    List (coefficientNative t hf).1 := by
  classical
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact (p.support.toList.flatMap fun left =>
    q.support.toList.filterMap fun right =>
      if left + right = m then some (p.coeff left * q.coeff right) else none)

/-- Primitive additions used by the fixed right-associated sum of a finite
coefficient list. -/
def coefficientSumQueries
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t) :
    List (coefficientNative t hf).1 →
      List (IndependentRingPrimitive.Query (coefficientNative t hf).1)
  | [] => [.zero]
  | value :: values => by
      letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
      exact .add value (values.foldr (· + ·) 0) :: coefficientSumQueries t hf values

/-- All coefficient multiplication and accumulation points used by a native
polynomial product.  Both index sets come from native finite supports. -/
noncomputable def polynomialMulQueries
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t) {C : Type u}
    (p q : @MvPolynomial C (coefficientNative t hf).1
      (coefficientNative t hf).2.toCommSemiring) :
    List (IndependentRingPrimitive.Query (coefficientNative t hf).1) := by
  classical
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  let pairs := p.support.toList.flatMap fun left =>
    q.support.toList.map fun right => (left, right)
  let monomials := pairs.map (fun pair => pair.1 + pair.2) |>.eraseDups
  exact pairs.map (fun pair => .mul (p.coeff pair.1) (q.coeff pair.2)) ++
    monomials.flatMap (fun m =>
      coefficientSumQueries t hf (polynomialProductTerms t hf p q m))

/-- Original object-table cells that supply one query of a substitution AST.
Variables use their raw image row; arithmetic queries name the corresponding
finite coefficient-operation trace. -/
noncomputable def substitutionQueryFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (_ht : CandidateTyped t ha A hA hf hc he hv ho)
    {X Y : (rawSite t ha A hA hf hc he hv ho).category} (f : X ⟶ Y) :
    IndependentPolynomialExpressions.Query
      (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
      (coefficientNative t hf).1
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) →
      ObjectFormula.{u, v, max u v} U
  | .coefficient _ => coefficientRefAnchor t hf .truth
  | .variable c => selectedImageAnchor t ha A hA hf hc he hv ho f c .truth
  | .zero => coefficientOperationAnchor t hf .zero .truth
  | .one => coefficientOperationAnchors t hf [.zero, .one] .truth
  | .add p q => coefficientOperationAnchors t hf
      (polynomialAddQueries t hf p q) .truth
  | .mul p q => coefficientOperationAnchors t hf
      (polynomialMulQueries t hf p q) .truth

/-- Object-table anchors corresponding to every query in the compiled AST
support.  Variable queries name their raw image rows; arithmetic queries name
the finite coefficient-operation trace used by the native polynomial value. -/
noncomputable def substitutionObjectFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    {X Y : (rawSite t ha A hA hf hc he hv ho).category} (f : X ⟶ Y)
    (p : @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
      (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) :
    ObjectFormula.{u, v, max u v} U := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  let table := substitutionTable t ha A hA hf hc he hv ho ht f
  let expression := polynomialExpression t hf p
  exact ObjectFormula.allList
    (IndependentPolynomialExpressions.support table expression).toList
      (substitutionQueryFormula t ha A hA hf hc he hv ho ht f)

/-- Every synthetic substitution query in the canonical AST support is
supplied by a finite formula over the original object table. -/
theorem substitutionSupport_anchored
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    {X Y : (rawSite t ha A hA hf hc he hv ho).category} (f : X ⟶ Y)
    (p : @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
      (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) :
    ∀ q ∈ IndependentPolynomialExpressions.support
        (substitutionTable t ha A hA hf hc he hv ho ht f)
        (polynomialExpression t hf p),
      (substitutionQueryFormula t ha A hA hf hc he hv ho ht f q).evaluate t := by
  intro q hq
  cases q <;> simp [substitutionQueryFormula, ObjectFormula.evaluate]

@[simp] theorem substitutionCellFormula_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    {X Y : (rawSite t ha A hA hf hc he hv ho).category} (f : X ⟶ Y)
    (p : @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
      (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)
    (expected : @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
      (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) :
    (substitutionCellFormula t ha A hA hf hc he hv ho ht f p expected).evaluate
        (substitutionTable t ha A hA hf hc he hv ho ht f) ↔
      substitutionValue t ha A hA hf hc he hv ho ht f p = expected := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  constructor
  · intro h
    exact IndependentPolynomialExpressions.evaluate_eq_expected_of_expressionFormula
      (substitutionTable t ha A hA hf hc he hv ho ht f)
      (substitutionTable t ha A hA hf hc he hv ho ht f)
      (polynomialExpression t hf p) expected h
  · intro h
    exact (IndependentPolynomialExpressions.expressionFormula_evaluate _ _ _).2 h

@[simp] theorem substitutionObjectFormula_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    {X Y : (rawSite t ha A hA hf hc he hv ho).category} (f : X ⟶ Y)
    (p : @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
      (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) :
    (substitutionObjectFormula t ha A hA hf hc he hv ho ht f p).evaluate t := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  simp only [substitutionObjectFormula, ObjectFormula.evaluate_allList]
  intro q hq
  exact substitutionSupport_anchored t ha A hA hf hc he hv ho ht f p q (by simpa using hq)

/-- Finite expression for the generator witness's sparse polynomial combination. -/
noncomputable def witnessExpression
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    (X : (rawSite t ha A hA hf hc he hv ho).category)
    (w : IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx →₀
      @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) :
    IndependentPolynomialExpressions.Expr Unit
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) :=
  IndependentPolynomialExpressions.Expr.sum
    (w.support.toList.map (fun i =>
      .mul (.coefficient (w i))
        (.coefficient (relationPolynomial t ha A hA hf hc he hv ho ht X i))))

abbrev witnessValue
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    (X : (rawSite t ha A hA hf hc he hv ho).category)
    (w : IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx →₀
      @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) :
    @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
      (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  let R := MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
    (coefficientNative t hf).1
  exact IndependentPolynomialExpressions.evaluate
    (IndependentPolynomialExpressions.nativeTable (RingHom.id R) (fun _ : Unit => 0))
    (witnessExpression t ha A hA hf hc he hv ho ht X w)

theorem witnessValue_eq_sum
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    (X : (rawSite t ha A hA hf hc he hv ho).category)
    (w : IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx →₀
      @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) :
    witnessValue t ha A hA hf hc he hv ho ht X w =
      w.sum (fun i a =>
        a * relationPolynomial t ha A hA hf hc he hv ho ht X i) := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  simp [witnessValue, witnessExpression, IndependentPolynomialExpressions.evaluate_sum,
    IndependentPolynomialExpressions.evaluate, IndependentPolynomialExpressions.nativeTable,
    Finsupp.sum]

/-- Primitive polynomial table for the finite generator combination. -/
abbrev witnessTable
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (_ht : CandidateTyped t ha A hA hf hc he hv ho)
    (X : (rawSite t ha A hA hf hc he hv ho).category) := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  let R := MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
    (coefficientNative t hf).1
  exact IndependentPolynomialExpressions.nativeTable (RingHom.id R) (fun _ : Unit => 0)

/-- Closed cell formula that traverses the complete finite AST of the
generator witness combination. -/
noncomputable def witnessCellFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    (X : (rawSite t ha A hA hf hc he hv ho).category)
    (w : IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx →₀
      @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact IndependentPolynomialExpressions.expressionFormula
    (witnessTable t ha A hA hf hc he hv ho ht X)
    (witnessExpression t ha A hA hf hc he hv ho ht X w)
    (witnessValue t ha A hA hf hc he hv ho ht X w)

/-- Original coefficient-operation cells supplying one synthetic query in the
finite generator witness.  Relation-polynomial rows themselves are anchored
separately by `witnessObjectFormula`. -/
noncomputable def witnessQueryFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (_ht : CandidateTyped t ha A hA hf hc he hv ho)
    (X : (rawSite t ha A hA hf hc he hv ho).category) :
    IndependentPolynomialExpressions.Query Unit
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) →
      ObjectFormula.{u, v, max u v} U
  | .coefficient _ => coefficientRefAnchor t hf .truth
  | .variable _ => coefficientOperationAnchor t hf .zero .truth
  | .zero => coefficientOperationAnchor t hf .zero .truth
  | .one => coefficientOperationAnchors t hf [.zero, .one] .truth
  | .add p q => coefficientOperationAnchors t hf
      (polynomialAddQueries t hf p q) .truth
  | .mul p q => coefficientOperationAnchors t hf
      (polynomialMulQueries t hf p q) .truth

/-- Object rows and the selected coefficient declaration used by the finite
generator-expression support. -/
noncomputable def witnessObjectFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    (X : (rawSite t ha A hA hf hc he hv ho).category)
    (w : IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx →₀
      @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) :
    ObjectFormula.{u, v, max u v} U := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  let table := witnessTable t ha A hA hf hc he hv ho ht X
  let expression := witnessExpression t ha A hA hf hc he hv ho ht X w
  exact .and
    (ObjectFormula.allList w.support.toList (fun i =>
      selectedPolynomialAnchor t ha A hA hf hc he hv ho X i .truth))
    (ObjectFormula.allList
      (IndependentPolynomialExpressions.support table expression).toList
        (witnessQueryFormula t ha A hA hf hc he hv ho ht X))

/-- Every synthetic generator-witness query in the canonical AST support is
supplied by finite relation and coefficient-operation cells from the original
object table. -/
theorem witnessSupport_anchored
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    (X : (rawSite t ha A hA hf hc he hv ho).category)
    (w : IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx →₀
      @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) :
    ∀ q ∈ IndependentPolynomialExpressions.support
        (witnessTable t ha A hA hf hc he hv ho ht X)
        (witnessExpression t ha A hA hf hc he hv ho ht X w),
      (witnessQueryFormula t ha A hA hf hc he hv ho ht X q).evaluate t := by
  intro q hq
  cases q <;> simp [witnessQueryFormula, ObjectFormula.evaluate]

@[simp] theorem witnessObjectFormula_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    (X : (rawSite t ha A hA hf hc he hv ho).category)
    (w : IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx →₀
      @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) :
    (witnessObjectFormula t ha A hA hf hc he hv ho ht X w).evaluate t := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  simp only [witnessObjectFormula, ObjectFormula.evaluate,
    ObjectFormula.evaluate_allList]
  constructor
  · intro i hi
    simp [ObjectFormula.evaluate]
  · intro q hq
    exact witnessSupport_anchored t ha A hA hf hc he hv ho ht X w q (by simpa using hq)

@[simp] theorem witnessCellFormula_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    (X : (rawSite t ha A hA hf hc he hv ho).category)
    (w : IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx →₀
      @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) :
    (witnessCellFormula t ha A hA hf hc he hv ho ht X w).evaluate
      (witnessTable t ha A hA hf hc he hv ho ht X) := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact (IndependentPolynomialExpressions.expressionFormula_evaluate _ _ _).2 rfl

/-- Object-table support of the raw identity equation. -/
noncomputable def identityFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    (W : (rawSite t ha A hA hf hc he hv ho).category)
    (c : IndependentRawCandidate.coord (rawRows t ha A hA) W.ctx) :
    ObjectFormula.{u, v, max u v} U := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact substitutionObjectFormula t ha A hA hf hc he hv ho ht (𝟙 W)
    (@MvPolynomial.X (coefficientNative t hf).1 _
      (coefficientNative t hf).2.toCommSemiring c)

/-- Finite polynomial-cell equation for the raw identity law. -/
noncomputable def identityPolynomialFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    (W : (rawSite t ha A hA hf hc he hv ho).category)
    (c : IndependentRawCandidate.coord (rawRows t ha A hA) W.ctx) := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  let p := @MvPolynomial.X (coefficientNative t hf).1 _
    (coefficientNative t hf).2.toCommSemiring c
  exact substitutionCellFormula t ha A hA hf hc he hv ho ht (𝟙 W) p p

@[simp] theorem identityFormula_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    (W : (rawSite t ha A hA hf hc he hv ho).category)
    (c : IndependentRawCandidate.coord (rawRows t ha A hA) W.ctx) :
    (identityFormula t ha A hA hf hc he hv ho ht W c).evaluate t ∧
      (identityPolynomialFormula t ha A hA hf hc he hv ho ht W c).evaluate
        (substitutionTable t ha A hA hf hc he hv ho ht (𝟙 W)) ↔
      variableImage t ha A hA hf hc he hv ho ht (𝟙 W) c =
        @MvPolynomial.X (coefficientNative t hf).1 _
          (coefficientNative t hf).2.toCommSemiring c := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  simp only [identityFormula, substitutionObjectFormula_evaluate, true_and,
    identityPolynomialFormula, substitutionCellFormula_evaluate]
  rw [substitutionValue_eq_mappedPolynomial]
  simp [mappedPolynomial, IndependentRawLocal.restriction,
    TypedCoordinateRestriction.polynomialMap]

/-- Object-table support of the raw composition equation. -/
noncomputable def compositionFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    {X Y Z : (rawSite t ha A hA hf hc he hv ho).category}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : IndependentRawCandidate.coord (rawRows t ha A hA) Z.ctx) :
    ObjectFormula.{u, v, max u v} U := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  let p := variableImage t ha A hA hf hc he hv ho ht g c
  exact selectedImageAnchor t ha A hA hf hc he hv ho (f ≫ g) c
    (selectedImageAnchor t ha A hA hf hc he hv ho g c
      (substitutionObjectFormula t ha A hA hf hc he hv ho ht f p))

/-- Finite polynomial-cell equation for raw restriction composition. -/
noncomputable def compositionPolynomialFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    {X Y Z : (rawSite t ha A hA hf hc he hv ho).category}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : IndependentRawCandidate.coord (rawRows t ha A hA) Z.ctx) := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact substitutionCellFormula t ha A hA hf hc he hv ho ht f
    (variableImage t ha A hA hf hc he hv ho ht g c)
    (variableImage t ha A hA hf hc he hv ho ht (f ≫ g) c)

@[simp] theorem compositionFormula_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    {X Y Z : (rawSite t ha A hA hf hc he hv ho).category}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : IndependentRawCandidate.coord (rawRows t ha A hA) Z.ctx) :
    (compositionFormula t ha A hA hf hc he hv ho ht f g c).evaluate t ∧
      (compositionPolynomialFormula t ha A hA hf hc he hv ho ht f g c).evaluate
        (substitutionTable t ha A hA hf hc he hv ho ht f) ↔
      variableImage t ha A hA hf hc he hv ho ht (f ≫ g) c =
        mappedPolynomial t ha A hA hf hc he hv ho ht f
          (variableImage t ha A hA hf hc he hv ho ht g c) := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  simp only [compositionFormula, selectedImageAnchor_evaluate,
    substitutionObjectFormula_evaluate, compositionPolynomialFormula,
    substitutionCellFormula_evaluate, true_and]
  rw [substitutionValue_eq_mappedPolynomial]
  exact eq_comm

/-- Object-table support of one raw relation-generator equation. -/
noncomputable def generatorFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    {X Y : (rawSite t ha A hA hf hc he hv ho).category} (f : X ⟶ Y)
    (r : IndependentRawCandidate.rel (rawRows t ha A hA) Y.ctx)
    (w : IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx →₀
      @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) :
    ObjectFormula.{u, v, max u v} U := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  let p := relationPolynomial t ha A hA hf hc he hv ho ht Y r
  exact selectedPolynomialAnchor t ha A hA hf hc he hv ho Y r
    (.and (witnessObjectFormula t ha A hA hf hc he hv ho ht X w)
      (substitutionObjectFormula t ha A hA hf hc he hv ho ht f p))

/-- Finite polynomial-cell equation comparing the compiled target relation
with the finite generator witness. -/
noncomputable def generatorPolynomialFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    {X Y : (rawSite t ha A hA hf hc he hv ho).category} (f : X ⟶ Y)
    (r : IndependentRawCandidate.rel (rawRows t ha A hA) Y.ctx)
    (w : IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx →₀
      @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact substitutionCellFormula t ha A hA hf hc he hv ho ht f
    (relationPolynomial t ha A hA hf hc he hv ho ht Y r)
    (witnessValue t ha A hA hf hc he hv ho ht X w)

@[simp] theorem generatorFormula_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    {X Y : (rawSite t ha A hA hf hc he hv ho).category} (f : X ⟶ Y)
    (r : IndependentRawCandidate.rel (rawRows t ha A hA) Y.ctx)
    (w : IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx →₀
      @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) :
    (generatorFormula t ha A hA hf hc he hv ho ht f r w).evaluate t ∧
      (witnessCellFormula t ha A hA hf hc he hv ho ht X w).evaluate
        (witnessTable t ha A hA hf hc he hv ho ht X) ∧
      (generatorPolynomialFormula t ha A hA hf hc he hv ho ht f r w).evaluate
        (substitutionTable t ha A hA hf hc he hv ho ht f) ↔
      w.sum (fun i a =>
        a * relationPolynomial t ha A hA hf hc he hv ho ht X i) =
        mappedPolynomial t ha A hA hf hc he hv ho ht f
          (relationPolynomial t ha A hA hf hc he hv ho ht Y r) := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  simp only [generatorFormula, selectedPolynomialAnchor_evaluate,
    ObjectFormula.evaluate, witnessObjectFormula_evaluate,
    substitutionObjectFormula_evaluate, true_and, witnessCellFormula_evaluate,
    generatorPolynomialFormula, substitutionCellFormula_evaluate]
  rw [witnessValue_eq_sum, substitutionValue_eq_mappedPolynomial]
  exact eq_comm

structure LawInstances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho) : Prop where
  generator : ∀ {X Y : (rawSite t ha A hA hf hc he hv ho).category}
    (f : X ⟶ Y) (r : IndependentRawCandidate.rel (rawRows t ha A hA) Y.ctx),
    ∃ w : IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx →₀
      @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring,
      (generatorFormula t ha A hA hf hc he hv ho ht f r w).evaluate t ∧
        (witnessCellFormula t ha A hA hf hc he hv ho ht X w).evaluate
          (witnessTable t ha A hA hf hc he hv ho ht X) ∧
        (generatorPolynomialFormula t ha A hA hf hc he hv ho ht f r w).evaluate
          (substitutionTable t ha A hA hf hc he hv ho ht f)
  identity : ∀ (W : (rawSite t ha A hA hf hc he hv ho).category)
    (c : IndependentRawCandidate.coord (rawRows t ha A hA) W.ctx),
    (identityFormula t ha A hA hf hc he hv ho ht W c).evaluate t ∧
      (identityPolynomialFormula t ha A hA hf hc he hv ho ht W c).evaluate
        (substitutionTable t ha A hA hf hc he hv ho ht (𝟙 W))
  composition : ∀ {X Y Z : (rawSite t ha A hA hf hc he hv ho).category}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : IndependentRawCandidate.coord (rawRows t ha A hA) Z.ctx),
    (compositionFormula t ha A hA hf hc he hv ho ht f g c).evaluate t ∧
      (compositionPolynomialFormula t ha A hA hf hc he hv ho ht f g c).evaluate
        (substitutionTable t ha A hA hf hc he hv ho ht f)

theorem lawful_iff_instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho) :
    (@IndependentRawCandidate.IsLawful _ _ (rawSite t ha A hA hf hc he hv ho)
      (coefficientNative t hf).1 (coefficientNative t hf).2
      (rawRows t ha A hA) ht) ↔
      LawInstances t ha A hA hf hc he hv ho ht := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  constructor
  · intro hl
    refine ⟨?_, ?_, ?_⟩
    · intro X Y f r
      obtain ⟨w, hw⟩ := hl.generator f r
      exact ⟨w, (generatorFormula_evaluate t ha A hA hf hc he hv ho ht f r w).2 hw⟩
    · intro W c
      exact (identityFormula_evaluate t ha A hA hf hc he hv ho ht W c).2
        (hl.identity W c)
    · intro X Y Z f g c
      exact (compositionFormula_evaluate t ha A hA hf hc he hv ho ht f g c).2
        (hl.composition f g c)
  · intro hi
    refine { generator := ?_, identity := ?_, composition := ?_ }
    · intro X Y f r
      obtain ⟨w, hw⟩ := hi.generator f r
      exact ⟨w, (generatorFormula_evaluate t ha A hA hf hc he hv ho ht f r w).1 hw⟩
    · intro W c
      exact (identityFormula_evaluate t ha A hA hf hc he hv ho ht W c).1
        (hi.identity W c)
    · intro X Y Z f g c
      exact (compositionFormula_evaluate t ha A hA hf hc he hv ho ht f g c).1
        (hi.composition f g c)

structure Instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc) : Prop where
  typed : TypedInstances t ha A hA hf hc he hv ho
  lawful : LawInstances t ha A hA hf hc he hv ho
    ((typed_iff_instances t ha A hA hf hc he hv ho).2 typed)

theorem rawLaws_iff_instances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc) :
    (∃ ht : CandidateTyped t ha A hA hf hc he hv ho,
      @IndependentRawCandidate.IsLawful _ _ (rawSite t ha A hA hf hc he hv ho)
        (coefficientNative t hf).1 (coefficientNative t hf).2
        (rawRows t ha A hA) ht) ↔
      Instances t ha A hA hf hc he hv ho := by
  constructor
  · rintro ⟨ht, hl⟩
    let hi := (typed_iff_instances t ha A hA hf hc he hv ho).1 ht
    refine ⟨hi, ?_⟩
    apply (lawful_iff_instances t ha A hA hf hc he hv ho
      ((typed_iff_instances t ha A hA hf hc he hv ho).2 hi)).1
    simpa only [Subsingleton.elim ht
      ((typed_iff_instances t ha A hA hf hc he hv ho).2 hi)] using hl
  · rintro ⟨ht, hl⟩
    exact ⟨(typed_iff_instances t ha A hA hf hc he hv ho).2 ht,
      (lawful_iff_instances t ha A hA hf hc he hv ho _).2 hl⟩

end Raw

end


end AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectDependentFinite

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryPrimitive.ObjectDependentFinite
