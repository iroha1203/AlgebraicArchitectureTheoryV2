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

/-- Typing witness for the coefficient carrier selected by the foundation rows. -/
abbrev coefficientTyped
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t) :=
  hf.coefficient.choose

/-- Closed object formula requiring one coefficient operation to have an exact value. -/
def coefficientValueFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (q : IndependentRingPrimitive.Query (coefficientNative t hf).1)
    (value : (coefficientNative t hf).1) : ObjectFormula.{u, v, max u v} U :=
  coefficientRefAnchor t hf
    (.cell (.coefficient (.operation (coefficientNative t hf).1 q))
      (ULift.up (ULift.up (some value))))

/-- Exact coefficient cells evaluate to the corresponding native ring operation. -/
@[simp] theorem coefficientValueFormula_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (q : IndependentRingPrimitive.Query (coefficientNative t hf).1)
    (value : (coefficientNative t hf).1) :
    (coefficientValueFormula t hf q value).evaluate t ↔
      IndependentRingPrimitive.read (coefficientNative t hf).2 q = value := by
  simp only [coefficientValueFormula, coefficientRefAnchor_evaluate,
    ObjectFormula.evaluate]
  apply Iff.trans (b := IndependentRingPrimitive.Carrier.active
    (IndependentGeometryPrimitive.coefficient t) (coefficientTyped t hf) q = value)
  · constructor
    · intro h
      have he := congrArg (fun result => result.down.down) h
      exact Option.some.inj ((Option.some_get _).trans he)
    · intro h
      apply ULift.ext
      apply ULift.ext
      exact (Option.some_get _).symm.trans (congrArg some h)
  · change IndependentRingPrimitive.Carrier.active
      (IndependentGeometryPrimitive.coefficient t) (coefficientTyped t hf) q = value ↔
    IndependentRingPrimitive.read
      (IndependentRingPrimitive.assemble
        (IndependentRingPrimitive.Carrier.active
          (IndependentGeometryPrimitive.coefficient t) (coefficientTyped t hf))
        hf.coefficient.choose_spec) q = value
    rw [IndependentRingPrimitive.read_assemble]

/-- Closed object formula fixing one raw variable-image cell to an expected polynomial.
The source and target contexts determine the unique morphism represented by the cell. -/
noncomputable def variableImageValueFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    {X Y : (rawSite t ha A hA hf hc he hv ho).category}
    (c : IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
    (expected : @MvPolynomial
      (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
      (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) :
    ObjectFormula.{u, v, max u v} U := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact contextAnchor t ha A hA (.le X.ctx Y.ctx)
    (rawAnchor t ha A hA (.coordinate X.ctx)
      (rawAnchor t ha A hA (.coordinate Y.ctx)
        (coefficientRefAnchor t hf
          (.cell (.atObject A (.raw (.image X.ctx Y.ctx
            (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
            (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
            (coefficientReference t hf) c)))
            (some (ULift.up (some
              (IndependentPolynomialExpressions.sparseEquiv expected))))))))

/-- An exact raw image cell recovers the selected native variable image. -/
@[simp] theorem variableImageValueFormula_evaluate
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
    (c : IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
    (expected : @MvPolynomial
      (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
      (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) :
    (variableImageValueFormula t ha A hA hf hc he hv ho c expected).evaluate t ↔
      variableImage t ha A hA hf hc he hv ho ht f c = expected := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  simp only [variableImageValueFormula, contextAnchor_evaluate, rawAnchor_evaluate,
    coefficientRefAnchor_evaluate, ObjectFormula.evaluate]
  refine Iff.trans (b := (rawRows t ha A hA
      (.image X.ctx Y.ctx
        (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
        (coefficientReference t hf) c)).down =
      some (IndependentPolynomialExpressions.sparseEquiv expected)) ?_ ?_
  · rw [← IndependentGeometryPrimitive.some_dependent t ha A hA
      (.raw (.image X.ctx Y.ctx
        (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
        (coefficientReference t hf) c))]
    constructor
    · intro h
      exact congrArg ULift.down (Option.some.inj h)
    · intro h
      congr 2
      exact ULift.ext _ _ h
  · change (rawRows t ha A hA
      (.image X.ctx Y.ctx
        (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
        (coefficientReference t hf) c)).down =
      some (IndependentPolynomialExpressions.sparseEquiv expected) ↔ _
    have hsome : (rawRows t ha A hA
        (.image X.ctx Y.ctx
          (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
          (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
          (coefficientReference t hf) c)).down.isSome := by
      exact (ht.image X.ctx Y.ctx
        (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
        (coefficientReference t hf) c).2 ⟨leOfHom f, rfl, rfl, rfl⟩
    cases hraw : (rawRows t ha A hA
        (.image X.ctx Y.ctx
          (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
          (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
          (coefficientReference t hf) c)).down with
    | none => simp [hraw] at hsome
    | some value =>
        have hraw : (rawRows t ha A hA
            (.image X.ctx Y.ctx
              (rawRows t ha A hA (.coordinate X.ctx)).down
              (rawRows t ha A hA (.coordinate Y.ctx)).down
              ⟨(coefficientNative t hf).1, (0 : (coefficientNative t hf).1)⟩ c)).down =
            some value := by
          simpa [IndependentRawCandidate.coord, rawRows, coefficientReference,
            IndependentRawCandidate.coefficientRef] using hraw
        simp [variableImage, IndependentRawLocal.variableImage,
          IndependentRawLocal.coord, localRows,
          IndependentRawCandidate.lower, IndependentRawCandidate.coord,
          rawRows,
          IndependentRawCandidate.coefficientRef, hraw,
          IndependentPolynomialExpressions.sparseEquiv]
        change value = expected ↔ value = expected
        rfl

/-- Closed object formula fixing one raw relation-polynomial cell to an expected value. -/
noncomputable def relationPolynomialValueFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (X : (rawSite t ha A hA hf hc he hv ho).category)
    (i : IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx)
    (expected : @MvPolynomial
      (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
      (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) :
    ObjectFormula.{u, v, max u v} U := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact rawAnchor t ha A hA (.coordinate X.ctx)
    (rawAnchor t ha A hA (.relation X.ctx)
      (coefficientRefAnchor t hf
        (.cell (.atObject A (.raw (.polynomial X.ctx
          (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
          (IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx)
          (coefficientReference t hf) i)))
          (some (ULift.up (some
            (IndependentPolynomialExpressions.sparseEquiv expected)))))))

/-- An exact raw polynomial cell recovers the selected native relation polynomial. -/
@[simp] theorem relationPolynomialValueFormula_evaluate
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
    (i : IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx)
    (expected : @MvPolynomial
      (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
      (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) :
    (relationPolynomialValueFormula t ha A hA hf hc he hv ho X i expected).evaluate t ↔
      relationPolynomial t ha A hA hf hc he hv ho ht X i = expected := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  simp only [relationPolynomialValueFormula, rawAnchor_evaluate,
    coefficientRefAnchor_evaluate, ObjectFormula.evaluate]
  refine Iff.trans (b := (rawRows t ha A hA
      (.polynomial X.ctx
        (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx)
        (coefficientReference t hf) i)).down =
      some (IndependentPolynomialExpressions.sparseEquiv expected)) ?_ ?_
  · rw [← IndependentGeometryPrimitive.some_dependent t ha A hA
      (.raw (.polynomial X.ctx
        (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx)
        (coefficientReference t hf) i))]
    constructor
    · intro h
      exact congrArg ULift.down (Option.some.inj h)
    · intro h
      congr 2
      exact ULift.ext _ _ h
  · change (rawRows t ha A hA
      (.polynomial X.ctx
        (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx)
        (coefficientReference t hf) i)).down =
      some (IndependentPolynomialExpressions.sparseEquiv expected) ↔ _
    have hsome : (rawRows t ha A hA
        (.polynomial X.ctx
          (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
          (IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx)
          (coefficientReference t hf) i)).down.isSome := by
      exact (ht.polynomial X.ctx
        (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx)
        (coefficientReference t hf) i).2 ⟨rfl, rfl, rfl⟩
    cases hraw : (rawRows t ha A hA
        (.polynomial X.ctx
          (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
          (IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx)
          (coefficientReference t hf) i)).down with
    | none => simp [hraw] at hsome
    | some value =>
        have hraw : (rawRows t ha A hA
            (.polynomial X.ctx
              (rawRows t ha A hA (.coordinate X.ctx)).down
              (rawRows t ha A hA (.relation X.ctx)).down
              ⟨(coefficientNative t hf).1, (0 : (coefficientNative t hf).1)⟩ i)).down =
            some value := by
          simpa [IndependentRawCandidate.coord, IndependentRawCandidate.rel,
            rawRows, coefficientReference, IndependentRawCandidate.coefficientRef] using hraw
        simp [relationPolynomial, IndependentRawLocal.relations,
          IndependentRawLocal.coord, IndependentRawLocal.rel,
          localRows, IndependentRawCandidate.lower,
          IndependentRawCandidate.coord, rawRows,
          IndependentRawCandidate.coefficientRef, hraw,
          IndependentPolynomialExpressions.sparseEquiv]
        change value = expected ↔ value = expected
        rfl

/-- A candidate table for the finitely many coefficient operations used by a formula. -/
abbrev coefficientTrace
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t) :=
  IndependentRingPrimitive.Table (coefficientNative t hf).1

/-- Right-associated sum read from a candidate coefficient-operation table. -/
def coefficientTraceSum
    (trace : coefficientTrace t hf) : List (coefficientNative t hf).1 →
      (coefficientNative t hf).1
  | [] => trace .zero
  | value :: values => trace (.add value (coefficientTraceSum trace values))

/-- Finite formula checking every addition used by a right-associated coefficient sum. -/
def coefficientSumFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (trace : coefficientTrace t hf) :
    List (coefficientNative t hf).1 → (coefficientNative t hf).1 →
      ObjectFormula.{u, v, max u v} U
  | [], expected => coefficientValueFormula t hf .zero expected
  | value :: values, expected =>
      .and (coefficientSumFormula t hf trace values
        (coefficientTraceSum trace values))
        (coefficientValueFormula t hf
          (.add value (coefficientTraceSum trace values)) expected)

/-- A validated coefficient-sum trace has the native list sum as its result. -/
theorem coefficientSumFormula_sound
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (trace : coefficientTrace t hf)
    (values : List (coefficientNative t hf).1)
    (expected : (coefficientNative t hf).1) :
    letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
    (coefficientSumFormula t hf trace values expected).evaluate t →
      values.sum = expected := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  induction values generalizing expected with
  | nil =>
      intro h
      simpa [coefficientSumFormula, coefficientValueFormula_evaluate,
        IndependentRingPrimitive.read] using h
  | cons value values ih =>
      intro h
      have hsum := ih (coefficientTraceSum trace values) h.1
      have hvalue := (coefficientValueFormula_evaluate t hf _ _).1 h.2
      change value + coefficientTraceSum trace values = expected at hvalue
      rw [← hsum] at hvalue
      exact hvalue

/-- The native coefficient table computes the ordinary right-associated sum. -/
@[simp] theorem coefficientTraceSum_native
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (values : List (coefficientNative t hf).1) :
    letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
    coefficientTraceSum (IndependentRingPrimitive.read (coefficientNative t hf).2) values =
      values.sum := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  induction values with
  | nil => rfl
  | cons value values ih =>
      simp [coefficientTraceSum, IndependentRingPrimitive.read, ih]

/-- The native coefficient table satisfies the finite sum formula. -/
theorem coefficientSumFormula_native
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (values : List (coefficientNative t hf).1) :
    letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
    (coefficientSumFormula t hf
      (IndependentRingPrimitive.read (coefficientNative t hf).2)
      values values.sum).evaluate t := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  induction values with
  | nil =>
      simp [coefficientSumFormula, coefficientValueFormula_evaluate,
        IndependentRingPrimitive.read]
  | cons value values ih =>
      simp only [coefficientSumFormula, ObjectFormula.evaluate,
        coefficientTraceSum_native]
      refine ⟨?_, (coefficientValueFormula_evaluate t hf _ _).2 rfl⟩
      simpa using ih

/-- Finite monomial support sufficient to compare two inputs with one output. -/
noncomputable def polynomialSupport3
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t) {C : Type u}
    (p q r : @MvPolynomial C (coefficientNative t hf).1
      (coefficientNative t hf).2.toCommSemiring) : Finset (C →₀ ℕ) := by
  classical
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact p.support ∪ q.support ∪ r.support

/-- Finite coefficient-cell formula asserting one polynomial addition. -/
noncomputable def polynomialAddFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t) {C : Type u}
    (p q r : @MvPolynomial C (coefficientNative t hf).1
      (coefficientNative t hf).2.toCommSemiring) :
    ObjectFormula.{u, v, max u v} U := by
  classical
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact ObjectFormula.allList (polynomialSupport3 t hf p q r).toList (fun m =>
    coefficientValueFormula t hf (.add (p.coeff m) (q.coeff m)) (r.coeff m))

/-- The polynomial addition formula is equivalent to native addition. -/
@[simp] theorem polynomialAddFormula_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t) {C : Type u}
    (p q r : @MvPolynomial C (coefficientNative t hf).1
      (coefficientNative t hf).2.toCommSemiring) :
    letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
    (polynomialAddFormula t hf p q r).evaluate t ↔ p + q = r := by
  classical
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  constructor
  · intro h
    rw [polynomialAddFormula, ObjectFormula.evaluate_allList] at h
    apply MvPolynomial.ext
    intro m
    by_cases hm : m ∈ polynomialSupport3 t hf p q r
    · have hcell := h m (by simpa using hm)
      rw [coefficientValueFormula_evaluate] at hcell
      simpa [IndependentRingPrimitive.read] using hcell
    · have hpnot : m ∉ p.support := fun hmp => hm (by
          simp [polynomialSupport3, hmp])
      have hqnot : m ∉ q.support := fun hmq => hm (by
          simp [polynomialSupport3, hmq])
      have hrnot : m ∉ r.support := fun hmr => hm (by
          simp [polynomialSupport3, hmr])
      have hp : p.coeff m = 0 := by
        simpa [MvPolynomial.mem_support_iff] using hpnot
      have hq : q.coeff m = 0 := by
        simpa [MvPolynomial.mem_support_iff] using hqnot
      have hr : r.coeff m = 0 := by
        simpa [MvPolynomial.mem_support_iff] using hrnot
      simp [hp, hq, hr]
  · intro h
    rw [polynomialAddFormula, ObjectFormula.evaluate_allList]
    intro m hm
    rw [coefficientValueFormula_evaluate]
    change p.coeff m + q.coeff m = r.coeff m
    simpa using congrArg (fun value => value.coeff m) h

/-- Finite coefficient-cell formula asserting that a polynomial is zero. -/
noncomputable def polynomialZeroFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t) {C : Type u}
    (r : @MvPolynomial C (coefficientNative t hf).1
      (coefficientNative t hf).2.toCommSemiring) :
    ObjectFormula.{u, v, max u v} U := by
  classical
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact ObjectFormula.allList (insert 0 r.support).toList (fun m =>
    coefficientValueFormula t hf .zero (r.coeff m))

/-- The zero formula is equivalent to equality with the native zero polynomial. -/
@[simp] theorem polynomialZeroFormula_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t) {C : Type u}
    (r : @MvPolynomial C (coefficientNative t hf).1
      (coefficientNative t hf).2.toCommSemiring) :
    letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
    (polynomialZeroFormula t hf r).evaluate t ↔ (0 : MvPolynomial C _) = r := by
  classical
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  constructor
  · intro h
    rw [polynomialZeroFormula, ObjectFormula.evaluate_allList] at h
    apply MvPolynomial.ext
    intro m
    by_cases hm : m ∈ insert 0 r.support
    · have hcell := h m (by simpa using hm)
      rw [coefficientValueFormula_evaluate] at hcell
      simpa [IndependentRingPrimitive.read] using hcell
    · have hrnot : m ∉ r.support := fun hmr => hm (by simp [hmr])
      have hr : r.coeff m = 0 := by
        simpa [MvPolynomial.mem_support_iff] using hrnot
      simp [hr]
  · intro h
    rw [polynomialZeroFormula, ObjectFormula.evaluate_allList]
    intro m hm
    rw [coefficientValueFormula_evaluate]
    change 0 = r.coeff m
    simpa using congrArg (fun value => value.coeff m) h

/-- Finite coefficient-cell formula asserting that a polynomial is one. -/
noncomputable def polynomialOneFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t) {C : Type u}
    (r : @MvPolynomial C (coefficientNative t hf).1
      (coefficientNative t hf).2.toCommSemiring) :
    ObjectFormula.{u, v, max u v} U := by
  classical
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact ObjectFormula.allList (insert 0 r.support).toList (fun m =>
    if m = 0 then coefficientValueFormula t hf .one (r.coeff m)
    else coefficientValueFormula t hf .zero (r.coeff m))

/-- The one formula is equivalent to equality with the native unit polynomial. -/
@[simp] theorem polynomialOneFormula_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t) {C : Type u}
    (r : @MvPolynomial C (coefficientNative t hf).1
      (coefficientNative t hf).2.toCommSemiring) :
    letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
    (polynomialOneFormula t hf r).evaluate t ↔ (1 : MvPolynomial C _) = r := by
  classical
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  constructor
  · intro h
    rw [polynomialOneFormula, ObjectFormula.evaluate_allList] at h
    apply MvPolynomial.ext
    intro m
    by_cases hm0 : m = 0
    · subst m
      have hcell := h 0 (by simp)
      simp only [if_pos, coefficientValueFormula_evaluate] at hcell
      simpa [IndependentRingPrimitive.read] using hcell
    · by_cases hm : m ∈ r.support
      · have hcell := h m (by simp [hm])
        simp only [if_neg hm0, coefficientValueFormula_evaluate] at hcell
        simpa [IndependentRingPrimitive.read, MvPolynomial.coeff_one,
          hm0, Ne.symm hm0] using hcell
      · have hr : r.coeff m = 0 := by
          simpa [MvPolynomial.mem_support_iff] using hm
        simp [MvPolynomial.coeff_one, Ne.symm hm0, hr]
  · intro h
    rw [polynomialOneFormula, ObjectFormula.evaluate_allList]
    intro m hm
    by_cases hm0 : m = 0
    · subst m
      simp only [if_pos, coefficientValueFormula_evaluate]
      change 1 = r.coeff 0
      simpa using congrArg (fun value => value.coeff 0) h
    · simp only [if_neg hm0, coefficientValueFormula_evaluate]
      change 0 = r.coeff m
      simpa [MvPolynomial.coeff_one, hm0, Ne.symm hm0] using
        congrArg (fun value => value.coeff m) h

/-- Finite coefficient-cell formula asserting a constant polynomial value. -/
noncomputable def polynomialCoefficientFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t) {C : Type u}
    (a : (coefficientNative t hf).1)
    (r : @MvPolynomial C (coefficientNative t hf).1
      (coefficientNative t hf).2.toCommSemiring) :
    ObjectFormula.{u, v, max u v} U := by
  classical
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact ObjectFormula.allList (insert 0 r.support).toList (fun m =>
    if m = 0 then coefficientValueFormula t hf (.add a 0) (r.coeff m)
    else coefficientValueFormula t hf .zero (r.coeff m))

/-- The constant formula is equivalent to equality with `MvPolynomial.C`. -/
@[simp] theorem polynomialCoefficientFormula_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t) {C : Type u}
    (a : (coefficientNative t hf).1)
    (r : @MvPolynomial C (coefficientNative t hf).1
      (coefficientNative t hf).2.toCommSemiring) :
    letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
    (polynomialCoefficientFormula t hf a r).evaluate t ↔ MvPolynomial.C a = r := by
  classical
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  constructor
  · intro h
    rw [polynomialCoefficientFormula, ObjectFormula.evaluate_allList] at h
    apply MvPolynomial.ext
    intro m
    by_cases hm0 : m = 0
    · subst m
      have hcell := h 0 (by simp)
      simp only [if_pos, coefficientValueFormula_evaluate] at hcell
      simpa [IndependentRingPrimitive.read] using hcell
    · by_cases hm : m ∈ r.support
      · have hcell := h m (by simp [hm])
        simp only [if_neg hm0, coefficientValueFormula_evaluate] at hcell
        simpa [IndependentRingPrimitive.read, hm0, Ne.symm hm0] using hcell
      · have hr : r.coeff m = 0 := by
          simpa [MvPolynomial.mem_support_iff] using hm
        simp [Ne.symm hm0, hr]
  · intro h
    rw [polynomialCoefficientFormula, ObjectFormula.evaluate_allList]
    intro m hm
    by_cases hm0 : m = 0
    · subst m
      simp only [if_pos, coefficientValueFormula_evaluate]
      change a + 0 = r.coeff 0
      simpa using congrArg (fun value => value.coeff 0) h
    · simp only [if_neg hm0, coefficientValueFormula_evaluate]
      change 0 = r.coeff m
      simpa [hm0, Ne.symm hm0] using congrArg (fun value => value.coeff m) h

/-- Products indexed by the finite antidiagonal of one output monomial. -/
noncomputable def polynomialProductValues
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (trace : coefficientTrace t hf) {C : Type u}
    (p q : @MvPolynomial C (coefficientNative t hf).1
      (coefficientNative t hf).2.toCommSemiring) (m : C →₀ ℕ) :
    List (coefficientNative t hf).1 := by
  classical
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact (Finset.antidiagonal m).toList.map (fun pair =>
    trace (.mul (p.coeff pair.1) (q.coeff pair.2)))

/-- Finite trace formula for one coefficient of a polynomial product. -/
noncomputable def polynomialMulCoefficientFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (trace : coefficientTrace t hf) {C : Type u}
    (p q : @MvPolynomial C (coefficientNative t hf).1
      (coefficientNative t hf).2.toCommSemiring) (m : C →₀ ℕ)
    (expected : (coefficientNative t hf).1) :
    ObjectFormula.{u, v, max u v} U := by
  classical
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact .and
    (ObjectFormula.allList (Finset.antidiagonal m).toList (fun pair =>
      coefficientValueFormula t hf (.mul (p.coeff pair.1) (q.coeff pair.2))
        (trace (.mul (p.coeff pair.1) (q.coeff pair.2)))))
    (coefficientSumFormula t hf trace (polynomialProductValues t hf trace p q m)
      expected)

/-- A validated product trace computes the native coefficient of the product. -/
theorem polynomialMulCoefficientFormula_sound
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (trace : coefficientTrace t hf) {C : Type u}
    (p q : @MvPolynomial C (coefficientNative t hf).1
      (coefficientNative t hf).2.toCommSemiring) (m : C →₀ ℕ)
    (expected : (coefficientNative t hf).1) :
    letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
    (polynomialMulCoefficientFormula t hf trace p q m expected).evaluate t →
      (p * q).coeff m = expected := by
  classical
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  intro h
  have hpairs := (ObjectFormula.evaluate_allList t _ _).1 h.1
  have hsum := coefficientSumFormula_sound t hf trace
    (polynomialProductValues t hf trace p q m) expected h.2
  have hmap :
      (Finset.antidiagonal m).toList.map (fun pair =>
        p.coeff pair.1 * q.coeff pair.2) =
      polynomialProductValues t hf trace p q m := by
    rw [polynomialProductValues]
    apply List.map_congr_left
    intro pair hpair
    have hcell := hpairs pair hpair
    rw [coefficientValueFormula_evaluate] at hcell
    exact hcell
  rw [MvPolynomial.coeff_mul, ← Finset.sum_map_toList]
  rw [hmap]
  exact hsum

/-- The native coefficient table satisfies every product-coefficient formula. -/
theorem polynomialMulCoefficientFormula_native
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t) {C : Type u}
    (p q : @MvPolynomial C (coefficientNative t hf).1
      (coefficientNative t hf).2.toCommSemiring) (m : C →₀ ℕ) :
    letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
    (polynomialMulCoefficientFormula t hf
      (IndependentRingPrimitive.read (coefficientNative t hf).2)
      p q m ((p * q).coeff m)).evaluate t := by
  classical
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  rw [polynomialMulCoefficientFormula, ObjectFormula.evaluate]
  constructor
  · rw [ObjectFormula.evaluate_allList]
    intro pair hpair
    rw [coefficientValueFormula_evaluate]
  · have hsum := coefficientSumFormula_native t hf
      (polynomialProductValues t hf
        (IndependentRingPrimitive.read (coefficientNative t hf).2) p q m)
    have hvalues :
        (polynomialProductValues t hf
          (IndependentRingPrimitive.read (coefficientNative t hf).2) p q m).sum =
        (p * q).coeff m := by
      rw [polynomialProductValues, MvPolynomial.coeff_mul,
        ← Finset.sum_map_toList]
      rfl
    rwa [hvalues] at hsum

/-- Finite coefficient-cell formula asserting one polynomial multiplication. -/
noncomputable def polynomialMulFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (trace : coefficientTrace t hf) {C : Type u}
    (p q r : @MvPolynomial C (coefficientNative t hf).1
      (coefficientNative t hf).2.toCommSemiring) :
    ObjectFormula.{u, v, max u v} U := by
  classical
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact ObjectFormula.allList (insert 0 ((p * q).support ∪ r.support)).toList (fun m =>
    polynomialMulCoefficientFormula t hf trace p q m (r.coeff m))

/-- The multiplication formula implies native polynomial multiplication. -/
theorem polynomialMulFormula_sound
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (trace : coefficientTrace t hf) {C : Type u}
    (p q r : @MvPolynomial C (coefficientNative t hf).1
      (coefficientNative t hf).2.toCommSemiring) :
    letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
    (polynomialMulFormula t hf trace p q r).evaluate t → p * q = r := by
  classical
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  intro h
  rw [polynomialMulFormula, ObjectFormula.evaluate_allList] at h
  apply MvPolynomial.ext
  intro m
  by_cases hm : m ∈ insert 0 ((p * q).support ∪ r.support)
  · exact polynomialMulCoefficientFormula_sound t hf trace p q m (r.coeff m)
      (h m (by simpa using hm))
  · have hpqnot : m ∉ (p * q).support := fun hmpq => hm (by simp [hmpq])
    have hrnot : m ∉ r.support := fun hmr => hm (by simp [hmr])
    have hpq : (p * q).coeff m = 0 := by
      simpa [MvPolynomial.mem_support_iff] using hpqnot
    have hr : r.coeff m = 0 := by
      simpa [MvPolynomial.mem_support_iff] using hrnot
    rw [hpq, hr]

/-- The native coefficient table satisfies the polynomial multiplication formula. -/
theorem polynomialMulFormula_native
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t) {C : Type u}
    (p q : @MvPolynomial C (coefficientNative t hf).1
      (coefficientNative t hf).2.toCommSemiring) :
    letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
    (polynomialMulFormula t hf
      (IndependentRingPrimitive.read (coefficientNative t hf).2)
      p q (p * q)).evaluate t := by
  classical
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  rw [polynomialMulFormula, ObjectFormula.evaluate_allList]
  intro m hm
  exact polynomialMulCoefficientFormula_native t hf p q m

/-- Translate one query of a comparison polynomial table into an object formula.
Variable queries read raw image cells; arithmetic queries read coefficient cells. -/
noncomputable def substitutionQueryFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    {X Y : (rawSite t ha A hA hf hc he hv ho).category}
    (trace : coefficientTrace t hf)
    (comparison : IndependentPolynomialExpressions.Table
      (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
      (coefficientNative t hf).1
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)) :
    IndependentPolynomialExpressions.Query
      (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
      (coefficientNative t hf).1
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) →
      ObjectFormula.{u, v, max u v} U
  | .coefficient a => polynomialCoefficientFormula t hf a (comparison (.coefficient a))
  | .variable c =>
      variableImageValueFormula t ha A hA hf hc he hv ho c (comparison (.variable c))
  | .zero => polynomialZeroFormula t hf (comparison .zero)
  | .one => polynomialOneFormula t hf (comparison .one)
  | .add p q => polynomialAddFormula t hf p q (comparison (.add p q))
  | .mul p q => polynomialMulFormula t hf trace p q (comparison (.mul p q))

/-- Every translated substitution query equates the native and comparison tables. -/
theorem substitutionQueryFormula_sound
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
    (trace : coefficientTrace t hf)
    (comparison : IndependentPolynomialExpressions.Table
      (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
      (coefficientNative t hf).1
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring))
    (q : IndependentPolynomialExpressions.Query
      (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
      (coefficientNative t hf).1
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)) :
    letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
    (substitutionQueryFormula t ha A hA hf hc he hv ho trace comparison q).evaluate t →
      substitutionTable t ha A hA hf hc he hv ho ht f q = comparison q := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  intro h
  cases q with
  | coefficient a =>
      exact (polynomialCoefficientFormula_evaluate t hf a _).1 h
  | «variable» c =>
      exact (variableImageValueFormula_evaluate t ha A hA hf hc he hv ho ht f c _).1 h
  | zero =>
      exact (polynomialZeroFormula_evaluate t hf _).1 h
  | one =>
      exact (polynomialOneFormula_evaluate t hf _).1 h
  | add p q =>
      exact (polynomialAddFormula_evaluate t hf p q _).1 h
  | mul p q =>
      exact polynomialMulFormula_sound t hf trace p q _ h

/-- Each substitution query is satisfied by the native polynomial table and ring trace. -/
theorem substitutionQueryFormula_native
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
    (q : IndependentPolynomialExpressions.Query
      (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
      (coefficientNative t hf).1
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)) :
    letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
    (substitutionQueryFormula t ha A hA hf hc he hv ho
      (IndependentRingPrimitive.read (coefficientNative t hf).2)
      (substitutionTable t ha A hA hf hc he hv ho ht f) q).evaluate t := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  cases q with
  | coefficient a => exact (polynomialCoefficientFormula_evaluate t hf a _).2 rfl
  | «variable» c =>
      exact (variableImageValueFormula_evaluate t ha A hA hf hc he hv ho ht f c _).2 rfl
  | zero => exact (polynomialZeroFormula_evaluate t hf _).2 rfl
  | one => exact (polynomialOneFormula_evaluate t hf _).2 rfl
  | add p q => exact (polynomialAddFormula_evaluate t hf p q _).2 rfl
  | mul p q => exact polynomialMulFormula_native t hf p q

/-- Finite object formula comparing the native substitution table with a separate
comparison table on the support of the compiled polynomial. -/
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
      (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)
    (trace : coefficientTrace t hf)
    (comparison : IndependentPolynomialExpressions.Table
      (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
      (coefficientNative t hf).1
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)) :
    ObjectFormula.{u, v, max u v} U := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact ObjectFormula.allList
    (IndependentPolynomialExpressions.support
      (substitutionTable t ha A hA hf hc he hv ho ht f)
      (IndependentPolynomialExpressions.compile p)).toList
    (substitutionQueryFormula t ha A hA hf hc he hv ho trace comparison)

/-- The substitution object formula gives pointwise table agreement on expression support. -/
theorem substitutionObjectFormula_sound
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
    (trace : coefficientTrace t hf)
    (comparison : IndependentPolynomialExpressions.Table
      (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
      (coefficientNative t hf).1
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring))
    (h : (substitutionObjectFormula t ha A hA hf hc he hv ho ht f p
      trace comparison).evaluate t) :
    letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
    ∀ q ∈ IndependentPolynomialExpressions.support
      (substitutionTable t ha A hA hf hc he hv ho ht f)
      (IndependentPolynomialExpressions.compile p),
      substitutionTable t ha A hA hf hc he hv ho ht f q = comparison q := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  rw [substitutionObjectFormula, ObjectFormula.evaluate_allList] at h
  intro q hq
  exact substitutionQueryFormula_sound t ha A hA hf hc he hv ho ht f trace comparison q
    (h q (by simpa using hq))

/-- The native substitution table satisfies its object-side support formula. -/
theorem substitutionObjectFormula_native
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
    (substitutionObjectFormula t ha A hA hf hc he hv ho ht f p
      (IndependentRingPrimitive.read (coefficientNative t hf).2)
      (substitutionTable t ha A hA hf hc he hv ho ht f)).evaluate t := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  rw [substitutionObjectFormula, ObjectFormula.evaluate_allList]
  intro q hq
  exact substitutionQueryFormula_native t ha A hA hf hc he hv ho ht f q

/-- Root-cell formula fixing the result of the compiled substitution expression. -/
noncomputable def substitutionRootFormula
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
  exact IndependentPolynomialExpressions.CellFormula.cell
    (IndependentPolynomialExpressions.rootQuery
      (substitutionTable t ha A hA hf hc he hv ho ht f)
      (IndependentPolynomialExpressions.compile p)) expected

/-- Object-side support agreement and a comparison-table root cell recover the
native substitution result. -/
theorem substitutionBridge_sound
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
      (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)
    (trace : coefficientTrace t hf)
    (comparison : IndependentPolynomialExpressions.Table
      (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
      (coefficientNative t hf).1
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring))
    (hobject : (substitutionObjectFormula t ha A hA hf hc he hv ho ht f p
      trace comparison).evaluate t)
    (hroot : (substitutionRootFormula t ha A hA hf hc he hv ho ht f p expected).evaluate
      comparison) :
    substitutionValue t ha A hA hf hc he hv ho ht f p = expected := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  let canonical := substitutionTable t ha A hA hf hc he hv ho ht f
  let expression := IndependentPolynomialExpressions.compile p
  have hagree : ∀ q ∈ IndependentPolynomialExpressions.support canonical expression,
      canonical q = comparison q :=
    substitutionObjectFormula_sound t ha A hA hf hc he hv ho ht f p
      trace comparison hobject
  have hformula :
      (IndependentPolynomialExpressions.expressionFormula canonical expression expected).evaluate
        comparison := by
    constructor
    · rw [IndependentPolynomialExpressions.CellFormula.evaluate_allList]
      intro q hq
      exact (hagree q (by simpa using hq)).symm
    · exact hroot
  have hcomparison :=
    IndependentPolynomialExpressions.evaluate_eq_expected_of_expressionFormula
      canonical comparison expression expected hformula
  have hevaluate := IndependentPolynomialExpressions.evaluate_eq_of_support
    canonical comparison expression hagree
  exact hevaluate.trans hcomparison

/-- A native substitution equality supplies the corresponding root-cell formula. -/
theorem substitutionRootFormula_native
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
      (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)
    (h : substitutionValue t ha A hA hf hc he hv ho ht f p = expected) :
    (substitutionRootFormula t ha A hA hf hc he hv ho ht f p expected).evaluate
      (substitutionTable t ha A hA hf hc he hv ho ht f) := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  change substitutionTable t ha A hA hf hc he hv ho ht f
      (IndependentPolynomialExpressions.rootQuery
        (substitutionTable t ha A hA hf hc he hv ho ht f)
        (IndependentPolynomialExpressions.compile p)) = expected
  exact (IndependentPolynomialExpressions.evaluate_eq_rootQuery
    (substitutionTable t ha A hA hf hc he hv ho ht f)
    (IndependentPolynomialExpressions.compile p)).symm.trans h

/-- Arithmetic formula copying one polynomial value through addition with zero. -/
noncomputable def polynomialIdentityFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t) {C : Type u}
    (p r : @MvPolynomial C (coefficientNative t hf).1
      (coefficientNative t hf).2.toCommSemiring) :
    ObjectFormula.{u, v, max u v} U := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact polynomialAddFormula t hf p 0 r

/-- The polynomial identity formula is equivalent to equality of its polynomials. -/
@[simp] theorem polynomialIdentityFormula_evaluate
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (hf : IndependentGeometryPrimitive.FoundationLaws t) {C : Type u}
    (p r : @MvPolynomial C (coefficientNative t hf).1
      (coefficientNative t hf).2.toCommSemiring) :
    letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
    (polynomialIdentityFormula t hf p r).evaluate t ↔ p = r := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  simp [polynomialIdentityFormula]

/-- Finite expression for a relation witness, with relation rows represented as variables. -/
noncomputable def witnessExpression
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (X : (rawSite t ha A hA hf hc he hv ho).category)
    (w : IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx →₀
      @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) :
    IndependentPolynomialExpressions.Expr
      (IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx)
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) :=
  IndependentPolynomialExpressions.Expr.sum
    (w.support.toList.map (fun i =>
      .mul (.coefficient (w i)) (.variable i)))

/-- Native polynomial table whose variables are the selected raw relation polynomials. -/
abbrev witnessTable
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (ht : CandidateTyped t ha A hA hf hc he hv ho)
    (X : (rawSite t ha A hA hf hc he hv ho).category) := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  let R := MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
    (coefficientNative t hf).1
  exact IndependentPolynomialExpressions.nativeTable (RingHom.id R)
    (relationPolynomial t ha A hA hf hc he hv ho ht X)

/-- Value of the finite witness expression in the native relation table. -/
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
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact IndependentPolynomialExpressions.evaluate
    (witnessTable t ha A hA hf hc he hv ho ht X)
    (witnessExpression t ha A hA hf hc he hv ho X w)

/-- The native witness expression evaluates to the expected finite relation sum. -/
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

/-- Translate one witness comparison-table query into exact object and coefficient cells. -/
noncomputable def witnessQueryFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (X : (rawSite t ha A hA hf hc he hv ho).category)
    (trace : coefficientTrace t hf)
    (comparison : IndependentPolynomialExpressions.Table
      (IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx)
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)) :
    IndependentPolynomialExpressions.Query
      (IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx)
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) →
      ObjectFormula.{u, v, max u v} U
  | .coefficient p => polynomialIdentityFormula t hf p (comparison (.coefficient p))
  | .variable i => relationPolynomialValueFormula t ha A hA hf hc he hv ho X i
      (comparison (.variable i))
  | .zero => polynomialZeroFormula t hf (comparison .zero)
  | .one => polynomialOneFormula t hf (comparison .one)
  | .add p q => polynomialAddFormula t hf p q (comparison (.add p q))
  | .mul p q => polynomialMulFormula t hf trace p q (comparison (.mul p q))

/-- Every translated witness query equates the native and comparison tables. -/
theorem witnessQueryFormula_sound
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
    (trace : coefficientTrace t hf)
    (comparison : IndependentPolynomialExpressions.Table
      (IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx)
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring))
    (q : IndependentPolynomialExpressions.Query
      (IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx)
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)) :
    letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
    (witnessQueryFormula t ha A hA hf hc he hv ho X trace comparison q).evaluate t →
      witnessTable t ha A hA hf hc he hv ho ht X q = comparison q := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  intro h
  cases q with
  | coefficient p => exact (polynomialIdentityFormula_evaluate t hf p _).1 h
  | «variable» i =>
      exact (relationPolynomialValueFormula_evaluate t ha A hA hf hc he hv ho ht X i _).1 h
  | zero => exact (polynomialZeroFormula_evaluate t hf _).1 h
  | one => exact (polynomialOneFormula_evaluate t hf _).1 h
  | add p q => exact (polynomialAddFormula_evaluate t hf p q _).1 h
  | mul p q => exact polynomialMulFormula_sound t hf trace p q _ h

/-- Each witness query is satisfied by the native relation table and ring trace. -/
theorem witnessQueryFormula_native
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
    (q : IndependentPolynomialExpressions.Query
      (IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx)
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)) :
    letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
    (witnessQueryFormula t ha A hA hf hc he hv ho X
      (IndependentRingPrimitive.read (coefficientNative t hf).2)
      (witnessTable t ha A hA hf hc he hv ho ht X) q).evaluate t := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  cases q with
  | coefficient p => exact (polynomialIdentityFormula_evaluate t hf p _).2 rfl
  | «variable» i =>
      exact (relationPolynomialValueFormula_evaluate t ha A hA hf hc he hv ho ht X i _).2 rfl
  | zero => exact (polynomialZeroFormula_evaluate t hf _).2 rfl
  | one => exact (polynomialOneFormula_evaluate t hf _).2 rfl
  | add p q => exact (polynomialAddFormula_evaluate t hf p q _).2 rfl
  | mul p q => exact polynomialMulFormula_native t hf p q

/-- Finite object formula comparing native relation evaluation with a separate
comparison table on the witness expression support. -/
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
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)
    (trace : coefficientTrace t hf)
    (comparison : IndependentPolynomialExpressions.Table
      (IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx)
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)) :
    ObjectFormula.{u, v, max u v} U := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact ObjectFormula.allList
    (IndependentPolynomialExpressions.support
      (witnessTable t ha A hA hf hc he hv ho ht X)
      (witnessExpression t ha A hA hf hc he hv ho X w)).toList
    (witnessQueryFormula t ha A hA hf hc he hv ho X trace comparison)

/-- The witness object formula gives pointwise table agreement on expression support. -/
theorem witnessObjectFormula_sound
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
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)
    (trace : coefficientTrace t hf)
    (comparison : IndependentPolynomialExpressions.Table
      (IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx)
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring))
    (h : (witnessObjectFormula t ha A hA hf hc he hv ho ht X w
      trace comparison).evaluate t) :
    letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
    ∀ q ∈ IndependentPolynomialExpressions.support
      (witnessTable t ha A hA hf hc he hv ho ht X)
      (witnessExpression t ha A hA hf hc he hv ho X w),
      witnessTable t ha A hA hf hc he hv ho ht X q = comparison q := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  rw [witnessObjectFormula, ObjectFormula.evaluate_allList] at h
  intro q hq
  exact witnessQueryFormula_sound t ha A hA hf hc he hv ho ht X trace comparison q
    (h q (by simpa using hq))

/-- The native witness table satisfies its object-side support formula. -/
theorem witnessObjectFormula_native
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
    (witnessObjectFormula t ha A hA hf hc he hv ho ht X w
      (IndependentRingPrimitive.read (coefficientNative t hf).2)
      (witnessTable t ha A hA hf hc he hv ho ht X)).evaluate t := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  rw [witnessObjectFormula, ObjectFormula.evaluate_allList]
  intro q hq
  exact witnessQueryFormula_native t ha A hA hf hc he hv ho ht X q

/-- Root-cell formula fixing the result of the finite witness expression. -/
noncomputable def witnessRootFormula
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
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)
    (expected : @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
      (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring) := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  exact IndependentPolynomialExpressions.CellFormula.cell
    (IndependentPolynomialExpressions.rootQuery
      (witnessTable t ha A hA hf hc he hv ho ht X)
      (witnessExpression t ha A hA hf hc he hv ho X w)) expected

/-- Object-side support agreement and a comparison-table root cell recover the
native witness value. -/
theorem witnessBridge_sound
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
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)
    (expected : @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
      (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)
    (trace : coefficientTrace t hf)
    (comparison : IndependentPolynomialExpressions.Table
      (IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx)
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)
      (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring))
    (hobject : (witnessObjectFormula t ha A hA hf hc he hv ho ht X w
      trace comparison).evaluate t)
    (hroot : (witnessRootFormula t ha A hA hf hc he hv ho ht X w expected).evaluate
      comparison) :
    witnessValue t ha A hA hf hc he hv ho ht X w = expected := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  let canonical := witnessTable t ha A hA hf hc he hv ho ht X
  let expression := witnessExpression t ha A hA hf hc he hv ho X w
  have hagree : ∀ q ∈ IndependentPolynomialExpressions.support canonical expression,
      canonical q = comparison q :=
    witnessObjectFormula_sound t ha A hA hf hc he hv ho ht X w trace comparison hobject
  have hformula :
      (IndependentPolynomialExpressions.expressionFormula canonical expression expected).evaluate
        comparison := by
    constructor
    · rw [IndependentPolynomialExpressions.CellFormula.evaluate_allList]
      intro q hq
      exact (hagree q (by simpa using hq)).symm
    · exact hroot
  have hcomparison :=
    IndependentPolynomialExpressions.evaluate_eq_expected_of_expressionFormula
      canonical comparison expression expected hformula
  have hevaluate := IndependentPolynomialExpressions.evaluate_eq_of_support
    canonical comparison expression hagree
  exact hevaluate.trans hcomparison

/-- A native witness equality supplies the corresponding root-cell formula. -/
theorem witnessRootFormula_native
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
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)
    (expected : @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
      (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)
    (h : witnessValue t ha A hA hf hc he hv ho ht X w = expected) :
    (witnessRootFormula t ha A hA hf hc he hv ho ht X w expected).evaluate
      (witnessTable t ha A hA hf hc he hv ho ht X) := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  change witnessTable t ha A hA hf hc he hv ho ht X
      (IndependentPolynomialExpressions.rootQuery
        (witnessTable t ha A hA hf hc he hv ho ht X)
        (witnessExpression t ha A hA hf hc he hv ho X w)) = expected
  exact (IndependentPolynomialExpressions.evaluate_eq_rootQuery
    (witnessTable t ha A hA hf hc he hv ho ht X)
    (witnessExpression t ha A hA hf hc he hv ho X w)).symm.trans h

/-- Finite raw-law instances carrying only exact source cells, arithmetic traces,
and separate comparison tables for generator, identity, and composition laws. -/
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
      ∃ p : @MvPolynomial
          (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
          (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring,
      ∃ result : @MvPolynomial
          (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
          (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring,
      ∃ substitutionTrace witnessTrace : coefficientTrace t hf,
      ∃ substitutionComparison : IndependentPolynomialExpressions.Table
          (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
          (coefficientNative t hf).1
          (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
            (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring),
      ∃ witnessComparison : IndependentPolynomialExpressions.Table
          (IndependentRawCandidate.rel (rawRows t ha A hA) X.ctx)
          (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
            (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring)
          (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
            (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring),
        (relationPolynomialValueFormula t ha A hA hf hc he hv ho Y r p).evaluate t ∧
        (substitutionObjectFormula t ha A hA hf hc he hv ho ht f p
          substitutionTrace substitutionComparison).evaluate t ∧
        (substitutionRootFormula t ha A hA hf hc he hv ho ht f p result).evaluate
          substitutionComparison ∧
        (witnessObjectFormula t ha A hA hf hc he hv ho ht X w
          witnessTrace witnessComparison).evaluate t ∧
        (witnessRootFormula t ha A hA hf hc he hv ho ht X w result).evaluate
          witnessComparison
  identity : ∀ (W : (rawSite t ha A hA hf hc he hv ho).category)
    (c : IndependentRawCandidate.coord (rawRows t ha A hA) W.ctx),
    ∃ trace : coefficientTrace t hf,
    ∃ comparison : IndependentPolynomialExpressions.Table
        (IndependentRawCandidate.coord (rawRows t ha A hA) W.ctx)
        (coefficientNative t hf).1
        (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) W.ctx)
          (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring),
      let p := @MvPolynomial.X (coefficientNative t hf).1 _
        (coefficientNative t hf).2.toCommSemiring c
      (substitutionObjectFormula t ha A hA hf hc he hv ho ht (𝟙 W) p
        trace comparison).evaluate t ∧
      (substitutionRootFormula t ha A hA hf hc he hv ho ht (𝟙 W) p p).evaluate comparison
  composition : ∀ {X Y Z : (rawSite t ha A hA hf hc he hv ho).category}
    (f : X ⟶ Y) (_g : Y ⟶ Z)
    (c : IndependentRawCandidate.coord (rawRows t ha A hA) Z.ctx),
    ∃ p : @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring,
    ∃ result : @MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
        (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring,
    ∃ trace : coefficientTrace t hf,
    ∃ comparison : IndependentPolynomialExpressions.Table
        (IndependentRawCandidate.coord (rawRows t ha A hA) Y.ctx)
        (coefficientNative t hf).1
        (@MvPolynomial (IndependentRawCandidate.coord (rawRows t ha A hA) X.ctx)
          (coefficientNative t hf).1 (coefficientNative t hf).2.toCommSemiring),
      (variableImageValueFormula t ha A hA hf hc he hv ho c p).evaluate t ∧
      (variableImageValueFormula t ha A hA hf hc he hv ho c result).evaluate t ∧
      (substitutionObjectFormula t ha A hA hf hc he hv ho ht f p
        trace comparison).evaluate t ∧
      (substitutionRootFormula t ha A hA hf hc he hv ho ht f p result).evaluate comparison

/-- Native raw lawfulness is equivalent to the finite provenance instances. -/
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
      let p := relationPolynomial t ha A hA hf hc he hv ho ht Y r
      let result := mappedPolynomial t ha A hA hf hc he hv ho ht f p
      let trace := IndependentRingPrimitive.read (coefficientNative t hf).2
      let substitutionComparison := substitutionTable t ha A hA hf hc he hv ho ht f
      let witnessComparison := witnessTable t ha A hA hf hc he hv ho ht X
      refine ⟨w, p, result, trace, trace, substitutionComparison, witnessComparison,
        (relationPolynomialValueFormula_evaluate t ha A hA hf hc he hv ho ht Y r p).2 rfl,
        substitutionObjectFormula_native t ha A hA hf hc he hv ho ht f p, ?_,
        witnessObjectFormula_native t ha A hA hf hc he hv ho ht X w, ?_⟩
      · apply substitutionRootFormula_native
        exact substitutionValue_eq_mappedPolynomial t ha A hA hf hc he hv ho ht f p
      · apply witnessRootFormula_native
        rw [witnessValue_eq_sum]
        exact hw
    · intro W c
      let p := @MvPolynomial.X (coefficientNative t hf).1 _
        (coefficientNative t hf).2.toCommSemiring c
      let trace := IndependentRingPrimitive.read (coefficientNative t hf).2
      let comparison := substitutionTable t ha A hA hf hc he hv ho ht (𝟙 W)
      refine ⟨trace, comparison,
        substitutionObjectFormula_native t ha A hA hf hc he hv ho ht (𝟙 W) p, ?_⟩
      apply substitutionRootFormula_native
      rw [substitutionValue_eq_mappedPolynomial]
      simpa [mappedPolynomial, IndependentRawLocal.restriction,
        TypedCoordinateRestriction.polynomialMap] using hl.identity W c
    · intro X Y Z f g c
      let p := variableImage t ha A hA hf hc he hv ho ht g c
      let result := variableImage t ha A hA hf hc he hv ho ht (f ≫ g) c
      let trace := IndependentRingPrimitive.read (coefficientNative t hf).2
      let comparison := substitutionTable t ha A hA hf hc he hv ho ht f
      refine ⟨p, result, trace, comparison,
        (variableImageValueFormula_evaluate t ha A hA hf hc he hv ho ht g c p).2 rfl,
        (variableImageValueFormula_evaluate t ha A hA hf hc he hv ho ht (f ≫ g) c result).2 rfl,
        substitutionObjectFormula_native t ha A hA hf hc he hv ho ht f p, ?_⟩
      apply substitutionRootFormula_native
      rw [substitutionValue_eq_mappedPolynomial]
      exact (hl.composition f g c).symm
  · intro hi
    refine { generator := ?_, identity := ?_, composition := ?_ }
    · intro X Y f r
      obtain ⟨w, p, result, substitutionTrace, witnessTrace,
        substitutionComparison, witnessComparison, hp, hsubObject, hsubRoot,
        hwitObject, hwitRoot⟩ := hi.generator f r
      have hp := (relationPolynomialValueFormula_evaluate
        t ha A hA hf hc he hv ho ht Y r p).1 hp
      have hsub := substitutionBridge_sound t ha A hA hf hc he hv ho ht f p result
        substitutionTrace substitutionComparison hsubObject hsubRoot
      have hwit := witnessBridge_sound t ha A hA hf hc he hv ho ht X w result
        witnessTrace witnessComparison hwitObject hwitRoot
      refine ⟨w, ?_⟩
      rw [witnessValue_eq_sum] at hwit
      rw [substitutionValue_eq_mappedPolynomial] at hsub
      calc
        w.sum (fun i a => a * relationPolynomial t ha A hA hf hc he hv ho ht X i) =
            result := hwit
        _ = mappedPolynomial t ha A hA hf hc he hv ho ht f p := hsub.symm
        _ = mappedPolynomial t ha A hA hf hc he hv ho ht f
            (relationPolynomial t ha A hA hf hc he hv ho ht Y r) :=
          congrArg (mappedPolynomial t ha A hA hf hc he hv ho ht f) hp.symm
    · intro W c
      obtain ⟨trace, comparison, hobject, hroot⟩ := hi.identity W c
      let p := @MvPolynomial.X (coefficientNative t hf).1 _
        (coefficientNative t hf).2.toCommSemiring c
      have hsub := substitutionBridge_sound t ha A hA hf hc he hv ho ht (𝟙 W) p p
        trace comparison hobject hroot
      rw [substitutionValue_eq_mappedPolynomial] at hsub
      dsimp [p] at hsub
      simpa [mappedPolynomial, IndependentRawLocal.restriction,
        TypedCoordinateRestriction.polynomialMap] using hsub
    · intro X Y Z f g c
      obtain ⟨p, result, trace, comparison, hp, hresult, hobject, hroot⟩ :=
        hi.composition f g c
      have hp := (variableImageValueFormula_evaluate
        t ha A hA hf hc he hv ho ht g c p).1 hp
      have hresult := (variableImageValueFormula_evaluate
        t ha A hA hf hc he hv ho ht (f ≫ g) c result).1 hresult
      have hsub := substitutionBridge_sound t ha A hA hf hc he hv ho ht f p result
        trace comparison hobject hroot
      rw [substitutionValue_eq_mappedPolynomial] at hsub
      calc
        variableImage t ha A hA hf hc he hv ho ht (f ≫ g) c = result := hresult
        _ = mappedPolynomial t ha A hA hf hc he hv ho ht f p := hsub.symm
        _ = mappedPolynomial t ha A hA hf hc he hv ho ht f
            (variableImage t ha A hA hf hc he hv ho ht g c) :=
          congrArg (mappedPolynomial t ha A hA hf hc he hv ho ht f) hp.symm


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
