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
    (W : ArchCtx A) (C : Type u) (c : C) : ObjectFormula.{u, v, 0} U :=
  rawAnchor t ha A hA (.coordinate W)
    (rawAnchor t ha A hA (.label W C c)
      (.equal (((rawRows t ha A hA (.label W C c)).down.isSome) = true)
        (C = IndependentRawCandidate.coord (rawRows t ha A hA) W)))

def localDataTypedFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (W : ArchCtx A) (C : Type u) (c : C) : ObjectFormula.{u, v, 0} U :=
  rawAnchor t ha A hA (.coordinate W)
    (rawAnchor t ha A hA (.localData W C c)
      (.equal (((rawRows t ha A hA (.localData W C c)).down.isSome) = true)
        (C = IndependentRawCandidate.coord (rawRows t ha A hA) W)))

def polynomialTypedFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (W : ArchCtx A) (C J : Type u) (r : IndependentRawCandidate.CoefficientRef.{v})
    (j : J) : ObjectFormula.{u, v, 0} U :=
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  rawAnchor t ha A hA (.coordinate W)
    (rawAnchor t ha A hA (.relation W)
      (coefficientRefAnchor t hf
        (rawAnchor t ha A hA (.polynomial W C J r j)
          (.equal (((rawRows t ha A hA (.polynomial W C J r j)).down.isSome) = true)
            (C = IndependentRawCandidate.coord (rawRows t ha A hA) W ∧
              J = IndependentRawCandidate.rel (rawRows t ha A hA) W ∧
              r = IndependentRawCandidate.coefficientRef (coefficientNative t hf).1)))))

def imageTypedFormula
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc)
    (W V : ArchCtx A) (C D : Type u) (r : IndependentRawCandidate.CoefficientRef.{v})
    (d : D) : ObjectFormula.{u, v, 0} U :=
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  contextAnchor t ha A hA (.le W V)
    (rawAnchor t ha A hA (.coordinate W)
      (rawAnchor t ha A hA (.coordinate V)
        (coefficientRefAnchor t hf
          (rawAnchor t ha A hA (.image W V C D r d)
            (.equal (((rawRows t ha A hA (.image W V C D r d)).down.isSome) = true)
              ((rawSite t ha A hA hf hc
                he hv ho).contextPreorder.le W V ∧
                C = IndependentRawCandidate.coord (rawRows t ha A hA) W ∧
                D = IndependentRawCandidate.coord (rawRows t ha A hA) V ∧
                r = IndependentRawCandidate.coefficientRef (coefficientNative t hf).1))))))

structure TypedInstances
    (t : IndependentGeometryPrimitive.Table.{u, v} U)
    (ha : IndependentGeometryPrimitive.IsActiveTyped t) (A : ArchitectureObject U)
    (hA : IndependentGeometryPrimitive.matching t (.object A) = true)
    (hf : IndependentGeometryPrimitive.FoundationLaws t)
    (hc : IndependentGeometryPrimitive.ContextLaws (rows t ha A hA))
    (he : IndependentGeometryPrimitive.EquationLaws (rows t ha A hA) hc)
    (hv : IndependentGeometryPrimitive.CoverageLaws t hf (rows t ha A hA) hc he)
    (ho : IndependentGeometryPrimitive.OverlapLaws (rows t ha A hA) hc) : Prop where
  label : ∀ W C c, (labelTypedFormula t ha A hA W C c).evaluate t
  localData : ∀ W C c, (localDataTypedFormula t ha A hA W C c).evaluate t
  polynomial : ∀ W C J r j,
    (polynomialTypedFormula t ha A hA hf W C J r j).evaluate t
  image : ∀ W V C D r d,
    (imageTypedFormula t ha A hA hf hc he hv ho W V C D r d).evaluate t

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
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro W C c
      simp only [labelTypedFormula, rawAnchor_evaluate, ObjectFormula.evaluate]
      exact propext (ht.label W C c)
    · intro W C c
      simp only [localDataTypedFormula, rawAnchor_evaluate, ObjectFormula.evaluate]
      exact propext (ht.localData W C c)
    · intro W C J r j
      simp only [polynomialTypedFormula, rawAnchor_evaluate,
        coefficientRefAnchor_evaluate, ObjectFormula.evaluate]
      exact propext (ht.polynomial W C J r j)
    · intro W V C D r d
      simp only [imageTypedFormula, contextAnchor_evaluate, rawAnchor_evaluate,
        coefficientRefAnchor_evaluate, ObjectFormula.evaluate]
      exact propext (ht.image W V C D r d)
  · intro hi
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro W C c
      have h := hi.label W C c
      simp only [labelTypedFormula, rawAnchor_evaluate, ObjectFormula.evaluate] at h
      exact eq_iff_iff.1 h
    · intro W C c
      have h := hi.localData W C c
      simp only [localDataTypedFormula, rawAnchor_evaluate, ObjectFormula.evaluate] at h
      exact eq_iff_iff.1 h
    · intro W C J r j
      have h := hi.polynomial W C J r j
      simp only [polynomialTypedFormula, rawAnchor_evaluate,
        coefficientRefAnchor_evaluate, ObjectFormula.evaluate] at h
      exact eq_iff_iff.1 h
    · intro W V C D r d
      have h := hi.image W V C D r d
      simp only [imageTypedFormula, contextAnchor_evaluate, rawAnchor_evaluate,
        coefficientRefAnchor_evaluate, ObjectFormula.evaluate] at h
      exact eq_iff_iff.1 h

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
    (IndependentPolynomialExpressions.compile p)

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
    TypedCoordinateRestriction.polynomialMap] using
    (IndependentPolynomialExpressions.evaluate_compile MvPolynomial.C
      (variableImage t ha A hA hf hc he hv ho ht f) p)

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

def identityFormula
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
  exact selectedImageAnchor t ha A hA hf hc he hv ho (𝟙 W) c
    (.equal (variableImage t ha A hA hf hc he hv ho ht (𝟙 W) c)
      (@MvPolynomial.X (coefficientNative t hf).1 _
        (coefficientNative t hf).2.toCommSemiring c))

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
    (identityFormula t ha A hA hf hc he hv ho ht W c).evaluate t ↔
      variableImage t ha A hA hf hc he hv ho ht (𝟙 W) c =
        @MvPolynomial.X (coefficientNative t hf).1 _
          (coefficientNative t hf).2.toCommSemiring c := by
  simp [identityFormula, selectedImageAnchor, ObjectFormula.evaluate]

def compositionFormula
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
      (.and
        (ObjectFormula.allList (MvPolynomial.vars p).toList (fun d =>
          selectedImageAnchor t ha A hA hf hc he hv ho f d .truth))
        (.equal (variableImage t ha A hA hf hc he hv ho ht (f ≫ g) c)
          (substitutionValue t ha A hA hf hc he hv ho ht f p))))

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
    (compositionFormula t ha A hA hf hc he hv ho ht f g c).evaluate t ↔
      variableImage t ha A hA hf hc he hv ho ht (f ≫ g) c =
        mappedPolynomial t ha A hA hf hc he hv ho ht f
          (variableImage t ha A hA hf hc he hv ho ht g c) := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  simp [compositionFormula, ObjectFormula.evaluate,
    substitutionValue_eq_mappedPolynomial]

def generatorFormula
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
    (.and
      (ObjectFormula.allList w.support.toList (fun i =>
        selectedPolynomialAnchor t ha A hA hf hc he hv ho X i .truth))
      (.and
        (ObjectFormula.allList (MvPolynomial.vars p).toList (fun c =>
          selectedImageAnchor t ha A hA hf hc he hv ho f c .truth))
        (.equal (witnessValue t ha A hA hf hc he hv ho ht X w)
          (substitutionValue t ha A hA hf hc he hv ho ht f p))))

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
    (generatorFormula t ha A hA hf hc he hv ho ht f r w).evaluate t ↔
      w.sum (fun i a =>
        a * relationPolynomial t ha A hA hf hc he hv ho ht X i) =
        mappedPolynomial t ha A hA hf hc he hv ho ht f
          (relationPolynomial t ha A hA hf hc he hv ho ht Y r) := by
  letI : CommRing (coefficientNative t hf).1 := (coefficientNative t hf).2
  simp [generatorFormula, ObjectFormula.evaluate, witnessValue_eq_sum,
    substitutionValue_eq_mappedPolynomial]

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
      (generatorFormula t ha A hA hf hc he hv ho ht f r w).evaluate t
  identity : ∀ (W : (rawSite t ha A hA hf hc he hv ho).category)
    (c : IndependentRawCandidate.coord (rawRows t ha A hA) W.ctx),
    (identityFormula t ha A hA hf hc he hv ho ht W c).evaluate t
  composition : ∀ {X Y Z : (rawSite t ha A hA hf hc he hv ho).category}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (c : IndependentRawCandidate.coord (rawRows t ha A hA) Z.ctx),
    (compositionFormula t ha A hA hf hc he hv ho ht f g c).evaluate t

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
