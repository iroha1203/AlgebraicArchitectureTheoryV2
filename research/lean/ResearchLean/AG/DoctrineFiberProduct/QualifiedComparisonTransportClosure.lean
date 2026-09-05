import ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonCoefficientTransport

/-!
# Typed closure of qualified-comparison transport

This module closes G-118(C1--C3).  C1 is the typed finite groupoid generated
by the selected canonical/generated endpoint change.  C2 multiplication is
connected to literal qualified membership and to every finite path.  C3 is
closed only under type-correct postcomposition by a C1 chain; its codomain is
recorded as the generated image rather than promoted to an ambient
equivalence.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 6000000

namespace UpperGeometryCompatibleProblemInputData

/-- The two endpoint presentations selected by the G-118 data. -/
inductive QualifiedComparisonDisplay
  | canonical
  | generated
  deriving DecidableEq

/-- Raw pairs in a selected endpoint presentation. -/
abbrev qualifiedComparisonDisplayPairAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    QualifiedComparisonDisplay → Type _
  | .canonical => CanonicalQualifiedPairAt input i
  | .generated => GeneratedQualifiedPairAt input i

noncomputable instance qualifiedComparisonDisplayPairGroup
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (display : QualifiedComparisonDisplay) :
    Group (qualifiedComparisonDisplayPairAt input i display) := by
  cases display <;> infer_instance

/-- Literal qualified membership in either selected presentation. -/
def qualifiedComparisonDisplayDecisionAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (display : QualifiedComparisonDisplay) →
      qualifiedComparisonDisplayPairAt input i display → Prop
  | .canonical, pair => pair ∈ qualifiedComparisonSubgroup
      (input.canonicalCompanionUpperRefinementBCSolution.component i)
  | .generated, pair => pair ∈ qualifiedComparisonSubgroup
      (input.generatedCompatibleUpperGeometryMateAt i)

/-- Complete product coefficient observation in either presentation. -/
noncomputable def qualifiedComparisonDisplayObservationAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    (display : QualifiedComparisonDisplay) →
      qualifiedComparisonDisplayPairAt input i display →*
        (Aut (CommRingCat.of k) × Aut (CommRingCat.of k))
  | .canonical => input.canonicalPairCoefficientObservationAt i
  | .generated => input.generatedPairCoefficientObservationAt i

/-- The selected C1 change on the complete base/pulled pair. -/
noncomputable def canonicalGeneratedPairMulEquivAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    CanonicalQualifiedPairAt input i ≃* GeneratedQualifiedPairAt input i :=
  MulEquiv.prodCongr
    (CompositeFiberAut.conjugationMulEquiv
      (input.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i))
    (CompositeFiberAut.conjugationMulEquiv
      (input.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i))

@[simp] theorem canonicalPairBackwardAt_forward
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (pair : CanonicalQualifiedPairAt input i) :
    input.canonicalPairBackwardAt i
        (input.canonicalGeneratedPairMulEquivAt i pair) = pair := by
  change (input.canonicalGeneratedPairMulEquivAt i).symm
      (input.canonicalGeneratedPairMulEquivAt i pair) = pair
  exact (input.canonicalGeneratedPairMulEquivAt i).symm_apply_apply pair

/-- One generator of the selected C1 presentation groupoid. -/
inductive QualifiedComparisonC1Step
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    QualifiedComparisonDisplay → QualifiedComparisonDisplay → Type
  | forward : QualifiedComparisonC1Step input i .canonical .generated
  | backward : QualifiedComparisonC1Step input i .generated .canonical

namespace QualifiedComparisonC1Step

/-- The inverse selected C1 generator. -/
def reverse
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k} {i : P.Vertex}
    {a b : QualifiedComparisonDisplay} :
    QualifiedComparisonC1Step input i a b →
      QualifiedComparisonC1Step input i b a
  | .forward => .backward
  | .backward => .forward

/-- The raw-pair equivalence carried by one C1 generator. -/
noncomputable def pairMulEquivAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k} {i : P.Vertex}
    {a b : QualifiedComparisonDisplay}
    (step : QualifiedComparisonC1Step input i a b) :
    qualifiedComparisonDisplayPairAt input i a ≃*
      qualifiedComparisonDisplayPairAt input i b := by
  cases step with
  | forward => exact input.canonicalGeneratedPairMulEquivAt i
  | backward => exact (input.canonicalGeneratedPairMulEquivAt i).symm

@[simp] theorem reverse_pairMulEquivAt_apply
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k} {i : P.Vertex}
    {a b : QualifiedComparisonDisplay}
    (step : QualifiedComparisonC1Step input i a b)
    (pair : qualifiedComparisonDisplayPairAt input i b) :
    step.reverse.pairMulEquivAt pair = step.pairMulEquivAt.symm pair := by
  cases step <;> rfl

/-- A C1 generator preserves and reflects literal qualified membership. -/
theorem decision_iff
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k} {i : P.Vertex}
    {a b : QualifiedComparisonDisplay}
    (step : QualifiedComparisonC1Step input i a b)
    (pair : qualifiedComparisonDisplayPairAt input i a) :
    input.qualifiedComparisonDisplayDecisionAt i b (step.pairMulEquivAt pair) ↔
      input.qualifiedComparisonDisplayDecisionAt i a pair := by
  cases step with
  | forward =>
      have h := input.canonicalPairBackwardAt_mem_qualifiedComparison_iff i
        (input.canonicalGeneratedPairMulEquivAt i pair)
      rw [input.canonicalPairBackwardAt_forward] at h
      exact h.symm
  | backward =>
      exact input.canonicalPairBackwardAt_mem_qualifiedComparison_iff i pair

/-- A C1 generator commutes with the complete coefficient observation. -/
theorem observation_apply
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k} {i : P.Vertex}
    {a b : QualifiedComparisonDisplay}
    (step : QualifiedComparisonC1Step input i a b)
    (pair : qualifiedComparisonDisplayPairAt input i a) :
    input.qualifiedComparisonDisplayObservationAt i b (step.pairMulEquivAt pair) =
      input.qualifiedComparisonDisplayObservationAt i a pair := by
  cases step with
  | forward =>
      have h := input.canonicalPairBackwardAt_coefficientObservation i
        (input.canonicalGeneratedPairMulEquivAt i pair)
      rw [input.canonicalPairBackwardAt_forward] at h
      exact h.symm
  | backward =>
      exact input.canonicalPairBackwardAt_coefficientObservation i pair

end QualifiedComparisonC1Step

/-- A type-correct finite chain of selected C1 changes. -/
inductive QualifiedComparisonC1Chain
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    QualifiedComparisonDisplay → QualifiedComparisonDisplay → Type
  | nil (display) : QualifiedComparisonC1Chain input i display display
  | cons {a b c} : QualifiedComparisonC1Step input i a b →
      QualifiedComparisonC1Chain input i b c →
      QualifiedComparisonC1Chain input i a c

namespace QualifiedComparisonC1Chain

/-- Type-correct concatenation of finite C1 chains. -/
def append
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k} {i : P.Vertex}
    {a b c : QualifiedComparisonDisplay} :
    QualifiedComparisonC1Chain input i a b →
      QualifiedComparisonC1Chain input i b c →
      QualifiedComparisonC1Chain input i a c
  | .nil _, right => right
  | .cons step tail, right => .cons step (tail.append right)

/-- Reverse a finite C1 chain. -/
def reverse
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k} {i : P.Vertex}
    {a b : QualifiedComparisonDisplay} :
    QualifiedComparisonC1Chain input i a b →
      QualifiedComparisonC1Chain input i b a
  | .nil display => .nil display
  | .cons step tail => tail.reverse.append (.cons step.reverse (.nil _))

/-- The raw-pair equivalence carried by a finite C1 chain. -/
noncomputable def pairMulEquivAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k} {i : P.Vertex}
    {a b : QualifiedComparisonDisplay}
    (chain : QualifiedComparisonC1Chain input i a b) :
    qualifiedComparisonDisplayPairAt input i a ≃*
      qualifiedComparisonDisplayPairAt input i b := by
  induction chain with
  | nil display => exact MulEquiv.refl _
  | cons step tail ih => exact step.pairMulEquivAt.trans ih

@[simp] theorem pairMulEquivAt_nil_apply
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k} {i : P.Vertex}
    {display : QualifiedComparisonDisplay}
    (pair : qualifiedComparisonDisplayPairAt input i display) :
    pairMulEquivAt (.nil display) pair = pair := rfl

theorem pairMulEquivAt_append_apply
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k} {i : P.Vertex}
    {a b c : QualifiedComparisonDisplay}
    (left : QualifiedComparisonC1Chain input i a b)
    (right : QualifiedComparisonC1Chain input i b c)
    (pair : qualifiedComparisonDisplayPairAt input i a) :
    pairMulEquivAt (left.append right) pair =
      pairMulEquivAt right (pairMulEquivAt left pair) := by
  induction left generalizing c with
  | nil display => rfl
  | cons step tail ih => exact ih right (step.pairMulEquivAt pair)

/-- Reversing a finite C1 chain gives the inverse raw-pair equivalence. -/
theorem pairMulEquivAt_reverse_apply
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k} {i : P.Vertex}
    {a b : QualifiedComparisonDisplay}
    (chain : QualifiedComparisonC1Chain input i a b)
    (pair : qualifiedComparisonDisplayPairAt input i b) :
    chain.reverse.pairMulEquivAt pair = chain.pairMulEquivAt.symm pair := by
  induction chain with
  | nil display => rfl
  | cons step tail ih =>
      change pairMulEquivAt
          (tail.reverse.append (.cons step.reverse (.nil _))) pair =
        step.pairMulEquivAt.symm (tail.pairMulEquivAt.symm pair)
      rw [pairMulEquivAt_append_apply, ih]
      change step.reverse.pairMulEquivAt (tail.pairMulEquivAt.symm pair) =
        step.pairMulEquivAt.symm (tail.pairMulEquivAt.symm pair)
      exact QualifiedComparisonC1Step.reverse_pairMulEquivAt_apply _ _

/-- Every finite C1 chain preserves and reflects qualified membership. -/
theorem decision_iff
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k} {i : P.Vertex}
    {a b : QualifiedComparisonDisplay}
    (chain : QualifiedComparisonC1Chain input i a b)
    (pair : qualifiedComparisonDisplayPairAt input i a) :
    input.qualifiedComparisonDisplayDecisionAt i b (chain.pairMulEquivAt pair) ↔
      input.qualifiedComparisonDisplayDecisionAt i a pair := by
  induction chain with
  | nil display => exact Iff.rfl
  | cons step tail ih =>
      exact (ih (step.pairMulEquivAt pair)).trans (step.decision_iff pair)

/-- Every finite C1 chain commutes with coefficient observation. -/
theorem observation_apply
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k} {i : P.Vertex}
    {a b : QualifiedComparisonDisplay}
    (chain : QualifiedComparisonC1Chain input i a b)
    (pair : qualifiedComparisonDisplayPairAt input i a) :
    input.qualifiedComparisonDisplayObservationAt i b (chain.pairMulEquivAt pair) =
      input.qualifiedComparisonDisplayObservationAt i a pair := by
  induction chain with
  | nil display => rfl
  | cons step tail ih =>
      exact (ih (step.pairMulEquivAt pair)).trans (step.observation_apply pair)

/-- C1 transport is bijective, in particular surjective, for every chain. -/
theorem pairMulEquivAt_bijective
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k} {i : P.Vertex}
    {a b : QualifiedComparisonDisplay}
    (chain : QualifiedComparisonC1Chain input i a b) :
    Function.Bijective chain.pairMulEquivAt := chain.pairMulEquivAt.bijective

end QualifiedComparisonC1Chain

/-- C2 pointwise multiplication remains a literal qualified pair at every
edge. -/
theorem coefficientTrivialUpperReselectionEndpointIntertwining_mul_mem
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {solution : GeometryCompatibleUpperRefinementBCSolution input}
    {baseFirst baseSecond : GeneratedBaseCoefficientTrivialUpperEdgeReselection input}
    {pulledFirst pulledSecond : GeneratedPulledCoefficientTrivialUpperEdgeReselection input}
    (first : CoefficientTrivialUpperReselectionEndpointIntertwining solution
      baseFirst pulledFirst)
    (second : CoefficientTrivialUpperReselectionEndpointIntertwining solution
      baseSecond pulledSecond)
    {i j : P.Vertex} (edge : P.Edge i j) :
    ((CoefficientTrivialUpperEdgeReselection.mul baseFirst baseSecond).toUpperEdgeReselection
        i j edge,
      (CoefficientTrivialUpperEdgeReselection.mul pulledFirst pulledSecond).toUpperEdgeReselection
        i j edge) ∈ qualifiedComparisonSubgroup (solution.component j) :=
  (coefficientTrivialUpperReselectionEndpointIntertwining_iff_forall_mem
    solution _ _).1 (first.mul second) edge

/-- C2 pointwise multiplication still fixes both coefficient rings. -/
theorem coefficientTrivialUpperReselection_mul_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (baseFirst baseSecond : GeneratedBaseCoefficientTrivialUpperEdgeReselection input)
    (pulledFirst pulledSecond : GeneratedPulledCoefficientTrivialUpperEdgeReselection input)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (CompositeFiberAut.hom
      ((CoefficientTrivialUpperEdgeReselection.mul baseFirst baseSecond).toUpperEdgeReselection
        i j edge)).geometry.coefficientHom = RingHom.id k ∧
    (CompositeFiberAut.hom
      ((CoefficientTrivialUpperEdgeReselection.mul pulledFirst pulledSecond).toUpperEdgeReselection
        i j edge)).geometry.coefficientHom = RingHom.id k :=
  ⟨(CoefficientTrivialUpperEdgeReselection.mul baseFirst baseSecond).coefficient_id edge,
    (CoefficientTrivialUpperEdgeReselection.mul pulledFirst pulledSecond).coefficient_id edge⟩

/-- C2 products intertwine every finite path. -/
theorem coefficientTrivialUpperReselectionEndpointIntertwining_mul_path
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {solution : GeometryCompatibleUpperRefinementBCSolution input}
    {baseFirst baseSecond : GeneratedBaseCoefficientTrivialUpperEdgeReselection input}
    {pulledFirst pulledSecond : GeneratedPulledCoefficientTrivialUpperEdgeReselection input}
    (first : CoefficientTrivialUpperReselectionEndpointIntertwining solution
      baseFirst pulledFirst)
    (second : CoefficientTrivialUpperReselectionEndpointIntertwining solution
      baseSecond pulledSecond)
    {i j : P.Vertex} (path : P.Path i j) :
    (upperReselectedPathLift input.generatedBaseRouteLiftData
      (CoefficientTrivialUpperEdgeReselection.mul baseFirst baseSecond).toUpperEdgeReselection
      path).comp (solution.component j) =
    (solution.component i).comp
      (upperReselectedPathLift input.generatedPulledRouteLiftData
        (CoefficientTrivialUpperEdgeReselection.mul pulledFirst pulledSecond).toUpperEdgeReselection
        path) :=
  CoefficientTrivialUpperReselectionEndpointIntertwining.reselectedPath_naturality
    (first.mul second) path

/-- C3 followed by any type-correct finite C1 display chain. -/
noncomputable def closedComparisonPairHomAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    {display : QualifiedComparisonDisplay}
    (chain : QualifiedComparisonC1Chain input i .generated display) :
    (CompositeFiberAut (input.sourceGeometry i).package ×
      CompositeFiberAut (input.sourceGeometry i).package) →*
      qualifiedComparisonDisplayPairAt input i display :=
  chain.pairMulEquivAt.toMonoidHom.comp (input.generatedComparisonPairHomAt i)

@[simp] theorem closedComparisonPairHomAt_apply
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    {display : QualifiedComparisonDisplay}
    (chain : QualifiedComparisonC1Chain input i .generated display)
    (pair : CompositeFiberAut (input.sourceGeometry i).package ×
      CompositeFiberAut (input.sourceGeometry i).package) :
    input.closedComparisonPairHomAt i chain pair =
      chain.pairMulEquivAt (input.generatedComparisonPairHomAt i pair) := rfl

@[simp] theorem closedComparisonPairHomAt_nil
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    input.closedComparisonPairHomAt i (.nil .generated) =
      input.generatedComparisonPairHomAt i := by
  apply MonoidHom.ext
  intro pair
  exact QualifiedComparisonC1Chain.pairMulEquivAt_nil_apply _

/-- Postcomposition by another type-correct C1 chain is the corresponding
composition of the closed C3 map. -/
theorem closedComparisonPairHomAt_append_apply
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    {middle display : QualifiedComparisonDisplay}
    (first : QualifiedComparisonC1Chain input i .generated middle)
    (second : QualifiedComparisonC1Chain input i middle display)
    (pair : CompositeFiberAut (input.sourceGeometry i).package ×
      CompositeFiberAut (input.sourceGeometry i).package) :
    input.closedComparisonPairHomAt i (first.append second) pair =
      second.pairMulEquivAt (input.closedComparisonPairHomAt i first pair) :=
  QualifiedComparisonC1Chain.pairMulEquivAt_append_apply first second _

/-- The only fixed-data C1 precomposition at the source is identity, and it
acts identically. -/
theorem closedComparisonPairHomAt_comp_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    {display : QualifiedComparisonDisplay}
    (chain : QualifiedComparisonC1Chain input i .generated display) :
    (input.closedComparisonPairHomAt i chain).comp (MonoidHom.id _) =
      input.closedComparisonPairHomAt i chain := by
  ext pair
  rfl

/-- The closed C3 map preserves qualified membership. -/
theorem closedComparisonPairHomAt_preserves_qualifiedComparison
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    {display : QualifiedComparisonDisplay}
    (chain : QualifiedComparisonC1Chain input i .generated display)
    {pair : CompositeFiberAut (input.sourceGeometry i).package ×
      CompositeFiberAut (input.sourceGeometry i).package}
    (membership : pair ∈ qualifiedComparisonSubgroup
      (𝟙 (input.sourceGeometry i).package)) :
    input.qualifiedComparisonDisplayDecisionAt i display
      (input.closedComparisonPairHomAt i chain pair) :=
  (chain.decision_iff _).2
    (input.generatedComparisonPairHomAt_preserves_qualifiedComparison i membership)

/-- Exact reflection for every closed C3 display is equivalent to `J_i = ⊥`. -/
theorem closedComparisonPairHomAt_reflects_qualifiedComparison_iff
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    {display : QualifiedComparisonDisplay}
    (chain : QualifiedComparisonC1Chain input i .generated display) :
    (∀ pair : CompositeFiberAut (input.sourceGeometry i).package ×
        CompositeFiberAut (input.sourceGeometry i).package,
      input.qualifiedComparisonDisplayDecisionAt i display
          (input.closedComparisonPairHomAt i chain pair) →
        pair ∈ qualifiedComparisonSubgroup
          (𝟙 (input.sourceGeometry i).package)) ↔
      input.generatedPulledComparisonKernel i = ⊥ := by
  rw [← input.generatedComparisonPairHomAt_reflects_qualifiedComparison_iff i]
  constructor <;> intro reflects pair membership
  · exact reflects pair ((chain.decision_iff _).2 membership)
  · exact reflects pair ((chain.decision_iff _).1 membership)

/-- Every closed C3 map commutes with the complete coefficient observation. -/
theorem closedComparisonPairHomAt_coefficientObservation
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    {display : QualifiedComparisonDisplay}
    (chain : QualifiedComparisonC1Chain input i .generated display)
    (pair : CompositeFiberAut (input.sourceGeometry i).package ×
      CompositeFiberAut (input.sourceGeometry i).package) :
    input.qualifiedComparisonDisplayObservationAt i display
        (input.closedComparisonPairHomAt i chain pair) =
      input.sourcePairCoefficientObservationAt i pair :=
  (chain.observation_apply _).trans
    (input.generatedComparisonPairHomAt_coefficientObservation i pair)

/-- The image generated by a closed C3 map. -/
noncomputable abbrev closedComparisonPairImageAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    {display : QualifiedComparisonDisplay}
    (chain : QualifiedComparisonC1Chain input i .generated display) :=
  (input.closedComparisonPairHomAt i chain).range

/-- C3 is unconditionally surjective onto its generated image. -/
theorem closedComparisonPairHomAt_rangeRestrict_surjective
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    {display : QualifiedComparisonDisplay}
    (chain : QualifiedComparisonC1Chain input i .generated display) :
    Function.Surjective (input.closedComparisonPairHomAt i chain).rangeRestrict :=
  (input.closedComparisonPairHomAt i chain).rangeRestrict_surjective

end UpperGeometryCompatibleProblemInputData

namespace UpperDecisionWitness

/-- The fixed information-loss witness survives every finite C1 chain. -/
theorem fixedQualifiedDecision_not_factor_after_c1_chain
    {display : UpperGeometryCompatibleProblemInputData.QualifiedComparisonDisplay}
    (chain : problem.data.QualifiedComparisonC1Chain PUnit.unit .generated display) :
    let positive := chain.pairMulEquivAt fixedPositiveQualifiedPair
    let negative := chain.pairMulEquivAt fixedNegativeQualifiedPair
    problem.data.qualifiedComparisonDisplayObservationAt PUnit.unit display positive =
        problem.data.qualifiedComparisonDisplayObservationAt PUnit.unit display negative ∧
      problem.data.qualifiedComparisonDisplayDecisionAt PUnit.unit display positive ∧
      ¬ problem.data.qualifiedComparisonDisplayDecisionAt PUnit.unit display negative ∧
      ¬ ∃ diagnostic : (Aut (CommRingCat.of Int) × Aut (CommRingCat.of Int)) → Prop,
        ∀ pair : problem.data.qualifiedComparisonDisplayPairAt PUnit.unit display,
          problem.data.qualifiedComparisonDisplayDecisionAt PUnit.unit display pair ↔
            diagnostic
              (problem.data.qualifiedComparisonDisplayObservationAt PUnit.unit display pair) := by
  dsimp only
  have collision := fixedCoefficientObservation_positive_eq_negative
  have transportedCollision :
      problem.data.qualifiedComparisonDisplayObservationAt PUnit.unit display
          (chain.pairMulEquivAt fixedPositiveQualifiedPair) =
        problem.data.qualifiedComparisonDisplayObservationAt PUnit.unit display
          (chain.pairMulEquivAt fixedNegativeQualifiedPair) := by
    rw [chain.observation_apply, chain.observation_apply]
    exact collision
  have positive := (chain.decision_iff fixedPositiveQualifiedPair).2
    fixedPositiveQualifiedDecision
  have negative := (chain.decision_iff fixedNegativeQualifiedPair).not.mpr
    fixedNegativeNotQualifiedDecision
  refine ⟨transportedCollision, positive, negative, ?_⟩
  rintro ⟨diagnostic, factors⟩
  have positiveObserved := (factors _).mp positive
  have negativeObserved := (factors _).mpr (transportedCollision ▸ positiveObserved)
  exact negative negativeObserved

end UpperDecisionWitness

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
