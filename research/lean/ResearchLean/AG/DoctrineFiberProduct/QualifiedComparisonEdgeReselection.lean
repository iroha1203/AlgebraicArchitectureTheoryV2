import ResearchLean.AG.DoctrineFiberProduct.QualifiedCoefficientObservation
import ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonFixedDecision
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryPairedCoefficientTrivialReselection

/-!
# Qualified comparison decisions for coefficient-trivial edge reselections

This module discharges G-118(C2).  It identifies the existing endpoint
intertwining predicate with pointwise membership in the actual qualified
comparison subgroup, and exhibits every fixed-base partner family as a torsor
under the literal product of target stabilizers intersected with coefficient
kernels.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

/-- The coefficient-trivial part of the target stabilizer of a complete
comparison.  This is the literal `K_H(c) ∩ ker κ_H` from G-118(C2). -/
noncomputable def qualifiedComparisonCoefficientTrivialTargetStabilizer
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    (comparison : GeometryTotalHom G H) : Subgroup (CompositeFiberAut H) :=
  qualifiedComparisonTargetStabilizer comparison ⊓
    (CompositeFiberAut.coefficientObservation H).ker

/-- Membership in the coefficient-trivial target stabilizer exposes exactly
the comparison-stabilizer and coefficient-kernel obligations. -/
@[simp] theorem mem_qualifiedComparisonCoefficientTrivialTargetStabilizer_iff
    {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U}
    {comparison : GeometryTotalHom G H}
    {automorphism : CompositeFiberAut H} :
    automorphism ∈
        qualifiedComparisonCoefficientTrivialTargetStabilizer comparison ↔
      automorphism ∈ qualifiedComparisonTargetStabilizer comparison ∧
        automorphism ∈
          (CompositeFiberAut.coefficientObservation H).ker :=
  Iff.rfl

namespace UpperGeometryCompatibleProblemInputData

set_option synthInstance.maxHeartbeats 100000

/-- The all-edge decision predicate is exactly pointwise membership in the
qualified comparison subgroup at the target of each edge. -/
theorem coefficientTrivialUpperReselectionEndpointIntertwining_iff_forall_mem
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    (solution : GeometryCompatibleUpperRefinementBCSolution input)
    (base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input)
    (pulled : GeneratedPulledCoefficientTrivialUpperEdgeReselection input) :
    CoefficientTrivialUpperReselectionEndpointIntertwining
        solution base pulled ↔
      ∀ {i j : P.Vertex} (edge : P.Edge i j),
        (base.toUpperEdgeReselection i j edge,
          pulled.toUpperEdgeReselection i j edge) ∈
            qualifiedComparisonSubgroup (solution.component j) :=
  Iff.rfl

/-- The edgewise product of the literal coefficient-trivial target
stabilizers for the theorem-generated comparison components. -/
abbrev GeneratedCoefficientTrivialTargetStabilizerFamily
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :=
  ∀ (i j : P.Vertex) (_edge : P.Edge i j),
    qualifiedComparisonCoefficientTrivialTargetStabilizer
      (input.generatedCompatibleUpperGeometryMateAt j)

/-- For a fixed generated base reselection, the family of all
coefficient-trivial pulled partners satisfying the actual comparison law. -/
abbrev GeneratedCoefficientTrivialPulledPartner
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input) :=
  { pulled : GeneratedPulledCoefficientTrivialUpperEdgeReselection input //
    CoefficientTrivialUpperReselectionEndpointIntertwining
      input.generatedGeometryCompatibleUpperRefinementBCSolution base pulled }

/-- Pointwise left multiplication by `K_(P_j)(c_j) ∩ ker κ_(P_j)`
preserves coefficient-trivial generated partner families. -/
noncomputable def generatedCoefficientTrivialPulledPartnerAction
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input}
    (stabilizer : GeneratedCoefficientTrivialTargetStabilizerFamily input)
    (partner : GeneratedCoefficientTrivialPulledPartner input base) :
    GeneratedCoefficientTrivialPulledPartner input base := by
  let pulled : GeneratedPulledCoefficientTrivialUpperEdgeReselection input := {
    toUpperEdgeReselection := fun i j edge =>
      (stabilizer i j edge).1 *
        (show CompositeFiberAut (input.generatedPulledRouteGeometryAt j) from
          partner.1.toUpperEdgeReselection i j edge)
    coefficient_id := by
      intro i j edge
      have stabilizerMembership :=
        mem_qualifiedComparisonCoefficientTrivialTargetStabilizer_iff.mp
          (stabilizer i j edge).2
      apply CompositeFiberAut.mem_coefficientObservation_ker_iff.mp
      exact (CompositeFiberAut.coefficientObservation
        (input.generatedPulledRouteGeometryAt j)).ker.mul_mem
          stabilizerMembership.2
          (CompositeFiberAut.mem_coefficientObservation_ker_iff.mpr
            (partner.1.coefficient_id edge))
  }
  refine ⟨pulled, ?_⟩
  intro i j edge
  let lift : QualifiedComparisonTargetLift
      (input.generatedCompatibleUpperGeometryMateAt j)
      (base.toUpperEdgeReselection i j edge) :=
    ⟨partner.1.toUpperEdgeReselection i j edge, partner.2 edge⟩
  let targetStabilizer : qualifiedComparisonTargetStabilizer
      (input.generatedCompatibleUpperGeometryMateAt j) :=
    ⟨(stabilizer i j edge).1,
      (mem_qualifiedComparisonCoefficientTrivialTargetStabilizer_iff.mp
        (stabilizer i j edge).2).1⟩
  exact (qualifiedComparisonTargetLiftAction targetStabilizer lift).2

/-- Scalar multiplication on partner families is the actual pointwise
coefficient-trivial target-stabilizer action. -/
noncomputable instance generatedCoefficientTrivialPulledPartnerSMul
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input} :
    SMul (GeneratedCoefficientTrivialTargetStabilizerFamily input)
      (GeneratedCoefficientTrivialPulledPartner input base) where
  smul := generatedCoefficientTrivialPulledPartnerAction

/-- The pointwise product laws make the partner-family action multiplicative. -/
noncomputable instance generatedCoefficientTrivialPulledPartnerMulAction
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input} :
    MulAction (GeneratedCoefficientTrivialTargetStabilizerFamily input)
      (GeneratedCoefficientTrivialPulledPartner input base) where
  one_smul partner := by
    apply Subtype.ext
    apply CoefficientTrivialUpperEdgeReselection.ext
    funext i j edge
    exact one_mul _
  mul_smul left right partner := by
    apply Subtype.ext
    apply CoefficientTrivialUpperEdgeReselection.ext
    funext i j edge
    exact mul_assoc _ _ _

/-- Every coefficient-trivial generated base reselection has an actual
coefficient-trivial pulled partner.  Existence comes from the isomorphism of
the theorem-generated comparison; coefficient triviality is then forced by
the qualified relation and the comparison's coefficient identity. -/
noncomputable def generatedCoefficientTrivialPulledPartnerOrigin
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input) :
    GeneratedCoefficientTrivialPulledPartner input base := by
  classical
  have pointwise : ∀ {i j : P.Vertex} (edge : P.Edge i j),
      ∃ pulled : CompositeFiberAut
          (input.generatedPulledRouteGeometryAt j),
        (base.toUpperEdgeReselection i j edge, pulled) ∈
            qualifiedComparisonSubgroup
              (input.generatedCompatibleUpperGeometryMateAt j) ∧
          (CompositeFiberAut.hom pulled).geometry.coefficientHom =
            RingHom.id k := by
    intro i j edge
    letI := input.generatedCompatibleUpperGeometryMateAt_isIso j
    let comparisonIso : input.generatedBaseRouteGeometryAt j ≅
        input.generatedPulledRouteGeometryAt j := by
      exact asIso (show input.generatedBaseRouteGeometryAt j ⟶
        input.generatedPulledRouteGeometryAt j from
          input.generatedCompatibleUpperGeometryMateAt j)
    let pair := qualifiedComparisonIsoGraphMulEquiv comparisonIso
      (base.toUpperEdgeReselection i j edge)
    have relation :
        (base.toUpperEdgeReselection i j edge, pair.1.2) ∈
          qualifiedComparisonSubgroup
            (input.generatedCompatibleUpperGeometryMateAt j) := by
      exact pair.2
    have coefficientEquality := congrArg
      (fun hom : GeometryTotalHom
          (input.generatedBaseRouteGeometryAt j)
          (input.generatedPulledRouteGeometryAt j) =>
        hom.geometry.coefficientHom) relation
    change
      (input.generatedCompatibleUpperGeometryMateAt j).geometry.coefficientHom.comp
          (CompositeFiberAut.hom
            (base.toUpperEdgeReselection i j edge)).geometry.coefficientHom =
        (CompositeFiberAut.hom pair.1.2).geometry.coefficientHom.comp
          (input.generatedCompatibleUpperGeometryMateAt j).geometry.coefficientHom
        at coefficientEquality
    rw [input.generatedCompatibleUpperGeometryMateAt_coefficient_id,
      base.coefficient_id edge] at coefficientEquality
    refine ⟨pair.1.2, relation, ?_⟩
    simpa only [RingHom.id_comp, RingHom.comp_id] using coefficientEquality.symm
  let pulled : GeneratedPulledCoefficientTrivialUpperEdgeReselection input := {
    toUpperEdgeReselection := fun i j edge =>
      Classical.choose (pointwise edge)
    coefficient_id := fun edge => (Classical.choose_spec (pointwise edge)).2
  }
  exact ⟨pulled, fun edge => (Classical.choose_spec (pointwise edge)).1⟩

/-- In particular, the partner family is never empty for an arbitrary fixed
coefficient-trivial generated base reselection. -/
theorem generatedCoefficientTrivialPulledPartner_nonempty
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input) :
    Nonempty (GeneratedCoefficientTrivialPulledPartner input base) :=
  ⟨input.generatedCoefficientTrivialPulledPartnerOrigin base⟩

/-! ## The source family and its generated H_B/H_P images -/

/-- A coefficient-trivial edge family on the source transport. -/
abbrev SourceCoefficientTrivialUpperEdgeReselection
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :=
  CoefficientTrivialUpperEdgeReselection input.sourceTransport

/-- The theorem-generated base homomorphism `H_B` preserves coefficient
identity. -/
theorem generatedBaseCompositeFiberAutAt_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package)
    (coefficientIdentity :
      (CompositeFiberAut.hom automorphism).geometry.coefficientHom =
        RingHom.id k) :
    (CompositeFiberAut.hom
      (input.generatedBaseCompositeFiberAutHomAt i automorphism)).geometry.coefficientHom =
        RingHom.id k := by
  have factorization := congrArg (fun hom => hom.geometry.coefficientHom)
    (input.generatedBaseCompositeFiberAutAt_fac i automorphism)
  change
    (input.generatedBaseRouteLegAt i).geometry.coefficientHom.comp
        (CompositeFiberAut.hom
          (input.generatedBaseCompositeFiberAutHomAt i automorphism)).geometry.coefficientHom =
      (CompositeFiberAut.hom automorphism).geometry.coefficientHom.comp
        (input.generatedBaseRouteLegAt i).geometry.coefficientHom
      at factorization
  rw [input.generatedBaseRouteLegAt_coefficient_id,
    coefficientIdentity] at factorization
  simpa only [RingHom.id_comp, RingHom.comp_id] using factorization

/-- The theorem-generated pulled homomorphism `H_P` preserves coefficient
identity. -/
theorem generatedPulledCompositeFiberAutAt_coefficient_id
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package)
    (coefficientIdentity :
      (CompositeFiberAut.hom automorphism).geometry.coefficientHom =
        RingHom.id k) :
    (CompositeFiberAut.hom
      (input.generatedPulledCompositeFiberAutHomAt i automorphism)).geometry.coefficientHom =
        RingHom.id k := by
  have factorization := congrArg (fun hom => hom.geometry.coefficientHom)
    (input.generatedPulledCompositeFiberAutAt_fac i automorphism)
  change
    (input.generatedPulledRouteLegAt i).geometry.coefficientHom.comp
        (CompositeFiberAut.hom
          (input.generatedPulledCompositeFiberAutHomAt i automorphism)).geometry.coefficientHom =
      (CompositeFiberAut.hom automorphism).geometry.coefficientHom.comp
        (input.generatedPulledRouteLegAt i).geometry.coefficientHom
      at factorization
  rw [input.generatedPulledRouteLegAt_coefficient_id,
    coefficientIdentity] at factorization
  simpa only [RingHom.id_comp, RingHom.comp_id] using factorization

/-- Apply `H_B` pointwise to a coefficient-trivial source family. -/
noncomputable def generatedBaseOfSourceCoefficientTrivialUpperEdgeReselection
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (source : SourceCoefficientTrivialUpperEdgeReselection input) :
    GeneratedBaseCoefficientTrivialUpperEdgeReselection input where
  toUpperEdgeReselection := fun i j edge =>
    input.generatedBaseCompositeFiberAutHomAt j
      (source.toUpperEdgeReselection i j edge)
  coefficient_id := fun edge =>
    input.generatedBaseCompositeFiberAutAt_coefficient_id _ _
      (source.coefficient_id edge)

/-- Apply `H_P` pointwise to the same coefficient-trivial source family. -/
noncomputable def generatedPulledOfSourceCoefficientTrivialUpperEdgeReselection
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (source : SourceCoefficientTrivialUpperEdgeReselection input) :
    GeneratedPulledCoefficientTrivialUpperEdgeReselection input where
  toUpperEdgeReselection := fun i j edge =>
    input.generatedPulledCompositeFiberAutHomAt j
      (source.toUpperEdgeReselection i j edge)
  coefficient_id := fun edge =>
    input.generatedPulledCompositeFiberAutAt_coefficient_id _ _
      (source.coefficient_id edge)

/-- The common source edge family maps through `H_B/H_P` to a pointwise
qualified generated pair. -/
theorem sourceCoefficientTrivialUpperEdgeReselection_generated_mem
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (source : SourceCoefficientTrivialUpperEdgeReselection input)
    {i j : P.Vertex} (edge : P.Edge i j) :
    (input.generatedBaseCompositeFiberAutHomAt j
        (source.toUpperEdgeReselection i j edge),
      input.generatedPulledCompositeFiberAutHomAt j
        (source.toUpperEdgeReselection i j edge)) ∈
      qualifiedComparisonSubgroup
        (input.generatedCompatibleUpperGeometryMateAt j) :=
  input.generatedQualifiedComparisonRelation_diagonal j
    (source.toUpperEdgeReselection i j edge)

/-- Hence every coefficient-trivial source family supplies the generated
paired endpoint law; this is source-to-paired existence, distinct from the
arbitrary paired-family preservation theorem above. -/
theorem sourceCoefficientTrivialUpperEdgeReselection_generated_endpointIntertwining
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (source : SourceCoefficientTrivialUpperEdgeReselection input) :
    CoefficientTrivialUpperReselectionEndpointIntertwining
      input.generatedGeometryCompatibleUpperRefinementBCSolution
      (input.generatedBaseOfSourceCoefficientTrivialUpperEdgeReselection source)
      (input.generatedPulledOfSourceCoefficientTrivialUpperEdgeReselection source) := by
  intro i j edge
  exact input.sourceCoefficientTrivialUpperEdgeReselection_generated_mem source edge

/-- The product action on a nonempty partner family is free. -/
theorem generatedCoefficientTrivialPulledPartnerAction_free
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input}
    (partner : GeneratedCoefficientTrivialPulledPartner input base)
    {left right : GeneratedCoefficientTrivialTargetStabilizerFamily input}
    (equality : left • partner = right • partner) : left = right := by
  funext i j edge
  apply Subtype.ext
  have valueEquality := congrArg
    (fun selected : GeneratedCoefficientTrivialPulledPartner input base =>
      selected.1.toUpperEdgeReselection i j edge) equality
  exact mul_right_cancel valueEquality

/-- Any two coefficient-trivial pulled partners differ by a unique edgewise
element of `K_(P_j)(c_j) ∩ ker κ_(P_j)`. -/
theorem generatedCoefficientTrivialPulledPartnerAction_transitive
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input}
    (source target : GeneratedCoefficientTrivialPulledPartner input base) :
    ∃ stabilizer : GeneratedCoefficientTrivialTargetStabilizerFamily input,
      stabilizer • source = target := by
  classical
  have pointwise : ∀ {i j : P.Vertex} (edge : P.Edge i j),
      ∃ stabilizer : qualifiedComparisonCoefficientTrivialTargetStabilizer
          (input.generatedCompatibleUpperGeometryMateAt j),
        stabilizer.1 *
            (show CompositeFiberAut
              (input.generatedPulledRouteGeometryAt j) from
              source.1.toUpperEdgeReselection i j edge) =
          (show CompositeFiberAut
            (input.generatedPulledRouteGeometryAt j) from
            target.1.toUpperEdgeReselection i j edge) := by
    intro i j edge
    let sourceLift : QualifiedComparisonTargetLift
        (input.generatedCompatibleUpperGeometryMateAt j)
        (base.toUpperEdgeReselection i j edge) :=
      ⟨source.1.toUpperEdgeReselection i j edge, source.2 edge⟩
    let targetLift : QualifiedComparisonTargetLift
        (input.generatedCompatibleUpperGeometryMateAt j)
        (base.toUpperEdgeReselection i j edge) :=
      ⟨target.1.toUpperEdgeReselection i j edge, target.2 edge⟩
    obtain ⟨stabilizer, action⟩ :=
      qualifiedComparisonTargetLiftAction_transitive sourceLift targetLift
    have sourceCoefficient : source.1.toUpperEdgeReselection i j edge ∈
        (CompositeFiberAut.coefficientObservation
          (input.generatedPulledRouteGeometryAt j)).ker :=
      CompositeFiberAut.mem_coefficientObservation_ker_iff.mpr
        (source.1.coefficient_id edge)
    have targetCoefficient : target.1.toUpperEdgeReselection i j edge ∈
        (CompositeFiberAut.coefficientObservation
          (input.generatedPulledRouteGeometryAt j)).ker :=
      CompositeFiberAut.mem_coefficientObservation_ker_iff.mpr
        (target.1.coefficient_id edge)
    have actionValue : stabilizer.1 *
        (show CompositeFiberAut
          (input.generatedPulledRouteGeometryAt j) from
          source.1.toUpperEdgeReselection i j edge) =
          (show CompositeFiberAut
            (input.generatedPulledRouteGeometryAt j) from
            target.1.toUpperEdgeReselection i j edge) :=
      congrArg Subtype.val action
    have stabilizerCoefficient : stabilizer.1 ∈
        (CompositeFiberAut.coefficientObservation
          (input.generatedPulledRouteGeometryAt j)).ker := by
      have productCoefficient : stabilizer.1 *
          (show CompositeFiberAut
            (input.generatedPulledRouteGeometryAt j) from
            source.1.toUpperEdgeReselection i j edge) ∈
          (CompositeFiberAut.coefficientObservation
            (input.generatedPulledRouteGeometryAt j)).ker := by
        rw [actionValue]
        exact targetCoefficient
      exact ((CompositeFiberAut.coefficientObservation
        (input.generatedPulledRouteGeometryAt j)).ker.mul_mem_cancel_right
          sourceCoefficient).mp productCoefficient
    exact ⟨⟨stabilizer.1,
      mem_qualifiedComparisonCoefficientTrivialTargetStabilizer_iff.mpr
        ⟨stabilizer.2, stabilizerCoefficient⟩⟩, actionValue⟩
  let stabilizer : GeneratedCoefficientTrivialTargetStabilizerFamily input :=
    fun _ _ edge => Classical.choose (pointwise edge)
  refine ⟨stabilizer, ?_⟩
  apply Subtype.ext
  apply CoefficientTrivialUpperEdgeReselection.ext
  funext i j edge
  exact Classical.choose_spec (pointwise edge)

/-- The partner family is a torsor: for every two partners there is exactly
one coefficient-trivial stabilizer family carrying the first to the second. -/
theorem generatedCoefficientTrivialPulledPartner_existsUnique
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    {input : UpperGeometryCompatibleProblemInputData ctx P k}
    {base : GeneratedBaseCoefficientTrivialUpperEdgeReselection input}
    (source target : GeneratedCoefficientTrivialPulledPartner input base) :
    ∃! stabilizer : GeneratedCoefficientTrivialTargetStabilizerFamily input,
      stabilizer • source = target := by
  obtain ⟨stabilizer, action⟩ :=
    generatedCoefficientTrivialPulledPartnerAction_transitive source target
  exact ⟨stabilizer, action, fun other otherAction =>
    generatedCoefficientTrivialPulledPartnerAction_free source
      (otherAction.trans action.symm)⟩

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
