import ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonStabilizer
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleGlobalMate
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleComparatorIncoherence

/-!
# Generated qualified-comparison classification

The generated base and pulled endpoint homomorphisms send every source
composite-fiber automorphism, not only an authored cell comparator, to a pair
preserving the generated upper mate.  The possible pulled source changes over
one fixed base source change are then classified by the preimage of the actual
target comparison stabilizer.

Implementation notes: the arbitrary-source intertwining is proved from the
two literal generated route factorizations and the generated mate triangle.
The residual subgroup is a `Subgroup.comap` of the target stabilizer; its
coset theorem is derived from the comparison equation and group operations,
not stored as an input certificate.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

namespace UpperGeometryCompatibleProblemInputData

/-- Every source composite-fiber automorphism generates endpoint changes that
intertwine the generated compatible upper mate. -/
theorem generatedCompatibleUpperGeometryMateAt_automorphism_intertwining
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (CompositeFiberAut.hom
        (input.generatedBaseCompositeFiberAutHomAt i automorphism)).comp
          (input.generatedCompatibleUpperGeometryMateAt i) =
      (input.generatedCompatibleUpperGeometryMateAt i).comp
        (CompositeFiberAut.hom
          (input.generatedPulledCompositeFiberAutHomAt i automorphism)) := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  let mate := input.generatedCompatibleUpperGeometryMateAt i
  let baseAutomorphism := CompositeFiberAut.hom
    (input.generatedBaseCompositeFiberAutHomAt i automorphism)
  let pulledAutomorphism := CompositeFiberAut.hom
    (input.generatedPulledCompositeFiberAutHomAt i automorphism)
  let pulledLeg := input.generatedPulledRouteLegAt i
  have hafterLeg :
      (((exactGeometryToRefinementGeometry U).map baseAutomorphism) ≫
          ((exactGeometryToRefinementGeometry U).map mate)) ≫ pulledLeg =
        (((exactGeometryToRefinementGeometry U).map mate) ≫
          ((exactGeometryToRefinementGeometry U).map pulledAutomorphism)) ≫
            pulledLeg := by
    have hbaseFac := input.generatedBaseCompositeFiberAutAt_fac i automorphism
    have hpulledFac := input.generatedPulledCompositeFiberAutAt_fac i automorphism
    have htriangle := input.generatedCompatibleUpperGeometryMateAt_triangle i
    calc
      _ = ((exactGeometryToRefinementGeometry U).map baseAutomorphism) ≫
          (((exactGeometryToRefinementGeometry U).map mate) ≫ pulledLeg) :=
        Category.assoc _ _ _
      _ = ((exactGeometryToRefinementGeometry U).map baseAutomorphism) ≫
          input.generatedBaseRouteLegAt i := congrArg _ htriangle
      _ = input.generatedBaseRouteLegAt i ≫
          (exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom automorphism) := hbaseFac
      _ = (((exactGeometryToRefinementGeometry U).map mate) ≫ pulledLeg) ≫
          (exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom automorphism) := congrArg
          (fun hom => hom ≫ (exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom automorphism)) htriangle.symm
      _ = ((exactGeometryToRefinementGeometry U).map mate) ≫
          (pulledLeg ≫ (exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom automorphism)) := Category.assoc _ _ _
      _ = ((exactGeometryToRefinementGeometry U).map mate) ≫
          (((exactGeometryToRefinementGeometry U).map pulledAutomorphism) ≫
            pulledLeg) := congrArg _ hpulledFac.symm
      _ = _ := (Category.assoc _ _ _).symm
  let left := (exactGeometryToRefinementGeometry U).map
    (baseAutomorphism.comp mate)
  let right := (exactGeometryToRefinementGeometry U).map
    (mate.comp pulledAutomorphism)
  have hafterLeg' : left.comp pulledLeg = right.comp pulledLeg := hafterLeg
  have hleftBase : left.base = right.base := by
    let packageLeft := left.base
    let packageRight := right.base
    have hpackageBase : packageLeft.base = packageRight.base := by
      change (exactPointedToRefinement U).map
          ((baseAutomorphism.comp mate).base.base) =
        (exactPointedToRefinement U).map
          ((mate.comp pulledAutomorphism).base.base)
      apply congrArg (exactPointedToRefinement U).map
      change baseAutomorphism.base.base.comp mate.base.base =
        mate.base.base.comp pulledAutomorphism.base.base
      rw [CompositeFiberAut.hom_base_base_eq,
        CompositeFiberAut.hom_base_base_eq]
      apply ExtInstHom.ext
      apply ExactDoctrineHom.ext
      · rfl
      · apply Equiv.ext
        intro atom
        rfl
    letI hpackageLeftLift :=
      UpperGeometryCleavage.refinementPackageHom_isHomLift_of_base_eq
        packageRight.base packageLeft hpackageBase
    letI hpackageRightLift :=
      UpperGeometryCleavage.refinementPackageHom_isHomLift_of_base_eq
        packageRight.base packageRight rfl
    letI : (refinementPackageProjection U).IsStronglyCartesian
        pulledLeg.base.base pulledLeg.base :=
      UpperGeometryCleavage.pulledRouteGeometryBase_isStronglyCartesian
        (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
        (input.sourceTargetGeometryAt i)
    apply CategoryTheory.Functor.IsStronglyCartesian.ext
      (refinementPackageProjection U)
      pulledLeg.base.base pulledLeg.base packageRight.base
    exact congrArg RefinementGeometryHom.base hafterLeg'
  letI hleftLift :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
      right.base left hleftBase
  letI hrightLift :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
      right.base right rfl
  letI := input.generatedPulledRouteLegAt_isStronglyCartesian i
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (refinementGeometryProjection U)
    pulledLeg.base pulledLeg right.base
  exact hafterLeg'

/-- Relation on two source endpoint changes obtained by testing their
generated images in the actual comparison subgroup. -/
noncomputable def GeneratedQualifiedComparisonRelation
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex)
    (baseChange pulledChange :
      CompositeFiberAut (input.sourceGeometry i).package) : Prop :=
  (input.generatedBaseCompositeFiberAutHomAt i baseChange,
      input.generatedPulledCompositeFiberAutHomAt i pulledChange) ∈
    qualifiedComparisonSubgroup
      (input.generatedCompatibleUpperGeometryMateAt i)

/-- Every source change lies on the diagonal of the generated comparison
relation. -/
theorem generatedQualifiedComparisonRelation_diagonal
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    input.GeneratedQualifiedComparisonRelation i automorphism automorphism :=
  input.generatedCompatibleUpperGeometryMateAt_automorphism_intertwining
    i automorphism

/-- Source changes whose generated pulled image becomes invisible after the
generated comparison. -/
noncomputable def generatedPulledComparisonKernel
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex) :
    Subgroup (CompositeFiberAut (input.sourceGeometry i).package) :=
  Subgroup.comap (input.generatedPulledCompositeFiberAutHomAt i)
    (qualifiedComparisonTargetStabilizer
      (input.generatedCompatibleUpperGeometryMateAt i))

/-- A generated pair preserves the mate exactly when its pulled source change
differs from the base source change by the residual pulled kernel. -/
theorem generatedQualifiedComparisonRelation_iff_difference_mem
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex)
    (baseChange pulledChange :
      CompositeFiberAut (input.sourceGeometry i).package) :
    input.GeneratedQualifiedComparisonRelation i baseChange pulledChange ↔
      pulledChange * baseChange⁻¹ ∈
        input.generatedPulledComparisonKernel i := by
  let baseImage := input.generatedBaseCompositeFiberAutHomAt i baseChange
  let diagonalPulled :=
    input.generatedPulledCompositeFiberAutHomAt i baseChange
  let pulledImage :=
    input.generatedPulledCompositeFiberAutHomAt i pulledChange
  let comparison := input.generatedCompatibleUpperGeometryMateAt i
  have diagonalRelation :
      (baseImage, diagonalPulled) ∈ qualifiedComparisonSubgroup comparison :=
    input.generatedQualifiedComparisonRelation_diagonal i baseChange
  constructor
  · intro relation
    have relation' :
        (baseImage, pulledImage) ∈ qualifiedComparisonSubgroup comparison :=
      relation
    have diagonalInverse :=
      (qualifiedComparisonSubgroup comparison).inv_mem diagonalRelation
    have diagonalInverseRelation :
        (show _ ⟶ _ from baseImage.1.inv) ≫ comparison =
          comparison ≫ diagonalPulled.1.inv := diagonalInverse
    have relationEquation :
        (show _ ⟶ _ from baseImage.1.hom) ≫ comparison =
          comparison ≫ pulledImage.1.hom := relation'
    change input.generatedPulledCompositeFiberAutHomAt i
        (pulledChange * baseChange⁻¹) ∈
      qualifiedComparisonTargetStabilizer comparison
    rw [map_mul, map_inv]
    change comparison ≫
        (diagonalPulled.1.inv ≫ pulledImage.1.hom) = comparison
    calc
      comparison ≫ (diagonalPulled.1.inv ≫ pulledImage.1.hom) =
          (comparison ≫ diagonalPulled.1.inv) ≫ pulledImage.1.hom := by simp
      _ = (baseImage.1.inv ≫ comparison) ≫ pulledImage.1.hom := by
        rw [diagonalInverseRelation]
      _ = baseImage.1.inv ≫ (comparison ≫ pulledImage.1.hom) :=
        Category.assoc _ _ _
      _ = baseImage.1.inv ≫ (baseImage.1.hom ≫ comparison) := by
        rw [relationEquation]
      _ = comparison := by simp
  · intro differenceMem
    let difference : qualifiedComparisonTargetStabilizer comparison :=
      ⟨input.generatedPulledCompositeFiberAutHomAt i
          (pulledChange * baseChange⁻¹), differenceMem⟩
    let diagonalLift : QualifiedComparisonTargetLift comparison baseImage :=
      ⟨diagonalPulled, diagonalRelation⟩
    have actedRelation := (difference • diagonalLift).2
    have actedValue : difference.1 * diagonalPulled = pulledImage := by
      change
        input.generatedPulledCompositeFiberAutHomAt i
              (pulledChange * baseChange⁻¹) *
            input.generatedPulledCompositeFiberAutHomAt i baseChange =
          input.generatedPulledCompositeFiberAutHomAt i pulledChange
      rw [map_mul, map_inv]
      simp
    change (baseImage, pulledImage) ∈ qualifiedComparisonSubgroup comparison
    change (baseImage, difference.1 * diagonalPulled) ∈
      qualifiedComparisonSubgroup comparison at actedRelation
    rw [actedValue] at actedRelation
    exact actedRelation

/-- Membership in the generated relation is equivalent to the corresponding
generated pulled-image difference lying in the actual target stabilizer. -/
theorem generatedQualifiedComparisonRelation_iff_target_stabilizer_image
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex)
    (baseChange pulledChange :
      CompositeFiberAut (input.sourceGeometry i).package) :
    input.GeneratedQualifiedComparisonRelation i baseChange pulledChange ↔
      input.generatedPulledCompositeFiberAutHomAt i pulledChange *
          (input.generatedPulledCompositeFiberAutHomAt i baseChange)⁻¹ ∈
        qualifiedComparisonTargetStabilizer
          (input.generatedCompatibleUpperGeometryMateAt i) := by
  rw [input.generatedQualifiedComparisonRelation_iff_difference_mem]
  change input.generatedPulledCompositeFiberAutHomAt i
      (pulledChange * baseChange⁻¹) ∈
        qualifiedComparisonTargetStabilizer
          (input.generatedCompatibleUpperGeometryMateAt i) ↔ _
  rw [map_mul, map_inv]

/-- Membership in the generated relation is the residual subgroup condition
on the literal source difference. -/
theorem generatedQualifiedComparisonRelation_iff_kernel_mem
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex)
    (baseChange pulledChange :
      CompositeFiberAut (input.sourceGeometry i).package) :
    input.GeneratedQualifiedComparisonRelation i baseChange pulledChange ↔
      pulledChange * baseChange⁻¹ ∈
        input.generatedPulledComparisonKernel i :=
  input.generatedQualifiedComparisonRelation_iff_difference_mem
    i baseChange pulledChange

/-- All pulled source changes over a fixed base source change form the right
coset of the generated residual subgroup. -/
theorem generatedQualifiedComparisonRelation_iff_exists_kernel_factor
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex)
    (baseChange pulledChange :
      CompositeFiberAut (input.sourceGeometry i).package) :
    input.GeneratedQualifiedComparisonRelation i baseChange pulledChange ↔
      ∃ residual : input.generatedPulledComparisonKernel i,
        pulledChange = residual.1 * baseChange := by
  rw [input.generatedQualifiedComparisonRelation_iff_kernel_mem]
  constructor
  · intro differenceMem
    refine ⟨⟨pulledChange * baseChange⁻¹, differenceMem⟩, ?_⟩
    simp
  · rintro ⟨residual, rfl⟩
    simpa only [mul_inv_cancel_right] using residual.2

end UpperGeometryCompatibleProblemInputData

namespace UpperDecisionWitness

/-- The generated comparison relation has a concrete negative instance: the
named generated base comparator is not compatible with the identity pulled
source change. -/
theorem generatedQualifiedComparisonRelation_base_identity_not :
    ¬ problem.data.GeneratedQualifiedComparisonRelation PUnit.unit
      (problem.data.sourceTransport.comparator DecisionCell.comparison) 1 := by
  simpa [UpperGeometryCompatibleProblemInputData.GeneratedQualifiedComparisonRelation,
    qualifiedComparisonSubgroup, UpperComparatorDescentAt,
    UpperGeometryCompatibleProblemInputData.generatedBaseRouteComparator,
    UpperGeometryCompatibleProblemInputData.generatedPulledIdentityComparatorTransport,
    solution,
    UpperGeometryCompatibleProblemInputData.generatedGeometryCompatibleUpperRefinementBCSolution]
    using generatedBaseIdentityPair_not_comparatorDescentAt

end UpperDecisionWitness

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
