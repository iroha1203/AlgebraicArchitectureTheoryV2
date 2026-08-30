import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleComparator

/-!
# Geometry stage of compatible comparator pullback

This module completes the second stage of the revision-4 G-115 comparator
construction.  For each generated route, it uses the exact package factor
from the first stage as the lower morphism for the strongly Cartesian
geometry pullback.  The resulting complete refinement-geometry factor is
then exactified to a `GeometryTotalHom`.

The group laws and the resulting `CompositeFiberAut` structures are kept as
successor obligations.  The declarations here expose the two factorization
laws needed to prove those laws by Cartesian uniqueness.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

namespace UpperGeometryCompatibleProblemInputData

/-- Base-route geometry candidate obtained by following the generated leg
with the complete source automorphism. -/
noncomputable def generatedBaseGeometryComparatorCandidateAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    RefinementGeometryHom (input.generatedBaseRouteGeometryAt i)
      (input.sourceGeometry i).package :=
  (input.generatedBaseRouteLegAt i).comp
    ((exactGeometryToRefinementGeometry U).map
      (CompositeFiberAut.hom automorphism))

/-- The base-route geometry candidate lies over the first-stage exact package
factor followed by the generated package leg. -/
theorem generatedBaseGeometryComparatorCandidateAt_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (input.generatedBaseGeometryComparatorCandidateAt i automorphism).base =
      ((exactPackageToRefinement U).map
        (input.generatedBasePackageComparatorAt i automorphism)).comp
        (input.generatedBaseRouteLegAt i).base := by
  rw [input.generatedBasePackageComparatorAt_toRefinement i automorphism]
  exact (input.generatedBasePackageComparatorRefinementAt_fac
    i automorphism).symm

/-- Universal geometry-stage pullback of a source automorphism along the
generated base-first route. -/
noncomputable def generatedBaseGeometryComparatorRefinementAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    RefinementGeometryHom (input.generatedBaseRouteGeometryAt i)
      (input.generatedBaseRouteGeometryAt i) := by
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      (input.generatedBaseRouteLegAt i).base
      (input.generatedBaseRouteLegAt i) :=
    input.generatedBaseRouteLegAt_isStronglyCartesian i
  let candidate := input.generatedBaseGeometryComparatorCandidateAt i automorphism
  letI := UpperGeometryCleavage.refinementGeometryHom_isHomLift candidate
  exact CategoryTheory.Functor.IsStronglyCartesian.map
    (refinementGeometryProjection U)
    (input.generatedBaseRouteLegAt i).base
    (input.generatedBaseRouteLegAt i)
    (g := (exactPackageToRefinement U).map
      (input.generatedBasePackageComparatorAt i automorphism))
    (input.generatedBaseGeometryComparatorCandidateAt_base i automorphism)
    candidate

/-- The base-route geometry pullback satisfies its defining factorization. -/
theorem generatedBaseGeometryComparatorRefinementAt_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (input.generatedBaseGeometryComparatorRefinementAt i automorphism).comp
        (input.generatedBaseRouteLegAt i) =
      input.generatedBaseGeometryComparatorCandidateAt i automorphism := by
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      (input.generatedBaseRouteLegAt i).base
      (input.generatedBaseRouteLegAt i) :=
    input.generatedBaseRouteLegAt_isStronglyCartesian i
  let candidate := input.generatedBaseGeometryComparatorCandidateAt i automorphism
  letI := UpperGeometryCleavage.refinementGeometryHom_isHomLift candidate
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (refinementGeometryProjection U)
    (input.generatedBaseRouteLegAt i).base
    (input.generatedBaseRouteLegAt i)
    (input.generatedBaseGeometryComparatorCandidateAt_base i automorphism)
    candidate

/-- The universal base-route geometry factor projects to the exact package
factor constructed in the first stage. -/
theorem generatedBaseGeometryComparatorRefinementAt_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (input.generatedBaseGeometryComparatorRefinementAt i automorphism).base =
      (exactPackageToRefinement U).map
        (input.generatedBasePackageComparatorAt i automorphism) := by
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      (input.generatedBaseRouteLegAt i).base
      (input.generatedBaseRouteLegAt i) :=
    input.generatedBaseRouteLegAt_isStronglyCartesian i
  let candidate := input.generatedBaseGeometryComparatorCandidateAt i automorphism
  letI := UpperGeometryCleavage.refinementGeometryHom_isHomLift candidate
  unfold generatedBaseGeometryComparatorRefinementAt
  exact (CategoryTheory.IsHomLift.eq_of_isHomLift
    (refinementGeometryProjection U)
    ((exactPackageToRefinement U).map
      (input.generatedBasePackageComparatorAt i automorphism))
    (CategoryTheory.Functor.IsStronglyCartesian.map
      (refinementGeometryProjection U)
      (input.generatedBaseRouteLegAt i).base
      (input.generatedBaseRouteLegAt i)
      (input.generatedBaseGeometryComparatorCandidateAt_base i automorphism)
      candidate)).symm

/-- Exact geometry endomorphism underlying the base-route pullback. -/
noncomputable def generatedBaseGeometryComparatorAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    GeometryTotalHom (input.generatedBaseRouteGeometryAt i)
      (input.generatedBaseRouteGeometryAt i) :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement
    (input.generatedBasePackageComparatorAt i automorphism)
    (input.generatedBaseGeometryComparatorRefinementAt i automorphism)
    (input.generatedBaseGeometryComparatorRefinementAt_base i automorphism)

/-- Exact embedding recovers the universal base-route geometry factor. -/
theorem generatedBaseGeometryComparatorAt_toRefinement
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (exactGeometryToRefinementGeometry U).map
        (input.generatedBaseGeometryComparatorAt i automorphism) =
      input.generatedBaseGeometryComparatorRefinementAt i automorphism := by
  exact UpperGeometryCleavage.exactGeometryHomOfRefinement_toRefinement _ _ _

/-- The exact base-route geometry factor retains the universal
factorization against the literal generated route leg. -/
theorem generatedBaseGeometryComparatorAt_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    ((exactGeometryToRefinementGeometry U).map
      (input.generatedBaseGeometryComparatorAt i automorphism)).comp
        (input.generatedBaseRouteLegAt i) =
      input.generatedBaseGeometryComparatorCandidateAt i automorphism := by
  rw [input.generatedBaseGeometryComparatorAt_toRefinement i automorphism]
  exact input.generatedBaseGeometryComparatorRefinementAt_fac i automorphism

/-- The first-stage base-route factors of a source automorphism and its
inverse compose to the identity. -/
theorem generatedBasePackageComparatorRefinementAt_hom_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    input.generatedBasePackageComparatorRefinementAt i automorphism ≫
        input.generatedBasePackageComparatorRefinementAt i automorphism⁻¹ =
      𝟙 (⟨(input.generatedBaseRouteGeometryAt i).core⟩ :
        RefinementPackageObject U) := by
  let vertical := (exactPointedToRefinement U).map
    (PackageTotalHom.id (input.generatedBaseRouteGeometryAt i).core).base
  let refId := 𝟙 ((exactPointedToRefinement U).obj
    (packagePoint (input.generatedBaseRouteGeometryAt i).core))
  have hvertical : vertical = refId := by
    change (exactPointedToRefinement U).map (𝟙 _) = 𝟙 _
    exact (exactPointedToRefinement U).map_id _
  letI hcomp : (refinementPackageProjection U).IsHomLift
      refId
      (input.generatedBasePackageComparatorRefinementAt i automorphism ≫
        input.generatedBasePackageComparatorRefinementAt i automorphism⁻¹) :=
    UpperGeometryCleavage.refinementPackageHom_isHomLift_of_base_eq _ _ (by
      change (input.generatedBasePackageComparatorRefinementAt
          i automorphism).base.comp
        (input.generatedBasePackageComparatorRefinementAt
          i automorphism⁻¹).base = _
      rw [input.generatedBasePackageComparatorRefinementAt_base,
        input.generatedBasePackageComparatorRefinementAt_base]
      change vertical.comp vertical = refId
      rw [hvertical]
      change refId ≫ refId = refId
      exact Category.comp_id _)
  letI hid : (refinementPackageProjection U).IsHomLift
      refId
      (𝟙 (⟨(input.generatedBaseRouteGeometryAt i).core⟩ :
        RefinementPackageObject U)) := by
    apply UpperGeometryCleavage.refinementPackageHom_isHomLift_of_base_eq
    rfl
  letI : (refinementPackageProjection U).IsStronglyCartesian
      (input.generatedBaseRouteLegAt i).base.base
      (input.generatedBaseRouteLegAt i).base :=
    UpperGeometryCleavage.baseRouteGeometryBase_isStronglyCartesian
      (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
      (input.sourceTargetGeometryAt i)
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (refinementPackageProjection U)
    (input.generatedBaseRouteLegAt i).base.base
    (input.generatedBaseRouteLegAt i).base
    refId
  calc
    (input.generatedBasePackageComparatorRefinementAt i automorphism ≫
        input.generatedBasePackageComparatorRefinementAt i automorphism⁻¹) ≫
        (input.generatedBaseRouteLegAt i).base =
      input.generatedBasePackageComparatorRefinementAt i automorphism ≫
        (input.generatedBasePackageComparatorRefinementAt i automorphism⁻¹ ≫
          (input.generatedBaseRouteLegAt i).base) := Category.assoc _ _ _
    _ = input.generatedBasePackageComparatorRefinementAt i automorphism ≫
        input.generatedBasePackageComparatorCandidateAt i automorphism⁻¹ := by
      exact congrArg
        (fun leg : RefinementPackageHom
            ⟨(input.generatedBaseRouteGeometryAt i).core⟩
            ⟨(input.sourceGeometry i).package.core⟩ =>
          (input.generatedBasePackageComparatorRefinementAt
            i automorphism).comp leg)
        (input.generatedBasePackageComparatorRefinementAt_fac
          i automorphism⁻¹)
    _ = (input.generatedBasePackageComparatorRefinementAt i automorphism ≫
          (input.generatedBaseRouteLegAt i).base) ≫
        (exactPackageToRefinement U).map
          (CompositeFiberAut.inv automorphism).base := by
      change (input.generatedBasePackageComparatorRefinementAt
          i automorphism).comp
          ((input.generatedBaseRouteLegAt i).base.comp
            ((exactPackageToRefinement U).map
              (CompositeFiberAut.inv automorphism).base)) =
        ((input.generatedBasePackageComparatorRefinementAt
          i automorphism).comp (input.generatedBaseRouteLegAt i).base).comp
            ((exactPackageToRefinement U).map
              (CompositeFiberAut.inv automorphism).base)
      exact (@Category.assoc
        (RefinementPackageTotalCategory U)
        (refinementPackageTotalCategory U) _ _ _ _
        (input.generatedBasePackageComparatorRefinementAt i automorphism)
        (input.generatedBaseRouteLegAt i).base
        ((exactPackageToRefinement U).map
          (CompositeFiberAut.inv automorphism).base)).symm
    _ = input.generatedBasePackageComparatorCandidateAt i automorphism ≫
        (exactPackageToRefinement U).map
          (CompositeFiberAut.inv automorphism).base := by
      exact congrArg
        (fun leg : RefinementPackageHom
            ⟨(input.generatedBaseRouteGeometryAt i).core⟩
            ⟨(input.sourceGeometry i).package.core⟩ =>
          leg.comp ((exactPackageToRefinement U).map
            (CompositeFiberAut.inv automorphism).base))
        (input.generatedBasePackageComparatorRefinementAt_fac
          i automorphism)
    _ = (input.generatedBaseRouteLegAt i).base ≫
        ((exactPackageToRefinement U).map
          (CompositeFiberAut.hom automorphism).base ≫
        (exactPackageToRefinement U).map
          (CompositeFiberAut.inv automorphism).base) := Category.assoc _ _ _
    _ = (input.generatedBaseRouteLegAt i).base := by
      rw [← Functor.map_comp]
      have h := congrArg GeometryTotalHom.base automorphism.1.hom_inv_id
      change (CompositeFiberAut.hom automorphism).base ≫
          (CompositeFiberAut.inv automorphism).base =
        𝟙 (input.sourceGeometry i).package.core at h
      rw [h, (exactPackageToRefinement U).map_id, Category.comp_id]
    _ = (𝟙 (⟨(input.generatedBaseRouteGeometryAt i).core⟩ :
          RefinementPackageObject U)) ≫
        (input.generatedBaseRouteLegAt i).base := by
      rw [Category.id_comp]

/-- The first-stage base-route inverse factor followed by the forward factor
also composes to the identity. -/
theorem generatedBasePackageComparatorRefinementAt_inv_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    input.generatedBasePackageComparatorRefinementAt i automorphism⁻¹ ≫
        input.generatedBasePackageComparatorRefinementAt i automorphism =
      𝟙 (⟨(input.generatedBaseRouteGeometryAt i).core⟩ :
        RefinementPackageObject U) := by
  simpa using input.generatedBasePackageComparatorRefinementAt_hom_inv
    i automorphism⁻¹

/-- Exact base-route package factors preserve the source inverse law. -/
theorem generatedBasePackageComparatorAt_hom_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    input.generatedBasePackageComparatorAt i automorphism ≫
        input.generatedBasePackageComparatorAt i automorphism⁻¹ =
      𝟙 (input.generatedBaseRouteGeometryAt i).core := by
  apply exactPackageToRefinement_map_injective
  rw [Functor.map_comp, input.generatedBasePackageComparatorAt_toRefinement,
    input.generatedBasePackageComparatorAt_toRefinement,
    (exactPackageToRefinement U).map_id]
  exact input.generatedBasePackageComparatorRefinementAt_hom_inv i automorphism

/-- Exact base-route package factors preserve the reverse inverse law. -/
theorem generatedBasePackageComparatorAt_inv_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    input.generatedBasePackageComparatorAt i automorphism⁻¹ ≫
        input.generatedBasePackageComparatorAt i automorphism =
      𝟙 (input.generatedBaseRouteGeometryAt i).core := by
  simpa using input.generatedBasePackageComparatorAt_hom_inv i automorphism⁻¹

/-- The geometry-stage base-route factors of a source automorphism and its
inverse compose to the identity. -/
theorem generatedBaseGeometryComparatorRefinementAt_hom_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (input.generatedBaseGeometryComparatorRefinementAt i automorphism).comp
        (input.generatedBaseGeometryComparatorRefinementAt i automorphism⁻¹) =
      𝟙 (⟨input.generatedBaseRouteGeometryAt i⟩ :
        RefinementGeometryObject U) := by
  let packageId := 𝟙 (⟨(input.generatedBaseRouteGeometryAt i).core⟩ :
    RefinementPackageObject U)
  letI hcomp : (refinementGeometryProjection U).IsHomLift packageId
      ((input.generatedBaseGeometryComparatorRefinementAt i automorphism).comp
        (input.generatedBaseGeometryComparatorRefinementAt i automorphism⁻¹)) :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq _ _ (by
      change (input.generatedBaseGeometryComparatorRefinementAt
          i automorphism).base.comp
        (input.generatedBaseGeometryComparatorRefinementAt
          i automorphism⁻¹).base = packageId
      rw [input.generatedBaseGeometryComparatorRefinementAt_base,
        input.generatedBaseGeometryComparatorRefinementAt_base]
      exact congrArg
        (fun hom : PackageTotalHom
            (input.generatedBaseRouteGeometryAt i).core
            (input.generatedBaseRouteGeometryAt i).core =>
          (exactPackageToRefinement U).map hom)
        (input.generatedBasePackageComparatorAt_hom_inv i automorphism))
  letI hid : (refinementGeometryProjection U).IsHomLift packageId
      (𝟙 (⟨input.generatedBaseRouteGeometryAt i⟩ :
        RefinementGeometryObject U)) := by
    apply UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
    rfl
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      (input.generatedBaseRouteLegAt i).base
      (input.generatedBaseRouteLegAt i) :=
    input.generatedBaseRouteLegAt_isStronglyCartesian i
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (refinementGeometryProjection U)
    (input.generatedBaseRouteLegAt i).base
    (input.generatedBaseRouteLegAt i)
    packageId
  calc
    (input.generatedBaseGeometryComparatorRefinementAt i automorphism ≫
        input.generatedBaseGeometryComparatorRefinementAt i automorphism⁻¹) ≫
        input.generatedBaseRouteLegAt i =
      input.generatedBaseGeometryComparatorRefinementAt i automorphism ≫
        (input.generatedBaseGeometryComparatorRefinementAt i automorphism⁻¹ ≫
          input.generatedBaseRouteLegAt i) := Category.assoc _ _ _
    _ = input.generatedBaseGeometryComparatorRefinementAt i automorphism ≫
        input.generatedBaseGeometryComparatorCandidateAt i automorphism⁻¹ := by
      exact congrArg
        (fun leg : RefinementGeometryHom
            (input.generatedBaseRouteGeometryAt i)
            (input.sourceGeometry i).package =>
          (input.generatedBaseGeometryComparatorRefinementAt
            i automorphism).comp leg)
        (input.generatedBaseGeometryComparatorRefinementAt_fac
          i automorphism⁻¹)
    _ = (input.generatedBaseGeometryComparatorRefinementAt i automorphism ≫
          input.generatedBaseRouteLegAt i) ≫
        (exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.inv automorphism) := by
      change (input.generatedBaseGeometryComparatorRefinementAt
          i automorphism).comp
          ((input.generatedBaseRouteLegAt i).comp
            ((exactGeometryToRefinementGeometry U).map
              (CompositeFiberAut.inv automorphism))) =
        ((input.generatedBaseGeometryComparatorRefinementAt
          i automorphism).comp (input.generatedBaseRouteLegAt i)).comp
            ((exactGeometryToRefinementGeometry U).map
              (CompositeFiberAut.inv automorphism))
      exact (@Category.assoc
        (RefinementGeometryCategory.{u, v} U)
        (refinementGeometryCategory U) _ _ _ _
        (input.generatedBaseGeometryComparatorRefinementAt i automorphism)
        (input.generatedBaseRouteLegAt i)
        ((exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.inv automorphism))).symm
    _ = input.generatedBaseGeometryComparatorCandidateAt i automorphism ≫
        (exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.inv automorphism) := by
      exact congrArg
        (fun leg : RefinementGeometryHom
            (input.generatedBaseRouteGeometryAt i)
            (input.sourceGeometry i).package =>
          leg.comp ((exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.inv automorphism)))
        (input.generatedBaseGeometryComparatorRefinementAt_fac
          i automorphism)
    _ = input.generatedBaseRouteLegAt i ≫
        ((exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom automorphism) ≫
        (exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.inv automorphism)) := Category.assoc _ _ _
    _ = input.generatedBaseRouteLegAt i := by
      rw [← Functor.map_comp]
      have hsource : CompositeFiberAut.hom automorphism ≫
          CompositeFiberAut.inv automorphism =
        𝟙 (input.sourceGeometry i).package := automorphism.1.hom_inv_id
      rw [hsource, (exactGeometryToRefinementGeometry U).map_id,
        Category.comp_id]
    _ = (𝟙 (⟨input.generatedBaseRouteGeometryAt i⟩ :
          RefinementGeometryObject U)) ≫
        input.generatedBaseRouteLegAt i := by
      exact (@Category.id_comp
        (RefinementGeometryCategory.{u, v} U)
        (refinementGeometryCategory U) _ _
        (input.generatedBaseRouteLegAt i)).symm

/-- The reverse geometry-stage base-route composition is also the identity. -/
theorem generatedBaseGeometryComparatorRefinementAt_inv_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (input.generatedBaseGeometryComparatorRefinementAt i automorphism⁻¹).comp
        (input.generatedBaseGeometryComparatorRefinementAt i automorphism) =
      𝟙 (⟨input.generatedBaseRouteGeometryAt i⟩ :
        RefinementGeometryObject U) := by
  simpa using input.generatedBaseGeometryComparatorRefinementAt_hom_inv
    i automorphism⁻¹

/-- Exact base-route geometry factors preserve the source inverse law. -/
theorem generatedBaseGeometryComparatorAt_hom_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (input.generatedBaseGeometryComparatorAt i automorphism).comp
        (input.generatedBaseGeometryComparatorAt i automorphism⁻¹) =
      𝟙 (input.generatedBaseRouteGeometryAt i) := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  change (exactGeometryToRefinementGeometry U).map
      (input.generatedBaseGeometryComparatorAt i automorphism ≫
        input.generatedBaseGeometryComparatorAt i automorphism⁻¹) =
    (exactGeometryToRefinementGeometry U).map
      (𝟙 (input.generatedBaseRouteGeometryAt i))
  rw [Functor.map_comp, input.generatedBaseGeometryComparatorAt_toRefinement,
    input.generatedBaseGeometryComparatorAt_toRefinement,
    (exactGeometryToRefinementGeometry U).map_id]
  exact input.generatedBaseGeometryComparatorRefinementAt_hom_inv i automorphism

/-- Exact base-route geometry factors preserve the reverse inverse law. -/
theorem generatedBaseGeometryComparatorAt_inv_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (input.generatedBaseGeometryComparatorAt i automorphism⁻¹).comp
        (input.generatedBaseGeometryComparatorAt i automorphism) =
      𝟙 (input.generatedBaseRouteGeometryAt i) := by
  simpa using input.generatedBaseGeometryComparatorAt_hom_inv i automorphism⁻¹

/-- Generated composite-fiber automorphism on the base-first route. -/
noncomputable def generatedBaseCompositeFiberAutAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    CompositeFiberAut (input.generatedBaseRouteGeometryAt i) :=
  ⟨{
    hom := input.generatedBaseGeometryComparatorAt i automorphism
    inv := input.generatedBaseGeometryComparatorAt i automorphism⁻¹
    hom_inv_id := input.generatedBaseGeometryComparatorAt_hom_inv i automorphism
    inv_hom_id := input.generatedBaseGeometryComparatorAt_inv_hom i automorphism
  }, by
    change (input.generatedBasePackageComparatorAt i automorphism).base =
      𝟙 (packagePoint (input.generatedBaseRouteGeometryAt i).core)
    rfl⟩

/-- The generated base-route automorphism has the exact pulled-back forward
geometry factor. -/
@[simp] theorem generatedBaseCompositeFiberAutAt_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    CompositeFiberAut.hom
      (input.generatedBaseCompositeFiberAutAt i automorphism) =
      input.generatedBaseGeometryComparatorAt i automorphism := rfl

/-- The generated base-route automorphism has the exact pulled-back inverse
geometry factor. -/
@[simp] theorem generatedBaseCompositeFiberAutAt_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    CompositeFiberAut.inv
      (input.generatedBaseCompositeFiberAutAt i automorphism) =
      input.generatedBaseGeometryComparatorAt i automorphism⁻¹ := rfl

/-- The generated base-route automorphism satisfies the Cartesian pullback
factorization against the literal route leg. -/
theorem generatedBaseCompositeFiberAutAt_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    ((exactGeometryToRefinementGeometry U).map
      (CompositeFiberAut.hom
        (input.generatedBaseCompositeFiberAutAt i automorphism))).comp
        (input.generatedBaseRouteLegAt i) =
      input.generatedBaseGeometryComparatorCandidateAt i automorphism := by
  rw [input.generatedBaseCompositeFiberAutAt_hom]
  exact input.generatedBaseGeometryComparatorAt_fac i automorphism

/-- Pulled-route geometry candidate obtained by following the generated leg
with the complete source automorphism. -/
noncomputable def generatedPulledGeometryComparatorCandidateAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    RefinementGeometryHom (input.generatedPulledRouteGeometryAt i)
      (input.sourceGeometry i).package :=
  (input.generatedPulledRouteLegAt i).comp
    ((exactGeometryToRefinementGeometry U).map
      (CompositeFiberAut.hom automorphism))

/-- The pulled-route geometry candidate lies over the first-stage exact
package factor followed by the generated package leg. -/
theorem generatedPulledGeometryComparatorCandidateAt_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (input.generatedPulledGeometryComparatorCandidateAt i automorphism).base =
      ((exactPackageToRefinement U).map
        (input.generatedPulledPackageComparatorAt i automorphism)).comp
        (input.generatedPulledRouteLegAt i).base := by
  rw [input.generatedPulledPackageComparatorAt_toRefinement i automorphism]
  exact (input.generatedPulledPackageComparatorRefinementAt_fac
    i automorphism).symm

/-- Universal geometry-stage pullback of a source automorphism along the
generated pulled-first route. -/
noncomputable def generatedPulledGeometryComparatorRefinementAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    RefinementGeometryHom (input.generatedPulledRouteGeometryAt i)
      (input.generatedPulledRouteGeometryAt i) := by
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      (input.generatedPulledRouteLegAt i).base
      (input.generatedPulledRouteLegAt i) :=
    input.generatedPulledRouteLegAt_isStronglyCartesian i
  let candidate := input.generatedPulledGeometryComparatorCandidateAt i automorphism
  letI := UpperGeometryCleavage.refinementGeometryHom_isHomLift candidate
  exact CategoryTheory.Functor.IsStronglyCartesian.map
    (refinementGeometryProjection U)
    (input.generatedPulledRouteLegAt i).base
    (input.generatedPulledRouteLegAt i)
    (g := (exactPackageToRefinement U).map
      (input.generatedPulledPackageComparatorAt i automorphism))
    (input.generatedPulledGeometryComparatorCandidateAt_base i automorphism)
    candidate

/-- The pulled-route geometry pullback satisfies its defining
factorization. -/
theorem generatedPulledGeometryComparatorRefinementAt_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (input.generatedPulledGeometryComparatorRefinementAt i automorphism).comp
        (input.generatedPulledRouteLegAt i) =
      input.generatedPulledGeometryComparatorCandidateAt i automorphism := by
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      (input.generatedPulledRouteLegAt i).base
      (input.generatedPulledRouteLegAt i) :=
    input.generatedPulledRouteLegAt_isStronglyCartesian i
  let candidate := input.generatedPulledGeometryComparatorCandidateAt i automorphism
  letI := UpperGeometryCleavage.refinementGeometryHom_isHomLift candidate
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (refinementGeometryProjection U)
    (input.generatedPulledRouteLegAt i).base
    (input.generatedPulledRouteLegAt i)
    (input.generatedPulledGeometryComparatorCandidateAt_base i automorphism)
    candidate

/-- The universal pulled-route geometry factor projects to the exact package
factor constructed in the first stage. -/
theorem generatedPulledGeometryComparatorRefinementAt_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (input.generatedPulledGeometryComparatorRefinementAt i automorphism).base =
      (exactPackageToRefinement U).map
        (input.generatedPulledPackageComparatorAt i automorphism) := by
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      (input.generatedPulledRouteLegAt i).base
      (input.generatedPulledRouteLegAt i) :=
    input.generatedPulledRouteLegAt_isStronglyCartesian i
  let candidate := input.generatedPulledGeometryComparatorCandidateAt i automorphism
  letI := UpperGeometryCleavage.refinementGeometryHom_isHomLift candidate
  unfold generatedPulledGeometryComparatorRefinementAt
  exact (CategoryTheory.IsHomLift.eq_of_isHomLift
    (refinementGeometryProjection U)
    ((exactPackageToRefinement U).map
      (input.generatedPulledPackageComparatorAt i automorphism))
    (CategoryTheory.Functor.IsStronglyCartesian.map
      (refinementGeometryProjection U)
      (input.generatedPulledRouteLegAt i).base
      (input.generatedPulledRouteLegAt i)
      (input.generatedPulledGeometryComparatorCandidateAt_base i automorphism)
      candidate)).symm

/-- Exact geometry endomorphism underlying the pulled-route pullback. -/
noncomputable def generatedPulledGeometryComparatorAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    GeometryTotalHom (input.generatedPulledRouteGeometryAt i)
      (input.generatedPulledRouteGeometryAt i) :=
  UpperGeometryCleavage.exactGeometryHomOfRefinement
    (input.generatedPulledPackageComparatorAt i automorphism)
    (input.generatedPulledGeometryComparatorRefinementAt i automorphism)
    (input.generatedPulledGeometryComparatorRefinementAt_base i automorphism)

/-- Exact embedding recovers the universal pulled-route geometry factor. -/
theorem generatedPulledGeometryComparatorAt_toRefinement
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (exactGeometryToRefinementGeometry U).map
        (input.generatedPulledGeometryComparatorAt i automorphism) =
      input.generatedPulledGeometryComparatorRefinementAt i automorphism := by
  exact UpperGeometryCleavage.exactGeometryHomOfRefinement_toRefinement _ _ _

/-- The exact pulled-route geometry factor retains the universal
factorization against the literal generated route leg. -/
theorem generatedPulledGeometryComparatorAt_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    ((exactGeometryToRefinementGeometry U).map
      (input.generatedPulledGeometryComparatorAt i automorphism)).comp
        (input.generatedPulledRouteLegAt i) =
      input.generatedPulledGeometryComparatorCandidateAt i automorphism := by
  rw [input.generatedPulledGeometryComparatorAt_toRefinement i automorphism]
  exact input.generatedPulledGeometryComparatorRefinementAt_fac i automorphism

/-- The first-stage pulled-route factors of a source automorphism and its
inverse compose to the identity. -/
theorem generatedPulledPackageComparatorRefinementAt_hom_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    input.generatedPulledPackageComparatorRefinementAt i automorphism ≫
        input.generatedPulledPackageComparatorRefinementAt i automorphism⁻¹ =
      𝟙 (⟨(input.generatedPulledRouteGeometryAt i).core⟩ :
        RefinementPackageObject U) := by
  let vertical := (exactPointedToRefinement U).map
    (PackageTotalHom.id (input.generatedPulledRouteGeometryAt i).core).base
  let refId := 𝟙 ((exactPointedToRefinement U).obj
    (packagePoint (input.generatedPulledRouteGeometryAt i).core))
  have hvertical : vertical = refId := by
    change (exactPointedToRefinement U).map (𝟙 _) = 𝟙 _
    exact (exactPointedToRefinement U).map_id _
  letI hcomp : (refinementPackageProjection U).IsHomLift refId
      (input.generatedPulledPackageComparatorRefinementAt i automorphism ≫
        input.generatedPulledPackageComparatorRefinementAt i automorphism⁻¹) :=
    UpperGeometryCleavage.refinementPackageHom_isHomLift_of_base_eq _ _ (by
      change (input.generatedPulledPackageComparatorRefinementAt
          i automorphism).base.comp
        (input.generatedPulledPackageComparatorRefinementAt
          i automorphism⁻¹).base = _
      rw [input.generatedPulledPackageComparatorRefinementAt_base,
        input.generatedPulledPackageComparatorRefinementAt_base]
      change vertical.comp vertical = refId
      rw [hvertical]
      change refId ≫ refId = refId
      exact Category.comp_id _)
  letI hid : (refinementPackageProjection U).IsHomLift refId
      (𝟙 (⟨(input.generatedPulledRouteGeometryAt i).core⟩ :
        RefinementPackageObject U)) := by
    apply UpperGeometryCleavage.refinementPackageHom_isHomLift_of_base_eq
    rfl
  letI : (refinementPackageProjection U).IsStronglyCartesian
      (input.generatedPulledRouteLegAt i).base.base
      (input.generatedPulledRouteLegAt i).base :=
    UpperGeometryCleavage.pulledRouteGeometryBase_isStronglyCartesian
      (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
      (input.sourceTargetGeometryAt i)
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (refinementPackageProjection U)
    (input.generatedPulledRouteLegAt i).base.base
    (input.generatedPulledRouteLegAt i).base
    refId
  calc
    (input.generatedPulledPackageComparatorRefinementAt i automorphism ≫
        input.generatedPulledPackageComparatorRefinementAt i automorphism⁻¹) ≫
        (input.generatedPulledRouteLegAt i).base =
      input.generatedPulledPackageComparatorRefinementAt i automorphism ≫
        (input.generatedPulledPackageComparatorRefinementAt i automorphism⁻¹ ≫
          (input.generatedPulledRouteLegAt i).base) := Category.assoc _ _ _
    _ = input.generatedPulledPackageComparatorRefinementAt i automorphism ≫
        input.generatedPulledPackageComparatorCandidateAt i automorphism⁻¹ := by
      exact congrArg
        (fun leg : RefinementPackageHom
            ⟨(input.generatedPulledRouteGeometryAt i).core⟩
            ⟨(input.sourceGeometry i).package.core⟩ =>
          (input.generatedPulledPackageComparatorRefinementAt
            i automorphism).comp leg)
        (input.generatedPulledPackageComparatorRefinementAt_fac
          i automorphism⁻¹)
    _ = (input.generatedPulledPackageComparatorRefinementAt i automorphism ≫
          (input.generatedPulledRouteLegAt i).base) ≫
        (exactPackageToRefinement U).map
          (CompositeFiberAut.inv automorphism).base := by
      change (input.generatedPulledPackageComparatorRefinementAt
          i automorphism).comp
          ((input.generatedPulledRouteLegAt i).base.comp
            ((exactPackageToRefinement U).map
              (CompositeFiberAut.inv automorphism).base)) =
        ((input.generatedPulledPackageComparatorRefinementAt
          i automorphism).comp (input.generatedPulledRouteLegAt i).base).comp
            ((exactPackageToRefinement U).map
              (CompositeFiberAut.inv automorphism).base)
      exact (@Category.assoc
        (RefinementPackageTotalCategory U)
        (refinementPackageTotalCategory U) _ _ _ _
        (input.generatedPulledPackageComparatorRefinementAt i automorphism)
        (input.generatedPulledRouteLegAt i).base
        ((exactPackageToRefinement U).map
          (CompositeFiberAut.inv automorphism).base)).symm
    _ = input.generatedPulledPackageComparatorCandidateAt i automorphism ≫
        (exactPackageToRefinement U).map
          (CompositeFiberAut.inv automorphism).base := by
      exact congrArg
        (fun leg : RefinementPackageHom
            ⟨(input.generatedPulledRouteGeometryAt i).core⟩
            ⟨(input.sourceGeometry i).package.core⟩ =>
          leg.comp ((exactPackageToRefinement U).map
            (CompositeFiberAut.inv automorphism).base))
        (input.generatedPulledPackageComparatorRefinementAt_fac
          i automorphism)
    _ = (input.generatedPulledRouteLegAt i).base ≫
        ((exactPackageToRefinement U).map
          (CompositeFiberAut.hom automorphism).base ≫
        (exactPackageToRefinement U).map
          (CompositeFiberAut.inv automorphism).base) := Category.assoc _ _ _
    _ = (input.generatedPulledRouteLegAt i).base := by
      rw [← Functor.map_comp]
      have h := congrArg GeometryTotalHom.base automorphism.1.hom_inv_id
      change (CompositeFiberAut.hom automorphism).base ≫
          (CompositeFiberAut.inv automorphism).base =
        𝟙 (input.sourceGeometry i).package.core at h
      rw [h, (exactPackageToRefinement U).map_id, Category.comp_id]
    _ = (𝟙 (⟨(input.generatedPulledRouteGeometryAt i).core⟩ :
          RefinementPackageObject U)) ≫
        (input.generatedPulledRouteLegAt i).base := by
      rw [Category.id_comp]

/-- The first-stage pulled-route inverse factor followed by the forward
factor also composes to the identity. -/
theorem generatedPulledPackageComparatorRefinementAt_inv_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    input.generatedPulledPackageComparatorRefinementAt i automorphism⁻¹ ≫
        input.generatedPulledPackageComparatorRefinementAt i automorphism =
      𝟙 (⟨(input.generatedPulledRouteGeometryAt i).core⟩ :
        RefinementPackageObject U) := by
  simpa using input.generatedPulledPackageComparatorRefinementAt_hom_inv
    i automorphism⁻¹

/-- Exact pulled-route package factors preserve the source inverse law. -/
theorem generatedPulledPackageComparatorAt_hom_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    input.generatedPulledPackageComparatorAt i automorphism ≫
        input.generatedPulledPackageComparatorAt i automorphism⁻¹ =
      𝟙 (input.generatedPulledRouteGeometryAt i).core := by
  apply exactPackageToRefinement_map_injective
  rw [Functor.map_comp, input.generatedPulledPackageComparatorAt_toRefinement,
    input.generatedPulledPackageComparatorAt_toRefinement,
    (exactPackageToRefinement U).map_id]
  exact input.generatedPulledPackageComparatorRefinementAt_hom_inv i automorphism

/-- Exact pulled-route package factors preserve the reverse inverse law. -/
theorem generatedPulledPackageComparatorAt_inv_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    input.generatedPulledPackageComparatorAt i automorphism⁻¹ ≫
        input.generatedPulledPackageComparatorAt i automorphism =
      𝟙 (input.generatedPulledRouteGeometryAt i).core := by
  simpa using input.generatedPulledPackageComparatorAt_hom_inv i automorphism⁻¹

/-- The geometry-stage pulled-route factors of a source automorphism and its
inverse compose to the identity. -/
theorem generatedPulledGeometryComparatorRefinementAt_hom_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (input.generatedPulledGeometryComparatorRefinementAt i automorphism).comp
        (input.generatedPulledGeometryComparatorRefinementAt i automorphism⁻¹) =
      𝟙 (⟨input.generatedPulledRouteGeometryAt i⟩ :
        RefinementGeometryObject U) := by
  let packageId := 𝟙 (⟨(input.generatedPulledRouteGeometryAt i).core⟩ :
    RefinementPackageObject U)
  letI hcomp : (refinementGeometryProjection U).IsHomLift packageId
      ((input.generatedPulledGeometryComparatorRefinementAt i automorphism).comp
        (input.generatedPulledGeometryComparatorRefinementAt i automorphism⁻¹)) :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq _ _ (by
      change (input.generatedPulledGeometryComparatorRefinementAt
          i automorphism).base.comp
        (input.generatedPulledGeometryComparatorRefinementAt
          i automorphism⁻¹).base = packageId
      rw [input.generatedPulledGeometryComparatorRefinementAt_base,
        input.generatedPulledGeometryComparatorRefinementAt_base]
      exact congrArg
        (fun hom : PackageTotalHom
            (input.generatedPulledRouteGeometryAt i).core
            (input.generatedPulledRouteGeometryAt i).core =>
          (exactPackageToRefinement U).map hom)
        (input.generatedPulledPackageComparatorAt_hom_inv i automorphism))
  letI hid : (refinementGeometryProjection U).IsHomLift packageId
      (𝟙 (⟨input.generatedPulledRouteGeometryAt i⟩ :
        RefinementGeometryObject U)) := by
    apply UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
    rfl
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      (input.generatedPulledRouteLegAt i).base
      (input.generatedPulledRouteLegAt i) :=
    input.generatedPulledRouteLegAt_isStronglyCartesian i
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (refinementGeometryProjection U)
    (input.generatedPulledRouteLegAt i).base
    (input.generatedPulledRouteLegAt i)
    packageId
  calc
    (input.generatedPulledGeometryComparatorRefinementAt i automorphism ≫
        input.generatedPulledGeometryComparatorRefinementAt i automorphism⁻¹) ≫
        input.generatedPulledRouteLegAt i =
      input.generatedPulledGeometryComparatorRefinementAt i automorphism ≫
        (input.generatedPulledGeometryComparatorRefinementAt i automorphism⁻¹ ≫
          input.generatedPulledRouteLegAt i) := Category.assoc _ _ _
    _ = input.generatedPulledGeometryComparatorRefinementAt i automorphism ≫
        input.generatedPulledGeometryComparatorCandidateAt i automorphism⁻¹ := by
      exact congrArg
        (fun leg : RefinementGeometryHom
            (input.generatedPulledRouteGeometryAt i)
            (input.sourceGeometry i).package =>
          (input.generatedPulledGeometryComparatorRefinementAt
            i automorphism).comp leg)
        (input.generatedPulledGeometryComparatorRefinementAt_fac
          i automorphism⁻¹)
    _ = (input.generatedPulledGeometryComparatorRefinementAt i automorphism ≫
          input.generatedPulledRouteLegAt i) ≫
        (exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.inv automorphism) := by
      change (input.generatedPulledGeometryComparatorRefinementAt
          i automorphism).comp
          ((input.generatedPulledRouteLegAt i).comp
            ((exactGeometryToRefinementGeometry U).map
              (CompositeFiberAut.inv automorphism))) =
        ((input.generatedPulledGeometryComparatorRefinementAt
          i automorphism).comp (input.generatedPulledRouteLegAt i)).comp
            ((exactGeometryToRefinementGeometry U).map
              (CompositeFiberAut.inv automorphism))
      exact (@Category.assoc
        (RefinementGeometryCategory.{u, v} U)
        (refinementGeometryCategory U) _ _ _ _
        (input.generatedPulledGeometryComparatorRefinementAt i automorphism)
        (input.generatedPulledRouteLegAt i)
        ((exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.inv automorphism))).symm
    _ = input.generatedPulledGeometryComparatorCandidateAt i automorphism ≫
        (exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.inv automorphism) := by
      exact congrArg
        (fun leg : RefinementGeometryHom
            (input.generatedPulledRouteGeometryAt i)
            (input.sourceGeometry i).package =>
          leg.comp ((exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.inv automorphism)))
        (input.generatedPulledGeometryComparatorRefinementAt_fac
          i automorphism)
    _ = input.generatedPulledRouteLegAt i ≫
        ((exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom automorphism) ≫
        (exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.inv automorphism)) := Category.assoc _ _ _
    _ = input.generatedPulledRouteLegAt i := by
      rw [← Functor.map_comp]
      have hsource : CompositeFiberAut.hom automorphism ≫
          CompositeFiberAut.inv automorphism =
        𝟙 (input.sourceGeometry i).package := automorphism.1.hom_inv_id
      rw [hsource, (exactGeometryToRefinementGeometry U).map_id,
        Category.comp_id]
    _ = (𝟙 (⟨input.generatedPulledRouteGeometryAt i⟩ :
          RefinementGeometryObject U)) ≫
        input.generatedPulledRouteLegAt i := by
      exact (@Category.id_comp
        (RefinementGeometryCategory.{u, v} U)
        (refinementGeometryCategory U) _ _
        (input.generatedPulledRouteLegAt i)).symm

/-- The reverse geometry-stage pulled-route composition is also the identity. -/
theorem generatedPulledGeometryComparatorRefinementAt_inv_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (input.generatedPulledGeometryComparatorRefinementAt i automorphism⁻¹).comp
        (input.generatedPulledGeometryComparatorRefinementAt i automorphism) =
      𝟙 (⟨input.generatedPulledRouteGeometryAt i⟩ :
        RefinementGeometryObject U) := by
  simpa using input.generatedPulledGeometryComparatorRefinementAt_hom_inv
    i automorphism⁻¹

/-- Exact pulled-route geometry factors preserve the source inverse law. -/
theorem generatedPulledGeometryComparatorAt_hom_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (input.generatedPulledGeometryComparatorAt i automorphism).comp
        (input.generatedPulledGeometryComparatorAt i automorphism⁻¹) =
      𝟙 (input.generatedPulledRouteGeometryAt i) := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  change (exactGeometryToRefinementGeometry U).map
      (input.generatedPulledGeometryComparatorAt i automorphism ≫
        input.generatedPulledGeometryComparatorAt i automorphism⁻¹) =
    (exactGeometryToRefinementGeometry U).map
      (𝟙 (input.generatedPulledRouteGeometryAt i))
  rw [Functor.map_comp, input.generatedPulledGeometryComparatorAt_toRefinement,
    input.generatedPulledGeometryComparatorAt_toRefinement,
    (exactGeometryToRefinementGeometry U).map_id]
  exact input.generatedPulledGeometryComparatorRefinementAt_hom_inv i automorphism

/-- Exact pulled-route geometry factors preserve the reverse inverse law. -/
theorem generatedPulledGeometryComparatorAt_inv_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (input.generatedPulledGeometryComparatorAt i automorphism⁻¹).comp
        (input.generatedPulledGeometryComparatorAt i automorphism) =
      𝟙 (input.generatedPulledRouteGeometryAt i) := by
  simpa using input.generatedPulledGeometryComparatorAt_hom_inv i automorphism⁻¹

/-- Generated composite-fiber automorphism on the pulled-first route. -/
noncomputable def generatedPulledCompositeFiberAutAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    CompositeFiberAut (input.generatedPulledRouteGeometryAt i) :=
  ⟨{
    hom := input.generatedPulledGeometryComparatorAt i automorphism
    inv := input.generatedPulledGeometryComparatorAt i automorphism⁻¹
    hom_inv_id := input.generatedPulledGeometryComparatorAt_hom_inv i automorphism
    inv_hom_id := input.generatedPulledGeometryComparatorAt_inv_hom i automorphism
  }, by
    change (input.generatedPulledPackageComparatorAt i automorphism).base =
      𝟙 (packagePoint (input.generatedPulledRouteGeometryAt i).core)
    rfl⟩

/-- The generated pulled-route automorphism has the exact pulled-back forward
geometry factor. -/
@[simp] theorem generatedPulledCompositeFiberAutAt_hom
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    CompositeFiberAut.hom
      (input.generatedPulledCompositeFiberAutAt i automorphism) =
      input.generatedPulledGeometryComparatorAt i automorphism := rfl

/-- The generated pulled-route automorphism has the exact pulled-back inverse
geometry factor. -/
@[simp] theorem generatedPulledCompositeFiberAutAt_inv
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    CompositeFiberAut.inv
      (input.generatedPulledCompositeFiberAutAt i automorphism) =
      input.generatedPulledGeometryComparatorAt i automorphism⁻¹ := rfl

/-- The generated pulled-route automorphism satisfies the Cartesian pullback
factorization against the literal route leg. -/
theorem generatedPulledCompositeFiberAutAt_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    ((exactGeometryToRefinementGeometry U).map
      (CompositeFiberAut.hom
        (input.generatedPulledCompositeFiberAutAt i automorphism))).comp
        (input.generatedPulledRouteLegAt i) =
      input.generatedPulledGeometryComparatorCandidateAt i automorphism := by
  rw [input.generatedPulledCompositeFiberAutAt_hom]
  exact input.generatedPulledGeometryComparatorAt_fac i automorphism

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
