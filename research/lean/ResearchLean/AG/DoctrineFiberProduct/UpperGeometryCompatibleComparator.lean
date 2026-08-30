import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleInput

/-!
# Cartesian pullback of compatible source comparators

This module begins the two-stage comparator construction required by the
revision-4 G-115 compatible locus.  The first stage pulls the package map of a
source `CompositeFiberAut` back along either generated strongly Cartesian
reverse-route leg.  Since the source automorphism is vertical after the
pointed projection, the universal factor lies over the exact identity and is
therefore recovered as an exact `PackageTotalHom`.

The geometry-stage pullback and the resulting generated
`CompositeFiberAut` are successor obligations.  Keeping the package stage
explicit prevents the invalid inference that a composite-fiber automorphism
is already vertical for `geometryProjection`.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

namespace UpperGeometryCleavage

/-- Recover an exact package morphism from a refinement package morphism whose
lower map is the exact embedding of a specified package map. -/
noncomputable def exactPackageHomOfRefinement
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    (f : PackageTotalHom P Q)
    (hom : RefinementPackageHom ⟨P⟩ ⟨Q⟩)
    (hbase : hom.base = (exactPointedToRefinement U).map f.base) :
    PackageTotalHom P Q where
  base := f.base
  upper := hom.upper
  atomEquiv_eq := by
    change hom.upper.atomEquiv = f.base.doctrineHom.atomEquiv
    rw [hom.atomEquiv_eq, hbase]
    apply Equiv.ext
    intro atom
    rfl

@[simp] theorem exactPackageHomOfRefinement_base
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    (f : PackageTotalHom P Q)
    (hom : RefinementPackageHom ⟨P⟩ ⟨Q⟩)
    (hbase : hom.base = (exactPointedToRefinement U).map f.base) :
    (exactPackageHomOfRefinement f hom hbase).base = f.base := rfl

/-- Re-embedding package exactification recovers the original complete
refinement package morphism. -/
theorem exactPackageHomOfRefinement_toRefinement
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    (f : PackageTotalHom P Q)
    (hom : RefinementPackageHom ⟨P⟩ ⟨Q⟩)
    (hbase : hom.base = (exactPointedToRefinement U).map f.base) :
    (exactPackageToRefinement U).map
        (exactPackageHomOfRefinement f hom hbase) = hom := by
  apply RefinementPackageHom.ext
  · exact hbase.symm
  · rfl

end UpperGeometryCleavage

namespace UpperGeometryCompatibleProblemInputData

/-- Base-route candidate obtained by following the generated leg with the
source automorphism's package map. -/
noncomputable def generatedBasePackageComparatorCandidateAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    RefinementPackageHom
      ⟨(input.generatedBaseRouteGeometryAt i).core⟩
      ⟨(input.sourceGeometry i).package.core⟩ :=
  (input.generatedBaseRouteLegAt i).base.comp
    ((exactPackageToRefinement U).map
      (CompositeFiberAut.hom automorphism).base)

/-- The base-route candidate has the same pointed lower map as the generated
route leg, because a composite-fiber automorphism is vertical after the
pointed projection. -/
theorem generatedBasePackageComparatorCandidateAt_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (input.generatedBasePackageComparatorCandidateAt i automorphism).base =
      (PointedRefinementHom.id
        (packagePoint (input.generatedBaseRouteGeometryAt i).core)).comp
        (input.generatedBaseRouteLegAt i).base.base := by
  apply PointedRefinementHom.ext
  apply RefinementDoctrineHom.ext
  · funext source
    change (CompositeFiberAut.hom automorphism).base.base.doctrineHom.sourceMap
        ((input.generatedBaseRouteLegAt i).base.base.doctrineHom.sourceMap source) =
      (input.generatedBaseRouteLegAt i).base.base.doctrineHom.sourceMap source
    rw [CompositeFiberAut.hom_base_base_eq]
    rfl
  · funext atom
    change (CompositeFiberAut.hom automorphism).base.base.doctrineHom.atomEquiv
        ((input.generatedBaseRouteLegAt i).base.base.doctrineHom.atomMap atom) =
      (input.generatedBaseRouteLegAt i).base.base.doctrineHom.atomMap atom
    rw [CompositeFiberAut.hom_base_base_eq]
    rfl

/-- Universal package-stage pullback of a source automorphism along the
generated base-first route. -/
noncomputable def generatedBasePackageComparatorRefinementAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    RefinementPackageHom
      ⟨(input.generatedBaseRouteGeometryAt i).core⟩
      ⟨(input.generatedBaseRouteGeometryAt i).core⟩ := by
  letI : (refinementPackageProjection U).IsStronglyCartesian
      (input.generatedBaseRouteLegAt i).base.base
      (input.generatedBaseRouteLegAt i).base := by
    exact UpperGeometryCleavage.baseRouteGeometryBase_isStronglyCartesian
      (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
      (input.sourceTargetGeometryAt i)
  let candidate := input.generatedBasePackageComparatorCandidateAt i automorphism
  letI : (refinementPackageProjection U).IsHomLift candidate.base candidate := by
    apply CategoryTheory.IsHomLift.of_fac'
      (refinementPackageProjection U) candidate.base candidate rfl rfl
    rfl
  exact CategoryTheory.Functor.IsStronglyCartesian.map
    (refinementPackageProjection U)
    (input.generatedBaseRouteLegAt i).base.base
    (input.generatedBaseRouteLegAt i).base
    (g := PointedRefinementHom.id _)
    (input.generatedBasePackageComparatorCandidateAt_base i automorphism)
    candidate

/-- The package pullback factors the generated route leg as the source
automorphism candidate. -/
theorem generatedBasePackageComparatorRefinementAt_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (input.generatedBasePackageComparatorRefinementAt i automorphism).comp
        (input.generatedBaseRouteLegAt i).base =
      input.generatedBasePackageComparatorCandidateAt i automorphism := by
  letI : (refinementPackageProjection U).IsStronglyCartesian
      (input.generatedBaseRouteLegAt i).base.base
      (input.generatedBaseRouteLegAt i).base := by
    exact UpperGeometryCleavage.baseRouteGeometryBase_isStronglyCartesian
      (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
      (input.sourceTargetGeometryAt i)
  let candidate := input.generatedBasePackageComparatorCandidateAt i automorphism
  letI : (refinementPackageProjection U).IsHomLift candidate.base candidate := by
    apply CategoryTheory.IsHomLift.of_fac'
      (refinementPackageProjection U) candidate.base candidate rfl rfl
    rfl
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (refinementPackageProjection U)
    (input.generatedBaseRouteLegAt i).base.base
    (input.generatedBaseRouteLegAt i).base
    (input.generatedBasePackageComparatorCandidateAt_base i automorphism)
    candidate

/-- The universal base-route factor lies over the pointed identity. -/
theorem generatedBasePackageComparatorRefinementAt_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (input.generatedBasePackageComparatorRefinementAt i automorphism).base =
      (exactPointedToRefinement U).map
        (PackageTotalHom.id (input.generatedBaseRouteGeometryAt i).core).base := by
  letI : (refinementPackageProjection U).IsStronglyCartesian
      (input.generatedBaseRouteLegAt i).base.base
      (input.generatedBaseRouteLegAt i).base := by
    exact UpperGeometryCleavage.baseRouteGeometryBase_isStronglyCartesian
      (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
      (input.sourceTargetGeometryAt i)
  let candidate := input.generatedBasePackageComparatorCandidateAt i automorphism
  letI : (refinementPackageProjection U).IsHomLift candidate.base candidate := by
    apply CategoryTheory.IsHomLift.of_fac'
      (refinementPackageProjection U) candidate.base candidate rfl rfl
    rfl
  unfold generatedBasePackageComparatorRefinementAt
  exact (CategoryTheory.IsHomLift.eq_of_isHomLift
    (refinementPackageProjection U) (PointedRefinementHom.id _)
    (CategoryTheory.Functor.IsStronglyCartesian.map
      (refinementPackageProjection U)
      (input.generatedBaseRouteLegAt i).base.base
      (input.generatedBaseRouteLegAt i).base
      (input.generatedBasePackageComparatorCandidateAt_base i automorphism)
      candidate)).symm

/-- Exact package endomorphism underlying the base-route pullback. -/
noncomputable def generatedBasePackageComparatorAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    PackageTotalHom (input.generatedBaseRouteGeometryAt i).core
      (input.generatedBaseRouteGeometryAt i).core :=
  UpperGeometryCleavage.exactPackageHomOfRefinement
    (PackageTotalHom.id (input.generatedBaseRouteGeometryAt i).core)
    (input.generatedBasePackageComparatorRefinementAt i automorphism)
    (input.generatedBasePackageComparatorRefinementAt_base i automorphism)

/-- Exact embedding recovers the universal base-route package factor. -/
theorem generatedBasePackageComparatorAt_toRefinement
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (exactPackageToRefinement U).map
        (input.generatedBasePackageComparatorAt i automorphism) =
      input.generatedBasePackageComparatorRefinementAt i automorphism := by
  exact UpperGeometryCleavage.exactPackageHomOfRefinement_toRefinement _ _ _

/-- Pulled-route candidate obtained by following the generated leg with the
source automorphism's package map. -/
noncomputable def generatedPulledPackageComparatorCandidateAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    RefinementPackageHom
      ⟨(input.generatedPulledRouteGeometryAt i).core⟩
      ⟨(input.sourceGeometry i).package.core⟩ :=
  (input.generatedPulledRouteLegAt i).base.comp
    ((exactPackageToRefinement U).map
      (CompositeFiberAut.hom automorphism).base)

/-- The pulled-route candidate has the same pointed lower map as the generated
route leg. -/
theorem generatedPulledPackageComparatorCandidateAt_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (input.generatedPulledPackageComparatorCandidateAt i automorphism).base =
      (PointedRefinementHom.id
        (packagePoint (input.generatedPulledRouteGeometryAt i).core)).comp
        (input.generatedPulledRouteLegAt i).base.base := by
  apply PointedRefinementHom.ext
  apply RefinementDoctrineHom.ext
  · funext source
    change (CompositeFiberAut.hom automorphism).base.base.doctrineHom.sourceMap
        ((input.generatedPulledRouteLegAt i).base.base.doctrineHom.sourceMap source) =
      (input.generatedPulledRouteLegAt i).base.base.doctrineHom.sourceMap source
    rw [CompositeFiberAut.hom_base_base_eq]
    rfl
  · funext atom
    change (CompositeFiberAut.hom automorphism).base.base.doctrineHom.atomEquiv
        ((input.generatedPulledRouteLegAt i).base.base.doctrineHom.atomMap atom) =
      (input.generatedPulledRouteLegAt i).base.base.doctrineHom.atomMap atom
    rw [CompositeFiberAut.hom_base_base_eq]
    rfl

/-- Universal package-stage pullback of a source automorphism along the
generated pulled-first route. -/
noncomputable def generatedPulledPackageComparatorRefinementAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    RefinementPackageHom
      ⟨(input.generatedPulledRouteGeometryAt i).core⟩
      ⟨(input.generatedPulledRouteGeometryAt i).core⟩ := by
  letI : (refinementPackageProjection U).IsStronglyCartesian
      (input.generatedPulledRouteLegAt i).base.base
      (input.generatedPulledRouteLegAt i).base := by
    exact UpperGeometryCleavage.pulledRouteGeometryBase_isStronglyCartesian
      (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
      (input.sourceTargetGeometryAt i)
  let candidate := input.generatedPulledPackageComparatorCandidateAt i automorphism
  letI : (refinementPackageProjection U).IsHomLift candidate.base candidate := by
    apply CategoryTheory.IsHomLift.of_fac'
      (refinementPackageProjection U) candidate.base candidate rfl rfl
    rfl
  exact CategoryTheory.Functor.IsStronglyCartesian.map
    (refinementPackageProjection U)
    (input.generatedPulledRouteLegAt i).base.base
    (input.generatedPulledRouteLegAt i).base
    (g := PointedRefinementHom.id _)
    (input.generatedPulledPackageComparatorCandidateAt_base i automorphism)
    candidate

/-- The pulled package pullback factors the generated route leg as the source
automorphism candidate. -/
theorem generatedPulledPackageComparatorRefinementAt_fac
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (input.generatedPulledPackageComparatorRefinementAt i automorphism).comp
        (input.generatedPulledRouteLegAt i).base =
      input.generatedPulledPackageComparatorCandidateAt i automorphism := by
  letI : (refinementPackageProjection U).IsStronglyCartesian
      (input.generatedPulledRouteLegAt i).base.base
      (input.generatedPulledRouteLegAt i).base := by
    exact UpperGeometryCleavage.pulledRouteGeometryBase_isStronglyCartesian
      (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
      (input.sourceTargetGeometryAt i)
  let candidate := input.generatedPulledPackageComparatorCandidateAt i automorphism
  letI : (refinementPackageProjection U).IsHomLift candidate.base candidate := by
    apply CategoryTheory.IsHomLift.of_fac'
      (refinementPackageProjection U) candidate.base candidate rfl rfl
    rfl
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (refinementPackageProjection U)
    (input.generatedPulledRouteLegAt i).base.base
    (input.generatedPulledRouteLegAt i).base
    (input.generatedPulledPackageComparatorCandidateAt_base i automorphism)
    candidate

/-- The universal pulled-route factor lies over the pointed identity. -/
theorem generatedPulledPackageComparatorRefinementAt_base
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (input.generatedPulledPackageComparatorRefinementAt i automorphism).base =
      (exactPointedToRefinement U).map
        (PackageTotalHom.id (input.generatedPulledRouteGeometryAt i).core).base := by
  letI : (refinementPackageProjection U).IsStronglyCartesian
      (input.generatedPulledRouteLegAt i).base.base
      (input.generatedPulledRouteLegAt i).base := by
    exact UpperGeometryCleavage.pulledRouteGeometryBase_isStronglyCartesian
      (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
      (input.sourceTargetGeometryAt i)
  let candidate := input.generatedPulledPackageComparatorCandidateAt i automorphism
  letI : (refinementPackageProjection U).IsHomLift candidate.base candidate := by
    apply CategoryTheory.IsHomLift.of_fac'
      (refinementPackageProjection U) candidate.base candidate rfl rfl
    rfl
  unfold generatedPulledPackageComparatorRefinementAt
  exact (CategoryTheory.IsHomLift.eq_of_isHomLift
    (refinementPackageProjection U) (PointedRefinementHom.id _)
    (CategoryTheory.Functor.IsStronglyCartesian.map
      (refinementPackageProjection U)
      (input.generatedPulledRouteLegAt i).base.base
      (input.generatedPulledRouteLegAt i).base
      (input.generatedPulledPackageComparatorCandidateAt_base i automorphism)
      candidate)).symm

/-- Exact package endomorphism underlying the pulled-route pullback. -/
noncomputable def generatedPulledPackageComparatorAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    PackageTotalHom (input.generatedPulledRouteGeometryAt i).core
      (input.generatedPulledRouteGeometryAt i).core :=
  UpperGeometryCleavage.exactPackageHomOfRefinement
    (PackageTotalHom.id (input.generatedPulledRouteGeometryAt i).core)
    (input.generatedPulledPackageComparatorRefinementAt i automorphism)
    (input.generatedPulledPackageComparatorRefinementAt_base i automorphism)

/-- Exact embedding recovers the universal pulled-route package factor. -/
theorem generatedPulledPackageComparatorAt_toRefinement
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    (exactPackageToRefinement U).map
        (input.generatedPulledPackageComparatorAt i automorphism) =
      input.generatedPulledPackageComparatorRefinementAt i automorphism := by
  exact UpperGeometryCleavage.exactPackageHomOfRefinement_toRefinement _ _ _

end UpperGeometryCompatibleProblemInputData
end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
