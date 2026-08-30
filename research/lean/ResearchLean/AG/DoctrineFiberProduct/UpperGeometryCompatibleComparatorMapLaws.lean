import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleComparatorGeometry

/-!
# Functorial laws for compatible comparator pullback

This module proves that the two Cartesian pullback constructions preserve the
identity and multiplication in the source composite-fiber automorphism group.
The proofs first establish the package laws and then use them to qualify the
geometry-level Cartesian uniqueness arguments.  The resulting maps are bundled
as group homomorphisms for the finite comparator-family construction.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

namespace UpperGeometryCompatibleProblemInputData

/-- The exact base-route package pullback sends the identity to the identity. -/
theorem generatedBasePackageComparatorAt_one
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    input.generatedBasePackageComparatorAt i
        (1 : CompositeFiberAut (input.sourceGeometry i).package) =
      𝟙 (input.generatedBaseRouteGeometryAt i).core := by
  apply exactPackageToRefinement_map_injective
  rw [input.generatedBasePackageComparatorAt_toRefinement,
    (exactPackageToRefinement U).map_id]
  let routeObject := (exactPackageToRefinement U).obj
    (input.generatedBaseRouteGeometryAt i).core
  let refId := 𝟙 ((exactPointedToRefinement U).obj
    (packagePoint (input.generatedBaseRouteGeometryAt i).core))
  letI hfactor : (refinementPackageProjection U).IsHomLift refId
      (input.generatedBasePackageComparatorRefinementAt i
        (1 : CompositeFiberAut (input.sourceGeometry i).package)) := by
    apply UpperGeometryCleavage.refinementPackageHom_isHomLift_of_base_eq
    rw [input.generatedBasePackageComparatorRefinementAt_base]
    change (exactPointedToRefinement U).map (𝟙 _) = 𝟙 _
    exact (exactPointedToRefinement U).map_id _
  letI hid : (refinementPackageProjection U).IsHomLift refId
      (𝟙 routeObject) := by
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
    input.generatedBasePackageComparatorRefinementAt i
          (1 : CompositeFiberAut (input.sourceGeometry i).package) ≫
        (input.generatedBaseRouteLegAt i).base =
      input.generatedBasePackageComparatorCandidateAt i 1 :=
        input.generatedBasePackageComparatorRefinementAt_fac i 1
    _ = (input.generatedBaseRouteLegAt i).base ≫
        (exactPackageToRefinement U).map (𝟙 _) := by rfl
    _ = (input.generatedBaseRouteLegAt i).base := by
      rw [(exactPackageToRefinement U).map_id, Category.comp_id]
    _ = 𝟙 routeObject ≫ (input.generatedBaseRouteLegAt i).base := by
      simp only [Category.id_comp]

/-- The exact base-route package pullback preserves source multiplication in
the categorical composition order underlying `Aut`. -/
theorem generatedBasePackageComparatorAt_mul
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (left right : CompositeFiberAut (input.sourceGeometry i).package) :
    input.generatedBasePackageComparatorAt i (left * right) =
      (input.generatedBasePackageComparatorAt i right).comp
        (input.generatedBasePackageComparatorAt i left) := by
  apply exactPackageToRefinement_map_injective
  change (exactPackageToRefinement U).map
      (input.generatedBasePackageComparatorAt i (left * right)) =
    (exactPackageToRefinement U).map
      (input.generatedBasePackageComparatorAt i right ≫
        input.generatedBasePackageComparatorAt i left)
  rw [input.generatedBasePackageComparatorAt_toRefinement,
    Functor.map_comp, input.generatedBasePackageComparatorAt_toRefinement,
    input.generatedBasePackageComparatorAt_toRefinement]
  let vertical := (exactPointedToRefinement U).map
    (PackageTotalHom.id (input.generatedBaseRouteGeometryAt i).core).base
  let refId := 𝟙 ((exactPointedToRefinement U).obj
    (packagePoint (input.generatedBaseRouteGeometryAt i).core))
  have hvertical : vertical = refId := by
    change (exactPointedToRefinement U).map (𝟙 _) = 𝟙 _
    exact (exactPointedToRefinement U).map_id _
  letI hproduct : (refinementPackageProjection U).IsHomLift refId
      (input.generatedBasePackageComparatorRefinementAt i (left * right)) := by
    apply UpperGeometryCleavage.refinementPackageHom_isHomLift_of_base_eq
    rw [input.generatedBasePackageComparatorRefinementAt_base]
    exact hvertical
  letI hcomposition : (refinementPackageProjection U).IsHomLift refId
      (input.generatedBasePackageComparatorRefinementAt i right ≫
        input.generatedBasePackageComparatorRefinementAt i left) := by
    apply UpperGeometryCleavage.refinementPackageHom_isHomLift_of_base_eq
    change (input.generatedBasePackageComparatorRefinementAt i right).base.comp
      (input.generatedBasePackageComparatorRefinementAt i left).base = refId
    rw [input.generatedBasePackageComparatorRefinementAt_base,
      input.generatedBasePackageComparatorRefinementAt_base]
    change vertical.comp vertical = refId
    rw [hvertical]
    change refId ≫ refId = refId
    rw [Category.comp_id]
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
    input.generatedBasePackageComparatorRefinementAt i (left * right) ≫
        (input.generatedBaseRouteLegAt i).base =
      input.generatedBasePackageComparatorCandidateAt i (left * right) :=
        input.generatedBasePackageComparatorRefinementAt_fac i (left * right)
    _ = (input.generatedBaseRouteLegAt i).base ≫
        (exactPackageToRefinement U).map
          ((CompositeFiberAut.hom right).base ≫
            (CompositeFiberAut.hom left).base) := by rfl
    _ = ((input.generatedBaseRouteLegAt i).base ≫
          (exactPackageToRefinement U).map
            (CompositeFiberAut.hom right).base) ≫
        (exactPackageToRefinement U).map
          (CompositeFiberAut.hom left).base := by
      rw [Functor.map_comp, Category.assoc]
    _ = input.generatedBasePackageComparatorCandidateAt i right ≫
        (exactPackageToRefinement U).map
          (CompositeFiberAut.hom left).base := by rfl
    _ = (input.generatedBasePackageComparatorRefinementAt i right ≫
          (input.generatedBaseRouteLegAt i).base) ≫
        (exactPackageToRefinement U).map
          (CompositeFiberAut.hom left).base := by
      exact congrArg
        (fun leg : RefinementPackageHom
            ⟨(input.generatedBaseRouteGeometryAt i).core⟩
            ⟨(input.sourceGeometry i).package.core⟩ =>
          leg ≫ (exactPackageToRefinement U).map
            (CompositeFiberAut.hom left).base)
        (input.generatedBasePackageComparatorRefinementAt_fac i right).symm
    _ = input.generatedBasePackageComparatorRefinementAt i right ≫
        ((input.generatedBaseRouteLegAt i).base ≫
          (exactPackageToRefinement U).map
            (CompositeFiberAut.hom left).base) := Category.assoc _ _ _
    _ = input.generatedBasePackageComparatorRefinementAt i right ≫
        input.generatedBasePackageComparatorCandidateAt i left := by rfl
    _ = input.generatedBasePackageComparatorRefinementAt i right ≫
        (input.generatedBasePackageComparatorRefinementAt i left ≫
          (input.generatedBaseRouteLegAt i).base) := by
      exact congrArg
        (fun leg : RefinementPackageHom
            ⟨(input.generatedBaseRouteGeometryAt i).core⟩
            ⟨(input.sourceGeometry i).package.core⟩ =>
          (input.generatedBasePackageComparatorRefinementAt i right).comp leg)
        (input.generatedBasePackageComparatorRefinementAt_fac i left).symm
    _ = (input.generatedBasePackageComparatorRefinementAt i right ≫
          input.generatedBasePackageComparatorRefinementAt i left) ≫
        (input.generatedBaseRouteLegAt i).base := (Category.assoc _ _ _).symm

/-- The exact pulled-route package pullback sends the identity to the identity. -/
theorem generatedPulledPackageComparatorAt_one
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    input.generatedPulledPackageComparatorAt i
        (1 : CompositeFiberAut (input.sourceGeometry i).package) =
      𝟙 (input.generatedPulledRouteGeometryAt i).core := by
  apply exactPackageToRefinement_map_injective
  rw [input.generatedPulledPackageComparatorAt_toRefinement,
    (exactPackageToRefinement U).map_id]
  let routeObject := (exactPackageToRefinement U).obj
    (input.generatedPulledRouteGeometryAt i).core
  let refId := 𝟙 ((exactPointedToRefinement U).obj
    (packagePoint (input.generatedPulledRouteGeometryAt i).core))
  letI hfactor : (refinementPackageProjection U).IsHomLift refId
      (input.generatedPulledPackageComparatorRefinementAt i
        (1 : CompositeFiberAut (input.sourceGeometry i).package)) := by
    apply UpperGeometryCleavage.refinementPackageHom_isHomLift_of_base_eq
    rw [input.generatedPulledPackageComparatorRefinementAt_base]
    change (exactPointedToRefinement U).map (𝟙 _) = 𝟙 _
    exact (exactPointedToRefinement U).map_id _
  letI hid : (refinementPackageProjection U).IsHomLift refId
      (𝟙 routeObject) := by
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
    input.generatedPulledPackageComparatorRefinementAt i
          (1 : CompositeFiberAut (input.sourceGeometry i).package) ≫
        (input.generatedPulledRouteLegAt i).base =
      input.generatedPulledPackageComparatorCandidateAt i 1 :=
        input.generatedPulledPackageComparatorRefinementAt_fac i 1
    _ = (input.generatedPulledRouteLegAt i).base ≫
        (exactPackageToRefinement U).map (𝟙 _) := by rfl
    _ = (input.generatedPulledRouteLegAt i).base := by
      rw [(exactPackageToRefinement U).map_id, Category.comp_id]
    _ = 𝟙 routeObject ≫ (input.generatedPulledRouteLegAt i).base := by
      simp only [Category.id_comp]

/-- The exact pulled-route package pullback preserves source multiplication in
the categorical composition order underlying `Aut`. -/
theorem generatedPulledPackageComparatorAt_mul
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (left right : CompositeFiberAut (input.sourceGeometry i).package) :
    input.generatedPulledPackageComparatorAt i (left * right) =
      (input.generatedPulledPackageComparatorAt i right).comp
        (input.generatedPulledPackageComparatorAt i left) := by
  apply exactPackageToRefinement_map_injective
  change (exactPackageToRefinement U).map
      (input.generatedPulledPackageComparatorAt i (left * right)) =
    (exactPackageToRefinement U).map
      (input.generatedPulledPackageComparatorAt i right ≫
        input.generatedPulledPackageComparatorAt i left)
  rw [input.generatedPulledPackageComparatorAt_toRefinement,
    Functor.map_comp, input.generatedPulledPackageComparatorAt_toRefinement,
    input.generatedPulledPackageComparatorAt_toRefinement]
  let vertical := (exactPointedToRefinement U).map
    (PackageTotalHom.id (input.generatedPulledRouteGeometryAt i).core).base
  let refId := 𝟙 ((exactPointedToRefinement U).obj
    (packagePoint (input.generatedPulledRouteGeometryAt i).core))
  have hvertical : vertical = refId := by
    change (exactPointedToRefinement U).map (𝟙 _) = 𝟙 _
    exact (exactPointedToRefinement U).map_id _
  letI hproduct : (refinementPackageProjection U).IsHomLift refId
      (input.generatedPulledPackageComparatorRefinementAt i (left * right)) := by
    apply UpperGeometryCleavage.refinementPackageHom_isHomLift_of_base_eq
    rw [input.generatedPulledPackageComparatorRefinementAt_base]
    exact hvertical
  letI hcomposition : (refinementPackageProjection U).IsHomLift refId
      (input.generatedPulledPackageComparatorRefinementAt i right ≫
        input.generatedPulledPackageComparatorRefinementAt i left) := by
    apply UpperGeometryCleavage.refinementPackageHom_isHomLift_of_base_eq
    change (input.generatedPulledPackageComparatorRefinementAt i right).base.comp
      (input.generatedPulledPackageComparatorRefinementAt i left).base = refId
    rw [input.generatedPulledPackageComparatorRefinementAt_base,
      input.generatedPulledPackageComparatorRefinementAt_base]
    change vertical.comp vertical = refId
    rw [hvertical]
    change refId ≫ refId = refId
    rw [Category.comp_id]
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
    input.generatedPulledPackageComparatorRefinementAt i (left * right) ≫
        (input.generatedPulledRouteLegAt i).base =
      input.generatedPulledPackageComparatorCandidateAt i (left * right) :=
        input.generatedPulledPackageComparatorRefinementAt_fac i (left * right)
    _ = (input.generatedPulledRouteLegAt i).base ≫
        (exactPackageToRefinement U).map
          ((CompositeFiberAut.hom right).base ≫
            (CompositeFiberAut.hom left).base) := by rfl
    _ = ((input.generatedPulledRouteLegAt i).base ≫
          (exactPackageToRefinement U).map
            (CompositeFiberAut.hom right).base) ≫
        (exactPackageToRefinement U).map
          (CompositeFiberAut.hom left).base := by
      rw [Functor.map_comp, Category.assoc]
    _ = input.generatedPulledPackageComparatorCandidateAt i right ≫
        (exactPackageToRefinement U).map
          (CompositeFiberAut.hom left).base := by rfl
    _ = (input.generatedPulledPackageComparatorRefinementAt i right ≫
          (input.generatedPulledRouteLegAt i).base) ≫
        (exactPackageToRefinement U).map
          (CompositeFiberAut.hom left).base := by
      exact congrArg
        (fun leg : RefinementPackageHom
            ⟨(input.generatedPulledRouteGeometryAt i).core⟩
            ⟨(input.sourceGeometry i).package.core⟩ =>
          leg ≫ (exactPackageToRefinement U).map
            (CompositeFiberAut.hom left).base)
        (input.generatedPulledPackageComparatorRefinementAt_fac i right).symm
    _ = input.generatedPulledPackageComparatorRefinementAt i right ≫
        ((input.generatedPulledRouteLegAt i).base ≫
          (exactPackageToRefinement U).map
            (CompositeFiberAut.hom left).base) := Category.assoc _ _ _
    _ = input.generatedPulledPackageComparatorRefinementAt i right ≫
        input.generatedPulledPackageComparatorCandidateAt i left := by rfl
    _ = input.generatedPulledPackageComparatorRefinementAt i right ≫
        (input.generatedPulledPackageComparatorRefinementAt i left ≫
          (input.generatedPulledRouteLegAt i).base) := by
      exact congrArg
        (fun leg : RefinementPackageHom
            ⟨(input.generatedPulledRouteGeometryAt i).core⟩
            ⟨(input.sourceGeometry i).package.core⟩ =>
          (input.generatedPulledPackageComparatorRefinementAt i right).comp leg)
        (input.generatedPulledPackageComparatorRefinementAt_fac i left).symm
    _ = (input.generatedPulledPackageComparatorRefinementAt i right ≫
          input.generatedPulledPackageComparatorRefinementAt i left) ≫
        (input.generatedPulledRouteLegAt i).base := (Category.assoc _ _ _).symm

/-- The exact base-route geometry pullback sends the identity to the identity. -/
theorem generatedBaseGeometryComparatorAt_one
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    input.generatedBaseGeometryComparatorAt i
        (1 : CompositeFiberAut (input.sourceGeometry i).package) =
      𝟙 (input.generatedBaseRouteGeometryAt i) := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  rw [input.generatedBaseGeometryComparatorAt_toRefinement,
    (exactGeometryToRefinementGeometry U).map_id]
  let routeObject := (exactGeometryToRefinementGeometry U).obj
    (input.generatedBaseRouteGeometryAt i)
  let packageId := 𝟙 ((exactPackageToRefinement U).obj
    (input.generatedBaseRouteGeometryAt i).core)
  letI hfactor : (refinementGeometryProjection U).IsHomLift packageId
      (input.generatedBaseGeometryComparatorRefinementAt i
        (1 : CompositeFiberAut (input.sourceGeometry i).package)) := by
    apply UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
    rw [input.generatedBaseGeometryComparatorRefinementAt_base,
      input.generatedBasePackageComparatorAt_one,
      (exactPackageToRefinement U).map_id]
  letI hid : (refinementGeometryProjection U).IsHomLift packageId
      (𝟙 routeObject) := by
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
    input.generatedBaseGeometryComparatorRefinementAt i
          (1 : CompositeFiberAut (input.sourceGeometry i).package) ≫
        input.generatedBaseRouteLegAt i =
      input.generatedBaseGeometryComparatorCandidateAt i 1 :=
        input.generatedBaseGeometryComparatorRefinementAt_fac i 1
    _ = input.generatedBaseRouteLegAt i ≫
        (exactGeometryToRefinementGeometry U).map (𝟙 _) := by rfl
    _ = input.generatedBaseRouteLegAt i := by
      rw [(exactGeometryToRefinementGeometry U).map_id, Category.comp_id]
    _ = 𝟙 routeObject ≫ input.generatedBaseRouteLegAt i := by
      simp only [Category.id_comp]

/-- The exact base-route geometry pullback preserves source multiplication in
the categorical composition order underlying `Aut`. -/
theorem generatedBaseGeometryComparatorAt_mul
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (left right : CompositeFiberAut (input.sourceGeometry i).package) :
    input.generatedBaseGeometryComparatorAt i (left * right) =
      (input.generatedBaseGeometryComparatorAt i right).comp
        (input.generatedBaseGeometryComparatorAt i left) := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  change (exactGeometryToRefinementGeometry U).map
      (input.generatedBaseGeometryComparatorAt i (left * right)) =
    (exactGeometryToRefinementGeometry U).map
      (input.generatedBaseGeometryComparatorAt i right ≫
        input.generatedBaseGeometryComparatorAt i left)
  rw [input.generatedBaseGeometryComparatorAt_toRefinement,
    Functor.map_comp, input.generatedBaseGeometryComparatorAt_toRefinement,
    input.generatedBaseGeometryComparatorAt_toRefinement]
  let packageComposite := (exactPackageToRefinement U).map
    (input.generatedBasePackageComparatorAt i right ≫
      input.generatedBasePackageComparatorAt i left)
  letI hproduct : (refinementGeometryProjection U).IsHomLift packageComposite
      (input.generatedBaseGeometryComparatorRefinementAt i (left * right)) := by
    apply UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
    rw [input.generatedBaseGeometryComparatorRefinementAt_base,
      input.generatedBasePackageComparatorAt_mul]
    rfl
  letI hcomposition : (refinementGeometryProjection U).IsHomLift packageComposite
      (input.generatedBaseGeometryComparatorRefinementAt i right ≫
        input.generatedBaseGeometryComparatorRefinementAt i left) := by
    apply UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
    change (input.generatedBaseGeometryComparatorRefinementAt i right).base.comp
      (input.generatedBaseGeometryComparatorRefinementAt i left).base =
        packageComposite
    rw [input.generatedBaseGeometryComparatorRefinementAt_base,
      input.generatedBaseGeometryComparatorRefinementAt_base]
    exact (Functor.map_comp (exactPackageToRefinement U)
      (input.generatedBasePackageComparatorAt i right)
      (input.generatedBasePackageComparatorAt i left)).symm
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      (input.generatedBaseRouteLegAt i).base
      (input.generatedBaseRouteLegAt i) :=
    input.generatedBaseRouteLegAt_isStronglyCartesian i
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (refinementGeometryProjection U)
    (input.generatedBaseRouteLegAt i).base
    (input.generatedBaseRouteLegAt i)
    packageComposite
  calc
    input.generatedBaseGeometryComparatorRefinementAt i (left * right) ≫
        input.generatedBaseRouteLegAt i =
      input.generatedBaseGeometryComparatorCandidateAt i (left * right) :=
        input.generatedBaseGeometryComparatorRefinementAt_fac i (left * right)
    _ = input.generatedBaseRouteLegAt i ≫
        (exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom right ≫ CompositeFiberAut.hom left) := by rfl
    _ = (input.generatedBaseRouteLegAt i ≫
          (exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom right)) ≫
        (exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom left) := by
      rw [Functor.map_comp, Category.assoc]
    _ = input.generatedBaseGeometryComparatorCandidateAt i right ≫
        (exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom left) := by rfl
    _ = (input.generatedBaseGeometryComparatorRefinementAt i right ≫
          input.generatedBaseRouteLegAt i) ≫
        (exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom left) := by
      exact congrArg
        (fun leg : RefinementGeometryHom
            (input.generatedBaseRouteGeometryAt i)
            (input.sourceGeometry i).package =>
          leg ≫ (exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom left))
        (input.generatedBaseGeometryComparatorRefinementAt_fac i right).symm
    _ = input.generatedBaseGeometryComparatorRefinementAt i right ≫
        (input.generatedBaseRouteLegAt i ≫
          (exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom left)) := Category.assoc _ _ _
    _ = input.generatedBaseGeometryComparatorRefinementAt i right ≫
        input.generatedBaseGeometryComparatorCandidateAt i left := by rfl
    _ = input.generatedBaseGeometryComparatorRefinementAt i right ≫
        (input.generatedBaseGeometryComparatorRefinementAt i left ≫
          input.generatedBaseRouteLegAt i) := by
      exact congrArg
        (fun leg : RefinementGeometryHom
            (input.generatedBaseRouteGeometryAt i)
            (input.sourceGeometry i).package =>
          (input.generatedBaseGeometryComparatorRefinementAt i right).comp leg)
        (input.generatedBaseGeometryComparatorRefinementAt_fac i left).symm
    _ = (input.generatedBaseGeometryComparatorRefinementAt i right ≫
          input.generatedBaseGeometryComparatorRefinementAt i left) ≫
        input.generatedBaseRouteLegAt i := (Category.assoc _ _ _).symm

/-- The exact pulled-route geometry pullback sends the identity to the identity. -/
theorem generatedPulledGeometryComparatorAt_one
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    input.generatedPulledGeometryComparatorAt i
        (1 : CompositeFiberAut (input.sourceGeometry i).package) =
      𝟙 (input.generatedPulledRouteGeometryAt i) := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  rw [input.generatedPulledGeometryComparatorAt_toRefinement,
    (exactGeometryToRefinementGeometry U).map_id]
  let routeObject := (exactGeometryToRefinementGeometry U).obj
    (input.generatedPulledRouteGeometryAt i)
  let packageId := 𝟙 ((exactPackageToRefinement U).obj
    (input.generatedPulledRouteGeometryAt i).core)
  letI hfactor : (refinementGeometryProjection U).IsHomLift packageId
      (input.generatedPulledGeometryComparatorRefinementAt i
        (1 : CompositeFiberAut (input.sourceGeometry i).package)) := by
    apply UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
    rw [input.generatedPulledGeometryComparatorRefinementAt_base,
      input.generatedPulledPackageComparatorAt_one,
      (exactPackageToRefinement U).map_id]
  letI hid : (refinementGeometryProjection U).IsHomLift packageId
      (𝟙 routeObject) := by
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
    input.generatedPulledGeometryComparatorRefinementAt i
          (1 : CompositeFiberAut (input.sourceGeometry i).package) ≫
        input.generatedPulledRouteLegAt i =
      input.generatedPulledGeometryComparatorCandidateAt i 1 :=
        input.generatedPulledGeometryComparatorRefinementAt_fac i 1
    _ = input.generatedPulledRouteLegAt i ≫
        (exactGeometryToRefinementGeometry U).map (𝟙 _) := by rfl
    _ = input.generatedPulledRouteLegAt i := by
      rw [(exactGeometryToRefinementGeometry U).map_id, Category.comp_id]
    _ = 𝟙 routeObject ≫ input.generatedPulledRouteLegAt i := by
      simp only [Category.id_comp]

/-- The exact pulled-route geometry pullback preserves source multiplication in
the categorical composition order underlying `Aut`. -/
theorem generatedPulledGeometryComparatorAt_mul
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (left right : CompositeFiberAut (input.sourceGeometry i).package) :
    input.generatedPulledGeometryComparatorAt i (left * right) =
      (input.generatedPulledGeometryComparatorAt i right).comp
        (input.generatedPulledGeometryComparatorAt i left) := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  change (exactGeometryToRefinementGeometry U).map
      (input.generatedPulledGeometryComparatorAt i (left * right)) =
    (exactGeometryToRefinementGeometry U).map
      (input.generatedPulledGeometryComparatorAt i right ≫
        input.generatedPulledGeometryComparatorAt i left)
  rw [input.generatedPulledGeometryComparatorAt_toRefinement,
    Functor.map_comp, input.generatedPulledGeometryComparatorAt_toRefinement,
    input.generatedPulledGeometryComparatorAt_toRefinement]
  let packageComposite := (exactPackageToRefinement U).map
    (input.generatedPulledPackageComparatorAt i right ≫
      input.generatedPulledPackageComparatorAt i left)
  letI hproduct : (refinementGeometryProjection U).IsHomLift packageComposite
      (input.generatedPulledGeometryComparatorRefinementAt i (left * right)) := by
    apply UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
    rw [input.generatedPulledGeometryComparatorRefinementAt_base,
      input.generatedPulledPackageComparatorAt_mul]
    rfl
  letI hcomposition : (refinementGeometryProjection U).IsHomLift packageComposite
      (input.generatedPulledGeometryComparatorRefinementAt i right ≫
        input.generatedPulledGeometryComparatorRefinementAt i left) := by
    apply UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
    change (input.generatedPulledGeometryComparatorRefinementAt i right).base.comp
      (input.generatedPulledGeometryComparatorRefinementAt i left).base =
        packageComposite
    rw [input.generatedPulledGeometryComparatorRefinementAt_base,
      input.generatedPulledGeometryComparatorRefinementAt_base]
    exact (Functor.map_comp (exactPackageToRefinement U)
      (input.generatedPulledPackageComparatorAt i right)
      (input.generatedPulledPackageComparatorAt i left)).symm
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      (input.generatedPulledRouteLegAt i).base
      (input.generatedPulledRouteLegAt i) :=
    input.generatedPulledRouteLegAt_isStronglyCartesian i
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (refinementGeometryProjection U)
    (input.generatedPulledRouteLegAt i).base
    (input.generatedPulledRouteLegAt i)
    packageComposite
  calc
    input.generatedPulledGeometryComparatorRefinementAt i (left * right) ≫
        input.generatedPulledRouteLegAt i =
      input.generatedPulledGeometryComparatorCandidateAt i (left * right) :=
        input.generatedPulledGeometryComparatorRefinementAt_fac i (left * right)
    _ = input.generatedPulledRouteLegAt i ≫
        (exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom right ≫ CompositeFiberAut.hom left) := by rfl
    _ = (input.generatedPulledRouteLegAt i ≫
          (exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom right)) ≫
        (exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom left) := by
      rw [Functor.map_comp, Category.assoc]
    _ = input.generatedPulledGeometryComparatorCandidateAt i right ≫
        (exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom left) := by rfl
    _ = (input.generatedPulledGeometryComparatorRefinementAt i right ≫
          input.generatedPulledRouteLegAt i) ≫
        (exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom left) := by
      exact congrArg
        (fun leg : RefinementGeometryHom
            (input.generatedPulledRouteGeometryAt i)
            (input.sourceGeometry i).package =>
          leg ≫ (exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom left))
        (input.generatedPulledGeometryComparatorRefinementAt_fac i right).symm
    _ = input.generatedPulledGeometryComparatorRefinementAt i right ≫
        (input.generatedPulledRouteLegAt i ≫
          (exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom left)) := Category.assoc _ _ _
    _ = input.generatedPulledGeometryComparatorRefinementAt i right ≫
        input.generatedPulledGeometryComparatorCandidateAt i left := by rfl
    _ = input.generatedPulledGeometryComparatorRefinementAt i right ≫
        (input.generatedPulledGeometryComparatorRefinementAt i left ≫
          input.generatedPulledRouteLegAt i) := by
      exact congrArg
        (fun leg : RefinementGeometryHom
            (input.generatedPulledRouteGeometryAt i)
            (input.sourceGeometry i).package =>
          (input.generatedPulledGeometryComparatorRefinementAt i right).comp leg)
        (input.generatedPulledGeometryComparatorRefinementAt_fac i left).symm
    _ = (input.generatedPulledGeometryComparatorRefinementAt i right ≫
          input.generatedPulledGeometryComparatorRefinementAt i left) ≫
        input.generatedPulledRouteLegAt i := (Category.assoc _ _ _).symm

/-- Normalize the generated base-route pullback at the source identity to the
target group identity. -/
@[simp] theorem generatedBaseCompositeFiberAutAt_one
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    input.generatedBaseCompositeFiberAutAt i
        (1 : CompositeFiberAut (input.sourceGeometry i).package) = 1 := by
  apply Subtype.ext
  apply Iso.ext
  exact input.generatedBaseGeometryComparatorAt_one i

/-- The generated base-route automorphism pullback preserves multiplication. -/
theorem generatedBaseCompositeFiberAutAt_mul
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (left right : CompositeFiberAut (input.sourceGeometry i).package) :
    input.generatedBaseCompositeFiberAutAt i (left * right) =
      input.generatedBaseCompositeFiberAutAt i left *
        input.generatedBaseCompositeFiberAutAt i right := by
  apply Subtype.ext
  apply Iso.ext
  exact input.generatedBaseGeometryComparatorAt_mul i left right

/-- Normalize the generated pulled-route pullback at the source identity to the
target group identity. -/
@[simp] theorem generatedPulledCompositeFiberAutAt_one
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    input.generatedPulledCompositeFiberAutAt i
        (1 : CompositeFiberAut (input.sourceGeometry i).package) = 1 := by
  apply Subtype.ext
  apply Iso.ext
  exact input.generatedPulledGeometryComparatorAt_one i

/-- The generated pulled-route automorphism pullback preserves multiplication. -/
theorem generatedPulledCompositeFiberAutAt_mul
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (left right : CompositeFiberAut (input.sourceGeometry i).package) :
    input.generatedPulledCompositeFiberAutAt i (left * right) =
      input.generatedPulledCompositeFiberAutAt i left *
        input.generatedPulledCompositeFiberAutAt i right := by
  apply Subtype.ext
  apply Iso.ext
  exact input.generatedPulledGeometryComparatorAt_mul i left right

/-- Group homomorphism pulling source composite-fiber automorphisms back along
the generated base-first route. -/
noncomputable def generatedBaseCompositeFiberAutHomAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    CompositeFiberAut (input.sourceGeometry i).package →*
      CompositeFiberAut (input.generatedBaseRouteGeometryAt i) where
  toFun := input.generatedBaseCompositeFiberAutAt i
  map_one' := input.generatedBaseCompositeFiberAutAt_one i
  map_mul' := input.generatedBaseCompositeFiberAutAt_mul i

/-- Group homomorphism pulling source composite-fiber automorphisms back along
the generated pulled-first route. -/
noncomputable def generatedPulledCompositeFiberAutHomAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex) :
    CompositeFiberAut (input.sourceGeometry i).package →*
      CompositeFiberAut (input.generatedPulledRouteGeometryAt i) where
  toFun := input.generatedPulledCompositeFiberAutAt i
  map_one' := input.generatedPulledCompositeFiberAutAt_one i
  map_mul' := input.generatedPulledCompositeFiberAutAt_mul i

/-- Normalize evaluation of the bundled base-route homomorphism to the
pointwise Cartesian pullback. -/
@[simp] theorem generatedBaseCompositeFiberAutHomAt_apply
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    input.generatedBaseCompositeFiberAutHomAt i automorphism =
      input.generatedBaseCompositeFiberAutAt i automorphism := rfl

/-- Normalize evaluation of the bundled pulled-route homomorphism to the
pointwise Cartesian pullback. -/
@[simp] theorem generatedPulledCompositeFiberAutHomAt_apply
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (input : UpperGeometryCompatibleProblemInputData ctx P k) (i : P.Vertex)
    (automorphism : CompositeFiberAut (input.sourceGeometry i).package) :
    input.generatedPulledCompositeFiberAutHomAt i automorphism =
      input.generatedPulledCompositeFiberAutAt i automorphism := rfl

end UpperGeometryCompatibleProblemInputData

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
