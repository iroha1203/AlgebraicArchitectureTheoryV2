import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleSourcePresentationNaturalityF1
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCanonicalAuthoredCochainTransport
import ResearchLean.AG.DoctrineFiberProduct.QualifiedComparisonBaseTransport

/-!
# Central generated-map naturality under source-presentation change

The source exact isomorphism and the two independently generated endpoint
isomorphisms induce conjugation equivalences on the source and endpoint
automorphism pairs.  Cartesian factorization proves that each generated
endpoint homomorphism intertwines these equivalences; the two component laws
then assemble into the G-118 C3 central naturality square for the independently
generated comparison pair homomorphisms.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 3000000

namespace UpperGeometryCompatibleSourcePresentationChange

variable {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
variable {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
variable {input : UpperGeometryCompatibleProblemInputData ctx P k}

/-- G-118 C3 source-pair conjugation induced by the selected complete source
isomorphism.  It runs from the independently reconstructed input to the old
input. -/
noncomputable def generatedSourcePairMulEquivAt
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (CompositeFiberAut (change.changedInput.sourceGeometry i).package ×
        CompositeFiberAut (change.changedInput.sourceGeometry i).package) ≃*
      (CompositeFiberAut (input.sourceGeometry i).package ×
        CompositeFiberAut (input.sourceGeometry i).package) :=
  MulEquiv.prodCongr
    (CompositeFiberAut.conjugationMulEquiv (change.geometryIso i))
    (CompositeFiberAut.conjugationMulEquiv (change.geometryIso i))

/-- G-118 C3 endpoint-pair conjugation induced by the independently generated
base and pulled exact isomorphisms. -/
noncomputable def generatedEndpointPairMulEquivAt
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (CompositeFiberAut (change.changedInput.generatedBaseRouteGeometryAt i) ×
        CompositeFiberAut
          (change.changedInput.generatedPulledRouteGeometryAt i)) ≃*
      (CompositeFiberAut (input.generatedBaseRouteGeometryAt i) ×
        CompositeFiberAut (input.generatedPulledRouteGeometryAt i)) :=
  MulEquiv.prodCongr
    (CompositeFiberAut.conjugationMulEquiv
      (change.generatedBaseRouteExactGeometryIsoAt i))
    (CompositeFiberAut.conjugationMulEquiv
      (change.generatedPulledRouteExactGeometryIsoAt i))

/-- G-118 C3 base component of central naturality.  The changed generated
pullback is conjugated to the old generated pullback of the source conjugate;
the equality is derived from both cartesian factor triangles. -/
theorem generatedBaseCompositeFiberAutAt_naturality
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex)
    (automorphism :
      CompositeFiberAut (change.changedInput.sourceGeometry i).package) :
    CompositeFiberAut.conjugationMulEquiv
        (change.generatedBaseRouteExactGeometryIsoAt i)
        (change.changedInput.generatedBaseCompositeFiberAutAt i automorphism) =
      input.generatedBaseCompositeFiberAutAt i
        (CompositeFiberAut.conjugationMulEquiv
          (change.geometryIso i) automorphism) := by
  apply CompositeFiberAut.conjugationEquiv_eq_of_intertwining
  apply (exactGeometryToRefinementGeometry U).map_injective
  let eta := (exactGeometryToRefinementGeometry U).map
    (change.generatedBaseRouteExactGeometryIsoAt i).hom
  let sourceIso := (exactGeometryToRefinementGeometry U).map
    (change.geometryIso i).hom
  let newAut := (exactGeometryToRefinementGeometry U).map
    (CompositeFiberAut.hom
      (change.changedInput.generatedBaseCompositeFiberAutAt i automorphism))
  let oldAut := (exactGeometryToRefinementGeometry U).map
    (CompositeFiberAut.hom
      (input.generatedBaseCompositeFiberAutAt i
        (CompositeFiberAut.conjugationMulEquiv
          (change.geometryIso i) automorphism)))
  let oldLeg := input.generatedBaseRouteLegAt i
  let newLeg := change.changedInput.generatedBaseRouteLegAt i
  have hsource :
      (CompositeFiberAut.hom automorphism).comp (change.geometryIso i).hom =
        (change.geometryIso i).hom.comp
          (CompositeFiberAut.hom
            (CompositeFiberAut.conjugationMulEquiv
              (change.geometryIso i) automorphism)) := by
    rw [CompositeFiberAut.conjugationMulEquiv_hom]
    change (CompositeFiberAut.hom automorphism) ≫ (change.geometryIso i).hom =
      (change.geometryIso i).hom ≫
        ((change.geometryIso i).inv ≫
          CompositeFiberAut.hom automorphism) ≫ (change.geometryIso i).hom
    rw [Category.assoc, Iso.hom_inv_id_assoc]
  have hafterLeg :
      (newAut ≫ eta) ≫ oldLeg = (eta ≫ oldAut) ≫ oldLeg := by
    calc
      (newAut ≫ eta) ≫ oldLeg = newAut ≫ (eta ≫ oldLeg) :=
        Category.assoc _ _ _
      _ = newAut ≫ (newLeg ≫ sourceIso) := by
        exact congrArg _ (change.generatedBaseRouteExactGeometryIsoAt_hom_fac i)
      _ = (newAut ≫ newLeg) ≫ sourceIso :=
        (Category.assoc _ _ _).symm
      _ = (newLeg ≫ (exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom automorphism)) ≫ sourceIso := by
        exact congrArg (fun hom => hom ≫ sourceIso)
          (change.changedInput.generatedBaseCompositeFiberAutAt_fac i automorphism)
      _ = newLeg ≫
          ((exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom automorphism) ≫ sourceIso) :=
        Category.assoc _ _ _
      _ = newLeg ≫
          (sourceIso ≫ (exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom
              (CompositeFiberAut.conjugationMulEquiv
                (change.geometryIso i) automorphism))) := by
        exact congrArg (fun hom => newLeg ≫ hom)
          (by simpa only [Functor.map_comp] using
            congrArg (exactGeometryToRefinementGeometry U).map hsource)
      _ = (newLeg ≫ sourceIso) ≫
          (exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom
              (CompositeFiberAut.conjugationMulEquiv
                (change.geometryIso i) automorphism)) :=
        (Category.assoc _ _ _).symm
      _ = (eta ≫ oldLeg) ≫
          (exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom
              (CompositeFiberAut.conjugationMulEquiv
                (change.geometryIso i) automorphism)) := by
        exact congrArg (fun hom => hom ≫
          (exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom
              (CompositeFiberAut.conjugationMulEquiv
                (change.geometryIso i) automorphism)))
          (change.generatedBaseRouteExactGeometryIsoAt_hom_fac i).symm
      _ = eta ≫ (oldLeg ≫
          (exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom
              (CompositeFiberAut.conjugationMulEquiv
                (change.geometryIso i) automorphism))) :=
        Category.assoc _ _ _
      _ = eta ≫ (oldAut ≫ oldLeg) := by
        exact congrArg _
          (input.generatedBaseCompositeFiberAutAt_fac i
            (CompositeFiberAut.conjugationMulEquiv
              (change.geometryIso i) automorphism)).symm
      _ = (eta ≫ oldAut) ≫ oldLeg := (Category.assoc _ _ _).symm
  let left := newAut.comp eta
  let right := eta.comp oldAut
  have hafterLeg' : left.comp oldLeg = right.comp oldLeg := hafterLeg
  change left = right
  have hleftBase : left.base = right.base := by
    let packageLeft := left.base
    let packageRight := right.base
    have hpackageBase : packageLeft.base = packageRight.base := by
      change (exactPointedToRefinement U).map
          (((CompositeFiberAut.hom
            (change.changedInput.generatedBaseCompositeFiberAutAt
              i automorphism)).comp
                (change.generatedBaseRouteExactGeometryIsoAt i).hom).base.base) =
        (exactPointedToRefinement U).map
          ((((change.generatedBaseRouteExactGeometryIsoAt i).hom).comp
            (CompositeFiberAut.hom
              (input.generatedBaseCompositeFiberAutAt i
                (CompositeFiberAut.conjugationMulEquiv
                  (change.geometryIso i) automorphism)))).base.base)
      apply congrArg (exactPointedToRefinement U).map
      change (CompositeFiberAut.hom
          (change.changedInput.generatedBaseCompositeFiberAutAt
            i automorphism)).base.base.comp
            (change.generatedBaseRouteExactGeometryIsoAt i).hom.base.base =
        (change.generatedBaseRouteExactGeometryIsoAt i).hom.base.base.comp
          (CompositeFiberAut.hom
            (input.generatedBaseCompositeFiberAutAt i
              (CompositeFiberAut.conjugationMulEquiv
                (change.geometryIso i) automorphism))).base.base
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
        oldLeg.base.base oldLeg.base :=
      UpperGeometryCleavage.baseRouteGeometryBase_isStronglyCartesian
        (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
        (input.sourceTargetGeometryAt i)
    apply CategoryTheory.Functor.IsStronglyCartesian.ext
      (refinementPackageProjection U)
      oldLeg.base.base oldLeg.base packageRight.base
    exact congrArg RefinementGeometryHom.base hafterLeg'
  letI hleftLift :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
      right.base left hleftBase
  letI hrightLift :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
      right.base right rfl
  letI := input.generatedBaseRouteLegAt_isStronglyCartesian i
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (refinementGeometryProjection U)
    oldLeg.base oldLeg right.base
  exact hafterLeg'

/-- G-118 C3 pulled component of central naturality.  The changed generated
pullback is conjugated to the old generated pullback of the source conjugate;
the equality is derived from both cartesian factor triangles. -/
theorem generatedPulledCompositeFiberAutAt_naturality
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex)
    (automorphism :
      CompositeFiberAut (change.changedInput.sourceGeometry i).package) :
    CompositeFiberAut.conjugationMulEquiv
        (change.generatedPulledRouteExactGeometryIsoAt i)
        (change.changedInput.generatedPulledCompositeFiberAutAt i automorphism) =
      input.generatedPulledCompositeFiberAutAt i
        (CompositeFiberAut.conjugationMulEquiv
          (change.geometryIso i) automorphism) := by
  apply CompositeFiberAut.conjugationEquiv_eq_of_intertwining
  apply (exactGeometryToRefinementGeometry U).map_injective
  let eta := (exactGeometryToRefinementGeometry U).map
    (change.generatedPulledRouteExactGeometryIsoAt i).hom
  let sourceIso := (exactGeometryToRefinementGeometry U).map
    (change.geometryIso i).hom
  let newAut := (exactGeometryToRefinementGeometry U).map
    (CompositeFiberAut.hom
      (change.changedInput.generatedPulledCompositeFiberAutAt i automorphism))
  let oldAut := (exactGeometryToRefinementGeometry U).map
    (CompositeFiberAut.hom
      (input.generatedPulledCompositeFiberAutAt i
        (CompositeFiberAut.conjugationMulEquiv
          (change.geometryIso i) automorphism)))
  let oldLeg := input.generatedPulledRouteLegAt i
  let newLeg := change.changedInput.generatedPulledRouteLegAt i
  have hsource :
      (CompositeFiberAut.hom automorphism).comp (change.geometryIso i).hom =
        (change.geometryIso i).hom.comp
          (CompositeFiberAut.hom
            (CompositeFiberAut.conjugationMulEquiv
              (change.geometryIso i) automorphism)) := by
    rw [CompositeFiberAut.conjugationMulEquiv_hom]
    change (CompositeFiberAut.hom automorphism) ≫ (change.geometryIso i).hom =
      (change.geometryIso i).hom ≫
        ((change.geometryIso i).inv ≫
          CompositeFiberAut.hom automorphism) ≫ (change.geometryIso i).hom
    rw [Category.assoc, Iso.hom_inv_id_assoc]
  have hafterLeg :
      (newAut ≫ eta) ≫ oldLeg = (eta ≫ oldAut) ≫ oldLeg := by
    calc
      (newAut ≫ eta) ≫ oldLeg = newAut ≫ (eta ≫ oldLeg) :=
        Category.assoc _ _ _
      _ = newAut ≫ (newLeg ≫ sourceIso) := by
        exact congrArg _
          (change.generatedPulledRouteExactGeometryIsoAt_hom_fac i)
      _ = (newAut ≫ newLeg) ≫ sourceIso :=
        (Category.assoc _ _ _).symm
      _ = (newLeg ≫ (exactGeometryToRefinementGeometry U).map
          (CompositeFiberAut.hom automorphism)) ≫ sourceIso := by
        exact congrArg (fun hom => hom ≫ sourceIso)
          (change.changedInput.generatedPulledCompositeFiberAutAt_fac
            i automorphism)
      _ = newLeg ≫
          ((exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom automorphism) ≫ sourceIso) :=
        Category.assoc _ _ _
      _ = newLeg ≫
          (sourceIso ≫ (exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom
              (CompositeFiberAut.conjugationMulEquiv
                (change.geometryIso i) automorphism))) := by
        exact congrArg (fun hom => newLeg ≫ hom)
          (by simpa only [Functor.map_comp] using
            congrArg (exactGeometryToRefinementGeometry U).map hsource)
      _ = (newLeg ≫ sourceIso) ≫
          (exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom
              (CompositeFiberAut.conjugationMulEquiv
                (change.geometryIso i) automorphism)) :=
        (Category.assoc _ _ _).symm
      _ = (eta ≫ oldLeg) ≫
          (exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom
              (CompositeFiberAut.conjugationMulEquiv
                (change.geometryIso i) automorphism)) := by
        exact congrArg (fun hom => hom ≫
          (exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom
              (CompositeFiberAut.conjugationMulEquiv
                (change.geometryIso i) automorphism)))
          (change.generatedPulledRouteExactGeometryIsoAt_hom_fac i).symm
      _ = eta ≫ (oldLeg ≫
          (exactGeometryToRefinementGeometry U).map
            (CompositeFiberAut.hom
              (CompositeFiberAut.conjugationMulEquiv
                (change.geometryIso i) automorphism))) :=
        Category.assoc _ _ _
      _ = eta ≫ (oldAut ≫ oldLeg) := by
        exact congrArg _
          (input.generatedPulledCompositeFiberAutAt_fac i
            (CompositeFiberAut.conjugationMulEquiv
              (change.geometryIso i) automorphism)).symm
      _ = (eta ≫ oldAut) ≫ oldLeg := (Category.assoc _ _ _).symm
  let left := newAut.comp eta
  let right := eta.comp oldAut
  have hafterLeg' : left.comp oldLeg = right.comp oldLeg := hafterLeg
  change left = right
  have hleftBase : left.base = right.base := by
    let packageLeft := left.base
    let packageRight := right.base
    have hpackageBase : packageLeft.base = packageRight.base := by
      change (exactPointedToRefinement U).map
          (((CompositeFiberAut.hom
            (change.changedInput.generatedPulledCompositeFiberAutAt
              i automorphism)).comp
                (change.generatedPulledRouteExactGeometryIsoAt i).hom).base.base) =
        (exactPointedToRefinement U).map
          ((((change.generatedPulledRouteExactGeometryIsoAt i).hom).comp
            (CompositeFiberAut.hom
              (input.generatedPulledCompositeFiberAutAt i
                (CompositeFiberAut.conjugationMulEquiv
                  (change.geometryIso i) automorphism)))).base.base)
      apply congrArg (exactPointedToRefinement U).map
      change (CompositeFiberAut.hom
          (change.changedInput.generatedPulledCompositeFiberAutAt
            i automorphism)).base.base.comp
            (change.generatedPulledRouteExactGeometryIsoAt i).hom.base.base =
        (change.generatedPulledRouteExactGeometryIsoAt i).hom.base.base.comp
          (CompositeFiberAut.hom
            (input.generatedPulledCompositeFiberAutAt i
              (CompositeFiberAut.conjugationMulEquiv
                (change.geometryIso i) automorphism))).base.base
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
        oldLeg.base.base oldLeg.base :=
      UpperGeometryCleavage.pulledRouteGeometryBase_isStronglyCartesian
        (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
        (input.sourceTargetGeometryAt i)
    apply CategoryTheory.Functor.IsStronglyCartesian.ext
      (refinementPackageProjection U)
      oldLeg.base.base oldLeg.base packageRight.base
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
    oldLeg.base oldLeg right.base
  exact hafterLeg'

/-- G-118 C3 central source-presentation naturality.  The independently
generated comparison maps satisfy the source-first and endpoint-last
composition square as an equality of bundled monoid homomorphisms. -/
theorem generatedComparisonPairHomAt_sourcePresentation_naturality
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (input.generatedComparisonPairHomAt i).comp
        (change.generatedSourcePairMulEquivAt i).toMonoidHom =
      (change.generatedEndpointPairMulEquivAt i).toMonoidHom.comp
        (change.changedInput.generatedComparisonPairHomAt i) := by
  apply MonoidHom.ext
  intro pair
  apply Prod.ext
  · exact (change.generatedBaseCompositeFiberAutAt_naturality i pair.1).symm
  · exact (change.generatedPulledCompositeFiberAutAt_naturality i pair.2).symm

end UpperGeometryCompatibleSourcePresentationChange

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
