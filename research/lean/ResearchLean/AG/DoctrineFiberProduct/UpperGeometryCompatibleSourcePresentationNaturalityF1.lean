import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleSourcePresentationNaturalityF0
import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleMateNaturality

/-!
# Generated endpoint factor laws under source-presentation change

The independently constructed endpoint isomorphisms from the F0s gate satisfy
the cartesian factorization triangles that characterize them.  Their
coefficient maps are then forced to be identities by the generated-leg and
selected source-change coefficient laws.
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

/-- G-118 C1s primary base-endpoint factor law.  The independently generated
`eta_B.hom` is characterized by `IsStronglyCartesian.fac`, not by a supplied
factorization certificate. -/
theorem generatedBaseRouteExactGeometryIsoAt_hom_fac
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (exactGeometryToRefinementGeometry U).map
          (change.generatedBaseRouteExactGeometryIsoAt i).hom ≫
        input.generatedBaseRouteLegAt i =
      change.changedInput.generatedBaseRouteLegAt i ≫
        (exactGeometryToRefinementGeometry U).map (change.geometryIso i).hom := by
  rw [show (change.generatedBaseRouteExactGeometryIsoAt i).hom =
      change.generatedBaseRouteExactGeometryHomAt i from rfl,
    change.generatedBaseRouteExactGeometryHomAt_toRefinement]
  let oldLeg := input.generatedBaseRouteLegAt i
  let newLeg := change.changedInput.generatedBaseRouteLegAt i
  let sourceIso := (exactGeometryToRefinementGeometry U).mapIso
    (change.geometryIso i)
  let candidate := newLeg ≫ sourceIso.hom
  let lowerIso := (exactPackageToRefinement U).mapIso
    (change.generatedBaseRouteExactCoreIsoAt i)
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      oldLeg.base oldLeg := input.generatedBaseRouteLegAt_isStronglyCartesian i
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      newLeg.base newLeg :=
    change.changedInput.generatedBaseRouteLegAt_isStronglyCartesian i
  letI : (refinementGeometryProjection U).IsHomLift
      sourceIso.hom.base sourceIso.hom :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift sourceIso.hom
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      sourceIso.hom.base sourceIso.hom :=
    CategoryTheory.Functor.IsStronglyCartesian.of_isIso
      (p := refinementGeometryProjection U) (f := sourceIso.hom.base)
      sourceIso.hom
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      candidate.base candidate := by
    dsimp only [candidate]
    exact CategoryTheory.Functor.IsStronglyCartesian.comp
      (refinementGeometryProjection U)
  have base_fac : candidate.base = lowerIso.hom ≫ oldLeg.base := by
    dsimp only [candidate, lowerIso, sourceIso, oldLeg, newLeg]
    exact (change.generatedBaseRouteExactCoreIsoAt_hom_fac i).symm
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (refinementGeometryProjection U)
    oldLeg.base oldLeg base_fac candidate

/-- G-118 C1s reverse base-endpoint factor law.  It is derived from the primary
factor law and the two actual isomorphism inverse laws. -/
theorem generatedBaseRouteExactGeometryIsoAt_inv_fac
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (exactGeometryToRefinementGeometry U).map
          (change.generatedBaseRouteExactGeometryIsoAt i).inv ≫
        change.changedInput.generatedBaseRouteLegAt i =
      input.generatedBaseRouteLegAt i ≫
        (exactGeometryToRefinementGeometry U).map (change.geometryIso i).inv := by
  let endpointIso := (exactGeometryToRefinementGeometry U).mapIso
    (change.generatedBaseRouteExactGeometryIsoAt i)
  let sourceIso := (exactGeometryToRefinementGeometry U).mapIso
    (change.geometryIso i)
  have hfac : RefinementGeometryHom.comp
      (change.changedInput.generatedBaseRouteLegAt i) sourceIso.hom =
    RefinementGeometryHom.comp endpointIso.hom
      (input.generatedBaseRouteLegAt i) :=
    (change.generatedBaseRouteExactGeometryIsoAt_hom_fac i).symm
  have hEndpoint := endpointIso.inv_hom_id
  change RefinementGeometryHom.comp endpointIso.inv endpointIso.hom =
    RefinementGeometryHom.id _ at hEndpoint
  have hSource := sourceIso.inv_hom_id
  change RefinementGeometryHom.comp sourceIso.inv sourceIso.hom =
    RefinementGeometryHom.id _ at hSource
  apply (cancel_mono sourceIso.hom).1
  change RefinementGeometryHom.comp
      (RefinementGeometryHom.comp endpointIso.inv
        (change.changedInput.generatedBaseRouteLegAt i)) sourceIso.hom =
    RefinementGeometryHom.comp
      (RefinementGeometryHom.comp (input.generatedBaseRouteLegAt i)
        sourceIso.inv) sourceIso.hom
  rw [UpperGeometryCleavage.refinementGeometryHom_comp_assoc,
    hfac,
    ← UpperGeometryCleavage.refinementGeometryHom_comp_assoc,
    hEndpoint,
    UpperGeometryCleavage.refinementGeometryHom_comp_assoc,
    hSource]
  have hidl :
      (𝟙 (⟨input.generatedBaseRouteGeometryAt i⟩ :
        RefinementGeometryCategory U)) ≫ input.generatedBaseRouteLegAt i =
        input.generatedBaseRouteLegAt i := Category.id_comp _
  change RefinementGeometryHom.comp (RefinementGeometryHom.id _)
      (input.generatedBaseRouteLegAt i) = input.generatedBaseRouteLegAt i at hidl
  have hidr : input.generatedBaseRouteLegAt i ≫
      (𝟙 (⟨(input.sourceGeometry i).package⟩ :
        RefinementGeometryCategory U)) = input.generatedBaseRouteLegAt i :=
    Category.comp_id _
  change RefinementGeometryHom.comp (input.generatedBaseRouteLegAt i)
      (RefinementGeometryHom.id _) = input.generatedBaseRouteLegAt i at hidr
  exact hidl.trans hidr.symm

/-- G-118 C1s base-endpoint coefficient law for `eta_B.hom`, forced by its
factorization together with the old, changed, and source coefficient laws. -/
theorem generatedBaseRouteExactGeometryIsoAt_hom_coefficient_id
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (change.generatedBaseRouteExactGeometryIsoAt i).hom.geometry.coefficientHom =
      RingHom.id k := by
  have h := congrArg (fun hom => hom.geometry.coefficientHom)
    (change.generatedBaseRouteExactGeometryIsoAt_hom_fac i)
  change
    (input.generatedBaseRouteLegAt i).geometry.coefficientHom.comp
        (change.generatedBaseRouteExactGeometryIsoAt i).hom.geometry.coefficientHom =
      (change.geometryIso i).hom.geometry.coefficientHom.comp
        (change.changedInput.generatedBaseRouteLegAt i).geometry.coefficientHom at h
  rw [input.generatedBaseRouteLegAt_coefficient_id,
    change.changedInput.generatedBaseRouteLegAt_coefficient_id,
    change.geometryIso_hom_coefficient_id] at h
  simpa only [RingHom.id_comp] using h

/-- G-118 C1s base-endpoint coefficient law for `eta_B.inv`, forced by the
reverse factorization and the corresponding inverse source coefficient law. -/
theorem generatedBaseRouteExactGeometryIsoAt_inv_coefficient_id
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (change.generatedBaseRouteExactGeometryIsoAt i).inv.geometry.coefficientHom =
      RingHom.id k := by
  have h := congrArg (fun hom => hom.geometry.coefficientHom)
    (change.generatedBaseRouteExactGeometryIsoAt_inv_fac i)
  change
    (change.changedInput.generatedBaseRouteLegAt i).geometry.coefficientHom.comp
        (change.generatedBaseRouteExactGeometryIsoAt i).inv.geometry.coefficientHom =
      (change.geometryIso i).inv.geometry.coefficientHom.comp
        (input.generatedBaseRouteLegAt i).geometry.coefficientHom at h
  rw [change.changedInput.generatedBaseRouteLegAt_coefficient_id,
    input.generatedBaseRouteLegAt_coefficient_id,
    change.geometryIso_inv_coefficient_id] at h
  simpa only [RingHom.id_comp] using h

/-- G-118 C1s primary pulled-endpoint factor law.  The independently generated
`eta_P.hom` is characterized by the pulled strongly-cartesian factorization. -/
theorem generatedPulledRouteExactGeometryIsoAt_hom_fac
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (exactGeometryToRefinementGeometry U).map
          (change.generatedPulledRouteExactGeometryIsoAt i).hom ≫
        input.generatedPulledRouteLegAt i =
      change.changedInput.generatedPulledRouteLegAt i ≫
        (exactGeometryToRefinementGeometry U).map (change.geometryIso i).hom := by
  rw [show (change.generatedPulledRouteExactGeometryIsoAt i).hom =
      change.generatedPulledRouteExactGeometryHomAt i from rfl,
    change.generatedPulledRouteExactGeometryHomAt_toRefinement]
  let oldLeg := input.generatedPulledRouteLegAt i
  let newLeg := change.changedInput.generatedPulledRouteLegAt i
  let sourceIso := (exactGeometryToRefinementGeometry U).mapIso
    (change.geometryIso i)
  let candidate := newLeg ≫ sourceIso.hom
  let lowerIso := (exactPackageToRefinement U).mapIso
    (change.generatedPulledRouteExactCoreIsoAt i)
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      oldLeg.base oldLeg := input.generatedPulledRouteLegAt_isStronglyCartesian i
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      newLeg.base newLeg :=
    change.changedInput.generatedPulledRouteLegAt_isStronglyCartesian i
  letI : (refinementGeometryProjection U).IsHomLift
      sourceIso.hom.base sourceIso.hom :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift sourceIso.hom
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      sourceIso.hom.base sourceIso.hom :=
    CategoryTheory.Functor.IsStronglyCartesian.of_isIso
      (p := refinementGeometryProjection U) (f := sourceIso.hom.base)
      sourceIso.hom
  letI : (refinementGeometryProjection U).IsStronglyCartesian
      candidate.base candidate := by
    dsimp only [candidate]
    exact CategoryTheory.Functor.IsStronglyCartesian.comp
      (refinementGeometryProjection U)
  have base_fac : candidate.base = lowerIso.hom ≫ oldLeg.base := by
    dsimp only [candidate, lowerIso, sourceIso, oldLeg, newLeg]
    exact (change.generatedPulledRouteExactCoreIsoAt_hom_fac i).symm
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (refinementGeometryProjection U)
    oldLeg.base oldLeg base_fac candidate

/-- G-118 C1s reverse pulled-endpoint factor law, derived from the primary
pulled factor law and the two actual isomorphism inverse laws. -/
theorem generatedPulledRouteExactGeometryIsoAt_inv_fac
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (exactGeometryToRefinementGeometry U).map
          (change.generatedPulledRouteExactGeometryIsoAt i).inv ≫
        change.changedInput.generatedPulledRouteLegAt i =
      input.generatedPulledRouteLegAt i ≫
        (exactGeometryToRefinementGeometry U).map (change.geometryIso i).inv := by
  let endpointIso := (exactGeometryToRefinementGeometry U).mapIso
    (change.generatedPulledRouteExactGeometryIsoAt i)
  let sourceIso := (exactGeometryToRefinementGeometry U).mapIso
    (change.geometryIso i)
  have hfac : RefinementGeometryHom.comp
      (change.changedInput.generatedPulledRouteLegAt i) sourceIso.hom =
    RefinementGeometryHom.comp endpointIso.hom
      (input.generatedPulledRouteLegAt i) :=
    (change.generatedPulledRouteExactGeometryIsoAt_hom_fac i).symm
  have hEndpoint := endpointIso.inv_hom_id
  change RefinementGeometryHom.comp endpointIso.inv endpointIso.hom =
    RefinementGeometryHom.id _ at hEndpoint
  have hSource := sourceIso.inv_hom_id
  change RefinementGeometryHom.comp sourceIso.inv sourceIso.hom =
    RefinementGeometryHom.id _ at hSource
  apply (cancel_mono sourceIso.hom).1
  change RefinementGeometryHom.comp
      (RefinementGeometryHom.comp endpointIso.inv
        (change.changedInput.generatedPulledRouteLegAt i)) sourceIso.hom =
    RefinementGeometryHom.comp
      (RefinementGeometryHom.comp (input.generatedPulledRouteLegAt i)
        sourceIso.inv) sourceIso.hom
  rw [UpperGeometryCleavage.refinementGeometryHom_comp_assoc,
    hfac,
    ← UpperGeometryCleavage.refinementGeometryHom_comp_assoc,
    hEndpoint,
    UpperGeometryCleavage.refinementGeometryHom_comp_assoc,
    hSource]
  have hidl :
      (𝟙 (⟨input.generatedPulledRouteGeometryAt i⟩ :
        RefinementGeometryCategory U)) ≫ input.generatedPulledRouteLegAt i =
        input.generatedPulledRouteLegAt i := Category.id_comp _
  change RefinementGeometryHom.comp (RefinementGeometryHom.id _)
      (input.generatedPulledRouteLegAt i) = input.generatedPulledRouteLegAt i at hidl
  have hidr : input.generatedPulledRouteLegAt i ≫
      (𝟙 (⟨(input.sourceGeometry i).package⟩ :
        RefinementGeometryCategory U)) = input.generatedPulledRouteLegAt i :=
    Category.comp_id _
  change RefinementGeometryHom.comp (input.generatedPulledRouteLegAt i)
      (RefinementGeometryHom.id _) = input.generatedPulledRouteLegAt i at hidr
  exact hidl.trans hidr.symm

/-- G-118 C1s pulled-endpoint coefficient law for `eta_P.hom`, derived from
the factor triangle and the old, changed, and source coefficient laws. -/
theorem generatedPulledRouteExactGeometryIsoAt_hom_coefficient_id
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (change.generatedPulledRouteExactGeometryIsoAt i).hom.geometry.coefficientHom =
      RingHom.id k := by
  have h := congrArg (fun hom => hom.geometry.coefficientHom)
    (change.generatedPulledRouteExactGeometryIsoAt_hom_fac i)
  change
    (input.generatedPulledRouteLegAt i).geometry.coefficientHom.comp
        (change.generatedPulledRouteExactGeometryIsoAt i).hom.geometry.coefficientHom =
      (change.geometryIso i).hom.geometry.coefficientHom.comp
        (change.changedInput.generatedPulledRouteLegAt i).geometry.coefficientHom at h
  rw [input.generatedPulledRouteLegAt_coefficient_id,
    change.changedInput.generatedPulledRouteLegAt_coefficient_id,
    change.geometryIso_hom_coefficient_id] at h
  simpa only [RingHom.id_comp] using h

/-- G-118 C1s pulled-endpoint coefficient law for `eta_P.inv`, derived from
the reverse factor triangle and the inverse source coefficient law. -/
theorem generatedPulledRouteExactGeometryIsoAt_inv_coefficient_id
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (change.generatedPulledRouteExactGeometryIsoAt i).inv.geometry.coefficientHom =
      RingHom.id k := by
  have h := congrArg (fun hom => hom.geometry.coefficientHom)
    (change.generatedPulledRouteExactGeometryIsoAt_inv_fac i)
  change
    (change.changedInput.generatedPulledRouteLegAt i).geometry.coefficientHom.comp
        (change.generatedPulledRouteExactGeometryIsoAt i).inv.geometry.coefficientHom =
      (change.geometryIso i).inv.geometry.coefficientHom.comp
        (input.generatedPulledRouteLegAt i).geometry.coefficientHom at h
  rw [change.changedInput.generatedPulledRouteLegAt_coefficient_id,
    input.generatedPulledRouteLegAt_coefficient_id,
    change.geometryIso_inv_coefficient_id] at h
  simpa only [RingHom.id_comp] using h

/-! ## Generated comparison-component naturality -/

/-- G-118 C3 lower naturality lemma.  The exact generated core mate square is
obtained by conjugating the actual `ctx.mate.naturality` equation by the
generated normalization isomorphisms. -/
theorem generatedCompatibleConjugateCoreMateAt_naturality
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (change.generatedBaseRouteExactCoreIsoAt i).hom ≫
        (input.generatedCompatibleConjugateCoreMateAt i).1 =
      (change.changedInput.generatedCompatibleConjugateCoreMateAt i).1 ≫
        (change.generatedPulledRouteExactCoreIsoAt i).hom := by
  have h :
      (((change.changedInput.generatedBaseRouteCoreIsoAt i) ≪≫
        (((ctx.legacyRegime).reverseBase ⋙
          exact_bottom_semantic_global_reindex_functor
            (ctx.configuration.pointedConfigurationAt ctx.source).pulledFst).mapIso
              (change.coreIso i)) ≪≫
        (input.generatedBaseRouteCoreIsoAt i).symm).hom ≫
          input.generatedCompatibleConjugateCoreMateAt i) =
      change.changedInput.generatedCompatibleConjugateCoreMateAt i ≫
        ((change.changedInput.generatedPulledRouteCoreIsoAt i) ≪≫
          ((exact_bottom_semantic_global_reindex_functor
              (ctx.configuration.pointedConfigurationAt ctx.source).pullbackFst ⋙
            (ctx.legacyRegime).reversePullback).mapIso (change.coreIso i)) ≪≫
          (input.generatedPulledRouteCoreIsoAt i).symm).hom := by
    dsimp [UpperGeometryCompatibleProblemInputData.generatedCompatibleConjugateCoreMateAt]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    simpa only [Functor.comp_map, Category.assoc] using
      congrArg
        (fun hom => (change.changedInput.generatedBaseRouteCoreIsoAt i).hom ≫
          hom ≫ (input.generatedPulledRouteCoreIsoAt i).inv)
        (ctx.mate.naturality (change.coreIso i).hom)
  exact congrArg
    (fun hom => CategoryTheory.Functor.Fiber.fiberInclusion.map hom) h

/-- G-118 C3 primary comparison-component naturality theorem.  The independently
generated old and changed mates satisfy `eta_P ∘ c' = c ∘ eta_B`; the result is
lifted from the lower naturality lemma using both mate triangles and
strongly-cartesian uniqueness. -/
theorem generatedCompatibleUpperGeometryMateAt_naturality
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    (change.generatedBaseRouteExactGeometryIsoAt i).hom.comp
        (input.generatedCompatibleUpperGeometryMateAt i) =
      (change.changedInput.generatedCompatibleUpperGeometryMateAt i).comp
        (change.generatedPulledRouteExactGeometryIsoAt i).hom := by
  apply (exactGeometryToRefinementGeometry U).map_injective
  let etaBase := (exactGeometryToRefinementGeometry U).map
    (change.generatedBaseRouteExactGeometryIsoAt i).hom
  let etaPulled := (exactGeometryToRefinementGeometry U).map
    (change.generatedPulledRouteExactGeometryIsoAt i).hom
  let oldMate := (exactGeometryToRefinementGeometry U).map
    (input.generatedCompatibleUpperGeometryMateAt i)
  let newMate := (exactGeometryToRefinementGeometry U).map
    (change.changedInput.generatedCompatibleUpperGeometryMateAt i)
  let oldPulledLeg := input.generatedPulledRouteLegAt i
  have hafterLeg :
      (etaBase ≫ oldMate) ≫ oldPulledLeg =
        (newMate ≫ etaPulled) ≫ oldPulledLeg := by
    calc
      (etaBase ≫ oldMate) ≫ oldPulledLeg =
          etaBase ≫ (oldMate ≫ oldPulledLeg) :=
        Category.assoc _ _ _
      _ = etaBase ≫ input.generatedBaseRouteLegAt i := by
        exact congrArg _ (input.generatedCompatibleUpperGeometryMateAt_triangle i)
      _ = change.changedInput.generatedBaseRouteLegAt i ≫
          (exactGeometryToRefinementGeometry U).map (change.geometryIso i).hom := by
        exact change.generatedBaseRouteExactGeometryIsoAt_hom_fac i
      _ = (newMate ≫ change.changedInput.generatedPulledRouteLegAt i) ≫
          (exactGeometryToRefinementGeometry U).map (change.geometryIso i).hom := by
        exact congrArg
          (fun hom => hom ≫
            (exactGeometryToRefinementGeometry U).map (change.geometryIso i).hom)
          (change.changedInput.generatedCompatibleUpperGeometryMateAt_triangle i).symm
      _ = newMate ≫
          (change.changedInput.generatedPulledRouteLegAt i ≫
            (exactGeometryToRefinementGeometry U).map (change.geometryIso i).hom) :=
        Category.assoc _ _ _
      _ = newMate ≫ (etaPulled ≫ oldPulledLeg) := by
        exact congrArg _
          (change.generatedPulledRouteExactGeometryIsoAt_hom_fac i).symm
      _ = (newMate ≫ etaPulled) ≫ oldPulledLeg :=
        (Category.assoc _ _ _).symm
  let left := (exactGeometryToRefinementGeometry U).map
    ((change.generatedBaseRouteExactGeometryIsoAt i).hom.comp
      (input.generatedCompatibleUpperGeometryMateAt i))
  let right := (exactGeometryToRefinementGeometry U).map
    ((change.changedInput.generatedCompatibleUpperGeometryMateAt i).comp
      (change.generatedPulledRouteExactGeometryIsoAt i).hom)
  have hafterLeg' : left.comp oldPulledLeg = right.comp oldPulledLeg := by
    exact hafterLeg
  have hleftBase : left.base = right.base := by
    change (exactPackageToRefinement U).map
        (((change.generatedBaseRouteExactGeometryIsoAt i).hom.comp
          (input.generatedCompatibleUpperGeometryMateAt i)).base) =
      (exactPackageToRefinement U).map
        (((change.changedInput.generatedCompatibleUpperGeometryMateAt i).comp
          (change.generatedPulledRouteExactGeometryIsoAt i).hom).base)
    apply congrArg (exactPackageToRefinement U).map
    change (change.generatedBaseRouteExactCoreIsoAt i).hom ≫
        (UpperGeometryCleavage.generatedRouteCoreMate
          (ctx.retarget (input.sourceFiberDiagram.obj ⟨i⟩))
          (input.sourceTargetGeometryAt i)).1 =
      (UpperGeometryCleavage.generatedRouteCoreMate
          (ctx.retarget (change.sourceFiber i))
          (change.changedInput.sourceTargetGeometryAt i)).1 ≫
        (change.generatedPulledRouteExactCoreIsoAt i).hom
    have hold := congrArg
      (fun hom => hom.1)
      (input.generatedCompatibleConjugateCoreMateAt_eq_generated i)
    have hnew := congrArg
      (fun hom => hom.1)
      (change.changedInput.generatedCompatibleConjugateCoreMateAt_eq_generated i)
    calc
      _ = (change.generatedBaseRouteExactCoreIsoAt i).hom ≫
          (input.generatedCompatibleConjugateCoreMateAt i).1 :=
        congrArg _ hold.symm
      _ = (change.changedInput.generatedCompatibleConjugateCoreMateAt i).1 ≫
          (change.generatedPulledRouteExactCoreIsoAt i).hom :=
        change.generatedCompatibleConjugateCoreMateAt_naturality i
      _ = _ := congrArg
        (fun hom => hom ≫
          (change.generatedPulledRouteExactCoreIsoAt i).hom) hnew
  letI hleftLift :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
      right.base left hleftBase
  letI hrightLift :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
      right.base right rfl
  letI := input.generatedPulledRouteLegAt_isStronglyCartesian i
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (refinementGeometryProjection U)
    oldPulledLeg.base oldPulledLeg right.base
  exact hafterLeg'

end UpperGeometryCompatibleSourcePresentationChange

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
