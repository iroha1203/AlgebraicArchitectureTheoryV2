import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryFiniteMate

/-!
# Finite core naturality of the generated upper geometry mate

The generated route endpoints are compared with the actual G-114 route
diagrams at every finite-presentation vertex.  Conjugating the actual diagrams
by these exact fiber isomorphisms produces the literal core diagrams underlying
the generated geometry family.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation CrossStageCoherence GeometryTransport

namespace UpperGeometryCleavage

set_option maxHeartbeats 3000000

/-- Recover an exact vertical core morphism from a refinement comparison whose
lower map is the exact endpoint transport. -/
noncomputable def exactCoreHomOfRefinementComparison
    {X : ExtractionInstance U} (source target : CoreFiber X)
    (comparison : RefinementPackageHom ⟨source.1⟩ ⟨target.1⟩)
    (hbase : comparison.base =
      (exactPointedToRefinement U).map
        (eqToHom (source.2.trans target.2.symm))) :
    source ⟶ target := by
  let total : PackageTotalHom source.1 target.1 := {
    base := eqToHom (source.2.trans target.2.symm)
    upper := comparison.upper
    atomEquiv_eq := by
      rw [comparison.atomEquiv_eq, hbase]
      rw [exactPointedToRefinement_map_eqToHom]
      apply Equiv.ext
      intro atom
      simp [ExtInstHom.eqToHom_atomEquiv]
  }
  refine ⟨total, ?_⟩
  apply CategoryTheory.IsHomLift.of_fac'
    (packageProjection U) (𝟙 X) total source.2 target.2
  change eqToHom (source.2.trans target.2.symm) =
    eqToHom source.2 ≫ 𝟙 X ≫ eqToHom target.2.symm
  simp

/-- Exactification followed by refinement embedding recovers the supplied
complete comparison. -/
theorem exactCoreHomOfRefinementComparison_toRefinement
    {X : ExtractionInstance U} (source target : CoreFiber X)
    (comparison : RefinementPackageHom ⟨source.1⟩ ⟨target.1⟩)
    (hbase : comparison.base =
      (exactPointedToRefinement U).map
        (eqToHom (source.2.trans target.2.symm))) :
    (exactPackageToRefinement U).map
        (exactCoreHomOfRefinementComparison source target comparison hbase).1 =
      comparison := by
  unfold exactCoreHomOfRefinementComparison
  apply RefinementPackageHom.ext
  · change PointedRefinementHom.ofExact
      (eqToHom (source.2.trans target.2.symm)) = comparison.base
    rw [hbase]
    rfl
  · rfl

/-- Exact core realization of the generated-to-actual base comparison. -/
noncomputable def baseRouteComparisonCoreHom
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    baseRouteCoreFiber ctx target ⟶
      (retargetedContext ctx target).baseMatePackage :=
  exactCoreHomOfRefinementComparison _ _
    (baseRouteComparisonHom ctx target) (by
      rw [baseRouteComparisonHom_base]
      rfl)

/-- The exact base comparison embeds to the universal refinement comparison. -/
theorem baseRouteComparisonCoreHom_toRefinement
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (exactPackageToRefinement U).map
        (baseRouteComparisonCoreHom ctx target).1 =
      baseRouteComparisonHom ctx target := by
  unfold baseRouteComparisonCoreHom
  apply exactCoreHomOfRefinementComparison_toRefinement

/-- Exact core realization of the actual-to-generated base comparison. -/
noncomputable def baseRouteComparisonCoreInv
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (retargetedContext ctx target).baseMatePackage ⟶
      baseRouteCoreFiber ctx target :=
  exactCoreHomOfRefinementComparison _ _
    (baseRouteComparisonInv ctx target) (by
      rw [baseRouteComparisonInv_base]
      rfl)

/-- The exact inverse base comparison embeds to its refinement inverse. -/
theorem baseRouteComparisonCoreInv_toRefinement
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (exactPackageToRefinement U).map
        (baseRouteComparisonCoreInv ctx target).1 =
      baseRouteComparisonInv ctx target := by
  unfold baseRouteComparisonCoreInv
  apply exactCoreHomOfRefinementComparison_toRefinement

/-- The universal base-route comparison lifted to an exact core isomorphism. -/
noncomputable def baseRouteComparisonCoreIso
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    baseRouteCoreFiber ctx target ≅
      (retargetedContext ctx target).baseMatePackage where
  hom := baseRouteComparisonCoreHom ctx target
  inv := baseRouteComparisonCoreInv ctx target
  hom_inv_id := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    apply exactPackageToRefinement_map_injective
    change (exactPackageToRefinement U).map
        (baseRouteComparisonCoreHom ctx target).1 ≫
      (exactPackageToRefinement U).map
        (baseRouteComparisonCoreInv ctx target).1 = 𝟙 _
    rw [baseRouteComparisonCoreHom_toRefinement,
      baseRouteComparisonCoreInv_toRefinement]
    exact (baseRouteComparisonIso ctx target).hom_inv_id
  inv_hom_id := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    apply exactPackageToRefinement_map_injective
    change (exactPackageToRefinement U).map
        (baseRouteComparisonCoreInv ctx target).1 ≫
      (exactPackageToRefinement U).map
        (baseRouteComparisonCoreHom ctx target).1 = 𝟙 _
    rw [baseRouteComparisonCoreInv_toRefinement,
      baseRouteComparisonCoreHom_toRefinement]
    exact (baseRouteComparisonIso ctx target).inv_hom_id

/-- Exact core realization of the generated-to-actual pulled comparison. -/
noncomputable def pulledRouteComparisonCoreHom
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    pulledRouteCoreFiber ctx target ⟶
      (retargetedContext ctx target).pulledMatePackage :=
  exactCoreHomOfRefinementComparison _ _
    (pulledRouteComparisonHom ctx target) (by
      rw [pulledRouteComparisonHom_base]
      rfl)

/-- The exact pulled comparison embeds to the universal refinement comparison. -/
theorem pulledRouteComparisonCoreHom_toRefinement
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (exactPackageToRefinement U).map
        (pulledRouteComparisonCoreHom ctx target).1 =
      pulledRouteComparisonHom ctx target := by
  unfold pulledRouteComparisonCoreHom
  apply exactCoreHomOfRefinementComparison_toRefinement

/-- Exact core realization of the actual-to-generated pulled comparison. -/
noncomputable def pulledRouteComparisonCoreInv
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (retargetedContext ctx target).pulledMatePackage ⟶
      pulledRouteCoreFiber ctx target :=
  exactCoreHomOfRefinementComparison _ _
    (pulledRouteComparisonInv ctx target) (by
      rw [pulledRouteComparisonInv_base]
      rfl)

/-- The exact inverse pulled comparison embeds to its refinement inverse. -/
theorem pulledRouteComparisonCoreInv_toRefinement
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (exactPackageToRefinement U).map
        (pulledRouteComparisonCoreInv ctx target).1 =
      pulledRouteComparisonInv ctx target := by
  unfold pulledRouteComparisonCoreInv
  apply exactCoreHomOfRefinementComparison_toRefinement

/-- The universal pulled-route comparison lifted to an exact core isomorphism. -/
noncomputable def pulledRouteComparisonCoreIso
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    pulledRouteCoreFiber ctx target ≅
      (retargetedContext ctx target).pulledMatePackage where
  hom := pulledRouteComparisonCoreHom ctx target
  inv := pulledRouteComparisonCoreInv ctx target
  hom_inv_id := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    apply exactPackageToRefinement_map_injective
    change (exactPackageToRefinement U).map
        (pulledRouteComparisonCoreHom ctx target).1 ≫
      (exactPackageToRefinement U).map
        (pulledRouteComparisonCoreInv ctx target).1 = 𝟙 _
    rw [pulledRouteComparisonCoreHom_toRefinement,
      pulledRouteComparisonCoreInv_toRefinement]
    exact (pulledRouteComparisonIso ctx target).hom_inv_id
  inv_hom_id := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    apply exactPackageToRefinement_map_injective
    change (exactPackageToRefinement U).map
        (pulledRouteComparisonCoreInv ctx target).1 ≫
      (exactPackageToRefinement U).map
        (pulledRouteComparisonCoreHom ctx target).1 = 𝟙 _
    rw [pulledRouteComparisonCoreInv_toRefinement,
      pulledRouteComparisonCoreHom_toRefinement]
    exact (pulledRouteComparisonIso ctx target).inv_hom_id

end UpperGeometryCleavage

namespace UpperRefinementBCProblemData

set_option maxHeartbeats 3000000

/-- Exact comparison from the generated base endpoint to the actual G-114 endpoint. -/
noncomputable def generatedBaseCoreIsoAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k) (i : P.Vertex) :
  UpperGeometryCleavage.baseRouteCoreFiber
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
        (problem.generatedTargetGeometryAt i) ≅
      (ctx.baseCoreDiagram problem.sourceFiberDiagram).obj ⟨i⟩ := by
  exact UpperGeometryCleavage.baseRouteComparisonCoreIso
    (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
    (problem.generatedTargetGeometryAt i)

/-- Exact comparison from the generated pulled endpoint to the actual G-114 endpoint. -/
noncomputable def generatedPulledCoreIsoAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k) (i : P.Vertex) :
    UpperGeometryCleavage.pulledRouteCoreFiber
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
        (problem.generatedTargetGeometryAt i) ≅
      (ctx.pulledCoreDiagram problem.sourceFiberDiagram).obj ⟨i⟩ := by
  exact UpperGeometryCleavage.pulledRouteComparisonCoreIso
    (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
    (problem.generatedTargetGeometryAt i)

/-- The actual base diagram conjugated onto the generated base endpoints. -/
noncomputable def generatedBaseCoreDiagram
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k) :
    PresentedPathCategory P ⥤
      CoreFiber (ctx.configuration.pullbackSourceAt ctx.source) where
  obj W := UpperGeometryCleavage.baseRouteCoreFiber
    (ctx.retarget (problem.sourceFiberDiagram.obj W))
    (problem.generatedTargetGeometryAt W.vertex)
  map {W V} path :=
    (problem.generatedBaseCoreIsoAt W.vertex).hom ≫
      (ctx.baseCoreDiagram problem.sourceFiberDiagram).map path ≫
        (problem.generatedBaseCoreIsoAt V.vertex).inv
  map_id W := by simp
  map_comp first second := by simp [Category.assoc]

/-- The actual pulled diagram conjugated onto the generated pulled endpoints. -/
noncomputable def generatedPulledCoreDiagram
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k) :
    PresentedPathCategory P ⥤
      CoreFiber (ctx.configuration.pullbackSourceAt ctx.source) where
  obj W := UpperGeometryCleavage.pulledRouteCoreFiber
    (ctx.retarget (problem.sourceFiberDiagram.obj W))
    (problem.generatedTargetGeometryAt W.vertex)
  map {W V} path :=
    (problem.generatedPulledCoreIsoAt W.vertex).hom ≫
      (ctx.pulledCoreDiagram problem.sourceFiberDiagram).map path ≫
        (problem.generatedPulledCoreIsoAt V.vertex).inv
  map_id W := by simp
  map_comp first second := by simp [Category.assoc]

/-- The exact G-114 mate conjugated onto the two generated endpoint families. -/
noncomputable def generatedConjugateCoreMateAt
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k) (i : P.Vertex) :
    (problem.generatedBaseCoreDiagram.obj ⟨i⟩) ⟶
      (problem.generatedPulledCoreDiagram.obj ⟨i⟩) :=
  (problem.generatedBaseCoreIsoAt i).hom ≫
    ctx.mate.app (problem.sourceFiberDiagram.obj ⟨i⟩) ≫
      (problem.generatedPulledCoreIsoAt i).inv

/-- Refinement embedding identifies the conjugated exact component with the
G-114 mate transported by the universal route comparisons. -/
theorem generatedConjugateCoreMateAt_toRefinement
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k) (i : P.Vertex) :
    (exactPackageToRefinement U).map
        (problem.generatedConjugateCoreMateAt i).1 =
      UpperGeometryCleavage.transportedG114RefinementMate
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
        (problem.generatedTargetGeometryAt i) := by
  unfold generatedConjugateCoreMateAt generatedBaseCoreIsoAt
    generatedPulledCoreIsoAt
  change (exactPackageToRefinement U).map
      (UpperGeometryCleavage.baseRouteComparisonCoreHom
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
        (problem.generatedTargetGeometryAt i)).1 ≫
    (exactPackageToRefinement U).map
      (ctx.mate.app (problem.sourceFiberDiagram.obj ⟨i⟩)).1 ≫
    (exactPackageToRefinement U).map
      (UpperGeometryCleavage.pulledRouteComparisonCoreInv
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
        (problem.generatedTargetGeometryAt i)).1 = _
  rw [UpperGeometryCleavage.baseRouteComparisonCoreHom_toRefinement,
    UpperGeometryCleavage.pulledRouteComparisonCoreInv_toRefinement]
  rfl

/-- The conjugated actual G-114 component is the pointwise generated exact
core mate. -/
theorem generatedConjugateCoreMateAt_eq_generated
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k) (i : P.Vertex) :
    problem.generatedConjugateCoreMateAt i =
      UpperGeometryCleavage.generatedRouteCoreMate
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
        (problem.generatedTargetGeometryAt i) := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  apply exactPackageToRefinement_map_injective
  change (exactPackageToRefinement U).map
      (problem.generatedConjugateCoreMateAt i).1 =
    (exactPackageToRefinement U).map
      (UpperGeometryCleavage.generatedRouteCoreMate
        (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
        (problem.generatedTargetGeometryAt i)).1
  rw [problem.generatedConjugateCoreMateAt_toRefinement,
    UpperGeometryCleavage.generatedRouteCoreMate_toRefinement,
    UpperGeometryCleavage.transportedG114RefinementMate_eq_generated]

/-- The conjugated exact core mate is natural along every presented path. -/
theorem generatedConjugateCoreMateAt_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k)
    {i j : P.Vertex} (path : P.Path i j) :
    problem.generatedBaseCoreDiagram.map path ≫
        problem.generatedConjugateCoreMateAt j =
      problem.generatedConjugateCoreMateAt i ≫
        problem.generatedPulledCoreDiagram.map path := by
  dsimp [generatedBaseCoreDiagram, generatedPulledCoreDiagram,
    generatedConjugateCoreMateAt]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simp only [ActiveRefinementBCContext.baseCoreDiagram,
    ActiveRefinementBCContext.pulledCoreDiagram, Functor.comp_map]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg
      (fun hom => (problem.generatedBaseCoreIsoAt i).hom ≫ hom ≫
        (problem.generatedPulledCoreIsoAt j).inv)
      (ctx.mate.naturality (problem.sourceFiberDiagram.map path))

/-- The pointwise generated exact core mate is natural along every presented
path after transporting the actual G-114 route diagrams to generated
endpoints. -/
theorem generatedRouteCoreMateAt_naturality
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k)
    {i j : P.Vertex} (path : P.Path i j) :
    problem.generatedBaseCoreDiagram.map path ≫
        UpperGeometryCleavage.generatedRouteCoreMate
          (ctx.retarget (problem.sourceFiberDiagram.obj ⟨j⟩))
          (problem.generatedTargetGeometryAt j) =
      UpperGeometryCleavage.generatedRouteCoreMate
          (ctx.retarget (problem.sourceFiberDiagram.obj ⟨i⟩))
          (problem.generatedTargetGeometryAt i) ≫
        problem.generatedPulledCoreDiagram.map path := by
  rw [← problem.generatedConjugateCoreMateAt_eq_generated i,
    ← problem.generatedConjugateCoreMateAt_eq_generated j]
  exact problem.generatedConjugateCoreMateAt_naturality path

/-- The finite natural transformation carried by the conjugated G-114 mate. -/
noncomputable def generatedConjugateCoreMate
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k) :
  problem.generatedBaseCoreDiagram ⟶ problem.generatedPulledCoreDiagram where
  app W := problem.generatedConjugateCoreMateAt W.vertex
  naturality _ _ path := problem.generatedConjugateCoreMateAt_naturality path

/-- The pointwise generated exact mates assembled as a finite natural
transformation. -/
noncomputable def generatedRouteCoreMateNatTrans
    {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
    {P : TransportCoherence.FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
    (problem : UpperRefinementBCProblemData ctx P k) :
    problem.generatedBaseCoreDiagram ⟶ problem.generatedPulledCoreDiagram where
  app W := UpperGeometryCleavage.generatedRouteCoreMate
    (ctx.retarget (problem.sourceFiberDiagram.obj W))
    (problem.generatedTargetGeometryAt W.vertex)
  naturality _ _ path := problem.generatedRouteCoreMateAt_naturality path

end UpperRefinementBCProblemData
end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
