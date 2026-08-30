import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryMateIdentification

/-!
# Isomorphism carried by the generated upper route mate

The forward and inverse comparisons generated from the two strongly cartesian
G-115 route legs are inverse as complete refinement-package morphisms.  Their
exact embeddings therefore form an isomorphism in the common core fiber.  This
is the reversible core API on which the geometry-level mate is constructed;
the completed G-112 and G-114 declarations remain unchanged.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation CrossStageCoherence GeometryTransport

namespace UpperGeometryCleavage

/-- The inverse and forward endpoint transports cancel at the pulled route source. -/
theorem routeSourceBase_comp_forward
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (routeSourceBase ctx target).comp (routeSourceForward ctx target) =
      PointedRefinementHom.id
        (packagePoint (pulledRouteGeometry ctx target).core) := by
  change
    (exactPointedToRefinement U).map
        (eqToHom ((pulledRouteGeometry_packagePoint_eq ctx target).trans
          (baseRouteGeometry_packagePoint_eq ctx target).symm)) ≫
      (exactPointedToRefinement U).map
        (eqToHom ((baseRouteGeometry_packagePoint_eq ctx target).trans
          (pulledRouteGeometry_packagePoint_eq ctx target).symm)) =
        𝟙 _
  rw [← Functor.map_comp]
  simp

/-- The universally generated route mate and its inverse form a complete
refinement-package isomorphism. -/
noncomputable def generatedRouteRefinementMateIso
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (⟨(baseRouteGeometry ctx target).core⟩ : RefinementPackageObject U) ≅
      ⟨(pulledRouteGeometry ctx target).core⟩ where
  hom := generatedRouteRefinementMate ctx target
  inv := generatedRouteRefinementMateInverse ctx target
  hom_inv_id := by
    letI hhom := generatedRouteRefinementMate_isHomLift ctx target
    letI hinv : (refinementPackageProjection U).IsHomLift
        (routeSourceBase ctx target)
        (generatedRouteRefinementMateInverse ctx target) := by
      letI := baseRouteGeometryBase_isStronglyCartesian ctx target
      letI := pulledRouteGeometryBase_isStronglyCartesian ctx target
      unfold generatedRouteRefinementMateInverse
      infer_instance
    letI hcomp : (refinementPackageProjection U).IsHomLift
        ((routeSourceForward ctx target).comp (routeSourceBase ctx target))
        ((generatedRouteRefinementMate ctx target).comp
          (generatedRouteRefinementMateInverse ctx target)) :=
      refinementPackageHom_isHomLift_of_base_eq _ _ (by
        change (generatedRouteRefinementMate ctx target).base.comp
          (generatedRouteRefinementMateInverse ctx target).base = _
        letI := generatedRouteRefinementMate_isHomLift ctx target
        have hforward := generatedRouteRefinementMate_base ctx target
        have hinverse := CategoryTheory.IsHomLift.eq_of_isHomLift
          (refinementPackageProjection U) (routeSourceBase ctx target)
          (generatedRouteRefinementMateInverse ctx target)
        change routeSourceBase ctx target =
          (generatedRouteRefinementMateInverse ctx target).base at hinverse
        rw [hforward, ← hinverse])
    letI hid : (refinementPackageProjection U).IsHomLift
        ((routeSourceForward ctx target).comp (routeSourceBase ctx target))
        (𝟙 (⟨(baseRouteGeometry ctx target).core⟩ :
          RefinementPackageObject U)) := by
      apply refinementPackageHom_isHomLift_of_base_eq
      rw [routeSourceForward_comp_base]
      rfl
    letI := baseRouteGeometryBase_isStronglyCartesian ctx target
    apply CategoryTheory.Functor.IsStronglyCartesian.ext
      (refinementPackageProjection U)
      (baseRouteGeometryHom ctx target).base.base
      (baseRouteGeometryHom ctx target).base
      ((routeSourceForward ctx target).comp (routeSourceBase ctx target))
    calc
      (generatedRouteRefinementMate ctx target ≫
          generatedRouteRefinementMateInverse ctx target) ≫
          (baseRouteGeometryHom ctx target).base =
        generatedRouteRefinementMate ctx target ≫
          (generatedRouteRefinementMateInverse ctx target ≫
            (baseRouteGeometryHom ctx target).base) :=
          Category.assoc _ _ _
      _ = generatedRouteRefinementMate ctx target ≫
          (pulledRouteGeometryHom ctx target).base := by
            exact congrArg
              (fun leg => (generatedRouteRefinementMate ctx target).comp leg)
              (generatedRouteRefinementMateInverse_fac ctx target)
      _ = (baseRouteGeometryHom ctx target).base :=
        generatedRouteRefinementMate_fac ctx target
      _ = 𝟙 (⟨(baseRouteGeometry ctx target).core⟩ :
          RefinementPackageObject U) ≫
          (baseRouteGeometryHom ctx target).base := by simp
  inv_hom_id := by
    letI hhom := generatedRouteRefinementMate_isHomLift ctx target
    letI hinv : (refinementPackageProjection U).IsHomLift
        (routeSourceBase ctx target)
        (generatedRouteRefinementMateInverse ctx target) := by
      letI := baseRouteGeometryBase_isStronglyCartesian ctx target
      letI := pulledRouteGeometryBase_isStronglyCartesian ctx target
      unfold generatedRouteRefinementMateInverse
      infer_instance
    letI hcomp : (refinementPackageProjection U).IsHomLift
        ((routeSourceBase ctx target).comp (routeSourceForward ctx target))
        ((generatedRouteRefinementMateInverse ctx target).comp
          (generatedRouteRefinementMate ctx target)) :=
      refinementPackageHom_isHomLift_of_base_eq _ _ (by
        change (generatedRouteRefinementMateInverse ctx target).base.comp
          (generatedRouteRefinementMate ctx target).base = _
        have hinverse := CategoryTheory.IsHomLift.eq_of_isHomLift
          (refinementPackageProjection U) (routeSourceBase ctx target)
          (generatedRouteRefinementMateInverse ctx target)
        change routeSourceBase ctx target =
          (generatedRouteRefinementMateInverse ctx target).base at hinverse
        rw [generatedRouteRefinementMate_base, ← hinverse])
    letI hid : (refinementPackageProjection U).IsHomLift
        ((routeSourceBase ctx target).comp (routeSourceForward ctx target))
        (𝟙 (⟨(pulledRouteGeometry ctx target).core⟩ :
          RefinementPackageObject U)) := by
      apply refinementPackageHom_isHomLift_of_base_eq
      rw [routeSourceBase_comp_forward]
      rfl
    letI := pulledRouteGeometryBase_isStronglyCartesian ctx target
    apply CategoryTheory.Functor.IsStronglyCartesian.ext
      (refinementPackageProjection U)
      (pulledRouteGeometryHom ctx target).base.base
      (pulledRouteGeometryHom ctx target).base
      ((routeSourceBase ctx target).comp (routeSourceForward ctx target))
    calc
      (generatedRouteRefinementMateInverse ctx target ≫
          generatedRouteRefinementMate ctx target) ≫
          (pulledRouteGeometryHom ctx target).base =
        generatedRouteRefinementMateInverse ctx target ≫
          (generatedRouteRefinementMate ctx target ≫
            (pulledRouteGeometryHom ctx target).base) :=
          Category.assoc _ _ _
      _ = generatedRouteRefinementMateInverse ctx target ≫
          (baseRouteGeometryHom ctx target).base := by
            exact congrArg
              (fun leg =>
                (generatedRouteRefinementMateInverse ctx target).comp leg)
              (generatedRouteRefinementMate_fac ctx target)
      _ = (pulledRouteGeometryHom ctx target).base :=
        generatedRouteRefinementMateInverse_fac ctx target
      _ = 𝟙 (⟨(pulledRouteGeometry ctx target).core⟩ :
          RefinementPackageObject U) ≫
          (pulledRouteGeometryHom ctx target).base := by simp

/-- The inverse universal comparison packaged as an exact vertical core-fiber
morphism. -/
noncomputable def generatedRouteCoreMateInverse
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    pulledRouteCoreFiber ctx target ⟶ baseRouteCoreFiber ctx target := by
  let comparison := generatedRouteRefinementMateInverse ctx target
  let total : PackageTotalHom
      (pulledRouteGeometry ctx target).core
      (baseRouteGeometry ctx target).core := {
    base := eqToHom ((pulledRouteGeometry_packagePoint_eq ctx target).trans
      (baseRouteGeometry_packagePoint_eq ctx target).symm)
    upper := comparison.upper
    atomEquiv_eq := by
      rw [comparison.atomEquiv_eq]
      letI : (refinementPackageProjection U).IsHomLift
          (routeSourceBase ctx target) comparison := by
        letI := baseRouteGeometryBase_isStronglyCartesian ctx target
        letI := pulledRouteGeometryBase_isStronglyCartesian ctx target
        unfold comparison generatedRouteRefinementMateInverse
        infer_instance
      have hfac := CategoryTheory.IsHomLift.fac'
        (refinementPackageProjection U) (routeSourceBase ctx target) comparison
      have hatom := congrArg (fun hom => hom.doctrineHom.atomEquiv) hfac
      apply Equiv.ext
      intro atom
      have hatom' := congrFun (congrArg Equiv.toFun hatom) atom
      simpa [routeSourceBase, ExtInstHom.eqToHom_atomEquiv] using hatom'
  }
  refine ⟨total, ?_⟩
  apply CategoryTheory.IsHomLift.of_fac'
    (packageProjection U)
    (𝟙 (ctx.configuration.pullbackSourceAt ctx.source)) total
    (pulledRouteGeometry_packagePoint_eq ctx target)
    (baseRouteGeometry_packagePoint_eq ctx target)
  change
    eqToHom ((pulledRouteGeometry_packagePoint_eq ctx target).trans
      (baseRouteGeometry_packagePoint_eq ctx target).symm) ≫
        eqToHom (baseRouteGeometry_packagePoint_eq ctx target) =
      eqToHom (pulledRouteGeometry_packagePoint_eq ctx target) ≫ 𝟙 _
  simp

/-- Exact embedding recovers the inverse generated refinement comparison. -/
theorem generatedRouteCoreMateInverse_toRefinement
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (exactPackageToRefinement U).map
        (generatedRouteCoreMateInverse ctx target).1 =
      generatedRouteRefinementMateInverse ctx target := by
  apply RefinementPackageHom.ext
  · change routeSourceBase ctx target =
      (generatedRouteRefinementMateInverse ctx target).base
    letI : (refinementPackageProjection U).IsHomLift
        (routeSourceBase ctx target)
        (generatedRouteRefinementMateInverse ctx target) := by
      letI := baseRouteGeometryBase_isStronglyCartesian ctx target
      letI := pulledRouteGeometryBase_isStronglyCartesian ctx target
      unfold generatedRouteRefinementMateInverse
      infer_instance
    exact CategoryTheory.IsHomLift.eq_of_isHomLift
      (refinementPackageProjection U) (routeSourceBase ctx target)
      (generatedRouteRefinementMateInverse ctx target)
  · rfl

/-- The exact core mate is an isomorphism before geometry data are attached. -/
noncomputable def generatedRouteCoreMateIso
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    baseRouteCoreFiber ctx target ≅ pulledRouteCoreFiber ctx target where
  hom := generatedRouteCoreMate ctx target
  inv := generatedRouteCoreMateInverse ctx target
  hom_inv_id := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    apply exactPackageToRefinement_map_injective
    change (exactPackageToRefinement U).map
        (generatedRouteCoreMate ctx target).1 ≫
          (exactPackageToRefinement U).map
            (generatedRouteCoreMateInverse ctx target).1 = 𝟙 _
    rw [generatedRouteCoreMate_toRefinement,
      generatedRouteCoreMateInverse_toRefinement]
    exact (generatedRouteRefinementMateIso ctx target).hom_inv_id
  inv_hom_id := by
    apply CategoryTheory.Functor.Fiber.hom_ext
    apply exactPackageToRefinement_map_injective
    change (exactPackageToRefinement U).map
        (generatedRouteCoreMateInverse ctx target).1 ≫
          (exactPackageToRefinement U).map
            (generatedRouteCoreMate ctx target).1 = 𝟙 _
    rw [generatedRouteCoreMateInverse_toRefinement,
      generatedRouteCoreMate_toRefinement]
    exact (generatedRouteRefinementMateIso ctx target).inv_hom_id

end UpperGeometryCleavage

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct.UpperGeometryCleavage
