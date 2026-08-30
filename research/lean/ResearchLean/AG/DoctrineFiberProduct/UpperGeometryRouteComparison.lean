import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryMateSquare

/-!
# Complete route comparisons for the upper geometry mate

The geometry-generated routes and the completed G-114 routes have the same
authored lower composites but independently selected source packages. This
module normalizes their lower endpoint transports inside G-115, then uses the
strong-cartesian universal property to generate complete package comparison
isomorphisms with both factor triangles. Completed predecessor APIs are read
only inputs.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation CrossStageCoherence GeometryTransport

namespace UpperGeometryCleavage

set_option maxHeartbeats 2000000

theorem exactLiftRefinementBase_eq_casts
    {X Y : ExtractionInstance U} (g : X ⟶ Y)
    (target : CoreFiber Y)
    (lift : StrongCartesianLift (cartSemanticInputOfHom g) target) :
    ((exactPackageToRefinement U).map lift.hom).base =
      (exactPointedToRefinement U).map (eqToHom lift.domainObject.2) ≫
        PointedRefinementHom.ofExact g ≫
        (exactPointedToRefinement U).map (eqToHom target.2.symm) := by
  change PointedRefinementHom.ofExact ((packageProjection U).map lift.hom) = _
  letI := lift.isStronglyCartesian
  rw [CategoryTheory.IsHomLift.fac'
    (packageProjection U) (cartSemanticInputOfHom g).hom lift.hom]
  rfl

theorem refinementPackageHomOfOver_base_eq_casts
    {X Y : ExtractionInstance U} {f : PointedRefinementHom X Y}
    {source : CoreFiber X} {target : CoreFiber Y}
    (hom : RefinementOverHom f source target) :
    (refinementPackageHomOfOver hom).base =
      (exactPointedToRefinement U).map (eqToHom source.2) ≫ f ≫
        (exactPointedToRefinement U).map (eqToHom target.2.symm) := by
  rcases hom with ⟨lower, rfl, upper, atom⟩
  rfl

theorem refinementPackageHom_isHomLift_of_base_eq
    {P Q : RefinementPackageObject U}
    (g : PointedRefinementHom (packagePoint P.package)
      (packagePoint Q.package))
    (hom : RefinementPackageHom P Q) (hbase : hom.base = g) :
    (refinementPackageProjection U).IsHomLift g hom := by
  apply CategoryTheory.IsHomLift.of_fac'
    (refinementPackageProjection U) g hom rfl rfl
  simpa using hbase

noncomputable def baseRouteActualSource
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    PointedRefinementHom
      (packagePoint (baseRouteGeometry ctx target).core)
      (packagePoint (retargetedContext ctx target).baseMatePackage.1) :=
  (exactPointedToRefinement U).map <| eqToHom <|
    (baseRouteGeometry_packagePoint_eq ctx target).trans
      (retargetedContext ctx target).baseMatePackage.2.symm

theorem baseRouteActualSource_fac
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (baseRouteActualSource ctx target).comp
        (retargetedContext ctx target).baseCompositeLeg.base =
      (baseRouteGeometryHom ctx target).base.base := by
  change baseRouteActualSource ctx target ≫
      ((exactPackageToRefinement U).map
        (exact_bottom_semantic_global_selected_lift
          (ctx.configuration.pointedConfigurationAt ctx.source).pulledFst
          (((retargetedContext ctx target).legacyRegime).reverseBase.obj
            (retargetedContext ctx target).targetPackage)).hom).base ≫
      (refinementPackageHomOfOver
        (((retargetedContext ctx target).legacyRegime).baseCleavage.lift
          (retargetedContext ctx target).targetPackage).hom).base =
    (exactPointedToRefinement U).map (baseRouteExactArrow ctx target) ≫
      (refinementBaseHom target.geometry
        (ctx.configuration.baseRefinementAt ctx.source) ctx.condition
        target.packagePoint_eq).base
  rw [refinementBaseHom_base_eq_casts]
  rw [exactLiftRefinementBase_eq_casts,
    refinementPackageHomOfOver_base_eq_casts]
  unfold baseRouteActualSource baseRouteExactArrow
  simp only [Functor.map_comp, exactPointedToRefinement_map_eqToHom]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  simp [retargetedContext, ActiveRefinementBCContext.retarget,
    RefinementBCConfiguration.pointedConfigurationAt,
    pointedRefinementCategory, PointedRefinementHom.comp,
    PointedRefinementHom.id, refinementHomComp, refinementHomId,
    exactPointedToRefinement, PointedRefinementHom.ofExact,
    exactToRefinement, Function.comp_def]
  rfl

noncomputable def pulledRouteActualSource
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    PointedRefinementHom
      (packagePoint (pulledRouteGeometry ctx target).core)
      (packagePoint (retargetedContext ctx target).pulledMatePackage.1) :=
  (exactPointedToRefinement U).map <| eqToHom <|
    (pulledRouteGeometry_packagePoint_eq ctx target).trans
      (retargetedContext ctx target).pulledMatePackage.2.symm

theorem pulledRouteActualSource_fac
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (pulledRouteActualSource ctx target).comp
        (retargetedContext ctx target).pulledCompositeLeg.base =
      (pulledRouteGeometryHom ctx target).base.base := by
  change pulledRouteActualSource ctx target ≫
      (refinementPackageHomOfOver
        (((retargetedContext ctx target).legacyRegime).pulledCleavage.lift
          (retargetedContext ctx target).pullbackTargetPackage).hom).base ≫
      ((exactPackageToRefinement U).map
        (exact_bottom_semantic_global_selected_lift
          (ctx.configuration.pointedConfigurationAt ctx.source).pullbackFst
          (retargetedContext ctx target).targetPackage).hom).base =
    (refinementBaseHom (pullbackTargetGeometry ctx target)
      (ctx.configuration.pulledRefinementAt ctx.source)
      (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
      (pullbackTargetGeometry_packagePoint_eq ctx target)).base ≫
      (exactPointedToRefinement U).map (pullbackTargetExactArrow ctx target)
  rw [refinementBaseHom_base_eq_casts]
  rw [refinementPackageHomOfOver_base_eq_casts,
    exactLiftRefinementBase_eq_casts]
  unfold pulledRouteActualSource pullbackTargetExactArrow
  simp only [Functor.map_comp, exactPointedToRefinement_map_eqToHom]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  simp [retargetedContext, ActiveRefinementBCContext.retarget,
    RefinementBCConfiguration.pointedConfigurationAt,
    RefinementBCConfiguration.pulledRefinementAt,
    pointedRefinementCategory, PointedRefinementHom.comp,
    PointedRefinementHom.id, refinementHomComp, refinementHomId,
    exactPointedToRefinement, PointedRefinementHom.ofExact,
    exactToRefinement, Function.comp_def]
  rfl

noncomputable def baseActualRouteSource
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    PointedRefinementHom
      (packagePoint (retargetedContext ctx target).baseMatePackage.1)
      (packagePoint (baseRouteGeometry ctx target).core) :=
  (exactPointedToRefinement U).map <| eqToHom <|
    (retargetedContext ctx target).baseMatePackage.2.trans
      (baseRouteGeometry_packagePoint_eq ctx target).symm

theorem baseActualRouteSource_comp
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (baseActualRouteSource ctx target).comp
        (baseRouteActualSource ctx target) =
      PointedRefinementHom.id
        (packagePoint (retargetedContext ctx target).baseMatePackage.1) := by
  change (exactPointedToRefinement U).map (eqToHom _) ≫
      (exactPointedToRefinement U).map (eqToHom _) = 𝟙 _
  rw [← Functor.map_comp]
  simp

theorem baseRouteActualSource_comp
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (baseRouteActualSource ctx target).comp
        (baseActualRouteSource ctx target) =
      PointedRefinementHom.id
        (packagePoint (baseRouteGeometry ctx target).core) := by
  change (exactPointedToRefinement U).map (eqToHom _) ≫
      (exactPointedToRefinement U).map (eqToHom _) = 𝟙 _
  rw [← Functor.map_comp]
  simp

theorem baseActualRouteSource_fac
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (baseActualRouteSource ctx target).comp
        (baseRouteGeometryHom ctx target).base.base =
      (retargetedContext ctx target).baseCompositeLeg.base := by
  calc
    (baseActualRouteSource ctx target).comp
        (baseRouteGeometryHom ctx target).base.base =
      (baseActualRouteSource ctx target).comp
        ((baseRouteActualSource ctx target).comp
          (retargetedContext ctx target).baseCompositeLeg.base) := by
            rw [baseRouteActualSource_fac]
    _ = ((baseActualRouteSource ctx target).comp
          (baseRouteActualSource ctx target)).comp
        (retargetedContext ctx target).baseCompositeLeg.base := by
          rw [PointedRefinementHom.comp]
          rfl
    _ = (PointedRefinementHom.id
          (packagePoint
            (retargetedContext ctx target).baseMatePackage.1)).comp
        (retargetedContext ctx target).baseCompositeLeg.base := by
          rw [baseActualRouteSource_comp]
    _ = (retargetedContext ctx target).baseCompositeLeg.base := by
      apply PointedRefinementHom.ext
      apply RefinementDoctrineHom.ext <;> rfl

noncomputable def pulledActualRouteSource
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    PointedRefinementHom
      (packagePoint (retargetedContext ctx target).pulledMatePackage.1)
      (packagePoint (pulledRouteGeometry ctx target).core) :=
  (exactPointedToRefinement U).map <| eqToHom <|
    (retargetedContext ctx target).pulledMatePackage.2.trans
      (pulledRouteGeometry_packagePoint_eq ctx target).symm

theorem pulledActualRouteSource_comp
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (pulledActualRouteSource ctx target).comp
        (pulledRouteActualSource ctx target) =
      PointedRefinementHom.id
        (packagePoint (retargetedContext ctx target).pulledMatePackage.1) := by
  change (exactPointedToRefinement U).map (eqToHom _) ≫
      (exactPointedToRefinement U).map (eqToHom _) = 𝟙 _
  rw [← Functor.map_comp]
  simp

theorem pulledRouteActualSource_comp
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (pulledRouteActualSource ctx target).comp
        (pulledActualRouteSource ctx target) =
      PointedRefinementHom.id
        (packagePoint (pulledRouteGeometry ctx target).core) := by
  change (exactPointedToRefinement U).map (eqToHom _) ≫
      (exactPointedToRefinement U).map (eqToHom _) = 𝟙 _
  rw [← Functor.map_comp]
  simp

theorem pulledActualRouteSource_fac
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (pulledActualRouteSource ctx target).comp
        (pulledRouteGeometryHom ctx target).base.base =
      (retargetedContext ctx target).pulledCompositeLeg.base := by
  calc
    (pulledActualRouteSource ctx target).comp
        (pulledRouteGeometryHom ctx target).base.base =
      (pulledActualRouteSource ctx target).comp
        ((pulledRouteActualSource ctx target).comp
          (retargetedContext ctx target).pulledCompositeLeg.base) := by
            rw [pulledRouteActualSource_fac]
    _ = ((pulledActualRouteSource ctx target).comp
          (pulledRouteActualSource ctx target)).comp
        (retargetedContext ctx target).pulledCompositeLeg.base := by
          rw [PointedRefinementHom.comp]
          rfl
    _ = (PointedRefinementHom.id
          (packagePoint
            (retargetedContext ctx target).pulledMatePackage.1)).comp
        (retargetedContext ctx target).pulledCompositeLeg.base := by
          rw [pulledActualRouteSource_comp]
    _ = (retargetedContext ctx target).pulledCompositeLeg.base := by
      apply PointedRefinementHom.ext
      apply RefinementDoctrineHom.ext <;> rfl

noncomputable def baseRouteComparisonHom
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    RefinementPackageHom ⟨(baseRouteGeometry ctx target).core⟩
      ⟨(retargetedContext ctx target).baseMatePackage.1⟩ := by
  letI := retargetedBaseComposite_isStronglyCartesian ctx target
  letI := baseRouteGeometryBase_isStronglyCartesian ctx target
  exact CategoryTheory.Functor.IsStronglyCartesian.map
    (refinementPackageProjection U)
    (retargetedContext ctx target).baseCompositeLeg.base
    (retargetedContext ctx target).baseCompositeLeg
    (g := baseRouteActualSource ctx target)
    (f' := (baseRouteGeometryHom ctx target).base.base)
    (baseRouteActualSource_fac ctx target).symm
    (baseRouteGeometryHom ctx target).base

theorem baseRouteComparisonHom_fac
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (baseRouteComparisonHom ctx target).comp
        (retargetedContext ctx target).baseCompositeLeg =
      (baseRouteGeometryHom ctx target).base := by
  letI := retargetedBaseComposite_isStronglyCartesian ctx target
  letI := baseRouteGeometryBase_isStronglyCartesian ctx target
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (refinementPackageProjection U)
    (retargetedContext ctx target).baseCompositeLeg.base
    (retargetedContext ctx target).baseCompositeLeg
    (baseRouteActualSource_fac ctx target).symm
    (baseRouteGeometryHom ctx target).base

noncomputable def pulledRouteComparisonHom
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    RefinementPackageHom ⟨(pulledRouteGeometry ctx target).core⟩
      ⟨(retargetedContext ctx target).pulledMatePackage.1⟩ := by
  letI := retargetedPulledComposite_isStronglyCartesian ctx target
  letI := pulledRouteGeometryBase_isStronglyCartesian ctx target
  exact CategoryTheory.Functor.IsStronglyCartesian.map
    (refinementPackageProjection U)
    (retargetedContext ctx target).pulledCompositeLeg.base
    (retargetedContext ctx target).pulledCompositeLeg
    (g := pulledRouteActualSource ctx target)
    (f' := (pulledRouteGeometryHom ctx target).base.base)
    (pulledRouteActualSource_fac ctx target).symm
    (pulledRouteGeometryHom ctx target).base

theorem pulledRouteComparisonHom_fac
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (pulledRouteComparisonHom ctx target).comp
        (retargetedContext ctx target).pulledCompositeLeg =
      (pulledRouteGeometryHom ctx target).base := by
  letI := retargetedPulledComposite_isStronglyCartesian ctx target
  letI := pulledRouteGeometryBase_isStronglyCartesian ctx target
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (refinementPackageProjection U)
    (retargetedContext ctx target).pulledCompositeLeg.base
    (retargetedContext ctx target).pulledCompositeLeg
    (pulledRouteActualSource_fac ctx target).symm
    (pulledRouteGeometryHom ctx target).base

noncomputable def baseRouteComparisonInv
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    RefinementPackageHom
      ⟨(retargetedContext ctx target).baseMatePackage.1⟩
      ⟨(baseRouteGeometry ctx target).core⟩ := by
  letI := baseRouteGeometryBase_isStronglyCartesian ctx target
  letI := retargetedBaseComposite_isStronglyCartesian ctx target
  exact CategoryTheory.Functor.IsStronglyCartesian.map
    (refinementPackageProjection U)
    (baseRouteGeometryHom ctx target).base.base
    (baseRouteGeometryHom ctx target).base
    (g := baseActualRouteSource ctx target)
    (f' := (retargetedContext ctx target).baseCompositeLeg.base)
    (baseActualRouteSource_fac ctx target).symm
    (retargetedContext ctx target).baseCompositeLeg

theorem baseRouteComparisonInv_fac
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (baseRouteComparisonInv ctx target).comp
        (baseRouteGeometryHom ctx target).base =
      (retargetedContext ctx target).baseCompositeLeg := by
  letI := baseRouteGeometryBase_isStronglyCartesian ctx target
  letI := retargetedBaseComposite_isStronglyCartesian ctx target
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (refinementPackageProjection U)
    (baseRouteGeometryHom ctx target).base.base
    (baseRouteGeometryHom ctx target).base
    (baseActualRouteSource_fac ctx target).symm
    (retargetedContext ctx target).baseCompositeLeg

noncomputable def pulledRouteComparisonInv
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    RefinementPackageHom
      ⟨(retargetedContext ctx target).pulledMatePackage.1⟩
      ⟨(pulledRouteGeometry ctx target).core⟩ := by
  letI := pulledRouteGeometryBase_isStronglyCartesian ctx target
  letI := retargetedPulledComposite_isStronglyCartesian ctx target
  exact CategoryTheory.Functor.IsStronglyCartesian.map
    (refinementPackageProjection U)
    (pulledRouteGeometryHom ctx target).base.base
    (pulledRouteGeometryHom ctx target).base
    (g := pulledActualRouteSource ctx target)
    (f' := (retargetedContext ctx target).pulledCompositeLeg.base)
    (pulledActualRouteSource_fac ctx target).symm
    (retargetedContext ctx target).pulledCompositeLeg

theorem pulledRouteComparisonInv_fac
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (pulledRouteComparisonInv ctx target).comp
        (pulledRouteGeometryHom ctx target).base =
      (retargetedContext ctx target).pulledCompositeLeg := by
  letI := pulledRouteGeometryBase_isStronglyCartesian ctx target
  letI := retargetedPulledComposite_isStronglyCartesian ctx target
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (refinementPackageProjection U)
    (pulledRouteGeometryHom ctx target).base.base
    (pulledRouteGeometryHom ctx target).base
    (pulledActualRouteSource_fac ctx target).symm
    (retargetedContext ctx target).pulledCompositeLeg

theorem baseRouteComparisonHom_isHomLift
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (refinementPackageProjection U).IsHomLift
      (baseRouteActualSource ctx target)
      (baseRouteComparisonHom ctx target) := by
  letI := retargetedBaseComposite_isStronglyCartesian ctx target
  letI := baseRouteGeometryBase_isStronglyCartesian ctx target
  unfold baseRouteComparisonHom
  infer_instance

theorem baseRouteComparisonInv_isHomLift
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (refinementPackageProjection U).IsHomLift
      (baseActualRouteSource ctx target)
      (baseRouteComparisonInv ctx target) := by
  letI := baseRouteGeometryBase_isStronglyCartesian ctx target
  letI := retargetedBaseComposite_isStronglyCartesian ctx target
  unfold baseRouteComparisonInv
  infer_instance

theorem baseRouteComparisonHom_base
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (baseRouteComparisonHom ctx target).base =
      baseRouteActualSource ctx target := by
  letI := baseRouteComparisonHom_isHomLift ctx target
  exact (CategoryTheory.IsHomLift.eq_of_isHomLift
    (refinementPackageProjection U)
    (baseRouteActualSource ctx target)
    (baseRouteComparisonHom ctx target)).symm

theorem baseRouteComparisonInv_base
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (baseRouteComparisonInv ctx target).base =
      baseActualRouteSource ctx target := by
  letI := baseRouteComparisonInv_isHomLift ctx target
  exact (CategoryTheory.IsHomLift.eq_of_isHomLift
    (refinementPackageProjection U)
    (baseActualRouteSource ctx target)
    (baseRouteComparisonInv ctx target)).symm

noncomputable def baseRouteComparisonIso
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (⟨(baseRouteGeometry ctx target).core⟩ : RefinementPackageObject U) ≅
      ⟨(retargetedContext ctx target).baseMatePackage.1⟩ where
  hom := baseRouteComparisonHom ctx target
  inv := baseRouteComparisonInv ctx target
  hom_inv_id := by
    letI hhom := baseRouteComparisonHom_isHomLift ctx target
    letI hinv := baseRouteComparisonInv_isHomLift ctx target
    letI hcomp : (refinementPackageProjection U).IsHomLift
        ((baseRouteActualSource ctx target).comp
          (baseActualRouteSource ctx target))
        ((baseRouteComparisonHom ctx target).comp
          (baseRouteComparisonInv ctx target)) :=
      refinementPackageHom_isHomLift_of_base_eq _ _ (by
        change (baseRouteComparisonHom ctx target).base.comp
          (baseRouteComparisonInv ctx target).base = _
        rw [baseRouteComparisonHom_base, baseRouteComparisonInv_base])
    letI hid : (refinementPackageProjection U).IsHomLift
        ((baseRouteActualSource ctx target).comp
          (baseActualRouteSource ctx target))
        (𝟙 (⟨(baseRouteGeometry ctx target).core⟩ :
          RefinementPackageObject U)) := by
      apply refinementPackageHom_isHomLift_of_base_eq
      rw [baseRouteActualSource_comp]
      rfl
    letI := baseRouteGeometryBase_isStronglyCartesian ctx target
    apply CategoryTheory.Functor.IsStronglyCartesian.ext
      (refinementPackageProjection U)
      (baseRouteGeometryHom ctx target).base.base
      (baseRouteGeometryHom ctx target).base
      ((baseRouteActualSource ctx target).comp
        (baseActualRouteSource ctx target))
    calc
      (baseRouteComparisonHom ctx target ≫
          baseRouteComparisonInv ctx target) ≫
          (baseRouteGeometryHom ctx target).base =
        baseRouteComparisonHom ctx target ≫
          (baseRouteComparisonInv ctx target ≫
            (baseRouteGeometryHom ctx target).base) :=
          Category.assoc _ _ _
      _ = baseRouteComparisonHom ctx target ≫
          (retargetedContext ctx target).baseCompositeLeg := by
            exact congrArg
              (fun leg => (baseRouteComparisonHom ctx target).comp leg)
              (baseRouteComparisonInv_fac ctx target)
      _ = (baseRouteGeometryHom ctx target).base :=
        baseRouteComparisonHom_fac ctx target
      _ = 𝟙 (⟨(baseRouteGeometry ctx target).core⟩ :
          RefinementPackageObject U) ≫
          (baseRouteGeometryHom ctx target).base :=
        by symm; apply Category.id_comp
  inv_hom_id := by
    letI hhom := baseRouteComparisonHom_isHomLift ctx target
    letI hinv := baseRouteComparisonInv_isHomLift ctx target
    letI hcomp : (refinementPackageProjection U).IsHomLift
        ((baseActualRouteSource ctx target).comp
          (baseRouteActualSource ctx target))
        ((baseRouteComparisonInv ctx target).comp
          (baseRouteComparisonHom ctx target)) :=
      refinementPackageHom_isHomLift_of_base_eq _ _ (by
        change (baseRouteComparisonInv ctx target).base.comp
          (baseRouteComparisonHom ctx target).base = _
        rw [baseRouteComparisonInv_base, baseRouteComparisonHom_base])
    letI hid : (refinementPackageProjection U).IsHomLift
        ((baseActualRouteSource ctx target).comp
          (baseRouteActualSource ctx target))
        (𝟙 (⟨(retargetedContext ctx target).baseMatePackage.1⟩ :
          RefinementPackageObject U)) := by
      apply refinementPackageHom_isHomLift_of_base_eq
      rw [baseActualRouteSource_comp]
      rfl
    letI := retargetedBaseComposite_isStronglyCartesian ctx target
    apply CategoryTheory.Functor.IsStronglyCartesian.ext
      (refinementPackageProjection U)
      (retargetedContext ctx target).baseCompositeLeg.base
      (retargetedContext ctx target).baseCompositeLeg
      ((baseActualRouteSource ctx target).comp
        (baseRouteActualSource ctx target))
    calc
      (baseRouteComparisonInv ctx target ≫
          baseRouteComparisonHom ctx target) ≫
          (retargetedContext ctx target).baseCompositeLeg =
        baseRouteComparisonInv ctx target ≫
          (baseRouteComparisonHom ctx target ≫
            (retargetedContext ctx target).baseCompositeLeg) :=
          Category.assoc _ _ _
      _ = baseRouteComparisonInv ctx target ≫
          (baseRouteGeometryHom ctx target).base := by
            exact congrArg
              (fun leg => (baseRouteComparisonInv ctx target).comp leg)
              (baseRouteComparisonHom_fac ctx target)
      _ = (retargetedContext ctx target).baseCompositeLeg :=
        baseRouteComparisonInv_fac ctx target
      _ = 𝟙 (⟨(retargetedContext ctx target).baseMatePackage.1⟩ :
          RefinementPackageObject U) ≫
          (retargetedContext ctx target).baseCompositeLeg :=
        by symm; apply Category.id_comp

theorem pulledRouteComparisonHom_isHomLift
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (refinementPackageProjection U).IsHomLift
      (pulledRouteActualSource ctx target)
      (pulledRouteComparisonHom ctx target) := by
  letI := retargetedPulledComposite_isStronglyCartesian ctx target
  letI := pulledRouteGeometryBase_isStronglyCartesian ctx target
  unfold pulledRouteComparisonHom
  infer_instance

theorem pulledRouteComparisonInv_isHomLift
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (refinementPackageProjection U).IsHomLift
      (pulledActualRouteSource ctx target)
      (pulledRouteComparisonInv ctx target) := by
  letI := pulledRouteGeometryBase_isStronglyCartesian ctx target
  letI := retargetedPulledComposite_isStronglyCartesian ctx target
  unfold pulledRouteComparisonInv
  infer_instance

theorem pulledRouteComparisonHom_base
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (pulledRouteComparisonHom ctx target).base =
      pulledRouteActualSource ctx target := by
  letI := pulledRouteComparisonHom_isHomLift ctx target
  simpa using CategoryTheory.IsHomLift.fac'
    (refinementPackageProjection U)
    (pulledRouteActualSource ctx target)
    (pulledRouteComparisonHom ctx target)

theorem pulledRouteComparisonInv_base
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (pulledRouteComparisonInv ctx target).base =
      pulledActualRouteSource ctx target := by
  letI := pulledRouteComparisonInv_isHomLift ctx target
  simpa using CategoryTheory.IsHomLift.fac'
    (refinementPackageProjection U)
    (pulledActualRouteSource ctx target)
    (pulledRouteComparisonInv ctx target)

noncomputable def pulledRouteComparisonIso
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (⟨(pulledRouteGeometry ctx target).core⟩ : RefinementPackageObject U) ≅
      ⟨(retargetedContext ctx target).pulledMatePackage.1⟩ where
  hom := pulledRouteComparisonHom ctx target
  inv := pulledRouteComparisonInv ctx target
  hom_inv_id := by
    letI hhom := pulledRouteComparisonHom_isHomLift ctx target
    letI hinv := pulledRouteComparisonInv_isHomLift ctx target
    letI hcomp : (refinementPackageProjection U).IsHomLift
        ((pulledRouteActualSource ctx target).comp
          (pulledActualRouteSource ctx target))
        ((pulledRouteComparisonHom ctx target).comp
          (pulledRouteComparisonInv ctx target)) :=
      refinementPackageHom_isHomLift_of_base_eq _ _ (by
        change (pulledRouteComparisonHom ctx target).base.comp
          (pulledRouteComparisonInv ctx target).base = _
        rw [pulledRouteComparisonHom_base, pulledRouteComparisonInv_base])
    letI hid : (refinementPackageProjection U).IsHomLift
        ((pulledRouteActualSource ctx target).comp
          (pulledActualRouteSource ctx target))
        (𝟙 (⟨(pulledRouteGeometry ctx target).core⟩ :
          RefinementPackageObject U)) := by
      apply refinementPackageHom_isHomLift_of_base_eq
      rw [pulledRouteActualSource_comp]
      rfl
    letI := pulledRouteGeometryBase_isStronglyCartesian ctx target
    apply CategoryTheory.Functor.IsStronglyCartesian.ext
      (refinementPackageProjection U)
      (pulledRouteGeometryHom ctx target).base.base
      (pulledRouteGeometryHom ctx target).base
      ((pulledRouteActualSource ctx target).comp
        (pulledActualRouteSource ctx target))
    calc
      (pulledRouteComparisonHom ctx target ≫
          pulledRouteComparisonInv ctx target) ≫
          (pulledRouteGeometryHom ctx target).base =
        pulledRouteComparisonHom ctx target ≫
          (pulledRouteComparisonInv ctx target ≫
            (pulledRouteGeometryHom ctx target).base) :=
          Category.assoc _ _ _
      _ = pulledRouteComparisonHom ctx target ≫
          (retargetedContext ctx target).pulledCompositeLeg := by
            exact congrArg
              (fun leg => (pulledRouteComparisonHom ctx target).comp leg)
              (pulledRouteComparisonInv_fac ctx target)
      _ = (pulledRouteGeometryHom ctx target).base :=
        pulledRouteComparisonHom_fac ctx target
      _ = 𝟙 (⟨(pulledRouteGeometry ctx target).core⟩ :
          RefinementPackageObject U) ≫
          (pulledRouteGeometryHom ctx target).base :=
        by symm; apply Category.id_comp
  inv_hom_id := by
    letI hhom := pulledRouteComparisonHom_isHomLift ctx target
    letI hinv := pulledRouteComparisonInv_isHomLift ctx target
    letI hcomp : (refinementPackageProjection U).IsHomLift
        ((pulledActualRouteSource ctx target).comp
          (pulledRouteActualSource ctx target))
        ((pulledRouteComparisonInv ctx target).comp
          (pulledRouteComparisonHom ctx target)) :=
      refinementPackageHom_isHomLift_of_base_eq _ _ (by
        change (pulledRouteComparisonInv ctx target).base.comp
          (pulledRouteComparisonHom ctx target).base = _
        rw [pulledRouteComparisonInv_base, pulledRouteComparisonHom_base])
    letI hid : (refinementPackageProjection U).IsHomLift
        ((pulledActualRouteSource ctx target).comp
          (pulledRouteActualSource ctx target))
        (𝟙 (⟨(retargetedContext ctx target).pulledMatePackage.1⟩ :
          RefinementPackageObject U)) := by
      apply refinementPackageHom_isHomLift_of_base_eq
      rw [pulledActualRouteSource_comp]
      rfl
    letI := retargetedPulledComposite_isStronglyCartesian ctx target
    apply CategoryTheory.Functor.IsStronglyCartesian.ext
      (refinementPackageProjection U)
      (retargetedContext ctx target).pulledCompositeLeg.base
      (retargetedContext ctx target).pulledCompositeLeg
      ((pulledActualRouteSource ctx target).comp
        (pulledRouteActualSource ctx target))
    calc
      (pulledRouteComparisonInv ctx target ≫
          pulledRouteComparisonHom ctx target) ≫
          (retargetedContext ctx target).pulledCompositeLeg =
        pulledRouteComparisonInv ctx target ≫
          (pulledRouteComparisonHom ctx target ≫
            (retargetedContext ctx target).pulledCompositeLeg) :=
          Category.assoc _ _ _
      _ = pulledRouteComparisonInv ctx target ≫
          (pulledRouteGeometryHom ctx target).base := by
            exact congrArg
              (fun leg => (pulledRouteComparisonInv ctx target).comp leg)
              (pulledRouteComparisonHom_fac ctx target)
      _ = (retargetedContext ctx target).pulledCompositeLeg :=
        pulledRouteComparisonInv_fac ctx target
      _ = 𝟙 (⟨(retargetedContext ctx target).pulledMatePackage.1⟩ :
          RefinementPackageObject U) ≫
          (retargetedContext ctx target).pulledCompositeLeg :=
        by symm; apply Category.id_comp
end UpperGeometryCleavage
end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct.UpperGeometryCleavage
