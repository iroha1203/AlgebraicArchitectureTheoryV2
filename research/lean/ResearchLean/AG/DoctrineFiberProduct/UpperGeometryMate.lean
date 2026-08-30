import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryRoutes

/-!
# Generated core mate for the geometry-compatible reverse routes

The exact and realized-refinement legs used by the two G-115 reverse routes
carry generated two-sided upper inverses. Hence each leg is strongly
cartesian, and so are the two literal route composites. These propositions
are the universal-property input for the upper mate; no comparison certificate
is accepted as data.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation CrossStageCoherence GeometryTransport

namespace UpperGeometryCleavage

/-- An exact inverse-package leg, viewed in the refinement category, is strongly
cartesian by its generated two-sided upper inverse. -/
theorem exactGeometryBase_isStronglyCartesian
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (G : GeometryPackage.{u, v} U) (f : X ⟶ packagePoint G.core) :
    (refinementPackageProjection U).IsStronglyCartesian
      (((exactPackageToRefinement U).map (exactBaseHom G f)).base)
      ((exactPackageToRefinement U).map (exactBaseHom G f)) := by
  apply refinementPackageHom_isStronglyCartesian_of_upper_inverse
    ((exactPackageToRefinement U).map (exactBaseHom G f))
    (inverseCorePackageBackwardUpper G.core f)
  · exact inverseCorePackageForward_comp_backward G.core f
  · exact inverseCorePackageBackward_comp_forward G.core f

/-- A realized-refinement geometry leg is strongly cartesian by the selected
transport inverse generated from realized reflection. -/
theorem refinementGeometryBase_isStronglyCartesian
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (G : GeometryPackage.{u, v} U) (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) :
    (refinementPackageProjection U).IsStronglyCartesian
      (refinementBaseHom G r condition hG).base
      (refinementBaseHom G r condition hG) := by
  subst Y
  let data := selectedTransportDataOfRealizedReflection r condition
    ⟨G.core, rfl⟩
  apply refinementPackageHom_isStronglyCartesian_of_upper_inverse
    (refinementBaseHom G r condition rfl)
    (SelectedRefinementTransport.inverseCorePackageBackwardUpper G.core data)
  · exact SelectedRefinementTransport.inverseCorePackageForward_comp_backward
      G.core data
  · exact SelectedRefinementTransport.inverseCorePackageBackward_comp_forward
      G.core data

/-- The literal base-first reverse route is strongly cartesian. -/
theorem baseRouteGeometryBase_isStronglyCartesian
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (refinementPackageProjection U).IsStronglyCartesian
      (baseRouteGeometryHom ctx target).base.base
      (baseRouteGeometryHom ctx target).base := by
  unfold baseRouteGeometryHom
  letI hexact : (refinementPackageProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map
        (baseRouteExactGeometryHom ctx target)).base.base)
      (((exactGeometryToRefinementGeometry U).map
        (baseRouteExactGeometryHom ctx target)).base) := by
    change (refinementPackageProjection U).IsStronglyCartesian
      (((exactPackageToRefinement U).map
        (exactBaseHom (baseRefinementGeometry ctx target)
          (baseRouteExactArrow ctx target))).base)
      ((exactPackageToRefinement U).map
        (exactBaseHom (baseRefinementGeometry ctx target)
          (baseRouteExactArrow ctx target)))
    exact exactGeometryBase_isStronglyCartesian
      (baseRefinementGeometry ctx target) (baseRouteExactArrow ctx target)
  letI hrefinement : (refinementPackageProjection U).IsStronglyCartesian
      (baseRefinementGeometryHom ctx target).base.base
      (baseRefinementGeometryHom ctx target).base := by
    change (refinementPackageProjection U).IsStronglyCartesian
      (refinementBaseHom target.geometry
        (ctx.configuration.baseRefinementAt ctx.source) ctx.condition
        target.packagePoint_eq).base
      (refinementBaseHom target.geometry
        (ctx.configuration.baseRefinementAt ctx.source) ctx.condition
        target.packagePoint_eq)
    exact refinementGeometryBase_isStronglyCartesian target.geometry
      (ctx.configuration.baseRefinementAt ctx.source) ctx.condition
      target.packagePoint_eq
  exact CategoryTheory.Functor.IsStronglyCartesian.comp
    (refinementPackageProjection U)

/-- The literal pulled-first reverse route is strongly cartesian. -/
theorem pulledRouteGeometryBase_isStronglyCartesian
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (refinementPackageProjection U).IsStronglyCartesian
      (pulledRouteGeometryHom ctx target).base.base
      (pulledRouteGeometryHom ctx target).base := by
  unfold pulledRouteGeometryHom
  letI hrefinement : (refinementPackageProjection U).IsStronglyCartesian
      (pulledRefinementGeometryHom ctx target).base.base
      (pulledRefinementGeometryHom ctx target).base := by
    change (refinementPackageProjection U).IsStronglyCartesian
      (refinementBaseHom (pullbackTargetGeometry ctx target)
        (ctx.configuration.pulledRefinementAt ctx.source)
        (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
        (pullbackTargetGeometry_packagePoint_eq ctx target)).base
      (refinementBaseHom (pullbackTargetGeometry ctx target)
        (ctx.configuration.pulledRefinementAt ctx.source)
        (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
        (pullbackTargetGeometry_packagePoint_eq ctx target))
    exact refinementGeometryBase_isStronglyCartesian
      (pullbackTargetGeometry ctx target)
      (ctx.configuration.pulledRefinementAt ctx.source)
      (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
      (pullbackTargetGeometry_packagePoint_eq ctx target)
  letI hexact : (refinementPackageProjection U).IsStronglyCartesian
      (((exactGeometryToRefinementGeometry U).map
        (pullbackTargetGeometryHom ctx target)).base.base)
      (((exactGeometryToRefinementGeometry U).map
        (pullbackTargetGeometryHom ctx target)).base) := by
    change (refinementPackageProjection U).IsStronglyCartesian
      (((exactPackageToRefinement U).map
        (exactBaseHom target.geometry
          (pullbackTargetExactArrow ctx target))).base)
      ((exactPackageToRefinement U).map
        (exactBaseHom target.geometry
          (pullbackTargetExactArrow ctx target)))
    exact exactGeometryBase_isStronglyCartesian target.geometry
      (pullbackTargetExactArrow ctx target)
  exact CategoryTheory.Functor.IsStronglyCartesian.comp
    (refinementPackageProjection U)

/-- The generated refinement source lies over the authored refinement source. -/
theorem refinementSourceGeometry_packagePoint_eq_source
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (G : GeometryPackage.{u, v} U) (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) :
    packagePoint (refinementSourceGeometry G r condition hG).core = X := by
  rw [refinementSourceGeometry_core]
  exact SelectedRefinementTransport.inverseCorePackage_point _ _

/-- The lower part of a generated refinement geometry leg is the authored
refinement, with only the two endpoint equalities inserted. -/
theorem refinementBaseHom_base_eq_casts
    {U : AtomCarrier.{u}} {X Y : ExtractionInstance U}
    (G : GeometryPackage.{u, v} U) (r : PointedRefinementHom X Y)
    (condition : RealizedLocusExtractionReflecting r)
    (hG : packagePoint G.core = Y) :
    (refinementBaseHom G r condition hG).base =
      ((exactPointedToRefinement U).map
        (eqToHom (refinementSourceGeometry_packagePoint_eq_source
          G r condition hG))) ≫ r ≫
        ((exactPointedToRefinement U).map (eqToHom hG.symm)) := by
  subst Y
  apply PointedRefinementHom.ext
  apply RefinementDoctrineHom.ext
  · funext source
    rfl
  · funext atom
    rfl

/-- Equality transport between the two generated route-source points. This is
the vertical lower leg over their common mixed pullback endpoint. -/
noncomputable def routeSourceBase
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    PointedRefinementHom
      (packagePoint (pulledRouteGeometry ctx target).core)
      (packagePoint (baseRouteGeometry ctx target).core) :=
  (exactPointedToRefinement U).map <| eqToHom <|
    (pulledRouteGeometry_packagePoint_eq ctx target).trans
      (baseRouteGeometry_packagePoint_eq ctx target).symm

/-- Equality transport in the G-114 mate direction, from the base-first route
source to the pulled-first route source. -/
noncomputable def routeSourceForward
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    PointedRefinementHom
      (packagePoint (baseRouteGeometry ctx target).core)
      (packagePoint (pulledRouteGeometry ctx target).core) :=
  (exactPointedToRefinement U).map <| eqToHom <|
    (baseRouteGeometry_packagePoint_eq ctx target).trans
      (pulledRouteGeometry_packagePoint_eq ctx target).symm

/-- The two endpoint transports cancel at the base-first source. -/
theorem routeSourceForward_comp_base
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (routeSourceForward ctx target).comp (routeSourceBase ctx target) =
      PointedRefinementHom.id
        (packagePoint (baseRouteGeometry ctx target).core) := by
  change
    (exactPointedToRefinement U).map
        (eqToHom ((baseRouteGeometry_packagePoint_eq ctx target).trans
          (pulledRouteGeometry_packagePoint_eq ctx target).symm)) ≫
      (exactPointedToRefinement U).map
        (eqToHom ((pulledRouteGeometry_packagePoint_eq ctx target).trans
          (baseRouteGeometry_packagePoint_eq ctx target).symm)) =
        𝟙 _
  rw [← Functor.map_comp]
  simp

/-- The vertical source identification followed by the base-first lower route
is the pulled-first lower route. The only substantive equality is the authored
pullback/refinement square. -/
theorem routeSourceBase_fac
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (routeSourceBase ctx target).comp
        (baseRouteGeometryHom ctx target).base.base =
      (pulledRouteGeometryHom ctx target).base.base := by
  change routeSourceBase ctx target ≫
        (exactPointedToRefinement U).map (baseRouteExactArrow ctx target) ≫
        (refinementBaseHom target.geometry
          (ctx.configuration.baseRefinementAt ctx.source) ctx.condition
          target.packagePoint_eq).base =
      (refinementBaseHom (pullbackTargetGeometry ctx target)
        (ctx.configuration.pulledRefinementAt ctx.source)
        (pulledRealizedReflection ctx.configuration ctx.source ctx.condition)
        (pullbackTargetGeometry_packagePoint_eq ctx target)).base ≫
        (exactPointedToRefinement U).map (pullbackTargetExactArrow ctx target)
  rw [refinementBaseHom_base_eq_casts,
    refinementBaseHom_base_eq_casts]
  unfold routeSourceBase baseRouteExactArrow pullbackTargetExactArrow
  rw [Functor.map_comp, Functor.map_comp]
  simp only [exactPointedToRefinement_map_eqToHom]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp]
  have hsquare0 := ctx.configuration.pulled_square_commutes_at ctx.source
  let sourceCast : PointedRefinementHom
      (packagePoint (pulledRouteGeometry ctx target).core)
      (ctx.configuration.pullbackSourceAt ctx.source) :=
    (exactPointedToRefinement U).map
      (eqToHom (pulledRouteGeometry_packagePoint_eq ctx target))
  let targetCast : PointedRefinementHom
      (ctx.configuration.targetPointAt ctx.source)
      (packagePoint target.geometry.core) :=
    (exactPointedToRefinement U).map (eqToHom target.packagePoint_eq.symm)
  have hsquare :
      sourceCast.comp
          (((PointedRefinementHom.ofExact
            (ctx.configuration.pointedConfigurationAt ctx.source).pulledFst).comp
              (ctx.configuration.baseRefinementAt ctx.source)).comp targetCast) =
        sourceCast.comp
          (((ctx.configuration.pulledRefinementAt ctx.source).comp
            (PointedRefinementHom.ofExact
              (ctx.configuration.pointedConfigurationAt ctx.source).pullbackFst)).comp
                targetCast) := by
    exact congrArg (fun hom => sourceCast.comp (hom.comp targetCast)) hsquare0.symm
  simpa [sourceCast, targetCast, pointedRefinementCategory,
    PointedRefinementHom.comp, PointedRefinementHom.id,
    refinementHomComp, refinementHomId, exactPointedToRefinement,
    PointedRefinementHom.ofExact, exactToRefinement,
    RefinementBCConfiguration.pulledRefinementAt, Function.comp_def,
    ExtInstHom.eqToHom_atomEquiv] using hsquare

/-- The forward endpoint identification followed by the pulled-first lower
route is the base-first lower route. -/
theorem routeSourceForward_fac
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (routeSourceForward ctx target).comp
        (pulledRouteGeometryHom ctx target).base.base =
      (baseRouteGeometryHom ctx target).base.base := by
  calc
    (routeSourceForward ctx target).comp
        (pulledRouteGeometryHom ctx target).base.base =
      (routeSourceForward ctx target).comp
        ((routeSourceBase ctx target).comp
          (baseRouteGeometryHom ctx target).base.base) := by
            rw [routeSourceBase_fac]
    _ = ((routeSourceForward ctx target).comp
          (routeSourceBase ctx target)).comp
        (baseRouteGeometryHom ctx target).base.base := by
          rw [PointedRefinementHom.comp]
          rfl
    _ = (PointedRefinementHom.id
          (packagePoint (baseRouteGeometry ctx target).core)).comp
        (baseRouteGeometryHom ctx target).base.base := by
          rw [routeSourceForward_comp_base]
    _ = (baseRouteGeometryHom ctx target).base.base := by
      apply PointedRefinementHom.ext
      apply RefinementDoctrineHom.ext <;> rfl

/-- The inverse-direction refinement-package comparison generated by the strong
cartesianness of the base-first route. -/
noncomputable def generatedRouteRefinementMateInverse
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    RefinementPackageHom ⟨(pulledRouteGeometry ctx target).core⟩
      ⟨(baseRouteGeometry ctx target).core⟩ := by
  letI := baseRouteGeometryBase_isStronglyCartesian ctx target
  letI := pulledRouteGeometryBase_isStronglyCartesian ctx target
  exact CategoryTheory.Functor.IsStronglyCartesian.map
    (refinementPackageProjection U)
    (baseRouteGeometryHom ctx target).base.base
    (baseRouteGeometryHom ctx target).base
    (g := routeSourceBase ctx target)
    (f' := (pulledRouteGeometryHom ctx target).base.base)
    (routeSourceBase_fac ctx target).symm
    (pulledRouteGeometryHom ctx target).base

/-- The inverse-direction comparison satisfies its complete package triangle. -/
theorem generatedRouteRefinementMateInverse_fac
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (generatedRouteRefinementMateInverse ctx target).comp
        (baseRouteGeometryHom ctx target).base =
      (pulledRouteGeometryHom ctx target).base := by
  letI := baseRouteGeometryBase_isStronglyCartesian ctx target
  letI := pulledRouteGeometryBase_isStronglyCartesian ctx target
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (refinementPackageProjection U)
    (baseRouteGeometryHom ctx target).base.base
    (baseRouteGeometryHom ctx target).base
    (routeSourceBase_fac ctx target).symm
    (pulledRouteGeometryHom ctx target).base

/-- The route comparison in the G-114 mate direction, generated by the strong
cartesianness of the pulled-first route. -/
noncomputable def generatedRouteRefinementMate
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    RefinementPackageHom ⟨(baseRouteGeometry ctx target).core⟩
      ⟨(pulledRouteGeometry ctx target).core⟩ := by
  letI := baseRouteGeometryBase_isStronglyCartesian ctx target
  letI := pulledRouteGeometryBase_isStronglyCartesian ctx target
  exact CategoryTheory.Functor.IsStronglyCartesian.map
    (refinementPackageProjection U)
    (pulledRouteGeometryHom ctx target).base.base
    (pulledRouteGeometryHom ctx target).base
    (g := routeSourceForward ctx target)
    (f' := (baseRouteGeometryHom ctx target).base.base)
    (routeSourceForward_fac ctx target).symm
    (baseRouteGeometryHom ctx target).base

/-- The generated G-114-direction comparison satisfies the package triangle. -/
theorem generatedRouteRefinementMate_fac
    (ctx : ActiveRefinementBCContext U) (target : TargetGeometry.{u, v} ctx) :
    (generatedRouteRefinementMate ctx target).comp
        (pulledRouteGeometryHom ctx target).base =
      (baseRouteGeometryHom ctx target).base := by
  letI := baseRouteGeometryBase_isStronglyCartesian ctx target
  letI := pulledRouteGeometryBase_isStronglyCartesian ctx target
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (refinementPackageProjection U)
    (pulledRouteGeometryHom ctx target).base.base
    (pulledRouteGeometryHom ctx target).base
    (routeSourceForward_fac ctx target).symm
    (baseRouteGeometryHom ctx target).base

end UpperGeometryCleavage

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct.UpperGeometryCleavage
