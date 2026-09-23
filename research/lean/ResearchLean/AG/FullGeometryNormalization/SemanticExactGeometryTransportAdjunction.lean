import ResearchLean.AG.FullGeometryNormalization.SemanticExactGeometryPull
import ResearchLean.AG.FullGeometryNormalization.ExactGeometryPullCocartesian
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Semantic complete-geometry transport and pullback adjunction

For an arbitrary semantic extraction-instance morphism, canonical geometry
transport and the exact geometry cleavage form an adjunction.  Both transposes
come from their universal properties.  The exact pull lift is also
cocartesian, making the generated unit and counit invertible.
-/

namespace AAT.AG.FullGeometryNormalization

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open DoctrineFiberProduct

set_option maxHeartbeats 3000000

/-- The semantic exact pull lift is cocartesian over its projected arrow. -/
theorem semanticGeometryPullLift_crossStageStronglyCocartesian_map
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y)
    (target : GeomFiber.{u, v} Y) :
    (crossStageProjection.{u, v} U).IsStronglyCocartesian
      ((crossStageProjection.{u, v} U).map
        (semanticGeometryPullLift input target))
      (semanticGeometryPullLift input target) := by
  let f := semanticGeometryPullBaseHom input target
  letI : (geometryProjection U).IsStronglyCocartesian
      (semanticGeometryPullLift input target).base
      (semanticGeometryPullLift input target) := by
    change (geometryProjection U).IsStronglyCocartesian
      (UpperGeometryCleavage.exactBaseHom target.1 f)
      (UpperGeometryCleavage.generatedExactGeometryHom target.1 f)
    exact generatedExactGeometryHom_isStronglyCocartesian target.1 f
  letI : (packageProjection U).IsStronglyCocartesian
      (semanticGeometryPullLift input target).base.base
      (semanticGeometryPullLift input target).base := by
    change (packageProjection U).IsStronglyCocartesian
      (UpperGeometryCleavage.exactBaseHom target.1 f).base
      (UpperGeometryCleavage.exactBaseHom target.1 f)
    exact packageTotalHom_isStronglyCocartesian_of_upper_inverse
      (UpperGeometryCleavage.exactBaseHom target.1 f)
      (inverseCorePackageBackwardUpper target.1.core f)
      (inverseCorePackageForward_comp_backward target.1.core f)
      (inverseCorePackageBackward_comp_forward target.1.core f)
  simpa only using geometryHom_isCompositeStronglyCocartesian
    (semanticGeometryPullLift input target)

/-- The semantic exact pull lift is cocartesian over the given arrow. -/
theorem semanticGeometryPullLift_crossStageStronglyCocartesian
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y)
    (target : GeomFiber.{u, v} Y) :
    (crossStageProjection.{u, v} U).IsStronglyCocartesian input
      (semanticGeometryPullLift input target) := by
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      ((crossStageProjection.{u, v} U).map
        (semanticGeometryPullLift input target))
      (semanticGeometryPullLift input target) :=
    semanticGeometryPullLift_crossStageStronglyCocartesian_map input target
  letI : (crossStageProjection.{u, v} U).IsHomLift input
      (semanticGeometryPullLift input target) :=
    semanticGeometryPullLift_isHomLift input target
  exact stronglyCocartesian_of_isHomLift
    (crossStageProjection.{u, v} U) input
    (semanticGeometryPullLift input target)

/-- Send a vertical map out of complete-geometry transport to its exact
cartesian transpose. -/
noncomputable def semanticGeometryTransportToPullHom
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y)
    (sourceGeometry : GeomFiber.{u, v} X)
    (targetGeometry : GeomFiber.{u, v} Y)
    (hom : (geomFiberTransportFunctor input).obj sourceGeometry ⟶
      targetGeometry) :
    sourceGeometry ⟶ (semanticGeometryPullFunctor input).obj targetGeometry := by
  let cartLift := semanticGeometryPullLift input targetGeometry
  letI : (crossStageProjection.{u, v} U).IsStronglyCartesian
      input cartLift :=
    semanticGeometryPullLift_crossStageStronglyCartesian input targetGeometry
  letI : (crossStageProjection.{u, v} U).IsHomLift input
      (geomFiberLift input sourceGeometry) :=
    geomFiberLift_isHomLift input sourceGeometry
  letI : (crossStageProjection.{u, v} U).IsHomLift
      (𝟙 Y) hom.1 := hom.2
  letI : (crossStageProjection.{u, v} U).IsHomLift input
      (geomFiberLift input sourceGeometry ≫ hom.1) := by
    simpa using inferInstanceAs
      ((crossStageProjection.{u, v} U).IsHomLift
        (input ≫ 𝟙 Y)
        (geomFiberLift input sourceGeometry ≫ hom.1))
  exact ⟨CategoryTheory.Functor.IsStronglyCartesian.map
      (crossStageProjection.{u, v} U) input cartLift
      (g := 𝟙 X) (f' := input)
      (show input = 𝟙 X ≫ input from by simp)
      (geomFiberLift input sourceGeometry ≫ hom.1), inferInstance⟩

/-- The cartesian transpose satisfies its defining factorization through the
exact complete-geometry lift. -/
theorem semanticGeometryTransportToPullHom_fac
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y)
    (sourceGeometry : GeomFiber.{u, v} X)
    (targetGeometry : GeomFiber.{u, v} Y)
    (hom : (geomFiberTransportFunctor input).obj sourceGeometry ⟶
      targetGeometry) :
    (semanticGeometryTransportToPullHom input sourceGeometry targetGeometry hom).1 ≫
        semanticGeometryPullLift input targetGeometry =
      geomFiberLift input sourceGeometry ≫ hom.1 := by
  let cartLift := semanticGeometryPullLift input targetGeometry
  letI : (crossStageProjection.{u, v} U).IsStronglyCartesian
      input cartLift :=
    semanticGeometryPullLift_crossStageStronglyCartesian input targetGeometry
  letI : (crossStageProjection.{u, v} U).IsHomLift input
      (geomFiberLift input sourceGeometry) :=
    geomFiberLift_isHomLift input sourceGeometry
  letI : (crossStageProjection.{u, v} U).IsHomLift
      (𝟙 Y) hom.1 := hom.2
  letI : (crossStageProjection.{u, v} U).IsHomLift input
      (geomFiberLift input sourceGeometry ≫ hom.1) := by
    simpa using inferInstanceAs
      ((crossStageProjection.{u, v} U).IsHomLift
        (input ≫ 𝟙 Y)
        (geomFiberLift input sourceGeometry ≫ hom.1))
  exact CategoryTheory.Functor.IsStronglyCartesian.fac
    (crossStageProjection.{u, v} U) input cartLift
    (show input = 𝟙 X ≫ input from by simp)
    (geomFiberLift input sourceGeometry ≫ hom.1)

/-- Send a vertical map into exact pullback to its cocartesian transpose out of
complete-geometry transport. -/
noncomputable def semanticGeometryPullToTransportHom
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y)
    (sourceGeometry : GeomFiber.{u, v} X)
    (targetGeometry : GeomFiber.{u, v} Y)
    (hom : sourceGeometry ⟶
      (semanticGeometryPullFunctor input).obj targetGeometry) :
    (geomFiberTransportFunctor input).obj sourceGeometry ⟶
      targetGeometry := by
  let cocartLift := geomFiberLift input sourceGeometry
  let cartLift := semanticGeometryPullLift input targetGeometry
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      input cocartLift :=
    geomFiberLift_isStronglyCocartesian input sourceGeometry
  letI : (crossStageProjection.{u, v} U).IsHomLift
      (𝟙 X) hom.1 := hom.2
  letI : (crossStageProjection.{u, v} U).IsHomLift input
      cartLift := semanticGeometryPullLift_isHomLift input targetGeometry
  letI : (crossStageProjection.{u, v} U).IsHomLift input
      (hom.1 ≫ cartLift) := by
    simpa using inferInstanceAs
      ((crossStageProjection.{u, v} U).IsHomLift
        ((𝟙 X) ≫ input)
        (hom.1 ≫ cartLift))
  exact ⟨CategoryTheory.Functor.IsStronglyCocartesian.map
      (crossStageProjection.{u, v} U) input cocartLift
      (g := 𝟙 Y) (f' := input)
      (show input = input ≫ 𝟙 Y from by simp)
      (hom.1 ≫ cartLift), inferInstance⟩

/-- The cocartesian transpose satisfies its defining factorization through the
canonical complete-geometry transport lift. -/
theorem semanticGeometryPullToTransportHom_fac
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y)
    (sourceGeometry : GeomFiber.{u, v} X)
    (targetGeometry : GeomFiber.{u, v} Y)
    (hom : sourceGeometry ⟶
      (semanticGeometryPullFunctor input).obj targetGeometry) :
    geomFiberLift input sourceGeometry ≫
        (semanticGeometryPullToTransportHom input sourceGeometry targetGeometry hom).1 =
      hom.1 ≫ semanticGeometryPullLift input targetGeometry := by
  let cocartLift := geomFiberLift input sourceGeometry
  let cartLift := semanticGeometryPullLift input targetGeometry
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      input cocartLift :=
    geomFiberLift_isStronglyCocartesian input sourceGeometry
  letI : (crossStageProjection.{u, v} U).IsHomLift
      (𝟙 X) hom.1 := hom.2
  letI : (crossStageProjection.{u, v} U).IsHomLift input
      cartLift := semanticGeometryPullLift_isHomLift input targetGeometry
  letI : (crossStageProjection.{u, v} U).IsHomLift input
      (hom.1 ≫ cartLift) := by
    simpa using inferInstanceAs
      ((crossStageProjection.{u, v} U).IsHomLift
        ((𝟙 X) ≫ input)
        (hom.1 ≫ cartLift))
  exact CategoryTheory.Functor.IsStronglyCocartesian.fac
    (crossStageProjection.{u, v} U) input cocartLift
    (show input = input ≫ 𝟙 Y from by simp) (hom.1 ≫ cartLift)

/-- Cartesian then cocartesian transposition is the identity in the target
geometry fiber. -/
theorem semanticGeometryPullToTransportHom_toPull
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y)
    (sourceGeometry : GeomFiber.{u, v} X)
    (targetGeometry : GeomFiber.{u, v} Y)
    (hom : (geomFiberTransportFunctor input).obj sourceGeometry ⟶
      targetGeometry) :
    semanticGeometryPullToTransportHom input sourceGeometry targetGeometry
        (semanticGeometryTransportToPullHom input sourceGeometry targetGeometry hom) =
      hom := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let cocartLift := geomFiberLift input sourceGeometry
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      input cocartLift :=
    geomFiberLift_isStronglyCocartesian input sourceGeometry
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (crossStageProjection.{u, v} U) input cocartLift
    (𝟙 Y)
  change cocartLift ≫
      (semanticGeometryPullToTransportHom input sourceGeometry targetGeometry
        (semanticGeometryTransportToPullHom input sourceGeometry targetGeometry hom)).1 =
    cocartLift ≫ hom.1
  rw [semanticGeometryPullToTransportHom_fac, semanticGeometryTransportToPullHom_fac]

/-- Cocartesian then cartesian transposition is the identity in the source
geometry fiber. -/
theorem semanticGeometryTransportToPullHom_toTransport
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y)
    (sourceGeometry : GeomFiber.{u, v} X)
    (targetGeometry : GeomFiber.{u, v} Y)
    (hom : sourceGeometry ⟶
      (semanticGeometryPullFunctor input).obj targetGeometry) :
    semanticGeometryTransportToPullHom input sourceGeometry targetGeometry
        (semanticGeometryPullToTransportHom input sourceGeometry targetGeometry hom) =
      hom := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let cartLift := semanticGeometryPullLift input targetGeometry
  letI : (crossStageProjection.{u, v} U).IsStronglyCartesian
      input cartLift :=
    semanticGeometryPullLift_crossStageStronglyCartesian input targetGeometry
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (crossStageProjection.{u, v} U) input cartLift
    (𝟙 X)
  change (semanticGeometryTransportToPullHom input sourceGeometry targetGeometry
      (semanticGeometryPullToTransportHom input sourceGeometry targetGeometry hom)).1 ≫
      cartLift = hom.1 ≫ cartLift
  rw [semanticGeometryTransportToPullHom_fac, semanticGeometryPullToTransportHom_fac]

/-- The complete-geometry transport/pullback hom-set equivalence generated by
the two universal properties. -/
noncomputable def semanticGeometryTransportPullHomEquiv
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y)
    (sourceGeometry : GeomFiber.{u, v} X)
    (targetGeometry : GeomFiber.{u, v} Y) :
    ((geomFiberTransportFunctor input).obj sourceGeometry ⟶
        targetGeometry) ≃
      (sourceGeometry ⟶ (semanticGeometryPullFunctor input).obj targetGeometry) where
  toFun := semanticGeometryTransportToPullHom input sourceGeometry targetGeometry
  invFun := semanticGeometryPullToTransportHom input sourceGeometry targetGeometry
  left_inv := semanticGeometryPullToTransportHom_toPull input sourceGeometry targetGeometry
  right_inv := semanticGeometryTransportToPullHom_toTransport input sourceGeometry targetGeometry

/-! ## Naturality of the generated correspondence -/

/-- The inverse transpose is natural in the source geometry. -/
theorem semanticGeometryPullToTransportHom_comp_left
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y)
    {first second : GeomFiber.{u, v} X}
    (sourceHom : first ⟶ second)
    (targetGeometry : GeomFiber.{u, v} Y)
    (hom : second ⟶ (semanticGeometryPullFunctor input).obj targetGeometry) :
    semanticGeometryPullToTransportHom input first targetGeometry (sourceHom ≫ hom) =
      (geomFiberTransportFunctor input).map sourceHom ≫
        semanticGeometryPullToTransportHom input second targetGeometry hom := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let cocartLift := geomFiberLift input first
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      input cocartLift :=
    geomFiberLift_isStronglyCocartesian input first
  apply CategoryTheory.Functor.IsStronglyCocartesian.ext
    (crossStageProjection.{u, v} U) input cocartLift
    (𝟙 Y)
  change cocartLift ≫
      (semanticGeometryPullToTransportHom input first targetGeometry
        (sourceHom ≫ hom)).1 =
    cocartLift ≫
      ((geomFiberTransportFunctor input).map sourceHom).1 ≫
      (semanticGeometryPullToTransportHom input second targetGeometry hom).1
  rw [semanticGeometryPullToTransportHom_fac]
  change (sourceHom.1 ≫ hom.1) ≫ semanticGeometryPullLift input targetGeometry = _
  have transportFac :
      geomFiberLift input first ≫
          ((geomFiberTransportFunctor input).map sourceHom).1 =
        sourceHom.1 ≫ geomFiberLift input second := by
    simpa only [geomFiberTransportFunctor] using
      geomFiberTransportMap_fac input sourceHom
  calc
    _ = sourceHom.1 ≫ (hom.1 ≫ semanticGeometryPullLift input targetGeometry) :=
      Category.assoc _ _ _
    _ = sourceHom.1 ≫
        (geomFiberLift input second ≫
          (semanticGeometryPullToTransportHom input second targetGeometry hom).1) := by
      rw [semanticGeometryPullToTransportHom_fac]
    _ = (sourceHom.1 ≫ geomFiberLift input second) ≫
        (semanticGeometryPullToTransportHom input second targetGeometry hom).1 :=
      (Category.assoc _ _ _).symm
    _ = (geomFiberLift input first ≫
        ((geomFiberTransportFunctor input).map sourceHom).1) ≫
          (semanticGeometryPullToTransportHom input second targetGeometry hom).1 := by
      rw [transportFac]
    _ = _ := Category.assoc _ _ _

/-- The forward transpose is natural in the target geometry. -/
theorem semanticGeometryTransportToPullHom_comp_right
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y)
    (sourceGeometry : GeomFiber.{u, v} X)
    {first second : GeomFiber.{u, v} Y}
    (hom : (geomFiberTransportFunctor input).obj sourceGeometry ⟶ first)
    (targetHom : first ⟶ second) :
    semanticGeometryTransportToPullHom input sourceGeometry second (hom ≫ targetHom) =
      semanticGeometryTransportToPullHom input sourceGeometry first hom ≫
        (semanticGeometryPullFunctor input).map targetHom := by
  apply CategoryTheory.Functor.Fiber.hom_ext
  let cartLift := semanticGeometryPullLift input second
  letI : (crossStageProjection.{u, v} U).IsStronglyCartesian
      input cartLift :=
    semanticGeometryPullLift_crossStageStronglyCartesian input second
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (crossStageProjection.{u, v} U) input cartLift
    (𝟙 X)
  change (semanticGeometryTransportToPullHom input sourceGeometry second
      (hom ≫ targetHom)).1 ≫ cartLift =
    ((semanticGeometryTransportToPullHom input sourceGeometry first hom).1 ≫
      ((semanticGeometryPullFunctor input).map targetHom).1) ≫ cartLift
  rw [semanticGeometryTransportToPullHom_fac]
  change geomFiberLift input sourceGeometry ≫
      (hom.1 ≫ targetHom.1) =
    ((semanticGeometryTransportToPullHom input sourceGeometry first hom).1 ≫
      (semanticGeometryPullMap input targetHom).1) ≫ cartLift
  rw [Category.assoc, semanticGeometryPullMap_fac]
  simpa only [Category.assoc] using congrArg
    (fun k => k ≫ targetHom.1)
    (semanticGeometryTransportToPullHom_fac
      input sourceGeometry first hom).symm

/-- The natural hom-equivalence package for exact complete-geometry transport
and pullback. -/
noncomputable def semanticGeometryTransportPullCoreHomEquiv
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y) :
    Adjunction.CoreHomEquiv
      (geomFiberTransportFunctor input)
      (semanticGeometryPullFunctor input) where
  homEquiv := semanticGeometryTransportPullHomEquiv input
  homEquiv_naturality_left_symm := by
    intro first second target sourceHom hom
    exact semanticGeometryPullToTransportHom_comp_left
      input sourceHom target hom
  homEquiv_naturality_right := by
    intro source first second hom targetHom
    exact semanticGeometryTransportToPullHom_comp_right
      input source hom targetHom

/-! ## Adjunction, unit, counit, and component equations -/

/-- Canonical complete-geometry cocartesian transport is left adjoint to exact
complete-geometry cartesian pullback. -/
noncomputable def semanticGeometryTransportPullAdjunction
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y) :
    geomFiberTransportFunctor input ⊣
      semanticGeometryPullFunctor input :=
  Adjunction.mkOfHomEquiv (semanticGeometryTransportPullCoreHomEquiv input)

/-- The generated unit of exact complete-geometry transport and pullback. -/
noncomputable def semanticGeometryTransportPullUnit
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y) :
    𝟭 (GeomFiber.{u, v} X) ⟶
      geomFiberTransportFunctor input ⋙
        semanticGeometryPullFunctor input :=
  (semanticGeometryTransportPullAdjunction input).unit

/-- The generated counit of exact complete-geometry transport and pullback. -/
noncomputable def semanticGeometryTransportPullCounit
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y) :
    semanticGeometryPullFunctor input ⋙
        geomFiberTransportFunctor input ⟶
      𝟭 (GeomFiber.{u, v} Y) :=
  (semanticGeometryTransportPullAdjunction input).counit

/-- The unit component is the cartesian transpose of the identity. -/
theorem semanticGeometryTransportPullUnit_app
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y)
    (sourceGeometry : GeomFiber.{u, v} X) :
    (semanticGeometryTransportPullUnit input).app sourceGeometry =
      semanticGeometryTransportToPullHom input sourceGeometry
        ((geomFiberTransportFunctor input).obj sourceGeometry)
        (𝟙 ((geomFiberTransportFunctor input).obj sourceGeometry)) := by
  rfl

/-- The counit component is the cocartesian transpose of the identity. -/
theorem semanticGeometryTransportPullCounit_app
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y)
    (targetGeometry : GeomFiber.{u, v} Y) :
    (semanticGeometryTransportPullCounit input).app targetGeometry =
      semanticGeometryPullToTransportHom input
        ((semanticGeometryPullFunctor input).obj targetGeometry)
        targetGeometry
        (𝟙 ((semanticGeometryPullFunctor input).obj targetGeometry)) := by
  rfl

/-- The unit component factors the canonical cocartesian lift through the exact
cartesian lift. -/
theorem semanticGeometryTransportPullUnit_app_fac
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y)
    (sourceGeometry : GeomFiber.{u, v} X) :
    ((semanticGeometryTransportPullUnit input).app sourceGeometry).1 ≫
        semanticGeometryPullLift input
          ((geomFiberTransportFunctor input).obj sourceGeometry) =
      geomFiberLift input sourceGeometry := by
  rw [semanticGeometryTransportPullUnit_app, semanticGeometryTransportToPullHom_fac]
  change geomFiberLift input sourceGeometry ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The counit component factors the exact cartesian lift through the canonical
cocartesian lift. -/
theorem semanticGeometryTransportPullCounit_app_fac
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y)
    (targetGeometry : GeomFiber.{u, v} Y) :
    geomFiberLift input
        ((semanticGeometryPullFunctor input).obj targetGeometry) ≫
      ((semanticGeometryTransportPullCounit input).app targetGeometry).1 =
        semanticGeometryPullLift input targetGeometry := by
  rw [semanticGeometryTransportPullCounit_app, semanticGeometryPullToTransportHom_fac]
  change 𝟙 _ ≫ semanticGeometryPullLift input targetGeometry = _
  exact Category.id_comp _

/-- Naturality of the generated unit. -/
theorem semanticGeometryTransportPullUnit_naturality
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y)
    {first second : GeomFiber.{u, v} X}
    (hom : first ⟶ second) :
    (𝟭 (GeomFiber.{u, v} X)).map hom ≫
        (semanticGeometryTransportPullUnit input).app second =
      (semanticGeometryTransportPullUnit input).app first ≫
        (geomFiberTransportFunctor input ⋙
          semanticGeometryPullFunctor input).map hom :=
  (semanticGeometryTransportPullUnit input).naturality hom

/-- Naturality of the generated counit. -/
theorem semanticGeometryTransportPullCounit_naturality
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y)
    {first second : GeomFiber.{u, v} Y}
    (hom : first ⟶ second) :
    (semanticGeometryPullFunctor input ⋙
        geomFiberTransportFunctor input).map hom ≫
        (semanticGeometryTransportPullCounit input).app second =
      (semanticGeometryTransportPullCounit input).app first ≫
        (𝟭 (GeomFiber.{u, v} Y)).map hom :=
  (semanticGeometryTransportPullCounit input).naturality hom

/-- The left triangle identity of the exact complete-geometry adjunction. -/
theorem semanticGeometryTransportPull_left_triangle
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y) :
    Functor.whiskerRight (semanticGeometryTransportPullUnit input)
        (geomFiberTransportFunctor input) ≫
      (Functor.associator
        (geomFiberTransportFunctor input)
        (semanticGeometryPullFunctor input)
        (geomFiberTransportFunctor input)).hom ≫
      Functor.whiskerLeft (geomFiberTransportFunctor input)
        (semanticGeometryTransportPullCounit input) =
      NatTrans.id
        (𝟭 (GeomFiber.{u, v} X) ⋙
          geomFiberTransportFunctor input) :=
  (semanticGeometryTransportPullAdjunction input).left_triangle

/-- The right triangle identity of the exact complete-geometry adjunction. -/
theorem semanticGeometryTransportPull_right_triangle
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y) :
    Functor.whiskerLeft (semanticGeometryPullFunctor input)
        (semanticGeometryTransportPullUnit input) ≫
      (Functor.associator
        (semanticGeometryPullFunctor input)
        (geomFiberTransportFunctor input)
        (semanticGeometryPullFunctor input)).inv ≫
      Functor.whiskerRight (semanticGeometryTransportPullCounit input)
        (semanticGeometryPullFunctor input) =
      NatTrans.id
        (semanticGeometryPullFunctor input ⋙
          𝟭 (GeomFiber.{u, v} X)) :=
  (semanticGeometryTransportPullAdjunction input).right_triangle


/-- A vertical geometry morphism is invertible when its total morphism is. -/
theorem semanticGeomFiberHom_isIso_of_total_isIso
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    {source target : GeomFiber.{u, v} X} (hom : source ⟶ target)
    [IsIso hom.1] : IsIso hom := by
  letI : (crossStageProjection.{u, v} U).IsHomLift (𝟙 X) hom.1 := hom.2
  let inverse : target ⟶ source :=
    ⟨inv hom.1, CategoryTheory.IsHomLift.lift_id_inv_isIso
      (crossStageProjection.{u, v} U) X hom.1⟩
  exact ⟨⟨inverse, by
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact IsIso.hom_inv_id hom.1, by
    apply CategoryTheory.Functor.Fiber.hom_ext
    exact IsIso.inv_hom_id hom.1⟩⟩

/-- Every generated exact complete-geometry adjunction unit component is
invertible by Cartesian cancellation over the identity base arrow. -/
theorem semanticGeometryTransportPullUnit_app_isIso
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y)
    (source : GeomFiber.{u, v} X) :
    IsIso ((semanticGeometryTransportPullUnit input).app source) := by
  let unit := (semanticGeometryTransportPullUnit input).app source
  let pullLift := semanticGeometryPullLift input
    ((geomFiberTransportFunctor input).obj source)
  let pushLift := geomFiberLift input source
  letI : (crossStageProjection.{u, v} U).IsStronglyCartesian
      input pullLift :=
    semanticGeometryPullLift_crossStageStronglyCartesian input _
  letI : (crossStageProjection.{u, v} U).IsStronglyCartesian
      input pushLift :=
    geomFiberLift_crossStageStronglyCartesian input source
  letI : (crossStageProjection.{u, v} U).IsHomLift
      (𝟙 X) unit.1 := unit.2
  have composed : (crossStageProjection.{u, v} U).IsStronglyCartesian
      ((𝟙 X) ≫ input)
      (unit.1 ≫ pullLift) := by
    rw [Category.id_comp, semanticGeometryTransportPullUnit_app_fac]
    exact geomFiberLift_crossStageStronglyCartesian input source
  letI : (crossStageProjection.{u, v} U).IsStronglyCartesian
      ((𝟙 X) ≫ input)
      (unit.1 ≫ pullLift) := composed
  letI : (crossStageProjection.{u, v} U).IsStronglyCartesian
      (𝟙 X) unit.1 :=
    CategoryTheory.Functor.IsStronglyCartesian.of_comp
      (p := crossStageProjection.{u, v} U)
      (f := 𝟙 X) (g := input)
      (φ := unit.1) (ψ := pullLift)
  letI : IsIso unit.1 :=
    CategoryTheory.Functor.IsStronglyCartesian.isIso_of_base_isIso
      (crossStageProjection.{u, v} U) (𝟙 X) unit.1
  exact semanticGeomFiberHom_isIso_of_total_isIso unit

/-- The generated unit does not change the fixed coefficient ring. -/
theorem semanticGeometryTransportPullUnit_app_coefficientHom
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y)
    (source : GeomFiber.{u, v} X) :
    ((semanticGeometryTransportPullUnit input).app source).1.geometry.coefficientHom =
      RingHom.id source.1.Coefficient := by
  have h := congrArg
    (fun hom : GeometryTotalHom _ _ => hom.geometry.coefficientHom)
    (semanticGeometryTransportPullUnit_app_fac input source)
  simpa [GeometryTotalHom.comp, GeomReadHom.comp, geomFiberLift,
    geomTransportAlongHom, geomTransportAlongGeometryHom] using h

/-- The generated exact complete-geometry adjunction unit is a natural
isomorphism. -/
theorem semanticGeometryTransportPullUnit_isIso
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y) :
    IsIso (semanticGeometryTransportPullUnit input) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro source
  exact semanticGeometryTransportPullUnit_app_isIso input source


/-- Every generated exact complete-geometry adjunction counit component is
invertible by cocartesian cancellation over the identity base arrow. -/
theorem semanticGeometryTransportPullCounit_app_isIso
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y)
    (target : GeomFiber.{u, v} Y) :
    IsIso ((semanticGeometryTransportPullCounit input).app target) := by
  let counit := (semanticGeometryTransportPullCounit input).app target
  let source := (semanticGeometryPullFunctor input).obj target
  let pushLift := geomFiberLift input source
  let pullLift := semanticGeometryPullLift input target
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      input pushLift :=
    geomFiberLift_isStronglyCocartesian input source
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      input pullLift :=
    semanticGeometryPullLift_crossStageStronglyCocartesian input target
  letI : (crossStageProjection.{u, v} U).IsHomLift
      (𝟙 Y) counit.1 := counit.2
  have composed : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      (input ≫ 𝟙 Y)
      (pushLift ≫ counit.1) := by
    rw [Category.comp_id, semanticGeometryTransportPullCounit_app_fac]
    exact semanticGeometryPullLift_crossStageStronglyCocartesian input target
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      (input ≫ 𝟙 Y)
      (pushLift ≫ counit.1) := composed
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      (𝟙 Y) counit.1 :=
    CategoryTheory.Functor.IsStronglyCocartesian.of_comp
      (p := crossStageProjection.{u, v} U)
      (f := input) (g := 𝟙 Y)
      (φ := pushLift) (ψ := counit.1)
  letI : IsIso counit.1 :=
    CategoryTheory.Functor.IsStronglyCocartesian.isIso_of_base_isIso
      (crossStageProjection.{u, v} U) (𝟙 Y) counit.1
  exact semanticGeomFiberHom_isIso_of_total_isIso counit

/-- The generated counit does not change the fixed coefficient ring. -/
theorem semanticGeometryTransportPullCounit_app_coefficientHom
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y)
    (target : GeomFiber.{u, v} Y) :
    ((semanticGeometryTransportPullCounit input).app target).1.geometry.coefficientHom =
      RingHom.id target.1.Coefficient := by
  have h := congrArg
    (fun hom : GeometryTotalHom _ _ => hom.geometry.coefficientHom)
    (semanticGeometryTransportPullCounit_app_fac input target)
  simpa [GeometryTotalHom.comp, GeomReadHom.comp, geomFiberLift,
    geomTransportAlongHom, geomTransportAlongGeometryHom] using h

/-- The generated exact complete-geometry adjunction counit is a natural
isomorphism. -/
theorem semanticGeometryTransportPullCounit_isIso
    {U : AtomCarrier.{u}}
    {X Y : ExtractionInstance U}
    (input : ExtInstHom X Y) :
    IsIso (semanticGeometryTransportPullCounit input) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro target
  exact semanticGeometryTransportPullCounit_app_isIso input target

end AAT.AG.FullGeometryNormalization

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization
