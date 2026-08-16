import ResearchLean.AG.CrossStageCoherence.PastingObstruction

/-!
# Pseudofunctor and obstruction-vocabulary unification

The compositor component itself is an isomorphism between the direct and
iterated transport targets, not an automorphism of either endpoint.  Its
categorical role is therefore recorded by normalizing the actual component
through two selected endpoint lifts.  The resulting `C_G` element equals the
canonical endpoint comparator, and core pushforward gives the analogous
normalized core compositor.  The specialized two-cell comparator invokes this
normalization; path whiskering and the resulting raw cochain then connect to
the general obstruction API.

## Implementation notes

The actual compositor component has distinct endpoints, so it is normalized
through the selected endpoint lifts before being read as a `C_G` element.
Merely aliasing the canonical comparator was rejected; the subsequent
equalities explicitly connect the genuine component, its pushforward, and the
specialized obstruction cochain.
-/

namespace AAT.AG.CrossStageCoherence

universe u v

open CategoryTheory
open AtomFoundation
open GeometryTransport
open TransportCoherence

set_option maxHeartbeats 3000000

/-- The pseudofunctor compositor normalizes the direct lift to the iterated
lift; it is deliberately not assigned a `C_G` type across distinct targets. -/
theorem pseudofunctorCompositor_normalization {U : AtomCarrier.{u}}
    {X Y Z : ExtractionInstance U} (σ : X ⟶ Y) (τ : Y ⟶ Z)
    (G : GeomFiber.{u, v} X) :
    geomFiberLift (σ ≫ τ) G ≫ (geomFiberCompositorApp σ τ G).hom.1 =
      geomFiberIteratedLift σ τ G :=
  geomFiberCompositorApp_hom_fac σ τ G

/-- Normalize the actual geometry compositor to two selected endpoint lifts. -/
noncomputable def normalizedGeomCompositor
    {U : AtomCarrier.{u}} {Y : ExtractionInstance U}
    {G : GeometryPackage.{u, v} U} {H : GeometryPackage.{u, v} U}
    (σ : packagePoint G.core ⟶ Y) (τ : Y ⟶ packagePoint H.core)
    (left right : GeometryTotalHom G H)
    (leftBase : left.base.base = σ ≫ τ)
    (rightBase : right.base.base = σ ≫ τ)
    [(geometryProjection U).IsStronglyCocartesian left.base left]
    [(geometryProjection U).IsStronglyCocartesian right.base right]
    [(packageProjection U).IsStronglyCocartesian left.base.base left.base]
    [(packageProjection U).IsStronglyCocartesian right.base.base right.base] :
    CompositeFiberAut H := by
  let source : GeomFiber.{u, v} (packagePoint G.core) := geomFiberMk G
  let target : GeomFiber.{u, v} (packagePoint H.core) := geomFiberMk H
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      left.base.base left := geometryHom_isCompositeStronglyCocartesian left
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      right.base.base right := geometryHom_isCompositeStronglyCocartesian right
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      ((crossStageProjection.{u, v} U).map left) left := by
    simpa only [crossStageProjection_map] using
      geometryHom_isCompositeStronglyCocartesian left
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      ((crossStageProjection.{u, v} U).map right) right := by
    simpa only [crossStageProjection_map] using
      geometryHom_isCompositeStronglyCocartesian right
  letI : (crossStageProjection.{u, v} U).IsHomLift (σ ≫ τ) left := by
    apply CategoryTheory.IsHomLift.of_commsq
      (crossStageProjection.{u, v} U) (σ ≫ τ) left rfl rfl
    simpa only [crossStageProjection_map, Category.id_comp, Category.comp_id] using leftBase
  letI : (crossStageProjection.{u, v} U).IsHomLift (σ ≫ τ) right := by
    apply CategoryTheory.IsHomLift.of_commsq
      (crossStageProjection.{u, v} U) (σ ≫ τ) right rfl rfl
    simpa only [crossStageProjection_map, Category.id_comp, Category.comp_id] using rightBase
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      (σ ≫ τ) left := stronglyCocartesian_of_isHomLift _ _ _
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      (σ ≫ τ) right := stronglyCocartesian_of_isHomLift _ _ _
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      (σ ≫ τ) (geomFiberLift (σ ≫ τ) source) :=
    geomFiberLift_isStronglyCocartesian (σ ≫ τ) source
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      (σ ≫ τ) (geomFiberIteratedLift σ τ source) :=
    geomFiberIteratedLift_isStronglyCocartesian σ τ source
  let directToLeft :
      (geomFiberTransportFunctor (σ ≫ τ)).obj source ≅ target :=
    strongLiftComparisonIso (crossStageProjection.{u, v} U) (σ ≫ τ)
      (geomFiberLift (σ ≫ τ) source) left
  let iteratedToRight :
      (geomFiberTransportFunctor τ).obj
          ((geomFiberTransportFunctor σ).obj source) ≅ target :=
    strongLiftComparisonIso (crossStageProjection.{u, v} U) (σ ≫ τ)
      (geomFiberIteratedLift σ τ source) right
  let endpointIso : target ≅ target :=
    directToLeft.symm |>.trans
      ((geomFiberCompositorApp σ τ source).trans iteratedToRight)
  let underlying : H ≅ H :=
    { hom := endpointIso.hom.1
      inv := endpointIso.inv.1
      hom_inv_id := by
        have equality := congrArg
          (fun morphism : target ⟶ target => morphism.1)
          endpointIso.hom_inv_id
        change endpointIso.hom.1 ≫ endpointIso.inv.1 = 𝟙 H at equality
        exact equality
      inv_hom_id := by
        have equality := congrArg
          (fun morphism : target ⟶ target => morphism.1)
          endpointIso.inv_hom_id
        change endpointIso.inv.1 ≫ endpointIso.hom.1 = 𝟙 H at equality
        exact equality }
  letI : (crossStageProjection.{u, v} U).IsHomLift
      (𝟙 (packagePoint H.core)) endpointIso.hom.1 := endpointIso.hom.2
  have homBase : underlying.hom.base.base = 𝟙 (packagePoint H.core) :=
    (CategoryTheory.IsHomLift.eq_of_isHomLift
      (crossStageProjection.{u, v} U) (𝟙 (packagePoint H.core))
      endpointIso.hom.1).symm
  exact ⟨underlying, homBase⟩

/-- The compositor-normalized geometry automorphism factors the selected left lift. -/
theorem normalizedGeomCompositor_fac
    {U : AtomCarrier.{u}} {Y : ExtractionInstance U}
    {G H : GeometryPackage.{u, v} U}
    (σ : packagePoint G.core ⟶ Y) (τ : Y ⟶ packagePoint H.core)
    (left right : GeometryTotalHom G H)
    (leftBase : left.base.base = σ ≫ τ)
    (rightBase : right.base.base = σ ≫ τ)
    [(geometryProjection U).IsStronglyCocartesian left.base left]
    [(geometryProjection U).IsStronglyCocartesian right.base right]
    [(packageProjection U).IsStronglyCocartesian left.base.base left.base]
    [(packageProjection U).IsStronglyCocartesian right.base.base right.base] :
    left.comp (CompositeFiberAut.hom
      (normalizedGeomCompositor σ τ left right
        leftBase rightBase)) = right := by
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      left.base.base left := geometryHom_isCompositeStronglyCocartesian left
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      right.base.base right := geometryHom_isCompositeStronglyCocartesian right
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      ((crossStageProjection.{u, v} U).map left) left := by
    simpa only [crossStageProjection_map] using
      geometryHom_isCompositeStronglyCocartesian left
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      ((crossStageProjection.{u, v} U).map right) right := by
    simpa only [crossStageProjection_map] using
      geometryHom_isCompositeStronglyCocartesian right
  letI : (crossStageProjection.{u, v} U).IsHomLift (σ ≫ τ) left := by
    apply CategoryTheory.IsHomLift.of_commsq
      (crossStageProjection.{u, v} U) (σ ≫ τ) left rfl rfl
    simpa only [crossStageProjection_map, Category.id_comp, Category.comp_id] using leftBase
  letI : (crossStageProjection.{u, v} U).IsHomLift (σ ≫ τ) right := by
    apply CategoryTheory.IsHomLift.of_commsq
      (crossStageProjection.{u, v} U) (σ ≫ τ) right rfl rfl
    simpa only [crossStageProjection_map, Category.id_comp, Category.comp_id] using rightBase
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      (σ ≫ τ) left := stronglyCocartesian_of_isHomLift _ _ _
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      (σ ≫ τ) right := stronglyCocartesian_of_isHomLift _ _ _
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      (σ ≫ τ) (geomFiberLift (σ ≫ τ) (geomFiberMk G)) :=
    geomFiberLift_isStronglyCocartesian (σ ≫ τ) (geomFiberMk G)
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      (σ ≫ τ) (geomFiberIteratedLift σ τ (geomFiberMk G)) :=
    geomFiberIteratedLift_isStronglyCocartesian σ τ (geomFiberMk G)
  let directToLeft :
      (geomFiberTransportFunctor (σ ≫ τ)).obj (geomFiberMk G) ≅
        geomFiberMk H :=
    strongLiftComparisonIso (crossStageProjection.{u, v} U) (σ ≫ τ)
      (geomFiberLift (σ ≫ τ) (geomFiberMk G)) left
  let iteratedToRight :
      (geomFiberTransportFunctor τ).obj
          ((geomFiberTransportFunctor σ).obj (geomFiberMk G)) ≅ geomFiberMk H :=
    strongLiftComparisonIso (crossStageProjection.{u, v} U) (σ ≫ τ)
      (geomFiberIteratedLift σ τ (geomFiberMk G)) right
  have directFac : geomFiberLift (σ ≫ τ) (geomFiberMk G) ≫
      directToLeft.hom.1 = left := by
    exact strongLiftComparisonHom_fac
      (C := geomFiberMk H) (crossStageProjection.{u, v} U) (σ ≫ τ)
        (geomFiberLift (σ ≫ τ) (geomFiberMk G)) left
  have iteratedFac : geomFiberIteratedLift σ τ (geomFiberMk G) ≫
      iteratedToRight.hom.1 = right := by
    exact strongLiftComparisonHom_fac
      (C := geomFiberMk H) (crossStageProjection.{u, v} U) (σ ≫ τ)
        (geomFiberIteratedLift σ τ (geomFiberMk G)) right
  unfold normalizedGeomCompositor
  dsimp only
  change left ≫
      (directToLeft.inv.1 ≫
        ((geomFiberCompositorApp σ τ (geomFiberMk G)).hom.1 ≫
          iteratedToRight.hom.1)) = right
  have directCancel : directToLeft.hom.1 ≫ directToLeft.inv.1 =
      𝟙 _ := congrArg (fun morphism => morphism.1) directToLeft.hom_inv_id
  have directTailCancel : directToLeft.hom.1 ≫
      (directToLeft.inv.1 ≫
        ((geomFiberCompositorApp σ τ (geomFiberMk G)).hom.1 ≫
          iteratedToRight.hom.1)) =
      (geomFiberCompositorApp σ τ (geomFiberMk G)).hom.1 ≫
        iteratedToRight.hom.1 := by
    rw [← Category.assoc, directCancel, Category.id_comp]
  calc
    left ≫ (directToLeft.inv.1 ≫
        ((geomFiberCompositorApp σ τ (geomFiberMk G)).hom.1 ≫
          iteratedToRight.hom.1)) =
      (geomFiberLift (σ ≫ τ) (geomFiberMk G) ≫ directToLeft.hom.1) ≫
        (directToLeft.inv.1 ≫
          ((geomFiberCompositorApp σ τ (geomFiberMk G)).hom.1 ≫
            iteratedToRight.hom.1)) := by rw [directFac]
    _ = geomFiberLift (σ ≫ τ) (geomFiberMk G) ≫
        ((geomFiberCompositorApp σ τ (geomFiberMk G)).hom.1 ≫
          iteratedToRight.hom.1) := by rw [Category.assoc, directTailCancel]
    _ = (geomFiberLift (σ ≫ τ) (geomFiberMk G) ≫
          (geomFiberCompositorApp σ τ (geomFiberMk G)).hom.1) ≫
        iteratedToRight.hom.1 := by rw [Category.assoc]
    _ = geomFiberIteratedLift σ τ (geomFiberMk G) ≫
        iteratedToRight.hom.1 := by rw [geomFiberCompositorApp_hom_fac]
    _ = right := iteratedFac

/-- Actual compositor normalization is the canonical composite-fiber comparator. -/
theorem normalizedGeomCompositor_eq_canonical
    {U : AtomCarrier.{u}} {Y : ExtractionInstance U}
    {G H : GeometryPackage.{u, v} U}
    (σ : packagePoint G.core ⟶ Y) (τ : Y ⟶ packagePoint H.core)
    (left right : GeometryTotalHom G H)
    (leftBase : left.base.base = σ ≫ τ)
    (rightBase : right.base.base = σ ≫ τ)
    [(geometryProjection U).IsStronglyCocartesian left.base left]
    [(geometryProjection U).IsStronglyCocartesian right.base right]
    [(packageProjection U).IsStronglyCocartesian left.base.base left.base]
    [(packageProjection U).IsStronglyCocartesian right.base.base right.base] :
    normalizedGeomCompositor σ τ left right leftBase rightBase =
      canonicalCompositeFiberComparator left right (leftBase.trans rightBase.symm) := by
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      left.base.base left := geometryHom_isCompositeStronglyCocartesian left
  apply CompositeFiberAut.ext_of_strong_fac left
  exact (normalizedGeomCompositor_fac σ τ left right
      leftBase rightBase).trans
    (canonicalCompositeFiberComparator_fac left right
      (leftBase.trans rightBase.symm)).symm

/-- Normalize the actual core compositor to the projected selected endpoint lifts. -/
noncomputable def normalizedCoreCompositor
    {U : AtomCarrier.{u}} {Y : ExtractionInstance U}
    {P Q : AATCorePackage U}
    (σ : packagePoint P ⟶ Y) (τ : Y ⟶ packagePoint Q)
    (left right : PackageTotalHom P Q)
    (leftBase : left.base = σ ≫ τ)
    (rightBase : right.base = σ ≫ τ)
    [(packageProjection U).IsStronglyCocartesian left.base left]
    [(packageProjection U).IsStronglyCocartesian right.base right] :
    PackageFiberAut Q := by
  let source : CoreFiber (packagePoint P) := ⟨P, rfl⟩
  let target : CoreFiber (packagePoint Q) := ⟨Q, rfl⟩
  letI : (packageProjection U).IsStronglyCocartesian
      ((packageProjection U).map left) left := by
    simpa only [packageProjection_map] using
      (inferInstanceAs
        ((packageProjection U).IsStronglyCocartesian left.base left))
  letI : (packageProjection U).IsStronglyCocartesian
      ((packageProjection U).map right) right := by
    simpa only [packageProjection_map] using
      (inferInstanceAs
        ((packageProjection U).IsStronglyCocartesian right.base right))
  letI : (packageProjection U).IsHomLift (σ ≫ τ) left := by
    apply CategoryTheory.IsHomLift.of_commsq
      (packageProjection U) (σ ≫ τ) left rfl rfl
    simpa only [packageProjection_map, Category.id_comp, Category.comp_id] using leftBase
  letI : (packageProjection U).IsHomLift (σ ≫ τ) right := by
    apply CategoryTheory.IsHomLift.of_commsq
      (packageProjection U) (σ ≫ τ) right rfl rfl
    simpa only [packageProjection_map, Category.id_comp, Category.comp_id] using rightBase
  letI : (packageProjection U).IsStronglyCocartesian (σ ≫ τ) left :=
    stronglyCocartesian_of_isHomLift _ _ _
  letI : (packageProjection U).IsStronglyCocartesian (σ ≫ τ) right :=
    stronglyCocartesian_of_isHomLift _ _ _
  letI : (packageProjection U).IsStronglyCocartesian
      (σ ≫ τ) (coreFiberLift (σ ≫ τ) source) :=
    coreFiberLift_isStronglyCocartesian (σ ≫ τ) source
  letI : (packageProjection U).IsStronglyCocartesian
      (σ ≫ τ) (coreFiberIteratedLift σ τ source) :=
    coreFiberIteratedLift_isStronglyCocartesian σ τ source
  let directToLeft :
      (coreFiberTransportFunctor (σ ≫ τ)).obj source ≅ target :=
    strongLiftComparisonIso (packageProjection U) (σ ≫ τ)
      (coreFiberLift (σ ≫ τ) source) left
  let iteratedToRight :
      (coreFiberTransportFunctor τ).obj
          ((coreFiberTransportFunctor σ).obj source) ≅ target :=
    strongLiftComparisonIso (packageProjection U) (σ ≫ τ)
      (coreFiberIteratedLift σ τ source) right
  let endpointIso : target ≅ target :=
    directToLeft.symm |>.trans
      ((coreFiberCompositorApp σ τ source).trans iteratedToRight)
  let underlying : Q ≅ Q :=
    { hom := endpointIso.hom.1
      inv := endpointIso.inv.1
      hom_inv_id := by
        have equality := congrArg
          (fun morphism : target ⟶ target => morphism.1)
          endpointIso.hom_inv_id
        change endpointIso.hom.1 ≫ endpointIso.inv.1 = 𝟙 Q at equality
        exact equality
      inv_hom_id := by
        have equality := congrArg
          (fun morphism : target ⟶ target => morphism.1)
          endpointIso.inv_hom_id
        change endpointIso.inv.1 ≫ endpointIso.hom.1 = 𝟙 Q at equality
        exact equality }
  letI : (packageProjection U).IsHomLift
      (𝟙 (packagePoint Q)) endpointIso.hom.1 := endpointIso.hom.2
  have homBase : underlying.hom.base = 𝟙 (packagePoint Q) :=
    (CategoryTheory.IsHomLift.eq_of_isHomLift
      (packageProjection U) (𝟙 (packagePoint Q)) endpointIso.hom.1).symm
  exact ⟨underlying, homBase⟩

/-- The compositor-normalized core automorphism factors the selected left lift. -/
theorem normalizedCoreCompositor_fac
    {U : AtomCarrier.{u}} {Y : ExtractionInstance U}
    {P Q : AATCorePackage U}
    (σ : packagePoint P ⟶ Y) (τ : Y ⟶ packagePoint Q)
    (left right : PackageTotalHom P Q)
    (leftBase : left.base = σ ≫ τ)
    (rightBase : right.base = σ ≫ τ)
    [(packageProjection U).IsStronglyCocartesian left.base left]
    [(packageProjection U).IsStronglyCocartesian right.base right] :
    left.comp (PackageFiberAut.hom
      (normalizedCoreCompositor σ τ left right
        leftBase rightBase)) = right := by
  letI : (packageProjection U).IsStronglyCocartesian
      ((packageProjection U).map left) left := by
    simpa only [packageProjection_map] using
      (inferInstanceAs
        ((packageProjection U).IsStronglyCocartesian left.base left))
  letI : (packageProjection U).IsStronglyCocartesian
      ((packageProjection U).map right) right := by
    simpa only [packageProjection_map] using
      (inferInstanceAs
        ((packageProjection U).IsStronglyCocartesian right.base right))
  letI : (packageProjection U).IsHomLift (σ ≫ τ) left := by
    apply CategoryTheory.IsHomLift.of_commsq
      (packageProjection U) (σ ≫ τ) left rfl rfl
    simpa only [packageProjection_map, Category.id_comp, Category.comp_id] using leftBase
  letI : (packageProjection U).IsHomLift (σ ≫ τ) right := by
    apply CategoryTheory.IsHomLift.of_commsq
      (packageProjection U) (σ ≫ τ) right rfl rfl
    simpa only [packageProjection_map, Category.id_comp, Category.comp_id] using rightBase
  letI : (packageProjection U).IsStronglyCocartesian (σ ≫ τ) left :=
    stronglyCocartesian_of_isHomLift _ _ _
  letI : (packageProjection U).IsStronglyCocartesian (σ ≫ τ) right :=
    stronglyCocartesian_of_isHomLift _ _ _
  letI : (packageProjection U).IsStronglyCocartesian
      (σ ≫ τ) (coreFiberLift (σ ≫ τ) (⟨P, rfl⟩ : CoreFiber _)) :=
    coreFiberLift_isStronglyCocartesian (σ ≫ τ) (⟨P, rfl⟩ : CoreFiber _)
  letI : (packageProjection U).IsStronglyCocartesian
      (σ ≫ τ) (coreFiberIteratedLift σ τ (⟨P, rfl⟩ : CoreFiber _)) :=
    coreFiberIteratedLift_isStronglyCocartesian σ τ (⟨P, rfl⟩ : CoreFiber _)
  let directToLeft :
      (coreFiberTransportFunctor (σ ≫ τ)).obj (⟨P, rfl⟩ : CoreFiber _) ≅
        (⟨Q, rfl⟩ : CoreFiber _) :=
    strongLiftComparisonIso (packageProjection U) (σ ≫ τ)
      (coreFiberLift (σ ≫ τ) (⟨P, rfl⟩ : CoreFiber _)) left
  let iteratedToRight :
      (coreFiberTransportFunctor τ).obj
          ((coreFiberTransportFunctor σ).obj (⟨P, rfl⟩ : CoreFiber _)) ≅
        (⟨Q, rfl⟩ : CoreFiber _) :=
    strongLiftComparisonIso (packageProjection U) (σ ≫ τ)
      (coreFiberIteratedLift σ τ (⟨P, rfl⟩ : CoreFiber _)) right
  have directFac : coreFiberLift (σ ≫ τ) (⟨P, rfl⟩ : CoreFiber _) ≫
      directToLeft.hom.1 = left := by
    exact strongLiftComparisonHom_fac (C := (⟨Q, rfl⟩ : CoreFiber _))
      (packageProjection U) (σ ≫ τ)
        (coreFiberLift (σ ≫ τ) (⟨P, rfl⟩ : CoreFiber _)) left
  have iteratedFac : coreFiberIteratedLift σ τ (⟨P, rfl⟩ : CoreFiber _) ≫
      iteratedToRight.hom.1 = right := by
    exact strongLiftComparisonHom_fac (C := (⟨Q, rfl⟩ : CoreFiber _))
      (packageProjection U) (σ ≫ τ)
        (coreFiberIteratedLift σ τ (⟨P, rfl⟩ : CoreFiber _)) right
  unfold normalizedCoreCompositor
  dsimp only
  change left ≫
      (directToLeft.inv.1 ≫
        ((coreFiberCompositorApp σ τ (⟨P, rfl⟩ : CoreFiber _)).hom.1 ≫
          iteratedToRight.hom.1)) = right
  have directCancel : directToLeft.hom.1 ≫ directToLeft.inv.1 =
      𝟙 _ := congrArg (fun morphism => morphism.1) directToLeft.hom_inv_id
  have directTailCancel : directToLeft.hom.1 ≫
      (directToLeft.inv.1 ≫
        ((coreFiberCompositorApp σ τ (⟨P, rfl⟩ : CoreFiber _)).hom.1 ≫
          iteratedToRight.hom.1)) =
      (coreFiberCompositorApp σ τ (⟨P, rfl⟩ : CoreFiber _)).hom.1 ≫
        iteratedToRight.hom.1 := by
    rw [← Category.assoc, directCancel, Category.id_comp]
  calc
    left ≫ (directToLeft.inv.1 ≫
        ((coreFiberCompositorApp σ τ (⟨P, rfl⟩ : CoreFiber _)).hom.1 ≫
          iteratedToRight.hom.1)) =
      (coreFiberLift (σ ≫ τ) (⟨P, rfl⟩ : CoreFiber _) ≫ directToLeft.hom.1) ≫
        (directToLeft.inv.1 ≫
          ((coreFiberCompositorApp σ τ (⟨P, rfl⟩ : CoreFiber _)).hom.1 ≫
            iteratedToRight.hom.1)) := by rw [directFac]
    _ = coreFiberLift (σ ≫ τ) (⟨P, rfl⟩ : CoreFiber _) ≫
        ((coreFiberCompositorApp σ τ (⟨P, rfl⟩ : CoreFiber _)).hom.1 ≫
          iteratedToRight.hom.1) := by rw [Category.assoc, directTailCancel]
    _ = (coreFiberLift (σ ≫ τ) (⟨P, rfl⟩ : CoreFiber _) ≫
          (coreFiberCompositorApp σ τ (⟨P, rfl⟩ : CoreFiber _)).hom.1) ≫
        iteratedToRight.hom.1 := by rw [Category.assoc]
    _ = coreFiberIteratedLift σ τ (⟨P, rfl⟩ : CoreFiber _) ≫
        iteratedToRight.hom.1 := by rw [coreFiberCompositorApp_hom_fac]
    _ = right := iteratedFac

/-- Actual core compositor normalization is the canonical core comparator. -/
theorem normalizedCoreCompositor_eq_canonical
    {U : AtomCarrier.{u}} {Y : ExtractionInstance U}
    {P Q : AATCorePackage U}
    (σ : packagePoint P ⟶ Y) (τ : Y ⟶ packagePoint Q)
    (left right : PackageTotalHom P Q)
    (leftBase : left.base = σ ≫ τ)
    (rightBase : right.base = σ ≫ τ)
    [(packageProjection U).IsStronglyCocartesian left.base left]
    [(packageProjection U).IsStronglyCocartesian right.base right] :
    normalizedCoreCompositor σ τ left right leftBase rightBase =
      canonicalFiberComparator left right (leftBase.trans rightBase.symm) := by
  apply PackageFiberAut.ext_of_strong_fac left
  exact (normalizedCoreCompositor_fac σ τ left right
      leftBase rightBase).trans
    (canonicalFiberComparator_fac left right
      (leftBase.trans rightBase.symm)).symm

/-- Projection carries actual geometry normalization to actual core normalization. -/
theorem normalizedGeomCompositor_pushforward
    {U : AtomCarrier.{u}} {Y : ExtractionInstance U}
    {G H : GeometryPackage.{u, v} U}
    (σ : packagePoint G.core ⟶ Y) (τ : Y ⟶ packagePoint H.core)
    (left right : GeometryTotalHom G H)
    (leftBase : left.base.base = σ ≫ τ)
    (rightBase : right.base.base = σ ≫ τ)
    [(geometryProjection U).IsStronglyCocartesian left.base left]
    [(geometryProjection U).IsStronglyCocartesian right.base right]
    [(packageProjection U).IsStronglyCocartesian left.base.base left.base]
    [(packageProjection U).IsStronglyCocartesian right.base.base right.base] :
    compositeFiberPushforward H
        (normalizedGeomCompositor σ τ left right
          leftBase rightBase) =
      normalizedCoreCompositor σ τ left.base right.base
        leftBase rightBase := by
  rw [normalizedGeomCompositor_eq_canonical,
    normalizedCoreCompositor_eq_canonical,
    compositeFiberPushforward_canonicalComparator]

/-- The first-generator split of a selected path at the pointed base. -/
structure PathBaseSplit
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U) {i j : P.Vertex}
    (path : P.Path i j) where
  /-- Intermediate vertex after the first selected generator. -/
  mid : P.Vertex
  /-- Pointed arrow contributed by the first path segment. -/
  first : packagePoint (data.geometry i).core ⟶
    packagePoint (data.geometry mid).core
  /-- Pointed arrow contributed by the remaining path segment. -/
  second : packagePoint (data.geometry mid).core ⟶
    packagePoint (data.geometry j).core
  /-- The two pointed segments compose to the selected path base. -/
  fac : first ≫ second = (data.pathLift path).base.base

/-- Split a path into its first edge and remaining pointed base arrows. -/
noncomputable def pathBaseSplit
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U) {i j : P.Vertex}
    (path : P.Path i j) : PathBaseSplit data path :=
  match path with
  | .nil vertex =>
      { mid := vertex
        first := 𝟙 _
        second := 𝟙 _
        fac := by rfl }
  | .cons edge tail =>
      { mid := _
        first := (data.edgeLift edge).base.base
        second := (data.pathLift tail).base.base
        fac := by rfl }



/-- After normalization to one endpoint, path whiskering produces an actual
`C_G` element with its universal-property factorization. -/
theorem pseudofunctorWhiskering_compositeFiber_fac
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U)
    (reselection : UpperEdgeReselection data) {i j : P.Vertex}
    (automorphism : CompositeFiberAut (data.geometry i))
    (path : P.Path i j) :
    (upperReselectedPathLift data reselection path).comp
      (CompositeFiberAut.hom
        (upperWhiskerCompositeFiberAut data reselection automorphism path)) =
      upperFiberAutThenPath data reselection automorphism path :=
  upperWhiskerCompositeFiberAut_fac data reselection automorphism path

/-- The `p` image of normalized upper whiskering is exactly the inherited core
whiskering, rather than a separately supplied compatibility. -/
theorem pseudofunctorWhiskering_pushforward
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerLiftData.{u, v} P U)
    (reselection : UpperEdgeReselection data) {i j : P.Vertex}
    (automorphism : CompositeFiberAut (data.geometry i))
    (path : P.Path i j) :
    compositeFiberPushforward (data.geometry j)
        (upperWhiskerCompositeFiberAut data reselection automorphism path) =
      whiskerFiberAut data.coreLiftData
        (pushforwardEdgeReselection data reselection)
        (compositeFiberPushforward (data.geometry i) automorphism) path :=
  pushforward_upperWhiskerCompositeFiberAut
    data reselection automorphism path

/-- Specialized comparator rebuilt directly from the general `C_G`
comparison after normalization of both paths to their declared endpoint. -/
noncomputable def pseudofunctorCanonicalComparator
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) (cell : P.TwoCell) :
    CompositeFiberAut (data.lift.geometry (P.twoTarget cell)) := by
  letI : (geometryProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoLeft cell)).base
      (upperReselectedPathLift data.lift reselection (P.twoLeft cell)) :=
    (upperReselectLiftData data.lift reselection).pathLift_geometryStrong
      (P.twoLeft cell)
  letI : (geometryProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoRight cell)).base
      (upperReselectedPathLift data.lift reselection (P.twoRight cell)) :=
    (upperReselectLiftData data.lift reselection).pathLift_geometryStrong
      (P.twoRight cell)
  letI : (packageProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoLeft cell)).base.base
      (upperReselectedPathLift data.lift reselection
        (P.twoLeft cell)).base :=
    (upperReselectLiftData data.lift reselection).pathLift_coreStrong
      (P.twoLeft cell)
  letI : (packageProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoRight cell)).base.base
      (upperReselectedPathLift data.lift reselection
        (P.twoRight cell)).base :=
    (upperReselectLiftData data.lift reselection).pathLift_coreStrong
      (P.twoRight cell)
  let split := pathBaseSplit
    (upperReselectLiftData data.lift reselection) (P.twoLeft cell)
  let left := upperReselectedPathLift data.lift reselection (P.twoLeft cell)
  let right := upperReselectedPathLift data.lift reselection (P.twoRight cell)
  have leftBase : left.base.base = split.first ≫ split.second := split.fac.symm
  have rightBase : right.base.base = split.first ≫ split.second :=
    (upperReselectedTwoCellBase data reselection cell).symm.trans leftBase
  exact normalizedGeomCompositor split.first split.second left right
    leftBase rightBase

/-- The reconstructed specialization is the obstruction vocabulary's canonical
comparator, by strong-cocartesian uniqueness. -/
theorem pseudofunctorCanonicalComparator_eq_upper
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) (cell : P.TwoCell) :
    pseudofunctorCanonicalComparator data reselection cell =
      upperCanonicalTwoCellComparator data reselection cell := by
  let left := upperReselectedPathLift data.lift reselection (P.twoLeft cell)
  let right := upperReselectedPathLift data.lift reselection (P.twoRight cell)
  letI : (geometryProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoLeft cell)).base
      (upperReselectedPathLift data.lift reselection (P.twoLeft cell)) :=
    (upperReselectLiftData data.lift reselection).pathLift_geometryStrong
      (P.twoLeft cell)
  letI : (geometryProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoRight cell)).base
      (upperReselectedPathLift data.lift reselection (P.twoRight cell)) :=
    (upperReselectLiftData data.lift reselection).pathLift_geometryStrong
      (P.twoRight cell)
  letI : (packageProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoLeft cell)).base.base
      (upperReselectedPathLift data.lift reselection
        (P.twoLeft cell)).base :=
    (upperReselectLiftData data.lift reselection).pathLift_coreStrong
      (P.twoLeft cell)
  letI : (packageProjection U).IsStronglyCocartesian
      (upperReselectedPathLift data.lift reselection
        (P.twoRight cell)).base.base
      (upperReselectedPathLift data.lift reselection
        (P.twoRight cell)).base :=
    (upperReselectLiftData data.lift reselection).pathLift_coreStrong
      (P.twoRight cell)
  letI : (crossStageProjection.{u, v} U).IsStronglyCocartesian
      left.base.base left :=
    (upperReselectLiftData data.lift reselection).pathLift_compositeStrong
      (P.twoLeft cell)
  have comparatorFac : left.comp
      (CompositeFiberAut.hom
        (pseudofunctorCanonicalComparator data reselection cell)) = right := by
    unfold pseudofunctorCanonicalComparator
    dsimp only
    apply normalizedGeomCompositor_fac
  apply CompositeFiberAut.ext_of_strong_fac left
  exact comparatorFac.trans
      (upperCanonicalTwoCellComparator_fac data reselection cell).symm

/-- Pseudofunctor-specialized raw defect, with authored and generated
provenance kept separate. -/
noncomputable def pseudofunctorRawTwoCellDefect
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) (cell : P.TwoCell) :
    CompositeFiberAut (data.lift.geometry (P.twoTarget cell)) :=
  data.comparator cell *
    (pseudofunctorCanonicalComparator data reselection cell)⁻¹

/-- The compositor-derived two-cell defect agrees with the upper obstruction API. -/
theorem pseudofunctorRawTwoCellDefect_eq_upper
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) (cell : P.TwoCell) :
    pseudofunctorRawTwoCellDefect data reselection cell =
      upperRawTwoCellDefect data reselection cell := by
  rw [pseudofunctorRawTwoCellDefect, upperRawTwoCellDefect,
    pseudofunctorCanonicalComparator_eq_upper]

/-- Assemble the compositor-derived two-cell defects into the specialized cochain. -/
noncomputable def pseudofunctorRawDefectCochain
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) :
    UpperDefectCochain data :=
  fun cell => pseudofunctorRawTwoCellDefect data reselection cell

/-- The specialized compositor cochain is pointwise the general upper cochain. -/
theorem pseudofunctorRawDefectCochain_eq_upper
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U)
    (reselection : UpperEdgeReselection data.lift) :
    pseudofunctorRawDefectCochain data reselection =
      upperRawDefectCochain data reselection := by
  funext cell
  exact pseudofunctorRawTwoCellDefect_eq_upper data reselection cell

/-- Orbit vanishing stated using the independently reconstructed specialized
cochain. -/
def PseudofunctorObstructionVanishes
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) : Prop :=
  ∃ reselection : UpperEdgeReselection data.lift,
    pseudofunctorRawDefectCochain data reselection =
      upperIdentityDefectCochain data

/-- The compositor-specialized orbit predicate is the general joint-vanishing predicate. -/
theorem pseudofunctorObstructionVanishes_iff_joint
    {P : FiniteTransportPresentation.{u}} {U : AtomCarrier.{u}}
    (data : TwoLayerTransportData.{u, v} P U) :
    PseudofunctorObstructionVanishes data ↔ JointVanishes data := by
  constructor
  · rintro ⟨reselection, identity⟩
    exact ⟨reselection,
      (pseudofunctorRawDefectCochain_eq_upper data reselection).symm.trans
        identity⟩
  · rintro ⟨reselection, identity⟩
    exact ⟨reselection,
      (pseudofunctorRawDefectCochain_eq_upper data reselection).trans
        identity⟩

end AAT.AG.CrossStageCoherence

#assert_standard_axioms_only AAT.AG.CrossStageCoherence
