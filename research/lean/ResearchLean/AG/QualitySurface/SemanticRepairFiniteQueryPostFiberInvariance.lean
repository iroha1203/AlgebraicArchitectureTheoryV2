import ResearchLean.AG.QualitySurface.SemanticRepairFiniteQueryReadingInsensitive

/-!
Cycle 28 evidence for `G-aat-quality-surface-04`.

This file gives an exact observation-level criterion for finite query-generated
observations to factor through the current canonical shadow.  The relevant
condition is not that every queried coordinate is current-shadow extensional,
and not that the post-map ignores all readings.  The exact condition is that
the post-map is invariant on every query-reading fiber over a fixed current
shadow.

This remains a support node.  It exposes the remaining premise instead of
deriving it from semantic soundness.
-/

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairFiniteQueryPostFiberInvariance

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryCurrentShadowCoordinates
open SemanticRepairFiniteQueryReadingInsensitive

universe u v w x y z

/-! ## Query-reading fibers over current shadows -/

/--
A query-reading vector is realizable over a fixed current canonical shadow
when some tower has that current shadow and that query trace vector.
-/
def QueryReadingsRealizableAtCurrentShadow
    {Atom : Type u}
    (query : List Atom)
    (shadow : FiniteTowerLayerShadow)
    (readings : List Bool) : Prop :=
  ∃ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
    canonicalTowerLayerShadow T = shadow ∧
      supportTraceVector query T.sourceTraceToken = readings

/--
A post-map is invariant on current-shadow fibers of a finite query when it
cannot distinguish any two query-reading vectors realized over the same current
shadow.
-/
def QueryPostInvariantOnCurrentShadowFibers
    {Atom : Type u}
    (query : List Atom)
    {Out : Type z}
    (post : FiniteTowerLayerShadow -> List Bool -> Out) : Prop :=
  ∀ shadow : FiniteTowerLayerShadow,
    ∀ leftReadings rightReadings : List Bool,
      QueryReadingsRealizableAtCurrentShadow.{u, v, w, x, y}
        (Atom := Atom) query shadow leftReadings ->
      QueryReadingsRealizableAtCurrentShadow.{u, v, w, x, y}
        (Atom := Atom) query shadow rightReadings ->
        post shadow leftReadings = post shadow rightReadings

/-- Each tower realizes its own query readings over its current shadow. -/
theorem queryReadingsRealizableAtCurrentShadow_self
    {Atom : Type u}
    (query : List Atom)
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    QueryReadingsRealizableAtCurrentShadow.{u, v, w, x, y}
      (Atom := Atom) query
      (canonicalTowerLayerShadow T)
      (supportTraceVector query T.sourceTraceToken) := by
  exact ⟨T, rfl, rfl⟩

/-! ## Exact observation-level criterion -/

/--
Fiber invariance of the post-map makes the generated finite query observation
current-shadow extensional.
-/
theorem queryTraceGeneratedObservation_shadowExtensional_of_postInvariantOnCurrentShadowFibers
    {Atom : Type u}
    {Out : Type z}
    {query : List Atom}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    (hinvariant :
      QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
        (Atom := Atom) query post) :
    ShadowExtensionalTowerObservation
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        post (canonicalTowerLayerShadow T)
          (supportTraceVector query T.sourceTraceToken)) := by
  intro left right hshadow
  change
    post (canonicalTowerLayerShadow left)
        (supportTraceVector query left.sourceTraceToken) =
      post (canonicalTowerLayerShadow right)
        (supportTraceVector query right.sourceTraceToken)
  rw [← hshadow]
  exact
    hinvariant
      (canonicalTowerLayerShadow left)
      (supportTraceVector query left.sourceTraceToken)
      (supportTraceVector query right.sourceTraceToken)
      (queryReadingsRealizableAtCurrentShadow_self query left)
      ⟨right, hshadow.symm, rfl⟩

/--
Current-shadow extensionality of the generated finite query observation forces
post-map invariance on every current-shadow fiber of the query.
-/
theorem postInvariantOnCurrentShadowFibers_of_queryTraceGeneratedObservation_shadowExtensional
    {Atom : Type u}
    {Out : Type z}
    {query : List Atom}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    (hext :
      ShadowExtensionalTowerObservation
        (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
          post (canonicalTowerLayerShadow T)
            (supportTraceVector query T.sourceTraceToken))) :
    QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
      (Atom := Atom) query post := by
  intro shadow leftReadings rightReadings hleft hright
  rcases hleft with ⟨left, hleftShadow, hleftReadings⟩
  rcases hright with ⟨right, hrightShadow, hrightReadings⟩
  have hshadow :
      canonicalTowerLayerShadow left = canonicalTowerLayerShadow right := by
    rw [hleftShadow, hrightShadow]
  have hobs := hext left right hshadow
  calc
    post shadow leftReadings =
        post (canonicalTowerLayerShadow left)
          (supportTraceVector query left.sourceTraceToken) := by
      rw [hleftShadow, hleftReadings]
    _ = post (canonicalTowerLayerShadow right)
          (supportTraceVector query right.sourceTraceToken) :=
      hobs
    _ = post shadow rightReadings := by
      rw [hrightShadow, hrightReadings]

/--
Exact criterion: a generated finite query observation is current-shadow
extensional iff its post-map is invariant on current-shadow fibers of that
query.
-/
theorem queryTraceGeneratedObservation_shadowExtensional_iff_postInvariantOnCurrentShadowFibers
    {Atom : Type u}
    {Out : Type z}
    (query : List Atom)
    (post : FiniteTowerLayerShadow -> List Bool -> Out) :
    ShadowExtensionalTowerObservation
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        post (canonicalTowerLayerShadow T)
          (supportTraceVector query T.sourceTraceToken)) ↔
      QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
        (Atom := Atom) query post := by
  exact
    ⟨postInvariantOnCurrentShadowFibers_of_queryTraceGeneratedObservation_shadowExtensional,
      queryTraceGeneratedObservation_shadowExtensional_of_postInvariantOnCurrentShadowFibers⟩

/--
Finite query package version of the exact current-shadow extensionality
criterion.
-/
theorem finiteTraceQueryObservation_shadowExtensional_iff_postInvariantOnCurrentShadowFibers
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (obs : FiniteTraceQueryObservation support Out) :
    ShadowExtensionalTowerObservation
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        obs.observe T) ↔
      QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
        (Atom := Atom) obs.query obs.post := by
  exact
    queryTraceGeneratedObservation_shadowExtensional_iff_postInvariantOnCurrentShadowFibers
      obs.query obs.post

/--
Post fiber invariance gives canonical-shadow factorization for finite query
packages.
-/
theorem finiteTraceQueryObservation_eq_canonicalShadowFactor_of_postInvariantOnCurrentShadowFibers
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (obs : FiniteTraceQueryObservation support Out)
    (hinvariant :
      QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
        (Atom := Atom) obs.query obs.post)
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    obs.observe T =
      canonicalShadowFactor
        (fun U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
          obs.observe U)
        (canonicalTowerLayerShadow T) := by
  exact
    shadowExtensionalObservation_factors
      ((finiteTraceQueryObservation_shadowExtensional_iff_postInvariantOnCurrentShadowFibers
        obs).2 hinvariant)
      T

/-! ## Previous sufficient conditions as fiber-invariance routes -/

/--
Query-coordinate current-shadow extensionality implies the exact post-fiber
invariance condition for every post-map.
-/
theorem postInvariantOnCurrentShadowFibers_of_queryCoordinateCurrentShadowExtensional
    {Atom : Type u}
    {Out : Type z}
    {query : List Atom}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    (hcoords :
      QueryTraceCoordinatesCurrentShadowExtensional.{u, v, w, x, y} query) :
    QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
      (Atom := Atom) query post := by
  exact
    postInvariantOnCurrentShadowFibers_of_queryTraceGeneratedObservation_shadowExtensional
      (queryTraceGeneratedObservation_shadowExtensional_of_coordinateCurrentShadowExtensional
        hcoords post)

/--
Reading-insensitive post-maps are invariant on every current-shadow fiber.
-/
theorem postInvariantOnCurrentShadowFibers_of_queryReadingsInsensitive
    {Atom : Type u}
    {Out : Type z}
    {query : List Atom}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    (hpost : QueryReadingsInsensitive post) :
    QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
      (Atom := Atom) query post := by
  intro shadow leftReadings rightReadings _ _
  exact hpost shadow leftReadings rightReadings

end SemanticRepairFiniteQueryPostFiberInvariance
end QualitySurface
end ResearchLean.AG
