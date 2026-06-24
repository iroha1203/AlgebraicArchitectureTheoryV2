import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryCurrentShadowCoordinates

/-!
Cycle 27 evidence for `G-aat-quality-surface-04`.

Cycle 26 gives a sufficient current-shadow factorization condition for finite
query-generated observations: every queried source-trace coordinate is
current-shadow extensional.  This file records the complementary boundary:
that coordinate condition is not necessary at the observation level.  If the
post-map ignores query readings, a finite query-generated observation factors
through the current canonical shadow even when the query itself contains a
trace-sensitive coordinate.

The result is an anti-weakening support node.  It prevents the query-vector
iff from being over-read as an observation-level iff.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQueryReadingInsensitive

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteSupportSeparation
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryCurrentShadowCoordinates

universe u v w x y z

/-! ## Reading-insensitive post-maps -/

/--
A post-map is insensitive to finite query readings when, at a fixed current
shadow, all reading vectors give the same output.
-/
def QueryReadingsInsensitive
    {Out : Type z}
    (post : FiniteTowerLayerShadow -> List Bool -> Out) : Prop :=
  ∀ shadow : FiniteTowerLayerShadow,
    ∀ leftReadings rightReadings : List Bool,
      post shadow leftReadings = post shadow rightReadings

/--
If the post-map ignores query readings, the generated observation is
current-shadow extensional for any query.
-/
theorem queryTraceGeneratedObservation_shadowExtensional_of_queryReadingsInsensitive
    {Atom : Type u}
    {Out : Type z}
    {query : List Atom}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    (hpost : QueryReadingsInsensitive post) :
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
  calc
    post (canonicalTowerLayerShadow left)
        (supportTraceVector query left.sourceTraceToken) =
        post (canonicalTowerLayerShadow left) [] :=
      hpost (canonicalTowerLayerShadow left)
        (supportTraceVector query left.sourceTraceToken) []
    _ = post (canonicalTowerLayerShadow right) [] := by
      rw [hshadow]
    _ = post (canonicalTowerLayerShadow right)
        (supportTraceVector query right.sourceTraceToken) :=
      hpost (canonicalTowerLayerShadow right) []
        (supportTraceVector query right.sourceTraceToken)

/--
A finite query-generated observation is current-shadow extensional when its
post-map ignores query readings.  No coordinate extensionality premise is used.
-/
theorem finiteTraceQueryObservation_shadowExtensional_of_queryReadingsInsensitive
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (obs : FiniteTraceQueryObservation support Out)
    (hpost : QueryReadingsInsensitive obs.post) :
    ShadowExtensionalTowerObservation
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        obs.observe T) := by
  exact
    queryTraceGeneratedObservation_shadowExtensional_of_queryReadingsInsensitive
      (query := obs.query) hpost

/--
Reading-insensitive finite query observations factor through the current
canonical shadow without support-shadow determinacy or query-coordinate
extensionality.
-/
theorem finiteTraceQueryObservation_eq_canonicalShadowFactor_of_queryReadingsInsensitive
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (obs : FiniteTraceQueryObservation support Out)
    (hpost : QueryReadingsInsensitive obs.post)
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    obs.observe T =
      canonicalShadowFactor
        (fun U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
          obs.observe U)
        (canonicalTowerLayerShadow T) := by
  exact
    shadowExtensionalObservation_factors
      (finiteTraceQueryObservation_shadowExtensional_of_queryReadingsInsensitive
        obs hpost)
      T

/-! ## Shadow-only post-maps -/

/-- A post-map generated only from the current shadow. -/
def shadowOnlyPost
    {Out : Type z}
    (read : FiniteTowerLayerShadow -> Out) :
    FiniteTowerLayerShadow -> List Bool -> Out :=
  fun shadow _ => read shadow

/-- Shadow-only post-maps are reading-insensitive. -/
theorem shadowOnlyPost_queryReadingsInsensitive
    {Out : Type z}
    (read : FiniteTowerLayerShadow -> Out) :
    QueryReadingsInsensitive (shadowOnlyPost read) := by
  intro shadow leftReadings rightReadings
  rfl

/-- Shadow-only finite query-generated observations are current-shadow extensional. -/
theorem queryTraceGeneratedObservation_shadowExtensional_of_shadowOnlyPost
    {Atom : Type u}
    {Out : Type z}
    {query : List Atom}
    (read : FiniteTowerLayerShadow -> Out) :
    ShadowExtensionalTowerObservation
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        shadowOnlyPost read (canonicalTowerLayerShadow T)
          (supportTraceVector query T.sourceTraceToken)) := by
  exact
    queryTraceGeneratedObservation_shadowExtensional_of_queryReadingsInsensitive
      (query := query)
      (shadowOnlyPost_queryReadingsInsensitive read)

/-! ## Concrete non-necessity witness -/

/-- Bool post-map that reads only the `h1` component of the current shadow. -/
def boolH1ShadowOnlyPost :
    FiniteTowerLayerShadow -> List Bool -> Bool :=
  shadowOnlyPost (fun shadow => shadow.h1)

/-- The Bool `h1` shadow-only post-map is reading-insensitive. -/
theorem boolH1ShadowOnlyPost_queryReadingsInsensitive :
    QueryReadingsInsensitive boolH1ShadowOnlyPost :=
  shadowOnlyPost_queryReadingsInsensitive (fun shadow => shadow.h1)

/--
The Bool `[true]` query with a shadow-only post-map is current-shadow
extensional even though the query coordinate itself is not.
-/
theorem boolTrueShadowOnlyFiniteTraceQueryObservation_shadowExtensional :
    ShadowExtensionalTowerObservation
      (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
        (boolTrueFiniteTraceQueryObservation boolH1ShadowOnlyPost).observe T) := by
  exact
    finiteTraceQueryObservation_shadowExtensional_of_queryReadingsInsensitive
      (boolTrueFiniteTraceQueryObservation boolH1ShadowOnlyPost)
      boolH1ShadowOnlyPost_queryReadingsInsensitive

/--
Query-coordinate extensionality is not necessary for observation-level
current-shadow extensionality.

The Bool `[true]` query has a non-current-shadow-extensional coordinate, but a
post-map that ignores query readings yields a current-shadow-extensional
observation.
-/
theorem boolTrueQueryCoordinateObligation_not_necessary_for_observationExtensional :
    (¬ QueryTraceCoordinatesCurrentShadowExtensional.{0, 0, 0, 0, 0}
      SemanticRepairFiniteQueryAdmissibility.boolTrueTraceQuery) /\
    ShadowExtensionalTowerObservation
      (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
        (boolTrueFiniteTraceQueryObservation boolH1ShadowOnlyPost).observe T) := by
  exact
    ⟨not_boolTrueTraceQueryCoordinatesCurrentShadowExtensional,
      boolTrueShadowOnlyFiniteTraceQueryObservation_shadowExtensional⟩

end SemanticRepairFiniteQueryReadingInsensitive
end QualitySurface
end Formal.AG.Research
