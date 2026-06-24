import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryFiberFactor
import Formal.AG.Research.QualitySurface.ReadingAdequacy

/-!
Cycle 30 evidence for `G-aat-quality-surface-04`.

Cycle 28 isolated the exact post-fiber invariance premise needed for finite
query-generated observations to factor through the current canonical shadow.
Cycle 29 made the induced factor explicit.  This file records a semantic-reading
route to that premise: a semantic reading must collapse realized query fibers at
a fixed current shadow, and the post-map must be faithful to that reading.

This remains a support node.  It exposes both semantic-reading obligations as
theorem arguments rather than hiding them in the observation package or claiming
that arbitrary semantic soundness has already been extracted.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQuerySemanticSoundness

open ReadingAdequacy
open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryPostFiberInvariance
open SemanticRepairFiniteQueryFiberFactor

universe u v w x y z

/-! ## Semantic readings on finite obstruction towers -/

/-- A semantic reading relation on finite semantic repair obstruction towers. -/
abbrev TowerSemanticReading
    {Atom : Type u} :=
  Reading
    (FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom)

/--
Two towers have the same generated post value for a fixed finite query and
post-map.
-/
def SameQueryPostValue
    {Atom : Type u}
    (query : List Atom)
    {Out : Type z}
    (post : FiniteTowerLayerShadow -> List Bool -> Out)
    (left right :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) : Prop :=
  post (canonicalTowerLayerShadow left)
      (supportTraceVector query left.sourceTraceToken) =
    post (canonicalTowerLayerShadow right)
      (supportTraceVector query right.sourceTraceToken)

/--
The post-map is sound for a semantic reading when semantically equivalent towers
have the same generated post value.
-/
def SemanticReadingFaithfulToQueryPost
    {Atom : Type u}
    (reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom))
    (query : List Atom)
    {Out : Type z}
    (post : FiniteTowerLayerShadow -> List Bool -> Out) : Prop :=
  FaithfulToInvariant reading
    (SameQueryPostValue.{u, v, w, x, y, z} query post)

/--
The semantic reading collapses every realized query-reading fiber over a fixed
current canonical shadow.

This premise mentions only the reading, current shadow, query, and realized
query vectors; it does not mention the post-map.
-/
def SemanticReadingCollapsesCurrentShadowQueryFibers
    {Atom : Type u}
    (reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom))
    (query : List Atom) : Prop :=
  ∀ {shadow : FiniteTowerLayerShadow}
    {leftReadings rightReadings : List Bool}
    {left right :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom},
    canonicalTowerLayerShadow left = shadow ->
    supportTraceVector query left.sourceTraceToken = leftReadings ->
    canonicalTowerLayerShadow right = shadow ->
    supportTraceVector query right.sourceTraceToken = rightReadings ->
      reading.Equivalent left right

/-! ## Semantic-reading route to post-fiber invariance -/

/--
Semantic-reading fiber collapse plus post faithfulness implies the exact
current-shadow post-fiber invariance condition.
-/
theorem postInvariantOnCurrentShadowFibers_of_semanticReadingAdequacy
    {Atom : Type u}
    {query : List Atom}
    {Out : Type z}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    {reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom)}
    (hcollapse :
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading query)
    (hfaithful :
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
        (Atom := Atom) reading query post) :
    QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
      (Atom := Atom) query post := by
  intro shadow leftReadings rightReadings hleft hright
  rcases hleft with ⟨left, hleftShadow, hleftReadings⟩
  rcases hright with ⟨right, hrightShadow, hrightReadings⟩
  have heq : reading.Equivalent left right :=
    hcollapse hleftShadow hleftReadings hrightShadow hrightReadings
  have hpost : SameQueryPostValue query post left right :=
    hfaithful left right heq
  calc
    post shadow leftReadings =
        post (canonicalTowerLayerShadow left)
          (supportTraceVector query left.sourceTraceToken) := by
      rw [hleftShadow, hleftReadings]
    _ = post (canonicalTowerLayerShadow right)
          (supportTraceVector query right.sourceTraceToken) :=
      hpost
    _ = post shadow rightReadings := by
      rw [hrightShadow, hrightReadings]

/--
Semantic-reading adequacy gives current-shadow extensionality for the generated
finite query observation.
-/
theorem queryTraceGeneratedObservation_shadowExtensional_of_semanticReadingAdequacy
    {Atom : Type u}
    {query : List Atom}
    {Out : Type z}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    {reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom)}
    (hcollapse :
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading query)
    (hfaithful :
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
        (Atom := Atom) reading query post) :
    ShadowExtensionalTowerObservation
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        post (canonicalTowerLayerShadow T)
          (supportTraceVector query T.sourceTraceToken)) := by
  exact
    queryTraceGeneratedObservation_shadowExtensional_of_postInvariantOnCurrentShadowFibers
      (postInvariantOnCurrentShadowFibers_of_semanticReadingAdequacy
        (Atom := Atom) hcollapse hfaithful)

/--
Semantic-reading adequacy identifies the generated observation with the explicit
canonical query-post factor.
-/
theorem queryTraceGeneratedObservation_eq_canonicalQueryPostFiberFactor_of_semanticReadingAdequacy
    {Atom : Type u}
    {query : List Atom}
    {Out : Type z}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    {reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom)}
    (hcollapse :
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading query)
    (hfaithful :
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
        (Atom := Atom) reading query post)
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    post (canonicalTowerLayerShadow T)
        (supportTraceVector query T.sourceTraceToken) =
      canonicalQueryPostFiberFactor
        (Atom := Atom) query post (canonicalTowerLayerShadow T) := by
  exact
    queryTraceGeneratedObservation_eq_canonicalQueryPostFiberFactor_of_postInvariant
      (Atom := Atom)
      (postInvariantOnCurrentShadowFibers_of_semanticReadingAdequacy
        (Atom := Atom) hcollapse hfaithful)
      T

/-! ## Finite query package surface -/

/-- Package-local abbreviation for semantic-reading post faithfulness. -/
abbrev SemanticReadingFaithfulToFiniteTraceQueryObservation
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom))
    (obs : FiniteTraceQueryObservation support Out) : Prop :=
  SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
    (Atom := Atom) reading obs.query obs.post

/-- Package-local abbreviation for semantic-reading query-fiber collapse. -/
abbrev SemanticReadingCollapsesFiniteTraceQueryFibers
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom))
    (obs : FiniteTraceQueryObservation support Out) : Prop :=
  SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
    (Atom := Atom) reading obs.query

/--
Finite query package version: semantic-reading adequacy implies the exact
post-fiber invariance condition for the package post-map.
-/
theorem finiteTraceQueryObservation_postInvariantOnCurrentShadowFibers_of_semanticReadingAdequacy
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (obs : FiniteTraceQueryObservation support Out)
    {reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom)}
    (hcollapse :
      SemanticReadingCollapsesFiniteTraceQueryFibers.{u, v, w, x, y, z}
        (Atom := Atom) reading obs)
    (hfaithful :
      SemanticReadingFaithfulToFiniteTraceQueryObservation.{u, v, w, x, y, z}
        (Atom := Atom) reading obs) :
    QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
      (Atom := Atom) obs.query obs.post := by
  exact
    postInvariantOnCurrentShadowFibers_of_semanticReadingAdequacy
      (Atom := Atom) hcollapse hfaithful

/--
Finite query package version of explicit canonical factorization under
semantic-reading adequacy.
-/
theorem finiteTraceQueryObservation_eq_canonicalQueryPostFiberFactor_of_semanticReadingAdequacy
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (obs : FiniteTraceQueryObservation support Out)
    {reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom)}
    (hcollapse :
      SemanticReadingCollapsesFiniteTraceQueryFibers.{u, v, w, x, y, z}
        (Atom := Atom) reading obs)
    (hfaithful :
      SemanticReadingFaithfulToFiniteTraceQueryObservation.{u, v, w, x, y, z}
        (Atom := Atom) reading obs)
    (T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom) :
    obs.observe T =
      canonicalQueryPostFiberFactor
        (Atom := Atom) obs.query obs.post (canonicalTowerLayerShadow T) := by
  exact
    finiteTraceQueryObservation_eq_canonicalQueryPostFiberFactor_of_postInvariant
      (Atom := Atom) obs
      (finiteTraceQueryObservation_postInvariantOnCurrentShadowFibers_of_semanticReadingAdequacy
        (Atom := Atom) obs hcollapse hfaithful)
      T

/--
Semantic-reading adequacy gives the same explicit factorization and uniqueness
package as post-fiber invariance, with the two semantic obligations visible.
-/
theorem finiteTraceQueryObservation_semanticReadingAdequacy_explicitFiberFactorization
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (obs : FiniteTraceQueryObservation support Out)
    {reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom)}
    (hcollapse :
      SemanticReadingCollapsesFiniteTraceQueryFibers.{u, v, w, x, y, z}
        (Atom := Atom) reading obs)
    (hfaithful :
      SemanticReadingFaithfulToFiniteTraceQueryObservation.{u, v, w, x, y, z}
        (Atom := Atom) reading obs) :
    (∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
      obs.observe T =
        canonicalQueryPostFiberFactor
          (Atom := Atom) obs.query obs.post (canonicalTowerLayerShadow T)) /\
      (∀ factor : FiniteTowerLayerShadow -> Out,
        (∀ shadow readings,
          QueryReadingsRealizableAtCurrentShadow.{u, v, w, x, y}
            (Atom := Atom) obs.query shadow readings ->
            obs.post shadow readings = factor shadow) ->
          ∀ shadow,
            factor shadow =
              canonicalQueryPostFiberFactor
                (Atom := Atom) obs.query obs.post shadow) := by
  have hinvariant :
      QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
        (Atom := Atom) obs.query obs.post :=
    finiteTraceQueryObservation_postInvariantOnCurrentShadowFibers_of_semanticReadingAdequacy
      (Atom := Atom) obs hcollapse hfaithful
  have hpackage :=
    queryTraceGeneratedObservation_explicitFiberFactorization
      (Atom := Atom) obs.post hinvariant
  constructor
  · intro T
    simpa [FiniteTraceQueryObservation.observe] using hpackage.1 T
  · exact hpackage.2

/-! ## Agreement with the universal canonical-shadow factor API -/

/--
The explicit finite-query factor agrees pointwise with the universal
`canonicalShadowFactor` induced by representative towers.
-/
theorem canonicalShadowFactor_eq_canonicalQueryPostFiberFactor_of_postInvariant
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (obs : FiniteTraceQueryObservation support Out)
    (hinvariant :
      QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
        (Atom := Atom) obs.query obs.post) :
    ∀ shadow,
      canonicalShadowFactor
          (fun U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
            obs.observe U)
          shadow =
        canonicalQueryPostFiberFactor
          (Atom := Atom) obs.query obs.post shadow := by
  intro shadow
  have hunique :=
    shadowExtensionalObservation_factor_pointwise_unique
      (observe :=
        fun U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
          obs.observe U)
      (factor :=
        fun shadow =>
          canonicalQueryPostFiberFactor
            (Atom := Atom) obs.query obs.post shadow)
      (finiteTraceQueryObservation_eq_canonicalQueryPostFiberFactor_of_postInvariant
        (Atom := Atom) obs hinvariant)
  exact (hunique shadow).symm

/--
Post-fiber invariance gives both the explicit query factorization and agreement
with the existing universal factor API.
-/
theorem finiteTraceQueryObservation_canonicalFactorAgreement_package_of_postInvariant
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (obs : FiniteTraceQueryObservation support Out)
    (hinvariant :
      QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
        (Atom := Atom) obs.query obs.post) :
    (∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
      obs.observe T =
        canonicalQueryPostFiberFactor
          (Atom := Atom) obs.query obs.post (canonicalTowerLayerShadow T)) /\
      (∀ shadow,
        canonicalShadowFactor
            (fun U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
              obs.observe U)
            shadow =
          canonicalQueryPostFiberFactor
            (Atom := Atom) obs.query obs.post shadow) := by
  exact
    ⟨finiteTraceQueryObservation_eq_canonicalQueryPostFiberFactor_of_postInvariant
      (Atom := Atom) obs hinvariant,
      canonicalShadowFactor_eq_canonicalQueryPostFiberFactor_of_postInvariant
        (Atom := Atom) obs hinvariant⟩

/--
Semantic-reading adequacy also identifies the explicit query factor with the
universal canonical-shadow factor.
-/
theorem canonicalShadowFactor_eq_canonicalQueryPostFiberFactor_of_semanticReadingAdequacy
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (obs : FiniteTraceQueryObservation support Out)
    {reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom)}
    (hcollapse :
      SemanticReadingCollapsesFiniteTraceQueryFibers.{u, v, w, x, y, z}
        (Atom := Atom) reading obs)
    (hfaithful :
      SemanticReadingFaithfulToFiniteTraceQueryObservation.{u, v, w, x, y, z}
        (Atom := Atom) reading obs) :
    ∀ shadow,
      canonicalShadowFactor
          (fun U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
            obs.observe U)
          shadow =
        canonicalQueryPostFiberFactor
          (Atom := Atom) obs.query obs.post shadow := by
  exact
    canonicalShadowFactor_eq_canonicalQueryPostFiberFactor_of_postInvariant
      (Atom := Atom) obs
      (finiteTraceQueryObservation_postInvariantOnCurrentShadowFibers_of_semanticReadingAdequacy
        (Atom := Atom) obs hcollapse hfaithful)

/--
Semantic-reading adequacy supplies the explicit factorization package and its
agreement with the universal representative-induced factor.
-/
theorem finiteTraceQueryObservation_semanticReadingAdequacy_canonicalFactorAgreement_package
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (obs : FiniteTraceQueryObservation support Out)
    {reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom)}
    (hcollapse :
      SemanticReadingCollapsesFiniteTraceQueryFibers.{u, v, w, x, y, z}
        (Atom := Atom) reading obs)
    (hfaithful :
      SemanticReadingFaithfulToFiniteTraceQueryObservation.{u, v, w, x, y, z}
        (Atom := Atom) reading obs) :
    (∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
      obs.observe T =
        canonicalQueryPostFiberFactor
          (Atom := Atom) obs.query obs.post (canonicalTowerLayerShadow T)) /\
      (∀ shadow,
        canonicalShadowFactor
            (fun U : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
              obs.observe U)
            shadow =
          canonicalQueryPostFiberFactor
            (Atom := Atom) obs.query obs.post shadow) := by
  exact
    ⟨finiteTraceQueryObservation_eq_canonicalQueryPostFiberFactor_of_semanticReadingAdequacy
      (Atom := Atom) obs hcollapse hfaithful,
      canonicalShadowFactor_eq_canonicalQueryPostFiberFactor_of_semanticReadingAdequacy
        (Atom := Atom) obs hcollapse hfaithful⟩

end SemanticRepairFiniteQuerySemanticSoundness
end QualitySurface
end Formal.AG.Research
