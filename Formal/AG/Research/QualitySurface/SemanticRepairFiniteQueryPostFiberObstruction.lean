import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryPostFiberInvariance
import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryCurrentShadowCoordinates

/-!
Cycle 31 evidence for `G-aat-quality-surface-04`.

Cycles 28-30 isolate the exact premise needed for finite query-generated
observations to factor through the current canonical shadow.  This file records
the corresponding obstruction: if a post-map separates two realized query-reading
vectors over the same current shadow, then no current-shadow factorization is
possible.

This remains a support / obstruction node.  It does not refute the target
theorem; it fixes a necessary condition that any semantic-soundness extraction
must discharge or explicitly rule out.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQueryPostFiberObstruction

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryAdmissibility
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryCurrentShadowCoordinates
open SemanticRepairFiniteQueryPostFiberInvariance
open SemanticRepairFiniteSupportSeparation

universe u v w x y z

/-! ## Generic post-fiber separation obstruction -/

/--
A post-map separates a current-shadow query fiber when two query-reading vectors
are both realized over the same current shadow but the post-map gives different
values.
-/
def QueryPostFiberSeparation
    {Atom : Type u}
    (query : List Atom)
    {Out : Type z}
    (post : FiniteTowerLayerShadow -> List Bool -> Out) : Prop :=
  ∃ shadow : FiniteTowerLayerShadow,
    ∃ leftReadings rightReadings : List Bool,
      QueryReadingsRealizableAtCurrentShadow.{u, v, w, x, y}
        (Atom := Atom) query shadow leftReadings ∧
      QueryReadingsRealizableAtCurrentShadow.{u, v, w, x, y}
        (Atom := Atom) query shadow rightReadings ∧
      post shadow leftReadings ≠ post shadow rightReadings

/--
Any separated current-shadow query fiber blocks post-fiber invariance.
-/
theorem not_postInvariantOnCurrentShadowFibers_of_queryPostFiberSeparation
    {Atom : Type u}
    {query : List Atom}
    {Out : Type z}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    (hsep :
      QueryPostFiberSeparation.{u, v, w, x, y, z}
        (Atom := Atom) query post) :
    ¬ QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
      (Atom := Atom) query post := by
  intro hinvariant
  rcases hsep with
    ⟨shadow, leftReadings, rightReadings, hleft, hright, hne⟩
  exact hne (hinvariant shadow leftReadings rightReadings hleft hright)

/--
Any separated current-shadow query fiber blocks current-shadow extensionality of
the generated finite query observation.
-/
theorem not_queryTraceGeneratedObservation_shadowExtensional_of_queryPostFiberSeparation
    {Atom : Type u}
    {query : List Atom}
    {Out : Type z}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    (hsep :
      QueryPostFiberSeparation.{u, v, w, x, y, z}
        (Atom := Atom) query post) :
    ¬ ShadowExtensionalTowerObservation
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        post (canonicalTowerLayerShadow T)
          (supportTraceVector query T.sourceTraceToken)) := by
  intro hext
  exact
    not_postInvariantOnCurrentShadowFibers_of_queryPostFiberSeparation hsep
      (postInvariantOnCurrentShadowFibers_of_queryTraceGeneratedObservation_shadowExtensional
        hext)

/--
Any separated current-shadow query fiber blocks factorization through the current
canonical shadow.
-/
theorem no_queryTraceGeneratedObservation_currentShadowFactor_of_queryPostFiberSeparation
    {Atom : Type u}
    {query : List Atom}
    {Out : Type z}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    (hsep :
      QueryPostFiberSeparation.{u, v, w, x, y, z}
        (Atom := Atom) query post) :
    ¬ ∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        post (canonicalTowerLayerShadow T)
            (supportTraceVector query T.sourceTraceToken) =
          factor (canonicalTowerLayerShadow T) := by
  intro hfactor
  rcases hfactor with ⟨factor, hfactor⟩
  rcases hsep with
    ⟨shadow, leftReadings, rightReadings, hleft, hright, hne⟩
  rcases hleft with ⟨left, hleftShadow, hleftReadings⟩
  rcases hright with ⟨right, hrightShadow, hrightReadings⟩
  have hleftFactor :
      post shadow leftReadings = factor shadow := by
    calc
      post shadow leftReadings =
          post (canonicalTowerLayerShadow left)
            (supportTraceVector query left.sourceTraceToken) := by
        rw [hleftShadow, hleftReadings]
      _ = factor (canonicalTowerLayerShadow left) := hfactor left
      _ = factor shadow := by rw [hleftShadow]
  have hrightFactor :
      post shadow rightReadings = factor shadow := by
    calc
      post shadow rightReadings =
          post (canonicalTowerLayerShadow right)
            (supportTraceVector query right.sourceTraceToken) := by
        rw [hrightShadow, hrightReadings]
      _ = factor (canonicalTowerLayerShadow right) := hfactor right
      _ = factor shadow := by rw [hrightShadow]
  exact hne (hleftFactor.trans hrightFactor.symm)

/-! ## Concrete Bool `[true]` query obstruction -/

/--
The Bool `[true]` query with the first-reading post-map separates a realized
current-shadow fiber.
-/
theorem boolFirstQueryReadingPost_currentShadowFiber_separates :
    QueryPostFiberSeparation.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      boolTrueTraceQuery
      boolFirstQueryReadingPost := by
  refine
    ⟨canonicalTowerLayerShadow boolTraceBaseTower,
      [false], [true], ?_, ?_, ?_⟩
  · exact ⟨boolTraceBaseTower, rfl, rfl⟩
  · exact
      ⟨boolTraceMissedTrueTower,
        bool_missedTrue_same_currentShadow.symm,
        rfl⟩
  · decide

/--
The concrete Bool first-reading post-map does not satisfy the exact post-fiber
invariance criterion.
-/
theorem not_boolFirstQueryReadingPostInvariantOnCurrentShadowFibers :
    ¬ QueryPostInvariantOnCurrentShadowFibers.{0, 0, 0, 0, 0}
      (Atom := Bool)
      boolTrueTraceQuery
      boolFirstQueryReadingPost := by
  exact
    not_postInvariantOnCurrentShadowFibers_of_queryPostFiberSeparation
      boolFirstQueryReadingPost_currentShadowFiber_separates

/--
The concrete Bool first-reading generated observation is not current-shadow
extensional, as an immediate consequence of post-fiber separation.
-/
theorem not_boolFirstQueryGeneratedObservation_shadowExtensional_of_postFiberSeparation :
    ¬ ShadowExtensionalTowerObservation
      (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
        boolFirstQueryReadingPost
          (canonicalTowerLayerShadow T)
          (supportTraceVector boolTrueTraceQuery T.sourceTraceToken)) := by
  exact
    not_queryTraceGeneratedObservation_shadowExtensional_of_queryPostFiberSeparation
      boolFirstQueryReadingPost_currentShadowFiber_separates

/--
The concrete Bool first-reading generated observation has no current-shadow
factor.
-/
theorem boolFirstQueryReadingPost_no_currentShadowFactor :
    ¬ ∃ factor : FiniteTowerLayerShadow -> Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
        boolFirstQueryReadingPost
            (canonicalTowerLayerShadow T)
            (supportTraceVector boolTrueTraceQuery T.sourceTraceToken) =
          factor (canonicalTowerLayerShadow T) := by
  exact
    no_queryTraceGeneratedObservation_currentShadowFactor_of_queryPostFiberSeparation
      boolFirstQueryReadingPost_currentShadowFiber_separates

end SemanticRepairFiniteQueryPostFiberObstruction
end QualitySurface
end Formal.AG.Research
