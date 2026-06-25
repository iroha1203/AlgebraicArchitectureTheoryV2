import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQuerySemanticSoundness
import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryPostFiberObstruction

/-!
Cycle 32 evidence for `G-aat-quality-surface-04`.

Cycle 30 gives a semantic-reading route to post-fiber invariance.  Cycle 31
shows that post-fiber separation obstructs current-shadow factorization.  This
file connects the two: semantic-reading collapse plus query-post faithfulness
rules out post-fiber separation.

This remains a support node.  It does not discharge the semantic-reading
obligations; it records the exact no-separation consequence once those
obligations are supplied.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQueryNoSeparation

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryPostFiberInvariance
open SemanticRepairFiniteQueryFiberFactor
open SemanticRepairFiniteQuerySemanticSoundness
open SemanticRepairFiniteQueryPostFiberObstruction

universe u v w x y z

/-! ## No-separation consequences of semantic-reading adequacy -/

/--
Semantic-reading collapse plus query-post faithfulness rules out post-fiber
separation.
-/
theorem not_queryPostFiberSeparation_of_semanticReadingAdequacy
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
    ¬ QueryPostFiberSeparation.{u, v, w, x, y, z}
      (Atom := Atom) query post := by
  intro hsep
  exact
    not_postInvariantOnCurrentShadowFibers_of_queryPostFiberSeparation hsep
      (postInvariantOnCurrentShadowFibers_of_semanticReadingAdequacy
        (Atom := Atom) hcollapse hfaithful)

/--
Contrapositive form: a separated query fiber rules out any supplied semantic
reading adequacy package for that query and post-map.
-/
theorem no_semanticReadingAdequacy_of_queryPostFiberSeparation
    {Atom : Type u}
    {query : List Atom}
    {Out : Type z}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    (hsep :
      QueryPostFiberSeparation.{u, v, w, x, y, z}
        (Atom := Atom) query post) :
    ¬ ∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading query ∧
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
        (Atom := Atom) reading query post := by
  intro hadequacy
  rcases hadequacy with ⟨reading, hcollapse, hfaithful⟩
  exact
    not_queryPostFiberSeparation_of_semanticReadingAdequacy
      (Atom := Atom)
      (reading := reading)
      hcollapse hfaithful hsep

/-! ## Finite query package surface -/

/--
Finite query package version of the no-separation consequence.
-/
theorem finiteTraceQueryObservation_no_queryPostFiberSeparation_of_semanticReadingAdequacy
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
    ¬ QueryPostFiberSeparation.{u, v, w, x, y, z}
      (Atom := Atom) obs.query obs.post := by
  exact
    not_queryPostFiberSeparation_of_semanticReadingAdequacy
      (Atom := Atom) hcollapse hfaithful

/--
Finite query package contrapositive: a separated query fiber rules out semantic
reading adequacy for that package.
-/
theorem finiteTraceQueryObservation_no_semanticReadingAdequacy_of_queryPostFiberSeparation
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (obs : FiniteTraceQueryObservation support Out)
    (hsep :
      QueryPostFiberSeparation.{u, v, w, x, y, z}
        (Atom := Atom) obs.query obs.post) :
    ¬ ∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesFiniteTraceQueryFibers.{u, v, w, x, y, z}
        (Atom := Atom) reading obs ∧
      SemanticReadingFaithfulToFiniteTraceQueryObservation.{u, v, w, x, y, z}
        (Atom := Atom) reading obs := by
  exact
    no_semanticReadingAdequacy_of_queryPostFiberSeparation
      (Atom := Atom) hsep

/--
The concrete Bool first-reading obstruction rules out any semantic-reading
adequacy package for that query and post-map.
-/
theorem no_boolFirstQueryReadingPost_semanticReadingAdequacy :
    ¬ ∃ reading : TowerSemanticReading.{0, 0, 0, 0, 0} (Atom := Bool),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{0, 0, 0, 0, 0}
        (Atom := Bool) reading
        SemanticRepairFiniteQueryAdmissibility.boolTrueTraceQuery ∧
      SemanticReadingFaithfulToQueryPost.{0, 0, 0, 0, 0, 0}
        (Atom := Bool) reading
        SemanticRepairFiniteQueryAdmissibility.boolTrueTraceQuery
        SemanticRepairFiniteQueryCurrentShadowCoordinates.boolFirstQueryReadingPost := by
  exact
    no_semanticReadingAdequacy_of_queryPostFiberSeparation
      SemanticRepairFiniteQueryPostFiberObstruction.boolFirstQueryReadingPost_currentShadowFiber_separates

end SemanticRepairFiniteQueryNoSeparation
end QualitySurface
end Formal.AG.Research
