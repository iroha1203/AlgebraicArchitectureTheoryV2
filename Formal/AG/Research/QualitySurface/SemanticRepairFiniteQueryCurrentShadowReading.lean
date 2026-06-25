import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryNoSeparation

/-!
Cycle 33 evidence for `G-aat-quality-surface-04`.

Cycle 30 exposed two semantic-reading obligations: collapse of current-shadow
query fibers and faithfulness to the query post-map.  Cycle 31-32 showed that
post-fiber separation obstructs those obligations.  This file supplies the
canonical current-shadow reading: it identifies towers exactly when their
current canonical shadows agree.

For that reading, query-fiber collapse is automatic.  The remaining faithfulness
condition is not hidden in the reading; it is proved equivalent to the existing
post-fiber invariance criterion, and hence to absence of post-fiber separation.
This is a support node, not target completion.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQueryCurrentShadowReading

open ReadingAdequacy
open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTargetCompletion
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryPostFiberInvariance
open SemanticRepairFiniteQueryFiberFactor
open SemanticRepairFiniteQuerySemanticSoundness
open SemanticRepairFiniteQueryPostFiberObstruction
open SemanticRepairFiniteQueryNoSeparation

universe u v w x y z

/-! ## The canonical current-shadow semantic reading -/

/--
The semantic reading that remembers exactly the current canonical shadow.

It intentionally does not mention a query or post-map.  Thus query-fiber
collapse is discharged by the reading itself, while post-map faithfulness
remains a separate theorem-level condition.
-/
def currentShadowSemanticReading
    {Atom : Type u} :
    TowerSemanticReading.{u, v, w, x, y} (Atom := Atom) where
  Equivalent left right :=
    canonicalTowerLayerShadow left = canonicalTowerLayerShadow right

/--
The current-shadow reading collapses every realized query-reading fiber over a
fixed current shadow.
-/
theorem currentShadowSemanticReading_collapsesCurrentShadowQueryFibers
    {Atom : Type u}
    (query : List Atom) :
    SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
      (Atom := Atom)
      (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
      query := by
  intro shadow _leftReadings _rightReadings left right
    hleftShadow _hleftReadings hrightShadow _hrightReadings
  change canonicalTowerLayerShadow left = canonicalTowerLayerShadow right
  rw [hleftShadow, hrightShadow]

/-! ## Faithfulness is exactly post-fiber invariance -/

/--
For the current-shadow reading, post faithfulness is exactly current-shadow
extensionality of the generated finite query observation.
-/
theorem currentShadowSemanticReading_faithfulToQueryPost_iff_generatedShadowExtensional
    {Atom : Type u}
    (query : List Atom)
    {Out : Type z}
    (post : FiniteTowerLayerShadow -> List Bool -> Out) :
    SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
      (Atom := Atom)
      (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
      query post ↔
    ShadowExtensionalTowerObservation
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        post (canonicalTowerLayerShadow T)
          (supportTraceVector query T.sourceTraceToken)) := by
  constructor
  · intro hfaithful left right hshadow
    exact hfaithful left right hshadow
  · intro hext left right hshadow
    exact hext left right hshadow

/--
For the current-shadow reading, post faithfulness is exactly the existing
post-fiber invariance criterion.
-/
theorem currentShadowSemanticReading_faithfulToQueryPost_iff_postInvariantOnCurrentShadowFibers
    {Atom : Type u}
    (query : List Atom)
    {Out : Type z}
    (post : FiniteTowerLayerShadow -> List Bool -> Out) :
    SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
      (Atom := Atom)
      (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
      query post ↔
    QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
      (Atom := Atom) query post := by
  exact
    (currentShadowSemanticReading_faithfulToQueryPost_iff_generatedShadowExtensional
      (Atom := Atom) query post).trans
      (queryTraceGeneratedObservation_shadowExtensional_iff_postInvariantOnCurrentShadowFibers
        (Atom := Atom) query post)

/--
Post-fiber invariance supplies a concrete semantic-reading adequacy package:
the canonical current-shadow reading discharges collapse, and faithfulness is
obtained from the same visible invariance premise.
-/
theorem currentShadowSemanticReading_semanticAdequacy_of_postInvariant
    {Atom : Type u}
    {query : List Atom}
    {Out : Type z}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    (hinvariant :
      QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
        (Atom := Atom) query post) :
    SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom)
        (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
        query ∧
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
        (Atom := Atom)
        (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
        query post := by
  exact
    ⟨currentShadowSemanticReading_collapsesCurrentShadowQueryFibers
      (Atom := Atom) query,
      (currentShadowSemanticReading_faithfulToQueryPost_iff_postInvariantOnCurrentShadowFibers
        (Atom := Atom) query post).2 hinvariant⟩

/--
Existence of a semantic-reading adequacy package for a finite query post-map is
equivalent to the exact post-fiber invariance condition.
-/
theorem exists_semanticReadingAdequacy_iff_postInvariantOnCurrentShadowFibers
    {Atom : Type u}
    (query : List Atom)
    {Out : Type z}
    (post : FiniteTowerLayerShadow -> List Bool -> Out) :
    (∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading query ∧
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
        (Atom := Atom) reading query post) ↔
    QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
      (Atom := Atom) query post := by
  constructor
  · intro hadequacy
    rcases hadequacy with ⟨reading, hcollapse, hfaithful⟩
    exact
      postInvariantOnCurrentShadowFibers_of_semanticReadingAdequacy
        (Atom := Atom) (reading := reading) hcollapse hfaithful
  · intro hinvariant
    exact
      ⟨currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom),
        (currentShadowSemanticReading_semanticAdequacy_of_postInvariant
          (Atom := Atom) hinvariant).1,
        (currentShadowSemanticReading_semanticAdequacy_of_postInvariant
          (Atom := Atom) hinvariant).2⟩

/-! ## No-separation exactness -/

/--
Absence of post-fiber separation is equivalent to the exact post-fiber
invariance criterion.
-/
theorem not_queryPostFiberSeparation_iff_postInvariantOnCurrentShadowFibers
    {Atom : Type u}
    (query : List Atom)
    {Out : Type z}
    [DecidableEq Out]
    (post : FiniteTowerLayerShadow -> List Bool -> Out) :
    ¬ QueryPostFiberSeparation.{u, v, w, x, y, z}
      (Atom := Atom) query post ↔
    QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
      (Atom := Atom) query post := by
  constructor
  · intro hnoSeparation shadow leftReadings rightReadings hleft hright
    by_cases hsame : post shadow leftReadings = post shadow rightReadings
    · exact hsame
    · exact False.elim
        (hnoSeparation
          ⟨shadow, leftReadings, rightReadings, hleft, hright, hsame⟩)
  · intro hinvariant hsep
    exact
      not_postInvariantOnCurrentShadowFibers_of_queryPostFiberSeparation hsep
        hinvariant

/--
Semantic-reading adequacy exists exactly when no post-fiber separation exists.
-/
theorem exists_semanticReadingAdequacy_iff_no_queryPostFiberSeparation
    {Atom : Type u}
    (query : List Atom)
    {Out : Type z}
    [DecidableEq Out]
    (post : FiniteTowerLayerShadow -> List Bool -> Out) :
    (∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading query ∧
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
        (Atom := Atom) reading query post) ↔
    ¬ QueryPostFiberSeparation.{u, v, w, x, y, z}
      (Atom := Atom) query post := by
  exact
    (exists_semanticReadingAdequacy_iff_postInvariantOnCurrentShadowFibers
      (Atom := Atom) query post).trans
      (not_queryPostFiberSeparation_iff_postInvariantOnCurrentShadowFibers
        (Atom := Atom) query post).symm

/--
A separated post-fiber rules out faithfulness for the current-shadow reading.
-/
theorem not_currentShadowSemanticReading_faithfulToQueryPost_of_queryPostFiberSeparation
    {Atom : Type u}
    {query : List Atom}
    {Out : Type z}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    (hsep :
      QueryPostFiberSeparation.{u, v, w, x, y, z}
        (Atom := Atom) query post) :
    ¬ SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
      (Atom := Atom)
      (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
      query post := by
  intro hfaithful
  exact
    not_postInvariantOnCurrentShadowFibers_of_queryPostFiberSeparation hsep
      ((currentShadowSemanticReading_faithfulToQueryPost_iff_postInvariantOnCurrentShadowFibers
        (Atom := Atom) query post).1 hfaithful)

/--
Faithfulness of the current-shadow reading rules out separated post-fibers.
-/
theorem no_queryPostFiberSeparation_of_currentShadowSemanticReading_faithfulToQueryPost
    {Atom : Type u}
    {query : List Atom}
    {Out : Type z}
    {post : FiniteTowerLayerShadow -> List Bool -> Out}
    (hfaithful :
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
        (Atom := Atom)
        (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
        query post) :
    ¬ QueryPostFiberSeparation.{u, v, w, x, y, z}
      (Atom := Atom) query post := by
  intro hsep
  exact
    not_currentShadowSemanticReading_faithfulToQueryPost_of_queryPostFiberSeparation
      (Atom := Atom) hsep hfaithful

/-! ## Factorization exactness -/

/--
Raw current-shadow factorization of a finite query-generated observation is
equivalent to the exact post-fiber invariance criterion.
-/
theorem queryTraceGeneratedObservation_currentShadowFactor_iff_postInvariantOnCurrentShadowFibers
    {Atom : Type u}
    (query : List Atom)
    {Out : Type z}
    (post : FiniteTowerLayerShadow -> List Bool -> Out) :
    (∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        post (canonicalTowerLayerShadow T)
            (supportTraceVector query T.sourceTraceToken) =
          factor (canonicalTowerLayerShadow T)) ↔
    QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
      (Atom := Atom) query post := by
  constructor
  · intro hfactor
    rcases hfactor with ⟨factor, hfactor⟩
    intro shadow leftReadings rightReadings hleft hright
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
    exact hleftFactor.trans hrightFactor.symm
  · intro hinvariant
    exact
      ⟨canonicalQueryPostFiberFactor.{u, v, w, x, y, z}
          (Atom := Atom) query post,
        queryTraceGeneratedObservation_eq_canonicalQueryPostFiberFactor_of_postInvariant
          (Atom := Atom) hinvariant⟩

/--
Raw current-shadow factorization of a finite query-generated observation is
equivalent to existence of a semantic-reading adequacy package.
-/
theorem queryTraceGeneratedObservation_currentShadowFactor_iff_exists_semanticReadingAdequacy
    {Atom : Type u}
    (query : List Atom)
    {Out : Type z}
    (post : FiniteTowerLayerShadow -> List Bool -> Out) :
    (∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        post (canonicalTowerLayerShadow T)
            (supportTraceVector query T.sourceTraceToken) =
          factor (canonicalTowerLayerShadow T)) ↔
    (∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesCurrentShadowQueryFibers.{u, v, w, x, y}
        (Atom := Atom) reading query ∧
      SemanticReadingFaithfulToQueryPost.{u, v, w, x, y, z}
        (Atom := Atom) reading query post) := by
  exact
    (queryTraceGeneratedObservation_currentShadowFactor_iff_postInvariantOnCurrentShadowFibers
      (Atom := Atom) query post).trans
      (exists_semanticReadingAdequacy_iff_postInvariantOnCurrentShadowFibers
        (Atom := Atom) query post).symm

/-! ## Finite query package surface -/

theorem finiteTraceQueryObservation_currentShadowSemanticReading_faithful_iff_postInvariant
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (obs : FiniteTraceQueryObservation support Out) :
    SemanticReadingFaithfulToFiniteTraceQueryObservation.{u, v, w, x, y, z}
      (Atom := Atom)
      (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
      obs ↔
    QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
      (Atom := Atom) obs.query obs.post := by
  exact
    currentShadowSemanticReading_faithfulToQueryPost_iff_postInvariantOnCurrentShadowFibers
      (Atom := Atom) obs.query obs.post

theorem finiteTraceQueryObservation_currentShadowSemanticAdequacy_of_postInvariant
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (obs : FiniteTraceQueryObservation support Out)
    (hinvariant :
      QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
        (Atom := Atom) obs.query obs.post) :
    SemanticReadingCollapsesFiniteTraceQueryFibers.{u, v, w, x, y, z}
        (Atom := Atom)
        (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
        obs ∧
      SemanticReadingFaithfulToFiniteTraceQueryObservation.{u, v, w, x, y, z}
        (Atom := Atom)
        (currentShadowSemanticReading.{u, v, w, x, y} (Atom := Atom))
        obs := by
  exact
    currentShadowSemanticReading_semanticAdequacy_of_postInvariant
      (Atom := Atom) hinvariant

theorem finiteTraceQueryObservation_exists_semanticReadingAdequacy_iff_postInvariant
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (obs : FiniteTraceQueryObservation support Out) :
    (∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesFiniteTraceQueryFibers.{u, v, w, x, y, z}
        (Atom := Atom) reading obs ∧
      SemanticReadingFaithfulToFiniteTraceQueryObservation.{u, v, w, x, y, z}
        (Atom := Atom) reading obs) ↔
    QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
      (Atom := Atom) obs.query obs.post := by
  exact
    exists_semanticReadingAdequacy_iff_postInvariantOnCurrentShadowFibers
      (Atom := Atom) obs.query obs.post

theorem finiteTraceQueryObservation_exists_semanticReadingAdequacy_iff_no_separation
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    [DecidableEq Out]
    (obs : FiniteTraceQueryObservation support Out) :
    (∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesFiniteTraceQueryFibers.{u, v, w, x, y, z}
        (Atom := Atom) reading obs ∧
      SemanticReadingFaithfulToFiniteTraceQueryObservation.{u, v, w, x, y, z}
        (Atom := Atom) reading obs) ↔
    ¬ QueryPostFiberSeparation.{u, v, w, x, y, z}
      (Atom := Atom) obs.query obs.post := by
  exact
    exists_semanticReadingAdequacy_iff_no_queryPostFiberSeparation
      (Atom := Atom) obs.query obs.post

theorem finiteTraceQueryObservation_currentShadowFactor_iff_postInvariant
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (obs : FiniteTraceQueryObservation support Out) :
    (∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        obs.observe T = factor (canonicalTowerLayerShadow T)) ↔
    QueryPostInvariantOnCurrentShadowFibers.{u, v, w, x, y}
      (Atom := Atom) obs.query obs.post := by
  exact
    queryTraceGeneratedObservation_currentShadowFactor_iff_postInvariantOnCurrentShadowFibers
      (Atom := Atom) obs.query obs.post

theorem finiteTraceQueryObservation_currentShadowFactor_iff_exists_semanticReadingAdequacy
    {Atom : Type u}
    {support : List Atom}
    {Out : Type z}
    (obs : FiniteTraceQueryObservation support Out) :
    (∃ factor : FiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        obs.observe T = factor (canonicalTowerLayerShadow T)) ↔
    (∃ reading : TowerSemanticReading.{u, v, w, x, y} (Atom := Atom),
      SemanticReadingCollapsesFiniteTraceQueryFibers.{u, v, w, x, y, z}
        (Atom := Atom) reading obs ∧
      SemanticReadingFaithfulToFiniteTraceQueryObservation.{u, v, w, x, y, z}
        (Atom := Atom) reading obs) := by
  exact
    queryTraceGeneratedObservation_currentShadowFactor_iff_exists_semanticReadingAdequacy
      (Atom := Atom) obs.query obs.post

/-! ## Concrete obstruction compatibility -/

/--
The Bool first-reading post-map is not faithful to the current-shadow semantic
reading.
-/
theorem not_boolFirstQueryReadingPost_currentShadowSemanticReadingFaithful :
    ¬ SemanticReadingFaithfulToQueryPost.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      (currentShadowSemanticReading.{0, 0, 0, 0, 0} (Atom := Bool))
      SemanticRepairFiniteQueryAdmissibility.boolTrueTraceQuery
      SemanticRepairFiniteQueryCurrentShadowCoordinates.boolFirstQueryReadingPost := by
  intro hfaithful
  exact
    SemanticRepairFiniteQueryPostFiberObstruction.not_boolFirstQueryReadingPostInvariantOnCurrentShadowFibers
      ((currentShadowSemanticReading_faithfulToQueryPost_iff_postInvariantOnCurrentShadowFibers
        (Atom := Bool)
        SemanticRepairFiniteQueryAdmissibility.boolTrueTraceQuery
        SemanticRepairFiniteQueryCurrentShadowCoordinates.boolFirstQueryReadingPost).1
        hfaithful)

end SemanticRepairFiniteQueryCurrentShadowReading
end QualitySurface
end Formal.AG.Research
