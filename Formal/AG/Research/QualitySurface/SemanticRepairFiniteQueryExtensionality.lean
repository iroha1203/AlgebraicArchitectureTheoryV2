import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryAdmissibility

/-!
Cycle 21 evidence for `G-aat-quality-surface-04`.

This file packages Cycle 20 finite query factorization as support-shadow
extensionality.  It is an extensionality bridge for query-generated
observations, not an unrestricted semantic-observation theorem.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQueryExtensionality

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteQueryAdmissibility

universe u v w x y z

/-! ## Supported query extensionality -/

/--
The finite trace vector of a supported query is extensional for the
finite-support trace shadow.
-/
theorem queryTraceVector_supportTraceShadowExtensional
    {Atom : Type u}
    {support query : List Atom}
    (hquery : QuerySupportedBy support query) :
    SupportTraceShadowExtensional
      (Atom := Atom)
      support
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        supportTraceVector query T.sourceTraceToken) := by
  rcases
    queryTraceVector_factors_through_supportTraceShadow
      (support := support) query hquery with
    ⟨factor, hfactor⟩
  exact supportTraceShadowExtensional_of_factorization factor hfactor

/--
An observation generated from the current four-bit layer and a supported query
vector is extensional for the finite-support trace shadow.
-/
theorem queryTraceGeneratedObservation_supportTraceShadowExtensional
    {Atom : Type u}
    {Out : Type z}
    {support query : List Atom}
    (hquery : QuerySupportedBy support query)
    (post : FiniteTowerLayerShadow -> List Bool -> Out) :
    SupportTraceShadowExtensional
      (Atom := Atom)
      support
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        post (canonicalTowerLayerShadow T)
          (supportTraceVector query T.sourceTraceToken)) := by
  rcases
    queryTraceGeneratedObservation_factors_through_supportTraceShadow
      (support := support) query hquery post with
    ⟨factor, hfactor⟩
  exact supportTraceShadowExtensional_of_factorization factor hfactor

/--
Same finite-support trace shadow implies the same supported query vector.
-/
theorem queryTraceVector_same_of_same_supportTraceShadow
    {Atom : Type u}
    {support query : List Atom}
    (hquery : QuerySupportedBy support query)
    {left right :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (hshadow :
      canonicalSupportTraceProbeTowerLayerShadow support left =
        canonicalSupportTraceProbeTowerLayerShadow support right) :
    supportTraceVector query left.sourceTraceToken =
      supportTraceVector query right.sourceTraceToken := by
  exact
    queryTraceVector_supportTraceShadowExtensional
      (Atom := Atom)
      hquery left right hshadow

/--
Same finite-support trace shadow implies the same supported query-generated
observation.
-/
theorem queryTraceGeneratedObservation_same_of_same_supportTraceShadow
    {Atom : Type u}
    {Out : Type z}
    {support query : List Atom}
    (hquery : QuerySupportedBy support query)
    (post : FiniteTowerLayerShadow -> List Bool -> Out)
    {left right :
      FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom}
    (hshadow :
      canonicalSupportTraceProbeTowerLayerShadow support left =
        canonicalSupportTraceProbeTowerLayerShadow support right) :
    post (canonicalTowerLayerShadow left)
        (supportTraceVector query left.sourceTraceToken) =
      post (canonicalTowerLayerShadow right)
        (supportTraceVector query right.sourceTraceToken) := by
  exact
    queryTraceGeneratedObservation_supportTraceShadowExtensional
      (Atom := Atom)
      hquery post left right hshadow

/-! ## Concrete complete-support query witness -/

/--
The Cycle 20 `[true]` query-generated observations are extensional for the
complete Bool support shadow.
-/
theorem boolTrueTraceQueryGeneratedObservation_supportTraceShadowExtensional
    {Out : Type z}
    (post : FiniteTowerLayerShadow -> List Bool -> Out) :
    SupportTraceShadowExtensional
      (Atom := Bool)
      SemanticRepairFiniteSupportCompleteness.boolCompleteTraceSupport
      (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
        post (canonicalTowerLayerShadow T)
          (supportTraceVector
            SemanticRepairFiniteQueryAdmissibility.boolTrueTraceQuery
            T.sourceTraceToken)) := by
  exact
    queryTraceGeneratedObservation_supportTraceShadowExtensional
      (support := SemanticRepairFiniteSupportCompleteness.boolCompleteTraceSupport)
      (query := SemanticRepairFiniteQueryAdmissibility.boolTrueTraceQuery)
      SemanticRepairFiniteQueryAdmissibility.boolTrueTraceQuery_supportedBy_completeBoolSupport
      post

end SemanticRepairFiniteQueryExtensionality
end QualitySurface
end Formal.AG.Research
