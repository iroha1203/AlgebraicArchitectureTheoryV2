import Formal.AG.Research.QualitySurface.SemanticRepairFiniteQueryRepresentationRealizedRecovery

/-!
Cycle 41 evidence for `G-aat-quality-surface-04`.

Cycle 40 exposed realized-tower recovery as a visible premise.  This file
discharges that premise for the canonical finite-support trace shadow: when a
query is supported by the visible support list, the support-shadow output itself
contains enough readings to recover the query vector on realized towers.

This is a support-shadow recovery theorem, not a current-shadow factorization
or target theorem completion result.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQueryRepresentationSupportRecovery

open SemanticRepairObstructionTower
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteSupportCompleteness
open SemanticRepairFiniteQueryAdmissibility
open SemanticRepairFiniteQueryObservation
open SemanticRepairFiniteQueryRepresentation
open SemanticRepairFiniteQueryRepresentationSupportControl
open SemanticRepairFiniteQueryRepresentationRealizedRecovery

universe u v w x y

/-! ## Support-shadow recovery of query readings -/

/--
If a query is visibly supported by a finite support list, then the canonical
support trace shadow recovers the query readings on realized towers.

The decoder is supplied by the existing support-shadow factorization theorem.
-/
theorem supportTraceShadowObservation_recoversSupportedQueryReadings
    {Atom : Type u}
    {support query : List Atom}
    (hquery : QuerySupportedBy support query) :
    ObservationRecoversQueryReadings.{u, v, w, x, y, 0}
      (Atom := Atom)
      query
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        canonicalSupportTraceProbeTowerLayerShadow support T) := by
  rcases
    queryTraceVector_factors_through_supportTraceShadow
      (support := support) query hquery with
    ⟨decode, hdecode⟩
  exact
    ⟨decode, by
      intro T
      exact (hdecode T).symm⟩

/--
A complete support recovers every finite query through the canonical support
trace shadow.
-/
theorem completeSupportTraceShadowObservation_recoversQueryReadings
    {Atom : Type u}
    {support query : List Atom}
    (hcomplete : FiniteSupportComplete support) :
    ObservationRecoversQueryReadings.{u, v, w, x, y, 0}
      (Atom := Atom)
      query
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        canonicalSupportTraceProbeTowerLayerShadow support T) := by
  exact
    supportTraceShadowObservation_recoversSupportedQueryReadings
      (Atom := Atom)
      (support := support)
      (query := query)
      (by
        intro atom _hmem
        exact hcomplete atom)

/--
The canonical support-shadow finite query observation recovers its own support
readings on realized towers.
-/
theorem supportTraceShadowFiniteTraceQueryObservation_recoversQueryReadings
    {Atom : Type u}
    (support : List Atom) :
    ObservationRecoversQueryReadings.{u, v, w, x, y, 0}
      (Atom := Atom)
      (supportTraceShadowFiniteTraceQueryObservation support).query
      (fun T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom =>
        (supportTraceShadowFiniteTraceQueryObservation support).observe T) := by
  exact
    ⟨fun shadow => shadow.sourceTraceReadings, by
      intro T
      rfl⟩

/--
The canonical support-shadow representation discharges the Cycle 40
realized-post recovery premise.
-/
theorem supportTraceShadowRepresentation_recoversQueryReadingsOnRealizedTowers
    {Atom : Type u}
    (support : List Atom) :
    QueryReadingsRecoveringPostOnRealizedTowers.{u, v, w, x, y, 0}
      (Atom := Atom)
      (supportTraceShadowFiniteTraceQueryObservationRepresentation
        support).package.query
      (supportTraceShadowFiniteTraceQueryObservationRepresentation
        support).package.post := by
  exact
    queryReadingsRecoveringPostOnRealizedTowers_of_observationRecoversQueryReadings
      (Atom := Atom)
      (supportTraceShadowFiniteTraceQueryObservationRepresentation support)
      (supportTraceShadowFiniteTraceQueryObservation_recoversQueryReadings
        (Atom := Atom) support)

/--
For a complete Bool support, the `[true]` query readings are recoverable from
the complete support trace shadow.
-/
theorem boolTrueCompleteSupportTraceShadowObservation_recoversQueryReadings :
    ObservationRecoversQueryReadings.{0, 0, 0, 0, 0, 0}
      (Atom := Bool)
      boolTrueTraceQuery
      (fun T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool =>
        canonicalSupportTraceProbeTowerLayerShadow boolCompleteTraceSupport T) := by
  exact
    supportTraceShadowObservation_recoversSupportedQueryReadings
      (Atom := Bool)
      (support := boolCompleteTraceSupport)
      (query := boolTrueTraceQuery)
      boolTrueTraceQuery_supportedBy_completeBoolSupport

end SemanticRepairFiniteQueryRepresentationSupportRecovery
end QualitySurface
end Formal.AG.Research
