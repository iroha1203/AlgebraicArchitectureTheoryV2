import Formal.AG.Research.QualitySurface.SemanticRepairFiniteSupportCompleteness

/-!
Cycle 20 evidence for `G-aat-quality-surface-04`.

This file separates finite trace-query admissibility from full arbitrary
observation factorization.  A query-generated observation factors through the
finite-support trace shadow when every queried coordinate is explicitly
supported by the finite support list.
-/

namespace Formal.AG.Research
namespace QualitySurface
namespace SemanticRepairFiniteQueryAdmissibility

open SemanticRepairObstructionTower
open SemanticRepairUniversalShadow
open SemanticRepairTraceProbeShadow
open SemanticRepairFiniteTraceSupport
open SemanticRepairFiniteSupportMembership
open SemanticRepairFiniteSupportCompleteness

universe u v w x y z

/-! ## Finite query support -/

/--
A finite trace query is supported by a finite support list when every queried
atom appears in that support list.  This is an explicit admissibility premise.
-/
def QuerySupportedBy
    {Atom : Type u}
    (support query : List Atom) : Prop :=
  ∀ atom : Atom, atom ∈ query -> atom ∈ support

/--
The trace vector of a supported finite query factors through the support trace
shadow.
-/
theorem queryTraceVector_factors_through_supportTraceShadow
    {Atom : Type u}
    {support : List Atom} :
    (query : List Atom) ->
    QuerySupportedBy support query ->
    ∃ factor : TraceProbeFiniteTowerLayerShadow -> List Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        supportTraceVector query T.sourceTraceToken =
          factor (canonicalSupportTraceProbeTowerLayerShadow support T)
  | [], _ => by
      exact ⟨fun _ => [], by intro T; rfl⟩
  | atom :: rest, hquery => by
      have hhead : atom ∈ support :=
        hquery atom (List.Mem.head rest)
      have htail : QuerySupportedBy support rest := by
        intro other hmem
        exact hquery other (List.Mem.tail atom hmem)
      rcases
        (sourceTraceCoordinate_factors_through_supportTraceProbeShadow
          (Atom := Atom) support hhead :
          ∃ factor : TraceProbeFiniteTowerLayerShadow -> Bool,
            ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
              T.sourceTraceToken atom =
                factor (canonicalSupportTraceProbeTowerLayerShadow support T)) with
        ⟨headFactor, hheadFactor⟩
      rcases
        queryTraceVector_factors_through_supportTraceShadow rest htail with
        ⟨tailFactor, htailFactor⟩
      exact
        ⟨fun shadow => headFactor shadow :: tailFactor shadow,
          by
            intro T
            change
              T.sourceTraceToken atom ::
                  supportTraceVector rest T.sourceTraceToken =
                headFactor
                    (canonicalSupportTraceProbeTowerLayerShadow support T) ::
                  tailFactor
                    (canonicalSupportTraceProbeTowerLayerShadow support T)
            rw [hheadFactor T, htailFactor T]⟩

/--
Every observation generated from the four-bit layer and a supported finite
query vector factors through the support trace shadow.
-/
theorem queryTraceGeneratedObservation_factors_through_supportTraceShadow
    {Atom : Type u}
    {Out : Type z}
    {support : List Atom}
    (query : List Atom)
    (hquery : QuerySupportedBy support query)
    (post : FiniteTowerLayerShadow -> List Bool -> Out) :
    ∃ factor : TraceProbeFiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{u, v, w, x, y} Atom,
        post (canonicalTowerLayerShadow T)
            (supportTraceVector query T.sourceTraceToken) =
          factor (canonicalSupportTraceProbeTowerLayerShadow support T) := by
  rcases
    queryTraceVector_factors_through_supportTraceShadow
      (support := support) query hquery with
    ⟨queryFactor, hqueryFactor⟩
  exact
    ⟨fun shadow => post shadow.layer (queryFactor shadow),
      by
        intro T
        change
          post (canonicalTowerLayerShadow T)
              (supportTraceVector query T.sourceTraceToken) =
            post
              (canonicalSupportTraceProbeTowerLayerShadow support T).layer
              (queryFactor
                (canonicalSupportTraceProbeTowerLayerShadow support T))
        rw [hqueryFactor T]
        rfl⟩

/-! ## Concrete complete-support query witness -/

/-- The singleton query reading the `true` Bool coordinate. -/
def boolTrueTraceQuery : List Bool :=
  [true]

/-- The query `[true]` is supported by the complete Bool support `[false, true]`. -/
theorem boolTrueTraceQuery_supportedBy_completeBoolSupport :
    QuerySupportedBy
      SemanticRepairFiniteSupportCompleteness.boolCompleteTraceSupport
      boolTrueTraceQuery := by
  intro atom hmem
  cases hmem with
  | head =>
      exact
        SemanticRepairFiniteSupportCompleteness.boolCompleteTraceSupport_complete
          true
  | tail _ htail =>
      cases htail

/-- The `[true]` query vector factors through the complete Bool support shadow. -/
theorem boolTrueTraceQuery_factors_through_completeBoolSupport :
    ∃ factor : TraceProbeFiniteTowerLayerShadow -> List Bool,
      ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
        supportTraceVector boolTrueTraceQuery T.sourceTraceToken =
          factor
            (canonicalSupportTraceProbeTowerLayerShadow
              SemanticRepairFiniteSupportCompleteness.boolCompleteTraceSupport T) := by
  exact
    queryTraceVector_factors_through_supportTraceShadow
      (support :=
        SemanticRepairFiniteSupportCompleteness.boolCompleteTraceSupport)
      boolTrueTraceQuery
      boolTrueTraceQuery_supportedBy_completeBoolSupport

/--
Generated observations from the current layer and the `[true]` query factor
through the complete Bool support shadow.
-/
theorem boolTrueTraceQueryGeneratedObservation_factors
    {Out : Type z}
    (post : FiniteTowerLayerShadow -> List Bool -> Out) :
    ∃ factor : TraceProbeFiniteTowerLayerShadow -> Out,
      ∀ T : FiniteSemanticRepairObstructionTower.{0, 0, 0, 0, 0} Bool,
        post (canonicalTowerLayerShadow T)
            (supportTraceVector boolTrueTraceQuery T.sourceTraceToken) =
          factor
            (canonicalSupportTraceProbeTowerLayerShadow
              SemanticRepairFiniteSupportCompleteness.boolCompleteTraceSupport T) := by
  exact
    queryTraceGeneratedObservation_factors_through_supportTraceShadow
      (support :=
        SemanticRepairFiniteSupportCompleteness.boolCompleteTraceSupport)
      boolTrueTraceQuery
      boolTrueTraceQuery_supportedBy_completeBoolSupport
      post

end SemanticRepairFiniteQueryAdmissibility
end QualitySurface
end Formal.AG.Research
