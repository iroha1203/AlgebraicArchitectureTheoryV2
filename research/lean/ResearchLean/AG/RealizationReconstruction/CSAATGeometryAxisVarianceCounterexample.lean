import ResearchLean.AG.RealizationReconstruction.CSAATGeometryForwardStructural
import Formal.Util.AssertStandardAxioms

/-!
# Variance counterexample for global target-reading restrictions

The fixed CS morphism class contains the unique total-lens morphism from an
empty state carrier to a one-point state carrier.  Its Law-index map has empty
source and nonempty target.  The source reading consequently has no readable
coordinate variable, whereas the target reading does.

This gives a concrete obstruction to using the existing contravariant
`ContextMorphism.observableRestrict` as the global observable component of
every noninvertible forward CS morphism.  It refutes that implementation route,
not the fixed G-123 target: a later forward/lax geometry interface must retain
the covariant coordinate and raw maps already constructed in Cycles 134--136.
-/

namespace AAT.AG.RealizationReconstruction

universe u

/-- Fixed one-point view parameter for the variance counterexample. -/
def axisVarianceLensInput : LensFamilyInput where
  View := PUnit
  reference := PUnit.unit

/-- The empty-state total lens.  All operation laws are vacuous. -/
def axisVarianceEmptyLens : LensRealization PUnit PUnit.unit where
  toLensData := {
    Carrier := PEmpty
    get := PEmpty.elim
    put := PEmpty.elim }
  condition := {
    put_get := fun state => PEmpty.elim state
    get_put := fun state => PEmpty.elim state
    put_put := fun state => PEmpty.elim state
    finite_fiber := inferInstance }

/-- The one-point total lens supplies an actual target Law coordinate. -/
def axisVarianceUnitLens : LensRealization PUnit PUnit.unit where
  toLensData := {
    Carrier := PUnit
    get := fun _ => PUnit.unit
    put := fun _ _ => PUnit.unit }
  condition := {
    put_get := fun _ => rfl
    get_put := fun _ _ => rfl
    put_put := fun _ _ _ => rfl
    finite_fiber := inferInstance }

/-- The unique empty-to-unit state map is an allowed, non-surjective primitive
lens morphism. -/
def axisVarianceForward : LensAATForwardMorphism
    (input := axisVarianceLensInput)
    axisVarianceEmptyLens axisVarianceUnitLens where
  stateMap := PEmpty.elim
  get_naturality state := PEmpty.elim state
  put_naturality state := PEmpty.elim state

/-- The source Law coordinate type is empty because every lens-law index
constructor requires a source state. -/
theorem axisVarianceSourceCoordinate_false
    (coordinate : (lensLawEquationSystem axisVarianceLensInput PEmpty
      axisVarianceEmptyLens.toLensData.toLawStructure).Coordinate) : False := by
  cases coordinate.1.down with
  | putGet state => exact PEmpty.elim state
  | getPut state view => exact PEmpty.elim state
  | putPut state first second => exact PEmpty.elim state

/-- No readable restriction exists from the rebased empty-source reading into
the independently constructed one-point target reading.  A target variable is
readable, but its restriction would have to be a readable source variable, and
there is no source coordinate. -/
theorem axisVariance_noTargetReadingRestriction :
    ¬ ∃ g : Site.ContextMorphism
        ((axisVarianceForward.lawContextFunctor).obj
          ⟨lensAATGeometryReadingContext axisVarianceLensInput
            axisVarianceEmptyLens⟩).ctx
        (lensAATGeometryReadingContext axisVarianceLensInput
          axisVarianceUnitLens),
      g.IsRestriction := by
  rintro ⟨g, hg⟩
  let targetCoordinate :
      (lensLawEquationSystem axisVarianceLensInput PUnit
        axisVarianceUnitLens.toLensData.toLawStructure).Coordinate :=
    (ULift.up (.putGet PUnit.unit), .point)
  have htarget :
      (lensAATGeometryReadingContext axisVarianceLensInput
        axisVarianceUnitLens).minimal.observableReads
        (MvPolynomial.X targetCoordinate) :=
    ⟨targetCoordinate, rfl⟩
  have hsource := hg.2.2.1 htarget
  rcases hsource with ⟨sourceCoordinate, _⟩
  exact axisVarianceSourceCoordinate_false sourceCoordinate

/-- Hence even the fixed point axis is not visible on the rebased source
context through the current target-reading restriction predicate. -/
theorem axisVariance_targetAxis_notReadable :
    ¬ (lensAATGeometryCoverageRequirements axisVarianceLensInput
      axisVarianceUnitLens).axisReadableOn
        ((axisVarianceForward.lawContextFunctor).obj
          ⟨lensAATGeometryReadingContext axisVarianceLensInput
            axisVarianceEmptyLens⟩).ctx
        (.point) := by
  rintro ⟨g, hg, _⟩
  exact axisVariance_noTargetReadingRestriction ⟨g, hg⟩

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
