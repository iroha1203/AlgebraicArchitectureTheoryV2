import ResearchLean.AG.FiniteDecoderRepresentability.CoverageTopology
import Formal.Util.AssertStandardAxioms

/-!
# Discrete compactness form of the coverage criterion

This module proves the compactness restatement in G-121(B).  It keeps the
topology explicit as `⊥`, so no topology on either semantic Source type is
added to the surrounding API.
-/

namespace AAT.AG.FiniteDecoderRepresentability

universe u v

open AtomFoundation DoctrineFiberProduct OnePoint

variable {U : AtomCarrier.{u}}

/-- G-121(B2) retains B1's fixed discrete topology on the Atom carrier. -/
local instance discreteCompactnessAtomTopology : TopologicalSpace U.Atom := ⊥

/-- The fixed bottom topology on the Atom carrier is discrete. -/
local instance discreteCompactnessAtomDiscreteTopology : DiscreteTopology U.Atom :=
  discreteTopology_bot U.Atom

/-- A type is finite exactly when its discrete topology is compact. -/
theorem finite_iff_compactSpace_bot (X : Type v) :
    Finite X ↔ @CompactSpace X ⊥ := by
  constructor
  · intro hfinite
    letI : Finite X := hfinite
    exact @Finite.compactSpace X ⊥ _
  · intro hcompact
    letI : TopologicalSpace X := ⊥
    letI : DiscreteTopology X := discreteTopology_bot X
    letI : CompactSpace X := hcompact
    exact finite_of_compact_of_discrete

/--
G-121(B2) compactness form of the anchored-coverage characterization.  Both
Source spaces carry the explicitly fixed discrete topology; the target
extraction predicates retain the genuine continuous extensions from B1.
-/
theorem nonempty_anchoredCoverageWitness_iff_compact_continuousExtensions
    [DecidableEq U.Atom] (input : CartSemanticInput U) :
    Nonempty (AnchoredCoverageWitness input) ↔
      @CompactSpace input.source.doctrine.Source ⊥ ∧
      @CompactSpace input.target.doctrine.Source ⊥ ∧
      ∀ targetSource : input.target.doctrine.Source,
        ∃ map : C(OnePoint U.Atom, Bool), ∀ atom : U.Atom,
          (map (atom : OnePoint U.Atom) = true ↔
            input.target.doctrine.extracts targetSource atom) := by
  rw [nonempty_anchoredCoverageWitness_iff_finite_continuousExtensions]
  rw [finite_iff_compactSpace_bot, finite_iff_compactSpace_bot]

#assert_standard_axioms_only AAT.AG.FiniteDecoderRepresentability

end AAT.AG.FiniteDecoderRepresentability
