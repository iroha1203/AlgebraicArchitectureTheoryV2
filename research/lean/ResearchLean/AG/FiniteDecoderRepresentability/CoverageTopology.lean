import ResearchLean.AG.FiniteDecoderRepresentability.PermutationTransport
import Formal.Util.AssertStandardAxioms

/-!
# Topological characterization of anchored coverage

This module proves the first characterization in G-121(B).  Target extraction
sets are finite or cofinite exactly when their Bool characteristic functions
extend continuously across the one-point compactification.  Combining this with
the accepted G-112 endpoint necessity and sufficiency theorems characterizes
nonempty anchored coverage by finite source types and those continuous extensions.

## Implementation notes

The continuous-extension condition is written directly in theorem statements
rather than stored in a new certificate.  Necessity converts a genuine continuous
map through the G-121(A1) inverse and derives finite/cofinite image from the raw
code.  Sufficiency passes the derived target condition to the accepted
`endpointFiniteTargetCofiniteCoverage`; it does not rebuild a coverage witness.
-/

namespace AAT.AG.FiniteDecoderRepresentability

universe u

open AtomFoundation DoctrineFiberProduct OnePoint

variable {U : AtomCarrier.{u}}

/-- G-121(B1) fixes the discrete topology on the Atom carrier. -/
local instance coverageTopologyAtomTopology : TopologicalSpace U.Atom := ⊥

/-- G-121(B1) uses the canonical discreteness proof for that topology. -/
local instance coverageTopologyAtomDiscreteTopology : DiscreteTopology U.Atom :=
  discreteTopology_bot U.Atom

/--
G-121(B1) API necessity: a continuous extension of every target extraction
predicate implies the accepted finite/cofinite extraction condition.  Each
extension and its pointwise specification are actual theorem premises.
-/
theorem allExtractionsFiniteOrCofinite_of_continuousExtensions
    [DecidableEq U.Atom] (object : ExtractionInstance U)
    (extensions : ∀ source : object.doctrine.Source,
      ∃ map : C(OnePoint U.Atom, Bool), ∀ atom : U.Atom,
        (map (atom : OnePoint U.Atom) = true ↔
          object.doctrine.extracts source atom)) :
    AllExtractionsFiniteOrCofinite object := by
  intro source
  obtain ⟨map, hmap⟩ := extensions source
  let code := continuousMapToAtomPredicateCode map
  have hcode : ∀ atom : U.Atom,
      code.Holds atom ↔ object.doctrine.extracts source atom := by
    intro atom
    have hright : code.eval atom = map (atom : OnePoint U.Atom) := by
      calc
        code.eval atom = atomPredicateCodeToContinuousMap code
            (atom : OnePoint U.Atom) := by
          rw [atomPredicateCodeToContinuousMap_apply_coe]
        _ = map (atom : OnePoint U.Atom) := by
          rw [atomPredicateCodeToContinuousMap_rightInverse]
    change code.eval atom = true ↔ object.doctrine.extracts source atom
    rw [hright]
    exact hmap atom
  have hset : extractedAtomSet object source =
      {atom | code.Holds atom} := by
    ext atom
    exact (hcode atom).symm
  rw [hset]
  simpa only [Set.compl_setOf] using atomPredicateCode_finiteOrCofinite code

/--
G-121(B1) API sufficiency: the accepted finite/cofinite extraction condition
constructs a genuine continuous Bool extension for every source cell by G-112
encoding followed by the G-121(A1) map.
-/
theorem continuousExtensions_of_allExtractionsFiniteOrCofinite
    [DecidableEq U.Atom] (object : ExtractionInstance U)
    (hfinite : AllExtractionsFiniteOrCofinite object) :
    ∀ source : object.doctrine.Source,
      ∃ map : C(OnePoint U.Atom, Bool), ∀ atom : U.Atom,
        (map (atom : OnePoint U.Atom) = true ↔
          object.doctrine.extracts source atom) := by
  intro source
  let code := finiteOrCofiniteAtomPredicateCode
    (fun atom => object.doctrine.extracts source atom) (hfinite source)
  refine ⟨atomPredicateCodeToContinuousMap code, ?_⟩
  intro atom
  rw [atomPredicateCodeToContinuousMap_apply_coe]
  change code.Holds atom ↔ object.doctrine.extracts source atom
  exact finiteOrCofiniteAtomPredicateCode_holds_iff _ _ atom

/--
G-121(B1) equivalence between the accepted target extraction condition and
continuous extendability on the one-point compactification.  No endpoint or
coverage certificate is included in either side.
-/
theorem allExtractionsFiniteOrCofinite_iff_continuousExtensions
    [DecidableEq U.Atom] (object : ExtractionInstance U) :
    AllExtractionsFiniteOrCofinite object ↔
      ∀ source : object.doctrine.Source,
        ∃ map : C(OnePoint U.Atom, Bool), ∀ atom : U.Atom,
          (map (atom : OnePoint U.Atom) = true ↔
            object.doctrine.extracts source atom) :=
  ⟨continuousExtensions_of_allExtractionsFiniteOrCofinite object,
    allExtractionsFiniteOrCofinite_of_continuousExtensions object⟩

/--
G-121(B1) main theorem: anchored G-112 coverage exists exactly when both endpoint
Source types are finite and every target extraction predicate extends continuously.
The reverse implication invokes the accepted G-112 coverage constructor.
-/
theorem nonempty_anchoredCoverageWitness_iff_finite_continuousExtensions
    [DecidableEq U.Atom] (input : CartSemanticInput U) :
    Nonempty (AnchoredCoverageWitness input) ↔
      Finite input.source.doctrine.Source ∧
      Finite input.target.doctrine.Source ∧
      ∀ targetSource : input.target.doctrine.Source,
        ∃ map : C(OnePoint U.Atom, Bool), ∀ atom : U.Atom,
          (map (atom : OnePoint U.Atom) = true ↔
            input.target.doctrine.extracts targetSource atom) := by
  constructor
  · rintro ⟨witness⟩
    have hsource := coveredObjectWitness_necessary witness.sourceAnchor
    have htarget := coveredObjectWitness_necessary witness.targetAnchor
    exact ⟨hsource.1, htarget.1,
      continuousExtensions_of_allExtractionsFiniteOrCofinite input.target htarget.2⟩
  · rintro ⟨hsource, htarget, hextensions⟩
    letI : Finite input.source.doctrine.Source := hsource
    letI : Finite input.target.doctrine.Source := htarget
    exact endpointFiniteTargetCofiniteCoverage input
      (allExtractionsFiniteOrCofinite_of_continuousExtensions
        input.target hextensions)

#assert_standard_axioms_only AAT.AG.FiniteDecoderRepresentability

end AAT.AG.FiniteDecoderRepresentability
