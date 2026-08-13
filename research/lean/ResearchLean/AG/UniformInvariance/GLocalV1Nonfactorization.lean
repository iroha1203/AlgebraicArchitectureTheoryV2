import ResearchLean.AG.UniformInvariance.GLocalV1T3T6Observation
import ResearchLean.AG.UniformInvariance.GLocalV1T3T6Uniformity
import Formal.Util.AssertStandardAxioms

/-!
# Permanent-observation nonfactorization

This module closes fixed GOAL claim (v)(d).  It combines the independently
proved equality of the permanent `G_local-v1` observations with the opposite
semantic uniformity labels of the registered T3 and T6 presentations.  Hence
no predicate on the observation value can characterize `UniformPresentation`
on every computable finite comparison presentation.

The proof introduces no predicate enumeration, decidability assumption,
presentation field, checker result, or external label.  Its only material
inputs are the three preceding Lean theorems, and both directions of the
hypothetical factorization equivalence are used.
-/

namespace AAT.AG.ResolutionInvariance

open FiniteComparisonPresentation
open GLocalV1T3T6Witnesses

/-- Semantic uniformity on finite comparison presentations does not factor
through the permanent `G_local-v1` observation.

Position: fixed GOAL claim (v)(d), quantified over every Prop-valued predicate
on the permanent observation and every computable finite comparison
presentation.  Premise provenance: the hypothetical factorization is locally
introduced for contradiction; the proof uses only T3 uniformity, T3/T6
observation equality, and T6 nonuniformity, never an external registered
label or a conclusion-equivalent certificate. -/
theorem uniformPresentation_not_factors_through_obsG :
    ∀ p : GLocalV1ObsValue → Prop,
      ¬ (∀ P : FiniteComparisonPresentation.{0},
        p (obsG P) ↔ UniformPresentation P) := by
  intro p hfactor
  have ht3 : p (obsG t3Presentation) :=
    (hfactor t3Presentation).mpr t3_uniformPresentation
  have ht6 : p (obsG t6Presentation) := by
    rw [← t3_obsG_eq_t6_obsG]
    exact ht3
  exact t6_not_uniformPresentation
    ((hfactor t6Presentation).mp ht6)

end AAT.AG.ResolutionInvariance

#assert_standard_axioms_only AAT.AG.ResolutionInvariance
