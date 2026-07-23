import Formal.AG.LawAlgebra.RingedSiteFiniteExample
import Formal.AG.Examples.FiniteModelLegacy

noncomputable section

namespace AAT.AG.LawAlgebra.FiniteExamples.RingedSite

namespace FiniteModel

open AAT.AG.FiniteModel

/-- The generated compatibility law of the ringed-site fixture is NoCycle. -/
@[simp] theorem site_law_eq_noCycleLaw :
    site.equationSystem.toLegacyLawUniverse.law PUnit.unit = noCycleLaw := by
  change (equationSystem twoPatchContextPreorder).toLegacyLawUniverse.law
    PUnit.unit = noCycleLaw
  exact equationSystem_legacy_law_eq_noCycleLaw twoPatchContextPreorder

end FiniteModel

end AAT.AG.LawAlgebra.FiniteExamples.RingedSite
