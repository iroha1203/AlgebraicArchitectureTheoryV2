import Formal.AG.Atom.Atom
import Formal.Util.AssertStandardAxioms

namespace ResearchLean.AG.Smoke

/-- Package-direction smoke witness using a definition from the root package. -/
abbrev AtomCarrier := AAT.AG.AtomCarrier

/-- Research package code can construct the root package's atom record view. -/
def atomRecord {U : AAT.AG.AtomCarrier} (atom : U.Atom) := U.record atom

#assert_standard_axioms_only ResearchLean.AG.Smoke
