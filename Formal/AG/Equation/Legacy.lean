import Formal.AG.Equation.Basic
import Formal.AG.Atom.Law

/-!
# One-way legacy display bridge

This leaf module exposes an architectural equation as the old display-only
`Law` predicate.  It intentionally provides no construction in the reverse
direction: a free predicate does not determine observable rings, restrictions,
or either Atom-indexed coordinate family.
-/

namespace AAT.AG
namespace ArchitecturalEquationSystem

universe u

variable {U : AtomCarrier.{u}} {A₀ : ArchitectureObject U}
variable {C : Site.ContextPreorderCategory A₀}

/-- I.定義7.2: forget one equation to the legacy display predicate. -/
def toLegacyLaw (E : ArchitecturalEquationSystem C) (index : E.Index) : Law U where
  holds := fun object => E.EquationHolds index object

/-- The one-way legacy predicate is exactly the equation-residual vanishing predicate. -/
theorem toLegacyLaw_holds_iff (E : ArchitecturalEquationSystem C)
    (index : E.Index) (object : ArchitectureObject U) :
    (E.toLegacyLaw index).holds object ↔ E.EquationHolds index object :=
  Iff.rfl

end ArchitecturalEquationSystem
end AAT.AG
