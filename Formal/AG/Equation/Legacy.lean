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

namespace EquationRole

/-- Convert the equation role to the legacy display role. -/
def toLegacy : EquationRole -> LawRole
  | .required => .required
  | .optional => .optional
  | .derived => .derived

end EquationRole

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

/--
The equation-generated witness display: an index/Atom pair is bad when its
object-dependent residual is nonzero in at least one selected context.
-/
def toLegacyWitnessFamily (E : ArchitecturalEquationSystem C) :
    LawWitnessFamily U where
  Witness := E.Coordinate
  badWitness object coordinate :=
    ∃ W : Site.ContextCategoryObject C,
      E.equationResidual W object coordinate.1 coordinate.2 ≠ 0

/--
One-way compatibility view of an architectural equation system as the old
natural-language law universe.

Every law, role, and witness is generated from `E`; no free predicate,
coverage assumption, exactness assumption, or reverse bridge is accepted.
-/
def toLegacyLawUniverse (E : ArchitecturalEquationSystem C) : LawUniverse U where
  Index := E.Index
  law := E.toLegacyLaw
  role index := (E.role index).toLegacy
  witnessFamily := E.toLegacyWitnessFamily
  SelectedReading := PUnit
  selectedReading := PUnit.unit

/-- Required-role membership is preserved by the generated legacy view. -/
theorem toLegacyLawUniverse_required_iff
    (E : ArchitecturalEquationSystem C) (index : E.Index) :
    E.toLegacyLawUniverse.Required index ↔ E.Required index := by
  cases hrole : E.role index <;>
    simp [LawUniverse.Required, ArchitecturalEquationSystem.Required,
      toLegacyLawUniverse, EquationRole.toLegacy, hrole]

/-- Optional-role membership is preserved by the generated legacy view. -/
theorem toLegacyLawUniverse_optional_iff
    (E : ArchitecturalEquationSystem C) (index : E.Index) :
    E.toLegacyLawUniverse.Optional index ↔ E.Optional index := by
  cases hrole : E.role index <;>
    simp [LawUniverse.Optional, ArchitecturalEquationSystem.Optional,
      toLegacyLawUniverse, EquationRole.toLegacy, hrole]

/-- Derived-role membership is preserved by the generated legacy view. -/
theorem toLegacyLawUniverse_derived_iff
    (E : ArchitecturalEquationSystem C) (index : E.Index) :
    E.toLegacyLawUniverse.Derived index ↔ E.Derived index := by
  cases hrole : E.role index <;>
    simp [LawUniverse.Derived, ArchitecturalEquationSystem.Derived,
      toLegacyLawUniverse, EquationRole.toLegacy, hrole]

end ArchitecturalEquationSystem
end AAT.AG
