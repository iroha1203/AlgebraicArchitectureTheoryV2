import ResearchLean.AG.DoctrineFiberProduct.ConfigurationDescent

/-!
# G-116 distinct architecture objects over every configuration

The configuration projection forgets the decoration carried by an
`ArchitectureObject`.  This module constructs two objects with different
`StructureMaps` types over an arbitrary configuration and proves that they are
distinct.

## Implementation notes

The two decoration types are lifted into the carrier universe because
`ArchitectureObject.StructureMaps` lives in `Type u`.  Using two values of one
decoration type was rejected: clause G-116(e1) specifically fixes a
type-changing decoration, and the chosen presentation exposes that difference
directly through the structure projection.  The two object definitions and
their inequality theorem are supporting API for the final G-116(e1) existence
theorem.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open AtomFoundation

/-- Supporting constructor for G-116(e1): the unit-decorated witness over the
configuration supplied by the fixed statement. -/
def unitDecoratedArchitectureObject
    {U : AtomCarrier.{u}} (configuration : AtomConfiguration U) :
    ArchitectureObject U where
  configuration := configuration
  StructureMaps := ULift.{u} PUnit
  SelectedQuantities := ULift.{u} PUnit
  structureMaps := ULift.up PUnit.unit
  selectedQuantities := ULift.up PUnit.unit

/-- Supporting constructor for G-116(e1): the Boolean-decorated witness over
the configuration supplied by the fixed statement. -/
def boolDecoratedArchitectureObject
    {U : AtomCarrier.{u}} (configuration : AtomConfiguration U) :
    ArchitectureObject U where
  configuration := configuration
  StructureMaps := ULift.{u} Bool
  SelectedQuantities := ULift.{u} PUnit
  structureMaps := ULift.up false
  selectedQuantities := ULift.up PUnit.unit

/-- Supporting API for G-116(e1): the two explicit witness constructors are
distinct.  The supplied configuration is ambient data; distinctness is
generated from the unequal cardinalities of their decoration types. -/
theorem unitDecoratedArchitectureObject_ne_boolDecoratedArchitectureObject
    {U : AtomCarrier.{u}} (configuration : AtomConfiguration U) :
    unitDecoratedArchitectureObject configuration ≠
      boolDecoratedArchitectureObject configuration := by
  intro equality
  have typeEquality : ULift.{u} PUnit = ULift.{u} Bool :=
    congrArg ArchitectureObject.StructureMaps equality
  have cardEquality : Fintype.card (ULift.{u} PUnit) =
      Fintype.card (ULift.{u} Bool) :=
    Fintype.card_congr (Equiv.cast typeEquality)
  norm_num at cardEquality

/-- G-116(e1) main theorem: every supplied configuration over an arbitrary
carrier is the projection of two distinct architecture objects.  There are no
additional premises. -/
theorem exists_distinct_architectureObjects_over_configuration
    {U : AtomCarrier.{u}} (configuration : AtomConfiguration U) :
    ∃ x y : ArchitectureObject U,
      x ≠ y ∧ x.configuration = configuration ∧
        y.configuration = configuration := by
  exact ⟨unitDecoratedArchitectureObject configuration,
    boolDecoratedArchitectureObject configuration,
    unitDecoratedArchitectureObject_ne_boolDecoratedArchitectureObject
      configuration,
    rfl,
    rfl⟩

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct

end AAT.AG.DoctrineFiberProduct
