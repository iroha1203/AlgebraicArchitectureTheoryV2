import ResearchLean.AG.DoctrineFiberProduct.IdempotentExchangeKaroubiImage

/-!
# G-116 distinct architecture objects over every configuration

The configuration projection forgets the decoration carried by an
`ArchitectureObject`.  This module constructs two objects with different
`StructureMaps` types over an arbitrary configuration and proves that they are
distinct.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open AtomFoundation

/-- A unit-decorated architecture object over an arbitrary configuration. -/
def unitDecoratedArchitectureObject
    {U : AtomCarrier.{u}} (configuration : AtomConfiguration U) :
    ArchitectureObject U where
  configuration := configuration
  StructureMaps := ULift.{u} PUnit
  SelectedQuantities := ULift.{u} PUnit
  structureMaps := ULift.up PUnit.unit
  selectedQuantities := ULift.up PUnit.unit

/-- A Boolean-decorated architecture object over an arbitrary configuration. -/
def boolDecoratedArchitectureObject
    {U : AtomCarrier.{u}} (configuration : AtomConfiguration U) :
    ArchitectureObject U where
  configuration := configuration
  StructureMaps := ULift.{u} Bool
  SelectedQuantities := ULift.{u} PUnit
  structureMaps := ULift.up false
  selectedQuantities := ULift.up PUnit.unit

/-- The unit- and Boolean-decorated objects over the same configuration are
distinct. -/
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

/-- G-116(e1): every configuration is the projection of two distinct
architecture objects. -/
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
