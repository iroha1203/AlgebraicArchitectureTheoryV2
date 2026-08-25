import ResearchLean.AG.DoctrineFiberProduct.CartesianBranch

/-!
# Obstruction to a nonvacuous finite no-lift transport

The fixed G-110 ledger asks for a universe-polymorphic `FiniteModelLift` that
starts from a concrete universe-zero `CartesianLiftNonexistence` and transports
its nonexistence proof to the canonical `ULift` carrier.  The selected global
left branch proves more: `CartesianLiftNonexistence` is empty at every carrier.

This module records the resulting obstruction at the exact source and target
types of the requested transport.  A function out of the empty source can of
course be defined, but it has no firing witness and therefore cannot satisfy
the fixed nonvacuity and anti-empty-elimination acceptance requirement.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open AtomFoundation

local instance finiteModelLiftObstructionAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- The exact universe-zero source type required by the fixed finite lift ledger. -/
abbrev FiniteModelLiftSource :=
  CartesianLiftNonexistence FiniteModel.carrier

/-- The exact canonical `ULift`-carrier target type of the requested transport. -/
abbrev FiniteModelLiftTarget : Type (u + 1) :=
  CartesianLiftNonexistence finiteModelLiftCarrier.{u}

/-- The selected global branch makes the requested universe-zero source empty. -/
theorem finiteModelLiftSource_isEmpty : IsEmpty FiniteModelLiftSource :=
  cartesianLiftNonexistence_isEmpty FiniteModel.carrier

/-- The selected global branch also makes every requested lifted target empty. -/
theorem finiteModelLiftTarget_isEmpty : IsEmpty FiniteModelLiftTarget.{u} :=
  cartesianLiftNonexistence_isEmpty finiteModelLiftCarrier.{u}

/-- There is no concrete finite counterexample from which the transport can fire. -/
theorem finiteModelLiftSource_not_nonempty :
    ¬ Nonempty FiniteModelLiftSource := by
  intro source
  exact finiteModelLiftSource_isEmpty.false source.some

/--
A proposed transport from the fixed source to the lifted target never has an
input firing.  This theorem is independent of the implementation of
`transport`: the obstruction is the empty source forced by the selected
global-left theorem.
-/
theorem finiteModelLiftTransport_never_fires
    (transport : FiniteModelLiftSource → FiniteModelLiftTarget.{u}) :
    ¬ ∃ source : FiniteModelLiftSource,
      transport source = transport source := by
  rintro ⟨source, _⟩
  exact finiteModelLiftSource_isEmpty.false source

/--
The combined source-and-target firing packet demanded by a nonvacuous
counterexample transport is uninhabited under the selected global branch.
-/
structure FiniteModelLiftFiring : Type (u + 1) where
  source : FiniteModelLiftSource
  target : FiniteModelLiftTarget.{u}

/-- No nonvacuous finite-model no-lift transport packet can be produced. -/
theorem finiteModelLiftFiring_isEmpty : IsEmpty FiniteModelLiftFiring.{u} := by
  refine ⟨?_⟩
  intro firing
  exact finiteModelLiftSource_isEmpty.false firing.source

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
