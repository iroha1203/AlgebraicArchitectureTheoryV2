import ResearchLean.AG.DoctrineFiberProduct.CartesianBranch

/-!
# Empty-wrapper obstruction for finite no-lift transport

The G-110 right-branch ledger asks for a universe-polymorphic `FiniteModelLift`
that starts from a concrete universe-zero `CartesianLiftNonexistence` and
transports its nonexistence proof to the canonical `ULift` carrier.  The
selected global left branch instead proves that `CartesianLiftNonexistence` is
empty at every carrier, so the right-branch transport is not applicable to the
current artifact.

This module records the resulting obstruction at the source and target types
of the no-lift corollary.  A function out of the empty source can of course be
defined, but that empty wrapper is not evidence for the data-level package
reindexing and strong-lift reflection route required when the right branch is
selected.

These theorems do not rule out that structural route.  They isolate why a bare
`CartesianLiftNonexistence` implication cannot replace it.
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

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
