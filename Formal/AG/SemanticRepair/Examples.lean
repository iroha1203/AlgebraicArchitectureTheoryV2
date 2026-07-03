import Formal.AG.SemanticRepair.GluingComplex

noncomputable section

namespace AAT.AG
namespace SemanticRepair

universe u v w x y

/--
X.例3.6: visible local coherence.

This bounded predicate records that the finite complex has a visible local
primitive.  It is intentionally weaker than global semantic repair coherence:
global coherence additionally requires the selected residual to be a `delta0`
boundary and the boundary primitive to be semantically closed.
-/
def VisibleLocalCoherent
    (K : FiniteSemanticRepairGluingComplex.{u, v, w, x, y}) : Prop :=
  Nonempty K.C0

namespace Example36

/--
X.例3.6: selected visible-local witness complex.

The complex has one visible local primitive, so `VisibleLocalCoherent` holds.
Its selected residual is `true`, while every `delta0` boundary is `false`;
hence the residual is not in `B1` and global coherence cannot be generated.
-/
def selectedVisibleLocalWitnessComplex :
    FiniteSemanticRepairGluingComplex.{0, 0, 0, 0, 0} where
  projection := CoverageWithoutFaithfulness.projection
  cover := CoverageWithoutFaithfulness.cover
  C0 := Unit
  C1 := Bool
  primitiveFinite := inferInstance
  cochainFinite := inferInstance
  supportOf := fun _ => CoverageWithoutFaithfulness.support
  delta0 := fun _ => false
  residual := true

/-- X.例3.6: the selected witness has visible local coherence. -/
theorem selectedVisibleLocalWitness_visibleLocalCoherent :
    VisibleLocalCoherent selectedVisibleLocalWitnessComplex :=
  ⟨()⟩

/-- X.例3.6: the selected residual is not a finite boundary, `r ∉ B¹`. -/
theorem selectedVisibleLocalWitness_residual_not_boundary :
    Not (B1 selectedVisibleLocalWitnessComplex
      selectedVisibleLocalWitnessComplex.residual) := by
  intro hboundary
  rcases hboundary with ⟨primitive, hprimitive⟩
  cases primitive
  cases hprimitive

/-- X.例3.6: the selected finite obstruction class is nonzero. -/
theorem selectedVisibleLocalWitness_obstructionNonzero :
    ObstructionClassNonzero selectedVisibleLocalWitnessComplex :=
  selectedVisibleLocalWitness_residual_not_boundary

/-- X.例3.6: nonzero boundary obstruction rules out global coherence. -/
theorem selectedVisibleLocalWitness_noGlobalRepairCoherent :
    Not (GlobalSemanticRepairCoherent selectedVisibleLocalWitnessComplex) :=
  no_globalRepairCoherent_of_nonzero_obstruction
    selectedVisibleLocalWitnessComplex
    selectedVisibleLocalWitness_obstructionNonzero

/--
X.例3.6: visible local coherence does not imply global semantic repair
coherence.

The selected finite witness simultaneously has a visible local primitive,
has residual `r ∉ B¹`, and has no global coherent repair certificate.
-/
theorem selectedVisibleLocalWitness_example36_package :
    VisibleLocalCoherent selectedVisibleLocalWitnessComplex /\
      Not (B1 selectedVisibleLocalWitnessComplex
        selectedVisibleLocalWitnessComplex.residual) /\
      Not (GlobalSemanticRepairCoherent selectedVisibleLocalWitnessComplex) :=
  ⟨selectedVisibleLocalWitness_visibleLocalCoherent,
    selectedVisibleLocalWitness_residual_not_boundary,
    selectedVisibleLocalWitness_noGlobalRepairCoherent⟩

end Example36

end SemanticRepair
end AAT.AG
