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

/-! ## X.定義3.1: full finite gluing-complex fixture -/

namespace FullFiniteGluingComplexExample

/--
X.定義3.1: a two-chart full finite complex with one overlap for each ordered
chart pair.  Its restrictions make every selected primitive charge precisely
the atom present on the left restriction and absent on the right.
-/
def fullFiniteSemanticRepairGluingComplex :
    FullFiniteSemanticRepairGluingComplex.{0, 0, 0, 0, 0} where
  projection := CoverageWithoutFaithfulness.projection
  cover := CoverageWithoutFaithfulness.cover
  Chart := Fin 2
  chartFinite := inferInstance
  chartEnumeration := (Finset.univ : Finset (Fin 2)).toList
  chart_enumeration_complete := by
    intro chart
    simp
  Overlap := fun _left _right => Unit
  overlapFinite := fun _ _ => inferInstance
  overlapEnumeration := (Finset.univ :
    Finset (Sigma fun left : Fin 2 => Sigma fun right : Fin 2 => Unit)).toList
  overlap_enumeration_complete := by
    intro overlap
    simp
  C0 := Bool
  C1 := Bool
  primitiveFinite := inferInstance
  cochainFinite := inferInstance
  c0Enumeration := (Finset.univ : Finset Bool).toList
  c0_enumeration_complete := by
    intro primitive
    simp
  c1Enumeration := (Finset.univ : Finset Bool).toList
  c1_enumeration_complete := by
    intro cochain
    simp
  supportOf := fun _ _ => True
  resL := fun primitive _ atom =>
    primitive = true /\ atom = CoverageWithoutFaithfulness.Atom.t
  resR := fun _ _ _ => False
  ev := fun cochain _ atom =>
    cochain = true /\ atom = CoverageWithoutFaithfulness.Atom.t
  delta0 := id
  residual := true
  restriction_difference := by
    intro primitive overlap atom
    simp

/-- The fixture records an overlap between the two distinct charts. -/
theorem has_nontrivial_overlap :
    exists overlap : Sigma fun _left : Fin 2 => Sigma fun _right : Fin 2 => Unit,
      overlap.1 != overlap.2.1 :=
  ⟨⟨(0 : Fin 2), (1 : Fin 2), ()⟩, by decide⟩

/--
The nontrivial overlap evaluates the selected `delta0` cochain through the
left-only restriction, exercising the full restriction-difference law.
-/
theorem delta0_charges_left_only_on_nontrivial_overlap :
    fullFiniteSemanticRepairGluingComplex.ev
        (fullFiniteSemanticRepairGluingComplex.delta0 true)
        ⟨(0 : Fin 2), (1 : Fin 2), ()⟩ CoverageWithoutFaithfulness.Atom.t := by
  exact
    (FullFiniteSemanticRepairGluingComplex.delta0_ev_iff_restriction_xor
      fullFiniteSemanticRepairGluingComplex true
      ⟨(0 : Fin 2), (1 : Fin 2), ()⟩ CoverageWithoutFaithfulness.Atom.t).mpr
      (Or.inl ⟨by simp [fullFiniteSemanticRepairGluingComplex],
        by simp [fullFiniteSemanticRepairGluingComplex]⟩)

/-- The fixture discharges theorem 3.4's faithfulness hypotheses from total support. -/
theorem semanticFaithfulnessHypotheses :
    SemanticFaithfulnessHypotheses
      fullFiniteSemanticRepairGluingComplex.toFiniteSemanticRepairGluingComplex := by
  constructor
  · intro _primitive _hboundary residual _hresidual
    exact ⟨residual, trivial, rfl⟩
  · intro _primitive _hboundary _residual _candidate _hresidual _hcandidate _hprojection
    trivial

/-- X.定理3.4 on the full Definition 3.1 fixture, through the forgetful bridge. -/
theorem finiteSemanticRepairGluingDescent_iff :
    FullFiniteSemanticRepairGluingComplex.GlobalSemanticRepairCoherent
        fullFiniteSemanticRepairGluingComplex <->
      FullFiniteSemanticRepairGluingComplex.ObstructionClassVanishes
        fullFiniteSemanticRepairGluingComplex :=
  FullFiniteSemanticRepairGluingComplex.finiteSemanticRepairGluingDescent_iff
    fullFiniteSemanticRepairGluingComplex semanticFaithfulnessHypotheses

end FullFiniteGluingComplexExample

end SemanticRepair
end AAT.AG
