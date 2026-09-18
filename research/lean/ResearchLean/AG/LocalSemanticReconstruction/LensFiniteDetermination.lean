import ResearchLean.AG.LocalSemanticReconstruction.FiniteEffectiveness
import ResearchLean.AG.LocalSemanticReconstruction.LensFiberKaroubiCoherence
import ResearchLean.AG.RealizationReconstruction.FixedFLensConnection
import Formal.Util.AssertStandardAxioms

/-!
# Finite determination of product-lens invertible changes

For a product lens, the complete-update operations connect every visible fiber
to the fixed reference fiber.  An invertible lens change is therefore read by
its action on the hidden coordinate at that fiber.  The accepted fixed-graph
classification identifies this reading with one permutation of the finite
complement.

This module applies the common `FiniteReading` definitions without conflating
their three properties.  Separation and extension are proved independently;
local coherence is the intrinsic bijectivity of the raw finite table.  The
effectiveness program decides that predicate, rejects exactly the nonbijective
tables, and constructs the actual `LensInvertibleChange` for every accepted
table.
-/

namespace AAT.AG.LocalSemanticReconstruction

open AAT.AG.RealizationReconstruction
open AAT.AG.RealizationReconstruction.FixedFLensConnection

universe u

namespace LensFiniteDetermination

variable {V K : Type u} {reference : V} [Fintype K]
  {visible : Equiv.Perm V}

/-- Read an actual product-lens invertible change at one point of the finite
reference fiber. -/
def readProductLensChangeAt
    (change : LensInvertibleChange
      (LensRealization.product V K reference)
      (LensRealization.product V K reference) visible)
    (hidden : K) : K :=
  (change.h (reference, hidden)).2

/-- The point reading is the hidden coordinate of the complete state change
evaluated in the fixed reference fiber. -/
theorem readProductLensChangeAt_eq_reference_evaluation
    (change : LensInvertibleChange
      (LensRealization.product V K reference)
      (LensRealization.product V K reference) visible)
    (hidden : K) :
    readProductLensChangeAt change hidden =
      (change.h (reference, hidden)).2 := by
  rfl

/-- The same reading is the accepted complete-update-graph fiber permutation
at the reference vertex. -/
@[simp] theorem readProductLensChangeAt_eq_fiberPerm
    (change : LensInvertibleChange
      (LensRealization.product V K reference)
      (LensRealization.product V K reference) visible)
    (hidden : K) :
    readProductLensChangeAt change hidden =
      change.toFollowingStateChange.fiberPerm reference hidden :=
  rfl

/-- The explicit finite reading set is the entire finite reference fiber. -/
def fullReferenceFiber : Finset K := Finset.univ

/-- Convert a raw table on the explicit full fiber set to its underlying
function on the hidden carrier. -/
def tableFunction
    (table : {hidden // hidden ∈ fullReferenceFiber (K := K)} → K) : K → K :=
  fun hidden => table ⟨hidden, Finset.mem_univ hidden⟩

/-- Independent local coherence for an invertible lens change: the raw finite
table must be bijective.  This predicate does not mention global extension. -/
def TableCoherent
    (table : {hidden // hidden ∈ fullReferenceFiber (K := K)} → K) : Prop :=
  Function.Bijective (tableFunction table)

/-- Bijectivity of the finite raw table is decidable from the supplied finite
enumeration and equality decision. -/
instance tableCoherentDecidable [DecidableEq K]
    (table : {hidden // hidden ∈ fullReferenceFiber (K := K)} → K) :
    Decidable (TableCoherent table) := by
  unfold TableCoherent Function.Bijective Function.Injective Function.Surjective
  infer_instance

/-- Compute the unique preimage of one value by searching the supplied finite
enumeration.  The uniqueness proof is data used by `Finset.choose`; no global
choice operator is used by this finite search. -/
def finiteInverseOfBijective [DecidableEq K]
    (function : K → K) (bijective : Function.Bijective function)
    (value : K) : K :=
  Finset.choose (fun candidate => function candidate = value) Finset.univ (by
    obtain ⟨candidate, mapsTo⟩ := bijective.2 value
    refine ⟨candidate, ⟨Finset.mem_univ candidate, mapsTo⟩, ?_⟩
    intro other otherProperty
    exact bijective.1 (otherProperty.2.trans mapsTo.symm))

/-- Construct a finite permutation with a computational inverse obtained by
finite search, rather than by an unbounded choice of preimages. -/
def finitePermutationOfBijective [DecidableEq K]
    (function : K → K) (bijective : Function.Bijective function) :
    Equiv.Perm K where
  toFun := function
  invFun := finiteInverseOfBijective function bijective
  left_inv hidden := by
    apply bijective.1
    exact (Finset.choose_spec
      (fun candidate => function candidate = function hidden)
      Finset.univ _).2
  right_inv hidden :=
    (Finset.choose_spec
      (fun candidate => function candidate = hidden)
      Finset.univ _).2

/-- The full finite reference-fiber reading separates actual product-lens
invertible changes. -/
theorem fullReferenceFiber_separates :
    FiniteReading.Separates
      (readProductLensChangeAt (V := V) (K := K)
        (reference := reference) (visible := visible))
      (fullReferenceFiber (K := K)) := by
  intro first second equality
  apply (LensInvertibleChange.equivHiddenPermutations
    (V := V) (K := K) (reference := reference)
    (visible := visible)).injective
  apply Equiv.ext
  intro hidden
  simpa only [readProductLensChangeAt_eq_fiberPerm] using
    congrFun equality ⟨hidden, Finset.mem_univ hidden⟩

/-- Every coherent full-fiber table extends to an actual product-lens
invertible change by the accepted hidden-permutation constructor. -/
theorem fullReferenceFiber_extends :
    FiniteReading.Extends
      (readProductLensChangeAt (V := V) (K := K)
        (reference := reference) (visible := visible))
      (fullReferenceFiber (K := K))
      (TableCoherent (K := K)) := by
  intro table coherent
  let permutation : Equiv.Perm K :=
    Equiv.ofBijective (tableFunction table) coherent
  refine ⟨LensInvertibleChange.ofHiddenPermutation
    (V := V) (reference := reference) (visible := visible) permutation, ?_⟩
  funext hidden
  exact congrArg table (Subtype.ext rfl)

/-- The entire finite reference fiber is a determining set: separation and
extension remain available as the two separately proved conjuncts. -/
theorem fullReferenceFiber_determining :
    FiniteReading.Determining
      (readProductLensChangeAt (V := V) (K := K)
        (reference := reference) (visible := visible))
      (fullReferenceFiber (K := K))
      (TableCoherent (K := K)) :=
  ⟨fullReferenceFiber_separates, fullReferenceFiber_extends⟩

/-- Decide bijectivity of a raw finite table and, exactly when it is coherent,
construct the actual product-lens invertible change classified by that table. -/
def effectivenessProgram [DecidableEq K] :
    FiniteReading.EffectivenessProgram
      (readProductLensChangeAt (V := V) (K := K)
        (reference := reference) (visible := visible))
      (fullReferenceFiber (K := K))
      (TableCoherent (K := K)) where
  coherenceTest table := decide (TableCoherent table)
  coherenceTest_eq_true_iff table := by
    simp
  extend? table :=
    if coherent : TableCoherent table then
      some (LensInvertibleChange.ofHiddenPermutation
        (V := V) (reference := reference) (visible := visible)
        (finitePermutationOfBijective (tableFunction table) coherent))
    else
      none
  extend_eq_none_iff table := by
    split_ifs with coherent
    · simp [coherent]
    · simp [coherent]
  restrict_eq_of_extend_eq_some table change success := by
    split_ifs at success with coherent
    · cases success
      funext hidden
      exact congrArg table (Subtype.ext rfl)

/-- The executable program proves the third common finite-reading property for
actual product-lens invertible changes. -/
theorem fullReferenceFiber_effective [DecidableEq K] :
    FiniteReading.Effective
      (readProductLensChangeAt (V := V) (K := K)
        (reference := reference) (visible := visible))
      (fullReferenceFiber (K := K))
      (TableCoherent (K := K)) :=
  ⟨effectivenessProgram (V := V) (K := K)
    (reference := reference) (visible := visible)⟩

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.LensFiniteDetermination

end LensFiniteDetermination

end AAT.AG.LocalSemanticReconstruction
