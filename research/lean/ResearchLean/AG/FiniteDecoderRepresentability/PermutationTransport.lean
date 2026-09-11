import ResearchLean.AG.FiniteDecoderRepresentability.EncoderChoice
import Formal.Util.AssertStandardAxioms

/-!
# Permutation transport on codes and one-point extensions

This module proves the transport clause of G-121(A).  Every Atom permutation,
without a finite-support restriction, extends to a homeomorphism of the one-point
compactification fixing infinity.  Pullback along its inverse defines the matching
action on continuous Bool-valued maps, and the G-121(A1) equivalence intertwines
that action with the existing `AtomPredicateCode.transport`.

## Implementation notes

The OnePoint homeomorphism is obtained from mathlib's `Homeomorph.onePointCongr`
after viewing the arbitrary permutation as a homeomorphism of discrete spaces.
The continuous-map action is pullback, so its composition order agrees with the
existing code theorem `AtomPredicateCode.transport_trans`.  No finite-support
permutation code or newly authored permutation representation is used.
-/

namespace AAT.AG.FiniteDecoderRepresentability

universe u

open AtomFoundation DoctrineFiberProduct OnePoint

variable {U : AtomCarrier.{u}}

/-- G-121(A5) fixes the discrete topology on the Atom carrier. -/
local instance permutationTransportAtomTopology : TopologicalSpace U.Atom := ⊥

/-- G-121(A5) uses the canonical discreteness proof for that topology. -/
local instance permutationTransportAtomDiscreteTopology : DiscreteTopology U.Atom :=
  discreteTopology_bot U.Atom

/--
G-121(A5) main construction extending an arbitrary Atom permutation to the
one-point compactification.  Its only input is the fixed target permutation.
-/
def onePointAtomPerm (equiv : Equiv.Perm U.Atom) :
    OnePoint U.Atom ≃ₜ OnePoint U.Atom :=
  Homeomorph.onePointCongr equiv.toHomeomorphOfDiscrete

/-- G-121(A5) API: the extended permutation fixes the point at infinity. -/
@[simp]
theorem onePointAtomPerm_apply_infty (equiv : Equiv.Perm U.Atom) :
    onePointAtomPerm equiv ∞ = ∞ := by
  rfl

/-- G-121(A5) API: the extension restricts to the authored Atom permutation. -/
@[simp]
theorem onePointAtomPerm_apply_coe (equiv : Equiv.Perm U.Atom)
    (atom : U.Atom) :
    onePointAtomPerm equiv (atom : OnePoint U.Atom) = equiv atom := by
  rfl

/-- G-121(A5) coherence: extension preserves the identity permutation. -/
@[simp]
theorem onePointAtomPerm_refl :
    onePointAtomPerm (Equiv.refl U.Atom) = Homeomorph.refl _ := by
  ext x
  induction x using OnePoint.rec <;> rfl

/-- G-121(A5) coherence: extension commutes with permutation inverse. -/
@[simp]
theorem onePointAtomPerm_symm (equiv : Equiv.Perm U.Atom) :
    (onePointAtomPerm equiv).symm = onePointAtomPerm equiv.symm := by
  ext x
  induction x using OnePoint.rec <;> rfl

/-- G-121(A5) coherence: extension preserves permutation composition. -/
theorem onePointAtomPerm_trans (first second : Equiv.Perm U.Atom) :
    onePointAtomPerm (first.trans second) =
      (onePointAtomPerm first).trans (onePointAtomPerm second) := by
  ext x
  induction x using OnePoint.rec <;> rfl

/--
G-121(A5) evaluation API at an arbitrary target Atom.  It is the inverse-point
form of the existing `AtomPredicateCode.eval_transport` theorem.
-/
@[simp]
theorem atomPredicateCode_eval_transport_apply [DecidableEq U.Atom]
    (code : AtomPredicateCode U) (equiv : Equiv.Perm U.Atom)
    (atom : U.Atom) :
    (code.transport equiv).eval atom = code.eval (equiv.symm atom) := by
  nth_rewrite 1 [← equiv.apply_symm_apply atom]
  exact AtomPredicateCode.eval_transport code equiv (equiv.symm atom)

/--
G-121(A5) main continuous-map action: pull back along the inverse of the
extended Atom permutation.  It requires no finite-support hypothesis.
-/
def continuousPredicateTransport (map : C(OnePoint U.Atom, Bool))
    (equiv : Equiv.Perm U.Atom) : C(OnePoint U.Atom, Bool) :=
  map.comp ((onePointAtomPerm equiv).symm : C(OnePoint U.Atom, OnePoint U.Atom))

/-- G-121(A5) API exposing the pullback action pointwise. -/
@[simp]
theorem continuousPredicateTransport_apply
    (map : C(OnePoint U.Atom, Bool)) (equiv : Equiv.Perm U.Atom)
    (x : OnePoint U.Atom) :
    continuousPredicateTransport map equiv x =
      map ((onePointAtomPerm equiv).symm x) := by
  rfl

/-- G-121(A5) coherence: continuous pullback by identity is identity. -/
@[simp]
theorem continuousPredicateTransport_refl
    (map : C(OnePoint U.Atom, Bool)) :
    continuousPredicateTransport map (Equiv.refl U.Atom) = map := by
  ext x
  induction x using OnePoint.rec <;>
    simp

/-- G-121(A5) coherence: successive continuous pullbacks compose. -/
theorem continuousPredicateTransport_trans
    (map : C(OnePoint U.Atom, Bool))
    (first second : Equiv.Perm U.Atom) :
    continuousPredicateTransport (continuousPredicateTransport map first) second =
      continuousPredicateTransport map (first.trans second) := by
  ext x
  induction x using OnePoint.rec <;> simp

/-- G-121(A5) coherence: pullback by a permutation and its inverse cancels. -/
@[simp]
theorem continuousPredicateTransport_symm_cancel
    (map : C(OnePoint U.Atom, Bool)) (equiv : Equiv.Perm U.Atom) :
    continuousPredicateTransport (continuousPredicateTransport map equiv) equiv.symm =
      map := by
  rw [continuousPredicateTransport_trans]
  simp

/--
G-121(A5) main equivariance theorem: the A1 code/continuous-map equivalence
intertwines existing code transport with continuous pullback by the inverse.
-/
theorem atomPredicateCodeToContinuousMap_transport [DecidableEq U.Atom]
    (code : AtomPredicateCode U) (equiv : Equiv.Perm U.Atom) :
    atomPredicateCodeToContinuousMap (code.transport equiv) =
      continuousPredicateTransport (atomPredicateCodeToContinuousMap code) equiv := by
  ext x
  induction x using OnePoint.rec with
  | infty => rfl
  | coe atom =>
      simp [atomPredicateCode_eval_transport_apply]

#assert_standard_axioms_only AAT.AG.FiniteDecoderRepresentability

end AAT.AG.FiniteDecoderRepresentability
