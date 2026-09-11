import ResearchLean.AG.FiniteDecoderRepresentability.FinOneCounterexample
import Mathlib.Data.Nat.Bitwise
import Formal.Util.AssertStandardAxioms

/-!
# The fixed infinite-support semantic automorphism

This module begins G-121(E) with the fixed natural-number carrier and the
adjacent-pair permutation.  The all-true singleton-source code is preserved by
the arbitrary semantic permutation, but no arrow with the same literal code
endpoints can decode that automorphism because every Atom moves.

## Implementation notes

XOR with one gives the adjacent-pair permutation without a parity branch in the
definition and supplies its inverse law directly.  Since this permutation is
involutive, the same semantic hom is used as both directions of the isomorphism.
The private instances only expose the fixed `Nat` Atom projection to typeclass
search.  For the one-point lift, the target's discrete Atom topology is fixed as
the bottom topology before reusing the unrestricted permutation lift from A.
-/

namespace AAT.AG.FiniteDecoderRepresentability

open CategoryTheory AtomFoundation DoctrineFiberProduct OnePoint

/-- G-121(E)'s fixed carrier, with every coordinate reading the identity on `Nat`. -/
def natSwapCarrier : AtomCarrier where
  AtomKind := Nat
  Axis := Nat
  Subject := Nat
  Predicate := Nat
  Payload := Nat
  Atom := Nat
  kind := id
  axis := id
  subject := id
  predicate := id
  payload := id

private instance : DecidableEq natSwapCarrier.Atom := by
  change DecidableEq Nat
  infer_instance

private instance : Infinite natSwapCarrier.Atom := by
  change Infinite Nat
  infer_instance

/-- G-121(E)'s raw extraction table `(true, ∅)`. -/
def natSwapTrueTable : AtomPredicateCode natSwapCarrier where
  defaultValue := true
  exceptions := ∅

/-- G-121(E)'s singleton-source fixed code `P_*`. -/
def natSwapCode : FiniteInstanceCode natSwapCarrier where
  doctrine :=
    { sourceCard := 1
      normalize := id
      extraction := fun _ => natSwapTrueTable }
  point := ULift.up 0

/-- G-121(E)'s fixed semantic object `X_* = D₀(P_*)`. -/
abbrev natSwapSemanticObject : ExtractionInstance natSwapCarrier :=
  natSwapCode.toSemantic

/-- G-121(E) computation API: `simp` exposes the source cardinality as one. -/
@[simp] theorem natSwapCode_sourceCard :
    natSwapCode.doctrine.sourceCard = 1 := rfl

/-- G-121(E) computation API: `simp` removes the source normalization. -/
@[simp] theorem natSwapCode_normalize (source : natSwapCode.doctrine.Source) :
    natSwapCode.doctrine.normalize source = source := rfl

/-- G-121(E) computation API: `simp` exposes every table as `(true, ∅)`. -/
@[simp] theorem natSwapCode_extraction (source : natSwapCode.doctrine.Source) :
    natSwapCode.doctrine.extraction source = natSwapTrueTable := rfl

/-- G-121(E) computation API: `simp` exposes the unique selected source point. -/
@[simp] theorem natSwapCode_point :
    natSwapCode.point = ULift.up (0 : Fin 1) := rfl

/-- The fixed extraction table evaluates true at every natural-number Atom. -/
@[simp] theorem natSwapTrueTable_eval (atom : natSwapCarrier.Atom) :
    natSwapTrueTable.eval atom = true := by
  simp [natSwapTrueTable, AtomPredicateCode.eval]

/-- Swap adjacent natural numbers by toggling their least significant bit. -/
def natAdjacentSwapNat : Equiv.Perm Nat where
  toFun atom := atom ^^^ 1
  invFun atom := atom ^^^ 1
  left_inv atom := Nat.xor_xor_cancel_right atom 1
  right_inv atom := Nat.xor_xor_cancel_right atom 1

/-- The natural-number swap, exposed at the fixed carrier's Atom projection. -/
def natAdjacentSwap : Equiv.Perm natSwapCarrier.Atom :=
  natAdjacentSwapNat

/-- G-121(E) computation API: `simp` exposes the swap as XOR with one at every Atom. -/
@[simp] theorem natAdjacentSwap_apply (atom : natSwapCarrier.Atom) :
    natAdjacentSwap atom = Nat.xor atom 1 := rfl

/-- G-121(E) computation API on even inputs. -/
@[simp] theorem natAdjacentSwap_even (n : Nat) :
    natAdjacentSwap (2 * n) = 2 * n + 1 := by
  rw [natAdjacentSwap_apply]
  exact Nat.xor_one_of_even ⟨n, by omega⟩

/-- G-121(E) computation API on odd inputs. -/
@[simp] theorem natAdjacentSwap_odd (n : Nat) :
    natAdjacentSwap (2 * n + 1) = 2 * n := by
  rw [natAdjacentSwap_apply]
  calc
    Nat.xor (2 * n + 1) 1 = (2 * n + 1) - 1 :=
      Nat.xor_one_of_odd ⟨n, by omega⟩
    _ = 2 * n := Nat.add_sub_cancel (2 * n) 1

/-- Every Atom is moved by the adjacent-pair permutation. -/
theorem natAdjacentSwap_ne (atom : natSwapCarrier.Atom) :
    natAdjacentSwap atom ≠ atom := by
  change Nat at atom
  intro h
  rw [natAdjacentSwap_apply] at h
  have hx : atom ^^^ 1 = atom ^^^ 0 := by simpa using h
  have : (1 : Nat) = 0 := Nat.xor_right_inj.mp hx
  omega

/-- G-121(E) decoded API: the fixed semantic object extracts every Atom. -/
@[simp] theorem natSwapCode_extracts (source : natSwapCode.doctrine.Source)
    (atom : natSwapCarrier.Atom) :
    natSwapCode.toSemantic.doctrine.extracts source atom := by
  simp [FiniteInstanceCode.toSemantic, natSwapCode,
    FiniteDoctrineCode.toDoctrine_extracts_iff, AtomPredicateCode.Holds]

/-- The all-true decoded extraction is invariant under the adjacent swap. -/
theorem natSwapCode_extracts_iff (source : natSwapCode.doctrine.Source)
    (atom : natSwapCarrier.Atom) :
    natSwapCode.toSemantic.doctrine.extracts source (natAdjacentSwap atom) ↔
      natSwapCode.toSemantic.doctrine.extracts source atom := by
  simp only [natSwapCode_extracts]

/-- The adjacent swap gives a semantic endomorphism with identity source map. -/
def natAdjacentSwapSemanticHom :
    natSwapCode.toSemantic ⟶ natSwapCode.toSemantic where
  doctrineHom :=
    { sourceMap := id
      atomEquiv := natAdjacentSwap
      normalize_eq := by intro; rfl
      extraction_iff := by
        intro source atom
        simpa only [id_eq] using natSwapCode_extracts_iff source atom }
  source_eq := rfl

/-- The semantic endomorphism is an automorphism because the swap is involutive. -/
def natAdjacentSwapSemanticIso :
    natSwapCode.toSemantic ≅ natSwapCode.toSemantic where
  hom := natAdjacentSwapSemanticHom
  inv := natAdjacentSwapSemanticHom
  hom_inv_id := by
    apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · rfl
    · apply Equiv.ext
      intro atom
      exact Nat.xor_xor_cancel_right atom 1
  inv_hom_id := by
    apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · rfl
    · apply Equiv.ext
      intro atom
      exact Nat.xor_xor_cancel_right atom 1

/-- G-121(E) computation API: `simp` exposes the automorphism's source map as identity. -/
@[simp] theorem natAdjacentSwapSemanticIso_hom_sourceMap :
    natAdjacentSwapSemanticIso.hom.doctrineHom.sourceMap = id := rfl

/-- G-121(E) computation API: `simp` exposes the automorphism's Atom equivalence as the swap. -/
@[simp] theorem natAdjacentSwapSemanticIso_hom_atomEquiv :
    natAdjacentSwapSemanticIso.hom.doctrineHom.atomEquiv = natAdjacentSwap := rfl

/-- G-121(E) computation API: `simp` exposes the automorphism's inverse source map as identity. -/
@[simp] theorem natAdjacentSwapSemanticIso_inv_sourceMap :
    natAdjacentSwapSemanticIso.inv.doctrineHom.sourceMap = id := rfl

/-- G-121(E) computation API: `simp` exposes the inverse Atom equivalence as the involutive swap. -/
@[simp] theorem natAdjacentSwapSemanticIso_inv_atomEquiv :
    natAdjacentSwapSemanticIso.inv.doctrineHom.atomEquiv = natAdjacentSwap := rfl

/-- The adjacent swap's actual support is the whole natural-number carrier. -/
theorem natAdjacentSwap_support_eq_univ :
    atomPermutationSupport natAdjacentSwap = Set.univ := by
  ext atom
  simp only [atomPermutationSupport, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  exact natAdjacentSwap_ne atom

/-- Consequently the adjacent swap has infinite actual support. -/
theorem natAdjacentSwap_support_infinite :
    (atomPermutationSupport natAdjacentSwap).Infinite := by
  rw [natAdjacentSwap_support_eq_univ]
  exact Set.infinite_univ

/-- No fixed-endpoint finite-code arrow decodes the adjacent-swap semantic arrow. -/
theorem not_exists_natSwapCodeHom :
    ¬ ∃ codeHom : FiniteCodeCartHom natSwapCode natSwapCode,
      finiteCodeCartRealization.map codeHom = natAdjacentSwapSemanticIso.hom := by
  rw [exists_finiteCodeCartHom_map_iff_of_infinite]
  exact natAdjacentSwap_support_infinite

/-- The fixed decoder is not full on the natural-number carrier. -/
theorem natSwap_finiteCodeCartRealization_not_full :
    ¬ (finiteCodeCartRealization (U := natSwapCarrier)).Full := by
  intro hfull
  obtain ⟨codeHom, hmap⟩ :=
    hfull.map_surjective natAdjacentSwapSemanticIso.hom
  exact not_exists_natSwapCodeHom ⟨codeHom, hmap⟩

/-- G-121(E) fixes the discrete topology before forming the one-point extension. -/
local instance natSwapAtomTopology : TopologicalSpace natSwapCarrier.Atom := ⊥

/-- The fixed bottom topology is discrete. -/
local instance natSwapAtomDiscreteTopology : DiscreteTopology natSwapCarrier.Atom :=
  discreteTopology_bot natSwapCarrier.Atom

/-- The adjacent swap extends to the G-121(A) one-point homeomorphism. -/
def natAdjacentSwapOnePointHomeomorph :
    OnePoint natSwapCarrier.Atom ≃ₜ OnePoint natSwapCarrier.Atom :=
  onePointAtomPerm natAdjacentSwap

/-- G-121(E) computation API: the one-point extension fixes infinity. -/
@[simp] theorem natAdjacentSwapOnePointHomeomorph_infty :
    natAdjacentSwapOnePointHomeomorph (∞ : OnePoint natSwapCarrier.Atom) = ∞ :=
  onePointAtomPerm_apply_infty natAdjacentSwap

/-- G-121(E) computation API: the one-point extension restricts to the swap. -/
@[simp] theorem natAdjacentSwapOnePointHomeomorph_coe
    (atom : natSwapCarrier.Atom) :
    natAdjacentSwapOnePointHomeomorph (atom : OnePoint natSwapCarrier.Atom) =
      natAdjacentSwap atom :=
  onePointAtomPerm_apply_coe natAdjacentSwap atom

#assert_standard_axioms_only AAT.AG.FiniteDecoderRepresentability

end AAT.AG.FiniteDecoderRepresentability
