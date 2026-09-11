import ResearchLean.AG.FiniteDecoderRepresentability.NatSwapAnchoredCoverage
import Mathlib.Logic.Equiv.Nat
import Formal.Util.AssertStandardAxioms

/-!
# Subset-indexed semantic automorphisms

For every `S : Set Nat`, this module swaps the adjacent pair `(2n, 2n+1)`
exactly when `n ∈ S`.  The permutation acts on the fixed all-true semantic
object from G-121(E), and its even-input computation proves that the resulting
map from subsets to semantic automorphisms is injective.

## Implementation notes

The construction conjugates a conditional summand swap on `Nat ⊕ Nat` by
`Equiv.natSumNatEquivNat`.  This makes the pair index explicit and proves
involutivity before any semantic structure is built.  The semantic inverse uses
the actual inverse equivalence, so the categorical inverse laws do not assume
the desired subset injectivity.
-/

namespace AAT.AG.FiniteDecoderRepresentability

open CategoryTheory AtomFoundation DoctrineFiberProduct

/-- Conditionally exchange the two copies of a natural number at indices in `S`. -/
noncomputable def subsetSumSwapFn (S : Set Nat) : Nat ⊕ Nat → Nat ⊕ Nat
  := by
  classical
  exact fun
    | Sum.inl n => if n ∈ S then Sum.inr n else Sum.inl n
    | Sum.inr n => if n ∈ S then Sum.inl n else Sum.inr n

/-- G-121(E) computation API: membership makes the raw function send `inl` to `inr`. -/
theorem subsetSumSwapFn_inl_of_mem (S : Set Nat) (n : Nat) (h : n ∈ S) :
    subsetSumSwapFn S (Sum.inl n) = Sum.inr n := by
  classical
  simp [subsetSumSwapFn, h]

/-- G-121(E) computation API: nonmembership makes the raw function fix `inl`. -/
theorem subsetSumSwapFn_inl_of_not_mem (S : Set Nat) (n : Nat) (h : n ∉ S) :
    subsetSumSwapFn S (Sum.inl n) = Sum.inl n := by
  classical
  simp [subsetSumSwapFn, h]

/-- G-121(E) computation API: membership makes the raw function send `inr` to `inl`. -/
theorem subsetSumSwapFn_inr_of_mem (S : Set Nat) (n : Nat) (h : n ∈ S) :
    subsetSumSwapFn S (Sum.inr n) = Sum.inl n := by
  classical
  simp [subsetSumSwapFn, h]

/-- G-121(E) computation API: nonmembership makes the raw function fix `inr`. -/
theorem subsetSumSwapFn_inr_of_not_mem (S : Set Nat) (n : Nat) (h : n ∉ S) :
    subsetSumSwapFn S (Sum.inr n) = Sum.inr n := by
  classical
  simp [subsetSumSwapFn, h]

/-- The conditional summand swap is an involution. -/
theorem subsetSumSwapFn_involutive (S : Set Nat) :
    Function.Involutive (subsetSumSwapFn S) := by
  classical
  intro value
  cases value with
  | inl n => by_cases h : n ∈ S <;> simp [subsetSumSwapFn, h]
  | inr n => by_cases h : n ∈ S <;> simp [subsetSumSwapFn, h]

/-- The conditional summand swap as an actual permutation. -/
noncomputable def subsetSumSwap (S : Set Nat) : Equiv.Perm (Nat ⊕ Nat) :=
  (subsetSumSwapFn_involutive S).toPerm

/-- G-121(E) computation API: `simp` reduces the permutation to the raw conditional function. -/
@[simp] theorem subsetSumSwap_apply (S : Set Nat) (value : Nat ⊕ Nat) :
    subsetSumSwap S value = subsetSumSwapFn S value := rfl

/-- G-121(E)'s permutation `σ_S`, transported from the even/odd sum model. -/
noncomputable def subsetAdjacentSwap (S : Set Nat) :
    Equiv.Perm natSwapCarrier.Atom :=
  Equiv.natSumNatEquivNat.symm.trans
    ((subsetSumSwap S).trans Equiv.natSumNatEquivNat)

/-- G-121(E) computation API: membership makes `σ_S` send an even input to its odd mate. -/
theorem subsetAdjacentSwap_even_of_mem (S : Set Nat) (n : Nat)
    (h : n ∈ S) : subsetAdjacentSwap S (2 * n) = 2 * n + 1 := by
  classical
  change Equiv.natSumNatEquivNat
    (subsetSumSwap S (Equiv.natSumNatEquivNat.symm (2 * n))) = _
  rw [← show Equiv.natSumNatEquivNat (Sum.inl n) = 2 * n by rfl]
  rw [Equiv.symm_apply_apply]
  rw [subsetSumSwap_apply, subsetSumSwapFn_inl_of_mem S n h]
  rfl

/-- G-121(E) computation API: nonmembership makes `σ_S` fix an even input. -/
theorem subsetAdjacentSwap_even_of_not_mem (S : Set Nat) (n : Nat)
    (h : n ∉ S) : subsetAdjacentSwap S (2 * n) = 2 * n := by
  classical
  change Equiv.natSumNatEquivNat
    (subsetSumSwap S (Equiv.natSumNatEquivNat.symm (2 * n))) = _
  rw [← show Equiv.natSumNatEquivNat (Sum.inl n) = 2 * n by rfl]
  rw [Equiv.symm_apply_apply]
  rw [subsetSumSwap_apply, subsetSumSwapFn_inl_of_not_mem S n h]

/-- G-121(E) computation API: membership makes `σ_S` send an odd input to its even mate. -/
theorem subsetAdjacentSwap_odd_of_mem (S : Set Nat) (n : Nat)
    (h : n ∈ S) : subsetAdjacentSwap S (2 * n + 1) = 2 * n := by
  classical
  change Equiv.natSumNatEquivNat
    (subsetSumSwap S (Equiv.natSumNatEquivNat.symm (2 * n + 1))) = _
  rw [← show Equiv.natSumNatEquivNat (Sum.inr n) = 2 * n + 1 by rfl]
  rw [Equiv.symm_apply_apply]
  rw [subsetSumSwap_apply, subsetSumSwapFn_inr_of_mem S n h]
  rfl

/-- G-121(E) computation API: nonmembership makes `σ_S` fix an odd input. -/
theorem subsetAdjacentSwap_odd_of_not_mem (S : Set Nat) (n : Nat)
    (h : n ∉ S) : subsetAdjacentSwap S (2 * n + 1) = 2 * n + 1 := by
  classical
  change Equiv.natSumNatEquivNat
    (subsetSumSwap S (Equiv.natSumNatEquivNat.symm (2 * n + 1))) = _
  rw [← show Equiv.natSumNatEquivNat (Sum.inr n) = 2 * n + 1 by rfl]
  rw [Equiv.symm_apply_apply]
  rw [subsetSumSwap_apply, subsetSumSwapFn_inr_of_not_mem S n h]

/-- The target's required evaluation detects membership in `S` exactly. -/
theorem subsetAdjacentSwap_even_eq_odd_iff (S : Set Nat) (n : Nat) :
    subsetAdjacentSwap S (2 * n) = 2 * n + 1 ↔ n ∈ S := by
  classical
  by_cases h : n ∈ S
  · exact ⟨fun _ => h, fun _ => subsetAdjacentSwap_even_of_mem S n h⟩
  · constructor
    · intro heq
      rw [subsetAdjacentSwap_even_of_not_mem S n h] at heq
      exact ((Nat.ne_of_lt (Nat.lt_succ_self (2 * n))) heq).elim
    · exact fun hmem => (h hmem).elim

/-- The fixed all-true semantic object is invariant under every `σ_S`. -/
theorem natSubsetSwap_extracts_iff (S : Set Nat)
    (source : natSwapCode.doctrine.Source) (atom : natSwapCarrier.Atom) :
    natSwapCode.toSemantic.doctrine.extracts source (subsetAdjacentSwap S atom) ↔
      natSwapCode.toSemantic.doctrine.extracts source atom := by
  simp only [natSwapCode_extracts]

/-- Identity source map and `σ_S` define the semantic endomorphism `u_S.hom`. -/
noncomputable def natSubsetSwapSemanticHom (S : Set Nat) :
    natSwapCode.toSemantic ⟶ natSwapCode.toSemantic where
  doctrineHom :=
    { sourceMap := id
      atomEquiv := subsetAdjacentSwap S
      normalize_eq := by intro; rfl
      extraction_iff := by
        intro source atom
        simpa only [id_eq] using natSubsetSwap_extracts_iff S source atom }
  source_eq := rfl

/-- The inverse semantic arrow uses the inverse permutation of `σ_S`. -/
noncomputable def natSubsetSwapSemanticInv (S : Set Nat) :
    natSwapCode.toSemantic ⟶ natSwapCode.toSemantic where
  doctrineHom :=
    { sourceMap := id
      atomEquiv := (subsetAdjacentSwap S).symm
      normalize_eq := by intro; rfl
      extraction_iff := by
        intro source atom
        simp only [natSwapCode_extracts] }
  source_eq := rfl

/-- G-121(E) computation API: `simp` exposes the helper hom's source map as identity. -/
@[simp] theorem natSubsetSwapSemanticHom_sourceMap (S : Set Nat) :
    (natSubsetSwapSemanticHom S).doctrineHom.sourceMap = id := rfl

/-- G-121(E) computation API: `simp` exposes the helper hom's Atom map as `σ_S`. -/
@[simp] theorem natSubsetSwapSemanticHom_atomEquiv (S : Set Nat) :
    (natSubsetSwapSemanticHom S).doctrineHom.atomEquiv = subsetAdjacentSwap S := rfl

/-- G-121(E) computation API: `simp` exposes the helper inverse's source map as identity. -/
@[simp] theorem natSubsetSwapSemanticInv_sourceMap (S : Set Nat) :
    (natSubsetSwapSemanticInv S).doctrineHom.sourceMap = id := rfl

/-- G-121(E) computation API: `simp` exposes the helper inverse's Atom map as `σ_S⁻¹`. -/
@[simp] theorem natSubsetSwapSemanticInv_atomEquiv (S : Set Nat) :
    (natSubsetSwapSemanticInv S).doctrineHom.atomEquiv =
      (subsetAdjacentSwap S).symm := rfl

/-- G-121(E)'s subset-indexed semantic automorphism `u_S`. -/
noncomputable def natSubsetSemanticAut (S : Set Nat) :
    natSwapCode.toSemantic ≅ natSwapCode.toSemantic where
  hom := natSubsetSwapSemanticHom S
  inv := natSubsetSwapSemanticInv S
  hom_inv_id := by
    apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · rfl
    · apply Equiv.ext
      intro atom
      exact (subsetAdjacentSwap S).apply_symm_apply atom
  inv_hom_id := by
    apply ExtInstHom.ext
    apply ExactDoctrineHom.ext
    · rfl
    · apply Equiv.ext
      intro atom
      exact (subsetAdjacentSwap S).symm_apply_apply atom

/-- G-121(E) computation API: `simp` exposes `u_S.hom`'s source map as identity. -/
@[simp] theorem natSubsetSemanticAut_hom_sourceMap (S : Set Nat) :
    (natSubsetSemanticAut S).hom.doctrineHom.sourceMap = id := rfl

/-- G-121(E) computation API: `simp` exposes `u_S.hom`'s Atom map as `σ_S`. -/
@[simp] theorem natSubsetSemanticAut_hom_atomEquiv (S : Set Nat) :
    (natSubsetSemanticAut S).hom.doctrineHom.atomEquiv = subsetAdjacentSwap S := rfl

/-- Different subsets give different semantic automorphisms. -/
theorem natSubsetSemanticAut_injective :
    Function.Injective natSubsetSemanticAut := by
  intro S T heq
  have hperm : subsetAdjacentSwap S = subsetAdjacentSwap T :=
    congrArg (fun iso => iso.hom.doctrineHom.atomEquiv) heq
  apply Set.ext
  intro n
  rw [← subsetAdjacentSwap_even_eq_odd_iff S n,
    ← subsetAdjacentSwap_even_eq_odd_iff T n, hperm]

/-- Package the subset family as an injection into `Aut(X_*)`. -/
noncomputable def natSubsetSemanticAutEmbedding :
    Set Nat ↪ (natSwapCode.toSemantic ≅ natSwapCode.toSemantic) where
  toFun := natSubsetSemanticAut
  inj' := natSubsetSemanticAut_injective

/-- G-121(E) computation API: `simp` exposes the embedding value as `u_S`. -/
@[simp] theorem natSubsetSemanticAutEmbedding_apply (S : Set Nat) :
    natSubsetSemanticAutEmbedding S = natSubsetSemanticAut S := rfl

#assert_standard_axioms_only AAT.AG.FiniteDecoderRepresentability

end AAT.AG.FiniteDecoderRepresentability
