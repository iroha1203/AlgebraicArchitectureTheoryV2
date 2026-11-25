import Formal.SHIGURE.Part2.Profiles.Colimit
import Formal.SHIGURE.Part2.Profiles.SchemeComposition
import Mathlib.Data.Fintype.EquivFin

/-!
# Support profiles of copying maps

Definition 4.5 and Theorem 4.6 give the affine support charts and their
filtered recovery and composition. Example 4.7 checks the infinite identity
and the failure of the zero row over the integers.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace SHIGURE.Copying.SupportProfile

/-- Example 4.7. The identity of the natural numbers is represented on the singleton profiles. -/
theorem natIdentity_represented_on_singletons :
    ∃ p : specOver ℤ ⟶ (identityProfile ℕ).chart ℤ,
      (affinePointCocone ℤ ℤ ℕ ℕ).ι.app (identityProfile ℕ) p =
        CoalgHom.id ℤ (CopyCoalgebra ℤ ℕ) := by
  refine ⟨(affinePointRowsEquiv (k := ℤ) (identityProfile ℕ)).symm (identityRows ℤ ℕ), ?_⟩
  change (coalgebraRowsEquiv ℕ ℕ).symm
    ((identityProfile ℕ).affinePointRowsEquiv
      ((identityProfile ℕ).affinePointRowsEquiv.symm (identityRows ℤ ℕ))).val = _
  rw [Equiv.apply_symm_apply]
  exact mapOfRows_identityRows ℤ ℕ

/-- Example 4.7. No single finite output set supports all rows of the identity over the integers. -/
theorem natIdentity_no_common_output :
    ¬ ∃ S : Finset ℕ, ∀ n : ℕ,
      (((coalgebraRowsEquiv ℕ ℕ) (CoalgHom.id ℤ (CopyCoalgebra ℤ ℕ))).val n).support ⊆ S := by
  rintro ⟨S, hS⟩
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset S
  apply hn
  apply hS n
  rw [coalgebraRowsEquiv_id, Finsupp.mem_support_iff, Finsupp.single_eq_same]
  exact one_ne_zero

/-- Example 4.7. The integer zero row satisfies all idempotence and orthogonality
tests, and fails the sum equation. -/
theorem zeroRow_orthogonal_not_complete :
    (∀ y : ℕ, IsIdempotentElem ((0 : CopyCoalgebra ℤ ℕ) y)) ∧
      (∀ y z : ℕ, y ≠ z → (0 : CopyCoalgebra ℤ ℕ) y * (0 : CopyCoalgebra ℤ ℕ) z = 0) ∧
      (0 : CopyCoalgebra ℤ ℕ).sum (fun _ r => r) ≠ 1 := by
  simp [IsIdempotentElem]

end SHIGURE.Copying.SupportProfile
