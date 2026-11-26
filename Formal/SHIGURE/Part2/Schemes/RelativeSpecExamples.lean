import Formal.SHIGURE.Part2.Schemes.RelativeSpecAlgebraBaseChange
import Mathlib.RingTheory.Int.Basic

/-! # A failure of the localization condition for algebra sheaves -/

namespace SHIGURE.SchemeDescent.RelativeSpecExamples

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

private abbrev intRing := CommRingCat.of ℤ
private abbrev intScheme := Spec intRing

private def pointAtTwo : PrimeSpectrum ℤ :=
  ⟨Ideal.span {2}, (Ideal.span_singleton_prime (by decide : (2 : ℤ) ≠ 0)).mpr
    (Int.prime_iff_natAbs_prime.mpr Nat.prime_two)⟩

private def stalkToRat : intScheme.presheaf.stalk pointAtTwo ⟶ CommRingCat.of ℚ := by
  change (Spec.structureSheaf ℤ).presheaf.stalk pointAtTwo ⟶ _
  let S := (Spec.structureSheaf ℤ).presheaf.stalk pointAtTwo
  letI : Algebra ℤ S := StructureSheaf.stalkAlgebra ℤ pointAtTwo
  haveI : IsLocalization pointAtTwo.asIdeal.primeCompl S := StructureSheaf.IsLocalization.to_stalk ℤ pointAtTwo
  refine CommRingCat.ofHom (IsLocalization.lift (S := S) (M := pointAtTwo.asIdeal.primeCompl)
    (g := Int.castRingHom ℚ) ?_)
  intro n
  have nonzero : n.val ≠ 0 := fun same => n.property (same ▸ Ideal.zero_mem _)
  exact isUnit_iff_ne_zero.mpr (by
    change (n.val : ℚ) ≠ 0
    exact_mod_cast nonzero)

/-- The algebra sheaf with value ℚ at the point (2) and no sections off that point except zero. -/
def skyscraperAlgebraAtTwo : Under intScheme.sheaf := by
  classical
  let x : (intScheme : TopCat) := pointAtTwo
  let F : (intScheme : TopCat).Presheaf CommRingCat := intScheme.presheaf
  let A := CommRingCat.of ℚ
  let read : F.stalk x ⟶ A := stalkToRat
  exact Under.mk (Y := skyscraperSheaf x A)
    ⟨StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf x read⟩

/-- Localizing this algebra's global ring at 2 cannot give its sections on the principal open D(2). -/
theorem skyscraperAlgebraAtTwo_not_localization :
    let F : (intScheme : TopCat).Presheaf CommRingCat := skyscraperAlgebraAtTwo.right.val
    let r : Γ(intScheme, ⊤) := 2
    let action : Γ(intScheme, ⊤) ⟶ F.obj (.op ⊤) := skyscraperAlgebraAtTwo.hom.val.app (.op ⊤)
    letI : Algebra (F.obj (.op ⊤)) (F.obj (.op (intScheme.basicOpen r))) :=
      (F.map (homOfLE (intScheme.basicOpen_le r)).op).hom.toAlgebra
    ¬ IsLocalization.Away (action r) (F.obj (.op (intScheme.basicOpen r))) := by
  classical
  let F : (intScheme : TopCat).Presheaf CommRingCat := skyscraperAlgebraAtTwo.right.val
  let r : Γ(intScheme, ⊤) := 2
  let W := intScheme.basicOpen r
  let action : Γ(intScheme, ⊤) ⟶ F.obj (.op ⊤) := skyscraperAlgebraAtTwo.hom.val.app (.op ⊤)
  letI : Algebra (F.obj (.op ⊤)) (F.obj (.op W)) :=
    (F.map (homOfLE (intScheme.basicOpen_le r)).op).hom.toAlgebra
  change ¬ IsLocalization.Away (action r) (F.obj (.op W))
  have outside : pointAtTwo ∉ W := by
    change pointAtTwo ∉ intScheme.basicOpen (2 : Γ(intScheme, ⊤))
    rw [basicOpen_eq_of_affine', map_ofNat]
    exact fun h => h (Ideal.subset_span (by simp))
  have global : F.obj (.op ⊤) = CommRingCat.of ℚ := by
    simp only [F, skyscraperAlgebraAtTwo, Under.mk_right, skyscraperSheaf,
      skyscraperPresheaf_obj, Opens.mem_top, if_true]
  have localRing : F.obj (.op W) = terminal CommRingCat := by
    simp only [F, skyscraperAlgebraAtTwo, Under.mk_right, skyscraperSheaf,
      skyscraperPresheaf_obj, if_neg outside]
  haveI : Nontrivial (F.obj (.op ⊤)) := global.symm ▸ (inferInstance : Nontrivial ℚ)
  haveI : Subsingleton (F.obj (.op W)) := localRing.symm ▸
    CommRingCat.subsingleton_of_isTerminal terminalIsTerminal
  have unit : IsUnit (action r) := by
    change IsUnit (action.hom (2 : Γ(intScheme, ⊤)))
    rw [map_ofNat]
    change IsUnit (2 : F.obj (.op ⊤))
    rw [global]
    exact isUnit_iff_ne_zero.mpr (by norm_num)
  intro localization
  letI : IsLocalization.Away (action r) (F.obj (.op W)) := localization
  have injective := IsLocalization.injective
    (M := Submonoid.powers (action r)) (F.obj (.op W))
    (Submonoid.powers_le.mpr unit.mem_nonZeroDivisors)
  exact zero_ne_one (injective (Subsingleton.elim _ _))

end

end SHIGURE.SchemeDescent.RelativeSpecExamples
