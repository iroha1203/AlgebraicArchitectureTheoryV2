import ResearchLean.AG.ComparisonInformationLoss.KaroubiRestriction
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.Tactic.FinCases

/-!
# Finite witnesses for Karoubi restriction information loss

This file supplies the two fixed three-point examples required by G-120(C) in
the category of finite sets. The first exhibits failure of reflection for the
constant-zero idempotent. The second exhibits a compatible automorphism of the
two-point idempotent image that has no lift to a raw three-point permutation.

Implementation notes: the image swap in the second example is constructed as
an actual automorphism in the Karoubi envelope, not as a permutation of the
raw three-point carrier. Its lift obstruction is proved for every possible raw
centralizing automorphism by evaluating the sandwich at `1` and the
centralizer equation at `2`; a preselected list of permutations is not used.
-/

open CategoryTheory
open CategoryTheory.Idempotents

namespace AAT.AG.ComparisonInformationLoss.KaroubiRestrictionFiniteWitness

/-- The fixed three-point object in the category of finite sets. -/
abbrev ThreePoint : FintypeCat := FintypeCat.of (Fin 3)

/-! ## Constant-zero reflection failure -/

/-- The constant-zero idempotent in the first fixed example. -/
def constantZero : ThreePoint ⟶ ThreePoint :=
  FintypeCat.homMk (fun _ => 0)

/-- The constant-zero map evaluates to `0` at every point. -/
@[simp]
theorem constantZero_apply (x : Fin 3) : constantZero x = 0 := rfl

/-- The constant-zero endomorphism is idempotent. -/
theorem constantZero_idempotent : constantZero ≫ constantZero = constantZero := by
  apply FintypeCat.hom_ext
  intro x
  rfl

/-- The raw source change swapping `1` and `2`. -/
noncomputable def swapTwelveAut : Aut ThreePoint :=
  FintypeCat.equivEquivIso (Equiv.swap (1 : Fin 3) 2)

/-- Swapping `1` and `2` centralizes the constant-zero idempotent. -/
theorem swapTwelve_centralizes_constantZero :
    swapTwelveAut.hom ≫ constantZero = constantZero ≫ swapTwelveAut.hom := by
  apply FintypeCat.hom_ext
  intro x
  fin_cases x <;> decide

/-- The endpoint pair `(swap(1,2), id)`, packaged as an element of `H`. -/
noncomputable def constantZeroCentralizingPair :
    centralizingEndpointSubgroup ThreePoint ThreePoint constantZero constantZero :=
  ⟨(swapTwelveAut, 1), swapTwelve_centralizes_constantZero, by simp⟩

/-- The fixed raw endpoint pair belongs to the centralizer product `H`. -/
theorem constantZeroCentralizingPair_mem_H :
    (constantZeroCentralizingPair : Aut ThreePoint × Aut ThreePoint) ∈
      centralizingEndpointSubgroup ThreePoint ThreePoint constantZero constantZero :=
  constantZeroCentralizingPair.property

/-- The raw comparison equation fails at `1`, where its two sides evaluate to
`2` and `1`. -/
theorem constantZeroCentralizingPair_raw_mismatch :
    swapTwelveAut.hom ≫ 𝟙 ThreePoint ≠
      𝟙 ThreePoint ≫ (1 : Aut ThreePoint).hom := by
  intro hsquare
  have hpoint := ConcreteCategory.congr_hom hsquare (1 : Fin 3)
  change (2 : Fin 3) = 1 at hpoint
  exact (by decide : (2 : Fin 3) ≠ 1) hpoint

/-- The fixed raw endpoint pair does not preserve the identity comparison. -/
theorem constantZeroCentralizingPair_not_mem_GammaZero :
    constantZeroCentralizingPair ∉
      centralizingCompatibleSubgroup (𝟙 ThreePoint) constantZero constantZero := by
  intro h
  exact constantZeroCentralizingPair_raw_mismatch h

/-- Sandwiching collapses the mismatched raw pair to a compatible image-side
pair. -/
theorem constantZero_restriction_mem_GammaImage :
    idempotentEndpointRestrictionHom ThreePoint ThreePoint
        constantZero constantZero constantZero_idempotent constantZero_idempotent
        constantZeroCentralizingPair ∈
      comparisonAutomorphismSubgroup
        (idempotentImageComparison (𝟙 ThreePoint) constantZero constantZero
          constantZero_idempotent constantZero_idempotent (by simp)) := by
  change
    (idempotentEndpointRestrictionHom ThreePoint ThreePoint
      constantZero constantZero constantZero_idempotent constantZero_idempotent
      constantZeroCentralizingPair).1.hom ≫
        idempotentImageComparison (𝟙 ThreePoint) constantZero constantZero
          constantZero_idempotent constantZero_idempotent (by simp) =
      idempotentImageComparison (𝟙 ThreePoint) constantZero constantZero
          constantZero_idempotent constantZero_idempotent (by simp) ≫
        (idempotentEndpointRestrictionHom ThreePoint ThreePoint
          constantZero constantZero constantZero_idempotent constantZero_idempotent
          constantZeroCentralizingPair).2.hom
  apply Karoubi.Hom.ext
  simp only [Karoubi.comp_f]
  rw [idempotentEndpointRestrictionHom_fst_hom_f,
    idempotentEndpointRestrictionHom_snd_hom_f,
    idempotentImageComparison_f]
  apply FintypeCat.hom_ext
  intro x
  rfl

/-- The first fixed example refutes reflection: an element of `H` maps into
`Gamma_a` but does not lie in `Gamma_0`. -/
theorem constantZero_reflection_fails :
    (comparisonAutomorphismSubgroup
        (idempotentImageComparison (𝟙 ThreePoint) constantZero constantZero
          constantZero_idempotent constantZero_idempotent (by simp))).comap
        (idempotentEndpointRestrictionHom ThreePoint ThreePoint
          constantZero constantZero constantZero_idempotent constantZero_idempotent) ≠
      centralizingCompatibleSubgroup (𝟙 ThreePoint) constantZero constantZero := by
  intro hreflection
  apply constantZeroCentralizingPair_not_mem_GammaZero
  rw [← hreflection]
  exact constantZero_restriction_mem_GammaImage

/-! ## Unequal-fiber lift obstruction -/

/-- The second fixed idempotent: `0 ↦ 0`, `1 ↦ 1`, `2 ↦ 1`. -/
def unequalFiberFold : ThreePoint ⟶ ThreePoint :=
  FintypeCat.homMk (fun x => if x = 0 then 0 else 1)

/-- Pointwise evaluation formula for the unequal-fiber fold. -/
@[simp]
theorem unequalFiberFold_apply (x : Fin 3) :
    unequalFiberFold x = (if x = 0 then 0 else 1) := rfl

/-- The unequal-fiber fold is idempotent. -/
theorem unequalFiberFold_idempotent :
    unequalFiberFold ≫ unequalFiberFold = unequalFiberFold := by
  apply FintypeCat.hom_ext
  intro x
  fin_cases x <;> decide

/-- The zero fiber of the unequal-fiber fold is the singleton `{0}`. -/
theorem unequalFiberFold_eq_zero_iff (x : Fin 3) :
    unequalFiberFold x = 0 ↔ x = 0 := by
  fin_cases x <;> decide

/-- For the identity raw comparison, the normalized comparison `a` is exactly
the fold idempotent, as required by the fixed example. -/
theorem unequalFiber_imageComparison_f :
    (idempotentImageComparison (𝟙 ThreePoint) unequalFiberFold unequalFiberFold
      unequalFiberFold_idempotent unequalFiberFold_idempotent (by simp)).f =
        unequalFiberFold := by
  rw [idempotentImageComparison_f]
  simpa using unequalFiberFold_idempotent

/-- The image map exchanging `0` and `1`; raw point `2` has the same value as
raw point `1` because both represent the second image point. -/
def unequalFiberImageSwap : ThreePoint ⟶ ThreePoint :=
  FintypeCat.homMk (fun x => if x = 0 then 1 else 0)

/-- Pointwise evaluation formula for the swap of the two image points. -/
@[simp]
theorem unequalFiberImageSwap_apply (x : Fin 3) :
    unequalFiberImageSwap x = (if x = 0 then 1 else 0) := rfl

/-- The two-point image swap as a genuine self-inverse automorphism of the
Karoubi object. -/
def unequalFiberImageSwapAut :
    Aut (idempotentKaroubiObject ThreePoint unequalFiberFold
      unequalFiberFold_idempotent) where
  hom :=
    { f := unequalFiberImageSwap
      comm := by
        apply FintypeCat.hom_ext
        intro x
        fin_cases x <;> rfl }
  inv :=
    { f := unequalFiberImageSwap
      comm := by
        apply FintypeCat.hom_ext
        intro x
        fin_cases x <;> rfl }
  hom_inv_id := by
    apply Karoubi.Hom.ext
    apply FintypeCat.hom_ext
    intro x
    fin_cases x <;> rfl
  inv_hom_id := by
    apply Karoubi.Hom.ext
    apply FintypeCat.hom_ext
    intro x
    fin_cases x <;> rfl

/-- The fixed compatible pair that swaps the two image points at both
endpoints. -/
def unequalFiberImageSwapPair :
    comparisonAutomorphismSubgroup
      (idempotentImageComparison (𝟙 ThreePoint) unequalFiberFold unequalFiberFold
        unequalFiberFold_idempotent unequalFiberFold_idempotent (by simp)) :=
  ⟨(unequalFiberImageSwapAut, unequalFiberImageSwapAut), by
    apply Karoubi.Hom.ext
    simp only [Karoubi.comp_f]
    rw [unequalFiber_imageComparison_f]
    apply FintypeCat.hom_ext
    intro x
    fin_cases x <;> rfl⟩

/-- The underlying map of an automorphism in `FintypeCat` is injective. -/
theorem fintypeAut_hom_injective {X : FintypeCat} (b : Aut X) :
    Function.Injective b.hom := by
  intro x y h
  have hinv := congrArg (fun z => b.inv z) h
  simpa only [FintypeCat.hom_inv_id_apply] using hinv

/-- No raw centralizing permutation can restrict to the image swap. Evaluating
the sandwich at `1` forces `b(1)=0`; evaluating centrality at `2` then forces
`b(2)=0`, contradicting injectivity. -/
theorem unequalFiberImageSwapPair_not_mem_restrictionRange :
    ((unequalFiberImageSwapPair :
      comparisonAutomorphismSubgroup
        (idempotentImageComparison (𝟙 ThreePoint) unequalFiberFold unequalFiberFold
          unequalFiberFold_idempotent unequalFiberFold_idempotent (by simp))) :
        Aut (idempotentKaroubiObject ThreePoint unequalFiberFold
          unequalFiberFold_idempotent) ×
          Aut (idempotentKaroubiObject ThreePoint unequalFiberFold
            unequalFiberFold_idempotent)) ∉
      (idempotentEndpointRestrictionHom ThreePoint ThreePoint
        unequalFiberFold unequalFiberFold unequalFiberFold_idempotent
        unequalFiberFold_idempotent).range := by
  rintro ⟨pair, hpair⟩
  have hsource := congrArg
    (fun q : Aut (idempotentKaroubiObject ThreePoint unequalFiberFold
        unequalFiberFold_idempotent) ×
        Aut (idempotentKaroubiObject ThreePoint unequalFiberFold
          unequalFiberFold_idempotent) => q.1.hom.f) hpair
  change
    (idempotentEndpointRestrictionHom ThreePoint ThreePoint unequalFiberFold
      unequalFiberFold unequalFiberFold_idempotent unequalFiberFold_idempotent
      pair).1.hom.f = unequalFiberImageSwap at hsource
  rw [idempotentEndpointRestrictionHom_fst_hom_f] at hsource
  have hone := ConcreteCategory.congr_hom hsource (1 : Fin 3)
  change unequalFiberFold (pair.1.1.hom (unequalFiberFold 1)) =
    unequalFiberImageSwap 1 at hone
  have hbOne : pair.1.1.hom (1 : Fin 3) = 0 :=
    (unequalFiberFold_eq_zero_iff _).mp (by simpa using hone)
  have hcentral := ConcreteCategory.congr_hom pair.property.1 (2 : Fin 3)
  change unequalFiberFold (pair.1.1.hom 2) =
    pair.1.1.hom (unequalFiberFold 2) at hcentral
  change unequalFiberFold (pair.1.1.hom 2) = pair.1.1.hom 1 at hcentral
  rw [hbOne] at hcentral
  have hbTwo : pair.1.1.hom (2 : Fin 3) = 0 :=
    (unequalFiberFold_eq_zero_iff _).mp hcentral
  have hequal : pair.1.1.hom (1 : Fin 3) = pair.1.1.hom 2 := by
    rw [hbOne, hbTwo]
  have : (1 : Fin 3) = 2 := fintypeAut_hom_injective pair.1.1 hequal
  exact (by decide : (1 : Fin 3) ≠ 2) this

/-- The compatible image swap is not even in the image of `r : H → ...`, so
it has no raw lift among all centralizing endpoint pairs. -/
theorem unequalFiberImageSwapPair_not_mem_compatibleImage :
    ((unequalFiberImageSwapPair :
      comparisonAutomorphismSubgroup
        (idempotentImageComparison (𝟙 ThreePoint) unequalFiberFold unequalFiberFold
          unequalFiberFold_idempotent unequalFiberFold_idempotent (by simp))) :
        Aut (idempotentKaroubiObject ThreePoint unequalFiberFold
          unequalFiberFold_idempotent) ×
          Aut (idempotentKaroubiObject ThreePoint unequalFiberFold
            unequalFiberFold_idempotent)) ∉
      Subgroup.map
        (idempotentEndpointRestrictionHom ThreePoint ThreePoint
          unequalFiberFold unequalFiberFold unequalFiberFold_idempotent
          unequalFiberFold_idempotent)
        (centralizingCompatibleSubgroup (𝟙 ThreePoint) unequalFiberFold
          unequalFiberFold) := by
  rintro ⟨pair, _hmem, hpair⟩
  exact unequalFiberImageSwapPair_not_mem_restrictionRange ⟨pair, hpair⟩

/-- The existing C.3 lift fiber over the fixed image swap is empty. -/
theorem unequalFiberImageSwapPair_has_no_compatibleLift :
    ¬ Nonempty
      (IdempotentCompatibleLiftFiber (𝟙 ThreePoint) unequalFiberFold
        unequalFiberFold unequalFiberFold_idempotent unequalFiberFold_idempotent
        (by simp) unequalFiberImageSwapPair) := by
  intro h
  apply unequalFiberImageSwapPair_not_mem_compatibleImage
  exact (nonempty_idempotentCompatibleLiftFiber_iff_mem_map
    (𝟙 ThreePoint) unequalFiberFold unequalFiberFold
    unequalFiberFold_idempotent unequalFiberFold_idempotent (by simp)
    unequalFiberImageSwapPair).mp h

#assert_standard_axioms_only AAT.AG.ComparisonInformationLoss.KaroubiRestrictionFiniteWitness

end AAT.AG.ComparisonInformationLoss.KaroubiRestrictionFiniteWitness
