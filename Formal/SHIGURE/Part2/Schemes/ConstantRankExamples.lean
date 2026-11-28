import Formal.SHIGURE.Part2.Schemes.ConstantRank
import Formal.SHIGURE.Part2.Schemes.FiniteLocallyFreeExamples

/-! # Affine comparison and witnesses for prescribed rank

The coefficient criterion identifies Definition 6.1 on a spectrum with the
existing finite locally free module condition and its stalk ranks. Trivial
bundles supply every rank, including zero. The rank-one rational bundle
fails the rank-zero condition, so the predicate detects the specified rank.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Scheme.Modules TopologicalSpace
open SHIGURE.CoefficientDescent

noncomputable section

universe u

variable {R : CommRingCat.{u}}

/-- Rank base change for the actual coefficient functor used by the affine
comparison in Definition 6.1. The B.5 finite local freeness assumption
supplies finite presentation and flatness. -/
private theorem affine_rank_extendScalars {S : CommRingCat.{u}} (f : R ⟶ S)
    (M : ModuleCat.{u} R) (finite : FiniteLocallyFree R M) (p : PrimeSpectrum S) :
    Module.rankAtStalk ((ModuleCat.extendScalars f.hom).obj M) p =
      Module.rankAtStalk M (p.comap f.hom) := by
  letI : Algebra R S := f.hom.toAlgebra
  letI := finite.finitePresentation
  letI := finite.flat
  exact (congrFun (Module.rankAtStalk_eq_of_equiv
    (extendScalarsTensorIso (B := S) M).toLinearEquiv) p).trans
      (Module.rankAtStalk_baseChange (R := R) (M := M) p)

/-- On the whole affine chart, the rank of a finite locally free associated
sheaf is exactly its coefficient module rank. The canonical isomorphism
between the original ring and global sections supplies the comparison. -/
theorem affineTilde_on_top_constantRank_iff (M : ModuleCat.{u} R)
    (finite : FiniteLocallyFree R M) (n : ℕ) :
    HasConstantRankOn ((tilde.functor R).obj M) (isAffineOpen_top (Spec R)) n ↔
      ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = n := by
  let h := isAffineOpen_top (Spec R)
  let e := Scheme.ΓSpecIso R
  let P := (ModuleCat.extendScalars e.inv.hom).obj M
  have fromSpec : h.fromSpec = Spec.map e.inv := by
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  let comparison : (tilde.functor Γ(Spec R, ⊤)).obj P ≅ ((tilde.functor R).obj M).restrict h.fromSpec :=
    ((tildeRestrictIso e.inv).app M).symm ≪≫
      (restrictFunctorCongr fromSpec.symm).app ((tilde.functor R).obj M)
  rw [hasConstantRankOn_iff n P comparison]
  constructor
  · intro ranks p
    have value := (affine_rank_extendScalars e.inv M finite (p.comap e.hom.hom)).symm.trans
      (ranks (p.comap e.hom.hom))
    have point : (p.comap e.hom.hom).comap e.inv.hom = p := by
      change (Spec.map e.hom ≫ Spec.map e.inv) p = p
      rw [← Spec.map_comp, e.inv_hom_id, Spec.map_id]
      rfl
    exact (congrArg (fun q : PrimeSpectrum R => Module.rankAtStalk M q) point).symm.trans value
  · intro ranks p
    exact (affine_rank_extendScalars e.inv M finite p).trans (ranks _)

/-- The finite locally free rank condition of Definition 6.1 on a spectrum
is the coefficient finite local freeness condition of B.5 together with
constant `Module.rankAtStalk`. This is an equivalence for arbitrary rings. -/
theorem affineTilde_finiteLocallyFreeOfRank_iff (M : ModuleCat.{u} R) (n : ℕ) :
    IsFiniteLocallyFreeOfRank ((tilde.functor R).obj M) n ↔
      FiniteLocallyFree R M ∧ ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = n := by
  constructor
  · intro h
    have finite := (affineTilde_finiteLocallyFree_iff M).mp h.1
    exact ⟨finite, (affineTilde_on_top_constantRank_iff M finite n).mp
      (h.2 ⟨⊤, isAffineOpen_top _⟩)⟩
  · rintro ⟨finite, ranks⟩
    apply IsFiniteLocallyFreeOfRank.of_affineCover
      (fun _ : ULift.{u} Unit => ⟨⊤, isAffineOpen_top (Spec R)⟩) (by simp)
    · intro _
      exact (affineTilde_on_top_finiteLocallyFree_iff M).mpr finite
    · intro _
      exact (affineTilde_on_top_constantRank_iff M finite n).mpr ranks

namespace Examples

/-- Every trivial rank-`n` affine bundle has the prescribed rank in
Definition 6.1, over any ring and including `n = 0`. -/
theorem finiteFreeAffine_isFiniteLocallyFreeOfRank (R : CommRingCat.{u}) (n : ℕ) :
    IsFiniteLocallyFreeOfRank ((tilde.functor R).obj (finiteFreeModule R n)) n := by
  apply (affineTilde_finiteLocallyFreeOfRank_iff _ n).mpr
  refine ⟨(affineTilde_finiteLocallyFree_iff _).mp (finiteFreeAffine_isFiniteLocallyFree R n), ?_⟩
  intro p
  letI : Nontrivial R := p.nontrivial
  change Module.rankAtStalk (R := R) (Fin n → R) p = n
  simp [Module.rankAtStalk_eq_finrank_of_free]

/-- The rational rank-one trivial bundle fails rank zero, verifying that
the prescribed-rank predicate is not simply finite local freeness. -/
theorem rationalRankOne_not_rankZero :
    ¬ IsFiniteLocallyFreeOfRank
      ((tilde.functor (CommRingCat.of ℚ)).obj (finiteFreeModule (CommRingCat.of ℚ) 1)) 0 := by
  intro h
  let p : PrimeSpectrum ℚ := ⟨⊥, Ideal.isPrime_bot⟩
  have wrong := (affineTilde_finiteLocallyFreeOfRank_iff _ 0).mp h |>.2 p
  have right := (affineTilde_finiteLocallyFreeOfRank_iff _ 1).mp
    (finiteFreeAffine_isFiniteLocallyFreeOfRank (CommRingCat.of ℚ) 1) |>.2 p
  exact Nat.one_ne_zero (right.symm.trans wrong)

/-- Over the zero ring there are no coefficient primes, so a trivial
finite bundle satisfies every prescribed rank condition. Definition 6.1
therefore retains the mathematically required empty-spectrum behavior. -/
theorem finiteFreeAffine_all_ranks_of_subsingleton (R : CommRingCat.{u}) [Subsingleton R] (m n : ℕ) :
    IsFiniteLocallyFreeOfRank ((tilde.functor R).obj (finiteFreeModule R m)) n := by
  apply (affineTilde_finiteLocallyFreeOfRank_iff _ n).mpr
  refine ⟨(affineTilde_finiteLocallyFree_iff _).mp (finiteFreeAffine_isFiniteLocallyFree R m), ?_⟩
  intro p
  exact isEmptyElim p

end Examples

end

end SHIGURE.SchemeDescent
