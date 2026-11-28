import Formal.SHIGURE.Part2.Schemes.FiniteFppfProduct
import Formal.SHIGURE.Part2.Schemes.QuasiCoherentZariskiStack
import Formal.SHIGURE.Part2.Schemes.DescentCoveringRefinement

/-! # Morphism descent for the chosen finite affine fppf refinement -/

namespace SHIGURE.SchemeDescent.AffineRefinement

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite

noncomputable section

universe u

variable {A : CommRingCat.{u}} {cover : FppfCover (Spec A)} (refinement : AffineRefinement cover)

private abbrev Q := quasiCoherentModulesPseudofunctor.{u}

set_option maxHeartbeats 600000 in
/-- Morphism descent for the single product cover implies morphism descent for the
affine component family. The product components form a Zariski cover of the source. -/
theorem affineComponents_isPrestackFor
    (effective : Q.IsPrestackFor (Presieve.singleton (Spec.map refinement.productMap))) :
    Q.IsPrestackFor (Sieve.ofArrows refinement.affine.cover.X refinement.affine.cover.f).arrows := by
  let P := Sieve.ofArrows refinement.productCover.X refinement.productCover.f
  let S := Sieve.ofArrows refinement.affine.cover.X refinement.affine.cover.f
  let p := Spec.map refinement.productMap
  letI := quasiCoherentModules_isZariskiStack.{u}
  have smaller : S ≤ P := refinement.toProductCover.sieve₀_le_sieve₀
  have base : Q.IsPrestackFor P.arrows := by
    have singleton : P = Sieve.generate (Presieve.singleton p) := by
      change Sieve.generate (Presieve.ofArrows (fun _ : PUnit => Spec refinement.productRing) (fun _ => p)) = _
      rw [Presieve.ofArrows_pUnit]
    rw [singleton, IsPrestackFor_generate_iff]
    exact effective
  have outer : S.pullback p ∈ Scheme.zariskiTopology _ := by
    have mem : Sieve.ofArrows refinement.productOpenCover.X refinement.productOpenCover.f ∈
        Scheme.zariskiTopology _ :=
      Precoverage.generate_mem_toGrothendieck refinement.productOpenCover.mem₀
    apply Scheme.zariskiTopology.superset_covering _ mem
    rw [Sieve.ofArrows, Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    change S (refinement.productOpenCover.f i ≫ p)
    have factor : refinement.productOpenCover.f i ≫ p = refinement.affine.f i := refinement.toProductCover.w₀ i
    rw [factor]
    exact Sieve.ofArrows_mk _ _ i
  apply isPrestackFor_refining_arrows Q Scheme.zariskiTopology smaller base
  intro Y f hf
  obtain ⟨U, a, _, ⟨i⟩, ha⟩ := hf
  cases i
  have factored : a ≫ p = f := ha
  rw [← factored, Sieve.pullback_comp]
  exact Scheme.zariskiTopology.pullback_stable a outer

end

end SHIGURE.SchemeDescent.AffineRefinement
