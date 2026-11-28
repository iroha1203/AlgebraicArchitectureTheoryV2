import Formal.SHIGURE.Part2.Schemes.Effective.FppfStack
import Mathlib.AlgebraicGeometry.Cover.Sigma

/-! # The rational two-component fppf cover

The affine charts are the two rational factors of `ℚ × ℚ`. -/

namespace SHIGURE.SchemeDescent.EffectiveExamples

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

/-- The affine base has two disjoint rational components. -/
abbrev rationalProduct : CommRingCat := .of (Bool → ℚ)

private def rationalRings (_ : Bool) : CommRingCat := .of ℚ

/-- The inclusion of one actual rational component into the product spectrum. -/
def rationalComponent (i : Bool) : Spec (rationalRings i) ⟶ Spec rationalProduct :=
  Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i))

private theorem rationalComponent_exists (x : Spec rationalProduct) :
    ∃ i, x ∈ Set.range (rationalComponent i) := by
  obtain ⟨z, hz⟩ := (sigmaSpec rationalRings).surjective x
  obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk (fun i => Spec (rationalRings i))).surjective z
  rw [sigmaMk_mk, ← Scheme.Hom.comp_apply, ι_sigmaSpec] at hz
  exact ⟨i, y, hz⟩

/-- The two actual affine spectra form an fppf covering family. -/
def rationalAffineCover : Scheme.AffineCover FppfComponent (Spec rationalProduct) where
  I₀ := Bool
  X := rationalRings
  f := rationalComponent
  idx x := (rationalComponent_exists x).choose
  covers x := (rationalComponent_exists x).choose_spec
  map_prop i := by
    have opened : IsOpenImmersion (rationalComponent i) :=
      inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun _ : Bool => ℚ) i))))
    exact ⟨inferInstance, inferInstance⟩

end

end SHIGURE.SchemeDescent.EffectiveExamples
