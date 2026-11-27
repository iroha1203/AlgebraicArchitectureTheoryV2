import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Formal.SHIGURE.Part2.Descent.Standard
import Formal.SHIGURE.Part2.Schemes.AffineOverlapRingDiagram

/-! # Ring maps across an affine faithfully flat cover -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory TensorProduct SHIGURE.CoefficientDescent

noncomputable section

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.FaithfullyFlat A B]

/-- Faithfully flat scalar extension is injective on coefficients. -/
private theorem scalar_injective : Function.Injective (algebraMap A B) :=
  (RingHom.faithfullyFlat_algebraMap_iff.2
    (inferInstance : Module.FaithfullyFlat A B)).injective

/-- The two actual double-overlap readings agree exactly on the image
of the faithfully flat ring map. -/
theorem affineCover_double_equalizer (b : B) :
    affineDoubleEmbedding A B 0 b = affineDoubleEmbedding A B 1 b ↔
      ∃ a : A, algebraMap A B a = b := by
  constructor
  · intro h
    change b ⊗ₜ[A] (1 : B) = (1 : B) ⊗ₜ[A] b at h
    let t : B ⊗[A] A := b ⊗ₜ[A] (1 : A)
    let D := standardDatum (A := A) (B := B) (M := A)
    have ht : t ∈ D.toCoaction.descended := by
      apply (D.mem_descended_iff t).2
      change b ⊗ₜ[A] ((1 : B) ⊗ₜ[A] (1 : A)) = (1 : B) ⊗ₜ[A] t
      let l := TensorProduct.congr (LinearEquiv.refl A B) (TensorProduct.rid A B)
      apply l.injective
      calc
        _ = b ⊗ₜ[A] (1 : B) := by simp [l]
        _ = (1 : B) ⊗ₜ[A] b := h
        _ = _ := by simp [l, t]
    obtain ⟨a, ha⟩ := (standardUnitEquiv (A := A) (B := B) (M := A)).surjective ⟨t, ht⟩
    refine ⟨a, ?_⟩
    have hval : (1 : B) ⊗ₜ[A] a = t := congrArg Subtype.val ha
    have reduced := congrArg (TensorProduct.rid A B) hval
    simpa [t, Algebra.smul_def] using reduced
  · rintro ⟨a, rfl⟩
    exact ((affineDoubleEmbedding A B 0).commutes a).trans
      ((affineDoubleEmbedding A B 1).commutes a).symm

variable (C : Type u) [CommRing C]

/-- Descent of any ring map along the two original projections of the
singleton faithfully flat affine cover. -/
def affineCover_ringHomEqualizer :
    (C →+* A) ≃ {f : C →+* B //
      (affineDoubleEmbedding A B 0).toRingHom.comp f =
        (affineDoubleEmbedding A B 1).toRingHom.comp f} where
  toFun f := ⟨(algebraMap A B).comp f, by
    ext x
    exact (affineCover_double_equalizer (A := A) (B := B) _).2 ⟨f x, rfl⟩⟩
  invFun f := by
    let a (x : C) := Classical.choose ((affineCover_double_equalizer (A := A) (B := B) (f.1 x)).1 (RingHom.congr_fun f.2 x))
    have ha (x : C) : algebraMap A B (a x) = f.1 x :=
      Classical.choose_spec ((affineCover_double_equalizer (A := A) (B := B) (f.1 x)).1 (RingHom.congr_fun f.2 x))
    exact
      { toFun := a
        map_one' := scalar_injective (A := A) (B := B) (by rw [ha, map_one, map_one])
        map_mul' := fun x y => scalar_injective (A := A) (B := B) (by rw [ha, map_mul, map_mul, ha, ha])
        map_zero' := scalar_injective (A := A) (B := B) (by rw [ha, map_zero, map_zero])
        map_add' := fun x y => scalar_injective (A := A) (B := B) (by rw [ha, map_add, map_add, ha, ha]) }
  left_inv f := by
    ext x
    apply scalar_injective (A := A) (B := B)
    have h := (affineCover_double_equalizer (A := A) (B := B) ((algebraMap A B) (f x))).2 ⟨f x, rfl⟩
    exact Classical.choose_spec ((affineCover_double_equalizer (A := A) (B := B) _).1 h)
  right_inv f := by
    apply Subtype.ext
    ext x
    exact Classical.choose_spec ((affineCover_double_equalizer (A := A) (B := B) (f.1 x)).1 (RingHom.congr_fun f.2 x))


/-- The affine scheme map supplied by a compatible local map is unique
and its restriction is the original local map. -/
theorem affineCover_descendsMap (g : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of C))
    (same : affineDoubleProjection A B 0 ≫ g = affineDoubleProjection A B 1 ≫ g) :
    ∃! h : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of C), affineScalarMap A B ≫ h = g := by
  let c := (Scheme.Spec.preimage g).unop
  have gc : Spec.map c = g := Scheme.Spec.map_preimage _
  have ringEq : (affineDoubleEmbedding A B 0).toRingHom.comp c.hom =
      (affineDoubleEmbedding A B 1).toRingHom.comp c.hom := by
    have eq : c ≫ affineDoubleRingHom A B 0 = c ≫ affineDoubleRingHom A B 1 := by
      apply Spec.map_injective
      rw [Spec.map_comp, Spec.map_comp, gc]
      exact same
    exact congrArg (fun f : CommRingCat.of C ⟶ CommRingCat.of (B ⊗[A] B) => f.hom) eq
  let E := affineCover_ringHomEqualizer (A := A) (B := B) C
  let h := E.symm ⟨c.hom, ringEq⟩
  have hcomp : (algebraMap A B).comp h = c.hom :=
    congrArg Subtype.val (E.apply_symm_apply ⟨c.hom, ringEq⟩)
  have restrict (r : C →+* A) :
      affineScalarMap A B ≫ Spec.map (CommRingCat.ofHom r) =
        Spec.map (CommRingCat.ofHom ((algebraMap A B).comp r)) :=
    (Spec.map_comp (CommRingCat.ofHom r) (CommRingCat.ofHom (algebraMap A B))).symm
  have hh : affineScalarMap A B ≫ Spec.map (CommRingCat.ofHom h) = g := by
    rw [restrict h, hcomp]
    exact gc
  refine ⟨Spec.map (CommRingCat.ofHom h), hh, ?_⟩
  intro k hk
  change affineScalarMap A B ≫ k = g at hk
  let a := CommRingCat.ofHom (algebraMap A B)
  have ff : a.hom.FaithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance
  letI : Flat (affineScalarMap A B) := ((flat_and_surjective_SpecMap_iff a).2 ff).1
  letI : Surjective (affineScalarMap A B) := ((flat_and_surjective_SpecMap_iff a).2 ff).2
  letI : Epi (affineScalarMap A B) := Flat.epi_of_flat_of_surjective _
  exact (cancel_epi (affineScalarMap A B)).1 (hk.trans hh.symm)

end

end SHIGURE.SchemeDescent
