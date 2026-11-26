import Formal.SHIGURE.Part2.Quantities.Representation
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Factorization through the zero locus of the Laws

Theorem 5.5 characterizes the factorization by vanishing of the named
residuals and by vanishing of the ideal they generate after pullback.

## Implementation notes

The ideal sheaf is transported with mathlib's `IdealSheafData.comap`,
which describes the ideal of the pulled-back closed subscheme.
Using the pullback of the ideal as a module would retain the conormal
contribution even at points where its image in the structure sheaf is zero.
-/

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

namespace SHIGURE.Quantities.Presentation

variable {k : Type u} [CommRing k] {sig : Signature.{u}} {A : Structure sig} (P : Presentation k A)
variable {T : Over (Spec (CommRingCat.of k))}

/-- Read the quantity sections given by a map into the ambient affine space. -/
def ambientCandidate (p : T ⟶ P.ambientScheme) : P.Candidate Γ(T.left, ⊤) :=
  fun j x => specOverPointEquiv T P.CoordinateAlgebra p (P.universalQuantity j x)

/-- Reading the ambient point on the generators and evaluating recovers its full algebra map. -/
theorem evaluate_ambientCandidate (p : T ⟶ P.ambientScheme) :
    letI := globalSectionsAlgebra T
    P.evaluate (P.ambientCandidate p) = specOverPointEquiv T P.CoordinateAlgebra p := by
  letI := globalSectionsAlgebra T
  exact (P.evaluate_unique _ _ (fun _ => rfl)).symm

/-- The ideal sheaf of the Law scheme is associated to the actual named residual ideal. -/
theorem residualIdealSheaf_eq :
    P.lawInclusion.left.ker = Scheme.IdealSheafData.ofIdealTop
      (P.residualIdeal.comap (Scheme.ΓSpecIso (CommRingCat.of P.CoordinateAlgebra)).hom.hom) := by
  letI : IsAffine P.ambientScheme.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of P.CoordinateAlgebra)))
  rw [Scheme.ker_of_isAffine]
  congr 1
  let q := CommRingCat.ofHom (Ideal.Quotient.mk P.residualIdeal)
  let e := Scheme.ΓSpecIso (CommRingCat.of P.LawAlgebra)
  have he : Function.Injective e.hom.hom := e.commRingCatIsoToRingEquiv.injective
  ext x
  rw [RingHom.mem_ker, Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
  change (Spec.map q).appTop.hom x = 0 ↔ q.hom ((Scheme.ΓSpecIso _).hom.hom x) = 0
  have h := congrArg (fun f : Γ(P.ambientScheme.left, ⊤) ⟶ CommRingCat.of P.LawAlgebra => f.hom x)
    (Scheme.ΓSpecIso_naturality q)
  change e.hom.hom ((Spec.map q).appTop.hom x) = q.hom ((Scheme.ΓSpecIso _).hom.hom x) at h
  rw [← h, map_eq_zero_iff _ he]

/-- The generated image ideal of the pulled-back residual ideal sheaf. -/
def pulledResidualIdeal (p : T ⟶ P.ambientScheme) : T.left.IdealSheafData :=
  P.lawInclusion.left.ker.comap p.left

/-- A relative test map factors uniquely through the Law scheme exactly when the image ideal is zero. -/
theorem pulledResidualIdeal_eq_bot_iff_factor (p : T ⟶ P.ambientScheme) :
    P.pulledResidualIdeal p = ⊥ ↔ ∃! f : T ⟶ P.lawScheme, f ≫ P.lawInclusion = p := by
  letI := P.lawInclusion_closed
  have hI : P.pulledResidualIdeal p = ⊥ ↔ P.lawInclusion.left.ker ≤ p.left.ker := by
    change P.lawInclusion.left.ker.comap p.left = ⊥ ↔ _
    rw [← le_bot_iff, ← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_bot]
  rw [hI]
  constructor
  · intro h
    let f := IsClosedImmersion.lift P.lawInclusion.left p.left h
    have hf : f ≫ P.lawInclusion.left = p.left := IsClosedImmersion.lift_fac _ _ _
    let F : T ⟶ P.lawScheme := Over.homMk f (by
      rw [← Over.w P.lawInclusion, ← Category.assoc, hf, Over.w p])
    refine ⟨F, Over.OverMorphism.ext hf, ?_⟩
    intro g hg
    apply Over.OverMorphism.ext
    apply (cancel_mono P.lawInclusion.left).mp
    exact (congrArg (fun g : T ⟶ P.ambientScheme => g.left) hg).trans hf.symm
  · rintro ⟨f, hf, _⟩
    rw [← congrArg (fun g : T ⟶ P.ambientScheme => g.left) hf]
    exact f.left.le_ker_comp _

/-- The Law evaluation on global sections is equivalent to unique factorization. -/
theorem ambientCandidate_holds_iff_factor (p : T ⟶ P.ambientScheme) :
    letI := globalSectionsAlgebra T
    P.Holds (P.ambientCandidate p) ↔ ∃! f : T ⟶ P.lawScheme, f ≫ P.lawInclusion = p := by
  letI := globalSectionsAlgebra T
  letI := P.lawInclusion_closed
  constructor
  · intro h
    let g := P.modelAlgHomEquiv (R := Γ(T.left, ⊤)) ⟨P.ambientCandidate p, h⟩
    let f := (specOverPointEquiv T P.LawAlgebra).symm g
    have hf : f ≫ P.lawInclusion = p := by
      apply (specOverPointEquiv T P.CoordinateAlgebra).injective
      change specOverPointEquiv T P.CoordinateAlgebra (f ≫ specOverMap (Ideal.Quotient.mkₐ k P.residualIdeal)) = _
      rw [specOverPointEquiv_postcomp]
      change ((specOverPointEquiv T P.LawAlgebra) ((specOverPointEquiv T P.LawAlgebra).symm g)).comp _ = _
      rw [Equiv.apply_symm_apply, ← evaluate_ambientCandidate]
      exact Ideal.Quotient.liftₐ_comp _ _ _
    refine ⟨f, hf, ?_⟩
    intro f' hf'
    apply Over.OverMorphism.ext
    apply (cancel_mono P.lawInclusion.left).mp
    exact congrArg (fun g : T ⟶ P.ambientScheme => g.left) (hf'.trans hf.symm)
  · rintro ⟨f, hf, _⟩
    rw [← hf]
    let g := specOverPointEquiv T P.LawAlgebra f
    have hread : P.ambientCandidate (f ≫ P.lawInclusion) = P.readCoordinates g := by
      funext j x
      exact AlgHom.congr_fun (specOverPointEquiv_postcomp T f (Ideal.Quotient.mkₐ k P.residualIdeal)) _
    rw [hread]
    exact P.readCoordinates_holds g

/-- The two vanishing conditions in Theorem 5.5 agree for every relative test scheme. -/
theorem ambientCandidate_holds_iff_pulledResidualIdeal_eq_bot (p : T ⟶ P.ambientScheme) :
    letI := globalSectionsAlgebra T
    P.Holds (P.ambientCandidate p) ↔ P.pulledResidualIdeal p = ⊥ := by
  letI := globalSectionsAlgebra T
  exact (P.ambientCandidate_holds_iff_factor p).trans (P.pulledResidualIdeal_eq_bot_iff_factor p).symm

/-- The original residuals pull back to zero as global sections exactly when the generated image ideal vanishes. -/
theorem residualSections_eq_zero_iff_pulledResidualIdeal_eq_bot (p : T ⟶ P.ambientScheme) :
    (∀ l e, specOverPointEquiv T P.CoordinateAlgebra p (P.residual l e) = 0) ↔
      P.pulledResidualIdeal p = ⊥ := by
  letI := globalSectionsAlgebra T
  rw [← P.ambientCandidate_holds_iff_pulledResidualIdeal_eq_bot p, ← P.evaluate_ambientCandidate p]
  constructor
  · intro h l e
    have he := h l e
    rwa [P.evaluate_residual, sub_eq_zero] at he
  · intro h l e
    rw [P.evaluate_residual, h l e, sub_self]

end SHIGURE.Quantities.Presentation
