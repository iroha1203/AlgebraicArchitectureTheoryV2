import Formal.SHIGURE.Part2.Quantities.Coordinates
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Relative representation of quantity models

Theorem 5.4 represents the functor of quantity models by the quotient by
the named universal residuals. The same quotient represents models valued
in the global sections of any test scheme over the coefficient scheme.
-/

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

namespace SHIGURE.Quantities.Presentation

variable {k : Type u} [CommRing k] {sig : Signature.{u}} {A : Structure sig} (P : Presentation k A)
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

/-- The map of Construction 5.2 is the closed immersion of the residual quotient. -/
theorem lawInclusion_closed : IsClosedImmersion P.lawInclusion.left :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- Vanishing of the generators under evaluation is exactly direct Law satisfaction. -/
theorem holds_iff_residualIdeal_le_ker (q : P.Candidate R) :
    P.Holds q ↔ P.residualIdeal ≤ RingHom.ker (P.evaluate q).toRingHom := by
  rw [residualIdeal, Ideal.span_le]
  constructor
  · intro h r hr
    obtain ⟨⟨l, e⟩, rfl⟩ := hr
    change P.evaluate q (P.residual l e) = 0
    rw [evaluate_residual, h l e, sub_self]
  · intro h l e
    have hr : P.evaluate q (P.residual l e) = 0 := h ⟨⟨l, e⟩, rfl⟩
    rw [evaluate_residual, sub_eq_zero] at hr
    exact hr

/-- A point of the Law algebra gives a candidate by reading its coordinate images. -/
def readCoordinates (f : P.LawAlgebra →ₐ[k] R) : P.Candidate R :=
  fun j x => f (Ideal.Quotient.mkₐ k P.residualIdeal (P.universalQuantity j x))

/-- Evaluation at the coordinate images is the composite through the quotient. -/
theorem evaluate_readCoordinates (f : P.LawAlgebra →ₐ[k] R) :
    P.evaluate (P.readCoordinates f) = f.comp (Ideal.Quotient.mkₐ k P.residualIdeal) := by
  symm
  apply P.evaluate_unique
  intro x
  rfl

/-- A point of the quotient satisfies each of the original required equations. -/
theorem readCoordinates_holds (f : P.LawAlgebra →ₐ[k] R) : P.Holds (P.readCoordinates f) := by
  apply (P.holds_iff_residualIdeal_le_ker _).mpr
  intro a ha
  change P.evaluate (P.readCoordinates f) a = 0
  rw [evaluate_readCoordinates, AlgHom.comp_apply]
  have hz : Ideal.Quotient.mkₐ k P.residualIdeal a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
  rw [hz, map_zero]

/-- The coordinate bijection of Theorem 5.4, before applying the spectrum functor. -/
def modelAlgHomEquiv : P.Model R ≃ (P.LawAlgebra →ₐ[k] R) where
  toFun q := Ideal.Quotient.liftₐ P.residualIdeal (P.evaluate q.val)
    ((P.holds_iff_residualIdeal_le_ker q.val).mp q.property)
  invFun f := ⟨P.readCoordinates f, P.readCoordinates_holds f⟩
  left_inv q := by
    apply Subtype.ext
    funext j x
    exact P.evaluate_X q.val ⟨j, x⟩
  right_inv f := by
    apply AlgHom.ext
    intro a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
    change P.evaluate (P.readCoordinates f) b = f (Ideal.Quotient.mkₐ k P.residualIdeal b)
    rw [evaluate_readCoordinates, AlgHom.comp_apply]

/-- The coordinate bijection commutes with maps of coefficient algebras. -/
theorem modelAlgHomEquiv_natural (f : R →ₐ[k] S) (q : P.Model R) :
    P.modelAlgHomEquiv (P.map f q) = f.comp (P.modelAlgHomEquiv q) := by
  apply AlgHom.ext
  intro a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  change P.evaluate (fun j x => f (q.val j x)) b = f (P.evaluate q.val b)
  exact congrFun (congrArg DFunLike.coe (P.evaluate_natural q.val f)).symm b

/-- Read the identity of the Law algebra as the universal quantity model. -/
def universalModel : P.Model P.LawAlgebra := P.modelAlgHomEquiv.symm (AlgHom.id k P.LawAlgebra)

/-- The universal model is the family of residue classes of the coordinate variables. -/
theorem universalModel_value (j : P.Quantity) (x : P.Domain j) :
    P.universalModel.val j x = Ideal.Quotient.mkₐ k P.residualIdeal (P.universalQuantity j x) := rfl

/-- Equation (5.4) for affine test schemes, using the full faithfulness of spectrum. -/
def modelAffinePointEquiv : P.Model R ≃ (specOver R ⟶ P.lawScheme) :=
  P.modelAlgHomEquiv.trans {
    toFun := specOverMap
    invFun p := ⟨(Spec.preimage p.left).hom, by
      intro a
      have hw := congrArg Spec.preimage (Over.w p)
      change Spec.preimage (p.left ≫ Spec.map (CommRingCat.ofHom (algebraMap k P.LawAlgebra))) =
        Spec.preimage (Spec.map (CommRingCat.ofHom (algebraMap k R))) at hw
      rw [Spec.preimage_comp, Spec.preimage_map, Spec.preimage_map] at hw
      exact congrArg (fun f : CommRingCat.of k ⟶ CommRingCat.of R => f.hom a) hw⟩
    left_inv f := by
      apply AlgHom.coe_ringHom_injective
      change (Spec.preimage (Spec.map (CommRingCat.ofHom f.toRingHom))).hom = _
      simp
    right_inv p := by
      apply Over.OverMorphism.ext
      change Spec.map (Spec.preimage p.left) = p.left
      exact Spec.map_preimage p.left }

/-- Change of coefficients in equation (5.4) is precomposition by the spectral map. -/
theorem modelAffinePointEquiv_natural (f : R →ₐ[k] S) (q : P.Model R) :
    P.modelAffinePointEquiv (P.map f q) = specOverMap f ≫ P.modelAffinePointEquiv q := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left]
  change (specOverMap (P.modelAlgHomEquiv (P.map f q))).left =
    (specOverMap f).left ≫ (specOverMap (P.modelAlgHomEquiv q)).left
  rw [modelAlgHomEquiv_natural, specOverMap_left, specOverMap_left, specOverMap_left]
  exact Spec.map_comp (CommRingCat.ofHom (P.modelAlgHomEquiv q).toRingHom) (CommRingCat.ofHom f.toRingHom)

/-- Quantity models in the global sections of an arbitrary relative test scheme. -/
def modelGlobalSectionsEquiv (T : Over (Spec (CommRingCat.of k))) :
    letI := globalSectionsAlgebra T
    P.Model Γ(T.left, ⊤) ≃ (T ⟶ P.lawScheme) := by
  letI := globalSectionsAlgebra T
  exact P.modelAlgHomEquiv.trans (specOverPointEquiv T P.LawAlgebra).symm

/-- Pulling back a test scheme corresponds to pulling back every quantity section. -/
theorem modelGlobalSectionsEquiv_natural {T U : Over (Spec (CommRingCat.of k))} (f : U ⟶ T) :
    letI := globalSectionsAlgebra T
    letI := globalSectionsAlgebra U
    ∀ q : P.Model Γ(T.left, ⊤),
      P.modelGlobalSectionsEquiv U (P.map (globalSectionsMap f) q) = f ≫ P.modelGlobalSectionsEquiv T q := by
  letI := globalSectionsAlgebra T
  letI := globalSectionsAlgebra U
  intro q
  apply (specOverPointEquiv U P.LawAlgebra).injective
  rw [specOverPointEquiv_precomp]
  change (specOverPointEquiv U P.LawAlgebra) ((specOverPointEquiv U P.LawAlgebra).symm
      (P.modelAlgHomEquiv (P.map (globalSectionsMap f) q))) =
    (globalSectionsMap f).comp ((specOverPointEquiv T P.LawAlgebra) ((specOverPointEquiv T P.LawAlgebra).symm
      (P.modelAlgHomEquiv q)))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, modelAlgHomEquiv_natural]

end SHIGURE.Quantities.Presentation
