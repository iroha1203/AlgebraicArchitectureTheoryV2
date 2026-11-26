import Formal.SHIGURE.Part2.QuantityTransport.Correspondences
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The tensor-product presentation of the correspondence

Proposition 5.9 presents the correspondence by adjoining the equations
matching corresponding coordinates in the tensor product of the two
Law algebras. The comparison below identifies its two projections
with the projections of the eliminated presentation.
-/

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

noncomputable section

namespace SHIGURE.Quantities

variable {k : Type u} [CommRing k]

/-- An algebra isomorphism induces an isomorphism of the relative affine spectra. -/
def specOverAlgEquiv {A B : Type u} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (e : A ≃ₐ[k] B) : specOver (k := k) B ≅ specOver (k := k) A :=
  Over.isoMk (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op) (Over.w (specOverMap e.toAlgHom))

/-- The relative spectrum of a composite is the composite of the spectra in reverse order. -/
theorem specOverMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra k A] [Algebra k B] [Algebra k C] (f : A →ₐ[k] B) (g : B →ₐ[k] C) :
    specOverMap g ≫ specOverMap f = specOverMap (g.comp f) := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, specOverMap_left]
  exact (Spec.map_comp (CommRingCat.ofHom f.toRingHom) (CommRingCat.ofHom g.toRingHom)).symm

namespace QuantityMap

variable {sig sig' : Signature.{u}}
variable {A : Structure sig} {B : Structure sig'}
variable {P : Presentation k A} {Q : Presentation k B}
variable (h : QuantityMap P Q)

/-- Use the commutative tensor product ring when forming the agreement ideal. -/
local instance : CommRing (P.LawAlgebra ⊗[k] Q.LawAlgebra) :=
  Algebra.TensorProduct.instCommRing

/-- The equations equating each source coordinate to its transported target coordinate. -/
def agreementIdeal : Ideal (P.LawAlgebra ⊗[k] Q.LawAlgebra) :=
  Ideal.span (Set.range fun x : P.Coordinate =>
    (Ideal.Quotient.mk P.residualIdeal (MvPolynomial.X x) ⊗ₜ[k] 1) -
      (1 ⊗ₜ[k] Ideal.Quotient.mk Q.residualIdeal (MvPolynomial.X (h.coordinate x))))

/-- The agreement equations generate a two-sided ideal in the commutative tensor product. -/
instance agreementIdeal_isTwoSided : h.agreementIdeal.IsTwoSided :=
  ⟨fun b ha => mul_comm b _ ▸ h.agreementIdeal.smul_mem _ ha⟩

/-- The product of the two Law schemes with the matching equations imposed on it. -/
abbrev AgreementAlgebra := (P.LawAlgebra ⊗[k] Q.LawAlgebra) ⧸ h.agreementIdeal

/-- The source Law algebra in the quotient by the matching equations. -/
def agreementSource : P.LawAlgebra →ₐ[k] h.AgreementAlgebra :=
  (Ideal.Quotient.mkₐ k h.agreementIdeal).comp Algebra.TensorProduct.includeLeft

/-- The target Law algebra in the quotient by the matching equations. -/
def agreementTarget : Q.LawAlgebra →ₐ[k] h.AgreementAlgebra :=
  (Ideal.Quotient.mkₐ k h.agreementIdeal).comp Algebra.TensorProduct.includeRight

/-- The defining agreement generator identifies the source and target forms of each coordinate. -/
private theorem agreement_variable (x : P.Coordinate) :
    h.agreementSource (Ideal.Quotient.mk P.residualIdeal (MvPolynomial.X x)) =
      h.agreementTarget (Ideal.Quotient.mk Q.residualIdeal (MvPolynomial.X (h.coordinate x))) := by
  exact (Ideal.Quotient.eq (I := h.agreementIdeal)).mpr (Ideal.subset_span ⟨x, rfl⟩)

/-- The two algebra maps agree after transporting all polynomial coordinates. -/
private theorem agreement_polynomial :
    (h.agreementTarget.comp (Ideal.Quotient.mkₐ k Q.residualIdeal)).comp h.polynomial =
      h.agreementSource.comp (Ideal.Quotient.mkₐ k P.residualIdeal) := by
  apply MvPolynomial.algHom_ext
  intro x
  rw [AlgHom.comp_apply, polynomial_X]
  exact (h.agreement_variable x).symm

/-- The source and target maps determine the ring map by the tensor product universal property. -/
private def tensorToEliminated : (P.LawAlgebra ⊗[k] Q.LawAlgebra) →ₐ[k] h.correspondencePresentation.LawAlgebra :=
  Algebra.TensorProduct.lift h.sourceQuotient h.targetQuotient (fun _ _ => Commute.all _ _)

/-- Eliminate the source coordinates from the tensor-product presentation. -/
def agreementToEliminated : h.AgreementAlgebra →ₐ[k] h.correspondencePresentation.LawAlgebra :=
  Ideal.Quotient.liftₐ h.agreementIdeal h.tensorToEliminated (by
    change h.agreementIdeal ≤ RingHom.ker h.tensorToEliminated.toRingHom
    rw [agreementIdeal, Ideal.span_le]
    rintro x ⟨y, rfl⟩
    change h.tensorToEliminated (_ - _) = 0
    simp only [map_sub, tensorToEliminated, Algebra.TensorProduct.lift_tmul, map_one, mul_one, one_mul,
      sub_eq_zero]
    change Ideal.Quotient.mk h.correspondencePresentation.residualIdeal (h.polynomial (MvPolynomial.X y)) =
      Ideal.Quotient.mk h.correspondencePresentation.residualIdeal (MvPolynomial.X (h.coordinate y))
    rw [polynomial_X])

/-- The eliminated target coordinates give all coordinates in the agreement quotient. -/
def eliminatedToAgreement : h.correspondencePresentation.LawAlgebra →ₐ[k] h.AgreementAlgebra :=
  Ideal.Quotient.liftₐ h.correspondencePresentation.residualIdeal
    (h.agreementTarget.comp (Ideal.Quotient.mkₐ k Q.residualIdeal)) (by
      change h.correspondencePresentation.residualIdeal ≤
        RingHom.ker (h.agreementTarget.comp (Ideal.Quotient.mkₐ k Q.residualIdeal)).toRingHom
      rw [correspondenceIdeal, sup_le_iff, Ideal.map_le_iff_le_comap]
      constructor
      · intro a ha
        change h.agreementTarget (Ideal.Quotient.mk Q.residualIdeal a) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
      · intro a ha
        change ((h.agreementTarget.comp (Ideal.Quotient.mkₐ k Q.residualIdeal)).comp h.polynomial) a = 0
        rw [agreement_polynomial]
        change h.agreementSource (Ideal.Quotient.mk P.residualIdeal a) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero])

/-- Eliminating variables preserves the source algebra map. -/
theorem agreementToEliminated_comp_source : h.agreementToEliminated.comp h.agreementSource = h.sourceQuotient := by
  change (h.agreementToEliminated.comp (Ideal.Quotient.mkₐ k h.agreementIdeal)).comp
    Algebra.TensorProduct.includeLeft = _
  rw [agreementToEliminated, Ideal.Quotient.liftₐ_comp, tensorToEliminated,
    Algebra.TensorProduct.lift_comp_includeLeft]

/-- Eliminating variables preserves the target algebra map. -/
theorem agreementToEliminated_comp_target : h.agreementToEliminated.comp h.agreementTarget = h.targetQuotient := by
  change (h.agreementToEliminated.comp (Ideal.Quotient.mkₐ k h.agreementIdeal)).comp
    Algebra.TensorProduct.includeRight = _
  rw [agreementToEliminated, Ideal.Quotient.liftₐ_comp, tensorToEliminated,
    Algebra.TensorProduct.lift_comp_includeRight']

/-- The inverse comparison maps the eliminated source algebra to the original tensor projection. -/
private theorem eliminatedToAgreement_comp_source :
    h.eliminatedToAgreement.comp h.sourceQuotient = h.agreementSource := by
  apply AlgHom.ext
  intro q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact AlgHom.congr_fun h.agreement_polynomial a

/-- The inverse comparison maps the eliminated target algebra to the original tensor projection. -/
private theorem eliminatedToAgreement_comp_target :
    h.eliminatedToAgreement.comp h.targetQuotient = h.agreementTarget := by
  apply AlgHom.ext
  intro q
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
  rfl

/-- The two concrete algebras defining Proposition 5.9 are isomorphic with their projections. -/
def agreementAlgebraEquiv : h.AgreementAlgebra ≃ₐ[k] h.correspondencePresentation.LawAlgebra :=
  AlgEquiv.ofAlgHom h.agreementToEliminated h.eliminatedToAgreement (by
    apply AlgHom.ext
    intro q
    obtain ⟨a, rfl⟩ := h.targetQuotient_surjective q
    exact AlgHom.congr_fun (by
      rw [AlgHom.comp_assoc, eliminatedToAgreement_comp_target, agreementToEliminated_comp_target]
      : (h.agreementToEliminated.comp h.eliminatedToAgreement).comp h.targetQuotient = h.targetQuotient) a)
    (by
      have eq : (h.eliminatedToAgreement.comp h.agreementToEliminated).comp
          (Ideal.Quotient.mkₐ k h.agreementIdeal) = Ideal.Quotient.mkₐ k h.agreementIdeal := by
        apply Algebra.TensorProduct.ext
        · change ((h.eliminatedToAgreement.comp h.agreementToEliminated).comp h.agreementSource) =
            h.agreementSource
          rw [AlgHom.comp_assoc, agreementToEliminated_comp_source, eliminatedToAgreement_comp_source]
        · change ((h.eliminatedToAgreement.comp h.agreementToEliminated).comp h.agreementTarget) =
            h.agreementTarget
          rw [AlgHom.comp_assoc, agreementToEliminated_comp_target, eliminatedToAgreement_comp_target]
      apply AlgHom.ext
      intro q
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
      exact AlgHom.congr_fun eq a)

/-- The two concrete presentations of the correspondence give isomorphic schemes over the base. -/
def agreementSchemeIso : h.correspondenceScheme ≅ specOver (k := k) h.AgreementAlgebra :=
  specOverAlgEquiv h.agreementAlgebraEquiv

/-- The tensor-product presentation gives the same projection to the source Law scheme. -/
theorem agreementSchemeIso_source :
    h.agreementSchemeIso.hom ≫ specOverMap h.agreementSource = h.sourceProjection := by
  change specOverMap h.agreementToEliminated ≫ specOverMap h.agreementSource = _
  rw [specOverMap_comp, agreementToEliminated_comp_source]
  rfl

/-- The tensor-product presentation gives the same projection to the target Law scheme. -/
theorem agreementSchemeIso_target :
    h.agreementSchemeIso.hom ≫ specOverMap h.agreementTarget = h.targetProjection := by
  change specOverMap h.agreementToEliminated ≫ specOverMap h.agreementTarget = _
  rw [specOverMap_comp, agreementToEliminated_comp_target]
  rfl

end QuantityMap
end SHIGURE.Quantities
