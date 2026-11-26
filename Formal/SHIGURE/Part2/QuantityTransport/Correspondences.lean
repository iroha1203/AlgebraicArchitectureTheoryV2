import Formal.SHIGURE.Part2.QuantityTransport.Maps
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# The correspondence of quantity models

Chapter 5, Proposition 5.9. Eliminating the source variables leaves
the target variables with both the target equations and the transported
source equations.

## Implementation notes

The presentation on the target coordinates gives the second projection
as a quotient. The separate tensor-product presentation retains the two
original sets of coordinates and is compared to this presentation by
the agreement equations.
-/

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

namespace SHIGURE.Quantities.QuantityMap

variable {k : Type u} [CommRing k] {sig sig' : Signature.{u}}
variable {A : Structure sig} {B : Structure sig'}
variable {P : Presentation k A} {Q : Presentation k B}
variable (h : QuantityMap P Q)

/-- The target coordinates with all the remaining equations after eliminating the source coordinates. -/
def correspondencePresentation : Presentation k B where
  Quantity := Q.Quantity
  Domain := Q.Domain
  Law := Q.Law ⊕ P.Law
  Input := Sum.elim Q.Input P.Input
  left
    | .inl l, e => Q.left l e
    | .inr l, e => (P.left l e).rename h.coordinate
  right
    | .inl l, e => Q.right l e
    | .inr l, e => (P.right l e).rename h.coordinate

private theorem evaluate_renamed {R : Type u} [CommRing R] (q : Q.Candidate R)
    (t : Expression k P.Coordinate) [Algebra k R] :
    (t.rename h.coordinate).eval (fun x => q x.1 x.2) =
      t.eval (fun x => h.candidate q x.1 x.2) :=
  Expression.eval_rename _ _ _

/-- The source equation after elimination is the image of its original residual. -/
theorem correspondenceResidual_source (l : P.Law) (e : P.Input l) :
    h.correspondencePresentation.residual (.inr l) e = h.polynomial (P.residual l e) := by
  change ((P.left l e).rename h.coordinate).eval (fun x => Q.universalQuantity x.1 x.2) -
      ((P.right l e).rename h.coordinate).eval (fun x => Q.universalQuantity x.1 x.2) = _
  rw [h.evaluate_renamed, h.evaluate_renamed, Presentation.residual, map_sub,
    ← Expression.eval_map, ← Expression.eval_map]
  have w : h.polynomial ∘ (fun x : P.Coordinate => P.universalQuantity x.1 x.2) =
      fun x => h.candidate Q.universalQuantity x.1 x.2 :=
    funext h.polynomial_X
  rw [w]

/-- The eliminated residual ideal is the sum of the target ideal and the image of the source ideal. -/
theorem correspondenceIdeal :
    h.correspondencePresentation.residualIdeal =
      Q.residualIdeal ⊔ P.residualIdeal.map h.polynomial.toRingHom := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · apply h.correspondencePresentation.residualIdeal_le_iff.mpr
    rintro (l | l) e
    · change Q.residual l e ∈ Q.residualIdeal ⊔ P.residualIdeal.map h.polynomial.toRingHom
      exact Ideal.mem_sup_left (Q.residualIdeal_le_iff.mp le_rfl l e)
    · change h.correspondencePresentation.residual (.inr l) e ∈
        Q.residualIdeal ⊔ P.residualIdeal.map h.polynomial.toRingHom
      rw [correspondenceResidual_source]
      exact Ideal.mem_sup_right (Ideal.mem_map_of_mem h.polynomial.toRingHom (P.residualIdeal_le_iff.mp le_rfl l e))
  · apply Q.residualIdeal_le_iff.mpr
    intro l e
    exact h.correspondencePresentation.residualIdeal_le_iff.mp le_rfl (.inl l) e
  · rw [Ideal.map_le_iff_le_comap, P.residualIdeal_le_iff]
    intro l e
    change h.polynomial (P.residual l e) ∈ h.correspondencePresentation.residualIdeal
    rw [← correspondenceResidual_source]
    exact h.correspondencePresentation.residualIdeal_le_iff.mp le_rfl (.inr l) e

/-- The affine scheme of pairs with matching quantity assignments. -/
abbrev correspondenceScheme := h.correspondencePresentation.lawScheme

/-- A pair of lawful models whose named quantities agree after pullback. -/
abbrev CompatiblePair (R : Type u) [CommRing R] [Algebra k R] :=
  {q : P.Model R × Q.Model R // q.1.val = h.candidate q.2.val}

/-- A solution of the eliminated equations is a unique compatible pair. -/
def compatiblePairEquiv (R : Type u) [CommRing R] [Algebra k R] :
    h.correspondencePresentation.Model R ≃ h.CompatiblePair R where
  toFun q := ⟨⟨⟨h.candidate q.val, fun l e => by
      simpa only [correspondencePresentation, evaluate_renamed] using q.property (.inr l) e⟩,
    ⟨q.val, fun l e => q.property (.inl l) e⟩⟩, rfl⟩
  invFun q := ⟨q.val.2.val, fun l e => by
    cases l with
    | inl l => exact q.val.2.property l e
    | inr l =>
      change ((P.left l e).rename h.coordinate).eval (fun x => q.val.2.val x.1 x.2) =
        ((P.right l e).rename h.coordinate).eval (fun x => q.val.2.val x.1 x.2)
      rw [h.evaluate_renamed, h.evaluate_renamed, ← q.property]
      exact q.val.1.property l e⟩
  left_inv _ := Subtype.ext rfl
  right_inv q := Subtype.ext (Prod.ext (Subtype.ext q.property.symm) (Subtype.ext rfl))

/-- Change coefficients in both members of a compatible pair. -/
def mapCompatiblePair {R S : Type u} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (f : R →ₐ[k] S) (q : h.CompatiblePair R) : h.CompatiblePair S :=
  ⟨⟨P.map f q.val.1, Q.map f q.val.2⟩, by
    change (fun j x => f (q.val.1.val j x)) = _
    rw [q.property]
    rfl⟩

/-- The pair representation commutes with coefficient maps on both sides. -/
theorem compatiblePairEquiv_natural {R S : Type u} [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (f : R →ₐ[k] S) (q : h.CompatiblePair R) :
    (h.compatiblePairEquiv S).symm (h.mapCompatiblePair f q) =
      h.correspondencePresentation.map f ((h.compatiblePairEquiv R).symm q) :=
  Subtype.ext rfl

/-- The correspondence represents compatible pairs on every test scheme over the coefficient base. -/
def compatiblePairSchemeEquiv (T : Over (Spec (CommRingCat.of k))) :
    letI := globalSectionsAlgebra T
    h.CompatiblePair Γ(T.left, ⊤) ≃ (T ⟶ h.correspondenceScheme) := by
  letI := globalSectionsAlgebra T
  exact (h.compatiblePairEquiv _).symm.trans (h.correspondencePresentation.modelGlobalSectionsEquiv T)

/-- The representation of compatible pairs is natural on arbitrary test schemes. -/
theorem compatiblePairSchemeEquiv_natural {T U : Over (Spec (CommRingCat.of k))} (f : U ⟶ T) :
    letI := globalSectionsAlgebra T
    letI := globalSectionsAlgebra U
    ∀ q : h.CompatiblePair Γ(T.left, ⊤),
      h.compatiblePairSchemeEquiv U (h.mapCompatiblePair (globalSectionsMap f) q) =
        f ≫ h.compatiblePairSchemeEquiv T q := by
  letI := globalSectionsAlgebra T
  letI := globalSectionsAlgebra U
  intro q
  change h.correspondencePresentation.modelGlobalSectionsEquiv U
      ((h.compatiblePairEquiv _).symm (h.mapCompatiblePair (globalSectionsMap f) q)) = _
  rw [compatiblePairEquiv_natural]
  exact h.correspondencePresentation.modelGlobalSectionsEquiv_natural f ((h.compatiblePairEquiv _).symm q)

/-- The second projection on algebras quotients by the remaining source equations. -/
def targetQuotient : Q.LawAlgebra →ₐ[k] h.correspondencePresentation.LawAlgebra :=
  Ideal.quotientMapₐ h.correspondencePresentation.residualIdeal (AlgHom.id k Q.CoordinateAlgebra) (by
    intro x hx
    change x ∈ h.correspondencePresentation.residualIdeal
    rw [h.correspondenceIdeal]
    exact Ideal.mem_sup_left hx)

/-- The actual second projection of the correspondence. -/
def targetProjection : h.correspondenceScheme ⟶ Q.lawScheme :=
  specOverMap h.targetQuotient

/-- The first projection reads each source coordinate at its transported target coordinate. -/
def sourceQuotient : P.LawAlgebra →ₐ[k] h.correspondencePresentation.LawAlgebra :=
  Ideal.quotientMapₐ h.correspondencePresentation.residualIdeal h.polynomial (by
    intro x hx
    change h.polynomial x ∈ h.correspondencePresentation.residualIdeal
    rw [h.correspondenceIdeal]
    exact Ideal.mem_sup_right (Ideal.mem_map_of_mem h.polynomial.toRingHom hx))

/-- The first projection of the correspondence to the source Law scheme. -/
def sourceProjection : h.correspondenceScheme ⟶ P.lawScheme :=
  specOverMap h.sourceQuotient

/-- The first projection reads the source model of each compatible pair. -/
theorem modelAlgHomEquiv_source {R : Type u} [CommRing R] [Algebra k R]
    (q : h.correspondencePresentation.Model R) :
    P.modelAlgHomEquiv ((h.compatiblePairEquiv R q).val.1) =
      (h.correspondencePresentation.modelAlgHomEquiv q).comp h.sourceQuotient := by
  apply AlgHom.ext
  intro a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  change P.evaluate (h.candidate q.val) b = Q.evaluate q.val (h.polynomial b)
  exact AlgHom.congr_fun (h.evaluate_candidate q.val) b

/-- The second projection reads the target model of each compatible pair. -/
theorem modelAlgHomEquiv_target {R : Type u} [CommRing R] [Algebra k R]
    (q : h.correspondencePresentation.Model R) :
    Q.modelAlgHomEquiv ((h.compatiblePairEquiv R q).val.2) =
      (h.correspondencePresentation.modelAlgHomEquiv q).comp h.targetQuotient := by
  apply AlgHom.ext
  intro a
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  rfl

/-- Both scheme projections realize the two given models on every relative test scheme. -/
theorem compatiblePairSchemeEquiv_projections (T : Over (Spec (CommRingCat.of k))) :
    letI := globalSectionsAlgebra T
    ∀ q : h.CompatiblePair Γ(T.left, ⊤),
      h.compatiblePairSchemeEquiv T q ≫ h.sourceProjection = P.modelGlobalSectionsEquiv T q.val.1 ∧
        h.compatiblePairSchemeEquiv T q ≫ h.targetProjection = Q.modelGlobalSectionsEquiv T q.val.2 := by
  letI := globalSectionsAlgebra T
  intro q
  let e := h.compatiblePairEquiv Γ(T.left, ⊤)
  let z := e.symm q
  have pair := e.apply_symm_apply q
  constructor
  · apply (specOverPointEquiv T P.LawAlgebra).injective
    change specOverPointEquiv T P.LawAlgebra
      (h.correspondencePresentation.modelGlobalSectionsEquiv T z ≫ specOverMap h.sourceQuotient) = _
    rw [specOverPointEquiv_postcomp]
    change ((specOverPointEquiv T h.correspondencePresentation.LawAlgebra)
        ((specOverPointEquiv T h.correspondencePresentation.LawAlgebra).symm
          (h.correspondencePresentation.modelAlgHomEquiv z))).comp h.sourceQuotient =
      (specOverPointEquiv T P.LawAlgebra)
        ((specOverPointEquiv T P.LawAlgebra).symm (P.modelAlgHomEquiv q.val.1))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, ← h.modelAlgHomEquiv_source]
    exact congrArg (fun (p : h.CompatiblePair Γ(T.left, ⊤)) => P.modelAlgHomEquiv p.val.1) pair
  · apply (specOverPointEquiv T Q.LawAlgebra).injective
    change specOverPointEquiv T Q.LawAlgebra
      (h.correspondencePresentation.modelGlobalSectionsEquiv T z ≫ specOverMap h.targetQuotient) = _
    rw [specOverPointEquiv_postcomp]
    change ((specOverPointEquiv T h.correspondencePresentation.LawAlgebra)
        ((specOverPointEquiv T h.correspondencePresentation.LawAlgebra).symm
          (h.correspondencePresentation.modelAlgHomEquiv z))).comp h.targetQuotient =
      (specOverPointEquiv T Q.LawAlgebra)
        ((specOverPointEquiv T Q.LawAlgebra).symm (Q.modelAlgHomEquiv q.val.2))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, ← h.modelAlgHomEquiv_target]
    exact congrArg (fun (p : h.CompatiblePair Γ(T.left, ⊤)) => Q.modelAlgHomEquiv p.val.2) pair

/-- Every element of the eliminated quotient already comes from a target coordinate polynomial. -/
theorem targetQuotient_surjective : Function.Surjective h.targetQuotient := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk Q.residualIdeal a, rfl⟩

/-- The second projection is a closed immersion, since its algebra map is surjective. -/
theorem targetProjection_closed : IsClosedImmersion h.targetProjection.left :=
  IsClosedImmersion.spec_of_surjective _ h.targetQuotient_surjective

/-- The second projection is an isomorphism precisely when the transported source Laws
already vanish on the target Law scheme. Together with the first projection this is the
graph criterion of Proposition 5.9. -/
theorem targetProjection_isIso_iff :
    IsIso h.targetProjection.left ↔ P.residualIdeal.map h.polynomial.toRingHom ≤ Q.residualIdeal := by
  change IsIso (Spec.map (CommRingCat.ofHom h.targetQuotient.toRingHom)) ↔ _
  rw [isIso_SpecMap_iff]
  constructor
  · intro hb x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply hb.injective
    change h.targetQuotient (Ideal.Quotient.mk Q.residualIdeal x) = h.targetQuotient 0
    rw [map_zero]
    change Ideal.Quotient.mk h.correspondencePresentation.residualIdeal x = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [h.correspondenceIdeal]
    exact Ideal.mem_sup_right hx
  · intro hi
    refine ⟨?_, h.targetQuotient_surjective⟩
    change Function.Injective h.targetQuotient.toRingHom
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk h.correspondencePresentation.residualIdeal a = 0 at hx
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    have ha := Ideal.Quotient.eq_zero_iff_mem.mp hx
    rwa [h.correspondenceIdeal, sup_eq_left.mpr hi] at ha

/-- The correspondence is the graph of a map defined on all of the target Law scheme
exactly when its equations already contain the transported source equations. -/
theorem correspondence_isGraph_iff :
    (∃ (i : h.correspondenceScheme ≅ Q.lawScheme) (g : Q.lawScheme ⟶ P.lawScheme),
      i.hom = h.targetProjection ∧ i.hom ≫ g = h.sourceProjection) ↔
      P.residualIdeal.map h.polynomial.toRingHom ≤ Q.residualIdeal := by
  constructor
  · rintro ⟨i, _, hi, _⟩
    apply h.targetProjection_isIso_iff.mp
    rw [← hi]
    change IsIso ((Over.forget _).map i.hom)
    infer_instance
  · intro hi
    letI := h.targetProjection_isIso_iff.mpr hi
    let i := Over.isoMk (asIso h.targetProjection.left) (Over.w h.targetProjection)
    refine ⟨i, i.inv ≫ h.sourceProjection, Over.OverMorphism.ext rfl, ?_⟩
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

end SHIGURE.Quantities.QuantityMap
