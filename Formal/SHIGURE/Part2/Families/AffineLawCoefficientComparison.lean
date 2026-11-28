import Formal.SHIGURE.Part2.Families.SchemeLawLocality

/-! # Affine realization properties under coefficient isomorphisms

These API lemmas support the affine comparison in Definition 6.1 and B.3.
Actual tensor-structure isomorphisms preserve local freeness, stalk ranks,
and both written Law families. Extension along a ring isomorphism reflects
the same property: extension back along the inverse is compared with the
original structure by the scalar tower and scalar unit isomorphisms.
-/

open CategoryTheory SHIGURE.TensorRealization SHIGURE.CoefficientDescent

universe u

noncomputable section

namespace SHIGURE.RealizationFamilies

variable {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
variable {sig : Signature.{u}}
variable (P : AffineLawPresentation k sig) (rank : sig.SortType → ℕ)

/-- B.3 syntax API: the identity coefficient map leaves each written
tensor expression unchanged. -/
theorem tensorExpression_mapScalars_id {X Y : TensorShape sig.SortType}
    (t : TensorExpression R sig X Y) : t.mapScalars (RingHom.id R) = t := by
  induction t <;> simp_all only [TensorExpression.mapScalars, RingHom.id_apply]

/-- B.3 syntax API: identity coefficient substitution preserves a tensor Law. -/
theorem tensorLaw_mapScalars_id (law : TensorLaw R sig) :
    law.mapScalars (RingHom.id R) = law := by
  cases law with
  | mk X Y left right =>
    simp only [TensorLaw.mapScalars, tensorExpression_mapScalars_id]

/-- B.3 Law API: a ring-isomorphism coefficient extension detects every
written tensor equation on arbitrary carrier modules. -/
theorem TensorLaw.holds_iff_baseChange_ringEquiv [Algebra R S]
    (e : R ≃+* S) (he : algebraMap R S = e.toRingHom)
    (law : TensorLaw R sig) (A : TensorStructure R sig) :
    (law.mapScalars (algebraMap R S)).holds (extendStructure R S A) ↔ law.holds A := by
  refine ⟨?_, fun h => tensorLaw_holds_baseChange h⟩
  intro h
  letI : Algebra S R := e.symm.toRingHom.toAlgebra
  letI : IsScalarTower R S R := IsScalarTower.of_algebraMap_eq fun r => by
    change r = e.symm (algebraMap R S r)
    rw [he]
    exact (e.symm_apply_apply r).symm
  have back := tensorLaw_holds_baseChange (R := R) h
  have coefficients : (algebraMap S R).comp (algebraMap R S) = RingHom.id R := by
    ext r
    change e.symm (algebraMap R S r) = r
    rw [he]
    exact e.symm_apply_apply r
  rw [tensorLaw_mapScalars_comp, coefficients, tensorLaw_mapScalars_id] at back
  exact (TensorLaw.holds_iff_of_iso law
    (structureScalarTower (k := R) (R := S) (S := R) A ≪≫ structureScalarUnit A)).mp back

/-- Definition 6.1 and B.3 Law API: the universal scalar tests of a
polynomial Law are reflected by a ring-isomorphism coefficient extension. -/
theorem PolynomialLaw.holds_iff_baseChange_ringEquiv [Algebra R S]
    (e : R ≃+* S) (he : algebraMap R S = e.toRingHom)
    {Γ : List sig.SortType} {s : sig.SortType} (law : PolynomialLaw k sig Γ s)
    (c : k →+* R) (A : TensorStructure R sig) :
    law.Holds ((algebraMap R S).comp c) (extendStructure R S A) ↔ law.Holds c A := by
  refine ⟨?_, fun h => law.holds_baseChange c A h⟩
  intro h
  letI : Algebra S R := e.symm.toRingHom.toAlgebra
  letI : IsScalarTower R S R := IsScalarTower.of_algebraMap_eq fun r => by
    change r = e.symm (algebraMap R S r)
    rw [he]
    exact (e.symm_apply_apply r).symm
  have back := law.holds_baseChange (S := R) ((algebraMap R S).comp c)
    (extendStructure R S A) h
  have coefficients : (algebraMap S R).comp ((algebraMap R S).comp c) = c := by
    ext a
    change e.symm (algebraMap R S (c a)) = c a
    rw [he]
    exact e.symm_apply_apply (c a)
  rw [coefficients] at back
  exact (law.holds_iff_of_iso c
    (structureScalarTower (k := R) (R := S) (S := R) A ≪≫ structureScalarUnit A)).mp back

/-- API for Definition 6.1: every condition in `affineProperty` is invariant
under an actual tensor-structure isomorphism, over an arbitrary ring. -/
theorem affineProperty_iff_of_iso (c : k →+* R) {A B : TensorStructure R sig}
    (e : A ≅ B) : affineProperty P rank c A ↔ affineProperty P rank c B := by
  have transport {A B : TensorStructure R sig} (e : A ≅ B)
      (h : affineProperty P rank c A) : affineProperty P rank c B := by
    obtain ⟨finite, ranks, tensor, polynomial⟩ := h
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s
      obtain ⟨finite, projective⟩ := finiteLocallyFree_iff_finite_projective.mp (finite s)
      exact finiteLocallyFree_iff_finite_projective.mpr
        ⟨Module.Finite.equiv (tensorStructureIsoOnSort e s),
          Module.Projective.of_equiv (tensorStructureIsoOnSort e s)⟩
    · intro s p
      exact (congrFun (Module.rankAtStalk_eq_of_equiv
        (tensorStructureIsoOnSort e s)) p).symm.trans (ranks s p)
    · intro i
      exact (TensorLaw.holds_iff_of_iso ((P.tensorLaw i).mapScalars c) e).mp (tensor i)
    · intro i
      exact ((P.polynomialLaw i).holds_iff_of_iso c e).mp (polynomial i)
  exact ⟨transport e, transport e.symm⟩

/-- B.3 coefficient comparison API: extension along a ring isomorphism
reflects the full property of Definition 6.1. The algebra compatibility is
the equality of the actual coefficient map with the given isomorphism. -/
theorem affineProperty_of_baseChange_ringEquiv [Algebra R S]
    (e : R ≃+* S) (he : algebraMap R S = e.toRingHom)
    (c : k →+* R) (A : TensorStructure R sig)
    (h : affineProperty P rank ((algebraMap R S).comp c) (extendStructure R S A)) :
    affineProperty P rank c A := by
  letI : Algebra S R := e.symm.toRingHom.toAlgebra
  letI : IsScalarTower R S R := IsScalarTower.of_algebraMap_eq fun r => by
    change r = e.symm (algebraMap R S r)
    rw [he]
    exact (e.symm_apply_apply r).symm
  have back := affineProperty_baseChange (S := R) P rank
    ((algebraMap R S).comp c) (extendStructure R S A) h
  have coefficients : (algebraMap S R).comp ((algebraMap R S).comp c) = c := by
    ext a
    change e.symm (algebraMap R S (c a)) = c a
    rw [he]
    exact e.symm_apply_apply (c a)
  rw [coefficients] at back
  exact (affineProperty_iff_of_iso P rank c
    (structureScalarTower (k := R) (R := S) (S := R) A ≪≫ structureScalarUnit A)).mp back

end SHIGURE.RealizationFamilies
