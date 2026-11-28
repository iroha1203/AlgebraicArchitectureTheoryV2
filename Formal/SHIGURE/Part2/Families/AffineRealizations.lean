import Formal.SHIGURE.Part2.Tensor.ExpressionBaseChange
import Formal.SHIGURE.Part2.Realizations.PolynomialCoefficientChange
import Formal.SHIGURE.Part2.Descent.FiniteLocallyFree
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Core

/-! # Affine families of finite locally free tensor realizations -/

open CategoryTheory SHIGURE.TensorRealization SHIGURE.CoefficientDescent
open scoped TensorProduct

universe u

noncomputable section

namespace SHIGURE.RealizationFamilies

variable {k R S : Type u} [CommRing k] [CommRing R] [CommRing S]
variable {sig : Signature.{u}}

/-- The two small families of equations have independently typed indices. -/
structure AffineLawPresentation (k : Type u) [CommRing k] (sig : Signature.{u}) where
  tensorIndex : Type u
  tensorLaw : tensorIndex → TensorLaw k sig
  polynomialIndex : Type u
  inputs : polynomialIndex → List sig.SortType
  output : polynomialIndex → sig.SortType
  polynomialLaw (i : polynomialIndex) : PolynomialLaw k sig (inputs i) (output i)

variable (P : AffineLawPresentation k sig) (rank : sig.SortType → ℕ)

/-- A realization has locally free carriers of the specified rank and satisfies
every written tensor and polynomial equation. -/
def affineProperty (c : k →+* R) : ObjectProperty (TensorStructure R sig) := fun A =>
  (∀ s, FiniteLocallyFree R (A.carrier s)) ∧
  (∀ s (p : PrimeSpectrum R), Module.rankAtStalk (A.carrier s) p = rank s) ∧
  (∀ i, ((P.tensorLaw i).mapScalars c).holds A) ∧
  (∀ i, (P.polynomialLaw i).Holds c A)

/-- The full subcategory retains every structure-preserving linear arrow. -/
abbrev AffineRealization (c : k →+* R) := (affineProperty P rank c).FullSubcategory

/-- Its maximal subgroupoid keeps precisely the isomorphisms. -/
abbrev AffineRealizationCore (c : k →+* R) := Core (AffineRealization P rank c)

theorem tensorExpression_mapScalars_comp (f : k →+* R) (g : R →+* S)
    {X Y : TensorShape sig.SortType} (t : TensorExpression k sig X Y) :
    (t.mapScalars f).mapScalars g = t.mapScalars (g.comp f) := by
  induction t <;> simp_all [TensorExpression.mapScalars, RingHom.comp_apply]

theorem tensorLaw_mapScalars_comp (f : k →+* R) (g : R →+* S)
    (law : TensorLaw k sig) :
    (law.mapScalars f).mapScalars g = law.mapScalars (g.comp f) := by
  cases law with
  | mk X Y left right =>
    simp only [TensorLaw.mapScalars, tensorExpression_mapScalars_comp]

variable [Algebra R S]

/-- The actual scalar extension preserves the specified local freeness, stalk
ranks, and both families of Laws. -/
theorem affineProperty_baseChange (c : k →+* R) (A : TensorStructure R sig)
    (h : affineProperty P rank c A) :
    affineProperty P rank ((algebraMap R S).comp c) (extendStructure R S A) := by
  obtain ⟨finite, ranks, tensor, polynomial⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s
    obtain ⟨hf, hp⟩ := finiteLocallyFree_iff_finite_projective.mp (finite s)
    letI : Module.Finite R (A.carrier s) := hf
    letI : Module.Projective R (A.carrier s) := hp
    change FiniteLocallyFree S (S ⊗[R] A.carrier s)
    exact finiteLocallyFree_iff_finite_projective.mpr ⟨inferInstance, inferInstance⟩
  · intro s p
    letI : Module.Finite R (A.carrier s) := (finiteLocallyFree_iff_finite_projective.mp (finite s)).1
    letI : Module.Flat R (A.carrier s) := (finite s).flat
    change Module.rankAtStalk (S ⊗[R] A.carrier s) p = rank s
    rw [Module.rankAtStalk_baseChange]
    exact ranks s _
  · intro i
    rw [← tensorLaw_mapScalars_comp]
    exact tensorLaw_holds_baseChange (tensor i)
  · intro i
    exact (P.polynomialLaw i).holds_baseChange c A (polynomial i)

/-- Scalar extension acts on all maps of the full realization category. -/
def affineBaseChange (c : k →+* R) :
    AffineRealization P rank c ⥤ AffineRealization P rank ((algebraMap R S).comp c) where
  obj A := ⟨extendStructure R S A.obj, affineProperty_baseChange P rank c A.obj A.property⟩
  map f := ObjectProperty.homMk (extendStructureMap S f.hom)
  map_id A := by
    apply ObjectProperty.hom_ext
    exact (extendStructureFunctor R S sig).map_id A.obj
  map_comp f g := by
    apply ObjectProperty.hom_ext
    exact (extendStructureFunctor R S sig).map_comp f.hom g.hom

/-- The induced functor acts on the maximum subgroupoids. -/
def affineCoreBaseChange (c : k →+* R) :
    AffineRealizationCore P rank c ⥤
      AffineRealizationCore P rank ((algebraMap R S).comp c) :=
  (affineBaseChange (S := S) P rank c).core

/-- The unit comparison is the ordinary structured scalar-unit isomorphism,
restricted to the full realization category. -/
def affineScalarUnit (c : k →+* R) :
    affineBaseChange (S := R) P rank c ≅ 𝟭 (AffineRealization P rank c) :=
  NatIso.ofComponents
    (fun A => ObjectProperty.isoMk _ (structureScalarUnit A.obj))
    (by
      intro A B f
      apply ObjectProperty.hom_ext
      exact (scalarUnitNatIso R sig).hom.naturality f.hom)

/-- The scalar unit comparison also acts on the maximal subgroupoid. -/
def affineCoreScalarUnit (c : k →+* R) :
    affineCoreBaseChange (S := R) P rank c ≅ 𝟭 (AffineRealizationCore P rank c) :=
  (affineScalarUnit P rank c).core ≪≫ Functor.coreId _

section Tower

variable {T : Type u} [CommRing T] [Algebra S T]

/-- The iterated and direct extensions are compared by the structured scalar
tower, with the composite coefficient map defining the direct algebra. -/
def affineScalarTower (c : k →+* R) :
    letI : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
    letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
    affineBaseChange (S := S) P rank c ⋙
        affineBaseChange (S := T) P rank ((algebraMap R S).comp c) ≅
      affineBaseChange (S := T) P rank c := by
  letI : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  exact NatIso.ofComponents
    (fun A => ObjectProperty.isoMk _ (structureScalarTower (R := S) (S := T) A.obj))
    (by
      intro A B f
      apply ObjectProperty.hom_ext
      exact (scalarTowerNatIso (k := R) (R := S) (S := T) sig).hom.naturality f.hom)

/-- The scalar tower comparison restricts to the maximal subgroupoids. -/
def affineCoreScalarTower (c : k →+* R) :
    letI : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
    letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
    affineCoreBaseChange (S := S) P rank c ⋙
        affineCoreBaseChange (S := T) P rank ((algebraMap R S).comp c) ≅
      affineCoreBaseChange (S := T) P rank c := by
  letI : Algebra R T := ((algebraMap S T).comp (algebraMap R S)).toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  exact (Functor.coreComp _ _).symm ≪≫ (affineScalarTower (S := S) (T := T) P rank c).core

end Tower

end SHIGURE.RealizationFamilies
