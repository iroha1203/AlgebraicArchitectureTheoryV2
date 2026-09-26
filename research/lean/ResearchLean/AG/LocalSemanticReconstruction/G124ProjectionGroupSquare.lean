import ResearchLean.AG.LocalSemanticReconstruction.G124KaroubiProjection
import ResearchLean.AG.RealizationComparisonIdempotents.NormalizationComparisonGroup
import Formal.Util.AssertStandardAxioms

/-! Endpoint automorphism squares and bottom-fixed subgroup transport for
the direct G-124 component projections. -/

namespace AAT.AG.LocalSemanticReconstruction.G124ProjectionGroupSquare

open CategoryTheory IndependentAATPrimitiveReconstruction
open G124ProjectionGlobal RealizationComparisonIdempotents
open RealizationReconstruction

universe u₁ u₂ u₃ v₁ v₂ v₃ u v

/-- The naturality square of a component comparison controls the entire
endpoint automorphism, not merely its object action. -/
theorem endpoint_square
    {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
    (F : C ⥤ D) (L : D ⥤ E) (R : C ⥤ E)
    (η : F ⋙ L ≅ R) (X : C) (a : Aut X) :
    (η.app X).conjAut (L.mapIso (F.mapIso a)) = R.mapIso a := by
  apply Iso.ext
  have h := η.hom.naturality a.hom
  dsimp at h
  simp only [Iso.conjAut_hom, Iso.conj_apply, Functor.mapIso_hom]
  change L.map (F.map a.hom) ≫ (η.app X).hom =
    (η.app X).hom ≫ R.map a.hom at h
  rw [h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The bottom map on the local comparison pair, conjugated by the III-1
canonical component isomorphism, is the original bottom map. -/
theorem bottom_endpoint_square (parameter : Parameter.{u, v})
    (X : NativeCategory parameter) (a : Aut X) :
    ((bottomReadingIso parameter).app X).conjAut
        ((localBottom parameter).mapIso ((reading parameter).mapIso a)) =
      (nativeBottom parameter).mapIso a :=
  endpoint_square (reading parameter) (localBottom parameter)
    (nativeBottom parameter) (bottomReadingIso parameter) X a

theorem observation_endpoint_square (parameter : Parameter.{u, v})
    (X : NativeCategory parameter) (a : Aut X) :
    ((observationReadingIso parameter).app X).conjAut
        ((localObservation parameter).mapIso ((reading parameter).mapIso a)) =
      (nativeObservation parameter).mapIso a :=
  endpoint_square (reading parameter) (localObservation parameter)
    (nativeObservation parameter) (observationReadingIso parameter) X a

theorem coefficient_endpoint_square (parameter : Parameter.{u, v})
    (X : NativeCategory parameter) (a : Aut X) :
    ((coefficientReadingIso parameter).app X).conjAut
        ((localCoefficient parameter).mapIso ((reading parameter).mapIso a)) =
      (nativeCoefficient parameter).mapIso a :=
  endpoint_square (reading parameter) (localCoefficient parameter)
    (nativeCoefficient parameter) (coefficientReadingIso parameter) X a

/-- The raw bottom-fixed condition is the kernel of the actual native
pointed-extraction action. -/
noncomputable def nativeBottomFixed (parameter : Parameter.{u, v})
    (X : NativeCategory parameter) : Subgroup (Aut X) :=
  (functorAutomorphismHom (nativeBottom parameter) X).ker

/-- The corresponding condition in the local primitive category uses the
direct III-1 bottom functor. -/
noncomputable def localBottomFixed (parameter : Parameter.{u, v})
    (X : LocalCategory parameter) : Subgroup (Aut X) :=
  (functorAutomorphismHom (localBottom parameter) X).ker

/-- Bottom fixedness is preserved and reflected by the *whole* endpoint
automorphism equivalence, using the III-1 natural comparison for conjugation. -/
theorem bottom_fixed_iff (parameter : Parameter.{u, v})
    (X : NativeCategory parameter) (a : Aut X) :
    a ∈ nativeBottomFixed parameter X ↔
      fullyFaithfulEndpointAutMulEquiv
        (reading parameter) (equivalence parameter).fullyFaithfulFunctor X a ∈
          localBottomFixed parameter ((reading parameter).obj X) := by
  rw [nativeBottomFixed, localBottomFixed, MonoidHom.mem_ker, MonoidHom.mem_ker]
  change (nativeBottom parameter).mapIso a = Iso.refl _ ↔
    (localBottom parameter).mapIso ((reading parameter).mapIso a) = Iso.refl _
  rw [← bottom_endpoint_square parameter X a]
  have hr : ((bottomReadingIso parameter).app X).conjAut
      (Iso.refl _) = Iso.refl _ := by
    apply Iso.ext
    simp [Iso.conjAut_hom, Iso.conj_apply]
  change ((bottomReadingIso parameter).app X).conjAut
      (Iso.refl ((localBottom parameter).obj ((reading parameter).obj X))) =
    Iso.refl ((nativeBottom parameter).obj X) at hr
  constructor
  · intro h
    apply ((bottomReadingIso parameter).app X).conjAut.injective
    exact h.trans hr.symm
  · intro h
    rw [h]
    exact hr

/-- A comparison pair is bottom-fixed exactly when both of its actual
endpoint automorphisms are fixed by the pointed-extraction projection. -/
noncomputable def nativeBottomFixedComparison (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y) :
    Subgroup (GeneratedArrowComparisonSubgroup c) where
  carrier pair :=
    pair.1.1 ∈ nativeBottomFixed parameter X ∧
      pair.1.2 ∈ nativeBottomFixed parameter Y
  one_mem' := ⟨one_mem _, one_mem _⟩
  mul_mem' := by
    intro first second hf hs
    exact ⟨mul_mem hf.1 hs.1, mul_mem hf.2 hs.2⟩
  inv_mem' := by
    intro pair hp
    exact ⟨inv_mem hp.1, inv_mem hp.2⟩

noncomputable def localBottomFixedComparison (parameter : Parameter.{u, v})
    {X Y : LocalCategory parameter} (c : X ⟶ Y) :
    Subgroup (GeneratedArrowComparisonSubgroup c) where
  carrier pair :=
    pair.1.1 ∈ localBottomFixed parameter X ∧
      pair.1.2 ∈ localBottomFixed parameter Y
  one_mem' := ⟨one_mem _, one_mem _⟩
  mul_mem' := by
    intro first second hf hs
    exact ⟨mul_mem hf.1 hs.1, mul_mem hf.2 hs.2⟩
  inv_mem' := by
    intro pair hp
    exact ⟨inv_mem hp.1, inv_mem hp.2⟩

/-- The full comparison-group equivalence preserves and reflects the
two-endpoint bottom qualification, for arbitrary (including noninvertible)
comparisons. -/
theorem bottom_comparison_mem_iff (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y)
    (pair : GeneratedArrowComparisonSubgroup c) :
    pair ∈ nativeBottomFixedComparison parameter c ↔
      G124ComparisonTransport.comparisonMulEquiv parameter c pair ∈
        localBottomFixedComparison parameter ((reading parameter).map c) := by
  change (pair.1.1 ∈ nativeBottomFixed parameter X ∧
      pair.1.2 ∈ nativeBottomFixed parameter Y) ↔
    ((reading parameter).mapIso pair.1.1 ∈
        localBottomFixed parameter ((reading parameter).obj X) ∧
      (reading parameter).mapIso pair.1.2 ∈
        localBottomFixed parameter ((reading parameter).obj Y))
  exact and_congr (bottom_fixed_iff parameter X pair.1.1)
    (bottom_fixed_iff parameter Y pair.1.2)

/-- The two endpoint observations of every transported comparison pair
commute with each of the three actual III-1 projection comparisons. -/
theorem bottom_comparison_pair_square (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y)
    (pair : GeneratedArrowComparisonSubgroup c) :
    (((bottomReadingIso parameter).app X).conjAut
        ((localBottom parameter).mapIso
          (G124ComparisonTransport.comparisonMulEquiv parameter c pair).1.1),
      ((bottomReadingIso parameter).app Y).conjAut
        ((localBottom parameter).mapIso
          (G124ComparisonTransport.comparisonMulEquiv parameter c pair).1.2)) =
      ((nativeBottom parameter).mapIso pair.1.1,
        (nativeBottom parameter).mapIso pair.1.2) := by
  apply Prod.ext
  · exact bottom_endpoint_square parameter X pair.1.1
  · exact bottom_endpoint_square parameter Y pair.1.2

theorem observation_comparison_pair_square (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y)
    (pair : GeneratedArrowComparisonSubgroup c) :
    (((observationReadingIso parameter).app X).conjAut
        ((localObservation parameter).mapIso
          (G124ComparisonTransport.comparisonMulEquiv parameter c pair).1.1),
      ((observationReadingIso parameter).app Y).conjAut
        ((localObservation parameter).mapIso
          (G124ComparisonTransport.comparisonMulEquiv parameter c pair).1.2)) =
      ((nativeObservation parameter).mapIso pair.1.1,
        (nativeObservation parameter).mapIso pair.1.2) := by
  apply Prod.ext
  · exact observation_endpoint_square parameter X pair.1.1
  · exact observation_endpoint_square parameter Y pair.1.2

theorem coefficient_comparison_pair_square (parameter : Parameter.{u, v})
    {X Y : NativeCategory parameter} (c : X ⟶ Y)
    (pair : GeneratedArrowComparisonSubgroup c) :
    (((coefficientReadingIso parameter).app X).conjAut
        ((localCoefficient parameter).mapIso
          (G124ComparisonTransport.comparisonMulEquiv parameter c pair).1.1),
      ((coefficientReadingIso parameter).app Y).conjAut
        ((localCoefficient parameter).mapIso
          (G124ComparisonTransport.comparisonMulEquiv parameter c pair).1.2)) =
      ((nativeCoefficient parameter).mapIso pair.1.1,
        (nativeCoefficient parameter).mapIso pair.1.2) := by
  apply Prod.ext
  · exact coefficient_endpoint_square parameter X pair.1.1
  · exact coefficient_endpoint_square parameter Y pair.1.2

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G124ProjectionGroupSquare

end AAT.AG.LocalSemanticReconstruction.G124ProjectionGroupSquare
