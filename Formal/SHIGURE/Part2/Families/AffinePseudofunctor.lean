import Formal.SHIGURE.Part2.Families.AffineRealizations
import Formal.SHIGURE.Part2.Tensor.CoefficientPoints
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-! # Coherent coefficient change for affine realizations -/

open CategoryTheory SHIGURE.TensorRealization
open CategoryTheory.Bicategory

universe u

noncomputable section

namespace SHIGURE.RealizationFamilies

variable {k : Type u} [CommRing k] {sig : Signature.{u}}
variable (P : AffineLawPresentation k sig) (rank : sig.SortType → ℕ)

/-- The category of realizations over a commutative base algebra. -/
abbrev algebraRealizations (R : CommAlgCat.{u} k) :=
  AffineRealization P rank (algebraMap k R)

/-- Extend along the actual algebra map, using its compatibility with the
fixed base coefficients to read the resulting Laws over the target algebra. -/
def algebraBaseChange {R S : CommAlgCat.{u} k} (f : R ⟶ S) :
    algebraRealizations P rank R ⥤ algebraRealizations P rank S := by
  letI : Algebra R S := f.hom.toRingHom.toAlgebra
  have coefficients : (algebraMap R S).comp (algebraMap k R) = algebraMap k S :=
    RingHom.ext fun a => f.hom.commutes a
  exact
    { obj := fun A => ⟨extendStructure R S A.obj, by
        have h := affineProperty_baseChange (S := S) P rank (algebraMap k R) A.obj A.property
        rw [coefficients] at h
        exact h⟩
      map := fun f => ObjectProperty.homMk (extendStructureMap S f.hom)
      map_id := fun A => ObjectProperty.hom_ext _ ((extendStructureFunctor R S sig).map_id A.obj)
      map_comp := fun f g => ObjectProperty.hom_ext _
        ((extendStructureFunctor R S sig).map_comp f.hom g.hom) }

/-- The unit comparison for the algebra identity. -/
def algebraBaseChangeId (R : CommAlgCat.{u} k) :
    algebraBaseChange P rank (𝟙 R) ≅ 𝟭 (algebraRealizations P rank R) :=
  NatIso.ofComponents (fun A => ObjectProperty.isoMk _ (structureScalarUnit A.obj)) (by
    intro A B f
    apply ObjectProperty.hom_ext
    exact (scalarUnitNatIso R sig).hom.naturality f.hom)

/-- The tower comparison for two algebra maps, from iterated to direct extension. -/
def algebraBaseChangeComp {R S T : CommAlgCat.{u} k} (f : R ⟶ S) (g : S ⟶ T) :
    algebraBaseChange P rank f ⋙ algebraBaseChange P rank g ≅
      algebraBaseChange P rank (f ≫ g) := by
  letI : Algebra R S := f.hom.toRingHom.toAlgebra
  letI : Algebra S T := g.hom.toRingHom.toAlgebra
  letI : Algebra R T := (g.hom.toRingHom.comp f.hom.toRingHom).toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  exact NatIso.ofComponents
    (fun A => ObjectProperty.isoMk _ (structureScalarTower (R := S) (S := T) A.obj)) (by
      intro A B p
      apply ObjectProperty.hom_ext
      exact (scalarTowerNatIso (k := R) (R := S) (S := T) sig).hom.naturality p.hom)

/-- The two tower comparisons for three algebra maps agree. -/
theorem algebraBaseChange_assoc {R S T U : CommAlgCat.{u} k}
    (f : R ⟶ S) (g : S ⟶ T) (h : T ⟶ U) :
    Functor.whiskerRight (algebraBaseChangeComp P rank f g).hom (algebraBaseChange P rank h) ≫
        (algebraBaseChangeComp P rank (f ≫ g) h).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (algebraBaseChange P rank f) (algebraBaseChangeComp P rank g h).hom ≫
          (algebraBaseChangeComp P rank f (g ≫ h)).hom := by
  letI : Algebra R S := f.hom.toRingHom.toAlgebra
  letI : Algebra S T := g.hom.toRingHom.toAlgebra
  letI : Algebra T U := h.hom.toRingHom.toAlgebra
  letI : Algebra R T := (g.hom.toRingHom.comp f.hom.toRingHom).toAlgebra
  letI : Algebra S U := (h.hom.toRingHom.comp g.hom.toRingHom).toAlgebra
  letI : Algebra R U := (h.hom.toRingHom.comp (g.hom.toRingHom.comp f.hom.toRingHom)).toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower S T U := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R S U := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R T U := IsScalarTower.of_algebraMap_eq' rfl
  apply NatTrans.ext
  funext A
  apply ObjectProperty.hom_ext
  exact structureScalarTower_three (k := R) (R := S) (S := T) (T := U) A.obj

/-- The first identity algebra map gives the scalar unit comparison. -/
theorem algebraBaseChange_id_comp {R S : CommAlgCat.{u} k} (f : R ⟶ S) :
    (algebraBaseChangeComp P rank (𝟙 R) f).hom =
      Functor.whiskerRight (algebraBaseChangeId P rank R).hom (algebraBaseChange P rank f) ≫
        (Functor.leftUnitor _).hom := by
  letI : Algebra R S := f.hom.toRingHom.toAlgebra
  apply NatTrans.ext
  funext A
  apply ObjectProperty.hom_ext
  exact structureScalarTower_leftUnit (k := R) (R := S) A.obj

/-- The second identity algebra map gives the scalar unit comparison. -/
theorem algebraBaseChange_comp_id {R S : CommAlgCat.{u} k} (f : R ⟶ S) :
    (algebraBaseChangeComp P rank f (𝟙 S)).hom =
      Functor.whiskerLeft (algebraBaseChange P rank f) (algebraBaseChangeId P rank S).hom ≫
        (Functor.rightUnitor _).hom := by
  letI : Algebra R S := f.hom.toRingHom.toAlgebra
  apply NatTrans.ext
  funext A
  apply ObjectProperty.hom_ext
  exact structureScalarTower_rightUnit (k := R) (R := S) A.obj

/-- Coefficient extension on the maximal subgroupoids. -/
def algebraCoreBaseChange {R S : CommAlgCat.{u} k} (f : R ⟶ S) :
    Core (algebraRealizations P rank R) ⥤ Core (algebraRealizations P rank S) :=
  (algebraBaseChange P rank f).core

/-- The scalar unit comparison on maximal subgroupoids. -/
def algebraCoreBaseChangeId (R : CommAlgCat.{u} k) :
    algebraCoreBaseChange P rank (𝟙 R) ≅ 𝟭 (Core (algebraRealizations P rank R)) :=
  (algebraBaseChangeId P rank R).core ≪≫ Functor.coreId _

/-- The scalar tower comparison on maximal subgroupoids. -/
def algebraCoreBaseChangeComp {R S T : CommAlgCat.{u} k} (f : R ⟶ S) (g : S ⟶ T) :
    algebraCoreBaseChange P rank f ⋙ algebraCoreBaseChange P rank g ≅
      algebraCoreBaseChange P rank (f ≫ g) :=
  (Functor.coreComp _ _).symm ≪≫ (algebraBaseChangeComp P rank f g).core

/-- The three-stage tower identity holds on the maximal subgroupoids. -/
theorem algebraCoreBaseChange_assoc {R S T U : CommAlgCat.{u} k}
    (f : R ⟶ S) (g : S ⟶ T) (h : T ⟶ U) :
    Functor.whiskerRight (algebraCoreBaseChangeComp P rank f g).hom (algebraCoreBaseChange P rank h) ≫
        (algebraCoreBaseChangeComp P rank (f ≫ g) h).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (algebraCoreBaseChange P rank f) (algebraCoreBaseChangeComp P rank g h).hom ≫
          (algebraCoreBaseChangeComp P rank f (g ≫ h)).hom := by
  apply NatTrans.ext
  funext A
  apply Core.hom_ext
  exact congrArg (fun t => t.app A.of) (algebraBaseChange_assoc P rank f g h)

/-- The left unit identity holds on the maximal subgroupoids. -/
theorem algebraCoreBaseChange_id_comp {R S : CommAlgCat.{u} k} (f : R ⟶ S) :
    (algebraCoreBaseChangeComp P rank (𝟙 R) f).hom =
      Functor.whiskerRight (algebraCoreBaseChangeId P rank R).hom (algebraCoreBaseChange P rank f) ≫
        (Functor.leftUnitor _).hom := by
  apply NatTrans.ext
  funext A
  apply Core.hom_ext
  exact congrArg (fun t => t.app A.of) (algebraBaseChange_id_comp P rank f)

/-- The right unit identity holds on the maximal subgroupoids. -/
theorem algebraCoreBaseChange_comp_id {R S : CommAlgCat.{u} k} (f : R ⟶ S) :
    (algebraCoreBaseChangeComp P rank f (𝟙 S)).hom =
      Functor.whiskerLeft (algebraCoreBaseChange P rank f) (algebraCoreBaseChangeId P rank S).hom ≫
        (Functor.rightUnitor _).hom := by
  apply NatTrans.ext
  funext A
  apply Core.hom_ext
  exact congrArg (fun t => t.app A.of) (algebraBaseChange_comp_id P rank f)

/-- Affine finite locally free realization groupoids form a pseudofunctor on
commutative base algebras, with actual scalar extension as its arrow action. -/
def affineRealizationPseudofunctor :
    Pseudofunctor (LocallyDiscrete (CommAlgCat.{u} k)) Cat := by
  refine LocallyDiscrete.mkPseudofunctor
    (fun R => Cat.of (Core (algebraRealizations P rank R)))
    (fun f => (algebraCoreBaseChange P rank f).toCatHom)
    (fun R => Cat.Hom.isoMk (algebraCoreBaseChangeId P rank R))
    (fun f g => Cat.Hom.isoMk (algebraCoreBaseChangeComp P rank f g).symm) ?_ ?_ ?_
  · intro R S T U f g h
    ext1
    let e₁ := algebraCoreBaseChangeComp P rank (f ≫ g) h
    let e₂ := Functor.isoWhiskerRight (algebraCoreBaseChangeComp P rank f g) (algebraCoreBaseChange P rank h)
    let e₃ := Functor.isoWhiskerLeft (algebraCoreBaseChange P rank f) (algebraCoreBaseChangeComp P rank g h)
    let e₄ := algebraCoreBaseChangeComp P rank f (g ≫ h)
    change e₁.inv ≫ e₂.inv ≫ (Functor.associator _ _ _).hom ≫ e₃.hom ≫ e₄.hom = _
    have coherence : e₂.hom ≫ e₁.hom = (Functor.associator _ _ _).hom ≫ e₃.hom ≫ e₄.hom :=
      algebraCoreBaseChange_assoc P rank f g h
    have rearranged : e₃.hom ≫ e₄.hom =
        (Functor.associator _ _ _).inv ≫ e₂.hom ≫ e₁.hom := by
      rw [coherence]
      simp
    simp [rearranged]
  · intro R S f
    ext1
    let e₁ := algebraCoreBaseChangeComp P rank (𝟙 R) f
    let e₂ := Functor.isoWhiskerRight (algebraCoreBaseChangeId P rank R) (algebraCoreBaseChange P rank f)
    let e₃ := (algebraCoreBaseChange P rank f).leftUnitor
    change e₁.inv ≫ e₂.hom ≫ e₃.hom = _
    have coherence : e₁.hom = e₂.hom ≫ e₃.hom := algebraCoreBaseChange_id_comp P rank f
    simp [← coherence]
  · intro R S f
    ext1
    let e₁ := algebraCoreBaseChangeComp P rank f (𝟙 S)
    let e₂ := Functor.isoWhiskerLeft (algebraCoreBaseChange P rank f) (algebraCoreBaseChangeId P rank S)
    let e₃ := (algebraCoreBaseChange P rank f).rightUnitor
    change e₁.inv ≫ e₂.hom ≫ e₃.hom = _
    have coherence : e₁.hom = e₂.hom ≫ e₃.hom := algebraCoreBaseChange_comp_id P rank f
    simp [← coherence]

end SHIGURE.RealizationFamilies
