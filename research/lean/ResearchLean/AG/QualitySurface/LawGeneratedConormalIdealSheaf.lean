import ResearchLean.AG.QualitySurface.LawGeneratedRingSheaf
import Formal.Util.AssertStandardAxioms
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Law-generated conormal ideal sheaf

The kernel of the law-generated sheafified ring projection `O/I² → O/I`
inherits the ambient multiplication action.  The action factors through the
categorical kernel, and its unit and associativity laws are proved from the
internal ring laws.  No action, stability, kernel comparison, or exactness
certificate is supplied as input.
-/

noncomputable section

namespace ResearchLean.AG.QualitySurface
namespace LawGeneratedConormalIdealSheaf

universe u

open CategoryTheory Limits MonoidalCategory
open Monoidal MonoidalClosed MonoidalClosed.FunctorCategory
open scoped MonObj ModObj
open scoped MonoidalClosed.FunctorCategory
open AAT.AG AAT.AG.LawAlgebra
open LawGeneratedRingSheaf

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable (G : ArchitecturalEquationSystem S.contextPreorder)

noncomputable local instance moduleSheafMonoidal :
    MonoidalCategory (Sheaf S.topology (LargeZMod.{u})) :=
  Sheaf.monoidalCategory S.topology (LargeZMod.{u})

noncomputable local instance moduleSheafBraided :
    BraidedCategory (Sheaf S.topology (LargeZMod.{u})) :=
  Sheaf.braidedCategory S.topology (LargeZMod.{u})

noncomputable local instance moduleSheafMonoidalClosed :
    MonoidalClosed (Sheaf S.topology (LargeZMod.{u})) :=
  Reflective.monoidalClosed (sheafificationAdjunction S.topology (LargeZMod.{u}))

noncomputable local instance moduleSheafTensorLeftAdditive
    (X : Sheaf S.topology (LargeZMod.{u})) : (tensorLeft X).Additive := by
  letI := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tensorLeft X)
  exact Functor.additive_of_preservesBinaryBiproducts (tensorLeft X)

noncomputable local instance moduleSheafTensorRightAdditive
    (X : Sheaf S.topology (LargeZMod.{u})) : (tensorRight X).Additive :=
  Functor.additive_of_iso (BraidedCategory.tensorLeftIsoTensorRight X)

noncomputable local instance moduleSheafMonoidalPreadditive :
    MonoidalPreadditive (Sheaf S.topology (LargeZMod.{u})) where
  whiskerLeft_zero := by
    intros X Y Z
    change (tensorLeft X).map (0 : Y ⟶ Z) = 0
    exact (tensorLeft X).map_zero Y Z
  zero_whiskerRight := by
    intros X Y Z
    change (tensorRight X).map (0 : Y ⟶ Z) = 0
    exact (tensorRight X).map_zero Y Z
  whiskerLeft_add := by
    intros X Y Z f g
    change (tensorLeft X).map (f + g) = _
    exact (tensorLeft X).map_add
  add_whiskerRight := by
    intros X Y Z f g
    change (tensorRight X).map (f + g) = _
    exact (tensorRight X).map_add

/-- Underlying module morphism of the sheafified ring projection. -/
noncomputable abbrev projectionModuleSheaf :
    (q1RingSheafObject G).X ⟶ (q0RingSheafObject G).X :=
  (projectionRingSheaf G).hom.hom

/-- Carrier of the law-generated conormal ideal sheaf. -/
noncomputable abbrev conormalIdealCarrier :
    Sheaf S.topology (LargeZMod.{u}) :=
  kernel (projectionModuleSheaf G)

/-- Multiplication by `O/I²` annihilates the quotient after kernel inclusion. -/
theorem multiplication_kernel_annihilates :
    ((q1RingSheafObject G).X ◁ kernel.ι (projectionModuleSheaf G)) ≫
        μ[(q1RingSheafObject G).X] ≫ projectionModuleSheaf G = 0 := by
  dsimp only [projectionModuleSheaf]
  rw [IsMonHom.mul_hom]
  rw [← id_tensorHom]
  slice_lhs 1 2 => rw [tensorHom_comp_tensorHom]
  rw [Category.id_comp, kernel.condition, MonoidalPreadditive.tensor_zero, zero_comp]

/-- Ambient multiplication factored through the categorical kernel. -/
noncomputable def conormalIdealAction :
    (q1RingSheafObject G).X ⊗ conormalIdealCarrier G ⟶ conormalIdealCarrier G :=
  kernel.lift (projectionModuleSheaf G)
    (((q1RingSheafObject G).X ◁ kernel.ι (projectionModuleSheaf G)) ≫
      μ[(q1RingSheafObject G).X]) (multiplication_kernel_annihilates G)

@[reassoc]
theorem conormalIdealAction_inclusion :
    conormalIdealAction G ≫ kernel.ι (projectionModuleSheaf G) =
      ((q1RingSheafObject G).X ◁ kernel.ι (projectionModuleSheaf G)) ≫
        μ[(q1RingSheafObject G).X] :=
  kernel.lift_ι _ _ _

theorem conormalIdealAction_one :
    η[(q1RingSheafObject G).X] ▷ conormalIdealCarrier G ≫ conormalIdealAction G =
      (λ_ (conormalIdealCarrier G)).hom := by
  apply (cancel_mono (kernel.ι (projectionModuleSheaf G))).1
  rw [Category.assoc, conormalIdealAction_inclusion]
  change η[(q1RingSheafObject G).X] ▷ conormalIdealCarrier G ≫
      (q1RingSheafObject G).X ◁ kernel.ι (projectionModuleSheaf G) ≫
        μ[(q1RingSheafObject G).X] =
    (λ_ (conormalIdealCarrier G)).hom ≫ kernel.ι (projectionModuleSheaf G)
  rw [← whisker_exchange_assoc]
  rw [MonObj.one_mul]
  simp

theorem conormalIdealAction_mul :
    μ[(q1RingSheafObject G).X] ▷ conormalIdealCarrier G ≫ conormalIdealAction G =
      (α_ (q1RingSheafObject G).X (q1RingSheafObject G).X
        (conormalIdealCarrier G)).hom ≫
      (q1RingSheafObject G).X ◁ conormalIdealAction G ≫ conormalIdealAction G := by
  apply (cancel_mono (kernel.ι (projectionModuleSheaf G))).1
  simp only [Category.assoc]
  rw [conormalIdealAction_inclusion]
  rw [← MonoidalCategory.whiskerLeft_comp_assoc]
  rw [conormalIdealAction_inclusion]
  simp only [mon_tauto]

/-- The categorical kernel with its generated ambient module structure. -/
noncomputable def conormalIdealModObj :
    ModObj (q1RingSheafObject G).X (conormalIdealCarrier G) where
  smul := conormalIdealAction G
  one_smul' := conormalIdealAction_one G
  mul_smul' := conormalIdealAction_mul G

/-- The law-generated true conormal ideal object. -/
noncomputable def conormalIdeal :
    Mod_ (Sheaf S.topology (LargeZMod.{u})) (q1RingSheafObject G).X := by
  letI := conormalIdealModObj G
  exact { X := conormalIdealCarrier G }

/-- Inclusion of the generated conormal ideal into the regular ambient module. -/
noncomputable def conormalIdealInclusion :
    conormalIdeal G ⟶ Mod_.regular (q1RingSheafObject G).X :=
  Mod_.Hom.mk' (kernel.ι (projectionModuleSheaf G))
    (conormalIdealAction_inclusion G)

@[simp]
theorem conormalIdealInclusion_hom :
    (conormalIdealInclusion G).hom = kernel.ι (projectionModuleSheaf G) :=
  rfl

/-- The bundled ideal inclusion is killed by the quotient projection. -/
theorem conormalIdealInclusion_projection_zero :
    (conormalIdealInclusion G).hom ≫ projectionModuleSheaf G = 0 :=
  kernel.condition (projectionModuleSheaf G)

end LawGeneratedConormalIdealSheaf
end ResearchLean.AG.QualitySurface

#assert_standard_axioms_only ResearchLean.AG.QualitySurface.LawGeneratedConormalIdealSheaf
