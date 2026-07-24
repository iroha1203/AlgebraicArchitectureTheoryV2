import Formal.AG.SemanticRepair.Conormal.LawGeneratedIdealPowerLiftedSheafification
import Formal.Util.AssertStandardAxioms
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Internal.Module
import Mathlib.CategoryTheory.Monoidal.Mod_
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Tactic

/-!
# Law-generated ring-sheaf checkpoint

The observable rings and their two ideal-power quotients are interpreted as
commutative algebra objects in large-universe integer modules.  Monoidal
sheafification transports the `O/I^2` and `O/I` ring objects and their
projection to the selected AAT site.  The categorical kernel and its proved
ambient action are the next checkpoint.

No ring action, ideal-stability premise, kernel comparison, or exactness
certificate is supplied as input.
-/

noncomputable section

namespace AAT.AG.SemanticRepair.Conormal
namespace LawGeneratedRingSheaf

universe u

open CategoryTheory Limits Opposite MonoidalCategory
open scoped MonObj ModObj
open AAT.AG AAT.AG.LawAlgebra

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable (G : ArchitecturalEquationSystem S.contextPreorder)

/-- Large-universe integers used as the scalar ring for internal ring objects. -/
abbrev LargeInt := ULift.{u + 1} ℤ

/-- Large-universe integer modules. -/
abbrev LargeZMod := ModuleCat.{u + 1} LargeInt.{u}

/-- Canonical large-integer algebra structure on a lifted commutative ring. -/
noncomputable def uliftIntAlgebra (R : Type u) [CommRing R] :
    Algebra LargeInt.{u} (ULift.{u + 1} R) :=
  ((Int.castRingHom (ULift.{u + 1} R)).comp
    ULift.ringEquiv.toRingHom).toAlgebra

attribute [local instance] uliftIntAlgebra

/-- Universe lift of a ring homomorphism. -/
def liftRingHom {R T : Type u} [CommRing R] [CommRing T] (f : R →+* T) :
    ULift.{u + 1} R →+* ULift.{u + 1} T :=
  ULift.ringEquiv.symm.toRingHom.comp (f.comp ULift.ringEquiv.toRingHom)

@[simp] theorem liftRingHom_up {R T : Type u} [CommRing R] [CommRing T]
    (f : R →+* T) (x : R) : liftRingHom f (ULift.up x) = ULift.up (f x) := rfl

/-- A lifted ring map is linear over the canonical large integers. -/
def liftAlgHom {R T : Type u} [CommRing R] [CommRing T] (f : R →+* T) :
    ULift.{u + 1} R →ₐ[LargeInt.{u}] ULift.{u + 1} T where
  __ := liftRingHom f
  commutes' z := by
    obtain ⟨z⟩ := z
    apply ULift.down_injective
    change f (z : R) = (z : T)
    exact map_intCast f z

/-- Lift a commutative ring to its internal commutative algebra object. -/
noncomputable def commRingObject (R : Type u) [CommRing R] :
    CommMon (LargeZMod.{u}) := by
  let B : AlgCat.{u + 1} LargeInt.{u} := AlgCat.of LargeInt.{u} (ULift.{u + 1} R)
  let M : Mon (LargeZMod.{u}) :=
    ModuleCat.MonModuleEquivalenceAlgebra.inverse.obj B
  refine { M with comm := ?_ }
  constructor
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  intro x y
  change (μ[M.X] : M.X ⊗ M.X ⟶ M.X)
      ((β_ M.X M.X).hom (x ⊗ₜ y)) = μ[M.X] (x ⊗ₜ y)
  rw [ModuleCat.MonoidalCategory.braiding_hom_apply]
  dsimp [M, ModuleCat.MonModuleEquivalenceAlgebra.inverse,
    ModuleCat.MonModuleEquivalenceAlgebra.inverseObj]
  change (y : ULift.{u + 1} R) * x = x * y
  exact @mul_comm (ULift.{u + 1} R) (inferInstance : CommMagma (ULift.{u + 1} R)) y x

/-- A lifted ring homomorphism is a morphism of internal commutative rings. -/
noncomputable def commRingObjectMap {R T : Type u} [CommRing R] [CommRing T]
    (f : R →+* T) : commRingObject R ⟶ commRingObject T := by
  apply CommMon.homMk
  simpa only [commRingObject] using
    (ModuleCat.MonModuleEquivalenceAlgebra.inverse.map
      (AlgCat.ofHom (liftAlgHom f)))

/-! ## Raw law-generated internal ring presheaves -/

/-- Observable rings as internal commutative rings in large integer modules. -/
noncomputable def observableRingCoefficient :
    S.categoryᵒᵖ ⥤ CommMon (LargeZMod.{u}) where
  obj W := commRingObject (G.Observable W.unop)
  map φ := commRingObjectMap (G.restrict φ.unop)
  map_id X := by
    apply InducedCategory.hom_ext
    apply Mon.hom_injective
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x⟩ := x
    exact congrArg ULift.up (G.restrict_id X.unop x)
  map_comp φ ψ := by
    apply InducedCategory.hom_ext
    apply Mon.hom_injective
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x⟩ := x
    exact congrArg ULift.up (G.restrict_comp ψ.unop φ.unop x)

/-- First-order quotients `O/I²` as internal commutative rings. -/
noncomputable def q1RingCoefficient :
    S.categoryᵒᵖ ⥤ CommMon (LargeZMod.{u}) where
  obj W := commRingObject (LawGeneratedIdealPowerSequence.Raw.Q1 G W.unop)
  map φ := commRingObjectMap (LawGeneratedIdealPowerSequence.Raw.q1Restrict G φ.unop)
  map_id X := by
    apply InducedCategory.hom_ext
    apply Mon.hom_injective
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x⟩ := x
    change ULift.up
      (LawGeneratedIdealPowerSequence.Raw.q1Restrict G (𝟙 X).unop x) = ULift.up x
    apply congrArg ULift.up
    refine Quotient.inductionOn' x ?_
    intro r
    change LawGeneratedIdealPowerSequence.Raw.q1Restrict G (𝟙 X).unop
        (Ideal.Quotient.mk ((LawGeneratedIdealPowerSequence.Raw.I G X.unop) ^ 2) r) =
      Ideal.Quotient.mk ((LawGeneratedIdealPowerSequence.Raw.I G X.unop) ^ 2) r
    rw [LawGeneratedIdealPowerSequence.Raw.q1Restrict_mk]
    exact congrArg _ (by simpa using G.restrict_id X.unop r)
  map_comp φ ψ := by
    apply InducedCategory.hom_ext
    apply Mon.hom_injective
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x⟩ := x
    change ULift.up
      (LawGeneratedIdealPowerSequence.Raw.q1Restrict G (φ ≫ ψ).unop x) =
      ULift.up (LawGeneratedIdealPowerSequence.Raw.q1Restrict G ψ.unop
        (LawGeneratedIdealPowerSequence.Raw.q1Restrict G φ.unop x))
    apply congrArg ULift.up
    refine Quotient.inductionOn' x ?_
    intro r
    change LawGeneratedIdealPowerSequence.Raw.q1Restrict G (φ ≫ ψ).unop
        (Ideal.Quotient.mk ((LawGeneratedIdealPowerSequence.Raw.I G _) ^ 2) r) =
      LawGeneratedIdealPowerSequence.Raw.q1Restrict G ψ.unop
        (LawGeneratedIdealPowerSequence.Raw.q1Restrict G φ.unop
          (Ideal.Quotient.mk
            ((LawGeneratedIdealPowerSequence.Raw.I G _) ^ 2) r))
    rw [LawGeneratedIdealPowerSequence.Raw.q1Restrict_mk,
      LawGeneratedIdealPowerSequence.Raw.q1Restrict_mk,
      LawGeneratedIdealPowerSequence.Raw.q1Restrict_mk]
    exact congrArg _ (by simpa using G.restrict_comp ψ.unop φ.unop r)

/-- Quotients `O/I` as internal commutative rings. -/
noncomputable def q0RingCoefficient :
    S.categoryᵒᵖ ⥤ CommMon (LargeZMod.{u}) where
  obj W := commRingObject (G.ObstructionQuotient W.unop)
  map φ := commRingObjectMap (G.obstructionQuotientRestrict φ.unop)
  map_id X := by
    apply InducedCategory.hom_ext
    apply Mon.hom_injective
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x⟩ := x
    change ULift.up (G.obstructionQuotientRestrict (𝟙 X).unop x) = ULift.up x
    apply congrArg ULift.up
    refine Quotient.inductionOn' x ?_
    intro r
    change G.obstructionQuotientRestrict (𝟙 X).unop
        (Ideal.Quotient.mk (G.obstructionIdeal X.unop) r) =
      Ideal.Quotient.mk (G.obstructionIdeal X.unop) r
    rw [G.obstructionQuotientRestrict_mk]
    exact congrArg _ (by simpa using G.restrict_id X.unop r)
  map_comp φ ψ := by
    apply InducedCategory.hom_ext
    apply Mon.hom_injective
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x⟩ := x
    change ULift.up (G.obstructionQuotientRestrict (φ ≫ ψ).unop x) =
      ULift.up (G.obstructionQuotientRestrict ψ.unop
        (G.obstructionQuotientRestrict φ.unop x))
    apply congrArg ULift.up
    refine Quotient.inductionOn' x ?_
    intro r
    change G.obstructionQuotientRestrict (φ ≫ ψ).unop
        (Ideal.Quotient.mk (G.obstructionIdeal _) r) =
      G.obstructionQuotientRestrict ψ.unop
        (G.obstructionQuotientRestrict φ.unop
          (Ideal.Quotient.mk (G.obstructionIdeal _) r))
    rw [G.obstructionQuotientRestrict_mk, G.obstructionQuotientRestrict_mk,
      G.obstructionQuotientRestrict_mk]
    exact congrArg _ (by simpa using G.restrict_comp ψ.unop φ.unop r)

/-- Underlying module presheaf of the observable internal ring. -/
noncomputable abbrev observableModuleCoefficient :
    S.categoryᵒᵖ ⥤ LargeZMod.{u} :=
  observableRingCoefficient G ⋙ CommMon.forget₂Mon (LargeZMod.{u}) ⋙
    Mon.forget (LargeZMod.{u})

/-- Underlying module presheaf of `O/I²`. -/
noncomputable abbrev q1ModuleCoefficient :
    S.categoryᵒᵖ ⥤ LargeZMod.{u} :=
  q1RingCoefficient G ⋙ CommMon.forget₂Mon (LargeZMod.{u}) ⋙
    Mon.forget (LargeZMod.{u})

/-- Underlying module presheaf of `O/I`. -/
noncomputable abbrev q0ModuleCoefficient :
    S.categoryᵒᵖ ⥤ LargeZMod.{u} :=
  q0RingCoefficient G ⋙ CommMon.forget₂Mon (LargeZMod.{u}) ⋙
    Mon.forget (LargeZMod.{u})

/-- The quotient projections form a morphism of raw internal ring presheaves. -/
noncomputable def projectionRingCoefficient :
    q1RingCoefficient G ⟶ q0RingCoefficient G where
  app W := commRingObjectMap
    (LawGeneratedIdealPowerSequence.Raw.projectionAt G W.unop)
  naturality {X Y} φ := by
    apply InducedCategory.hom_ext
    apply Mon.hom_injective
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x⟩ := x
    change ULift.up
        (LawGeneratedIdealPowerSequence.Raw.projectionAt G Y.unop
          (LawGeneratedIdealPowerSequence.Raw.q1Restrict G φ.unop x)) =
      ULift.up (G.obstructionQuotientRestrict φ.unop
        (LawGeneratedIdealPowerSequence.Raw.projectionAt G X.unop x))
    apply congrArg ULift.up
    refine Quotient.inductionOn' x ?_
    intro r
    change LawGeneratedIdealPowerSequence.Raw.projectionAt G Y.unop
        (LawGeneratedIdealPowerSequence.Raw.q1Restrict G φ.unop
          (Ideal.Quotient.mk
            ((LawGeneratedIdealPowerSequence.Raw.I G X.unop) ^ 2) r)) =
      G.obstructionQuotientRestrict φ.unop
        (LawGeneratedIdealPowerSequence.Raw.projectionAt G X.unop
          (Ideal.Quotient.mk
            ((LawGeneratedIdealPowerSequence.Raw.I G X.unop) ^ 2) r))
    rw [LawGeneratedIdealPowerSequence.Raw.q1Restrict_mk,
      LawGeneratedIdealPowerSequence.Raw.projectionAt_mk,
      LawGeneratedIdealPowerSequence.Raw.projectionAt_mk,
      G.obstructionQuotientRestrict_mk]

/-! ## Internal ring presheaves and monoidal sheafification -/

/-- The raw first-order quotient as one internal commutative ring presheaf object. -/
noncomputable def q1RingPresheafObject :
    CommMon (S.categoryᵒᵖ ⥤ LargeZMod.{u}) :=
  (Monoidal.commMonFunctorCategoryEquivalence S.categoryᵒᵖ
    (LargeZMod.{u})).inverse.obj (q1RingCoefficient G)

/-- The raw obstruction quotient as one internal commutative ring presheaf object. -/
noncomputable def q0RingPresheafObject :
    CommMon (S.categoryᵒᵖ ⥤ LargeZMod.{u}) :=
  (Monoidal.commMonFunctorCategoryEquivalence S.categoryᵒᵖ
    (LargeZMod.{u})).inverse.obj (q0RingCoefficient G)

/-- Projection of the raw internal commutative ring presheaves. -/
noncomputable def projectionRingPresheaf :
    q1RingPresheafObject G ⟶ q0RingPresheafObject G :=
  (Monoidal.commMonFunctorCategoryEquivalence S.categoryᵒᵖ
    (LargeZMod.{u})).inverse.map (projectionRingCoefficient G)

/-- Canonical monoidal sheafification on large integer modules. -/
noncomputable abbrev moduleSheafification :
    (S.categoryᵒᵖ ⥤ LargeZMod.{u}) ⥤ Sheaf S.topology (LargeZMod.{u}) :=
  presheafToSheaf S.topology (LargeZMod.{u})

noncomputable local instance moduleSheafMonoidal :
    MonoidalCategory (Sheaf S.topology (LargeZMod.{u})) :=
  Sheaf.monoidalCategory S.topology (LargeZMod.{u})

noncomputable local instance moduleSheafBraided :
    BraidedCategory (Sheaf S.topology (LargeZMod.{u})) :=
  Sheaf.braidedCategory S.topology (LargeZMod.{u})

/-- The sheafified internal ring `O/I²`. -/
noncomputable def q1RingSheafObject :
    CommMon (Sheaf S.topology (LargeZMod.{u})) :=
  (moduleSheafification (S := S)).mapCommMon.obj (q1RingPresheafObject G)

/-- The sheafified internal ring `O/I`. -/
noncomputable def q0RingSheafObject :
    CommMon (Sheaf S.topology (LargeZMod.{u})) :=
  (moduleSheafification (S := S)).mapCommMon.obj (q0RingPresheafObject G)

/-- Sheafified internal-ring projection `O/I² → O/I`. -/
noncomputable def projectionRingSheaf :
    q1RingSheafObject G ⟶ q0RingSheafObject G :=
  (moduleSheafification (S := S)).mapCommMon.map (projectionRingPresheaf G)

end LawGeneratedRingSheaf
end AAT.AG.SemanticRepair.Conormal

#assert_standard_axioms_only AAT.AG.SemanticRepair.Conormal.LawGeneratedRingSheaf
