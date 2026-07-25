import Formal.AG.SemanticRepair.Conormal.LawGeneratedConormalIdealSheaf
import Formal.Util.AssertStandardAxioms
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Tactic

/-!
# Canonical comparison for the law-generated conormal sheaf

The additive ideal-power sequence and the underlying additive sheaves of the
internal quotient-ring sheaves are compared by the canonical natural
isomorphism expressing preservation of sheafification by the module forgetful
functor.  The conormal comparison is then generated from uniqueness of the
categorical kernel; it is not accepted as input data.
-/

noncomputable section

namespace AAT.AG.SemanticRepair.Conormal
namespace LawGeneratedConormalComparison

universe u

open CategoryTheory Limits Opposite
open AAT.AG AAT.AG.LawAlgebra
open LawGeneratedRingSheaf LawGeneratedConormalIdealSheaf

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable (G : ArchitecturalEquationSystem S.contextPreorder)

noncomputable def moduleForgetEquivalence :
    CategoryTheory.Equivalence (LargeZMod.{u}) AddCommGrpCat.{u + 1} :=
  (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (ULift.ringEquiv.symm : ℤ ≃+* LargeInt.{u})).trans
    (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).asEquivalence

/-- Forget a large integer module to its additive commutative group. -/
abbrev moduleForget : LargeZMod.{u} ⥤ AddCommGrpCat.{u + 1} :=
  forget₂ (LargeZMod.{u}) AddCommGrpCat.{u + 1}

/-- Large integer modules and large additive groups are canonically equivalent. -/
noncomputable local instance moduleForgetIsEquivalence : moduleForget.IsEquivalence :=
  moduleForgetEquivalence.isEquivalence_functor

noncomputable local instance moduleForgetPreservesSheafification :
    S.topology.PreservesSheafification moduleForget := by
  exact Sheaf.preservesSheafification_of_adjunction S.topology
    (Adjunction.ofIsLeftAdjoint moduleForget)

noncomputable local instance moduleSheafMonoidal :
    MonoidalCategory (Sheaf S.topology (LargeZMod.{u})) :=
  Sheaf.monoidalCategory S.topology (LargeZMod.{u})

noncomputable local instance moduleSheafBraided :
    BraidedCategory (Sheaf S.topology (LargeZMod.{u})) :=
  Sheaf.braidedCategory S.topology (LargeZMod.{u})

/-- Canonical natural comparison between the two sheafification routes. -/
noncomputable def sheafificationComparison :
    (Functor.whiskeringRight S.categoryᵒᵖ
        (LargeZMod.{u}) AddCommGrpCat.{u + 1}).obj moduleForget ⋙
        presheafToSheaf S.topology AddCommGrpCat.{u + 1} ≅
      presheafToSheaf S.topology (LargeZMod.{u}) ⋙
        sheafCompose S.topology moduleForget :=
  sheafComposeNatIso S.topology moduleForget
    (sheafificationAdjunction S.topology (LargeZMod.{u}))
    (sheafificationAdjunction S.topology AddCommGrpCat.{u + 1})

/-- Canonical comparison for the first-order quotient `O/I²`. -/
noncomputable def q1SheafIso :
    (LawGeneratedIdealPowerLiftedSheafification.sheafifiedShortComplex G).X₂ ≅
      (sheafCompose S.topology moduleForget).obj (q1RingSheafObject G).X :=
  (sheafificationComparison (S := S)).app (q1ModuleCoefficient G)

/-- Canonical comparison for the obstruction quotient `O/I`. -/
noncomputable def q0SheafIso :
    (LawGeneratedIdealPowerLiftedSheafification.sheafifiedShortComplex G).X₃ ≅
      (sheafCompose S.topology moduleForget).obj (q0RingSheafObject G).X :=
  (sheafificationComparison (S := S)).app (q0ModuleCoefficient G)

/-- The quotient comparisons commute with the sheafified projection. -/
theorem projection_square :
    (q1SheafIso G).hom ≫
        (sheafCompose S.topology moduleForget).map (projectionModuleSheaf G) =
      (LawGeneratedIdealPowerLiftedSheafification.sheafifiedShortComplex G).g ≫
        (q0SheafIso G).hom := by
  exact ((sheafificationComparison (S := S)).hom.naturality
    (projectionRingPresheaf G).hom.hom).symm

/-- Canonical comparison from the additive conormal sheaf to the true ideal carrier. -/
noncomputable def conormalSheafIso :
    (LawGeneratedIdealPowerLiftedSheafification.sheafifiedShortComplex G).X₁ ≅
      (sheafCompose S.topology moduleForget).obj (conormalIdealCarrier G) :=
  (IsLimit.conePointUniqueUpToIso
      (LawGeneratedIdealPowerLiftedSheafification.sheafifiedShortComplex_shortExact G).fIsKernel
      (kernelIsKernel
        (LawGeneratedIdealPowerLiftedSheafification.sheafifiedShortComplex G).g)) ≪≫
    (kernel.mapIso
      (LawGeneratedIdealPowerLiftedSheafification.sheafifiedShortComplex G).g
      ((sheafCompose S.topology moduleForget).map (projectionModuleSheaf G))
      (q1SheafIso G) (q0SheafIso G) (projection_square G).symm) ≪≫
    (PreservesKernel.iso (sheafCompose S.topology moduleForget)
      (projectionModuleSheaf G)).symm

/-- The generated conormal comparison carries inclusion to inclusion. -/
@[reassoc]
theorem conormalSheafIso_inclusion :
    (conormalSheafIso G).hom ≫
        (sheafCompose S.topology moduleForget).map
          (kernel.ι (projectionModuleSheaf G)) =
      (LawGeneratedIdealPowerLiftedSheafification.sheafifiedShortComplex G).f ≫
        (q1SheafIso G).hom := by
  dsimp [conormalSheafIso]
  simp
  rw [← Category.assoc]
  congr 1
  simpa using
    IsLimit.conePointUniqueUpToIso_hom_comp
      (LawGeneratedIdealPowerLiftedSheafification.sheafifiedShortComplex_shortExact G).fIsKernel
      (kernelIsKernel
        (LawGeneratedIdealPowerLiftedSheafification.sheafifiedShortComplex G).g)
      WalkingParallelPair.zero

/-- The underlying additive short complex of the true conormal ideal sequence. -/
noncomputable def internalUnderlyingShortComplex :
    ShortComplex (Sheaf S.topology AddCommGrpCat.{u + 1}) :=
  ShortComplex.mk
    ((sheafCompose S.topology moduleForget).map
      (kernel.ι (projectionModuleSheaf G)))
    ((sheafCompose S.topology moduleForget).map (projectionModuleSheaf G))
    (by rw [← Functor.map_comp, kernel.condition, Functor.map_zero])

/-- The entire additive sequence is canonically the underlying ideal sequence. -/
noncomputable def shortComplexIso :
    LawGeneratedIdealPowerLiftedSheafification.sheafifiedShortComplex G ≅
      internalUnderlyingShortComplex G :=
  ShortComplex.isoMk (conormalSheafIso G) (q1SheafIso G) (q0SheafIso G)
    (conormalSheafIso_inclusion G) (projection_square G)

/-- The underlying true-ideal sequence is short exact. -/
theorem internalUnderlyingShortExact :
    (internalUnderlyingShortComplex G).ShortExact :=
  ShortComplex.shortExact_of_iso (shortComplexIso G)
    (LawGeneratedIdealPowerLiftedSheafification.sheafifiedShortComplex_shortExact G)

end LawGeneratedConormalComparison
end AAT.AG.SemanticRepair.Conormal

#assert_standard_axioms_only AAT.AG.SemanticRepair.Conormal.LawGeneratedConormalComparison
