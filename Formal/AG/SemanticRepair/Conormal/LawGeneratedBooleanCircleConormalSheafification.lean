import Formal.AG.SemanticRepair.Conormal.LawGeneratedBooleanCircleRawConormalSheaf
import Formal.AG.SemanticRepair.Conormal.LawGeneratedIdealPowerLiftedSheafification
import Formal.Util.AssertStandardAxioms
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Canonical sheafification comparison for the Boolean-circle conormal coefficients

The two concrete raw conormal presheaves proved to be sheaves in Cycle 20 are
lifted to the coefficient universe used by the existing short exact sequence.
Mathlib's canonical sheafification unit then gives the comparison with the
first object of that sequence.  No comparison, restriction compatibility, or
cohomology conclusion is accepted as input data.
-/

noncomputable section

namespace AAT.AG.SemanticRepair.Conormal
namespace LawGeneratedBooleanCircleConormalSheafification

universe u

open CategoryTheory Opposite
open AAT.AG AAT.AG.LawAlgebra
open LawGeneratedBooleanCircleSite
open LawGeneratedBooleanCircleLawCore
open LawGeneratedBooleanCircleRawConormalSheaf
open LawGeneratedIdealPowerSequence.Raw
open LawGeneratedIdealPowerLiftedSheafification

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable (G : ArchitecturalEquationSystem S.contextPreorder)

/-- A raw conormal sheaf remains a sheaf after the canonical additive universe lift. -/
theorem liftedConormal_isSheaf
    (hG : Presheaf.IsSheaf S.topology (conormalCoefficient G)) :
    Presheaf.IsSheaf S.topology (liftedShortComplex G).X₁ := by
  change Presheaf.IsSheaf S.topology
    ((liftPresheafFunctor (S := S)).obj (conormalCoefficient G))
  exact Presheaf.isSheaf_comp_of_isSheaf S.topology
    (conormalCoefficient G) AddCommGrpCat.uliftFunctor hG

/-- The first sheafified term is canonically the sheafification of the lifted raw conormal. -/
noncomputable def liftedRawConormalSheafificationIso
    (hG : Presheaf.IsSheaf S.topology (conormalCoefficient G)) :
    (liftedShortComplex G).X₁ ≅ (sheafifiedShortComplex G).X₁.val := by
  let P := (liftedShortComplex G).X₁
  let hP : Presheaf.IsSheaf S.topology P := liftedConormal_isSheaf G hG
  simpa only [
    LawGeneratedIdealPowerLiftedSheafification.sheafifiedShortComplex,
    ShortComplex.map] using
    (S.topology.isoSheafify hP ≪≫
      plusPlusIsoSheafify S.topology AddCommGrpCat.{u + 1} P)

/-- The comparison hom is exactly the canonical abstract sheafification unit. -/
theorem liftedRawConormalSheafificationIso_hom
    (hG : Presheaf.IsSheaf S.topology (conormalCoefficient G)) :
    (liftedRawConormalSheafificationIso G hG).hom =
      CategoryTheory.toSheafify S.topology (liftedShortComplex G).X₁ := by
  dsimp [liftedRawConormalSheafificationIso]
  rw [toSheafify_plusPlusIsoSheafify_hom]

/-- A small raw conormal section is canonically its universe lift. -/
noncomputable def rawToLiftedX1Equiv (W : S.category) :
    Conormal G W ≃+ (liftedShortComplex G).X₁.obj (op W) := by
  change Conormal G W ≃+ ULift.{u + 1} (Conormal G W)
  exact AddEquiv.ulift.symm

/-- The lifted restriction is the universe lift of the raw conormal restriction. -/
theorem liftedX1_map_up {source target : S.category}
    (f : source ⟶ target) (x : Conormal G target) :
    (liftedShortComplex G).X₁.map f.op (rawToLiftedX1Equiv G target x) =
      rawToLiftedX1Equiv G source (conormalRestrict G f x) := by
  rfl

/-- Sectionwise comparison from the small raw conormal to the sheafified first term. -/
noncomputable def rawConormalX1Equiv
    (hG : Presheaf.IsSheaf S.topology (conormalCoefficient G))
    (W : S.category) :
    Conormal G W ≃+ (sheafifiedShortComplex G).X₁.val.obj (op W) :=
  (rawToLiftedX1Equiv G W).trans
    ((liftedRawConormalSheafificationIso G hG).app (op W)).addCommGroupIsoToAddEquiv

/-- The sectionwise comparison commutes with every raw restriction. -/
theorem rawConormalX1Equiv_restrict
    (hG : Presheaf.IsSheaf S.topology (conormalCoefficient G))
    {source target : S.category} (f : source ⟶ target)
    (x : Conormal G target) :
    rawConormalX1Equiv G hG source (conormalRestrict G f x) =
      (sheafifiedShortComplex G).X₁.val.map f.op
        (rawConormalX1Equiv G hG target x) := by
  rw [rawConormalX1Equiv, rawConormalX1Equiv]
  change
    (liftedRawConormalSheafificationIso G hG).hom.app (op source)
        (rawToLiftedX1Equiv G source (conormalRestrict G f x)) =
      (sheafifiedShortComplex G).X₁.val.map f.op
        ((liftedRawConormalSheafificationIso G hG).hom.app (op target)
          (rawToLiftedX1Equiv G target x))
  rw [← liftedX1_map_up G f x]
  exact (liftedRawConormalSheafificationIso G hG).hom.naturality_apply f.op
    (rawToLiftedX1Equiv G target x)

/-! ## Concrete Boolean-circle comparisons -/

/-- The lifted square-zero conormal coefficient is a sheaf. -/
theorem squareZeroLiftedConormal_isSheaf :
    Presheaf.IsSheaf site.topology (liftedShortComplex squareZeroCore).X₁ :=
  liftedConormal_isSheaf squareZeroCore squareZeroRawConormal_isSheaf

/-- The lifted idempotent conormal coefficient is a sheaf. -/
theorem idempotentLiftedConormal_isSheaf :
    Presheaf.IsSheaf site.topology (liftedShortComplex idempotentCore).X₁ :=
  liftedConormal_isSheaf idempotentCore idempotentRawConormal_isSheaf

/-- Canonical comparison for the concrete square-zero conormal coefficient. -/
noncomputable def squareZeroConormalSheafificationIso :
    (liftedShortComplex squareZeroCore).X₁ ≅
      (sheafifiedShortComplex squareZeroCore).X₁.val :=
  liftedRawConormalSheafificationIso squareZeroCore squareZeroRawConormal_isSheaf

/-- Canonical comparison for the concrete idempotent conormal coefficient. -/
noncomputable def idempotentConormalSheafificationIso :
    (liftedShortComplex idempotentCore).X₁ ≅
      (sheafifiedShortComplex idempotentCore).X₁.val :=
  liftedRawConormalSheafificationIso idempotentCore idempotentRawConormal_isSheaf

/-- Sectionwise square-zero comparison, with no sheaf premise left as an argument. -/
noncomputable def squareZeroRawConormalX1Equiv (W : site.category) :
    Conormal squareZeroCore W ≃+
      (sheafifiedShortComplex squareZeroCore).X₁.val.obj (op W) :=
  rawConormalX1Equiv squareZeroCore squareZeroRawConormal_isSheaf W

/-- Sectionwise idempotent comparison, with no sheaf premise left as an argument. -/
noncomputable def idempotentRawConormalX1Equiv (W : site.category) :
    Conormal idempotentCore W ≃+
      (sheafifiedShortComplex idempotentCore).X₁.val.obj (op W) :=
  rawConormalX1Equiv idempotentCore idempotentRawConormal_isSheaf W

/-- The concrete square-zero sectionwise comparison commutes with restriction. -/
theorem squareZeroRawConormalX1Equiv_restrict
    {source target : site.category} (f : source ⟶ target)
    (x : Conormal squareZeroCore target) :
    squareZeroRawConormalX1Equiv source
        (conormalRestrict squareZeroCore f x) =
      (sheafifiedShortComplex squareZeroCore).X₁.val.map f.op
        (squareZeroRawConormalX1Equiv target x) :=
  rawConormalX1Equiv_restrict squareZeroCore squareZeroRawConormal_isSheaf f x

/-- The concrete idempotent sectionwise comparison commutes with restriction. -/
theorem idempotentRawConormalX1Equiv_restrict
    {source target : site.category} (f : source ⟶ target)
    (x : Conormal idempotentCore target) :
    idempotentRawConormalX1Equiv source
        (conormalRestrict idempotentCore f x) =
      (sheafifiedShortComplex idempotentCore).X₁.val.map f.op
        (idempotentRawConormalX1Equiv target x) :=
  rawConormalX1Equiv_restrict idempotentCore idempotentRawConormal_isSheaf f x

end LawGeneratedBooleanCircleConormalSheafification
end AAT.AG.SemanticRepair.Conormal

#assert_standard_axioms_only AAT.AG.SemanticRepair.Conormal.LawGeneratedBooleanCircleConormalSheafification
