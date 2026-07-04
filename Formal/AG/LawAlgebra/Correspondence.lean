import Formal.AG.Atom.LawfulnessZero
import Formal.AG.Atom.ThreeReading
import Formal.AG.LawAlgebra.LawEquation
import Formal.AG.LawAlgebra.LawfulLocus

noncomputable section

namespace AAT.AG
namespace LawAlgebra

universe u v w

namespace Correspondence

open LawfulLocus

variable {U : AtomCarrier.{u}}
variable {R : Type v} [CommRing R]
variable {IOb : Ideal R}
variable (s : LawfulSectionData.{v, w} R IOb)
variable (Obj : ArchitectureObject U)
variable (LU : LawUniverse U)
variable (Sig : SignatureAxes U)
variable {Value : Type u}
variable (valuation : ObstructionValuation U Value)
variable (aggregation :
  ZeroReflectingAggregation Value valuation.domain LU.RequiredIndex)

/--
III.定理11.1: explicit assumptions for the Lawfulness-Ideal Correspondence.

The seven named assumptions are kept visible as theorem data:
obstruction soundness, obstruction completeness, axis exactness, witness
coverage, U-adequate cover, sheaf descent for `Ob_U`, and ring restriction
compatibility. The theorem-shaped fields are the assumptions themselves, not
additional unnamed bridges.
-/
structure LawfulnessIdealCorrespondenceAssumptions where
  obstructionSoundness :
    ∀ index : LU.RequiredIndex, ObstructionSound valuation (LU.law index.1)
  obstructionCompleteness :
    ∀ index : LU.RequiredIndex, ObstructionComplete valuation (LU.law index.1)
  axisExactness : Lawfulness Obj LU ↔ RequiredSignatureAxesZero Obj Sig
  uAdequateCover : Prop
  obstructionSheafDescent : Prop
  ringRestrictionCompatibility : Prop
  witnessCoverage :
    uAdequateCover -> obstructionSheafDescent -> ringRestrictionCompatibility ->
      (s.Lawful ↔ Lawfulness Obj LU)
  uAdequateCover_holds : uAdequateCover
  obstructionSheafDescent_holds : obstructionSheafDescent
  ringRestrictionCompatibility_holds : ringRestrictionCompatibility

namespace LawfulnessIdealCorrespondenceAssumptions

/-- III.定理11.1: local ideal lawfulness agrees with PRD-1 lawfulness. -/
theorem lawful_iff_semanticLawfulness
    (H : LawfulnessIdealCorrespondenceAssumptions s Obj LU Sig valuation) :
    s.Lawful ↔ Lawfulness Obj LU :=
  H.witnessCoverage H.uAdequateCover_holds H.obstructionSheafDescent_holds
    H.ringRestrictionCompatibility_holds

/--
III.定理11.1: local ideal lawfulness agrees with aggregate obstruction
valuation zero, using PRD-1 `omegaU`.
-/
theorem lawful_iff_omegaU_zero
    (H : LawfulnessIdealCorrespondenceAssumptions s Obj LU Sig valuation) :
    s.Lawful ↔ omegaU valuation LU aggregation Obj = valuation.domain.zero :=
  (lawful_iff_semanticLawfulness s Obj LU Sig valuation H).trans
    (lawfulness_iff_omegaU_zero valuation LU aggregation
      H.obstructionSoundness H.obstructionCompleteness Obj)

/--
III.定理11.1: local ideal lawfulness agrees with PRD-1
`RequiredSignatureAxesZero`.
-/
theorem lawful_iff_requiredSignatureAxesZero
    (H : LawfulnessIdealCorrespondenceAssumptions s Obj LU Sig valuation) :
    s.Lawful ↔ RequiredSignatureAxesZero Obj Sig :=
  (lawful_iff_semanticLawfulness s Obj LU Sig valuation H).trans
    H.axisExactness

end LawfulnessIdealCorrespondenceAssumptions

/-- III.定理11.1: theorem package exposing each edge of the five-term chain. -/
structure LawfulnessIdealCorrespondencePackage
    (H : LawfulnessIdealCorrespondenceAssumptions s Obj LU Sig valuation) where
  lawful_iff_pulled :
    s.Lawful ↔ s.pulledObstructionIdeal = ⊥
  pulled_iff_factors :
    s.pulledObstructionIdeal = ⊥ ↔ s.FactorsThroughLawfulLocus
  factors_iff_omega :
    s.FactorsThroughLawfulLocus ↔
      omegaU valuation LU aggregation Obj = valuation.domain.zero
  omega_iff_signature :
    omegaU valuation LU aggregation Obj = valuation.domain.zero ↔
      RequiredSignatureAxesZero Obj Sig
  lawful_iff_signature :
    s.Lawful ↔ RequiredSignatureAxesZero Obj Sig

/-- III.定理11.1: `Lawful_U(s)` is exactly `s^* I_Ob^U = 0`. -/
theorem lawful_iff_pulledObstructionIdeal_eq_bot :
    s.Lawful ↔ s.pulledObstructionIdeal = ⊥ :=
  LawfulSectionData.lawful_iff_pulledObstructionIdeal_eq_bot R s

/--
III.定理11.1 hardening: for a selected witness-ideal family, local ideal
lawfulness is exactly the statement that the selected local obstruction ideal
is killed by the section pullback.
-/
theorem localObstructionIdeal_le_ker_iff_lawful
    (F : ObstructionIdeal.SelectedLawWitnessIdealFamily.{u, v} R)
    (s : LawfulLocus.LocalLawfulSectionData.{u, v, w} R F) :
    F.localObstructionIdeal ≤ RingHom.ker s.pullback ↔ s.Lawful := by
  change F.localObstructionIdeal ≤ RingHom.ker s.pullback ↔
    Ideal.map s.pullback F.localObstructionIdeal = ⊥
  exact (Ideal.map_eq_bot_iff_le_ker s.pullback).symm

/--
III.定理11.1 hardening: if a section kills every selected law witness ideal,
then it is lawful for the generated local obstruction ideal.

This uses `SelectedLawWitnessIdealFamily.localObstructionIdeal` as the
load-bearing bridge, rather than consuming the old `witnessCoverage` field as
the conclusion.
-/
theorem lawful_of_selectedWitnessIdeals_le_ker
    (F : ObstructionIdeal.SelectedLawWitnessIdealFamily.{u, v} R)
    (s : LawfulLocus.LocalLawfulSectionData.{u, v, w} R F)
    (hkill :
      ∀ L, F.selected L -> F.witnessIdeal L ≤ RingHom.ker s.pullback) :
    s.Lawful :=
  (localObstructionIdeal_le_ker_iff_lawful F s).mp
    ((ObstructionIdeal.SelectedLawWitnessIdealFamily.localObstructionIdeal_le_iff
      R F (RingHom.ker s.pullback)).mpr hkill)

/--
III.定理11.1 / III.定理11.4 bridge: in a generated law-equation core, killing
each required law witness ideal makes the section lawful for the generated
local obstruction ideal.
-/
theorem lawful_of_generatedLawWitnessIdeals_le_ker
    {A : ArchitectureObject U} {S : Site.AATSite A}
    (G : SemanticLawEquationWitnessIdealCore S) (W : S.category)
    (s : LawfulSectionData.{u, w} (G.Observable W) (G.obstructionIdeal W))
    (hkill :
      ∀ lawIndex, S.lawUniverse.Required lawIndex ->
        G.lawWitnessIdeal W lawIndex ≤ RingHom.ker s.pullback) :
    s.Lawful :=
  lawful_of_selectedWitnessIdeals_le_ker
    (F := G.selectedLawWitnessIdealFamily W) (s := s) hkill

/--
III.定理11.1 / III.定理11.4 bridge: displayed required laws force the displayed
defect into the generated local obstruction ideal.
-/
theorem displayedRequiredLawsHoldOn_defect_mem_localObstructionIdeal
    {A : ArchitectureObject U} {S : Site.AATSite A}
    {G : SemanticLawEquationWitnessIdealCore S}
    (D : LawEquationDefectSource G)
    (hholds : D.DisplayedRequiredLawsHoldOn) (i : D.Chart) :
    D.defect i (D.input i) ∈ G.obstructionIdeal (D.chart i) :=
  (D.interpret_eq_zero_iff_defect_mem_obstructionIdeal i).mp
    (D.displayedRequiredLawsHoldOn_constructs_interpret_eq_zero hholds i)

/-- III.定理11.1: `s^* I_Ob^U = 0` is exactly factorization through `Flat_U(X)`. -/
theorem pulledObstructionIdeal_eq_bot_iff_factorsThroughLawfulLocus :
    s.pulledObstructionIdeal = ⊥ ↔ s.FactorsThroughLawfulLocus :=
  (lawful_iff_pulledObstructionIdeal_eq_bot s).symm.trans
    (LawfulSectionData.lawful_iff_factorsThroughLawfulLocus R s)

/-- III.定理11.1: factorization through `Flat_U(X)` agrees with `omega_U = 0`. -/
theorem factorsThroughLawfulLocus_iff_omegaU_zero
    (H : LawfulnessIdealCorrespondenceAssumptions s Obj LU Sig valuation) :
    s.FactorsThroughLawfulLocus ↔
      omegaU valuation LU aggregation Obj = valuation.domain.zero :=
  (LawfulSectionData.lawful_iff_factorsThroughLawfulLocus R s).symm.trans
    (LawfulnessIdealCorrespondenceAssumptions.lawful_iff_omegaU_zero
      s Obj LU Sig valuation aggregation H)

/--
III.定理11.1: aggregate obstruction zero agrees with required signature axes
zero.
-/
theorem omegaU_zero_iff_requiredSignatureAxesZero
    (H : LawfulnessIdealCorrespondenceAssumptions s Obj LU Sig valuation) :
    omegaU valuation LU aggregation Obj = valuation.domain.zero ↔
      RequiredSignatureAxesZero Obj Sig :=
  (LawfulnessIdealCorrespondenceAssumptions.lawful_iff_omegaU_zero
      s Obj LU Sig valuation aggregation H).symm.trans
    (LawfulnessIdealCorrespondenceAssumptions.lawful_iff_requiredSignatureAxesZero
      s Obj LU Sig valuation H)

/--
III.定理11.1: the five-term Lawfulness-Ideal Correspondence theorem package.
-/
def lawfulnessIdealCorrespondence
    (H : LawfulnessIdealCorrespondenceAssumptions s Obj LU Sig valuation) :
    LawfulnessIdealCorrespondencePackage s Obj LU Sig valuation aggregation H where
  lawful_iff_pulled := lawful_iff_pulledObstructionIdeal_eq_bot s
  pulled_iff_factors := pulledObstructionIdeal_eq_bot_iff_factorsThroughLawfulLocus s
  factors_iff_omega :=
    factorsThroughLawfulLocus_iff_omegaU_zero s Obj LU Sig valuation aggregation H
  omega_iff_signature :=
    omegaU_zero_iff_requiredSignatureAxesZero s Obj LU Sig valuation aggregation H
  lawful_iff_signature :=
    LawfulnessIdealCorrespondenceAssumptions.lawful_iff_requiredSignatureAxesZero
      s Obj LU Sig valuation H

end Correspondence

end LawAlgebra
end AAT.AG
