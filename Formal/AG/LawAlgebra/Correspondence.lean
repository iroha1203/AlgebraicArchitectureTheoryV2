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
      ∀ lawIndex, S.equationSystem.Required lawIndex ->
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

end Correspondence

end LawAlgebra
end AAT.AG
