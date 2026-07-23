import ResearchLean.AG.QualitySurface.SemanticRepairLawEquationRealization
import Formal.AG.Examples.FiniteModel

/-!
G-06 law-equation realization: concrete finite witness instance.

This file discharges the two obligations recorded by Cycle 348:

1. `quotientIsSheaf` is discharged for a selected concrete finite instance.
   On the Part I/II finite model site (`Formal/AG/Examples/FiniteModel.lean`),
   every admissible cover family generates the top sieve, because admissible
   atom-support coverage forces a nonempty patch index and the singleton
   context preorder makes every hom subsingleton.  Hence *every* presheaf
   satisfies the AAT sheaf condition on that site, and in particular the
   generated obstruction-quotient coefficient does.  The sheaf condition is
   proved, not supplied.

2. A nondegenerate finite witness is fixed.  The observable ring is `ℤ`, the
   violation coordinates of the single required law are the constant `2`, so
   the local obstruction ideal is contained in `span {2}`.  The defect `1` is
   not in the ideal and its obstruction-quotient class is nonzero, while every
   violation coordinate has zero class.  The quotient realization therefore
   distinguishes lawful from non-lawful readings; nothing collapses
   definitionally.
-/

noncomputable section

universe u v w x y z r a b

namespace ResearchLean.AG
namespace QualitySurface
namespace SemanticRepairCechGrounding

open CategoryTheory
open Opposite
open SemanticRepairSheafH1
open SemanticRepairTrueSheafH1
open SemanticRepairObstructionTower

namespace SemanticRepairCoverRelativeCochainRealization
namespace CoverRelativeCechGeneratedSemanticCoefficient

/-! ## The finite-model site has a trivial generated topology -/

/--
On the finite-model singleton site, every admissible cover family generates a
sieve whose pullback along any map is the top sieve.  Admissibility forces a
nonempty patch index through required atom-support coverage, and the equality
context preorder makes every hom subsingleton, so the generated sieve absorbs
every arrow.
-/
theorem finiteModelSite_generate_pullback_eq_top
    {X Y : AAT.AG.FiniteModel.site.category} (f : Y ⟶ X)
    (Fam :
      AAT.AG.Site.AATCoverageFamily AAT.AG.FiniteModel.site.requirements
        AAT.AG.FiniteModel.site.overlap X) :
    (Sieve.generate Fam.presieve).pullback f = ⊤ := by
  rw [← Sieve.id_mem_iff_eq_top]
  obtain ⟨i, _hvisible⟩ :=
    Fam.admissible.atomSupportCoverage AAT.AG.FiniteModel.FiniteAtom.componentA
      trivial
  have hYX : Y.ctx = X.ctx := leOfHom f
  have hiX : Fam.patch i = X.ctx := Fam.inclusion i
  have hle :
      Y ≤ AAT.AG.Site.ContextCategoryObject.of
        AAT.AG.FiniteModel.siteContextPreorder (Fam.patch i) :=
    show Y.ctx = Fam.patch i from hYX.trans hiX.symm
  exact
    ⟨AAT.AG.Site.ContextCategoryObject.of
        AAT.AG.FiniteModel.siteContextPreorder (Fam.patch i),
      homOfLE hle, homOfLE (Fam.inclusion i),
      Presieve.ofArrows.mk i, Subsingleton.elim _ _⟩

/--
Every presheaf on the finite-model site satisfies the AAT sheaf condition.

The proof characterizes the generated Grothendieck topology through
`Precoverage.isSheaf_toGrothendieck_iff` and reduces every admissible cover to
the top sieve; it does not postulate the sheaf condition and does not use any
subsingleton assumption on the coefficient values.
-/
theorem finiteModelSite_AATSheafCondition
    (F : AAT.AG.Site.AATPresheaf AAT.AG.FiniteModel.site) :
    AAT.AG.Site.AATSheafCondition AAT.AG.FiniteModel.site F := by
  rw [AAT.AG.Site.AATSheafCondition.iff_presieve_isSheaf]
  refine (Precoverage.isSheaf_toGrothendieck_iff F).mpr ?_
  intro X Y f R hR
  obtain ⟨Fam, rfl⟩ := hR
  rw [finiteModelSite_generate_pullback_eq_top f Fam]
  exact Presieve.isSheafFor_top F

/-! ## The concrete law-equation witness instance -/

/-- Selected singleton semantic repair site over the finite-model atoms. -/
def finiteModelSemanticRepairSite :
    SemanticRepairSite.{0, 0} AAT.AG.FiniteModel.carrier.Atom where
  Chart := PUnit
  chartOrder := [PUnit.unit]
  sourceTraceToken := fun _ => true

instance : Nonempty AAT.AG.FiniteModel.FiniteAtom :=
  ⟨AAT.AG.FiniteModel.FiniteAtom.componentA⟩

/-- Each witness ideal of the finite-model law realization is inside `span {2}`. -/
theorem finiteModel_witnessIdeal_le
    (W : AAT.AG.FiniteModel.site.category)
    (equationIndex : AAT.AG.FiniteModel.site.equationSystem.Index) :
    AAT.AG.FiniteModel.site.equationSystem.witnessIdeal W equationIndex ≤
      Ideal.span {(2 : ℤ)} := by
  refine Ideal.span_le.mpr ?_
  rintro x ⟨atom, rfl⟩
  exact Ideal.subset_span rfl

/-- The local obstruction ideal of the finite-model realization is inside `span {2}`. -/
theorem finiteModel_obstructionIdeal_le
    (W : AAT.AG.FiniteModel.site.category) :
    AAT.AG.FiniteModel.site.equationSystem.obstructionIdeal W ≤
      Ideal.span {(2 : ℤ)} := by
  refine
    (AAT.AG.LawAlgebra.ObstructionIdeal.SelectedLawWitnessIdealFamily.localObstructionIdeal_le_iff
      _ _ _).mpr ?_
  intro lawIndex _hselected
  exact finiteModel_witnessIdeal_le W lawIndex

/--
Nondegeneracy, ideal level: the defect `1` is not in the local obstruction
ideal of the finite-model realization.
-/
theorem finiteModel_one_notMem_obstructionIdeal
    (W : AAT.AG.FiniteModel.site.category) :
    (1 : ℤ) ∉ AAT.AG.FiniteModel.site.equationSystem.obstructionIdeal W := by
  intro hmem
  have htwo := finiteModel_obstructionIdeal_le W hmem
  rw [Ideal.mem_span_singleton] at htwo
  have htwo' : (2 : ℤ) ∣ (1 : ℤ) := htwo
  obtain ⟨c, hc⟩ := htwo'
  omega

/--
Nondegeneracy, quotient level: the obstruction-quotient class of the defect
`1` is nonzero.  This is the non-lawful witness demanded by the Cycle 348
remaining work: the generated coefficient does not collapse to zero.
-/
theorem finiteModel_defectOne_class_ne_zero
    (W : AAT.AG.FiniteModel.site.category) :
    Ideal.Quotient.mk
        (AAT.AG.FiniteModel.site.equationSystem.obstructionIdeal W)
        (1 : ℤ) ≠ 0 := by
  intro h
  exact finiteModel_one_notMem_obstructionIdeal W
    (Ideal.Quotient.eq_zero_iff_mem.mp h)

/-- The generated obstruction quotient of the finite-model realization is nontrivial. -/
theorem finiteModel_obstructionQuotient_nontrivial
    (W : AAT.AG.FiniteModel.site.category) :
    ∃ x : AAT.AG.FiniteModel.site.equationSystem.ObstructionQuotient W, x ≠ 0 :=
  ⟨Ideal.Quotient.mk
      (AAT.AG.FiniteModel.site.equationSystem.obstructionIdeal W) 1,
    finiteModel_defectOne_class_ne_zero W⟩

/--
Lawful side: every violation coordinate has zero obstruction-quotient class.
Together with the nonzero defect class this shows the quotient realization
separates lawful from non-lawful readings.
-/
theorem finiteModel_violationCoordinate_class_eq_zero
    (W : AAT.AG.FiniteModel.site.category)
    (equationIndex : AAT.AG.FiniteModel.site.equationSystem.Index)
    (atom : AAT.AG.FiniteModel.carrier.Atom) :
    Ideal.Quotient.mk
        (AAT.AG.FiniteModel.site.equationSystem.obstructionIdeal W)
        (AAT.AG.FiniteModel.site.equationSystem.violationCoordinate
          W equationIndex atom) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr
    (AAT.AG.FiniteModel.site.equationSystem.witnessIdeal_le_obstructionIdeal W
      (AAT.AG.FiniteModel.site_equation_required equationIndex)
      (Ideal.subset_span ⟨atom, rfl⟩))

/--
The concrete law-equation geometry: the finite-model core together with the
*proved* sheaf condition of its generated obstruction-quotient coefficient.
The `quotientIsSheaf` field is discharged by
`finiteModelSite_AATSheafCondition`, not supplied as an assumption.
-/
def finiteModelLawEquationGeometry :
    SemanticLawEquationWitnessIdealGeometry finiteModelSemanticRepairSite
      AAT.AG.FiniteModel.site where
  supportAtom := AAT.AG.FiniteModel.FiniteAtom.componentA
  supportAtom_traceVisible := rfl
  lawSupport := fun _ _ => [PUnit.unit]
  lawSupport_nonempty := fun _ _ =>
    ⟨PUnit.unit, List.mem_singleton_self PUnit.unit⟩
  lawSupport_required := fun _ _ lawIndex _ => by
    cases lawIndex
    exact
      (AAT.AG.FiniteModel.site.equationSystem.toLegacyLawUniverse_required_iff
        PUnit.unit).mpr
        (AAT.AG.FiniteModel.site_equation_required PUnit.unit)
  quotientIsSheaf :=
    finiteModelSite_AATSheafCondition
      AAT.AG.FiniteModel.site.equationSystem.obstructionQuotientPresheaf

/--
Cycle 349 witness packet: the concrete finite instance exists, its quotient
sheaf condition is proved, the quotient is nontrivial, the non-lawful defect
`1` has nonzero class, and every violation coordinate has zero class.
-/
theorem finiteModel_lawEquation_witness_packet :
    Nonempty
        (SemanticLawEquationWitnessIdealGeometry finiteModelSemanticRepairSite
          AAT.AG.FiniteModel.site) /\
      (forall F : AAT.AG.Site.AATPresheaf AAT.AG.FiniteModel.site,
        AAT.AG.Site.AATSheafCondition AAT.AG.FiniteModel.site F) /\
      (forall W : AAT.AG.FiniteModel.site.category,
        ∃ x : AAT.AG.FiniteModel.site.equationSystem.ObstructionQuotient W,
          x ≠ 0) /\
      (forall W : AAT.AG.FiniteModel.site.category,
        Ideal.Quotient.mk
            (AAT.AG.FiniteModel.site.equationSystem.obstructionIdeal W)
            (1 : ℤ) ≠ 0) /\
      (forall (W : AAT.AG.FiniteModel.site.category)
        (equationIndex : AAT.AG.FiniteModel.site.equationSystem.Index)
        (atom : AAT.AG.FiniteModel.carrier.Atom),
        Ideal.Quotient.mk
            (AAT.AG.FiniteModel.site.equationSystem.obstructionIdeal W)
            (AAT.AG.FiniteModel.site.equationSystem.violationCoordinate
              W equationIndex atom) =
          0) :=
  ⟨⟨finiteModelLawEquationGeometry⟩,
    finiteModelSite_AATSheafCondition,
    finiteModel_obstructionQuotient_nontrivial,
    finiteModel_defectOne_class_ne_zero,
    finiteModel_violationCoordinate_class_eq_zero⟩

end CoverRelativeCechGeneratedSemanticCoefficient
end SemanticRepairCoverRelativeCochainRealization

end SemanticRepairCechGrounding
end QualitySurface
end ResearchLean.AG
