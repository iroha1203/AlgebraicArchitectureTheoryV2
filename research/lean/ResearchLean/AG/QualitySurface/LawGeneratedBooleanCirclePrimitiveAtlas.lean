import ResearchLean.AG.QualitySurface.LawGeneratedBooleanCircleConormalH1Pair
import ResearchLean.AG.QualitySurface.LawGeneratedSemanticFirstOrderRepair
import Formal.Util.AssertStandardAxioms
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Tactic

/-!
# Primitive lawful-reading atlas on the Boolean circle

The three selected chart inputs are the three concrete component Atoms.  Each
input displays the required law.  Its raw reading is a common lawful unit plus
the selected law generator exactly on component A.  Pairwise differences are
computed as explicit finite required-law witness combinations.  Thus the
Cycle 16 explicit atlas is generated from concrete Atom/law data rather than
accepted as an overlap equation.
-/

noncomputable section

namespace ResearchLean.AG.QualitySurface
namespace LawGeneratedBooleanCirclePrimitiveAtlas

open CategoryTheory
open AAT.AG AAT.AG.LawAlgebra
open LawGeneratedBooleanCircleSite
open LawGeneratedBooleanCircleLawCore
open LawGeneratedBooleanCircleTopology
open LawGeneratedBooleanCircleTupleProfile
open LawGeneratedSemanticFirstOrderRepair

local instance : DecidableEq geometry.cover.Index := Classical.decEq _

/-- The primitive component input selected by each chart. -/
def componentAtom : Fin 3 → FiniteModel.FiniteAtom :=
  Fin.cases FiniteModel.FiniteAtom.componentA
    (Fin.cases FiniteModel.FiniteAtom.componentB
      (fun _ => FiniteModel.FiniteAtom.componentC))

/-- Chart zero carries component A. -/
@[simp] theorem componentAtom_zero :
    componentAtom 0 = FiniteModel.FiniteAtom.componentA := rfl

/-- Chart one carries component B. -/
@[simp] theorem componentAtom_one :
    componentAtom 1 = FiniteModel.FiniteAtom.componentB := rfl

/-- Chart two carries component C. -/
@[simp] theorem componentAtom_two :
    componentAtom 2 = FiniteModel.FiniteAtom.componentC := rfl

/-- A common raw reading whose first coordinate is nonzero. -/
def lawfulUnit : AmbientRing := (1, 0)

/-- The common raw lawful unit is nonzero. -/
theorem lawfulUnit_ne_zero : lawfulUnit ≠ 0 := by
  intro h
  have hfst := congrArg (fun x : AmbientRing => x.1) h
  norm_num [lawfulUnit] at hfst

/-- Primitive reading: common lawful unit plus the law generator on component A. -/
def readingFromComponent (g : AmbientRing)
    (atom : FiniteModel.FiniteAtom) : AmbientRing :=
  lawfulUnit + if atom = FiniteModel.FiniteAtom.componentA then g else 0

/-- The scalar recording whether one selected chart is component A. -/
def chartWeight (i : Fin 3) : AmbientRing := if i = 0 then 1 else 0

/-- Reading the selected chart input agrees with its explicit chart weight. -/
@[simp] theorem reading_componentAtom (g : AmbientRing) (i : Fin 3) :
    readingFromComponent g (componentAtom i) = lawfulUnit + chartWeight i * g := by
  fin_cases i <;> simp [readingFromComponent, chartWeight]

/-- Concrete Atom/law source shared by both Boolean-circle law generators. -/
def primitiveSource (g : AmbientRing) :
    PatchReadingSource (geometry := geometry) (core g) where
  LocalInput := fun _ => FiniteModel.FiniteAtom
  input := componentAtom
  lawSupport := fun _ _ => [PUnit.unit]
  lawSupport_required := by
    intro _ _ lawIndex _
    exact core_required g lawIndex
  readingOfLocalInput := fun _ atom => readingFromComponent g atom

/-- The required law displayed by one primitive chart input. -/
def primitiveDisplayedLaw (g : AmbientRing) (i : Fin 3) :
    DisplayedRequiredLaw (G := core g) (geometry := geometry)
      (primitiveSource g) i where
  lawIndex := PUnit.unit
  mem := by simp [primitiveSource]

/-- Every canonical primitive pair overlap is nondeep. -/
theorem primitivePair_not_deep (i j : Fin 3) :
    ¬ Deep (PairOverlap (geometry := geometry) i j) := by
  simpa [PairOverlap, LawGeneratedLargeCoefficientH0.pairSimplex,
    LawGeneratedBooleanCircleSquareZeroH1.edge] using
    pairOverlap_not_deep
      (LawGeneratedBooleanCircleSquareZeroH1.edge i j)

/-- One finite required-law coefficient realizes the endpoint weight difference. -/
noncomputable def primitiveCoefficients (g : AmbientRing) (i j : Fin 3) :
    (PairDisplayedRequiredLaw (G := core g) (geometry := geometry)
        (primitiveSource g) i j × FiniteModel.FiniteAtom) →₀
      (core g).Observable (PairOverlap (geometry := geometry) i j) :=
  Finsupp.single
    (Sum.inl (primitiveDisplayedLaw g i), FiniteModel.FiniteAtom.componentA)
    (chartWeight j - chartWeight i)

/-- The primitive pair expansion is proved by computation from the two inputs. -/
noncomputable def primitiveOverlap (g : AmbientRing) (i j : Fin 3) :
    OverlapLawCombination (G := core g) (geometry := geometry)
      (primitiveSource g) i j where
  coefficients := primitiveCoefficients g i j
  difference_eq := by
    have hpair := primitivePair_not_deep i j
    have hright : (core g).restrict (pairToRight (geometry := geometry) i j) =
        RingHom.id AmbientRing := by
      change ambientRestrict (pairToRight (geometry := geometry) i j) =
        RingHom.id AmbientRing
      exact ambientRestrict_of_not_deep _ hpair
    have hleft : (core g).restrict (pairToLeft (geometry := geometry) i j) =
        RingHom.id AmbientRing := by
      change ambientRestrict (pairToLeft (geometry := geometry) i j) =
        RingHom.id AmbientRing
      exact ambientRestrict_of_not_deep _ hpair
    have hcoordinate : (core g).violationCoordinate
        (PairOverlap (geometry := geometry) i j) PUnit.unit
          FiniteModel.FiniteAtom.componentA = g := by
      change generatorWitness g (PairOverlap (geometry := geometry) i j) = g
      simp [generatorWitness, hpair]
    rw [hright, hleft]
    change readingFromComponent g (componentAtom j) -
        readingFromComponent g (componentAtom i) = _
    rw [reading_componentAtom, reading_componentAtom]
    classical
    change lawfulUnit + chartWeight j * g - (lawfulUnit + chartWeight i * g) =
      (primitiveCoefficients g i j).sum fun p c =>
        c * (core g).violationCoordinate (PairOverlap (geometry := geometry) i j)
          (PairDisplayedRequiredLaw.lawIndex (G := core g) p.1) p.2
    rw [show primitiveCoefficients g i j =
      Finsupp.single
        (Sum.inl (primitiveDisplayedLaw g i), FiniteModel.FiniteAtom.componentA)
        (chartWeight j - chartWeight i) from rfl]
    rw [Finsupp.sum_single_index]
    · change lawfulUnit + chartWeight j * g - (lawfulUnit + chartWeight i * g) =
        (chartWeight j - chartWeight i) *
          generatorWitness g (PairOverlap (geometry := geometry) i j)
      rw [show generatorWitness g (PairOverlap (geometry := geometry) i j) = g by
        simpa using hcoordinate]
      ring
    · simp

/-- The primitive explicit atlas, with no supplied overlap equation. -/
noncomputable def primitiveAtlas (g : AmbientRing) :
    ExplicitLawGeneratedReadingAtlas (geometry := geometry) (core g) where
  source := primitiveSource g
  overlap := primitiveOverlap g

/-! ## Nonzero lawful quotient section -/

/-- Every covering sieve contains every arrow whose source is not the selected base. -/
theorem coveringSieve_contains_nonbase_arrow
    {X : site.category} {R : Sieve X} (hR : R ∈ site.topology X)
    {Y : site.category} (f : Y ⟶ X) (hY : Y ≠ base) : R f := by
  change (Site.admissiblePrecoverage coverageRequirements contextOverlap).Saturate X R at hR
  induction hR generalizing Y with
  | of X S hS =>
      rcases hS with ⟨F, rfl⟩
      have hX := family_base_eq F
      subst X
      exact selectedSieve_le_familySieve F f
        (nonbase_arrow_mem_selectedSieve f hY)
  | top X => simp
  | pullback X S hS Y' g ih =>
      exact ih (f ≫ g) hY
  | transitive X S R hS hlocal ihS ihLocal =>
      have hSf : S f := ihS f hY
      have hpull := ihLocal hSf (𝟙 Y) hY
      simpa using hpull

/-- The sheafification unit is injective at every non-base object of this topology. -/
theorem toSheafify_app_injective_of_ne_base
    (P : site.categoryᵒᵖ ⥤ AddCommGrpCat.{1})
    (Y : site.category) (hY : Y ≠ base) :
    Function.Injective ((toSheafify site.topology P).app (Opposite.op Y)) := by
  intro x y hxy
  have hcover := Presheaf.equalizerSieve_mem site.topology
    (toSheafify site.topology P) x y hxy
  have hid := coveringSieve_contains_nonbase_arrow hcover (𝟙 Y) hY
  simpa using hid

/-- Every selected chart object differs from the base. -/
theorem patch_ne_base (i : geometry.cover.Index) :
    Patch (geometry := geometry) i ≠ base := by
  intro h
  apply cover_patch_ne_base i
  exact congrArg Site.ContextCategoryObject.ctx h

/-- Every selected patch is nondeep. -/
theorem primitivePatch_not_deep (i : geometry.cover.Index) :
    ¬ Deep (Patch (geometry := geometry) i) := by
  change Fin 3 at i
  simpa [Patch, LawGeneratedBooleanCircleRawConormalSheaf.chartObject] using
    LawGeneratedBooleanCircleRawConormalSheaf.chart_not_deep i

/-- The selected component-A raw square-zero reading is genuinely nonzero. -/
theorem squareZeroPrimitiveAtlas_reading_zero_ne_zero :
    ExplicitLawGeneratedReadingAtlas.reading (G := squareZeroCore)
      (primitiveAtlas squareZeroGenerator)
        (show geometry.cover.Index from (0 : Fin 3)) ≠ 0 := by
  change readingFromComponent squareZeroGenerator (componentAtom 0) ≠ 0
  intro h
  have hfst := congrArg (fun x : AmbientRing => x.1) h
  norm_num [readingFromComponent, componentAtom, lawfulUnit, squareZeroGenerator] at hfst

/-- The component-A raw `O/I` quotient class is nonzero before sheafification. -/
theorem squareZeroLiftedRawQ0Reading_zero_ne_zero :
    liftedRawQ0Reading squareZeroCore (primitiveAtlas squareZeroGenerator)
      (show geometry.cover.Index from (0 : Fin 3)) ≠ 0 := by
  intro h
  have hdown := congrArg ULift.down h
  change Ideal.Quotient.mk
      (squareZeroCore.obstructionIdeal
        (Patch (geometry := geometry) (show geometry.cover.Index from (0 : Fin 3))))
      (readingFromComponent squareZeroGenerator (componentAtom 0)) = 0 at hdown
  have hmem : readingFromComponent squareZeroGenerator (componentAtom 0) ∈
      squareZeroCore.obstructionIdeal
        (Patch (geometry := geometry) (show geometry.cover.Index from (0 : Fin 3))) := by
    exact Ideal.Quotient.eq_zero_iff_mem.mp hdown
  rw [squareZero_obstructionIdeal_of_not_deep _
    (primitivePatch_not_deep
      (show geometry.cover.Index from (0 : Fin 3)))] at hmem
  have hle : Ideal.span ({squareZeroGenerator} : Set AmbientRing) ≤
      RingHom.ker (RingHom.fst AmbientField DualFactor) := by
    apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    simp [squareZeroGenerator]
  have hz := hle hmem
  change (RingHom.fst AmbientField DualFactor)
      (readingFromComponent squareZeroGenerator (componentAtom 0)) = 0 at hz
  norm_num [readingFromComponent, componentAtom, lawfulUnit, squareZeroGenerator] at hz

/-- The actual sheafified local lawful `Q₀` section is nonzero. -/
theorem squareZeroLocalQ0_zero_ne_zero :
    localQ0 squareZeroCore (primitiveAtlas squareZeroGenerator)
      (show geometry.cover.Index from (0 : Fin 3)) ≠ 0 := by
  intro h
  apply squareZeroLiftedRawQ0Reading_zero_ne_zero
  apply toSheafify_app_injective_of_ne_base
    (LawGeneratedSemanticFirstOrderRepair.LiftedSequence squareZeroCore).X₃
    (Patch (geometry := geometry) (show geometry.cover.Index from (0 : Fin 3)))
    (patch_ne_base (show geometry.cover.Index from (0 : Fin 3)))
  simpa [localQ0] using h

/-- The generated actual lawful base section in sheafified `Q₀` is nonzero. -/
theorem squareZeroAdditiveAtlasQ0Reading_ne_zero :
    additiveAtlasQ0Reading squareZeroCore (primitiveAtlas squareZeroGenerator) ≠ 0 := by
  intro h
  apply squareZeroLocalQ0_zero_ne_zero
  rw [← additiveAtlasQ0Reading_restrict squareZeroCore
    (primitiveAtlas squareZeroGenerator)
      (show geometry.cover.Index from (0 : Fin 3))]
  rw [h, map_zero]

/-- Concrete primitive lawful-reading representation for the square-zero core. -/
abbrev LawfulReadingRepresentation :=
  ExplicitLawGeneratedReadingAtlas (geometry := geometry) squareZeroCore

/-- The concrete square-zero lawful-reading representation. -/
noncomputable def squareZeroLawfulReadingRepresentation :
    LawfulReadingRepresentation :=
  primitiveAtlas squareZeroGenerator

/-- The concrete representation yields the full Cycle 16 semantic repair equivalence. -/
noncomputable def squareZeroSemanticFirstOrderRepairEquiv :
    SemanticFirstOrderRepair squareZeroCore squareZeroLawfulReadingRepresentation ≃
      (toLocalLiftData squareZeroCore squareZeroLawfulReadingRepresentation).GlobalLift :=
  SemanticFirstOrderRepairEquiv squareZeroCore squareZeroLawfulReadingRepresentation

/-- Its connecting class detects existence of a semantic first-order repair. -/
theorem squareZeroConnectingClass_isZero_iff_semanticRepair :
    (LawGeneratedLargeCoefficientCech.threeTermComplex geometry
      (AdditiveSequence squareZeroCore).X₁.val).H1IsZero
      ((toLocalLiftData squareZeroCore squareZeroLawfulReadingRepresentation).connectingClass
        (LawGeneratedIdealPowerLiftedSheafification.sheafifiedShortComplex_shortExact
          squareZeroCore)) ↔
      Nonempty (SemanticFirstOrderRepair squareZeroCore
        squareZeroLawfulReadingRepresentation) :=
  connectingClass_isZero_iff_nonempty_semanticFirstOrderRepair
    squareZeroCore squareZeroLawfulReadingRepresentation

end LawGeneratedBooleanCirclePrimitiveAtlas
end ResearchLean.AG.QualitySurface

#assert_standard_axioms_only ResearchLean.AG.QualitySurface.LawGeneratedBooleanCirclePrimitiveAtlas
