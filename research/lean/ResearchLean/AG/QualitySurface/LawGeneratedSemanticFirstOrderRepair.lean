import ResearchLean.AG.QualitySurface.LawGeneratedConormalComparison
import ResearchLean.AG.QualitySurface.LawGeneratedLargeConormalDescent
import ResearchLean.AG.QualitySurface.LawGeneratedLargeCoefficientH0
import Formal.Util.AssertStandardAxioms
import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic

/-!
# Law-generated semantic first-order repair

Patch readings whose pairwise differences are finite combinations of required-law
witnesses glue to an actual `O/I` section.  The same raw patch readings give
local `O/I²` lifts.  The resulting additive lift problem is then compared with
the internal quotient-ring sheaves by the canonical comparison of the preceding
cycle.

No global raw reading, global lift, vanishing class, comparison map, or
effectivity certificate is supplied as input.
-/

noncomputable section

namespace ResearchLean.AG.QualitySurface
namespace LawGeneratedSemanticFirstOrderRepair

universe u

open CategoryTheory Limits Opposite
open AAT.AG AAT.AG.LawAlgebra
open LawGeneratedRingSheaf LawGeneratedConormalIdealSheaf

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U}
variable {S : Site.AATSite A}
variable {geometry : Site.FinitePosetCoverGeometry S}
variable (G : ArchitecturalEquationSystem S.contextPreorder)

noncomputable local instance moduleSheafMonoidal :
    MonoidalCategory (Sheaf S.topology (LargeZMod.{u})) :=
  Sheaf.monoidalCategory S.topology (LargeZMod.{u})

noncomputable local instance moduleSheafBraided :
    BraidedCategory (Sheaf S.topology (LargeZMod.{u})) :=
  Sheaf.braidedCategory S.topology (LargeZMod.{u})

noncomputable local instance moduleForgetIsEquivalence :
    (LawGeneratedConormalComparison.moduleForget :
      LargeZMod.{u} ⥤ AddCommGrpCat.{u + 1}).IsEquivalence :=
  LawGeneratedConormalComparison.moduleForgetEquivalence.isEquivalence_functor

noncomputable local instance moduleForgetPreservesSheafification :
    S.topology.PreservesSheafification
      (LawGeneratedConormalComparison.moduleForget :
        LargeZMod.{u} ⥤ AddCommGrpCat.{u + 1}) := by
  exact Sheaf.preservesSheafification_of_adjunction S.topology
    (Adjunction.ofIsLeftAdjoint LawGeneratedConormalComparison.moduleForget)

/-- The selected cover patch as a context-category object. -/
abbrev Patch (i : geometry.cover.Index) : S.category :=
  Site.ContextCategoryObject.of S.contextPreorder (geometry.cover.patch i)

/-- The canonical pair overlap used by the large Cech complex. -/
abbrev PairOverlap (i j : geometry.cover.Index) : S.category :=
  LawGeneratedLargeCoefficientCech.overlapObject geometry 1
    (LawGeneratedLargeCoefficientH0.pairSimplex i j)

/-- Projection from the canonical pair overlap to its left patch. -/
def pairToLeft (i j : geometry.cover.Index) : PairOverlap i j ⟶ Patch i :=
  homOfLE (by
    simpa [PairOverlap, LawGeneratedLargeCoefficientH0.pairSimplex] using
      geometry.canonicalTupleOverlapFromOverlap_le_patch 1
        (LawGeneratedLargeCoefficientH0.pairSimplex i j) 0)

/-- Projection from the canonical pair overlap to its right patch. -/
def pairToRight (i j : geometry.cover.Index) : PairOverlap i j ⟶ Patch j :=
  homOfLE (by
    simpa [PairOverlap, LawGeneratedLargeCoefficientH0.pairSimplex] using
      geometry.canonicalTupleOverlapFromOverlap_le_patch 1
        (LawGeneratedLargeCoefficientH0.pairSimplex i j) 1)

/-- Raw reading inputs displayed on every selected patch. -/
structure PatchReadingSource where
  LocalInput : geometry.cover.Index → Type u
  input : ∀ i : geometry.cover.Index, LocalInput i
  lawSupport :
    ∀ i : geometry.cover.Index, LocalInput i → List G.Index
  lawSupport_required :
    ∀ i (localInput : LocalInput i) (lawIndex : G.Index),
      lawIndex ∈ lawSupport i localInput → G.Required lawIndex
  readingOfLocalInput :
    ∀ i : geometry.cover.Index, LocalInput i →
      G.Observable (Patch (geometry := geometry) i)

namespace PatchReadingSource

/-- The selected raw reading on a patch. -/
def reading (D : PatchReadingSource (geometry := geometry) G)
    (i : geometry.cover.Index) : G.Observable (Patch (geometry := geometry) i) :=
  D.readingOfLocalInput i (D.input i)

end PatchReadingSource

/-- One displayed required law on a selected patch input. -/
structure DisplayedRequiredLaw
    (D : PatchReadingSource (geometry := geometry) G)
    (i : geometry.cover.Index) where
  lawIndex : G.Index
  mem : lawIndex ∈ D.lawSupport i (D.input i)

/-- Requiredness is generated from the source's displayed law support. -/
theorem DisplayedRequiredLaw.required
    {D : PatchReadingSource (geometry := geometry) G}
    {i : geometry.cover.Index}
    (law : DisplayedRequiredLaw (G := G) (geometry := geometry) D i) :
    G.Required law.lawIndex :=
  D.lawSupport_required i (D.input i) law.lawIndex law.mem

/-- A displayed required law from either endpoint of a canonical pair. -/
abbrev PairDisplayedRequiredLaw
    (D : PatchReadingSource (geometry := geometry) G)
    (i j : geometry.cover.Index) :=
  Sum (DisplayedRequiredLaw (G := G) (geometry := geometry) D i)
    (DisplayedRequiredLaw (G := G) (geometry := geometry) D j)

/-- The law index carried by a pairwise displayed-law witness. -/
def PairDisplayedRequiredLaw.lawIndex
    {D : PatchReadingSource (geometry := geometry) G}
    {i j : geometry.cover.Index} :
    PairDisplayedRequiredLaw (G := G) (geometry := geometry) D i j →
      G.Index
  | Sum.inl law => law.lawIndex
  | Sum.inr law => law.lawIndex

/-- Its law index is required by the selected equation system. -/
theorem PairDisplayedRequiredLaw.required
    {D : PatchReadingSource (geometry := geometry) G}
    {i j : geometry.cover.Index}
    (law : PairDisplayedRequiredLaw (G := G) (geometry := geometry) D i j) :
    G.Required law.lawIndex := by
  cases law with
  | inl law => exact DisplayedRequiredLaw.required (G := G) law
  | inr law => exact DisplayedRequiredLaw.required (G := G) law

/-- Evaluate pairwise required-law coefficients on the pair overlap. -/
def evaluateCombination
    (D : PatchReadingSource (geometry := geometry) G)
    (i j : geometry.cover.Index)
    (coeff :
      (PairDisplayedRequiredLaw (G := G) (geometry := geometry) D i j × U.Atom) →₀
      G.Observable (PairOverlap (geometry := geometry) i j)) :
    G.Observable (PairOverlap (geometry := geometry) i j) :=
  coeff.sum fun p c ↦ c * G.violationCoordinate _
    (PairDisplayedRequiredLaw.lawIndex (G := G) p.1) p.2

/--
Finite required-law witness expansion of one pairwise reading difference.
The only data are its coefficients and the displayed raw equation.
-/
structure OverlapLawCombination
    (D : PatchReadingSource (geometry := geometry) G)
    (i j : geometry.cover.Index) where
  coefficients :
    (PairDisplayedRequiredLaw (G := G) (geometry := geometry) D i j × U.Atom) →₀
      G.Observable (PairOverlap (geometry := geometry) i j)
  difference_eq :
    G.restrict (pairToRight (geometry := geometry) i j)
        (D.readingOfLocalInput j (D.input j)) -
      G.restrict (pairToLeft (geometry := geometry) i j)
        (D.readingOfLocalInput i (D.input i)) =
      evaluateCombination G D i j coefficients

/--
Patch readings with an explicitly supplied required-law witness expansion for
each pairwise difference.  The expansion is conditional atlas input; this
structure contains no quotient section or first-order lift.
-/
structure ExplicitLawGeneratedReadingAtlas where
  source : PatchReadingSource (geometry := geometry) G
  overlap : ∀ i j : geometry.cover.Index,
    OverlapLawCombination (G := G) (geometry := geometry) source i j

namespace ExplicitLawGeneratedReadingAtlas

/-- The raw reading selected by the atlas on one patch. -/
def reading (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G)
    (i : geometry.cover.Index) : G.Observable (Patch (geometry := geometry) i) :=
  atlas.source.readingOfLocalInput i (atlas.source.input i)

end ExplicitLawGeneratedReadingAtlas

/-- Every explicit required-law combination belongs to the generated ideal. -/
theorem evaluateCombination_mem_obstructionIdeal
    (D : PatchReadingSource (geometry := geometry) G)
    (i j : geometry.cover.Index)
    (coeff :
      (PairDisplayedRequiredLaw (G := G) (geometry := geometry) D i j × U.Atom) →₀
      G.Observable (PairOverlap (geometry := geometry) i j)) :
    evaluateCombination G D i j coeff ∈
      G.obstructionIdeal (PairOverlap (geometry := geometry) i j) := by
  classical
  rw [evaluateCombination, Finsupp.sum]
  apply Ideal.sum_mem
  intro p hp
  apply (G.obstructionIdeal (PairOverlap (geometry := geometry) i j)).mul_mem_left
  have hrequired : G.Required
      (PairDisplayedRequiredLaw.lawIndex (G := G) p.1) := by
    cases p.1 with
    | inl law => exact law.required
    | inr law => exact law.required
  apply G.witnessIdeal_le_obstructionIdeal _ hrequired
  apply Ideal.subset_span
  exact ⟨p.2, rfl⟩

/-- Pairwise raw readings become equal after quotienting by the law ideal. -/
theorem rawQ0_pair_compatible
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G)
    (i j : geometry.cover.Index) :
    Ideal.Quotient.mk (G.obstructionIdeal (PairOverlap (geometry := geometry) i j))
        (G.restrict (pairToRight (geometry := geometry) i j)
          (atlas.source.readingOfLocalInput j (atlas.source.input j))) =
      Ideal.Quotient.mk (G.obstructionIdeal (PairOverlap (geometry := geometry) i j))
        (G.restrict (pairToLeft (geometry := geometry) i j)
          (atlas.source.readingOfLocalInput i (atlas.source.input i))) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [(atlas.overlap i j).difference_eq]
  exact evaluateCombination_mem_obstructionIdeal G atlas.source i j _

/-! ## Local quotient sections generated from the raw atlas -/

/-- The large additive law-generated short complex. -/
abbrev AdditiveSequence :=
  LawGeneratedIdealPowerLiftedSheafification.sheafifiedShortComplex G

/-- The universe-lifted raw sequence before sheafification. -/
abbrev LiftedSequence :=
  LawGeneratedIdealPowerLiftedSheafification.liftedShortComplex G

/-- Raw patch reading viewed in the universe-lifted `O/I` presheaf. -/
def liftedRawQ0Reading
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G)
    (i : geometry.cover.Index) :
    (LiftedSequence G).X₃.obj (op (Patch (geometry := geometry) i)) :=
  ULift.up
    (Ideal.Quotient.mk (G.obstructionIdeal (Patch (geometry := geometry) i))
      (atlas.source.readingOfLocalInput i (atlas.source.input i)))

/-- Raw patch reading viewed in the universe-lifted `O/I²` presheaf. -/
def liftedRawQ1Reading
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G)
    (i : geometry.cover.Index) :
    (LiftedSequence G).X₂.obj (op (Patch (geometry := geometry) i)) :=
  ULift.up
    (Ideal.Quotient.mk
      ((LawGeneratedIdealPowerSequence.Raw.I G
        (Patch (geometry := geometry) i)) ^ 2)
      (atlas.source.readingOfLocalInput i (atlas.source.input i)))

/-- The actual sheafified local `O/I` section generated by one patch reading. -/
def localQ0
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G)
    (i : geometry.cover.Index) :
    (AdditiveSequence G).X₃.val.obj (op (Patch (geometry := geometry) i)) :=
  (toSheafify S.topology (LiftedSequence G).X₃).app _
    (liftedRawQ0Reading G atlas i)

/-- The actual sheafified local `O/I²` lift generated by the same raw reading. -/
def localQ1
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G)
    (i : geometry.cover.Index) :
    (AdditiveSequence G).X₂.val.obj (op (Patch (geometry := geometry) i)) :=
  (toSheafify S.topology (LiftedSequence G).X₂).app _
    (liftedRawQ1Reading G atlas i)

/-- Sheafified local `O/I` readings agree on every canonical pair overlap. -/
theorem localQ0_pair_compatible
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G)
    (i j : geometry.cover.Index) :
    (AdditiveSequence G).X₃.val.map
        (pairToRight (geometry := geometry) i j).op (localQ0 G atlas j) =
      (AdditiveSequence G).X₃.val.map
        (pairToLeft (geometry := geometry) i j).op (localQ0 G atlas i) := by
  have hright := (toSheafify S.topology (LiftedSequence G).X₃).naturality_apply
    (pairToRight (geometry := geometry) i j).op
      (liftedRawQ0Reading G atlas j)
  have hleft := (toSheafify S.topology (LiftedSequence G).X₃).naturality_apply
    (pairToLeft (geometry := geometry) i j).op
      (liftedRawQ0Reading G atlas i)
  change
    (sheafify S.topology (LiftedSequence G).X₃).map
        (pairToRight (geometry := geometry) i j).op
        ((toSheafify S.topology (LiftedSequence G).X₃).app _
          (liftedRawQ0Reading G atlas j)) =
      (sheafify S.topology (LiftedSequence G).X₃).map
        (pairToLeft (geometry := geometry) i j).op
        ((toSheafify S.topology (LiftedSequence G).X₃).app _
          (liftedRawQ0Reading G atlas i))
  rw [← hright, ← hleft]
  apply congrArg ((toSheafify S.topology (LiftedSequence G).X₃).app _)
  apply congrArg ULift.up
  simpa [liftedRawQ0Reading, LiftedSequence,
    LawGeneratedIdealPowerLiftedSheafification.liftedShortComplex,
    LawGeneratedIdealPowerLiftedSheafification.liftPresheafFunctor,
    LawGeneratedIdealPowerSequence.Raw.shortComplex]
    using rawQ0_pair_compatible G atlas i j

/-- The raw `O/I²` patch section projects to its generated local `O/I` section. -/
theorem localQ1_projects
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G)
    (i : geometry.cover.Index) :
    (AdditiveSequence G).g.val.app _ (localQ1 G atlas i) = localQ0 G atlas i := by
  have hnat := toSheafify_naturality S.topology (LiftedSequence G).g
  have happ := congrArg
    (fun eta => eta.app (op (Patch (geometry := geometry) i))) hnat
  have helem := ConcreteCategory.congr_hom happ (liftedRawQ1Reading G atlas i)
  change
    (toSheafify S.topology (LiftedSequence G).X₃).app _
        ((LiftedSequence G).g.app _ (liftedRawQ1Reading G atlas i)) =
      (sheafifyMap S.topology (LiftedSequence G).g).app _
        ((toSheafify S.topology (LiftedSequence G).X₂).app _
          (liftedRawQ1Reading G atlas i)) at helem
  change
    (sheafifyMap S.topology (LiftedSequence G).g).app _
        ((toSheafify S.topology (LiftedSequence G).X₂).app _
          (liftedRawQ1Reading G atlas i)) =
      (toSheafify S.topology (LiftedSequence G).X₃).app _
        (liftedRawQ0Reading G atlas i)
  rw [← helem]
  apply congrArg ((toSheafify S.topology (LiftedSequence G).X₃).app _)
  rfl

/-! ## Actual additive `Q₀` section by sheaf amalgamation -/

/-- Pairwise equality extends to every common refinement of two cover patches. -/
theorem localQ0_arrowsCompatible
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G) :
    Presieve.Arrows.Compatible
      ((AdditiveSequence G).X₃.val ⋙ forget AddCommGrpCat)
      (fun i : geometry.cover.Index ↦ homOfLE (geometry.cover.inclusion i))
      (localQ0 G atlas) := by
  intro i j Z gi gj hcomm
  let overlapObj := PairOverlap (geometry := geometry) i j
  have hZi : S.contextPreorder.le Z.ctx (geometry.cover.patch i) := leOfHom gi
  have hZj : S.contextPreorder.le Z.ctx (geometry.cover.patch j) := leOfHom gj
  let sigma := LawGeneratedLargeCoefficientH0.pairSimplex i j
  have hkLe : S.contextPreorder.le Z.ctx
      (geometry.canonicalTupleOverlapFromOverlap 1 sigma) :=
    geometry.canonicalTupleOverlapFromOverlap_lift sigma (by
      intro k
      refine Fin.cases hZi (fun _ ↦ hZj) k)
  let kHom : Z ⟶ overlapObj := homOfLE hkLe
  let toI : overlapObj ⟶ Patch (geometry := geometry) i :=
    pairToLeft (geometry := geometry) i j
  let toJ : overlapObj ⟶ Patch (geometry := geometry) j :=
    pairToRight (geometry := geometry) i j
  have hpair := localQ0_pair_compatible G atlas i j
  rw [show gi = kHom ≫ toI from Subsingleton.elim _ _,
    show gj = kHom ≫ toJ from Subsingleton.elim _ _]
  change
    (((AdditiveSequence G).X₃.val ⋙ forget AddCommGrpCat).map
      (kHom ≫ toI).op) (localQ0 G atlas i) =
    (((AdditiveSequence G).X₃.val ⋙ forget AddCommGrpCat).map
      (kHom ≫ toJ).op) (localQ0 G atlas j)
  rw [op_comp, op_comp, FunctorToTypes.map_comp_apply,
    FunctorToTypes.map_comp_apply]
  exact congrArg
    (((AdditiveSequence G).X₃.val ⋙ forget AddCommGrpCat).map kHom.op)
    hpair.symm

/-- The additive local quotient readings as a compatible cover family. -/
noncomputable def additiveQ0Family
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G) :
    Presieve.FamilyOfElements
      ((AdditiveSequence G).X₃.val ⋙ forget AddCommGrpCat)
      geometry.cover.presieve := by
  simpa [Site.AATCoverageFamily.presieve] using
    (localQ0_arrowsCompatible G atlas).familyOfElements

theorem additiveQ0Family_compatible
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G) :
    (additiveQ0Family G atlas).Compatible := by
  simpa [additiveQ0Family, Site.AATCoverageFamily.presieve] using
    (localQ0_arrowsCompatible G atlas).familyOfElements_compatible

/--
The actual additive `Q₀` base section generated by the explicit patch atlas.
-/
noncomputable def additiveAtlasQ0Reading
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G) :
    (AdditiveSequence G).X₃.val.obj (op geometry.base) :=
  (LawGeneratedLargeCoefficientH0.isSheafFor_selectedCover
      (geometry := geometry) (AdditiveSequence G).X₃).amalgamate
    (additiveQ0Family G atlas) (additiveQ0Family_compatible G atlas)

/-- The generated base reading restricts to every displayed local reading. -/
theorem additiveAtlasQ0Reading_restrict
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G)
    (i : geometry.cover.Index) :
    (AdditiveSequence G).X₃.val.map
        (homOfLE (geometry.cover.inclusion i)).op
        (additiveAtlasQ0Reading G atlas) =
      localQ0 G atlas i := by
  have hvalid :=
    (LawGeneratedLargeCoefficientH0.isSheafFor_selectedCover
      (geometry := geometry) (AdditiveSequence G).X₃).valid_glue
      (additiveQ0Family_compatible G atlas)
      (homOfLE (geometry.cover.inclusion i))
      (show geometry.cover.presieve (homOfLE (geometry.cover.inclusion i)) by
        exact Presieve.ofArrows.mk i)
  calc
    _ = additiveQ0Family G atlas (homOfLE (geometry.cover.inclusion i))
        (show geometry.cover.presieve (homOfLE (geometry.cover.inclusion i)) by
          exact Presieve.ofArrows.mk i) := by
      simpa [additiveAtlasQ0Reading] using hvalid
    _ = localQ0 G atlas i := by
      simp [additiveQ0Family, Site.AATCoverageFamily.presieve]

/-- D0 local-lift data generated from the explicit atlas, without extra premises. -/
noncomputable def toLocalLiftData
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G) :
    LawGeneratedLargeConormalDescent.LocalLiftData geometry (AdditiveSequence G) where
  baseSection := additiveAtlasQ0Reading G atlas
  localLifts := localQ1 G atlas
  localLifts_project := by
    intro i
    rw [localQ1_projects G atlas i,
      additiveAtlasQ0Reading_restrict G atlas i]

/-! ## Independent internal-ring `Q₀` amalgamation -/

/-- The same raw local quotient sent independently into the module sheafification. -/
def internalLocalQ0
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G)
    (i : geometry.cover.Index) :
    (q0RingSheafObject G).X.val.obj (op (Patch (geometry := geometry) i)) :=
  (toSheafify S.topology (q0ModuleCoefficient G)).app _
    (liftedRawQ0Reading G atlas i)

/-- The independently sheafified internal local readings agree on pair overlaps. -/
theorem internalLocalQ0_pair_compatible
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G)
    (i j : geometry.cover.Index) :
    (q0RingSheafObject G).X.val.map
        (pairToRight (geometry := geometry) i j).op (internalLocalQ0 G atlas j) =
      (q0RingSheafObject G).X.val.map
        (pairToLeft (geometry := geometry) i j).op (internalLocalQ0 G atlas i) := by
  have hright := (toSheafify S.topology (q0ModuleCoefficient G)).naturality_apply
    (pairToRight (geometry := geometry) i j).op
      (liftedRawQ0Reading G atlas j)
  have hleft := (toSheafify S.topology (q0ModuleCoefficient G)).naturality_apply
    (pairToLeft (geometry := geometry) i j).op
      (liftedRawQ0Reading G atlas i)
  change
    (sheafify S.topology (q0ModuleCoefficient G)).map
        (pairToRight (geometry := geometry) i j).op
        ((toSheafify S.topology (q0ModuleCoefficient G)).app _
          (liftedRawQ0Reading G atlas j)) =
      (sheafify S.topology (q0ModuleCoefficient G)).map
        (pairToLeft (geometry := geometry) i j).op
        ((toSheafify S.topology (q0ModuleCoefficient G)).app _
          (liftedRawQ0Reading G atlas i))
  rw [← hright, ← hleft]
  apply congrArg ((toSheafify S.topology (q0ModuleCoefficient G)).app _)
  apply congrArg ULift.up
  simpa [liftedRawQ0Reading, LiftedSequence,
    LawGeneratedIdealPowerLiftedSheafification.liftedShortComplex,
    LawGeneratedIdealPowerLiftedSheafification.liftPresheafFunctor,
    LawGeneratedIdealPowerSequence.Raw.shortComplex]
    using rawQ0_pair_compatible G atlas i j

/-- The underlying type presheaf of the internal `Q₀` module sheaf. -/
abbrev internalQ0TypePresheaf :=
  (q0RingSheafObject G).X.val ⋙ forget (LargeZMod.{u})

/-- The internal `Q₀` sheaf is effective for the selected cover. -/
theorem internalQ0_isSheafFor_selectedCover :
    Presieve.IsSheafFor (internalQ0TypePresheaf G) geometry.cover.presieve := by
  apply (Presieve.isSheafFor_iff_generate geometry.cover.presieve).2
  exact (isSheaf_iff_isSheaf_of_type S.topology _).1
    (Presheaf.isSheaf_comp_of_isSheaf S.topology (q0RingSheafObject G).X.val
      (forget (LargeZMod.{u})) (q0RingSheafObject G).X.cond)
    (Sieve.generate geometry.cover.presieve) geometry.coverAdequate.isCover

/-- Internal local readings agree after every common refinement. -/
theorem internalLocalQ0_arrowsCompatible
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G) :
    Presieve.Arrows.Compatible (internalQ0TypePresheaf G)
      (fun i : geometry.cover.Index ↦ homOfLE (geometry.cover.inclusion i))
      (internalLocalQ0 G atlas) := by
  intro i j Z gi gj hcomm
  let overlapObj := PairOverlap (geometry := geometry) i j
  have hZi : S.contextPreorder.le Z.ctx (geometry.cover.patch i) := leOfHom gi
  have hZj : S.contextPreorder.le Z.ctx (geometry.cover.patch j) := leOfHom gj
  let sigma := LawGeneratedLargeCoefficientH0.pairSimplex i j
  have hkLe : S.contextPreorder.le Z.ctx
      (geometry.canonicalTupleOverlapFromOverlap 1 sigma) :=
    geometry.canonicalTupleOverlapFromOverlap_lift sigma (by
      intro k
      refine Fin.cases hZi (fun _ ↦ hZj) k)
  let kHom : Z ⟶ overlapObj := homOfLE hkLe
  let toI : overlapObj ⟶ Patch (geometry := geometry) i :=
    pairToLeft (geometry := geometry) i j
  let toJ : overlapObj ⟶ Patch (geometry := geometry) j :=
    pairToRight (geometry := geometry) i j
  have hpair := internalLocalQ0_pair_compatible G atlas i j
  rw [show gi = kHom ≫ toI from Subsingleton.elim _ _,
    show gj = kHom ≫ toJ from Subsingleton.elim _ _]
  change
    (internalQ0TypePresheaf G).map (kHom ≫ toI).op
        (internalLocalQ0 G atlas i) =
      (internalQ0TypePresheaf G).map (kHom ≫ toJ).op
        (internalLocalQ0 G atlas j)
  rw [op_comp, op_comp, FunctorToTypes.map_comp_apply,
    FunctorToTypes.map_comp_apply]
  exact congrArg ((internalQ0TypePresheaf G).map kHom.op) hpair.symm

/-- The internal local readings as a compatible selected-cover family. -/
noncomputable def internalQ0Family
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G) :
    Presieve.FamilyOfElements (internalQ0TypePresheaf G)
      geometry.cover.presieve := by
  simpa [Site.AATCoverageFamily.presieve] using
    (internalLocalQ0_arrowsCompatible G atlas).familyOfElements

theorem internalQ0Family_compatible
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G) :
    (internalQ0Family G atlas).Compatible := by
  simpa [internalQ0Family, Site.AATCoverageFamily.presieve] using
    (internalLocalQ0_arrowsCompatible G atlas).familyOfElements_compatible

/-- The independently amalgamated internal-ring `Q₀` reading. -/
noncomputable def internalAtlasQ0Reading
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G) :
    (q0RingSheafObject G).X.val.obj (op geometry.base) :=
  (internalQ0_isSheafFor_selectedCover (geometry := geometry) G).amalgamate
    (internalQ0Family G atlas) (internalQ0Family_compatible G atlas)

theorem internalAtlasQ0Reading_restrict
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G)
    (i : geometry.cover.Index) :
    (q0RingSheafObject G).X.val.map
        (homOfLE (geometry.cover.inclusion i)).op
        (internalAtlasQ0Reading G atlas) = internalLocalQ0 G atlas i := by
  have hvalid :=
    (internalQ0_isSheafFor_selectedCover (geometry := geometry) G).valid_glue
      (internalQ0Family_compatible G atlas)
      (homOfLE (geometry.cover.inclusion i))
      (show geometry.cover.presieve (homOfLE (geometry.cover.inclusion i)) by
        exact Presieve.ofArrows.mk i)
  calc
    _ = internalQ0Family G atlas (homOfLE (geometry.cover.inclusion i))
        (show geometry.cover.presieve (homOfLE (geometry.cover.inclusion i)) by
          exact Presieve.ofArrows.mk i) := by
      simpa [internalAtlasQ0Reading] using hvalid
    _ = internalLocalQ0 G atlas i := by
      simp [internalQ0Family, Site.AATCoverageFamily.presieve]

/-! ## Canonical representation of the independently generated readings -/

/-- The Cycle 15 comparison identifies the two local sheafification units. -/
theorem q0SheafIso_localQ0
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G)
    (i : geometry.cover.Index) :
    (LawGeneratedConormalComparison.q0SheafIso G).hom.val.app _
        (localQ0 G atlas i) = internalLocalQ0 G atlas i := by
  have hfac := sheafComposeIso_hom_fac S.topology
    LawGeneratedConormalComparison.moduleForget (q0ModuleCoefficient G)
  have happ := congrArg
    (fun eta => eta.app (op (Patch (geometry := geometry) i))) hfac
  have hx := ConcreteCategory.congr_hom happ
    (liftedRawQ0Reading G atlas i)
  change
    (LawGeneratedConormalComparison.q0SheafIso G).hom.val.app _
        (localQ0 G atlas i) = internalLocalQ0 G atlas i
  exact hx

/--
The canonical Cycle 15 comparison carries the independently amalgamated
additive reading to the independently amalgamated internal-ring reading.
-/
theorem atlasQ0Comparison
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G) :
    (LawGeneratedConormalComparison.q0SheafIso G).hom.val.app _
        (additiveAtlasQ0Reading G atlas) = internalAtlasQ0Reading G atlas := by
  apply (internalQ0_isSheafFor_selectedCover (geometry := geometry) G).isSeparatedFor.ext
  rintro Y _ ⟨i⟩
  let inclusion : Patch (geometry := geometry) i ⟶ geometry.base :=
    homOfLE (geometry.cover.inclusion i)
  have hnat :=
    (LawGeneratedConormalComparison.q0SheafIso G).hom.val.naturality_apply
      inclusion.op (additiveAtlasQ0Reading G atlas)
  calc
    (q0RingSheafObject G).X.val.map inclusion.op
        ((LawGeneratedConormalComparison.q0SheafIso G).hom.val.app _
          (additiveAtlasQ0Reading G atlas)) =
      (LawGeneratedConormalComparison.q0SheafIso G).hom.val.app _
        ((AdditiveSequence G).X₃.val.map inclusion.op
          (additiveAtlasQ0Reading G atlas)) := by
      simpa only using hnat.symm
    _ = (LawGeneratedConormalComparison.q0SheafIso G).hom.val.app _
        (localQ0 G atlas i) := by
      have hadd := additiveAtlasQ0Reading_restrict G atlas i
      change (AdditiveSequence G).X₃.val.map inclusion.op
        (additiveAtlasQ0Reading G atlas) = localQ0 G atlas i at hadd
      rw [hadd]
    _ = internalLocalQ0 G atlas i := q0SheafIso_localQ0 G atlas i
    _ = (q0RingSheafObject G).X.val.map inclusion.op
        (internalAtlasQ0Reading G atlas) :=
      (internalAtlasQ0Reading_restrict G atlas i).symm

/-! ## Semantic first-order repair and D0 comparison -/

/-- Pointwise form of the Cycle 15 projection comparison. -/
theorem projection_square_apply
    (x : (AdditiveSequence G).X₂.val.obj (op geometry.base)) :
    (projectionModuleSheaf G).val.app _
        ((LawGeneratedConormalComparison.q1SheafIso G).hom.val.app _ x) =
      (LawGeneratedConormalComparison.q0SheafIso G).hom.val.app _
        ((AdditiveSequence G).g.val.app _ x) := by
  have hsquare := LawGeneratedConormalComparison.projection_square G
  have happ := congrArg
    (fun eta => eta.val.app (op geometry.base)) hsquare
  exact ConcreteCategory.congr_hom happ x

/--
All actual internal-ring `Q₁` base sections projecting to the independently
generated atlas `Q₀` reading.
-/
def InternalFirstOrderLift
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G) : Type (u + 1) :=
  { repair : (q1RingSheafObject G).X.val.obj (op geometry.base) //
    (projectionModuleSheaf G).val.app _ repair = internalAtlasQ0Reading G atlas }

/-- The internal repair fiber and the complete D0 global-lift fiber are equivalent. -/
noncomputable def internalFirstOrderLiftEquiv
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G) :
    InternalFirstOrderLift G atlas ≃
      (toLocalLiftData G atlas).GlobalLift where
  toFun repair := by
    refine ⟨(LawGeneratedConormalComparison.q1SheafIso G).inv.val.app _ repair.1, ?_⟩
    change (AdditiveSequence G).g.val.app _
      ((LawGeneratedConormalComparison.q1SheafIso G).inv.val.app _ repair.1) =
        additiveAtlasQ0Reading G atlas
    have hmapped :
      (LawGeneratedConormalComparison.q0SheafIso G).hom.val.app _
          ((AdditiveSequence G).g.val.app _
            ((LawGeneratedConormalComparison.q1SheafIso G).inv.val.app _ repair.1)) =
        (LawGeneratedConormalComparison.q0SheafIso G).hom.val.app _
          (additiveAtlasQ0Reading G atlas) := by
      calc
        _ = (projectionModuleSheaf G).val.app _
          ((LawGeneratedConormalComparison.q1SheafIso G).hom.val.app _
            ((LawGeneratedConormalComparison.q1SheafIso G).inv.val.app _ repair.1)) :=
          (projection_square_apply G _).symm
        _ = (projectionModuleSheaf G).val.app _ repair.1 := by
          have h := congrArg
            (fun eta => eta.val.app (op geometry.base))
            (LawGeneratedConormalComparison.q1SheafIso G).inv_hom_id
          exact congrArg
            (fun y => (projectionModuleSheaf G).val.app _ y)
            (ConcreteCategory.congr_hom h repair.1)
        _ = internalAtlasQ0Reading G atlas := repair.2
        _ = (LawGeneratedConormalComparison.q0SheafIso G).hom.val.app _
          (additiveAtlasQ0Reading G atlas) :=
          (atlasQ0Comparison G atlas).symm
    have hinv := congrArg
      ((LawGeneratedConormalComparison.q0SheafIso G).inv.val.app _) hmapped
    have hcancel := congrArg
      (fun eta => eta.val.app (op geometry.base))
      (LawGeneratedConormalComparison.q0SheafIso G).hom_inv_id
    calc
      _ = (LawGeneratedConormalComparison.q0SheafIso G).inv.val.app _
          ((LawGeneratedConormalComparison.q0SheafIso G).hom.val.app _
            ((AdditiveSequence G).g.val.app _
              ((LawGeneratedConormalComparison.q1SheafIso G).inv.val.app _ repair.1))) :=
        (ConcreteCategory.congr_hom hcancel _).symm
      _ = (LawGeneratedConormalComparison.q0SheafIso G).inv.val.app _
          ((LawGeneratedConormalComparison.q0SheafIso G).hom.val.app _
            (additiveAtlasQ0Reading G atlas)) := hinv
      _ = additiveAtlasQ0Reading G atlas :=
        ConcreteCategory.congr_hom hcancel _
  invFun lift := by
    refine ⟨(LawGeneratedConormalComparison.q1SheafIso G).hom.val.app _ lift.1, ?_⟩
    calc
      (projectionModuleSheaf G).val.app _
          ((LawGeneratedConormalComparison.q1SheafIso G).hom.val.app _ lift.1) =
        (LawGeneratedConormalComparison.q0SheafIso G).hom.val.app _
          ((AdditiveSequence G).g.val.app _ lift.1) :=
        projection_square_apply G lift.1
      _ = (LawGeneratedConormalComparison.q0SheafIso G).hom.val.app _
          (additiveAtlasQ0Reading G atlas) := by
        congr 1
        simpa [toLocalLiftData] using lift.2
      _ = internalAtlasQ0Reading G atlas := atlasQ0Comparison G atlas
  left_inv repair := by
    apply Subtype.ext
    have h := congrArg
      (fun eta => eta.val.app (op geometry.base))
      (LawGeneratedConormalComparison.q1SheafIso G).inv_hom_id
    exact ConcreteCategory.congr_hom h repair.1
  right_inv lift := by
    apply Subtype.ext
    have h := congrArg
      (fun eta => eta.val.app (op geometry.base))
      (LawGeneratedConormalComparison.q1SheafIso G).hom_inv_id
    exact ConcreteCategory.congr_hom h lift.1

/--
The law-generated connecting class vanishes exactly when an internal
first-order lift exists.
-/
theorem connectingClass_isZero_iff_nonempty_internalFirstOrderLift
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G) :
    (LawGeneratedLargeCoefficientCech.threeTermComplex geometry
      (AdditiveSequence G).X₁.val).H1IsZero
      ((toLocalLiftData G atlas).connectingClass
        (LawGeneratedIdealPowerLiftedSheafification.sheafifiedShortComplex_shortExact G)) ↔
      Nonempty (InternalFirstOrderLift G atlas) := by
  change
    (LawGeneratedLargeCoefficientCech.threeTermComplex geometry
      (AdditiveSequence G).X₁.val).H1IsZero
      ((toLocalLiftData G atlas).connectingClassFor
        (LawGeneratedIdealPowerLiftedSheafification.sheafifiedShortComplex_shortExact G)
        (toLocalLiftData G atlas).chosenGeneratorLocalLiftFamily) ↔ _
  rw [(toLocalLiftData G atlas).connectingClassFor_isZero_iff_nonempty_globalLift
    (LawGeneratedIdealPowerLiftedSheafification.sheafifiedShortComplex_shortExact G)
    (toLocalLiftData G atlas).chosenGeneratorLocalLiftFamily]
  exact (internalFirstOrderLiftEquiv G atlas).nonempty_congr.symm

/-! ## Correction-primitive semantic representation -/

/--
A semantic first-order repair is the kernel-valued correction primitive which
makes the explicit local first-order readings compatible.  Its equation is the
Čech coboundary equation itself; no global lift is stored.
-/
def SemanticFirstOrderRepair
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G) :
    Type (u + 1) :=
  let P := toLocalLiftData G atlas
  let hK :=
    LawGeneratedIdealPowerLiftedSheafification.sheafifiedShortComplex_shortExact G
  { b : LawGeneratedLargeCoefficientCech.Cochain geometry
      (AdditiveSequence G).X₁.val 0 //
    P.localLiftDifferenceFor hK P.chosenGeneratorLocalLiftFamily =
      LawGeneratedLargeCoefficientCech.d0 geometry (AdditiveSequence G).X₁.val b }

/-- A correction primitive generates an actual global lift by sheaf amalgamation. -/
noncomputable def semanticRepairToGlobalLift
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G)
    (repair : SemanticFirstOrderRepair G atlas) :
    (toLocalLiftData G atlas).GlobalLift := by
  let P := toLocalLiftData G atlas
  let hK :=
    LawGeneratedIdealPowerLiftedSheafification.sheafifiedShortComplex_shortExact G
  let L := P.chosenGeneratorLocalLiftFamily
  exact ⟨P.amalgamatedCorrectedLocalLift hK L repair.1 repair.2,
    P.projection_amalgamatedCorrectedLocalLift hK L repair.1 repair.2⟩

/-- Every actual global lift generates its correction primitive. -/
def globalLiftToSemanticRepair
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G)
    (lift : (toLocalLiftData G atlas).GlobalLift) :
    SemanticFirstOrderRepair G atlas := by
  let P := toLocalLiftData G atlas
  let hK :=
    LawGeneratedIdealPowerLiftedSheafification.sheafifiedShortComplex_shortExact G
  let L := P.chosenGeneratorLocalLiftFamily
  exact ⟨P.primitiveOfGlobal hK L lift,
    P.localLiftDifferenceFor_eq_d0_primitiveOfGlobal hK L lift⟩

/-- Amalgamation of the primitive generated by a global lift returns that lift. -/
theorem semanticRepairToGlobalLift_globalLiftToSemanticRepair
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G)
    (lift : (toLocalLiftData G atlas).GlobalLift) :
    semanticRepairToGlobalLift G atlas (globalLiftToSemanticRepair G atlas lift) =
      lift := by
  let P := toLocalLiftData G atlas
  let hK :=
    LawGeneratedIdealPowerLiftedSheafification.sheafifiedShortComplex_shortExact G
  let L := P.chosenGeneratorLocalLiftFamily
  apply Subtype.ext
  apply (LawGeneratedLargeConormalDescent.LocalLiftData.isSheafFor_selectedCover
    (geometry := geometry) (AdditiveSequence G).X₂).isSeparatedFor.ext
  rintro Y _ ⟨i⟩
  change (AdditiveSequence G).X₂.val.map
      (homOfLE (geometry.cover.inclusion i)).op
      (P.amalgamatedCorrectedLocalLift hK L
        (P.primitiveOfGlobal hK L lift)
        (P.localLiftDifferenceFor_eq_d0_primitiveOfGlobal hK L lift)) =
    (AdditiveSequence G).X₂.val.map
      (homOfLE (geometry.cover.inclusion i)).op lift.1
  rw [P.amalgamatedCorrectedLocalLift_restrict]
  rw [P.correctedLocalLift_eq_cochain]
  change
    P.localLiftCochainFor L (P.zeroSimplex i) -
        P.kernelCochain 0 (P.primitiveOfGlobal hK L lift) (P.zeroSimplex i) =
      P.globalRestrictionCochain lift (P.zeroSimplex i)
  change
    P.localLiftCochainFor L (P.zeroSimplex i) -
        (AdditiveSequence G).f.val.app _
          (P.primitiveOfGlobal hK L lift (P.zeroSimplex i)) =
      P.globalRestrictionCochain lift (P.zeroSimplex i)
  rw [P.kernel_primitiveOfGlobal]
  abel

/-- Restricting an amalgamated correction recovers its corrected cochain. -/
theorem globalRestrictionCochain_semanticRepairToGlobalLift
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G)
    (repair : SemanticFirstOrderRepair G atlas)
    (tau : LawGeneratedLargeCoefficientCech.Tuple geometry 0) :
    let P := toLocalLiftData G atlas
    let L := P.chosenGeneratorLocalLiftFamily
    P.globalRestrictionCochain (semanticRepairToGlobalLift G atlas repair) tau =
      P.correctedLocalLiftCochain L repair.1 tau := by
  dsimp only
  let P := toLocalLiftData G atlas
  let hK :=
    LawGeneratedIdealPowerLiftedSheafification.sheafifiedShortComplex_shortExact G
  let L := P.chosenGeneratorLocalLiftFamily
  let i := tau 0
  have htau : tau = P.zeroSimplex i := by
    funext k
    have hk : k = 0 := Fin.eq_zero k
    subst k
    rfl
  rw [htau]
  change (AdditiveSequence G).X₂.val.map
      (homOfLE (geometry.cover.inclusion i)).op
        (P.amalgamatedCorrectedLocalLift hK L repair.1 repair.2) =
    P.correctedLocalLiftCochain L repair.1 (P.zeroSimplex i)
  rw [P.amalgamatedCorrectedLocalLift_restrict,
    P.correctedLocalLift_eq_cochain]

/-- Extracting a primitive after amalgamation recovers the supplied primitive. -/
theorem globalLiftToSemanticRepair_semanticRepairToGlobalLift
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G)
    (repair : SemanticFirstOrderRepair G atlas) :
    globalLiftToSemanticRepair G atlas (semanticRepairToGlobalLift G atlas repair) =
      repair := by
  let P := toLocalLiftData G atlas
  let hK :=
    LawGeneratedIdealPowerLiftedSheafification.sheafifiedShortComplex_shortExact G
  let L := P.chosenGeneratorLocalLiftFamily
  apply Subtype.ext
  change P.primitiveOfGlobal hK L (semanticRepairToGlobalLift G atlas repair) = repair.1
  funext tau
  apply (LawGeneratedLargeConormalDescent.sectionKernelEquiv
    (AdditiveSequence G) hK _).injective
  apply Subtype.ext
  rw [LawGeneratedLargeConormalDescent.sectionKernelEquiv_apply]
  rw [P.kernel_primitiveOfGlobal]
  rw [globalRestrictionCochain_semanticRepairToGlobalLift G atlas repair tau]
  rw [LawGeneratedLargeConormalDescent.sectionKernelEquiv_apply]
  change
    P.localLiftCochainFor L tau -
        (P.localLiftCochainFor L tau -
          (AdditiveSequence G).f.val.app _ (repair.1 tau)) =
      (AdditiveSequence G).f.val.app _ (repair.1 tau)
  abel

/-- Correction primitives are constructively equivalent to all D0 global lifts. -/
noncomputable def SemanticFirstOrderRepairEquiv
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G) :
    SemanticFirstOrderRepair G atlas ≃ (toLocalLiftData G atlas).GlobalLift where
  toFun := semanticRepairToGlobalLift G atlas
  invFun := globalLiftToSemanticRepair G atlas
  left_inv := globalLiftToSemanticRepair_semanticRepairToGlobalLift G atlas
  right_inv := semanticRepairToGlobalLift_globalLiftToSemanticRepair G atlas

/-- The connecting class vanishes exactly when a correction primitive exists. -/
theorem connectingClass_isZero_iff_nonempty_semanticFirstOrderRepair
    (atlas : ExplicitLawGeneratedReadingAtlas (geometry := geometry) G) :
    (LawGeneratedLargeCoefficientCech.threeTermComplex geometry
      (AdditiveSequence G).X₁.val).H1IsZero
      ((toLocalLiftData G atlas).connectingClass
        (LawGeneratedIdealPowerLiftedSheafification.sheafifiedShortComplex_shortExact G)) ↔
      Nonempty (SemanticFirstOrderRepair G atlas) := by
  change
    (LawGeneratedLargeCoefficientCech.threeTermComplex geometry
      (AdditiveSequence G).X₁.val).H1IsZero
      ((toLocalLiftData G atlas).connectingClassFor
        (LawGeneratedIdealPowerLiftedSheafification.sheafifiedShortComplex_shortExact G)
        (toLocalLiftData G atlas).chosenGeneratorLocalLiftFamily) ↔ _
  rw [(toLocalLiftData G atlas).connectingClassFor_isZero_iff_nonempty_globalLift
    (LawGeneratedIdealPowerLiftedSheafification.sheafifiedShortComplex_shortExact G)
    (toLocalLiftData G atlas).chosenGeneratorLocalLiftFamily]
  exact (SemanticFirstOrderRepairEquiv G atlas).nonempty_congr.symm

end LawGeneratedSemanticFirstOrderRepair
end ResearchLean.AG.QualitySurface

#assert_standard_axioms_only ResearchLean.AG.QualitySurface.LawGeneratedSemanticFirstOrderRepair
