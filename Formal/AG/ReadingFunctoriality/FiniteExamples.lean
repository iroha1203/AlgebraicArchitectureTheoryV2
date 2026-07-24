import Formal.AG.ReadingFunctoriality.Core
import Formal.AG.ReadingFunctoriality.Coverage
import Formal.AG.ReadingFunctoriality.Coefficient
import Formal.AG.ReadingFunctoriality.StandardSchemeCoefficient
import Formal.AG.ReadingFunctoriality.CoefficientGeometry
import Formal.AG.ReadingFunctoriality.LerayComparison
import Formal.AG.ReadingFunctoriality.LargeLerayComparison
import Formal.AG.ReadingFunctoriality.LinearLerayComparison
import Formal.AG.Examples.FiniteModel
import Formal.AG.LawAlgebra.ClosedEquationalGeometry
import Formal.AG.LawAlgebra.StandardSchemeFiniteExample
import Formal.AG.LawAlgebra.FiniteExamples
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.CategoryTheory.Limits.Shapes.FiniteMultiequalizer
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Reading-functoriality reference models

This module owns the positive and negative firing declarations fixed by Part 4
SD9.
-/

noncomputable section

namespace AAT.AG.ReadingFunctorialityFinite

universe v

open CategoryTheory
open Opposite

/-! ## R3: nonidentity selected-cover refinement -/

/-- Finite two-patch site used by the Part 4 refinement reference model. -/
noncomputable def finiteSite :
    Site.AATSite FiniteModel.corePackage.object :=
  FiniteModel.twoPatchSite

private theorem finite_componentC_not_mem :
    ¬ FiniteModel.object.configuration.family.mem
      FiniteModel.FiniteAtom.componentC := by
  intro h
  exact FiniteModel.componentC_not_extracted_withoutComponentC
    ((FiniteModel.extractionDoctrine.atomize_mem_iff
      FiniteModel.ExtractionSource.withoutComponentC
      FiniteModel.FiniteAtom.componentC).mp h)

/--
Selected terminal context of the finite refinement reference model.

The empty observable type makes restriction of observables into an arbitrary
source context canonical.  Its support reading is exactly the finite object
family used by the selected two-patch model.
-/
private def finiteTerminalContext :
    Site.ArchCtx FiniteModel.object where
  minimal := {
    Support := PUnit
    Axis := PUnit
    Observable := Empty
    supportReads := fun _ atom => atom ≠ FiniteModel.FiniteAtom.componentC
    supportReads_objectFamily := fun hselected =>
      FiniteModel.allFamily_mem _ hselected
    axisReads := fun _ => True
    observableReads := fun observable => Empty.elim observable
  }
  Extension := FiniteModel.TwoPatchContextIndex
  extension := .base

private def finiteContextToTerminalMorphism (X : finiteSite.category) :
    Site.ContextMorphism X.ctx finiteTerminalContext where
  supportMap _ := PUnit.unit
  axisMap _ := PUnit.unit
  observableRestrict := Empty.elim

private theorem finiteContextToTerminalMorphism_isRestriction
    (X : finiteSite.category) :
    (finiteContextToTerminalMorphism X).IsRestriction := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro support atom hread hatom
    subst atom
    exact finite_componentC_not_mem
      (X.ctx.minimal.supportReads_objectFamily hread)
  · intro axis hread
    trivial
  · intro observable
    exact Empty.elim observable
  · intro support atom hread
    exact FiniteModel.allFamily_mem _ hread

/-- Selected base of the finite refinement reference model. -/
noncomputable def finiteBase : finiteSite.category :=
  Site.ContextCategoryObject.of finiteSite.contextPreorder
    finiteTerminalContext

private theorem finiteContextLeBase (X : finiteSite.category) :
    finiteSite.contextPreorder.le X.ctx finiteBase.ctx :=
  ⟨finiteContextToTerminalMorphism X,
    finiteContextToTerminalMorphism_isRestriction X⟩

private noncomputable def finiteContextToBase (X : finiteSite.category) :
    X ⟶ finiteBase :=
  homOfLE (finiteContextLeBase X)

/-- The selected finite base is terminal in the actual context category. -/
noncomputable def finiteBaseIsTerminal : Limits.IsTerminal finiteBase :=
  Limits.IsTerminal.ofUniqueHom finiteContextToBase
    (fun _ _ => Subsingleton.elim _ _)

/-- Coarse selected cover of the finite refinement reference model. -/
noncomputable def coarseCover :
    Site.AATCoverageFamily finiteSite.requirements finiteSite.overlap finiteBase where
  Index := FiniteModel.TwoPatchCoverIndex
  patch := FiniteModel.twoPatchCoverPatch
  inclusion i := finiteContextLeBase
    (Site.ContextCategoryObject.of finiteSite.contextPreorder
      (FiniteModel.twoPatchCoverPatch i))
  admissible := {
    atomSupportCoverage := by
      intro atom hreq
      rcases hreq with rfl | rfl
      · exact ⟨FiniteModel.TwoPatchCoverIndex.left, by
          simp [finiteSite, FiniteModel.twoPatchSite,
            FiniteModel.twoPatchSelectedGeometryReading,
            FiniteModel.twoPatchCoverPatch,
            FiniteModel.twoPatchCoverContextIndex,
            FiniteModel.twoPatchCoverageRequirements,
            FiniteModel.twoPatchSupportVisibleOn]⟩
      · exact ⟨FiniteModel.TwoPatchCoverIndex.right, by
          simp [finiteSite, FiniteModel.twoPatchSite,
            FiniteModel.twoPatchSelectedGeometryReading,
            FiniteModel.twoPatchCoverPatch,
            FiniteModel.twoPatchCoverContextIndex,
            FiniteModel.twoPatchCoverageRequirements,
            FiniteModel.twoPatchSupportVisibleOn]⟩
    equationCoordinateCoverage := by
      intro _coordinate _hreq
      exact Or.inl ⟨FiniteModel.TwoPatchCoverIndex.left, trivial⟩
    violationWitnessCoverage := by
      intro _witness _hreq
      exact Or.inl ⟨FiniteModel.TwoPatchCoverIndex.left, trivial⟩
    signatureAxisCoverage := by
      intro _axis _hreq
      exact ⟨FiniteModel.TwoPatchCoverIndex.left, by
        simp [finiteSite, FiniteModel.twoPatchSite,
          FiniteModel.twoPatchSelectedGeometryReading,
          FiniteModel.twoPatchCoverPatch,
          FiniteModel.twoPatchCoverContextIndex,
          FiniteModel.twoPatchCoverageRequirements]⟩
    boundaryCoverage := fun _i _j => trivial
    nonGeneration := by
      intro _i _support _atom hselected
      exact FiniteModel.allFamily_mem _ hselected
  }

/--
Fine selected cover obtained by retaining two labelled copies of every coarse
chart.

Implementation notes: duplicating chart labels preserves the underlying
presieve while giving an actual refinement whose index map is not injective.
-/
noncomputable def fineCover :
    Site.AATCoverageFamily finiteSite.requirements finiteSite.overlap finiteBase where
  Index := coarseCover.Index × Bool
  patch i := coarseCover.patch i.1
  inclusion i := coarseCover.inclusion i.1
  admissible := {
    atomSupportCoverage := by
      intro atom hreq
      rcases coarseCover.admissible.atomSupportCoverage atom hreq with ⟨i, hi⟩
      exact ⟨(i, false), hi⟩
    equationCoordinateCoverage := by
      intro coordinate hreq
      rcases coarseCover.admissible.equationCoordinateCoverage coordinate hreq with h | h
      · rcases h with ⟨i, hi⟩
        exact Or.inl ⟨(i, false), hi⟩
      · rcases h with ⟨i, j, hij⟩
        exact Or.inr ⟨(i, false), (j, false), hij⟩
    violationWitnessCoverage := by
      intro witness hreq
      rcases coarseCover.admissible.violationWitnessCoverage witness hreq with h | h
      · rcases h with ⟨i, hi⟩
        exact Or.inl ⟨(i, false), hi⟩
      · rcases h with ⟨i, j, hij⟩
        exact Or.inr ⟨(i, false), (j, false), hij⟩
    signatureAxisCoverage := by
      intro axis hreq
      rcases coarseCover.admissible.signatureAxisCoverage axis hreq with ⟨i, hi⟩
      exact ⟨(i, false), hi⟩
    boundaryCoverage := by
      intro i j
      exact coarseCover.admissible.boundaryCoverage i.1 j.1
    nonGeneration := by
      intro i support atom hselected
      exact coarseCover.admissible.nonGeneration i.1 hselected
  }

/-- Actual fine-to-coarse chart refinement of the duplicated finite cover. -/
noncomputable def coarseToFineCover :
    Site.AATCoverageFamily.Refinement coarseCover fineCover where
  indexMap i := i.1
  factor i := finiteSite.contextPreorder.refl (fineCover.patch i)
  factor_triangle _ := Subsingleton.elim _ _

/-- The finite refinement genuinely duplicates indices and is not bijective. -/
theorem coarseToFineCover_not_bijective :
    ¬ Function.Bijective coarseToFineCover.indexMap := by
  intro h
  let i : coarseCover.Index := FiniteModel.TwoPatchCoverIndex.left
  have hp : (i, false) = (i, true) := h.1 rfl
  exact Bool.false_ne_true (congrArg Prod.snd hp)

/-- Degree-dependent simplex data that cannot come from one R3 refinement map. -/
noncomputable def brokenFaceMap :
    ∀ n,
      (Cohomology.canonicalCoverRelative fineCover).simplex n →
        (Cohomology.canonicalCoverRelative coarseCover).simplex n
  | 0 => fun _ _ => .left
  | _ + 1 => fun _ _ => .right

/-- The R3 broken simplex data is not induced by any selected-cover refinement. -/
theorem brokenFaceMap_not_refinement :
    ¬ ∃ r : Site.AATCoverageFamily.Refinement coarseCover fineCover,
      r.simplexMap = brokenFaceMap := by
  rintro ⟨r, hr⟩
  let selected : fineCover.Index :=
    (FiniteModel.TwoPatchCoverIndex.left, false)
  let σ₀ : (Cohomology.canonicalCoverRelative fineCover).simplex 0 :=
    fun _ => selected
  let σ₁ : (Cohomology.canonicalCoverRelative fineCover).simplex 1 :=
    fun _ => selected
  have hleft :
      r.indexMap selected = FiniteModel.TwoPatchCoverIndex.left := by
    have h := congrFun (congrFun (congrFun hr 0) σ₀) (0 : Fin 1)
    simpa [Site.AATCoverageFamily.Refinement.simplexMap,
      brokenFaceMap, σ₀] using h
  have hright :
      r.indexMap selected = FiniteModel.TwoPatchCoverIndex.right := by
    have h := congrFun (congrFun (congrFun hr 1) σ₁) (0 : Fin 2)
    simpa [Site.AATCoverageFamily.Refinement.simplexMap,
      brokenFaceMap, σ₁] using h
  rw [hleft] at hright
  exact FiniteModel.TwoPatchCoverIndex.noConfusion hright

private inductive NonLerayContextIndex where
  | left
  | right
  | base

private def nonLeraySupportReads
    (i : NonLerayContextIndex) (atom : FiniteModel.carrier.Atom) : Prop :=
  match i with
  | .left => atom = FiniteModel.FiniteAtom.componentA
  | .right => atom = FiniteModel.FiniteAtom.componentB
  | .base => atom = FiniteModel.FiniteAtom.componentA ∨
      atom = FiniteModel.FiniteAtom.componentB

private def nonLerayContext (i : NonLerayContextIndex) :
    Site.ArchCtx FiniteModel.object where
  minimal := {
    Support := PUnit
    Axis := PUnit
    Observable := PUnit
    supportReads := fun _ atom => nonLeraySupportReads i atom
    supportReads_objectFamily := by
      intro support atom h
      cases i with
      | left =>
          rw [h]
          exact FiniteModel.allFamily_mem _ (by simp)
      | right =>
          rw [h]
          exact FiniteModel.allFamily_mem _ (by simp)
      | base =>
          rcases h with h | h
          · rw [h]
            exact FiniteModel.allFamily_mem _ (by simp)
          · rw [h]
            exact FiniteModel.allFamily_mem _ (by simp)
    axisReads := fun _ => True
    observableReads := fun _ => True
  }
  Extension := NonLerayContextIndex
  extension := i

private noncomputable abbrev nonLerayContextPreorder :
    Site.ContextPreorderCategory FiniteModel.object :=
  Site.contextMorphismPreorderCategory FiniteModel.object

private def nonLerayContextMorphism
    (i j : NonLerayContextIndex)
    (_h : ∀ atom, nonLeraySupportReads i atom →
      nonLeraySupportReads j atom) :
    Site.ContextMorphism (nonLerayContext i) (nonLerayContext j) where
  supportMap := id
  axisMap := id
  observableRestrict := id

private theorem nonLerayContextMorphism_isRestriction
    (i j : NonLerayContextIndex)
    (h : ∀ atom, nonLeraySupportReads i atom →
      nonLeraySupportReads j atom) :
    (nonLerayContextMorphism i j h).IsRestriction := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro support atom ha
    exact h atom ha
  · intro axis haxis
    exact trivial
  · intro observable hobservable
    exact trivial
  · intro support atom ha
    exact (nonLerayContext j).supportReads_objectFamily ha

private theorem nonLerayContextLe_of_support
    (i j : NonLerayContextIndex)
    (h : ∀ atom, nonLeraySupportReads i atom →
      nonLeraySupportReads j atom) :
    nonLerayContextPreorder.le (nonLerayContext i) (nonLerayContext j) :=
  ⟨nonLerayContextMorphism i j h,
    nonLerayContextMorphism_isRestriction i j h⟩

private theorem nonLeray_left_le_base :
    nonLerayContextPreorder.le
      (nonLerayContext .left) (nonLerayContext .base) := by
  apply nonLerayContextLe_of_support
  simp [nonLeraySupportReads]

private theorem nonLeray_right_le_base :
    nonLerayContextPreorder.le
      (nonLerayContext .right) (nonLerayContext .base) := by
  apply nonLerayContextLe_of_support
  simp [nonLeraySupportReads]

private theorem nonLeray_not_le_of_atom
    (i j : NonLerayContextIndex) (atom : FiniteModel.carrier.Atom)
    (hi : nonLeraySupportReads i atom)
    (hj : ¬ nonLeraySupportReads j atom) :
    ¬ nonLerayContextPreorder.le (nonLerayContext i) (nonLerayContext j) := by
  rintro ⟨f, hf⟩
  have hread := hf.1 (support := PUnit.unit) hi
  apply hj
  simpa [nonLerayContext] using hread

private theorem nonLeray_left_not_le_right :
    ¬ nonLerayContextPreorder.le
      (nonLerayContext .left) (nonLerayContext .right) := by
  apply nonLeray_not_le_of_atom .left .right FiniteModel.FiniteAtom.componentA
  · simp [nonLeraySupportReads]
  · simp [nonLeraySupportReads]

private theorem nonLeray_right_not_le_left :
    ¬ nonLerayContextPreorder.le
      (nonLerayContext .right) (nonLerayContext .left) := by
  apply nonLeray_not_le_of_atom .right .left FiniteModel.FiniteAtom.componentB
  · simp [nonLeraySupportReads]
  · simp [nonLeraySupportReads]

private theorem nonLeray_base_not_le_left :
    ¬ nonLerayContextPreorder.le
      (nonLerayContext .base) (nonLerayContext .left) := by
  apply nonLeray_not_le_of_atom .base .left FiniteModel.FiniteAtom.componentB
  · simp [nonLeraySupportReads]
  · simp [nonLeraySupportReads]

private theorem nonLeray_base_not_le_right :
    ¬ nonLerayContextPreorder.le
      (nonLerayContext .base) (nonLerayContext .right) := by
  apply nonLeray_not_le_of_atom .base .right FiniteModel.FiniteAtom.componentA
  · simp [nonLeraySupportReads]
  · simp [nonLeraySupportReads]

private noncomputable def nonLerayOverlap :
    Site.ContextOverlapPullback nonLerayContextPreorder :=
  Site.meetOverlapPullback nonLerayContextPreorder Site.productContextFiniteMeet

private def nonLeraySupportVisibleOn
    (W : Site.ArchCtx FiniteModel.object)
    (atom : FiniteModel.carrier.Atom) : Prop :=
  (W = nonLerayContext .left ∧ atom = FiniteModel.FiniteAtom.componentA) ∨
  (W = nonLerayContext .right ∧ atom = FiniteModel.FiniteAtom.componentB)

private def nonLerayCoverageRequirements :
    Site.CoverageRequirements FiniteModel.object
      (FiniteModel.equationSystem nonLerayContextPreorder) FiniteModel.signature where
  requiredSupport := fun atom =>
    atom = FiniteModel.FiniteAtom.componentA ∨
      atom = FiniteModel.FiniteAtom.componentB
  requiredEquationCoordinate := fun _ => True
  selectedViolationWitness := fun _ => True
  requiredAxis := fun _ => True
  supportVisibleOn := nonLeraySupportVisibleOn
  equationCoordinateVisibleOn := fun _ _ => True
  violationWitnessVisibleOn := fun _ _ => True
  axisReadableOn := fun W _ =>
    W = nonLerayContext .left ∨ W = nonLerayContext .right
  boundaryVisibleOn := fun _ _ => True

/-- Independent AAT site carrying the selected strict-diamond countermodel. -/
noncomputable def nonLeraySite :
    Site.AATSite FiniteModel.corePackage.object where
  contextPreorder := nonLerayContextPreorder
  equationSystem := FiniteModel.equationSystem nonLerayContextPreorder
  signature := FiniteModel.signature
  requirements := nonLerayCoverageRequirements
  overlap := nonLerayOverlap

/-- Top object of the selected strict-diamond configuration. -/
noncomputable def nonLerayBase : nonLeraySite.category :=
  Site.ContextCategoryObject.of nonLerayContextPreorder
    (nonLerayContext .base)

private inductive NonLerayCoverIndex where
  | left
  | right

private def nonLerayCoverPatch : NonLerayCoverIndex → Site.ArchCtx FiniteModel.object
  | .left => nonLerayContext .left
  | .right => nonLerayContext .right

/-- Two-branch cover used to compare the explicit Čech class with actual local cohomology. -/
noncomputable def nonLerayComparisonCover :
    Site.AATCoverageFamily nonLeraySite.requirements
      nonLeraySite.overlap nonLerayBase where
  Index := NonLerayCoverIndex
  patch := nonLerayCoverPatch
  inclusion := by
    intro i
    cases i
    · exact nonLeray_left_le_base
    · exact nonLeray_right_le_base
  admissible := {
    atomSupportCoverage := by
      intro atom h
      rcases h with rfl | rfl
      · exact ⟨.left, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨.right, Or.inr ⟨rfl, rfl⟩⟩
    equationCoordinateCoverage := by
      intro coordinate h
      exact Or.inl ⟨.left, trivial⟩
    violationWitnessCoverage := by
      intro witness h
      exact Or.inl ⟨.left, trivial⟩
    signatureAxisCoverage := by
      intro axis h
      exact ⟨.left, Or.inl rfl⟩
    boundaryCoverage := by
      intro i j
      trivial
    nonGeneration := by
      intro i support atom h
      cases i <;>
        simp [nonLerayBase, nonLerayCoverPatch, nonLerayContext,
          nonLeraySupportReads] at h
      · rcases h with h | h
        · rw [h]; exact FiniteModel.allFamily_mem _ (by simp)
        · rw [h]; exact FiniteModel.allFamily_mem _ (by simp)
      · rcases h with h | h
        · rw [h]; exact FiniteModel.allFamily_mem _ (by simp)
        · rw [h]; exact FiniteModel.allFamily_mem _ (by simp)
  }

/-- The comparison-cover index is exactly a two-point type. -/
def nonLerayComparisonCoverIndexEquiv :
    nonLerayComparisonCover.Index ≃ Bool where
  toFun
    | .left => false
    | .right => true
  invFun
    | false => .left
    | true => .right
  left_inv i := by cases i <;> rfl
  right_inv b := by cases b <;> rfl

/-- Left middle object of the selected strict-diamond configuration. -/
def nonLerayLeftObject : nonLeraySite.category :=
  Site.ContextCategoryObject.of nonLerayContextPreorder
    (nonLerayContext .left)

/-- Right middle object of the selected strict-diamond configuration. -/
def nonLerayRightObject : nonLeraySite.category :=
  Site.ContextCategoryObject.of nonLerayContextPreorder
    (nonLerayContext .right)

/-- The comparison cover has distinct left and right branches. -/
theorem nonLerayComparisonCover_twoBranches :
    ∃ i j : nonLerayComparisonCover.Index,
      i ≠ j ∧
        nonLerayComparisonCover.patch i = nonLerayLeftObject.ctx ∧
        nonLerayComparisonCover.patch j = nonLerayRightObject.ctx := by
  refine ⟨NonLerayCoverIndex.left, NonLerayCoverIndex.right, ?_, rfl, rfl⟩
  simp

private theorem nonLeray_admissibleCover_has_left
    {Z : nonLeraySite.category}
    (F : Site.AATCoverageFamily nonLeraySite.requirements
      nonLeraySite.overlap Z) :
    ∃ i : F.Index, F.patch i = nonLerayContext .left := by
  rcases F.admissible.atomSupportCoverage
      FiniteModel.FiniteAtom.componentA (Or.inl rfl) with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  rcases hi with hi | hi
  · exact hi.1
  · exact False.elim (by simpa using hi.2)

private theorem nonLeray_admissibleCover_has_right
    {Z : nonLeraySite.category}
    (F : Site.AATCoverageFamily nonLeraySite.requirements
      nonLeraySite.overlap Z) :
    ∃ i : F.Index, F.patch i = nonLerayContext .right := by
  rcases F.admissible.atomSupportCoverage
      FiniteModel.FiniteAtom.componentB (Or.inr rfl) with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  rcases hi with hi | hi
  · exact False.elim (by simpa using hi.2)
  · exact hi.1

private theorem nonLeray_topology_contains_of_hom_to_left
    {X : nonLeraySite.category}
    (hX : X ⟶ nonLerayLeftObject) :
    ∀ {Z : nonLeraySite.category} (f : X ⟶ Z)
      {R : Sieve Z}, R ∈ nonLeraySite.topology Z → R f := by
  intro Z f R hR
  change (Site.admissiblePrecoverage nonLerayCoverageRequirements
    nonLerayOverlap).Saturate Z R at hR
  induction hR with
  | of Z P hP =>
      rcases hP with ⟨F, rfl⟩
      rcases nonLeray_admissibleCover_has_left F with ⟨i, hi⟩
      let g : X ⟶ Site.ContextCategoryObject.of nonLerayContextPreorder
          (F.patch i) :=
        hX ≫ eqToHom (congrArg
          (Site.ContextCategoryObject.of nonLerayContextPreorder) hi).symm
      have hinclusion : (Sieve.generate F.presieve)
          (homOfLE (F.inclusion i)) :=
        Sieve.le_generate F.presieve _ (Presieve.ofArrows.mk i)
      have hcomp := (Sieve.generate F.presieve).downward_closed
        hinclusion g
      convert hcomp using 1
  | top Z => simp
  | pullback Z S hS Y g ih =>
      change S (f ≫ g)
      exact ih (f ≫ g)
  | transitive Z S R hS hlocal ihS ihlocal =>
      have hSf : S f := ihS f
      have hRf : (R.pullback f) (𝟙 X) := ihlocal hSf (𝟙 X)
      simpa using hRf

private theorem nonLeray_topology_contains_of_hom_to_right
    {X : nonLeraySite.category}
    (hX : X ⟶ nonLerayRightObject) :
    ∀ {Z : nonLeraySite.category} (f : X ⟶ Z)
      {R : Sieve Z}, R ∈ nonLeraySite.topology Z → R f := by
  intro Z f R hR
  change (Site.admissiblePrecoverage nonLerayCoverageRequirements
    nonLerayOverlap).Saturate Z R at hR
  induction hR with
  | of Z P hP =>
      rcases hP with ⟨F, rfl⟩
      rcases nonLeray_admissibleCover_has_right F with ⟨i, hi⟩
      let g : X ⟶ Site.ContextCategoryObject.of nonLerayContextPreorder
          (F.patch i) :=
        hX ≫ eqToHom (congrArg
          (Site.ContextCategoryObject.of nonLerayContextPreorder) hi).symm
      have hinclusion : (Sieve.generate F.presieve)
          (homOfLE (F.inclusion i)) :=
        Sieve.le_generate F.presieve _ (Presieve.ofArrows.mk i)
      have hcomp := (Sieve.generate F.presieve).downward_closed
        hinclusion g
      convert hcomp using 1
  | top Z => simp
  | pullback Z S hS Y g ih =>
      change S (f ≫ g)
      exact ih (f ≫ g)
  | transitive Z S R hS hlocal ihS ihlocal =>
      have hSf : S f := ihS f
      have hRf : (R.pullback f) (𝟙 X) := ihlocal hSf (𝟙 X)
      simpa using hRf

private theorem nonLeray_topology_eq_top_of_hom_to_left
    {X : nonLeraySite.category}
    (hX : X ⟶ nonLerayLeftObject)
    {R : Sieve X} (hR : R ∈ nonLeraySite.topology X) :
    R = ⊤ := by
  apply top_unique
  intro Y f hf
  exact nonLeray_topology_contains_of_hom_to_left (f ≫ hX) f hR

private theorem nonLeray_topology_eq_top_of_hom_to_right
    {X : nonLeraySite.category}
    (hX : X ⟶ nonLerayRightObject)
    {R : Sieve X} (hR : R ∈ nonLeraySite.topology X) :
    R = ⊤ := by
  apply top_unique
  intro Y f hf
  exact nonLeray_topology_contains_of_hom_to_right (f ≫ hX) f hR

private noncomputable def nonLeraySheafifiedFreeYoneda
    (X : nonLeraySite.category) :
    Sheaf nonLeraySite.topology AddCommGrpCat.{1} :=
  (presheafToSheaf nonLeraySite.topology AddCommGrpCat.{1}).obj
    (yoneda.obj X ⋙ AddCommGrpCat.free)

private theorem nonLeraySheafifiedFreeYoneda_projective_of_hom_to_left
    (X : nonLeraySite.category) (hX : X ⟶ nonLerayLeftObject) :
    Projective (nonLeraySheafifiedFreeYoneda X) := by
  constructor
  intro E G f e he
  letI : Epi e := he
  have hloc : Presheaf.IsLocallySurjective nonLeraySite.topology e.val :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{1} e).2 inferInstance
  let x := Cohomology.sheafifiedFreeYonedaHomAddEquiv X G f
  have hcover := Presheaf.imageSieve_mem nonLeraySite.topology e.val x
  have htop := nonLeray_topology_eq_top_of_hom_to_left hX hcover
  have hid : Presheaf.imageSieve e.val x (𝟙 X) := by
    rw [htop]
    trivial
  rcases hid with ⟨t, ht⟩
  let lift : nonLeraySheafifiedFreeYoneda X ⟶ E :=
    (Cohomology.sheafifiedFreeYonedaHomAddEquiv X E).symm t
  refine ⟨lift, ?_⟩
  apply (Cohomology.sheafifiedFreeYonedaHomAddEquiv X G).injective
  rw [Cohomology.sheafifiedFreeYonedaHomAddEquiv_comp]
  change e.val.app (op X)
      (Cohomology.sheafifiedFreeYonedaHomAddEquiv X E lift) = x
  rw [show Cohomology.sheafifiedFreeYonedaHomAddEquiv X E lift = t by
    exact (Cohomology.sheafifiedFreeYonedaHomAddEquiv X E).apply_symm_apply t]
  simpa using ht

private theorem nonLeraySheafifiedFreeYoneda_projective_of_hom_to_right
    (X : nonLeraySite.category) (hX : X ⟶ nonLerayRightObject) :
    Projective (nonLeraySheafifiedFreeYoneda X) := by
  constructor
  intro E G f e he
  letI : Epi e := he
  have hloc : Presheaf.IsLocallySurjective nonLeraySite.topology e.val :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{1} e).2 inferInstance
  let x := Cohomology.sheafifiedFreeYonedaHomAddEquiv X G f
  have hcover := Presheaf.imageSieve_mem nonLeraySite.topology e.val x
  have htop := nonLeray_topology_eq_top_of_hom_to_right hX hcover
  have hid : Presheaf.imageSieve e.val x (𝟙 X) := by
    rw [htop]
    trivial
  rcases hid with ⟨t, ht⟩
  let lift : nonLeraySheafifiedFreeYoneda X ⟶ E :=
    (Cohomology.sheafifiedFreeYonedaHomAddEquiv X E).symm t
  refine ⟨lift, ?_⟩
  apply (Cohomology.sheafifiedFreeYonedaHomAddEquiv X G).injective
  rw [Cohomology.sheafifiedFreeYonedaHomAddEquiv_comp]
  change e.val.app (op X)
      (Cohomology.sheafifiedFreeYonedaHomAddEquiv X E lift) = x
  rw [show Cohomology.sheafifiedFreeYonedaHomAddEquiv X E lift = t by
    exact (Cohomology.sheafifiedFreeYonedaHomAddEquiv X E).apply_symm_apply t]
  simpa using ht

private theorem nonLerayComparisonCover_isLeray_for
    (Ob : Cohomology.ObstructionSheaf nonLeraySite) :
    Cohomology.IsLerayFor nonLerayComparisonCover Ob := by
  intro q hq p σ
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  let X := (Cohomology.canonicalCoverRelative
    nonLerayComparisonCover).overlap p σ
  have hprojection := Cohomology.canonicalTupleOverlapProjection
    nonLerayComparisonCover σ (0 : Fin (p + 1))
  cases hindex : σ 0 with
  | left =>
      have hp : X ⟶ nonLerayLeftObject := by
        simpa [X, Cohomology.canonicalCoverRelative,
          nonLerayCoverPatch, hindex] using hprojection
      letI : Projective (nonLeraySheafifiedFreeYoneda X) :=
        nonLeraySheafifiedFreeYoneda_projective_of_hom_to_left X hp
      exact CategoryTheory.Abelian.Ext.subsingleton_of_projective
        (nonLeraySheafifiedFreeYoneda X) Ob.toAddCommGrpSheaf n
  | right =>
      have hp : X ⟶ nonLerayRightObject := by
        simpa [X, Cohomology.canonicalCoverRelative,
          nonLerayCoverPatch, hindex] using hprojection
      letI : Projective (nonLeraySheafifiedFreeYoneda X) :=
        nonLeraySheafifiedFreeYoneda_projective_of_hom_to_right X hp
      exact CategoryTheory.Abelian.Ext.subsingleton_of_projective
        (nonLeraySheafifiedFreeYoneda X) Ob.toAddCommGrpSheaf n

private def nonLeraySelectedOverlapContext : Site.ArchCtx FiniteModel.object :=
  nonLerayOverlap.overlap (nonLerayContext .base)
    (nonLerayContext .left) (nonLerayContext .right)

/-- Bottom object obtained from the actual overlap of the two comparison branches. -/
def nonLerayOverlapObject : nonLeraySite.category :=
  Site.ContextCategoryObject.of nonLerayContextPreorder
    nonLeraySelectedOverlapContext

/-- The selected bottom object is definitionally the actual pair overlap. -/
theorem nonLerayPairOverlap_eq :
    nonLeraySite.overlap.overlap nonLerayBase.ctx
        nonLerayLeftObject.ctx nonLerayRightObject.ctx =
      nonLerayOverlapObject.ctx :=
  rfl

private theorem nonLeray_left_not_le_overlapObject :
    ¬ nonLerayContextPreorder.le
      nonLerayLeftObject.ctx nonLerayOverlapObject.ctx := by
  rintro ⟨f, hf⟩
  have hread := hf.1 (support := PUnit.unit)
    (atom := FiniteModel.FiniteAtom.componentA)
    (by
      change nonLeraySupportReads .left FiniteModel.FiniteAtom.componentA
      simp [nonLeraySupportReads])
  change
    nonLeraySupportReads .left FiniteModel.FiniteAtom.componentA ∧
      nonLeraySupportReads .right FiniteModel.FiniteAtom.componentA at hread
  simpa [nonLeraySupportReads] using hread.2

private theorem nonLeray_right_not_le_overlapObject :
    ¬ nonLerayContextPreorder.le
      nonLerayRightObject.ctx nonLerayOverlapObject.ctx := by
  rintro ⟨f, hf⟩
  have hread := hf.1 (support := PUnit.unit)
    (atom := FiniteModel.FiniteAtom.componentB)
    (by
      change nonLeraySupportReads .right FiniteModel.FiniteAtom.componentB
      simp [nonLeraySupportReads])
  change
    nonLeraySupportReads .left FiniteModel.FiniteAtom.componentB ∧
      nonLeraySupportReads .right FiniteModel.FiniteAtom.componentB at hread
  simpa [nonLeraySupportReads] using hread.1

/--
The actual overlap, the two branch objects, and the base have exactly the
strict-diamond order relations required by the negative firing.
-/
theorem nonLerayStrictDiamond :
    nonLerayContextPreorder.le
        nonLerayOverlapObject.ctx nonLerayLeftObject.ctx ∧
      nonLerayContextPreorder.le
        nonLerayOverlapObject.ctx nonLerayRightObject.ctx ∧
      nonLerayContextPreorder.le nonLerayLeftObject.ctx nonLerayBase.ctx ∧
      nonLerayContextPreorder.le nonLerayRightObject.ctx nonLerayBase.ctx ∧
      ¬ nonLerayContextPreorder.le nonLerayLeftObject.ctx nonLerayRightObject.ctx ∧
      ¬ nonLerayContextPreorder.le nonLerayRightObject.ctx nonLerayLeftObject.ctx ∧
      ¬ nonLerayContextPreorder.le nonLerayBase.ctx nonLerayLeftObject.ctx ∧
      ¬ nonLerayContextPreorder.le nonLerayBase.ctx nonLerayRightObject.ctx ∧
      ¬ nonLerayContextPreorder.le
        nonLerayLeftObject.ctx nonLerayOverlapObject.ctx ∧
      ¬ nonLerayContextPreorder.le
        nonLerayRightObject.ctx nonLerayOverlapObject.ctx := by
  refine ⟨?_, ?_, nonLeray_left_le_base, nonLeray_right_le_base,
    nonLeray_left_not_le_right, nonLeray_right_not_le_left,
    nonLeray_base_not_le_left, nonLeray_base_not_le_right,
    nonLeray_left_not_le_overlapObject,
    nonLeray_right_not_le_overlapObject⟩
  · exact Site.productContextFiniteMeet.meet_le_left _ _
  · exact Site.productContextFiniteMeet.meet_le_right _ _

/--
Among the four selected strict-diamond objects, only the base admits an
admissible AAT coverage family; the exhibited family is the two-branch cover.
-/
theorem nonLeraySelectedCoverClassification :
    Nonempty
        (Site.AATCoverageFamily nonLeraySite.requirements
          nonLeraySite.overlap nonLerayBase) ∧
      ¬ Nonempty
        (Site.AATCoverageFamily nonLeraySite.requirements
          nonLeraySite.overlap nonLerayLeftObject) ∧
      ¬ Nonempty
        (Site.AATCoverageFamily nonLeraySite.requirements
          nonLeraySite.overlap nonLerayRightObject) ∧
      ¬ Nonempty
        (Site.AATCoverageFamily nonLeraySite.requirements
          nonLeraySite.overlap nonLerayOverlapObject) := by
  refine ⟨⟨nonLerayComparisonCover⟩, ?_, ?_, ?_⟩
  · rintro ⟨F⟩
    rcases nonLeray_admissibleCover_has_right F with ⟨i, hi⟩
    have hinclusion := F.inclusion i
    rw [hi] at hinclusion
    exact nonLeray_right_not_le_left hinclusion
  · rintro ⟨F⟩
    rcases nonLeray_admissibleCover_has_left F with ⟨i, hi⟩
    have hinclusion := F.inclusion i
    rw [hi] at hinclusion
    exact nonLeray_left_not_le_right hinclusion
  · rintro ⟨F⟩
    rcases nonLeray_admissibleCover_has_left F with ⟨i, hi⟩
    have hinclusion := F.inclusion i
    rw [hi] at hinclusion
    exact nonLeray_left_not_le_overlapObject hinclusion

private def NonLerayNoMarkerReads (W : Site.ArchCtx FiniteModel.object) : Prop :=
  (∀ support : W.Support,
      ¬ W.minimal.supportReads support FiniteModel.FiniteAtom.componentA) ∧
    (∀ support : W.Support,
      ¬ W.minimal.supportReads support FiniteModel.FiniteAtom.componentB)

private theorem nonLerayNoMarkerReads_of_le
    {W V : Site.ArchCtx FiniteModel.object}
    (h : nonLerayContextPreorder.le W V)
    (hV : NonLerayNoMarkerReads V) :
    NonLerayNoMarkerReads W := by
  let f := nonLerayContextPreorder.readableMorphism h
  have hf := nonLerayContextPreorder.readableMorphism_isRestriction h
  constructor
  · intro support hread
    exact hV.1 (f.supportMap support) (hf.1 hread)
  · intro support hread
    exact hV.2 (f.supportMap support) (hf.1 hread)

private noncomputable def nonLerayCoefficientSubgroup
    (W : Site.ArchCtx FiniteModel.object) : AddSubgroup (ZMod 2) := by
  classical
  exact if NonLerayNoMarkerReads W then ⊤ else ⊥

private theorem nonLerayCoefficientSubgroup_mono
    {W V : Site.ArchCtx FiniteModel.object}
    (h : nonLerayContextPreorder.le W V) :
    nonLerayCoefficientSubgroup V ≤ nonLerayCoefficientSubgroup W := by
  by_cases hV : NonLerayNoMarkerReads V
  · have hW := nonLerayNoMarkerReads_of_le h hV
    simp [nonLerayCoefficientSubgroup, hV, hW]
  · simp [nonLerayCoefficientSubgroup, hV]

private noncomputable def nonLerayCoefficientPresheaf :
    nonLeraySite.categoryᵒᵖ ⥤ AddCommGrpCat.{0} where
  obj X := AddCommGrpCat.of (nonLerayCoefficientSubgroup X.unop.ctx)
  map {X Y} f := AddCommGrpCat.ofHom
    (AddSubgroup.inclusion
      (nonLerayCoefficientSubgroup_mono (leOfHom f.unop)))
  map_id X := by
    apply AddCommGrpCat.hom_ext
    ext x
    rfl
  map_comp {X Y Z} f g := by
    apply AddCommGrpCat.hom_ext
    ext x
    rfl

private theorem nonLeraySelectedOverlap_noMarkerReads :
    NonLerayNoMarkerReads nonLeraySelectedOverlapContext := by
  constructor
  · rintro ⟨leftSupport, rightSupport⟩ h
    simp [nonLeraySelectedOverlapContext, nonLerayOverlap,
      Site.meetOverlapPullback, Site.productContextFiniteMeet, Site.productContext,
      nonLerayContext, nonLeraySupportReads] at h
  · rintro ⟨leftSupport, rightSupport⟩ h
    simp [nonLeraySelectedOverlapContext, nonLerayOverlap,
      Site.meetOverlapPullback, Site.productContextFiniteMeet, Site.productContext,
      nonLerayContext, nonLeraySupportReads] at h

private theorem nonLerayLeft_not_noMarkerReads :
    ¬ NonLerayNoMarkerReads (nonLerayContext .left) := by
  intro h
  exact h.1 PUnit.unit (by simp [nonLerayContext, nonLeraySupportReads])

private theorem nonLerayRight_not_noMarkerReads :
    ¬ NonLerayNoMarkerReads (nonLerayContext .right) := by
  intro h
  exact h.2 PUnit.unit (by simp [nonLerayContext, nonLeraySupportReads])

private theorem nonLerayBase_not_noMarkerReads :
    ¬ NonLerayNoMarkerReads (nonLerayContext .base) := by
  intro h
  exact h.1 PUnit.unit (by simp [nonLerayContext, nonLeraySupportReads])

private theorem nonLerayCoefficientSubgroup_overlap_eq_top :
    nonLerayCoefficientSubgroup nonLeraySelectedOverlapContext = ⊤ := by
  simp [nonLerayCoefficientSubgroup,
    nonLeraySelectedOverlap_noMarkerReads]

private theorem nonLerayCoefficientSubgroup_left_eq_bot :
    nonLerayCoefficientSubgroup (nonLerayContext .left) = ⊥ := by
  simp [nonLerayCoefficientSubgroup, nonLerayLeft_not_noMarkerReads]

private theorem nonLerayCoefficientSubgroup_right_eq_bot :
    nonLerayCoefficientSubgroup (nonLerayContext .right) = ⊥ := by
  simp [nonLerayCoefficientSubgroup, nonLerayRight_not_noMarkerReads]

private theorem nonLerayCoefficientSubgroup_base_eq_bot :
    nonLerayCoefficientSubgroup (nonLerayContext .base) = ⊥ := by
  simp [nonLerayCoefficientSubgroup, nonLerayBase_not_noMarkerReads]

private noncomputable def nonLerayOverlapCoefficientAddEquiv :
    nonLerayCoefficientSubgroup nonLeraySelectedOverlapContext ≃+ ZMod 2 where
  toFun x := x.1
  invFun z := ⟨z, by
    rw [nonLerayCoefficientSubgroup_overlap_eq_top]
    trivial⟩
  left_inv x := by ext; rfl
  right_inv z := rfl
  map_add' x y := rfl

private theorem nonLerayNoMarkerReads_product_left
    {W V : Site.ArchCtx FiniteModel.object}
    (hW : NonLerayNoMarkerReads W) :
    NonLerayNoMarkerReads (Site.productContext W V) := by
  constructor
  · rintro ⟨w, v⟩ h
    exact hW.1 w h.1
  · rintro ⟨w, v⟩ h
    exact hW.2 w h.1

private theorem nonLerayProductWithLeft_not_noMarkerReads
    {W : Site.ArchCtx FiniteModel.object} {support : W.Support}
    (hread : W.minimal.supportReads support FiniteModel.FiniteAtom.componentA) :
    ¬ NonLerayNoMarkerReads
      (Site.productContext W (nonLerayContext .left)) := by
  intro h
  exact h.1 (support, PUnit.unit)
    ⟨hread, by simp [nonLerayContext, nonLeraySupportReads]⟩

private theorem nonLerayProductWithRight_not_noMarkerReads
    {W : Site.ArchCtx FiniteModel.object} {support : W.Support}
    (hread : W.minimal.supportReads support FiniteModel.FiniteAtom.componentB) :
    ¬ NonLerayNoMarkerReads
      (Site.productContext W (nonLerayContext .right)) := by
  intro h
  exact h.2 (support, PUnit.unit)
    ⟨hread, by simp [nonLerayContext, nonLeraySupportReads]⟩

private def nonLerayProductObject
    (X Y : nonLeraySite.category) : nonLeraySite.category :=
  Site.ContextCategoryObject.of nonLerayContextPreorder
    (Site.productContext X.ctx Y.ctx)

private noncomputable def nonLerayProductLeft
    (X Y : nonLeraySite.category) : nonLerayProductObject X Y ⟶ X :=
  homOfLE (Site.productContextFiniteMeet.meet_le_left X.ctx Y.ctx)

private noncomputable def nonLerayProductRight
    (X Y : nonLeraySite.category) : nonLerayProductObject X Y ⟶ Y :=
  homOfLE (Site.productContextFiniteMeet.meet_le_right X.ctx Y.ctx)

private theorem nonLerayCoefficientPresheaf_isSheaf :
    Presieve.IsSheaf nonLeraySite.topology
      (nonLerayCoefficientPresheaf ⋙ forget AddCommGrpCat.{0}) := by
  rw [Site.AATSite.topology, Site.AATGrothendieckTopology]
  rw [Precoverage.isSheaf_toGrothendieck_iff]
  intro X Y f R hR
  rcases hR with ⟨F, rfl⟩
  intro family hfamily
  classical
  have hmarker : ∃ i : F.Index,
      nonLerayCoefficientSubgroup
          (Site.productContext Y.ctx (F.patch i)) =
        nonLerayCoefficientSubgroup Y.ctx := by
    by_cases hY : NonLerayNoMarkerReads Y.ctx
    · rcases nonLeray_admissibleCover_has_left F with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      have hQ := nonLerayNoMarkerReads_product_left
        (V := F.patch i) hY
      simp [nonLerayCoefficientSubgroup, hY, hQ]
    · simp only [NonLerayNoMarkerReads, not_and_or, not_forall,
        not_not] at hY
      rcases hY with hA | hB
      · rcases hA with ⟨support, hsupport⟩
        rcases nonLeray_admissibleCover_has_left F with ⟨i, hi⟩
        refine ⟨i, ?_⟩
        have hQ : ¬ NonLerayNoMarkerReads
            (Site.productContext Y.ctx (F.patch i)) := by
          rw [hi]
          exact nonLerayProductWithLeft_not_noMarkerReads hsupport
        have hYnot : ¬ NonLerayNoMarkerReads Y.ctx := fun h =>
          h.1 support hsupport
        simp [nonLerayCoefficientSubgroup, hYnot, hQ]
      · rcases hB with ⟨support, hsupport⟩
        rcases nonLeray_admissibleCover_has_right F with ⟨i, hi⟩
        refine ⟨i, ?_⟩
        have hQ : ¬ NonLerayNoMarkerReads
            (Site.productContext Y.ctx (F.patch i)) := by
          rw [hi]
          exact nonLerayProductWithRight_not_noMarkerReads hsupport
        have hYnot : ¬ NonLerayNoMarkerReads Y.ctx := fun h =>
          h.2 support hsupport
        simp [nonLerayCoefficientSubgroup, hYnot, hQ]
  rcases hmarker with ⟨i, hsubgroup⟩
  let patchObject := Site.ContextCategoryObject.of nonLerayContextPreorder
    (F.patch i)
  let Q := nonLerayProductObject Y patchObject
  let q : Q ⟶ Y := nonLerayProductLeft Y patchObject
  let qpatch : Q ⟶ patchObject := nonLerayProductRight Y patchObject
  have hq : (Sieve.generate F.presieve).pullback f q := by
    change Sieve.generate F.presieve (q ≫ f)
    have hinclusion : Sieve.generate F.presieve
        (homOfLE (F.inclusion i)) :=
      Sieve.le_generate F.presieve _ (Presieve.ofArrows.mk i)
    have hcomp := (Sieve.generate F.presieve).downward_closed
      hinclusion qpatch
    convert hcomp using 1
  let reference := family q hq
  have reference_mem_Y : reference.1 ∈ nonLerayCoefficientSubgroup Y.ctx := by
    rw [← hsubgroup]
    exact reference.2
  let global : nonLerayCoefficientSubgroup Y.ctx :=
    ⟨reference.1, reference_mem_Y⟩
  have hconstant : ∀ {Z : nonLeraySite.category}
      (g : Z ⟶ Y) (hg : (Sieve.generate F.presieve).pullback f g),
      (family g hg).1 = reference.1 := by
    intro Z g hg
    let P := nonLerayProductObject Z Q
    let pz : P ⟶ Z := nonLerayProductLeft Z Q
    let pq : P ⟶ Q := nonLerayProductRight Z Q
    have hcompat := hfamily pz pq hg hq (Subsingleton.elim _ _)
    exact congrArg Subtype.val hcompat
  refine ⟨global, ?_, ?_⟩
  · intro Z g hg
    apply Subtype.ext
    change global.1 = (family g hg).1
    exact (hconstant g hg).symm
  · intro other hother
    apply Subtype.ext
    have hqOther := hother q hq
    have hval := congrArg Subtype.val hqOther
    change other.1 = global.1
    exact hval

/-- Small additive coefficient used by the strict-diamond countermodel. -/
noncomputable def nonLerayObstructionSheaf :
    Cohomology.ObstructionSheaf nonLeraySite :=
  Cohomology.ObstructionSheaf.ofAddCommGrpValued
    nonLerayCoefficientPresheaf
    ((Site.AATSheafCondition.iff_presieve_isSheaf nonLeraySite _).2
      nonLerayCoefficientPresheaf_isSheaf)

/-- The strict-diamond coefficient is zero at the base. -/
theorem nonLerayBaseCoefficient_subsingleton :
    Subsingleton
      ((nonLerayObstructionSheaf.toAddCommGrpSheaf.val.obj
        (op nonLerayBase) : Type 1)) := by
  letI : Subsingleton
      (nonLerayObstructionSheaf.carrier.toPresheaf.obj
        (op nonLerayBase)) := by
    change Subsingleton
      (nonLerayCoefficientSubgroup (nonLerayContext .base))
    rw [nonLerayCoefficientSubgroup_base_eq_bot]
    infer_instance
  exact (nonLerayObstructionSheaf.toAddCommGrpSheafObjAddEquiv
    nonLerayBase).symm.injective.subsingleton

/-- The strict-diamond coefficient is zero at the left branch. -/
theorem nonLerayLeftCoefficient_subsingleton :
    Subsingleton
      ((nonLerayObstructionSheaf.toAddCommGrpSheaf.val.obj
        (op nonLerayLeftObject) : Type 1)) := by
  letI : Subsingleton
      (nonLerayObstructionSheaf.carrier.toPresheaf.obj
        (op nonLerayLeftObject)) := by
    change Subsingleton
      (nonLerayCoefficientSubgroup (nonLerayContext .left))
    rw [nonLerayCoefficientSubgroup_left_eq_bot]
    infer_instance
  exact (nonLerayObstructionSheaf.toAddCommGrpSheafObjAddEquiv
    nonLerayLeftObject).symm.injective.subsingleton

/-- The strict-diamond coefficient is zero at the right branch. -/
theorem nonLerayRightCoefficient_subsingleton :
    Subsingleton
      ((nonLerayObstructionSheaf.toAddCommGrpSheaf.val.obj
        (op nonLerayRightObject) : Type 1)) := by
  letI : Subsingleton
      (nonLerayObstructionSheaf.carrier.toPresheaf.obj
        (op nonLerayRightObject)) := by
    change Subsingleton
      (nonLerayCoefficientSubgroup (nonLerayContext .right))
    rw [nonLerayCoefficientSubgroup_right_eq_bot]
    infer_instance
  exact (nonLerayObstructionSheaf.toAddCommGrpSheafObjAddEquiv
    nonLerayRightObject).symm.injective.subsingleton

/-- The actual overlap coefficient is additively equivalent to `ZMod 2`. -/
noncomputable def nonLerayOverlapCoefficientEquiv :
    ((nonLerayObstructionSheaf.toAddCommGrpSheaf.val.obj
      (op nonLerayOverlapObject) : Type 1)) ≃+ ZMod 2 :=
  (nonLerayObstructionSheaf.toAddCommGrpSheafObjAddEquiv
    nonLerayOverlapObject).symm.trans nonLerayOverlapCoefficientAddEquiv

/-- The two-point comparison cover is Leray for the strict-diamond coefficient. -/
theorem nonLerayComparisonCover_isLeray :
    Cohomology.IsLerayFor
      nonLerayComparisonCover nonLerayObstructionSheaf :=
  nonLerayComparisonCover_isLeray_for nonLerayObstructionSheaf

private theorem nonLerayPairOverlap_noMarkerReads
    (σ : (Cohomology.canonicalCoverRelative
      nonLerayComparisonCover).simplex 1)
    (hne : σ 0 ≠ σ 1) :
    NonLerayNoMarkerReads
      ((Cohomology.canonicalCoverRelative
        nonLerayComparisonCover).overlap 1 σ).ctx := by
  cases h0 : σ 0 <;> cases h1 : σ 1
  · exact False.elim (hne (h0.trans h1.symm))
  · change NonLerayNoMarkerReads
      (nonLeraySite.overlap.overlap nonLerayBase.ctx
        (nonLerayCoverPatch (σ 0)) (nonLerayCoverPatch (σ 1)))
    rw [show σ 0 = .left from h0, show σ 1 = .right from h1]
    constructor <;> rintro ⟨a, b⟩ h <;>
      simp [nonLerayCoverPatch,
        nonLeraySite, nonLerayOverlap, Site.meetOverlapPullback,
        Site.productContextFiniteMeet, Site.productContext,
        nonLerayContext, nonLeraySupportReads] at h
  · change NonLerayNoMarkerReads
      (nonLeraySite.overlap.overlap nonLerayBase.ctx
        (nonLerayCoverPatch (σ 0)) (nonLerayCoverPatch (σ 1)))
    rw [show σ 0 = .right from h0, show σ 1 = .left from h1]
    constructor <;> rintro ⟨a, b⟩ h <;>
      simp [nonLerayCoverPatch,
        nonLeraySite, nonLerayOverlap, Site.meetOverlapPullback,
        Site.productContextFiniteMeet, Site.productContext,
        nonLerayContext, nonLeraySupportReads] at h
  · exact False.elim (hne (h0.trans h1.symm))

/-- Decidable equality for the two branches of the comparison cover. -/
local instance : DecidableEq nonLerayComparisonCover.Index := Classical.decEq _

private noncomputable def nonLerayCechOneCochain :
    (Cohomology.canonicalCechComplex nonLerayComparisonCover
      nonLerayObstructionSheaf).AdditiveCochain 1 := by
  intro σ
  by_cases h : σ 0 = σ 1
  · exact 0
  · exact ⟨1, by
      have hNoMarker := nonLerayPairOverlap_noMarkerReads σ h
      change (1 : ZMod 2) ∈ nonLerayCoefficientSubgroup
        ((Cohomology.canonicalCoverRelative
          nonLerayComparisonCover).overlap 1 σ).ctx
      unfold nonLerayCoefficientSubgroup
      rw [if_pos hNoMarker]
      trivial⟩

private theorem nonLerayCechOneCochain_val
    (σ : (Cohomology.canonicalCoverRelative
      nonLerayComparisonCover).simplex 1) :
    (nonLerayCechOneCochain σ).1 =
      if σ 0 = σ 1 then 0 else (1 : ZMod 2) := by
  classical
  by_cases h : σ 0 = σ 1 <;>
    simp [nonLerayCechOneCochain, h]

private theorem nonLerayObstructionMap_val {X Y : nonLeraySite.category}
    (f : X ⟶ Y)
    (x : nonLerayObstructionSheaf.carrier.toPresheaf.obj (Opposite.op Y)) :
    (nonLerayObstructionSheaf.mapAddMonoidHom f x).1 = x.1 :=
  rfl

private theorem nonLerayFace_zero_first
    (σ : (Cohomology.canonicalCoverRelative
      nonLerayComparisonCover).simplex 2) :
    ((Cohomology.canonicalCoverRelative nonLerayComparisonCover).face 1
      (0 : Fin 3) σ) 0 = σ 1 :=
  rfl

private theorem nonLeraySimplexMap_zero_first
    (σ : (Cohomology.canonicalCoverRelative
      nonLerayComparisonCover).simplex 2) :
    (Site.FinitePosetCechCanonicalTupleSimplex.simplexMap
      (SimplexCategory.δ (0 : Fin 3)) σ) 0 = σ 1 :=
  rfl

private theorem nonLerayFace_zero_second
    (σ : (Cohomology.canonicalCoverRelative
      nonLerayComparisonCover).simplex 2) :
    ((Cohomology.canonicalCoverRelative nonLerayComparisonCover).face 1
      (0 : Fin 3) σ) 1 = σ 2 :=
  rfl

private theorem nonLeraySimplexMap_zero_second
    (σ : (Cohomology.canonicalCoverRelative
      nonLerayComparisonCover).simplex 2) :
    (Site.FinitePosetCechCanonicalTupleSimplex.simplexMap
      (SimplexCategory.δ (0 : Fin 3)) σ) 1 = σ 2 :=
  rfl

private theorem nonLerayFace_one_first
    (σ : (Cohomology.canonicalCoverRelative
      nonLerayComparisonCover).simplex 2) :
    ((Cohomology.canonicalCoverRelative nonLerayComparisonCover).face 1
      (1 : Fin 3) σ) 0 = σ 0 :=
  rfl

private theorem nonLeraySimplexMap_one_first
    (σ : (Cohomology.canonicalCoverRelative
      nonLerayComparisonCover).simplex 2) :
    (Site.FinitePosetCechCanonicalTupleSimplex.simplexMap
      (SimplexCategory.δ (1 : Fin 3)) σ) 0 = σ 0 :=
  rfl

private theorem nonLerayFace_one_second
    (σ : (Cohomology.canonicalCoverRelative
      nonLerayComparisonCover).simplex 2) :
    ((Cohomology.canonicalCoverRelative nonLerayComparisonCover).face 1
      (1 : Fin 3) σ) 1 = σ 2 :=
  rfl

private theorem nonLeraySimplexMap_one_second
    (σ : (Cohomology.canonicalCoverRelative
      nonLerayComparisonCover).simplex 2) :
    (Site.FinitePosetCechCanonicalTupleSimplex.simplexMap
      (SimplexCategory.δ (1 : Fin 3)) σ) 1 = σ 2 :=
  rfl

private theorem nonLerayFace_two_first
    (σ : (Cohomology.canonicalCoverRelative
      nonLerayComparisonCover).simplex 2) :
    ((Cohomology.canonicalCoverRelative nonLerayComparisonCover).face 1
      (2 : Fin 3) σ) 0 = σ 0 :=
  rfl

private theorem nonLeraySimplexMap_two_first
    (σ : (Cohomology.canonicalCoverRelative
      nonLerayComparisonCover).simplex 2) :
    (Site.FinitePosetCechCanonicalTupleSimplex.simplexMap
      (SimplexCategory.δ (2 : Fin 3)) σ) 0 = σ 0 :=
  rfl

private theorem nonLerayFace_two_second
    (σ : (Cohomology.canonicalCoverRelative
      nonLerayComparisonCover).simplex 2) :
    ((Cohomology.canonicalCoverRelative nonLerayComparisonCover).face 1
      (2 : Fin 3) σ) 1 = σ 1 :=
  rfl

private theorem nonLeraySimplexMap_two_second
    (σ : (Cohomology.canonicalCoverRelative
      nonLerayComparisonCover).simplex 2) :
    (Site.FinitePosetCechCanonicalTupleSimplex.simplexMap
      (SimplexCategory.δ (2 : Fin 3)) σ) 1 = σ 1 :=
  rfl

set_option maxHeartbeats 800000 in
private theorem nonLerayCechOneCochain_isCocycle :
    (Cohomology.canonicalCechComplex nonLerayComparisonCover
      nonLerayObstructionSheaf).d 1 nonLerayCechOneCochain =
        (0 : (Cohomology.canonicalCechComplex nonLerayComparisonCover
          nonLerayObstructionSheaf).AdditiveCochain 2) := by
  funext σ
  rw [Cohomology.canonicalCechComplex_d_apply]
  refine Subtype.ext ?_
  classical
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fintype.sum_empty, add_zero,
    Cohomology.canonicalCoverRelative_face]
  rw [AddSubgroup.coe_add, AddSubgroup.coe_add,
    AddSubgroup.coe_zsmul, AddSubgroup.coe_zsmul,
    AddSubgroup.coe_zsmul]
  rw [nonLerayObstructionMap_val, nonLerayObstructionMap_val,
    nonLerayObstructionMap_val]
  norm_num
  simp_rw [nonLerayCechOneCochain_val]
  change _ = (0 : ZMod 2)
  have h0 : σ 0 = .left ∨ σ 0 = .right := by
    cases σ 0 <;> simp
  have h1 : σ 1 = .left ∨ σ 1 = .right := by
    cases σ 1 <;> simp
  have h2 : σ 2 = .left ∨ σ 2 = .right := by
    cases σ 2 <;> simp
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2 <;>
    simp [SimplexCategory.δ, Fin.succAbove, h0, h1, h2] <;>
    decide

private noncomputable def nonLerayCechOneCocycle :
    (Cohomology.canonicalCechComplex nonLerayComparisonCover
      nonLerayObstructionSheaf).CechCocycle 1 :=
  ⟨nonLerayCechOneCochain, nonLerayCechOneCochain_isCocycle⟩

private theorem nonLerayDegreeZeroCoefficient_eq_bot
    (σ : (Cohomology.canonicalCoverRelative
      nonLerayComparisonCover).simplex 0) :
    nonLerayCoefficientSubgroup
      ((Cohomology.canonicalCoverRelative
        nonLerayComparisonCover).overlap 0 σ).ctx = ⊥ := by
  cases h : σ 0
  · simpa [Cohomology.canonicalCoverRelative,
      Cohomology.canonicalTupleOverlap, nonLerayComparisonCover,
      nonLerayCoverPatch, h] using nonLerayCoefficientSubgroup_left_eq_bot
  · simpa [Cohomology.canonicalCoverRelative,
      Cohomology.canonicalTupleOverlap, nonLerayComparisonCover,
      nonLerayCoverPatch, h] using nonLerayCoefficientSubgroup_right_eq_bot

private theorem nonLerayCechZeroCochain_eq_zero
    (b : (Cohomology.canonicalCechComplex nonLerayComparisonCover
      nonLerayObstructionSheaf).AdditiveCochain 0) :
    b = 0 := by
  funext σ
  refine Subtype.ext ?_
  let x : ZMod 2 := (b σ).1
  have hx : x ∈ nonLerayCoefficientSubgroup
      ((Cohomology.canonicalCoverRelative
        nonLerayComparisonCover).overlap 0 σ).ctx := (b σ).2
  rw [nonLerayDegreeZeroCoefficient_eq_bot σ] at hx
  change x = 0 at hx
  exact hx

private def nonLerayMixedOneSimplex :
    (Cohomology.canonicalCoverRelative
      nonLerayComparisonCover).simplex 1 :=
  fun i => if i = 0 then .left else .right

private theorem nonLerayCechOneCochain_mixed_val :
    (nonLerayCechOneCochain nonLerayMixedOneSimplex).1 =
      (1 : ZMod 2) := by
  simp [nonLerayCechOneCochain_val, nonLerayMixedOneSimplex]

private theorem nonLerayCechOneCochain_ne_zero :
    nonLerayCechOneCochain ≠ 0 := by
  intro h
  have hv := congrArg
    (fun c => (c nonLerayMixedOneSimplex).1) h
  change (nonLerayCechOneCochain nonLerayMixedOneSimplex).1 =
    ((0 : (Cohomology.canonicalCechComplex nonLerayComparisonCover
      nonLerayObstructionSheaf).AdditiveCochain 1)
        nonLerayMixedOneSimplex).1 at hv
  rw [nonLerayCechOneCochain_mixed_val] at hv
  change (1 : ZMod 2) = 0 at hv
  exact one_ne_zero hv

private theorem nonLerayCechOneClass_ne_zero :
    (Cohomology.canonicalCechComplex nonLerayComparisonCover
      nonLerayObstructionSheaf).additiveH1Class
        nonLerayCechOneCocycle ≠ 0 := by
  intro hzero
  let K := Cohomology.canonicalCechComplex nonLerayComparisonCover
    nonLerayObstructionSheaf
  rcases (K.additiveH1Class_eq_zero_iff
    nonLerayCechOneCocycle).mp hzero with ⟨b, hb⟩
  rw [nonLerayCechZeroCochain_eq_zero b] at hb
  have : nonLerayCechOneCochain = 0 := by
    simpa [K] using hb
  exact nonLerayCechOneCochain_ne_zero this

/-- The explicit degree-one Čech class makes the comparison-cover Čech H¹ nontrivial. -/
theorem nonLerayCechHOne_nontrivial :
    Nontrivial
      ((Cohomology.canonicalCechComplex
        nonLerayComparisonCover nonLerayObstructionSheaf).AdditiveCechHn 1) := by
  let K := Cohomology.canonicalCechComplex nonLerayComparisonCover
    nonLerayObstructionSheaf
  exact ⟨⟨K.additiveH1Class nonLerayCechOneCocycle, 0,
    nonLerayCechOneClass_ne_zero⟩⟩

/-- Leray comparison sends the explicit Čech class to a nonzero actual local H¹ class. -/
theorem nonLerayHPrimeOne_nontrivial :
    Nontrivial
      ((nonLerayObstructionSheaf.toAddCommGrpSheaf).H' 1 nonLerayBase) := by
  letI : Nontrivial
      ((Cohomology.canonicalCechComplex nonLerayComparisonCover
        nonLerayObstructionSheaf).AdditiveCechHn 1) :=
    nonLerayCechHOne_nontrivial
  exact (Cohomology.cechToSheafHAtBaseEquiv nonLerayComparisonCover
    nonLerayObstructionSheaf nonLerayComparisonCover_isLeray
      1).toEquiv.symm.nontrivial

private def nonLerayIdentityCoverPatch :
    Option NonLerayCoverIndex → Site.ArchCtx FiniteModel.object
  | none => nonLerayContext .base
  | some i => nonLerayCoverPatch i

/-- Identity-containing selected cover used by the premise-free negative firing. -/
noncomputable def nonLerayCover :
    Site.AATCoverageFamily nonLeraySite.requirements
      nonLeraySite.overlap nonLerayBase where
  Index := Option NonLerayCoverIndex
  patch := nonLerayIdentityCoverPatch
  inclusion := by
    intro i
    cases i with
    | none => exact nonLerayContextPreorder.refl _
    | some i =>
        cases i
        · exact nonLeray_left_le_base
        · exact nonLeray_right_le_base
  admissible := {
    atomSupportCoverage := by
      intro atom h
      rcases h with rfl | rfl
      · exact ⟨some .left, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨some .right, Or.inr ⟨rfl, rfl⟩⟩
    equationCoordinateCoverage := by
      intro coordinate h
      exact Or.inl ⟨some .left, trivial⟩
    violationWitnessCoverage := by
      intro witness h
      exact Or.inl ⟨some .left, trivial⟩
    signatureAxisCoverage := by
      intro axis h
      exact ⟨some .left, Or.inl rfl⟩
    boundaryCoverage := by
      intro i j
      trivial
    nonGeneration := by
      intro i support atom h
      cases i with
      | none =>
          simp [nonLerayBase, nonLerayIdentityCoverPatch,
            nonLerayContext, nonLeraySupportReads] at h
          rcases h with h | h
          · rw [h]; exact FiniteModel.allFamily_mem _ (by simp)
          · rw [h]; exact FiniteModel.allFamily_mem _ (by simp)
      | some i =>
          exact nonLerayComparisonCover.admissible.nonGeneration i h
  }

/-- The negative selected cover contains the base as an identity chart. -/
theorem nonLerayCover_containsIdentity :
    ∃ i : nonLerayCover.Index,
      nonLerayCover.patch i = nonLerayBase.ctx :=
  ⟨none, rfl⟩

/-- The identity-containing selected cover is not Leray, without a caller-supplied cohomology premise. -/
theorem nonLerayCover_not_completionEvidence :
    ¬ Cohomology.IsLerayFor nonLerayCover nonLerayObstructionSheaf := by
  let σ : (Cohomology.canonicalCoverRelative nonLerayCover).simplex 0 :=
    fun _ => none
  letI : Nontrivial
      ((nonLerayObstructionSheaf.toAddCommGrpSheaf).H' 1
        ((Cohomology.canonicalCoverRelative nonLerayCover).overlap 0 σ)) := by
    simpa [σ, Cohomology.canonicalCoverRelative,
      Cohomology.canonicalTupleOverlap, nonLerayCover,
      nonLerayIdentityCoverPatch] using nonLerayHPrimeOne_nontrivial
  exact Cohomology.not_isLerayFor_of_nontrivialHPrime
    (𝒰 := nonLerayCover) (Ob := nonLerayObstructionSheaf)
    (q := 1) (p := 0) (by omega) σ

/-- The same concrete coefficient rejects the generic large-sheaf Leray predicate. -/
theorem nonLerayCover_not_isLerayForSheaf :
    ¬ Cohomology.IsLerayForSheaf
      nonLerayCover nonLerayObstructionSheaf.toAddCommGrpSheaf := by
  let σ : (Cohomology.canonicalCoverRelative nonLerayCover).simplex 0 :=
    fun _ => none
  letI : Nontrivial
      ((nonLerayObstructionSheaf.toAddCommGrpSheaf).H' 1
        ((Cohomology.canonicalCoverRelative nonLerayCover).overlap 0 σ)) := by
    simpa [σ, Cohomology.canonicalCoverRelative,
      Cohomology.canonicalTupleOverlap, nonLerayCover,
      nonLerayIdentityCoverPatch] using nonLerayHPrimeOne_nontrivial
  exact Cohomology.not_isLerayForSheaf_of_nontrivialHPrime
    (𝒰 := nonLerayCover)
    (F := nonLerayObstructionSheaf.toAddCommGrpSheaf)
    (q := 1) (p := 0) (by omega) σ

/-! ## SD9 positive actual-Sheaf-H firing -/

/-- Named additive sheafification instance used by the finite SD9 firing. -/
noncomputable instance finiteAddCommGrpHasSheafify :
    HasSheafify finiteSite.topology AddCommGrpCat.{1} := by
  infer_instance

private noncomputable def finiteCoefficientPresheaf :
    finiteSite.categoryᵒᵖ ⥤ AddCommGrpCat.{0} where
  obj _ := AddCommGrpCat.of (ZMod 2)
  map _ := AddCommGrpCat.ofHom (AddMonoidHom.id (ZMod 2))
  map_id _ := rfl
  map_comp _ _ := rfl

private def finiteProductObject
    (X Y : finiteSite.category) : finiteSite.category :=
  Site.ContextCategoryObject.of finiteSite.contextPreorder
    (Site.productContext X.ctx Y.ctx)

private noncomputable def finiteProductLeft
    (X Y : finiteSite.category) : finiteProductObject X Y ⟶ X :=
  homOfLE (Site.productContextFiniteMeet.meet_le_left X.ctx Y.ctx)

private noncomputable def finiteProductRight
    (X Y : finiteSite.category) : finiteProductObject X Y ⟶ Y :=
  homOfLE (Site.productContextFiniteMeet.meet_le_right X.ctx Y.ctx)

private theorem finiteCoefficientPresheaf_isSheaf :
    Presieve.IsSheaf finiteSite.topology
      (finiteCoefficientPresheaf ⋙ forget AddCommGrpCat.{0}) := by
  rw [Site.AATSite.topology, Site.AATGrothendieckTopology]
  rw [Precoverage.isSheaf_toGrothendieck_iff]
  intro X Y f R hR
  rcases hR with ⟨F, rfl⟩
  intro family hfamily
  classical
  rcases F.admissible.atomSupportCoverage
      FiniteModel.FiniteAtom.componentA (Or.inl rfl) with ⟨i, hi⟩
  let patchObject := Site.ContextCategoryObject.of finiteSite.contextPreorder
    (F.patch i)
  let Q := finiteProductObject Y patchObject
  let q : Q ⟶ Y := finiteProductLeft Y patchObject
  let qpatch : Q ⟶ patchObject := finiteProductRight Y patchObject
  have hq : (Sieve.generate F.presieve).pullback f q := by
    change Sieve.generate F.presieve (q ≫ f)
    have hinclusion : Sieve.generate F.presieve
        (homOfLE (F.inclusion i)) :=
      Sieve.le_generate F.presieve _ (Presieve.ofArrows.mk i)
    have hcomp := (Sieve.generate F.presieve).downward_closed
      hinclusion qpatch
    convert hcomp using 1
  let reference := family q hq
  have hconstant : ∀ {Z : finiteSite.category}
      (g : Z ⟶ Y) (hg : (Sieve.generate F.presieve).pullback f g),
      family g hg = reference := by
    intro Z g hg
    let P := finiteProductObject Z Q
    let pz : P ⟶ Z := finiteProductLeft Z Q
    let pq : P ⟶ Q := finiteProductRight Z Q
    have hcompat := hfamily pz pq hg hq (Subsingleton.elim _ _)
    simpa [finiteCoefficientPresheaf] using hcompat
  refine ⟨reference, ?_, ?_⟩
  · intro Z g hg
    simpa [finiteCoefficientPresheaf] using (hconstant g hg).symm
  · intro other hother
    simpa [finiteCoefficientPresheaf] using hother q hq

/-- Nonzero constant `ZMod 2` obstruction coefficient on the finite positive model. -/
noncomputable def finiteObstructionSheaf :
    Cohomology.ObstructionSheaf finiteSite :=
  Cohomology.ObstructionSheaf.ofAddCommGrpValued
    finiteCoefficientPresheaf
    ((Site.AATSheafCondition.iff_presieve_isSheaf finiteSite _).2
      finiteCoefficientPresheaf_isSheaf)

private def finiteLeftObject : finiteSite.category :=
  Site.ContextCategoryObject.of finiteSite.contextPreorder
    (FiniteModel.twoPatchContext .left)

private def finiteRightObject : finiteSite.category :=
  Site.ContextCategoryObject.of finiteSite.contextPreorder
    (FiniteModel.twoPatchContext .right)

private theorem finite_admissibleCover_has_left
    {Z : finiteSite.category}
    (F : Site.AATCoverageFamily finiteSite.requirements
      finiteSite.overlap Z) :
    ∃ i : F.Index, F.patch i = FiniteModel.twoPatchContext .left := by
  rcases F.admissible.atomSupportCoverage
      FiniteModel.FiniteAtom.componentA (Or.inl rfl) with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  simpa [finiteSite, FiniteModel.twoPatchSite,
    FiniteModel.twoPatchSelectedGeometryReading,
    FiniteModel.twoPatchCoverageRequirements,
    FiniteModel.twoPatchSupportVisibleOn] using hi

private theorem finite_admissibleCover_has_right
    {Z : finiteSite.category}
    (F : Site.AATCoverageFamily finiteSite.requirements
      finiteSite.overlap Z) :
    ∃ i : F.Index, F.patch i = FiniteModel.twoPatchContext .right := by
  rcases F.admissible.atomSupportCoverage
      FiniteModel.FiniteAtom.componentB (Or.inr rfl) with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  simpa [finiteSite, FiniteModel.twoPatchSite,
    FiniteModel.twoPatchSelectedGeometryReading,
    FiniteModel.twoPatchCoverageRequirements,
    FiniteModel.twoPatchSupportVisibleOn] using hi

private theorem finite_topology_contains_of_hom_to_left
    {X : finiteSite.category} (hX : X ⟶ finiteLeftObject) :
    ∀ {Z : finiteSite.category} (f : X ⟶ Z)
      {R : Sieve Z}, R ∈ finiteSite.topology Z → R f := by
  intro Z f R hR
  change (Site.admissiblePrecoverage finiteSite.requirements
    finiteSite.overlap).Saturate Z R at hR
  induction hR with
  | of Z P hP =>
      rcases hP with ⟨F, rfl⟩
      rcases finite_admissibleCover_has_left F with ⟨i, hi⟩
      let g : X ⟶ Site.ContextCategoryObject.of finiteSite.contextPreorder
          (F.patch i) :=
        hX ≫ eqToHom (congrArg
          (Site.ContextCategoryObject.of finiteSite.contextPreorder) hi).symm
      have hinclusion : (Sieve.generate F.presieve)
          (homOfLE (F.inclusion i)) :=
        Sieve.le_generate F.presieve _ (Presieve.ofArrows.mk i)
      have hcomp := (Sieve.generate F.presieve).downward_closed
        hinclusion g
      convert hcomp using 1
  | top Z => simp
  | pullback Z S hS Y g ih =>
      change S (f ≫ g)
      exact ih (f ≫ g)
  | transitive Z S R hS hlocal ihS ihlocal =>
      have hSf : S f := ihS f
      have hRf : (R.pullback f) (𝟙 X) := ihlocal hSf (𝟙 X)
      simpa using hRf

private theorem finite_topology_contains_of_hom_to_right
    {X : finiteSite.category} (hX : X ⟶ finiteRightObject) :
    ∀ {Z : finiteSite.category} (f : X ⟶ Z)
      {R : Sieve Z}, R ∈ finiteSite.topology Z → R f := by
  intro Z f R hR
  change (Site.admissiblePrecoverage finiteSite.requirements
    finiteSite.overlap).Saturate Z R at hR
  induction hR with
  | of Z P hP =>
      rcases hP with ⟨F, rfl⟩
      rcases finite_admissibleCover_has_right F with ⟨i, hi⟩
      let g : X ⟶ Site.ContextCategoryObject.of finiteSite.contextPreorder
          (F.patch i) :=
        hX ≫ eqToHom (congrArg
          (Site.ContextCategoryObject.of finiteSite.contextPreorder) hi).symm
      have hinclusion : (Sieve.generate F.presieve)
          (homOfLE (F.inclusion i)) :=
        Sieve.le_generate F.presieve _ (Presieve.ofArrows.mk i)
      have hcomp := (Sieve.generate F.presieve).downward_closed
        hinclusion g
      convert hcomp using 1
  | top Z => simp
  | pullback Z S hS Y g ih =>
      change S (f ≫ g)
      exact ih (f ≫ g)
  | transitive Z S R hS hlocal ihS ihlocal =>
      have hSf : S f := ihS f
      have hRf : (R.pullback f) (𝟙 X) := ihlocal hSf (𝟙 X)
      simpa using hRf

private theorem finite_topology_eq_top_of_hom_to_left
    {X : finiteSite.category} (hX : X ⟶ finiteLeftObject)
    {R : Sieve X} (hR : R ∈ finiteSite.topology X) : R = ⊤ := by
  apply top_unique
  intro Y f hf
  exact finite_topology_contains_of_hom_to_left (f ≫ hX) f hR

private theorem finite_topology_eq_top_of_hom_to_right
    {X : finiteSite.category} (hX : X ⟶ finiteRightObject)
    {R : Sieve X} (hR : R ∈ finiteSite.topology X) : R = ⊤ := by
  apply top_unique
  intro Y f hf
  exact finite_topology_contains_of_hom_to_right (f ≫ hX) f hR

private noncomputable def finiteSheafifiedFreeYoneda
    (X : finiteSite.category) :
    Sheaf finiteSite.topology AddCommGrpCat.{1} :=
  (presheafToSheaf finiteSite.topology AddCommGrpCat.{1}).obj
    (yoneda.obj X ⋙ AddCommGrpCat.free)

private theorem finiteSheafifiedFreeYoneda_projective_of_hom_to_left
    (X : finiteSite.category) (hX : X ⟶ finiteLeftObject) :
    Projective (finiteSheafifiedFreeYoneda X) := by
  constructor
  intro E G f e he
  letI : Epi e := he
  have hloc : Presheaf.IsLocallySurjective finiteSite.topology e.val :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{1} e).2 inferInstance
  let x := Cohomology.sheafifiedFreeYonedaHomAddEquiv X G f
  have hcover := Presheaf.imageSieve_mem finiteSite.topology e.val x
  have htop := finite_topology_eq_top_of_hom_to_left hX hcover
  have hid : Presheaf.imageSieve e.val x (𝟙 X) := by
    rw [htop]
    trivial
  rcases hid with ⟨t, ht⟩
  let lift : finiteSheafifiedFreeYoneda X ⟶ E :=
    (Cohomology.sheafifiedFreeYonedaHomAddEquiv X E).symm t
  refine ⟨lift, ?_⟩
  apply (Cohomology.sheafifiedFreeYonedaHomAddEquiv X G).injective
  rw [Cohomology.sheafifiedFreeYonedaHomAddEquiv_comp]
  change e.val.app (Opposite.op X)
      (Cohomology.sheafifiedFreeYonedaHomAddEquiv X E lift) = x
  rw [show Cohomology.sheafifiedFreeYonedaHomAddEquiv X E lift = t by
    exact (Cohomology.sheafifiedFreeYonedaHomAddEquiv X E).apply_symm_apply t]
  simpa using ht

private theorem finiteSheafifiedFreeYoneda_projective_of_hom_to_right
    (X : finiteSite.category) (hX : X ⟶ finiteRightObject) :
    Projective (finiteSheafifiedFreeYoneda X) := by
  constructor
  intro E G f e he
  letI : Epi e := he
  have hloc : Presheaf.IsLocallySurjective finiteSite.topology e.val :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{1} e).2 inferInstance
  let x := Cohomology.sheafifiedFreeYonedaHomAddEquiv X G f
  have hcover := Presheaf.imageSieve_mem finiteSite.topology e.val x
  have htop := finite_topology_eq_top_of_hom_to_right hX hcover
  have hid : Presheaf.imageSieve e.val x (𝟙 X) := by
    rw [htop]
    trivial
  rcases hid with ⟨t, ht⟩
  let lift : finiteSheafifiedFreeYoneda X ⟶ E :=
    (Cohomology.sheafifiedFreeYonedaHomAddEquiv X E).symm t
  refine ⟨lift, ?_⟩
  apply (Cohomology.sheafifiedFreeYonedaHomAddEquiv X G).injective
  rw [Cohomology.sheafifiedFreeYonedaHomAddEquiv_comp]
  change e.val.app (Opposite.op X)
      (Cohomology.sheafifiedFreeYonedaHomAddEquiv X E lift) = x
  rw [show Cohomology.sheafifiedFreeYonedaHomAddEquiv X E lift = t by
    exact (Cohomology.sheafifiedFreeYonedaHomAddEquiv X E).apply_symm_apply t]
  simpa using ht

/-- The actual finite positive model discharges Leray vanishing for its selected cover. -/
theorem finiteLerayCover :
    Cohomology.IsLerayFor coarseCover finiteObstructionSheaf := by
  intro q hq p σ
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  let X := (Cohomology.canonicalCoverRelative coarseCover).overlap p σ
  have hprojection := Cohomology.canonicalTupleOverlapProjection
    coarseCover σ (0 : Fin (p + 1))
  cases hindex : σ 0 with
  | left =>
      have hp : X ⟶ finiteLeftObject := by
        simpa [X, Cohomology.canonicalCoverRelative, coarseCover,
          FiniteModel.twoPatchCover, FiniteModel.twoPatchCoverPatch,
          FiniteModel.twoPatchCoverContextIndex, hindex] using hprojection
      letI : Projective (finiteSheafifiedFreeYoneda X) :=
        finiteSheafifiedFreeYoneda_projective_of_hom_to_left X hp
      exact CategoryTheory.Abelian.Ext.subsingleton_of_projective
        (finiteSheafifiedFreeYoneda X) finiteObstructionSheaf.toAddCommGrpSheaf n
  | right =>
      have hp : X ⟶ finiteRightObject := by
        simpa [X, Cohomology.canonicalCoverRelative, coarseCover,
          FiniteModel.twoPatchCover, FiniteModel.twoPatchCoverPatch,
          FiniteModel.twoPatchCoverContextIndex, hindex] using hprojection
      letI : Projective (finiteSheafifiedFreeYoneda X) :=
        finiteSheafifiedFreeYoneda_projective_of_hom_to_right X hp
      exact CategoryTheory.Abelian.Ext.subsingleton_of_projective
        (finiteSheafifiedFreeYoneda X) finiteObstructionSheaf.toAddCommGrpSheaf n

/-- The strict finite cover refinement induces a nonzero Čech cochain map. -/
theorem coarseToFineCechHom_nonzero :
    ∃ (n : Nat)
      (c : (Cohomology.canonicalCechComplex
        coarseCover finiteObstructionSheaf).AdditiveCochain n)
      (σ : (Cohomology.canonicalCoverRelative fineCover).simplex n),
      (coarseToFineCover.canonicalCechHom finiteObstructionSheaf).app n c σ ≠ 0 := by
  refine ⟨0, fun _ => (1 : ZMod 2), fun _ =>
    (FiniteModel.TwoPatchCoverIndex.left, false), ?_⟩
  change (1 : ZMod 2) ≠ 0
  decide

/-- The finite positive model fires the actual terminal Čech-to-sheaf-cohomology comparison. -/
theorem finite_cechToSheafH_bijective (n : Nat) :
    Function.Bijective
      (Cohomology.cechToSheafH coarseCover finiteObstructionSheaf
        finiteBaseIsTerminal finiteLerayCover n) :=
  Cohomology.cechToSheafH_bijective coarseCover finiteObstructionSheaf
    finiteBaseIsTerminal finiteLerayCover n

/-! ## R9a: positive core reading change and signed-query obstruction -/

private inductive PositiveExtractionSource where
  | source
  | target

private def positiveSourceAllows (atom : FiniteModel.carrier.Atom) : Prop :=
  atom = FiniteModel.FiniteAtom.componentA ∨
    atom = FiniteModel.FiniteAtom.componentB ∨
      atom = FiniteModel.FiniteAtom.dependsAB

private def positiveTargetAllows (atom : FiniteModel.carrier.Atom) : Prop :=
  atom = FiniteModel.FiniteAtom.componentC ∨
    atom = FiniteModel.FiniteAtom.dependsBC

private def positiveExtractionDoctrine :
    ExtractionDoctrine FiniteModel.carrier where
  Source := PositiveExtractionSource
  Vocabulary := PUnit
  SemanticReading := PUnit
  Resolution := PUnit
  vocabulary := PUnit.unit
  semanticReading := PUnit.unit
  resolution := PUnit.unit
  vocabularyAllows := fun _ _ => True
  semanticAllows := fun _ selectedSource atom =>
    match selectedSource with
    | .source => positiveSourceAllows atom
    | .target => positiveTargetAllows atom
  resolutionAllows := fun _ _ _ => True
  sourceSemantics := fun _ _ => True
  normalize := id

private def positiveCompositionReading :
    CompositionReading FiniteModel.carrier where
  compose family _ := {
    family := family
    relation := fun _ _ => False
    identification := fun _ _ => False
  }
  family_eq := by intros; rfl
  family_supported := by
    intro family hfinite
    exact ⟨fun h => False.elim h, fun h => False.elim h⟩

/-- Empty readable context used to refute the constant nonzero residual below. -/
private def emptyEquationContext
    (A : ArchitectureObject FiniteModel.carrier) : Site.ArchCtx A where
  minimal := {
    Support := PUnit
    Axis := PUnit
    Observable := PUnit
    supportReads := fun _ _ => False
    supportReads_objectFamily := fun h => False.elim h
    axisReads := fun _ => False
    observableReads := fun _ => False
  }
  Extension := PUnit
  extension := PUnit.unit

/-- Singleton required equation whose residual is constantly nonzero. -/
private noncomputable def falseEquationSystem
    (A : ArchitectureObject FiniteModel.carrier) :
    ArchitecturalEquationSystem (Site.contextMorphismPreorderCategory A) where
  Index := PUnit
  role _ := EquationRole.required
  Observable := fun _ => Int
  observableCommRing := fun _ => inferInstance
  restrict := fun _ => RingHom.id Int
  restrict_id := by intros; rfl
  restrict_comp := by intros; rfl
  violationCoordinate := fun _ _ _ => 2
  violationCoordinate_restrict := by intros; rfl
  equationResidual := fun _ _ _ _ => 1
  equationResidual_restrict := by intros; rfl

/-- Equation reading for a selected exact detector of the constantly false equation. -/
private noncomputable def falseEquationReading
    (A : ArchitectureObject FiniteModel.carrier)
    (datum : FiniteCircuitDatum FiniteModel.carrier) : EquationReading A where
  contextPreorder := Site.contextMorphismPreorderCategory A
  equationSystem := falseEquationSystem A
  circuits := {
    code := fun _ => .exact datum
  }
  circuitSound := by
    intro _index _object _query _hmatches _haccepts hequation
    have hcoordinate := hequation
      (Site.ContextCategoryObject.of
        (Site.contextMorphismPreorderCategory A) (emptyEquationContext A))
      FiniteModel.FiniteAtom.componentA
    have hfalse : (1 : Int) = 0 := by
      simpa only [falseEquationSystem] using hcoordinate
    norm_num at hfalse

private def positiveSourceDatum : FiniteCircuitDatum FiniteModel.carrier where
  queries := [(.atomPresent FiniteModel.FiniteAtom.componentA, true)]

private def positiveTargetDatum : FiniteCircuitDatum FiniteModel.carrier where
  queries := [(.atomPresent FiniteModel.FiniteAtom.componentC, true)]

private noncomputable def positiveSourceCoreReading :
    CoreReading FiniteModel.carrier where
  doctrine := positiveExtractionDoctrine
  source := .source
  family_listFinite := ⟨FiniteModel.FiniteAtom.all,
    fun atom _ => FiniteModel.FiniteAtom.mem_all atom⟩
  composition := positiveCompositionReading
  objectReading := FiniteModel.objectReading
  equationReading := falseEquationReading _ positiveSourceDatum
  invariantReading := FiniteModel.invariantFamily
  signatureReading := FiniteModel.signature
  operationReading := FiniteModel.operationReading

private noncomputable def positiveTargetCoreReading :
    CoreReading FiniteModel.carrier where
  doctrine := positiveExtractionDoctrine
  source := .target
  family_listFinite := ⟨FiniteModel.FiniteAtom.all,
    fun atom _ => FiniteModel.FiniteAtom.mem_all atom⟩
  composition := positiveCompositionReading
  objectReading := FiniteModel.objectReading
  equationReading := falseEquationReading _ positiveTargetDatum
  invariantReading := FiniteModel.invariantFamily
  signatureReading := FiniteModel.signature
  operationReading := FiniteModel.operationReading

/-- Source core whose three selected atoms force a collision under any exact map to the target. -/
noncomputable def positiveSourceCore :
    AATCorePackage FiniteModel.carrier :=
  AATCorePackage.generate FiniteModel.axiomSystem positiveSourceCoreReading

/-- Target core whose second selected atom is moved to the common image by the base operation. -/
noncomputable def positiveTargetCore :
    AATCorePackage FiniteModel.carrier :=
  AATCorePackage.generate FiniteModel.axiomSystem positiveTargetCoreReading

private theorem positiveSourceCore_family_mem_iff
    (atom : FiniteModel.carrier.Atom) :
    positiveSourceCore.family.mem atom ↔ positiveSourceAllows atom := by
  rw [positiveSourceCore.family_mem_iff_extracts]
  change (True ∧ positiveSourceAllows atom ∧ True ∧ True) ↔ _
  simp

private theorem positiveTargetCore_family_mem_iff
    (atom : FiniteModel.carrier.Atom) :
    positiveTargetCore.family.mem atom ↔ positiveTargetAllows atom := by
  rw [positiveTargetCore.family_mem_iff_extracts]
  change (True ∧ positiveTargetAllows atom ∧ True ∧ True) ↔ _
  simp

private def positiveAtomMap (_ : FiniteModel.carrier.Atom) :
    FiniteModel.carrier.Atom :=
  FiniteModel.FiniteAtom.componentC

private def positiveQueryMap :
    CircuitQuery FiniteModel.carrier → CircuitQuery FiniteModel.carrier
  | .atomPresent _ => .atomPresent FiniteModel.FiniteAtom.componentC
  | .relationPresent _ _ =>
      .relationPresent FiniteModel.FiniteAtom.componentC
        FiniteModel.FiniteAtom.componentC
  | .identificationPresent _ _ =>
      .identificationPresent FiniteModel.FiniteAtom.componentC
        FiniteModel.FiniteAtom.componentC

private def positiveCircuitMap
    (datum : FiniteCircuitDatum FiniteModel.carrier) :
    FiniteCircuitDatum FiniteModel.carrier where
  queries := datum.queries.map fun pair => (positiveQueryMap pair.1, pair.2)

private def positiveObjectMap
    (A : ArchitectureObject FiniteModel.carrier) :
    ArchitectureObject FiniteModel.carrier :=
  FiniteModel.objectOfConfiguration (A.configuration.transport positiveAtomMap)

private def positiveCompositionMap
    (family : AtomFamily FiniteModel.carrier) (hfinite : family.ListFinite) :
    ConfigurationHom
      (positiveSourceCore.reading.composition.compose family hfinite)
      (positiveTargetCore.reading.composition.compose
        (family.transport positiveAtomMap) (hfinite.transport positiveAtomMap)) where
  atomMap := positiveAtomMap
  maps_family h := ⟨_, h, rfl⟩
  maps_relation h := False.elim h
  maps_identification h := False.elim h

private def positiveTransportOperation
    {A B : ArchitectureObject FiniteModel.carrier}
    (op : FiniteModel.operationReading.Op A B) :
    FiniteModel.operationReading.Op (positiveObjectMap A) (positiveObjectMap B) where
  atomMap := id
  maps_family := by
    rintro target ⟨source, hsource, hmap⟩
    exact ⟨op.atomMap source, op.maps_family hsource, by
      simpa [positiveAtomMap] using hmap⟩
  maps_relation := by
    rintro target₁ target₂ ⟨source₁, source₂, hsource, hmap₁, hmap₂⟩
    exact ⟨op.atomMap source₁, op.atomMap source₂,
      op.maps_relation hsource,
      by simpa [positiveAtomMap] using hmap₁,
      by simpa [positiveAtomMap] using hmap₂⟩
  maps_identification := by
    rintro target₁ target₂ ⟨source₁, source₂, hsource, hmap₁, hmap₂⟩
    exact ⟨op.atomMap source₁, op.atomMap source₂,
      op.maps_identification hsource,
      by simpa [positiveAtomMap] using hmap₁,
      by simpa [positiveAtomMap] using hmap₂⟩

private theorem positiveTransport_subset_target :
    (positiveSourceCore.family.transport positiveAtomMap).Subset
      positiveTargetCore.family := by
  rintro atom ⟨source, hsource, rfl⟩
  exact (positiveTargetCore_family_mem_iff _).mpr (Or.inl rfl)

/-- The concrete selected operation used by the positive base-reachability firing. -/
private def positiveBaseOperation :
    FiniteModel.operationReading.Op
      positiveTargetCore.object
      (positiveObjectMap positiveSourceCore.object) where
  atomMap := positiveAtomMap
  maps_family := by
    intro atom h
    exact ⟨FiniteModel.FiniteAtom.componentA, by
      rw [positiveSourceCore.object_configuration_eq,
        positiveSourceCore.configuration_family_eq]
      exact (positiveSourceCore_family_mem_iff _).mpr (Or.inl rfl), rfl⟩
  maps_relation := by
    intro atom₁ atom₂ h
    rw [positiveTargetCore.object_configuration_eq] at h
    change False at h
    exact False.elim h
  maps_identification := by
    intro atom₁ atom₂ h
    rw [positiveTargetCore.object_configuration_eq] at h
    change False at h
    exact False.elim h

private theorem positiveBaseOperation_moves_selected_atom :
    positiveTargetCore.family.mem FiniteModel.FiniteAtom.dependsBC ∧
      positiveBaseOperation.atomMap FiniteModel.FiniteAtom.dependsBC ≠
        FiniteModel.FiniteAtom.dependsBC := by
  constructor
  · exact (positiveTargetCore_family_mem_iff _).mpr (Or.inr rfl)
  · simp [positiveBaseOperation, positiveAtomMap]

private theorem positiveCircuitMap_positive
    (datum : FiniteCircuitDatum FiniteModel.carrier)
    (hpositive : datum.Positive) :
    (positiveCircuitMap datum).Positive := by
  intro query expected hmem
  rcases List.mem_map.mp hmem with ⟨pair, hpair, hp⟩
  cases hp
  exact hpositive pair.1 pair.2 hpair

private theorem positiveCircuitMap_matches
    (datum : FiniteCircuitDatum FiniteModel.carrier)
    (A : ArchitectureObject FiniteModel.carrier)
    (hpositive : datum.Positive)
    (hmatches : datum.Matches A) :
    (positiveCircuitMap datum).Matches (positiveObjectMap A) := by
  intro query expected hmem
  rcases List.mem_map.mp hmem with ⟨pair, hpair, hp⟩
  cases hp
  rcases pair with ⟨sourceQuery, sourceExpected⟩
  have hexpected : sourceExpected = true :=
    hpositive sourceQuery sourceExpected hpair
  subst sourceExpected
  constructor
  · intro _
    rfl
  · intro _
    have hholds : sourceQuery.Holds A :=
      (hmatches sourceQuery true hpair).mpr rfl
    cases sourceQuery with
    | atomPresent atom =>
        exact ⟨atom, hholds, rfl⟩
    | relationPresent atom₁ atom₂ =>
        exact ⟨⟨atom₁, hholds.1, rfl⟩,
          ⟨⟨atom₂, hholds.2.1, rfl⟩,
            ⟨atom₁, atom₂, hholds.2.2, rfl, rfl⟩⟩⟩
    | identificationPresent atom₁ atom₂ =>
        exact ⟨⟨atom₁, hholds.1, rfl⟩,
          ⟨⟨atom₂, hholds.2.1, rfl⟩,
            ⟨atom₁, atom₂, hholds.2.2, rfl, rfl⟩⟩⟩

/-- Positive-only core reading change that collapses the selected source atoms. -/
noncomputable def positiveCoreChange :
    PositiveCoreReadingHom positiveSourceCore positiveTargetCore where
  atomMap := positiveAtomMap
  extraction_mono := by
    exact positiveTransport_subset_target
  compositionMap := positiveCompositionMap
  compositionMap_atomMap := by intros; rfl
  objectMap := positiveObjectMap
  object_formation_eq := by intros; rfl
  base_reachable := by
    exact OperationReading.Reachable.step
      OperationReading.Reachable.base positiveBaseOperation
  configurationMap A := AtomConfiguration.transportHom positiveAtomMap A.configuration
  configurationMap_atomMap := by intros; rfl
  operationMap := positiveTransportOperation
  operation_naturality := by
    intro A B op
    apply ConfigurationHom.ext
    funext atom
    rfl
  equationMap := id
  queryMap := positiveCircuitMap
  positive_preserved := positiveCircuitMap_positive
  matches_of_positive := positiveCircuitMap_matches
  accepts_mono := by
    intro i datum hpositive haccepts
    cases i
    have hsource : positiveSourceDatum = datum :=
      (CircuitDetectorCode.eval_exact_eq_true_iff positiveSourceDatum datum).mp haccepts
    subst datum
    change (CircuitDetectorCode.exact positiveTargetDatum).eval
      (positiveCircuitMap positiveSourceDatum) = true
    apply (CircuitDetectorCode.eval_exact_eq_true_iff _ _).mpr
    rfl

/-- Selected equation of the positive finite model. -/
noncomputable def positiveEquationIndex :
    positiveSourceCore.algebra.equationSystem.Index :=
  PUnit.unit

/-- Distinguished positive atom-presence query. -/
noncomputable def positiveQuery : CircuitQuery FiniteModel.carrier :=
  .atomPresent FiniteModel.FiniteAtom.componentA

/-- Positive circuit accepted at the selected source base object. -/
noncomputable def positiveCircuit :
    PositiveCircuitDatum positiveSourceCore
      positiveSourceCore.baseObject positiveEquationIndex := by
  refine ⟨positiveSourceDatum, ?_, ?_, ?_⟩
  · exact FiniteCircuitDatum.positive_singleton positiveQuery
  · intro query expected hmem
    simp only [positiveSourceDatum, List.mem_singleton] at hmem
    cases hmem
    constructor
    · intro _
      rfl
    · intro _
      change positiveSourceCore.object.configuration.family.mem
        FiniteModel.FiniteAtom.componentA
      rw [positiveSourceCore.object_configuration_eq,
        positiveSourceCore.configuration_family_eq]
      exact (positiveSourceCore_family_mem_iff _).mpr (Or.inl rfl)
  · exact (CircuitDetectorCode.eval_exact_eq_true_iff _ _).mpr rfl

/-- The selected positive query occurs in the positive circuit. -/
theorem positiveQuery_mem :
    (positiveQuery, true) ∈ positiveCircuit.1.queries := by
  simp [positiveCircuit, positiveQuery, positiveSourceDatum]

/-- The selected positive circuit has at least one query. -/
theorem positiveCircuit_queries_nonempty :
    positiveCircuit.1.queries ≠ [] :=
  List.ne_nil_of_mem positiveQuery_mem

/-- Transported positive circuit at the mapped base object and equation. -/
def positiveCircuit_transport :
    PositiveCircuitDatum positiveTargetCore
      (positiveCoreChange.objMap positiveSourceCore.baseObject)
      (positiveCoreChange.equationMap positiveEquationIndex) :=
  positiveCoreChange.mapPositiveCircuit positiveCircuit

/-- The mapped source base is reachable from the selected target base. -/
theorem positiveBase_target_reachable :
    positiveTargetCore.reading.operationReading.Reachable
      positiveTargetCore.object
      (positiveCoreChange.objectMap positiveSourceCore.object) :=
  positiveCoreChange.base_reachable

private def positiveSingletonConfiguration
    (atom : FiniteModel.carrier.Atom) : AtomConfiguration FiniteModel.carrier where
  family := { mem := fun actual => actual = atom }
  relation _ _ := False
  identification _ _ := False

private def positiveSingletonObject
    (atom : FiniteModel.carrier.Atom) : ArchitectureObject FiniteModel.carrier :=
  FiniteModel.objectOfConfiguration (positiveSingletonConfiguration atom)

/-- Signed negative query that distinguishes the two collapsed source atoms. -/
noncomputable def negativeCircuit : FiniteCircuitDatum FiniteModel.carrier where
  queries := [(.atomPresent FiniteModel.FiniteAtom.componentB, false)]

/-- The signed negative query is not a positive circuit datum. -/
theorem negativeCircuit_not_positive : ¬ negativeCircuit.Positive :=
  FiniteCircuitDatum.not_positive_singleton_false _

private theorem negativeCircuit_matches_componentA :
    negativeCircuit.Matches
      (positiveSingletonObject FiniteModel.FiniteAtom.componentA) := by
  intro query expected hmem
  simp only [negativeCircuit, List.mem_singleton] at hmem
  cases hmem
  constructor
  · intro h
    change FiniteModel.FiniteAtom.componentB =
      FiniteModel.FiniteAtom.componentA at h
    exact FiniteModel.FiniteAtom.noConfusion h
  · intro h
    exact Bool.noConfusion h

private theorem negativeCircuit_not_matches_componentB :
    ¬ negativeCircuit.Matches
      (positiveSingletonObject FiniteModel.FiniteAtom.componentB) := by
  intro hmatches
  have h := (hmatches (.atomPresent FiniteModel.FiniteAtom.componentB) false
    (by simp [negativeCircuit])).mp
      (show (CircuitQuery.atomPresent FiniteModel.FiniteAtom.componentB).Holds
        (positiveSingletonObject FiniteModel.FiniteAtom.componentB) by
          change FiniteModel.FiniteAtom.componentB =
            FiniteModel.FiniteAtom.componentB
          rfl)
  exact Bool.noConfusion h

private theorem positiveObjectMap_singletons_eq :
    positiveObjectMap
        (positiveSingletonObject FiniteModel.FiniteAtom.componentA) =
      positiveObjectMap
        (positiveSingletonObject FiniteModel.FiniteAtom.componentB) := by
  apply congrArg FiniteModel.objectOfConfiguration
  apply AtomConfiguration.ext
  · ext atom
    constructor <;> rintro ⟨source, hsource, rfl⟩
    · exact ⟨FiniteModel.FiniteAtom.componentB, rfl, rfl⟩
    · exact ⟨FiniteModel.FiniteAtom.componentA, rfl, rfl⟩
  · intro a b
    constructor <;> rintro ⟨source₁, source₂, h, _, _⟩ <;> exact False.elim h
  · intro a b
    constructor <;> rintro ⟨source₁, source₂, h, _, _⟩ <;> exact False.elim h

/-- No signed query can reflect the collapsed negative query along the positive map. -/
theorem negativeCircuit_not_transportable :
    ¬ ∃ target : FiniteCircuitDatum FiniteModel.carrier,
      ∀ A,
        negativeCircuit.Matches A ↔
          target.Matches (positiveCoreChange.objectMap A) := by
  rintro ⟨target, htarget⟩
  have hA := (htarget
    (positiveSingletonObject FiniteModel.FiniteAtom.componentA)).mp
      negativeCircuit_matches_componentA
  change target.Matches
    (positiveObjectMap
      (positiveSingletonObject FiniteModel.FiniteAtom.componentA)) at hA
  rw [positiveObjectMap_singletons_eq] at hA
  exact negativeCircuit_not_matches_componentB
    ((htarget (positiveSingletonObject FiniteModel.FiniteAtom.componentB)).mpr
      (by simpa [positiveCoreChange] using hA))

private def negativeAtomCircuit
    (atom : FiniteModel.carrier.Atom) : FiniteCircuitDatum FiniteModel.carrier where
  queries := [(.atomPresent atom, false)]

private theorem negativeAtomCircuit_matches_of_ne
    {forbidden present : FiniteModel.carrier.Atom}
    (hne : forbidden ≠ present) :
    (negativeAtomCircuit forbidden).Matches (positiveSingletonObject present) := by
  intro query expected hmem
  simp only [negativeAtomCircuit, List.mem_singleton] at hmem
  cases hmem
  constructor
  · intro hholds
    change forbidden = present at hholds
    exact False.elim (hne hholds)
  · intro h
    exact Bool.noConfusion h

private theorem negativeAtomCircuit_not_matches_self
    (atom : FiniteModel.carrier.Atom) :
    ¬ (negativeAtomCircuit atom).Matches (positiveSingletonObject atom) := by
  intro hmatches
  have h := (hmatches (.atomPresent atom) false
    (by simp [negativeAtomCircuit])).mp
      (show (CircuitQuery.atomPresent atom).Holds
        (positiveSingletonObject atom) by
          change atom = atom
          rfl)
  exact Bool.noConfusion h

private theorem signedExact_objectMap_singletons_eq
    (f : SignedExactCoreReadingHom positiveSourceCore positiveTargetCore)
    {a b : FiniteModel.carrier.Atom}
    (hab : f.atomMap a = f.atomMap b) :
    f.objectMap (positiveSingletonObject a) =
      f.objectMap (positiveSingletonObject b) := by
  change f.objectMap
      (positiveSourceCore.reading.objectReading.object
        (positiveSingletonConfiguration a)) =
    f.objectMap
      (positiveSourceCore.reading.objectReading.object
        (positiveSingletonConfiguration b))
  rw [f.object_formation_eq, f.object_formation_eq]
  apply congrArg FiniteModel.objectOfConfiguration
  apply AtomConfiguration.ext
  · ext atom
    constructor
    · rintro ⟨source, hsource, rfl⟩
      change source = a at hsource
      subst source
      exact ⟨b, rfl, hab.symm⟩
    · rintro ⟨source, hsource, rfl⟩
      change source = b at hsource
      subst source
      exact ⟨a, rfl, hab⟩
  · intro atom₁ atom₂
    constructor <;> rintro ⟨source₁, source₂, hsource, _, _⟩ <;>
      exact False.elim hsource
  · intro atom₁ atom₂
    constructor <;> rintro ⟨source₁, source₂, hsource, _, _⟩ <;>
      exact False.elim hsource

private theorem signedExact_atomMap_injective
    (f : SignedExactCoreReadingHom positiveSourceCore positiveTargetCore) :
    Function.Injective f.atomMap := by
  intro a b hab
  by_contra hne
  have hsource :
      (negativeAtomCircuit b).Matches (positiveSingletonObject a) :=
    negativeAtomCircuit_matches_of_ne (Ne.symm hne)
  have htarget :=
    (f.matches_iff (negativeAtomCircuit b) (positiveSingletonObject a)).mp hsource
  rw [signedExact_objectMap_singletons_eq f hab] at htarget
  exact negativeAtomCircuit_not_matches_self b
    ((f.matches_iff (negativeAtomCircuit b) (positiveSingletonObject b)).mpr htarget)

private theorem positiveTargetFamily_not_exactTransport
    (f : SignedExactCoreReadingHom positiveSourceCore positiveTargetCore) : False := by
  have hA_source : positiveSourceCore.family.mem FiniteModel.FiniteAtom.componentA :=
    (positiveSourceCore_family_mem_iff _).mpr (Or.inl rfl)
  have hB_source : positiveSourceCore.family.mem FiniteModel.FiniteAtom.componentB :=
    (positiveSourceCore_family_mem_iff _).mpr (Or.inr (Or.inl rfl))
  have hAB_source : positiveSourceCore.family.mem FiniteModel.FiniteAtom.dependsAB :=
    (positiveSourceCore_family_mem_iff _).mpr (Or.inr (Or.inr rfl))
  have hA_target : positiveTargetCore.family.mem
      (f.atomMap FiniteModel.FiniteAtom.componentA) := by
    rw [f.extraction_eq]
    exact ⟨FiniteModel.FiniteAtom.componentA, hA_source, rfl⟩
  have hB_target : positiveTargetCore.family.mem
      (f.atomMap FiniteModel.FiniteAtom.componentB) := by
    rw [f.extraction_eq]
    exact ⟨FiniteModel.FiniteAtom.componentB, hB_source, rfl⟩
  have hAB_target : positiveTargetCore.family.mem
      (f.atomMap FiniteModel.FiniteAtom.dependsAB) := by
    rw [f.extraction_eq]
    exact ⟨FiniteModel.FiniteAtom.dependsAB, hAB_source, rfl⟩
  have hA := (positiveTargetCore_family_mem_iff _).mp hA_target
  have hB := (positiveTargetCore_family_mem_iff _).mp hB_target
  have hAB := (positiveTargetCore_family_mem_iff _).mp hAB_target
  have hinjective := signedExact_atomMap_injective f
  rcases hA with hA | hA <;> rcases hB with hB | hB <;>
    rcases hAB with hAB | hAB
  · exact FiniteModel.FiniteAtom.noConfusion
      (hinjective (hA.trans hB.symm))
  · exact FiniteModel.FiniteAtom.noConfusion
      (hinjective (hA.trans hB.symm))
  · exact FiniteModel.FiniteAtom.noConfusion
      (hinjective (hA.trans hAB.symm))
  · exact FiniteModel.FiniteAtom.noConfusion
      (hinjective (hB.trans hAB.symm))
  · exact FiniteModel.FiniteAtom.noConfusion
      (hinjective (hB.trans hAB.symm))
  · exact FiniteModel.FiniteAtom.noConfusion
      (hinjective (hA.trans hAB.symm))
  · exact FiniteModel.FiniteAtom.noConfusion
      (hinjective (hA.trans hB.symm))
  · exact FiniteModel.FiniteAtom.noConfusion
      (hinjective (hA.trans hB.symm))

/-- The positive-only reading change cannot be strengthened to signed exactness. -/
theorem positiveOnly_not_signedExact :
    ¬ Nonempty
      (SignedExactCoreReadingHom positiveSourceCore positiveTargetCore) := by
  rintro ⟨f⟩
  exact positiveTargetFamily_not_exactTransport f

/-! ## R9b: nonidentity exact core reading change -/

private def exactAtomMap : FiniteModel.carrier.Atom → FiniteModel.carrier.Atom
  | .componentA => .componentB
  | .componentB => .componentA
  | atom => atom

@[simp] private theorem exactAtomMap_involutive
    (atom : FiniteModel.carrier.Atom) :
    exactAtomMap (exactAtomMap atom) = atom := by
  cases atom <;> rfl

private theorem exactAtomMap_injective : Function.Injective exactAtomMap :=
  Function.LeftInverse.injective exactAtomMap_involutive

private def exactAtomEquiv :
    FiniteModel.carrier.Atom ≃ FiniteModel.carrier.Atom where
  toFun := exactAtomMap
  invFun := exactAtomMap
  left_inv := exactAtomMap_involutive
  right_inv := exactAtomMap_involutive

private def exactExtractionDoctrine : ExtractionDoctrine FiniteModel.carrier where
  Source := PUnit
  Vocabulary := PUnit
  SemanticReading := PUnit
  Resolution := PUnit
  vocabulary := PUnit.unit
  semanticReading := PUnit.unit
  resolution := PUnit.unit
  vocabularyAllows := fun _ _ => True
  semanticAllows := fun _ _ _ => True
  resolutionAllows := fun _ _ _ => True
  sourceSemantics := fun _ _ => True
  normalize := id

private def exactCompositionReading : CompositionReading FiniteModel.carrier where
  compose family _ := {
    family := family
    relation := fun _ _ => False
    identification := fun _ _ => False
  }
  family_eq := by intros; rfl
  family_supported := by
    intro family hfinite
    exact ⟨fun h => False.elim h, fun h => False.elim h⟩

private def exactCircuitDatum : FiniteCircuitDatum FiniteModel.carrier where
  queries := [(.atomPresent FiniteModel.FiniteAtom.componentC, true)]

private def exactRoleWeight : EquationRole → Int
  | .required => 1
  | .optional => 2
  | .derived => 3

/--
Three-role equation system whose residual records actual Atom membership in
the selected architecture object.
-/
private noncomputable def exactEquationSystem
    (A : ArchitectureObject FiniteModel.carrier) :
    ArchitecturalEquationSystem (Site.contextMorphismPreorderCategory A) := by
  classical
  exact {
    Index := EquationRole
    role := id
    Observable := fun _ => Int
    observableCommRing := fun _ => inferInstance
    restrict := fun _ => RingHom.id Int
    restrict_id := by intros; rfl
    restrict_comp := by intros; rfl
    violationCoordinate := fun _ role _ => exactRoleWeight role
    violationCoordinate_restrict := by intros; rfl
    equationResidual := fun _ object role atom =>
      if object.configuration.family.mem atom then exactRoleWeight role else 0
    equationResidual_restrict := by intros; rfl
  }

/--
Exact detector reading for the role-complete, object-dependent equation
fixture.
-/
private noncomputable def exactEquationReading
    (A : ArchitectureObject FiniteModel.carrier) :
    EquationReading A where
  contextPreorder := Site.contextMorphismPreorderCategory A
  equationSystem := exactEquationSystem A
  circuits := {
    code := fun _ => .exact exactCircuitDatum
  }
  circuitSound := by
    classical
    intro index object datum hmatches haccepts hequation
    have hdatum : exactCircuitDatum = datum :=
      (CircuitDetectorCode.eval_exact_eq_true_iff
        exactCircuitDatum datum).mp haccepts
    subst datum
    have hpresent :
        object.configuration.family.mem FiniteModel.FiniteAtom.componentC := by
      exact (hmatches
        (.atomPresent FiniteModel.FiniteAtom.componentC) true
        (by simp [exactCircuitDatum])).mpr rfl
    have hcoordinate := hequation
      (Site.ContextCategoryObject.of
        (Site.contextMorphismPreorderCategory A) (emptyEquationContext A))
      FiniteModel.FiniteAtom.componentC
    change
      (if object.configuration.family.mem FiniteModel.FiniteAtom.componentC
        then exactRoleWeight index else 0) = 0 at hcoordinate
    rw [if_pos hpresent] at hcoordinate
    cases index <;> norm_num [exactRoleWeight] at hcoordinate

private def exactInvariantFamily : InvariantFamily FiniteModel.carrier where
  Index := Bool
  invariant
    | false => .function { Value := PUnit, evaluate := fun _ => PUnit.unit }
    | true => .predicate { holds := fun _ => True }

private def exactSignature : ArchitectureSignature FiniteModel.carrier where
  Axis := PUnit
  Coordinate _ := Nat
  selected _ := True
  coordinate _ _ := 0

private noncomputable def exactCoreReading : CoreReading FiniteModel.carrier where
  doctrine := exactExtractionDoctrine
  source := PUnit.unit
  family_listFinite := ⟨FiniteModel.FiniteAtom.all,
    fun atom _ => FiniteModel.FiniteAtom.mem_all atom⟩
  composition := exactCompositionReading
  objectReading := FiniteModel.objectReading
  equationReading := exactEquationReading _
  invariantReading := exactInvariantFamily
  signatureReading := exactSignature
  operationReading := FiniteModel.operationReading

/-- Source core for the nonidentity exact finite reading change. -/
noncomputable def exactSourceCore : AATCorePackage FiniteModel.carrier :=
  AATCorePackage.generate FiniteModel.axiomSystem exactCoreReading

/-- Target core for the nonidentity exact finite reading change. -/
noncomputable def exactTargetCore : AATCorePackage FiniteModel.carrier :=
  AATCorePackage.generate FiniteModel.axiomSystem exactCoreReading

private theorem exactSourceCore_family_mem
    (atom : FiniteModel.carrier.Atom) : exactSourceCore.family.mem atom := by
  rw [exactSourceCore.family_mem_iff_extracts]
  exact ⟨trivial, trivial, trivial, trivial⟩

private theorem exactTargetCore_family_mem
    (atom : FiniteModel.carrier.Atom) : exactTargetCore.family.mem atom := by
  rw [exactTargetCore.family_mem_iff_extracts]
  exact ⟨trivial, trivial, trivial, trivial⟩

private theorem exactFamily_transport :
    exactTargetCore.family = exactSourceCore.family.transport exactAtomMap := by
  ext atom
  constructor
  · intro _
    exact ⟨exactAtomMap atom, exactSourceCore_family_mem _, by simp⟩
  · intro _
    exact exactTargetCore_family_mem atom

private def exactObjectMap (A : ArchitectureObject FiniteModel.carrier) :
    ArchitectureObject FiniteModel.carrier :=
  FiniteModel.objectOfConfiguration (A.configuration.transport exactAtomMap)

private def exactQueryMap :
    CircuitQuery FiniteModel.carrier → CircuitQuery FiniteModel.carrier
  | .atomPresent atom => .atomPresent (exactAtomMap atom)
  | .relationPresent atom₁ atom₂ =>
      .relationPresent (exactAtomMap atom₁) (exactAtomMap atom₂)
  | .identificationPresent atom₁ atom₂ =>
      .identificationPresent (exactAtomMap atom₁) (exactAtomMap atom₂)

@[simp] private theorem exactQueryMap_involutive
    (query : CircuitQuery FiniteModel.carrier) :
    exactQueryMap (exactQueryMap query) = query := by
  cases query <;> simp [exactQueryMap]

private def exactDatumMap (datum : FiniteCircuitDatum FiniteModel.carrier) :
    FiniteCircuitDatum FiniteModel.carrier where
  queries := datum.queries.map fun pair => (exactQueryMap pair.1, pair.2)

@[simp] private theorem exactDatumMap_involutive
    (datum : FiniteCircuitDatum FiniteModel.carrier) :
    exactDatumMap (exactDatumMap datum) = datum := by
  cases datum with
  | mk queries =>
      simp [exactDatumMap, Function.comp_def]

private theorem exactDatumMap_injective : Function.Injective exactDatumMap :=
  Function.LeftInverse.injective exactDatumMap_involutive

@[simp] private theorem exactDatumMap_exactCircuitDatum :
    exactDatumMap exactCircuitDatum = exactCircuitDatum := by
  rfl

private theorem exactQueryMap_holds_iff
    (query : CircuitQuery FiniteModel.carrier)
    (A : ArchitectureObject FiniteModel.carrier) :
    (exactQueryMap query).Holds (exactObjectMap A) ↔ query.Holds A := by
  cases query with
  | atomPresent atom =>
      constructor
      · rintro ⟨source, hsource, heq⟩
        have hsource_eq : source = atom := exactAtomMap_injective heq
        subst source
        exact hsource
      · intro h
        exact ⟨atom, h, rfl⟩
  | relationPresent atom₁ atom₂ =>
      constructor
      · rintro ⟨⟨source₁, hsource₁, heq₁⟩,
          ⟨⟨source₂, hsource₂, heq₂⟩,
            ⟨relationSource₁, relationSource₂, hrelation,
              hrelation₁, hrelation₂⟩⟩⟩
        have hs₁ : source₁ = atom₁ := exactAtomMap_injective heq₁
        have hs₂ : source₂ = atom₂ := exactAtomMap_injective heq₂
        have hr₁ : relationSource₁ = atom₁ := exactAtomMap_injective hrelation₁
        have hr₂ : relationSource₂ = atom₂ := exactAtomMap_injective hrelation₂
        subst source₁
        subst source₂
        subst relationSource₁
        subst relationSource₂
        exact ⟨hsource₁, hsource₂, hrelation⟩
      · rintro ⟨h₁, h₂, hrelation⟩
        exact ⟨⟨atom₁, h₁, rfl⟩, ⟨⟨atom₂, h₂, rfl⟩,
          ⟨atom₁, atom₂, hrelation, rfl, rfl⟩⟩⟩
  | identificationPresent atom₁ atom₂ =>
      constructor
      · rintro ⟨⟨source₁, hsource₁, heq₁⟩,
          ⟨⟨source₂, hsource₂, heq₂⟩,
            ⟨identificationSource₁, identificationSource₂, hidentification,
              hidentification₁, hidentification₂⟩⟩⟩
        have hs₁ : source₁ = atom₁ := exactAtomMap_injective heq₁
        have hs₂ : source₂ = atom₂ := exactAtomMap_injective heq₂
        have hi₁ : identificationSource₁ = atom₁ :=
          exactAtomMap_injective hidentification₁
        have hi₂ : identificationSource₂ = atom₂ :=
          exactAtomMap_injective hidentification₂
        subst source₁
        subst source₂
        subst identificationSource₁
        subst identificationSource₂
        exact ⟨hsource₁, hsource₂, hidentification⟩
      · rintro ⟨h₁, h₂, hidentification⟩
        exact ⟨⟨atom₁, h₁, rfl⟩, ⟨⟨atom₂, h₂, rfl⟩,
          ⟨atom₁, atom₂, hidentification, rfl, rfl⟩⟩⟩

private theorem exactDatumMap_matches_iff
    (datum : FiniteCircuitDatum FiniteModel.carrier)
    (A : ArchitectureObject FiniteModel.carrier) :
    datum.Matches A ↔ (exactDatumMap datum).Matches (exactObjectMap A) := by
  constructor
  · intro hmatches query expected hmem
    rcases List.mem_map.mp hmem with ⟨pair, hpair, hp⟩
    cases hp
    exact (exactQueryMap_holds_iff pair.1 A).trans
      (hmatches pair.1 pair.2 hpair)
  · intro hmatches query expected hmem
    have hmapped := hmatches (exactQueryMap query) expected
      (List.mem_map.mpr ⟨(query, expected), hmem, rfl⟩)
    exact (exactQueryMap_holds_iff query A).symm.trans hmapped

private theorem exactDatumMap_accepts_iff
    (datum : FiniteCircuitDatum FiniteModel.carrier) :
    (CircuitDetectorCode.exact exactCircuitDatum).eval datum = true ↔
    (CircuitDetectorCode.exact exactCircuitDatum).eval
      (exactDatumMap datum) = true := by
  rw [CircuitDetectorCode.eval_exact_eq_true_iff,
    CircuitDetectorCode.eval_exact_eq_true_iff]
  constructor
  · intro h
    subst datum
    rfl
  · intro h
    exact exactDatumMap_injective (by simpa using h)

private theorem exactDatumMap_eq_transport
    (datum : FiniteCircuitDatum FiniteModel.carrier) :
    exactDatumMap datum = datum.transport exactAtomEquiv := by
  have hquery :
      exactQueryMap =
        fun query => query.transport exactAtomEquiv := by
    funext query
    cases query <;> rfl
  cases datum
  simp [exactDatumMap, FiniteCircuitDatum.transport, hquery]

private theorem exactComposition_eq
    (family : AtomFamily FiniteModel.carrier) (hfinite : family.ListFinite) :
    exactTargetCore.reading.composition.compose
        (family.transport exactAtomMap) (hfinite.transport exactAtomMap) =
      (exactSourceCore.reading.composition.compose family hfinite).transport
        exactAtomMap := by
  apply AtomConfiguration.ext
  · rfl
  · intro atom₁ atom₂
    constructor
    · intro h
      exact False.elim h
    · rintro ⟨source₁, source₂, h, _, _⟩
      exact False.elim h
  · intro atom₁ atom₂
    constructor
    · intro h
      exact False.elim h
    · rintro ⟨source₁, source₂, h, _, _⟩
      exact False.elim h

private def exactOperationMap
    {A B : ArchitectureObject FiniteModel.carrier}
    (op : FiniteModel.operationReading.Op A B) :
    FiniteModel.operationReading.Op (exactObjectMap A) (exactObjectMap B) where
  atomMap atom := exactAtomMap (op.atomMap (exactAtomMap atom))
  maps_family := by
    rintro target ⟨source, hsource, rfl⟩
    exact ⟨op.atomMap source, op.maps_family hsource, by simp⟩
  maps_relation := by
    rintro target₁ target₂ ⟨source₁, source₂, hsource, rfl, rfl⟩
    exact ⟨op.atomMap source₁, op.atomMap source₂,
      op.maps_relation hsource, by simp, by simp⟩
  maps_identification := by
    rintro target₁ target₂ ⟨source₁, source₂, hsource, rfl, rfl⟩
    exact ⟨op.atomMap source₁, op.atomMap source₂,
      op.maps_identification hsource, by simp, by simp⟩

/-- Exact finite core change induced by the component-A/component-B involution. -/
noncomputable def nonidentityExactCoreChange :
    SignedExactCoreReadingHom exactSourceCore exactTargetCore where
  atomEquiv := exactAtomEquiv
  extraction_eq := by
    simpa [exactAtomEquiv] using exactFamily_transport
  composition_eq := by
    intro family hfinite
    simpa [exactAtomEquiv] using exactComposition_eq family hfinite
  objectMap := exactObjectMap
  object_formation_eq := by intros; rfl
  configurationMap A :=
    AtomConfiguration.transportHom exactAtomEquiv A.configuration
  configurationMap_atomMap := by intros; rfl
  configuration_eq := by intros; rfl
  equationTransport := {
    contextEquivalence := CategoryTheory.Equivalence.refl
    equationEquiv := Equiv.refl EquationRole
    role_eq := by intro i; rfl
    observableEquiv := fun _ => RingEquiv.refl Int
    observable_naturality := by intros; rfl
    violationCoordinate_eq := by intros; rfl
    equationResidual_eq := by
      classical
      intro W A role atom
      have hmem :
          (exactObjectMap A).configuration.family.mem
              (exactAtomEquiv atom) ↔
            A.configuration.family.mem atom := by
        simpa [exactAtomEquiv] using
          exactQueryMap_holds_iff (.atomPresent atom) A
      change
        (if A.configuration.family.mem atom
          then exactRoleWeight role else 0) =
        (if (exactObjectMap A).configuration.family.mem (exactAtomEquiv atom)
          then exactRoleWeight role else 0)
      by_cases h : A.configuration.family.mem atom
      · rw [if_pos h, if_pos (hmem.mpr h)]
      · rw [if_neg h, if_neg (fun htarget => h (hmem.mp htarget))]
  }
  detectorCode_eq := by
    intro i
    cases i <;>
      change
        CircuitDetectorCode.exact exactCircuitDatum =
          CircuitDetectorCode.exact
            (exactCircuitDatum.transport exactAtomEquiv) <;>
      rw [← exactDatumMap_eq_transport, exactDatumMap_exactCircuitDatum]
  operationMap := exactOperationMap
  operation_naturality := by
    intro A B op
    apply ConfigurationHom.ext
    funext atom
    change exactAtomMap (op.atomMap (exactAtomMap (exactAtomMap atom))) =
      exactAtomMap (op.atomMap atom)
    rw [exactAtomMap_involutive]
  invariantMap := id
  invariant_transport := by
    intro i
    cases i
    · exact ⟨Equiv.refl PUnit, fun _ => rfl⟩
    · exact fun _ => Iff.rfl
  axisMap := id
  coordinateEquiv := fun _ => Equiv.refl Nat
  axis_selected_iff := by intro i; cases i; rfl
  coordinate_eq := by intro A i; cases i; rfl

/-- The exact finite core change is nonidentity on primitive atoms. -/
theorem nonidentityExactCoreChange_fires :
    nonidentityExactCoreChange.atomMap ≠ id := by
  intro hidentity
  have h := congrFun hidentity FiniteModel.FiniteAtom.componentA
  change FiniteModel.FiniteAtom.componentB =
    FiniteModel.FiniteAtom.componentA at h
  exact FiniteModel.FiniteAtom.noConfusion h

/-- The exact fixture preserves the optional role rather than swapping it with derived. -/
theorem nonidentityExactCoreChange_optional_role :
    exactTargetCore.algebra.equationSystem.role
        (nonidentityExactCoreChange.equationMap EquationRole.optional) =
      EquationRole.optional :=
  nonidentityExactCoreChange.equationTransport.role_eq EquationRole.optional

/-- The exact fixture preserves the derived role rather than swapping it with optional. -/
theorem nonidentityExactCoreChange_derived_role :
    exactTargetCore.algebra.equationSystem.role
        (nonidentityExactCoreChange.equationMap EquationRole.derived) =
      EquationRole.derived :=
  nonidentityExactCoreChange.equationTransport.role_eq EquationRole.derived

/-! ## R9e: coefficient arithmetic, raw data, and negative primitives -/

/-!
### Implementation notes

The positive coefficient change uses the canonical inclusion
`Int → Polynomial Int`. Polynomial rings are free, hence flat, over their
coefficient ring, while the coefficient of `X` detects failure of surjectivity.
The selected ideal is `(2)`; its properness before and after extension is
detected by the unit criterion for constant polynomials.

The raw fixture reuses the existing typed finite raw presheaf. The negative
raw change preserves its coordinate and restriction data and keeps the same
`Unit` relation index, but replaces every relation polynomial by zero. This
was chosen instead of changing only an index type, so the rejection theorem
detects an actual relation-polynomial difference from canonical base change.
-/

/-- The canonical flat, non-surjective coefficient change from integers to polynomials. -/
noncomputable def intPolynomialFlatChange :
    FlatCoefficientChange Int (Polynomial Int) where
  hom := Polynomial.C
  flat := by
    change (algebraMap Int (Polynomial Int)).Flat
    rw [RingHom.flat_algebraMap_iff]
    exact Module.Flat.of_free

/-- The positive coefficient change uses the canonical constant-polynomial inclusion. -/
@[simp] theorem intPolynomialFlatChange_hom :
    intPolynomialFlatChange.hom = Polynomial.C :=
  rfl

/-- The positive coefficient change is genuinely nonidentity on its target ring. -/
theorem intPolynomialFlatChange_nonidentity :
    ¬ Function.Surjective intPolynomialFlatChange.hom := by
  intro hsurjective
  rcases hsurjective Polynomial.X with ⟨z, hz⟩
  have hcoeff := congrArg (fun p : Polynomial Int => p.coeff 1) hz
  simp only [intPolynomialFlatChange, Polynomial.coeff_C,
    Polynomial.coeff_X] at hcoeff
  norm_num at hcoeff

/-- The selected nonzero proper source ideal `(2)`. -/
noncomputable def properIdeal : Ideal Int :=
  Ideal.span {2}

/-- Characterization of the selected proper source ideal. -/
theorem properIdeal_eq : properIdeal = Ideal.span {2} :=
  rfl

/-- The selected source ideal `(2)` is proper. -/
theorem properIdeal_ne_top : properIdeal ≠ ⊤ := by
  exact Ideal.span_singleton_ne_top (by
    intro hunit
    rcases Int.isUnit_iff.mp hunit with h | h <;> norm_num at h)

/-- Extending `(2)` along the polynomial inclusion remains a proper ideal. -/
theorem properIdeal_baseChange :
    properIdeal.map intPolynomialFlatChange.hom ≠ ⊤ := by
  rw [properIdeal_eq, intPolynomialFlatChange_hom, Ideal.map_span]
  change Ideal.span (Polynomial.C '' {2}) ≠ ⊤
  rw [Set.image_singleton]
  exact Ideal.span_singleton_ne_top (by
    rw [Polynomial.isUnit_C]
    intro hunit
    rcases Int.isUnit_iff.mp hunit with h | h <;> norm_num at h)

/-- The existing finite typed raw restriction system used by coefficient firing. -/
noncomputable def coefficientRaw :
    LawAlgebra.RawAmbientRestrictionSystem finiteSite Int :=
  LawAlgebra.FiniteExamples.RawPresheaf.system

/-- The canonical integer quotient map to `ZMod 2`. -/
noncomputable def intZModTwo : Int →+* ZMod 2 :=
  Int.castRingHom (ZMod 2)

/-- The quotient `Int → ZMod 2` is not flat, detected by its nonzero two-torsion. -/
theorem intZModTwo_not_flat : ¬ intZModTwo.Flat := by
  intro hflat
  letI : Module Int (ZMod 2) := intZModTwo.toAlgebra.toModule
  haveI : Module.Flat Int (ZMod 2) := by
    exact hflat
  have hinjective :=
    Module.Flat.isSMulRegular_of_isRegular (M := ZMod 2)
      (IsRegular.of_ne_zero' (by norm_num : (2 : Int) ≠ 0))
  have hone : (1 : ZMod 2) = 0 := by
    apply hinjective
    change (2 : ZMod 2) = 0
    decide
  norm_num at hone

/-- Internal zero-relation family used by the noncanonical raw-system firing. -/
private noncomputable def brokenRelationFamily (W : finiteSite.category) :
    LawAlgebra.StructuralRelationFamily
      ((coefficientRaw.baseChange intPolynomialFlatChange.hom).coordFamily W)
      (Polynomial Int) where
  Relation := Unit
  polynomial := fun _ => 0

/-- Restriction coherence for zero relations, derived from their generated bottom ideal. -/
private noncomputable def brokenRestrictionStable
    {X Y : finiteSite.category} (f : X ⟶ Y) :
    LawAlgebra.RestrictionStableStructuralRelations
      (brokenRelationFamily X) (brokenRelationFamily Y)
      (finiteSite.contextPreorder.morphism (CategoryTheory.leOfHom f)) where
  restriction :=
    ((coefficientRaw.baseChange intPolynomialFlatChange.hom).restrictionStable f).restriction
  maps_JStruct := by
    intro p hp
    have hJ : (brokenRelationFamily Y).JStruct = ⊥ := by
      rw [LawAlgebra.StructuralRelationFamily.JStruct, Ideal.span_eq_bot]
      rintro _ ⟨relation, rfl⟩
      cases relation
      rfl
    have hp0 : p = 0 := by
      rw [hJ] at hp
      simpa using hp
    subst p
    simp

/-- A coherent raw system whose zero relations do not arise by canonical base change. -/
noncomputable def brokenRelationChange :
    LawAlgebra.RawAmbientRestrictionSystem finiteSite (Polynomial Int) where
  coordFamily :=
    (coefficientRaw.baseChange intPolynomialFlatChange.hom).coordFamily
  relationFamily := brokenRelationFamily
  restrictionStable := brokenRestrictionStable
  identity_polynomialMap :=
    (coefficientRaw.baseChange intPolynomialFlatChange.hom).identity_polynomialMap
  composition_polynomialMap :=
    (coefficientRaw.baseChange intPolynomialFlatChange.hom).composition_polynomialMap

/-- The zero-relation change differs from canonical transport of the selected nonzero relation. -/
theorem brokenRelationChange_not_rawBaseChange :
    brokenRelationChange ≠
      coefficientRaw.baseChange intPolynomialFlatChange.hom := by
  intro h
  let HasNonzeroRelation
      (raw : LawAlgebra.RawAmbientRestrictionSystem
        finiteSite (Polynomial Int)) : Prop :=
    ∃ r : (raw.relationFamily
        LawAlgebra.FiniteExamples.RawPresheaf.left).Relation,
      (raw.relationFamily
        LawAlgebra.FiniteExamples.RawPresheaf.left).polynomial r ≠ 0
  have hproperty : HasNonzeroRelation brokenRelationChange =
      HasNonzeroRelation
        (coefficientRaw.baseChange intPolynomialFlatChange.hom) :=
    congrArg HasNonzeroRelation h
  have hcanonical : HasNonzeroRelation
      (coefficientRaw.baseChange intPolynomialFlatChange.hom) := by
    refine ⟨(), ?_⟩
    change MvPolynomial.map Polynomial.C (MvPolynomial.X () ^ 2 - 1) ≠ 0
    intro hzero
    have heval := congrArg
      (MvPolynomial.eval₂Hom (RingHom.id (Polynomial Int))
        (fun _ : Unit => 0)) hzero
    simp at heval
  have hbroken : HasNonzeroRelation brokenRelationChange := by
    rw [hproperty]
    exact hcanonical
  rcases hbroken with ⟨relation, hrelation⟩
  cases relation
  exact hrelation rfl

/-! ## R9h: finite linear Cech and actual sheaf-cohomology firing -/

/-!
### Implementation notes

The linear firing uses its own three-context presentation.  The base reads the
entire selected object and has no observables, so it is terminal in the actual
context category.  The two middle contexts read the two selected marker atoms;
their actual meet reads neither marker.  The coefficient presheaf is the
submodule `Int` on marker-free contexts and zero elsewhere.  This makes the
mixed overlap nonzero while the two branches and the terminal base are zero.

The site, cover, coefficient presheaf, and gluing proof are constructed here
from primitive data.  In particular, this lane does not reuse `finiteSite`,
`coarseCover`, or an `ObstructionSheaf` as its positive firing witness.
-/

private inductive FiniteLinearContextIndex where
  | left
  | right
  | base

private def finiteLinearSupportReads
    (i : FiniteLinearContextIndex)
    (atom : FiniteModel.carrier.Atom) : Prop :=
  match i with
  | .left => atom = FiniteModel.FiniteAtom.componentA
  | .right => atom = FiniteModel.FiniteAtom.componentB
  | .base => FiniteModel.object.configuration.family.mem atom

private def finiteLinearContext (i : FiniteLinearContextIndex) :
    Site.ArchCtx FiniteModel.object where
  minimal := {
    Support := PUnit
    Axis := PUnit
    Observable := Empty
    supportReads := fun _ atom => finiteLinearSupportReads i atom
    supportReads_objectFamily := by
      intro support atom h
      cases i with
      | left =>
          rw [h]
          exact FiniteModel.allFamily_mem _ (by simp)
      | right =>
          rw [h]
          exact FiniteModel.allFamily_mem _ (by simp)
      | base => exact h
    axisReads := fun _ => True
    observableReads := Empty.elim
  }
  Extension := FiniteLinearContextIndex
  extension := i

private noncomputable abbrev finiteLinearContextPreorder :
    Site.ContextPreorderCategory FiniteModel.object :=
  Site.contextMorphismPreorderCategory FiniteModel.object

private def finiteLinearContextMorphism
    (i j : FiniteLinearContextIndex)
    (_h : ∀ atom, finiteLinearSupportReads i atom →
      finiteLinearSupportReads j atom) :
    Site.ContextMorphism (finiteLinearContext i) (finiteLinearContext j) where
  supportMap := id
  axisMap := id
  observableRestrict := Empty.elim

private theorem finiteLinearContextMorphism_isRestriction
    (i j : FiniteLinearContextIndex)
    (h : ∀ atom, finiteLinearSupportReads i atom →
      finiteLinearSupportReads j atom) :
    (finiteLinearContextMorphism i j h).IsRestriction := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro support atom hread
    change finiteLinearSupportReads i atom at hread
    exact h atom hread
  · intro axis hread
    trivial
  · intro observable
    exact Empty.elim observable
  · intro support atom hread
    exact (finiteLinearContext j).supportReads_objectFamily hread

private theorem finiteLinearContextLe_of_support
    (i j : FiniteLinearContextIndex)
    (h : ∀ atom, finiteLinearSupportReads i atom →
      finiteLinearSupportReads j atom) :
    finiteLinearContextPreorder.le
      (finiteLinearContext i) (finiteLinearContext j) :=
  ⟨finiteLinearContextMorphism i j h,
    finiteLinearContextMorphism_isRestriction i j h⟩

private theorem finiteLinear_left_le_base :
    finiteLinearContextPreorder.le
      (finiteLinearContext .left) (finiteLinearContext .base) := by
  apply finiteLinearContextLe_of_support
  intro atom h
  rw [h]
  exact FiniteModel.allFamily_mem _ (by simp)

private theorem finiteLinear_right_le_base :
    finiteLinearContextPreorder.le
      (finiteLinearContext .right) (finiteLinearContext .base) := by
  apply finiteLinearContextLe_of_support
  intro atom h
  rw [h]
  exact FiniteModel.allFamily_mem _ (by simp)

private theorem finiteLinear_not_le_of_atom
    (i j : FiniteLinearContextIndex) (atom : FiniteModel.carrier.Atom)
    (hi : finiteLinearSupportReads i atom)
    (hj : ¬ finiteLinearSupportReads j atom) :
    ¬ finiteLinearContextPreorder.le
      (finiteLinearContext i) (finiteLinearContext j) := by
  rintro ⟨f, hf⟩
  have hread := hf.1 (support := PUnit.unit) hi
  apply hj
  simpa [finiteLinearContext] using hread

private theorem finiteLinear_left_not_le_right :
    ¬ finiteLinearContextPreorder.le
      (finiteLinearContext .left) (finiteLinearContext .right) := by
  apply finiteLinear_not_le_of_atom .left .right
    FiniteModel.FiniteAtom.componentA
  · simp [finiteLinearSupportReads]
  · simp [finiteLinearSupportReads]

private theorem finiteLinear_right_not_le_left :
    ¬ finiteLinearContextPreorder.le
      (finiteLinearContext .right) (finiteLinearContext .left) := by
  apply finiteLinear_not_le_of_atom .right .left
    FiniteModel.FiniteAtom.componentB
  · simp [finiteLinearSupportReads]
  · simp [finiteLinearSupportReads]

private theorem finiteLinear_base_not_le_left :
    ¬ finiteLinearContextPreorder.le
      (finiteLinearContext .base) (finiteLinearContext .left) := by
  apply finiteLinear_not_le_of_atom .base .left
    FiniteModel.FiniteAtom.componentB
  · exact FiniteModel.allFamily_mem _ (by simp)
  · simp [finiteLinearSupportReads]

private theorem finiteLinear_base_not_le_right :
    ¬ finiteLinearContextPreorder.le
      (finiteLinearContext .base) (finiteLinearContext .right) := by
  apply finiteLinear_not_le_of_atom .base .right
    FiniteModel.FiniteAtom.componentA
  · exact FiniteModel.allFamily_mem _ (by simp)
  · simp [finiteLinearSupportReads]

private noncomputable def finiteLinearOverlap :
    Site.ContextOverlapPullback finiteLinearContextPreorder :=
  Site.meetOverlapPullback finiteLinearContextPreorder
    Site.productContextFiniteMeet

private def finiteLinearSupportVisibleOn
    (W : Site.ArchCtx FiniteModel.object)
    (atom : FiniteModel.carrier.Atom) : Prop :=
  (W = finiteLinearContext .left ∧
      atom = FiniteModel.FiniteAtom.componentA) ∨
    (W = finiteLinearContext .right ∧
      atom = FiniteModel.FiniteAtom.componentB)

private def finiteLinearCoverageRequirements :
    Site.CoverageRequirements FiniteModel.object
      (FiniteModel.equationSystem finiteLinearContextPreorder) FiniteModel.signature where
  requiredSupport := fun atom =>
    atom = FiniteModel.FiniteAtom.componentA ∨
      atom = FiniteModel.FiniteAtom.componentB
  requiredEquationCoordinate := fun _ => True
  selectedViolationWitness := fun _ => True
  requiredAxis := fun _ => True
  supportVisibleOn := finiteLinearSupportVisibleOn
  equationCoordinateVisibleOn := fun _ _ => True
  violationWitnessVisibleOn := fun _ _ => True
  axisReadableOn := fun W _ =>
    W = finiteLinearContext .left ∨ W = finiteLinearContext .right
  boundaryVisibleOn := fun _ _ => True

/-- Independent AAT site used by the finite linear coefficient firing. -/
noncomputable def finiteLinearSite :
    Site.AATSite FiniteModel.corePackage.object where
  contextPreorder := finiteLinearContextPreorder
  equationSystem := FiniteModel.equationSystem finiteLinearContextPreorder
  signature := FiniteModel.signature
  requirements := finiteLinearCoverageRequirements
  overlap := finiteLinearOverlap

/-- Named additive sheafification instance for the independent linear site. -/
noncomputable instance finiteLinearAddCommGrpHasSheafify :
    HasSheafify finiteLinearSite.topology AddCommGrpCat.{1} := by
  infer_instance

/-- Terminal context selected by the finite linear coefficient model. -/
noncomputable def finiteLinearBase : finiteLinearSite.category :=
  Site.ContextCategoryObject.of finiteLinearContextPreorder
    (finiteLinearContext .base)

private def finiteLinearContextToBaseMorphism
    (X : finiteLinearSite.category) :
    Site.ContextMorphism X.ctx (finiteLinearContext .base) where
  supportMap _ := PUnit.unit
  axisMap _ := PUnit.unit
  observableRestrict := Empty.elim

private theorem finiteLinearContextToBaseMorphism_isRestriction
    (X : finiteLinearSite.category) :
    (finiteLinearContextToBaseMorphism X).IsRestriction := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro support atom hread
    change finiteLinearSupportReads .base atom
    exact X.ctx.minimal.supportReads_objectFamily hread
  · intro axis hread
    trivial
  · intro observable
    exact Empty.elim observable
  · intro support atom hread
    change FiniteModel.object.configuration.family.mem atom at hread
    exact hread

private theorem finiteLinearContextLeBase (X : finiteLinearSite.category) :
    finiteLinearSite.contextPreorder.le X.ctx finiteLinearBase.ctx :=
  ⟨finiteLinearContextToBaseMorphism X,
    finiteLinearContextToBaseMorphism_isRestriction X⟩

private noncomputable def finiteLinearContextToBase
    (X : finiteLinearSite.category) : X ⟶ finiteLinearBase :=
  homOfLE (finiteLinearContextLeBase X)

/-- The selected base is terminal in the actual context category. -/
noncomputable def finiteLinearBaseIsTerminal : Limits.IsTerminal finiteLinearBase :=
  Limits.IsTerminal.ofUniqueHom finiteLinearContextToBase
    (fun _ _ => Subsingleton.elim _ _)

/-- Left branch of the independent strict-diamond model. -/
def finiteLinearLeftObject : finiteLinearSite.category :=
  Site.ContextCategoryObject.of finiteLinearContextPreorder
    (finiteLinearContext .left)

/-- Right branch of the independent strict-diamond model. -/
def finiteLinearRightObject : finiteLinearSite.category :=
  Site.ContextCategoryObject.of finiteLinearContextPreorder
    (finiteLinearContext .right)

private def finiteLinearSelectedOverlapContext :
    Site.ArchCtx FiniteModel.object :=
  finiteLinearOverlap.overlap (finiteLinearContext .base)
    (finiteLinearContext .left) (finiteLinearContext .right)

/-- Actual overlap of the two branches in the independent linear model. -/
def finiteLinearOverlapObject : finiteLinearSite.category :=
  Site.ContextCategoryObject.of finiteLinearContextPreorder
    finiteLinearSelectedOverlapContext

/-- The selected overlap is definitionally the site's actual pair overlap. -/
theorem finiteLinearPairOverlap_eq :
    finiteLinearSite.overlap.overlap finiteLinearBase.ctx
        finiteLinearLeftObject.ctx finiteLinearRightObject.ctx =
      finiteLinearOverlapObject.ctx :=
  rfl

private theorem finiteLinear_left_not_le_overlapObject :
    ¬ finiteLinearSite.contextPreorder.le
      finiteLinearLeftObject.ctx finiteLinearOverlapObject.ctx := by
  rintro ⟨f, hf⟩
  have hread := hf.1 (support := PUnit.unit)
    (atom := FiniteModel.FiniteAtom.componentA)
    (by
      change finiteLinearSupportReads .left FiniteModel.FiniteAtom.componentA
      rfl)
  change
    finiteLinearSupportReads .left FiniteModel.FiniteAtom.componentA ∧
      finiteLinearSupportReads .right FiniteModel.FiniteAtom.componentA at hread
  simpa [finiteLinearSupportReads] using hread.2

private theorem finiteLinear_right_not_le_overlapObject :
    ¬ finiteLinearSite.contextPreorder.le
      finiteLinearRightObject.ctx finiteLinearOverlapObject.ctx := by
  rintro ⟨f, hf⟩
  have hread := hf.1 (support := PUnit.unit)
    (atom := FiniteModel.FiniteAtom.componentB)
    (by
      change finiteLinearSupportReads .right FiniteModel.FiniteAtom.componentB
      rfl)
  change
    finiteLinearSupportReads .left FiniteModel.FiniteAtom.componentB ∧
      finiteLinearSupportReads .right FiniteModel.FiniteAtom.componentB at hread
  simpa [finiteLinearSupportReads] using hread.1

/-- The actual overlap, branches, and terminal base form a strict diamond. -/
theorem finiteLinearStrictDiamond :
    finiteLinearSite.contextPreorder.le
        finiteLinearOverlapObject.ctx finiteLinearLeftObject.ctx ∧
      finiteLinearSite.contextPreorder.le
        finiteLinearOverlapObject.ctx finiteLinearRightObject.ctx ∧
      finiteLinearSite.contextPreorder.le
        finiteLinearLeftObject.ctx finiteLinearBase.ctx ∧
      finiteLinearSite.contextPreorder.le
        finiteLinearRightObject.ctx finiteLinearBase.ctx ∧
      (¬ finiteLinearSite.contextPreorder.le
        finiteLinearLeftObject.ctx finiteLinearRightObject.ctx) ∧
      (¬ finiteLinearSite.contextPreorder.le
        finiteLinearRightObject.ctx finiteLinearLeftObject.ctx) ∧
      (¬ finiteLinearSite.contextPreorder.le
        finiteLinearBase.ctx finiteLinearLeftObject.ctx) ∧
      (¬ finiteLinearSite.contextPreorder.le
        finiteLinearBase.ctx finiteLinearRightObject.ctx) ∧
      (¬ finiteLinearSite.contextPreorder.le
        finiteLinearLeftObject.ctx finiteLinearOverlapObject.ctx) ∧
      (¬ finiteLinearSite.contextPreorder.le
        finiteLinearRightObject.ctx finiteLinearOverlapObject.ctx) := by
  refine ⟨?_, ?_, finiteLinear_left_le_base, finiteLinear_right_le_base,
    finiteLinear_left_not_le_right, finiteLinear_right_not_le_left,
    finiteLinear_base_not_le_left, finiteLinear_base_not_le_right,
    finiteLinear_left_not_le_overlapObject,
    finiteLinear_right_not_le_overlapObject⟩
  · exact Site.productContextFiniteMeet.meet_le_left _ _
  · exact Site.productContextFiniteMeet.meet_le_right _ _

private inductive FiniteLinearCoverIndex where
  | left
  | right

private def finiteLinearCoverPatch :
    FiniteLinearCoverIndex -> Site.ArchCtx FiniteModel.object
  | .left => finiteLinearContext .left
  | .right => finiteLinearContext .right

/-- Two-branch cover of the independent strict-diamond model. -/
noncomputable def finiteLinearCover :
    Site.AATCoverageFamily finiteLinearSite.requirements
      finiteLinearSite.overlap finiteLinearBase where
  Index := FiniteLinearCoverIndex
  patch := finiteLinearCoverPatch
  inclusion := by
    intro i
    cases i
    · exact finiteLinear_left_le_base
    · exact finiteLinear_right_le_base
  admissible := {
    atomSupportCoverage := by
      intro atom h
      rcases h with rfl | rfl
      · exact ⟨.left, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨.right, Or.inr ⟨rfl, rfl⟩⟩
    equationCoordinateCoverage := by
      intro coordinate h
      exact Or.inl ⟨.left, trivial⟩
    violationWitnessCoverage := by
      intro witness h
      exact Or.inl ⟨.left, trivial⟩
    signatureAxisCoverage := by
      intro axis h
      exact ⟨.left, Or.inl rfl⟩
    boundaryCoverage := by
      intro i j
      trivial
    nonGeneration := by
      intro i support atom h
      simpa [finiteLinearBase, finiteLinearContext,
        finiteLinearSupportReads] using h
  }

/-- The finite linear cover has exactly two branch indices. -/
def finiteLinearCoverIndexEquiv : finiteLinearCover.Index ≃ Bool where
  toFun
    | .left => false
    | .right => true
  invFun
    | false => .left
    | true => .right
  left_inv i := by cases i <;> rfl
  right_inv b := by cases b <;> rfl

/-- The finite linear cover contains distinct left and right branches. -/
theorem finiteLinearCover_twoBranches :
    ∃ i j : finiteLinearCover.Index,
      i ≠ j ∧
        finiteLinearCover.patch i = finiteLinearLeftObject.ctx ∧
        finiteLinearCover.patch j = finiteLinearRightObject.ctx := by
  refine ⟨.left, .right, ?_, rfl, rfl⟩
  simp

private def FiniteLinearNoMarkerReads
    (W : Site.ArchCtx FiniteModel.object) : Prop :=
  (∀ support : W.Support,
      ¬ W.minimal.supportReads support FiniteModel.FiniteAtom.componentA) ∧
    (∀ support : W.Support,
      ¬ W.minimal.supportReads support FiniteModel.FiniteAtom.componentB)

private theorem finiteLinearNoMarkerReads_of_le
    {W V : Site.ArchCtx FiniteModel.object}
    (h : finiteLinearContextPreorder.le W V)
    (hV : FiniteLinearNoMarkerReads V) :
    FiniteLinearNoMarkerReads W := by
  let f := finiteLinearContextPreorder.readableMorphism h
  have hf := finiteLinearContextPreorder.readableMorphism_isRestriction h
  constructor
  · intro support hread
    exact hV.1 (f.supportMap support) (hf.1 hread)
  · intro support hread
    exact hV.2 (f.supportMap support) (hf.1 hread)

private noncomputable def finiteLinearCoefficientSubmodule
    (W : Site.ArchCtx FiniteModel.object) : Submodule Int (ULift Int) := by
  classical
  exact if FiniteLinearNoMarkerReads W then ⊤ else ⊥

private theorem finiteLinearCoefficientSubmodule_mono
    {W V : Site.ArchCtx FiniteModel.object}
    (h : finiteLinearContextPreorder.le W V) :
    finiteLinearCoefficientSubmodule V ≤
      finiteLinearCoefficientSubmodule W := by
  by_cases hV : FiniteLinearNoMarkerReads V
  · have hW := finiteLinearNoMarkerReads_of_le h hV
    simp [finiteLinearCoefficientSubmodule, hV, hW]
  · simp [finiteLinearCoefficientSubmodule, hV]

private noncomputable def finiteLinearCoefficientPresheaf :
    finiteLinearSite.categoryᵒᵖ ⥤ ModuleCat.{1} Int where
  obj X := ModuleCat.of Int
    (finiteLinearCoefficientSubmodule X.unop.ctx)
  map {X Y} f := ModuleCat.ofHom
    (Submodule.inclusion
      (finiteLinearCoefficientSubmodule_mono (leOfHom f.unop)))
  map_id X := by
    apply ModuleCat.hom_ext
    ext x
    rfl
  map_comp {X Y Z} f g := by
    apply ModuleCat.hom_ext
    ext x
    rfl

private theorem finiteLinear_admissibleCover_has_left
    {Z : finiteLinearSite.category}
    (F : Site.AATCoverageFamily finiteLinearSite.requirements
      finiteLinearSite.overlap Z) :
    ∃ i : F.Index, F.patch i = finiteLinearContext .left := by
  rcases F.admissible.atomSupportCoverage
      FiniteModel.FiniteAtom.componentA (Or.inl rfl) with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  rcases hi with hi | hi
  · exact hi.1
  · exact False.elim (by simpa using hi.2)

private theorem finiteLinear_admissibleCover_has_right
    {Z : finiteLinearSite.category}
    (F : Site.AATCoverageFamily finiteLinearSite.requirements
      finiteLinearSite.overlap Z) :
    ∃ i : F.Index, F.patch i = finiteLinearContext .right := by
  rcases F.admissible.atomSupportCoverage
      FiniteModel.FiniteAtom.componentB (Or.inr rfl) with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  rcases hi with hi | hi
  · exact False.elim (by simpa using hi.2)
  · exact hi.1

private theorem finiteLinearNoMarkerReads_product_left
    {W V : Site.ArchCtx FiniteModel.object}
    (hW : FiniteLinearNoMarkerReads W) :
    FiniteLinearNoMarkerReads (Site.productContext W V) := by
  constructor
  · rintro ⟨w, v⟩ h
    exact hW.1 w h.1
  · rintro ⟨w, v⟩ h
    exact hW.2 w h.1

private theorem finiteLinearProductWithLeft_not_noMarkerReads
    {W : Site.ArchCtx FiniteModel.object} {support : W.Support}
    (hread : W.minimal.supportReads support
      FiniteModel.FiniteAtom.componentA) :
    ¬ FiniteLinearNoMarkerReads
      (Site.productContext W (finiteLinearContext .left)) := by
  intro h
  exact h.1 (support, PUnit.unit)
    ⟨hread, by simp [finiteLinearContext, finiteLinearSupportReads]⟩

private theorem finiteLinearProductWithRight_not_noMarkerReads
    {W : Site.ArchCtx FiniteModel.object} {support : W.Support}
    (hread : W.minimal.supportReads support
      FiniteModel.FiniteAtom.componentB) :
    ¬ FiniteLinearNoMarkerReads
      (Site.productContext W (finiteLinearContext .right)) := by
  intro h
  exact h.2 (support, PUnit.unit)
    ⟨hread, by simp [finiteLinearContext, finiteLinearSupportReads]⟩

private def finiteLinearProductObject
    (X Y : finiteLinearSite.category) : finiteLinearSite.category :=
  Site.ContextCategoryObject.of finiteLinearContextPreorder
    (Site.productContext X.ctx Y.ctx)

private noncomputable def finiteLinearProductLeft
    (X Y : finiteLinearSite.category) : finiteLinearProductObject X Y ⟶ X :=
  homOfLE (Site.productContextFiniteMeet.meet_le_left X.ctx Y.ctx)

private noncomputable def finiteLinearProductRight
    (X Y : finiteLinearSite.category) : finiteLinearProductObject X Y ⟶ Y :=
  homOfLE (Site.productContextFiniteMeet.meet_le_right X.ctx Y.ctx)

private theorem finiteLinearCoefficientPresheaf_isSheaf_ofTypes :
    Presieve.IsSheaf finiteLinearSite.topology
      (finiteLinearCoefficientPresheaf ⋙
        forget₂ (ModuleCat.{1} Int) AddCommGrpCat.{1} ⋙
        forget AddCommGrpCat.{1}) := by
  rw [Site.AATSite.topology, Site.AATGrothendieckTopology]
  rw [Precoverage.isSheaf_toGrothendieck_iff]
  intro X Y f R hR
  rcases hR with ⟨F, rfl⟩
  intro family hfamily
  classical
  have hmarker : ∃ i : F.Index,
      finiteLinearCoefficientSubmodule
          (Site.productContext Y.ctx (F.patch i)) =
        finiteLinearCoefficientSubmodule Y.ctx := by
    by_cases hY : FiniteLinearNoMarkerReads Y.ctx
    · rcases finiteLinear_admissibleCover_has_left F with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      have hQ := finiteLinearNoMarkerReads_product_left
        (V := F.patch i) hY
      simp [finiteLinearCoefficientSubmodule, hY, hQ]
    · simp only [FiniteLinearNoMarkerReads, not_and_or, not_forall,
        not_not] at hY
      rcases hY with hA | hB
      · rcases hA with ⟨support, hsupport⟩
        rcases finiteLinear_admissibleCover_has_left F with ⟨i, hi⟩
        refine ⟨i, ?_⟩
        have hQ : ¬ FiniteLinearNoMarkerReads
            (Site.productContext Y.ctx (F.patch i)) := by
          rw [hi]
          exact finiteLinearProductWithLeft_not_noMarkerReads hsupport
        have hYnot : ¬ FiniteLinearNoMarkerReads Y.ctx := fun h =>
          h.1 support hsupport
        simp [finiteLinearCoefficientSubmodule, hYnot, hQ]
      · rcases hB with ⟨support, hsupport⟩
        rcases finiteLinear_admissibleCover_has_right F with ⟨i, hi⟩
        refine ⟨i, ?_⟩
        have hQ : ¬ FiniteLinearNoMarkerReads
            (Site.productContext Y.ctx (F.patch i)) := by
          rw [hi]
          exact finiteLinearProductWithRight_not_noMarkerReads hsupport
        have hYnot : ¬ FiniteLinearNoMarkerReads Y.ctx := fun h =>
          h.2 support hsupport
        simp [finiteLinearCoefficientSubmodule, hYnot, hQ]
  rcases hmarker with ⟨i, hsubmodule⟩
  let patchObject := Site.ContextCategoryObject.of finiteLinearContextPreorder
    (F.patch i)
  let Q := finiteLinearProductObject Y patchObject
  let q : Q ⟶ Y := finiteLinearProductLeft Y patchObject
  let qpatch : Q ⟶ patchObject := finiteLinearProductRight Y patchObject
  have hq : (Sieve.generate F.presieve).pullback f q := by
    change Sieve.generate F.presieve (q ≫ f)
    have hinclusion : Sieve.generate F.presieve
        (homOfLE (F.inclusion i)) :=
      Sieve.le_generate F.presieve _ (Presieve.ofArrows.mk i)
    have hcomp := (Sieve.generate F.presieve).downward_closed
      hinclusion qpatch
    convert hcomp using 1
  let reference := family q hq
  have reference_mem_Y : reference.1 ∈
      finiteLinearCoefficientSubmodule Y.ctx := by
    rw [← hsubmodule]
    exact reference.2
  let global : finiteLinearCoefficientSubmodule Y.ctx :=
    ⟨reference.1, reference_mem_Y⟩
  have hconstant : ∀ {Z : finiteLinearSite.category}
      (g : Z ⟶ Y) (hg : (Sieve.generate F.presieve).pullback f g),
      (family g hg).1 = reference.1 := by
    intro Z g hg
    let P := finiteLinearProductObject Z Q
    let pz : P ⟶ Z := finiteLinearProductLeft Z Q
    let pq : P ⟶ Q := finiteLinearProductRight Z Q
    have hcompat := hfamily pz pq hg hq (Subsingleton.elim _ _)
    exact congrArg Subtype.val hcompat
  refine ⟨global, ?_, ?_⟩
  · intro Z g hg
    apply Subtype.ext
    change global.1 = (family g hg).1
    exact (hconstant g hg).symm
  · intro other hother
    apply Subtype.ext
    have hqOther := hother q hq
    have hval := congrArg Subtype.val hqOther
    change other.1 = global.1
    exact hval

private theorem finiteLinearCoefficientPresheaf_isSheaf :
    Presheaf.IsSheaf finiteLinearSite.topology
      (finiteLinearCoefficientPresheaf ⋙
        forget₂ (ModuleCat.{1} Int) AddCommGrpCat.{1}) := by
  apply Presheaf.isSheaf_of_isSheaf_comp
    (P := finiteLinearCoefficientPresheaf ⋙
      forget₂ (ModuleCat.{1} Int) AddCommGrpCat.{1})
    (s := forget AddCommGrpCat.{1})
  rw [isSheaf_iff_isSheaf_of_type]
  exact finiteLinearCoefficientPresheaf_isSheaf_ofTypes

/-- `Int`-linear coefficient sheaf on the independent strict-diamond site. -/
noncomputable def finiteLinearCoefficientSheaf :
    Cohomology.LinearCoefficientSheaf Int finiteLinearSite where
  modulePresheaf := finiteLinearCoefficientPresheaf
  isSheaf := finiteLinearCoefficientPresheaf_isSheaf

/-!
The finite-dimensional measurement fixture needs the same strict-diamond
coefficient geometry over an explicitly finite field.  The following
Type-valued presheaf is the `ZMod 2` instance of the marker-reading
construction above.  It remains in this source file because the order and
cover lemmas used to prove the sheaf condition are intentionally private to
the strict-diamond model.
-/

/-- `ZMod 2` sections are nonzero exactly on contexts reading neither selected
marker. -/
noncomputable def finiteLinearF2CoefficientSubmodule
    (W : Site.ArchCtx FiniteModel.object) : Submodule (ZMod 2) (ZMod 2) := by
  classical
  exact if FiniteLinearNoMarkerReads W then ⊤ else ⊥

private theorem finiteLinearF2CoefficientSubmodule_mono
    {W V : Site.ArchCtx FiniteModel.object}
    (h : finiteLinearContextPreorder.le W V) :
    finiteLinearF2CoefficientSubmodule V ≤
      finiteLinearF2CoefficientSubmodule W := by
  by_cases hV : FiniteLinearNoMarkerReads V
  · have hW := finiteLinearNoMarkerReads_of_le h hV
    simp [finiteLinearF2CoefficientSubmodule, hV, hW]
  · simp [finiteLinearF2CoefficientSubmodule, hV]

/-- Type-valued finite-field coefficient presheaf on the strict-diamond
site. -/
noncomputable def finiteLinearF2CoefficientPresheaf :
    Site.AATPresheaf finiteLinearSite where
  obj X := finiteLinearF2CoefficientSubmodule X.unop.ctx
  map {X Y} f x :=
    ⟨x.1, finiteLinearF2CoefficientSubmodule_mono (leOfHom f.unop) x.2⟩
  map_id X := by
    funext x
    rfl
  map_comp {X Y Z} f g := by
    funext x
    rfl

private theorem finiteLinearF2CoefficientPresheaf_isSheaf :
    Presieve.IsSheaf finiteLinearSite.topology
      finiteLinearF2CoefficientPresheaf := by
  rw [Site.AATSite.topology, Site.AATGrothendieckTopology]
  rw [Precoverage.isSheaf_toGrothendieck_iff]
  intro X Y f R hR
  rcases hR with ⟨F, rfl⟩
  intro family hfamily
  classical
  have hmarker : ∃ i : F.Index,
      finiteLinearF2CoefficientSubmodule
          (Site.productContext Y.ctx (F.patch i)) =
        finiteLinearF2CoefficientSubmodule Y.ctx := by
    by_cases hY : FiniteLinearNoMarkerReads Y.ctx
    · rcases finiteLinear_admissibleCover_has_left F with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      have hQ := finiteLinearNoMarkerReads_product_left
        (V := F.patch i) hY
      simp [finiteLinearF2CoefficientSubmodule, hY, hQ]
    · simp only [FiniteLinearNoMarkerReads, not_and_or, not_forall,
        not_not] at hY
      rcases hY with hA | hB
      · rcases hA with ⟨support, hsupport⟩
        rcases finiteLinear_admissibleCover_has_left F with ⟨i, hi⟩
        refine ⟨i, ?_⟩
        have hQ : ¬ FiniteLinearNoMarkerReads
            (Site.productContext Y.ctx (F.patch i)) := by
          rw [hi]
          exact finiteLinearProductWithLeft_not_noMarkerReads hsupport
        have hYnot : ¬ FiniteLinearNoMarkerReads Y.ctx := fun h =>
          h.1 support hsupport
        unfold finiteLinearF2CoefficientSubmodule
        rw [if_neg hQ, if_neg hYnot]
      · rcases hB with ⟨support, hsupport⟩
        rcases finiteLinear_admissibleCover_has_right F with ⟨i, hi⟩
        refine ⟨i, ?_⟩
        have hQ : ¬ FiniteLinearNoMarkerReads
            (Site.productContext Y.ctx (F.patch i)) := by
          rw [hi]
          exact finiteLinearProductWithRight_not_noMarkerReads hsupport
        have hYnot : ¬ FiniteLinearNoMarkerReads Y.ctx := fun h =>
          h.2 support hsupport
        unfold finiteLinearF2CoefficientSubmodule
        rw [if_neg hQ, if_neg hYnot]
  rcases hmarker with ⟨i, hsubmodule⟩
  let patchObject := Site.ContextCategoryObject.of finiteLinearContextPreorder
    (F.patch i)
  let Q := finiteLinearProductObject Y patchObject
  let q : Q ⟶ Y := finiteLinearProductLeft Y patchObject
  let qpatch : Q ⟶ patchObject := finiteLinearProductRight Y patchObject
  have hq : (Sieve.generate F.presieve).pullback f q := by
    change Sieve.generate F.presieve (q ≫ f)
    have hinclusion : Sieve.generate F.presieve
        (homOfLE (F.inclusion i)) :=
      Sieve.le_generate F.presieve _ (Presieve.ofArrows.mk i)
    have hcomp := (Sieve.generate F.presieve).downward_closed
      hinclusion qpatch
    convert hcomp using 1
  let reference := family q hq
  have reference_mem_Y : reference.1 ∈
      finiteLinearF2CoefficientSubmodule Y.ctx := by
    rw [← hsubmodule]
    exact reference.2
  let global : finiteLinearF2CoefficientSubmodule Y.ctx :=
    ⟨reference.1, reference_mem_Y⟩
  have hconstant : ∀ {Z : finiteLinearSite.category}
      (g : Z ⟶ Y) (hg : (Sieve.generate F.presieve).pullback f g),
      (family g hg).1 = reference.1 := by
    intro Z g hg
    let P := finiteLinearProductObject Z Q
    let pz : P ⟶ Z := finiteLinearProductLeft Z Q
    let pq : P ⟶ Q := finiteLinearProductRight Z Q
    have hcompat := hfamily pz pq hg hq (Subsingleton.elim _ _)
    exact congrArg Subtype.val hcompat
  refine ⟨global, ?_, ?_⟩
  · intro Z g hg
    apply Subtype.ext
    change global.1 = (family g hg).1
    exact (hconstant g hg).symm
  · intro other hother
    apply Subtype.ext
    have hqOther := hother q hq
    have hval := congrArg Subtype.val hqOther
    change other.1 = global.1
    exact hval

/-- Named additive structure on each finite-field coefficient section. -/
noncomputable def finiteLinearF2SectionAddCommGroup
    (W : finiteLinearSite.category) :
    AddCommGroup (finiteLinearF2CoefficientSubmodule W.ctx) :=
  inferInstance

/-- `ZMod 2` obstruction sheaf whose patch sections vanish while mixed-overlap
sections remain nontrivial. -/
noncomputable def finiteLinearF2ObstructionSheaf :
    Cohomology.ObstructionSheaf finiteLinearSite where
  carrier := {
    carrier := finiteLinearF2CoefficientPresheaf
    isSheaf := by
      intro base cover hcover
      exact finiteLinearF2CoefficientPresheaf_isSheaf cover hcover
  }
  addCommGroup W := finiteLinearF2SectionAddCommGroup W
  map_zero := by
    intros
    apply Subtype.ext
    rfl
  map_add := by
    intros
    apply Subtype.ext
    rfl

@[simp]
theorem finiteLinearF2ObstructionSheaf_toPresheaf :
    finiteLinearF2ObstructionSheaf.carrier.toPresheaf =
      finiteLinearF2CoefficientPresheaf :=
  rfl

/-- Every strict-diamond finite-field restriction is the linear inclusion of
the corresponding coefficient submodules. -/
noncomputable def finiteLinearF2RestrictionLinear
    {source target : finiteLinearSite.category} (f : source ⟶ target) :
    finiteLinearF2CoefficientSubmodule target.ctx →ₗ[ZMod 2]
      finiteLinearF2CoefficientSubmodule source.ctx :=
  Submodule.inclusion
    (finiteLinearF2CoefficientSubmodule_mono (leOfHom f))

@[simp]
theorem finiteLinearF2Section_zero_val
    (W : finiteLinearSite.category) :
    letI : AddCommGroup (finiteLinearF2CoefficientSubmodule W.ctx) :=
      finiteLinearF2ObstructionSheaf.addCommGroup W
    ((0 : finiteLinearF2CoefficientSubmodule W.ctx).1 : ZMod 2) = 0 := by
  rfl

@[simp]
theorem finiteLinearF2Section_add_val
    (W : finiteLinearSite.category)
    (x y : finiteLinearF2CoefficientSubmodule W.ctx) :
    letI : AddCommGroup (finiteLinearF2CoefficientSubmodule W.ctx) :=
      finiteLinearF2ObstructionSheaf.addCommGroup W
    (x + y).1 = x.1 + y.1 := by
  rfl

@[simp]
theorem finiteLinearF2Section_neg_val
    (W : finiteLinearSite.category)
    (x : finiteLinearF2CoefficientSubmodule W.ctx) :
    letI : AddCommGroup (finiteLinearF2CoefficientSubmodule W.ctx) :=
      finiteLinearF2ObstructionSheaf.addCommGroup W
    (-x).1 = -x.1 := by
  rfl

@[simp]
theorem finiteLinearF2RestrictionLinear_apply
    {source target : finiteLinearSite.category} (f : source ⟶ target)
    (x : finiteLinearF2CoefficientSubmodule target.ctx) :
    finiteLinearF2RestrictionLinear f x =
      finiteLinearF2CoefficientPresheaf.map f.op x :=
  rfl

@[simp]
theorem finiteLinearF2CoefficientPresheaf_map_val
    {source target : finiteLinearSite.category} (f : source ⟶ target)
    (x : finiteLinearF2CoefficientSubmodule target.ctx) :
    (finiteLinearF2CoefficientPresheaf.map f.op x).1 = x.1 :=
  rfl

/-- Finiteness of the selected two-branch cover, transported from `Bool`. -/
noncomputable instance finiteLinearCoverIndexFintype :
    Fintype finiteLinearCover.Index :=
  Fintype.ofEquiv Bool finiteLinearCoverIndexEquiv.symm

/-- Canonical polynomial coefficient sheaf obtained from the integer model. -/
noncomputable def finiteBaseChangedLinearCoefficientSheaf :
    Cohomology.LinearCoefficientSheaf (Polynomial Int) finiteLinearSite :=
  finiteLinearCoefficientSheaf.baseChange intPolynomialFlatChange

private noncomputable def finiteLinearRawPolynomialPresheaf :
    finiteLinearSite.categoryᵒᵖ ⥤ ModuleCat.{1} (Polynomial Int) :=
  finiteLinearCoefficientSheaf.rawBaseChangePresheaf intPolynomialFlatChange

private theorem finiteLinearRawPolynomialPresheaf_map_injective
    {X Y : finiteLinearSite.category} (g : X ⟶ Y) :
    Function.Injective (finiteLinearRawPolynomialPresheaf.map g.op) := by
  letI : Algebra Int (Polynomial Int) := intPolynomialFlatChange.hom.toAlgebra
  letI : Module Int (Polynomial Int) := Algebra.toModule
  haveI : Module.Flat Int (Polynomial Int) := by
    exact intPolynomialFlatChange.flat
  have hinjective : Function.Injective
      (finiteLinearCoefficientPresheaf.map g.op).hom := by
    change Function.Injective (Submodule.inclusion
      (finiteLinearCoefficientSubmodule_mono (leOfHom g)))
    intro x y hxy
    apply Subtype.ext
    exact congrArg
      (fun z : finiteLinearCoefficientSubmodule X.ctx => (z : ULift Int)) hxy
  change Function.Injective
    ((ModuleCat.extendScalars intPolynomialFlatChange.hom).map
      (finiteLinearCoefficientPresheaf.map g.op)).hom
  simpa only [ModuleCat.extendScalars, ModuleCat.ExtendScalars.map',
    LinearMap.baseChange_eq_ltensor] using
    (Module.Flat.lTensor_preserves_injective_linearMap
      (finiteLinearCoefficientPresheaf.map g.op).hom hinjective)

private theorem finiteLinearRawPolynomialPresheaf_isSheaf_ofTypes :
    Presieve.IsSheaf finiteLinearSite.topology
      (finiteLinearRawPolynomialPresheaf ⋙
        forget₂ (ModuleCat.{1} (Polynomial Int)) AddCommGrpCat.{1} ⋙
        forget AddCommGrpCat.{1}) := by
  rw [Site.AATSite.topology, Site.AATGrothendieckTopology]
  rw [Precoverage.isSheaf_toGrothendieck_iff]
  intro X Y f R hR
  rcases hR with ⟨F, rfl⟩
  intro family hfamily
  classical
  have hmarker : ∃ i : F.Index,
      finiteLinearCoefficientSubmodule
          (Site.productContext Y.ctx (F.patch i)) =
        finiteLinearCoefficientSubmodule Y.ctx := by
    by_cases hY : FiniteLinearNoMarkerReads Y.ctx
    · rcases finiteLinear_admissibleCover_has_left F with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      have hQ := finiteLinearNoMarkerReads_product_left
        (V := F.patch i) hY
      simp [finiteLinearCoefficientSubmodule, hY, hQ]
    · simp only [FiniteLinearNoMarkerReads, not_and_or, not_forall,
        not_not] at hY
      rcases hY with hA | hB
      · rcases hA with ⟨support, hsupport⟩
        rcases finiteLinear_admissibleCover_has_left F with ⟨i, hi⟩
        refine ⟨i, ?_⟩
        have hQ : ¬ FiniteLinearNoMarkerReads
            (Site.productContext Y.ctx (F.patch i)) := by
          rw [hi]
          exact finiteLinearProductWithLeft_not_noMarkerReads hsupport
        have hYnot : ¬ FiniteLinearNoMarkerReads Y.ctx := fun h =>
          h.1 support hsupport
        simp [finiteLinearCoefficientSubmodule, hYnot, hQ]
      · rcases hB with ⟨support, hsupport⟩
        rcases finiteLinear_admissibleCover_has_right F with ⟨i, hi⟩
        refine ⟨i, ?_⟩
        have hQ : ¬ FiniteLinearNoMarkerReads
            (Site.productContext Y.ctx (F.patch i)) := by
          rw [hi]
          exact finiteLinearProductWithRight_not_noMarkerReads hsupport
        have hYnot : ¬ FiniteLinearNoMarkerReads Y.ctx := fun h =>
          h.2 support hsupport
        simp [finiteLinearCoefficientSubmodule, hYnot, hQ]
  rcases hmarker with ⟨i, hsubmodule⟩
  let patchObject := Site.ContextCategoryObject.of finiteLinearContextPreorder
    (F.patch i)
  let Q := finiteLinearProductObject Y patchObject
  let q : Q ⟶ Y := finiteLinearProductLeft Y patchObject
  let qpatch : Q ⟶ patchObject := finiteLinearProductRight Y patchObject
  have hq : (Sieve.generate F.presieve).pullback f q := by
    change Sieve.generate F.presieve (q ≫ f)
    have hinclusion : Sieve.generate F.presieve
        (homOfLE (F.inclusion i)) :=
      Sieve.le_generate F.presieve _ (Presieve.ofArrows.mk i)
    have hcomp := (Sieve.generate F.presieve).downward_closed
      hinclusion qpatch
    convert hcomp using 1
  haveI : IsIso (finiteLinearCoefficientPresheaf.map q.op) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    constructor
    · change Function.Injective (Submodule.inclusion
        (finiteLinearCoefficientSubmodule_mono (leOfHom q)))
      intro x y hxy
      apply Subtype.ext
      exact congrArg
        (fun z : finiteLinearCoefficientSubmodule Q.ctx => (z : ULift Int)) hxy
    · intro y
      refine ⟨⟨y.1, ?_⟩, ?_⟩
      · have hy := y.2
        change y.1 ∈ finiteLinearCoefficientSubmodule
          (Site.productContext Y.ctx (F.patch i)) at hy
        rw [hsubmodule] at hy
        exact hy
      · apply Subtype.ext
        rfl
  haveI : IsIso (finiteLinearRawPolynomialPresheaf.map q.op) := by
    change IsIso ((ModuleCat.extendScalars intPolynomialFlatChange.hom).map
      (finiteLinearCoefficientPresheaf.map q.op))
    infer_instance
  let reference := family q hq
  let global := inv (finiteLinearRawPolynomialPresheaf.map q.op) reference
  refine ⟨global, ?_, ?_⟩
  · intro Z g hg
    let P := finiteLinearProductObject Z Q
    let pz : P ⟶ Z := finiteLinearProductLeft Z Q
    let pq : P ⟶ Q := finiteLinearProductRight Z Q
    apply finiteLinearRawPolynomialPresheaf_map_injective pz
    have hcompat := hfamily pz pq hg hq (Subsingleton.elim _ _)
    change
      (finiteLinearRawPolynomialPresheaf ⋙
        forget₂ (ModuleCat.{1} (Polynomial Int)) AddCommGrpCat.{1} ⋙
        forget AddCommGrpCat.{1}).map pz.op
          ((finiteLinearRawPolynomialPresheaf ⋙
            forget₂ (ModuleCat.{1} (Polynomial Int)) AddCommGrpCat.{1} ⋙
            forget AddCommGrpCat.{1}).map g.op global) = _
    calc
      _ = (finiteLinearRawPolynomialPresheaf ⋙
            forget₂ (ModuleCat.{1} (Polynomial Int)) AddCommGrpCat.{1} ⋙
            forget AddCommGrpCat.{1}).map pq.op
          ((finiteLinearRawPolynomialPresheaf ⋙
            forget₂ (ModuleCat.{1} (Polynomial Int)) AddCommGrpCat.{1} ⋙
            forget AddCommGrpCat.{1}).map q.op global) := by
              rw [← FunctorToTypes.map_comp_apply,
                ← FunctorToTypes.map_comp_apply]
              congr 2
      _ = (finiteLinearRawPolynomialPresheaf ⋙
            forget₂ (ModuleCat.{1} (Polynomial Int)) AddCommGrpCat.{1} ⋙
            forget AddCommGrpCat.{1}).map pq.op reference := by
            dsimp [global]
            rw [IsIso.inv_hom_id_apply]
      _ = (finiteLinearRawPolynomialPresheaf ⋙
            forget₂ (ModuleCat.{1} (Polynomial Int)) AddCommGrpCat.{1} ⋙
            forget AddCommGrpCat.{1}).map pz.op (family g hg) :=
            hcompat.symm
  · intro other hother
    apply finiteLinearRawPolynomialPresheaf_map_injective q
    change
      (finiteLinearRawPolynomialPresheaf ⋙
        forget₂ (ModuleCat.{1} (Polynomial Int)) AddCommGrpCat.{1} ⋙
        forget AddCommGrpCat.{1}).map q.op other =
      (finiteLinearRawPolynomialPresheaf ⋙
        forget₂ (ModuleCat.{1} (Polynomial Int)) AddCommGrpCat.{1} ⋙
        forget AddCommGrpCat.{1}).map q.op global
    dsimp [global]
    rw [IsIso.inv_hom_id_apply]
    exact hother q hq

private theorem finiteLinearRawPolynomialPresheaf_isSheaf :
    Presheaf.IsSheaf finiteLinearSite.topology
      (finiteLinearRawPolynomialPresheaf ⋙
        forget₂ (ModuleCat.{1} (Polynomial Int)) AddCommGrpCat.{1}) := by
  apply Presheaf.isSheaf_of_isSheaf_comp
    (P := finiteLinearRawPolynomialPresheaf ⋙
      forget₂ (ModuleCat.{1} (Polynomial Int)) AddCommGrpCat.{1})
    (s := forget AddCommGrpCat.{1})
  rw [isSheaf_iff_isSheaf_of_type]
  exact finiteLinearRawPolynomialPresheaf_isSheaf_ofTypes

/-- Canonical coefficient change commutes with every degree of the finite Čech complex. -/
theorem finiteCechCoefficientCompatible :
    Cohomology.LinearCoefficientSheaf.CechCoefficientBaseChangeCompatible
      finiteLinearCoefficientSheaf intPolynomialFlatChange finiteLinearCover :=
  Cohomology.LinearCoefficientSheaf.cechCoefficientBaseChangeCompatible_of_finite_raw_isSheaf
      finiteLinearCoefficientSheaf intPolynomialFlatChange finiteLinearCover
      finiteLinearRawPolynomialPresheaf_isSheaf

private theorem finiteLinear_topology_contains_of_hom_to_left
    {X : finiteLinearSite.category}
    (hX : X ⟶ finiteLinearLeftObject) :
    ∀ {Z : finiteLinearSite.category} (f : X ⟶ Z)
      {R : Sieve Z}, R ∈ finiteLinearSite.topology Z → R f := by
  intro Z f R hR
  change (Site.admissiblePrecoverage finiteLinearCoverageRequirements
    finiteLinearOverlap).Saturate Z R at hR
  induction hR with
  | of Z P hP =>
      rcases hP with ⟨F, rfl⟩
      rcases finiteLinear_admissibleCover_has_left F with ⟨i, hi⟩
      let g : X ⟶ Site.ContextCategoryObject.of finiteLinearContextPreorder
          (F.patch i) :=
        hX ≫ eqToHom (congrArg
          (Site.ContextCategoryObject.of finiteLinearContextPreorder) hi).symm
      have hinclusion : (Sieve.generate F.presieve)
          (homOfLE (F.inclusion i)) :=
        Sieve.le_generate F.presieve _ (Presieve.ofArrows.mk i)
      have hcomp := (Sieve.generate F.presieve).downward_closed
        hinclusion g
      convert hcomp using 1
  | top Z => simp
  | pullback Z S hS Y g ih =>
      change S (f ≫ g)
      exact ih (f ≫ g)
  | transitive Z S R hS hlocal ihS ihlocal =>
      have hSf : S f := ihS f
      have hRf : (R.pullback f) (𝟙 X) := ihlocal hSf (𝟙 X)
      simpa using hRf

private theorem finiteLinear_topology_contains_of_hom_to_right
    {X : finiteLinearSite.category}
    (hX : X ⟶ finiteLinearRightObject) :
    ∀ {Z : finiteLinearSite.category} (f : X ⟶ Z)
      {R : Sieve Z}, R ∈ finiteLinearSite.topology Z → R f := by
  intro Z f R hR
  change (Site.admissiblePrecoverage finiteLinearCoverageRequirements
    finiteLinearOverlap).Saturate Z R at hR
  induction hR with
  | of Z P hP =>
      rcases hP with ⟨F, rfl⟩
      rcases finiteLinear_admissibleCover_has_right F with ⟨i, hi⟩
      let g : X ⟶ Site.ContextCategoryObject.of finiteLinearContextPreorder
          (F.patch i) :=
        hX ≫ eqToHom (congrArg
          (Site.ContextCategoryObject.of finiteLinearContextPreorder) hi).symm
      have hinclusion : (Sieve.generate F.presieve)
          (homOfLE (F.inclusion i)) :=
        Sieve.le_generate F.presieve _ (Presieve.ofArrows.mk i)
      have hcomp := (Sieve.generate F.presieve).downward_closed
        hinclusion g
      convert hcomp using 1
  | top Z => simp
  | pullback Z S hS Y g ih =>
      change S (f ≫ g)
      exact ih (f ≫ g)
  | transitive Z S R hS hlocal ihS ihlocal =>
      have hSf : S f := ihS f
      have hRf : (R.pullback f) (𝟙 X) := ihlocal hSf (𝟙 X)
      simpa using hRf

private theorem finiteLinear_topology_eq_top_of_hom_to_left
    {X : finiteLinearSite.category}
    (hX : X ⟶ finiteLinearLeftObject)
    {R : Sieve X} (hR : R ∈ finiteLinearSite.topology X) :
    R = ⊤ := by
  apply top_unique
  intro Y f hf
  exact finiteLinear_topology_contains_of_hom_to_left (f ≫ hX) f hR

private theorem finiteLinear_topology_eq_top_of_hom_to_right
    {X : finiteLinearSite.category}
    (hX : X ⟶ finiteLinearRightObject)
    {R : Sieve X} (hR : R ∈ finiteLinearSite.topology X) :
    R = ⊤ := by
  apply top_unique
  intro Y f hf
  exact finiteLinear_topology_contains_of_hom_to_right (f ≫ hX) f hR

private noncomputable def finiteLinearSheafifiedFreeYoneda
    (X : finiteLinearSite.category) :
    Sheaf finiteLinearSite.topology AddCommGrpCat.{1} :=
  (presheafToSheaf finiteLinearSite.topology AddCommGrpCat.{1}).obj
    (yoneda.obj X ⋙ AddCommGrpCat.free)

private theorem finiteLinearSheafifiedFreeYoneda_projective_of_hom_to_left
    (X : finiteLinearSite.category) (hX : X ⟶ finiteLinearLeftObject) :
    Projective (finiteLinearSheafifiedFreeYoneda X) := by
  constructor
  intro E G f e he
  letI : Epi e := he
  have hloc : Presheaf.IsLocallySurjective finiteLinearSite.topology e.val :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{1} e).2 inferInstance
  let x := Cohomology.sheafifiedFreeYonedaHomAddEquiv X G f
  have hcover := Presheaf.imageSieve_mem finiteLinearSite.topology e.val x
  have htop := finiteLinear_topology_eq_top_of_hom_to_left hX hcover
  have hid : Presheaf.imageSieve e.val x (𝟙 X) := by
    rw [htop]
    trivial
  rcases hid with ⟨t, ht⟩
  let lift : finiteLinearSheafifiedFreeYoneda X ⟶ E :=
    (Cohomology.sheafifiedFreeYonedaHomAddEquiv X E).symm t
  refine ⟨lift, ?_⟩
  apply (Cohomology.sheafifiedFreeYonedaHomAddEquiv X G).injective
  rw [Cohomology.sheafifiedFreeYonedaHomAddEquiv_comp]
  change e.val.app (op X)
      (Cohomology.sheafifiedFreeYonedaHomAddEquiv X E lift) = x
  rw [show Cohomology.sheafifiedFreeYonedaHomAddEquiv X E lift = t by
    exact (Cohomology.sheafifiedFreeYonedaHomAddEquiv X E).apply_symm_apply t]
  simpa using ht

private theorem finiteLinearSheafifiedFreeYoneda_projective_of_hom_to_right
    (X : finiteLinearSite.category) (hX : X ⟶ finiteLinearRightObject) :
    Projective (finiteLinearSheafifiedFreeYoneda X) := by
  constructor
  intro E G f e he
  letI : Epi e := he
  have hloc : Presheaf.IsLocallySurjective finiteLinearSite.topology e.val :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{1} e).2 inferInstance
  let x := Cohomology.sheafifiedFreeYonedaHomAddEquiv X G f
  have hcover := Presheaf.imageSieve_mem finiteLinearSite.topology e.val x
  have htop := finiteLinear_topology_eq_top_of_hom_to_right hX hcover
  have hid : Presheaf.imageSieve e.val x (𝟙 X) := by
    rw [htop]
    trivial
  rcases hid with ⟨t, ht⟩
  let lift : finiteLinearSheafifiedFreeYoneda X ⟶ E :=
    (Cohomology.sheafifiedFreeYonedaHomAddEquiv X E).symm t
  refine ⟨lift, ?_⟩
  apply (Cohomology.sheafifiedFreeYonedaHomAddEquiv X G).injective
  rw [Cohomology.sheafifiedFreeYonedaHomAddEquiv_comp]
  change e.val.app (op X)
      (Cohomology.sheafifiedFreeYonedaHomAddEquiv X E lift) = x
  rw [show Cohomology.sheafifiedFreeYonedaHomAddEquiv X E lift = t by
    exact (Cohomology.sheafifiedFreeYonedaHomAddEquiv X E).apply_symm_apply t]
  simpa using ht

private theorem finiteLinearCover_isLeray_for
    {R : Type} [CommRing R]
    (Ob : Cohomology.LinearCoefficientSheaf R finiteLinearSite) :
    Cohomology.LinearCoefficientSheaf.IsLinearLerayFor finiteLinearCover Ob := by
  intro q hq p σ
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  let X := (Cohomology.canonicalCoverRelative finiteLinearCover).overlap p σ
  have hprojection := Cohomology.canonicalTupleOverlapProjection
    finiteLinearCover σ (0 : Fin (p + 1))
  cases hindex : σ 0 with
  | left =>
      have hp : X ⟶ finiteLinearLeftObject := by
        simpa [X, Cohomology.canonicalCoverRelative,
          finiteLinearCoverPatch, hindex] using hprojection
      letI : Projective (finiteLinearSheafifiedFreeYoneda X) :=
        finiteLinearSheafifiedFreeYoneda_projective_of_hom_to_left X hp
      exact CategoryTheory.Abelian.Ext.subsingleton_of_projective
        (finiteLinearSheafifiedFreeYoneda X) Ob.toAddCommGrpSheaf n
  | right =>
      have hp : X ⟶ finiteLinearRightObject := by
        simpa [X, Cohomology.canonicalCoverRelative,
          finiteLinearCoverPatch, hindex] using hprojection
      letI : Projective (finiteLinearSheafifiedFreeYoneda X) :=
        finiteLinearSheafifiedFreeYoneda_projective_of_hom_to_right X hp
      exact CategoryTheory.Abelian.Ext.subsingleton_of_projective
        (finiteLinearSheafifiedFreeYoneda X) Ob.toAddCommGrpSheaf n

/-- The selected finite cover is Leray for the source integer coefficient. -/
theorem finiteLinearLerayCover :
    Cohomology.LinearCoefficientSheaf.IsLinearLerayFor
      finiteLinearCover finiteLinearCoefficientSheaf :=
  finiteLinearCover_isLeray_for finiteLinearCoefficientSheaf

/-- The same selected finite cover is Leray for the canonical target coefficient. -/
theorem finiteTargetLinearLerayCover :
    Cohomology.LinearCoefficientSheaf.IsLinearLerayFor finiteLinearCover
      finiteBaseChangedLinearCoefficientSheaf :=
  finiteLinearCover_isLeray_for finiteBaseChangedLinearCoefficientSheaf

/-- Canonical linear Čech complex of the finite integer model. -/
noncomputable def finiteLinearCech :
    Cohomology.LinearCoverRelativeCechComplex Int
      finiteLinearCover finiteLinearCoefficientSheaf :=
  finiteLinearCoefficientSheaf.canonicalLinearCech finiteLinearCover

/-- Degree selected by the finite nonzero class. -/
def finiteDegree : Nat := 1

private def finiteLinearPotential : FiniteLinearCoverIndex → Int
  | .left => 0
  | .right => 1

private def finiteLinearOneValue
    (i j : FiniteLinearCoverIndex) : ULift Int :=
  ULift.up (finiteLinearPotential j - finiteLinearPotential i)

private theorem finiteLinearNoMarkerReads_left_right :
    FiniteLinearNoMarkerReads
      (Site.productContext (finiteLinearContext .left)
        (finiteLinearContext .right)) := by
  constructor <;> rintro ⟨leftSupport, rightSupport⟩ hread
  · simpa [finiteLinearContext, finiteLinearSupportReads] using hread.2
  · simpa [finiteLinearContext, finiteLinearSupportReads] using hread.1

private theorem finiteLinearNoMarkerReads_right_left :
    FiniteLinearNoMarkerReads
      (Site.productContext (finiteLinearContext .right)
        (finiteLinearContext .left)) := by
  constructor <;> rintro ⟨rightSupport, leftSupport⟩ hread
  · simpa [finiteLinearContext, finiteLinearSupportReads] using hread.1
  · simpa [finiteLinearContext, finiteLinearSupportReads] using hread.2

/-- Finite-field potential on the two selected cover branches. -/
def finiteLinearF2Potential : finiteLinearCover.Index → ZMod 2
  | .left => 0
  | .right => 1

/-- Canonical finite-field section on a pair overlap.  Equal branches give the
zero section; a mixed pair gives the nonzero section of the full overlap
module. -/
noncomputable def finiteLinearF2PairSection
    (i j : finiteLinearCover.Index) :
    finiteLinearF2CoefficientSubmodule
      (finiteLinearSite.overlap.overlap finiteLinearBase.ctx
        (finiteLinearCover.patch i) (finiteLinearCover.patch j)) := by
  cases i <;> cases j
  · exact 0
  · refine ⟨1, ?_⟩
    unfold finiteLinearF2CoefficientSubmodule
    rw [if_pos]
    · exact Submodule.mem_top
    · exact finiteLinearNoMarkerReads_left_right
  · refine ⟨1, ?_⟩
    unfold finiteLinearF2CoefficientSubmodule
    rw [if_pos]
    · exact Submodule.mem_top
    · exact finiteLinearNoMarkerReads_right_left
  · exact 0

@[simp]
theorem finiteLinearF2PairSection_val
    (i j : finiteLinearCover.Index) :
    (finiteLinearF2PairSection i j).1 =
      finiteLinearF2Potential j - finiteLinearF2Potential i := by
  cases i <;> cases j <;>
    simp [finiteLinearF2PairSection, finiteLinearF2Potential]

private noncomputable def finiteLinearCechOneCochain :
    finiteLinearCech.complex.X 1 := fun σ => by
  refine ⟨finiteLinearOneValue (σ 0) (σ 1), ?_⟩
  cases h0 : σ 0 <;> cases h1 : σ 1
  · rw [show finiteLinearOneValue .left .left = 0 by rfl]
    exact Submodule.zero_mem _
  · have hnomarker : FiniteLinearNoMarkerReads
        ((Cohomology.canonicalCoverRelative finiteLinearCover).overlap 1 σ).ctx := by
      simpa [Cohomology.canonicalCoverRelative,
        Cohomology.canonicalTupleOverlap, finiteLinearCover,
        finiteLinearCoverPatch, h0, h1] using
        finiteLinearNoMarkerReads_left_right
    change FiniteLinearNoMarkerReads
      (finiteLinearSite.overlap.overlap finiteLinearBase.ctx
        (Site.ContextCategoryObject.of finiteLinearSite.contextPreorder
          (finiteLinearCover.patch (σ 0))).ctx
        (finiteLinearCover.patch (σ 1))) at hnomarker
    simp [finiteLinearOneValue, finiteLinearPotential,
      finiteLinearCoefficientSubmodule, hnomarker]
  · have hnomarker : FiniteLinearNoMarkerReads
        ((Cohomology.canonicalCoverRelative finiteLinearCover).overlap 1 σ).ctx := by
      simpa [Cohomology.canonicalCoverRelative,
        Cohomology.canonicalTupleOverlap, finiteLinearCover,
        finiteLinearCoverPatch, h0, h1] using
        finiteLinearNoMarkerReads_right_left
    change FiniteLinearNoMarkerReads
      (finiteLinearSite.overlap.overlap finiteLinearBase.ctx
        (Site.ContextCategoryObject.of finiteLinearSite.contextPreorder
          (finiteLinearCover.patch (σ 0))).ctx
        (finiteLinearCover.patch (σ 1))) at hnomarker
    simp [finiteLinearOneValue, finiteLinearPotential,
      finiteLinearCoefficientSubmodule, hnomarker]
  · rw [show finiteLinearOneValue .right .right = 0 by rfl]
    exact Submodule.zero_mem _

private theorem finiteLinearCoefficientMap_val
    {X Y : finiteLinearSite.category} (f : X ⟶ Y)
    (x : finiteLinearCoefficientSheaf.modulePresheaf.obj (op Y)) :
    ((finiteLinearCoefficientSheaf.modulePresheaf.map f.op) x).1 = x.1 :=
  rfl

private theorem finiteLinearCechOneCochain_isCocycle :
    finiteLinearCech.complex.d 1 2 finiteLinearCechOneCochain = 0 := by
  change
    (finiteLinearCoefficientSheaf.canonicalLinearCech
      finiteLinearCover).complex.d 1 2 finiteLinearCechOneCochain = 0
  funext σ
  rw [Cohomology.LinearCoefficientSheaf.canonicalLinearCech_d_apply]
  classical
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fintype.sum_empty, add_zero]
  norm_num
  apply Subtype.ext
  change
    ((finiteLinearCoefficientSheaf.modulePresheaf.map
        (Cohomology.canonicalTupleOverlapMap finiteLinearCover
          (SimplexCategory.δ (0 : Fin 3)) σ).op)
      (finiteLinearCechOneCochain
        (fun j => σ ((SimplexCategory.δ (0 : Fin 3)).toOrderHom j)))).1 +
      (-((finiteLinearCoefficientSheaf.modulePresheaf.map
          (Cohomology.canonicalTupleOverlapMap finiteLinearCover
            (SimplexCategory.δ (1 : Fin 3)) σ).op)
        (finiteLinearCechOneCochain
          (fun j => σ ((SimplexCategory.δ (1 : Fin 3)).toOrderHom j)))).1 +
        ((finiteLinearCoefficientSheaf.modulePresheaf.map
          (Cohomology.canonicalTupleOverlapMap finiteLinearCover
            (SimplexCategory.δ (2 : Fin 3)) σ).op)
        (finiteLinearCechOneCochain
          (fun j => σ ((SimplexCategory.δ (2 : Fin 3)).toOrderHom j)))).1) = 0
  rw [finiteLinearCoefficientMap_val, finiteLinearCoefficientMap_val,
    finiteLinearCoefficientMap_val]
  apply ULift.down_injective
  simp [finiteLinearCechOneCochain, finiteLinearOneValue,
    SimplexCategory.δ, Fin.succAbove]

private noncomputable def finiteLinearDegreeOneCochainHom :
    ModuleCat.of Int (ULift Int) ⟶ finiteLinearCech.complex.X 1 :=
  ModuleCat.ofHom
    { toFun := fun r => r.down • finiteLinearCechOneCochain
      map_add' := by
        intro x y
        simp [add_smul]
      map_smul' := by
        intro x y
        simp [mul_smul] }

private theorem finiteLinearDegreeOneCochainHom_comp_d :
    finiteLinearDegreeOneCochainHom ≫ finiteLinearCech.complex.d 1 2 = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (finiteLinearCech.complex.d 1 2)
      (r.down • finiteLinearCechOneCochain) = 0
  rw [map_smul, finiteLinearCechOneCochain_isCocycle]
  simp

/-- Explicit degree-one cycle in the canonical finite linear Čech complex. -/
noncomputable def finiteCocycle :
    finiteLinearCech.complex.cycles finiteDegree :=
  (finiteLinearCech.complex.liftCycles finiteLinearDegreeOneCochainHom 2
    (by simp) finiteLinearDegreeOneCochainHom_comp_d).hom
      (ULift.up 1)

private theorem finiteCocycle_iCycles :
    (finiteLinearCech.complex.iCycles 1).hom finiteCocycle =
      finiteLinearCechOneCochain := by
  have h := ConcreteCategory.congr_hom
    (finiteLinearCech.complex.liftCycles_i
      finiteLinearDegreeOneCochainHom 2 (by simp)
      finiteLinearDegreeOneCochainHom_comp_d) (ULift.up 1)
  rw [ConcreteCategory.comp_apply] at h
  dsimp only [finiteCocycle]
  convert h using 1
  change finiteLinearCechOneCochain =
    (1 : Int) • finiteLinearCechOneCochain
  simp

private theorem finiteLinearCoefficientSubmodule_left_eq_bot :
    finiteLinearCoefficientSubmodule (finiteLinearContext .left) = ⊥ := by
  have hnot : ¬ FiniteLinearNoMarkerReads (finiteLinearContext .left) := by
    intro h
    exact h.1 PUnit.unit (by rfl)
  simp [finiteLinearCoefficientSubmodule, hnot]

private theorem finiteLinearCoefficientSubmodule_right_eq_bot :
    finiteLinearCoefficientSubmodule (finiteLinearContext .right) = ⊥ := by
  have hnot : ¬ FiniteLinearNoMarkerReads (finiteLinearContext .right) := by
    intro h
    exact h.2 PUnit.unit (by rfl)
  simp [finiteLinearCoefficientSubmodule, hnot]

/-- Every selected cover patch has only the zero finite-field section. -/
theorem finiteLinearF2CoefficientSubmodule_patch_eq_bot
    (i : finiteLinearCover.Index) :
    finiteLinearF2CoefficientSubmodule (finiteLinearCover.patch i) = ⊥ := by
  cases i with
  | left =>
      have hnot : ¬ FiniteLinearNoMarkerReads (finiteLinearContext .left) := by
        intro h
        exact h.1 PUnit.unit (by rfl)
      simp [finiteLinearCover, finiteLinearCoverPatch,
        finiteLinearF2CoefficientSubmodule, hnot]
  | right =>
      have hnot : ¬ FiniteLinearNoMarkerReads (finiteLinearContext .right) := by
        intro h
        exact h.2 PUnit.unit (by rfl)
      simp [finiteLinearCover, finiteLinearCoverPatch,
        finiteLinearF2CoefficientSubmodule, hnot]

private theorem finiteLinearDegreeZeroCoefficient_eq_bot
    (σ : (Cohomology.canonicalCoverRelative finiteLinearCover).simplex 0) :
    finiteLinearCoefficientSubmodule
      ((Cohomology.canonicalCoverRelative finiteLinearCover).overlap 0 σ).ctx =
        ⊥ := by
  cases h : σ 0
  · simpa [Cohomology.canonicalCoverRelative,
      Cohomology.canonicalTupleOverlap, finiteLinearCover,
      finiteLinearCoverPatch, h] using
      finiteLinearCoefficientSubmodule_left_eq_bot
  · simpa [Cohomology.canonicalCoverRelative,
      Cohomology.canonicalTupleOverlap, finiteLinearCover,
      finiteLinearCoverPatch, h] using
      finiteLinearCoefficientSubmodule_right_eq_bot

private theorem finiteLinearCechZeroCochain_eq_zero
    (b : finiteLinearCech.complex.X 0) : b = 0 := by
  funext σ
  apply Subtype.ext
  have hb : (b σ).1 ∈ (⊥ : Submodule Int (ULift Int)) := by
    rw [← finiteLinearDegreeZeroCoefficient_eq_bot σ]
    exact (b σ).2
  exact hb

private theorem moduleCochainHomologyπ_eq_zero_iff
    {R : Type} [CommRing R]
    (K : CochainComplex (ModuleCat.{1} R) Nat)
    (n : Nat) (z : K.cycles n) :
    (K.homologyπ n).hom z = 0 ↔
      ∃ y : K.X (n - 1),
        (K.d (n - 1) n).hom y = (K.iCycles n).hom z := by
  let Q := ShortComplex.mk (K.toCycles (n - 1) n) (K.homologyπ n)
    (K.toCycles_comp_homologyπ (n - 1) n)
  have hQ : Q.Exact := ShortComplex.exact_of_g_is_cokernel _
    (K.homologyIsCokernel (n - 1) n (by cases n <;> simp))
  have hfun : Function.Exact Q.f.hom Q.g.hom :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact Q).mp hQ
  constructor
  · intro hz
    rcases (hfun z).mp hz with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    have hi := congrArg (K.iCycles n).hom hy
    have hcomp := ConcreteCategory.congr_hom (K.toCycles_i (n - 1) n) y
    rw [ConcreteCategory.comp_apply] at hcomp
    exact hcomp.symm.trans hi
  · rintro ⟨y, hy⟩
    apply (hfun z).mpr
    refine ⟨y, ?_⟩
    apply (ModuleCat.mono_iff_injective (K.iCycles n)).mp inferInstance
    have hcomp := ConcreteCategory.congr_hom (K.toCycles_i (n - 1) n) y
    rw [ConcreteCategory.comp_apply] at hcomp
    exact hcomp.trans hy

private def finiteLinearMixedOneSimplex :
    (Cohomology.canonicalCoverRelative finiteLinearCover).simplex 1 :=
  fun i => if i = 0 then .left else .right

private theorem finiteLinearCechOneCochain_mixed_val :
    (finiteLinearCechOneCochain finiteLinearMixedOneSimplex).1 = ULift.up 1 := by
  rfl

private theorem finiteLinearCechOneCochain_ne_zero :
    finiteLinearCechOneCochain ≠ 0 := by
  intro h
  have hv := congrArg
    (fun c => (c finiteLinearMixedOneSimplex).1.down) h
  change (1 : Int) = 0 at hv
  norm_num at hv

private theorem finiteLinearCechOneClass_ne_zero :
    (finiteLinearCech.complex.homologyπ 1).hom finiteCocycle ≠ 0 := by
  intro hzero
  rcases (moduleCochainHomologyπ_eq_zero_iff
    finiteLinearCech.complex 1 finiteCocycle).mp hzero with ⟨b, hb⟩
  rw [finiteLinearCechZeroCochain_eq_zero b, map_zero] at hb
  have hcycle : (finiteLinearCech.complex.iCycles 1).hom finiteCocycle = 0 :=
    hb.symm
  rw [finiteCocycle_iCycles] at hcycle
  exact finiteLinearCechOneCochain_ne_zero hcycle

private theorem intPolynomialModuleScalarExtensionUnit_injective
    (M : ModuleCat.{v} Int) :
    Function.Injective
      (Derived.Intersection.moduleScalarExtensionUnit.{0, v}
        intPolynomialFlatChange M) := by
  intro x y hxy
  rw [Derived.Intersection.moduleScalarExtensionUnit_apply,
    Derived.Intersection.moduleScalarExtensionUnit_apply] at hxy
  letI : Module Int (Polynomial Int) :=
    Module.compHom (Polynomial Int) intPolynomialFlatChange.hom
  let coeffZero : Polynomial Int →ₗ[Int] Int :=
    { toFun := fun p : Polynomial Int => Polynomial.coeff p 0
      map_add' := by simp
      map_smul' := by
        intro r p
        change (Polynomial.C r * p).coeff 0 = r * p.coeff 0
        simp }
  let contract := (LinearMap.lsmul Int M).comp coeffZero
  have hretract := congrArg (TensorProduct.lift contract) hxy
  simpa [contract, coeffZero] using hretract

/-- Actual terminal degree-one source class obtained from Leray comparison. -/
noncomputable def finiteActualSourceClass :
    finiteLinearCoefficientSheaf.terminalLerayHModule
      finiteLinearCover finiteLinearBaseIsTerminal finiteLinearLerayCover
        finiteDegree :=
  finiteLinearCoefficientSheaf.cechToSheafHLinearIso
    finiteLinearCover finiteLinearBaseIsTerminal finiteLinearLerayCover
      finiteDegree
    (finiteLinearCech.complex.homologyπ finiteDegree finiteCocycle)

/-- Canonical actual-`Sheaf.H` map for the finite coefficient firing. -/
noncomputable def finiteSheafHBaseChangeMap :
    Derived.Intersection.moduleScalarExtension.{0, 2}
        intPolynomialFlatChange
        (finiteLinearCoefficientSheaf.terminalLerayHModule
          finiteLinearCover finiteLinearBaseIsTerminal
            finiteLinearLerayCover finiteDegree) ⟶
      finiteBaseChangedLinearCoefficientSheaf.terminalLerayHModule
        finiteLinearCover finiteLinearBaseIsTerminal
          finiteTargetLinearLerayCover finiteDegree :=
  Cohomology.LinearCoefficientSheaf.sheafHFlatBaseChangeMap
    finiteLinearCoefficientSheaf intPolynomialFlatChange finiteLinearCover
    finiteLinearBaseIsTerminal finiteLinearLerayCover
    finiteTargetLinearLerayCover finiteDegree

/-- The finite actual-`Sheaf.H` base-change map is the hom of the canonical iso. -/
noncomputable def finiteSheafHBaseChangeIso :
    Derived.Intersection.moduleScalarExtension.{0, 2}
        intPolynomialFlatChange
        (finiteLinearCoefficientSheaf.terminalLerayHModule
          finiteLinearCover finiteLinearBaseIsTerminal
            finiteLinearLerayCover finiteDegree) ≅
      finiteBaseChangedLinearCoefficientSheaf.terminalLerayHModule
        finiteLinearCover finiteLinearBaseIsTerminal
          finiteTargetLinearLerayCover finiteDegree :=
  Cohomology.LinearCoefficientSheaf.sheafHFlatBaseChangeIso
    finiteLinearCoefficientSheaf intPolynomialFlatChange finiteLinearCover
    finiteLinearBaseIsTerminal finiteCechCoefficientCompatible
    finiteLinearLerayCover finiteTargetLinearLerayCover finiteDegree

/-- Identification of the canonical actual-`Sheaf.H` map with the iso hom. -/
theorem finiteSheafHBaseChangeIso_hom :
    finiteSheafHBaseChangeIso.hom = finiteSheafHBaseChangeMap :=
  Cohomology.LinearCoefficientSheaf.sheafHFlatBaseChangeIso_hom
    finiteLinearCoefficientSheaf intPolynomialFlatChange finiteLinearCover
    finiteLinearBaseIsTerminal finiteCechCoefficientCompatible
    finiteLinearLerayCover finiteTargetLinearLerayCover finiteDegree

/-- The explicit degree-one class remains nonzero after polynomial scalar extension. -/
theorem finiteClass_baseChange_nonzero :
    finiteLinearCech.classBaseChange intPolynomialFlatChange
      finiteDegree finiteCocycle ≠ 0 := by
  intro hzero
  have hunit :
      Derived.Intersection.moduleScalarExtensionUnit.{0, 1}
          intPolynomialFlatChange (finiteLinearCech.complex.homology finiteDegree)
          (finiteLinearCech.complex.homologyπ finiteDegree finiteCocycle) = 0 := by
    apply (ConcreteCategory.bijective_of_isIso
      (finiteLinearCech.hnFlatBaseChangeIso
        intPolynomialFlatChange finiteDegree).hom).1
    rw [finiteLinearCech.class_baseChange_naturality, hzero, map_zero]
  have hsource :
      finiteLinearCech.complex.homologyπ finiteDegree finiteCocycle = 0 := by
    apply intPolynomialModuleScalarExtensionUnit_injective
      (finiteLinearCech.complex.homology finiteDegree)
    simpa using hunit
  exact finiteLinearCechOneClass_ne_zero (by simpa [finiteDegree] using hsource)

/-- The canonical actual terminal `Sheaf.H` class has nonzero coefficient image. -/
theorem finiteSheafHClass_baseChange_nonzero :
    finiteSheafHBaseChangeMap
        (Derived.Intersection.moduleScalarExtensionUnit.{0, 2}
          intPolynomialFlatChange
          (finiteLinearCoefficientSheaf.terminalLerayHModule
            finiteLinearCover finiteLinearBaseIsTerminal
              finiteLinearLerayCover finiteDegree)
          finiteActualSourceClass) ≠ 0 := by
  intro hzero
  have hunit :
      Derived.Intersection.moduleScalarExtensionUnit.{0, 2}
          intPolynomialFlatChange
          (finiteLinearCoefficientSheaf.terminalLerayHModule
            finiteLinearCover finiteLinearBaseIsTerminal
              finiteLinearLerayCover finiteDegree)
          finiteActualSourceClass = 0 := by
    apply (ConcreteCategory.bijective_of_isIso
      finiteSheafHBaseChangeIso.hom).1
    rw [finiteSheafHBaseChangeIso_hom, hzero, map_zero]
  have hsource : finiteActualSourceClass = 0 := by
    apply intPolynomialModuleScalarExtensionUnit_injective
      (finiteLinearCoefficientSheaf.terminalLerayHModule
        finiteLinearCover finiteLinearBaseIsTerminal finiteLinearLerayCover
          finiteDegree)
    simpa using hunit
  apply finiteLinearCechOneClass_ne_zero
  apply (finiteLinearCoefficientSheaf.cechToSheafHLinearIso
    finiteLinearCover finiteLinearBaseIsTerminal finiteLinearLerayCover
      finiteDegree).injective
  simpa [finiteActualSourceClass, finiteDegree] using hsource

/-- The zero cycle does not provide a positive firing witness. -/
theorem zeroClass_not_firing :
    finiteLinearCech.classBaseChange intPolynomialFlatChange
      finiteDegree 0 = 0 := by
  rw [← finiteLinearCech.class_baseChange_naturality]
  simp

/-! ## R9c: independent topology and selected-cover firing -/

private inductive TopologyContextIndex where
  | left
  | right
  | auxBase
  | auxPatch
  | base

private def topologySupportReads
    (i : TopologyContextIndex) (atom : FiniteModel.carrier.Atom) : Prop :=
  match i with
  | .left => atom = FiniteModel.FiniteAtom.componentA
  | .right => atom = FiniteModel.FiniteAtom.componentB
  | .auxBase | .auxPatch =>
      atom = FiniteModel.FiniteAtom.componentA ∨
        atom = FiniteModel.FiniteAtom.componentB
  | .base => FiniteModel.object.configuration.family.mem atom

private def topologyAxisReads (i : TopologyContextIndex) : Prop :=
  i ≠ .auxPatch

private def TopologyObservable : TopologyContextIndex → Type
  | .base => Empty
  | _ => PUnit

private def topologyObservableReads (i : TopologyContextIndex) :
    TopologyObservable i → Prop :=
  match i with
  | .auxBase | .auxPatch => fun _ => True
  | .left | .right => fun _ => False
  | .base => Empty.elim

private def topologyContext (i : TopologyContextIndex) :
    Site.ArchCtx FiniteModel.object where
  minimal := {
    Support := PUnit
    Axis := PUnit
    Observable := TopologyObservable i
    supportReads := fun _ atom => topologySupportReads i atom
    supportReads_objectFamily := by
      intro support atom h
      cases i with
      | left =>
          rw [h]
          exact FiniteModel.allFamily_mem _ (by simp)
      | right =>
          rw [h]
          exact FiniteModel.allFamily_mem _ (by simp)
      | auxBase | auxPatch =>
          rcases h with rfl | rfl <;>
            exact FiniteModel.allFamily_mem _ (by simp)
      | base => exact h
    axisReads := fun _ => topologyAxisReads i
    observableReads := topologyObservableReads i
  }
  Extension := TopologyContextIndex
  extension := i

private noncomputable abbrev topologyContextPreorder :
    Site.ContextPreorderCategory FiniteModel.object :=
  Site.contextMorphismPreorderCategory FiniteModel.object

private def topologyContextMorphism
    (i j : TopologyContextIndex)
    (_hsupport : ∀ atom, topologySupportReads i atom →
      topologySupportReads j atom)
    (_haxis : topologyAxisReads i → topologyAxisReads j)
    (observableRestrict : TopologyObservable j → TopologyObservable i)
    (_hobservable : ∀ observable,
      topologyObservableReads j observable →
        topologyObservableReads i (observableRestrict observable)) :
    Site.ContextMorphism (topologyContext i) (topologyContext j) where
  supportMap := id
  axisMap := id
  observableRestrict := observableRestrict

private theorem topologyContextMorphism_isRestriction
    (i j : TopologyContextIndex)
    (hsupport : ∀ atom, topologySupportReads i atom →
      topologySupportReads j atom)
    (haxis : topologyAxisReads i → topologyAxisReads j) :
    ∀ (observableRestrict : TopologyObservable j → TopologyObservable i)
      (hobservable : ∀ observable,
        topologyObservableReads j observable →
          topologyObservableReads i (observableRestrict observable)),
      (topologyContextMorphism i j hsupport haxis
        observableRestrict hobservable).IsRestriction := by
  intro observableRestrict hobservable
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro support atom hread
    exact hsupport atom hread
  · intro axis hread
    exact haxis hread
  · intro observable hread
    exact hobservable observable hread
  · intro support atom hread
    exact (topologyContext j).supportReads_objectFamily hread

private theorem topologyContextLe_of_reads
    (i j : TopologyContextIndex)
    (hsupport : ∀ atom, topologySupportReads i atom →
      topologySupportReads j atom)
    (haxis : topologyAxisReads i → topologyAxisReads j)
    (observableRestrict : TopologyObservable j → TopologyObservable i)
    (hobservable : ∀ observable,
      topologyObservableReads j observable →
        topologyObservableReads i (observableRestrict observable)) :
    topologyContextPreorder.le (topologyContext i) (topologyContext j) :=
  ⟨topologyContextMorphism i j hsupport haxis observableRestrict hobservable,
    topologyContextMorphism_isRestriction i j hsupport haxis
      observableRestrict hobservable⟩

private theorem topology_not_le_of_atom
    (i j : TopologyContextIndex) (atom : FiniteModel.carrier.Atom)
    (hi : topologySupportReads i atom)
    (hj : ¬ topologySupportReads j atom) :
    ¬ topologyContextPreorder.le (topologyContext i) (topologyContext j) := by
  rintro ⟨f, hf⟩
  apply hj
  simpa [topologyContext] using
    (hf.1 (support := PUnit.unit) (atom := atom) hi)

private theorem topology_not_le_of_axis
    (i j : TopologyContextIndex)
    (hi : topologyAxisReads i) (hj : ¬ topologyAxisReads j) :
    ¬ topologyContextPreorder.le (topologyContext i) (topologyContext j) := by
  rintro ⟨f, hf⟩
  apply hj
  simpa [topologyContext] using
    (hf.2.1 (axis := PUnit.unit) hi)

private theorem topology_left_le_base :
    topologyContextPreorder.le
      (topologyContext .left) (topologyContext .base) := by
  refine topologyContextLe_of_reads .left .base ?_ ?_ Empty.elim ?_
  · intro atom h
    rw [h]
    exact FiniteModel.allFamily_mem _ (by simp)
  · simp [topologyAxisReads]
  · intro observable
    exact Empty.elim observable

private theorem topology_right_le_base :
    topologyContextPreorder.le
      (topologyContext .right) (topologyContext .base) := by
  refine topologyContextLe_of_reads .right .base ?_ ?_ Empty.elim ?_
  · intro atom h
    rw [h]
    exact FiniteModel.allFamily_mem _ (by simp)
  · simp [topologyAxisReads]
  · intro observable
    exact Empty.elim observable

private theorem topology_auxBase_le_base :
    topologyContextPreorder.le
      (topologyContext .auxBase) (topologyContext .base) := by
  refine topologyContextLe_of_reads .auxBase .base ?_ ?_ Empty.elim ?_
  · intro atom h
    rcases h with rfl | rfl <;>
      exact FiniteModel.allFamily_mem _ (by simp)
  · simp [topologyAxisReads]
  · intro observable
    exact Empty.elim observable

private theorem topology_auxPatch_le_auxBase :
    topologyContextPreorder.le
      (topologyContext .auxPatch) (topologyContext .auxBase) := by
  refine topologyContextLe_of_reads .auxPatch .auxBase ?_ ?_ id ?_
  · intro atom h
    exact h
  · simp [topologyAxisReads]
  · intro observable h
    exact h

private noncomputable def topologyOverlap :
    Site.ContextOverlapPullback topologyContextPreorder :=
  Site.meetOverlapPullback topologyContextPreorder
    Site.productContextFiniteMeet

private def topologySupportVisibleOn
    (W : Site.ArchCtx FiniteModel.object)
    (atom : FiniteModel.carrier.Atom) : Prop :=
  (W = topologyContext .left ∧
      atom = FiniteModel.FiniteAtom.componentA) ∨
    (W = topologyContext .right ∧
      atom = FiniteModel.FiniteAtom.componentB)

private def topologyCoverageRequirements :
    Site.CoverageRequirements FiniteModel.object
      (FiniteModel.equationSystem topologyContextPreorder) FiniteModel.signature where
  requiredSupport := fun atom =>
    atom = FiniteModel.FiniteAtom.componentA ∨
      atom = FiniteModel.FiniteAtom.componentB
  requiredEquationCoordinate := fun _ => True
  selectedViolationWitness := fun _ => True
  requiredAxis := fun _ => True
  supportVisibleOn := topologySupportVisibleOn
  equationCoordinateVisibleOn := fun _ _ => True
  violationWitnessVisibleOn := fun _ _ => True
  axisReadableOn := fun W _ =>
    W = topologyContext .left ∨ W = topologyContext .right
  boundaryVisibleOn := fun _ base => base = topologyContext .base

/-- Independent site carrying the strict topology-change example. -/
noncomputable def topologySite :
    Site.AATSite FiniteModel.corePackage.object where
  contextPreorder := topologyContextPreorder
  equationSystem := FiniteModel.equationSystem topologyContextPreorder
  signature := FiniteModel.signature
  requirements := topologyCoverageRequirements
  overlap := topologyOverlap

/-- Terminal object of the topology-change model. -/
noncomputable def topologyBase : topologySite.category :=
  Site.ContextCategoryObject.of topologyContextPreorder (topologyContext .base)

private def topologyContextToBaseMorphism (X : topologySite.category) :
    Site.ContextMorphism X.ctx (topologyContext .base) where
  supportMap _ := PUnit.unit
  axisMap _ := PUnit.unit
  observableRestrict := Empty.elim

private theorem topologyContextToBaseMorphism_isRestriction
    (X : topologySite.category) :
    (topologyContextToBaseMorphism X).IsRestriction := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro support atom hread
    exact X.ctx.minimal.supportReads_objectFamily hread
  · intro axis hread
    simp [topologyContext, topologyAxisReads]
  · intro observable
    exact Empty.elim observable
  · intro support atom hread
    exact hread

private theorem topologyContextLeBase (X : topologySite.category) :
    topologySite.contextPreorder.le X.ctx topologyBase.ctx :=
  ⟨topologyContextToBaseMorphism X,
    topologyContextToBaseMorphism_isRestriction X⟩

private noncomputable def topologyContextToBase
    (X : topologySite.category) : X ⟶ topologyBase :=
  homOfLE (topologyContextLeBase X)

/-- The selected topology base is terminal in the actual context category. -/
noncomputable def topologyBaseIsTerminal : Limits.IsTerminal topologyBase :=
  Limits.IsTerminal.ofUniqueHom topologyContextToBase
    (fun _ _ => Subsingleton.elim _ _)

/-- Left branch of the topology-change diamond. -/
def topologyLeftObject : topologySite.category :=
  Site.ContextCategoryObject.of topologyContextPreorder (topologyContext .left)

/-- Right branch of the topology-change diamond. -/
def topologyRightObject : topologySite.category :=
  Site.ContextCategoryObject.of topologyContextPreorder (topologyContext .right)

private def topologySelectedOverlapContext : Site.ArchCtx FiniteModel.object :=
  topologyOverlap.overlap (topologyContext .base)
    (topologyContext .left) (topologyContext .right)

/-- Actual overlap of the two selected branches. -/
def topologyOverlapObject : topologySite.category :=
  Site.ContextCategoryObject.of topologyContextPreorder
    topologySelectedOverlapContext

theorem topologyPairOverlap_eq :
    topologySite.overlap.overlap topologyBase.ctx
        topologyLeftObject.ctx topologyRightObject.ctx =
      topologyOverlapObject.ctx := rfl

private theorem topology_left_not_le_right :
    ¬ topologyContextPreorder.le
      (topologyContext .left) (topologyContext .right) := by
  apply topology_not_le_of_atom .left .right
    FiniteModel.FiniteAtom.componentA
  · simp [topologySupportReads]
  · simp [topologySupportReads]

private theorem topology_right_not_le_left :
    ¬ topologyContextPreorder.le
      (topologyContext .right) (topologyContext .left) := by
  apply topology_not_le_of_atom .right .left
    FiniteModel.FiniteAtom.componentB
  · simp [topologySupportReads]
  · simp [topologySupportReads]

private theorem topology_base_not_le_left :
    ¬ topologyContextPreorder.le
      (topologyContext .base) (topologyContext .left) := by
  apply topology_not_le_of_atom .base .left
    FiniteModel.FiniteAtom.componentB
  · exact FiniteModel.allFamily_mem _ (by simp)
  · simp [topologySupportReads]

private theorem topology_base_not_le_right :
    ¬ topologyContextPreorder.le
      (topologyContext .base) (topologyContext .right) := by
  apply topology_not_le_of_atom .base .right
    FiniteModel.FiniteAtom.componentA
  · exact FiniteModel.allFamily_mem _ (by simp)
  · simp [topologySupportReads]

private theorem topology_left_not_le_overlap :
    ¬ topologySite.contextPreorder.le
      topologyLeftObject.ctx topologyOverlapObject.ctx := by
  rintro ⟨f, hf⟩
  have hread := hf.1 (support := PUnit.unit)
    (atom := FiniteModel.FiniteAtom.componentA)
    (show topologySupportReads .left
      FiniteModel.FiniteAtom.componentA by rfl)
  change topologySupportReads .left FiniteModel.FiniteAtom.componentA ∧
    topologySupportReads .right FiniteModel.FiniteAtom.componentA at hread
  simpa [topologySupportReads] using hread.2

private theorem topology_right_not_le_overlap :
    ¬ topologySite.contextPreorder.le
      topologyRightObject.ctx topologyOverlapObject.ctx := by
  rintro ⟨f, hf⟩
  have hread := hf.1 (support := PUnit.unit)
    (atom := FiniteModel.FiniteAtom.componentB)
    (show topologySupportReads .right
      FiniteModel.FiniteAtom.componentB by rfl)
  change topologySupportReads .left FiniteModel.FiniteAtom.componentB ∧
    topologySupportReads .right FiniteModel.FiniteAtom.componentB at hread
  simpa [topologySupportReads] using hread.1

/-- The selected overlap and branches form a strict diamond below the base. -/
theorem topologyStrictDiamond :
    topologySite.contextPreorder.le
        topologyOverlapObject.ctx topologyLeftObject.ctx ∧
      topologySite.contextPreorder.le
        topologyOverlapObject.ctx topologyRightObject.ctx ∧
      topologySite.contextPreorder.le
        topologyLeftObject.ctx topologyBase.ctx ∧
      topologySite.contextPreorder.le
        topologyRightObject.ctx topologyBase.ctx ∧
      ¬ topologySite.contextPreorder.le
        topologyLeftObject.ctx topologyRightObject.ctx ∧
      ¬ topologySite.contextPreorder.le
        topologyRightObject.ctx topologyLeftObject.ctx ∧
      ¬ topologySite.contextPreorder.le
        topologyBase.ctx topologyLeftObject.ctx ∧
      ¬ topologySite.contextPreorder.le
        topologyBase.ctx topologyRightObject.ctx ∧
      ¬ topologySite.contextPreorder.le
        topologyLeftObject.ctx topologyOverlapObject.ctx ∧
      ¬ topologySite.contextPreorder.le
        topologyRightObject.ctx topologyOverlapObject.ctx := by
  refine ⟨Site.productContextFiniteMeet.meet_le_left _ _,
    Site.productContextFiniteMeet.meet_le_right _ _,
    topology_left_le_base, topology_right_le_base,
    topology_left_not_le_right, topology_right_not_le_left,
    topology_base_not_le_left, topology_base_not_le_right,
    topology_left_not_le_overlap, topology_right_not_le_overlap⟩

/-- Auxiliary base used to separate the two generated topologies. -/
def topologyAuxBase : topologySite.category :=
  Site.ContextCategoryObject.of topologyContextPreorder (topologyContext .auxBase)

/-- Strict auxiliary patch below the auxiliary base. -/
def topologyAuxPatch : topologySite.category :=
  Site.ContextCategoryObject.of topologyContextPreorder (topologyContext .auxPatch)

/-- The strict auxiliary-patch inclusion into the auxiliary base. -/
noncomputable def topologyAuxInclusion : topologyAuxPatch ⟶ topologyAuxBase :=
  homOfLE topology_auxPatch_le_auxBase

private def topologyLeftAuxOverlapContext : Site.ArchCtx FiniteModel.object :=
  topologyOverlap.overlap (topologyContext .base)
    (topologyContext .left) (topologyContext .auxBase)

private def topologyRightAuxOverlapContext : Site.ArchCtx FiniteModel.object :=
  topologyOverlap.overlap (topologyContext .base)
    (topologyContext .right) (topologyContext .auxBase)

/-- The actual meet overlap of the left branch and the auxiliary base. -/
def topologyLeftAuxOverlap : topologySite.category :=
  Site.ContextCategoryObject.of topologyContextPreorder
    topologyLeftAuxOverlapContext

/-- The actual meet overlap of the right branch and the auxiliary base. -/
def topologyRightAuxOverlap : topologySite.category :=
  Site.ContextCategoryObject.of topologyContextPreorder
    topologyRightAuxOverlapContext

theorem topologyLeftAuxOverlap_eq :
    topologySite.overlap.overlap topologyBase.ctx
        topologyLeftObject.ctx topologyAuxBase.ctx =
      topologyLeftAuxOverlap.ctx := rfl

theorem topologyRightAuxOverlap_eq :
    topologySite.overlap.overlap topologyBase.ctx
        topologyRightObject.ctx topologyAuxBase.ctx =
      topologyRightAuxOverlap.ctx := rfl

private theorem topology_left_not_le_auxBase :
    ¬ topologySite.contextPreorder.le
      topologyLeftObject.ctx topologyAuxBase.ctx := by
  rintro ⟨f, hf⟩
  have h := hf.2.2.1 (observable := PUnit.unit) trivial
  simpa [topologyLeftObject, topologyAuxBase, topologyContext,
    topologyObservableReads] using h

private theorem topology_right_not_le_auxBase :
    ¬ topologySite.contextPreorder.le
      topologyRightObject.ctx topologyAuxBase.ctx := by
  rintro ⟨f, hf⟩
  have h := hf.2.2.1 (observable := PUnit.unit) trivial
  simpa [topologyRightObject, topologyAuxBase, topologyContext,
    topologyObservableReads] using h

private theorem topology_left_not_le_auxPatch :
    ¬ topologySite.contextPreorder.le
      topologyLeftObject.ctx topologyAuxPatch.ctx := by
  rintro ⟨f, hf⟩
  have h := hf.2.2.1 (observable := PUnit.unit) trivial
  simpa [topologyLeftObject, topologyAuxPatch, topologyContext,
    topologyObservableReads] using h

private theorem topology_right_not_le_auxPatch :
    ¬ topologySite.contextPreorder.le
      topologyRightObject.ctx topologyAuxPatch.ctx := by
  rintro ⟨f, hf⟩
  have h := hf.2.2.1 (observable := PUnit.unit) trivial
  simpa [topologyRightObject, topologyAuxPatch, topologyContext,
    topologyObservableReads] using h

private theorem topologyOverlapObservableFalse
    (observable : topologyOverlapObject.ctx.Observable) :
    ¬ topologyOverlapObject.ctx.minimal.observableReads observable := by
  rcases observable with observable | observable
  · change topologyObservableReads .left observable → False
    exact id
  · change topologyObservableReads .right observable → False
    exact id

private theorem topology_overlap_not_le_auxBase :
    ¬ topologySite.contextPreorder.le
      topologyOverlapObject.ctx topologyAuxBase.ctx := by
  rintro ⟨f, hf⟩
  have h := hf.2.2.1 (observable := PUnit.unit) trivial
  exact topologyOverlapObservableFalse _ h

private theorem topology_overlap_not_le_auxPatch :
    ¬ topologySite.contextPreorder.le
      topologyOverlapObject.ctx topologyAuxPatch.ctx := by
  rintro ⟨f, hf⟩
  have h := hf.2.2.1 (observable := PUnit.unit) trivial
  exact topologyOverlapObservableFalse _ h

theorem topologyAuxOffDiamond :
    (¬ topologySite.contextPreorder.le
        topologyLeftObject.ctx topologyAuxBase.ctx) ∧
      (¬ topologySite.contextPreorder.le
        topologyRightObject.ctx topologyAuxBase.ctx) ∧
      (¬ topologySite.contextPreorder.le
        topologyAuxBase.ctx topologyLeftObject.ctx) ∧
      (¬ topologySite.contextPreorder.le
        topologyAuxBase.ctx topologyRightObject.ctx) ∧
      (¬ topologySite.contextPreorder.le
        topologyLeftObject.ctx topologyAuxPatch.ctx) ∧
      (¬ topologySite.contextPreorder.le
        topologyRightObject.ctx topologyAuxPatch.ctx) ∧
      (¬ topologySite.contextPreorder.le
        topologyAuxPatch.ctx topologyLeftObject.ctx) ∧
      (¬ topologySite.contextPreorder.le
        topologyAuxPatch.ctx topologyRightObject.ctx) ∧
      (¬ topologySite.contextPreorder.le
        topologyOverlapObject.ctx topologyAuxBase.ctx) ∧
      (¬ topologySite.contextPreorder.le
        topologyAuxBase.ctx topologyOverlapObject.ctx) ∧
      (¬ topologySite.contextPreorder.le
        topologyOverlapObject.ctx topologyAuxPatch.ctx) ∧
      (¬ topologySite.contextPreorder.le
        topologyAuxPatch.ctx topologyOverlapObject.ctx) := by
  refine ⟨topology_left_not_le_auxBase,
    topology_right_not_le_auxBase, ?_, ?_,
    topology_left_not_le_auxPatch, topology_right_not_le_auxPatch,
    ?_, ?_, topology_overlap_not_le_auxBase, ?_,
    topology_overlap_not_le_auxPatch, ?_⟩
  · apply topology_not_le_of_atom .auxBase .left
      FiniteModel.FiniteAtom.componentB
    · simp [topologySupportReads]
    · simp [topologySupportReads]
  · apply topology_not_le_of_atom .auxBase .right
      FiniteModel.FiniteAtom.componentA
    · simp [topologySupportReads]
    · simp [topologySupportReads]
  · apply topology_not_le_of_atom .auxPatch .left
      FiniteModel.FiniteAtom.componentB
    · simp [topologySupportReads]
    · simp [topologySupportReads]
  · apply topology_not_le_of_atom .auxPatch .right
      FiniteModel.FiniteAtom.componentA
    · simp [topologySupportReads]
    · simp [topologySupportReads]
  · rintro ⟨f, hf⟩
    have hread := hf.1 (support := PUnit.unit)
      (atom := FiniteModel.FiniteAtom.componentA)
      (show topologySupportReads .auxBase
        FiniteModel.FiniteAtom.componentA by simp [topologySupportReads])
    change topologySupportReads .left FiniteModel.FiniteAtom.componentA ∧
      topologySupportReads .right FiniteModel.FiniteAtom.componentA at hread
    simpa [topologySupportReads] using hread.2
  · rintro ⟨f, hf⟩
    have hread := hf.1 (support := PUnit.unit)
      (atom := FiniteModel.FiniteAtom.componentA)
      (show topologySupportReads .auxPatch
        FiniteModel.FiniteAtom.componentA by simp [topologySupportReads])
    change topologySupportReads .left FiniteModel.FiniteAtom.componentA ∧
      topologySupportReads .right FiniteModel.FiniteAtom.componentA at hread
    simpa [topologySupportReads] using hread.2

theorem topologyLeftAuxOverlap_not_le_auxPatch :
    ¬ topologySite.contextPreorder.le
      topologyLeftAuxOverlap.ctx topologyAuxPatch.ctx := by
  rintro ⟨f, hf⟩
  have haxis := hf.2.1 (axis := (PUnit.unit, PUnit.unit))
    (by
      change topologyAxisReads .left ∧ topologyAxisReads .auxBase
      simp [topologyAxisReads])
  change topologyAxisReads .auxPatch at haxis
  exact haxis rfl

theorem topologyRightAuxOverlap_not_le_auxPatch :
    ¬ topologySite.contextPreorder.le
      topologyRightAuxOverlap.ctx topologyAuxPatch.ctx := by
  rintro ⟨f, hf⟩
  have haxis := hf.2.1 (axis := (PUnit.unit, PUnit.unit))
    (by
      change topologyAxisReads .right ∧ topologyAxisReads .auxBase
      simp [topologyAxisReads])
  change topologyAxisReads .auxPatch at haxis
  exact haxis rfl

/-- The sieve generated by the strict auxiliary-patch inclusion. -/
noncomputable def topologyAuxSieve : Sieve topologyAuxBase :=
  Sieve.generate (Presieve.singleton topologyAuxInclusion)

@[simp] theorem topologyAuxSieve_eq_generateSingleton :
    topologyAuxSieve =
      Sieve.generate (Presieve.singleton topologyAuxInclusion) := rfl

/-- The precoverage whose sole selected cover is the auxiliary singleton cover. -/
noncomputable def topologyAuxPrecoverage : Precoverage topologySite.category where
  coverings X := {R | ∃ _h : X = topologyAuxBase,
    HEq R (Presieve.singleton topologyAuxInclusion)}

theorem topologyAuxPrecoverage_mem_iff
    {X : topologySite.category} {R : Presieve X} :
    R ∈ topologyAuxPrecoverage X ↔
      ∃ _h : X = topologyAuxBase,
        HEq R (Presieve.singleton topologyAuxInclusion) := Iff.rfl

private inductive TopologyCoarseCoverIndex where
  | left
  | right

private def topologyCoarseCoverPatch :
    TopologyCoarseCoverIndex → Site.ArchCtx FiniteModel.object
  | .left => topologyContext .left
  | .right => topologyContext .right

/-- The selected two-branch cover generating the coarse topology. -/
noncomputable def topologyCoarseCover :
    Site.AATCoverageFamily topologySite.requirements
      topologySite.overlap topologyBase where
  Index := TopologyCoarseCoverIndex
  patch := topologyCoarseCoverPatch
  inclusion := by
    intro i
    cases i
    · exact topology_left_le_base
    · exact topology_right_le_base
  admissible := {
    atomSupportCoverage := by
      intro atom h
      rcases h with rfl | rfl
      · exact ⟨.left, Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨.right, Or.inr ⟨rfl, rfl⟩⟩
    equationCoordinateCoverage := by
      intro coordinate h
      exact Or.inl ⟨.left, trivial⟩
    violationWitnessCoverage := by
      intro witness h
      exact Or.inl ⟨.left, trivial⟩
    signatureAxisCoverage := by
      intro axis h
      exact ⟨.left, Or.inl rfl⟩
    boundaryCoverage := by
      intro i j
      rfl
    nonGeneration := by
      intro i support atom h
      simpa [topologyBase, topologyContext, topologySupportReads] using h
  }

private def topologyFineCoverPatch : Bool × Bool →
    Site.ArchCtx FiniteModel.object
  | (false, _) => topologyContext .left
  | (true, _) => topologyContext .right

/-- A four-index presentation of the same presieve as the coarse cover. -/
noncomputable def topologyFineCover :
    Site.AATCoverageFamily topologySite.requirements
      topologySite.overlap topologyBase where
  Index := Bool × Bool
  patch := topologyFineCoverPatch
  inclusion := by
    rintro ⟨i, duplicate⟩
    cases i
    · exact topology_left_le_base
    · exact topology_right_le_base
  admissible := {
    atomSupportCoverage := by
      intro atom h
      rcases h with rfl | rfl
      · exact ⟨(false, false), Or.inl ⟨rfl, rfl⟩⟩
      · exact ⟨(true, false), Or.inr ⟨rfl, rfl⟩⟩
    equationCoordinateCoverage := by
      intro coordinate h
      exact Or.inl ⟨(false, false), trivial⟩
    violationWitnessCoverage := by
      intro witness h
      exact Or.inl ⟨(false, false), trivial⟩
    signatureAxisCoverage := by
      intro axis h
      exact ⟨(false, false), Or.inl rfl⟩
    boundaryCoverage := by
      intro i j
      rfl
    nonGeneration := by
      rintro ⟨i, duplicate⟩ support atom h
      simpa [topologyBase, topologyContext, topologySupportReads] using h
  }

/-- Identification of the two coarse-cover indices with `Bool`. -/
def topologyCoarseCoverIndexEquiv : topologyCoarseCover.Index ≃ Bool where
  toFun
    | .left => false
    | .right => true
  invFun
    | false => .left
    | true => .right
  left_inv i := by cases i <;> rfl
  right_inv i := by cases i <;> rfl

/-- Identification of the duplicated fine-cover indices with `Bool × Bool`. -/
def topologyFineCoverIndexEquiv : topologyFineCover.Index ≃ Bool × Bool :=
  Equiv.refl _

theorem topologyCoarseCover_twoBranches :
    ∃ i j : topologyCoarseCover.Index,
      i ≠ j ∧
        topologyCoarseCover.patch i = topologyLeftObject.ctx ∧
        topologyCoarseCover.patch j = topologyRightObject.ctx := by
  exact ⟨.left, .right, by simp, rfl, rfl⟩

theorem topologyCoarseCover_presieve_eq_fineCover :
    topologyCoarseCover.presieve = topologyFineCover.presieve := by
  apply le_antisymm
  · intro Y f h
    cases h with
    | mk i =>
        cases i
        · exact Presieve.ofArrows.mk (false, false)
        · exact Presieve.ofArrows.mk (true, false)
  · intro Y f h
    cases h with
    | mk i =>
        rcases i with ⟨i, duplicate⟩
        cases i
        · exact Presieve.ofArrows.mk TopologyCoarseCoverIndex.left
        · exact Presieve.ofArrows.mk TopologyCoarseCoverIndex.right

/-- The precoverage whose sole selected cover is the coarse two-branch cover. -/
noncomputable def topologyCoarsePrecoverage :
    Precoverage topologySite.category where
  coverings X := {R | ∃ _h : X = topologyBase,
    HEq R topologyCoarseCover.presieve}

theorem topologyCoarsePrecoverage_mem_iff
    {X : topologySite.category} {R : Presieve X} :
    R ∈ topologyCoarsePrecoverage X ↔
      ∃ _h : X = topologyBase,
        HEq R topologyCoarseCover.presieve := Iff.rfl

/-- The explicit refinement from the duplicated fine cover to the coarse cover. -/
noncomputable def topologyCoarseToFineCover :
    Site.AATCoverageFamily.Refinement
      topologyCoarseCover topologyFineCover where
  indexMap i := if i.1 then .right else .left
  factor := by
    rintro ⟨i, duplicate⟩
    cases i <;> exact topologySite.contextPreorder.refl _
  factor_triangle := by
    intro i
    exact Subsingleton.elim _ _

theorem topologyCoarseToFineCover_not_bijective :
    ¬ Function.Bijective topologyCoarseToFineCover.indexMap := by
  intro h
  have heq := h.1 (show
    topologyCoarseToFineCover.indexMap (false, false) =
      topologyCoarseToFineCover.indexMap (false, true) by rfl)
  exact (show (false, false) ≠ (false, true) by simp) heq

private theorem topology_admissibleCover_has_left
    {Z : topologySite.category}
    (F : Site.AATCoverageFamily topologySite.requirements
      topologySite.overlap Z) :
    ∃ i : F.Index, F.patch i = topologyContext .left := by
  rcases F.admissible.atomSupportCoverage
      FiniteModel.FiniteAtom.componentA (Or.inl rfl) with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  rcases hi with hi | hi
  · exact hi.1
  · exact False.elim (by simpa using hi.2)

private theorem topology_admissibleCover_has_right
    {Z : topologySite.category}
    (F : Site.AATCoverageFamily topologySite.requirements
      topologySite.overlap Z) :
    ∃ i : F.Index, F.patch i = topologyContext .right := by
  rcases F.admissible.atomSupportCoverage
      FiniteModel.FiniteAtom.componentB (Or.inr rfl) with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  rcases hi with hi | hi
  · exact False.elim (by simpa using hi.2)
  · exact hi.1

private theorem topology_admissibleCover_base_eq
    {Z : topologySite.category}
    (F : Site.AATCoverageFamily topologySite.requirements
      topologySite.overlap Z) : Z = topologyBase := by
  rcases topology_admissibleCover_has_left F with ⟨i, hi⟩
  have hbase := F.admissible.boundaryCoverage i i
  change Z.ctx = topologyContext .base at hbase
  cases Z
  cases hbase
  rfl

private theorem topologyCoarseCover_presieve_le_admissible
    (F : Site.AATCoverageFamily topologySite.requirements
      topologySite.overlap topologyBase) :
    topologyCoarseCover.presieve ≤ F.presieve := by
  intro Y f hf
  cases hf with
  | mk i =>
      cases i with
      | left =>
          rcases topology_admissibleCover_has_left F with ⟨j, hj⟩
          let hobj := (congrArg
            (Site.ContextCategoryObject.of topologyContextPreorder) hj).symm
          exact Presieve.ofArrows.mk' j hobj (Subsingleton.elim _ _)
      | right =>
          rcases topology_admissibleCover_has_right F with ⟨j, hj⟩
          let hobj := (congrArg
            (Site.ContextCategoryObject.of topologyContextPreorder) hj).symm
          exact Presieve.ofArrows.mk' j hobj (Subsingleton.elim _ _)

private theorem topologySite_le_coarseGenerated :
    topologySite.topology ≤ topologyCoarsePrecoverage.toGrothendieck := by
  intro Z R hR
  change (Site.admissiblePrecoverage topologySite.requirements
    topologySite.overlap).Saturate Z R at hR
  induction hR with
  | of Z P hP =>
      rcases hP with ⟨F, rfl⟩
      have hbase := topology_admissibleCover_base_eq F
      subst Z
      have hcover : Sieve.generate topologyCoarseCover.presieve ∈
          topologyCoarsePrecoverage.toGrothendieck topologyBase :=
        Precoverage.generate_mem_toGrothendieck ⟨rfl, HEq.rfl⟩
      exact topologyCoarsePrecoverage.toGrothendieck.superset_covering
        (Sieve.generate_mono
          (topologyCoarseCover_presieve_le_admissible F)) hcover
  | top Z => simp
  | pullback Z S hS Y f ih =>
      exact topologyCoarsePrecoverage.toGrothendieck.pullback_stable f ih
  | transitive Z S R hS hlocal ihS ihlocal =>
      exact topologyCoarsePrecoverage.toGrothendieck.transitive ihS R ihlocal

private theorem topologyCoarseGenerated_le_site :
    topologyCoarsePrecoverage.toGrothendieck ≤ topologySite.topology := by
  intro Z R hR
  change topologyCoarsePrecoverage.Saturate Z R at hR
  induction hR with
  | of Z P hP =>
      rcases hP with ⟨hZ, hP⟩
      subst Z
      have hP : P = topologyCoarseCover.presieve := eq_of_heq hP
      subst P
      exact Site.AATCoverageFamily.mem_topology topologyCoarseCover
  | top Z => simp
  | pullback Z S hS Y f ih =>
      exact topologySite.topology.pullback_stable f ih
  | transitive Z S R hS hlocal ihS ihlocal =>
      exact topologySite.topology.transitive ihS R ihlocal

theorem topologySite_topology_eq_coarseGenerated :
    topologySite.topology = topologyCoarsePrecoverage.toGrothendieck :=
  le_antisymm topologySite_le_coarseGenerated topologyCoarseGenerated_le_site

private theorem topologySite_contains_of_hom_to_left
    {X : topologySite.category} (hX : X ⟶ topologyLeftObject) :
    ∀ {Z : topologySite.category} (f : X ⟶ Z)
      {R : Sieve Z}, R ∈ topologySite.topology Z → R f := by
  intro Z f R hR
  change (Site.admissiblePrecoverage topologySite.requirements
    topologySite.overlap).Saturate Z R at hR
  induction hR with
  | of Z P hP =>
      rcases hP with ⟨F, rfl⟩
      rcases topology_admissibleCover_has_left F with ⟨i, hi⟩
      let g : X ⟶ Site.ContextCategoryObject.of topologyContextPreorder
          (F.patch i) :=
        hX ≫ eqToHom (congrArg
          (Site.ContextCategoryObject.of topologyContextPreorder) hi).symm
      have hinclusion : (Sieve.generate F.presieve)
          (homOfLE (F.inclusion i)) :=
        Sieve.le_generate F.presieve _ (Presieve.ofArrows.mk i)
      have hcomp := (Sieve.generate F.presieve).downward_closed
        hinclusion g
      convert hcomp using 1
  | top Z => simp
  | pullback Z S hS Y g ih =>
      change S (f ≫ g)
      exact ih (f ≫ g)
  | transitive Z S R hS hlocal ihS ihlocal =>
      have hSf : S f := ihS f
      have hRf : (R.pullback f) (𝟙 X) := ihlocal hSf (𝟙 X)
      simpa using hRf

/-- Coarse topology generated by the selected two-branch precoverage. -/
noncomputable def coarseTopology :
    GrothendieckTopology topologySite.category := topologySite.topology

@[simp] theorem coarseTopology_eq_site :
    coarseTopology = topologySite.topology := rfl

/-- The terminal morphism from the auxiliary base to the topology base. -/
noncomputable def topologyAuxBaseToBase : topologyAuxBase ⟶ topologyBase :=
  topologyBaseIsTerminal.from topologyAuxBase

/-- The coarse covering sieve pulled back from the base to the auxiliary base. -/
noncomputable def topologyCoarsePullbackAtAuxBase : Sieve topologyAuxBase :=
  (Sieve.generate topologyCoarseCover.presieve).pullback
    topologyAuxBaseToBase

theorem topologyCoarseCover_mem_coarseTopology :
    Sieve.generate topologyCoarseCover.presieve ∈
      coarseTopology topologyBase := by
  exact Site.AATCoverageFamily.mem_topology topologyCoarseCover

theorem topologyCoarsePullbackAtAuxBase_mem :
    topologyCoarsePullbackAtAuxBase ∈ coarseTopology topologyAuxBase :=
  coarseTopology.pullback_stable topologyAuxBaseToBase
    topologyCoarseCover_mem_coarseTopology

private noncomputable def topologyLeftAuxToLeft :
    topologyLeftAuxOverlap ⟶ topologyLeftObject :=
  homOfLE (Site.productContextFiniteMeet.meet_le_left _ _)

private noncomputable def topologyLeftAuxToAuxBase :
    topologyLeftAuxOverlap ⟶ topologyAuxBase :=
  homOfLE (Site.productContextFiniteMeet.meet_le_right _ _)

private theorem topologyLeftAuxToAuxBase_mem_coarsePullback :
    topologyCoarsePullbackAtAuxBase topologyLeftAuxToAuxBase := by
  change Sieve.generate topologyCoarseCover.presieve
    (topologyLeftAuxToAuxBase ≫ topologyAuxBaseToBase)
  have hinclusion : Sieve.generate topologyCoarseCover.presieve
      (homOfLE (topologyCoarseCover.inclusion
        TopologyCoarseCoverIndex.left)) :=
    Sieve.le_generate topologyCoarseCover.presieve _
      (Presieve.ofArrows.mk TopologyCoarseCoverIndex.left)
  have hcomp := (Sieve.generate topologyCoarseCover.presieve).downward_closed
    hinclusion topologyLeftAuxToLeft
  convert hcomp using 1

private theorem topologyLeftAuxToAuxBase_not_mem_auxSieve :
    ¬ topologyAuxSieve topologyLeftAuxToAuxBase := by
  rintro ⟨Y, g, inclusion, hinclusion, hcomp⟩
  cases hinclusion
  apply topologyLeftAuxOverlap_not_le_auxPatch
  exact leOfHom g

theorem topologyCoarsePullbackAtAuxBase_not_le_auxSieve :
    ¬ topologyCoarsePullbackAtAuxBase ≤ topologyAuxSieve := by
  intro hle
  exact topologyLeftAuxToAuxBase_not_mem_auxSieve
    (hle _ topologyLeftAuxToAuxBase_mem_coarsePullback)

/-- Fine topology obtained by adjoining the strict auxiliary singleton cover. -/
noncomputable def fineTopology :
    GrothendieckTopology topologySite.category :=
  coarseTopology ⊔ topologyAuxPrecoverage.toGrothendieck

@[simp] theorem fineTopology_eq_coarse_sup_aux :
    fineTopology =
      coarseTopology ⊔ topologyAuxPrecoverage.toGrothendieck := rfl

private theorem topologyAuxGenerated_contains_of_hom_to_patch
    {X : topologySite.category} (hX : X ⟶ topologyAuxPatch) :
    ∀ {Z : topologySite.category} (f : X ⟶ Z)
      {R : Sieve Z},
      R ∈ topologyAuxPrecoverage.toGrothendieck Z → R f := by
  intro Z f R hR
  change topologyAuxPrecoverage.Saturate Z R at hR
  induction hR with
  | of Z P hP =>
      rcases hP with ⟨hZ, hP⟩
      subst Z
      have hP : P = Presieve.singleton topologyAuxInclusion := eq_of_heq hP
      subst P
      exact ⟨topologyAuxPatch, hX, topologyAuxInclusion,
        Presieve.singleton.mk, Subsingleton.elim _ _⟩
  | top Z => simp
  | pullback Z S hS Y g ih =>
      change S (f ≫ g)
      exact ih (f ≫ g)
  | transitive Z S R hS hlocal ihS ihlocal =>
      have hSf : S f := ihS f
      have hRf : (R.pullback f) (𝟙 X) := ihlocal hSf (𝟙 X)
      simpa using hRf

private def topologyPointObject : topologySite.category :=
  Site.ContextCategoryObject.of topologyContextPreorder
    (Site.productContext topologyLeftObject.ctx topologyAuxPatch.ctx)

private noncomputable def topologyPointToLeft :
    topologyPointObject ⟶ topologyLeftObject :=
  homOfLE (Site.productContextFiniteMeet.meet_le_left _ _)

private noncomputable def topologyPointToAuxPatch :
    topologyPointObject ⟶ topologyAuxPatch :=
  homOfLE (Site.productContextFiniteMeet.meet_le_right _ _)

private noncomputable def topologyPointGrothendieckTopology :
    GrothendieckTopology topologySite.category where
  sieves Z := {R | ∀ f : topologyPointObject ⟶ Z, R f}
  top_mem' := by
    intro Z f
    trivial
  pullback_stable' := by
    intro X Y R g hR f
    exact hR (f ≫ g)
  transitive' := by
    intro X S hS R hlocal f
    have hSf := hS f
    have hlocalf := hlocal hSf (𝟙 topologyPointObject)
    simpa using hlocalf

private theorem topologyFine_le_pointTopology :
    fineTopology ≤ topologyPointGrothendieckTopology := by
  apply sup_le
  · intro Z R hR f
    exact topologySite_contains_of_hom_to_left topologyPointToLeft f hR
  · intro Z R hR f
    exact topologyAuxGenerated_contains_of_hom_to_patch
      topologyPointToAuxPatch f hR

theorem fineTopology_ne_top : fineTopology ≠ ⊤ := by
  intro htop
  have hbot : (⊥ : Sieve topologyBase) ∈ fineTopology topologyBase := by
    rw [htop]
    simp
  have hpoint := topologyFine_le_pointTopology topologyBase hbot
    (topologyBaseIsTerminal.from topologyPointObject)
  exact hpoint

/-- The degree in which the topology-change Čech map is tested. -/
def nonzeroDegree : Nat := 1

noncomputable instance topologyCoarseAddCommGrpHasSheafify :
    HasSheafify coarseTopology AddCommGrpCat.{1} := by infer_instance

noncomputable instance topologyFineAddCommGrpHasSheafify :
    HasSheafify fineTopology AddCommGrpCat.{1} := by infer_instance

noncomputable instance topologyCoarseAddCommGrpHasExt :
    HasExt.{2} (Sheaf coarseTopology AddCommGrpCat.{1}) :=
  HasExt.standard (Sheaf coarseTopology AddCommGrpCat.{1})

noncomputable instance topologyFineAddCommGrpHasExt :
    HasExt.{2} (Sheaf fineTopology AddCommGrpCat.{1}) :=
  HasExt.standard (Sheaf fineTopology AddCommGrpCat.{1})

theorem topologyAuxSieve_mem_fineTopology :
    topologyAuxSieve ∈ fineTopology topologyAuxBase := by
  apply (show topologyAuxPrecoverage.toGrothendieck ≤ fineTopology from
    le_sup_right)
  exact Precoverage.generate_mem_toGrothendieck ⟨rfl, HEq.rfl⟩

theorem topologyAuxSieve_not_mem_coarseTopology :
    topologyAuxSieve ∉ coarseTopology topologyAuxBase := by
  intro hcover
  have hmem := topologySite_contains_of_hom_to_left
    topologyLeftAuxToLeft topologyLeftAuxToAuxBase hcover
  exact topologyLeftAuxToAuxBase_not_mem_auxSieve hmem

/-- The canonical cover selection induced by the coarse-to-fine topology order. -/
noncomputable def coarseFineTopologyRefinement :
    CoverageTopologyRefinement coarseTopology fineTopology where
  refineCover X R hR := ⟨R,
    (show coarseTopology ≤ fineTopology from le_sup_left) X hR, le_rfl⟩

theorem coarseFineTopology_strict : coarseTopology ≠ fineTopology := by
  intro heq
  exact topologyAuxSieve_not_mem_coarseTopology
    (heq ▸ topologyAuxSieve_mem_fineTopology)

theorem coarseFineTopologyRefinement_selects_fineCover :
    (coarseFineTopologyRefinement.refineCover
      topologyBase (Sieve.generate topologyCoarseCover.presieve)
      topologyCoarseCover_mem_coarseTopology).1 =
        Sieve.generate topologyFineCover.presieve := by
  rw [show (coarseFineTopologyRefinement.refineCover
      topologyBase (Sieve.generate topologyCoarseCover.presieve)
      topologyCoarseCover_mem_coarseTopology).1 =
        Sieve.generate topologyCoarseCover.presieve by rfl]
  rw [topologyCoarseCover_presieve_eq_fineCover]

theorem topologyFineCover_mem_fineTopology :
    Sieve.generate topologyFineCover.presieve ∈ fineTopology topologyBase := by
  rw [← topologyCoarseCover_presieve_eq_fineCover]
  exact (show coarseTopology ≤ fineTopology from le_sup_left)
    topologyBase topologyCoarseCover_mem_coarseTopology

/-- A degree-dependent simplex map that cannot arise from one refinement index map. -/
noncomputable def topologyBrokenFaceMap :
    ∀ n,
      (Cohomology.canonicalCoverRelative topologyFineCover).simplex n →
        (Cohomology.canonicalCoverRelative topologyCoarseCover).simplex n
  | 0 => fun _ _ => .left
  | _ + 1 => fun _ _ => .right

theorem topologyBrokenFaceMap_not_refinement :
    ¬ ∃ r : Site.AATCoverageFamily.Refinement
        topologyCoarseCover topologyFineCover,
      r.simplexMap = topologyBrokenFaceMap := by
  rintro ⟨r, hr⟩
  let selected : topologyFineCover.Index := (false, false)
  let σ₀ : (Cohomology.canonicalCoverRelative topologyFineCover).simplex 0 :=
    fun _ => selected
  let σ₁ : (Cohomology.canonicalCoverRelative topologyFineCover).simplex 1 :=
    fun _ => selected
  have hleft : r.indexMap selected = TopologyCoarseCoverIndex.left := by
    have h := congrFun (congrFun (congrFun hr 0) σ₀) (0 : Fin 1)
    simpa [Site.AATCoverageFamily.Refinement.simplexMap,
      topologyBrokenFaceMap, σ₀] using h
  have hright : r.indexMap selected = TopologyCoarseCoverIndex.right := by
    have h := congrFun (congrFun (congrFun hr 1) σ₁) (0 : Fin 2)
    simpa [Site.AATCoverageFamily.Refinement.simplexMap,
      topologyBrokenFaceMap, σ₁] using h
  rw [hleft] at hright
  exact TopologyCoarseCoverIndex.noConfusion hright

private def TopologyNoMarkerReads
    (W : Site.ArchCtx FiniteModel.object) : Prop :=
  (∀ support : W.Support,
      ¬ W.minimal.supportReads support FiniteModel.FiniteAtom.componentA) ∧
    (∀ support : W.Support,
      ¬ W.minimal.supportReads support FiniteModel.FiniteAtom.componentB)

private theorem topologyNoMarkerReads_of_le
    {W V : Site.ArchCtx FiniteModel.object}
    (h : topologyContextPreorder.le W V)
    (hV : TopologyNoMarkerReads V) : TopologyNoMarkerReads W := by
  let f := topologyContextPreorder.readableMorphism h
  have hf := topologyContextPreorder.readableMorphism_isRestriction h
  constructor
  · intro support hread
    exact hV.1 (f.supportMap support) (hf.1 hread)
  · intro support hread
    exact hV.2 (f.supportMap support) (hf.1 hread)

private noncomputable def topologyCoefficientSubmodule
    (W : Site.ArchCtx FiniteModel.object) :
    Submodule (ZMod 2) (ZMod 2) := by
  classical
  exact if TopologyNoMarkerReads W then ⊤ else ⊥

private theorem topologyCoefficientSubmodule_mono
    {W V : Site.ArchCtx FiniteModel.object}
    (h : topologyContextPreorder.le W V) :
    topologyCoefficientSubmodule V ≤ topologyCoefficientSubmodule W := by
  by_cases hV : TopologyNoMarkerReads V
  · have hW := topologyNoMarkerReads_of_le h hV
    simp [topologyCoefficientSubmodule, hV, hW]
  · simp [topologyCoefficientSubmodule, hV]

private noncomputable def topologyCoefficientModulePresheaf :
    topologySite.categoryᵒᵖ ⥤ ModuleCat.{0} (ZMod 2) where
  obj X := ModuleCat.of (ZMod 2) (topologyCoefficientSubmodule X.unop.ctx)
  map {X Y} f := ModuleCat.ofHom
    (Submodule.inclusion (topologyCoefficientSubmodule_mono (leOfHom f.unop)))
  map_id X := by
    apply ModuleCat.hom_ext
    ext x
    rfl
  map_comp {X Y Z} f g := by
    apply ModuleCat.hom_ext
    ext x
    rfl

private noncomputable def topologyCoefficientPresheaf :
    topologySite.categoryᵒᵖ ⥤ AddCommGrpCat.{0} :=
  topologyCoefficientModulePresheaf ⋙
    forget₂ (ModuleCat.{0} (ZMod 2)) AddCommGrpCat.{0}

private theorem topologyNoMarkerReads_product_left
    {W V : Site.ArchCtx FiniteModel.object}
    (hW : TopologyNoMarkerReads W) :
    TopologyNoMarkerReads (Site.productContext W V) := by
  constructor
  · rintro ⟨w, v⟩ h
    exact hW.1 w h.1
  · rintro ⟨w, v⟩ h
    exact hW.2 w h.1

private theorem topologyProductWithLeft_not_noMarkerReads
    {W : Site.ArchCtx FiniteModel.object} {support : W.Support}
    (hread : W.minimal.supportReads support
      FiniteModel.FiniteAtom.componentA) :
    ¬ TopologyNoMarkerReads
      (Site.productContext W (topologyContext .left)) := by
  intro h
  exact h.1 (support, PUnit.unit)
    ⟨hread, by simp [topologyContext, topologySupportReads]⟩

private theorem topologyProductWithRight_not_noMarkerReads
    {W : Site.ArchCtx FiniteModel.object} {support : W.Support}
    (hread : W.minimal.supportReads support
      FiniteModel.FiniteAtom.componentB) :
    ¬ TopologyNoMarkerReads
      (Site.productContext W (topologyContext .right)) := by
  intro h
  exact h.2 (support, PUnit.unit)
    ⟨hread, by simp [topologyContext, topologySupportReads]⟩

private def topologyProductObject
    (X Y : topologySite.category) : topologySite.category :=
  Site.ContextCategoryObject.of topologyContextPreorder
    (Site.productContext X.ctx Y.ctx)

private noncomputable def topologyProductLeft
    (X Y : topologySite.category) : topologyProductObject X Y ⟶ X :=
  homOfLE (Site.productContextFiniteMeet.meet_le_left X.ctx Y.ctx)

private noncomputable def topologyProductRight
    (X Y : topologySite.category) : topologyProductObject X Y ⟶ Y :=
  homOfLE (Site.productContextFiniteMeet.meet_le_right X.ctx Y.ctx)

private theorem topologyCoefficientPresheaf_isSheaf_ofTypes :
    Presieve.IsSheaf topologySite.topology
      (topologyCoefficientPresheaf ⋙ forget AddCommGrpCat.{0}) := by
  rw [Site.AATSite.topology, Site.AATGrothendieckTopology]
  rw [Precoverage.isSheaf_toGrothendieck_iff]
  intro X Y f R hR
  rcases hR with ⟨F, rfl⟩
  intro family hfamily
  classical
  have hmarker : ∃ i : F.Index,
      topologyCoefficientSubmodule
          (Site.productContext Y.ctx (F.patch i)) =
        topologyCoefficientSubmodule Y.ctx := by
    by_cases hY : TopologyNoMarkerReads Y.ctx
    · rcases topology_admissibleCover_has_left F with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      have hQ := topologyNoMarkerReads_product_left (V := F.patch i) hY
      simp [topologyCoefficientSubmodule, hY, hQ]
    · simp only [TopologyNoMarkerReads, not_and_or, not_forall,
        not_not] at hY
      rcases hY with hA | hB
      · rcases hA with ⟨support, hsupport⟩
        rcases topology_admissibleCover_has_left F with ⟨i, hi⟩
        refine ⟨i, ?_⟩
        have hQ : ¬ TopologyNoMarkerReads
            (Site.productContext Y.ctx (F.patch i)) := by
          rw [hi]
          exact topologyProductWithLeft_not_noMarkerReads hsupport
        have hYnot : ¬ TopologyNoMarkerReads Y.ctx := fun h =>
          h.1 support hsupport
        have hleft : topologyCoefficientSubmodule
            (Site.productContext Y.ctx (F.patch i)) = ⊥ := by
          rw [topologyCoefficientSubmodule, if_neg hQ]
        have hright : topologyCoefficientSubmodule Y.ctx = ⊥ := by
          rw [topologyCoefficientSubmodule, if_neg hYnot]
        rw [hleft, hright]
      · rcases hB with ⟨support, hsupport⟩
        rcases topology_admissibleCover_has_right F with ⟨i, hi⟩
        refine ⟨i, ?_⟩
        have hQ : ¬ TopologyNoMarkerReads
            (Site.productContext Y.ctx (F.patch i)) := by
          rw [hi]
          exact topologyProductWithRight_not_noMarkerReads hsupport
        have hYnot : ¬ TopologyNoMarkerReads Y.ctx := fun h =>
          h.2 support hsupport
        have hleft : topologyCoefficientSubmodule
            (Site.productContext Y.ctx (F.patch i)) = ⊥ := by
          rw [topologyCoefficientSubmodule, if_neg hQ]
        have hright : topologyCoefficientSubmodule Y.ctx = ⊥ := by
          rw [topologyCoefficientSubmodule, if_neg hYnot]
        rw [hleft, hright]
  rcases hmarker with ⟨i, hsubmodule⟩
  let patchObject := Site.ContextCategoryObject.of topologyContextPreorder
    (F.patch i)
  let Q := topologyProductObject Y patchObject
  let q : Q ⟶ Y := topologyProductLeft Y patchObject
  let qpatch : Q ⟶ patchObject := topologyProductRight Y patchObject
  have hq : (Sieve.generate F.presieve).pullback f q := by
    change Sieve.generate F.presieve (q ≫ f)
    have hinclusion : Sieve.generate F.presieve
        (homOfLE (F.inclusion i)) :=
      Sieve.le_generate F.presieve _ (Presieve.ofArrows.mk i)
    have hcomp := (Sieve.generate F.presieve).downward_closed
      hinclusion qpatch
    convert hcomp using 1
  let reference := family q hq
  have reference_mem_Y : reference.1 ∈ topologyCoefficientSubmodule Y.ctx := by
    rw [← hsubmodule]
    exact reference.2
  let global : topologyCoefficientSubmodule Y.ctx :=
    ⟨reference.1, reference_mem_Y⟩
  have hconstant : ∀ {Z : topologySite.category}
      (g : Z ⟶ Y) (hg : (Sieve.generate F.presieve).pullback f g),
      (family g hg).1 = reference.1 := by
    intro Z g hg
    let P := topologyProductObject Z Q
    let pz : P ⟶ Z := topologyProductLeft Z Q
    let pq : P ⟶ Q := topologyProductRight Z Q
    have hcompat := hfamily pz pq hg hq (Subsingleton.elim _ _)
    exact congrArg Subtype.val hcompat
  refine ⟨global, ?_, ?_⟩
  · intro Z g hg
    apply Subtype.ext
    change global.1 = (family g hg).1
    exact (hconstant g hg).symm
  · intro other hother
    apply Subtype.ext
    have hqOther := hother q hq
    have hval := congrArg Subtype.val hqOther
    change other.1 = global.1
    exact hval

/-- Concrete obstruction coefficient concentrated on the selected overlap. -/
noncomputable def topologyObstructionSheaf :
    Cohomology.ObstructionSheaf topologySite :=
  Cohomology.ObstructionSheaf.ofAddCommGrpValued
    topologyCoefficientPresheaf
    ((Site.AATSheafCondition.iff_presieve_isSheaf topologySite _).2
      topologyCoefficientPresheaf_isSheaf_ofTypes)

private theorem topologyCoefficientSubmodule_eq_bot_of_readsA
    (W : Site.ArchCtx FiniteModel.object) (support : W.Support)
    (hread : W.minimal.supportReads support
      FiniteModel.FiniteAtom.componentA) :
    topologyCoefficientSubmodule W = ⊥ := by
  have hnot : ¬ TopologyNoMarkerReads W := fun h => h.1 support hread
  simp [topologyCoefficientSubmodule, hnot]

private theorem topologyCoefficientSubmodule_eq_bot_of_readsB
    (W : Site.ArchCtx FiniteModel.object) (support : W.Support)
    (hread : W.minimal.supportReads support
      FiniteModel.FiniteAtom.componentB) :
    topologyCoefficientSubmodule W = ⊥ := by
  have hnot : ¬ TopologyNoMarkerReads W := fun h => h.2 support hread
  simp [topologyCoefficientSubmodule, hnot]

theorem topologyBaseCoefficient_subsingleton :
    Subsingleton
      ((topologyObstructionSheaf.toAddCommGrpSheaf.val.obj
        (Opposite.op topologyBase) : Type 1)) := by
  change Subsingleton (ULift (topologyCoefficientSubmodule topologyBase.ctx))
  rw [topologyCoefficientSubmodule_eq_bot_of_readsA _ PUnit.unit]
  · infer_instance
  · exact FiniteModel.allFamily_mem _ (by simp)

theorem topologyLeftCoefficient_subsingleton :
    Subsingleton
      ((topologyObstructionSheaf.toAddCommGrpSheaf.val.obj
        (Opposite.op topologyLeftObject) : Type 1)) := by
  change Subsingleton (ULift (topologyCoefficientSubmodule topologyLeftObject.ctx))
  rw [topologyCoefficientSubmodule_eq_bot_of_readsA _ PUnit.unit]
  · infer_instance
  · rfl

theorem topologyRightCoefficient_subsingleton :
    Subsingleton
      ((topologyObstructionSheaf.toAddCommGrpSheaf.val.obj
        (Opposite.op topologyRightObject) : Type 1)) := by
  change Subsingleton (ULift (topologyCoefficientSubmodule topologyRightObject.ctx))
  rw [topologyCoefficientSubmodule_eq_bot_of_readsB _ PUnit.unit]
  · infer_instance
  · rfl

private theorem topologyOverlap_noMarkerReads :
    TopologyNoMarkerReads topologyOverlapObject.ctx := by
  constructor <;> rintro ⟨leftSupport, rightSupport⟩ hread
  · simpa [topologyContext, topologySupportReads] using hread.2
  · simpa [topologyContext, topologySupportReads] using hread.1

private theorem topologyReverseOverlap_noMarkerReads :
    TopologyNoMarkerReads
      (Site.productContext (topologyContext .right) (topologyContext .left)) := by
  constructor <;> rintro ⟨rightSupport, leftSupport⟩ hread
  · simpa [topologyContext, topologySupportReads] using hread.1
  · simpa [topologyContext, topologySupportReads] using hread.2

/-- The additive equivalence between the selected overlap coefficient and `ZMod 2`. -/
noncomputable def topologyOverlapCoefficientEquiv :
    ((topologyObstructionSheaf.toAddCommGrpSheaf.val.obj
      (Opposite.op topologyOverlapObject) : Type 1)) ≃+ ZMod 2 where
  toFun x := x.down.1
  invFun x := ULift.up ⟨x, by
    simp [topologyCoefficientSubmodule, topologyOverlap_noMarkerReads]⟩
  left_inv x := by
    apply ULift.down_injective
    apply Subtype.ext
    rfl
  right_inv x := rfl
  map_add' x y := rfl

theorem topologyAuxBaseCoefficient_subsingleton :
    Subsingleton
      ((topologyObstructionSheaf.toAddCommGrpSheaf.val.obj
        (Opposite.op topologyAuxBase) : Type 1)) := by
  change Subsingleton (ULift (topologyCoefficientSubmodule topologyAuxBase.ctx))
  rw [topologyCoefficientSubmodule_eq_bot_of_readsA _ PUnit.unit]
  · infer_instance
  · exact Or.inl rfl

theorem topologyAuxPatchCoefficient_subsingleton :
    Subsingleton
      ((topologyObstructionSheaf.toAddCommGrpSheaf.val.obj
        (Opposite.op topologyAuxPatch) : Type 1)) := by
  change Subsingleton (ULift (topologyCoefficientSubmodule topologyAuxPatch.ctx))
  rw [topologyCoefficientSubmodule_eq_bot_of_readsA _ PUnit.unit]
  · infer_instance
  · exact Or.inl rfl

theorem topologyLeftAuxOverlapCoefficient_subsingleton :
    Subsingleton
      ((topologyObstructionSheaf.toAddCommGrpSheaf.val.obj
        (Opposite.op topologyLeftAuxOverlap) : Type 1)) := by
  change Subsingleton
    (ULift (topologyCoefficientSubmodule topologyLeftAuxOverlap.ctx))
  rw [topologyCoefficientSubmodule_eq_bot_of_readsA _
    (PUnit.unit, PUnit.unit)]
  · infer_instance
  · exact ⟨rfl, Or.inl rfl⟩

theorem topologyRightAuxOverlapCoefficient_subsingleton :
    Subsingleton
      ((topologyObstructionSheaf.toAddCommGrpSheaf.val.obj
        (Opposite.op topologyRightAuxOverlap) : Type 1)) := by
  change Subsingleton
    (ULift (topologyCoefficientSubmodule topologyRightAuxOverlap.ctx))
  rw [topologyCoefficientSubmodule_eq_bot_of_readsB _
    (PUnit.unit, PUnit.unit)]
  · infer_instance
  · exact ⟨rfl, Or.inr rfl⟩

private def topologyPotential : TopologyCoarseCoverIndex → ZMod 2
  | .left => 0
  | .right => 1

private def topologyOneValue
    (i j : TopologyCoarseCoverIndex) : ZMod 2 :=
  topologyPotential j - topologyPotential i

private noncomputable def topologyCechOneCochain :
    (Cohomology.canonicalCechComplex
      topologyCoarseCover topologyObstructionSheaf).AdditiveCochain 1 :=
  fun σ => by
    refine ⟨topologyOneValue (σ 0) (σ 1), ?_⟩
    cases h0 : σ 0 <;> cases h1 : σ 1
    · rw [show topologyOneValue .left .left = 0 by rfl]
      exact Submodule.zero_mem _
    · have hnomarker : TopologyNoMarkerReads
          ((Cohomology.canonicalCoverRelative topologyCoarseCover).overlap
            1 σ).ctx := by
        simpa [Cohomology.canonicalCoverRelative,
          Cohomology.canonicalTupleOverlap, topologyCoarseCover,
          topologyCoarseCoverPatch, h0, h1] using topologyOverlap_noMarkerReads
      have hmem : topologyOneValue .left .right ∈
          topologyCoefficientSubmodule
            ((Cohomology.canonicalCoverRelative topologyCoarseCover).overlap
              1 σ).ctx := by
        rw [topologyCoefficientSubmodule, if_pos hnomarker]
        exact Submodule.mem_top
      simpa using hmem
    · have hnomarker : TopologyNoMarkerReads
          ((Cohomology.canonicalCoverRelative topologyCoarseCover).overlap
            1 σ).ctx := by
        simpa [Cohomology.canonicalCoverRelative,
          Cohomology.canonicalTupleOverlap, topologyCoarseCover,
          topologyCoarseCoverPatch, h0, h1] using
          topologyReverseOverlap_noMarkerReads
      have hmem : topologyOneValue .right .left ∈
          topologyCoefficientSubmodule
            ((Cohomology.canonicalCoverRelative topologyCoarseCover).overlap
              1 σ).ctx := by
        rw [topologyCoefficientSubmodule, if_pos hnomarker]
        exact Submodule.mem_top
      simpa using hmem
    · rw [show topologyOneValue .right .right = 0 by
        simp [topologyOneValue, topologyPotential]]
      exact Submodule.zero_mem _

theorem topologyCoarseToFineCechHom_nonzero :
    ∃ (c : (Cohomology.canonicalCechComplex
          topologyCoarseCover topologyObstructionSheaf).AdditiveCochain 1)
      (σ : (Cohomology.canonicalCoverRelative topologyFineCover).simplex 1),
      (topologyCoarseToFineCover.canonicalCechHom
        topologyObstructionSheaf).app 1 c σ ≠ 0 := by
  let σ : (Cohomology.canonicalCoverRelative topologyFineCover).simplex 1 :=
    fun i => if i = 0 then (false, false) else (true, false)
  refine ⟨topologyCechOneCochain, σ, ?_⟩
  intro hzero
  have hval := congrArg Subtype.val hzero
  change (topologyCechOneCochain
    (topologyCoarseToFineCover.simplexMap 1 σ)).1 = 0 at hval
  have hone : (topologyCechOneCochain
      (topologyCoarseToFineCover.simplexMap 1 σ)).1 = (1 : ZMod 2) := by
    simp [topologyCechOneCochain,
      Site.AATCoverageFamily.Refinement.simplexMap,
      topologyCoarseToFineCover, σ, topologyOneValue, topologyPotential]
  rw [hone] at hval
  exact one_ne_zero hval

private theorem topologyProductWithAuxPatch_not_noMarkerReads_of_A
    {W : Site.ArchCtx FiniteModel.object} {support : W.Support}
    (hread : W.minimal.supportReads support
      FiniteModel.FiniteAtom.componentA) :
    ¬ TopologyNoMarkerReads
      (Site.productContext W topologyAuxPatch.ctx) := by
  intro h
  exact h.1 (support, PUnit.unit)
    ⟨hread, by
      change topologySupportReads .auxPatch FiniteModel.FiniteAtom.componentA
      exact Or.inl rfl⟩

private theorem topologyProductWithAuxPatch_not_noMarkerReads_of_B
    {W : Site.ArchCtx FiniteModel.object} {support : W.Support}
    (hread : W.minimal.supportReads support
      FiniteModel.FiniteAtom.componentB) :
    ¬ TopologyNoMarkerReads
      (Site.productContext W topologyAuxPatch.ctx) := by
  intro h
  exact h.2 (support, PUnit.unit)
    ⟨hread, by
      change topologySupportReads .auxPatch FiniteModel.FiniteAtom.componentB
      exact Or.inr rfl⟩

private theorem topologyCoefficientPresheaf_isSheaf_aux_ofTypes :
    Presieve.IsSheaf topologyAuxPrecoverage.toGrothendieck
      (topologyCoefficientPresheaf ⋙ forget AddCommGrpCat.{0}) := by
  rw [Precoverage.isSheaf_toGrothendieck_iff]
  intro X Y f R hR
  rcases hR with ⟨hX, hR⟩
  subst X
  have hR : R = Presieve.singleton topologyAuxInclusion := eq_of_heq hR
  subst R
  intro family hfamily
  classical
  have hsubmodule : topologyCoefficientSubmodule
      (Site.productContext Y.ctx topologyAuxPatch.ctx) =
        topologyCoefficientSubmodule Y.ctx := by
    by_cases hY : TopologyNoMarkerReads Y.ctx
    · have hQ := topologyNoMarkerReads_product_left
        (V := topologyAuxPatch.ctx) hY
      simp [topologyCoefficientSubmodule, hY, hQ]
    · simp only [TopologyNoMarkerReads, not_and_or, not_forall,
        not_not] at hY
      rcases hY with hA | hB
      · rcases hA with ⟨support, hsupport⟩
        have hQ := topologyProductWithAuxPatch_not_noMarkerReads_of_A hsupport
        have hYnot : ¬ TopologyNoMarkerReads Y.ctx := fun h =>
          h.1 support hsupport
        rw [topologyCoefficientSubmodule, if_neg hQ,
          topologyCoefficientSubmodule, if_neg hYnot]
      · rcases hB with ⟨support, hsupport⟩
        have hQ := topologyProductWithAuxPatch_not_noMarkerReads_of_B hsupport
        have hYnot : ¬ TopologyNoMarkerReads Y.ctx := fun h =>
          h.2 support hsupport
        rw [topologyCoefficientSubmodule, if_neg hQ,
          topologyCoefficientSubmodule, if_neg hYnot]
  let Q := topologyProductObject Y topologyAuxPatch
  let q : Q ⟶ Y := topologyProductLeft Y topologyAuxPatch
  let qpatch : Q ⟶ topologyAuxPatch :=
    topologyProductRight Y topologyAuxPatch
  have hq : (Sieve.generate
      (Presieve.singleton topologyAuxInclusion)).pullback f q := by
    change Sieve.generate (Presieve.singleton topologyAuxInclusion) (q ≫ f)
    have hinclusion : Sieve.generate
        (Presieve.singleton topologyAuxInclusion) topologyAuxInclusion :=
      Sieve.le_generate _ _ Presieve.singleton.mk
    have hcomp := (Sieve.generate
      (Presieve.singleton topologyAuxInclusion)).downward_closed
        hinclusion qpatch
    convert hcomp using 1
  let reference := family q hq
  have reference_mem_Y : reference.1 ∈ topologyCoefficientSubmodule Y.ctx := by
    rw [← hsubmodule]
    exact reference.2
  let global : topologyCoefficientSubmodule Y.ctx :=
    ⟨reference.1, reference_mem_Y⟩
  have hconstant : ∀ {Z : topologySite.category}
      (g : Z ⟶ Y)
      (hg : (Sieve.generate
        (Presieve.singleton topologyAuxInclusion)).pullback f g),
      (family g hg).1 = reference.1 := by
    intro Z g hg
    let P := topologyProductObject Z Q
    let pz : P ⟶ Z := topologyProductLeft Z Q
    let pq : P ⟶ Q := topologyProductRight Z Q
    have hcompat := hfamily pz pq hg hq (Subsingleton.elim _ _)
    exact congrArg Subtype.val hcompat
  refine ⟨global, ?_, ?_⟩
  · intro Z g hg
    apply Subtype.ext
    change global.1 = (family g hg).1
    exact (hconstant g hg).symm
  · intro other hother
    apply Subtype.ext
    have hqOther := hother q hq
    have hval := congrArg Subtype.val hqOther
    change other.1 = global.1
    exact hval

private theorem topologyCoefficientPresheaf_isSheaf_fine_ofTypes :
    Presieve.IsSheaf fineTopology
      (topologyCoefficientPresheaf ⋙ forget AddCommGrpCat.{0}) := by
  let K := coarseTopology.toCoverage
  let L := topologyAuxPrecoverage.toGrothendieck.toCoverage
  have htop : (K ⊔ L).toGrothendieck = fineTopology := by
    calc
      (K ⊔ L).toGrothendieck =
          K.toGrothendieck ⊔ L.toGrothendieck :=
        (Coverage.gi topologySite.category).gc.l_sup
      _ = coarseTopology ⊔ topologyAuxPrecoverage.toGrothendieck := by
        rw [(Coverage.gi topologySite.category).l_u_eq,
          (Coverage.gi topologySite.category).l_u_eq]
      _ = fineTopology := fineTopology_eq_coarse_sup_aux.symm
  rw [← htop]
  apply (Presieve.isSheaf_sup K L _).2
  constructor
  · rw [(Coverage.gi topologySite.category).l_u_eq]
    simpa [coarseTopology] using topologyCoefficientPresheaf_isSheaf_ofTypes
  · rw [(Coverage.gi topologySite.category).l_u_eq]
    exact topologyCoefficientPresheaf_isSheaf_aux_ofTypes

private theorem topologyCoefficientPresheaf_isSheaf_fine :
    Presheaf.IsSheaf fineTopology
      topologyObstructionSheaf.toAddCommGrpSheaf.val := by
  refine (Presheaf.isSheaf_iff_isSheaf_forget
    (J := fineTopology)
    (P' := topologyObstructionSheaf.toAddCommGrpSheaf.val)
    (forget AddCommGrpCat.{1})).2 ?_
  refine (isSheaf_iff_isSheaf_of_type fineTopology _).2 ?_
  change Presieve.IsSheaf fineTopology
    ((topologyCoefficientPresheaf ⋙ forget AddCommGrpCat.{0}) ⋙
      uliftFunctor.{1, 0})
  exact Presieve.isSheaf_comp_uliftFunctor fineTopology
    topologyCoefficientPresheaf_isSheaf_fine_ofTypes

/-- The topology coefficient as one presheaf with coarse and fine sheaf proofs. -/
noncomputable def topologyCoefficient :
    CommonCoefficientSheaf coarseTopology fineTopology where
  presheaf := topologyObstructionSheaf.toAddCommGrpSheaf.val
  isSheaf_coarse := by
    simpa [coarseTopology] using topologyObstructionSheaf.toAddCommGrpSheaf.cond
  isSheaf_fine := topologyCoefficientPresheaf_isSheaf_fine

/--
Normalize the common coefficient to the original obstruction presheaf; the
`simp` direction exposes the single presheaf shared by both sheaf proofs.
-/
@[simp] theorem topologyCoefficient_presheaf :
    topologyCoefficient.presheaf =
      topologyObstructionSheaf.toAddCommGrpSheaf.val := rfl

private theorem topologySite_contains_of_hom_to_right
    {X : topologySite.category} (hX : X ⟶ topologyRightObject) :
    ∀ {Z : topologySite.category} (f : X ⟶ Z)
      {R : Sieve Z}, R ∈ topologySite.topology Z → R f := by
  intro Z f R hR
  change (Site.admissiblePrecoverage topologySite.requirements
    topologySite.overlap).Saturate Z R at hR
  induction hR with
  | of Z P hP =>
      rcases hP with ⟨F, rfl⟩
      rcases topology_admissibleCover_has_right F with ⟨i, hi⟩
      let g : X ⟶ Site.ContextCategoryObject.of topologyContextPreorder
          (F.patch i) :=
        hX ≫ eqToHom (congrArg
          (Site.ContextCategoryObject.of topologyContextPreorder) hi).symm
      have hinclusion : (Sieve.generate F.presieve)
          (homOfLE (F.inclusion i)) :=
        Sieve.le_generate F.presieve _ (Presieve.ofArrows.mk i)
      have hcomp := (Sieve.generate F.presieve).downward_closed
        hinclusion g
      convert hcomp using 1
  | top Z => simp
  | pullback Z S hS Y g ih =>
      change S (f ≫ g)
      exact ih (f ≫ g)
  | transitive Z S R hS hlocal ihS ihlocal =>
      have hSf : S f := ihS f
      have hRf : (R.pullback f) (𝟙 X) := ihlocal hSf (𝟙 X)
      simpa using hRf

private theorem topologySite_topology_eq_top_of_hom_to_left
    {X : topologySite.category} (hX : X ⟶ topologyLeftObject)
    {R : Sieve X} (hR : R ∈ coarseTopology X) : R = ⊤ := by
  apply le_antisymm le_top
  intro Y f hf
  exact topologySite_contains_of_hom_to_left (f ≫ hX) f hR

private theorem topologySite_topology_eq_top_of_hom_to_right
    {X : topologySite.category} (hX : X ⟶ topologyRightObject)
    {R : Sieve X} (hR : R ∈ coarseTopology X) : R = ⊤ := by
  apply le_antisymm le_top
  intro Y f hf
  exact topologySite_contains_of_hom_to_right (f ≫ hX) f hR

private noncomputable def topologySheafifiedFreeYoneda
    (X : topologySite.category) :
    Sheaf coarseTopology AddCommGrpCat.{1} :=
  (presheafToSheaf coarseTopology AddCommGrpCat.{1}).obj
    (yoneda.obj X ⋙ AddCommGrpCat.free)

private theorem topologySheafifiedFreeYoneda_projective_of_hom_to_left
    (X : topologySite.category) (hX : X ⟶ topologyLeftObject) :
    Projective (topologySheafifiedFreeYoneda X) := by
  constructor
  intro E G f e he
  letI : Epi e := he
  have hloc : Presheaf.IsLocallySurjective coarseTopology e.val :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{1} e).2 inferInstance
  let x := Cohomology.sheafifiedFreeYonedaHomAddEquiv X G f
  have hcover := Presheaf.imageSieve_mem coarseTopology e.val x
  have htop := topologySite_topology_eq_top_of_hom_to_left hX hcover
  have hid : Presheaf.imageSieve e.val x (𝟙 X) := by
    rw [htop]
    trivial
  rcases hid with ⟨t, ht⟩
  let lift : topologySheafifiedFreeYoneda X ⟶ E :=
    (Cohomology.sheafifiedFreeYonedaHomAddEquiv X E).symm t
  refine ⟨lift, ?_⟩
  apply (Cohomology.sheafifiedFreeYonedaHomAddEquiv X G).injective
  rw [Cohomology.sheafifiedFreeYonedaHomAddEquiv_comp]
  change e.val.app (op X)
      (Cohomology.sheafifiedFreeYonedaHomAddEquiv X E lift) = x
  rw [show Cohomology.sheafifiedFreeYonedaHomAddEquiv X E lift = t by
    exact (Cohomology.sheafifiedFreeYonedaHomAddEquiv X E).apply_symm_apply t]
  simpa using ht

private theorem topologySheafifiedFreeYoneda_projective_of_hom_to_right
    (X : topologySite.category) (hX : X ⟶ topologyRightObject) :
    Projective (topologySheafifiedFreeYoneda X) := by
  constructor
  intro E G f e he
  letI : Epi e := he
  have hloc : Presheaf.IsLocallySurjective coarseTopology e.val :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{1} e).2 inferInstance
  let x := Cohomology.sheafifiedFreeYonedaHomAddEquiv X G f
  have hcover := Presheaf.imageSieve_mem coarseTopology e.val x
  have htop := topologySite_topology_eq_top_of_hom_to_right hX hcover
  have hid : Presheaf.imageSieve e.val x (𝟙 X) := by
    rw [htop]
    trivial
  rcases hid with ⟨t, ht⟩
  let lift : topologySheafifiedFreeYoneda X ⟶ E :=
    (Cohomology.sheafifiedFreeYonedaHomAddEquiv X E).symm t
  refine ⟨lift, ?_⟩
  apply (Cohomology.sheafifiedFreeYonedaHomAddEquiv X G).injective
  rw [Cohomology.sheafifiedFreeYonedaHomAddEquiv_comp]
  change e.val.app (op X)
      (Cohomology.sheafifiedFreeYonedaHomAddEquiv X E lift) = x
  rw [show Cohomology.sheafifiedFreeYonedaHomAddEquiv X E lift = t by
    exact (Cohomology.sheafifiedFreeYonedaHomAddEquiv X E).apply_symm_apply t]
  simpa using ht

/-- The selected coarse cover is Leray for the topology obstruction coefficient. -/
theorem topologyCoarseLerayCover :
    Cohomology.IsLerayFor topologyCoarseCover topologyObstructionSheaf := by
  intro q hq p σ
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  let X := (Cohomology.canonicalCoverRelative
    topologyCoarseCover).overlap p σ
  have hprojection := Cohomology.canonicalTupleOverlapProjection
    topologyCoarseCover σ (0 : Fin (p + 1))
  cases hindex : σ 0 with
  | left =>
      have hp : X ⟶ topologyLeftObject := by
        simpa [X, Cohomology.canonicalCoverRelative,
          topologyCoarseCoverPatch, hindex] using hprojection
      letI : Projective (topologySheafifiedFreeYoneda X) :=
        topologySheafifiedFreeYoneda_projective_of_hom_to_left X hp
      exact CategoryTheory.Abelian.Ext.subsingleton_of_projective
        (topologySheafifiedFreeYoneda X)
          topologyObstructionSheaf.toAddCommGrpSheaf n
  | right =>
      have hp : X ⟶ topologyRightObject := by
        simpa [X, Cohomology.canonicalCoverRelative,
          topologyCoarseCoverPatch, hindex] using hprojection
      letI : Projective (topologySheafifiedFreeYoneda X) :=
        topologySheafifiedFreeYoneda_projective_of_hom_to_right X hp
      exact CategoryTheory.Abelian.Ext.subsingleton_of_projective
        (topologySheafifiedFreeYoneda X)
          topologyObstructionSheaf.toAddCommGrpSheaf n

@[simp] private theorem topologyObstructionMap_val
    {X Y : topologySite.category} (f : X ⟶ Y)
    (x : topologyObstructionSheaf.carrier.toPresheaf.obj (op Y)) :
    (topologyObstructionSheaf.mapAddMonoidHom f x).1 = x.1 := rfl

set_option maxHeartbeats 800000 in
private theorem topologyCechOneCochain_isCocycle :
    (Cohomology.canonicalCechComplex topologyCoarseCover
      topologyObstructionSheaf).d 1 topologyCechOneCochain =
        (0 : (Cohomology.canonicalCechComplex topologyCoarseCover
          topologyObstructionSheaf).AdditiveCochain 2) := by
  funext σ
  rw [Cohomology.canonicalCechComplex_d_apply]
  refine Subtype.ext ?_
  classical
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp only [Fintype.sum_empty, add_zero,
    Cohomology.canonicalCoverRelative_face]
  rw [Submodule.coe_add, Submodule.coe_add]
  norm_num
  rw [Submodule.coe_neg, topologyObstructionMap_val]
  change _ = (0 : ZMod 2)
  cases h0 : σ 0 <;> cases h1 : σ 1 <;> cases h2 : σ 2 <;>
    simp [topologyCechOneCochain, topologyOneValue, topologyPotential,
      SimplexCategory.δ, Fin.succAbove, h0, h1, h2] <;>
    decide

/-- The explicit degree-one cocycle on the selected coarse cover. -/
noncomputable def topologyCechOneCocycle :
    (Cohomology.canonicalCechComplex
      topologyCoarseCover topologyObstructionSheaf).CechCocycle 1 :=
  ⟨topologyCechOneCochain, topologyCechOneCochain_isCocycle⟩

/-- The explicit degree-one additive Čech class. -/
noncomputable def topologyCechOneClass :
    (Cohomology.canonicalCechComplex
      topologyCoarseCover topologyObstructionSheaf).AdditiveCechHn 1 :=
  (Cohomology.canonicalCechComplex
    topologyCoarseCover topologyObstructionSheaf).additiveH1Class
      topologyCechOneCocycle

private theorem topologyCoefficientSubmodule_left_eq_bot :
    topologyCoefficientSubmodule topologyLeftObject.ctx = ⊥ := by
  exact topologyCoefficientSubmodule_eq_bot_of_readsA _ PUnit.unit rfl

private theorem topologyCoefficientSubmodule_right_eq_bot :
    topologyCoefficientSubmodule topologyRightObject.ctx = ⊥ := by
  exact topologyCoefficientSubmodule_eq_bot_of_readsB _ PUnit.unit rfl

private theorem topologyDegreeZeroCoefficient_eq_bot
    (σ : (Cohomology.canonicalCoverRelative topologyCoarseCover).simplex 0) :
    topologyCoefficientSubmodule
      ((Cohomology.canonicalCoverRelative
        topologyCoarseCover).overlap 0 σ).ctx = ⊥ := by
  cases h : σ 0
  · simpa [Cohomology.canonicalCoverRelative,
      Cohomology.canonicalTupleOverlap, topologyCoarseCover,
      topologyCoarseCoverPatch, h] using
      topologyCoefficientSubmodule_left_eq_bot
  · simpa [Cohomology.canonicalCoverRelative,
      Cohomology.canonicalTupleOverlap, topologyCoarseCover,
      topologyCoarseCoverPatch, h] using
      topologyCoefficientSubmodule_right_eq_bot

private theorem topologyCechZeroCochain_eq_zero
    (b : (Cohomology.canonicalCechComplex topologyCoarseCover
      topologyObstructionSheaf).AdditiveCochain 0) : b = 0 := by
  funext σ
  refine Subtype.ext ?_
  let x : ZMod 2 := (b σ).1
  have hx : x ∈ topologyCoefficientSubmodule
      ((Cohomology.canonicalCoverRelative
        topologyCoarseCover).overlap 0 σ).ctx := (b σ).2
  rw [topologyDegreeZeroCoefficient_eq_bot σ] at hx
  change x = 0 at hx
  exact hx

private def topologyMixedOneSimplex :
    (Cohomology.canonicalCoverRelative topologyCoarseCover).simplex 1 :=
  fun i => if i = 0 then .left else .right

private def topologyReverseMixedOneSimplex :
    (Cohomology.canonicalCoverRelative topologyCoarseCover).simplex 1 :=
  fun i => if i = 0 then .right else .left

private def topologyMixedTwoSimplex :
    (Cohomology.canonicalCoverRelative topologyCoarseCover).simplex 2 :=
  fun i => if i = 1 then .right else .left

private theorem topologyOneSimplex_eq_mixed
    (σ : (Cohomology.canonicalCoverRelative
      topologyCoarseCover).simplex 1)
    (h0 : σ 0 = .left) (h1 : σ 1 = .right) :
    σ = topologyMixedOneSimplex := by
  funext i
  fin_cases i
  · exact h0
  · exact h1

private theorem topologyOneSimplex_eq_reverse_mixed
    (σ : (Cohomology.canonicalCoverRelative
      topologyCoarseCover).simplex 1)
    (h0 : σ 0 = .right) (h1 : σ 1 = .left) :
    σ = topologyReverseMixedOneSimplex := by
  funext i
  fin_cases i
  · exact h0
  · exact h1

private theorem topologyDegreeOneCoefficient_eq_bot_of_same
    (σ : (Cohomology.canonicalCoverRelative
      topologyCoarseCover).simplex 1)
    (h : σ 0 = σ 1) :
    topologyCoefficientSubmodule
      ((Cohomology.canonicalCoverRelative
        topologyCoarseCover).overlap 1 σ).ctx = ⊥ := by
  cases h0 : σ 0 with
  | left =>
      have h1 : σ 1 = .left := h.symm.trans h0
      have hsigma : σ = fun _ => .left := by
        funext i
        fin_cases i
        · exact h0
        · exact h1
      subst σ
      apply topologyCoefficientSubmodule_eq_bot_of_readsA _
        (PUnit.unit, PUnit.unit)
      change topologySupportReads .left
          FiniteModel.FiniteAtom.componentA ∧
        topologySupportReads .left FiniteModel.FiniteAtom.componentA
      simp [topologySupportReads]
  | right =>
      have h1 : σ 1 = .right := h.symm.trans h0
      have hsigma : σ = fun _ => .right := by
        funext i
        fin_cases i
        · exact h0
        · exact h1
      subst σ
      apply topologyCoefficientSubmodule_eq_bot_of_readsB _
        (PUnit.unit, PUnit.unit)
      change topologySupportReads .right
          FiniteModel.FiniteAtom.componentB ∧
        topologySupportReads .right FiniteModel.FiniteAtom.componentB
      simp [topologySupportReads]

private theorem topologyCechOneCochain_value_eq_zero_of_same
    (c : (Cohomology.canonicalCechComplex topologyCoarseCover
      topologyObstructionSheaf).AdditiveCochain 1)
    (σ : (Cohomology.canonicalCoverRelative
      topologyCoarseCover).simplex 1)
    (h : σ 0 = σ 1) : c σ = 0 := by
  apply Subtype.ext
  change (c σ).1 = 0
  have hx : (c σ).1 ∈ topologyCoefficientSubmodule
      ((Cohomology.canonicalCoverRelative
        topologyCoarseCover).overlap 1 σ).ctx := (c σ).2
  have hx' : (c σ).1 ∈ (⊥ : Submodule (ZMod 2) (ZMod 2)) := by
    simpa only [topologyDegreeOneCoefficient_eq_bot_of_same σ h] using hx
  exact hx'

private theorem topologyMixedTwoFaceZero :
    Site.FinitePosetCechCanonicalTupleSimplex.simplexMap
      (SimplexCategory.δ (0 : Fin 3)) topologyMixedTwoSimplex =
        topologyReverseMixedOneSimplex := by
  funext i
  fin_cases i <;> rfl

private theorem topologyMixedTwoFaceOne :
    Site.FinitePosetCechCanonicalTupleSimplex.simplexMap
      (SimplexCategory.δ (Fin.succ 0 : Fin 3)) topologyMixedTwoSimplex =
        (fun _ => .left) := by
  funext i
  fin_cases i <;> rfl

private theorem topologyMixedTwoFaceTwo :
    Site.FinitePosetCechCanonicalTupleSimplex.simplexMap
      (SimplexCategory.δ ((Fin.succ 0).succ : Fin 3))
        topologyMixedTwoSimplex =
        topologyMixedOneSimplex := by
  funext i
  fin_cases i <;> rfl

private theorem topologyCechOneCocycle_mixed_reverse_eq
    (c : (Cohomology.canonicalCechComplex topologyCoarseCover
      topologyObstructionSheaf).CechCocycle 1) :
    (c.1 topologyMixedOneSimplex).1 =
      (c.1 topologyReverseMixedOneSimplex).1 := by
  have h := congrFun c.2 topologyMixedTwoSimplex
  rw [Cohomology.canonicalCechComplex_d_apply] at h
  have hv := congrArg Subtype.val h
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ] at hv
  simp only [Fintype.sum_empty, add_zero,
    Cohomology.canonicalCoverRelative_face] at hv
  rw [Submodule.coe_add, Submodule.coe_add] at hv
  norm_num at hv
  rw [Submodule.coe_neg, topologyObstructionMap_val] at hv
  rw [topologyMixedTwoFaceZero, topologyMixedTwoFaceOne,
    topologyMixedTwoFaceTwo] at hv
  rw [show c.1 (fun _ => .left) = 0 by
    apply topologyCechOneCochain_value_eq_zero_of_same
    rfl] at hv
  have hv' :
      (c.1 topologyReverseMixedOneSimplex).1 +
        (c.1 topologyMixedOneSimplex).1 = 0 := by
    simpa using hv
  have hneg :
      (c.1 topologyReverseMixedOneSimplex).1 =
        -(c.1 topologyMixedOneSimplex).1 :=
    eq_neg_of_add_eq_zero_left hv'
  simpa only [ZMod.neg_eq_self_mod_two] using hneg.symm

private theorem topologyCechOneCocycle_cochain_eq_zero_or_eq_one
    (c : (Cohomology.canonicalCechComplex topologyCoarseCover
      topologyObstructionSheaf).CechCocycle 1) :
    c.1 = (0 : (Cohomology.canonicalCechComplex topologyCoarseCover
      topologyObstructionSheaf).AdditiveCochain 1) ∨
    c.1 = topologyCechOneCochain := by
  let x : ZMod 2 := (c.1 topologyMixedOneSimplex).1
  have hx : x = 0 ∨ x = 1 := by
    have hxlt : x.val < 2 := x.val_lt
    have hxval : x.val = 0 ∨ x.val = 1 := by omega
    rcases hxval with hxval | hxval
    · left
      apply ZMod.val_injective
      simpa using hxval
    · right
      apply ZMod.val_injective
      simpa using hxval
  have hmixed : (c.1 topologyMixedOneSimplex).1 = 0 ∨
      (c.1 topologyMixedOneSimplex).1 = 1 := hx
  rcases hmixed with hmixed | hmixed
  · left
    funext σ
    apply Subtype.ext
    change (c.1 σ).1 = 0
    cases h0 : σ 0 <;> cases h1 : σ 1
    · have hsame : σ 0 = σ 1 := h0.trans h1.symm
      rw [topologyCechOneCochain_value_eq_zero_of_same c.1 σ hsame]
      simp
    · rw [topologyOneSimplex_eq_mixed σ h0 h1]
      exact hmixed
    · rw [topologyOneSimplex_eq_reverse_mixed σ h0 h1]
      rw [← topologyCechOneCocycle_mixed_reverse_eq c, hmixed]
    · have hsame : σ 0 = σ 1 := h0.trans h1.symm
      rw [topologyCechOneCochain_value_eq_zero_of_same c.1 σ hsame]
      simp
  · right
    funext σ
    apply Subtype.ext
    cases h0 : σ 0 <;> cases h1 : σ 1
    · have hsame : σ 0 = σ 1 := h0.trans h1.symm
      rw [topologyCechOneCochain_value_eq_zero_of_same c.1 σ hsame]
      simp [topologyCechOneCochain, topologyOneValue, topologyPotential, h0, h1]
    · rw [topologyOneSimplex_eq_mixed σ h0 h1]
      exact hmixed
    · rw [topologyOneSimplex_eq_reverse_mixed σ h0 h1]
      rw [← topologyCechOneCocycle_mixed_reverse_eq c, hmixed]
      rfl
    · have hsame : σ 0 = σ 1 := h0.trans h1.symm
      rw [topologyCechOneCochain_value_eq_zero_of_same c.1 σ hsame]
      simp [topologyCechOneCochain, topologyOneValue, topologyPotential, h0, h1]

private theorem topologyCechOneCochain_mixed_val :
    (topologyCechOneCochain topologyMixedOneSimplex).1 =
      (1 : ZMod 2) := by
  rfl

private theorem topologyCechOneCochain_ne_zero :
    topologyCechOneCochain ≠ 0 := by
  intro h
  have hv := congrArg
    (fun c => (c topologyMixedOneSimplex).1) h
  change (topologyCechOneCochain topologyMixedOneSimplex).1 =
    ((0 : (Cohomology.canonicalCechComplex topologyCoarseCover
      topologyObstructionSheaf).AdditiveCochain 1)
        topologyMixedOneSimplex).1 at hv
  rw [topologyCechOneCochain_mixed_val] at hv
  change (1 : ZMod 2) = 0 at hv
  exact one_ne_zero hv

/-- The explicit topology-change Čech class is nonzero. -/
theorem topologyCechOneClass_ne_zero : topologyCechOneClass ≠ 0 := by
  intro hzero
  let K := Cohomology.canonicalCechComplex
    topologyCoarseCover topologyObstructionSheaf
  rcases (K.additiveH1Class_eq_zero_iff
    topologyCechOneCocycle).mp hzero with ⟨b, hb⟩
  rw [topologyCechZeroCochain_eq_zero b] at hb
  have : topologyCechOneCochain = 0 := by
    simpa [K] using hb
  exact topologyCechOneCochain_ne_zero this

/-- Every selected degree-one Čech class is zero or the explicit mixed class. -/
theorem topologyCechHOne_eq_zero_or_eq_one
    (x : (Cohomology.canonicalCechComplex topologyCoarseCover
      topologyObstructionSheaf).AdditiveCechHn 1) :
    x = 0 ∨ x = topologyCechOneClass := by
  let K := Cohomology.canonicalCechComplex
    topologyCoarseCover topologyObstructionSheaf
  change K.CechCocycleSubgroup 1 ⧸
    K.CechCoboundarySubgroupSucc 0 at x
  rcases QuotientAddGroup.mk_surjective x with ⟨z, rfl⟩
  let c : K.CechCocycle 1 := ⟨z.1, z.2⟩
  rcases topologyCechOneCocycle_cochain_eq_zero_or_eq_one c with h | h
  · left
    have hz : z = 0 := by
      apply Subtype.ext
      exact h
    subst z
    simp
  · right
    have hz : z =
        (⟨topologyCechOneCochain,
          topologyCechOneCochain_isCocycle⟩ : K.CechCocycleSubgroup 1) := by
      apply Subtype.ext
      exact h
    rw [hz]
    rfl

/-- The coarse actual `Sheaf.H` class represented by the explicit Čech class. -/
noncomputable def topologySourceHOneClass :
    topologyCoefficient.coarse.H nonzeroDegree :=
  Cohomology.cechToSheafH topologyCoarseCover topologyObstructionSheaf
    topologyBaseIsTerminal topologyCoarseLerayCover nonzeroDegree
    topologyCechOneClass

/-- Unfold the source class to the selected coarse Čech comparison. -/
theorem topologySourceHOneClass_eq_cech :
    topologySourceHOneClass =
      Cohomology.cechToSheafH topologyCoarseCover topologyObstructionSheaf
        topologyBaseIsTerminal topologyCoarseLerayCover nonzeroDegree
      topologyCechOneClass := rfl

private def topologyFineSupportVisibleOn
    (W : Site.ArchCtx FiniteModel.object)
    (atom : FiniteModel.carrier.Atom) : Prop :=
  topologySupportVisibleOn W atom ∨
    (W = topologyAuxPatch.ctx ∧
      (atom = FiniteModel.FiniteAtom.componentA ∨
        atom = FiniteModel.FiniteAtom.componentB))

private def topologyFineBoundaryVisibleOn
    (W base : Site.ArchCtx FiniteModel.object) : Prop :=
  (base = topologyBase.ctx ∧
      ∀ axis : W.Axis, W.minimal.axisReads axis) ∨
    (base = topologyAuxBase.ctx ∧
      ∃ axis : W.Axis, ¬ W.minimal.axisReads axis)

private def topologyFineCoverageRequirements :
    Site.CoverageRequirements FiniteModel.object
      (FiniteModel.equationSystem topologyContextPreorder) FiniteModel.signature where
  requiredSupport := fun atom =>
    atom = FiniteModel.FiniteAtom.componentA ∨
      atom = FiniteModel.FiniteAtom.componentB
  requiredEquationCoordinate := fun _ => False
  selectedViolationWitness := fun _ => False
  requiredAxis := fun _ => False
  supportVisibleOn := topologyFineSupportVisibleOn
  equationCoordinateVisibleOn := fun _ _ => False
  violationWitnessVisibleOn := fun _ _ => False
  axisReadableOn := fun _ _ => False
  boundaryVisibleOn := topologyFineBoundaryVisibleOn

private noncomputable def topologyFineSite :
    Site.AATSite FiniteModel.corePackage.object where
  contextPreorder := topologyContextPreorder
  equationSystem := FiniteModel.equationSystem topologyContextPreorder
  signature := FiniteModel.signature
  requirements := topologyFineCoverageRequirements
  overlap := topologyOverlap

private noncomputable def topologyFineSiteCoarseCover :
    Site.AATCoverageFamily topologyFineSite.requirements
      topologyFineSite.overlap topologyBase where
  Index := TopologyCoarseCoverIndex
  patch := topologyCoarseCoverPatch
  inclusion := by
    intro i
    cases i
    · exact topology_left_le_base
    · exact topology_right_le_base
  admissible := {
    atomSupportCoverage := by
      intro atom h
      rcases h with rfl | rfl
      · exact ⟨.left, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩
      · exact ⟨.right, Or.inl (Or.inr ⟨rfl, rfl⟩)⟩
    equationCoordinateCoverage := by
      intro coordinate h
      exact False.elim h
    violationWitnessCoverage := by
      intro witness h
      exact False.elim h
    signatureAxisCoverage := by
      intro axis h
      exact False.elim h
    boundaryCoverage := by
      intro i j
      apply Or.inl
      refine ⟨rfl, ?_⟩
      rintro ⟨leftAxis, rightAxis⟩
      cases i <;> cases j <;>
        change topologyAxisReads _ ∧ topologyAxisReads _ <;>
        simp [topologyAxisReads]
    nonGeneration := by
      intro i support atom h
      simpa [topologyBase, topologyContext, topologySupportReads] using h
  }

private noncomputable def topologyFineSiteAuxCover :
    Site.AATCoverageFamily topologyFineSite.requirements
      topologyFineSite.overlap topologyAuxBase where
  Index := PUnit
  patch := fun _ => topologyAuxPatch.ctx
  inclusion := fun _ => topology_auxPatch_le_auxBase
  admissible := {
    atomSupportCoverage := by
      intro atom h
      rcases h with rfl | rfl
      · exact ⟨PUnit.unit, Or.inr ⟨rfl, Or.inl rfl⟩⟩
      · exact ⟨PUnit.unit, Or.inr ⟨rfl, Or.inr rfl⟩⟩
    equationCoordinateCoverage := by
      intro coordinate h
      exact False.elim h
    violationWitnessCoverage := by
      intro witness h
      exact False.elim h
    signatureAxisCoverage := by
      intro axis h
      exact False.elim h
    boundaryCoverage := by
      intro i j
      apply Or.inr
      refine ⟨rfl, (PUnit.unit, PUnit.unit), ?_⟩
      change ¬ (topologyAxisReads .auxPatch ∧ topologyAxisReads .auxPatch)
      simp [topologyAxisReads]
    nonGeneration := by
      intro i support atom h
      simpa [topologyAuxBase, topologyAuxPatch, topologyContext] using
        (topologyContext .auxBase).supportReads_objectFamily h
  }

private theorem topologyFineSiteCoarseCover_mem :
    Sieve.generate topologyFineSiteCoarseCover.presieve ∈
      topologyFineSite.topology topologyBase :=
  Site.AATCoverageFamily.mem_topology topologyFineSiteCoarseCover

private theorem topologyFineSiteAuxCover_mem :
    Sieve.generate topologyFineSiteAuxCover.presieve ∈
      topologyFineSite.topology topologyAuxBase :=
  Site.AATCoverageFamily.mem_topology topologyFineSiteAuxCover

private theorem topologyFineSiteCoarseCover_presieve_eq :
    topologyFineSiteCoarseCover.presieve =
      topologyCoarseCover.presieve := rfl

private theorem topologyFineSiteAuxCover_presieve_eq :
    topologyFineSiteAuxCover.presieve =
      Presieve.singleton topologyAuxInclusion := by
  apply le_antisymm
  · intro Y f hf
    cases hf with
    | mk i =>
        exact Presieve.singleton.mk
  · intro Y f hf
    cases hf
    exact Presieve.ofArrows.mk PUnit.unit

private theorem topologyFine_left_self_all_axes_readable :
    ∀ axis : (topologyFineSite.overlap.overlap topologyBase.ctx
      (topologyContext .left) (topologyContext .left)).Axis,
      (topologyFineSite.overlap.overlap topologyBase.ctx
        (topologyContext .left) (topologyContext .left)).minimal.axisReads axis := by
  rintro ⟨leftAxis, rightAxis⟩
  change topologyAxisReads .left ∧ topologyAxisReads .left
  simp [topologyAxisReads]

private theorem topologyFine_right_self_all_axes_readable :
    ∀ axis : (topologyFineSite.overlap.overlap topologyBase.ctx
      (topologyContext .right) (topologyContext .right)).Axis,
      (topologyFineSite.overlap.overlap topologyBase.ctx
        (topologyContext .right) (topologyContext .right)).minimal.axisReads axis := by
  rintro ⟨leftAxis, rightAxis⟩
  change topologyAxisReads .right ∧ topologyAxisReads .right
  simp [topologyAxisReads]

private theorem topologyFine_aux_self_has_unreadable_axis :
    ∃ axis : (topologyFineSite.overlap.overlap topologyAuxBase.ctx
      topologyAuxPatch.ctx topologyAuxPatch.ctx).Axis,
      ¬ (topologyFineSite.overlap.overlap topologyAuxBase.ctx
        topologyAuxPatch.ctx topologyAuxPatch.ctx).minimal.axisReads axis := by
  refine ⟨(PUnit.unit, PUnit.unit), ?_⟩
  change ¬ (topologyAxisReads .auxPatch ∧ topologyAxisReads .auxPatch)
  simp [topologyAxisReads]

private theorem topology_base_not_le_auxBase :
    ¬ topologyContextPreorder.le topologyBase.ctx topologyAuxBase.ctx := by
  rintro ⟨f, hf⟩
  exact Empty.elim (f.observableRestrict PUnit.unit)

private theorem topologyFine_admissible_has_left_or_aux
    {Z : topologyFineSite.category}
    (F : Site.AATCoverageFamily topologyFineSite.requirements
      topologyFineSite.overlap Z) :
    ∃ i : F.Index,
      F.patch i = topologyContext .left ∨
        F.patch i = topologyAuxPatch.ctx := by
  rcases F.admissible.atomSupportCoverage
      FiniteModel.FiniteAtom.componentA (Or.inl rfl) with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  rcases hi with hi | hi
  · rcases hi with (⟨hleft, hatom⟩ | ⟨hright, hatom⟩)
    · exact Or.inl hleft
    · exact False.elim (by simpa using hatom)
  · exact Or.inr hi.1

private theorem topologyFine_admissible_has_right_or_aux
    {Z : topologyFineSite.category}
    (F : Site.AATCoverageFamily topologyFineSite.requirements
      topologyFineSite.overlap Z) :
    ∃ i : F.Index,
      F.patch i = topologyContext .right ∨
        F.patch i = topologyAuxPatch.ctx := by
  rcases F.admissible.atomSupportCoverage
      FiniteModel.FiniteAtom.componentB (Or.inr rfl) with ⟨i, hi⟩
  refine ⟨i, ?_⟩
  rcases hi with hi | hi
  · rcases hi with (⟨hleft, hatom⟩ | ⟨hright, hatom⟩)
    · exact False.elim (by simpa using hatom)
    · exact Or.inl hright
  · exact Or.inr hi.1

private theorem topologyFine_admissible_base_eq_base_or_aux
    {Z : topologyFineSite.category}
    (F : Site.AATCoverageFamily topologyFineSite.requirements
      topologyFineSite.overlap Z) :
    Z = topologyBase ∨ Z = topologyAuxBase := by
  rcases topologyFine_admissible_has_left_or_aux F with ⟨i, hi⟩
  have hboundary := F.admissible.boundaryCoverage i i
  change (Z.ctx = topologyBase.ctx ∧
      ∀ axis : (topologyFineSite.overlap.overlap Z.ctx
        (F.patch i) (F.patch i)).Axis,
        (topologyFineSite.overlap.overlap Z.ctx
          (F.patch i) (F.patch i)).minimal.axisReads axis) ∨
    (Z.ctx = topologyAuxBase.ctx ∧
      ∃ axis : (topologyFineSite.overlap.overlap Z.ctx
        (F.patch i) (F.patch i)).Axis,
        ¬ (topologyFineSite.overlap.overlap Z.ctx
          (F.patch i) (F.patch i)).minimal.axisReads axis) at hboundary
  rcases hboundary with hbase | haux
  · left
    cases Z
    cases hbase.1
    rfl
  · right
    cases Z
    cases haux.1
    rfl

private theorem topologyFineCoarseCover_presieve_le_admissible
    (F : Site.AATCoverageFamily topologyFineSite.requirements
      topologyFineSite.overlap topologyBase) :
    topologyFineSiteCoarseCover.presieve ≤ F.presieve := by
  intro Y f hf
  cases hf with
  | mk i =>
      cases i with
      | left =>
          rcases topologyFine_admissible_has_left_or_aux F with ⟨j, hj⟩
          rcases hj with hj | hj
          · let hobj := (congrArg
              (Site.ContextCategoryObject.of topologyContextPreorder) hj).symm
            exact Presieve.ofArrows.mk' j hobj (Subsingleton.elim _ _)
          · have hboundary := F.admissible.boundaryCoverage j j
            change (topologyBase.ctx = topologyBase.ctx ∧
                ∀ axis : (topologyFineSite.overlap.overlap topologyBase.ctx
                  (F.patch j) (F.patch j)).Axis,
                  (topologyFineSite.overlap.overlap topologyBase.ctx
                    (F.patch j) (F.patch j)).minimal.axisReads axis) ∨
              (topologyBase.ctx = topologyAuxBase.ctx ∧
                ∃ axis : (topologyFineSite.overlap.overlap topologyBase.ctx
                  (F.patch j) (F.patch j)).Axis,
                  ¬ (topologyFineSite.overlap.overlap topologyBase.ctx
                    (F.patch j) (F.patch j)).minimal.axisReads axis) at hboundary
            rcases hboundary with hbase | haux
            · rw [hj] at hbase
              rcases topologyFine_aux_self_has_unreadable_axis with
                ⟨axis, haxis⟩
              exact False.elim (haxis (hbase.2 axis))
            · exact False.elim (by
                apply topology_base_not_le_auxBase
                rw [haux.1]
                exact topologyContextPreorder.refl _)
      | right =>
          rcases topologyFine_admissible_has_right_or_aux F with ⟨j, hj⟩
          rcases hj with hj | hj
          · let hobj := (congrArg
              (Site.ContextCategoryObject.of topologyContextPreorder) hj).symm
            exact Presieve.ofArrows.mk' j hobj (Subsingleton.elim _ _)
          · have hboundary := F.admissible.boundaryCoverage j j
            change (topologyBase.ctx = topologyBase.ctx ∧
                ∀ axis : (topologyFineSite.overlap.overlap topologyBase.ctx
                  (F.patch j) (F.patch j)).Axis,
                  (topologyFineSite.overlap.overlap topologyBase.ctx
                    (F.patch j) (F.patch j)).minimal.axisReads axis) ∨
              (topologyBase.ctx = topologyAuxBase.ctx ∧
                ∃ axis : (topologyFineSite.overlap.overlap topologyBase.ctx
                  (F.patch j) (F.patch j)).Axis,
                  ¬ (topologyFineSite.overlap.overlap topologyBase.ctx
                    (F.patch j) (F.patch j)).minimal.axisReads axis) at hboundary
            rcases hboundary with hbase | haux
            · rw [hj] at hbase
              rcases topologyFine_aux_self_has_unreadable_axis with
                ⟨axis, haxis⟩
              exact False.elim (haxis (hbase.2 axis))
            · exact False.elim (by
                apply topology_base_not_le_auxBase
                rw [haux.1]
                exact topologyContextPreorder.refl _)

private theorem topologyFineAuxCover_presieve_le_admissible
    (F : Site.AATCoverageFamily topologyFineSite.requirements
      topologyFineSite.overlap topologyAuxBase) :
    topologyFineSiteAuxCover.presieve ≤ F.presieve := by
  intro Y f hf
  cases hf with
  | mk i =>
      rcases topologyFine_admissible_has_left_or_aux F with ⟨j, hj⟩
      rcases hj with hj | hj
      · have hboundary := F.admissible.boundaryCoverage j j
        change (topologyAuxBase.ctx = topologyBase.ctx ∧
            ∀ axis : (topologyFineSite.overlap.overlap topologyAuxBase.ctx
              (F.patch j) (F.patch j)).Axis,
              (topologyFineSite.overlap.overlap topologyAuxBase.ctx
                (F.patch j) (F.patch j)).minimal.axisReads axis) ∨
          (topologyAuxBase.ctx = topologyAuxBase.ctx ∧
            ∃ axis : (topologyFineSite.overlap.overlap topologyAuxBase.ctx
              (F.patch j) (F.patch j)).Axis,
              ¬ (topologyFineSite.overlap.overlap topologyAuxBase.ctx
                (F.patch j) (F.patch j)).minimal.axisReads axis) at hboundary
        rcases hboundary with hbase | haux
        · exact False.elim (by
            apply topology_base_not_le_auxBase
            rw [← hbase.1]
            exact topologyContextPreorder.refl _)
        · rw [hj] at haux
          rcases haux.2 with ⟨axis, haxis⟩
          exact False.elim (haxis (topologyFine_left_self_all_axes_readable axis))
      · let hobj := (congrArg
          (Site.ContextCategoryObject.of topologyContextPreorder) hj).symm
        exact Presieve.ofArrows.mk' j hobj (Subsingleton.elim _ _)

private theorem topologyFineSite_le_fineTopology :
    topologyFineSite.topology ≤ fineTopology := by
  intro Z R hR
  change (Site.admissiblePrecoverage topologyFineSite.requirements
    topologyFineSite.overlap).Saturate Z R at hR
  induction hR with
  | of Z P hP =>
      rcases hP with ⟨F, rfl⟩
      rcases topologyFine_admissible_base_eq_base_or_aux F with hbase | haux
      · subst Z
        have hcover : Sieve.generate topologyFineSiteCoarseCover.presieve ∈
            fineTopology topologyBase := by
          rw [topologyFineSiteCoarseCover_presieve_eq]
          exact (show coarseTopology ≤ fineTopology from le_sup_left)
            topologyBase topologyCoarseCover_mem_coarseTopology
        exact fineTopology.superset_covering
          (Sieve.generate_mono
            (topologyFineCoarseCover_presieve_le_admissible F)) hcover
      · subst Z
        have hcover : Sieve.generate topologyFineSiteAuxCover.presieve ∈
            fineTopology topologyAuxBase := by
          rw [topologyFineSiteAuxCover_presieve_eq]
          exact (show topologyAuxPrecoverage.toGrothendieck ≤ fineTopology from
            le_sup_right) topologyAuxBase
            (Precoverage.generate_mem_toGrothendieck ⟨rfl, HEq.rfl⟩)
        exact fineTopology.superset_covering
          (Sieve.generate_mono
            (topologyFineAuxCover_presieve_le_admissible F)) hcover
  | top Z => simp
  | pullback Z S hS Y f ih =>
      exact fineTopology.pullback_stable f ih
  | transitive Z S R hS hlocal ihS ihlocal =>
      exact fineTopology.transitive ihS R ihlocal

private theorem topologyCoarseGenerated_le_fineSite :
    topologyCoarsePrecoverage.toGrothendieck ≤
      topologyFineSite.topology := by
  intro Z R hR
  change topologyCoarsePrecoverage.Saturate Z R at hR
  induction hR with
  | of Z P hP =>
      rcases hP with ⟨hZ, hP⟩
      subst Z
      have hP : P = topologyCoarseCover.presieve := eq_of_heq hP
      subst P
      rw [← topologyFineSiteCoarseCover_presieve_eq]
      exact topologyFineSiteCoarseCover_mem
  | top Z => simp
  | pullback Z S hS Y f ih =>
      exact topologyFineSite.topology.pullback_stable f ih
  | transitive Z S R hS hlocal ihS ihlocal =>
      exact topologyFineSite.topology.transitive ihS R ihlocal

private theorem topologyAuxGenerated_le_fineSite :
    topologyAuxPrecoverage.toGrothendieck ≤
      topologyFineSite.topology := by
  intro Z R hR
  change topologyAuxPrecoverage.Saturate Z R at hR
  induction hR with
  | of Z P hP =>
      rcases hP with ⟨hZ, hP⟩
      subst Z
      have hP : P = Presieve.singleton topologyAuxInclusion := eq_of_heq hP
      subst P
      rw [← topologyFineSiteAuxCover_presieve_eq]
      exact topologyFineSiteAuxCover_mem
  | top Z => simp
  | pullback Z S hS Y f ih =>
      exact topologyFineSite.topology.pullback_stable f ih
  | transitive Z S R hS hlocal ihS ihlocal =>
      exact topologyFineSite.topology.transitive ihS R ihlocal

private theorem fineTopology_le_topologyFineSite :
    fineTopology ≤ topologyFineSite.topology := by
  rw [fineTopology_eq_coarse_sup_aux]
  apply sup_le
  · rw [coarseTopology, topologySite_topology_eq_coarseGenerated]
    exact topologyCoarseGenerated_le_fineSite
  · exact topologyAuxGenerated_le_fineSite

private theorem topologyFineSite_topology_eq_fineTopology :
    topologyFineSite.topology = fineTopology :=
  le_antisymm topologyFineSite_le_fineTopology
    fineTopology_le_topologyFineSite

private theorem topologyCoefficientPresheaf_isSheaf_fineSite_ofTypes :
    Presieve.IsSheaf topologyFineSite.topology
      (topologyCoefficientPresheaf ⋙ forget AddCommGrpCat.{0}) := by
  rw [topologyFineSite_topology_eq_fineTopology]
  exact topologyCoefficientPresheaf_isSheaf_fine_ofTypes

private noncomputable def topologyFineObstructionSheaf :
    Cohomology.ObstructionSheaf topologyFineSite :=
  Cohomology.ObstructionSheaf.ofAddCommGrpValued
    topologyCoefficientPresheaf
    ((Site.AATSheafCondition.iff_presieve_isSheaf topologyFineSite _).2
      topologyCoefficientPresheaf_isSheaf_fineSite_ofTypes)

private def TopologyNoObservableReads
    (W : Site.ArchCtx FiniteModel.object) : Prop :=
  ∀ observable : W.Observable,
    ¬ W.minimal.observableReads observable

private theorem topologyNoObservableReads_left :
    TopologyNoObservableReads topologyLeftObject.ctx := by
  intro observable
  change ¬ topologyObservableReads .left observable
  exact id

private theorem topologyNoObservableReads_right :
    TopologyNoObservableReads topologyRightObject.ctx := by
  intro observable
  change ¬ topologyObservableReads .right observable
  exact id

private theorem topologyNoObservableReads_product
    {W V : Site.ArchCtx FiniteModel.object}
    (hW : TopologyNoObservableReads W)
    (hV : TopologyNoObservableReads V) :
    TopologyNoObservableReads (Site.productContext W V) := by
  rintro (observable | observable) hread
  · exact hW observable hread
  · exact hV observable hread

private theorem topologyFineSelectedOverlap_noObservableReads :
    ∀ p (sigma : (Cohomology.canonicalCoverRelative
      topologyFineSiteCoarseCover).simplex p),
      TopologyNoObservableReads
        ((Cohomology.canonicalCoverRelative
          topologyFineSiteCoarseCover).overlap p sigma).ctx := by
  intro p
  induction p with
  | zero =>
      intro sigma
      cases hindex : sigma 0 with
      | left =>
          simpa [Cohomology.canonicalCoverRelative,
            Cohomology.canonicalTupleOverlap,
            topologyFineSiteCoarseCover, topologyCoarseCoverPatch,
            hindex] using topologyNoObservableReads_left
      | right =>
          simpa [Cohomology.canonicalCoverRelative,
            Cohomology.canonicalTupleOverlap,
            topologyFineSiteCoarseCover, topologyCoarseCoverPatch,
            hindex] using topologyNoObservableReads_right
  | succ p ih =>
      intro sigma
      apply topologyNoObservableReads_product
      · exact ih (fun i => sigma i.castSucc)
      · cases sigma (Fin.last (p + 1)) with
        | left => exact topologyNoObservableReads_left
        | right => exact topologyNoObservableReads_right

private theorem topologyFineSite_contains_of_selected_projection
    {X : topologyFineSite.category}
    (hnoObservable : TopologyNoObservableReads X.ctx)
    (hprojection : Nonempty (X ⟶ topologyLeftObject) ∨
      Nonempty (X ⟶ topologyRightObject)) :
    ∀ {Z : topologyFineSite.category} (f : X ⟶ Z)
      {R : Sieve Z}, R ∈ topologyFineSite.topology Z → R f := by
  intro Z f R hR
  change (Site.admissiblePrecoverage topologyFineSite.requirements
    topologyFineSite.overlap).Saturate Z R at hR
  induction hR with
  | of Z P hP =>
      rcases hP with ⟨F, rfl⟩
      rcases topologyFine_admissible_base_eq_base_or_aux F with hbase | haux
      · subst Z
        rcases hprojection with hleft | hright
        · rcases hleft with ⟨hleft⟩
          have hinclusion : Sieve.generate F.presieve
              (homOfLE (topologyFineSiteCoarseCover.inclusion
                TopologyCoarseCoverIndex.left)) :=
            Sieve.le_generate F.presieve _
              (topologyFineCoarseCover_presieve_le_admissible F _
                (Presieve.ofArrows.mk TopologyCoarseCoverIndex.left))
          have hcomp := (Sieve.generate F.presieve).downward_closed
            hinclusion hleft
          convert hcomp using 1
        · rcases hright with ⟨hright⟩
          have hinclusion : Sieve.generate F.presieve
              (homOfLE (topologyFineSiteCoarseCover.inclusion
                TopologyCoarseCoverIndex.right)) :=
            Sieve.le_generate F.presieve _
              (topologyFineCoarseCover_presieve_le_admissible F _
                (Presieve.ofArrows.mk TopologyCoarseCoverIndex.right))
          have hcomp := (Sieve.generate F.presieve).downward_closed
            hinclusion hright
          convert hcomp using 1
      · subst Z
        let readable := topologyContextPreorder.readableMorphism (leOfHom f)
        have hrestriction :=
          topologyContextPreorder.readableMorphism_isRestriction (leOfHom f)
        have hread := hrestriction.2.2.1
          (observable := PUnit.unit) trivial
        exact False.elim (hnoObservable _ hread)
  | top Z => simp
  | pullback Z S hS Y g ih =>
      change S (f ≫ g)
      exact ih (f ≫ g)
  | transitive Z S R hS hlocal ihS ihlocal =>
      have hSf : S f := ihS f
      have hRf : (R.pullback f) (𝟙 X) := ihlocal hSf (𝟙 X)
      simpa using hRf

private theorem topologyFineSite_topology_eq_top_of_selected_overlap
    (p : Nat)
    (sigma : (Cohomology.canonicalCoverRelative
      topologyFineSiteCoarseCover).simplex p)
    {R : Sieve ((Cohomology.canonicalCoverRelative
      topologyFineSiteCoarseCover).overlap p sigma)}
    (hR : R ∈ topologyFineSite.topology _) : R = ⊤ := by
  let X := (Cohomology.canonicalCoverRelative
    topologyFineSiteCoarseCover).overlap p sigma
  have hprojection := Cohomology.canonicalTupleOverlapProjection
    topologyFineSiteCoarseCover sigma (0 : Fin (p + 1))
  have hbranch : Nonempty (X ⟶ topologyLeftObject) ∨
      Nonempty (X ⟶ topologyRightObject) := by
    cases hindex : sigma 0 with
    | left =>
        left
        exact ⟨by
          simpa [X, Cohomology.canonicalCoverRelative,
            topologyFineSiteCoarseCover, topologyCoarseCoverPatch,
            hindex] using hprojection⟩
    | right =>
        right
        exact ⟨by
          simpa [X, Cohomology.canonicalCoverRelative,
            topologyFineSiteCoarseCover, topologyCoarseCoverPatch,
            hindex] using hprojection⟩
  apply le_antisymm le_top
  intro Y f hf
  have hid : R (𝟙 X) :=
    topologyFineSite_contains_of_selected_projection
      (topologyFineSelectedOverlap_noObservableReads p sigma)
        hbranch (𝟙 X) hR
  exact R.downward_closed hid f

private noncomputable def topologyFineSheafifiedFreeYoneda
    (X : topologyFineSite.category) :
    Sheaf topologyFineSite.topology AddCommGrpCat.{1} :=
  (presheafToSheaf topologyFineSite.topology AddCommGrpCat.{1}).obj
    (yoneda.obj X ⋙ AddCommGrpCat.free)

private theorem topologyFineSheafifiedFreeYoneda_projective
    (p : Nat)
    (sigma : (Cohomology.canonicalCoverRelative
      topologyFineSiteCoarseCover).simplex p) :
    Projective (topologyFineSheafifiedFreeYoneda
      ((Cohomology.canonicalCoverRelative
        topologyFineSiteCoarseCover).overlap p sigma)) := by
  let X := (Cohomology.canonicalCoverRelative
    topologyFineSiteCoarseCover).overlap p sigma
  constructor
  intro E G f e he
  letI : Epi e := he
  have hloc : Presheaf.IsLocallySurjective topologyFineSite.topology e.val :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{1} e).2 inferInstance
  let x := Cohomology.sheafifiedFreeYonedaHomAddEquiv X G f
  have hcover := Presheaf.imageSieve_mem topologyFineSite.topology e.val x
  have htop := topologyFineSite_topology_eq_top_of_selected_overlap
    p sigma hcover
  have hid : Presheaf.imageSieve e.val x (𝟙 X) := by
    rw [htop]
    trivial
  rcases hid with ⟨t, ht⟩
  let lift : topologyFineSheafifiedFreeYoneda X ⟶ E :=
    (Cohomology.sheafifiedFreeYonedaHomAddEquiv X E).symm t
  refine ⟨lift, ?_⟩
  apply (Cohomology.sheafifiedFreeYonedaHomAddEquiv X G).injective
  rw [Cohomology.sheafifiedFreeYonedaHomAddEquiv_comp]
  change e.val.app (op X)
      (Cohomology.sheafifiedFreeYonedaHomAddEquiv X E lift) = x
  rw [show Cohomology.sheafifiedFreeYonedaHomAddEquiv X E lift = t by
    exact (Cohomology.sheafifiedFreeYonedaHomAddEquiv X E).apply_symm_apply t]
  simpa using ht

private theorem topologyFineLerayCover :
    Cohomology.IsLerayFor topologyFineSiteCoarseCover
      topologyFineObstructionSheaf := by
  intro q hq p sigma
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  let X := (Cohomology.canonicalCoverRelative
    topologyFineSiteCoarseCover).overlap p sigma
  letI : Projective (topologyFineSheafifiedFreeYoneda X) :=
    topologyFineSheafifiedFreeYoneda_projective p sigma
  exact CategoryTheory.Abelian.Ext.subsingleton_of_projective
    (topologyFineSheafifiedFreeYoneda X)
      topologyFineObstructionSheaf.toAddCommGrpSheaf n

private noncomputable def topologyCoarseFineCechOneEquiv :
    (Cohomology.canonicalCechComplex
      topologyCoarseCover topologyObstructionSheaf).AdditiveCechHn 1 ≃+
    (Cohomology.canonicalCechComplex
      topologyFineSiteCoarseCover topologyFineObstructionSheaf).AdditiveCechHn 1 :=
  AddEquiv.refl _

private noncomputable def topologyFineActualCechToRawHOneEquiv :
    (Cohomology.canonicalCechComplex
      topologyFineSiteCoarseCover topologyFineObstructionSheaf).AdditiveCechHn 1 ≃+
      topologyFineObstructionSheaf.toAddCommGrpSheaf.H nonzeroDegree :=
  AddEquiv.ofBijective
    (Cohomology.cechToSheafH topologyFineSiteCoarseCover
      topologyFineObstructionSheaf topologyBaseIsTerminal
      topologyFineLerayCover nonzeroDegree)
    (Cohomology.cechToSheafH_bijective topologyFineSiteCoarseCover
      topologyFineObstructionSheaf topologyBaseIsTerminal
      topologyFineLerayCover nonzeroDegree)

private theorem topologySheaf_heq_of_val_eq
    {J J' : GrothendieckTopology topologySite.category}
    {F : Sheaf J AddCommGrpCat.{1}}
    {G : Sheaf J' AddCommGrpCat.{1}}
    (hJ : J = J') (hval : F.val = G.val) : HEq F G := by
  subst J'
  cases F with
  | mk F hF =>
      cases G with
      | mk G hG =>
          dsimp at hval
          subst G
          rfl

@[ext] private structure TopologyFineHIndex where
  topology : GrothendieckTopology topologySite.category
  sheaf : Sheaf topology AddCommGrpCat.{1}
  hasExt : HasExt.{2} (Sheaf topology AddCommGrpCat.{1})

private noncomputable def topologyFineRawHIndex : TopologyFineHIndex where
  topology := topologyFineSite.topology
  sheaf := topologyFineObstructionSheaf.toAddCommGrpSheaf
  hasExt := inferInstance

private noncomputable def topologyFineTargetHIndex : TopologyFineHIndex where
  topology := fineTopology
  sheaf := topologyCoefficient.fine
  hasExt := inferInstance

private noncomputable def topologyFineHCarrier
    (p : TopologyFineHIndex) : Type 2 :=
  letI := p.hasExt
  p.sheaf.H nonzeroDegree

private noncomputable instance topologyFineHCarrierAddCommGroup
    (p : TopologyFineHIndex) : AddCommGroup (topologyFineHCarrier p) := by
  dsimp [topologyFineHCarrier]
  letI := p.hasExt
  infer_instance

private theorem topologyFineHIndex_eq :
    topologyFineRawHIndex = topologyFineTargetHIndex := by
  apply TopologyFineHIndex.ext
  · exact topologyFineSite_topology_eq_fineTopology
  · exact topologySheaf_heq_of_val_eq
      topologyFineSite_topology_eq_fineTopology rfl

private noncomputable def topologyFineHOneTransport :
    topologyFineObstructionSheaf.toAddCommGrpSheaf.H nonzeroDegree ≃+
      topologyCoefficient.fine.H nonzeroDegree := by
  change topologyFineHCarrier topologyFineRawHIndex ≃+
    topologyFineHCarrier topologyFineTargetHIndex
  exact AddEquiv.cast topologyFineHIndex_eq

private noncomputable def topologyFineActualCechToHOneEquiv :
    (Cohomology.canonicalCechComplex
      topologyFineSiteCoarseCover topologyFineObstructionSheaf).AdditiveCechHn 1 ≃+
      topologyCoefficient.fine.H nonzeroDegree :=
  topologyFineActualCechToRawHOneEquiv.trans topologyFineHOneTransport

/-- The fine actual `Sheaf.H` comparison obtained from its injective resolution. -/
noncomputable def topologyCechToFineHOneEquiv :
    (Cohomology.canonicalCechComplex
      topologyCoarseCover topologyObstructionSheaf).AdditiveCechHn 1 ≃+
        topologyCoefficient.fine.H nonzeroDegree :=
  topologyCoarseFineCechOneEquiv.trans
    topologyFineActualCechToHOneEquiv

/-- The fine actual `Sheaf.H` class represented by the explicit Čech class. -/
noncomputable def topologyTargetHOneClass :
    topologyCoefficient.fine.H nonzeroDegree :=
  topologyCechToFineHOneEquiv topologyCechOneClass

/-- The independently constructed fine class is nonzero. -/
theorem topologyTargetHOneClass_ne_zero :
    topologyTargetHOneClass ≠ 0 := by
  intro hzero
  apply topologyCechOneClass_ne_zero
  apply topologyCechToFineHOneEquiv.injective
  simpa [topologyTargetHOneClass] using hzero


/-!
## R9f finite coefficient-geometry sheafification

This section constructs the algebra-valued sheafification instances required by
the R9f coefficient-geometry firing.  The actual finite reference site has a
large object type because an architecture context stores carrier types, but its
readable isomorphism classes have a small finite-profile classification.

## Implementation notes

`ContextCode` records every finite Atom subset jointly read by one support,
together with the nonempty and readable states of the axis and observable
carriers.  A readable restriction preserves this code in the appropriate
direction, and equality of codes reconstructs restrictions in both directions.
Consequently the thin context category is essentially small.

Sheafification is constructed on Mathlib's small model and transported back
along the site equivalence.  The topology itself is unchanged.  The target
category `AATCommAlgCat` is an under-category; local concrete-category data
identifies its concrete forgetful functor with `Under.forget` followed by the
commutative-ring forgetful functor, allowing the standard left-exact
sheafification construction to apply.

The human-approved module-DAG extension imports Mathlib's canonical
filtered-colimit preservation for `Under.forget` and canonical finite-category
structure for a walking multicospan.  The R9f implementation reuses those
instances directly instead of reproducing their generic constructions.

For coefficient extension, the same finite classification is strengthened to
an actual finite matching argument.  The site is transported to the thin
skeleton of its small model.  Every covering sieve there has finitely many
arrows and relations, so its matching multicospan is finite.  Flat coefficient
extension preserves that finite limit, and `HasSheafCompose` transports back
to the original finite-site topology.

The firing geometry uses the single affine chart at `finiteBase`.  Its
semantic core generates the constant equation `2`, and the identity raw
presentation realizes that equation through the Part 3 bridge theorem.  To
detect the coefficient change, two maps to `ZMod 2` are constructed on the
actual pushout defining the changed sheafified section ring: both agree on the
source section ring, while the new coefficient `Polynomial.X` is sent to `0`
and `1`.  They kill the generated target law ideal, descend to the lawful
closed subscheme, and show that the canonical lawful-locus map is not an
isomorphism.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open scoped AlgebraicGeometry

private local instance : Fintype FiniteModel.FiniteAtom where
  elems := FiniteModel.FiniteAtom.all.toFinset
  complete atom := by
    simpa using FiniteModel.FiniteAtom.mem_all atom

private structure ContextCode where
  support : Finset (Finset FiniteModel.FiniteAtom)
  axisNonempty : Prop
  axisReadable : Prop
  observableNonempty : Prop
  observableReadable : Prop

private noncomputable def contextSupportCode (W : finiteSite.category) :
    Finset (Finset FiniteModel.FiniteAtom) := by
  classical
  exact Finset.univ.filter fun p => ∃ s : W.ctx.Support,
    ∀ a ∈ p, W.ctx.minimal.supportReads s a

private noncomputable def contextCode (W : finiteSite.category) : ContextCode where
  support := contextSupportCode W
  axisNonempty := Nonempty W.ctx.Axis
  axisReadable := ∃ x : W.ctx.Axis, W.ctx.minimal.axisReads x
  observableNonempty := Nonempty W.ctx.Observable
  observableReadable := ∃ x : W.ctx.Observable, W.ctx.minimal.observableReads x

private theorem supportCode_mono {W V : finiteSite.category}
    (h : finiteSite.contextPreorder.le W.ctx V.ctx) :
    contextSupportCode W ⊆ contextSupportCode V := by
  classical
  rcases h with ⟨f, hf⟩
  intro p hp
  rw [contextSupportCode, Finset.mem_filter] at hp ⊢
  refine ⟨hp.1, ?_⟩
  rcases hp.2 with ⟨s, hs⟩
  exact ⟨f.supportMap s, fun a ha => hf.1 (hs a ha)⟩

private theorem axisNonempty_mono {W V : finiteSite.category}
    (h : finiteSite.contextPreorder.le W.ctx V.ctx) :
    Nonempty W.ctx.Axis → Nonempty V.ctx.Axis := by
  rcases h with ⟨f, _hf⟩
  rintro ⟨x⟩
  exact ⟨f.axisMap x⟩

private theorem axisReadable_mono {W V : finiteSite.category}
    (h : finiteSite.contextPreorder.le W.ctx V.ctx) :
    (∃ x : W.ctx.Axis, W.ctx.minimal.axisReads x) →
      ∃ x : V.ctx.Axis, V.ctx.minimal.axisReads x := by
  rcases h with ⟨f, hf⟩
  rintro ⟨x, hx⟩
  exact ⟨f.axisMap x, hf.2.1 hx⟩

private theorem observableNonempty_anti {W V : finiteSite.category}
    (h : finiteSite.contextPreorder.le W.ctx V.ctx) :
    Nonempty V.ctx.Observable → Nonempty W.ctx.Observable := by
  rcases h with ⟨f, _hf⟩
  rintro ⟨x⟩
  exact ⟨f.observableRestrict x⟩

private theorem observableReadable_anti {W V : finiteSite.category}
    (h : finiteSite.contextPreorder.le W.ctx V.ctx) :
    (∃ x : V.ctx.Observable, V.ctx.minimal.observableReads x) →
      ∃ x : W.ctx.Observable, W.ctx.minimal.observableReads x := by
  rcases h with ⟨f, hf⟩
  rintro ⟨x, hx⟩
  exact ⟨f.observableRestrict x, hf.2.2.1 hx⟩

private theorem contextCode_eq_of_mutual {W V : finiteSite.category}
    (hWV : finiteSite.contextPreorder.le W.ctx V.ctx)
    (hVW : finiteSite.contextPreorder.le V.ctx W.ctx) :
    contextCode W = contextCode V := by
  unfold contextCode
  congr 1
  · exact Finset.Subset.antisymm (supportCode_mono hWV) (supportCode_mono hVW)
  · exact propext ⟨axisNonempty_mono hWV, axisNonempty_mono hVW⟩
  · exact propext ⟨axisReadable_mono hWV, axisReadable_mono hVW⟩
  · exact propext ⟨observableNonempty_anti hVW, observableNonempty_anti hWV⟩
  · exact propext ⟨observableReadable_anti hVW, observableReadable_anti hWV⟩

private theorem contextLe_of_code_eq {W V : finiteSite.category}
    (hcode : contextCode W = contextCode V) :
    finiteSite.contextPreorder.le W.ctx V.ctx := by
  classical
  have hsupport : ∀ s : W.ctx.Support, ∃ t : V.ctx.Support,
      ∀ a, W.ctx.minimal.supportReads s a →
        V.ctx.minimal.supportReads t a := by
    intro s
    let p : Finset FiniteModel.FiniteAtom :=
      Finset.univ.filter fun a => W.ctx.minimal.supportReads s a
    have hpW : p ∈ contextSupportCode W := by
      rw [contextSupportCode, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, s, ?_⟩
      intro a ha
      exact (Finset.mem_filter.mp ha).2
    have hpV : p ∈ contextSupportCode V := by
      have hs := congrArg ContextCode.support hcode
      change contextSupportCode W = contextSupportCode V at hs
      rw [← hs]
      exact hpW
    rw [contextSupportCode, Finset.mem_filter] at hpV
    rcases hpV.2 with ⟨t, ht⟩
    refine ⟨t, fun a ha => ht a ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩
  let supportMap : W.ctx.Support → V.ctx.Support :=
    fun s => Classical.choose (hsupport s)
  have hsupportMap : ∀ {s a}, W.ctx.minimal.supportReads s a →
      V.ctx.minimal.supportReads (supportMap s) a := by
    intro s a hread
    exact Classical.choose_spec (hsupport s) a hread
  have haxisNonempty : Nonempty W.ctx.Axis → Nonempty V.ctx.Axis := by
    have h := congrArg ContextCode.axisNonempty hcode
    change (Nonempty W.ctx.Axis : Prop) = Nonempty V.ctx.Axis at h
    exact fun hW => h ▸ hW
  have haxisReadable : (∃ x : W.ctx.Axis, W.ctx.minimal.axisReads x) →
      ∃ x : V.ctx.Axis, V.ctx.minimal.axisReads x := by
    have h := congrArg ContextCode.axisReadable hcode
    change (∃ x : W.ctx.Axis, W.ctx.minimal.axisReads x) =
      (∃ x : V.ctx.Axis, V.ctx.minimal.axisReads x) at h
    exact fun hW => h ▸ hW
  let axisMap : W.ctx.Axis → V.ctx.Axis := fun x =>
    if hx : W.ctx.minimal.axisReads x then
      Classical.choose (haxisReadable ⟨x, hx⟩)
    else Classical.choice (haxisNonempty ⟨x⟩)
  have haxisMap : ∀ {x}, W.ctx.minimal.axisReads x →
      V.ctx.minimal.axisReads (axisMap x) := by
    intro x hx
    simp only [axisMap, dif_pos hx]
    exact Classical.choose_spec (haxisReadable ⟨x, hx⟩)
  have hobservableNonempty : Nonempty V.ctx.Observable → Nonempty W.ctx.Observable := by
    have h := congrArg ContextCode.observableNonempty hcode
    change (Nonempty W.ctx.Observable : Prop) = Nonempty V.ctx.Observable at h
    exact fun hV => h.symm ▸ hV
  have hobservableReadable :
      (∃ x : V.ctx.Observable, V.ctx.minimal.observableReads x) →
        ∃ x : W.ctx.Observable, W.ctx.minimal.observableReads x := by
    have h := congrArg ContextCode.observableReadable hcode
    change (∃ x : W.ctx.Observable, W.ctx.minimal.observableReads x) =
      (∃ x : V.ctx.Observable, V.ctx.minimal.observableReads x) at h
    exact fun hV => h.symm ▸ hV
  let observableRestrict : V.ctx.Observable → W.ctx.Observable := fun x =>
    if hx : V.ctx.minimal.observableReads x then
      Classical.choose (hobservableReadable ⟨x, hx⟩)
    else Classical.choice (hobservableNonempty ⟨x⟩)
  have hobservableRestrict : ∀ {x}, V.ctx.minimal.observableReads x →
      W.ctx.minimal.observableReads (observableRestrict x) := by
    intro x hx
    simp only [observableRestrict, dif_pos hx]
    exact Classical.choose_spec (hobservableReadable ⟨x, hx⟩)
  let f : Site.ContextMorphism W.ctx V.ctx := {
    supportMap := supportMap
    axisMap := axisMap
    observableRestrict := observableRestrict }
  refine ⟨f, ?_⟩
  exact ⟨hsupportMap, haxisMap, hobservableRestrict,
    fun hread => V.ctx.supportReads_objectFamily hread⟩

private theorem contextCode_eq_of_isomorphic (W V : finiteSite.category)
    (h : (CategoryTheory.isIsomorphicSetoid finiteSite.category).r W V) :
    contextCode W = contextCode V := by
  rcases h with ⟨i⟩
  exact contextCode_eq_of_mutual (leOfHom i.hom) (leOfHom i.inv)

private noncomputable def skeletonContextCode :
    Skeleton finiteSite.category → ContextCode :=
  Quotient.lift contextCode contextCode_eq_of_isomorphic

private theorem skeletonContextCode_injective :
    Function.Injective skeletonContextCode := by
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro W V hcode
  apply Quotient.sound
  refine ⟨{
    hom := homOfLE (contextLe_of_code_eq hcode)
    inv := homOfLE (contextLe_of_code_eq hcode.symm) }⟩

private theorem finiteSite_essentiallySmall :
    EssentiallySmall.{0} finiteSite.category := by
  apply CategoryTheory.essentiallySmall_iff_of_thin.mpr
  exact small_of_injective skeletonContextCode_injective

private noncomputable instance finiteSiteEssentiallySmall :
    EssentiallySmall.{0} finiteSite.category :=
  finiteSite_essentiallySmall

private abbrev coefficientBase (k : Type) [CommRing k] :=
  CommRingCat.of (ULift.{0} k)

private abbrev CoefficientUnder (k : Type) [CommRing k] :=
  Under (coefficientBase k)

private instance coefficientUnderHomFunLike {k : Type} [CommRing k]
    (A B : CoefficientUnder k) : FunLike (A ⟶ B) A B where
  coe f := f.right
  coe_injective' f g h := by
    ext x
    exact congrFun h x

private instance coefficientUnderConcreteCategory {k : Type} [CommRing k] :
    ConcreteCategory (CoefficientUnder k) (fun A B => A ⟶ B) where
  hom := id
  ofHom := id
  hom_ofHom _ := rfl
  ofHom_hom _ := rfl
  id_apply _ := rfl
  comp_apply _ _ _ := rfl

private instance coefficientUnderForgetPreservesLimits
    {k : Type} [CommRing k] :
    PreservesLimits (forget (CoefficientUnder k)) := by
  change PreservesLimits
    (Under.forget (coefficientBase k) ⋙ forget CommRingCat.{0})
  infer_instance

private instance coefficientUnderForgetReflectsIsomorphisms
    {k : Type} [CommRing k] :
    (forget (CoefficientUnder k)).ReflectsIsomorphisms := by
  change (Under.forget (coefficientBase k) ⋙
    forget CommRingCat.{0}).ReflectsIsomorphisms
  infer_instance

private instance coefficientUnderForgetPreservesFilteredColimits
    {k : Type} [CommRing k] :
    PreservesFilteredColimits (forget (CoefficientUnder k)) := by
  change PreservesFilteredColimits
    (Under.forget (coefficientBase k) ⋙ forget CommRingCat.{0})
  infer_instance

private theorem finiteCommRingHasSheafify
    (k : Type) [CommRing k] :
    HasSheafify finiteSite.topology
      (LawAlgebra.AATCommAlgCat.{0, 0} k) := by
  letI : EssentiallySmall.{0} finiteSite.category :=
    finiteSite_essentiallySmall
  exact CategoryTheory.hasSheafifyEssentiallySmallSite _ _

/-- Algebra-valued sheafification for integer coefficients on the finite reference site. -/
noncomputable instance finiteIntHasSheafify :
    HasSheafify finiteSite.topology
      (LawAlgebra.AATCommAlgCat.{0, 0} Int) :=
  finiteCommRingHasSheafify Int

/-- Algebra-valued sheafification for polynomial coefficients on the finite reference site. -/
noncomputable instance finitePolynomialIntHasSheafify :
    HasSheafify finiteSite.topology
      (LawAlgebra.AATCommAlgCat.{0, 0} (Polynomial Int)) :=
  finiteCommRingHasSheafify (Polynomial Int)

private noncomputable instance finiteSiteSmallModelThin :
    Quiver.IsThin (SmallModel.{0} finiteSite.category) := fun X Y => by
  constructor
  intro f g
  apply (equivSmallModel finiteSite.category).inverse.map_injective
  exact Subsingleton.elim _ _

private noncomputable def finiteSiteSmallEquivalence :
    finiteSite.category ≌
      ThinSkeleton (SmallModel.{0} finiteSite.category) :=
  (equivSmallModel finiteSite.category).trans
    (ThinSkeleton.equivalence (SmallModel.{0} finiteSite.category)).symm

private noncomputable def smallSkeletonContextCode :
    Skeleton (SmallModel.{0} finiteSite.category) → ContextCode :=
  fun W => skeletonContextCode
    ((equivSmallModel finiteSite.category).skeletonEquiv.symm W)

private noncomputable instance finiteContextCode : Finite ContextCode := by
  apply Finite.of_injective
    (fun c : ContextCode =>
      (c.support, c.axisNonempty, c.axisReadable,
        c.observableNonempty, c.observableReadable))
  intro c d h
  rcases c with ⟨cs, ca, car, co, cor⟩
  rcases d with ⟨ds, da, dar, dob, dor⟩
  simp only [Prod.mk.injEq] at h
  simp_all

private theorem smallSkeletonContextCode_injective :
    Function.Injective smallSkeletonContextCode :=
  skeletonContextCode_injective.comp
    (equivSmallModel finiteSite.category).skeletonEquiv.symm.injective

private noncomputable instance finiteSmallSkeleton :
    Finite (ThinSkeleton (SmallModel.{0} finiteSite.category)) :=
  Finite.of_injective smallSkeletonContextCode
    smallSkeletonContextCode_injective

private noncomputable abbrev finiteTopologySmall :
    GrothendieckTopology
      (ThinSkeleton (SmallModel.{0} finiteSite.category)) :=
  finiteSiteSmallEquivalence.inverse.inducedTopology finiteSite.topology

private noncomputable instance finiteCoverArrow
    {C : Type} [SmallCategory C] [FinCategory C]
    (J : GrothendieckTopology C) (X : C) (S : J.Cover X) :
    Finite S.Arrow := by
  apply Finite.of_injective
    (fun I : S.Arrow => (⟨I.Y, I.f⟩ : Σ Y : C, Y ⟶ X))
  intro I K h
  cases I
  cases K
  simp_all

private noncomputable instance finiteCoverArrowRelation
    {C : Type} [SmallCategory C] [FinCategory C]
    (J : GrothendieckTopology C) (X : C) (S : J.Cover X)
    (I K : S.Arrow) : Finite (I.Relation K) := by
  apply Finite.of_injective
    (fun r : I.Relation K =>
      (⟨r.Z, (r.g₁, r.g₂)⟩ :
        Σ Z : C, (Z ⟶ I.Y) × (Z ⟶ K.Y)))
  intro r s h
  cases r
  cases s
  simp only [Sigma.mk.inj_iff] at h
  rcases h with ⟨hZ, hpair⟩
  cases hZ
  cases hpair
  rfl

private noncomputable instance finiteCoverRelation
    {C : Type} [SmallCategory C] [FinCategory C]
    (J : GrothendieckTopology C) (X : C) (S : J.Cover X) :
    Finite S.Relation := by
  apply Finite.of_surjective
    (fun t : Σ I : S.Arrow, Σ K : S.Arrow, I.Relation K =>
      (⟨t.2.2⟩ : S.Relation))
  intro r
  exact ⟨⟨r.fst, r.snd, r.r⟩, by cases r; rfl⟩

private noncomputable instance coefficientExtensionSmallHasSheafCompose :
    finiteTopologySmall.HasSheafCompose
      (intPolynomialFlatChange.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{0, 0} Int ⥤
          LawAlgebra.AATCommAlgCat.{0, 0} (Polynomial Int)) := by
  letI : ∀ (X : ThinSkeleton (SmallModel.{0} finiteSite.category))
      (S : finiteTopologySmall.Cover X)
      (P : (ThinSkeleton (SmallModel.{0} finiteSite.category))ᵒᵖ ⥤
        LawAlgebra.AATCommAlgCat.{0, 0} Int),
      PreservesLimit (S.index P).multicospan
        (intPolynomialFlatChange.coefficientExtension :
          LawAlgebra.AATCommAlgCat.{0, 0} Int ⥤
            LawAlgebra.AATCommAlgCat.{0, 0} (Polynomial Int)) := by
    intro X S P
    classical
    letI : Fintype S.Arrow := Fintype.ofFinite S.Arrow
    letI : Fintype S.Relation := Fintype.ofFinite S.Relation
    letI : Fintype S.shape.L := by
      change Fintype S.Arrow
      exact Fintype.ofFinite S.Arrow
    letI : Fintype S.shape.R := by
      change Fintype S.Relation
      exact Fintype.ofFinite S.Relation
    letI : DecidableEq S.shape.L := Classical.decEq _
    letI : DecidableEq S.shape.R := Classical.decEq _
    letI : FinCategory (WalkingMulticospan S.shape) := by
      infer_instance
    infer_instance
  exact CategoryTheory.hasSheafCompose_of_preservesMulticospan _ _

/-- The flat extension from integers to integer polynomials preserves sheaves
on the actual finite reference-site topology.  Its matching limits are finite
after transport to the finite thin skeleton and are preserved by flat
coefficient extension. -/
noncomputable instance coefficientExtension_hasSheafCompose :
    finiteSite.topology.HasSheafCompose
      (intPolynomialFlatChange.coefficientExtension :
        LawAlgebra.AATCommAlgCat.{0, 0} Int ⥤
          LawAlgebra.AATCommAlgCat.{0, 0} (Polynomial Int)) :=
  finiteSiteSmallEquivalence.hasSheafCompose
    finiteSite.topology finiteTopologySmall _

/-- The changed finite affine chart is the canonical coefficient pullback. -/
noncomputable def coefficientSectionSpecBaseChangeIso_fires :
    LawAlgebra.architectureChartSpec
        (coefficientRaw.baseChange intPolynomialFlatChange.hom) finiteBase ≅
      pullback
        (AlgebraicGeometry.Scheme.Spec.map
          (coefficientRaw.toRingedSite.structureSheaf.val.obj
            (op finiteBase)).hom.op)
        (AlgebraicGeometry.Scheme.Spec.map
          (CommRingCat.ofHom intPolynomialFlatChange.liftedHom).op) :=
  LawAlgebra.RawAmbientRestrictionSystem.sheafifiedSectionSpecBaseChangeIso
    coefficientRaw intPolynomialFlatChange finiteBase

/-! ## Concrete coefficient geometry -/

private def coefficientProductObject
    (X Y : finiteSite.category) : finiteSite.category :=
  Site.ContextCategoryObject.of finiteSite.contextPreorder
    (Site.productContext X.ctx Y.ctx)

private noncomputable def coefficientProductLeft
    (X Y : finiteSite.category) : coefficientProductObject X Y ⟶ X :=
  homOfLE (Site.productContextFiniteMeet.meet_le_left X.ctx Y.ctx)

private noncomputable def coefficientProductRight
    (X Y : finiteSite.category) : coefficientProductObject X Y ⟶ Y :=
  homOfLE (Site.productContextFiniteMeet.meet_le_right X.ctx Y.ctx)

private theorem finiteSitePresheaf_isSheaf_of_bijective
    (P : CategoryTheory.Functor finiteSite.categoryᵒᵖ Type)
    (hbij : ∀ {X Y : finiteSite.category} (f : X ⟶ Y),
      Function.Bijective (P.map f.op)) :
    Presieve.IsSheaf finiteSite.topology P := by
  rw [Site.AATSite.topology, Site.AATGrothendieckTopology]
  rw [Precoverage.isSheaf_toGrothendieck_iff]
  intro X Y f R hR
  rcases hR with ⟨F, rfl⟩
  intro family hfamily
  classical
  rcases F.admissible.atomSupportCoverage
      FiniteModel.FiniteAtom.componentA (Or.inl rfl) with ⟨i, hi⟩
  let patchObject := Site.ContextCategoryObject.of finiteSite.contextPreorder
    (F.patch i)
  let Q := coefficientProductObject Y patchObject
  let q : Q ⟶ Y := coefficientProductLeft Y patchObject
  let qpatch : Q ⟶ patchObject := coefficientProductRight Y patchObject
  have hq : (Sieve.generate F.presieve).pullback f q := by
    change Sieve.generate F.presieve (q ≫ f)
    have hinclusion : Sieve.generate F.presieve
        (homOfLE (F.inclusion i)) :=
      Sieve.le_generate F.presieve _ (Presieve.ofArrows.mk i)
    have hcomp := (Sieve.generate F.presieve).downward_closed hinclusion qpatch
    convert hcomp using 1
  rcases (hbij q).2 (family q hq) with ⟨global, hglobal⟩
  refine ⟨global, ?_, ?_⟩
  · intro Z g hg
    let PQ := coefficientProductObject Z Q
    let pz : PQ ⟶ Z := coefficientProductLeft Z Q
    let pq : PQ ⟶ Q := coefficientProductRight Z Q
    apply (hbij pz).1
    have hcompat := hfamily pz pq hg hq (Subsingleton.elim _ _)
    calc
      P.map pz.op (P.map g.op global) =
          P.map pq.op (P.map q.op global) := by
            rw [← FunctorToTypes.map_comp_apply,
              ← FunctorToTypes.map_comp_apply]
            congr 2
      _ = P.map pq.op (family q hq) := by rw [hglobal]
      _ = P.map pz.op (family g hg) := hcompat.symm
  · intro other hother
    apply (hbij q).1
    rw [hglobal]
    exact hother q hq

private theorem coefficientRawRestriction_bijective
    {X Y : finiteSite.category} (f : X ⟶ Y) :
    Function.Bijective (coefficientRaw.toPresheaf.map f.op).right := by
  change Function.Bijective
    ((coefficientRaw.restrictionStable f).quotientDesc)
  let q := (coefficientRaw.restrictionStable f).quotientDesc
  let r := (coefficientRaw.restrictionStable f).restriction.polynomialMap
  have hr : r.comp r = RingHom.id _ := by
    have hsign :
        (LawAlgebra.FiniteExamples.RawPresheaf.gauge X *
          LawAlgebra.FiniteExamples.RawPresheaf.gauge Y) *
        (LawAlgebra.FiniteExamples.RawPresheaf.gauge X *
          LawAlgebra.FiniteExamples.RawPresheaf.gauge Y) = 1 := by
      calc
        _ = (LawAlgebra.FiniteExamples.RawPresheaf.gauge X *
              LawAlgebra.FiniteExamples.RawPresheaf.gauge X) *
            (LawAlgebra.FiniteExamples.RawPresheaf.gauge Y *
              LawAlgebra.FiniteExamples.RawPresheaf.gauge Y) := by ring
        _ = 1 := by
          rw [LawAlgebra.FiniteExamples.RawPresheaf.gauge_sq,
            LawAlgebra.FiniteExamples.RawPresheaf.gauge_sq, one_mul]
    apply MvPolynomial.ringHom_ext
    · intro z
      simp [r, LawAlgebra.TypedCoordinateRestriction.polynomialMap]
    · intro i
      cases i
      change
        (LawAlgebra.FiniteExamples.RawPresheaf.coordinateRestriction f).polynomialMap
            ((LawAlgebra.FiniteExamples.RawPresheaf.coordinateRestriction f).polynomialMap
              (MvPolynomial.X ())) =
          MvPolynomial.X ()
      rw [LawAlgebra.FiniteExamples.RawPresheaf.coordinateRestriction_polynomialMap_X,
        map_mul]
      erw [LawAlgebra.TypedCoordinateRestriction.polynomialMap_C]
      rw [LawAlgebra.FiniteExamples.RawPresheaf.coordinateRestriction_polynomialMap_X]
      rw [← mul_assoc]
      erw [← MvPolynomial.C.map_mul]
      rw [hsign, map_one, one_mul]
  have hinv : ∀ x, q (q x) = x := by
    intro x
    refine Quotient.inductionOn x ?_
    intro p
    change q (q ((coefficientRaw.relationFamily Y).quotientMap p)) =
      (coefficientRaw.relationFamily Y).quotientMap p
    rw [LawAlgebra.RestrictionStableStructuralRelations.quotientDesc_mk]
    change q ((coefficientRaw.relationFamily Y).quotientMap
      ((coefficientRaw.restrictionStable f).restriction.polynomialMap p)) =
        (coefficientRaw.relationFamily Y).quotientMap p
    rw [LawAlgebra.RestrictionStableStructuralRelations.quotientDesc_mk]
    change (coefficientRaw.relationFamily Y).quotientMap
        ((r.comp r) p) =
      (coefficientRaw.relationFamily Y).quotientMap p
    rw [hr]
    rfl
  exact ⟨fun x y h => by
      calc
        x = q (q x) := (hinv x).symm
        _ = q (q y) := congrArg q h
        _ = y := hinv y,
    fun y => ⟨q y, hinv y⟩⟩

private theorem coefficientRawPresheaf_isSheaf :
    Presheaf.IsSheaf finiteSite.topology coefficientRaw.toPresheaf := by
  intro E
  apply finiteSitePresheaf_isSheaf_of_bijective
  intro X Y f
  letI : IsIso (coefficientRaw.toPresheaf.map f.op) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    exact coefficientRawRestriction_bijective f
  change Function.Bijective (fun g : E ⟶
    coefficientRaw.toPresheaf.obj (op Y) =>
      g ≫ coefficientRaw.toPresheaf.map f.op)
  constructor
  · intro a b h
    exact (cancel_mono (coefficientRaw.toPresheaf.map f.op)).mp h
  · intro b
    exact ⟨b ≫ inv (coefficientRaw.toPresheaf.map f.op), by simp⟩

/-- The concrete source geometry is the actual single-affine chart at the finite base context. -/
noncomputable def coefficientScheme :
    LawAlgebra.StandardArchitectureScheme coefficientRaw :=
  LawAlgebra.StandardArchitectureScheme.singleAffine coefficientRaw finiteBase

private theorem coefficientRawRestriction_id
    (W : finiteSite.category) (x : coefficientRaw.rawAlgebra W) :
    (coefficientRaw.restrictionStable (𝟙 W)).quotientDesc x = x := by
  have h := congrArg (fun q => q x) (coefficientRaw.quotientDesc_id W)
  simpa using h

private theorem coefficientRawRestriction_comp
    {W₀ W₁ W₂ : finiteSite.category}
    (f : W₀ ⟶ W₁) (g : W₁ ⟶ W₂)
    (x : coefficientRaw.rawAlgebra W₂) :
    (coefficientRaw.restrictionStable (f ≫ g)).quotientDesc x =
      (coefficientRaw.restrictionStable f).quotientDesc
        ((coefficientRaw.restrictionStable g).quotientDesc x) := by
  have h := congrArg (fun q => q x) (coefficientRaw.quotientDesc_comp f g)
  simpa [RingHom.comp_apply] using h

/-- The coefficient firing core generates the proper equation `(2)` from its selected atom. -/
noncomputable def coefficientSemanticCore :
    ArchitecturalEquationSystem finiteSite.contextPreorder where
  Index := finiteSite.equationSystem.Index
  role := finiteSite.equationSystem.role
  Observable W := coefficientRaw.rawAlgebra W
  observableCommRing W := inferInstance
  restrict f := (coefficientRaw.restrictionStable f).quotientDesc
  restrict_id := coefficientRawRestriction_id
  restrict_comp := coefficientRawRestriction_comp
  violationCoordinate W _ atom :=
    match atom with
    | FiniteModel.FiniteAtom.componentA => 2
    | _ => 0
  violationCoordinate_restrict := by
    intro source target f lawIndex atom
    cases atom <;> simp only [map_ofNat, map_zero]
  equationResidual W A _i _atom :=
    (FiniteModel.noCycleResidual A : coefficientRaw.rawAlgebra W)
  equationResidual_restrict := by
    intro source target f A i atom
    rw [map_intCast]

/-- The semantic observable ring is identified with the selected raw quotient objectwise. -/
noncomputable def coefficientBridge :
    LawAlgebra.SemanticLawEquationSchemeBridge
      coefficientRaw coefficientSemanticCore where
  toRawPresentation W := RingEquiv.refl (coefficientRaw.rawAlgebra W)

/-- The identity presentation is restriction-natural and its canonical units are invertible. -/
theorem coefficientBridge_valid :
    LawAlgebra.IsSemanticLawEquationSchemeBridge
      coefficientRaw coefficientSemanticCore coefficientBridge where
  restriction_natural := by
    intro source target f x
    have hn := coefficientRaw.toRingedSite.canonical.naturality f.op
    have ha := congrArg (fun q => q.right x) hn
    change
      (coefficientRaw.toRingedSite.canonical.app (op source)).right
          ((coefficientRaw.restrictionStable f).quotientDesc x) =
        (coefficientRaw.toRingedSite.structureSheaf.val.map f.op).right
          ((coefficientRaw.toRingedSite.canonical.app (op target)).right x)
    simpa only [CommRingCat.comp_apply,
      LawAlgebra.RawAmbientRestrictionSystem.toRingedSite_raw] using ha
  presentation_stable W := {
    canonical_isIso := by
      haveI : IsIso (CategoryTheory.toSheafify
          finiteSite.topology coefficientRaw.toPresheaf) :=
        CategoryTheory.isIso_toSheafify finiteSite.topology
          coefficientRawPresheaf_isSheaf
      change IsIso ((CategoryTheory.toSheafify
        finiteSite.topology coefficientRaw.toPresheaf).app (op W))
      infer_instance }

/-- The concrete bridge realizes the semantic-core ideal sheaf on the source chart. -/
theorem coefficientSemanticCore_realized :
    LawAlgebra.SemanticCoreIdealSheafRealized coefficientRaw coefficientScheme
      coefficientSemanticCore coefficientBridge :=
  LawAlgebra.semanticCoreIdealSheaf_realized coefficientRaw coefficientScheme
    coefficientSemanticCore coefficientBridge coefficientBridge_valid

/-- The realized source equation agrees with its transported equation on the changed chart. -/
theorem coefficientSemanticCore_baseChangedChart
    (j : coefficientScheme.atlas.Index)
    (i : finiteSite.equationSystem.Index) :
    let R' :=
      LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore
        coefficientRaw coefficientScheme coefficientSemanticCore
          coefficientBridge intPolynomialFlatChange
    let hR' :=
      (LawAlgebra.ClosedEquationalLawReading.baseChangeOfSemanticCore_valid
        coefficientRaw coefficientScheme coefficientSemanticCore
          coefficientBridge intPolynomialFlatChange).witness_compatible
    let j' := cast
      (coefficientScheme.baseChangedAtlas_Index
        coefficientRaw intPolynomialFlatChange).symm j
    Scheme.IdealSheafData.comap
        (Scheme.IdealSheafData.ofIdealTop
          (X := (coefficientScheme.atlas.chart j).domain)
          (Ideal.map
            (AlgebraicGeometry.Scheme.ΓSpecIso
              (LawAlgebra.SheafifiedSectionRing coefficientRaw
                (coefficientScheme.atlas.chart j).context)).inv.hom
            (Ideal.map
              (coefficientBridge.toSheafifiedSection
                (coefficientScheme.atlas.chart j).context)
              (coefficientSemanticCore.witnessIdeal
                (coefficientScheme.atlas.chart j).context i))))
        (coefficientScheme.baseChangedChartMap
          coefficientRaw intPolynomialFlatChange j) =
      Scheme.IdealSheafData.comap
        (LawAlgebra.lawWitnessIdealSheaf
          (coefficientRaw.baseChange intPolynomialFlatChange.hom)
          (coefficientScheme.baseChange
            coefficientRaw intPolynomialFlatChange)
          R' hR' i (Set.mem_univ i))
        ((coefficientScheme.baseChangedAtlas
          coefficientRaw intPolynomialFlatChange).chart j').map :=
  LawAlgebra.semanticCoreLawWitnessIdeal_baseChangedChart
    coefficientRaw coefficientScheme coefficientSemanticCore
      coefficientBridge coefficientBridge_valid intPolynomialFlatChange j i

open AAT.AG.LawAlgebra

private abbrev targetRaw :=
  coefficientRaw.baseChange intPolynomialFlatChange.hom

private abbrev targetScheme :=
  coefficientScheme.baseChange coefficientRaw intPolynomialFlatChange

private abbrev targetReading :=
  ClosedEquationalLawReading.baseChangeOfSemanticCore coefficientRaw
    coefficientScheme coefficientSemanticCore coefficientBridge
      intPolynomialFlatChange

private theorem targetReadingValid :
    IsClosedEquationalLawReading targetRaw targetScheme targetReading :=
  ClosedEquationalLawReading.baseChangeOfSemanticCore_valid coefficientRaw
    coefficientScheme coefficientSemanticCore coefficientBridge
      intPolynomialFlatChange

private theorem targetRequired :
    RequiredClosed targetRaw targetScheme targetReading :=
  ClosedEquationalLawReading.baseChangeOfSemanticCore_requiredClosed coefficientRaw
    coefficientScheme coefficientSemanticCore coefficientBridge
      intPolynomialFlatChange

private abbrev targetLawIdeal : targetScheme.underlying.IdealSheafData :=
  lawGeneratedIdealSheaf targetRaw targetScheme targetReading
    targetReadingValid targetRequired

private abbrev targetLawful : Scheme :=
  lawfulClosedSubscheme targetRaw targetScheme targetReading
    targetReadingValid targetRequired

private abbrev targetImmersion : targetLawful ⟶ targetScheme.underlying :=
  lawfulClosedImmersion targetRaw targetScheme targetReading
    targetReadingValid targetRequired

private def coeffEval (z : ZMod 2) : Polynomial Int →+* ZMod 2 :=
  Polynomial.eval₂RingHom (Int.castRingHom (ZMod 2)) z

private def ambientEval (z : ZMod 2) :
    MvPolynomial Unit (Polynomial Int) →+* ZMod 2 :=
  MvPolynomial.eval₂Hom (coeffEval z) (fun _ => 1)

private theorem target_JStruct_le_ker (z : ZMod 2) :
    (targetRaw.relationFamily finiteBase).JStruct ≤
      RingHom.ker (ambientEval z) := by
  rw [StructuralRelationFamily.JStruct]
  apply Ideal.span_le.mpr
  rintro p ⟨r, rfl⟩
  cases r
  simp [RawAmbientRestrictionSystem.baseChange, ambientEval, coeffEval,
    LawAlgebra.StructuralRelationFamily.baseChange, coefficientRaw,
    LawAlgebra.FiniteExamples.RawPresheaf.system,
    LawAlgebra.FiniteExamples.RawPresheaf.relationFamily]
  have hx := MvPolynomial.eval₂Hom_X'
    (Polynomial.eval₂RingHom (Int.castRingHom (ZMod 2)) z)
    (fun _ : Unit => (1 : ZMod 2)) ()
  apply sub_eq_zero.mpr
  exact hx

private def targetRawEval (z : ZMod 2) :
    targetRaw.rawAlgebra finiteBase →+* ZMod 2 :=
  Ideal.Quotient.lift _ (ambientEval z) (target_JStruct_le_ker z)

private def sourceIndex : coefficientScheme.atlas.Index :=
  StandardArchitectureScheme.singleAffineIndex coefficientRaw finiteBase

private def targetIndex : targetScheme.atlas.Index :=
  cast (coefficientScheme.baseChangedAtlas_Index coefficientRaw
    intPolynomialFlatChange).symm sourceIndex

private noncomputable def changedChartMap :
    (targetScheme.atlas.chart targetIndex).domain ⟶ targetScheme.underlying :=
  (targetScheme.atlas.chart targetIndex).map

private theorem changedChartMap_surjective :
    Function.Surjective changedChartMap := by
  letI : Subsingleton coefficientScheme.atlas.Index :=
    StandardArchitectureScheme.singleAffine_index_subsingleton
      coefficientRaw finiteBase
  letI : Subsingleton targetScheme.atlas.Index := by
    change Subsingleton coefficientScheme.atlas.Index
    infer_instance
  intro x
  rcases targetScheme.atlasValid.covers x with ⟨j, y, hy⟩
  have hj : j = targetIndex := Subsingleton.elim _ _
  subst j
  exact ⟨y, hy⟩

private theorem changedChartMap_isIso : IsIso changedChartMap := by
  letI : IsOpenImmersion changedChartMap :=
    (targetScheme.atlasValid.chart_valid targetIndex).isOpenImmersion
  letI : Epi changedChartMap.base :=
    ConcreteCategory.epi_of_surjective _ changedChartMap_surjective
  apply IsOpenImmersion.isIso

attribute [local instance] changedChartMap_isIso

private local instance targetSchemeIsAffine : IsAffine targetScheme.underlying := by
  letI : IsAffine (targetScheme.atlas.chart targetIndex).domain :=
    (targetScheme.atlas.chart targetIndex).domain_isAffine
  exact IsAffine.of_isIso (inv changedChartMap)

private noncomputable instance coefficientCanonicalIsIso :
    IsIso (coefficientRaw.toRingedSite.canonical.app (op finiteBase)) :=
  coefficientBridge_valid.presentation_stable finiteBase |>.canonical_isIso

private noncomputable def sourceRawEvalInt :
    coefficientRaw.rawAlgebra finiteBase →+* Int :=
  LawAlgebra.FiniteExamples.RawPresheaf.quotientOneEval.comp
    (coefficientRaw.restrictionStable
      LawAlgebra.FiniteExamples.RawPresheaf.leftToBase).quotientDesc

private theorem sourceRawEvalInt_intCast (z : Int) : sourceRawEvalInt z = z := by
  change LawAlgebra.FiniteExamples.RawPresheaf.quotientOneEval
    ((coefficientRaw.restrictionStable
      LawAlgebra.FiniteExamples.RawPresheaf.leftToBase).quotientDesc z) = z
  simp

private noncomputable def sourceRawEvalAlg :
    coefficientRaw.rawAlgebra finiteBase →ₐ[Int] Int where
  __ := sourceRawEvalInt
  commutes' := sourceRawEvalInt_intCast

private noncomputable def sourceEvalAlg :
    SheafifiedSectionRing coefficientRaw finiteBase →ₐ[Int] ZMod 2 :=
  (Algebra.ofId Int (ZMod 2)).comp
    (sourceRawEvalAlg.comp
      (coefficientBridge_valid.presentation_stable finiteBase).comparison.toAlgHom)

private abbrev oldObject :=
  coefficientRaw.toRingedSite.structureSheaf.val.obj (op finiteBase)

private abbrev newObject :=
  targetRaw.toRingedSite.structureSheaf.val.obj (op finiteBase)

private noncomputable def sourceEval :
    oldObject.right ⟶ CommRingCat.of (ZMod 2) :=
  CommRingCat.ofHom sourceEvalAlg.toRingHom

private noncomputable def coeffEvalCat (z : ZMod 2) :
    CommRingCat.of (ULift (Polynomial Int)) ⟶ CommRingCat.of (ZMod 2) :=
  CommRingCat.ofHom ((coeffEval z).comp ULift.ringEquiv.toRingHom)

private theorem actualCompatibility (z : ZMod 2) :
    oldObject.hom ≫ sourceEval =
      CommRingCat.ofHom intPolynomialFlatChange.liftedHom ≫ coeffEvalCat z := by
  apply CommRingCat.hom_ext
  ext x
  rcases x with ⟨x⟩
  change sourceEvalAlg (algebraMap Int
      (SheafifiedSectionRing coefficientRaw finiteBase) x) =
    coeffEval z (Polynomial.C x)
  rw [sourceEvalAlg.commutes]
  simp [coeffEval]

private noncomputable def targetEval (z : ZMod 2) :
    newObject.right ⟶ CommRingCat.of (ZMod 2) :=
  (RawAmbientRestrictionSystem.sheafifiedSectionObjectBaseChangeIso
    coefficientRaw intPolynomialFlatChange finiteBase).inv.right ≫
      pushout.desc sourceEval (coeffEvalCat z) (actualCompatibility z)

private theorem targetEval_source (z : ZMod 2) :
    RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
        coefficientRaw intPolynomialFlatChange finiteBase ≫
      targetEval z = sourceEval := by
  simp [targetEval,
    RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap_eq]

private theorem targetEval_coefficient (z : ZMod 2) :
    newObject.hom ≫ targetEval z = coeffEvalCat z := by
  let e := RawAmbientRestrictionSystem.sheafifiedSectionObjectBaseChangeIso
    coefficientRaw intPolynomialFlatChange finiteBase
  rw [targetEval]
  rw [← Category.assoc]
  have hw : newObject.hom ≫ e.inv.right =
      (intPolynomialFlatChange.coefficientExtension.obj oldObject).hom := by
    exact e.inv.w.symm
  rw [hw]
  change pushout.inr oldObject.hom
      (CommRingCat.ofHom intPolynomialFlatChange.liftedHom) ≫
        pushout.desc sourceEval (coeffEvalCat z) (actualCompatibility z) = coeffEvalCat z
  rw [pushout.inr_desc]

private theorem sourceEval_two :
    sourceEval
        ((sheafificationUnitAlgHom coefficientRaw finiteBase)
          (2 : coefficientRaw.rawAlgebra finiteBase)) = 0 := by
  change sourceEvalAlg
      ((sheafificationUnitAlgHom coefficientRaw finiteBase)
        (2 : coefficientRaw.rawAlgebra finiteBase)) = 0
  let P := coefficientBridge_valid.presentation_stable finiteBase
  have hc : P.comparison
      ((sheafificationUnitAlgHom coefficientRaw finiteBase) 2) = 2 := by
    rw [← P.comparison_symm_toAlgHom]
    exact P.comparison.apply_symm_apply _
  change ((Algebra.ofId Int (ZMod 2)).comp
    (sourceRawEvalAlg.comp P.comparison.toAlgHom))
      ((sheafificationUnitAlgHom coefficientRaw finiteBase) 2) = 0
  rw [AlgHom.comp_apply, AlgHom.comp_apply]
  calc
    _ = (Algebra.ofId Int (ZMod 2)) (sourceRawEvalAlg 2) := by
      exact congrArg
        (fun y => (Algebra.ofId Int (ZMod 2)) (sourceRawEvalAlg y)) hc
    _ = 0 := by
      change ((sourceRawEvalInt 2 : Int) : ZMod 2) = 0
      have htwo : (2 : coefficientRaw.rawAlgebra finiteBase) =
          algebraMap Int (coefficientRaw.rawAlgebra finiteBase) 2 := by
        norm_num
      rw [htwo]
      change ((sourceRawEvalInt
        ((2 : Int) : coefficientRaw.rawAlgebra finiteBase) : Int) : ZMod 2) = 0
      rw [sourceRawEvalInt_intCast]
      change (2 : ZMod 2) = 0
      decide

private noncomputable def targetAmbientEval (z : ZMod 2) :
    Γ(targetScheme.underlying, ⊤) →+* ZMod 2 :=
  (changedChartMap.appTop ≫
    (Scheme.ΓSpecIso (SheafifiedSectionRing targetRaw finiteBase)).hom ≫
    targetEval z).hom

private theorem targetInterpretation_chart :
    targetScheme.decoration.interpretation ≫ changedChartMap.appTop ≫
        (Scheme.ΓSpecIso (SheafifiedSectionRing targetRaw finiteBase)).hom =
      𝟙 _ := by
  have h := (targetScheme.atlasValid.chart_valid targetIndex).interpretation_compatible
  change sheafifiedRestriction targetRaw (𝟙 finiteBase) = _ at h
  simpa only [sheafifiedRestriction_id] using h.symm

private theorem targetAmbientEval_baseChanged_interpretation (z : ZMod 2)
    (x : SheafifiedSectionRing coefficientRaw finiteBase) :
    targetAmbientEval z
        ((coefficientScheme.baseChangeMap coefficientRaw intPolynomialFlatChange).appTop
          (coefficientScheme.decoration.interpretation x)) =
      sourceEval x := by
  have hdecor := coefficientScheme.baseChangedDecoration_interpretation
    coefficientRaw intPolynomialFlatChange
  have hcomp :
      coefficientScheme.decoration.interpretation ≫
          (coefficientScheme.baseChangeMap coefficientRaw intPolynomialFlatChange).appTop ≫
          changedChartMap.appTop ≫
          (Scheme.ΓSpecIso (SheafifiedSectionRing targetRaw finiteBase)).hom ≫
          targetEval z =
        sourceEval := by
    have hd := congrArg
      (fun q => q ≫ changedChartMap.appTop ≫
        (Scheme.ΓSpecIso (SheafifiedSectionRing targetRaw finiteBase)).hom ≫
        targetEval z) hdecor
    have hchart := congrArg
      (fun q =>
        RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
            coefficientRaw intPolynomialFlatChange finiteBase ≫ q ≫ targetEval z)
      targetInterpretation_chart
    calc
      _ = RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
              coefficientRaw intPolynomialFlatChange finiteBase ≫
            targetScheme.decoration.interpretation ≫ changedChartMap.appTop ≫
            (Scheme.ΓSpecIso
              (SheafifiedSectionRing targetRaw finiteBase)).hom ≫
            targetEval z := by
              simpa only [Category.assoc] using hd.symm
      _ = RawAmbientRestrictionSystem.sheafifiedSectionBaseChangeMap
              coefficientRaw intPolynomialFlatChange finiteBase ≫ targetEval z := by
              simpa only [Category.assoc, Category.comp_id, Category.id_comp] using hchart
      _ = sourceEval := targetEval_source z
  exact congrArg (fun f => f x) hcomp

private theorem targetEquation_eval_zero (z : ZMod 2)
    (i : finiteSite.equationSystem.Index)
    (atom : FiniteModel.FiniteAtom) :
    targetAmbientEval z
      (baseChangedSemanticCoreGlobalEquation coefficientRaw coefficientScheme
      coefficientSemanticCore coefficientBridge intPolynomialFlatChange i atom) = 0 := by
  cases i
  rw [baseChangedSemanticCoreGlobalEquation]
  rw [semanticCoreGlobalEquation]
  rw [targetAmbientEval_baseChanged_interpretation]
  cases atom <;>
    simp [coefficientSemanticCore, coefficientBridge,
      SemanticLawEquationSchemeBridge.toSheafifiedSection] ;
    simpa only using sourceEval_two

private theorem targetLawIdeal_le_ker (z : ZMod 2) :
    targetLawIdeal.ideal ⟨⊤, isAffineOpen_top _⟩ ≤
      RingHom.ker (targetAmbientEval z) := by
  rw [lawGeneratedIdealSheaf_ideal]
  refine iSup_le fun i => ?_
  rw [localLawWitnessIdeal]
  apply Ideal.span_le.mpr
  rintro x ⟨atom, rfl⟩
  change targetAmbientEval z
    ((targetReading.witness i.1 (targetRequired.closed i.1 i.2.1)).coordinate
      ⟨⊤, isAffineOpen_top _⟩ atom) = 0
  simpa [targetReading, ClosedEquationalLawReading.baseChangeOfSemanticCore,
    ClosedEquationalLawWitness.ofGlobalSections_coordinate] using
      targetEquation_eval_zero z i.1 atom


private noncomputable def targetLawfulTopIso :
    Γ(targetLawful, ⊤) ≅ CommRingCat.of
      (Γ(targetScheme.underlying, ⊤) ⧸
        targetLawIdeal.ideal ⟨⊤, isAffineOpen_top _⟩) :=
  targetLawIdeal.subschemeObjIso
    (⟨⊤, isAffineOpen_top _⟩ : targetScheme.underlying.affineOpens)

private theorem targetImmersion_appTop_topIso :
    targetImmersion.appTop ≫ targetLawfulTopIso.hom =
      CommRingCat.ofHom
        (Ideal.Quotient.mk
          (targetLawIdeal.ideal ⟨⊤, isAffineOpen_top targetScheme.underlying⟩)) := by
  let U : targetScheme.underlying.affineOpens :=
    ⟨⊤, isAffineOpen_top targetScheme.underlying⟩
  have h := targetLawIdeal.subschemeι_app U
  have hc := congrArg (fun q => q ≫ targetLawfulTopIso.hom) h
  simpa only [U, targetLawfulTopIso, Category.assoc, Iso.inv_hom_id,
    Category.comp_id] using hc

private noncomputable def targetLawfulQuotientEval (z : ZMod 2) :
    (Γ(targetScheme.underlying, ⊤) ⧸
      targetLawIdeal.ideal ⟨⊤, isAffineOpen_top _⟩) →+* ZMod 2 :=
  Ideal.Quotient.lift _ (targetAmbientEval z) (targetLawIdeal_le_ker z)

private noncomputable def targetLawfulEval (z : ZMod 2) :
    Γ(targetLawful, ⊤) →+* ZMod 2 :=
  (targetLawfulQuotientEval z).comp targetLawfulTopIso.hom.hom

private theorem targetLawfulEval_on_immersion (z : ZMod 2)
    (x : Γ(targetScheme.underlying, ⊤)) :
    targetLawfulEval z (targetImmersion.appTop x) = targetAmbientEval z x := by
  have h := ConcreteCategory.congr_hom targetImmersion_appTop_topIso x
  simpa [targetLawfulEval, targetLawfulQuotientEval] using
    congrArg (targetLawfulQuotientEval z) h

private noncomputable def targetChartSections :
    Γ(targetScheme.underlying, ⊤) ⟶ SheafifiedSectionRing targetRaw finiteBase :=
  changedChartMap.appTop ≫
    (Scheme.ΓSpecIso (SheafifiedSectionRing targetRaw finiteBase)).hom

private noncomputable instance targetChartSectionsIsIso :
    IsIso targetChartSections := by
  dsimp only [targetChartSections]
  infer_instance

private noncomputable def targetAmbientCoefficientX :
    Γ(targetScheme.underlying, ⊤) :=
  inv targetChartSections
    (newObject.hom (ULift.up (Polynomial.X : Polynomial Int)))

private theorem targetAmbientEval_coefficientX (z : ZMod 2) :
    targetAmbientEval z targetAmbientCoefficientX = z := by
  have hsection : targetChartSections targetAmbientCoefficientX =
      newObject.hom (ULift.up (Polynomial.X : Polynomial Int)) := by
    simp [targetAmbientCoefficientX]
  have hcoeff := ConcreteCategory.congr_hom (targetEval_coefficient z)
    (ULift.up (Polynomial.X : Polynomial Int))
  change targetEval z (targetChartSections targetAmbientCoefficientX) = z
  rw [hsection]
  calc
    _ = coeffEvalCat z (ULift.up (Polynomial.X : Polynomial Int)) := by
      simpa only [ConcreteCategory.comp_apply] using hcoeff
    _ = z := by
      change Polynomial.eval₂ (Int.castRingHom (ZMod 2)) z Polynomial.X = z
      simp

private noncomputable def targetLawfulCoefficientX : Γ(targetLawful, ⊤) :=
  targetImmersion.appTop targetAmbientCoefficientX

private theorem targetLawfulEval_coefficientX (z : ZMod 2) :
    targetLawfulEval z targetLawfulCoefficientX = z := by
  rw [targetLawfulCoefficientX, targetLawfulEval_on_immersion,
    targetAmbientEval_coefficientX]

private theorem targetLawfulEval_ne :
    targetLawfulEval 0 ≠ targetLawfulEval 1 := by
  intro h
  have hx := DFunLike.congr_fun h targetLawfulCoefficientX
  rw [targetLawfulEval_coefficientX, targetLawfulEval_coefficientX] at hx
  norm_num at hx

private noncomputable instance sourceInterpretationIsIso :
    IsIso coefficientScheme.decoration.interpretation := by
  change IsIso
    ((Scheme.ΓSpecIso (SheafifiedSectionRing coefficientRaw finiteBase)).inv)
  infer_instance

private theorem targetAmbientEval_agree_on_baseMap
    (x : Γ(coefficientScheme.underlying, ⊤)) :
    targetAmbientEval 0
        ((coefficientScheme.baseChangeMap coefficientRaw intPolynomialFlatChange).appTop x) =
      targetAmbientEval 1
        ((coefficientScheme.baseChangeMap coefficientRaw intPolynomialFlatChange).appTop x) := by
  rcases (ConcreteCategory.bijective_of_isIso
    coefficientScheme.decoration.interpretation).2 x with ⟨y, rfl⟩
  exact (targetAmbientEval_baseChanged_interpretation 0 y).trans
    (targetAmbientEval_baseChanged_interpretation 1 y).symm

private abbrev sourceReading :=
  ClosedEquationalLawReading.ofSemanticCore coefficientRaw coefficientScheme
    coefficientSemanticCore coefficientBridge

private theorem sourceReadingValid :
    IsClosedEquationalLawReading coefficientRaw coefficientScheme sourceReading :=
  ClosedEquationalLawReading.ofSemanticCore_valid coefficientRaw coefficientScheme
    coefficientSemanticCore coefficientBridge

private theorem sourceRequired :
    RequiredClosed coefficientRaw coefficientScheme sourceReading :=
  ClosedEquationalLawReading.ofSemanticCore_requiredClosed coefficientRaw coefficientScheme
    coefficientSemanticCore coefficientBridge

private abbrev sourceLawful : Scheme :=
  lawfulClosedSubscheme coefficientRaw coefficientScheme sourceReading
    sourceReadingValid sourceRequired

private abbrev sourceImmersion : sourceLawful ⟶ coefficientScheme.underlying :=
  lawfulClosedImmersion coefficientRaw coefficientScheme sourceReading
    sourceReadingValid sourceRequired

private abbrev lawfulComparison : targetLawful ⟶ sourceLawful :=
  lawfulClosedSubschemeBaseChangeMap coefficientRaw coefficientScheme
    coefficientSemanticCore coefficientBridge intPolynomialFlatChange

private local instance sourceSchemeIsAffine :
    IsAffine coefficientScheme.underlying := by
  change IsAffine (Spec (SheafifiedSectionRing coefficientRaw finiteBase))
  infer_instance

private noncomputable local instance sourceImmersionClosed :
    IsClosedImmersion sourceImmersion := by
  dsimp only [sourceImmersion, lawfulClosedImmersion]
  infer_instance

private theorem lawfulComparison_appTop_immersion :
    sourceImmersion.appTop ≫ lawfulComparison.appTop =
      (coefficientScheme.baseChangeMap coefficientRaw intPolynomialFlatChange).appTop ≫
        targetImmersion.appTop := by
  have h := lawfulClosedSubschemeBaseChangeMap_immersion coefficientRaw coefficientScheme
    coefficientSemanticCore coefficientBridge intPolynomialFlatChange
  simpa only [Scheme.Hom.comp_appTop] using congrArg Scheme.Hom.appTop h

private theorem targetLawfulEval_agree_on_comparison
    (x : Γ(sourceLawful, ⊤)) :
    targetLawfulEval 0 (lawfulComparison.appTop x) =
      targetLawfulEval 1 (lawfulComparison.appTop x) := by
  rcases (IsClosedImmersion.isAffine_surjective_of_isAffine sourceImmersion).2 x with
    ⟨y, rfl⟩
  have himm := ConcreteCategory.congr_hom lawfulComparison_appTop_immersion y
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at himm
  rw [himm, targetLawfulEval_on_immersion, targetLawfulEval_on_immersion]
  exact targetAmbientEval_agree_on_baseMap y

private theorem lawfulComparison_not_surjective :
    ¬ Function.Surjective lawfulComparison.appTop := by
  intro hsurj
  apply targetLawfulEval_ne
  apply RingHom.ext
  intro y
  rcases hsurj y with ⟨x, rfl⟩
  exact targetLawfulEval_agree_on_comparison x

private theorem lawfulComparison_not_isIso : ¬ IsIso lawfulComparison := by
  intro h
  letI : IsIso lawfulComparison := h
  exact lawfulComparison_not_surjective
    (ConcreteCategory.bijective_of_isIso lawfulComparison.appTop).2


/-- The realized proper law ideal changes the lawful locus under polynomial coefficient extension. -/
theorem lawfulLocus_baseChange_fires :
    LawAlgebra.SemanticCoreIdealSheafRealized
        coefficientRaw coefficientScheme coefficientSemanticCore coefficientBridge ∧
    ¬ IsIso
      (LawAlgebra.lawfulClosedSubschemeBaseChangeMap
        coefficientRaw coefficientScheme coefficientSemanticCore
        coefficientBridge intPolynomialFlatChange) :=
  ⟨coefficientSemanticCore_realized, lawfulComparison_not_isIso⟩

end AAT.AG.ReadingFunctorialityFinite
