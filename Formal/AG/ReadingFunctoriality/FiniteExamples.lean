import Formal.AG.ReadingFunctoriality.Core
import Formal.AG.ReadingFunctoriality.Coverage
import Formal.AG.ReadingFunctoriality.Coefficient
import Formal.AG.ReadingFunctoriality.StandardSchemeCoefficient
import Formal.AG.ReadingFunctoriality.CoefficientGeometry
import Formal.AG.ReadingFunctoriality.LerayComparison
import Formal.AG.ReadingFunctoriality.LargeLerayComparison
import Formal.AG.ReadingFunctoriality.LinearLerayComparison
import Formal.AG.Examples.FiniteModel
import Formal.AG.LawAlgebra.ClosedEquationalGeometryFiniteExample
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
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
    lawWitnessCoverage := by
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
    lawWitnessCoverage := by
      intro witness hreq
      rcases coarseCover.admissible.lawWitnessCoverage witness hreq with h | h
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
      FiniteModel.lawUniverse FiniteModel.signature where
  requiredSupport := fun atom =>
    atom = FiniteModel.FiniteAtom.componentA ∨
      atom = FiniteModel.FiniteAtom.componentB
  requiredWitness := fun _ => True
  requiredAxis := fun _ => True
  supportVisibleOn := nonLeraySupportVisibleOn
  witnessVisibleOn := fun _ _ => True
  axisReadableOn := fun W _ =>
    W = nonLerayContext .left ∨ W = nonLerayContext .right
  boundaryVisibleOn := fun _ _ => True

/-- Independent AAT site carrying the selected strict-diamond countermodel. -/
noncomputable def nonLeraySite :
    Site.AATSite FiniteModel.corePackage.object where
  contextPreorder := nonLerayContextPreorder
  lawUniverse := FiniteModel.lawUniverse
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
    lawWitnessCoverage := by
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
    lawWitnessCoverage := by
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
    atom = FiniteModel.FiniteAtom.componentB

private def positiveTargetAllows (atom : FiniteModel.carrier.Atom) : Prop :=
  atom = FiniteModel.FiniteAtom.componentC

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

private def positiveLaw : Law FiniteModel.carrier where
  holds _ := False

private def positiveLawUniverse : LawUniverse FiniteModel.carrier where
  Index := PUnit
  law _ := positiveLaw
  role _ := LawRole.required
  witnessFamily := { Witness := PUnit, badWitness := fun _ _ => True }
  SelectedReading := PUnit
  selectedReading := PUnit.unit
  coverageAssumptions := True
  exactnessAssumptions := True

private def positiveSourceDatum : FiniteCircuitDatum FiniteModel.carrier where
  queries := [(.atomPresent FiniteModel.FiniteAtom.componentA, true)]

private def positiveTargetDatum : FiniteCircuitDatum FiniteModel.carrier where
  queries := [(.atomPresent FiniteModel.FiniteAtom.componentC, true)]

private noncomputable def positiveSourceCircuitReading :
    CircuitReading positiveLawUniverse where
  code _ := .exact positiveSourceDatum
  sound := by
    intro i A Q hmatches haccepts
    exact fun h => h

private noncomputable def positiveTargetCircuitReading :
    CircuitReading positiveLawUniverse where
  code _ := .exact positiveTargetDatum
  sound := by
    intro i A Q hmatches haccepts
    exact fun h => h

private noncomputable def positiveSourceLawReading :
    LawReading FiniteModel.carrier where
  lawUniverse := positiveLawUniverse
  circuits := positiveSourceCircuitReading

private noncomputable def positiveTargetLawReading :
    LawReading FiniteModel.carrier where
  lawUniverse := positiveLawUniverse
  circuits := positiveTargetCircuitReading

private noncomputable def positiveSourceCoreReading :
    CoreReading FiniteModel.carrier where
  doctrine := positiveExtractionDoctrine
  source := .source
  family_listFinite := ⟨FiniteModel.FiniteAtom.all,
    fun atom _ => FiniteModel.FiniteAtom.mem_all atom⟩
  composition := positiveCompositionReading
  objectReading := FiniteModel.objectReading
  lawReading := positiveSourceLawReading
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
  lawReading := positiveTargetLawReading
  invariantReading := FiniteModel.invariantFamily
  signatureReading := FiniteModel.signature
  operationReading := FiniteModel.operationReading

/-- Source core whose selected family contains the two distinguishable source atoms. -/
noncomputable def positiveSourceCore :
    AATCorePackage FiniteModel.carrier :=
  AATCorePackage.generate FiniteModel.axiomSystem positiveSourceCoreReading

/-- Target core whose selected family contains the common image atom. -/
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

private theorem positiveTargetFamily_eq_transport :
    positiveTargetCore.family =
      positiveSourceCore.family.transport positiveAtomMap := by
  ext atom
  constructor
  · intro htarget
    have hatom : atom = FiniteModel.FiniteAtom.componentC := by
      exact (positiveTargetCore_family_mem_iff atom).mp htarget
    subst atom
    exact ⟨FiniteModel.FiniteAtom.componentA, by
      exact (positiveSourceCore_family_mem_iff _).mpr (Or.inl rfl), rfl⟩
  · rintro ⟨source, hsource, rfl⟩
    exact (positiveTargetCore_family_mem_iff _).mpr rfl

private theorem positiveObjectMap_source_eq_target :
    positiveObjectMap positiveSourceCore.object = positiveTargetCore.object := by
  apply congrArg FiniteModel.objectOfConfiguration
  apply AtomConfiguration.ext
  · simpa [positiveSourceCore, positiveTargetCore,
      positiveSourceCoreReading, positiveTargetCoreReading,
      positiveCompositionReading] using positiveTargetFamily_eq_transport.symm
  · intro a b
    constructor
    · rintro ⟨source₁, source₂, h, _, _⟩
      exact False.elim h
    · intro h
      exact False.elim h
  · intro a b
    constructor
    · rintro ⟨source₁, source₂, h, _, _⟩
      exact False.elim h
    · intro h
      exact False.elim h

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
    intro atom h
    rw [positiveTargetFamily_eq_transport]
    exact h
  compositionMap := positiveCompositionMap
  compositionMap_atomMap := by intros; rfl
  objectMap := positiveObjectMap
  object_formation_eq := by intros; rfl
  base_reachable := by
    rw [positiveObjectMap_source_eq_target]
    exact OperationReading.Reachable.base
  configurationMap A := AtomConfiguration.transportHom positiveAtomMap A.configuration
  configurationMap_atomMap := by intros; rfl
  operationMap := positiveTransportOperation
  operation_naturality := by
    intro A B op
    apply ConfigurationHom.ext
    funext atom
    rfl
  lawMap := id
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

/-- Selected law of the positive finite model. -/
noncomputable def positiveLawIndex :
    positiveSourceCore.algebra.lawReading.lawUniverse.Index :=
  PUnit.unit

/-- Distinguished positive atom-presence query. -/
noncomputable def positiveQuery : CircuitQuery FiniteModel.carrier :=
  .atomPresent FiniteModel.FiniteAtom.componentA

/-- Positive circuit accepted at the selected source base object. -/
noncomputable def positiveCircuit :
    PositiveCircuitDatum positiveSourceCore
      positiveSourceCore.baseObject positiveLawIndex := by
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

/-- Transported positive circuit at the mapped base object and law. -/
def positiveCircuit_transport :
    PositiveCircuitDatum positiveTargetCore
      (positiveCoreChange.objMap positiveSourceCore.baseObject)
      (positiveCoreChange.lawMap positiveLawIndex) :=
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

private theorem exactAtomMap_componentA
    (f : SignedExactCoreReadingHom positiveSourceCore positiveTargetCore) :
    f.atomMap FiniteModel.FiniteAtom.componentA =
      FiniteModel.FiniteAtom.componentC := by
  have hsource : positiveSourceCore.family.mem FiniteModel.FiniteAtom.componentA := by
    exact (positiveSourceCore_family_mem_iff _).mpr (Or.inl rfl)
  have htransport :
      (positiveSourceCore.family.transport f.atomMap).mem
        (f.atomMap FiniteModel.FiniteAtom.componentA) :=
    ⟨_, hsource, rfl⟩
  rw [← f.extraction_eq] at htransport
  exact (positiveTargetCore_family_mem_iff _).mp htransport

private theorem exactAtomMap_componentB
    (f : SignedExactCoreReadingHom positiveSourceCore positiveTargetCore) :
    f.atomMap FiniteModel.FiniteAtom.componentB =
      FiniteModel.FiniteAtom.componentC := by
  have hsource : positiveSourceCore.family.mem FiniteModel.FiniteAtom.componentB := by
    exact (positiveSourceCore_family_mem_iff _).mpr (Or.inr rfl)
  have htransport :
      (positiveSourceCore.family.transport f.atomMap).mem
        (f.atomMap FiniteModel.FiniteAtom.componentB) :=
    ⟨_, hsource, rfl⟩
  rw [← f.extraction_eq] at htransport
  exact (positiveTargetCore_family_mem_iff _).mp htransport

private theorem exactObjectMap_singletons_eq
    (f : SignedExactCoreReadingHom positiveSourceCore positiveTargetCore) :
    f.objectMap (positiveSingletonObject FiniteModel.FiniteAtom.componentA) =
      f.objectMap (positiveSingletonObject FiniteModel.FiniteAtom.componentB) := by
  change f.objectMap
      (positiveSourceCore.reading.objectReading.object
        (positiveSingletonConfiguration FiniteModel.FiniteAtom.componentA)) =
    f.objectMap
      (positiveSourceCore.reading.objectReading.object
        (positiveSingletonConfiguration FiniteModel.FiniteAtom.componentB))
  rw [f.object_formation_eq, f.object_formation_eq]
  apply congrArg FiniteModel.objectOfConfiguration
  apply AtomConfiguration.ext
  · ext atom
    constructor
    · rintro ⟨source, hsource, rfl⟩
      change source = FiniteModel.FiniteAtom.componentA at hsource
      subst source
      exact ⟨FiniteModel.FiniteAtom.componentB, rfl, by
        rw [exactAtomMap_componentA f, exactAtomMap_componentB f]⟩
    · rintro ⟨source, hsource, rfl⟩
      change source = FiniteModel.FiniteAtom.componentB at hsource
      subst source
      exact ⟨FiniteModel.FiniteAtom.componentA, rfl, by
        rw [exactAtomMap_componentA f, exactAtomMap_componentB f]⟩
  · intro a b
    constructor <;> rintro ⟨source₁, source₂, h, _, _⟩ <;> exact False.elim h
  · intro a b
    constructor <;> rintro ⟨source₁, source₂, h, _, _⟩ <;> exact False.elim h

/-- The positive-only reading change cannot be strengthened to signed exactness. -/
theorem positiveOnly_not_signedExact :
    ¬ Nonempty
      (SignedExactCoreReadingHom positiveSourceCore positiveTargetCore) := by
  rintro ⟨f⟩
  have hA := (f.matches_iff negativeCircuit
    (positiveSingletonObject FiniteModel.FiniteAtom.componentA)).mp
      negativeCircuit_matches_componentA
  rw [exactObjectMap_singletons_eq f] at hA
  exact negativeCircuit_not_matches_componentB
    ((f.matches_iff negativeCircuit
      (positiveSingletonObject FiniteModel.FiniteAtom.componentB)).mpr hA)

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

private def exactLaw : Law FiniteModel.carrier where
  holds _ := False

private def exactLawUniverse : LawUniverse FiniteModel.carrier where
  Index := PUnit
  law _ := exactLaw
  role _ := LawRole.required
  witnessFamily := { Witness := PUnit, badWitness := fun _ _ => True }
  SelectedReading := PUnit
  selectedReading := PUnit.unit
  coverageAssumptions := True
  exactnessAssumptions := True

private def exactCircuitDatum : FiniteCircuitDatum FiniteModel.carrier where
  queries := [(.atomPresent FiniteModel.FiniteAtom.componentC, true)]

private noncomputable def exactCircuitReading :
    CircuitReading exactLawUniverse where
  code _ := .exact exactCircuitDatum
  sound := by
    intro i A Q hmatches haccepts
    exact fun h => h

private noncomputable def exactLawReading : LawReading FiniteModel.carrier where
  lawUniverse := exactLawUniverse
  circuits := exactCircuitReading

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
  lawReading := exactLawReading
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
    exactCircuitReading.accepts PUnit.unit datum = true ↔
      exactCircuitReading.accepts PUnit.unit (exactDatumMap datum) = true := by
  change (CircuitDetectorCode.exact exactCircuitDatum).eval datum = true ↔
    (CircuitDetectorCode.exact exactCircuitDatum).eval (exactDatumMap datum) = true
  rw [CircuitDetectorCode.eval_exact_eq_true_iff,
    CircuitDetectorCode.eval_exact_eq_true_iff]
  constructor
  · intro h
    subst datum
    rfl
  · intro h
    exact exactDatumMap_injective (by simpa using h)

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
  atomMap := exactAtomMap
  extraction_eq := exactFamily_transport
  composition_eq := exactComposition_eq
  objectMap := exactObjectMap
  object_formation_eq := by intros; rfl
  configurationMap A := AtomConfiguration.transportHom exactAtomMap A.configuration
  configurationMap_atomMap := by intros; rfl
  lawMap := id
  required_iff := by intro i; cases i; rfl
  law_holds_iff := by intro i A; cases i; rfl
  queryMap := exactDatumMap
  matches_iff := exactDatumMap_matches_iff
  accepts_iff := by intro i datum; cases i; exact exactDatumMap_accepts_iff datum
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
      FiniteModel.lawUniverse FiniteModel.signature where
  requiredSupport := fun atom =>
    atom = FiniteModel.FiniteAtom.componentA ∨
      atom = FiniteModel.FiniteAtom.componentB
  requiredWitness := fun _ => True
  requiredAxis := fun _ => True
  supportVisibleOn := finiteLinearSupportVisibleOn
  witnessVisibleOn := fun _ _ => True
  axisReadableOn := fun W _ =>
    W = finiteLinearContext .left ∨ W = finiteLinearContext .right
  boundaryVisibleOn := fun _ _ => True

/-- Independent AAT site used by the finite linear coefficient firing. -/
noncomputable def finiteLinearSite :
    Site.AATSite FiniteModel.corePackage.object where
  contextPreorder := finiteLinearContextPreorder
  lawUniverse := FiniteModel.lawUniverse
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
    lawWitnessCoverage := by
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


end AAT.AG.ReadingFunctorialityFinite
