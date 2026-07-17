import Formal.AG.ReadingFunctoriality.Core
import Formal.AG.ReadingFunctoriality.Coverage
import Formal.AG.ReadingFunctoriality.Coefficient
import Formal.AG.ReadingFunctoriality.StandardSchemeCoefficient
import Formal.AG.ReadingFunctoriality.CoefficientGeometry
import Formal.AG.ReadingFunctoriality.LerayComparison
import Formal.AG.Examples.FiniteModel
import Formal.AG.LawAlgebra.ClosedEquationalGeometryFiniteExample
import Mathlib.Algebra.Category.ModuleCat.Adjunctions
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.CategoryTheory.Sites.EpiMono

/-!
# Reading-functoriality reference models

This module owns the positive and negative firing declarations fixed by Part 4
SD9.
-/

noncomputable section

namespace AAT.AG.ReadingFunctorialityFinite

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


end AAT.AG.ReadingFunctorialityFinite
