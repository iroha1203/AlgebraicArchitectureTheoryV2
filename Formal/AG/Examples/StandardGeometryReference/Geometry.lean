import Formal.AG.Examples.FiniteModel
import Formal.AG.LawAlgebra.AffineChart
import Formal.AG.LawAlgebra.StandardScheme
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.ZMod
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Limits.Shapes.FiniteMultiequalizer

/-!
# Standard geometry reference: stable geometry

This module owns SD0--SD1: the fixed integer-polynomial data, selected site,
raw sheaf, localization presentations, and actual two-principal-open atlas.
It deliberately imports neither `LawEquation` nor
`ClosedEquationalGeometry`, so changes to the equation layer do not
invalidate these stable constructions.

## Implementation notes — R1 / SD0

* The context preorder is constructed from the approved selected-index order.
  The broader existing finite-model preorder was rejected because it admits
  arrows not present in the fixed SD0 statement.
* The overlap package is built for the full context category and specializes
  to `twoPatchContextMeet` on the selected contexts. Reusing a meet package
  for a different preorder would not establish the required pullback fields.
* The two `HasSheafify` instances are derived from small covers, finite
  multiequalizers, and the limit/colimit behavior of the under category.
  Supplying an arbitrary sheafification certificate was rejected.
* Raw sections use exactly the coordinate and two inverse variables, with two
  context-dependent relations. Restriction maps are the fixed piecewise
  variable images; arbitrary localization isomorphisms are not input data.
* The raw sheaf theorem is proved by principal-open gluing and reconstruction
  of ring and under-category morphisms. The localization presentations and
  their restriction equations are then derived from quotient and
  `IsLocalization.Away` universal properties.

## Implementation notes — R2 / SD1

These notes cover every nontrivial SD1 definition, including the chart-domain
isomorphisms, `leftChart`, `rightChart`, `referenceAtlas`,
`referenceOverlapPresentation`, `referenceScheme`, and `actualOverlapIso`.

* The scheme is the actual `Spec ℤ[x]`; its charts are the canonical
  localization-away morphisms for `x` and `1 - x`. The overlap is obtained
  from the localization pushout, and `referenceScheme` is assembled with
  `StandardArchitectureScheme.ofPresentation`. Reusing an existing
  two-chart fixture was rejected because it would not prove that these fixed
  proper principal opens and their nonempty mixed overlap are the selected
  atlas.
* Self-overlaps use identity pullback squares and mixed overlaps use the
  proved localization pullback. Accepting an arbitrary atlas, overlap
  isomorphism, or pullback certificate as fixture data was rejected because
  the construction and its provenance must be internal to this model.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace AAT.AG.Examples.StandardGeometryReferenceModels

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AAT.AG.LawAlgebra
open AlgebraicGeometry
open scoped AlgebraicGeometry Classical

noncomputable section

/--
SD0 fixture data declaration for the task-specific fixed polynomial data that feeds the Part II and Part III constructions.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
abbrev AmbientRing := MvPolynomial Unit Int

/--
SD0 constructor-provenance or no-unfold API lemma for the task-specific fixed polynomial data that feeds the Part II and Part III constructions.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem ambientRing_eq :
    AmbientRing = MvPolynomial Unit Int :=
  rfl

/--
SD0 fixture data declaration for the task-specific fixed polynomial data that feeds the Part II and Part III constructions.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def coordinate : AmbientRing := MvPolynomial.X ()

/--
SD0 constructor-provenance or no-unfold API lemma for the task-specific fixed polynomial data that feeds the Part II and Part III constructions.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem coordinate_eq :
    coordinate = MvPolynomial.X () :=
  rfl

/--
SD0 fixture data declaration for the task-specific fixed polynomial data that feeds the Part II and Part III constructions.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def leftGenerator : AmbientRing := coordinate

/--
SD0 constructor-provenance or no-unfold API lemma for the task-specific fixed polynomial data that feeds the Part II and Part III constructions.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem leftGenerator_eq :
    leftGenerator = coordinate :=
  rfl

/--
SD0 fixture data declaration for the task-specific fixed polynomial data that feeds the Part II and Part III constructions.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def rightGenerator : AmbientRing := 1 - coordinate

/--
SD0 constructor-provenance or no-unfold API lemma for the task-specific fixed polynomial data that feeds the Part II and Part III constructions.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem rightGenerator_eq :
    rightGenerator = 1 - coordinate :=
  rfl

/--
SD0 fixture data declaration for the task-specific fixed polynomial data that feeds the Part II and Part III constructions.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def overlapGenerator : AmbientRing := leftGenerator * rightGenerator

/--
SD0 constructor-provenance or no-unfold API lemma for the task-specific fixed polynomial data that feeds the Part II and Part III constructions.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem overlapGenerator_eq :
    overlapGenerator = leftGenerator * rightGenerator :=
  rfl

/--
SD0 fixture data declaration for the task-specific fixed polynomial data that feeds the Part II and Part III constructions.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def coverGenerator : Bool → AmbientRing
  | false => leftGenerator
  | true => rightGenerator

/--
SD0 constructor-provenance or no-unfold API lemma for the task-specific fixed polynomial data that feeds the Part II and Part III constructions.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem coverGenerator_false :
    coverGenerator false = leftGenerator :=
  rfl

/--
SD0 constructor-provenance or no-unfold API lemma for the task-specific fixed polynomial data that feeds the Part II and Part III constructions.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem coverGenerator_true :
    coverGenerator true = rightGenerator :=
  rfl

/--
SD0 main fixture theorem for the task-specific fixed polynomial data that feeds the Part II and Part III constructions.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem coverGenerator_span_eq_top :
    Ideal.span (Set.range coverGenerator) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have hleft : leftGenerator ∈ Ideal.span (Set.range coverGenerator) :=
    Ideal.subset_span (Set.mem_range_self false)
  have hright : rightGenerator ∈ Ideal.span (Set.range coverGenerator) :=
    Ideal.subset_span (Set.mem_range_self true)
  have hsum := Ideal.add_mem _ hleft hright
  simpa [leftGenerator, rightGenerator] using hsum

private theorem twoPatchContext_injective :
    Function.Injective AAT.AG.FiniteModel.twoPatchContext := by
  intro i j h
  cases i <;> cases j <;>
    simp_all [AAT.AG.FiniteModel.twoPatchContext]

private abbrev ReferenceLe
    (W V : Site.ArchCtx AAT.AG.FiniteModel.corePackage.object) : Prop :=
  W = V ∨
    ∃ i j : AAT.AG.FiniteModel.TwoPatchContextIndex,
      W = AAT.AG.FiniteModel.twoPatchContext i ∧
      V = AAT.AG.FiniteModel.twoPatchContext j ∧
      AAT.AG.FiniteModel.twoPatchContextIndexLe i j

private theorem referenceReadableMorphismExists
    {source target : Site.ArchCtx AAT.AG.FiniteModel.corePackage.object}
    (h : ReferenceLe source target) :
    ∃ f : Site.ContextMorphism source target, f.IsRestriction := by
  rcases h with rfl | ⟨i, j, rfl, rfl, _hij⟩
  · exact ⟨Site.identityContextMorphism _,
      ⟨fun h => h, fun h => h, fun h => h,
        fun h => source.supportReads_objectFamily h⟩⟩
  · exact ⟨AAT.AG.FiniteModel.twoPatchContextMorphism i j,
      AAT.AG.FiniteModel.twoPatchContextMorphism_isRestriction i j⟩

/--
SD0 fixture data declaration for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def referenceContextPreorder :
    Site.ContextPreorderCategory
      AAT.AG.FiniteModel.corePackage.object where
  le W V := ReferenceLe W V
  refl W := Or.inl rfl
  trans := by
    intro W V X hWV hVX
    rcases hWV with rfl | ⟨i, j, rfl, hVj, hij⟩
    · exact hVX
    rcases hVX with hVX | ⟨k, l, hVk, rfl, hkl⟩
    · exact hVX ▸ Or.inr ⟨i, j, rfl, hVj, hij⟩
    · have hjk : j = k := twoPatchContext_injective (hVj.symm.trans hVk)
      subst k
      exact Or.inr ⟨i, l, rfl, rfl,
        AAT.AG.FiniteModel.twoPatchContextIndexLe_trans hij hkl⟩
  readableMorphism := fun h => Classical.choose (referenceReadableMorphismExists h)
  readableMorphism_isRestriction := fun h =>
    Classical.choose_spec (referenceReadableMorphismExists h)

/-- Generated finite core specialized to the reference context preorder. -/
noncomputable def referenceCorePackage :
    AATCorePackage AAT.AG.FiniteModel.carrier :=
  AAT.AG.FiniteModel.corePackageFor referenceContextPreorder

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem referenceContextPreorder_le_iff
    (W V : Site.ArchCtx AAT.AG.FiniteModel.corePackage.object) :
    referenceContextPreorder.le W V ↔
      W = V ∨
        ∃ i j : AAT.AG.FiniteModel.TwoPatchContextIndex,
          W = AAT.AG.FiniteModel.twoPatchContext i ∧
          V = AAT.AG.FiniteModel.twoPatchContext j ∧
          AAT.AG.FiniteModel.twoPatchContextIndexLe i j :=
  Iff.rfl

private theorem referenceLe_antisymm
    {W V : Site.ArchCtx AAT.AG.FiniteModel.corePackage.object}
    (hWV : ReferenceLe W V) (hVW : ReferenceLe V W) : W = V := by
  rcases hWV with rfl | ⟨i, j, rfl, rfl, hij⟩
  · rfl
  rcases hVW with h | ⟨k, l, hjk, hil, hkl⟩
  · exact h.symm
  · have hjk' : j = k := twoPatchContext_injective hjk
    have hil' : i = l := twoPatchContext_injective hil
    subst k
    subst l
    have hji : AAT.AG.FiniteModel.twoPatchContextIndexLe j i := hkl
    exact congrArg AAT.AG.FiniteModel.twoPatchContext
      (AAT.AG.FiniteModel.twoPatchContextIndexLe_antisymm hij hji)

private theorem referenceLe_to_selected
    {W : Site.ArchCtx AAT.AG.FiniteModel.corePackage.object}
    {j : AAT.AG.FiniteModel.TwoPatchContextIndex}
    (h : ReferenceLe W (AAT.AG.FiniteModel.twoPatchContext j)) :
    ∃ i, W = AAT.AG.FiniteModel.twoPatchContext i ∧
      AAT.AG.FiniteModel.twoPatchContextIndexLe i j := by
  rcases h with h | ⟨i, k, hWi, hkj, hik⟩
  · exact ⟨j, h, AAT.AG.FiniteModel.twoPatchContextIndexLe_refl j⟩
  · have hkj' : j = k := twoPatchContext_injective hkj
    subst k
    exact ⟨i, hWi, hik⟩

private theorem referenceLe_selected_meet
    {W : Site.ArchCtx AAT.AG.FiniteModel.corePackage.object}
    {i j : AAT.AG.FiniteModel.TwoPatchContextIndex}
    (hi : ReferenceLe W (AAT.AG.FiniteModel.twoPatchContext i))
    (hj : ReferenceLe W (AAT.AG.FiniteModel.twoPatchContext j)) :
    ReferenceLe W
      (AAT.AG.FiniteModel.twoPatchContext
        (AAT.AG.FiniteModel.twoPatchContextMeet i j)) := by
  rcases referenceLe_to_selected hi with ⟨k, hWk, hki⟩
  rcases referenceLe_to_selected hj with ⟨l, hWl, hlj⟩
  have hkl : k = l := twoPatchContext_injective (hWk.symm.trans hWl)
  subst l
  exact Or.inr ⟨k, AAT.AG.FiniteModel.twoPatchContextMeet i j,
    hWk, rfl, AAT.AG.FiniteModel.twoPatchContext_le_meet hki hlj⟩

private abbrev IsSelectedContext
    (W : Site.ArchCtx AAT.AG.FiniteModel.corePackage.object) : Prop :=
  ∃ i, W = AAT.AG.FiniteModel.twoPatchContext i

private theorem referenceLe_source_nonselected_eq
    {W V : Site.ArchCtx AAT.AG.FiniteModel.corePackage.object}
    (hW : ¬ IsSelectedContext W) (h : ReferenceLe W V) : W = V := by
  rcases h with h | ⟨i, _j, hWi, _hVj, _hij⟩
  · exact h
  · exact (hW ⟨i, hWi⟩).elim

private theorem referenceLe_target_nonselected_eq
    {W V : Site.ArchCtx AAT.AG.FiniteModel.corePackage.object}
    (hV : ¬ IsSelectedContext V) (h : ReferenceLe W V) : W = V := by
  rcases h with h | ⟨_i, j, _hWi, hVj, _hij⟩
  · exact h
  · exact (hV ⟨j, hVj⟩).elim

private noncomputable def referenceOverlapObject
    (_base left right : Site.ArchCtx AAT.AG.FiniteModel.corePackage.object) :
    Site.ArchCtx AAT.AG.FiniteModel.corePackage.object := by
  classical
  exact if hleft : IsSelectedContext left then
    if hright : IsSelectedContext right then
      AAT.AG.FiniteModel.twoPatchContext
        (AAT.AG.FiniteModel.twoPatchContextMeet
          (Classical.choose hleft) (Classical.choose hright))
    else left
  else left

private theorem referenceOverlapObject_selected
    (base : Site.ArchCtx AAT.AG.FiniteModel.corePackage.object)
    (left right : AAT.AG.FiniteModel.TwoPatchContextIndex) :
    referenceOverlapObject
        base
        (AAT.AG.FiniteModel.twoPatchContext left)
        (AAT.AG.FiniteModel.twoPatchContext right) =
      AAT.AG.FiniteModel.twoPatchContext
        (AAT.AG.FiniteModel.twoPatchContextMeet left right) := by
  classical
  unfold referenceOverlapObject
  split
  next hleft =>
    split
    next hright =>
      have hi : Classical.choose hleft = left := by
        apply twoPatchContext_injective
        exact (Classical.choose_spec hleft).symm
      have hj : Classical.choose hright = right := by
        apply twoPatchContext_injective
        exact (Classical.choose_spec hright).symm
      rw [hi, hj]
    next hright => exact (hright ⟨right, rfl⟩).elim
  next hleft => exact (hleft ⟨left, rfl⟩).elim

private theorem referenceOverlapObject_spec
    {base left right : Site.ArchCtx AAT.AG.FiniteModel.corePackage.object}
    (hl : ReferenceLe left base) (hr : ReferenceLe right base) :
    ReferenceLe (referenceOverlapObject base left right) left ∧
      ReferenceLe (referenceOverlapObject base left right) right ∧
      ReferenceLe (referenceOverlapObject base left right) base ∧
      ∀ {Y}, ReferenceLe Y left → ReferenceLe Y right →
        ReferenceLe Y (referenceOverlapObject base left right) := by
  classical
  by_cases hleft : IsSelectedContext left
  · rcases hleft with ⟨i, rfl⟩
    by_cases hright : IsSelectedContext right
    · rcases hright with ⟨j, rfl⟩
      rw [referenceOverlapObject_selected base]
      refine ⟨?_, ?_, ?_, ?_⟩
      · exact Or.inr ⟨_, i, rfl, rfl,
          AAT.AG.FiniteModel.twoPatchContextMeet_le_left i j⟩
      · exact Or.inr ⟨_, j, rfl, rfl,
          AAT.AG.FiniteModel.twoPatchContextMeet_le_right i j⟩
      · exact referenceContextPreorder.trans
          (Or.inr ⟨_, i, rfl, rfl,
            AAT.AG.FiniteModel.twoPatchContextMeet_le_left i j⟩) hl
      · intro Y hYi hYj
        exact referenceLe_selected_meet hYi hYj
    · have hrEq : right = base := referenceLe_source_nonselected_eq hright hr
      have hbaseNot : ¬ IsSelectedContext base := by simpa [hrEq] using hright
      have hlEq : AAT.AG.FiniteModel.twoPatchContext i = base :=
        referenceLe_target_nonselected_eq hbaseNot hl
      exact (hbaseNot ⟨i, hlEq.symm⟩).elim
  · have hlEq : left = base := referenceLe_source_nonselected_eq hleft hl
    have hbaseNot : ¬ IsSelectedContext base := by simpa [hlEq] using hleft
    have hrEq : right = base := referenceLe_target_nonselected_eq hbaseNot hr
    subst right
    subst base
    simp only [referenceOverlapObject, dif_neg hleft]
    exact ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl, fun hY _ => hY⟩

/--
SD0 fixture data declaration for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def referenceOverlap :
    Site.ContextOverlapPullback referenceContextPreorder where
  overlap := referenceOverlapObject
  overlap_le_left := fun hl hr => (referenceOverlapObject_spec hl hr).1
  overlap_le_right := fun hl hr => (referenceOverlapObject_spec hl hr).2.1
  overlap_le_base := fun hl hr => (referenceOverlapObject_spec hl hr).2.2.1
  overlap_lift := fun hl hr hYl hYr =>
    (referenceOverlapObject_spec hl hr).2.2.2 hYl hYr

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem referenceOverlap_selected
    (base left right : AAT.AG.FiniteModel.TwoPatchContextIndex) :
    referenceOverlap.overlap
        (AAT.AG.FiniteModel.twoPatchContext base)
        (AAT.AG.FiniteModel.twoPatchContext left)
        (AAT.AG.FiniteModel.twoPatchContext right) =
      AAT.AG.FiniteModel.twoPatchContext
        (AAT.AG.FiniteModel.twoPatchContextMeet left right) := by
  exact referenceOverlapObject_selected
    (AAT.AG.FiniteModel.twoPatchContext base) left right

/--
SD0 fixture data declaration for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def referenceCoverageRequirements :
    Site.CoverageRequirements
      referenceCorePackage.object
      referenceCorePackage.equationSystem
      referenceCorePackage.algebra.signatureReading where
  requiredSupport := fun atom =>
    atom = AAT.AG.FiniteModel.FiniteAtom.componentA ∨
      atom = AAT.AG.FiniteModel.FiniteAtom.componentB
  requiredEquationCoordinate := fun _ => True
  selectedViolationWitness := fun _ => True
  requiredAxis := fun _ => True
  supportVisibleOn := AAT.AG.FiniteModel.twoPatchSupportVisibleOn
  equationCoordinateVisibleOn := fun _ _ => True
  violationWitnessVisibleOn := fun _ _ => True
  axisReadableOn := fun W _ =>
    W = AAT.AG.FiniteModel.twoPatchContext
        AAT.AG.FiniteModel.TwoPatchContextIndex.left ∨
      W = AAT.AG.FiniteModel.twoPatchContext
        AAT.AG.FiniteModel.TwoPatchContextIndex.right
  boundaryVisibleOn := fun _ _ => True

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem referenceCoverageRequirements_eq :
    referenceCoverageRequirements =
      { requiredSupport := fun atom =>
          atom = AAT.AG.FiniteModel.FiniteAtom.componentA ∨
            atom = AAT.AG.FiniteModel.FiniteAtom.componentB
        requiredEquationCoordinate := fun _ => True
        selectedViolationWitness := fun _ => True
        requiredAxis := fun _ => True
        supportVisibleOn := AAT.AG.FiniteModel.twoPatchSupportVisibleOn
        equationCoordinateVisibleOn := fun _ _ => True
        violationWitnessVisibleOn := fun _ _ => True
        axisReadableOn := fun W _ =>
          W = AAT.AG.FiniteModel.twoPatchContext
              AAT.AG.FiniteModel.TwoPatchContextIndex.left ∨
            W = AAT.AG.FiniteModel.twoPatchContext
              AAT.AG.FiniteModel.TwoPatchContextIndex.right
        boundaryVisibleOn := fun _ _ => True } :=
  rfl

/--
SD0 fixture data declaration for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def referenceSelectedGeometryReading :
    Site.SelectedGeometryReading referenceCorePackage where
  requirements := referenceCoverageRequirements
  overlap := referenceOverlap

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem referenceSelectedGeometryReading_eq :
    referenceSelectedGeometryReading =
      { requirements := referenceCoverageRequirements
        overlap := referenceOverlap } :=
  rfl

/--
SD0 fixture data declaration for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def referenceSite :
    Site.AATSite referenceCorePackage.object :=
  referenceSelectedGeometryReading.toAATSite

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem referenceSite_eq :
    referenceSite = referenceSelectedGeometryReading.toAATSite :=
  rfl

/-- Every equation in the reference site is required. -/
theorem referenceSite_equation_required
    (index : referenceSite.equationSystem.Index) :
    referenceSite.equationSystem.Required index := by
  cases index
  rfl

/-- The reference site's symbolic coordinate is the core-selected constant `2`. -/
@[simp] theorem referenceSite_violationCoordinate
    (W : referenceSite.category)
    (index : referenceSite.equationSystem.Index)
    (atom : AAT.AG.FiniteModel.carrier.Atom) :
    referenceSite.equationSystem.violationCoordinate W index atom = 2 :=
  rfl

private noncomputable def referenceIncomingCode
    {X Y : referenceSite.category} (_f : Y ⟶ X) :
    Option AAT.AG.FiniteModel.TwoPatchContextIndex := by
  classical
  exact if hY : IsSelectedContext Y.ctx then some (Classical.choose hY) else none

private theorem referenceIncomingCode_injective
    (X : referenceSite.category) :
    Function.Injective
      (fun a : Σ Y : referenceSite.category, Y ⟶ X =>
        referenceIncomingCode a.2) := by
  classical
  rintro ⟨Y, f⟩ ⟨Z, g⟩ hcode
  by_cases hY : IsSelectedContext Y.ctx
  · by_cases hZ : IsSelectedContext Z.ctx
    · simp only [referenceIncomingCode, dif_pos hY, dif_pos hZ,
        Option.some.injEq] at hcode
      have hctx : Y.ctx = Z.ctx :=
        (Classical.choose_spec hY).trans <|
          congrArg AAT.AG.FiniteModel.twoPatchContext hcode |>.trans <|
            (Classical.choose_spec hZ).symm
      have hYZ : Y = Z := by
        cases Y
        cases Z
        simp only [Site.ContextCategoryObject.ctx] at hctx
        cases hctx
        rfl
      subst Z
      have hfg : f = g := Subsingleton.elim _ _
      subst g
      rfl
    · simp [referenceIncomingCode, hY, hZ] at hcode
  · by_cases hZ : IsSelectedContext Z.ctx
    · simp [referenceIncomingCode, hY, hZ] at hcode
    · have hYX : Y.ctx = X.ctx :=
        referenceLe_source_nonselected_eq hY (CategoryTheory.leOfHom f)
      have hZX : Z.ctx = X.ctx :=
        referenceLe_source_nonselected_eq hZ (CategoryTheory.leOfHom g)
      have hYZ : Y = Z := by
        cases Y
        cases Z
        simp only [Site.ContextCategoryObject.ctx] at hYX hZX ⊢
        cases hYX.trans hZX.symm
        rfl
      subst Z
      have hfg : f = g := Subsingleton.elim _ _
      subst g
      rfl

private noncomputable def referenceCoverCode
    {X : referenceSite.category} (S : referenceSite.topology.Cover X) :
    Set (Option AAT.AG.FiniteModel.TwoPatchContextIndex) :=
  {c | ∃ a : Σ Y : referenceSite.category, Y ⟶ X,
    referenceIncomingCode a.2 = c ∧ S a.2}

private theorem referenceCoverCode_injective
    (X : referenceSite.category) :
    Function.Injective (@referenceCoverCode X) := by
  intro S T hST
  apply CategoryTheory.GrothendieckTopology.Cover.ext
  intro Y f
  constructor
  · intro hSf
    have hmem : referenceIncomingCode f ∈ referenceCoverCode S :=
      ⟨⟨Y, f⟩, rfl, hSf⟩
    rw [hST] at hmem
    rcases hmem with ⟨⟨Z, g⟩, hcode, hTg⟩
    have hsigma := referenceIncomingCode_injective X
      (a₁ := ⟨Z, g⟩) (a₂ := ⟨Y, f⟩) hcode
    cases hsigma
    exact hTg
  · intro hTf
    have hmem : referenceIncomingCode f ∈ referenceCoverCode T :=
      ⟨⟨Y, f⟩, rfl, hTf⟩
    rw [← hST] at hmem
    rcases hmem with ⟨⟨Z, g⟩, hcode, hSg⟩
    have hsigma := referenceIncomingCode_injective X
      (a₁ := ⟨Z, g⟩) (a₂ := ⟨Y, f⟩) hcode
    cases hsigma
    exact hSg

private noncomputable instance referenceCoverSmall
    (X : referenceSite.category) :
    Small.{u} (referenceSite.topology.Cover X) :=
  small_of_injective (referenceCoverCode_injective X)

private abbrev ReferenceCoefficientBase (k : Type) [CommRing k] :=
  CommRingCat.of (ULift.{u} k)

private abbrev ReferenceCoefficientUnder (k : Type) [CommRing k] :=
  Under (ReferenceCoefficientBase.{u} k)

private instance referenceCoefficientUnderHomFunLike
    {k : Type} [CommRing k] (A B : ReferenceCoefficientUnder.{u} k) :
    FunLike (A ⟶ B) A B where
  coe f := f.right
  coe_injective' f g h := by
    ext x
    exact congrFun h x

private instance referenceCoefficientUnderConcreteCategory
    {k : Type} [CommRing k] :
    ConcreteCategory (ReferenceCoefficientUnder.{u} k)
      (fun A B => A ⟶ B) where
  hom := id
  ofHom := id
  hom_ofHom _ := rfl
  ofHom_hom _ := rfl
  id_apply _ := rfl
  comp_apply _ _ _ := rfl

private instance referenceCoefficientUnderForgetPreservesLimits
    {k : Type} [CommRing k] :
    PreservesLimits (forget (ReferenceCoefficientUnder.{u} k)) := by
  change PreservesLimits
    (Under.forget (ReferenceCoefficientBase.{u} k) ⋙ forget CommRingCat.{u})
  infer_instance

private instance referenceCoefficientUnderForgetReflectsIsomorphisms
    {k : Type} [CommRing k] :
    (forget (ReferenceCoefficientUnder.{u} k)).ReflectsIsomorphisms := by
  change (Under.forget (ReferenceCoefficientBase.{u} k) ⋙
    forget CommRingCat.{u}).ReflectsIsomorphisms
  infer_instance

private instance referenceCoefficientUnderForgetPreservesFilteredColimits
    {k : Type} [CommRing k] :
    PreservesFilteredColimits
      (forget (ReferenceCoefficientUnder.{u} k)) := by
  change PreservesFilteredColimits
    (Under.forget (ReferenceCoefficientBase.{u} k) ⋙ forget CommRingCat.{u})
  infer_instance

private example (X : referenceSite.category) :
    Small.{0} (referenceSite.topology.Cover X)ᵒᵖ := by
  infer_instance

private example : HasFiniteLimits (AATCommAlgCat Int) := by
  infer_instance

private example : PreservesLimits (forget (AATCommAlgCat Int)) := by
  infer_instance

private example : (forget (AATCommAlgCat Int)).ReflectsIsomorphisms := by
  infer_instance

private example : HasColimits (AATCommAlgCat Int) := by
  infer_instance

private example (X : referenceSite.category) :
    IsFiltered (referenceSite.topology.Cover X)ᵒᵖ := by
  infer_instance

private noncomputable instance referenceCoverHasColimits
    {k : Type} [CommRing k] (X : referenceSite.category) :
    HasColimitsOfShape (referenceSite.topology.Cover X)ᵒᵖ
      (ReferenceCoefficientUnder.{u} k) := by
  let K := (referenceSite.topology.Cover X)ᵒᵖ
  letI : EssentiallySmall.{0} K := by infer_instance
  exact Limits.hasColimitsOfShape_of_essentiallySmall K
    (ReferenceCoefficientUnder.{u} k)

private noncomputable instance referenceCoverForgetPreservesColimits
    {k : Type} [CommRing k] (X : referenceSite.category) :
    PreservesColimitsOfShape (referenceSite.topology.Cover X)ᵒᵖ
      (forget (ReferenceCoefficientUnder.{u} k)) := by
  let K := (referenceSite.topology.Cover X)ᵒᵖ
  letI : EssentiallySmall.{0} K := by infer_instance
  letI : IsFiltered (SmallModel.{0} K) :=
    IsFiltered.of_equivalence (equivSmallModel.{0} K)
  letI : PreservesFilteredColimitsOfSize.{0, 0}
      (forget (ReferenceCoefficientUnder.{u} k)) :=
    preservesFilteredColimitsOfSize_shrink _
  letI : PreservesColimitsOfShape (SmallModel.{0} K)
      (forget (ReferenceCoefficientUnder.{u} k)) := by infer_instance
  exact preservesColimitsOfShape_of_equiv
    (equivSmallModel.{0} K).symm _

private example (X : referenceSite.category) :
    HasColimitsOfShape (referenceSite.topology.Cover X)ᵒᵖ
      (AATCommAlgCat Int) := by
  exact referenceCoverHasColimits (k := Int) X

private noncomputable instance referenceCoverArrowFinite
    (X : referenceSite.category) (S : referenceSite.topology.Cover X) :
    Finite S.Arrow := by
  apply Finite.of_injective (fun I : S.Arrow => referenceIncomingCode I.f)
  intro I K h
  have hsigma := referenceIncomingCode_injective X
    (a₁ := ⟨I.Y, I.f⟩) (a₂ := ⟨K.Y, K.f⟩) h
  cases I
  cases K
  simp_all

private noncomputable instance referenceCoverArrowRelationFinite
    (X : referenceSite.category) (S : referenceSite.topology.Cover X)
    (I K : S.Arrow) : Finite (I.Relation K) := by
  apply Finite.of_injective
    (fun r : I.Relation K => referenceIncomingCode r.g₁)
  intro r s h
  have hsigma := referenceIncomingCode_injective I.Y
    (a₁ := ⟨r.Z, r.g₁⟩) (a₂ := ⟨s.Z, s.g₁⟩) h
  cases r with
  | mk Zr g1r g2r wr =>
    cases s with
    | mk Zs g1s g2s ws =>
      have hZ : Zr = Zs := congrArg Sigma.fst hsigma
      subst Zs
      have hg1 : g1r = g1s := Subsingleton.elim _ _
      subst g1s
      have hg2 : g2r = g2s := Subsingleton.elim _ _
      subst g2s
      rfl

private noncomputable instance referenceCoverRelationFinite
    (X : referenceSite.category) (S : referenceSite.topology.Cover X) :
    Finite S.Relation := by
  apply Finite.of_surjective
    (fun t : Σ I : S.Arrow, Σ K : S.Arrow, I.Relation K =>
      (⟨t.2.2⟩ : S.Relation))
  intro r
  exact ⟨⟨r.fst, r.snd, r.r⟩, by cases r; rfl⟩

private noncomputable instance referenceWalkingMulticospanFinCategory
    (X : referenceSite.category) (S : referenceSite.topology.Cover X) :
    FinCategory (WalkingMulticospan S.shape) := by
  classical
  letI : Fintype S.Arrow := Fintype.ofFinite S.Arrow
  letI : Fintype S.Relation := Fintype.ofFinite S.Relation
  letI : Fintype S.shape.L := Fintype.ofFinite S.Arrow
  letI : Fintype S.shape.R := Fintype.ofFinite S.Relation
  letI : DecidableEq S.shape.L := Classical.decEq _
  letI : DecidableEq S.shape.R := Classical.decEq _
  infer_instance

private noncomputable instance referenceHasMultiequalizer
    {k : Type} [CommRing k]
    (P : referenceSite.categoryᵒᵖ ⥤ ReferenceCoefficientUnder.{u} k)
    (X : referenceSite.category) (S : referenceSite.topology.Cover X) :
    HasMultiequalizer (S.index P) := by
  classical
  letI : Fintype S.Arrow := Fintype.ofFinite S.Arrow
  letI : Fintype S.Relation := Fintype.ofFinite S.Relation
  letI : Fintype S.shape.L := Fintype.ofFinite S.Arrow
  letI : Fintype S.shape.R := Fintype.ofFinite S.Relation
  letI : DecidableEq S.shape.L := Classical.decEq _
  letI : DecidableEq S.shape.R := Classical.decEq _
  letI : FinCategory (WalkingMulticospan S.shape) := by infer_instance
  infer_instance

private example (X : referenceSite.category) :
    PreservesColimitsOfShape (referenceSite.topology.Cover X)ᵒᵖ
      (forget (AATCommAlgCat Int)) := by
  infer_instance

private example (P : referenceSite.categoryᵒᵖ ⥤ AATCommAlgCat Int)
    (X : referenceSite.category) (S : referenceSite.topology.Cover X) :
    HasMultiequalizer (S.index P) := by
  infer_instance

/--
SD0 premise-discharge instance for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable instance referenceSite_hasSheafifyInt :
    HasSheafify referenceSite.topology (AATCommAlgCat Int) := by
  infer_instance

/--
SD0 premise-discharge instance for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable instance referenceSite_hasSheafifyPolynomialInt :
    HasSheafify referenceSite.topology
      (AATCommAlgCat (Polynomial Int)) := by
  infer_instance

/--
SD0 fixture data declaration for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def context
    (i : AAT.AG.FiniteModel.TwoPatchContextIndex) :
    referenceSite.category :=
  Site.ContextCategoryObject.of referenceContextPreorder
    (AAT.AG.FiniteModel.twoPatchContext i)

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem context_ctx
    (i : AAT.AG.FiniteModel.TwoPatchContextIndex) :
    (context i).ctx = AAT.AG.FiniteModel.twoPatchContext i :=
  rfl

/--
SD0 fixture data declaration for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def overlapContext : referenceSite.category :=
  context AAT.AG.FiniteModel.TwoPatchContextIndex.overlap

/--
SD0 fixture data declaration for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def leftContext : referenceSite.category :=
  context AAT.AG.FiniteModel.TwoPatchContextIndex.left

/--
SD0 fixture data declaration for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def rightContext : referenceSite.category :=
  context AAT.AG.FiniteModel.TwoPatchContextIndex.right

/--
SD0 fixture data declaration for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def baseContext : referenceSite.category :=
  context AAT.AG.FiniteModel.TwoPatchContextIndex.base

private theorem context_injective : Function.Injective context := by
  intro i j h
  apply twoPatchContext_injective
  exact congrArg Site.ContextCategoryObject.ctx h

private theorem context_ne_of_ne
    {i j : AAT.AG.FiniteModel.TwoPatchContextIndex} (h : i ≠ j) :
    context i ≠ context j := by
  intro hij
  exact h (context_injective hij)

@[simp] private theorem context_eq_context_iff
    (i j : AAT.AG.FiniteModel.TwoPatchContextIndex) :
    context i = context j ↔ i = j :=
  context_injective.eq_iff

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem context_hom_iff
    (i j : AAT.AG.FiniteModel.TwoPatchContextIndex) :
    Nonempty (context i ⟶ context j) ↔
      AAT.AG.FiniteModel.twoPatchContextIndexLe i j := by
  constructor
  · rintro ⟨f⟩
    have h := CategoryTheory.leOfHom f
    change ReferenceLe _ _ at h
    rcases h with h | ⟨k, l, hki, hlj, hkl⟩
    · have hij : i = j := twoPatchContext_injective h
      subst j
      exact AAT.AG.FiniteModel.twoPatchContextIndexLe_refl i
    · have hki' : i = k := twoPatchContext_injective hki
      have hlj' : j = l := twoPatchContext_injective hlj
      subst k
      subst l
      exact hkl
  · intro hij
    exact ⟨homOfLE (Or.inr ⟨i, j, rfl, rfl, hij⟩)⟩

/--
SD0 fixture data declaration for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def leftToBase : leftContext ⟶ baseContext :=
  homOfLE (Or.inr ⟨_, _, rfl, rfl, by
    simp [AAT.AG.FiniteModel.twoPatchContextIndexLe]⟩)

/--
SD0 fixture data declaration for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def rightToBase : rightContext ⟶ baseContext :=
  homOfLE (Or.inr ⟨_, _, rfl, rfl, by
    simp [AAT.AG.FiniteModel.twoPatchContextIndexLe]⟩)

/--
SD0 fixture data declaration for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def overlapToLeft : overlapContext ⟶ leftContext :=
  homOfLE (Or.inr ⟨_, _, rfl, rfl, by
    simp [AAT.AG.FiniteModel.twoPatchContextIndexLe]⟩)

/--
SD0 fixture data declaration for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def overlapToRight : overlapContext ⟶ rightContext :=
  homOfLE (Or.inr ⟨_, _, rfl, rfl, by
    simp [AAT.AG.FiniteModel.twoPatchContextIndexLe]⟩)

/--
SD0 fixture data declaration for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def referenceCover :
    Site.AATCoverageFamily
      referenceSite.requirements referenceSite.overlap baseContext where
  Index := AAT.AG.FiniteModel.TwoPatchCoverIndex
  patch := AAT.AG.FiniteModel.twoPatchCoverPatch
  inclusion := by
    intro i
    cases i
    · exact Or.inr ⟨_, _, rfl, rfl, by
        simp [AAT.AG.FiniteModel.twoPatchCoverContextIndex,
          AAT.AG.FiniteModel.twoPatchContextIndexLe]⟩
    · exact Or.inr ⟨_, _, rfl, rfl, by
        simp [AAT.AG.FiniteModel.twoPatchCoverContextIndex,
          AAT.AG.FiniteModel.twoPatchContextIndexLe]⟩
  admissible := {
    atomSupportCoverage := by
      intro atom hreq
      rcases hreq with rfl | rfl
      · exact ⟨AAT.AG.FiniteModel.TwoPatchCoverIndex.left, by
          simp [referenceCoverageRequirements,
            AAT.AG.FiniteModel.twoPatchCoverPatch,
            AAT.AG.FiniteModel.twoPatchCoverContextIndex,
            AAT.AG.FiniteModel.twoPatchCoverageRequirements,
            AAT.AG.FiniteModel.twoPatchSupportVisibleOn]⟩
      · exact ⟨AAT.AG.FiniteModel.TwoPatchCoverIndex.right, by
          simp [referenceCoverageRequirements,
            AAT.AG.FiniteModel.twoPatchCoverPatch,
            AAT.AG.FiniteModel.twoPatchCoverContextIndex,
            AAT.AG.FiniteModel.twoPatchCoverageRequirements,
            AAT.AG.FiniteModel.twoPatchSupportVisibleOn]⟩
    equationCoordinateCoverage := by
      intro _ _
      exact Or.inl ⟨AAT.AG.FiniteModel.TwoPatchCoverIndex.left, trivial⟩
    violationWitnessCoverage := by
      intro _ _
      exact Or.inl ⟨AAT.AG.FiniteModel.TwoPatchCoverIndex.left, trivial⟩
    signatureAxisCoverage := by
      intro _ _
      exact ⟨AAT.AG.FiniteModel.TwoPatchCoverIndex.left, by
        simp [referenceCoverageRequirements,
          AAT.AG.FiniteModel.twoPatchCoverPatch,
          AAT.AG.FiniteModel.twoPatchCoverContextIndex,
          AAT.AG.FiniteModel.twoPatchCoverageRequirements]⟩
    boundaryCoverage := by
      intro _ _
      trivial
    nonGeneration := by
      intro _ support atom hselected
      exact AAT.AG.FiniteModel.allFamily_mem _ hselected
  }

/--
SD0 fixture data declaration for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def referenceCoverIndexEquiv :
    referenceCover.Index ≃ AAT.AG.FiniteModel.TwoPatchCoverIndex :=
  Equiv.refl _

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem referenceCover_patch
    (i : AAT.AG.FiniteModel.TwoPatchCoverIndex) :
    referenceCover.patch (referenceCoverIndexEquiv.symm i) =
      AAT.AG.FiniteModel.twoPatchCoverPatch i :=
  rfl

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem referenceCover_presieve :
    referenceCover.presieve =
      Presieve.ofArrows
        (fun i : AAT.AG.FiniteModel.TwoPatchCoverIndex =>
          context (AAT.AG.FiniteModel.twoPatchCoverContextIndex i))
        (fun i => match i with
          | AAT.AG.FiniteModel.TwoPatchCoverIndex.left => leftToBase
          | AAT.AG.FiniteModel.TwoPatchCoverIndex.right => rightToBase) := by
  rfl

/--
SD0 main fixture theorem for Part II definitions 3.1, 4.1, and 6.1–8.1, including proposition 4.2 and assumption 4.3.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem referenceCover_topologyCover :
    Sieve.generate referenceCover.presieve ∈
      referenceSite.topology baseContext := by
  change Sieve.generate referenceCover.presieve ∈
    (Site.AATGrothendieckTopology
      referenceCoverageRequirements referenceOverlap) baseContext
  exact Site.AATGrothendieckTopology.generate_mem referenceCover

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
inductive ReferenceRawCoordinate where
  | coordinate
  | leftInverse
  | rightInverse
  deriving DecidableEq

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem referenceRawCoordinate_cases (c : ReferenceRawCoordinate) :
    c = .coordinate ∨ c = .leftInverse ∨ c = .rightInverse := by
  cases c <;> simp

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def referenceCoordinateFamily (W : referenceSite.category) :
    CoordinateFamily W.ctx where
  Coord := ReferenceRawCoordinate
  label _ := CoordinateLabel.semantic
  LocalData _ := PUnit

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem referenceCoordinateFamily_coord
    (W : referenceSite.category) :
    (referenceCoordinateFamily W).Coord = ReferenceRawCoordinate :=
  rfl

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem referenceCoordinateFamily_label
    (W : referenceSite.category) (c : ReferenceRawCoordinate) :
    (referenceCoordinateFamily W).label c = CoordinateLabel.semantic :=
  rfl

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem referenceCoordinateFamily_localData
    (W : referenceSite.category) (c : ReferenceRawCoordinate) :
    (referenceCoordinateFamily W).LocalData c = PUnit :=
  rfl

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def rawVariable (W : referenceSite.category) (c : ReferenceRawCoordinate) :
    FreeTypedCommAlg (referenceCoordinateFamily W) Int :=
  MvPolynomial.X c

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem rawVariable_eq
    (W : referenceSite.category) (c : ReferenceRawCoordinate) :
    rawVariable W c = MvPolynomial.X c :=
  rfl

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def rawX (W : referenceSite.category) :
    FreeTypedCommAlg (referenceCoordinateFamily W) Int :=
  rawVariable W .coordinate

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem rawX_eq (W : referenceSite.category) :
    rawX W = rawVariable W .coordinate :=
  rfl

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def rawLeftInverse (W : referenceSite.category) :
    FreeTypedCommAlg (referenceCoordinateFamily W) Int :=
  rawVariable W .leftInverse

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem rawLeftInverse_eq (W : referenceSite.category) :
    rawLeftInverse W = rawVariable W .leftInverse :=
  rfl

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def rawRightInverse (W : referenceSite.category) :
    FreeTypedCommAlg (referenceCoordinateFamily W) Int :=
  rawVariable W .rightInverse

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem rawRightInverse_eq (W : referenceSite.category) :
    rawRightInverse W = rawVariable W .rightInverse :=
  rfl

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def leftInverseRelation (W : referenceSite.category) :
    FreeTypedCommAlg (referenceCoordinateFamily W) Int :=
  rawX W * rawLeftInverse W - 1

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem leftInverseRelation_eq (W : referenceSite.category) :
    leftInverseRelation W = rawX W * rawLeftInverse W - 1 :=
  rfl

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def rightInverseRelation (W : referenceSite.category) :
    FreeTypedCommAlg (referenceCoordinateFamily W) Int :=
  (1 - rawX W) * rawRightInverse W - 1

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem rightInverseRelation_eq (W : referenceSite.category) :
    rightInverseRelation W = (1 - rawX W) * rawRightInverse W - 1 :=
  rfl

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def leftIsInverted (W : referenceSite.category) : Prop :=
  W = leftContext ∨ W = overlapContext

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def rightIsInverted (W : referenceSite.category) : Prop :=
  W = rightContext ∨ W = overlapContext

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem leftIsInverted_iff (W : referenceSite.category) :
    leftIsInverted W ↔ W = leftContext ∨ W = overlapContext :=
  Iff.rfl

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem rightIsInverted_iff (W : referenceSite.category) :
    rightIsInverted W ↔ W = rightContext ∨ W = overlapContext :=
  Iff.rfl

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem leftIsInverted_left : leftIsInverted leftContext :=
  Or.inl rfl

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem leftIsInverted_overlap : leftIsInverted overlapContext :=
  Or.inr rfl

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem leftIsInverted_base : ¬ leftIsInverted baseContext := by
  have hbl : baseContext ≠ leftContext := context_ne_of_ne (by decide)
  have hbo : baseContext ≠ overlapContext := context_ne_of_ne (by decide)
  simpa [leftIsInverted] using And.intro hbl hbo

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem leftIsInverted_right : ¬ leftIsInverted rightContext := by
  have hrl : rightContext ≠ leftContext := context_ne_of_ne (by decide)
  have hro : rightContext ≠ overlapContext := context_ne_of_ne (by decide)
  simpa [leftIsInverted] using And.intro hrl hro

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem rightIsInverted_right : rightIsInverted rightContext :=
  Or.inl rfl

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem rightIsInverted_overlap : rightIsInverted overlapContext :=
  Or.inr rfl

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem rightIsInverted_base : ¬ rightIsInverted baseContext := by
  have hbr : baseContext ≠ rightContext := context_ne_of_ne (by decide)
  have hbo : baseContext ≠ overlapContext := context_ne_of_ne (by decide)
  simpa [rightIsInverted] using And.intro hbr hbo

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem rightIsInverted_left : ¬ rightIsInverted leftContext := by
  have hlr : leftContext ≠ rightContext := context_ne_of_ne (by decide)
  have hlo : leftContext ≠ overlapContext := context_ne_of_ne (by decide)
  simpa [rightIsInverted] using And.intro hlr hlo

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def referenceRelationPolynomial
    (W : referenceSite.category) : Bool →
      FreeTypedCommAlg (referenceCoordinateFamily W) Int
  | false => if leftIsInverted W then leftInverseRelation W else rawLeftInverse W
  | true => if rightIsInverted W then rightInverseRelation W else rawRightInverse W

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem referenceRelationPolynomial_false
    (W : referenceSite.category) :
    referenceRelationPolynomial W false =
      if leftIsInverted W then leftInverseRelation W else rawLeftInverse W :=
  rfl

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem referenceRelationPolynomial_true
    (W : referenceSite.category) :
    referenceRelationPolynomial W true =
      if rightIsInverted W then rightInverseRelation W else rawRightInverse W :=
  rfl

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def referenceRelationFamily
    (W : referenceSite.category) :
    StructuralRelationFamily (referenceCoordinateFamily W) Int where
  Relation := Bool
  polynomial := referenceRelationPolynomial W

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem referenceRelationFamily_relation
    (W : referenceSite.category) :
    (referenceRelationFamily W).Relation = Bool :=
  rfl

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem referenceRelationFamily_polynomial
    (W : referenceSite.category) (r : Bool) :
    (referenceRelationFamily W).polynomial r =
      referenceRelationPolynomial W r :=
  rfl

private theorem relationFamily_JStruct_eq
    (W : referenceSite.category) :
    (referenceRelationFamily W).JStruct =
      Ideal.span {referenceRelationPolynomial W false,
        referenceRelationPolynomial W true} := by
  rw [StructuralRelationFamily.JStruct]
  congr 1
  ext p
  constructor
  · rintro ⟨r, rfl⟩
    cases r <;> simp
  · intro hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · exact ⟨false, rfl⟩
    · exact ⟨true, rfl⟩

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem base_JStruct_eq :
    (referenceRelationFamily baseContext).JStruct =
      Ideal.span {rawLeftInverse baseContext, rawRightInverse baseContext} := by
  rw [relationFamily_JStruct_eq]
  rw [referenceRelationPolynomial_false, referenceRelationPolynomial_true,
    if_neg leftIsInverted_base, if_neg rightIsInverted_base]

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem left_JStruct_eq :
    (referenceRelationFamily leftContext).JStruct =
      Ideal.span {leftInverseRelation leftContext, rawRightInverse leftContext} := by
  rw [relationFamily_JStruct_eq]
  rw [referenceRelationPolynomial_false, referenceRelationPolynomial_true,
    if_pos leftIsInverted_left, if_neg rightIsInverted_left]

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem right_JStruct_eq :
    (referenceRelationFamily rightContext).JStruct =
      Ideal.span {rawLeftInverse rightContext, rightInverseRelation rightContext} := by
  rw [relationFamily_JStruct_eq]
  rw [referenceRelationPolynomial_false, referenceRelationPolynomial_true,
    if_neg leftIsInverted_right, if_pos rightIsInverted_right]

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem overlap_JStruct_eq :
    (referenceRelationFamily overlapContext).JStruct =
      Ideal.span {leftInverseRelation overlapContext,
        rightInverseRelation overlapContext} := by
  rw [relationFamily_JStruct_eq]
  rw [referenceRelationPolynomial_false, referenceRelationPolynomial_true,
    if_pos leftIsInverted_overlap, if_pos rightIsInverted_overlap]

private theorem contextObject_ext
    {W V : referenceSite.category} (h : W.ctx = V.ctx) : W = V := by
  cases W
  cases V
  cases h
  rfl

private theorem contextObject_eq
    {W : referenceSite.category}
    {i : AAT.AG.FiniteModel.TwoPatchContextIndex}
    (h : W.ctx = AAT.AG.FiniteModel.twoPatchContext i) :
    W = context i :=
  contextObject_ext h

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def referenceTypedRestriction
    {source target : referenceSite.category} (f : source ⟶ target) :
    TypedCoordinateRestriction
      (referenceCoordinateFamily source)
      (referenceCoordinateFamily target) Int
      (referenceSite.contextPreorder.morphism
        (CategoryTheory.leOfHom f)) where
  variableImage
    | .coordinate => rawX source
    | .leftInverse =>
        if leftIsInverted target then rawLeftInverse source
        else if leftIsInverted source then leftInverseRelation source
        else rawLeftInverse source
    | .rightInverse =>
        if rightIsInverted target then rawRightInverse source
        else if rightIsInverted source then rightInverseRelation source
        else rawRightInverse source

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem referenceTypedRestriction_variableImage
    {source target : referenceSite.category} (f : source ⟶ target)
    (c : ReferenceRawCoordinate) :
    (referenceTypedRestriction f).variableImage c =
      match c with
      | .coordinate => rawX source
      | .leftInverse =>
          if leftIsInverted target then rawLeftInverse source
          else if leftIsInverted source then leftInverseRelation source
          else rawLeftInverse source
      | .rightInverse =>
          if rightIsInverted target then rawRightInverse source
          else if rightIsInverted source then rightInverseRelation source
          else rawRightInverse source :=
  by cases c <;> rfl

private theorem referenceTypedRestriction_polynomialMap_variable
    {source target : referenceSite.category} (f : source ⟶ target)
    (c : ReferenceRawCoordinate) :
    (referenceTypedRestriction f).polynomialMap (MvPolynomial.X c) =
      (referenceTypedRestriction f).variableImage c :=
  TypedCoordinateRestriction.polynomialMap_X _ _

@[simp] private theorem referenceTypedRestriction_polynomialMap_coordinate
    {source target : referenceSite.category} (f : source ⟶ target) :
    (referenceTypedRestriction f).polynomialMap
        (MvPolynomial.X ReferenceRawCoordinate.coordinate) = rawX source := by
  rw [referenceTypedRestriction_polynomialMap_variable]
  rfl

@[simp] private theorem referenceTypedRestriction_polynomialMap_leftInverse
    {source target : referenceSite.category} (f : source ⟶ target) :
    (referenceTypedRestriction f).polynomialMap
        (MvPolynomial.X ReferenceRawCoordinate.leftInverse) =
      if leftIsInverted target then rawLeftInverse source
      else if leftIsInverted source then leftInverseRelation source
      else rawLeftInverse source := by
  rw [referenceTypedRestriction_polynomialMap_variable]
  rfl

@[simp] private theorem referenceTypedRestriction_polynomialMap_rightInverse
    {source target : referenceSite.category} (f : source ⟶ target) :
    (referenceTypedRestriction f).polynomialMap
        (MvPolynomial.X ReferenceRawCoordinate.rightInverse) =
      if rightIsInverted target then rawRightInverse source
      else if rightIsInverted source then rightInverseRelation source
      else rawRightInverse source := by
  rw [referenceTypedRestriction_polynomialMap_variable]
  rfl

@[simp] private theorem referenceTypedRestriction_polynomialMap_rawX
    {source target : referenceSite.category} (f : source ⟶ target) :
    (referenceTypedRestriction f).polynomialMap (rawX target) = rawX source := by
  rw [rawX_eq, rawVariable_eq,
    referenceTypedRestriction_polynomialMap_variable]
  rfl

@[simp] private theorem referenceTypedRestriction_polynomialMap_rawLeftInverse
    {source target : referenceSite.category} (f : source ⟶ target) :
    (referenceTypedRestriction f).polynomialMap (rawLeftInverse target) =
      if leftIsInverted target then rawLeftInverse source
      else if leftIsInverted source then leftInverseRelation source
      else rawLeftInverse source := by
  rw [rawLeftInverse_eq, rawVariable_eq,
    referenceTypedRestriction_polynomialMap_variable]
  rfl

@[simp] private theorem referenceTypedRestriction_polynomialMap_rawRightInverse
    {source target : referenceSite.category} (f : source ⟶ target) :
    (referenceTypedRestriction f).polynomialMap (rawRightInverse target) =
      if rightIsInverted target then rawRightInverse source
      else if rightIsInverted source then rightInverseRelation source
      else rawRightInverse source := by
  rw [rawRightInverse_eq, rawVariable_eq,
    referenceTypedRestriction_polynomialMap_variable]
  rfl

private theorem leftIsInverted_mono
    {source target : referenceSite.category} (f : source ⟶ target) :
    leftIsInverted target → leftIsInverted source := by
  intro ht
  have hle : ReferenceLe source.ctx target.ctx := CategoryTheory.leOfHom f
  rcases hle with hctx | ⟨i, j, hs, htgt, hij⟩
  · have hobj : source = target := contextObject_ext hctx
    subst target
    exact ht
  · have hsource : source = context i := contextObject_eq hs
    have htarget : target = context j := contextObject_eq htgt
    subst source
    subst target
    cases i <;> cases j <;>
      simp_all [AAT.AG.FiniteModel.twoPatchContextIndexLe,
        leftIsInverted_overlap, leftIsInverted_left,
        leftIsInverted_right, leftIsInverted_base, leftContext,
        rightContext, overlapContext, baseContext]
    all_goals
      have hnot : ¬ leftIsInverted baseContext := by
        simpa only [baseContext] using leftIsInverted_base
      exact (hnot ht).elim

private theorem rightIsInverted_mono
    {source target : referenceSite.category} (f : source ⟶ target) :
    rightIsInverted target → rightIsInverted source := by
  intro ht
  have hle : ReferenceLe source.ctx target.ctx := CategoryTheory.leOfHom f
  rcases hle with hctx | ⟨i, j, hs, htgt, hij⟩
  · have hobj : source = target := contextObject_ext hctx
    subst target
    exact ht
  · have hsource : source = context i := contextObject_eq hs
    have htarget : target = context j := contextObject_eq htgt
    subst source
    subst target
    cases i <;> cases j <;>
      simp_all [AAT.AG.FiniteModel.twoPatchContextIndexLe,
        rightIsInverted_overlap, rightIsInverted_left,
        rightIsInverted_right, rightIsInverted_base, leftContext,
        rightContext, overlapContext, baseContext]
    all_goals
      have hnot : ¬ rightIsInverted baseContext := by
        simpa only [baseContext] using rightIsInverted_base
      exact (hnot ht).elim

@[simp] private theorem referenceTypedRestriction_polynomialMap_relation
    {source target : referenceSite.category} (f : source ⟶ target)
    (r : Bool) :
    (referenceTypedRestriction f).polynomialMap
        (referenceRelationPolynomial target r) =
      referenceRelationPolynomial source r := by
  cases r
  · rw [referenceRelationPolynomial_false,
      referenceRelationPolynomial_false]
    by_cases ht : leftIsInverted target
    · have hs := leftIsInverted_mono f ht
      rw [if_pos ht, if_pos hs]
      simp only [leftInverseRelation, map_sub, map_mul, map_one]
      rw [referenceTypedRestriction_polynomialMap_rawX,
        referenceTypedRestriction_polynomialMap_rawLeftInverse]
      rw [if_pos ht]
    · rw [if_neg ht]
      by_cases hs : leftIsInverted source
      · rw [if_pos hs,
          referenceTypedRestriction_polynomialMap_rawLeftInverse]
        rw [if_neg ht, if_pos hs]
      · rw [if_neg hs,
          referenceTypedRestriction_polynomialMap_rawLeftInverse]
        rw [if_neg ht, if_neg hs]

  · rw [referenceRelationPolynomial_true,
      referenceRelationPolynomial_true]
    by_cases ht : rightIsInverted target
    · have hs := rightIsInverted_mono f ht
      rw [if_pos ht, if_pos hs]
      simp only [rightInverseRelation, map_sub, map_mul, map_one]
      rw [referenceTypedRestriction_polynomialMap_rawX,
        referenceTypedRestriction_polynomialMap_rawRightInverse]
      rw [if_pos ht]
    · rw [if_neg ht]
      by_cases hs : rightIsInverted source
      · rw [if_pos hs,
          referenceTypedRestriction_polynomialMap_rawRightInverse]
        rw [if_neg ht, if_pos hs]
      · rw [if_neg hs,
          referenceTypedRestriction_polynomialMap_rawRightInverse]
        rw [if_neg ht, if_neg hs]

private theorem referenceTypedRestriction_polynomialMap_leftInverseRelation
    {source target : referenceSite.category} (f : source ⟶ target)
    (ht : leftIsInverted target) :
    (referenceTypedRestriction f).polynomialMap (leftInverseRelation target) =
      leftInverseRelation source := by
  have hs := leftIsInverted_mono f ht
  rw [← show referenceRelationPolynomial target false =
      leftInverseRelation target by
        rw [referenceRelationPolynomial_false, if_pos ht]]
  rw [referenceTypedRestriction_polynomialMap_relation]
  rw [referenceRelationPolynomial_false, if_pos hs]

private theorem referenceTypedRestriction_polynomialMap_rightInverseRelation
    {source target : referenceSite.category} (f : source ⟶ target)
    (ht : rightIsInverted target) :
    (referenceTypedRestriction f).polynomialMap (rightInverseRelation target) =
      rightInverseRelation source := by
  have hs := rightIsInverted_mono f ht
  rw [← show referenceRelationPolynomial target true =
      rightInverseRelation target by
        rw [referenceRelationPolynomial_true, if_pos ht]]
  rw [referenceTypedRestriction_polynomialMap_relation]
  rw [referenceRelationPolynomial_true, if_pos hs]

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem referenceTypedRestriction_maps_JStruct
    {source target : referenceSite.category} (f : source ⟶ target)
    (p : FreeTypedCommAlg (referenceCoordinateFamily target) Int)
    (hp : p ∈ (referenceRelationFamily target).JStruct) :
    (referenceTypedRestriction f).polynomialMap p ∈
      (referenceRelationFamily source).JStruct := by
  have hmap : Ideal.map (referenceTypedRestriction f).polynomialMap
      (referenceRelationFamily target).JStruct ≤
        (referenceRelationFamily source).JStruct := by
    rw [StructuralRelationFamily.JStruct,
      StructuralRelationFamily.JStruct, Ideal.map_span]
    apply Ideal.span_le.mpr
    rintro q ⟨r, ⟨s, rfl⟩, rfl⟩
    cases s
    · change (referenceTypedRestriction f).polynomialMap
          (referenceRelationPolynomial target false) ∈
        (referenceRelationFamily source).JStruct
      rw [referenceTypedRestriction_polynomialMap_relation]
      exact Ideal.subset_span ⟨false, rfl⟩
    · change (referenceTypedRestriction f).polynomialMap
          (referenceRelationPolynomial target true) ∈
        (referenceRelationFamily source).JStruct
      rw [referenceTypedRestriction_polynomialMap_relation]
      exact Ideal.subset_span ⟨true, rfl⟩
  exact hmap (Ideal.mem_map_of_mem (referenceTypedRestriction f).polynomialMap hp)

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def referenceRestrictionStable
    {source target : referenceSite.category} (f : source ⟶ target) :
    RestrictionStableStructuralRelations
      (referenceRelationFamily source)
      (referenceRelationFamily target)
      (referenceSite.contextPreorder.morphism
        (CategoryTheory.leOfHom f)) where
  restriction := referenceTypedRestriction f
  maps_JStruct := referenceTypedRestriction_maps_JStruct f

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem referenceRestrictionStable_identity (W : referenceSite.category) :
    (referenceRestrictionStable (𝟙 W)).restriction.polynomialMap =
      RingHom.id (FreeTypedCommAlg (referenceCoordinateFamily W) Int) := by
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [TypedCoordinateRestriction.polynomialMap]
  · intro c
    change (referenceTypedRestriction (𝟙 W)).polynomialMap
        (MvPolynomial.X c) = MvPolynomial.X c
    cases c
    · exact referenceTypedRestriction_polynomialMap_coordinate (f := 𝟙 W)
    · change (referenceTypedRestriction (𝟙 W)).polynomialMap
          (MvPolynomial.X ReferenceRawCoordinate.leftInverse) =
        rawLeftInverse W
      rw [referenceTypedRestriction_polynomialMap_leftInverse]
      by_cases h : leftIsInverted W
      · rw [if_pos h]
      · rw [if_neg h, if_neg h]
    · change (referenceTypedRestriction (𝟙 W)).polynomialMap
          (MvPolynomial.X ReferenceRawCoordinate.rightInverse) =
        rawRightInverse W
      rw [referenceTypedRestriction_polynomialMap_rightInverse]
      by_cases h : rightIsInverted W
      · rw [if_pos h]
      · rw [if_neg h, if_neg h]

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem referenceRestrictionStable_comp
    {X Y Z : referenceSite.category} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (referenceRestrictionStable (f ≫ g)).restriction.polynomialMap =
      ((referenceRestrictionStable f).restriction.polynomialMap).comp
        ((referenceRestrictionStable g).restriction.polynomialMap) := by
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [TypedCoordinateRestriction.polynomialMap]
  · intro c
    change (referenceTypedRestriction (f ≫ g)).polynomialMap
        (MvPolynomial.X c) =
      (referenceTypedRestriction f).polynomialMap
        ((referenceTypedRestriction g).polynomialMap (MvPolynomial.X c))
    cases c
    · rw [referenceTypedRestriction_polynomialMap_coordinate (f := f ≫ g),
        referenceTypedRestriction_polynomialMap_coordinate (f := g),
        referenceTypedRestriction_polynomialMap_rawX (f := f)]
    · by_cases hZ : leftIsInverted Z
      · have hY := leftIsInverted_mono g hZ
        have hX := leftIsInverted_mono f hY
        rw [referenceTypedRestriction_polynomialMap_leftInverse (f := f ≫ g),
          if_pos hZ,
          referenceTypedRestriction_polynomialMap_leftInverse (f := g),
          if_pos hZ,
          referenceTypedRestriction_polynomialMap_rawLeftInverse (f := f),
          if_pos hY]
      · by_cases hY : leftIsInverted Y
        · have hX := leftIsInverted_mono f hY
          rw [referenceTypedRestriction_polynomialMap_leftInverse (f := f ≫ g),
            if_neg hZ, if_pos hX,
            referenceTypedRestriction_polynomialMap_leftInverse (f := g),
            if_neg hZ, if_pos hY,
            referenceTypedRestriction_polynomialMap_leftInverseRelation f hY]
        · by_cases hX : leftIsInverted X
          · rw [referenceTypedRestriction_polynomialMap_leftInverse (f := f ≫ g),
              if_neg hZ, if_pos hX,
              referenceTypedRestriction_polynomialMap_leftInverse (f := g),
              if_neg hZ, if_neg hY,
              referenceTypedRestriction_polynomialMap_rawLeftInverse (f := f),
              if_neg hY, if_pos hX]
          · rw [referenceTypedRestriction_polynomialMap_leftInverse (f := f ≫ g),
              if_neg hZ, if_neg hX,
              referenceTypedRestriction_polynomialMap_leftInverse (f := g),
              if_neg hZ, if_neg hY,
              referenceTypedRestriction_polynomialMap_rawLeftInverse (f := f),
              if_neg hY, if_neg hX]
    · by_cases hZ : rightIsInverted Z
      · have hY := rightIsInverted_mono g hZ
        have hX := rightIsInverted_mono f hY
        rw [referenceTypedRestriction_polynomialMap_rightInverse (f := f ≫ g),
          if_pos hZ,
          referenceTypedRestriction_polynomialMap_rightInverse (f := g),
          if_pos hZ,
          referenceTypedRestriction_polynomialMap_rawRightInverse (f := f),
          if_pos hY]
      · by_cases hY : rightIsInverted Y
        · have hX := rightIsInverted_mono f hY
          rw [referenceTypedRestriction_polynomialMap_rightInverse (f := f ≫ g),
            if_neg hZ, if_pos hX,
            referenceTypedRestriction_polynomialMap_rightInverse (f := g),
            if_neg hZ, if_pos hY,
            referenceTypedRestriction_polynomialMap_rightInverseRelation f hY]
        · by_cases hX : rightIsInverted X
          · rw [referenceTypedRestriction_polynomialMap_rightInverse (f := f ≫ g),
              if_neg hZ, if_pos hX,
              referenceTypedRestriction_polynomialMap_rightInverse (f := g),
              if_neg hZ, if_neg hY,
              referenceTypedRestriction_polynomialMap_rawRightInverse (f := f),
              if_neg hY, if_pos hX]
          · rw [referenceTypedRestriction_polynomialMap_rightInverse (f := f ≫ g),
              if_neg hZ, if_neg hX,
              referenceTypedRestriction_polynomialMap_rightInverse (f := g),
              if_neg hZ, if_neg hY,
              referenceTypedRestriction_polynomialMap_rawRightInverse (f := f),
              if_neg hY, if_neg hX]

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def referenceRaw :
    RawAmbientRestrictionSystem referenceSite Int where
  coordFamily := referenceCoordinateFamily
  relationFamily := referenceRelationFamily
  restrictionStable := referenceRestrictionStable
  identity_polynomialMap := referenceRestrictionStable_identity
  composition_polynomialMap := referenceRestrictionStable_comp

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem referenceRaw_coordFamily (W : referenceSite.category) :
    referenceRaw.coordFamily W = referenceCoordinateFamily W :=
  rfl

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem referenceRaw_relationFamily (W : referenceSite.category) :
    referenceRaw.relationFamily W = referenceRelationFamily W :=
  rfl

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem referenceRaw_restrictionStable
    {source target : referenceSite.category} (f : source ⟶ target) :
    referenceRaw.restrictionStable f = referenceRestrictionStable f :=
  rfl

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def rawCoordinate (W : referenceSite.category) :
    referenceRaw.rawAlgebra W :=
  (referenceRelationFamily W).quotientMap (rawX W)

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem rawCoordinate_eq (W : referenceSite.category) :
    rawCoordinate W =
      (referenceRelationFamily W).quotientMap (rawX W) :=
  rfl

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem rawCoordinate_restrict
    {source target : referenceSite.category} (f : source ⟶ target) :
    (referenceRaw.restrictionStable f).quotientDesc
        (rawCoordinate target) = rawCoordinate source := by
  rw [rawCoordinate_eq, rawCoordinate_eq,
    referenceRaw_restrictionStable]
  change (referenceRelationFamily source).quotientMap
      ((referenceTypedRestriction f).polynomialMap (rawX target)) =
    (referenceRelationFamily source).quotientMap (rawX source)
  rw [show (referenceTypedRestriction f).polynomialMap (rawX target) =
      rawX source by
    rw [rawX_eq, rawVariable_eq,
      referenceTypedRestriction_polynomialMap_variable]
    rfl]

private noncomputable def baseConfiguration :
    (referenceRelationFamily baseContext).Configuration AmbientRing where
  val
    | .coordinate => coordinate
    | .leftInverse => 0
    | .rightInverse => 0
  property r := by
    cases r
    · change MvPolynomial.aeval (fun c => match c with
          | .coordinate => coordinate
          | .leftInverse => 0
          | .rightInverse => 0)
        (referenceRelationPolynomial baseContext false) = 0
      rw [referenceRelationPolynomial_false, if_neg leftIsInverted_base]
      simp [rawLeftInverse, rawVariable]
    · change MvPolynomial.aeval (fun c => match c with
          | .coordinate => coordinate
          | .leftInverse => 0
          | .rightInverse => 0)
        (referenceRelationPolynomial baseContext true) = 0
      rw [referenceRelationPolynomial_true, if_neg rightIsInverted_base]
      simp [rawRightInverse, rawVariable]

private noncomputable def baseRawToAmbientAlgHom :
    referenceRaw.rawAlgebra baseContext →ₐ[Int] AmbientRing :=
  (referenceRelationFamily baseContext).configurationRepresentability
    AmbientRing baseConfiguration

private noncomputable def ambientToBaseRawAlgHom :
    AmbientRing →ₐ[Int] referenceRaw.rawAlgebra baseContext :=
  MvPolynomial.aeval (fun _ => rawCoordinate baseContext)

@[simp] private theorem baseRawToAmbientAlgHom_rawCoordinate :
    baseRawToAmbientAlgHom (rawCoordinate baseContext) = coordinate := by
  change (referenceRelationFamily baseContext).quotientAlgHomOfConfiguration
      baseConfiguration
      ((referenceRelationFamily baseContext).quotientMap (rawX baseContext)) =
    coordinate
  rw [StructuralRelationFamily.quotientAlgHomOfConfiguration_mk]
  change MvPolynomial.bind₁ (fun c => match c with
      | .coordinate => coordinate
      | .leftInverse => 0
      | .rightInverse => 0)
    (MvPolynomial.X ReferenceRawCoordinate.coordinate) = coordinate
  rw [MvPolynomial.bind₁_X_right]

@[simp] private theorem ambientToBaseRawAlgHom_coordinate :
    ambientToBaseRawAlgHom coordinate = rawCoordinate baseContext := by
  simp [ambientToBaseRawAlgHom, coordinate]

private theorem baseRawToAmbientAlgHom_comp_ambientToBaseRawAlgHom :
    baseRawToAmbientAlgHom.comp ambientToBaseRawAlgHom =
      AlgHom.id Int AmbientRing := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i
  change baseRawToAmbientAlgHom
      (ambientToBaseRawAlgHom coordinate) = coordinate
  rw [ambientToBaseRawAlgHom_coordinate,
    baseRawToAmbientAlgHom_rawCoordinate]

@[simp] private theorem base_rawLeftInverse_eq_zero :
    (referenceRelationFamily baseContext).quotientMap
        (rawLeftInverse baseContext) = 0 := by
  have h :=
    (referenceRelationFamily baseContext).quotientMap_polynomial_eq_zero false
  rw [referenceRelationFamily_polynomial, referenceRelationPolynomial_false,
    if_neg leftIsInverted_base] at h
  exact h

@[simp] private theorem base_rawRightInverse_eq_zero :
    (referenceRelationFamily baseContext).quotientMap
        (rawRightInverse baseContext) = 0 := by
  have h :=
    (referenceRelationFamily baseContext).quotientMap_polynomial_eq_zero true
  rw [referenceRelationFamily_polynomial, referenceRelationPolynomial_true,
    if_neg rightIsInverted_base] at h
  exact h

private theorem ambientToBaseRawAlgHom_comp_baseRawToAmbientAlgHom :
    ambientToBaseRawAlgHom.comp baseRawToAmbientAlgHom =
      AlgHom.id Int (referenceRaw.rawAlgebra baseContext) := by
  apply Ideal.Quotient.algHom_ext _
  apply MvPolynomial.algHom_ext
  intro c
  cases c
  · change ambientToBaseRawAlgHom
        (baseRawToAmbientAlgHom (rawCoordinate baseContext)) =
      rawCoordinate baseContext
    rw [baseRawToAmbientAlgHom_rawCoordinate,
      ambientToBaseRawAlgHom_coordinate]
  · change ambientToBaseRawAlgHom (baseRawToAmbientAlgHom
        ((referenceRelationFamily baseContext).quotientMap
          (rawLeftInverse baseContext))) = _
    have hmap : baseRawToAmbientAlgHom
        ((referenceRelationFamily baseContext).quotientMap
          (rawLeftInverse baseContext)) = 0 := by
      change (referenceRelationFamily baseContext).configurationAlgHom
          baseConfiguration (rawLeftInverse baseContext) = 0
      change MvPolynomial.bind₁ (fun c => match c with
          | .coordinate => coordinate
          | .leftInverse => 0
          | .rightInverse => 0)
        (MvPolynomial.X ReferenceRawCoordinate.leftInverse) = 0
      rw [MvPolynomial.bind₁_X_right]
    rw [hmap, map_zero]
    change 0 = (referenceRelationFamily baseContext).quotientMap
      (rawLeftInverse baseContext)
    rw [base_rawLeftInverse_eq_zero]
  · change ambientToBaseRawAlgHom (baseRawToAmbientAlgHom
        ((referenceRelationFamily baseContext).quotientMap
          (rawRightInverse baseContext))) = _
    have hmap : baseRawToAmbientAlgHom
        ((referenceRelationFamily baseContext).quotientMap
          (rawRightInverse baseContext)) = 0 := by
      change (referenceRelationFamily baseContext).configurationAlgHom
          baseConfiguration (rawRightInverse baseContext) = 0
      change MvPolynomial.bind₁ (fun c => match c with
          | .coordinate => coordinate
          | .leftInverse => 0
          | .rightInverse => 0)
        (MvPolynomial.X ReferenceRawCoordinate.rightInverse) = 0
      rw [MvPolynomial.bind₁_X_right]
    rw [hmap, map_zero]
    change 0 = (referenceRelationFamily baseContext).quotientMap
      (rawRightInverse baseContext)
    rw [base_rawRightInverse_eq_zero]

private noncomputable def baseRawRingEquiv :
    referenceRaw.rawAlgebra baseContext ≃+* AmbientRing :=
  RingEquiv.ofRingHom baseRawToAmbientAlgHom.toRingHom
    ambientToBaseRawAlgHom.toRingHom
    (by
      exact congrArg AlgHom.toRingHom
        baseRawToAmbientAlgHom_comp_ambientToBaseRawAlgHom)
    (by
      exact congrArg AlgHom.toRingHom
        ambientToBaseRawAlgHom_comp_baseRawToAmbientAlgHom)

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def baseRawAlgebraIso :
    CommRingCat.of (referenceRaw.rawAlgebra baseContext) ≅
      CommRingCat.of AmbientRing :=
  baseRawRingEquiv.toCommRingCatIso

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem baseRawAlgebraIso_coordinate :
    baseRawAlgebraIso.hom (rawCoordinate baseContext) = coordinate := by
  change baseRawToAmbientAlgHom (rawCoordinate baseContext) = coordinate
  exact baseRawToAmbientAlgHom_rawCoordinate

private noncomputable def rawLeftInverseClass (W : referenceSite.category) :
    referenceRaw.rawAlgebra W :=
  (referenceRelationFamily W).quotientMap (rawLeftInverse W)

private noncomputable def rawRightInverseClass (W : referenceSite.category) :
    referenceRaw.rawAlgebra W :=
  (referenceRelationFamily W).quotientMap (rawRightInverse W)

private noncomputable def ambientToRawAlgHom (W : referenceSite.category) :
    AmbientRing →ₐ[Int] referenceRaw.rawAlgebra W :=
  MvPolynomial.aeval (fun _ => rawCoordinate W)

@[simp] private theorem ambientToRawAlgHom_coordinate (W : referenceSite.category) :
    ambientToRawAlgHom W coordinate = rawCoordinate W := by
  change MvPolynomial.aeval (fun _ => rawCoordinate W)
      (MvPolynomial.X ()) = rawCoordinate W
  rw [MvPolynomial.aeval_X]

private theorem left_rawCoordinate_mul_inverse :
    rawCoordinate leftContext * rawLeftInverseClass leftContext = 1 := by
  have h :=
    (referenceRelationFamily leftContext).quotientMap_polynomial_eq_zero false
  rw [referenceRelationFamily_polynomial, referenceRelationPolynomial_false,
    if_pos leftIsInverted_left] at h
  change rawCoordinate leftContext * rawLeftInverseClass leftContext - 1 = 0 at h
  exact sub_eq_zero.mp h

private theorem left_rawCoordinate_isUnit :
    IsUnit (rawCoordinate leftContext) :=
  isUnit_iff_exists_inv.mpr ⟨rawLeftInverseClass leftContext,
    left_rawCoordinate_mul_inverse⟩

private noncomputable def leftConfiguration :
    (referenceRelationFamily leftContext).Configuration
      (Localization.Away leftGenerator) where
  val
    | .coordinate => algebraMap AmbientRing
        (Localization.Away leftGenerator) coordinate
    | .leftInverse => IsLocalization.Away.invSelf leftGenerator
    | .rightInverse => 0
  property r := by
    cases r
    · change MvPolynomial.aeval (fun c => match c with
          | .coordinate => algebraMap AmbientRing
              (Localization.Away leftGenerator) coordinate
          | .leftInverse => IsLocalization.Away.invSelf leftGenerator
          | .rightInverse => 0)
        (referenceRelationPolynomial leftContext false) = 0
      rw [referenceRelationPolynomial_false, if_pos leftIsInverted_left]
      simp only [leftInverseRelation, map_sub, map_mul, map_one,
        rawX_eq, rawLeftInverse_eq, rawVariable_eq, MvPolynomial.aeval_X]
      rw [show coordinate = leftGenerator by rfl,
        IsLocalization.Away.mul_invSelf]
      exact sub_self 1
    · change MvPolynomial.aeval (fun c => match c with
          | .coordinate => algebraMap AmbientRing
              (Localization.Away leftGenerator) coordinate
          | .leftInverse => IsLocalization.Away.invSelf leftGenerator
          | .rightInverse => 0)
        (referenceRelationPolynomial leftContext true) = 0
      rw [referenceRelationPolynomial_true, if_neg rightIsInverted_left]
      simp [rawRightInverse, rawVariable]

private noncomputable def leftRawToLocalizationAlgHom :
    referenceRaw.rawAlgebra leftContext →ₐ[Int]
      Localization.Away leftGenerator :=
  (referenceRelationFamily leftContext).configurationRepresentability
    (Localization.Away leftGenerator) leftConfiguration

private noncomputable def leftLocalizationToRawRingHom :
    Localization.Away leftGenerator →+* referenceRaw.rawAlgebra leftContext :=
  IsLocalization.Away.lift leftGenerator
    (by
      change IsUnit (ambientToRawAlgHom leftContext leftGenerator)
      rw [leftGenerator, ambientToRawAlgHom_coordinate]
      exact left_rawCoordinate_isUnit)

@[simp] private theorem leftRawToLocalizationAlgHom_rawCoordinate :
    leftRawToLocalizationAlgHom (rawCoordinate leftContext) =
      algebraMap AmbientRing (Localization.Away leftGenerator) coordinate := by
  change (referenceRelationFamily leftContext).quotientAlgHomOfConfiguration
      leftConfiguration
      ((referenceRelationFamily leftContext).quotientMap (rawX leftContext)) = _
  rw [StructuralRelationFamily.quotientAlgHomOfConfiguration_mk]
  change MvPolynomial.aeval (fun c => match c with
      | .coordinate => algebraMap AmbientRing
          (Localization.Away leftGenerator) coordinate
      | .leftInverse => IsLocalization.Away.invSelf leftGenerator
      | .rightInverse => 0)
    (MvPolynomial.X ReferenceRawCoordinate.coordinate) = _
  rw [MvPolynomial.aeval_X]

@[simp] private theorem leftRawToLocalizationAlgHom_rawLeftInverse :
    leftRawToLocalizationAlgHom (rawLeftInverseClass leftContext) =
      IsLocalization.Away.invSelf leftGenerator := by
  change (referenceRelationFamily leftContext).quotientAlgHomOfConfiguration
      leftConfiguration
      ((referenceRelationFamily leftContext).quotientMap
        (rawLeftInverse leftContext)) = _
  rw [StructuralRelationFamily.quotientAlgHomOfConfiguration_mk]
  change MvPolynomial.aeval (fun c => match c with
      | .coordinate => algebraMap AmbientRing
          (Localization.Away leftGenerator) coordinate
      | .leftInverse => IsLocalization.Away.invSelf leftGenerator
      | .rightInverse => 0)
    (MvPolynomial.X ReferenceRawCoordinate.leftInverse) = _
  rw [MvPolynomial.aeval_X]

private theorem leftLocalizationToRawRingHom_comp_algebraMap :
    leftLocalizationToRawRingHom.comp
        (algebraMap AmbientRing (Localization.Away leftGenerator)) =
      ambientToRawAlgHom leftContext :=
  IsLocalization.Away.lift_comp _ _

private theorem leftLocalizationToRawRingHom_invSelf :
    leftLocalizationToRawRingHom (IsLocalization.Away.invSelf leftGenerator) =
      rawLeftInverseClass leftContext := by
  apply left_rawCoordinate_isUnit.mul_left_cancel
  calc
    rawCoordinate leftContext *
        leftLocalizationToRawRingHom (IsLocalization.Away.invSelf leftGenerator) =
      leftLocalizationToRawRingHom
        (algebraMap AmbientRing (Localization.Away leftGenerator) leftGenerator *
          IsLocalization.Away.invSelf leftGenerator) := by
            rw [map_mul]
            congr 1
            have h := RingHom.congr_fun
              leftLocalizationToRawRingHom_comp_algebraMap coordinate
            change leftLocalizationToRawRingHom
                (algebraMap AmbientRing
                  (Localization.Away leftGenerator) coordinate) =
              ambientToRawAlgHom leftContext coordinate at h
            rw [ambientToRawAlgHom_coordinate] at h
            simpa only [leftGenerator] using h.symm
    _ = 1 := by rw [IsLocalization.Away.mul_invSelf, map_one]
    _ = rawCoordinate leftContext * rawLeftInverseClass leftContext :=
      left_rawCoordinate_mul_inverse.symm

private theorem leftRawToLocalization_comp_leftLocalizationToRaw :
    leftRawToLocalizationAlgHom.toRingHom.comp leftLocalizationToRawRingHom =
      RingHom.id (Localization.Away leftGenerator) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers leftGenerator)
  rw [RingHom.comp_assoc, leftLocalizationToRawRingHom_comp_algebraMap]
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [ambientToRawAlgHom]
  · intro i
    cases i
    change leftRawToLocalizationAlgHom
        (ambientToRawAlgHom leftContext coordinate) =
      algebraMap AmbientRing (Localization.Away leftGenerator) coordinate
    rw [ambientToRawAlgHom_coordinate,
      leftRawToLocalizationAlgHom_rawCoordinate]

private theorem leftLocalizationToRaw_comp_leftRawToLocalization :
    leftLocalizationToRawRingHom.comp leftRawToLocalizationAlgHom.toRingHom =
      RingHom.id (referenceRaw.rawAlgebra leftContext) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro z
    have h := RingHom.congr_fun leftLocalizationToRawRingHom_comp_algebraMap
      (MvPolynomial.C z : AmbientRing)
    simpa [leftRawToLocalizationAlgHom,
      StructuralRelationFamily.configurationAlgHom, leftConfiguration,
      ambientToRawAlgHom] using h
  · intro c
    cases c
    · change leftLocalizationToRawRingHom
          (leftRawToLocalizationAlgHom (rawCoordinate leftContext)) =
        rawCoordinate leftContext
      rw [leftRawToLocalizationAlgHom_rawCoordinate]
      have h := RingHom.congr_fun
        leftLocalizationToRawRingHom_comp_algebraMap coordinate
      calc
        leftLocalizationToRawRingHom
            (algebraMap AmbientRing
              (Localization.Away leftGenerator) coordinate) =
          ambientToRawAlgHom leftContext coordinate := h
        _ = rawCoordinate leftContext :=
          ambientToRawAlgHom_coordinate leftContext
    · change leftLocalizationToRawRingHom
          (leftRawToLocalizationAlgHom (rawLeftInverseClass leftContext)) =
        rawLeftInverseClass leftContext
      rw [leftRawToLocalizationAlgHom_rawLeftInverse]
      exact leftLocalizationToRawRingHom_invSelf
    · change leftLocalizationToRawRingHom
          (leftRawToLocalizationAlgHom (rawRightInverseClass leftContext)) =
        rawRightInverseClass leftContext
      have h :=
        (referenceRelationFamily leftContext).quotientMap_polynomial_eq_zero true
      rw [referenceRelationFamily_polynomial, referenceRelationPolynomial_true,
        if_neg rightIsInverted_left] at h
      change rawRightInverseClass leftContext = 0 at h
      simp [h]

private noncomputable def leftRawRingEquiv :
    referenceRaw.rawAlgebra leftContext ≃+*
      Localization.Away leftGenerator :=
  RingEquiv.ofRingHom leftRawToLocalizationAlgHom.toRingHom
    leftLocalizationToRawRingHom
    leftRawToLocalization_comp_leftLocalizationToRaw
    leftLocalizationToRaw_comp_leftRawToLocalization

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def leftRawAlgebraIso :
    CommRingCat.of (referenceRaw.rawAlgebra leftContext) ≅
      CommRingCat.of (Localization.Away leftGenerator) :=
  leftRawRingEquiv.toCommRingCatIso

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem leftRawAlgebraIso_coordinate :
    leftRawAlgebraIso.hom (rawCoordinate leftContext) =
      algebraMap AmbientRing (Localization.Away leftGenerator) coordinate := by
  change leftRawToLocalizationAlgHom (rawCoordinate leftContext) = _
  exact leftRawToLocalizationAlgHom_rawCoordinate

private theorem right_rawGenerator_mul_inverse :
    (1 - rawCoordinate rightContext) * rawRightInverseClass rightContext = 1 := by
  have h :=
    (referenceRelationFamily rightContext).quotientMap_polynomial_eq_zero true
  rw [referenceRelationFamily_polynomial, referenceRelationPolynomial_true,
    if_pos rightIsInverted_right] at h
  change (1 - rawCoordinate rightContext) * rawRightInverseClass rightContext - 1 = 0 at h
  exact sub_eq_zero.mp h

private theorem right_rawGenerator_isUnit :
    IsUnit (1 - rawCoordinate rightContext) :=
  isUnit_iff_exists_inv.mpr ⟨rawRightInverseClass rightContext,
    right_rawGenerator_mul_inverse⟩

private noncomputable def rightConfiguration :
    (referenceRelationFamily rightContext).Configuration
      (Localization.Away rightGenerator) where
  val
    | .coordinate => algebraMap AmbientRing
        (Localization.Away rightGenerator) coordinate
    | .leftInverse => 0
    | .rightInverse => IsLocalization.Away.invSelf rightGenerator
  property r := by
    cases r
    · change MvPolynomial.aeval (fun c => match c with
          | .coordinate => algebraMap AmbientRing
              (Localization.Away rightGenerator) coordinate
          | .leftInverse => 0
          | .rightInverse => IsLocalization.Away.invSelf rightGenerator)
        (referenceRelationPolynomial rightContext false) = 0
      rw [referenceRelationPolynomial_false, if_neg leftIsInverted_right]
      simp [rawLeftInverse, rawVariable]
    · change MvPolynomial.aeval (fun c => match c with
          | .coordinate => algebraMap AmbientRing
              (Localization.Away rightGenerator) coordinate
          | .leftInverse => 0
          | .rightInverse => IsLocalization.Away.invSelf rightGenerator)
        (referenceRelationPolynomial rightContext true) = 0
      rw [referenceRelationPolynomial_true, if_pos rightIsInverted_right]
      simp only [rightInverseRelation, map_sub, map_mul, map_one,
        rawX_eq, rawRightInverse_eq, rawVariable_eq, MvPolynomial.aeval_X]
      rw [show 1 - algebraMap AmbientRing
          (Localization.Away rightGenerator) coordinate =
        algebraMap AmbientRing (Localization.Away rightGenerator)
          rightGenerator by simp [rightGenerator],
        IsLocalization.Away.mul_invSelf]
      exact sub_self 1

private noncomputable def rightRawToLocalizationAlgHom :
    referenceRaw.rawAlgebra rightContext →ₐ[Int]
      Localization.Away rightGenerator :=
  (referenceRelationFamily rightContext).configurationRepresentability
    (Localization.Away rightGenerator) rightConfiguration

private noncomputable def rightLocalizationToRawRingHom :
    Localization.Away rightGenerator →+* referenceRaw.rawAlgebra rightContext :=
  IsLocalization.Away.lift rightGenerator
    (by
      change IsUnit (ambientToRawAlgHom rightContext rightGenerator)
      rw [rightGenerator, map_sub, map_one, ambientToRawAlgHom_coordinate]
      exact right_rawGenerator_isUnit)

@[simp] private theorem rightRawToLocalizationAlgHom_rawCoordinate :
    rightRawToLocalizationAlgHom (rawCoordinate rightContext) =
      algebraMap AmbientRing (Localization.Away rightGenerator) coordinate := by
  change (referenceRelationFamily rightContext).quotientAlgHomOfConfiguration
      rightConfiguration
      ((referenceRelationFamily rightContext).quotientMap (rawX rightContext)) = _
  rw [StructuralRelationFamily.quotientAlgHomOfConfiguration_mk]
  change MvPolynomial.aeval (fun c => match c with
      | .coordinate => algebraMap AmbientRing
          (Localization.Away rightGenerator) coordinate
      | .leftInverse => 0
      | .rightInverse => IsLocalization.Away.invSelf rightGenerator)
    (MvPolynomial.X ReferenceRawCoordinate.coordinate) = _
  rw [MvPolynomial.aeval_X]

@[simp] private theorem rightRawToLocalizationAlgHom_rawRightInverse :
    rightRawToLocalizationAlgHom (rawRightInverseClass rightContext) =
      IsLocalization.Away.invSelf rightGenerator := by
  change (referenceRelationFamily rightContext).quotientAlgHomOfConfiguration
      rightConfiguration
      ((referenceRelationFamily rightContext).quotientMap
        (rawRightInverse rightContext)) = _
  rw [StructuralRelationFamily.quotientAlgHomOfConfiguration_mk]
  change MvPolynomial.aeval (fun c => match c with
      | .coordinate => algebraMap AmbientRing
          (Localization.Away rightGenerator) coordinate
      | .leftInverse => 0
      | .rightInverse => IsLocalization.Away.invSelf rightGenerator)
    (MvPolynomial.X ReferenceRawCoordinate.rightInverse) = _
  rw [MvPolynomial.aeval_X]

private theorem rightLocalizationToRawRingHom_comp_algebraMap :
    rightLocalizationToRawRingHom.comp
        (algebraMap AmbientRing (Localization.Away rightGenerator)) =
      ambientToRawAlgHom rightContext :=
  IsLocalization.Away.lift_comp _ _

private theorem rightLocalizationToRawRingHom_invSelf :
    rightLocalizationToRawRingHom (IsLocalization.Away.invSelf rightGenerator) =
      rawRightInverseClass rightContext := by
  apply right_rawGenerator_isUnit.mul_left_cancel
  calc
    (1 - rawCoordinate rightContext) *
        rightLocalizationToRawRingHom (IsLocalization.Away.invSelf rightGenerator) =
      rightLocalizationToRawRingHom
        (algebraMap AmbientRing (Localization.Away rightGenerator) rightGenerator *
          IsLocalization.Away.invSelf rightGenerator) := by
            rw [map_mul]
            congr 1
            have h := RingHom.congr_fun
              rightLocalizationToRawRingHom_comp_algebraMap coordinate
            change rightLocalizationToRawRingHom
                (algebraMap AmbientRing
                  (Localization.Away rightGenerator) coordinate) =
              ambientToRawAlgHom rightContext coordinate at h
            rw [ambientToRawAlgHom_coordinate] at h
            simpa only [rightGenerator, map_sub, map_one] using
              congrArg (1 - ·) h.symm
    _ = 1 := by rw [IsLocalization.Away.mul_invSelf, map_one]
    _ = (1 - rawCoordinate rightContext) * rawRightInverseClass rightContext :=
      right_rawGenerator_mul_inverse.symm

private theorem rightRawToLocalization_comp_rightLocalizationToRaw :
    rightRawToLocalizationAlgHom.toRingHom.comp rightLocalizationToRawRingHom =
      RingHom.id (Localization.Away rightGenerator) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers rightGenerator)
  rw [RingHom.comp_assoc, rightLocalizationToRawRingHom_comp_algebraMap]
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [ambientToRawAlgHom]
  · intro i
    cases i
    change rightRawToLocalizationAlgHom
        (ambientToRawAlgHom rightContext coordinate) =
      algebraMap AmbientRing (Localization.Away rightGenerator) coordinate
    rw [ambientToRawAlgHom_coordinate,
      rightRawToLocalizationAlgHom_rawCoordinate]

private theorem rightLocalizationToRaw_comp_rightRawToLocalization :
    rightLocalizationToRawRingHom.comp rightRawToLocalizationAlgHom.toRingHom =
      RingHom.id (referenceRaw.rawAlgebra rightContext) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro z
    have h := RingHom.congr_fun rightLocalizationToRawRingHom_comp_algebraMap
      (MvPolynomial.C z : AmbientRing)
    simpa [rightRawToLocalizationAlgHom,
      StructuralRelationFamily.configurationAlgHom, rightConfiguration,
      ambientToRawAlgHom] using h
  · intro c
    cases c
    · change rightLocalizationToRawRingHom
          (rightRawToLocalizationAlgHom (rawCoordinate rightContext)) =
        rawCoordinate rightContext
      rw [rightRawToLocalizationAlgHom_rawCoordinate]
      have h := RingHom.congr_fun
        rightLocalizationToRawRingHom_comp_algebraMap coordinate
      calc
        rightLocalizationToRawRingHom
            (algebraMap AmbientRing
              (Localization.Away rightGenerator) coordinate) =
          ambientToRawAlgHom rightContext coordinate := h
        _ = rawCoordinate rightContext :=
          ambientToRawAlgHom_coordinate rightContext
    · change rightLocalizationToRawRingHom
          (rightRawToLocalizationAlgHom (rawLeftInverseClass rightContext)) =
        rawLeftInverseClass rightContext
      have h :=
        (referenceRelationFamily rightContext).quotientMap_polynomial_eq_zero false
      rw [referenceRelationFamily_polynomial, referenceRelationPolynomial_false,
        if_neg leftIsInverted_right] at h
      change rawLeftInverseClass rightContext = 0 at h
      simp [h]
    · change rightLocalizationToRawRingHom
          (rightRawToLocalizationAlgHom (rawRightInverseClass rightContext)) =
        rawRightInverseClass rightContext
      rw [rightRawToLocalizationAlgHom_rawRightInverse]
      exact rightLocalizationToRawRingHom_invSelf

private noncomputable def rightRawRingEquiv :
    referenceRaw.rawAlgebra rightContext ≃+*
      Localization.Away rightGenerator :=
  RingEquiv.ofRingHom rightRawToLocalizationAlgHom.toRingHom
    rightLocalizationToRawRingHom
    rightRawToLocalization_comp_rightLocalizationToRaw
    rightLocalizationToRaw_comp_rightRawToLocalization

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def rightRawAlgebraIso :
    CommRingCat.of (referenceRaw.rawAlgebra rightContext) ≅
      CommRingCat.of (Localization.Away rightGenerator) :=
  rightRawRingEquiv.toCommRingCatIso

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem rightRawAlgebraIso_coordinate :
    rightRawAlgebraIso.hom (rawCoordinate rightContext) =
      algebraMap AmbientRing (Localization.Away rightGenerator) coordinate := by
  change rightRawToLocalizationAlgHom (rawCoordinate rightContext) = _
  exact rightRawToLocalizationAlgHom_rawCoordinate

private noncomputable def overlapLeftInverse : Localization.Away overlapGenerator :=
  algebraMap AmbientRing (Localization.Away overlapGenerator) rightGenerator *
    IsLocalization.Away.invSelf overlapGenerator

private noncomputable def overlapRightInverse : Localization.Away overlapGenerator :=
  algebraMap AmbientRing (Localization.Away overlapGenerator) leftGenerator *
    IsLocalization.Away.invSelf overlapGenerator

private theorem overlap_left_mul_inverse :
    algebraMap AmbientRing (Localization.Away overlapGenerator) leftGenerator *
      overlapLeftInverse = 1 := by
  rw [overlapLeftInverse, ← mul_assoc]
  have hmap :
      algebraMap AmbientRing (Localization.Away overlapGenerator) leftGenerator *
          algebraMap AmbientRing (Localization.Away overlapGenerator) rightGenerator =
        algebraMap AmbientRing (Localization.Away overlapGenerator)
          overlapGenerator := by
    rw [← map_mul, overlapGenerator_eq]
  rw [hmap, IsLocalization.Away.mul_invSelf]

private theorem overlap_right_mul_inverse :
    algebraMap AmbientRing (Localization.Away overlapGenerator) rightGenerator *
      overlapRightInverse = 1 := by
  rw [overlapRightInverse, ← mul_assoc]
  conv_lhs =>
    lhs
    rw [mul_comm]
  have hmap :
      algebraMap AmbientRing (Localization.Away overlapGenerator) leftGenerator *
          algebraMap AmbientRing (Localization.Away overlapGenerator) rightGenerator =
        algebraMap AmbientRing (Localization.Away overlapGenerator)
          overlapGenerator := by
    rw [← map_mul, overlapGenerator_eq]
  rw [hmap, IsLocalization.Away.mul_invSelf]

private theorem overlap_rawLeft_mul_inverse :
    rawCoordinate overlapContext * rawLeftInverseClass overlapContext = 1 := by
  have h :=
    (referenceRelationFamily overlapContext).quotientMap_polynomial_eq_zero false
  rw [referenceRelationFamily_polynomial, referenceRelationPolynomial_false,
    if_pos leftIsInverted_overlap] at h
  change rawCoordinate overlapContext * rawLeftInverseClass overlapContext - 1 = 0 at h
  exact sub_eq_zero.mp h

private theorem overlap_rawRight_mul_inverse :
    (1 - rawCoordinate overlapContext) * rawRightInverseClass overlapContext = 1 := by
  have h :=
    (referenceRelationFamily overlapContext).quotientMap_polynomial_eq_zero true
  rw [referenceRelationFamily_polynomial, referenceRelationPolynomial_true,
    if_pos rightIsInverted_overlap] at h
  change (1 - rawCoordinate overlapContext) * rawRightInverseClass overlapContext - 1 = 0 at h
  exact sub_eq_zero.mp h

private theorem overlap_rawLeft_isUnit :
    IsUnit (rawCoordinate overlapContext) :=
  isUnit_iff_exists_inv.mpr ⟨rawLeftInverseClass overlapContext,
    overlap_rawLeft_mul_inverse⟩

private theorem overlap_rawRight_isUnit :
    IsUnit (1 - rawCoordinate overlapContext) :=
  isUnit_iff_exists_inv.mpr ⟨rawRightInverseClass overlapContext,
    overlap_rawRight_mul_inverse⟩

private theorem overlap_rawGenerator_isUnit :
    IsUnit (ambientToRawAlgHom overlapContext overlapGenerator) := by
  rw [overlapGenerator, map_mul, leftGenerator, rightGenerator, map_sub,
    map_one, ambientToRawAlgHom_coordinate]
  exact overlap_rawLeft_isUnit.mul overlap_rawRight_isUnit

private noncomputable def overlapConfiguration :
    (referenceRelationFamily overlapContext).Configuration
      (Localization.Away overlapGenerator) where
  val
    | .coordinate => algebraMap AmbientRing
        (Localization.Away overlapGenerator) coordinate
    | .leftInverse => overlapLeftInverse
    | .rightInverse => overlapRightInverse
  property r := by
    cases r
    · change MvPolynomial.aeval (fun c => match c with
          | .coordinate => algebraMap AmbientRing
              (Localization.Away overlapGenerator) coordinate
          | .leftInverse => overlapLeftInverse
          | .rightInverse => overlapRightInverse)
        (referenceRelationPolynomial overlapContext false) = 0
      rw [referenceRelationPolynomial_false, if_pos leftIsInverted_overlap]
      simp only [leftInverseRelation, map_sub, map_mul, map_one,
        rawX_eq, rawLeftInverse_eq, rawVariable_eq, MvPolynomial.aeval_X]
      rw [show coordinate = leftGenerator by rfl, overlap_left_mul_inverse]
      exact sub_self 1
    · change MvPolynomial.aeval (fun c => match c with
          | .coordinate => algebraMap AmbientRing
              (Localization.Away overlapGenerator) coordinate
          | .leftInverse => overlapLeftInverse
          | .rightInverse => overlapRightInverse)
        (referenceRelationPolynomial overlapContext true) = 0
      rw [referenceRelationPolynomial_true, if_pos rightIsInverted_overlap]
      simp only [rightInverseRelation, map_sub, map_mul, map_one,
        rawX_eq, rawRightInverse_eq, rawVariable_eq, MvPolynomial.aeval_X]
      rw [show 1 - algebraMap AmbientRing
          (Localization.Away overlapGenerator) coordinate =
        algebraMap AmbientRing (Localization.Away overlapGenerator)
          rightGenerator by simp [rightGenerator],
        overlap_right_mul_inverse]
      exact sub_self 1

private noncomputable def overlapRawToLocalizationAlgHom :
    referenceRaw.rawAlgebra overlapContext →ₐ[Int]
      Localization.Away overlapGenerator :=
  (referenceRelationFamily overlapContext).configurationRepresentability
    (Localization.Away overlapGenerator) overlapConfiguration

private noncomputable def overlapLocalizationToRawRingHom :
    Localization.Away overlapGenerator →+* referenceRaw.rawAlgebra overlapContext :=
  IsLocalization.Away.lift overlapGenerator overlap_rawGenerator_isUnit

@[simp] private theorem overlapRawToLocalizationAlgHom_rawCoordinate :
    overlapRawToLocalizationAlgHom (rawCoordinate overlapContext) =
      algebraMap AmbientRing (Localization.Away overlapGenerator) coordinate := by
  change (referenceRelationFamily overlapContext).quotientAlgHomOfConfiguration
      overlapConfiguration
      ((referenceRelationFamily overlapContext).quotientMap (rawX overlapContext)) = _
  rw [StructuralRelationFamily.quotientAlgHomOfConfiguration_mk]
  change MvPolynomial.aeval (fun c => match c with
      | .coordinate => algebraMap AmbientRing
          (Localization.Away overlapGenerator) coordinate
      | .leftInverse => overlapLeftInverse
      | .rightInverse => overlapRightInverse)
    (MvPolynomial.X ReferenceRawCoordinate.coordinate) = _
  rw [MvPolynomial.aeval_X]

@[simp] private theorem overlapRawToLocalizationAlgHom_rawLeftInverse :
    overlapRawToLocalizationAlgHom (rawLeftInverseClass overlapContext) =
      overlapLeftInverse := by
  change (referenceRelationFamily overlapContext).quotientAlgHomOfConfiguration
      overlapConfiguration
      ((referenceRelationFamily overlapContext).quotientMap
        (rawLeftInverse overlapContext)) = _
  rw [StructuralRelationFamily.quotientAlgHomOfConfiguration_mk]
  change MvPolynomial.aeval (fun c => match c with
      | .coordinate => algebraMap AmbientRing
          (Localization.Away overlapGenerator) coordinate
      | .leftInverse => overlapLeftInverse
      | .rightInverse => overlapRightInverse)
    (MvPolynomial.X ReferenceRawCoordinate.leftInverse) = _
  rw [MvPolynomial.aeval_X]

@[simp] private theorem overlapRawToLocalizationAlgHom_rawRightInverse :
    overlapRawToLocalizationAlgHom (rawRightInverseClass overlapContext) =
      overlapRightInverse := by
  change (referenceRelationFamily overlapContext).quotientAlgHomOfConfiguration
      overlapConfiguration
      ((referenceRelationFamily overlapContext).quotientMap
        (rawRightInverse overlapContext)) = _
  rw [StructuralRelationFamily.quotientAlgHomOfConfiguration_mk]
  change MvPolynomial.aeval (fun c => match c with
      | .coordinate => algebraMap AmbientRing
          (Localization.Away overlapGenerator) coordinate
      | .leftInverse => overlapLeftInverse
      | .rightInverse => overlapRightInverse)
    (MvPolynomial.X ReferenceRawCoordinate.rightInverse) = _
  rw [MvPolynomial.aeval_X]

private theorem overlapLocalizationToRawRingHom_comp_algebraMap :
    overlapLocalizationToRawRingHom.comp
        (algebraMap AmbientRing (Localization.Away overlapGenerator)) =
      ambientToRawAlgHom overlapContext :=
  IsLocalization.Away.lift_comp _ _

private theorem overlapLocalizationToRawRingHom_leftInverse :
    overlapLocalizationToRawRingHom overlapLeftInverse =
      rawLeftInverseClass overlapContext := by
  apply overlap_rawLeft_isUnit.mul_left_cancel
  calc
    rawCoordinate overlapContext *
        overlapLocalizationToRawRingHom overlapLeftInverse =
      overlapLocalizationToRawRingHom
        (algebraMap AmbientRing (Localization.Away overlapGenerator) leftGenerator *
          overlapLeftInverse) := by
            rw [map_mul]
            congr 1
            have h := RingHom.congr_fun
              overlapLocalizationToRawRingHom_comp_algebraMap coordinate
            change overlapLocalizationToRawRingHom
                (algebraMap AmbientRing
                  (Localization.Away overlapGenerator) coordinate) =
              ambientToRawAlgHom overlapContext coordinate at h
            rw [ambientToRawAlgHom_coordinate] at h
            simpa only [leftGenerator] using h.symm
    _ = 1 := by rw [overlap_left_mul_inverse, map_one]
    _ = rawCoordinate overlapContext * rawLeftInverseClass overlapContext :=
      overlap_rawLeft_mul_inverse.symm

private theorem overlapLocalizationToRawRingHom_rightInverse :
    overlapLocalizationToRawRingHom overlapRightInverse =
      rawRightInverseClass overlapContext := by
  apply overlap_rawRight_isUnit.mul_left_cancel
  calc
    (1 - rawCoordinate overlapContext) *
        overlapLocalizationToRawRingHom overlapRightInverse =
      overlapLocalizationToRawRingHom
        (algebraMap AmbientRing (Localization.Away overlapGenerator) rightGenerator *
          overlapRightInverse) := by
            rw [map_mul]
            congr 1
            have h := RingHom.congr_fun
              overlapLocalizationToRawRingHom_comp_algebraMap coordinate
            change overlapLocalizationToRawRingHom
                (algebraMap AmbientRing
                  (Localization.Away overlapGenerator) coordinate) =
              ambientToRawAlgHom overlapContext coordinate at h
            rw [ambientToRawAlgHom_coordinate] at h
            simpa only [rightGenerator, map_sub, map_one] using
              congrArg (1 - ·) h.symm
    _ = 1 := by rw [overlap_right_mul_inverse, map_one]
    _ = (1 - rawCoordinate overlapContext) * rawRightInverseClass overlapContext :=
      overlap_rawRight_mul_inverse.symm

private theorem overlapRawToLocalization_comp_overlapLocalizationToRaw :
    overlapRawToLocalizationAlgHom.toRingHom.comp overlapLocalizationToRawRingHom =
      RingHom.id (Localization.Away overlapGenerator) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers overlapGenerator)
  rw [RingHom.comp_assoc, overlapLocalizationToRawRingHom_comp_algebraMap]
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [ambientToRawAlgHom]
  · intro i
    cases i
    change overlapRawToLocalizationAlgHom
        (ambientToRawAlgHom overlapContext coordinate) =
      algebraMap AmbientRing (Localization.Away overlapGenerator) coordinate
    rw [ambientToRawAlgHom_coordinate,
      overlapRawToLocalizationAlgHom_rawCoordinate]

private theorem overlapLocalizationToRaw_comp_overlapRawToLocalization :
    overlapLocalizationToRawRingHom.comp overlapRawToLocalizationAlgHom.toRingHom =
      RingHom.id (referenceRaw.rawAlgebra overlapContext) := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro z
    have h := RingHom.congr_fun overlapLocalizationToRawRingHom_comp_algebraMap
      (MvPolynomial.C z : AmbientRing)
    simpa [overlapRawToLocalizationAlgHom,
      StructuralRelationFamily.configurationAlgHom, overlapConfiguration,
      ambientToRawAlgHom] using h
  · intro c
    cases c
    · change overlapLocalizationToRawRingHom
          (overlapRawToLocalizationAlgHom (rawCoordinate overlapContext)) =
        rawCoordinate overlapContext
      rw [overlapRawToLocalizationAlgHom_rawCoordinate]
      have h := RingHom.congr_fun
        overlapLocalizationToRawRingHom_comp_algebraMap coordinate
      calc
        overlapLocalizationToRawRingHom
            (algebraMap AmbientRing
              (Localization.Away overlapGenerator) coordinate) =
          ambientToRawAlgHom overlapContext coordinate := h
        _ = rawCoordinate overlapContext :=
          ambientToRawAlgHom_coordinate overlapContext
    · change overlapLocalizationToRawRingHom
          (overlapRawToLocalizationAlgHom
            (rawLeftInverseClass overlapContext)) =
        rawLeftInverseClass overlapContext
      rw [overlapRawToLocalizationAlgHom_rawLeftInverse]
      exact overlapLocalizationToRawRingHom_leftInverse
    · change overlapLocalizationToRawRingHom
          (overlapRawToLocalizationAlgHom
            (rawRightInverseClass overlapContext)) =
        rawRightInverseClass overlapContext
      rw [overlapRawToLocalizationAlgHom_rawRightInverse]
      exact overlapLocalizationToRawRingHom_rightInverse

private noncomputable def overlapRawRingEquiv :
    referenceRaw.rawAlgebra overlapContext ≃+*
      Localization.Away overlapGenerator :=
  RingEquiv.ofRingHom overlapRawToLocalizationAlgHom.toRingHom
    overlapLocalizationToRawRingHom
    overlapRawToLocalization_comp_overlapLocalizationToRaw
    overlapLocalizationToRaw_comp_overlapRawToLocalization

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def overlapRawAlgebraIso :
    CommRingCat.of (referenceRaw.rawAlgebra overlapContext) ≅
      CommRingCat.of (Localization.Away overlapGenerator) :=
  overlapRawRingEquiv.toCommRingCatIso

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem overlapRawAlgebraIso_coordinate :
    overlapRawAlgebraIso.hom (rawCoordinate overlapContext) =
      algebraMap AmbientRing (Localization.Away overlapGenerator) coordinate := by
  change overlapRawToLocalizationAlgHom (rawCoordinate overlapContext) = _
  exact overlapRawToLocalizationAlgHom_rawCoordinate

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem leftGenerator_dvd_overlap : leftGenerator ∣ overlapGenerator :=
  ⟨rightGenerator, rfl⟩

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem rightGenerator_dvd_overlap : rightGenerator ∣ overlapGenerator :=
  ⟨leftGenerator, mul_comm _ _⟩

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem leftGenerator_isUnit_on_overlap :
    IsUnit
      (algebraMap AmbientRing (Localization.Away overlapGenerator)
        leftGenerator) :=
  IsLocalization.Away.isUnit_of_dvd
    overlapGenerator leftGenerator_dvd_overlap

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem rightGenerator_isUnit_on_overlap :
    IsUnit
      (algebraMap AmbientRing (Localization.Away overlapGenerator)
        rightGenerator) :=
  IsLocalization.Away.isUnit_of_dvd
    overlapGenerator rightGenerator_dvd_overlap

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def leftToOverlapRingHom :
    Localization.Away leftGenerator →+*
      Localization.Away overlapGenerator :=
  IsLocalization.Away.lift leftGenerator leftGenerator_isUnit_on_overlap

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def rightToOverlapRingHom :
    Localization.Away rightGenerator →+*
      Localization.Away overlapGenerator :=
  IsLocalization.Away.lift rightGenerator rightGenerator_isUnit_on_overlap

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem leftToOverlapRingHom_comp_algebraMap :
    leftToOverlapRingHom.comp
        (algebraMap AmbientRing (Localization.Away leftGenerator)) =
      algebraMap AmbientRing (Localization.Away overlapGenerator) :=
  IsLocalization.Away.lift_comp _ _

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem rightToOverlapRingHom_comp_algebraMap :
    rightToOverlapRingHom.comp
        (algebraMap AmbientRing (Localization.Away rightGenerator)) =
      algebraMap AmbientRing (Localization.Away overlapGenerator) :=
  IsLocalization.Away.lift_comp _ _

private theorem baseToLeft_transport :
    leftRawToLocalizationAlgHom.toRingHom.comp
        ((referenceRestrictionStable leftToBase).quotientDesc.comp
          ambientToBaseRawAlgHom.toRingHom) =
      algebraMap AmbientRing (Localization.Away leftGenerator) := by
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [ambientToBaseRawAlgHom]
  · intro i
    cases i
    change leftRawToLocalizationAlgHom
        ((referenceRestrictionStable leftToBase).quotientDesc
          (ambientToBaseRawAlgHom coordinate)) =
      algebraMap AmbientRing (Localization.Away leftGenerator) coordinate
    rw [ambientToBaseRawAlgHom_coordinate,
      show (referenceRestrictionStable leftToBase).quotientDesc
          (rawCoordinate baseContext) = rawCoordinate leftContext by
        simpa only [referenceRaw_restrictionStable] using
          rawCoordinate_restrict (f := leftToBase)]
    exact leftRawToLocalizationAlgHom_rawCoordinate

private theorem baseToRight_transport :
    rightRawToLocalizationAlgHom.toRingHom.comp
        ((referenceRestrictionStable rightToBase).quotientDesc.comp
          ambientToBaseRawAlgHom.toRingHom) =
      algebraMap AmbientRing (Localization.Away rightGenerator) := by
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [ambientToBaseRawAlgHom]
  · intro i
    cases i
    change rightRawToLocalizationAlgHom
        ((referenceRestrictionStable rightToBase).quotientDesc
          (ambientToBaseRawAlgHom coordinate)) =
      algebraMap AmbientRing (Localization.Away rightGenerator) coordinate
    rw [ambientToBaseRawAlgHom_coordinate,
      show (referenceRestrictionStable rightToBase).quotientDesc
          (rawCoordinate baseContext) = rawCoordinate rightContext by
        simpa only [referenceRaw_restrictionStable] using
          rawCoordinate_restrict (f := rightToBase)]
    exact rightRawToLocalizationAlgHom_rawCoordinate

private theorem leftToOverlap_transport :
    overlapRawToLocalizationAlgHom.toRingHom.comp
        ((referenceRestrictionStable overlapToLeft).quotientDesc.comp
          leftLocalizationToRawRingHom) =
      leftToOverlapRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers leftGenerator)
  rw [RingHom.comp_assoc, RingHom.comp_assoc,
    leftLocalizationToRawRingHom_comp_algebraMap,
    leftToOverlapRingHom_comp_algebraMap]
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [ambientToRawAlgHom]
  · intro i
    cases i
    change overlapRawToLocalizationAlgHom
        ((referenceRestrictionStable overlapToLeft).quotientDesc
          (ambientToRawAlgHom leftContext coordinate)) =
      algebraMap AmbientRing (Localization.Away overlapGenerator) coordinate
    rw [ambientToRawAlgHom_coordinate,
      show (referenceRestrictionStable overlapToLeft).quotientDesc
          (rawCoordinate leftContext) = rawCoordinate overlapContext by
        simpa only [referenceRaw_restrictionStable] using
          rawCoordinate_restrict (f := overlapToLeft)]
    exact overlapRawToLocalizationAlgHom_rawCoordinate

private theorem rightToOverlap_transport :
    overlapRawToLocalizationAlgHom.toRingHom.comp
        ((referenceRestrictionStable overlapToRight).quotientDesc.comp
          rightLocalizationToRawRingHom) =
      rightToOverlapRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers rightGenerator)
  rw [RingHom.comp_assoc, RingHom.comp_assoc,
    rightLocalizationToRawRingHom_comp_algebraMap,
    rightToOverlapRingHom_comp_algebraMap]
  apply MvPolynomial.ringHom_ext
  · intro z
    simp [ambientToRawAlgHom]
  · intro i
    cases i
    change overlapRawToLocalizationAlgHom
        ((referenceRestrictionStable overlapToRight).quotientDesc
          (ambientToRawAlgHom rightContext coordinate)) =
      algebraMap AmbientRing (Localization.Away overlapGenerator) coordinate
    rw [ambientToRawAlgHom_coordinate,
      show (referenceRestrictionStable overlapToRight).quotientDesc
          (rawCoordinate rightContext) = rawCoordinate overlapContext by
        simpa only [referenceRaw_restrictionStable] using
          rawCoordinate_restrict (f := overlapToRight)]
    exact overlapRawToLocalizationAlgHom_rawCoordinate

private theorem baseToLeft_transport_apply
    (a : referenceRaw.rawAlgebra baseContext) :
    leftRawToLocalizationAlgHom
        ((referenceRestrictionStable leftToBase).quotientDesc a) =
      algebraMap AmbientRing (Localization.Away leftGenerator)
        (baseRawToAmbientAlgHom a) := by
  have h := RingHom.congr_fun baseToLeft_transport (baseRawToAmbientAlgHom a)
  change leftRawToLocalizationAlgHom
      ((referenceRestrictionStable leftToBase).quotientDesc
        (ambientToBaseRawAlgHom (baseRawToAmbientAlgHom a))) = _ at h
  rw [show ambientToBaseRawAlgHom (baseRawToAmbientAlgHom a) = a by
    exact baseRawRingEquiv.left_inv a] at h
  exact h

private theorem baseToRight_transport_apply
    (a : referenceRaw.rawAlgebra baseContext) :
    rightRawToLocalizationAlgHom
        ((referenceRestrictionStable rightToBase).quotientDesc a) =
      algebraMap AmbientRing (Localization.Away rightGenerator)
        (baseRawToAmbientAlgHom a) := by
  have h := RingHom.congr_fun baseToRight_transport (baseRawToAmbientAlgHom a)
  change rightRawToLocalizationAlgHom
      ((referenceRestrictionStable rightToBase).quotientDesc
        (ambientToBaseRawAlgHom (baseRawToAmbientAlgHom a))) = _ at h
  rw [show ambientToBaseRawAlgHom (baseRawToAmbientAlgHom a) = a by
    exact baseRawRingEquiv.left_inv a] at h
  exact h

private theorem leftToOverlap_transport_apply
    (a : referenceRaw.rawAlgebra leftContext) :
    overlapRawToLocalizationAlgHom
        ((referenceRestrictionStable overlapToLeft).quotientDesc a) =
      leftToOverlapRingHom (leftRawToLocalizationAlgHom a) := by
  have h := RingHom.congr_fun leftToOverlap_transport
    (leftRawToLocalizationAlgHom a)
  change overlapRawToLocalizationAlgHom
      ((referenceRestrictionStable overlapToLeft).quotientDesc
        (leftLocalizationToRawRingHom (leftRawToLocalizationAlgHom a))) = _ at h
  rw [show leftLocalizationToRawRingHom (leftRawToLocalizationAlgHom a) = a by
    exact leftRawRingEquiv.left_inv a] at h
  exact h

private theorem rightToOverlap_transport_apply
    (a : referenceRaw.rawAlgebra rightContext) :
    overlapRawToLocalizationAlgHom
        ((referenceRestrictionStable overlapToRight).quotientDesc a) =
      rightToOverlapRingHom (rightRawToLocalizationAlgHom a) := by
  have h := RingHom.congr_fun rightToOverlap_transport
    (rightRawToLocalizationAlgHom a)
  change overlapRawToLocalizationAlgHom
      ((referenceRestrictionStable overlapToRight).quotientDesc
        (rightLocalizationToRawRingHom (rightRawToLocalizationAlgHom a))) = _ at h
  rw [show rightLocalizationToRawRingHom (rightRawToLocalizationAlgHom a) = a by
    exact rightRawRingEquiv.left_inv a] at h
  exact h

private theorem leftGenerator_ne_rightGenerator :
    leftGenerator ≠ rightGenerator := by
  intro h
  have h' := congrArg
    (MvPolynomial.eval₂Hom (RingHom.id Int) (fun _ : Unit => (0 : Int))) h
  norm_num [leftGenerator, rightGenerator, coordinate] at h'

private theorem awayToAway_self_eq (x : AmbientRing) :
    IsLocalization.Away.awayToAwayRight
        (S := Localization.Away x)
        (P := Localization.Away (x * x)) x x =
      IsLocalization.Away.awayToAwayLeft
        (S := Localization.Away x) x x := by
  apply IsLocalization.ringHom_ext (Submonoid.powers x)
  rw [IsLocalization.Away.awayToAwayRight,
    IsLocalization.Away.awayToAwayLeft]

private theorem awayToAway_left_eq :
    IsLocalization.Away.awayToAwayRight
        (S := Localization.Away leftGenerator)
        (P := Localization.Away (leftGenerator * rightGenerator))
        leftGenerator rightGenerator =
      leftToOverlapRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers leftGenerator)
  rw [IsLocalization.Away.awayToAwayRight,
    IsLocalization.Away.lift_comp,
    leftToOverlapRingHom_comp_algebraMap]
  simp only [overlapGenerator]

private theorem awayToAway_right_eq :
    IsLocalization.Away.awayToAwayLeft
        (S := Localization.Away rightGenerator)
        (P := Localization.Away (leftGenerator * rightGenerator))
        rightGenerator leftGenerator =
      rightToOverlapRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers rightGenerator)
  rw [IsLocalization.Away.awayToAwayLeft,
    IsLocalization.Away.lift_comp,
    rightToOverlapRingHom_comp_algebraMap]
  simp only [overlapGenerator]

private noncomputable def overlapSwapRingHom :
    Localization.Away overlapGenerator →+*
      Localization.Away (rightGenerator * leftGenerator) :=
  IsLocalization.Away.lift overlapGenerator (by
    change IsUnit (algebraMap AmbientRing
      (Localization.Away (rightGenerator * leftGenerator))
        (leftGenerator * rightGenerator))
    rw [mul_comm leftGenerator rightGenerator]
    exact IsLocalization.Away.algebraMap_isUnit _)

private theorem awayToAway_right_swap_eq :
    IsLocalization.Away.awayToAwayRight
        (S := Localization.Away rightGenerator)
        (P := Localization.Away (rightGenerator * leftGenerator))
        rightGenerator leftGenerator =
      overlapSwapRingHom.comp rightToOverlapRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers rightGenerator)
  rw [RingHom.comp_assoc, rightToOverlapRingHom_comp_algebraMap,
    IsLocalization.Away.awayToAwayRight,
    IsLocalization.Away.lift_comp, overlapSwapRingHom,
    IsLocalization.Away.lift_comp]

private theorem awayToAway_left_swap_eq :
    IsLocalization.Away.awayToAwayLeft
        (S := Localization.Away leftGenerator)
        (P := Localization.Away (rightGenerator * leftGenerator))
        leftGenerator rightGenerator =
      overlapSwapRingHom.comp leftToOverlapRingHom := by
  apply IsLocalization.ringHom_ext (Submonoid.powers leftGenerator)
  rw [RingHom.comp_assoc, leftToOverlapRingHom_comp_algebraMap,
    IsLocalization.Away.awayToAwayLeft,
    IsLocalization.Away.lift_comp, overlapSwapRingHom,
    IsLocalization.Away.lift_comp]

private abbrev referenceRawTypePresheaf :
    referenceSite.categoryᵒᵖ ⥤ Type :=
  referenceRaw.toPresheaf ⋙ Under.forget _ ⋙ forget CommRingCat

private theorem referenceRaw_isSheafFor_referenceCover :
    Presieve.IsSheafFor referenceRawTypePresheaf referenceCover.presieve := by
  rw [referenceCover_presieve,
    Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible]
  constructor
  · intro a b hab
    apply baseRawRingEquiv.injective
    refine Localization.algebraMap_injective_of_span_eq_top
      (Set.range coverGenerator) coverGenerator_span_eq_top ?_
    funext z
    rcases z with ⟨z, i, rfl⟩
    cases i
    · have h := congrFun (congrArg Subtype.val hab)
          AAT.AG.FiniteModel.TwoPatchCoverIndex.left
      change (referenceRaw.restrictionStable leftToBase).quotientDesc a =
        (referenceRaw.restrictionStable leftToBase).quotientDesc b at h
      simp only [referenceRaw_restrictionStable] at h
      have h' := congrArg leftRawToLocalizationAlgHom h
      change algebraMap AmbientRing (Localization.Away leftGenerator)
          (baseRawRingEquiv a) =
        algebraMap AmbientRing (Localization.Away leftGenerator)
          (baseRawRingEquiv b)
      calc
        _ = leftRawToLocalizationAlgHom
              ((referenceRestrictionStable leftToBase).quotientDesc a) :=
          (baseToLeft_transport_apply a).symm
        _ = leftRawToLocalizationAlgHom
              ((referenceRestrictionStable leftToBase).quotientDesc b) := h'
        _ = _ := baseToLeft_transport_apply b
    · have h := congrFun (congrArg Subtype.val hab)
          AAT.AG.FiniteModel.TwoPatchCoverIndex.right
      change (referenceRaw.restrictionStable rightToBase).quotientDesc a =
        (referenceRaw.restrictionStable rightToBase).quotientDesc b at h
      simp only [referenceRaw_restrictionStable] at h
      have h' := congrArg rightRawToLocalizationAlgHom h
      change algebraMap AmbientRing (Localization.Away rightGenerator)
          (baseRawRingEquiv a) =
        algebraMap AmbientRing (Localization.Away rightGenerator)
          (baseRawRingEquiv b)
      calc
        _ = rightRawToLocalizationAlgHom
              ((referenceRestrictionStable rightToBase).quotientDesc a) :=
          (baseToRight_transport_apply a).symm
        _ = rightRawToLocalizationAlgHom
              ((referenceRestrictionStable rightToBase).quotientDesc b) := h'
        _ = _ := baseToRight_transport_apply b
  · rintro ⟨s, hs⟩
    let l : Localization.Away leftGenerator :=
      leftRawToLocalizationAlgHom
        (s AAT.AG.FiniteModel.TwoPatchCoverIndex.left)
    let r : Localization.Away rightGenerator :=
      rightRawToLocalizationAlgHom
        (s AAT.AG.FiniteModel.TwoPatchCoverIndex.right)
    have hlr : leftToOverlapRingHom l = rightToOverlapRingHom r := by
      have hcomp := hs
        AAT.AG.FiniteModel.TwoPatchCoverIndex.left
        AAT.AG.FiniteModel.TwoPatchCoverIndex.right
        overlapContext overlapToLeft overlapToRight (Subsingleton.elim _ _)
      change (referenceRaw.restrictionStable overlapToLeft).quotientDesc
          (s AAT.AG.FiniteModel.TwoPatchCoverIndex.left) =
        (referenceRaw.restrictionStable overlapToRight).quotientDesc
          (s AAT.AG.FiniteModel.TwoPatchCoverIndex.right) at hcomp
      simp only [referenceRaw_restrictionStable] at hcomp
      have hcomp' := congrArg overlapRawToLocalizationAlgHom hcomp
      calc
        leftToOverlapRingHom l =
            overlapRawToLocalizationAlgHom
              ((referenceRestrictionStable overlapToLeft).quotientDesc
                (s AAT.AG.FiniteModel.TwoPatchCoverIndex.left)) :=
          (leftToOverlap_transport_apply _).symm
        _ = overlapRawToLocalizationAlgHom
              ((referenceRestrictionStable overlapToRight).quotientDesc
                (s AAT.AG.FiniteModel.TwoPatchCoverIndex.right)) := hcomp'
        _ = rightToOverlapRingHom r := rightToOverlap_transport_apply _
    let patchSection : ∀ z : Set.range coverGenerator,
        Localization.Away z.1 := fun z =>
      if hz : z.1 = leftGenerator then
        hz ▸ l
      else
        have hr : z.1 = rightGenerator := by
          rcases z.2 with ⟨i, hi⟩
          cases i
          · exact False.elim (hz hi.symm)
          · exact hi.symm
        hr ▸ r
    have hlocal : ∀ a b : Set.range coverGenerator,
        IsLocalization.Away.awayToAwayRight
            (P := Localization.Away (a.1 * b.1)) a.1 b.1 (patchSection a) =
          IsLocalization.Away.awayToAwayLeft b.1 a.1 (patchSection b) := by
      have hmixed :
          IsLocalization.Away.awayToAwayRight
              (S := Localization.Away leftGenerator)
              (P := Localization.Away (leftGenerator * rightGenerator))
              leftGenerator rightGenerator l =
            IsLocalization.Away.awayToAwayLeft
              (S := Localization.Away rightGenerator)
              rightGenerator leftGenerator r := by
        rw [awayToAway_left_eq, awayToAway_right_eq]
        exact hlr
      intro a b
      rcases a with ⟨a, ia, rfl⟩
      rcases b with ⟨b, ib, rfl⟩
      cases ia <;> cases ib
      · simp only [coverGenerator_false, patchSection, dif_pos rfl]
        exact RingHom.congr_fun (awayToAway_self_eq leftGenerator) l
      · simp only [coverGenerator_false, coverGenerator_true,
          patchSection, dif_pos rfl,
          dif_neg leftGenerator_ne_rightGenerator.symm]
        exact hmixed
      · simp only [coverGenerator_false, coverGenerator_true,
          patchSection, dif_pos rfl,
          dif_neg leftGenerator_ne_rightGenerator.symm]
        rw [awayToAway_right_swap_eq, awayToAway_left_swap_eq]
        exact congrArg overlapSwapRingHom hlr.symm
      · simp only [coverGenerator_true, patchSection,
          dif_neg leftGenerator_ne_rightGenerator.symm]
        exact RingHom.congr_fun (awayToAway_self_eq rightGenerator) r
    obtain ⟨p, hp, _⟩ :=
      Localization.existsUnique_algebraMap_eq_of_span_eq_top
        (Set.range coverGenerator) coverGenerator_span_eq_top patchSection hlocal
    refine ⟨ambientToBaseRawAlgHom p, ?_⟩
    apply Subtype.ext
    funext i
    cases i
    · change (referenceRaw.restrictionStable leftToBase).quotientDesc
          (ambientToBaseRawAlgHom p) =
        s AAT.AG.FiniteModel.TwoPatchCoverIndex.left
      simp only [referenceRaw_restrictionStable]
      apply leftRawRingEquiv.injective
      change leftRawToLocalizationAlgHom
          ((referenceRestrictionStable leftToBase).quotientDesc
            (ambientToBaseRawAlgHom p)) =
        leftRawToLocalizationAlgHom
          (s AAT.AG.FiniteModel.TwoPatchCoverIndex.left)
      rw [baseToLeft_transport_apply]
      rw [show baseRawToAmbientAlgHom (ambientToBaseRawAlgHom p) = p by
        exact baseRawRingEquiv.right_inv p]
      change algebraMap AmbientRing (Localization.Away leftGenerator) p = l
      have h := hp ⟨leftGenerator, ⟨false, rfl⟩⟩
      simpa [patchSection, l] using h
    · change (referenceRaw.restrictionStable rightToBase).quotientDesc
          (ambientToBaseRawAlgHom p) =
        s AAT.AG.FiniteModel.TwoPatchCoverIndex.right
      simp only [referenceRaw_restrictionStable]
      apply rightRawRingEquiv.injective
      change rightRawToLocalizationAlgHom
          ((referenceRestrictionStable rightToBase).quotientDesc
            (ambientToBaseRawAlgHom p)) =
        rightRawToLocalizationAlgHom
          (s AAT.AG.FiniteModel.TwoPatchCoverIndex.right)
      rw [baseToRight_transport_apply]
      rw [show baseRawToAmbientAlgHom (ambientToBaseRawAlgHom p) = p by
        exact baseRawRingEquiv.right_inv p]
      change algebraMap AmbientRing (Localization.Away rightGenerator) p = r
      have h := hp ⟨rightGenerator, ⟨true, rfl⟩⟩
      have hne : rightGenerator ≠ leftGenerator :=
        leftGenerator_ne_rightGenerator.symm
      simpa only [patchSection, dif_neg hne, r] using h

private theorem selectedTarget_of_le
    (i : AAT.AG.FiniteModel.TwoPatchContextIndex)
    (W : Site.ArchCtx AAT.AG.FiniteModel.corePackage.object)
    (h : ReferenceLe (AAT.AG.FiniteModel.twoPatchContext i) W) :
    ∃ j : AAT.AG.FiniteModel.TwoPatchContextIndex,
      W = AAT.AG.FiniteModel.twoPatchContext j ∧
        AAT.AG.FiniteModel.twoPatchContextIndexLe i j := by
  rcases h with hEq | ⟨i', j, hi', hW, hij⟩
  · exact ⟨i, hEq.symm,
      AAT.AG.FiniteModel.twoPatchContextIndexLe_refl i⟩
  · have hii : i' = i := twoPatchContext_injective hi'.symm
    subst i'
    exact ⟨j, hW, hij⟩

private theorem commonSelectedUpper_eq_base
    (W : Site.ArchCtx AAT.AG.FiniteModel.corePackage.object)
    (hl : ReferenceLe
      (AAT.AG.FiniteModel.twoPatchContext
        AAT.AG.FiniteModel.TwoPatchContextIndex.left) W)
    (hr : ReferenceLe
      (AAT.AG.FiniteModel.twoPatchContext
        AAT.AG.FiniteModel.TwoPatchContextIndex.right) W) :
    W = AAT.AG.FiniteModel.twoPatchContext
      AAT.AG.FiniteModel.TwoPatchContextIndex.base := by
  obtain ⟨i, hWi, hli⟩ := selectedTarget_of_le _ W hl
  obtain ⟨j, hWj, hrj⟩ := selectedTarget_of_le _ W hr
  have hij : i = j := twoPatchContext_injective (hWi.symm.trans hWj)
  subst j
  cases i <;>
    simp [AAT.AG.FiniteModel.twoPatchContextIndexLe] at hli hrj ⊢
  exact hWi

private theorem admissibleCover_base_eq
    {X : referenceSite.category}
    (F : Site.AATCoverageFamily referenceSite.requirements
      referenceSite.overlap X) :
    X = baseContext := by
  obtain ⟨iL, hiL⟩ := F.admissible.atomSupportCoverage
    AAT.AG.FiniteModel.FiniteAtom.componentA (Or.inl rfl)
  obtain ⟨iR, hiR⟩ := F.admissible.atomSupportCoverage
    AAT.AG.FiniteModel.FiniteAtom.componentB (Or.inr rfl)
  have hpatchL : F.patch iL = AAT.AG.FiniteModel.twoPatchContext
      AAT.AG.FiniteModel.TwoPatchContextIndex.left := by
    simpa [referenceSite, referenceSelectedGeometryReading,
      referenceCoverageRequirements,
      AAT.AG.FiniteModel.twoPatchCoverageRequirements,
      AAT.AG.FiniteModel.twoPatchSupportVisibleOn] using hiL
  have hpatchR : F.patch iR = AAT.AG.FiniteModel.twoPatchContext
      AAT.AG.FiniteModel.TwoPatchContextIndex.right := by
    simpa [referenceSite, referenceSelectedGeometryReading,
      referenceCoverageRequirements,
      AAT.AG.FiniteModel.twoPatchCoverageRequirements,
      AAT.AG.FiniteModel.twoPatchSupportVisibleOn] using hiR
  have hl : ReferenceLe
      (AAT.AG.FiniteModel.twoPatchContext
        AAT.AG.FiniteModel.TwoPatchContextIndex.left) X.ctx := by
    rw [← hpatchL]
    exact F.inclusion iL
  have hr : ReferenceLe
      (AAT.AG.FiniteModel.twoPatchContext
        AAT.AG.FiniteModel.TwoPatchContextIndex.right) X.ctx := by
    rw [← hpatchR]
    exact F.inclusion iR
  exact contextObject_ext (commonSelectedUpper_eq_base X.ctx hl hr)

private theorem referenceCover_generate_le_admissible
    (F : Site.AATCoverageFamily referenceSite.requirements
      referenceSite.overlap baseContext) :
    Sieve.generate referenceCover.presieve ≤ Sieve.generate F.presieve := by
  apply Sieve.generate_mono
  obtain ⟨iL, hiL⟩ := F.admissible.atomSupportCoverage
    AAT.AG.FiniteModel.FiniteAtom.componentA (Or.inl rfl)
  obtain ⟨iR, hiR⟩ := F.admissible.atomSupportCoverage
    AAT.AG.FiniteModel.FiniteAtom.componentB (Or.inr rfl)
  have hpatchL : F.patch iL = AAT.AG.FiniteModel.twoPatchContext
      AAT.AG.FiniteModel.TwoPatchContextIndex.left := by
    simpa [referenceSite, referenceSelectedGeometryReading,
      referenceCoverageRequirements,
      AAT.AG.FiniteModel.twoPatchCoverageRequirements,
      AAT.AG.FiniteModel.twoPatchSupportVisibleOn] using hiL
  have hpatchR : F.patch iR = AAT.AG.FiniteModel.twoPatchContext
      AAT.AG.FiniteModel.TwoPatchContextIndex.right := by
    simpa [referenceSite, referenceSelectedGeometryReading,
      referenceCoverageRequirements,
      AAT.AG.FiniteModel.twoPatchCoverageRequirements,
      AAT.AG.FiniteModel.twoPatchSupportVisibleOn] using hiR
  rw [referenceCover_presieve]
  intro Y f hf
  rcases hf with ⟨i⟩
  cases i
  · apply Presieve.ofArrows.mk' iL
      (contextObject_ext hpatchL.symm)
    apply Subsingleton.elim
  · apply Presieve.ofArrows.mk' iR
      (contextObject_ext hpatchR.symm)
    apply Subsingleton.elim

private theorem source_eq_base_or_referenceCover_mem
    {Y : referenceSite.category} (f : Y ⟶ baseContext) :
    Y = baseContext ∨ Sieve.generate referenceCover.presieve f := by
  have hle : ReferenceLe Y.ctx baseContext.ctx := CategoryTheory.leOfHom f
  rcases hle with hctx | ⟨i, j, hYi, hBj, hij⟩
  · exact Or.inl (contextObject_ext hctx)
  · have hj : j = AAT.AG.FiniteModel.TwoPatchContextIndex.base :=
      twoPatchContext_injective hBj.symm
    subst j
    have hY : Y = context i := contextObject_eq hYi
    subst Y
    cases i
    · right
      have hmem : referenceCover.presieve leftToBase := by
        rw [referenceCover_presieve]
        exact Presieve.ofArrows.mk
          AAT.AG.FiniteModel.TwoPatchCoverIndex.left
      have hleft : Sieve.generate referenceCover.presieve leftToBase :=
        (Sieve.le_generate referenceCover.presieve) _ hmem
      have hover := (Sieve.generate referenceCover.presieve).downward_closed
        hleft overlapToLeft
      simpa using hover
    · right
      have hmem : referenceCover.presieve leftToBase := by
        rw [referenceCover_presieve]
        exact Presieve.ofArrows.mk
          AAT.AG.FiniteModel.TwoPatchCoverIndex.left
      have hleft : Sieve.generate referenceCover.presieve leftToBase :=
        (Sieve.le_generate referenceCover.presieve) _ hmem
      simpa using hleft
    · right
      have hmem : referenceCover.presieve rightToBase := by
        rw [referenceCover_presieve]
        exact Presieve.ofArrows.mk
          AAT.AG.FiniteModel.TwoPatchCoverIndex.right
      have hright : Sieve.generate referenceCover.presieve rightToBase :=
        (Sieve.le_generate referenceCover.presieve) _ hmem
      simpa using hright
    · exact Or.inl rfl

private theorem referenceRaw_isSheafFor_referenceCover_pullback
    {Y : referenceSite.category} (f : Y ⟶ baseContext) :
    Presieve.IsSheafFor referenceRawTypePresheaf
      (Sieve.pullback f (Sieve.generate referenceCover.presieve)).arrows := by
  rcases source_eq_base_or_referenceCover_mem f with hY | hf
  · subst Y
    have hfId : f = 𝟙 baseContext := Subsingleton.elim _ _
    subst f
    simpa using
      (Presieve.isSheafFor_iff_generate referenceCover.presieve).mp
        referenceRaw_isSheafFor_referenceCover
  · rw [Sieve.pullback_eq_top_of_mem _ hf]
    exact Presieve.isSheafFor_top _

private theorem referenceRawType_isSheaf :
    Presieve.IsSheaf referenceSite.topology referenceRawTypePresheaf := by
  rw [Site.AATSite.topology, Site.AATGrothendieckTopology,
    Precoverage.isSheaf_toGrothendieck_iff]
  intro X Y f R hR
  rcases hR with ⟨F, rfl⟩
  have hX := admissibleCover_base_eq F
  subst X
  apply Presieve.isSheafFor_subsieve referenceRawTypePresheaf
    (S := Sieve.pullback f
      (Sieve.generate referenceCover.presieve))
    (R := (Sieve.pullback f
      (Sieve.generate F.presieve)).arrows)
  · intro Z g hg
    exact (Sieve.pullback_monotone f
      (referenceCover_generate_le_admissible F)) g hg
  · intro Z g
    simpa [Sieve.pullback_comp] using
      referenceRaw_isSheafFor_referenceCover_pullback (g ≫ f)

/--
SD0 main fixture theorem for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem referenceRaw_isSheaf :
    Presheaf.IsSheaf referenceSite.topology referenceRaw.toPresheaf := by
  intro E X R hR
  have hType := referenceRawType_isSheaf R hR
  intro x hx
  let elemFamily (e : E) :
      Presieve.FamilyOfElements referenceRawTypePresheaf R :=
    fun _ f hf => (x f hf).right e
  have elemCompatible (e : E) : (elemFamily e).Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ w
    have h := congrArg (fun q => q.right e)
      (hx g₁ g₂ hf₁ hf₂ w)
    simpa [elemFamily, referenceRawTypePresheaf] using h
  let glued (e : E) : (referenceRaw.toPresheaf.obj (op X)).right :=
    hType.amalgamate (elemFamily e) (elemCompatible e)
  have glued_local (e : E) {Y : referenceSite.category}
      (f : Y ⟶ X) (hf : R f) :
      (referenceRaw.toPresheaf.map f.op).right (glued e) =
        (x f hf).right e := by
    exact hType.valid_glue (elemCompatible e) f hf
  have glued_ext {a b : (referenceRaw.toPresheaf.obj (op X)).right}
      (h : ∀ (Y : referenceSite.category) (f : Y ⟶ X) (hf : R f),
        (referenceRaw.toPresheaf.map f.op).right a =
          (referenceRaw.toPresheaf.map f.op).right b) : a = b := by
    apply hType.isSeparatedFor.ext
    intro Y f hf
    exact h Y f hf
  let gluedRingHom : E.right →+*
      (referenceRaw.toPresheaf.obj (op X)).right :=
    { toFun := glued
      map_one' := by
        apply glued_ext
        intro Y f hf
        calc
          (referenceRaw.toPresheaf.map f.op).right (glued 1) =
              (x f hf).right 1 := glued_local 1 f hf
          _ = 1 := map_one _
          _ = (referenceRaw.toPresheaf.map f.op).right 1 := (map_one _).symm
      map_mul' := by
        intro a b
        apply glued_ext
        intro Y f hf
        calc
          (referenceRaw.toPresheaf.map f.op).right (glued (a * b)) =
              (x f hf).right (a * b) := glued_local (a * b) f hf
          _ = (x f hf).right a * (x f hf).right b := map_mul _ _ _
          _ = (referenceRaw.toPresheaf.map f.op).right (glued a) *
              (referenceRaw.toPresheaf.map f.op).right (glued b) := by
            rw [glued_local a f hf, glued_local b f hf]
          _ = (referenceRaw.toPresheaf.map f.op).right (glued a * glued b) :=
            (map_mul _ _ _).symm
      map_zero' := by
        apply glued_ext
        intro Y f hf
        calc
          (referenceRaw.toPresheaf.map f.op).right (glued 0) =
              (x f hf).right 0 := glued_local 0 f hf
          _ = 0 := map_zero _
          _ = (referenceRaw.toPresheaf.map f.op).right 0 := (map_zero _).symm
      map_add' := by
        intro a b
        apply glued_ext
        intro Y f hf
        calc
          (referenceRaw.toPresheaf.map f.op).right (glued (a + b)) =
              (x f hf).right (a + b) := glued_local (a + b) f hf
          _ = (x f hf).right a + (x f hf).right b := map_add _ _ _
          _ = (referenceRaw.toPresheaf.map f.op).right (glued a) +
              (referenceRaw.toPresheaf.map f.op).right (glued b) := by
            rw [glued_local a f hf, glued_local b f hf]
          _ = (referenceRaw.toPresheaf.map f.op).right (glued a + glued b) :=
            (map_add _ _ _).symm }
  let gluedHom : E ⟶ referenceRaw.toPresheaf.obj (op X) :=
    Under.homMk (CommRingCat.ofHom gluedRingHom) (by
      ext a
      change glued (E.hom a) =
        (referenceRaw.toPresheaf.obj (op X)).hom a
      apply glued_ext
      intro Y f hf
      have hxw := Under.w (x f hf)
      have hpw := Under.w (referenceRaw.toPresheaf.map f.op)
      calc
        (referenceRaw.toPresheaf.map f.op).right (glued (E.hom a)) =
            (x f hf).right (E.hom a) := glued_local (E.hom a) f hf
        _ = (referenceRaw.toPresheaf.obj (op Y)).hom a := by
          simpa only [CommRingCat.comp_apply] using
            congrArg (fun q => q a) hxw
        _ = (referenceRaw.toPresheaf.map f.op).right
            ((referenceRaw.toPresheaf.obj (op X)).hom a) := by
          simpa only [CommRingCat.comp_apply] using
            (congrArg (fun q => q a) hpw).symm)
  refine ⟨gluedHom, ?_, ?_⟩
  · intro Y f hf
    apply Under.UnderMorphism.ext
    apply ConcreteCategory.hom_ext
    intro e
    simpa only [gluedHom, gluedRingHom, CommRingCat.comp_apply] using
      glued_local e f hf
  · intro other hother
    apply Under.UnderMorphism.ext
    apply ConcreteCategory.hom_ext
    intro e
    apply glued_ext
    intro Y f hf
    have h := congrArg (fun q => q.right e) (hother f hf)
    have hotherLocal : (referenceRaw.toPresheaf.map f.op).right (other.right e) =
        (x f hf).right e := by
      simpa only [CommRingCat.comp_apply] using h
    exact hotherLocal.trans (glued_local e f hf).symm

/--
SD0 constructor-provenance or no-unfold API lemma for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem canonical_component_isIso (W : referenceSite.category) :
    IsIso (referenceRaw.toRingedSite.canonical.app (op W)) := by
  haveI : IsIso (CategoryTheory.toSheafify referenceSite.topology
      referenceRaw.toPresheaf) :=
    CategoryTheory.isIso_toSheafify
      (J := referenceSite.topology) referenceRaw_isSheaf
  change IsIso ((CategoryTheory.toSheafify referenceSite.topology
    referenceRaw.toPresheaf).app (op W))
  infer_instance

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def baseSectionRingIso :
    SheafifiedSectionRing referenceRaw baseContext ≅
      CommRingCat.of AmbientRing := by
  letI := canonical_component_isIso baseContext
  exact (asIso
    (referenceRaw.toRingedSite.canonical.app (op baseContext)).right).symm ≪≫
      baseRawAlgebraIso

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def leftSectionRingIso :
    SheafifiedSectionRing referenceRaw leftContext ≅
      CommRingCat.of (Localization.Away leftGenerator) := by
  letI := canonical_component_isIso leftContext
  exact (asIso
    (referenceRaw.toRingedSite.canonical.app (op leftContext)).right).symm ≪≫
      leftRawAlgebraIso

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def rightSectionRingIso :
    SheafifiedSectionRing referenceRaw rightContext ≅
      CommRingCat.of (Localization.Away rightGenerator) := by
  letI := canonical_component_isIso rightContext
  exact (asIso
    (referenceRaw.toRingedSite.canonical.app (op rightContext)).right).symm ≪≫
      rightRawAlgebraIso

/--
SD0 fixture data declaration for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def overlapSectionRingIso :
    SheafifiedSectionRing referenceRaw overlapContext ≅
      CommRingCat.of (Localization.Away overlapGenerator) := by
  letI := canonical_component_isIso overlapContext
  exact (asIso
    (referenceRaw.toRingedSite.canonical.app (op overlapContext)).right).symm ≪≫
      overlapRawAlgebraIso

/--
SD0 main fixture theorem for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem left_restriction_is_localization :
    baseSectionRingIso.inv ≫
        sheafifiedRestriction referenceRaw leftToBase ≫
        leftSectionRingIso.hom =
      CommRingCat.ofHom
        (algebraMap AmbientRing (Localization.Away leftGenerator)) := by
  letI := canonical_component_isIso baseContext
  letI := canonical_component_isIso leftContext
  rw [baseSectionRingIso, leftSectionRingIso, Iso.trans_inv,
    Iso.trans_hom]
  have hnat :
      (referenceRaw.toRingedSite.canonical.app (op baseContext)).right ≫
          sheafifiedRestriction referenceRaw leftToBase =
        CommRingCat.ofHom
            (referenceRaw.restrictionStable leftToBase).quotientDesc ≫
          (referenceRaw.toRingedSite.canonical.app (op leftContext)).right := by
    apply ConcreteCategory.hom_ext
    intro x
    have hn :=
      referenceRaw.toRingedSite.canonical.naturality leftToBase.op
    have ha := congrArg (fun q => q.right x) hn
    simpa only [CommRingCat.comp_apply,
      RawAmbientRestrictionSystem.toRingedSite_raw,
      sheafifiedRestriction] using ha.symm
  rw [show (asIso
      (referenceRaw.toRingedSite.canonical.app (op baseContext)).right).symm.inv =
        (referenceRaw.toRingedSite.canonical.app (op baseContext)).right by
      simpa only [Iso.symm_inv, asIso_hom]]
  slice_lhs 2 3 => rw [hnat]
  rw [show (asIso
      (referenceRaw.toRingedSite.canonical.app (op leftContext)).right).symm.hom =
        inv (referenceRaw.toRingedSite.canonical.app (op leftContext)).right by
      simpa only [Iso.symm_hom, asIso_inv]]
  simp only [Category.assoc]
  simp only [IsIso.hom_inv_id_assoc]
  rw [referenceRaw_restrictionStable]
  apply ConcreteCategory.hom_ext
  intro a
  exact RingHom.congr_fun baseToLeft_transport a

/--
SD0 main fixture theorem for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem right_restriction_is_localization :
    baseSectionRingIso.inv ≫
        sheafifiedRestriction referenceRaw rightToBase ≫
        rightSectionRingIso.hom =
      CommRingCat.ofHom
        (algebraMap AmbientRing (Localization.Away rightGenerator)) := by
  letI := canonical_component_isIso baseContext
  letI := canonical_component_isIso rightContext
  rw [baseSectionRingIso, rightSectionRingIso, Iso.trans_inv,
    Iso.trans_hom]
  have hnat :
      (referenceRaw.toRingedSite.canonical.app (op baseContext)).right ≫
          sheafifiedRestriction referenceRaw rightToBase =
        CommRingCat.ofHom
            (referenceRaw.restrictionStable rightToBase).quotientDesc ≫
          (referenceRaw.toRingedSite.canonical.app (op rightContext)).right := by
    apply ConcreteCategory.hom_ext
    intro x
    have hn :=
      referenceRaw.toRingedSite.canonical.naturality rightToBase.op
    have ha := congrArg (fun q => q.right x) hn
    simpa only [CommRingCat.comp_apply,
      RawAmbientRestrictionSystem.toRingedSite_raw,
      sheafifiedRestriction] using ha.symm
  rw [show (asIso
      (referenceRaw.toRingedSite.canonical.app (op baseContext)).right).symm.inv =
        (referenceRaw.toRingedSite.canonical.app (op baseContext)).right by
      simpa only [Iso.symm_inv, asIso_hom]]
  slice_lhs 2 3 => rw [hnat]
  rw [show (asIso
      (referenceRaw.toRingedSite.canonical.app (op rightContext)).right).symm.hom =
        inv (referenceRaw.toRingedSite.canonical.app (op rightContext)).right by
      simpa only [Iso.symm_hom, asIso_inv]]
  simp only [Category.assoc]
  simp only [IsIso.hom_inv_id_assoc]
  rw [referenceRaw_restrictionStable]
  apply ConcreteCategory.hom_ext
  intro a
  exact RingHom.congr_fun baseToRight_transport a

/--
SD0 main fixture theorem for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem overlap_left_restriction_is_localization :
    leftSectionRingIso.inv ≫
        sheafifiedRestriction referenceRaw overlapToLeft ≫
        overlapSectionRingIso.hom =
      CommRingCat.ofHom leftToOverlapRingHom := by
  letI := canonical_component_isIso leftContext
  letI := canonical_component_isIso overlapContext
  rw [leftSectionRingIso, overlapSectionRingIso, Iso.trans_inv,
    Iso.trans_hom]
  have hnat :
      (referenceRaw.toRingedSite.canonical.app (op leftContext)).right ≫
          sheafifiedRestriction referenceRaw overlapToLeft =
        CommRingCat.ofHom
            (referenceRaw.restrictionStable overlapToLeft).quotientDesc ≫
          (referenceRaw.toRingedSite.canonical.app (op overlapContext)).right := by
    apply ConcreteCategory.hom_ext
    intro x
    have hn :=
      referenceRaw.toRingedSite.canonical.naturality overlapToLeft.op
    have ha := congrArg (fun q => q.right x) hn
    simpa only [CommRingCat.comp_apply,
      RawAmbientRestrictionSystem.toRingedSite_raw,
      sheafifiedRestriction] using ha.symm
  rw [show (asIso
      (referenceRaw.toRingedSite.canonical.app (op leftContext)).right).symm.inv =
        (referenceRaw.toRingedSite.canonical.app (op leftContext)).right by
      simpa only [Iso.symm_inv, asIso_hom]]
  slice_lhs 2 3 => rw [hnat]
  rw [show (asIso
      (referenceRaw.toRingedSite.canonical.app (op overlapContext)).right).symm.hom =
        inv (referenceRaw.toRingedSite.canonical.app (op overlapContext)).right by
      simpa only [Iso.symm_hom, asIso_inv]]
  simp only [Category.assoc]
  simp only [IsIso.hom_inv_id_assoc]
  rw [referenceRaw_restrictionStable]
  apply ConcreteCategory.hom_ext
  intro a
  exact RingHom.congr_fun leftToOverlap_transport a

/--
SD0 main fixture theorem for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem overlap_right_restriction_is_localization :
    rightSectionRingIso.inv ≫
        sheafifiedRestriction referenceRaw overlapToRight ≫
        overlapSectionRingIso.hom =
      CommRingCat.ofHom rightToOverlapRingHom := by
  letI := canonical_component_isIso rightContext
  letI := canonical_component_isIso overlapContext
  rw [rightSectionRingIso, overlapSectionRingIso, Iso.trans_inv,
    Iso.trans_hom]
  have hnat :
      (referenceRaw.toRingedSite.canonical.app (op rightContext)).right ≫
          sheafifiedRestriction referenceRaw overlapToRight =
        CommRingCat.ofHom
            (referenceRaw.restrictionStable overlapToRight).quotientDesc ≫
          (referenceRaw.toRingedSite.canonical.app (op overlapContext)).right := by
    apply ConcreteCategory.hom_ext
    intro x
    have hn :=
      referenceRaw.toRingedSite.canonical.naturality overlapToRight.op
    have ha := congrArg (fun q => q.right x) hn
    simpa only [CommRingCat.comp_apply,
      RawAmbientRestrictionSystem.toRingedSite_raw,
      sheafifiedRestriction] using ha.symm
  rw [show (asIso
      (referenceRaw.toRingedSite.canonical.app (op rightContext)).right).symm.inv =
        (referenceRaw.toRingedSite.canonical.app (op rightContext)).right by
      simpa only [Iso.symm_inv, asIso_hom]]
  slice_lhs 2 3 => rw [hnat]
  rw [show (asIso
      (referenceRaw.toRingedSite.canonical.app (op overlapContext)).right).symm.hom =
        inv (referenceRaw.toRingedSite.canonical.app (op overlapContext)).right by
      simpa only [Iso.symm_hom, asIso_inv]]
  simp only [Category.assoc]
  simp only [IsIso.hom_inv_id_assoc]
  rw [referenceRaw_restrictionStable]
  apply ConcreteCategory.hom_ext
  intro a
  exact RingHom.congr_fun rightToOverlap_transport a

private theorem left_algebraMap_not_surjective :
    ¬ Function.Surjective
      (algebraMap AmbientRing (Localization.Away leftGenerator)) := by
  intro hsurj
  obtain ⟨p, hp⟩ := hsurj (IsLocalization.Away.invSelf leftGenerator)
  have heq : algebraMap AmbientRing (Localization.Away leftGenerator)
      (leftGenerator * p) = algebraMap AmbientRing
        (Localization.Away leftGenerator) 1 := by
    rw [map_mul, hp, IsLocalization.Away.mul_invSelf, map_one]
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq leftGenerator heq
  have hgen : leftGenerator ≠ 0 := by
    simpa [leftGenerator, coordinate] using
      (MvPolynomial.X_ne_zero (R := Int) ())
  have hmul : leftGenerator * p = 1 :=
    mul_left_cancel₀ (pow_ne_zero n hgen) (by simpa [mul_assoc] using hn)
  have hev := congrArg
    (MvPolynomial.eval₂Hom (RingHom.id Int) (fun _ : Unit => (0 : Int))) hmul
  norm_num [leftGenerator, coordinate] at hev

private theorem rightGenerator_ne_zero : rightGenerator ≠ 0 := by
  intro h
  have h' := congrArg
    (MvPolynomial.eval₂Hom (RingHom.id Int) (fun _ : Unit => (0 : Int))) h
  norm_num [rightGenerator, coordinate] at h'

private theorem right_algebraMap_not_surjective :
    ¬ Function.Surjective
      (algebraMap AmbientRing (Localization.Away rightGenerator)) := by
  intro hsurj
  obtain ⟨p, hp⟩ := hsurj (IsLocalization.Away.invSelf rightGenerator)
  have heq : algebraMap AmbientRing (Localization.Away rightGenerator)
      (rightGenerator * p) = algebraMap AmbientRing
        (Localization.Away rightGenerator) 1 := by
    rw [map_mul, hp, IsLocalization.Away.mul_invSelf, map_one]
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq rightGenerator heq
  have hmul : rightGenerator * p = 1 :=
    mul_left_cancel₀ (pow_ne_zero n rightGenerator_ne_zero)
      (by simpa [mul_assoc] using hn)
  have hev := congrArg
    (MvPolynomial.eval₂Hom (RingHom.id Int) (fun _ : Unit => (1 : Int))) hmul
  norm_num [rightGenerator, coordinate] at hev

/--
SD0 main fixture theorem for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem left_restriction_not_isIso :
    ¬ IsIso (sheafifiedRestriction referenceRaw leftToBase) := by
  intro h
  letI := h
  have hIso : IsIso
      (baseSectionRingIso.inv ≫
        sheafifiedRestriction referenceRaw leftToBase ≫
        leftSectionRingIso.hom) := inferInstance
  have hAlg : IsIso (CommRingCat.ofHom
      (algebraMap AmbientRing (Localization.Away leftGenerator))) := by
    rw [← left_restriction_is_localization]
    exact hIso
  exact left_algebraMap_not_surjective
    ((ConcreteCategory.isIso_iff_bijective _).mp hAlg).2

/--
SD0 main fixture theorem for Part II definitions 9.1–11.2 and Part III definitions 4.1–4.3 with conditions 4.4–4.5.
Its material data are fixed or constructed inside this fixture; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem right_restriction_not_isIso :
    ¬ IsIso (sheafifiedRestriction referenceRaw rightToBase) := by
  intro h
  letI := h
  have hIso : IsIso
      (baseSectionRingIso.inv ≫
        sheafifiedRestriction referenceRaw rightToBase ≫
        rightSectionRingIso.hom) := inferInstance
  have hAlg : IsIso (CommRingCat.ofHom
      (algebraMap AmbientRing (Localization.Away rightGenerator))) := by
    rw [← right_restriction_is_localization]
    exact hIso
  exact right_algebraMap_not_surjective
    ((ConcreteCategory.isIso_iff_bijective _).mp hAlg).2

/-!
### SD1 actual principal-open atlas

The ambient scheme is `Spec ℤ[x]`.  Its two charts are the canonical
localization-away morphisms for `x` and `1 - x`; their joint coverage is
proved from the span computation already fixed by SD0.  The mixed overlap is
constructed from the localization pushout and transported to the
architecture chart restriction square.  Self-overlaps use the identity
pullback squares.  The overlap presentation, decoration compatibility, and
triple cocycle are then supplied by the generic `StandardArchitectureScheme`
API.
-/

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def ambientScheme : AlgebraicGeometry.Scheme :=
  AlgebraicGeometry.Spec (CommRingCat.of AmbientRing)

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem ambientScheme_eq :
    ambientScheme =
      AlgebraicGeometry.Spec (CommRingCat.of AmbientRing) :=
  rfl

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def baseChartDomainIso :
    architectureChartSpec referenceRaw baseContext ≅
      ambientScheme :=
  AlgebraicGeometry.Scheme.Spec.mapIso baseSectionRingIso.symm.op

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem baseChartDomainIso_eq :
    baseChartDomainIso =
      AlgebraicGeometry.Scheme.Spec.mapIso baseSectionRingIso.symm.op :=
  rfl

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def leftChartDomainIso :
    architectureChartSpec referenceRaw leftContext ≅
      AlgebraicGeometry.Spec
        (CommRingCat.of (Localization.Away leftGenerator)) :=
  AlgebraicGeometry.Scheme.Spec.mapIso leftSectionRingIso.symm.op

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem leftChartDomainIso_eq :
    leftChartDomainIso =
      AlgebraicGeometry.Scheme.Spec.mapIso leftSectionRingIso.symm.op :=
  rfl

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def rightChartDomainIso :
    architectureChartSpec referenceRaw rightContext ≅
      AlgebraicGeometry.Spec
        (CommRingCat.of (Localization.Away rightGenerator)) :=
  AlgebraicGeometry.Scheme.Spec.mapIso rightSectionRingIso.symm.op

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem rightChartDomainIso_eq :
    rightChartDomainIso =
      AlgebraicGeometry.Scheme.Spec.mapIso rightSectionRingIso.symm.op :=
  rfl

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def overlapChartDomainIso :
    architectureChartSpec referenceRaw overlapContext ≅
      AlgebraicGeometry.Spec
        (CommRingCat.of (Localization.Away overlapGenerator)) :=
  AlgebraicGeometry.Scheme.Spec.mapIso overlapSectionRingIso.symm.op

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem overlapChartDomainIso_eq :
    overlapChartDomainIso =
      AlgebraicGeometry.Scheme.Spec.mapIso overlapSectionRingIso.symm.op :=
  rfl

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def ambientDecoration :
    AATReadingDecoration referenceRaw ambientScheme :=
  AATReadingDecoration.pullback
    referenceRaw baseChartDomainIso.inv
    (AATReadingDecoration.ofContext referenceRaw baseContext)

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem ambientDecoration_eq :
    ambientDecoration =
      AATReadingDecoration.pullback
        referenceRaw baseChartDomainIso.inv
        (AATReadingDecoration.ofContext referenceRaw baseContext) :=
  rfl

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def leftChart :
    ArchitectureAffineChart
      referenceRaw ambientScheme ambientDecoration where
  context := leftContext
  contextHom := leftToBase
  map :=
    leftChartDomainIso.hom ≫
      AlgebraicGeometry.Scheme.Spec.map
        (CommRingCat.ofHom
          (algebraMap AmbientRing
            (Localization.Away leftGenerator))).op

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def rightChart :
    ArchitectureAffineChart
      referenceRaw ambientScheme ambientDecoration where
  context := rightContext
  contextHom := rightToBase
  map :=
    rightChartDomainIso.hom ≫
      AlgebraicGeometry.Scheme.Spec.map
        (CommRingCat.ofHom
          (algebraMap AmbientRing
            (Localization.Away rightGenerator))).op

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def referenceAtlas :
    ArchitectureAffineAtlas
      referenceRaw ambientScheme ambientDecoration where
  Index := Bool
  chart
    | false => leftChart
    | true => rightChart

private theorem leftChart_map_eq_restriction :
    leftChart.map =
      architectureChartRestriction referenceRaw leftToBase ≫
        baseChartDomainIso.hom := by
  simp only [leftChart, leftChartDomainIso, baseChartDomainIso,
    architectureChartRestriction, Functor.mapIso_hom]
  rw [← AlgebraicGeometry.Scheme.Spec.map_comp,
    ← AlgebraicGeometry.Scheme.Spec.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, Quiver.Hom.unop_op]
  change
    CommRingCat.ofHom
          (algebraMap AmbientRing (Localization.Away leftGenerator)) ≫
        leftSectionRingIso.inv =
      baseSectionRingIso.inv ≫
        sheafifiedRestriction referenceRaw leftToBase
  rw [← cancel_mono leftSectionRingIso.hom]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact left_restriction_is_localization.symm

private theorem rightChart_map_eq_restriction :
    rightChart.map =
      architectureChartRestriction referenceRaw rightToBase ≫
        baseChartDomainIso.hom := by
  simp only [rightChart, rightChartDomainIso, baseChartDomainIso,
    architectureChartRestriction, Functor.mapIso_hom]
  rw [← AlgebraicGeometry.Scheme.Spec.map_comp,
    ← AlgebraicGeometry.Scheme.Spec.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, Quiver.Hom.unop_op]
  change
    CommRingCat.ofHom
          (algebraMap AmbientRing (Localization.Away rightGenerator)) ≫
        rightSectionRingIso.inv =
      baseSectionRingIso.inv ≫
        sheafifiedRestriction referenceRaw rightToBase
  rw [← cancel_mono rightSectionRingIso.hom]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact right_restriction_is_localization.symm

private theorem leftChart_valid :
    IsArchitectureAffineChart referenceRaw leftChart := by
  constructor
  · simp only [leftChart]
    rw [AlgebraicGeometry.Scheme.Spec_map]
    simp only [Quiver.Hom.unop_op]
    letI : AlgebraicGeometry.IsOpenImmersion leftChartDomainIso.hom := by
      infer_instance
    letI : AlgebraicGeometry.IsOpenImmersion
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            (algebraMap AmbientRing
              (Localization.Away leftGenerator)))) := by
      infer_instance
    exact AlgebraicGeometry.IsOpenImmersion.comp _ _
  · rw [leftChart_map_eq_restriction]
    simp only [leftChart]
    simp only [ambientDecoration, AATReadingDecoration.pullback_interpretation,
      AATReadingDecoration.ofContext_interpretation,
      AlgebraicGeometry.Scheme.Hom.comp_appTop, Category.assoc]
    rw [← Category.assoc baseChartDomainIso.inv.appTop,
      ← AlgebraicGeometry.Scheme.Hom.comp_appTop,
      baseChartDomainIso.hom_inv_id,
      AlgebraicGeometry.Scheme.Hom.id_appTop, Category.id_comp]
    rw [architectureChartRestriction_appTop]
    simp only [Iso.inv_hom_id_assoc]

private theorem rightChart_valid :
    IsArchitectureAffineChart referenceRaw rightChart := by
  constructor
  · simp only [rightChart]
    rw [AlgebraicGeometry.Scheme.Spec_map]
    simp only [Quiver.Hom.unop_op]
    letI : AlgebraicGeometry.IsOpenImmersion rightChartDomainIso.hom := by
      infer_instance
    letI : AlgebraicGeometry.IsOpenImmersion
        (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom
            (algebraMap AmbientRing
              (Localization.Away rightGenerator)))) := by
      infer_instance
    exact AlgebraicGeometry.IsOpenImmersion.comp _ _
  · rw [rightChart_map_eq_restriction]
    simp only [rightChart]
    simp only [ambientDecoration, AATReadingDecoration.pullback_interpretation,
      AATReadingDecoration.ofContext_interpretation,
      AlgebraicGeometry.Scheme.Hom.comp_appTop, Category.assoc]
    rw [← Category.assoc baseChartDomainIso.inv.appTop,
      ← AlgebraicGeometry.Scheme.Hom.comp_appTop,
      baseChartDomainIso.hom_inv_id,
      AlgebraicGeometry.Scheme.Hom.id_appTop, Category.id_comp]
    rw [architectureChartRestriction_appTop]
    simp only [Iso.inv_hom_id_assoc]

/--
SD1 main fixture theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem referenceAtlas_valid :
    IsArchitectureAffineAtlas referenceRaw referenceAtlas := by
  constructor
  · intro i
    cases i
    · exact leftChart_valid
    · exact rightChart_valid
  · intro x
    let C := AlgebraicGeometry.Scheme.affineOpenCoverOfSpanRangeEqTop
      (R := CommRingCat.of AmbientRing)
      coverGenerator coverGenerator_span_eq_top
    rcases C.covers x with ⟨y, hy⟩
    generalize hi : C.idx x = i at y hy
    cases i
    · refine ⟨false, leftChartDomainIso.inv y, ?_⟩
      simpa only [referenceAtlas, leftChart,
        AlgebraicGeometry.Scheme.inv_hom_apply,
        AlgebraicGeometry.Scheme.Hom.comp_apply,
        AlgebraicGeometry.Scheme.Spec_map, Quiver.Hom.unop_op,
        AlgebraicGeometry.Scheme.affineOpenCoverOfSpanRangeEqTop_f,
        C, coverGenerator_false] using hy
    · refine ⟨true, rightChartDomainIso.inv y, ?_⟩
      simpa only [referenceAtlas, rightChart,
        AlgebraicGeometry.Scheme.inv_hom_apply,
        AlgebraicGeometry.Scheme.Hom.comp_apply,
        AlgebraicGeometry.Scheme.Spec_map, Quiver.Hom.unop_op,
        AlgebraicGeometry.Scheme.affineOpenCoverOfSpanRangeEqTop_f,
        C, coverGenerator_true] using hy

private abbrev leftLocalizationMap :
    CommRingCat.of AmbientRing ⟶
      CommRingCat.of (Localization.Away leftGenerator) :=
  CommRingCat.ofHom
    (algebraMap AmbientRing (Localization.Away leftGenerator))

private abbrev rightLocalizationMap :
    CommRingCat.of AmbientRing ⟶
      CommRingCat.of (Localization.Away rightGenerator) :=
  CommRingCat.ofHom
    (algebraMap AmbientRing (Localization.Away rightGenerator))

private abbrev leftOverlapMap :
    CommRingCat.of (Localization.Away leftGenerator) ⟶
      CommRingCat.of (Localization.Away overlapGenerator) :=
  CommRingCat.ofHom leftToOverlapRingHom

private abbrev rightOverlapMap :
    CommRingCat.of (Localization.Away rightGenerator) ⟶
      CommRingCat.of (Localization.Away overlapGenerator) :=
  CommRingCat.ofHom rightToOverlapRingHom

private theorem overlapGenerator_isUnit_in_pushoutTarget
    (s : PushoutCocone leftLocalizationMap rightLocalizationMap) :
    IsUnit
      ((s.inl.hom.comp
          (algebraMap AmbientRing (Localization.Away leftGenerator)))
        overlapGenerator) := by
  rw [overlapGenerator_eq, map_mul]
  apply IsUnit.mul
  · exact (IsLocalization.Away.algebraMap_isUnit leftGenerator).map s.inl.hom
  · have hy :=
      (IsLocalization.Away.algebraMap_isUnit rightGenerator).map s.inr.hom
    have hc := congrArg (fun q => q.hom rightGenerator) s.condition
    have hc' :
        s.inl.hom
            (algebraMap AmbientRing
              (Localization.Away leftGenerator) rightGenerator) =
          s.inr.hom
            (algebraMap AmbientRing
              (Localization.Away rightGenerator) rightGenerator) := by
      simpa only [CommRingCat.comp_apply] using hc
    change IsUnit
      (s.inl.hom
        (algebraMap AmbientRing
          (Localization.Away leftGenerator) rightGenerator))
    rw [hc']
    exact hy

private noncomputable def overlapPushoutDesc
    (s : PushoutCocone leftLocalizationMap rightLocalizationMap) :
    CommRingCat.of (Localization.Away overlapGenerator) ⟶ s.pt :=
  CommRingCat.ofHom
    (IsLocalization.Away.lift overlapGenerator
      (overlapGenerator_isUnit_in_pushoutTarget s))

private theorem overlapPushoutDesc_comp_algebraMap
    (s : PushoutCocone leftLocalizationMap rightLocalizationMap) :
    (overlapPushoutDesc s).hom.comp
        (algebraMap AmbientRing (Localization.Away overlapGenerator)) =
      s.inl.hom.comp
        (algebraMap AmbientRing (Localization.Away leftGenerator)) :=
  IsLocalization.Away.lift_comp overlapGenerator
    (overlapGenerator_isUnit_in_pushoutTarget s)

private theorem localizationSquare_isPushout :
    IsPushout leftLocalizationMap rightLocalizationMap
      leftOverlapMap rightOverlapMap := by
  refine
    { w := ?_
      isColimit' := ⟨PushoutCocone.IsColimit.mk _ overlapPushoutDesc
        ?_ ?_ ?_⟩ }
  · apply ConcreteCategory.hom_ext
    intro a
    simpa only [CommRingCat.comp_apply] using
      congrArg (fun q => q a)
        (leftToOverlapRingHom_comp_algebraMap.trans
          rightToOverlapRingHom_comp_algebraMap.symm)
  · intro s
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers leftGenerator)
    change
      ((overlapPushoutDesc s).hom.comp leftToOverlapRingHom).comp
          (algebraMap AmbientRing (Localization.Away leftGenerator)) =
        s.inl.hom.comp
          (algebraMap AmbientRing (Localization.Away leftGenerator))
    rw [RingHom.comp_assoc, leftToOverlapRingHom_comp_algebraMap]
    exact overlapPushoutDesc_comp_algebraMap s
  · intro s
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers rightGenerator)
    change
      ((overlapPushoutDesc s).hom.comp rightToOverlapRingHom).comp
          (algebraMap AmbientRing (Localization.Away rightGenerator)) =
        s.inr.hom.comp
          (algebraMap AmbientRing (Localization.Away rightGenerator))
    rw [RingHom.comp_assoc, rightToOverlapRingHom_comp_algebraMap]
    rw [overlapPushoutDesc_comp_algebraMap]
    exact congrArg CommRingCat.Hom.hom s.condition
  · intro s m hmLeft _hmRight
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (Submonoid.powers overlapGenerator)
    change
      m.hom.comp
          (algebraMap AmbientRing (Localization.Away overlapGenerator)) =
        (overlapPushoutDesc s).hom.comp
          (algebraMap AmbientRing (Localization.Away overlapGenerator))
    rw [← leftToOverlapRingHom_comp_algebraMap]
    rw [← RingHom.comp_assoc, ← RingHom.comp_assoc]
    have hm := congrArg CommRingCat.Hom.hom hmLeft
    change m.hom.comp leftToOverlapRingHom = s.inl.hom at hm
    rw [hm]
    rw [RingHom.comp_assoc, leftToOverlapRingHom_comp_algebraMap,
      overlapPushoutDesc_comp_algebraMap]

private theorem localizationSquare_isPullback :
    IsPullback
      (AlgebraicGeometry.Spec.map leftOverlapMap)
      (AlgebraicGeometry.Spec.map rightOverlapMap)
      (AlgebraicGeometry.Spec.map leftLocalizationMap)
      (AlgebraicGeometry.Spec.map rightLocalizationMap) :=
  AlgebraicGeometry.isPullback_SpecMap_of_isPushout
    leftLocalizationMap rightLocalizationMap
    leftOverlapMap rightOverlapMap localizationSquare_isPushout

private theorem overlapChart_toLeft :
    overlapChartDomainIso.hom ≫
        AlgebraicGeometry.Spec.map leftOverlapMap =
      architectureChartRestriction referenceRaw overlapToLeft ≫
        leftChartDomainIso.hom := by
  simp only [overlapChartDomainIso, leftChartDomainIso,
    architectureChartRestriction, Functor.mapIso_hom,
    AlgebraicGeometry.Scheme.Spec_map, Quiver.Hom.unop_op]
  rw [← AlgebraicGeometry.Spec.map_comp,
    ← AlgebraicGeometry.Spec.map_comp]
  congr 1
  change
    leftOverlapMap ≫ overlapSectionRingIso.inv =
      leftSectionRingIso.inv ≫
        sheafifiedRestriction referenceRaw overlapToLeft
  rw [← cancel_mono overlapSectionRingIso.hom]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact overlap_left_restriction_is_localization.symm

private theorem overlapChart_toRight :
    overlapChartDomainIso.hom ≫
        AlgebraicGeometry.Spec.map rightOverlapMap =
      architectureChartRestriction referenceRaw overlapToRight ≫
        rightChartDomainIso.hom := by
  simp only [overlapChartDomainIso, rightChartDomainIso,
    architectureChartRestriction, Functor.mapIso_hom,
    AlgebraicGeometry.Scheme.Spec_map, Quiver.Hom.unop_op]
  rw [← AlgebraicGeometry.Spec.map_comp,
    ← AlgebraicGeometry.Spec.map_comp]
  congr 1
  change
    rightOverlapMap ≫ overlapSectionRingIso.inv =
      rightSectionRingIso.inv ≫
        sheafifiedRestriction referenceRaw overlapToRight
  rw [← cancel_mono overlapSectionRingIso.hom]
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact overlap_right_restriction_is_localization.symm

private theorem referenceAtlas_pairContext_false_true :
    referenceAtlas.pairContext referenceRaw false true = overlapContext := by
  change
    Site.ContextCategoryObject.of referenceContextPreorder
        (referenceOverlap.overlap
          (AAT.AG.FiniteModel.twoPatchContext
            AAT.AG.FiniteModel.TwoPatchContextIndex.base)
          (AAT.AG.FiniteModel.twoPatchContext
            AAT.AG.FiniteModel.TwoPatchContextIndex.left)
          (AAT.AG.FiniteModel.twoPatchContext
            AAT.AG.FiniteModel.TwoPatchContextIndex.right)) =
      Site.ContextCategoryObject.of referenceContextPreorder
        (AAT.AG.FiniteModel.twoPatchContext
          AAT.AG.FiniteModel.TwoPatchContextIndex.overlap)
  congr 1
  exact referenceOverlap_selected _ _ _

private theorem referenceAtlas_pairContext_true_false :
    referenceAtlas.pairContext referenceRaw true false = overlapContext := by
  change
    Site.ContextCategoryObject.of referenceContextPreorder
        (referenceOverlap.overlap
          (AAT.AG.FiniteModel.twoPatchContext
            AAT.AG.FiniteModel.TwoPatchContextIndex.base)
          (AAT.AG.FiniteModel.twoPatchContext
            AAT.AG.FiniteModel.TwoPatchContextIndex.right)
          (AAT.AG.FiniteModel.twoPatchContext
            AAT.AG.FiniteModel.TwoPatchContextIndex.left)) =
      Site.ContextCategoryObject.of referenceContextPreorder
        (AAT.AG.FiniteModel.twoPatchContext
          AAT.AG.FiniteModel.TwoPatchContextIndex.overlap)
  congr 1
  exact referenceOverlap_selected _ _ _

private theorem principalArchitectureSquare_isPullback :
    IsPullback
      (architectureChartRestriction referenceRaw overlapToLeft)
      (architectureChartRestriction referenceRaw overlapToRight)
      leftChart.map rightChart.map := by
  apply localizationSquare_isPullback.of_iso'
      overlapChartDomainIso leftChartDomainIso rightChartDomainIso
      (Iso.refl ambientScheme)
  · exact overlapChart_toLeft
  · exact overlapChart_toRight
  · rfl
  · rfl

private noncomputable def falseTruePairContextIso :
    referenceAtlas.pairContext referenceRaw false true ≅ overlapContext :=
  eqToIso referenceAtlas_pairContext_false_true

private noncomputable def falseTruePairDomainIso :
    architectureChartSpec referenceRaw
        (referenceAtlas.pairContext referenceRaw false true) ≅
      AlgebraicGeometry.Spec
        (CommRingCat.of (Localization.Away overlapGenerator)) :=
  architectureChartIso referenceRaw falseTruePairContextIso ≪≫
    overlapChartDomainIso

private theorem falseTruePairDomain_toLeft :
    falseTruePairDomainIso.hom ≫
        AlgebraicGeometry.Spec.map leftOverlapMap =
      architectureChartRestriction referenceRaw
          (referenceAtlas.pairToLeft referenceRaw false true) ≫
        leftChartDomainIso.hom := by
  simp only [falseTruePairDomainIso, Iso.trans_hom,
    architectureChartIso_hom, Category.assoc]
  rw [overlapChart_toLeft]
  rw [← Category.assoc, ← architectureChartRestriction_comp]
  exact congrArg
    (fun q => architectureChartRestriction referenceRaw q ≫
      leftChartDomainIso.hom)
    (Subsingleton.elim _ _)

private theorem falseTruePairDomain_toRight :
    falseTruePairDomainIso.hom ≫
        AlgebraicGeometry.Spec.map rightOverlapMap =
      architectureChartRestriction referenceRaw
          (referenceAtlas.pairToRight referenceRaw false true) ≫
        rightChartDomainIso.hom := by
  simp only [falseTruePairDomainIso, Iso.trans_hom,
    architectureChartIso_hom, Category.assoc]
  rw [overlapChart_toRight]
  rw [← Category.assoc, ← architectureChartRestriction_comp]
  exact congrArg
    (fun q => architectureChartRestriction referenceRaw q ≫
      rightChartDomainIso.hom)
    (Subsingleton.elim _ _)

private theorem falseTruePair_isPullback :
    IsPullback
      (architectureChartRestriction referenceRaw
        (referenceAtlas.pairToLeft referenceRaw false true))
      (architectureChartRestriction referenceRaw
        (referenceAtlas.pairToRight referenceRaw false true))
      leftChart.map rightChart.map := by
  apply localizationSquare_isPullback.of_iso'
      falseTruePairDomainIso leftChartDomainIso rightChartDomainIso
      (Iso.refl ambientScheme)
  · exact falseTruePairDomain_toLeft
  · exact falseTruePairDomain_toRight
  · rfl
  · rfl

private noncomputable def trueFalsePairContextIso :
    referenceAtlas.pairContext referenceRaw true false ≅ overlapContext :=
  eqToIso referenceAtlas_pairContext_true_false

private noncomputable def trueFalsePairDomainIso :
    architectureChartSpec referenceRaw
        (referenceAtlas.pairContext referenceRaw true false) ≅
      AlgebraicGeometry.Spec
        (CommRingCat.of (Localization.Away overlapGenerator)) :=
  architectureChartIso referenceRaw trueFalsePairContextIso ≪≫
    overlapChartDomainIso

private theorem trueFalsePairDomain_toLeft :
    trueFalsePairDomainIso.hom ≫
        AlgebraicGeometry.Spec.map rightOverlapMap =
      architectureChartRestriction referenceRaw
          (referenceAtlas.pairToLeft referenceRaw true false) ≫
        rightChartDomainIso.hom := by
  simp only [trueFalsePairDomainIso, Iso.trans_hom,
    architectureChartIso_hom, Category.assoc]
  rw [overlapChart_toRight]
  rw [← Category.assoc, ← architectureChartRestriction_comp]
  exact congrArg
    (fun q => architectureChartRestriction referenceRaw q ≫
      rightChartDomainIso.hom)
    (Subsingleton.elim _ _)

private theorem trueFalsePairDomain_toRight :
    trueFalsePairDomainIso.hom ≫
        AlgebraicGeometry.Spec.map leftOverlapMap =
      architectureChartRestriction referenceRaw
          (referenceAtlas.pairToRight referenceRaw true false) ≫
        leftChartDomainIso.hom := by
  simp only [trueFalsePairDomainIso, Iso.trans_hom,
    architectureChartIso_hom, Category.assoc]
  rw [overlapChart_toLeft]
  rw [← Category.assoc, ← architectureChartRestriction_comp]
  exact congrArg
    (fun q => architectureChartRestriction referenceRaw q ≫
      leftChartDomainIso.hom)
    (Subsingleton.elim _ _)

private theorem trueFalsePair_isPullback :
    IsPullback
      (architectureChartRestriction referenceRaw
        (referenceAtlas.pairToLeft referenceRaw true false))
      (architectureChartRestriction referenceRaw
        (referenceAtlas.pairToRight referenceRaw true false))
      rightChart.map leftChart.map := by
  apply localizationSquare_isPullback.flip.of_iso'
      trueFalsePairDomainIso rightChartDomainIso leftChartDomainIso
      (Iso.refl ambientScheme)
  · exact trueFalsePairDomain_toLeft
  · exact trueFalsePairDomain_toRight
  · rfl
  · rfl

private theorem referenceAtlas_pair_isPullback
    (i j : referenceAtlas.Index) :
    IsPullback
      (architectureChartRestriction referenceRaw
        (referenceAtlas.pairToLeft referenceRaw i j))
      (architectureChartRestriction referenceRaw
        (referenceAtlas.pairToRight referenceRaw i j))
      (referenceAtlas.chart i).map
      (referenceAtlas.chart j).map := by
  cases i <;> cases j
  · letI : IsIso
        (architectureChartRestriction referenceRaw
          (referenceAtlas.pairToLeft referenceRaw false false)) := by
      change IsIso
        (architectureChartIso referenceRaw
          (referenceAtlas.selfPairContextIso referenceRaw false)).hom
      infer_instance
    letI : AlgebraicGeometry.IsOpenImmersion
        (referenceAtlas.chart false).map := leftChart_valid.isOpenImmersion
    apply IsPullback.of_horiz_isIso_mono
    constructor
    exact congrArg
      (fun q => architectureChartRestriction referenceRaw q ≫ leftChart.map)
      (Subsingleton.elim _ _)
  · exact falseTruePair_isPullback
  · exact trueFalsePair_isPullback
  · letI : IsIso
        (architectureChartRestriction referenceRaw
          (referenceAtlas.pairToLeft referenceRaw true true)) := by
      change IsIso
        (architectureChartIso referenceRaw
          (referenceAtlas.selfPairContextIso referenceRaw true)).hom
      infer_instance
    letI : AlgebraicGeometry.IsOpenImmersion
        (referenceAtlas.chart true).map := rightChart_valid.isOpenImmersion
    apply IsPullback.of_horiz_isIso_mono
    constructor
    exact congrArg
      (fun q => architectureChartRestriction referenceRaw q ≫ rightChart.map)
      (Subsingleton.elim _ _)

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def referenceOverlapPresentation :
    ArchitectureOverlapPresentation referenceRaw referenceAtlas where
  comparison i j := (referenceAtlas_pair_isPullback i j).isoPullback

/--
SD1 main fixture theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem referenceOverlapPresentation_valid :
    IsArchitectureOverlapPresentation
      referenceRaw referenceOverlapPresentation := by
  constructor
  · intro i j
    exact IsPullback.isoPullback_hom_fst
      (referenceAtlas_pair_isPullback i j)
  · intro i j
    exact IsPullback.isoPullback_hom_snd
      (referenceAtlas_pair_isPullback i j)

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def referenceScheme :
    StandardArchitectureScheme referenceRaw :=
  StandardArchitectureScheme.ofPresentation
    referenceRaw ambientScheme ambientDecoration
    referenceAtlas referenceAtlas_valid
    referenceOverlapPresentation
    referenceOverlapPresentation_valid

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem referenceScheme_eq :
    referenceScheme =
      StandardArchitectureScheme.ofPresentation
        referenceRaw ambientScheme ambientDecoration
        referenceAtlas referenceAtlas_valid
        referenceOverlapPresentation
        referenceOverlapPresentation_valid :=
  rfl

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def leftIndex : referenceScheme.atlas.Index :=
  false

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
def rightIndex : referenceScheme.atlas.Index :=
  true

/--
SD1 main fixture theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem leftIndex_ne_rightIndex : leftIndex ≠ rightIndex := by
  change (false : Bool) ≠ true
  decide

/--
SD1 main fixture theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem index_cases (i : referenceScheme.atlas.Index) :
    i = leftIndex ∨ i = rightIndex := by
  cases i <;> simp [leftIndex, rightIndex]

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem referenceScheme_underlying :
    referenceScheme.underlying = ambientScheme :=
  rfl

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem left_chart_context :
    (referenceScheme.atlas.chart leftIndex).context = leftContext :=
  rfl

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem right_chart_context :
    (referenceScheme.atlas.chart rightIndex).context = rightContext :=
  rfl

/--
SD1 main fixture theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem chart_contexts_ne :
    (referenceScheme.atlas.chart leftIndex).context ≠
      (referenceScheme.atlas.chart rightIndex).context := by
  rw [left_chart_context, right_chart_context]
  intro h
  have hctx := congrArg Site.ContextCategoryObject.ctx h
  have heq := congrArg
    (fun W : Site.ArchitectureContext AAT.AG.FiniteModel.corePackage.object =>
      (⟨W.Extension, W.extension⟩ : Sigma fun T : Type => T)) hctx
  injection heq with _ hindex
  exact AAT.AG.FiniteModel.TwoPatchContextIndex.noConfusion hindex

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem left_chart_map :
    (referenceScheme.atlas.chart leftIndex).map =
      leftChartDomainIso.hom ≫
        AlgebraicGeometry.Scheme.Spec.map
          (CommRingCat.ofHom
            (algebraMap AmbientRing
              (Localization.Away leftGenerator))).op :=
  rfl

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem right_chart_map :
    (referenceScheme.atlas.chart rightIndex).map =
      rightChartDomainIso.hom ≫
        AlgebraicGeometry.Scheme.Spec.map
          (CommRingCat.ofHom
            (algebraMap AmbientRing
              (Localization.Away rightGenerator))).op :=
  rfl

/--
SD1 main fixture theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem left_chart_isOpenImmersion :
    AlgebraicGeometry.IsOpenImmersion
      (referenceScheme.atlas.chart leftIndex).map :=
  referenceScheme.atlasValid.chart_valid leftIndex |>.isOpenImmersion

/--
SD1 main fixture theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem right_chart_isOpenImmersion :
    AlgebraicGeometry.IsOpenImmersion
      (referenceScheme.atlas.chart rightIndex).map :=
  referenceScheme.atlasValid.chart_valid rightIndex |>.isOpenImmersion

/--
SD1 main fixture theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem twoChart_jointlyCovers :
    ⨆ i,
        ((referenceScheme.affineOpenCover referenceRaw).f i).opensRange =
      ⊤ :=
  referenceScheme.atlas.jointlyCovers referenceRaw referenceScheme.atlasValid

/--
SD1 main fixture theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem left_chart_not_isIso :
    ¬ IsIso (referenceScheme.atlas.chart leftIndex).map := by
  intro h
  have hChart : IsIso leftChart.map := h
  have hcomp : IsIso
      (architectureChartRestriction referenceRaw leftToBase ≫
        baseChartDomainIso.hom) := by
    rw [← leftChart_map_eq_restriction]
    exact hChart
  letI := hcomp
  haveI : IsIso
      (architectureChartRestriction referenceRaw leftToBase) :=
    CategoryTheory.IsIso.of_isIso_comp_right _ baseChartDomainIso.hom
  haveI : IsIso
      ((architectureChartRestriction referenceRaw leftToBase).appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw leftContext)).hom) :=
    inferInstance
  haveI : IsIso
      ((AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw baseContext)).hom ≫
        sheafifiedRestriction referenceRaw leftToBase) := by
    rw [← architectureChartRestriction_appTop]
    infer_instance
  haveI : IsIso (sheafifiedRestriction referenceRaw leftToBase) :=
    CategoryTheory.IsIso.of_isIso_comp_left
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing referenceRaw baseContext)).hom _
  exact left_restriction_not_isIso inferInstance

/--
SD1 main fixture theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem right_chart_not_isIso :
    ¬ IsIso (referenceScheme.atlas.chart rightIndex).map := by
  intro h
  have hChart : IsIso rightChart.map := h
  have hcomp : IsIso
      (architectureChartRestriction referenceRaw rightToBase ≫
        baseChartDomainIso.hom) := by
    rw [← rightChart_map_eq_restriction]
    exact hChart
  letI := hcomp
  haveI : IsIso
      (architectureChartRestriction referenceRaw rightToBase) :=
    CategoryTheory.IsIso.of_isIso_comp_right _ baseChartDomainIso.hom
  haveI : IsIso
      ((architectureChartRestriction referenceRaw rightToBase).appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw rightContext)).hom) :=
    inferInstance
  haveI : IsIso
      ((AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw baseContext)).hom ≫
        sheafifiedRestriction referenceRaw rightToBase) := by
    rw [← architectureChartRestriction_appTop]
    infer_instance
  haveI : IsIso (sheafifiedRestriction referenceRaw rightToBase) :=
    CategoryTheory.IsIso.of_isIso_comp_left
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing referenceRaw baseContext)).hom _
  exact right_restriction_not_isIso inferInstance

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem pair_context :
    referenceScheme.atlas.pairContext
        referenceRaw leftIndex rightIndex =
      overlapContext :=
  referenceAtlas_pairContext_false_true

/--
SD1 fixture data for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
noncomputable def actualOverlapIso :
    referenceScheme.atlas.actualOverlap
        referenceRaw leftIndex rightIndex ≅
      AlgebraicGeometry.Spec
        (CommRingCat.of (Localization.Away overlapGenerator)) :=
  (referenceScheme.overlap_is_actual_pullback
      referenceRaw leftIndex rightIndex).symm ≪≫
    eqToIso (by rw [pair_context]) ≪≫
    overlapChartDomainIso

/--
SD1 constructor-provenance or no-unfold API theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
As a simp rule, it normalizes the left-hand fixture expression to the right-hand concrete or canonical expression.
The executable contract fixes the exact declaration type.
-/
@[simp] theorem actualOverlapIso_eq :
    actualOverlapIso =
      (referenceScheme.overlap_is_actual_pullback
          referenceRaw leftIndex rightIndex).symm ≪≫
        eqToIso (by rw [pair_context]) ≪≫
        overlapChartDomainIso :=
  rfl

private theorem overlapGenerator_ne_zero : overlapGenerator ≠ 0 := by
  rw [overlapGenerator_eq]
  apply mul_ne_zero
  · simpa [leftGenerator, coordinate] using
      (MvPolynomial.X_ne_zero (R := Int) ())
  · intro h
    have h' := congrArg
      (MvPolynomial.eval₂Hom (RingHom.id Int) (fun _ : Unit => (0 : Int))) h
    norm_num [rightGenerator, coordinate] at h'

/--
SD1 main fixture theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem actualOverlap_nonempty :
    Nonempty
      (referenceScheme.atlas.actualOverlap
        referenceRaw leftIndex rightIndex) := by
  letI : Nontrivial (Localization.Away overlapGenerator) :=
    Function.Injective.nontrivial
      (IsLocalization.injective (Localization.Away overlapGenerator)
        (powers_le_nonZeroDivisors_of_noZeroDivisors overlapGenerator_ne_zero))
  let x := Classical.choice
    (inferInstance : Nonempty
      (AlgebraicGeometry.Spec
        (CommRingCat.of (Localization.Away overlapGenerator))))
  exact ⟨actualOverlapIso.inv x⟩

/--
SD1 main fixture theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem decoration_overlap :
    sheafifiedRestriction referenceRaw
        (referenceScheme.atlas.pairToLeft
            referenceRaw leftIndex rightIndex ≫
          (referenceScheme.atlas.chart leftIndex).contextHom) =
      sheafifiedRestriction referenceRaw
        (referenceScheme.atlas.pairToRight
            referenceRaw leftIndex rightIndex ≫
          (referenceScheme.atlas.chart rightIndex).contextHom) :=
  referenceScheme.atlas.decoration_overlap
    referenceRaw leftIndex rightIndex

/--
SD1 main fixture theorem for the actual two-principal-open atlas over `Spec ℤ[x]`.
Its material data are fixed or constructed inside this reference model; no external material certificate is used.
The executable contract fixes the exact declaration type.
-/
theorem actual_triple_cocycle :
    ∀ i j l : referenceScheme.atlas.Index,
      referenceScheme.atlas.actualTripleToLeft
            referenceRaw i j l ≫
          (referenceScheme.atlas.chart i).map =
        referenceScheme.atlas.actualTripleToMiddle
            referenceRaw i j l ≫
          (referenceScheme.atlas.chart j).map ∧
      referenceScheme.atlas.actualTripleToMiddle
            referenceRaw i j l ≫
          (referenceScheme.atlas.chart j).map =
        referenceScheme.atlas.actualTripleToRight
            referenceRaw i j l ≫
          (referenceScheme.atlas.chart l).map := by
  intro i j l
  exact referenceScheme.atlas.actualTriple_cocycle referenceRaw i j l


end
end AAT.AG.Examples.StandardGeometryReferenceModels
