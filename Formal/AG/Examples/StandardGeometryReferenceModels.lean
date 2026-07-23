import Formal.AG.Examples.FiniteModel
import Formal.AG.LawAlgebra.ClosedEquationalGeometry
import Formal.AG.ReadingFunctoriality.Coefficient
import Formal.AG.ReadingFunctoriality.StandardSchemeCoefficient
import Formal.AG.ReadingFunctoriality.CoefficientGeometry
import Mathlib.Algebra.MvPolynomial.Eval
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
# Standard geometry reference models

This module implements the fixed SD0--SD7 reference model over `ℤ[x]`.
It connects the selected four-context site and raw sheaf calculation to an
actual two-principal-open atlas, three law-generated closed geometries,
their 0/1/2 firing points and contravariant comparison maps, flat
coefficient change, negative fixtures, and the integrated firing theorem.

## Implementation notes — R1 / SD0

* The context preorder is constructed from the approved selected-index order.
  The broader existing finite-model preorder was rejected because it admits
  arrows not present in the fixed SD0 statement.
* The overlap package is built for the full context category and specializes
  to `twoPatchContextMeet` on the selected contexts.  Reusing a meet package
  for a different preorder would not establish the required pullback fields.
* The two `HasSheafify` instances are derived from small covers, finite
  multiequalizers, and the limit/colimit behavior of the under category.
  Supplying an arbitrary sheafification certificate was rejected.
* Raw sections use exactly the coordinate and two inverse variables, with two
  context-dependent relations.  Restriction maps are the fixed piecewise
  variable images; arbitrary localization isomorphisms are not input data.
* The raw sheaf theorem is proved by principal-open gluing and reconstruction
  of ring and under-category morphisms.  The localization presentations and
  their restriction equations are then derived from quotient and
  `IsLocalization.Away` universal properties.

## Implementation notes — R2 / SD1

These notes cover every nontrivial SD1 definition, including the chart-domain
isomorphisms, `leftChart`, `rightChart`, `referenceAtlas`,
`referenceOverlapPresentation`, `referenceScheme`, and `actualOverlapIso`.

* The scheme is the actual `Spec ℤ[x]`; its charts are the canonical
  localization-away morphisms for `x` and `1 - x`.  The overlap is obtained
  from the localization pushout, and `referenceScheme` is assembled with
  `StandardArchitectureScheme.ofPresentation`.  Reusing an existing
  two-chart fixture was rejected because it would not prove that these fixed
  proper principal opens and their nonempty mixed overlap are the selected
  atlas.
* Self-overlaps use identity pullback squares and mixed overlaps use the
  proved localization pullback.  Accepting an arbitrary atlas, overlap
  isomorphism, or pullback certificate as fixture data was rejected because
  the construction and its provenance must be internal to this model.

## Implementation notes — R3--R4 / SD2--SD3

These notes cover every nontrivial SD2--SD3 definition, including the weak,
strong, and rigid semantic cores and scheme bridges; their readings,
generated ideal sheaves, lawful closed subschemes, evaluation morphisms, and
0/1/2 firing packages.

* The three semantic cores share the fixed raw coordinate and differ by their
  concrete atom-indexed equations.  Their scheme bridges are built from the
  actual raw presentation, and the readings, ideals, and closed subschemes
  are obtained through the generic closed-equational APIs.  Supplying
  arbitrary ideals, exactness certificates, or closed subschemes was rejected
  because that would bypass generation by the selected laws.
* Evaluation points are actual `Scheme.Spec.map` morphisms induced by
  evaluation at `0`, `1`, and `2`.  For the selected weak and strong readings,
  semantic lawfulness, witness vanishing, ideal lawfulness, and factorization
  are connected for the same evaluation morphism through the generic
  correspondence theorems.  Encoding firing as a standalone predicate alias
  or as a conclusion-bearing certificate was rejected because it would not
  establish those four layers for the same morphism.

## Implementation notes — R5 / SD4

These notes cover every nontrivial SD4 definition, including
`weakToStrong`, `strongToRigid`, their validities, `lawComparison`,
`strongToRigidComparison`, `weakToRigidComparison`, and the composition
package.

* The inclusions use concrete total law and atom maps, and the scheme maps are
  built by `lawfulClosedSubschemeMap`; identity and composition laws come from
  the generic inclusion API.  Comparing only the order of the resulting
  ideals was rejected because the required output is the actual
  contravariant morphism between closed subschemes.
* Strict kernel and ideal inclusions prove that the comparison maps are not
  isomorphisms.  Replacing a comparison by an identity or taking a morphism as
  external fixture data was rejected because it would erase the strict
  weak/strong/rigid law hierarchy.

## Implementation notes — R6 / SD5

The nontrivial coefficient-change definitions carry declaration-local
`Implementation notes` below.  They adopt the free flat extension
`Int → Polynomial Int`, the generic scheme/reading base-change APIs, and the
induced mixed square; arbitrary flatness data, reconstructed atlases, and
external comparison morphisms are rejected there.

## Implementation notes — R7 / SD6--SD7

These notes cover every nontrivial SD6--SD7 definition, including
`duplicateLeftAtlas`, `unitIdealFixture`, `nonFlatCoefficientMap`,
`coordinateReflection`, `reflectedRightRingHom`, `brokenRightChart`, and
`standardGeometryReference_fires`.

* Each negative fixture preserves the surrounding concrete model while
  changing exactly the datum needed to expose one failure reason: duplicate
  coverage, collapsed strictness, empty unit-ideal geometry, non-flat
  coefficients, or reflected interpretation.  Taking an arbitrary invalid
  atlas, chart, ideal, or coefficient map was rejected because it would not
  identify the failed clause inside the fixed model.
* The integrated theorem is the direct conjunction of the previously proved
  component theorems.  A wrapper structure or certificate carrying those
  conclusions as fields was rejected because it would repackage rather than
  prove the complete firing matrix.
-/

set_option maxHeartbeats 4000000

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

private theorem referenceRawRestriction_id
    (W : referenceSite.category) (x : referenceRaw.rawAlgebra W) :
    (referenceRaw.restrictionStable (𝟙 W)).quotientDesc x = x := by
  have h := congrArg (fun q => q x) (referenceRaw.quotientDesc_id W)
  simpa using h

private theorem referenceRawRestriction_comp
    {W₀ W₁ W₂ : referenceSite.category}
    (f : W₀ ⟶ W₁) (g : W₁ ⟶ W₂)
    (x : referenceRaw.rawAlgebra W₂) :
    (referenceRaw.restrictionStable (f ≫ g)).quotientDesc x =
      (referenceRaw.restrictionStable f).quotientDesc
        ((referenceRaw.restrictionStable g).quotientDesc x) := by
  have h := congrArg (fun q => q x) (referenceRaw.quotientDesc_comp f g)
  simpa [RingHom.comp_apply] using h

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def weakLawEquationCore :
    SemanticLawEquationWitnessIdealCore referenceSite where
  Observable W := referenceRaw.rawAlgebra W
  observableCommRing W := inferInstance
  restrict f := (referenceRaw.restrictionStable f).quotientDesc
  restrict_id := referenceRawRestriction_id
  restrict_comp := referenceRawRestriction_comp
  violationWitness W _ a :=
    match a with
    | AAT.AG.FiniteModel.FiniteAtom.componentA =>
        rawCoordinate W * (rawCoordinate W - 1)
    | _ => 0
  violationWitness_restrict := by
    intro source target f lawIndex atom
    cases atom <;> simp only [map_mul, map_sub, map_one, map_zero,
      rawCoordinate_restrict]
  supportAtom := AAT.AG.FiniteModel.FiniteAtom.componentA
  supportLawIndex := PUnit.unit
  supportLawIndex_required :=
    referenceSite_equation_required PUnit.unit

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def strongLawEquationCore :
    SemanticLawEquationWitnessIdealCore referenceSite where
  Observable W := referenceRaw.rawAlgebra W
  observableCommRing W := inferInstance
  restrict f := (referenceRaw.restrictionStable f).quotientDesc
  restrict_id := referenceRawRestriction_id
  restrict_comp := referenceRawRestriction_comp
  violationWitness W _ a :=
    match a with
    | AAT.AG.FiniteModel.FiniteAtom.componentA =>
        rawCoordinate W * (rawCoordinate W - 1)
    | AAT.AG.FiniteModel.FiniteAtom.componentB => rawCoordinate W
    | _ => 0
  violationWitness_restrict := by
    intro source target f lawIndex atom
    cases atom <;> simp only [map_mul, map_sub, map_one, map_zero,
      rawCoordinate_restrict]
  supportAtom := AAT.AG.FiniteModel.FiniteAtom.componentA
  supportLawIndex := PUnit.unit
  supportLawIndex_required :=
    referenceSite_equation_required PUnit.unit

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def rigidLawEquationCore :
    SemanticLawEquationWitnessIdealCore referenceSite where
  Observable W := referenceRaw.rawAlgebra W
  observableCommRing W := inferInstance
  restrict f := (referenceRaw.restrictionStable f).quotientDesc
  restrict_id := referenceRawRestriction_id
  restrict_comp := referenceRawRestriction_comp
  violationWitness W _ a :=
    match a with
    | AAT.AG.FiniteModel.FiniteAtom.componentA =>
        rawCoordinate W * (rawCoordinate W - 1)
    | AAT.AG.FiniteModel.FiniteAtom.componentB => rawCoordinate W
    | AAT.AG.FiniteModel.FiniteAtom.componentC =>
        algebraMap Int (referenceRaw.rawAlgebra W) 2
    | _ => 0
  violationWitness_restrict := by
    intro source target f lawIndex atom
    cases atom <;> simp only [map_mul, map_sub, map_one, map_zero,
      map_ofNat, rawCoordinate_restrict]
  supportAtom := AAT.AG.FiniteModel.FiniteAtom.componentA
  supportLawIndex := PUnit.unit
  supportLawIndex_required :=
    referenceSite_equation_required PUnit.unit

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakLawEquationCore_observable
    (W : referenceSite.category) :
    weakLawEquationCore.Observable W = referenceRaw.rawAlgebra W :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongLawEquationCore_observable
    (W : referenceSite.category) :
    strongLawEquationCore.Observable W = referenceRaw.rawAlgebra W :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem rigidLawEquationCore_observable
    (W : referenceSite.category) :
    rigidLawEquationCore.Observable W = referenceRaw.rawAlgebra W :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakLawEquationCore_observableCommRing
    (W : referenceSite.category) :
    weakLawEquationCore.observableCommRing W =
      inferInstanceAs (CommRing (referenceRaw.rawAlgebra W)) :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongLawEquationCore_observableCommRing
    (W : referenceSite.category) :
    strongLawEquationCore.observableCommRing W =
      inferInstanceAs (CommRing (referenceRaw.rawAlgebra W)) :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem rigidLawEquationCore_observableCommRing
    (W : referenceSite.category) :
    rigidLawEquationCore.observableCommRing W =
      inferInstanceAs (CommRing (referenceRaw.rawAlgebra W)) :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakLawEquationCore_restrict
    {source target : referenceSite.category} (f : source ⟶ target) :
    weakLawEquationCore.restrict f =
      (referenceRaw.restrictionStable f).quotientDesc :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongLawEquationCore_restrict
    {source target : referenceSite.category} (f : source ⟶ target) :
    strongLawEquationCore.restrict f =
      (referenceRaw.restrictionStable f).quotientDesc :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem rigidLawEquationCore_restrict
    {source target : referenceSite.category} (f : source ⟶ target) :
    rigidLawEquationCore.restrict f =
      (referenceRaw.restrictionStable f).quotientDesc :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakViolationWitness_eq
    (W : referenceSite.category)
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    weakLawEquationCore.violationWitness W PUnit.unit a =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        rawCoordinate W * (rawCoordinate W - 1)
      else 0 :=
  by
    cases a <;> simp [weakLawEquationCore]

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongViolationWitness_eq
    (W : referenceSite.category)
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    strongLawEquationCore.violationWitness W PUnit.unit a =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        rawCoordinate W * (rawCoordinate W - 1)
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentB then
        rawCoordinate W
      else 0 :=
  by
    cases a <;> simp [strongLawEquationCore]

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem rigidViolationWitness_eq
    (W : referenceSite.category)
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    rigidLawEquationCore.violationWitness W PUnit.unit a =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        rawCoordinate W * (rawCoordinate W - 1)
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentB then
        rawCoordinate W
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentC then
        algebraMap Int (referenceRaw.rawAlgebra W) 2
      else 0 :=
  by
    cases a <;> simp [rigidLawEquationCore]

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakLawEquationCore_supportAtom :
    weakLawEquationCore.supportAtom =
      AAT.AG.FiniteModel.FiniteAtom.componentA :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongLawEquationCore_supportAtom :
    strongLawEquationCore.supportAtom =
      AAT.AG.FiniteModel.FiniteAtom.componentA :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem rigidLawEquationCore_supportAtom :
    rigidLawEquationCore.supportAtom =
      AAT.AG.FiniteModel.FiniteAtom.componentA :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakLawEquationCore_supportLawIndex :
    weakLawEquationCore.supportLawIndex = PUnit.unit :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongLawEquationCore_supportLawIndex :
    strongLawEquationCore.supportLawIndex = PUnit.unit :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem rigidLawEquationCore_supportLawIndex :
    rigidLawEquationCore.supportLawIndex = PUnit.unit :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def weakSchemeBridge :
    SemanticLawEquationSchemeBridge referenceRaw weakLawEquationCore where
  toRawPresentation W := RingEquiv.refl (referenceRaw.rawAlgebra W)

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def strongSchemeBridge :
    SemanticLawEquationSchemeBridge referenceRaw strongLawEquationCore where
  toRawPresentation W := RingEquiv.refl (referenceRaw.rawAlgebra W)

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def rigidSchemeBridge :
    SemanticLawEquationSchemeBridge referenceRaw rigidLawEquationCore where
  toRawPresentation W := RingEquiv.refl (referenceRaw.rawAlgebra W)

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakSchemeBridge_toRawPresentation
    (W : referenceSite.category) :
    weakSchemeBridge.toRawPresentation W =
      RingEquiv.refl (referenceRaw.rawAlgebra W) :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongSchemeBridge_toRawPresentation
    (W : referenceSite.category) :
    strongSchemeBridge.toRawPresentation W =
      RingEquiv.refl (referenceRaw.rawAlgebra W) :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem rigidSchemeBridge_toRawPresentation
    (W : referenceSite.category) :
    rigidSchemeBridge.toRawPresentation W =
      RingEquiv.refl (referenceRaw.rawAlgebra W) :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakSchemeBridge_valid :
    IsSemanticLawEquationSchemeBridge
      referenceRaw weakLawEquationCore weakSchemeBridge := by
  constructor
  · intro source target f x
    have hn := referenceRaw.toRingedSite.canonical.naturality f.op
    have ha := congrArg (fun q => q.right x) hn
    change
      (referenceRaw.toRingedSite.canonical.app (op source)).right
          ((referenceRaw.restrictionStable f).quotientDesc x) =
        (referenceRaw.toRingedSite.structureSheaf.val.map f.op).right
          ((referenceRaw.toRingedSite.canonical.app (op target)).right x)
    simpa only [CommRingCat.comp_apply,
      RawAmbientRestrictionSystem.toRingedSite_raw] using ha
  · intro W
    exact { canonical_isIso := canonical_component_isIso W }

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongSchemeBridge_valid :
    IsSemanticLawEquationSchemeBridge
      referenceRaw strongLawEquationCore strongSchemeBridge := by
  constructor
  · intro source target f x
    have hn := referenceRaw.toRingedSite.canonical.naturality f.op
    have ha := congrArg (fun q => q.right x) hn
    change
      (referenceRaw.toRingedSite.canonical.app (op source)).right
          ((referenceRaw.restrictionStable f).quotientDesc x) =
        (referenceRaw.toRingedSite.structureSheaf.val.map f.op).right
          ((referenceRaw.toRingedSite.canonical.app (op target)).right x)
    simpa only [CommRingCat.comp_apply,
      RawAmbientRestrictionSystem.toRingedSite_raw] using ha
  · intro W
    exact { canonical_isIso := canonical_component_isIso W }

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem rigidSchemeBridge_valid :
    IsSemanticLawEquationSchemeBridge
      referenceRaw rigidLawEquationCore rigidSchemeBridge := by
  constructor
  · intro source target f x
    have hn := referenceRaw.toRingedSite.canonical.naturality f.op
    have ha := congrArg (fun q => q.right x) hn
    change
      (referenceRaw.toRingedSite.canonical.app (op source)).right
          ((referenceRaw.restrictionStable f).quotientDesc x) =
        (referenceRaw.toRingedSite.structureSheaf.val.map f.op).right
          ((referenceRaw.toRingedSite.canonical.app (op target)).right x)
    simpa only [CommRingCat.comp_apply,
      RawAmbientRestrictionSystem.toRingedSite_raw] using ha
  · intro W
    exact { canonical_isIso := canonical_component_isIso W }

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def weakReading :
    ClosedEquationalLawReading referenceRaw referenceScheme :=
  ClosedEquationalLawReading.ofSemanticCore
    referenceRaw referenceScheme weakLawEquationCore weakSchemeBridge

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakReading_eq :
    weakReading =
      ClosedEquationalLawReading.ofSemanticCore
        referenceRaw referenceScheme weakLawEquationCore weakSchemeBridge :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def strongReading :
    ClosedEquationalLawReading referenceRaw referenceScheme :=
  ClosedEquationalLawReading.ofSemanticCore
    referenceRaw referenceScheme strongLawEquationCore strongSchemeBridge

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongReading_eq :
    strongReading =
      ClosedEquationalLawReading.ofSemanticCore
        referenceRaw referenceScheme strongLawEquationCore strongSchemeBridge :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def rigidReading :
    ClosedEquationalLawReading referenceRaw referenceScheme :=
  ClosedEquationalLawReading.ofSemanticCore
    referenceRaw referenceScheme rigidLawEquationCore rigidSchemeBridge

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem rigidReading_eq :
    rigidReading =
      ClosedEquationalLawReading.ofSemanticCore
        referenceRaw referenceScheme rigidLawEquationCore rigidSchemeBridge :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakReading_valid :
    IsClosedEquationalLawReading referenceRaw referenceScheme weakReading :=
  ClosedEquationalLawReading.ofSemanticCore_valid
    referenceRaw referenceScheme weakLawEquationCore weakSchemeBridge

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongReading_valid :
    IsClosedEquationalLawReading referenceRaw referenceScheme strongReading :=
  ClosedEquationalLawReading.ofSemanticCore_valid
    referenceRaw referenceScheme strongLawEquationCore strongSchemeBridge

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem rigidReading_valid :
    IsClosedEquationalLawReading referenceRaw referenceScheme rigidReading :=
  ClosedEquationalLawReading.ofSemanticCore_valid
    referenceRaw referenceScheme rigidLawEquationCore rigidSchemeBridge

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakReading_requiredClosed :
    RequiredClosed referenceRaw referenceScheme weakReading :=
  ClosedEquationalLawReading.ofSemanticCore_requiredClosed
    referenceRaw referenceScheme weakLawEquationCore weakSchemeBridge

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongReading_requiredClosed :
    RequiredClosed referenceRaw referenceScheme strongReading :=
  ClosedEquationalLawReading.ofSemanticCore_requiredClosed
    referenceRaw referenceScheme strongLawEquationCore strongSchemeBridge

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem rigidReading_requiredClosed :
    RequiredClosed referenceRaw referenceScheme rigidReading :=
  ClosedEquationalLawReading.ofSemanticCore_requiredClosed
    referenceRaw referenceScheme rigidLawEquationCore rigidSchemeBridge

private theorem reference_ofIdealTop_span_comap_eq_bot_iff
    (equation : AAT.AG.FiniteModel.carrier.Atom →
      Γ(referenceScheme.underlying, ⊤))
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ referenceScheme.underlying) :
    (Scheme.IdealSheafData.ofIdealTop
        (X := referenceScheme.underlying)
        (Ideal.span (Set.range equation))).comap s = ⊥ ↔
      ∀ a, s.appTop (equation a) = 0 := by
  haveI : IsAffine referenceScheme.underlying := by
    rw [referenceScheme_underlying, ambientScheme_eq]
    infer_instance
  let e := Scheme.IdealSheafData.equivOfIsAffine
    (X := referenceScheme.underlying)
  constructor
  · intro h a
    have hcomap :
        (Scheme.IdealSheafData.ofIdealTop
            (X := referenceScheme.underlying)
            (Ideal.span (Set.range equation))).comap s ≤ ⊥ := h.le
    have hle := (Scheme.IdealSheafData.map_gc s _ _).mp hcomap
    change Scheme.IdealSheafData.ofIdealTop
      (Ideal.span (Set.range equation)) ≤
        (⊥ : T.IdealSheafData).map s at hle
    rw [Scheme.IdealSheafData.map_bot,
      Scheme.ker_of_isAffine] at hle
    have hideal :
        Ideal.span (Set.range equation) ≤ RingHom.ker s.appTop.hom := by
      simpa [e] using e.toOrderIso.monotone hle
    exact hideal (Ideal.subset_span ⟨a, rfl⟩)
  · intro h
    apply le_antisymm
    · apply (Scheme.IdealSheafData.map_gc s _ _).mpr
      change Scheme.IdealSheafData.ofIdealTop
        (Ideal.span (Set.range equation)) ≤
          (⊥ : T.IdealSheafData).map s
      rw [Scheme.IdealSheafData.map_bot,
        Scheme.ker_of_isAffine]
      have hideal :
          Ideal.span (Set.range equation) ≤ RingHom.ker s.appTop.hom := by
        apply Ideal.span_le.mpr
        rintro _ ⟨a, rfl⟩
        exact h a
      apply Scheme.IdealSheafData.le_of_isAffine
      simpa using hideal
    · exact bot_le

private theorem referenceCore_lawIdealExact
    (G : SemanticLawEquationWitnessIdealCore referenceSite)
    (B : SemanticLawEquationSchemeBridge referenceRaw G)
    (i : referenceSite.equationSystem.toLegacyLawUniverse.Index) :
    LawIdealExact referenceRaw referenceScheme
      (ClosedEquationalLawReading.ofSemanticCore referenceRaw
        referenceScheme G B)
      (ClosedEquationalLawReading.ofSemanticCore_witnessCompatible
        referenceRaw referenceScheme G B)
      i (Set.mem_univ i) := by
  intro T s
  change (GeometricLawReading.ofSemanticCore referenceRaw referenceScheme
    G B).HoldsOn s i ↔ _
  rw [GeometricLawReading.ofSemanticCore_holdsOn]
  have hsheaf := lawWitnessIdealSheaf_ofGlobalSections referenceRaw
    referenceScheme
    (ClosedEquationalLawReading.ofSemanticCore referenceRaw
      referenceScheme G B)
    (ClosedEquationalLawReading.ofSemanticCore_witnessCompatible
      referenceRaw referenceScheme G B)
    i (Set.mem_univ i)
    (semanticCoreGlobalEquation referenceRaw referenceScheme G B i)
    (by
      exact ClosedEquationalLawReading.ofSemanticCore_witness referenceRaw
        referenceScheme G B i (Set.mem_univ i))
  rw [hsheaf]
  exact (reference_ofIdealTop_span_comap_eq_bot_iff
    (semanticCoreGlobalEquation referenceRaw referenceScheme G B i) s).symm

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakReading_requiredLawIdealExact :
    RequiredLawIdealExact referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed :=
  by
    intro i hi
    cases i
    intro T s
    simpa only [weakReading] using
      referenceCore_lawIdealExact weakLawEquationCore weakSchemeBridge
        PUnit.unit (T := T) s

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongReading_requiredLawIdealExact :
    RequiredLawIdealExact referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed :=
  by
    intro i hi
    cases i
    intro T s
    simpa only [strongReading] using
      referenceCore_lawIdealExact strongLawEquationCore strongSchemeBridge
        PUnit.unit (T := T) s

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem rigidReading_requiredLawIdealExact :
    RequiredLawIdealExact referenceRaw referenceScheme
      rigidReading rigidReading_valid rigidReading_requiredClosed :=
  by
    intro i hi
    cases i
    intro T s
    simpa only [rigidReading] using
      referenceCore_lawIdealExact rigidLawEquationCore rigidSchemeBridge
        PUnit.unit (T := T) s

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable abbrev weakIdealSheaf :
    referenceScheme.underlying.IdealSheafData :=
  lawGeneratedIdealSheaf referenceRaw referenceScheme
    weakReading weakReading_valid weakReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakIdealSheaf_eq :
    weakIdealSheaf =
      lawGeneratedIdealSheaf referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable abbrev strongIdealSheaf :
    referenceScheme.underlying.IdealSheafData :=
  lawGeneratedIdealSheaf referenceRaw referenceScheme
    strongReading strongReading_valid strongReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongIdealSheaf_eq :
    strongIdealSheaf =
      lawGeneratedIdealSheaf referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable abbrev rigidIdealSheaf :
    referenceScheme.underlying.IdealSheafData :=
  lawGeneratedIdealSheaf referenceRaw referenceScheme
    rigidReading rigidReading_valid rigidReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem rigidIdealSheaf_eq :
    rigidIdealSheaf =
      lawGeneratedIdealSheaf referenceRaw referenceScheme
        rigidReading rigidReading_valid rigidReading_requiredClosed :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable abbrev weakLocus : AlgebraicGeometry.Scheme :=
  lawfulClosedSubscheme referenceRaw referenceScheme
    weakReading weakReading_valid weakReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakLocus_eq :
    weakLocus =
      lawfulClosedSubscheme referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable abbrev strongLocus : AlgebraicGeometry.Scheme :=
  lawfulClosedSubscheme referenceRaw referenceScheme
    strongReading strongReading_valid strongReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongLocus_eq :
    strongLocus =
      lawfulClosedSubscheme referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable abbrev rigidLocus : AlgebraicGeometry.Scheme :=
  lawfulClosedSubscheme referenceRaw referenceScheme
    rigidReading rigidReading_valid rigidReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem rigidLocus_eq :
    rigidLocus =
      lawfulClosedSubscheme referenceRaw referenceScheme
        rigidReading rigidReading_valid rigidReading_requiredClosed :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable abbrev weakImmersion :
    weakLocus ⟶ referenceScheme.underlying :=
  lawfulClosedImmersion referenceRaw referenceScheme
    weakReading weakReading_valid weakReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakImmersion_eq :
    weakImmersion =
      lawfulClosedImmersion referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable abbrev strongImmersion :
    strongLocus ⟶ referenceScheme.underlying :=
  lawfulClosedImmersion referenceRaw referenceScheme
    strongReading strongReading_valid strongReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongImmersion_eq :
    strongImmersion =
      lawfulClosedImmersion referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable abbrev rigidImmersion :
    rigidLocus ⟶ referenceScheme.underlying :=
  lawfulClosedImmersion referenceRaw referenceScheme
    rigidReading rigidReading_valid rigidReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem rigidImmersion_eq :
    rigidImmersion =
      lawfulClosedImmersion referenceRaw referenceScheme
        rigidReading rigidReading_valid rigidReading_requiredClosed :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def ambientGlobalSectionsIso :
  Γ(referenceScheme.underlying, ⊤) ≅
      CommRingCat.of AmbientRing :=
  AlgebraicGeometry.Scheme.ΓSpecIso
    (CommRingCat.of AmbientRing)

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem ambientGlobalSectionsIso_eq :
    ambientGlobalSectionsIso =
      AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of AmbientRing) :=
  rfl

private theorem ambientGlobalSectionsIso_unit
    (x : referenceRaw.rawAlgebra baseContext) :
    ambientGlobalSectionsIso.hom
        (ambientDecoration.interpretation
          ((sheafificationUnitAlgHom referenceRaw baseContext) x)) =
      baseRawAlgebraIso.hom x := by
  letI := canonical_component_isIso baseContext
  simp only [ambientGlobalSectionsIso, ambientDecoration,
    AATReadingDecoration.pullback_interpretation,
    AATReadingDecoration.ofContext_interpretation,
    baseChartDomainIso, AlgebraicGeometry.Scheme.Spec.mapIso_inv]
  change
    (AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of AmbientRing)).hom
        (((AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing referenceRaw baseContext)).inv ≫
          (AlgebraicGeometry.Scheme.Spec.map
            baseSectionRingIso.hom.op).appTop)
          ((sheafificationUnitAlgHom referenceRaw baseContext) x)) =
      baseRawAlgebraIso.hom x
  rw [AlgebraicGeometry.Scheme.Spec_map]
  simp only [CommRingCat.comp_apply]
  have hΓ := congrArg
    (fun q => q.hom
      ((AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing referenceRaw baseContext)).inv
          ((sheafificationUnitAlgHom referenceRaw baseContext) x)))
    (AlgebraicGeometry.Scheme.ΓSpecIso_naturality
      baseSectionRingIso.hom)
  change
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of AmbientRing)).hom
        ((AlgebraicGeometry.Spec.map baseSectionRingIso.hom).appTop
          ((AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing referenceRaw baseContext)).inv
            ((sheafificationUnitAlgHom referenceRaw baseContext) x))) =
      baseSectionRingIso.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw baseContext)).hom
          ((AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing referenceRaw baseContext)).inv
            ((sheafificationUnitAlgHom referenceRaw baseContext) x))) at hΓ
  calc
    _ = baseSectionRingIso.hom
        ((sheafificationUnitAlgHom referenceRaw baseContext) x) := by
      simpa only [CommRingCat.comp_apply, Iso.inv_hom_id_apply,
        Quiver.Hom.unop_op] using hΓ
    _ = baseRawAlgebraIso.hom x := by
      change baseRawAlgebraIso.hom
          ((inv (referenceRaw.toRingedSite.canonical.app
            (op baseContext)).right)
            ((referenceRaw.toRingedSite.canonical.app
              (op baseContext)).right x)) = _
      have hcancel := congrArg
        (fun q => q x)
        (IsIso.hom_inv_id
          (referenceRaw.toRingedSite.canonical.app
            (op baseContext)).right)
      rw [show (inv (referenceRaw.toRingedSite.canonical.app
          (op baseContext)).right)
          ((referenceRaw.toRingedSite.canonical.app
            (op baseContext)).right x) = x by
        simpa only [CommRingCat.comp_apply, Category.id_comp] using hcancel]

private theorem weakGlobalEquation_image
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    ambientGlobalSectionsIso.hom
        (semanticCoreGlobalEquation referenceRaw referenceScheme
          weakLawEquationCore weakSchemeBridge PUnit.unit a) =
      baseRawAlgebraIso.hom
        (weakLawEquationCore.violationWitness baseContext PUnit.unit a) := by
  change ambientGlobalSectionsIso.hom
      (ambientDecoration.interpretation
        (weakSchemeBridge.toSheafifiedSection baseContext
          (weakLawEquationCore.violationWitness baseContext PUnit.unit a))) = _
  simpa [weakSchemeBridge,
    SemanticLawEquationSchemeBridge.toSheafifiedSection] using
      ambientGlobalSectionsIso_unit
        (weakLawEquationCore.violationWitness baseContext PUnit.unit a)

private theorem strongGlobalEquation_image
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    ambientGlobalSectionsIso.hom
        (semanticCoreGlobalEquation referenceRaw referenceScheme
          strongLawEquationCore strongSchemeBridge PUnit.unit a) =
      baseRawAlgebraIso.hom
        (strongLawEquationCore.violationWitness baseContext PUnit.unit a) := by
  change ambientGlobalSectionsIso.hom
      (ambientDecoration.interpretation
        (strongSchemeBridge.toSheafifiedSection baseContext
          (strongLawEquationCore.violationWitness baseContext PUnit.unit a))) = _
  simpa [strongSchemeBridge,
    SemanticLawEquationSchemeBridge.toSheafifiedSection] using
      ambientGlobalSectionsIso_unit
        (strongLawEquationCore.violationWitness baseContext PUnit.unit a)

private theorem rigidGlobalEquation_image
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    ambientGlobalSectionsIso.hom
        (semanticCoreGlobalEquation referenceRaw referenceScheme
          rigidLawEquationCore rigidSchemeBridge PUnit.unit a) =
      baseRawAlgebraIso.hom
        (rigidLawEquationCore.violationWitness baseContext PUnit.unit a) := by
  change ambientGlobalSectionsIso.hom
      (ambientDecoration.interpretation
        (rigidSchemeBridge.toSheafifiedSection baseContext
          (rigidLawEquationCore.violationWitness baseContext PUnit.unit a))) = _
  simpa [rigidSchemeBridge,
    SemanticLawEquationSchemeBridge.toSheafifiedSection] using
      ambientGlobalSectionsIso_unit
        (rigidLawEquationCore.violationWitness baseContext PUnit.unit a)

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakGlobalEquation_eq
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    ambientGlobalSectionsIso.hom
        (semanticCoreGlobalEquation
          referenceRaw referenceScheme
          weakLawEquationCore weakSchemeBridge PUnit.unit a) =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        coordinate * (coordinate - 1)
      else 0 := by
  rw [weakGlobalEquation_image]
  change baseRawAlgebraIso.hom
      (match a with
      | AAT.AG.FiniteModel.FiniteAtom.componentA =>
          rawCoordinate baseContext * (rawCoordinate baseContext - 1)
      | _ => 0) = _
  cases a
  case componentA =>
    simp only [↓reduceIte]
    change baseRawAlgebraIso.hom
        (rawCoordinate baseContext * (rawCoordinate baseContext - 1)) =
      coordinate * (coordinate - 1)
    rw [map_mul, map_sub, map_one, baseRawAlgebraIso_coordinate]
  all_goals simp

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongGlobalEquation_eq
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    ambientGlobalSectionsIso.hom
        (semanticCoreGlobalEquation
          referenceRaw referenceScheme
          strongLawEquationCore strongSchemeBridge PUnit.unit a) =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        coordinate * (coordinate - 1)
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentB then
        coordinate
      else 0 := by
  rw [strongGlobalEquation_image]
  change baseRawAlgebraIso.hom
      (match a with
      | AAT.AG.FiniteModel.FiniteAtom.componentA =>
          rawCoordinate baseContext * (rawCoordinate baseContext - 1)
      | AAT.AG.FiniteModel.FiniteAtom.componentB => rawCoordinate baseContext
      | _ => 0) = _
  cases a
  case componentA =>
    simp only [↓reduceIte]
    change baseRawAlgebraIso.hom
        (rawCoordinate baseContext * (rawCoordinate baseContext - 1)) =
      coordinate * (coordinate - 1)
    rw [map_mul, map_sub, map_one, baseRawAlgebraIso_coordinate]
  case componentB =>
    rw [if_neg (by simp), if_pos rfl]
    exact baseRawAlgebraIso_coordinate
  all_goals simp

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem rigidGlobalEquation_eq
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    ambientGlobalSectionsIso.hom
        (semanticCoreGlobalEquation
          referenceRaw referenceScheme
          rigidLawEquationCore rigidSchemeBridge PUnit.unit a) =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        coordinate * (coordinate - 1)
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentB then
        coordinate
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentC then
        MvPolynomial.C 2
      else 0 := by
  rw [rigidGlobalEquation_image]
  change baseRawAlgebraIso.hom
      (match a with
      | AAT.AG.FiniteModel.FiniteAtom.componentA =>
          rawCoordinate baseContext * (rawCoordinate baseContext - 1)
      | AAT.AG.FiniteModel.FiniteAtom.componentB => rawCoordinate baseContext
      | AAT.AG.FiniteModel.FiniteAtom.componentC =>
          algebraMap Int (referenceRaw.rawAlgebra baseContext) 2
      | _ => 0) = _
  cases a
  case componentA =>
    simp only [↓reduceIte]
    change baseRawAlgebraIso.hom
        (rawCoordinate baseContext * (rawCoordinate baseContext - 1)) =
      coordinate * (coordinate - 1)
    rw [map_mul, map_sub, map_one, baseRawAlgebraIso_coordinate]
  case componentB =>
    rw [if_neg (by simp), if_pos rfl]
    exact baseRawAlgebraIso_coordinate
  case componentC =>
    rw [if_neg (by simp), if_neg (by simp), if_pos rfl]
    change baseRawAlgebraIso.hom
        (algebraMap Int (referenceRaw.rawAlgebra baseContext) 2) =
      algebraMap Int AmbientRing 2
    simp only [map_ofNat]
  all_goals simp


/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
def weakAmbientIdeal : Ideal AmbientRing :=
  Ideal.span {coordinate * (coordinate - 1)}

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakAmbientIdeal_eq :
    weakAmbientIdeal =
      Ideal.span {coordinate * (coordinate - 1)} :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
def strongAmbientIdeal : Ideal AmbientRing :=
  Ideal.span {coordinate}

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongAmbientIdeal_eq :
    strongAmbientIdeal = Ideal.span {coordinate} :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
def rigidAmbientIdeal : Ideal AmbientRing :=
  Ideal.span {coordinate, MvPolynomial.C 2}

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem rigidAmbientIdeal_eq :
    rigidAmbientIdeal =
      Ideal.span {coordinate, MvPolynomial.C 2} :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
def weakLeftIdeal : Ideal (Localization.Away leftGenerator) :=
  Ideal.span
    {algebraMap AmbientRing (Localization.Away leftGenerator)
      (coordinate * (coordinate - 1))}

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakLeftIdeal_eq :
    weakLeftIdeal =
      Ideal.span
        {algebraMap AmbientRing (Localization.Away leftGenerator)
          (coordinate * (coordinate - 1))} :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
def weakRightIdeal : Ideal (Localization.Away rightGenerator) :=
  Ideal.span
    {algebraMap AmbientRing (Localization.Away rightGenerator)
      (coordinate * (coordinate - 1))}

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakRightIdeal_eq :
    weakRightIdeal =
      Ideal.span
        {algebraMap AmbientRing (Localization.Away rightGenerator)
          (coordinate * (coordinate - 1))} :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
def weakOverlapIdeal : Ideal (Localization.Away overlapGenerator) :=
  Ideal.span
    {algebraMap AmbientRing (Localization.Away overlapGenerator)
      (coordinate * (coordinate - 1))}

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakOverlapIdeal_eq :
    weakOverlapIdeal =
      Ideal.span
        {algebraMap AmbientRing (Localization.Away overlapGenerator)
          (coordinate * (coordinate - 1))} :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
def strongLeftIdeal : Ideal (Localization.Away leftGenerator) :=
  Ideal.span
    {algebraMap AmbientRing (Localization.Away leftGenerator) coordinate}

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongLeftIdeal_eq :
    strongLeftIdeal =
      Ideal.span
        {algebraMap AmbientRing
          (Localization.Away leftGenerator) coordinate} :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
def strongRightIdeal : Ideal (Localization.Away rightGenerator) :=
  Ideal.span
    {algebraMap AmbientRing (Localization.Away rightGenerator) coordinate}

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongRightIdeal_eq :
    strongRightIdeal =
      Ideal.span
        {algebraMap AmbientRing
          (Localization.Away rightGenerator) coordinate} :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
def strongOverlapIdeal : Ideal (Localization.Away overlapGenerator) :=
  Ideal.span
    {algebraMap AmbientRing (Localization.Away overlapGenerator) coordinate}

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongOverlapIdeal_eq :
    strongOverlapIdeal =
      Ideal.span
        {algebraMap AmbientRing
          (Localization.Away overlapGenerator) coordinate} :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def leftChartGlobalSectionsIso :
  Γ(leftChart.domain, ⊤) ≅
      CommRingCat.of (Localization.Away leftGenerator) :=
  AlgebraicGeometry.Scheme.ΓSpecIso
      (SheafifiedSectionRing referenceRaw leftContext) ≪≫
    leftSectionRingIso

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem leftChartGlobalSectionsIso_eq :
    leftChartGlobalSectionsIso =
      AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw leftContext) ≪≫
        leftSectionRingIso :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def rightChartGlobalSectionsIso :
  Γ(rightChart.domain, ⊤) ≅
      CommRingCat.of (Localization.Away rightGenerator) :=
  AlgebraicGeometry.Scheme.ΓSpecIso
      (SheafifiedSectionRing referenceRaw rightContext) ≪≫
    rightSectionRingIso

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem rightChartGlobalSectionsIso_eq :
    rightChartGlobalSectionsIso =
      AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw rightContext) ≪≫
        rightSectionRingIso :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def actualOverlapGlobalSectionsIso :
    Γ(referenceScheme.atlas.actualOverlap
        referenceRaw leftIndex rightIndex, ⊤) ≅
      CommRingCat.of (Localization.Away overlapGenerator) :=
  (asIso actualOverlapIso.inv.appTop) ≪≫
    AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of (Localization.Away overlapGenerator))

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem actualOverlapGlobalSectionsIso_eq :
    actualOverlapGlobalSectionsIso =
      (asIso actualOverlapIso.inv.appTop) ≪≫
        AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of (Localization.Away overlapGenerator)) :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def ambientTopAffineOpen :
    referenceScheme.underlying.affineOpens := by
  letI : IsAffine referenceScheme.underlying := by
    rw [referenceScheme_underlying, ambientScheme_eq]
    infer_instance
  exact ⟨⊤, isAffineOpen_top _⟩

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem ambientTopAffineOpen_obj :
    ambientTopAffineOpen.1 = ⊤ :=
  rfl

private theorem reference_local_top_eq_span
    (G : SemanticLawEquationWitnessIdealCore referenceSite)
    (B : SemanticLawEquationSchemeBridge referenceRaw G)
    (hi : (ClosedEquationalLawReading.ofSemanticCore referenceRaw
      referenceScheme G B).closed PUnit.unit) :
    localLawWitnessIdeal referenceRaw referenceScheme
        ((ClosedEquationalLawReading.ofSemanticCore referenceRaw
          referenceScheme G B).witness PUnit.unit hi)
        ambientTopAffineOpen =
      Ideal.span (Set.range (semanticCoreGlobalEquation referenceRaw
        referenceScheme G B PUnit.unit)) := by
  let reading := ClosedEquationalLawReading.ofSemanticCore referenceRaw
    referenceScheme G B
  rw [← lawWitnessIdealSheaf_ideal referenceRaw referenceScheme
    reading
    (ClosedEquationalLawReading.ofSemanticCore_valid referenceRaw
      referenceScheme G B).witness_compatible PUnit.unit hi
    ambientTopAffineOpen]
  rw [lawWitnessIdealSheaf_ofGlobalSections referenceRaw referenceScheme
    reading
    (ClosedEquationalLawReading.ofSemanticCore_valid referenceRaw
      referenceScheme G B).witness_compatible PUnit.unit hi
    (semanticCoreGlobalEquation referenceRaw referenceScheme G B PUnit.unit)]
  · rw [Scheme.IdealSheafData.ofIdealTop_ideal]
    simp [ambientTopAffineOpen]
  · simpa only [reading] using
      ClosedEquationalLawReading.ofSemanticCore_witness referenceRaw
        referenceScheme G B PUnit.unit hi

private theorem reference_generated_top_eq_span
    (G : SemanticLawEquationWitnessIdealCore referenceSite)
    (B : SemanticLawEquationSchemeBridge referenceRaw G) :
    (lawGeneratedIdealSheaf referenceRaw referenceScheme
      (ClosedEquationalLawReading.ofSemanticCore referenceRaw
        referenceScheme G B)
      (ClosedEquationalLawReading.ofSemanticCore_valid referenceRaw
        referenceScheme G B)
      (ClosedEquationalLawReading.ofSemanticCore_requiredClosed referenceRaw
        referenceScheme G B)).ideal ambientTopAffineOpen =
      Ideal.span (Set.range (semanticCoreGlobalEquation referenceRaw
        referenceScheme G B PUnit.unit)) := by
  let reading := ClosedEquationalLawReading.ofSemanticCore referenceRaw
    referenceScheme G B
  let valid := ClosedEquationalLawReading.ofSemanticCore_valid referenceRaw
    referenceScheme G B
  let required :=
    ClosedEquationalLawReading.ofSemanticCore_requiredClosed referenceRaw
      referenceScheme G B
  rw [lawGeneratedIdealSheaf_ideal]
  apply le_antisymm
  · refine iSup_le fun i => ?_
    cases i.1
    exact (reference_local_top_eq_span G B _).le
  · let idx : {i : referenceSite.equationSystem.Index //
        referenceSite.equationSystem.Required i ∧
          reading.selected ambientTopAffineOpen i} :=
      ⟨PUnit.unit,
        referenceSite_equation_required PUnit.unit,
        ClosedEquationalLawReading.ofSemanticCore_selected referenceRaw
          referenceScheme G B ambientTopAffineOpen PUnit.unit⟩
    have h := le_iSup (fun i :
      {i : referenceSite.equationSystem.Index //
          referenceSite.equationSystem.Required i ∧
            reading.selected ambientTopAffineOpen i} =>
        localLawWitnessIdeal referenceRaw referenceScheme
          (reading.witness i.1 (required.closed i.1 i.2.1))
          ambientTopAffineOpen) idx
    rw [reference_local_top_eq_span] at h
    exact h

private theorem weak_generated_top_eq_span :
    (lawGeneratedIdealSheaf referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed).ideal
        ambientTopAffineOpen =
      Ideal.span (Set.range (semanticCoreGlobalEquation referenceRaw
        referenceScheme weakLawEquationCore weakSchemeBridge PUnit.unit)) := by
  simpa only [weakReading, weakReading_valid, weakReading_requiredClosed] using
    reference_generated_top_eq_span weakLawEquationCore weakSchemeBridge

private theorem strong_generated_top_eq_span :
    (lawGeneratedIdealSheaf referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed).ideal
        ambientTopAffineOpen =
      Ideal.span (Set.range (semanticCoreGlobalEquation referenceRaw
        referenceScheme strongLawEquationCore strongSchemeBridge PUnit.unit)) := by
  simpa only [strongReading, strongReading_valid, strongReading_requiredClosed] using
    reference_generated_top_eq_span strongLawEquationCore strongSchemeBridge

private theorem rigid_generated_top_eq_span :
    (lawGeneratedIdealSheaf referenceRaw referenceScheme
      rigidReading rigidReading_valid rigidReading_requiredClosed).ideal
        ambientTopAffineOpen =
      Ideal.span (Set.range (semanticCoreGlobalEquation referenceRaw
        referenceScheme rigidLawEquationCore rigidSchemeBridge PUnit.unit)) := by
  simpa only [rigidReading, rigidReading_valid, rigidReading_requiredClosed] using
    reference_generated_top_eq_span rigidLawEquationCore rigidSchemeBridge

private theorem reference_generated_eq_witness
    (G : SemanticLawEquationWitnessIdealCore referenceSite)
    (B : SemanticLawEquationSchemeBridge referenceRaw G) :
    lawGeneratedIdealSheaf referenceRaw referenceScheme
        (ClosedEquationalLawReading.ofSemanticCore referenceRaw
          referenceScheme G B)
        (ClosedEquationalLawReading.ofSemanticCore_valid referenceRaw
          referenceScheme G B)
        (ClosedEquationalLawReading.ofSemanticCore_requiredClosed referenceRaw
          referenceScheme G B) =
      lawWitnessIdealSheaf referenceRaw referenceScheme
        (ClosedEquationalLawReading.ofSemanticCore referenceRaw
          referenceScheme G B)
        (ClosedEquationalLawReading.ofSemanticCore_witnessCompatible referenceRaw
          referenceScheme G B)
        PUnit.unit (show PUnit.unit ∈
          (Set.univ : Set referenceSite.equationSystem.toLegacyLawUniverse.Index) from
            Set.mem_univ PUnit.unit) := by
  letI : IsAffine referenceScheme.underlying := by
    rw [referenceScheme_underlying, ambientScheme_eq]
    infer_instance
  apply Scheme.IdealSheafData.ext_of_isAffine
  let hi : PUnit.unit ∈
      (Set.univ : Set referenceSite.equationSystem.toLegacyLawUniverse.Index) :=
    Set.mem_univ PUnit.unit
  have hw := lawWitnessIdealSheaf_ofGlobalSections referenceRaw
    referenceScheme
    (ClosedEquationalLawReading.ofSemanticCore referenceRaw
      referenceScheme G B)
    (ClosedEquationalLawReading.ofSemanticCore_witnessCompatible referenceRaw
      referenceScheme G B)
    PUnit.unit hi
    (semanticCoreGlobalEquation referenceRaw referenceScheme G B PUnit.unit)
    (ClosedEquationalLawReading.ofSemanticCore_witness referenceRaw
      referenceScheme G B PUnit.unit hi)
  rw [hw, Scheme.IdealSheafData.ofIdealTop_ideal]
  simpa [ambientTopAffineOpen] using reference_generated_top_eq_span G B

private theorem reference_generated_comap_chart
    (G : SemanticLawEquationWitnessIdealCore referenceSite)
    (B : SemanticLawEquationSchemeBridge referenceRaw G)
    (hB : IsSemanticLawEquationSchemeBridge referenceRaw G B)
    (j : referenceScheme.atlas.Index) :
    (lawGeneratedIdealSheaf referenceRaw referenceScheme
      (ClosedEquationalLawReading.ofSemanticCore referenceRaw
        referenceScheme G B)
      (ClosedEquationalLawReading.ofSemanticCore_valid referenceRaw
        referenceScheme G B)
      (ClosedEquationalLawReading.ofSemanticCore_requiredClosed referenceRaw
        referenceScheme G B)).comap
        (referenceScheme.atlas.chart j).map =
      Scheme.IdealSheafData.ofIdealTop
        (X := (referenceScheme.atlas.chart j).domain)
        (Ideal.map
          (AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing referenceRaw
              (referenceScheme.atlas.chart j).context)).inv.hom
          (Ideal.map
            (B.toSheafifiedSection
              (referenceScheme.atlas.chart j).context)
            (G.lawWitnessIdeal
              (referenceScheme.atlas.chart j).context PUnit.unit))) := by
  rw [reference_generated_eq_witness G B]
  exact (semanticCoreIdealSheaf_realized referenceRaw referenceScheme
    G B hB).2 j PUnit.unit

private theorem referenceIdeal_left_raw
    (G : SemanticLawEquationWitnessIdealCore referenceSite)
    (B : SemanticLawEquationSchemeBridge referenceRaw G)
    (hB : IsSemanticLawEquationSchemeBridge referenceRaw G B) :
    Ideal.map leftChartGlobalSectionsIso.hom.hom
        (((lawGeneratedIdealSheaf referenceRaw referenceScheme
          (ClosedEquationalLawReading.ofSemanticCore referenceRaw
            referenceScheme G B)
          (ClosedEquationalLawReading.ofSemanticCore_valid referenceRaw
            referenceScheme G B)
          (ClosedEquationalLawReading.ofSemanticCore_requiredClosed referenceRaw
            referenceScheme G B)).comap leftChart.map).ideal
          ⟨⊤, @isAffineOpen_top leftChart.domain
            leftChart.domain_isAffine⟩) =
      Ideal.map (leftRawAlgebraIso.hom.hom.comp
        (B.toRawPresentation leftContext).toRingHom)
        (G.lawWitnessIdeal leftContext PUnit.unit) := by
  letI := (hB.presentation_stable leftContext).canonical_isIso
  have hreal := congrArg
    (fun I : leftChart.domain.IdealSheafData =>
      I.ideal ⟨⊤, @isAffineOpen_top leftChart.domain
        leftChart.domain_isAffine⟩)
    (reference_generated_comap_chart G B hB leftIndex)
  change
    (((lawGeneratedIdealSheaf referenceRaw referenceScheme
      (ClosedEquationalLawReading.ofSemanticCore referenceRaw
        referenceScheme G B)
      (ClosedEquationalLawReading.ofSemanticCore_valid referenceRaw
        referenceScheme G B)
      (ClosedEquationalLawReading.ofSemanticCore_requiredClosed referenceRaw
        referenceScheme G B)).comap leftChart.map).ideal
      ⟨⊤, @isAffineOpen_top leftChart.domain leftChart.domain_isAffine⟩) =
    (Scheme.IdealSheafData.ofIdealTop
      (X := leftChart.domain)
      (Ideal.map
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw leftContext)).inv.hom
        (Ideal.map (B.toSheafifiedSection leftContext)
          (G.lawWitnessIdeal leftContext PUnit.unit)))).ideal
      ⟨⊤, @isAffineOpen_top leftChart.domain leftChart.domain_isAffine⟩ at hreal
  change Ideal.map leftChartGlobalSectionsIso.hom.hom
      (((lawGeneratedIdealSheaf referenceRaw referenceScheme
        (ClosedEquationalLawReading.ofSemanticCore referenceRaw
          referenceScheme G B)
        (ClosedEquationalLawReading.ofSemanticCore_valid referenceRaw
          referenceScheme G B)
        (ClosedEquationalLawReading.ofSemanticCore_requiredClosed referenceRaw
          referenceScheme G B)).comap leftChart.map).ideal
        ⟨⊤, @isAffineOpen_top leftChart.domain
          leftChart.domain_isAffine⟩) = _
  rw [hreal, Scheme.IdealSheafData.ofIdealTop_ideal]
  simp [leftChartGlobalSectionsIso, leftSectionRingIso,
    Ideal.map_map, SemanticLawEquationSchemeBridge.toSheafifiedSection,
    sheafificationUnitAlgHom]
  congr 1
  ext x
  simp only [RingHom.comp_apply, Iso.inv_hom_id_apply]
  have hcancel := congrArg
    (fun q => q ((B.toRawPresentation leftContext) x))
    (IsIso.hom_inv_id
      (referenceRaw.toRingedSite.canonical.app (op leftContext)).right)
  apply congrArg leftRawAlgebraIso.hom.hom
  change (inv (referenceRaw.toRingedSite.canonical.app
      (op leftContext)).right)
      ((referenceRaw.toRingedSite.canonical.app (op leftContext)).right
        ((B.toRawPresentation leftContext) x)) =
    (B.toRawPresentation leftContext) x
  simpa only [CommRingCat.comp_apply, Category.id_comp] using hcancel

private theorem referenceIdeal_right_raw
    (G : SemanticLawEquationWitnessIdealCore referenceSite)
    (B : SemanticLawEquationSchemeBridge referenceRaw G)
    (hB : IsSemanticLawEquationSchemeBridge referenceRaw G B) :
    Ideal.map rightChartGlobalSectionsIso.hom.hom
        (((lawGeneratedIdealSheaf referenceRaw referenceScheme
          (ClosedEquationalLawReading.ofSemanticCore referenceRaw
            referenceScheme G B)
          (ClosedEquationalLawReading.ofSemanticCore_valid referenceRaw
            referenceScheme G B)
          (ClosedEquationalLawReading.ofSemanticCore_requiredClosed referenceRaw
            referenceScheme G B)).comap rightChart.map).ideal
          ⟨⊤, @isAffineOpen_top rightChart.domain
            rightChart.domain_isAffine⟩) =
      Ideal.map (rightRawAlgebraIso.hom.hom.comp
        (B.toRawPresentation rightContext).toRingHom)
        (G.lawWitnessIdeal rightContext PUnit.unit) := by
  letI := (hB.presentation_stable rightContext).canonical_isIso
  have hreal := congrArg
    (fun I : rightChart.domain.IdealSheafData =>
      I.ideal ⟨⊤, @isAffineOpen_top rightChart.domain
        rightChart.domain_isAffine⟩)
    (reference_generated_comap_chart G B hB rightIndex)
  change
    (((lawGeneratedIdealSheaf referenceRaw referenceScheme
      (ClosedEquationalLawReading.ofSemanticCore referenceRaw
        referenceScheme G B)
      (ClosedEquationalLawReading.ofSemanticCore_valid referenceRaw
        referenceScheme G B)
      (ClosedEquationalLawReading.ofSemanticCore_requiredClosed referenceRaw
        referenceScheme G B)).comap rightChart.map).ideal
      ⟨⊤, @isAffineOpen_top rightChart.domain rightChart.domain_isAffine⟩) =
    (Scheme.IdealSheafData.ofIdealTop
      (X := rightChart.domain)
      (Ideal.map
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw rightContext)).inv.hom
        (Ideal.map (B.toSheafifiedSection rightContext)
          (G.lawWitnessIdeal rightContext PUnit.unit)))).ideal
      ⟨⊤, @isAffineOpen_top rightChart.domain rightChart.domain_isAffine⟩ at hreal
  change Ideal.map rightChartGlobalSectionsIso.hom.hom
      (((lawGeneratedIdealSheaf referenceRaw referenceScheme
        (ClosedEquationalLawReading.ofSemanticCore referenceRaw
          referenceScheme G B)
        (ClosedEquationalLawReading.ofSemanticCore_valid referenceRaw
          referenceScheme G B)
        (ClosedEquationalLawReading.ofSemanticCore_requiredClosed referenceRaw
          referenceScheme G B)).comap rightChart.map).ideal
        ⟨⊤, @isAffineOpen_top rightChart.domain
          rightChart.domain_isAffine⟩) = _
  rw [hreal, Scheme.IdealSheafData.ofIdealTop_ideal]
  simp [rightChartGlobalSectionsIso, rightSectionRingIso,
    Ideal.map_map, SemanticLawEquationSchemeBridge.toSheafifiedSection,
    sheafificationUnitAlgHom]
  congr 1
  ext x
  simp only [RingHom.comp_apply, Iso.inv_hom_id_apply]
  have hcancel := congrArg
    (fun q => q ((B.toRawPresentation rightContext) x))
    (IsIso.hom_inv_id
      (referenceRaw.toRingedSite.canonical.app (op rightContext)).right)
  apply congrArg rightRawAlgebraIso.hom.hom
  change (inv (referenceRaw.toRingedSite.canonical.app
      (op rightContext)).right)
      ((referenceRaw.toRingedSite.canonical.app (op rightContext)).right
        ((B.toRawPresentation rightContext) x)) =
    (B.toRawPresentation rightContext) x
  simpa only [CommRingCat.comp_apply, Category.id_comp] using hcancel

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakIdeal_left_eq :
    Ideal.map leftChartGlobalSectionsIso.hom.hom
        ((weakIdealSheaf.comap leftChart.map).ideal
          ⟨⊤, @isAffineOpen_top leftChart.domain
            leftChart.domain_isAffine⟩) =
      weakLeftIdeal := by
  have hraw := referenceIdeal_left_raw weakLawEquationCore
    weakSchemeBridge weakSchemeBridge_valid
  have hsource :
      Ideal.map leftChartGlobalSectionsIso.hom.hom
          ((weakIdealSheaf.comap leftChart.map).ideal
            ⟨⊤, @isAffineOpen_top leftChart.domain
              leftChart.domain_isAffine⟩) =
        Ideal.map leftRawAlgebraIso.hom.hom
          (weakLawEquationCore.lawWitnessIdeal leftContext PUnit.unit) := by
    simpa only [weakReading, weakReading_valid, weakReading_requiredClosed,
      weakSchemeBridge, RingHom.comp_id] using hraw
  rw [hsource, SemanticLawEquationWitnessIdealCore.lawWitnessIdeal,
    Ideal.map_span]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro y ⟨_, ⟨a, rfl⟩, rfl⟩
    change leftRawAlgebraIso.hom
      (weakLawEquationCore.violationWitness leftContext PUnit.unit a) ∈
        weakLeftIdeal
    rw [weakViolationWitness_eq]
    split
    · change leftRawAlgebraIso.hom
          (rawCoordinate leftContext * (rawCoordinate leftContext - 1)) ∈
        weakLeftIdeal
      rw [map_mul, map_sub, map_one, leftRawAlgebraIso_coordinate]
      rw [← map_one (algebraMap AmbientRing
          (Localization.Away leftGenerator)), ← map_sub, ← map_mul]
      exact Ideal.subset_span (Set.mem_singleton _)
    · exact map_zero leftRawAlgebraIso.hom.hom ▸ Ideal.zero_mem _
  · rw [weakLeftIdeal]
    apply Ideal.span_le.mpr
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    apply Ideal.subset_span
    refine ⟨weakLawEquationCore.violationWitness leftContext PUnit.unit
      AAT.AG.FiniteModel.FiniteAtom.componentA, ⟨?_, ?_⟩⟩
    · exact ⟨AAT.AG.FiniteModel.FiniteAtom.componentA, rfl⟩
    · rw [weakViolationWitness_eq, if_pos rfl]
      change leftRawAlgebraIso.hom
          (rawCoordinate leftContext * (rawCoordinate leftContext - 1)) = _
      rw [map_mul, map_sub, map_one, leftRawAlgebraIso_coordinate]
      rw [← map_one (algebraMap AmbientRing
          (Localization.Away leftGenerator)), ← map_sub, ← map_mul]

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakIdeal_right_eq :
    Ideal.map rightChartGlobalSectionsIso.hom.hom
        ((weakIdealSheaf.comap rightChart.map).ideal
          ⟨⊤, @isAffineOpen_top rightChart.domain
            rightChart.domain_isAffine⟩) =
      weakRightIdeal := by
  have hraw := referenceIdeal_right_raw weakLawEquationCore
    weakSchemeBridge weakSchemeBridge_valid
  have hsource :
      Ideal.map rightChartGlobalSectionsIso.hom.hom
          ((weakIdealSheaf.comap rightChart.map).ideal
            ⟨⊤, @isAffineOpen_top rightChart.domain
              rightChart.domain_isAffine⟩) =
        Ideal.map rightRawAlgebraIso.hom.hom
          (weakLawEquationCore.lawWitnessIdeal rightContext PUnit.unit) := by
    simpa only [weakReading, weakReading_valid, weakReading_requiredClosed,
      weakSchemeBridge, RingHom.comp_id] using hraw
  rw [hsource, SemanticLawEquationWitnessIdealCore.lawWitnessIdeal,
    Ideal.map_span]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro y ⟨_, ⟨a, rfl⟩, rfl⟩
    change rightRawAlgebraIso.hom
      (weakLawEquationCore.violationWitness rightContext PUnit.unit a) ∈
        weakRightIdeal
    rw [weakViolationWitness_eq]
    split
    · change rightRawAlgebraIso.hom
          (rawCoordinate rightContext * (rawCoordinate rightContext - 1)) ∈
        weakRightIdeal
      rw [map_mul, map_sub, map_one, rightRawAlgebraIso_coordinate]
      rw [← map_one (algebraMap AmbientRing
          (Localization.Away rightGenerator)), ← map_sub, ← map_mul]
      exact Ideal.subset_span (Set.mem_singleton _)
    · exact map_zero rightRawAlgebraIso.hom.hom ▸ Ideal.zero_mem _
  · rw [weakRightIdeal]
    apply Ideal.span_le.mpr
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    apply Ideal.subset_span
    refine ⟨weakLawEquationCore.violationWitness rightContext PUnit.unit
      AAT.AG.FiniteModel.FiniteAtom.componentA, ⟨?_, ?_⟩⟩
    · exact ⟨AAT.AG.FiniteModel.FiniteAtom.componentA, rfl⟩
    · rw [weakViolationWitness_eq, if_pos rfl]
      change rightRawAlgebraIso.hom
          (rawCoordinate rightContext * (rawCoordinate rightContext - 1)) = _
      rw [map_mul, map_sub, map_one, rightRawAlgebraIso_coordinate]
      rw [← map_one (algebraMap AmbientRing
          (Localization.Away rightGenerator)), ← map_sub, ← map_mul]

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongIdeal_left_eq :
    Ideal.map leftChartGlobalSectionsIso.hom.hom
        ((strongIdealSheaf.comap leftChart.map).ideal
          ⟨⊤, @isAffineOpen_top leftChart.domain
            leftChart.domain_isAffine⟩) =
      strongLeftIdeal := by
  have hraw := referenceIdeal_left_raw strongLawEquationCore
    strongSchemeBridge strongSchemeBridge_valid
  have hsource :
      Ideal.map leftChartGlobalSectionsIso.hom.hom
          ((strongIdealSheaf.comap leftChart.map).ideal
            ⟨⊤, @isAffineOpen_top leftChart.domain
              leftChart.domain_isAffine⟩) =
        Ideal.map leftRawAlgebraIso.hom.hom
          (strongLawEquationCore.lawWitnessIdeal leftContext PUnit.unit) := by
    simpa only [strongReading, strongReading_valid, strongReading_requiredClosed,
      strongSchemeBridge, RingHom.comp_id] using hraw
  rw [hsource, SemanticLawEquationWitnessIdealCore.lawWitnessIdeal,
    Ideal.map_span]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro y ⟨_, ⟨a, rfl⟩, rfl⟩
    change leftRawAlgebraIso.hom
      (strongLawEquationCore.violationWitness leftContext PUnit.unit a) ∈
        strongLeftIdeal
    rw [strongViolationWitness_eq]
    split
    · change leftRawAlgebraIso.hom
          (rawCoordinate leftContext * (rawCoordinate leftContext - 1)) ∈
        strongLeftIdeal
      rw [map_mul, map_sub, map_one, leftRawAlgebraIso_coordinate]
      exact strongLeftIdeal.mul_mem_right _
        (Ideal.subset_span (Set.mem_singleton _))
    · split
      · rw [leftRawAlgebraIso_coordinate]
        exact Ideal.subset_span (Set.mem_singleton _)
      · exact map_zero leftRawAlgebraIso.hom.hom ▸ Ideal.zero_mem _
  · rw [strongLeftIdeal]
    apply Ideal.span_le.mpr
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    apply Ideal.subset_span
    refine ⟨strongLawEquationCore.violationWitness leftContext PUnit.unit
      AAT.AG.FiniteModel.FiniteAtom.componentB, ⟨?_, ?_⟩⟩
    · exact ⟨AAT.AG.FiniteModel.FiniteAtom.componentB, rfl⟩
    · rw [strongViolationWitness_eq, if_neg (by simp), if_pos rfl]
      change leftRawAlgebraIso.hom (rawCoordinate leftContext) = _
      rw [leftRawAlgebraIso_coordinate]

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongIdeal_right_eq :
    Ideal.map rightChartGlobalSectionsIso.hom.hom
        ((strongIdealSheaf.comap rightChart.map).ideal
          ⟨⊤, @isAffineOpen_top rightChart.domain
            rightChart.domain_isAffine⟩) =
      strongRightIdeal := by
  have hraw := referenceIdeal_right_raw strongLawEquationCore
    strongSchemeBridge strongSchemeBridge_valid
  have hsource :
      Ideal.map rightChartGlobalSectionsIso.hom.hom
          ((strongIdealSheaf.comap rightChart.map).ideal
            ⟨⊤, @isAffineOpen_top rightChart.domain
              rightChart.domain_isAffine⟩) =
        Ideal.map rightRawAlgebraIso.hom.hom
          (strongLawEquationCore.lawWitnessIdeal rightContext PUnit.unit) := by
    simpa only [strongReading, strongReading_valid, strongReading_requiredClosed,
      strongSchemeBridge, RingHom.comp_id] using hraw
  rw [hsource, SemanticLawEquationWitnessIdealCore.lawWitnessIdeal,
    Ideal.map_span]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro y ⟨_, ⟨a, rfl⟩, rfl⟩
    change rightRawAlgebraIso.hom
      (strongLawEquationCore.violationWitness rightContext PUnit.unit a) ∈
        strongRightIdeal
    rw [strongViolationWitness_eq]
    split
    · change rightRawAlgebraIso.hom
          (rawCoordinate rightContext * (rawCoordinate rightContext - 1)) ∈
        strongRightIdeal
      rw [map_mul, map_sub, map_one, rightRawAlgebraIso_coordinate]
      exact strongRightIdeal.mul_mem_right _
        (Ideal.subset_span (Set.mem_singleton _))
    · split
      · rw [rightRawAlgebraIso_coordinate]
        exact Ideal.subset_span (Set.mem_singleton _)
      · exact map_zero rightRawAlgebraIso.hom.hom ▸ Ideal.zero_mem _
  · rw [strongRightIdeal]
    apply Ideal.span_le.mpr
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    apply Ideal.subset_span
    refine ⟨strongLawEquationCore.violationWitness rightContext PUnit.unit
      AAT.AG.FiniteModel.FiniteAtom.componentB, ⟨?_, ?_⟩⟩
    · exact ⟨AAT.AG.FiniteModel.FiniteAtom.componentB, rfl⟩
    · rw [strongViolationWitness_eq, if_neg (by simp), if_pos rfl]
      change rightRawAlgebraIso.hom (rawCoordinate rightContext) = _
      rw [rightRawAlgebraIso_coordinate]

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakIdeal_top_eq :
    Ideal.map ambientGlobalSectionsIso.hom.hom
        (weakIdealSheaf.ideal ambientTopAffineOpen) =
      weakAmbientIdeal := by
  change Ideal.map ambientGlobalSectionsIso.hom.hom
      ((lawGeneratedIdealSheaf referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed).ideal
        ambientTopAffineOpen) = weakAmbientIdeal
  rw [weak_generated_top_eq_span,
    Ideal.map_span]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro y ⟨_, ⟨a, rfl⟩, rfl⟩
    change ambientGlobalSectionsIso.hom
      (semanticCoreGlobalEquation referenceRaw referenceScheme
        weakLawEquationCore weakSchemeBridge PUnit.unit a) ∈ weakAmbientIdeal
    rw [weakGlobalEquation_eq]
    split
    · exact Ideal.subset_span (Set.mem_singleton _)
    · exact Ideal.zero_mem _
  · rw [weakAmbientIdeal]
    apply Ideal.span_le.mpr
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    apply Ideal.subset_span
    refine ⟨semanticCoreGlobalEquation referenceRaw referenceScheme
      weakLawEquationCore weakSchemeBridge PUnit.unit
      AAT.AG.FiniteModel.FiniteAtom.componentA, ⟨?_, ?_⟩⟩
    · exact ⟨AAT.AG.FiniteModel.FiniteAtom.componentA, rfl⟩
    · simpa using weakGlobalEquation_eq
        AAT.AG.FiniteModel.FiniteAtom.componentA

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongIdeal_top_eq :
    Ideal.map ambientGlobalSectionsIso.hom.hom
        (strongIdealSheaf.ideal ambientTopAffineOpen) =
      strongAmbientIdeal := by
  change Ideal.map ambientGlobalSectionsIso.hom.hom
      ((lawGeneratedIdealSheaf referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed).ideal
        ambientTopAffineOpen) = strongAmbientIdeal
  rw [strong_generated_top_eq_span,
    Ideal.map_span]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro y ⟨_, ⟨a, rfl⟩, rfl⟩
    change ambientGlobalSectionsIso.hom
      (semanticCoreGlobalEquation referenceRaw referenceScheme
        strongLawEquationCore strongSchemeBridge PUnit.unit a) ∈ strongAmbientIdeal
    rw [strongGlobalEquation_eq]
    split
    · exact (Ideal.span {coordinate}).mul_mem_right (coordinate - 1)
        (Ideal.subset_span (Set.mem_singleton coordinate))
    · split
      · exact Ideal.subset_span (Set.mem_singleton coordinate)
      · exact Ideal.zero_mem _
  · rw [strongAmbientIdeal]
    apply Ideal.span_le.mpr
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    apply Ideal.subset_span
    refine ⟨semanticCoreGlobalEquation referenceRaw referenceScheme
      strongLawEquationCore strongSchemeBridge PUnit.unit
      AAT.AG.FiniteModel.FiniteAtom.componentB, ⟨?_, ?_⟩⟩
    · exact ⟨AAT.AG.FiniteModel.FiniteAtom.componentB, rfl⟩
    · simpa using strongGlobalEquation_eq
        AAT.AG.FiniteModel.FiniteAtom.componentB

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem rigidIdeal_top_eq :
    Ideal.map ambientGlobalSectionsIso.hom.hom
        (rigidIdealSheaf.ideal ambientTopAffineOpen) =
      rigidAmbientIdeal := by
  change Ideal.map ambientGlobalSectionsIso.hom.hom
      ((lawGeneratedIdealSheaf referenceRaw referenceScheme
        rigidReading rigidReading_valid rigidReading_requiredClosed).ideal
        ambientTopAffineOpen) = rigidAmbientIdeal
  rw [rigid_generated_top_eq_span,
    Ideal.map_span]
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro y ⟨_, ⟨a, rfl⟩, rfl⟩
    change ambientGlobalSectionsIso.hom
      (semanticCoreGlobalEquation referenceRaw referenceScheme
        rigidLawEquationCore rigidSchemeBridge PUnit.unit a) ∈ rigidAmbientIdeal
    rw [rigidGlobalEquation_eq]
    split
    · exact (Ideal.span {coordinate, MvPolynomial.C 2}).mul_mem_right
        (coordinate - 1)
        (Ideal.subset_span (Set.mem_insert coordinate _))
    · split
      · exact Ideal.subset_span (Set.mem_insert coordinate _)
      · split
        · exact Ideal.subset_span
            (Set.mem_insert_of_mem coordinate (Set.mem_singleton _))
        · exact Ideal.zero_mem _
  · rw [rigidAmbientIdeal]
    apply Ideal.span_le.mpr
    intro y hy
    rcases (Set.mem_insert_iff.mp hy) with rfl | hy
    · apply Ideal.subset_span
      refine ⟨semanticCoreGlobalEquation referenceRaw referenceScheme
        rigidLawEquationCore rigidSchemeBridge PUnit.unit
        AAT.AG.FiniteModel.FiniteAtom.componentB, ⟨?_, ?_⟩⟩
      · exact ⟨AAT.AG.FiniteModel.FiniteAtom.componentB, rfl⟩
      · simpa using rigidGlobalEquation_eq
          AAT.AG.FiniteModel.FiniteAtom.componentB
    · rw [Set.mem_singleton_iff] at hy
      subst y
      apply Ideal.subset_span
      refine ⟨semanticCoreGlobalEquation referenceRaw referenceScheme
        rigidLawEquationCore rigidSchemeBridge PUnit.unit
        AAT.AG.FiniteModel.FiniteAtom.componentC, ⟨?_, ?_⟩⟩
      · exact ⟨AAT.AG.FiniteModel.FiniteAtom.componentC, rfl⟩
      · simpa using rigidGlobalEquation_eq
          AAT.AG.FiniteModel.FiniteAtom.componentC



/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
def evaluationRingHom (n : Int) :
    AmbientRing →+* Int :=
  MvPolynomial.eval₂Hom (RingHom.id Int) (fun _ => n)

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem evaluationRingHom_eq (n : Int) :
    evaluationRingHom n =
      MvPolynomial.eval₂Hom (RingHom.id Int) (fun _ => n) :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def evaluationPoint (n : Int) :
    AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
      referenceScheme.underlying :=
  AlgebraicGeometry.Scheme.Spec.map
    (CommRingCat.ofHom (evaluationRingHom n)).op

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem evaluationPoint_eq (n : Int) :
    evaluationPoint n =
      AlgebraicGeometry.Scheme.Spec.map
        (CommRingCat.ofHom (evaluationRingHom n)).op :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def zeroPoint :
    AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
      referenceScheme.underlying :=
  evaluationPoint 0

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem zeroPoint_eq :
    zeroPoint = evaluationPoint 0 :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def onePoint :
    AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
      referenceScheme.underlying :=
  evaluationPoint 1

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem onePoint_eq :
    onePoint = evaluationPoint 1 :=
  rfl

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def twoPoint :
    AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
      referenceScheme.underlying :=
  evaluationPoint 2

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem twoPoint_eq :
    twoPoint = evaluationPoint 2 :=
  rfl

private theorem evaluationPoint_normalized_appTop (n : Int) :
    (evaluationPoint n).appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom =
      ambientGlobalSectionsIso.hom ≫
        CommRingCat.ofHom (evaluationRingHom n) := by
  simpa only [evaluationPoint, referenceScheme_underlying, ambientScheme_eq,
    ambientGlobalSectionsIso, AlgebraicGeometry.Scheme.Spec_map,
    Quiver.Hom.unop_op] using
      AlgebraicGeometry.Scheme.ΓSpecIso_naturality
        (CommRingCat.ofHom (evaluationRingHom n))

private theorem evaluationPoint_normalized_apply (n : Int)
    (x : Γ(referenceScheme.underlying, ⊤)) :
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom
        ((evaluationPoint n).appTop x) =
      evaluationRingHom n (ambientGlobalSectionsIso.hom x) := by
  simpa only [CommRingCat.comp_apply] using congrArg
    (fun q => q x) (evaluationPoint_normalized_appTop n)

private theorem evaluationPoint_weak_semantic
    (n : Int) (hn : n * (n - 1) = 0) :
    SemanticLawfulAlong referenceRaw referenceScheme weakReading
      (evaluationPoint n) := by
  intro i _
  cases i
  change (GeometricLawReading.ofSemanticCore referenceRaw referenceScheme
    weakLawEquationCore weakSchemeBridge).HoldsOn (evaluationPoint n) PUnit.unit
  rw [GeometricLawReading.ofSemanticCore_holdsOn]
  intro a
  apply (ConcreteCategory.bijective_of_isIso
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom).1
  rw [map_zero, evaluationPoint_normalized_apply,
    weakGlobalEquation_eq]
  split
  · simpa [evaluationRingHom, coordinate] using hn
  · simp [evaluationRingHom]

private theorem evaluationPoint_strong_semantic
    (n : Int) (hn : n = 0) :
    SemanticLawfulAlong referenceRaw referenceScheme strongReading
      (evaluationPoint n) := by
  subst n
  intro i _
  cases i
  change (GeometricLawReading.ofSemanticCore referenceRaw referenceScheme
    strongLawEquationCore strongSchemeBridge).HoldsOn (evaluationPoint 0) PUnit.unit
  rw [GeometricLawReading.ofSemanticCore_holdsOn]
  intro a
  apply (ConcreteCategory.bijective_of_isIso
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom).1
  rw [map_zero, evaluationPoint_normalized_apply,
    strongGlobalEquation_eq]
  cases a <;> simp [evaluationRingHom, coordinate]

private theorem evaluationPoint_not_weak_semantic
    (n : Int) (hn : n * (n - 1) ≠ 0) :
    ¬ SemanticLawfulAlong referenceRaw referenceScheme weakReading
      (evaluationPoint n) := by
  intro h
  have hrequired := h PUnit.unit
    (referenceSite_equation_required PUnit.unit)
  change (GeometricLawReading.ofSemanticCore referenceRaw referenceScheme
    weakLawEquationCore weakSchemeBridge).HoldsOn (evaluationPoint n) PUnit.unit
      at hrequired
  rw [GeometricLawReading.ofSemanticCore_holdsOn] at hrequired
  have hA := hrequired AAT.AG.FiniteModel.FiniteAtom.componentA
  have hnorm := evaluationPoint_normalized_apply n
    (semanticCoreGlobalEquation referenceRaw referenceScheme
      weakLawEquationCore weakSchemeBridge PUnit.unit
      AAT.AG.FiniteModel.FiniteAtom.componentA)
  rw [hA, map_zero, weakGlobalEquation_eq] at hnorm
  apply hn
  simpa [evaluationRingHom, coordinate] using hnorm.symm

private theorem evaluationPoint_not_strong_semantic
    (n : Int) (hn : n ≠ 0) :
    ¬ SemanticLawfulAlong referenceRaw referenceScheme strongReading
      (evaluationPoint n) := by
  intro h
  have hrequired := h PUnit.unit
    (referenceSite_equation_required PUnit.unit)
  change (GeometricLawReading.ofSemanticCore referenceRaw referenceScheme
    strongLawEquationCore strongSchemeBridge).HoldsOn (evaluationPoint n) PUnit.unit
      at hrequired
  rw [GeometricLawReading.ofSemanticCore_holdsOn] at hrequired
  have hB := hrequired AAT.AG.FiniteModel.FiniteAtom.componentB
  have hnorm := evaluationPoint_normalized_apply n
    (semanticCoreGlobalEquation referenceRaw referenceScheme
      strongLawEquationCore strongSchemeBridge PUnit.unit
      AAT.AG.FiniteModel.FiniteAtom.componentB)
  rw [hB, map_zero, strongGlobalEquation_eq] at hnorm
  apply hn
  simpa [evaluationRingHom, coordinate] using hnorm.symm


/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weak_correspondence
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ referenceScheme.underlying) :
    (SemanticLawfulAlong referenceRaw referenceScheme weakReading s ↔
      WitnessVanishes referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed s) ∧
    (WitnessVanishes referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed s ↔
      IdealLawfulAlong referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed s) ∧
    (IdealLawfulAlong referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed s ↔
      Nonempty
        (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
          weakReading weakReading_valid weakReading_requiredClosed s))
  := lawfulnessIdealFactorizationCorrespondence referenceRaw referenceScheme
    weakReading weakReading_valid weakReading_requiredClosed
    weakReading_requiredLawIdealExact s

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strong_correspondence
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ referenceScheme.underlying) :
    (SemanticLawfulAlong referenceRaw referenceScheme strongReading s ↔
      WitnessVanishes referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed s) ∧
    (WitnessVanishes referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed s ↔
      IdealLawfulAlong referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed s) ∧
    (IdealLawfulAlong referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed s ↔
      Nonempty
        (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
          strongReading strongReading_valid strongReading_requiredClosed s)) := lawfulnessIdealFactorizationCorrespondence referenceRaw referenceScheme
    strongReading strongReading_valid strongReading_requiredClosed
    strongReading_requiredLawIdealExact s

private theorem weak_four_of_semantic
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ referenceScheme.underlying)
    (hs : SemanticLawfulAlong referenceRaw referenceScheme weakReading s) :
    SemanticLawfulAlong referenceRaw referenceScheme weakReading s ∧
    WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed s ∧
    IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed s ∧
    Nonempty (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed s) := by
  have h := weak_correspondence s
  exact ⟨hs, h.1.mp hs, h.2.1.mp (h.1.mp hs),
    h.2.2.mp (h.2.1.mp (h.1.mp hs))⟩

private theorem strong_four_of_semantic
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ referenceScheme.underlying)
    (hs : SemanticLawfulAlong referenceRaw referenceScheme strongReading s) :
    SemanticLawfulAlong referenceRaw referenceScheme strongReading s ∧
    WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed s ∧
    IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed s ∧
    Nonempty (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed s) := by
  have h := strong_correspondence s
  exact ⟨hs, h.1.mp hs, h.2.1.mp (h.1.mp hs),
    h.2.2.mp (h.2.1.mp (h.1.mp hs))⟩

private theorem weak_four_not_of_not_semantic
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ referenceScheme.underlying)
    (hs : ¬ SemanticLawfulAlong referenceRaw referenceScheme weakReading s) :
    ¬ SemanticLawfulAlong referenceRaw referenceScheme weakReading s ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed s ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed s ∧
    ¬ Nonempty (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed s) := by
  have h := weak_correspondence s
  exact ⟨hs, fun hw => hs (h.1.mpr hw),
    fun hi => hs (h.1.mpr (h.2.1.mpr hi)),
    fun hf => hs (h.1.mpr (h.2.1.mpr (h.2.2.mpr hf)))⟩

private theorem strong_four_not_of_not_semantic
    {T : AlgebraicGeometry.Scheme}
    (s : T ⟶ referenceScheme.underlying)
    (hs : ¬ SemanticLawfulAlong referenceRaw referenceScheme strongReading s) :
    ¬ SemanticLawfulAlong referenceRaw referenceScheme strongReading s ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed s ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed s ∧
    ¬ Nonempty (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed s) := by
  have h := strong_correspondence s
  exact ⟨hs, fun hw => hs (h.1.mpr hw),
    fun hi => hs (h.1.mpr (h.2.1.mpr hi)),
    fun hf => hs (h.1.mpr (h.2.1.mpr (h.2.2.mpr hf)))⟩

private def rigidEvaluationRingHom : AmbientRing →+* ZMod 2 :=
  MvPolynomial.eval₂Hom (Int.castRingHom (ZMod 2)) (fun _ => 0)

private theorem weakAmbientIdeal_le_evalZero :
    weakAmbientIdeal ≤ RingHom.ker (evaluationRingHom 0) := by
  rw [weakAmbientIdeal]
  apply Ideal.span_le.mpr
  rintro _ (rfl : _ = coordinate * (coordinate - 1))
  simp [evaluationRingHom, coordinate]

private theorem weakAmbientIdeal_le_evalOne :
    weakAmbientIdeal ≤ RingHom.ker (evaluationRingHom 1) := by
  rw [weakAmbientIdeal]
  apply Ideal.span_le.mpr
  rintro _ (rfl : _ = coordinate * (coordinate - 1))
  simp [evaluationRingHom, coordinate]

private theorem strongAmbientIdeal_le_evalZero :
    strongAmbientIdeal ≤ RingHom.ker (evaluationRingHom 0) := by
  rw [strongAmbientIdeal]
  apply Ideal.span_le.mpr
  rintro _ (rfl : _ = coordinate)
  simp [evaluationRingHom, coordinate]

private theorem rigidAmbientIdeal_le_evalModTwo :
    rigidAmbientIdeal ≤ RingHom.ker rigidEvaluationRingHom := by
  rw [rigidAmbientIdeal]
  apply Ideal.span_le.mpr
  intro p hp
  rcases Set.mem_insert_iff.mp hp with rfl | hp
  · simp [rigidEvaluationRingHom, coordinate]
  · have hp' : p = MvPolynomial.C 2 := by
      simpa only [Set.mem_singleton_iff] using hp
    subst p
    change rigidEvaluationRingHom (MvPolynomial.C 2) = 0
    simp only [rigidEvaluationRingHom, MvPolynomial.eval₂Hom_C]
    decide

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakAmbientIdeal_ne_bot :
    weakAmbientIdeal ≠ ⊥ := by
  intro h
  have hm : coordinate * (coordinate - 1) ∈ weakAmbientIdeal :=
    Ideal.subset_span (Set.mem_singleton _)
  rw [h] at hm
  have hz : coordinate * (coordinate - 1) = 0 := by simpa using hm
  have hev := congrArg (evaluationRingHom 2) hz
  norm_num [evaluationRingHom, coordinate] at hev

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakAmbientIdeal_ne_top :
    weakAmbientIdeal ≠ ⊤ := by
  intro h
  have hone : (1 : AmbientRing) ∈ weakAmbientIdeal := by rw [h]; simp
  have hk := weakAmbientIdeal_le_evalZero hone
  norm_num [evaluationRingHom] at hk

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongAmbientIdeal_ne_bot :
    strongAmbientIdeal ≠ ⊥ := by
  intro h
  have hm : coordinate ∈ strongAmbientIdeal :=
    Ideal.subset_span (Set.mem_singleton _)
  rw [h] at hm
  have hz : coordinate = 0 := by simpa using hm
  have hev := congrArg (evaluationRingHom 1) hz
  norm_num [evaluationRingHom, coordinate] at hev

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongAmbientIdeal_ne_top :
    strongAmbientIdeal ≠ ⊤ := by
  intro h
  have hone : (1 : AmbientRing) ∈ strongAmbientIdeal := by rw [h]; simp
  have hk := strongAmbientIdeal_le_evalZero hone
  norm_num [evaluationRingHom] at hk

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem rigidAmbientIdeal_ne_bot :
    rigidAmbientIdeal ≠ ⊥ := by
  intro h
  have hm : coordinate ∈ rigidAmbientIdeal :=
    Ideal.subset_span (Set.mem_insert coordinate _)
  rw [h] at hm
  have hz : coordinate = 0 := by simpa using hm
  have hev := congrArg (evaluationRingHom 1) hz
  norm_num [evaluationRingHom, coordinate] at hev

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem rigidAmbientIdeal_ne_top :
    rigidAmbientIdeal ≠ ⊤ := by
  intro h
  have hone : (1 : AmbientRing) ∈ rigidAmbientIdeal := by rw [h]; simp
  have hk := rigidAmbientIdeal_le_evalModTwo hone
  have : (1 : ZMod 2) = 0 := by
    simpa [rigidEvaluationRingHom] using hk
  norm_num at this

private theorem ideal_le_of_map_le_of_bijective
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Bijective f)
    {I J : Ideal R} (h : Ideal.map f I ≤ Ideal.map f J) : I ≤ J := by
  intro x hx
  have hxmap : f x ∈ Ideal.map f I := Ideal.mem_map_of_mem f hx
  have hjmap := h hxmap
  rw [Ideal.mem_map_iff_of_surjective f hf.2] at hjmap
  obtain ⟨y, hy, hyx⟩ := hjmap
  have hxy : y = x := hf.1 hyx
  simpa [hxy] using hy

private theorem weakAmbientIdeal_le_strongAmbientIdeal :
    weakAmbientIdeal ≤ strongAmbientIdeal := by
  rw [weakAmbientIdeal, strongAmbientIdeal]
  apply Ideal.span_le.mpr
  rintro _ (rfl : _ = coordinate * (coordinate - 1))
  exact (Ideal.span {coordinate}).mul_mem_right (coordinate - 1)
    (Ideal.subset_span (Set.mem_singleton coordinate))

private theorem strongAmbientIdeal_le_rigidAmbientIdeal :
    strongAmbientIdeal ≤ rigidAmbientIdeal := by
  rw [strongAmbientIdeal, rigidAmbientIdeal]
  apply Ideal.span_le.mpr
  rintro _ (rfl : _ = coordinate)
  exact Ideal.subset_span (Set.mem_insert coordinate _)

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakIdeal_lt_strongIdeal :
    weakIdealSheaf < strongIdealSheaf := by
  refine lt_of_le_of_ne ?_ ?_
  · letI : IsAffine referenceScheme.underlying := by
      rw [referenceScheme_underlying, ambientScheme_eq]
      infer_instance
    apply Scheme.IdealSheafData.le_of_isAffine
    have hmap :
        Ideal.map ambientGlobalSectionsIso.hom.hom
            (weakIdealSheaf.ideal ambientTopAffineOpen) ≤
          Ideal.map ambientGlobalSectionsIso.hom.hom
            (strongIdealSheaf.ideal ambientTopAffineOpen) := by
      rw [weakIdeal_top_eq, strongIdeal_top_eq]
      exact weakAmbientIdeal_le_strongAmbientIdeal
    have hsource := ideal_le_of_map_le_of_bijective
      ambientGlobalSectionsIso.hom.hom
      (ConcreteCategory.bijective_of_isIso ambientGlobalSectionsIso.hom) hmap
    simpa [ambientTopAffineOpen] using hsource
  · intro heq
    have htop := congrArg
      (fun I : referenceScheme.underlying.IdealSheafData =>
        Ideal.map ambientGlobalSectionsIso.hom.hom
          (I.ideal ambientTopAffineOpen)) heq
    change Ideal.map ambientGlobalSectionsIso.hom.hom
        (weakIdealSheaf.ideal ambientTopAffineOpen) =
      Ideal.map ambientGlobalSectionsIso.hom.hom
        (strongIdealSheaf.ideal ambientTopAffineOpen) at htop
    rw [weakIdeal_top_eq, strongIdeal_top_eq] at htop
    have hx : coordinate ∈ strongAmbientIdeal :=
      Ideal.subset_span (Set.mem_singleton coordinate)
    rw [← htop] at hx
    have hk := weakAmbientIdeal_le_evalOne hx
    norm_num [evaluationRingHom, coordinate] at hk

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongIdeal_lt_rigidIdeal :
    strongIdealSheaf < rigidIdealSheaf := by
  refine lt_of_le_of_ne ?_ ?_
  · letI : IsAffine referenceScheme.underlying := by
      rw [referenceScheme_underlying, ambientScheme_eq]
      infer_instance
    apply Scheme.IdealSheafData.le_of_isAffine
    have hmap :
        Ideal.map ambientGlobalSectionsIso.hom.hom
            (strongIdealSheaf.ideal ambientTopAffineOpen) ≤
          Ideal.map ambientGlobalSectionsIso.hom.hom
            (rigidIdealSheaf.ideal ambientTopAffineOpen) := by
      rw [strongIdeal_top_eq, rigidIdeal_top_eq]
      exact strongAmbientIdeal_le_rigidAmbientIdeal
    have hsource := ideal_le_of_map_le_of_bijective
      ambientGlobalSectionsIso.hom.hom
      (ConcreteCategory.bijective_of_isIso ambientGlobalSectionsIso.hom) hmap
    simpa [ambientTopAffineOpen] using hsource
  · intro heq
    have htop := congrArg
      (fun I : referenceScheme.underlying.IdealSheafData =>
        Ideal.map ambientGlobalSectionsIso.hom.hom
          (I.ideal ambientTopAffineOpen)) heq
    change Ideal.map ambientGlobalSectionsIso.hom.hom
        (strongIdealSheaf.ideal ambientTopAffineOpen) =
      Ideal.map ambientGlobalSectionsIso.hom.hom
        (rigidIdealSheaf.ideal ambientTopAffineOpen) at htop
    rw [strongIdeal_top_eq, rigidIdeal_top_eq] at htop
    have htwo : MvPolynomial.C 2 ∈ rigidAmbientIdeal :=
      Ideal.subset_span
        (Set.mem_insert_of_mem coordinate (Set.mem_singleton _))
    rw [← htop] at htwo
    have hk := strongAmbientIdeal_le_evalZero htwo
    change evaluationRingHom 0 (MvPolynomial.C 2) = 0 at hk
    have : (2 : Int) = 0 := by
      simpa only [evaluationRingHom, MvPolynomial.eval₂Hom_C,
        RingHom.id_apply] using hk
    norm_num at this


/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem zeroPoint_fires :
    SemanticLawfulAlong referenceRaw referenceScheme weakReading zeroPoint ∧
    WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed zeroPoint ∧
    IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed zeroPoint ∧
    Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed zeroPoint) ∧
    SemanticLawfulAlong referenceRaw referenceScheme strongReading zeroPoint ∧
    WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed zeroPoint ∧
    IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed zeroPoint ∧
    Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed zeroPoint) := by
  have hwsem : SemanticLawfulAlong referenceRaw referenceScheme weakReading
      zeroPoint := by
    simpa only [zeroPoint] using
      evaluationPoint_weak_semantic 0 (by norm_num)
  have hssem : SemanticLawfulAlong referenceRaw referenceScheme strongReading
      zeroPoint := by
    simpa only [zeroPoint] using
      evaluationPoint_strong_semantic 0 rfl
  rcases weak_four_of_semantic zeroPoint hwsem with ⟨hw₁, hw₂, hw₃, hw₄⟩
  rcases strong_four_of_semantic zeroPoint hssem with ⟨hs₁, hs₂, hs₃, hs₄⟩
  exact ⟨hw₁, hw₂, hw₃, hw₄, hs₁, hs₂, hs₃, hs₄⟩

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem onePoint_fires :
    SemanticLawfulAlong referenceRaw referenceScheme weakReading onePoint ∧
    WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed onePoint ∧
    IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed onePoint ∧
    Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed onePoint) ∧
    ¬ SemanticLawfulAlong referenceRaw referenceScheme strongReading onePoint ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed onePoint ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed onePoint ∧
    ¬ Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed onePoint) := by
  have hwsem : SemanticLawfulAlong referenceRaw referenceScheme weakReading
      onePoint := by
    simpa only [onePoint] using
      evaluationPoint_weak_semantic 1 (by norm_num)
  have hssem : ¬ SemanticLawfulAlong referenceRaw referenceScheme strongReading
      onePoint := by
    simpa only [onePoint] using
      evaluationPoint_not_strong_semantic 1 (by norm_num)
  rcases weak_four_of_semantic onePoint hwsem with ⟨hw₁, hw₂, hw₃, hw₄⟩
  rcases strong_four_not_of_not_semantic onePoint hssem with ⟨hs₁, hs₂, hs₃, hs₄⟩
  exact ⟨hw₁, hw₂, hw₃, hw₄, hs₁, hs₂, hs₃, hs₄⟩

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem twoPoint_fires :
    ¬ SemanticLawfulAlong referenceRaw referenceScheme weakReading twoPoint ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed twoPoint ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed twoPoint ∧
    ¬ Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed twoPoint) ∧
    ¬ SemanticLawfulAlong referenceRaw referenceScheme strongReading twoPoint ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed twoPoint ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed twoPoint ∧
    ¬ Nonempty
      (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
        strongReading strongReading_valid strongReading_requiredClosed twoPoint) := by
  have hwsem : ¬ SemanticLawfulAlong referenceRaw referenceScheme weakReading
      twoPoint := by
    simpa only [twoPoint] using
      evaluationPoint_not_weak_semantic 2 (by norm_num)
  have hssem : ¬ SemanticLawfulAlong referenceRaw referenceScheme strongReading
      twoPoint := by
    simpa only [twoPoint] using
      evaluationPoint_not_strong_semantic 2 (by norm_num)
  rcases weak_four_not_of_not_semantic twoPoint hwsem with ⟨hw₁, hw₂, hw₃, hw₄⟩
  rcases strong_four_not_of_not_semantic twoPoint hssem with ⟨hs₁, hs₂, hs₃, hs₄⟩
  exact ⟨hw₁, hw₂, hw₃, hw₄, hs₁, hs₂, hs₃, hs₄⟩

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakImmersion_ker :
    weakImmersion.ker = weakIdealSheaf := by
  exact lawfulClosedImmersion_ker referenceRaw referenceScheme weakReading
    weakReading_valid weakReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongImmersion_ker :
    strongImmersion.ker = strongIdealSheaf := by
  exact lawfulClosedImmersion_ker referenceRaw referenceScheme strongReading
    strongReading_valid strongReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem weakImmersion_zeroLocus :
    Set.range weakImmersion = weakIdealSheaf.support := by
  exact lawfulClosedImmersion_range referenceRaw referenceScheme weakReading
    weakReading_valid weakReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
@[simp] theorem strongImmersion_zeroLocus :
    Set.range strongImmersion = strongIdealSheaf.support := by
  exact lawfulClosedImmersion_range referenceRaw referenceScheme strongReading
    strongReading_valid strongReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def weakAffineQuotientChart :
    AlgebraicGeometry.Spec
        (CommRingCat.of
          (Γ(referenceScheme.underlying, ambientTopAffineOpen) ⧸
            weakIdealSheaf.ideal ambientTopAffineOpen)) ⟶
      weakLocus :=
  (lawfulClosedSubschemeCover
    referenceRaw referenceScheme weakReading weakReading_valid
    weakReading_requiredClosed).f ambientTopAffineOpen

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
noncomputable def strongAffineQuotientChart :
    AlgebraicGeometry.Spec
        (CommRingCat.of
          (Γ(referenceScheme.underlying, ambientTopAffineOpen) ⧸
            strongIdealSheaf.ideal ambientTopAffineOpen)) ⟶
      strongLocus :=
  (lawfulClosedSubschemeCover
    referenceRaw referenceScheme strongReading strongReading_valid
    strongReading_requiredClosed).f ambientTopAffineOpen

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakAffineQuotientChart_isIso :
    IsIso weakAffineQuotientChart := by
  change IsIso (weakIdealSheaf.subschemeCover.f ambientTopAffineOpen)
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  rw [Scheme.IdealSheafData.opensRange_subschemeCover_map]
  simp only [ambientTopAffineOpen_obj, Scheme.Hom.preimage_top]

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongAffineQuotientChart_isIso :
    IsIso strongAffineQuotientChart := by
  change IsIso (strongIdealSheaf.subschemeCover.f ambientTopAffineOpen)
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  rw [Scheme.IdealSheafData.opensRange_subschemeCover_map]
  simp only [ambientTopAffineOpen_obj, Scheme.Hom.preimage_top]

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakLocus_nonempty : Nonempty weakLocus := by
  let p : AlgebraicGeometry.Spec (CommRingCat.of Int) :=
    Classical.choice inferInstance
  exact zeroPoint_fires.2.2.2.1.map (fun t => t.1.base p)

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongLocus_nonempty : Nonempty strongLocus := by
  let p : AlgebraicGeometry.Spec (CommRingCat.of Int) :=
    Classical.choice inferInstance
  exact zeroPoint_fires.2.2.2.2.2.2.2.map (fun t => t.1.base p)

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakIdeal_overlap_agrees :
    (weakIdealSheaf.comap leftChart.map).comap
        (pullback.fst leftChart.map rightChart.map) =
      (weakIdealSheaf.comap rightChart.map).comap
        (pullback.snd leftChart.map rightChart.map) := by
  rw [← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, pullback.condition]

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongIdeal_overlap_agrees :
    (strongIdealSheaf.comap leftChart.map).comap
        (pullback.fst leftChart.map rightChart.map) =
      (strongIdealSheaf.comap rightChart.map).comap
        (pullback.snd leftChart.map rightChart.map) := by
  rw [← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, pullback.condition]

private theorem pairContext_cast_inv :
    (eqToIso (by rw [pair_context]) :
      architectureChartSpec referenceRaw
          (referenceScheme.atlas.pairContext
            referenceRaw leftIndex rightIndex) ≅
        architectureChartSpec referenceRaw overlapContext).inv =
      architectureChartRestriction referenceRaw
        (eqToHom pair_context.symm) := by
  change eqToHom
      (congrArg (architectureChartFunctor referenceRaw).obj
        pair_context.symm) =
    (architectureChartFunctor referenceRaw).map
      (eqToHom pair_context.symm)
  rw [CategoryTheory.eqToHom_map]

private theorem actualOverlapIso_inv_fst :
    actualOverlapIso.inv ≫ pullback.fst leftChart.map rightChart.map =
      overlapChartDomainIso.inv ≫
        architectureChartRestriction referenceRaw overlapToLeft := by
  rw [actualOverlapIso_eq]
  simp only [Iso.trans_inv, Iso.symm_inv,
    StandardArchitectureScheme.overlap_is_actual_pullback, Category.assoc]
  have hcmp :=
    referenceScheme.overlapsValid.comparison_fst leftIndex rightIndex
  change (referenceScheme.overlaps.comparison leftIndex rightIndex).hom ≫
      pullback.fst leftChart.map rightChart.map =
    architectureChartRestriction referenceRaw
      (referenceScheme.atlas.pairToLeft
        referenceRaw leftIndex rightIndex) at hcmp
  slice_lhs 3 4 =>
    rw [hcmp]
  rw [← cancel_epi overlapChartDomainIso.hom,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc]
  rw [pairContext_cast_inv]
  rw [← architectureChartRestriction_comp]
  exact congrArg (architectureChartRestriction referenceRaw)
    (Subsingleton.elim _ _)

private theorem overlapChartDomainIso_inv_appTop :
    overlapChartDomainIso.inv.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of
            (Localization.Away overlapGenerator))).hom =
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing referenceRaw overlapContext)).hom ≫
        overlapSectionRingIso.hom := by
  simpa only [overlapChartDomainIso,
    AlgebraicGeometry.Scheme.Spec_map, Quiver.Hom.unop_op] using
    AlgebraicGeometry.Scheme.ΓSpecIso_naturality
      overlapSectionRingIso.hom

private theorem actualOverlap_left_appTop :
    leftChartGlobalSectionsIso.inv ≫
        (pullback.fst leftChart.map rightChart.map).appTop ≫
        actualOverlapGlobalSectionsIso.hom =
      CommRingCat.ofHom leftToOverlapRingHom := by
  have hfst := congrArg (fun q => q.appTop) actualOverlapIso_inv_fst
  simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop] at hfst
  rw [leftChartGlobalSectionsIso, actualOverlapGlobalSectionsIso,
    Iso.trans_inv, Iso.trans_hom]
  simp only [Category.assoc, asIso_hom]
  slice_lhs 3 4 => rw [hfst]
  slice_lhs 4 5 => rw [overlapChartDomainIso_inv_appTop]
  slice_lhs 3 4 =>
    rw [architectureChartRestriction_appTop]
  slice_lhs 2 4 =>
    rw [Iso.inv_hom_id_assoc]
  exact overlap_left_restriction_is_localization

private theorem reference_ofIdealTop_comap_open
    {Y Z : Scheme} [IsAffine Y]
    (I : Ideal Γ(Z, ⊤)) (g : Y ⟶ Z) [IsOpenImmersion g] :
    (Scheme.IdealSheafData.ofIdealTop I).comap g =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map g.appTop.hom I) := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  simp only [Scheme.IdealSheafData.ofIdealTop_ideal]
  let e := g.appIso ⊤
  have comap_inv (J : Ideal Γ(Z, g ''ᵁ (⊤ : Y.Opens))) :
      Ideal.comap e.inv.hom J = Ideal.map e.hom.hom J := by
    ext x
    constructor
    · intro hx
      change e.inv x ∈ J at hx
      simpa using Ideal.mem_map_of_mem e.hom.hom hx
    · intro hx
      rw [Ideal.mem_map_iff_of_surjective e.hom.hom
        e.commRingCatIsoToRingEquiv.surjective] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      change e.inv x ∈ J
      rw [← hxy]
      simpa using hy
  rw [comap_inv, Ideal.map_map]
  have appTop_eq :
      e.hom.hom.comp
          (Z.presheaf.map (homOfLE le_top).op).hom =
        g.appTop.hom := by
    apply RingHom.ext
    intro z
    change ((Z.presheaf.map (homOfLE le_top).op) ≫ e.hom) z =
      g.appTop z
    simp only [e, Scheme.Hom.appIso_hom]
    rw [← Category.assoc, g.naturality, Category.assoc,
      ← Functor.map_comp]
    simp
  rw [appTop_eq]
  have top_res :
      (Y.presheaf.map (homOfLE le_top).op).hom =
        RingHom.id Γ(Y, ⊤) := by
    apply RingHom.ext
    intro z
    have h := Y.presheaf.map_id (Opposite.op (⊤ : Y.Opens))
    exact congrArg (fun q => q z) h
  rw [top_res, Ideal.map_id]

private theorem reference_ideal_top_comap_open
    {Y Z : Scheme} [IsAffine Y] [IsAffine Z]
    (J : Z.IdealSheafData) (g : Y ⟶ Z) [IsOpenImmersion g] :
    (J.comap g).ideal ⟨⊤, isAffineOpen_top Y⟩ =
      Ideal.map g.appTop.hom
        (J.ideal ⟨⊤, isAffineOpen_top Z⟩) := by
  have hJ : Scheme.IdealSheafData.ofIdealTop
      (J.ideal ⟨⊤, isAffineOpen_top Z⟩) = J :=
    Scheme.IdealSheafData.ext_of_isAffine (by simp)
  rw [← hJ, reference_ofIdealTop_comap_open]
  simp

private theorem left_span_map_overlap (a : AmbientRing) :
    Ideal.map leftToOverlapRingHom
        (Ideal.span {algebraMap AmbientRing
          (Localization.Away leftGenerator) a}) =
      Ideal.span {algebraMap AmbientRing
        (Localization.Away overlapGenerator) a} := by
  rw [Ideal.map_span, Set.image_singleton]
  exact congrArg (fun x => Ideal.span {x})
    (RingHom.congr_fun leftToOverlapRingHom_comp_algebraMap a)

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakIdeal_overlap_eq :
    Ideal.map actualOverlapGlobalSectionsIso.hom.hom
        ((weakIdealSheaf.comap
          (referenceScheme.atlas.actualOverlapToUnderlying
            referenceRaw leftIndex rightIndex)).ideal
          ⟨⊤, @isAffineOpen_top
            (referenceScheme.atlas.actualOverlap
              referenceRaw leftIndex rightIndex)
            (IsAffine.of_isIso actualOverlapIso.hom)⟩) =
      weakOverlapIdeal := by
  letI : IsOpenImmersion
      (pullback.fst
        (referenceScheme.atlas.chart leftIndex).map
        (referenceScheme.atlas.chart rightIndex).map) :=
    referenceScheme.atlas.overlap_left_isOpenImmersion
      referenceRaw referenceScheme.atlasValid leftIndex rightIndex
  letI : IsAffine
      (referenceScheme.atlas.actualOverlap
        referenceRaw leftIndex rightIndex) :=
    IsAffine.of_isIso actualOverlapIso.hom
  have hleft' :
      (weakIdealSheaf.comap leftChart.map).ideal
          ⟨⊤, @isAffineOpen_top leftChart.domain
            leftChart.domain_isAffine⟩ =
        Ideal.map leftChartGlobalSectionsIso.inv.hom weakLeftIdeal := by
    have hcomp :
        leftChartGlobalSectionsIso.inv.hom.comp
            leftChartGlobalSectionsIso.hom.hom =
          RingHom.id _ := by
      change (leftChartGlobalSectionsIso.hom ≫
        leftChartGlobalSectionsIso.inv).hom = _
      rw [Iso.hom_inv_id]
      rfl
    rw [← weakIdeal_left_eq, Ideal.map_map, hcomp]
    exact (Ideal.map_id _).symm
  rw [referenceScheme.atlas.actualOverlapToUnderlying_eq_left,
    Scheme.IdealSheafData.comap_comp]
  rw [reference_ideal_top_comap_open]
  change Ideal.map actualOverlapGlobalSectionsIso.hom.hom
      (Ideal.map
        (pullback.fst leftChart.map rightChart.map).appTop.hom
        ((weakIdealSheaf.comap leftChart.map).ideal
          ⟨⊤, @isAffineOpen_top leftChart.domain
            leftChart.domain_isAffine⟩)) = weakOverlapIdeal
  rw [hleft', Ideal.map_map, Ideal.map_map]
  change Ideal.map
      (leftChartGlobalSectionsIso.inv ≫
        (pullback.fst leftChart.map rightChart.map).appTop ≫
        actualOverlapGlobalSectionsIso.hom).hom weakLeftIdeal =
    weakOverlapIdeal
  rw [actualOverlap_left_appTop]
  simpa only [weakLeftIdeal, weakOverlapIdeal] using
    left_span_map_overlap (coordinate * (coordinate - 1))

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongIdeal_overlap_eq :
    Ideal.map actualOverlapGlobalSectionsIso.hom.hom
        ((strongIdealSheaf.comap
          (referenceScheme.atlas.actualOverlapToUnderlying
            referenceRaw leftIndex rightIndex)).ideal
          ⟨⊤, @isAffineOpen_top
            (referenceScheme.atlas.actualOverlap
              referenceRaw leftIndex rightIndex)
            (IsAffine.of_isIso actualOverlapIso.hom)⟩) =
      strongOverlapIdeal := by
  letI : IsOpenImmersion
      (pullback.fst
        (referenceScheme.atlas.chart leftIndex).map
        (referenceScheme.atlas.chart rightIndex).map) :=
    referenceScheme.atlas.overlap_left_isOpenImmersion
      referenceRaw referenceScheme.atlasValid leftIndex rightIndex
  letI : IsAffine
      (referenceScheme.atlas.actualOverlap
        referenceRaw leftIndex rightIndex) :=
    IsAffine.of_isIso actualOverlapIso.hom
  have hleft' :
      (strongIdealSheaf.comap leftChart.map).ideal
          ⟨⊤, @isAffineOpen_top leftChart.domain
            leftChart.domain_isAffine⟩ =
        Ideal.map leftChartGlobalSectionsIso.inv.hom strongLeftIdeal := by
    have hcomp :
        leftChartGlobalSectionsIso.inv.hom.comp
            leftChartGlobalSectionsIso.hom.hom =
          RingHom.id _ := by
      change (leftChartGlobalSectionsIso.hom ≫
        leftChartGlobalSectionsIso.inv).hom = _
      rw [Iso.hom_inv_id]
      rfl
    rw [← strongIdeal_left_eq, Ideal.map_map, hcomp]
    exact (Ideal.map_id _).symm
  rw [referenceScheme.atlas.actualOverlapToUnderlying_eq_left,
    Scheme.IdealSheafData.comap_comp]
  rw [reference_ideal_top_comap_open]
  change Ideal.map actualOverlapGlobalSectionsIso.hom.hom
      (Ideal.map
        (pullback.fst leftChart.map rightChart.map).appTop.hom
        ((strongIdealSheaf.comap leftChart.map).ideal
          ⟨⊤, @isAffineOpen_top leftChart.domain
            leftChart.domain_isAffine⟩)) = strongOverlapIdeal
  rw [hleft', Ideal.map_map, Ideal.map_map]
  change Ideal.map
      (leftChartGlobalSectionsIso.inv ≫
        (pullback.fst leftChart.map rightChart.map).appTop ≫
        actualOverlapGlobalSectionsIso.hom).hom strongLeftIdeal =
    strongOverlapIdeal
  rw [actualOverlap_left_appTop]
  simpa only [strongLeftIdeal, strongOverlapIdeal] using
    left_span_map_overlap coordinate

private theorem rigidTopIdeal_ne_top :
    rigidIdealSheaf.ideal ambientTopAffineOpen ≠ ⊤ := by
  intro htop
  apply rigidAmbientIdeal_ne_top
  have hmap := congrArg
    (Ideal.map ambientGlobalSectionsIso.hom.hom) htop
  rw [rigidIdeal_top_eq] at hmap
  simpa only [Ideal.map_top, eq_comm] using hmap

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem rigidLocus_nonempty : Nonempty rigidLocus := by
  letI : Nontrivial
      (Γ(referenceScheme.underlying, ambientTopAffineOpen) ⧸
        rigidIdealSheaf.ideal ambientTopAffineOpen) :=
    Ideal.Quotient.nontrivial_iff.mpr rigidTopIdeal_ne_top
  let p : AlgebraicGeometry.Spec
      (CommRingCat.of
        (Γ(referenceScheme.underlying, ambientTopAffineOpen) ⧸
          rigidIdealSheaf.ideal ambientTopAffineOpen)) :=
    Classical.choice inferInstance
  exact ⟨((lawfulClosedSubschemeCover
    referenceRaw referenceScheme rigidReading rigidReading_valid
    rigidReading_requiredClosed).f ambientTopAffineOpen).base p⟩

private theorem rigidImmersion_ker :
    rigidImmersion.ker = rigidIdealSheaf := by
  exact lawfulClosedImmersion_ker referenceRaw referenceScheme rigidReading
    rigidReading_valid rigidReading_requiredClosed

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem weakImmersion_not_isIso : ¬ IsIso weakImmersion := by
  intro hIso
  letI : IsIso weakImmersion := hIso
  have hk : weakIdealSheaf = ⊥ := by
    simpa only [weakImmersion_ker] using
      (Scheme.Hom.ker_eq_bot_of_isIso weakImmersion)
  apply weakAmbientIdeal_ne_bot
  rw [← weakIdeal_top_eq, hk]
  simp

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem strongImmersion_not_isIso : ¬ IsIso strongImmersion := by
  intro hIso
  letI : IsIso strongImmersion := hIso
  have hk : strongIdealSheaf = ⊥ := by
    simpa only [strongImmersion_ker] using
      (Scheme.Hom.ker_eq_bot_of_isIso strongImmersion)
  apply strongAmbientIdeal_ne_bot
  rw [← strongIdeal_top_eq, hk]
  simp

/--
SD2-SD3 standard-geometry reference-model declaration.
Its material data are constructed within the fixed integer-polynomial fixture, and the executable contract fixes the exact declaration type.
-/
theorem rigidImmersion_not_isIso : ¬ IsIso rigidImmersion := by
  intro hIso
  letI : IsIso rigidImmersion := hIso
  have hk : rigidIdealSheaf = ⊥ := by
    simpa only [rigidImmersion_ker] using
      (Scheme.Hom.ker_eq_bot_of_isIso rigidImmersion)
  apply rigidAmbientIdeal_ne_bot
  rw [← rigidIdeal_top_eq, hk]
  simp

/-! ## R5: law comparison -/

/-- The concrete atom map from the weak reading to the strong reading. -/
def weakToStrongAtomMap
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    AAT.AG.FiniteModel.carrier.Atom :=
  if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
    AAT.AG.FiniteModel.FiniteAtom.componentA
  else
    AAT.AG.FiniteModel.FiniteAtom.componentC

/-- The weak-to-strong atom map is fixed on every input. -/
@[simp] theorem weakToStrongAtomMap_eq
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    weakToStrongAtomMap a =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        AAT.AG.FiniteModel.FiniteAtom.componentA
      else
        AAT.AG.FiniteModel.FiniteAtom.componentC :=
  rfl

private theorem weakGlobalEquation_atomMap
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    semanticCoreGlobalEquation referenceRaw referenceScheme
        weakLawEquationCore weakSchemeBridge PUnit.unit a =
      semanticCoreGlobalEquation referenceRaw referenceScheme
        strongLawEquationCore strongSchemeBridge PUnit.unit
          (weakToStrongAtomMap a) := by
  apply (ConcreteCategory.bijective_of_isIso
    ambientGlobalSectionsIso.hom).1
  rw [weakGlobalEquation_eq, strongGlobalEquation_eq]
  cases a <;> simp [weakToStrongAtomMap]

/-- The concrete primitive inclusion from weak laws to strong laws. -/
def weakToStrong :
    ClosedEquationalLawInclusion
      referenceRaw referenceScheme weakReading strongReading where
  lawMap := id
  atomMap := fun _ => weakToStrongAtomMap

/-- The weak-to-strong inclusion preserves the sole law index. -/
@[simp] theorem weakToStrong_lawMap :
    weakToStrong.lawMap = id :=
  rfl

/-- The weak-to-strong inclusion uses the concrete atom map. -/
@[simp] theorem weakToStrong_atomMap :
    weakToStrong.atomMap PUnit.unit = weakToStrongAtomMap :=
  rfl

/-- The weak-to-strong inclusion preserves required laws, witnesses, and semantics. -/
theorem weakToStrong_valid :
    IsClosedEquationalLawInclusion
      referenceRaw referenceScheme weakToStrong where
  required_map := fun i hi => by simpa [weakToStrong] using hi
  closed_map := fun i _ => by
    change i ∈ (Set.univ : Set referenceSite.equationSystem.toLegacyLawUniverse.Index)
    exact Set.mem_univ i
  selected_map := fun V i _ => by
    change i ∈ (Set.univ : Set referenceSite.equationSystem.toLegacyLawUniverse.Index)
    exact Set.mem_univ i
  coordinate_eq := by
    intro i hi V a
    cases i
    simp only [weakReading, strongReading,
      ClosedEquationalLawReading.ofSemanticCore_witness,
      ClosedEquationalLawWitness.ofSemanticCore,
      ClosedEquationalLawWitness.ofGlobalSections_coordinate,
      weakToStrong]
    exact congrArg
      (referenceScheme.underlying.presheaf.map (homOfLE le_top).op)
      (weakGlobalEquation_atomMap a)
  semantic_monotone := by
    intro T s i hs
    cases i
    change (GeometricLawReading.ofSemanticCore referenceRaw referenceScheme
      weakLawEquationCore weakSchemeBridge).HoldsOn s PUnit.unit
    rw [GeometricLawReading.ofSemanticCore_holdsOn]
    change (GeometricLawReading.ofSemanticCore referenceRaw referenceScheme
      strongLawEquationCore strongSchemeBridge).HoldsOn s PUnit.unit at hs
    rw [GeometricLawReading.ofSemanticCore_holdsOn] at hs
    intro a
    rw [weakGlobalEquation_atomMap]
    exact hs (weakToStrongAtomMap a)

/-- The strong lawful locus maps contravariantly to the weak lawful locus. -/
noncomputable def lawComparison :
    strongLocus ⟶ weakLocus :=
  lawfulClosedSubschemeMap
    referenceRaw referenceScheme
    weakReading_valid strongReading_valid
    weakReading_requiredClosed strongReading_requiredClosed
    weakToStrong weakToStrong_valid

/-- The weak-to-strong comparison is the canonical law-inclusion map. -/
@[simp] theorem lawComparison_eq :
    lawComparison =
      lawfulClosedSubschemeMap
        referenceRaw referenceScheme
        weakReading_valid strongReading_valid
        weakReading_requiredClosed strongReading_requiredClosed
        weakToStrong weakToStrong_valid :=
  rfl

/-- The weak-to-strong law comparison is a closed immersion. -/
theorem lawComparison_isClosedImmersion :
    AlgebraicGeometry.IsClosedImmersion lawComparison :=
  lawfulClosedSubschemeMap_isClosedImmersion
    referenceRaw referenceScheme
    weakReading_valid strongReading_valid
    weakReading_requiredClosed strongReading_requiredClosed
    weakToStrong weakToStrong_valid

/-- The weak-to-strong law comparison commutes with the ambient immersions. -/
theorem lawComparison_immersion :
    lawComparison ≫ weakImmersion = strongImmersion :=
  lawfulClosedSubschemeMap_immersion
    referenceRaw referenceScheme
    weakReading_valid strongReading_valid
    weakReading_requiredClosed strongReading_requiredClosed
    weakToStrong weakToStrong_valid

/-- Strictness of the weak and strong ideals makes the comparison non-isomorphic. -/
theorem lawComparison_not_isIso :
    ¬ IsIso lawComparison := by
  intro hIso
  letI : IsIso lawComparison := hIso
  have hker := Scheme.Hom.ker_comp_of_isIso lawComparison weakImmersion
  have hsheaf : strongIdealSheaf = weakIdealSheaf := by
    calc
      strongIdealSheaf = strongImmersion.ker := strongImmersion_ker.symm
      _ = (lawComparison ≫ weakImmersion).ker := by rw [lawComparison_immersion]
      _ = weakImmersion.ker := hker
      _ = weakIdealSheaf := weakImmersion_ker
  exact (ne_of_lt weakIdeal_lt_strongIdeal) hsheaf.symm

/-- The concrete atom map from the strong reading to the rigid reading. -/
def strongToRigidAtomMap
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    AAT.AG.FiniteModel.carrier.Atom :=
  if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
    AAT.AG.FiniteModel.FiniteAtom.componentA
  else if a = AAT.AG.FiniteModel.FiniteAtom.componentB then
    AAT.AG.FiniteModel.FiniteAtom.componentB
  else
    AAT.AG.FiniteModel.FiniteAtom.dependsAB

/-- The strong-to-rigid atom map is fixed on every input. -/
@[simp] theorem strongToRigidAtomMap_eq
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    strongToRigidAtomMap a =
      if a = AAT.AG.FiniteModel.FiniteAtom.componentA then
        AAT.AG.FiniteModel.FiniteAtom.componentA
      else if a = AAT.AG.FiniteModel.FiniteAtom.componentB then
        AAT.AG.FiniteModel.FiniteAtom.componentB
      else
        AAT.AG.FiniteModel.FiniteAtom.dependsAB :=
  rfl

private theorem strongGlobalEquation_atomMap
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    semanticCoreGlobalEquation referenceRaw referenceScheme
        strongLawEquationCore strongSchemeBridge PUnit.unit a =
      semanticCoreGlobalEquation referenceRaw referenceScheme
        rigidLawEquationCore rigidSchemeBridge PUnit.unit
          (strongToRigidAtomMap a) := by
  apply (ConcreteCategory.bijective_of_isIso
    ambientGlobalSectionsIso.hom).1
  rw [strongGlobalEquation_eq, rigidGlobalEquation_eq]
  cases a <;> simp [strongToRigidAtomMap]

/-- The concrete primitive inclusion from strong laws to rigid laws. -/
def strongToRigid :
    ClosedEquationalLawInclusion
      referenceRaw referenceScheme strongReading rigidReading where
  lawMap := id
  atomMap := fun _ => strongToRigidAtomMap

/-- The strong-to-rigid inclusion preserves the sole law index. -/
@[simp] theorem strongToRigid_lawMap :
    strongToRigid.lawMap = id :=
  rfl

/-- The strong-to-rigid inclusion uses the concrete atom map. -/
@[simp] theorem strongToRigid_atomMap :
    strongToRigid.atomMap PUnit.unit = strongToRigidAtomMap :=
  rfl

/-- The strong-to-rigid inclusion preserves required laws, witnesses, and semantics. -/
theorem strongToRigid_valid :
    IsClosedEquationalLawInclusion
      referenceRaw referenceScheme strongToRigid where
  required_map := fun i hi => by simpa [strongToRigid] using hi
  closed_map := fun i _ => by
    change i ∈ (Set.univ : Set referenceSite.equationSystem.toLegacyLawUniverse.Index)
    exact Set.mem_univ i
  selected_map := fun V i _ => by
    change i ∈ (Set.univ : Set referenceSite.equationSystem.toLegacyLawUniverse.Index)
    exact Set.mem_univ i
  coordinate_eq := by
    intro i hi V a
    cases i
    simp only [strongReading, rigidReading,
      ClosedEquationalLawReading.ofSemanticCore_witness,
      ClosedEquationalLawWitness.ofSemanticCore,
      ClosedEquationalLawWitness.ofGlobalSections_coordinate,
      strongToRigid]
    exact congrArg
      (referenceScheme.underlying.presheaf.map (homOfLE le_top).op)
      (strongGlobalEquation_atomMap a)
  semantic_monotone := by
    intro T s i hs
    cases i
    change (GeometricLawReading.ofSemanticCore referenceRaw referenceScheme
      strongLawEquationCore strongSchemeBridge).HoldsOn s PUnit.unit
    rw [GeometricLawReading.ofSemanticCore_holdsOn]
    change (GeometricLawReading.ofSemanticCore referenceRaw referenceScheme
      rigidLawEquationCore rigidSchemeBridge).HoldsOn s PUnit.unit at hs
    rw [GeometricLawReading.ofSemanticCore_holdsOn] at hs
    intro a
    rw [strongGlobalEquation_atomMap]
    exact hs (strongToRigidAtomMap a)

/-- The rigid lawful locus maps contravariantly to the strong lawful locus. -/
noncomputable def strongToRigidComparison :
    rigidLocus ⟶ strongLocus :=
  lawfulClosedSubschemeMap
    referenceRaw referenceScheme
    strongReading_valid rigidReading_valid
    strongReading_requiredClosed rigidReading_requiredClosed
    strongToRigid strongToRigid_valid

/-- The strong-to-rigid comparison is the canonical law-inclusion map. -/
@[simp] theorem strongToRigidComparison_eq :
    strongToRigidComparison =
      lawfulClosedSubschemeMap
        referenceRaw referenceScheme
        strongReading_valid rigidReading_valid
        strongReading_requiredClosed rigidReading_requiredClosed
        strongToRigid strongToRigid_valid :=
  rfl

/-- The strong-to-rigid law comparison is a closed immersion. -/
theorem strongToRigidComparison_isClosedImmersion :
    AlgebraicGeometry.IsClosedImmersion strongToRigidComparison :=
  lawfulClosedSubschemeMap_isClosedImmersion
    referenceRaw referenceScheme
    strongReading_valid rigidReading_valid
    strongReading_requiredClosed rigidReading_requiredClosed
    strongToRigid strongToRigid_valid

/-- The strong-to-rigid comparison commutes with the ambient immersions. -/
theorem strongToRigidComparison_immersion :
    strongToRigidComparison ≫ strongImmersion = rigidImmersion :=
  lawfulClosedSubschemeMap_immersion
    referenceRaw referenceScheme
    strongReading_valid rigidReading_valid
    strongReading_requiredClosed rigidReading_requiredClosed
    strongToRigid strongToRigid_valid

/-- Strictness of the strong and rigid ideals makes the comparison non-isomorphic. -/
theorem strongToRigidComparison_not_isIso :
    ¬ IsIso strongToRigidComparison := by
  intro hIso
  letI : IsIso strongToRigidComparison := hIso
  have hker := Scheme.Hom.ker_comp_of_isIso
    strongToRigidComparison strongImmersion
  have hsheaf : rigidIdealSheaf = strongIdealSheaf := by
    calc
      rigidIdealSheaf = rigidImmersion.ker := rigidImmersion_ker.symm
      _ = (strongToRigidComparison ≫ strongImmersion).ker := by
        rw [strongToRigidComparison_immersion]
      _ = strongImmersion.ker := hker
      _ = strongIdealSheaf := strongImmersion_ker
  exact (ne_of_lt strongIdeal_lt_rigidIdeal) hsheaf.symm

/-- The composite inclusion from weak laws to rigid laws. -/
def weakToRigid :
    ClosedEquationalLawInclusion
      referenceRaw referenceScheme weakReading rigidReading :=
  weakToStrong.comp referenceRaw referenceScheme strongToRigid

/-- The weak-to-rigid inclusion is the generic composite inclusion. -/
@[simp] theorem weakToRigid_eq :
    weakToRigid =
      weakToStrong.comp referenceRaw referenceScheme strongToRigid :=
  rfl

/-- Validity of the weak-to-rigid inclusion is inherited from generic composition. -/
theorem weakToRigid_valid :
    IsClosedEquationalLawInclusion
      referenceRaw referenceScheme weakToRigid :=
  ClosedEquationalLawInclusion.comp_valid
    referenceRaw referenceScheme weakToStrong strongToRigid
    weakToStrong_valid strongToRigid_valid

/-- The rigid lawful locus maps directly to the weak lawful locus. -/
noncomputable def weakToRigidComparison :
    rigidLocus ⟶ weakLocus :=
  lawfulClosedSubschemeMap
    referenceRaw referenceScheme
    weakReading_valid rigidReading_valid
    weakReading_requiredClosed rigidReading_requiredClosed
    weakToRigid weakToRigid_valid

/-- The weak-to-rigid comparison is the canonical composite-inclusion map. -/
@[simp] theorem weakToRigidComparison_eq :
    weakToRigidComparison =
      lawfulClosedSubschemeMap
        referenceRaw referenceScheme
        weakReading_valid rigidReading_valid
        weakReading_requiredClosed rigidReading_requiredClosed
        weakToRigid weakToRigid_valid :=
  rfl

/-- The identity law inclusion induces the identity map of the weak locus. -/
theorem lawComparison_id_fires :
    lawfulClosedSubschemeMap
        referenceRaw referenceScheme
        weakReading_valid weakReading_valid
        weakReading_requiredClosed weakReading_requiredClosed
        (ClosedEquationalLawInclusion.refl
          referenceRaw referenceScheme weakReading)
        (ClosedEquationalLawInclusion.refl_valid
          referenceRaw referenceScheme weakReading) =
      𝟙 weakLocus :=
  lawfulClosedSubschemeMap_id referenceRaw referenceScheme
    weakReading weakReading_valid weakReading_requiredClosed

/-- The two non-isomorphic comparison legs compose by the generic law-inclusion theorem. -/
theorem lawComparison_comp_fires :
    strongToRigidComparison ≫ lawComparison = weakToRigidComparison :=
  lawfulClosedSubschemeMap_comp
    referenceRaw referenceScheme
    weakReading_valid strongReading_valid rigidReading_valid
    weakReading_requiredClosed strongReading_requiredClosed
    rigidReading_requiredClosed
    weakToStrong strongToRigid weakToStrong_valid strongToRigid_valid

/-! ## R6: coefficient change -/

/-!
### Implementation notes

The changed scheme, readings, generated ideals, chart squares, and lawful-locus maps are obtained
from the merged generic coefficient APIs. Strictness is detected by an actual point of the scheme
pullback above the source one-point, while non-isomorphism of the ambient projection is detected by
two coefficient-evaluation points that agree on all source sections and separate the new
polynomial coefficient. The mixed law square follows by composing with the monomorphic weak
ambient immersion and applying the two generic ambient-triangle theorems.
-/

/-- The canonical flat coefficient inclusion from integers to integer polynomials.

## Implementation notes

Flatness is constructed from the free `Int`-module structure of `Polynomial Int`; no
caller-supplied flatness certificate or alternate coefficient map is accepted.
-/
noncomputable def coefficientChange :
    FlatCoefficientChange Int (Polynomial Int) where
  hom := Polynomial.C
  flat := by
    change (algebraMap Int (Polynomial Int)).Flat
    rw [RingHom.flat_algebraMap_iff]
    exact Module.Flat.of_free

/-- The coefficient map is definitionally the constant-polynomial inclusion. -/
@[simp] theorem coefficientChange_hom :
    coefficientChange.hom = Polynomial.C :=
  rfl

/-- The polynomial variable witnesses failure of surjectivity. -/
theorem coefficientChange_not_surjective :
    ¬ Function.Surjective coefficientChange.hom := by
  intro hsurjective
  rcases hsurjective Polynomial.X with ⟨z, hz⟩
  have hcoeff := congrArg (fun p : Polynomial Int => p.coeff 1) hz
  simp only [coefficientChange, Polynomial.coeff_C,
    Polynomial.coeff_X] at hcoeff
  norm_num at hcoeff

/-- Scalar extension preserves the finite matching limits of the selected reference site.

## Implementation notes

The instance is discharged from the already constructed finite cover-arrow and relation
instances, followed by the generic finite-multicospan preservation theorem.
-/
noncomputable instance coefficientChange_hasSheafCompose :
    referenceSite.topology.HasSheafCompose
      (coefficientChange.coefficientExtension :
        AATCommAlgCat.{0, 0} Int ⥤
          AATCommAlgCat.{0, 0} (Polynomial Int)) := by
  letI : ∀ (X : referenceSite.category)
      (S : referenceSite.topology.Cover X)
      (P : referenceSite.categoryᵒᵖ ⥤ AATCommAlgCat.{0, 0} Int),
      PreservesLimit (S.index P).multicospan
        (coefficientChange.coefficientExtension :
          AATCommAlgCat.{0, 0} Int ⥤
            AATCommAlgCat.{0, 0} (Polynomial Int)) := by
    intro X S P
    classical
    letI : Fintype S.Arrow := Fintype.ofFinite S.Arrow
    letI : Fintype S.Relation := Fintype.ofFinite S.Relation
    letI : Fintype S.shape.L := Fintype.ofFinite S.Arrow
    letI : Fintype S.shape.R := Fintype.ofFinite S.Relation
    letI : DecidableEq S.shape.L := Classical.decEq _
    letI : DecidableEq S.shape.R := Classical.decEq _
    letI : FinCategory (WalkingMulticospan S.shape) := by
      infer_instance
    infer_instance
  exact CategoryTheory.hasSheafCompose_of_preservesMulticospan _ _

/-- The standard scheme obtained by the canonical generic coefficient base change.

## Implementation notes

This definition reuses `StandardArchitectureScheme.baseChange`; the changed atlas, overlaps,
decoration, and projection are not reconstructed inside the fixture.
-/
noncomputable def coefficientChangedScheme :
    StandardArchitectureScheme
      (referenceRaw.baseChange coefficientChange.hom) :=
  referenceScheme.baseChange referenceRaw coefficientChange

/-- The changed scheme is fixed to the generic base-change constructor. -/
@[simp] theorem coefficientChangedScheme_eq :
    coefficientChangedScheme =
      referenceScheme.baseChange referenceRaw coefficientChange :=
  rfl

/-- The weak reading transported by the generic semantic-core coefficient construction.

## Implementation notes

The target equations are the source equations sent through the actual base-change projection.
-/
noncomputable def coefficientChangedWeakReading :
    ClosedEquationalLawReading
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme :=
  ClosedEquationalLawReading.baseChangeOfSemanticCore
    referenceRaw referenceScheme
    weakLawEquationCore weakSchemeBridge coefficientChange

/-- The changed weak reading is fixed to `baseChangeOfSemanticCore`. -/
@[simp] theorem coefficientChangedWeakReading_eq :
    coefficientChangedWeakReading =
      ClosedEquationalLawReading.baseChangeOfSemanticCore
        referenceRaw referenceScheme
        weakLawEquationCore weakSchemeBridge coefficientChange :=
  rfl

/-- The strong reading transported by the generic semantic-core coefficient construction.

## Implementation notes

The target equations are the source equations sent through the actual base-change projection.
-/
noncomputable def coefficientChangedStrongReading :
    ClosedEquationalLawReading
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme :=
  ClosedEquationalLawReading.baseChangeOfSemanticCore
    referenceRaw referenceScheme
    strongLawEquationCore strongSchemeBridge coefficientChange

/-- The changed strong reading is fixed to `baseChangeOfSemanticCore`. -/
@[simp] theorem coefficientChangedStrongReading_eq :
    coefficientChangedStrongReading =
      ClosedEquationalLawReading.baseChangeOfSemanticCore
        referenceRaw referenceScheme
        strongLawEquationCore strongSchemeBridge coefficientChange :=
  rfl

/-- The transported weak reading satisfies the closed-equational reading laws. -/
theorem coefficientChangedWeakReading_valid :
    IsClosedEquationalLawReading
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme coefficientChangedWeakReading :=
  ClosedEquationalLawReading.baseChangeOfSemanticCore_valid
    referenceRaw referenceScheme
    weakLawEquationCore weakSchemeBridge coefficientChange

/-- The transported strong reading satisfies the closed-equational reading laws. -/
theorem coefficientChangedStrongReading_valid :
    IsClosedEquationalLawReading
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme coefficientChangedStrongReading :=
  ClosedEquationalLawReading.baseChangeOfSemanticCore_valid
    referenceRaw referenceScheme
    strongLawEquationCore strongSchemeBridge coefficientChange

/-- Every required weak law remains closed after coefficient change. -/
theorem coefficientChangedWeakReading_requiredClosed :
    RequiredClosed
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme coefficientChangedWeakReading :=
  ClosedEquationalLawReading.baseChangeOfSemanticCore_requiredClosed
    referenceRaw referenceScheme
    weakLawEquationCore weakSchemeBridge coefficientChange

/-- Every required strong law remains closed after coefficient change. -/
theorem coefficientChangedStrongReading_requiredClosed :
    RequiredClosed
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme coefficientChangedStrongReading :=
  ClosedEquationalLawReading.baseChangeOfSemanticCore_requiredClosed
    referenceRaw referenceScheme
    strongLawEquationCore strongSchemeBridge coefficientChange

/-- The changed weak generated ideal is the generic pullback of the source weak ideal. -/
theorem weakIdeal_baseChange :
    Scheme.IdealSheafData.comap weakIdealSheaf
        (referenceScheme.baseChangeMap
          referenceRaw coefficientChange) =
      lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedWeakReading
        coefficientChangedWeakReading_valid
        coefficientChangedWeakReading_requiredClosed :=
  lawGeneratedIdealSheaf_baseChange_ofSemanticCore
    referenceRaw referenceScheme weakLawEquationCore weakSchemeBridge
      coefficientChange

/-- The changed strong generated ideal is the generic pullback of the source strong ideal. -/
theorem strongIdeal_baseChange :
    Scheme.IdealSheafData.comap strongIdealSheaf
        (referenceScheme.baseChangeMap
          referenceRaw coefficientChange) =
      lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedStrongReading
        coefficientChangedStrongReading_valid
        coefficientChangedStrongReading_requiredClosed :=
  lawGeneratedIdealSheaf_baseChange_ofSemanticCore
    referenceRaw referenceScheme strongLawEquationCore strongSchemeBridge
      coefficientChange

/-- The coefficient-changed left chart forms the actual pullback square. -/
theorem leftChart_baseChange_isPullback :
    IsPullback
      ((referenceScheme.baseChangedAtlas
          referenceRaw coefficientChange).chart
        (cast
          (referenceScheme.baseChangedAtlas_Index
            referenceRaw coefficientChange).symm leftIndex)).map
      (referenceScheme.baseChangedChartMap
        referenceRaw coefficientChange leftIndex)
      (referenceScheme.baseChangeMap referenceRaw coefficientChange)
      (referenceScheme.atlas.chart leftIndex).map :=
  referenceScheme.baseChangedChart_isPullback
    referenceRaw coefficientChange leftIndex

/-- The coefficient-changed right chart forms the actual pullback square. -/
theorem rightChart_baseChange_isPullback :
    IsPullback
      ((referenceScheme.baseChangedAtlas
          referenceRaw coefficientChange).chart
        (cast
          (referenceScheme.baseChangedAtlas_Index
            referenceRaw coefficientChange).symm rightIndex)).map
      (referenceScheme.baseChangedChartMap
        referenceRaw coefficientChange rightIndex)
      (referenceScheme.baseChangeMap referenceRaw coefficientChange)
      (referenceScheme.atlas.chart rightIndex).map :=
  referenceScheme.baseChangedChart_isPullback
    referenceRaw coefficientChange rightIndex

/-- The changed weak-to-strong inclusion reuses the source law and atom maps.

## Implementation notes

Only the ambient raw system, scheme, and readings change; the generator indexing maps remain
definitionally those of `weakToStrong`.
-/
def coefficientChangedWeakToStrong :
    ClosedEquationalLawInclusion
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme
      coefficientChangedWeakReading
      coefficientChangedStrongReading where
  lawMap := weakToStrong.lawMap
  atomMap := weakToStrong.atomMap

/-- The changed inclusion has the source law-index map. -/
@[simp] theorem coefficientChangedWeakToStrong_lawMap :
    coefficientChangedWeakToStrong.lawMap = weakToStrong.lawMap :=
  rfl

/-- The changed inclusion has the source atom map. -/
@[simp] theorem coefficientChangedWeakToStrong_atomMap :
    coefficientChangedWeakToStrong.atomMap = weakToStrong.atomMap :=
  rfl

private theorem sourceGlobalEquation_atomMap
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    semanticCoreGlobalEquation
        referenceRaw referenceScheme weakLawEquationCore weakSchemeBridge
          PUnit.unit a =
      semanticCoreGlobalEquation
        referenceRaw referenceScheme strongLawEquationCore strongSchemeBridge
          PUnit.unit (weakToStrongAtomMap a) := by
  apply (ConcreteCategory.bijective_of_isIso
    ambientGlobalSectionsIso.hom).1
  rw [weakGlobalEquation_eq, strongGlobalEquation_eq]
  cases a <;> simp [weakToStrongAtomMap]

private theorem coefficientChangedGlobalEquation_atomMap
    (a : AAT.AG.FiniteModel.carrier.Atom) :
    baseChangedSemanticCoreGlobalEquation
        referenceRaw referenceScheme weakLawEquationCore weakSchemeBridge
          coefficientChange PUnit.unit a =
      baseChangedSemanticCoreGlobalEquation
        referenceRaw referenceScheme strongLawEquationCore strongSchemeBridge
          coefficientChange PUnit.unit (weakToStrongAtomMap a) := by
  exact congrArg
    (referenceScheme.baseChangeMap referenceRaw coefficientChange).appTop
    (sourceGlobalEquation_atomMap a)

/-- The changed inclusion preserves required laws, coordinates, and semantics. -/
theorem coefficientChangedWeakToStrong_valid :
    IsClosedEquationalLawInclusion
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme coefficientChangedWeakToStrong where
  required_map := fun i hi => by
    simpa [coefficientChangedWeakToStrong] using hi
  closed_map := fun i _ => by
    change i ∈ (Set.univ : Set referenceSite.equationSystem.toLegacyLawUniverse.Index)
    exact Set.mem_univ i
  selected_map := fun V i _ => by
    change i ∈ (Set.univ : Set referenceSite.equationSystem.toLegacyLawUniverse.Index)
    exact Set.mem_univ i
  coordinate_eq := by
    intro i hi V a
    cases i
    simp only [coefficientChangedWeakReading,
      coefficientChangedStrongReading,
      ClosedEquationalLawReading.baseChangeOfSemanticCore,
      ClosedEquationalLawWitness.ofGlobalSections_coordinate,
      coefficientChangedWeakToStrong, weakToStrong_atomMap]
    exact congrArg
      (coefficientChangedScheme.underlying.presheaf.map
        (homOfLE le_top).op)
      (coefficientChangedGlobalEquation_atomMap a)
  semantic_monotone := by
    intro T s i hs
    cases i
    change (ClosedEquationalLawReading.baseChangeOfSemanticCore
      referenceRaw referenceScheme weakLawEquationCore weakSchemeBridge
        coefficientChange).geometric.HoldsOn s PUnit.unit
    rw [ClosedEquationalLawReading.baseChangeOfSemanticCore_geometric_iff]
    change (ClosedEquationalLawReading.baseChangeOfSemanticCore
      referenceRaw referenceScheme strongLawEquationCore strongSchemeBridge
        coefficientChange).geometric.HoldsOn s PUnit.unit at hs
    rw [ClosedEquationalLawReading.baseChangeOfSemanticCore_geometric_iff]
      at hs
    change (GeometricLawReading.ofSemanticCore referenceRaw referenceScheme
      weakLawEquationCore weakSchemeBridge).HoldsOn
        (s ≫ referenceScheme.baseChangeMap
          referenceRaw coefficientChange) PUnit.unit
    rw [GeometricLawReading.ofSemanticCore_holdsOn]
    change (GeometricLawReading.ofSemanticCore referenceRaw referenceScheme
      strongLawEquationCore strongSchemeBridge).HoldsOn
        (s ≫ referenceScheme.baseChangeMap
          referenceRaw coefficientChange) PUnit.unit at hs
    rw [GeometricLawReading.ofSemanticCore_holdsOn] at hs
    intro a
    rw [sourceGlobalEquation_atomMap]
    exact hs (weakToStrongAtomMap a)

/-- The canonical changed strong-locus to weak-locus comparison.

## Implementation notes

The map is created directly by `lawfulClosedSubschemeMap`; no auxiliary comparison morphism is
accepted by the fixture.
-/
noncomputable def coefficientChangedLawComparison :
    lawfulClosedSubscheme
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedStrongReading
        coefficientChangedStrongReading_valid
        coefficientChangedStrongReading_requiredClosed ⟶
      lawfulClosedSubscheme
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedWeakReading
        coefficientChangedWeakReading_valid
        coefficientChangedWeakReading_requiredClosed :=
  lawfulClosedSubschemeMap
    (referenceRaw.baseChange coefficientChange.hom)
    coefficientChangedScheme
    coefficientChangedWeakReading_valid
    coefficientChangedStrongReading_valid
    coefficientChangedWeakReading_requiredClosed
    coefficientChangedStrongReading_requiredClosed
    coefficientChangedWeakToStrong
    coefficientChangedWeakToStrong_valid

/-- The changed comparison is fixed to the generic lawful-subscheme map. -/
@[simp] theorem coefficientChangedLawComparison_eq :
    coefficientChangedLawComparison =
      lawfulClosedSubschemeMap
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedWeakReading_valid
        coefficientChangedStrongReading_valid
        coefficientChangedWeakReading_requiredClosed
        coefficientChangedStrongReading_requiredClosed
        coefficientChangedWeakToStrong
        coefficientChangedWeakToStrong_valid :=
  rfl

/-- The changed law comparison is a closed immersion. -/
theorem coefficientChangedLawComparison_isClosedImmersion :
    AlgebraicGeometry.IsClosedImmersion
      coefficientChangedLawComparison :=
  lawfulClosedSubschemeMap_isClosedImmersion
    (referenceRaw.baseChange coefficientChange.hom)
    coefficientChangedScheme
    coefficientChangedWeakReading_valid
    coefficientChangedStrongReading_valid
    coefficientChangedWeakReading_requiredClosed
    coefficientChangedStrongReading_requiredClosed
    coefficientChangedWeakToStrong
    coefficientChangedWeakToStrong_valid

/-- The changed comparison commutes with the changed ambient immersions. -/
theorem coefficientChangedLawComparison_immersion :
    coefficientChangedLawComparison ≫
        lawfulClosedImmersion
          (referenceRaw.baseChange coefficientChange.hom)
          coefficientChangedScheme
          coefficientChangedWeakReading
          coefficientChangedWeakReading_valid
          coefficientChangedWeakReading_requiredClosed =
      lawfulClosedImmersion
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedStrongReading
        coefficientChangedStrongReading_valid
        coefficientChangedStrongReading_requiredClosed :=
  lawfulClosedSubschemeMap_immersion
    (referenceRaw.baseChange coefficientChange.hom)
    coefficientChangedScheme
    coefficientChangedWeakReading_valid
    coefficientChangedStrongReading_valid
    coefficientChangedWeakReading_requiredClosed
    coefficientChangedStrongReading_requiredClosed
    coefficientChangedWeakToStrong
    coefficientChangedWeakToStrong_valid

private def liftedPolynomialEval (n : Int) :
    ULift.{0, 0} (Polynomial Int) →+* Int :=
  (Polynomial.evalRingHom n).comp ULift.ringEquiv.toRingHom

private theorem ambientGlobalSectionsIso_unit_r6
    (x : referenceRaw.rawAlgebra baseContext) :
    ambientGlobalSectionsIso.hom
        (ambientDecoration.interpretation
          ((sheafificationUnitAlgHom referenceRaw baseContext) x)) =
      baseRawAlgebraIso.hom x := by
  letI := canonical_component_isIso baseContext
  simp only [ambientGlobalSectionsIso, ambientDecoration,
    AATReadingDecoration.pullback_interpretation,
    AATReadingDecoration.ofContext_interpretation,
    baseChartDomainIso, AlgebraicGeometry.Scheme.Spec.mapIso_inv]
  change
    (AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of AmbientRing)).hom
        (((AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing referenceRaw baseContext)).inv ≫
          (AlgebraicGeometry.Scheme.Spec.map
            baseSectionRingIso.hom.op).appTop)
          ((sheafificationUnitAlgHom referenceRaw baseContext) x)) =
      baseRawAlgebraIso.hom x
  rw [AlgebraicGeometry.Scheme.Spec_map]
  simp only [CommRingCat.comp_apply]
  have hΓ := congrArg
    (fun q => q.hom
      ((AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing referenceRaw baseContext)).inv
          ((sheafificationUnitAlgHom referenceRaw baseContext) x)))
    (AlgebraicGeometry.Scheme.ΓSpecIso_naturality
      baseSectionRingIso.hom)
  change
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of AmbientRing)).hom
        ((AlgebraicGeometry.Spec.map baseSectionRingIso.hom).appTop
          ((AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing referenceRaw baseContext)).inv
            ((sheafificationUnitAlgHom referenceRaw baseContext) x))) =
      baseSectionRingIso.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw baseContext)).hom
          ((AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing referenceRaw baseContext)).inv
            ((sheafificationUnitAlgHom referenceRaw baseContext) x))) at hΓ
  calc
    _ = baseSectionRingIso.hom
        ((sheafificationUnitAlgHom referenceRaw baseContext) x) := by
      simpa only [CommRingCat.comp_apply, Iso.inv_hom_id_apply,
        Quiver.Hom.unop_op] using hΓ
    _ = baseRawAlgebraIso.hom x := by
      change baseRawAlgebraIso.hom
          ((inv (referenceRaw.toRingedSite.canonical.app
            (op baseContext)).right)
            ((referenceRaw.toRingedSite.canonical.app
              (op baseContext)).right x)) = _
      have hcancel := congrArg
        (fun q => q x)
        (IsIso.hom_inv_id
          (referenceRaw.toRingedSite.canonical.app
            (op baseContext)).right)
      rw [show (inv (referenceRaw.toRingedSite.canonical.app
          (op baseContext)).right)
          ((referenceRaw.toRingedSite.canonical.app
            (op baseContext)).right x) = x by
        simpa only [CommRingCat.comp_apply, Category.id_comp] using hcancel]

private theorem evaluationPoint_normalized_appTop_r6 (n : Int) :
    (evaluationPoint n).appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom =
      ambientGlobalSectionsIso.hom ≫
        CommRingCat.ofHom (evaluationRingHom n) := by
  simpa only [evaluationPoint, referenceScheme_underlying, ambientScheme_eq,
    ambientGlobalSectionsIso, AlgebraicGeometry.Scheme.Spec_map,
    Quiver.Hom.unop_op] using
      AlgebraicGeometry.Scheme.ΓSpecIso_naturality
        (CommRingCat.ofHom (evaluationRingHom n))

private noncomputable def coefficientEvaluationPoint (n : Int) :
    AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
      AlgebraicGeometry.Spec
        (CommRingCat.of (ULift.{0, 0} (Polynomial Int))) :=
  AlgebraicGeometry.Scheme.Spec.map
    (CommRingCat.ofHom (liftedPolynomialEval n)).op

private theorem coefficientOnePoint_square (n : Int) :
    onePoint ≫ referenceScheme.coefficientStructureMap referenceRaw =
      coefficientEvaluationPoint n ≫
        AlgebraicGeometry.Scheme.Spec.map
          (CommRingCat.ofHom coefficientChange.liftedHom).op := by
  apply (AlgebraicGeometry.ΓSpec.adjunction.homEquiv
    (AlgebraicGeometry.Spec (CommRingCat.of Int))
    (op (CommRingCat.of (ULift Int)))).symm.injective
  rw [Adjunction.homEquiv_symm_apply, Adjunction.homEquiv_symm_apply]
  simp [onePoint, evaluationPoint,
    StandardArchitectureScheme.coefficientStructureMap,
    coefficientEvaluationPoint]
  apply Quiver.Hom.unop_inj
  simp only [unop_comp, Quiver.Hom.unop_op]
  let oldObject :=
    referenceRaw.toRingedSite.structureSheaf.val.obj
      (op referenceScheme.decoration.context)
  have hcoefficient :
      (AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of (ULift Int))).inv ≫
          (referenceScheme.coefficientStructureMap referenceRaw).appTop =
        oldObject.hom ≫ referenceScheme.decoration.interpretation := by
    simpa only [StandardArchitectureScheme.coefficientStructureMap] using
      (AlgebraicGeometry.ΓSpecIso_inv_ΓSpec_adjunction_homEquiv
        (oldObject.hom ≫ referenceScheme.decoration.interpretation))
  change (((AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of (ULift Int))).inv ≫
        (referenceScheme.coefficientStructureMap referenceRaw).appTop) ≫ _) = _
  rw [hcoefficient]
  rw [← cancel_mono
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom]
  simp only [Category.assoc]
  change oldObject.hom ≫ referenceScheme.decoration.interpretation ≫
      ((evaluationPoint 1).appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of Int)).hom) = _
  rw [evaluationPoint_normalized_appTop_r6]
  have hzero :
      (AlgebraicGeometry.Scheme.Spec.map
          (CommRingCat.ofHom (liftedPolynomialEval n)).op).appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of Int)).hom =
      (AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of (ULift.{0, 0} (Polynomial Int)))).hom ≫
        CommRingCat.ofHom (liftedPolynomialEval n) := by
    simpa only [AlgebraicGeometry.Scheme.Spec_map,
      Quiver.Hom.unop_op] using
        (AlgebraicGeometry.Scheme.ΓSpecIso_naturality
          (CommRingCat.ofHom (liftedPolynomialEval n)))
  have hchange :
      (AlgebraicGeometry.Scheme.Spec.map
          (CommRingCat.ofHom coefficientChange.liftedHom).op).appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of (ULift.{0, 0} (Polynomial Int)))).hom =
      (AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of (ULift.{0, 0} Int))).hom ≫
        CommRingCat.ofHom coefficientChange.liftedHom := by
    simpa only [AlgebraicGeometry.Scheme.Spec_map,
      Quiver.Hom.unop_op] using
        (AlgebraicGeometry.Scheme.ΓSpecIso_naturality
          (CommRingCat.ofHom coefficientChange.liftedHom))
  change _ = (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of (ULift.{0, 0} Int))).inv ≫
    (AlgebraicGeometry.Scheme.Spec.map
      (CommRingCat.ofHom coefficientChange.liftedHom).op).appTop ≫
    (AlgebraicGeometry.Scheme.Spec.map
      (CommRingCat.ofHom (liftedPolynomialEval n)).op).appTop ≫
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom
  rw [hzero]
  rw [← Category.assoc
    (AlgebraicGeometry.Scheme.Spec.map
      (CommRingCat.ofHom coefficientChange.liftedHom).op).appTop
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of (ULift.{0, 0} (Polynomial Int)))).hom
    (CommRingCat.ofHom (liftedPolynomialEval n))]
  rw [hchange]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  apply CommRingCat.hom_ext
  ext z
  rcases z with ⟨z⟩
  change evaluationRingHom 1
      (ambientGlobalSectionsIso.hom
        (referenceScheme.decoration.interpretation
          (oldObject.hom ⟨z⟩))) =
    liftedPolynomialEval n (coefficientChange.liftedHom ⟨z⟩)
  have hold : oldObject.hom ⟨z⟩ =
      (sheafificationUnitAlgHom referenceRaw baseContext)
        (algebraMap Int (referenceRaw.rawAlgebra baseContext) z) := by
    exact (sheafificationUnitAlgHom referenceRaw baseContext).commutes z |>.symm
  rw [hold]
  change evaluationRingHom 1
      (ambientGlobalSectionsIso.hom
        (ambientDecoration.interpretation
          ((sheafificationUnitAlgHom referenceRaw baseContext)
            (algebraMap Int (referenceRaw.rawAlgebra baseContext) z)))) = _
  rw [ambientGlobalSectionsIso_unit_r6]
  simp [evaluationRingHom, baseRawAlgebraIso]
  change z = Polynomial.eval n (Polynomial.C z)
  simp

private noncomputable def coefficientOnePoint (n : Int) :
    AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
      coefficientChangedScheme.underlying := by
  change AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
    pullback (referenceScheme.coefficientStructureMap referenceRaw)
      (AlgebraicGeometry.Scheme.Spec.map
        (CommRingCat.ofHom coefficientChange.liftedHom).op)
  exact pullback.lift onePoint (coefficientEvaluationPoint n)
    (coefficientOnePoint_square n)

private theorem coefficientOnePoint_fst (n : Int) :
    coefficientOnePoint n ≫
        referenceScheme.baseChangeMap referenceRaw coefficientChange =
      onePoint := by
  exact pullback.lift_fst _ _ _

private theorem coefficientOnePoint_weak_ideal :
    IdealLawfulAlong
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme coefficientChangedWeakReading
      coefficientChangedWeakReading_valid
      coefficientChangedWeakReading_requiredClosed
      (coefficientOnePoint 0) := by
  change Scheme.IdealSheafData.comap
      (lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme coefficientChangedWeakReading
        coefficientChangedWeakReading_valid
        coefficientChangedWeakReading_requiredClosed)
      (coefficientOnePoint 0) = ⊥
  rw [← weakIdeal_baseChange]
  rw [← Scheme.IdealSheafData.comap_comp]
  rw [coefficientOnePoint_fst]
  exact onePoint_fires.2.2.1

private theorem coefficientOnePoint_not_strong_ideal :
    ¬ IdealLawfulAlong
      (referenceRaw.baseChange coefficientChange.hom)
      coefficientChangedScheme coefficientChangedStrongReading
      coefficientChangedStrongReading_valid
      coefficientChangedStrongReading_requiredClosed
      (coefficientOnePoint 0) := by
  intro h
  apply onePoint_fires.2.2.2.2.2.2.1
  change Scheme.IdealSheafData.comap strongIdealSheaf onePoint = ⊥
  change Scheme.IdealSheafData.comap
      (lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme coefficientChangedStrongReading
        coefficientChangedStrongReading_valid
        coefficientChangedStrongReading_requiredClosed)
      (coefficientOnePoint 0) = ⊥ at h
  rw [← strongIdeal_baseChange] at h
  rw [← Scheme.IdealSheafData.comap_comp] at h
  rw [coefficientOnePoint_fst] at h
  exact h

/-- The transported weak ideal remains strictly below the transported strong ideal. -/
theorem coefficientChanged_ideal_strict :
    lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedWeakReading
        coefficientChangedWeakReading_valid
        coefficientChangedWeakReading_requiredClosed <
      lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom)
        coefficientChangedScheme
        coefficientChangedStrongReading
        coefficientChangedStrongReading_valid
        coefficientChangedStrongReading_requiredClosed := by
  refine lt_of_le_of_ne ?_ ?_
  · rw [← weakIdeal_baseChange, ← strongIdeal_baseChange]
    exact (Scheme.IdealSheafData.comap_mono
      (referenceScheme.baseChangeMap referenceRaw coefficientChange))
        weakIdeal_lt_strongIdeal.le
  · intro heq
    apply coefficientOnePoint_not_strong_ideal
    change Scheme.IdealSheafData.comap
        (lawGeneratedIdealSheaf
          (referenceRaw.baseChange coefficientChange.hom)
          coefficientChangedScheme coefficientChangedStrongReading
        coefficientChangedStrongReading_valid
        coefficientChangedStrongReading_requiredClosed)
        (coefficientOnePoint 0) = ⊥
    rw [← heq]
    exact coefficientOnePoint_weak_ideal

/-- Strictness of the changed ideals makes the changed comparison non-isomorphic. -/
theorem coefficientChangedLawComparison_not_isIso :
    ¬ IsIso coefficientChangedLawComparison := by
  intro hIso
  letI : IsIso coefficientChangedLawComparison := hIso
  let weakChangedIdeal := lawGeneratedIdealSheaf
    (referenceRaw.baseChange coefficientChange.hom)
    coefficientChangedScheme coefficientChangedWeakReading
    coefficientChangedWeakReading_valid
    coefficientChangedWeakReading_requiredClosed
  let strongChangedIdeal := lawGeneratedIdealSheaf
    (referenceRaw.baseChange coefficientChange.hom)
    coefficientChangedScheme coefficientChangedStrongReading
    coefficientChangedStrongReading_valid
    coefficientChangedStrongReading_requiredClosed
  let weakChangedImmersion := lawfulClosedImmersion
    (referenceRaw.baseChange coefficientChange.hom)
    coefficientChangedScheme coefficientChangedWeakReading
    coefficientChangedWeakReading_valid
    coefficientChangedWeakReading_requiredClosed
  let strongChangedImmersion := lawfulClosedImmersion
    (referenceRaw.baseChange coefficientChange.hom)
    coefficientChangedScheme coefficientChangedStrongReading
    coefficientChangedStrongReading_valid
    coefficientChangedStrongReading_requiredClosed
  have hker := Scheme.Hom.ker_comp_of_isIso
    coefficientChangedLawComparison weakChangedImmersion
  have hsheaf : strongChangedIdeal = weakChangedIdeal := by
    calc
      strongChangedIdeal = strongChangedImmersion.ker :=
        (lawfulClosedImmersion_ker
          (referenceRaw.baseChange coefficientChange.hom)
          coefficientChangedScheme coefficientChangedStrongReading
          coefficientChangedStrongReading_valid
          coefficientChangedStrongReading_requiredClosed).symm
      _ = (coefficientChangedLawComparison ≫ weakChangedImmersion).ker := by
        rw [coefficientChangedLawComparison_immersion]
      _ = weakChangedImmersion.ker := hker
      _ = weakChangedIdeal :=
        lawfulClosedImmersion_ker
          (referenceRaw.baseChange coefficientChange.hom)
          coefficientChangedScheme coefficientChangedWeakReading
          coefficientChangedWeakReading_valid
          coefficientChangedWeakReading_requiredClosed
  exact (ne_of_lt coefficientChanged_ideal_strict) hsheaf.symm

/-- Coefficient change and the concrete weak-to-strong law comparison form the mixed square. -/
theorem coefficient_law_comparison_square :
    coefficientChangedLawComparison ≫
        lawfulClosedSubschemeBaseChangeMap
          referenceRaw referenceScheme
          weakLawEquationCore weakSchemeBridge coefficientChange =
      lawfulClosedSubschemeBaseChangeMap
          referenceRaw referenceScheme
          strongLawEquationCore strongSchemeBridge coefficientChange ≫
        lawComparison := by
  letI : AlgebraicGeometry.IsClosedImmersion weakImmersion := by
    dsimp only [weakImmersion, lawfulClosedImmersion]
    infer_instance
  have hweak :
      lawfulClosedSubschemeBaseChangeMap
          referenceRaw referenceScheme weakLawEquationCore weakSchemeBridge
            coefficientChange ≫ weakImmersion =
        lawfulClosedImmersion
            (referenceRaw.baseChange coefficientChange.hom)
            coefficientChangedScheme coefficientChangedWeakReading
            coefficientChangedWeakReading_valid
            coefficientChangedWeakReading_requiredClosed ≫
          referenceScheme.baseChangeMap referenceRaw coefficientChange := by
    exact lawfulClosedSubschemeBaseChangeMap_immersion
      referenceRaw referenceScheme weakLawEquationCore weakSchemeBridge
        coefficientChange
  have hstrong :
      lawfulClosedSubschemeBaseChangeMap
          referenceRaw referenceScheme strongLawEquationCore strongSchemeBridge
            coefficientChange ≫ strongImmersion =
        lawfulClosedImmersion
            (referenceRaw.baseChange coefficientChange.hom)
            coefficientChangedScheme coefficientChangedStrongReading
            coefficientChangedStrongReading_valid
            coefficientChangedStrongReading_requiredClosed ≫
          referenceScheme.baseChangeMap referenceRaw coefficientChange := by
    exact lawfulClosedSubschemeBaseChangeMap_immersion
      referenceRaw referenceScheme strongLawEquationCore strongSchemeBridge
        coefficientChange
  rw [← cancel_mono weakImmersion]
  simp only [Category.assoc]
  rw [hweak]
  rw [← Category.assoc, coefficientChangedLawComparison_immersion]
  rw [lawComparison_immersion]
  rw [hstrong]

private noncomputable def coefficientProjection :
    coefficientChangedScheme.underlying ⟶
      AlgebraicGeometry.Spec
        (CommRingCat.of (ULift.{0, 0} (Polynomial Int))) := by
  change pullback (referenceScheme.coefficientStructureMap referenceRaw)
      (AlgebraicGeometry.Scheme.Spec.map
        (CommRingCat.ofHom coefficientChange.liftedHom).op) ⟶ _
  exact pullback.snd _ _

private def coefficientPointEval (n : Int) :
    Γ(coefficientChangedScheme.underlying, ⊤) →+* Int :=
  ((coefficientOnePoint n).appTop ≫
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom).hom

private noncomputable def targetCoefficientX :
    Γ(coefficientChangedScheme.underlying, ⊤) :=
  coefficientProjection.appTop
    ((AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of (ULift.{0, 0} (Polynomial Int)))).inv
        (ULift.up Polynomial.X))

private theorem coefficientEvaluationPoint_normalized (n : Int) :
    (coefficientEvaluationPoint n).appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom =
      (AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of (ULift.{0, 0} (Polynomial Int)))).hom ≫
        CommRingCat.ofHom (liftedPolynomialEval n) := by
  simpa only [coefficientEvaluationPoint,
    AlgebraicGeometry.Scheme.Spec_map, Quiver.Hom.unop_op] using
      (AlgebraicGeometry.Scheme.ΓSpecIso_naturality
        (CommRingCat.ofHom (liftedPolynomialEval n)))

private theorem coefficientPointEval_targetCoefficientX (n : Int) :
    coefficientPointEval n targetCoefficientX = n := by
  have hsnd : coefficientOnePoint n ≫ coefficientProjection =
      coefficientEvaluationPoint n := by
    exact pullback.lift_snd _ _ _
  have happ := congrArg AlgebraicGeometry.Scheme.Hom.appTop hsnd
  simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop] at happ
  change (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of Int)).hom
    ((coefficientOnePoint n).appTop
      (coefficientProjection.appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of (ULift.{0, 0} (Polynomial Int)))).inv
            (ULift.up Polynomial.X)))) = n
  have hpx := ConcreteCategory.congr_hom happ
    ((AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of (ULift.{0, 0} (Polynomial Int)))).inv
        (ULift.up Polynomial.X))
  rw [CommRingCat.comp_apply] at hpx
  rw [hpx]
  have hnormalized := ConcreteCategory.congr_hom
    (coefficientEvaluationPoint_normalized n)
    ((AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of (ULift.{0, 0} (Polynomial Int)))).inv
        (ULift.up Polynomial.X))
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at hnormalized
  rw [hnormalized]
  rw [Iso.inv_hom_id_apply]
  change Polynomial.eval n Polynomial.X = n
  simp

private theorem coefficientPointEval_agree_on_baseMap
    (x : Γ(referenceScheme.underlying, ⊤)) :
    coefficientPointEval 0
        ((referenceScheme.baseChangeMap
          referenceRaw coefficientChange).appTop x) =
      coefficientPointEval 1
        ((referenceScheme.baseChangeMap
          referenceRaw coefficientChange).appTop x) := by
  have hzero := congrArg AlgebraicGeometry.Scheme.Hom.appTop
    (coefficientOnePoint_fst 0)
  have hone := congrArg AlgebraicGeometry.Scheme.Hom.appTop
    (coefficientOnePoint_fst 1)
  simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop] at hzero hone
  change (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of Int)).hom
      ((coefficientOnePoint 0).appTop
        ((referenceScheme.baseChangeMap
          referenceRaw coefficientChange).appTop x)) =
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of Int)).hom
      ((coefficientOnePoint 1).appTop
        ((referenceScheme.baseChangeMap
          referenceRaw coefficientChange).appTop x))
  have hz := ConcreteCategory.congr_hom hzero x
  have ho := ConcreteCategory.congr_hom hone x
  rw [CommRingCat.comp_apply] at hz ho
  exact congrArg
    (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of Int)).hom
    (hz.trans ho.symm)

/-- The ambient coefficient-change projection is not an isomorphism. -/
theorem coefficientChange_schemeMap_not_isIso :
    ¬ IsIso
      (referenceScheme.baseChangeMap
        referenceRaw coefficientChange) := by
  intro hIso
  letI : IsIso
      (referenceScheme.baseChangeMap
        referenceRaw coefficientChange) := hIso
  have hsurjective : Function.Surjective
      (referenceScheme.baseChangeMap
        referenceRaw coefficientChange).appTop :=
    (ConcreteCategory.bijective_of_isIso
      (referenceScheme.baseChangeMap
        referenceRaw coefficientChange).appTop).2
  have heval : coefficientPointEval 0 = coefficientPointEval 1 := by
    apply RingHom.ext
    intro y
    rcases hsurjective y with ⟨x, rfl⟩
    exact coefficientPointEval_agree_on_baseMap x
  have hx := DFunLike.congr_fun heval targetCoefficientX
  rw [coefficientPointEval_targetCoefficientX,
    coefficientPointEval_targetCoefficientX] at hx
  norm_num at hx


/-!
## R7 negative fixtures and integrated firing

The duplicate atlas and reflected chart keep the underlying concrete maps visible while
isolating the failed coverage or interpretation clause.  Collapsed ideals, the unit ideal,
and `Int → ZMod 2` provide separate negative witnesses for strictness, nonempty closed
geometry, and flat coefficient change.  The integrated theorem is a direct conjunction of
the earlier component theorems rather than a new certificate structure.
-/

/-- A negative atlas whose two entries both reuse the left chart. -/
noncomputable def duplicateLeftAtlas :
    ArchitectureAffineAtlas referenceRaw
      referenceScheme.underlying referenceScheme.decoration where
  Index := Bool
  chart _ := leftChart

/-- Both entries of the duplicate atlas are the fixed left chart. -/
@[simp] theorem duplicateLeftAtlas_chart (i : Bool) :
    duplicateLeftAtlas.chart i = leftChart :=
  rfl

private theorem leftChart_normalized_appTop :
    ambientGlobalSectionsIso.inv ≫
        leftChart.map.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw leftContext)).hom ≫
        leftSectionRingIso.hom =
      CommRingCat.ofHom
        (algebraMap AmbientRing (Localization.Away leftGenerator)) := by
  simp [leftChart, ambientGlobalSectionsIso, ambientScheme_eq,
    AlgebraicGeometry.Scheme.Spec_map]

private theorem zeroPoint_normalized_appTop :
    zeroPoint.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom =
      ambientGlobalSectionsIso.hom ≫
        CommRingCat.ofHom (evaluationRingHom 0) := by
  simpa only [zeroPoint, evaluationPoint, referenceScheme_underlying,
    ambientScheme_eq, ambientGlobalSectionsIso,
    AlgebraicGeometry.Scheme.Spec_map, Quiver.Hom.unop_op] using
      AlgebraicGeometry.Scheme.ΓSpecIso_naturality
        (CommRingCat.ofHom (evaluationRingHom 0))

/-- The zero evaluation point does not factor through the left principal open. -/
theorem zeroPoint_not_factors_through_leftChart :
    ¬ ∃ lift : AlgebraicGeometry.Spec (CommRingCat.of Int) ⟶
        leftChart.domain,
      lift ≫ leftChart.map = zeroPoint := by
  rintro ⟨lift, hfactor⟩
  let φ : CommRingCat.of (Localization.Away leftGenerator) ⟶
      CommRingCat.of Int :=
    leftSectionRingIso.inv ≫
      (AlgebraicGeometry.Scheme.ΓSpecIso
        (SheafifiedSectionRing referenceRaw leftContext)).inv ≫
      lift.appTop ≫
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom
  have happ := congrArg AlgebraicGeometry.Scheme.Hom.appTop hfactor
  simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop] at happ
  have hcomp :
      CommRingCat.ofHom
          (algebraMap AmbientRing (Localization.Away leftGenerator)) ≫ φ =
        CommRingCat.ofHom (evaluationRingHom 0) := by
    rw [← leftChart_normalized_appTop]
    simp only [φ, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc leftChart.map.appTop lift.appTop
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of Int)).hom]
    rw [happ, zeroPoint_normalized_appTop]
    simp
  have hcoord := ConcreteCategory.congr_hom hcomp coordinate
  change φ (algebraMap AmbientRing
      (Localization.Away leftGenerator) coordinate) =
    evaluationRingHom 0 coordinate at hcoord
  have hunit : IsUnit
      (φ (algebraMap AmbientRing
        (Localization.Away leftGenerator) coordinate)) := by
    apply IsUnit.map φ.hom
    rw [← leftGenerator_eq]
    exact IsLocalization.Away.algebraMap_isUnit leftGenerator
  have hzero : φ (algebraMap AmbientRing
      (Localization.Away leftGenerator) coordinate) = 0 := by
    exact hcoord.trans (by simp [evaluationRingHom, coordinate])
  rw [hzero] at hunit
  exact not_isUnit_zero hunit

/-- The atlas duplicating the left chart fails pointwise coverage. -/
theorem duplicateLeftAtlas_not_valid :
    ¬ IsArchitectureAffineAtlas referenceRaw duplicateLeftAtlas := by
  intro hvalid
  have hsurjective : Function.Surjective leftChart.map := by
    intro x
    rcases hvalid.covers x with ⟨i, y, hy⟩
    exact ⟨y, by simpa only [duplicateLeftAtlas_chart] using hy⟩
  letI : AlgebraicGeometry.IsOpenImmersion leftChart.map := by
    simpa only [referenceScheme, referenceAtlas] using
      left_chart_isOpenImmersion
  have hrange : leftChart.map.opensRange = ⊤ := by
    apply top_unique
    intro x _
    exact AlgebraicGeometry.Scheme.Hom.mem_opensRange.mpr
      (hsurjective x)
  letI : IsIso leftChart.map :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top leftChart.map hrange
  apply zeroPoint_not_factors_through_leftChart
  exact ⟨zeroPoint ≫ inv leftChart.map, by simp⟩

/-- The strong reading collapsed to the weak reading. -/
noncomputable def collapsedStrongReading :
    ClosedEquationalLawReading referenceRaw referenceScheme :=
  weakReading

/-- The collapsed strong reading is definitionally the weak reading. -/
@[simp] theorem collapsedStrongReading_eq :
    collapsedStrongReading = weakReading :=
  rfl

/-- Collapsing the readings destroys strict ideal inclusion. -/
theorem collapsedIdeal_not_strict :
    ¬ lawGeneratedIdealSheaf
        referenceRaw referenceScheme
        weakReading weakReading_valid weakReading_requiredClosed <
      lawGeneratedIdealSheaf
        referenceRaw referenceScheme
        collapsedStrongReading weakReading_valid weakReading_requiredClosed := by
  simpa only [collapsedStrongReading] using
    (lt_irrefl (lawGeneratedIdealSheaf
      referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed))

/-- The unit ideal used as an empty closed-subscheme negative fixture. -/
noncomputable def unitIdealFixture :
    referenceScheme.underlying.IdealSheafData :=
  ⊤

/-- The unit-ideal fixture is the top ideal sheaf. -/
@[simp] theorem unitIdealFixture_eq :
    unitIdealFixture = ⊤ :=
  rfl

/-- The closed subscheme cut out by the unit ideal is empty. -/
theorem unitIdealFixture_subscheme_empty :
    IsEmpty unitIdealFixture.subscheme := by
  rw [unitIdealFixture_eq]
  infer_instance

/-- The quotient map to `ZMod 2`, used as a non-flat coefficient map. -/
noncomputable def nonFlatCoefficientMap :
    Int →+* ZMod 2 :=
  Int.castRingHom (ZMod 2)

/-- The negative coefficient map is the integer quotient to `ZMod 2`. -/
@[simp] theorem nonFlatCoefficientMap_eq :
    nonFlatCoefficientMap = Int.castRingHom (ZMod 2) :=
  rfl

/-- The quotient `Int → ZMod 2` is not flat, detected by two-torsion. -/
theorem nonFlatCoefficientMap_not_flat :
    ¬ nonFlatCoefficientMap.Flat := by
  intro hflat
  letI : Module Int (ZMod 2) := nonFlatCoefficientMap.toAlgebra.toModule
  haveI : Module.Flat Int (ZMod 2) := by
    exact hflat
  have hinjective : IsSMulRegular (ZMod 2) (2 : Int) := by
    have h := Module.Flat.rTensor_preserves_injective_linearMap (M := ZMod 2)
      (LinearMap.toSpanSingleton Int Int 2)
      (IsRegular.of_ne_zero' (by norm_num : (2 : Int) ≠ 0)).right
    have h2 : (fun (x : ZMod 2) => (2 : Int) • x) =
        ((TensorProduct.lid Int (ZMod 2)) ∘ₗ
          (LinearMap.rTensor (ZMod 2) (LinearMap.toSpanSingleton Int Int 2)) ∘ₗ
          (TensorProduct.lid Int (ZMod 2)).symm) := by
      ext
      simp
      change (2 : ZMod 2) * _ = (algebraMap Int (ZMod 2) 2) * _
      rfl
    rw [IsSMulRegular, h2]
    simp [h, LinearEquiv.injective]
  have hone : (1 : ZMod 2) = 0 := by
    apply hinjective
    change (2 : ZMod 2) = 0
    decide
  norm_num at hone

private noncomputable def coordinateReflectionAlgHom :
    AmbientRing →ₐ[Int] AmbientRing :=
  MvPolynomial.aeval (fun _ : Unit => rightGenerator)

private theorem coordinateReflectionAlgHom_involutive :
    coordinateReflectionAlgHom.comp coordinateReflectionAlgHom =
      AlgHom.id Int AmbientRing := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i
  simp [coordinateReflectionAlgHom, rightGenerator, coordinate]

/-- The involution of `Int[x]` sending `x` to `1 - x`. -/
noncomputable def coordinateReflection :
    AmbientRing ≃+* AmbientRing :=
  (AlgEquiv.ofAlgHom coordinateReflectionAlgHom coordinateReflectionAlgHom
    coordinateReflectionAlgHom_involutive
    coordinateReflectionAlgHom_involutive).toRingEquiv

/-- Coordinate reflection sends `x` to `1 - x`. -/
@[simp] theorem coordinateReflection_coordinate :
    coordinateReflection coordinate = rightGenerator := by
  simp [coordinateReflection, coordinateReflectionAlgHom, coordinate]

/-- Coordinate reflection sends `1 - x` back to `x`. -/
@[simp] theorem coordinateReflection_rightGenerator :
    coordinateReflection rightGenerator = coordinate := by
  simp [coordinateReflection, coordinateReflectionAlgHom,
    rightGenerator, coordinate]

/-- The right-localization map precomposed with coordinate reflection. -/
noncomputable def reflectedRightRingHom :
    AmbientRing →+* Localization.Away rightGenerator :=
  (algebraMap AmbientRing
    (Localization.Away rightGenerator)).comp
      coordinateReflection.toRingHom

/-- The reflected right-localization map sends `x` to the image of `1 - x`. -/
@[simp] theorem reflectedRightRingHom_coordinate :
    reflectedRightRingHom coordinate =
      algebraMap AmbientRing
        (Localization.Away rightGenerator) rightGenerator := by
  rw [reflectedRightRingHom, RingHom.comp_apply,
    show coordinateReflection.toRingHom coordinate =
      coordinateReflection coordinate from rfl,
    coordinateReflection_coordinate]

/-- A right-context chart whose open map uses reflected coordinates. -/
noncomputable def brokenRightChart :
    ArchitectureAffineChart referenceRaw
      referenceScheme.underlying referenceScheme.decoration where
  context := rightContext
  contextHom := rightToBase
  map :=
    rightChartDomainIso.hom ≫
      AlgebraicGeometry.Scheme.Spec.map
        (CommRingCat.ofHom reflectedRightRingHom).op

/-- The broken chart retains the fixed right context. -/
@[simp] theorem brokenRightChart_context :
    brokenRightChart.context = rightContext :=
  rfl

/-- The broken chart map is the reflected right-localization map. -/
@[simp] theorem brokenRightChart_map :
    brokenRightChart.map =
      rightChartDomainIso.hom ≫
        AlgebraicGeometry.Scheme.Spec.map
          (CommRingCat.ofHom reflectedRightRingHom).op :=
  rfl

private theorem brokenRightChart_normalized_appTop :
    baseSectionRingIso.inv ≫
        ambientDecoration.interpretation ≫
        brokenRightChart.map.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing referenceRaw rightContext)).hom ≫
        rightSectionRingIso.hom =
      CommRingCat.ofHom reflectedRightRingHom := by
  simp [brokenRightChart, AlgebraicGeometry.Scheme.Spec_map]

/-- Coordinate reflection preserves the open-immersion property of the right chart. -/
theorem brokenRightChart_isOpenImmersion :
    AlgebraicGeometry.IsOpenImmersion brokenRightChart.map := by
  simp only [brokenRightChart]
  rw [AlgebraicGeometry.Scheme.Spec_map]
  simp only [Quiver.Hom.unop_op]
  letI : AlgebraicGeometry.IsOpenImmersion rightChartDomainIso.hom := by
    infer_instance
  let reflectionMap : CommRingCat.of AmbientRing ⟶
      CommRingCat.of AmbientRing :=
    CommRingCat.ofHom coordinateReflection.toRingHom
  let localizationMap : CommRingCat.of AmbientRing ⟶
      CommRingCat.of (Localization.Away rightGenerator) :=
    CommRingCat.ofHom
      (algebraMap AmbientRing (Localization.Away rightGenerator))
  have hreflected : CommRingCat.ofHom reflectedRightRingHom =
      reflectionMap ≫ localizationMap := by
    dsimp [reflectionMap, localizationMap, reflectedRightRingHom]
  rw [hreflected, AlgebraicGeometry.Spec.map_comp]
  letI : IsIso reflectionMap :=
    (ConcreteCategory.isIso_iff_bijective reflectionMap).2
      coordinateReflection.bijective
  letI : AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map localizationMap) := by
    infer_instance
  letI : AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Spec.map reflectionMap) := by
    infer_instance
  exact AlgebraicGeometry.IsOpenImmersion.comp _ _

private theorem reflectedRightGenerator_ne_zero : rightGenerator ≠ 0 := by
  intro h
  have h' := congrArg
    (MvPolynomial.eval₂Hom (RingHom.id Int) (fun _ : Unit => (0 : Int))) h
  norm_num [rightGenerator, coordinate] at h'

/-- The reflected chart map disagrees with the fixed right-context interpretation. -/
theorem brokenRightChart_interpretation_ne :
    sheafifiedRestriction referenceRaw brokenRightChart.contextHom ≠
      referenceScheme.decoration.interpretation ≫
        brokenRightChart.map.appTop ≫
        (AlgebraicGeometry.Scheme.ΓSpecIso
          (SheafifiedSectionRing
            referenceRaw brokenRightChart.context)).hom := by
  intro hinterpretation
  have hinterpretation' :
      sheafifiedRestriction referenceRaw rightToBase =
        ambientDecoration.interpretation ≫
          brokenRightChart.map.appTop ≫
          (AlgebraicGeometry.Scheme.ΓSpecIso
            (SheafifiedSectionRing referenceRaw rightContext)).hom := by
    simpa only [brokenRightChart, referenceScheme] using hinterpretation
  have hmaps :
      CommRingCat.ofHom
          (algebraMap AmbientRing (Localization.Away rightGenerator)) =
        CommRingCat.ofHom reflectedRightRingHom := by
    calc
      CommRingCat.ofHom
          (algebraMap AmbientRing (Localization.Away rightGenerator)) =
          baseSectionRingIso.inv ≫
            sheafifiedRestriction referenceRaw rightToBase ≫
            rightSectionRingIso.hom :=
        right_restriction_is_localization.symm
      _ = baseSectionRingIso.inv ≫
            ambientDecoration.interpretation ≫
            brokenRightChart.map.appTop ≫
            (AlgebraicGeometry.Scheme.ΓSpecIso
              (SheafifiedSectionRing referenceRaw rightContext)).hom ≫
            rightSectionRingIso.hom := by
        rw [hinterpretation']
        rfl
      _ = CommRingCat.ofHom reflectedRightRingHom :=
        brokenRightChart_normalized_appTop
  have hcoord := ConcreteCategory.congr_hom hmaps coordinate
  change algebraMap AmbientRing
      (Localization.Away rightGenerator) coordinate =
    reflectedRightRingHom coordinate at hcoord
  rw [reflectedRightRingHom_coordinate] at hcoord
  have hinjective : Function.Injective
      (algebraMap AmbientRing (Localization.Away rightGenerator)) :=
    IsLocalization.injective (Localization.Away rightGenerator)
      (powers_le_nonZeroDivisors_of_noZeroDivisors
        reflectedRightGenerator_ne_zero)
  have hsource : coordinate = rightGenerator := hinjective hcoord
  have heval := congrArg (evaluationRingHom 0) hsource
  simp [evaluationRingHom, coordinate, rightGenerator] at heval

/-- The reflected right chart fails the interpretation clause of chart validity. -/
theorem brokenRightChart_not_valid :
    ¬ IsArchitectureAffineChart referenceRaw brokenRightChart := by
  intro hvalid
  exact brokenRightChart_interpretation_ne hvalid.interpretation_compatible

/--
All positive component theorems fire simultaneously in the fixed standard-geometry model.

This theorem is assembled only from the component theorems; it does not replace their
individual executable contracts or the negative fixtures above.
-/
theorem standardGeometryReference_fires :
    Presheaf.IsSheaf referenceSite.topology referenceRaw.toPresheaf ∧
    (∀ W : referenceSite.category,
      IsIso (referenceRaw.toRingedSite.canonical.app (op W))) ∧
    (⨆ i, ((referenceScheme.affineOpenCover referenceRaw).f i).opensRange = ⊤) ∧
    AlgebraicGeometry.IsOpenImmersion
      (referenceScheme.atlas.chart leftIndex).map ∧
    AlgebraicGeometry.IsOpenImmersion
      (referenceScheme.atlas.chart rightIndex).map ∧
    ¬ IsIso (referenceScheme.atlas.chart leftIndex).map ∧
    ¬ IsIso (referenceScheme.atlas.chart rightIndex).map ∧
    Nonempty (referenceScheme.atlas.actualOverlap
      referenceRaw leftIndex rightIndex) ∧
    ¬ IsIso (sheafifiedRestriction referenceRaw leftToBase) ∧
    Ideal.map ambientGlobalSectionsIso.hom.hom
        (weakIdealSheaf.ideal ambientTopAffineOpen) = weakAmbientIdeal ∧
    Ideal.map ambientGlobalSectionsIso.hom.hom
        (strongIdealSheaf.ideal ambientTopAffineOpen) = strongAmbientIdeal ∧
    Ideal.map ambientGlobalSectionsIso.hom.hom
        (rigidIdealSheaf.ideal ambientTopAffineOpen) = rigidAmbientIdeal ∧
    Ideal.map leftChartGlobalSectionsIso.hom.hom
        ((weakIdealSheaf.comap leftChart.map).ideal
          ⟨⊤, @isAffineOpen_top leftChart.domain leftChart.domain_isAffine⟩) =
      weakLeftIdeal ∧
    Ideal.map rightChartGlobalSectionsIso.hom.hom
        ((weakIdealSheaf.comap rightChart.map).ideal
          ⟨⊤, @isAffineOpen_top rightChart.domain rightChart.domain_isAffine⟩) =
      weakRightIdeal ∧
    Ideal.map actualOverlapGlobalSectionsIso.hom.hom
        ((weakIdealSheaf.comap
          (referenceScheme.atlas.actualOverlapToUnderlying
            referenceRaw leftIndex rightIndex)).ideal
          ⟨⊤, @isAffineOpen_top
            (referenceScheme.atlas.actualOverlap referenceRaw leftIndex rightIndex)
            (IsAffine.of_isIso actualOverlapIso.hom)⟩) =
      weakOverlapIdeal ∧
    (weakIdealSheaf.comap leftChart.map).comap
        (pullback.fst leftChart.map rightChart.map) =
      (weakIdealSheaf.comap rightChart.map).comap
        (pullback.snd leftChart.map rightChart.map) ∧
    Ideal.map leftChartGlobalSectionsIso.hom.hom
        ((strongIdealSheaf.comap leftChart.map).ideal
          ⟨⊤, @isAffineOpen_top leftChart.domain leftChart.domain_isAffine⟩) =
      strongLeftIdeal ∧
    Ideal.map rightChartGlobalSectionsIso.hom.hom
        ((strongIdealSheaf.comap rightChart.map).ideal
          ⟨⊤, @isAffineOpen_top rightChart.domain rightChart.domain_isAffine⟩) =
      strongRightIdeal ∧
    Ideal.map actualOverlapGlobalSectionsIso.hom.hom
        ((strongIdealSheaf.comap
          (referenceScheme.atlas.actualOverlapToUnderlying
            referenceRaw leftIndex rightIndex)).ideal
          ⟨⊤, @isAffineOpen_top
            (referenceScheme.atlas.actualOverlap referenceRaw leftIndex rightIndex)
            (IsAffine.of_isIso actualOverlapIso.hom)⟩) =
      strongOverlapIdeal ∧
    (strongIdealSheaf.comap leftChart.map).comap
        (pullback.fst leftChart.map rightChart.map) =
      (strongIdealSheaf.comap rightChart.map).comap
        (pullback.snd leftChart.map rightChart.map) ∧
    weakAmbientIdeal ≠ ⊥ ∧ weakAmbientIdeal ≠ ⊤ ∧
    strongAmbientIdeal ≠ ⊥ ∧ strongAmbientIdeal ≠ ⊤ ∧
    weakIdealSheaf < strongIdealSheaf ∧
    rigidAmbientIdeal ≠ ⊥ ∧ rigidAmbientIdeal ≠ ⊤ ∧
    strongIdealSheaf < rigidIdealSheaf ∧
    weakImmersion.ker = weakIdealSheaf ∧
    strongImmersion.ker = strongIdealSheaf ∧
    Set.range weakImmersion = weakIdealSheaf.support ∧
    Set.range strongImmersion = strongIdealSheaf.support ∧
    IsIso weakAffineQuotientChart ∧ IsIso strongAffineQuotientChart ∧
    Nonempty weakLocus ∧ Nonempty strongLocus ∧ Nonempty rigidLocus ∧
    ¬ IsIso weakImmersion ∧ ¬ IsIso strongImmersion ∧ ¬ IsIso rigidImmersion ∧
    SemanticLawfulAlong referenceRaw referenceScheme weakReading zeroPoint ∧
    WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed zeroPoint ∧
    IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed zeroPoint ∧
    Nonempty (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed zeroPoint) ∧
    SemanticLawfulAlong referenceRaw referenceScheme strongReading zeroPoint ∧
    WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed zeroPoint ∧
    IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed zeroPoint ∧
    Nonempty (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed zeroPoint) ∧
    SemanticLawfulAlong referenceRaw referenceScheme weakReading onePoint ∧
    WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed onePoint ∧
    IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed onePoint ∧
    Nonempty (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed onePoint) ∧
    ¬ SemanticLawfulAlong referenceRaw referenceScheme strongReading onePoint ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed onePoint ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed onePoint ∧
    ¬ Nonempty (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed onePoint) ∧
    ¬ SemanticLawfulAlong referenceRaw referenceScheme weakReading twoPoint ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed twoPoint ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed twoPoint ∧
    ¬ Nonempty (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
      weakReading weakReading_valid weakReading_requiredClosed twoPoint) ∧
    ¬ SemanticLawfulAlong referenceRaw referenceScheme strongReading twoPoint ∧
    ¬ WitnessVanishes referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed twoPoint ∧
    ¬ IdealLawfulAlong referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed twoPoint ∧
    ¬ Nonempty (FactorsThroughLawfulClosedSubscheme referenceRaw referenceScheme
      strongReading strongReading_valid strongReading_requiredClosed twoPoint) ∧
    AlgebraicGeometry.IsClosedImmersion lawComparison ∧
    lawComparison ≫ weakImmersion = strongImmersion ∧
    ¬ IsIso lawComparison ∧
    AlgebraicGeometry.IsClosedImmersion strongToRigidComparison ∧
    strongToRigidComparison ≫ strongImmersion = rigidImmersion ∧
    ¬ IsIso strongToRigidComparison ∧
    strongToRigidComparison ≫ lawComparison = weakToRigidComparison ∧
    ¬ Function.Surjective coefficientChange.hom ∧
    IsPullback
      ((referenceScheme.baseChangedAtlas referenceRaw coefficientChange).chart
        (cast (referenceScheme.baseChangedAtlas_Index
          referenceRaw coefficientChange).symm leftIndex)).map
      (referenceScheme.baseChangedChartMap referenceRaw coefficientChange leftIndex)
      (referenceScheme.baseChangeMap referenceRaw coefficientChange)
      (referenceScheme.atlas.chart leftIndex).map ∧
    IsPullback
      ((referenceScheme.baseChangedAtlas referenceRaw coefficientChange).chart
        (cast (referenceScheme.baseChangedAtlas_Index
          referenceRaw coefficientChange).symm rightIndex)).map
      (referenceScheme.baseChangedChartMap referenceRaw coefficientChange rightIndex)
      (referenceScheme.baseChangeMap referenceRaw coefficientChange)
      (referenceScheme.atlas.chart rightIndex).map ∧
    Scheme.IdealSheafData.comap weakIdealSheaf
        (referenceScheme.baseChangeMap referenceRaw coefficientChange) =
      lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom) coefficientChangedScheme
        coefficientChangedWeakReading coefficientChangedWeakReading_valid
        coefficientChangedWeakReading_requiredClosed ∧
    Scheme.IdealSheafData.comap strongIdealSheaf
        (referenceScheme.baseChangeMap referenceRaw coefficientChange) =
      lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom) coefficientChangedScheme
        coefficientChangedStrongReading coefficientChangedStrongReading_valid
        coefficientChangedStrongReading_requiredClosed ∧
    lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom) coefficientChangedScheme
        coefficientChangedWeakReading coefficientChangedWeakReading_valid
        coefficientChangedWeakReading_requiredClosed <
      lawGeneratedIdealSheaf
        (referenceRaw.baseChange coefficientChange.hom) coefficientChangedScheme
        coefficientChangedStrongReading coefficientChangedStrongReading_valid
        coefficientChangedStrongReading_requiredClosed ∧
    AlgebraicGeometry.IsClosedImmersion coefficientChangedLawComparison ∧
    coefficientChangedWeakToStrong.lawMap = weakToStrong.lawMap ∧
    coefficientChangedWeakToStrong.atomMap = weakToStrong.atomMap ∧
    ¬ IsIso coefficientChangedLawComparison ∧
    coefficientChangedLawComparison ≫
        lawfulClosedSubschemeBaseChangeMap referenceRaw referenceScheme
          weakLawEquationCore weakSchemeBridge coefficientChange =
      lawfulClosedSubschemeBaseChangeMap referenceRaw referenceScheme
          strongLawEquationCore strongSchemeBridge coefficientChange ≫
        lawComparison ∧
    ¬ IsIso (referenceScheme.baseChangeMap referenceRaw coefficientChange) := by
  rcases zeroPoint_fires with ⟨z1, z2, z3, z4, z5, z6, z7, z8⟩
  rcases onePoint_fires with ⟨o1, o2, o3, o4, o5, o6, o7, o8⟩
  rcases twoPoint_fires with ⟨t1, t2, t3, t4, t5, t6, t7, t8⟩
  exact ⟨
    referenceRaw_isSheaf, fun W => canonical_component_isIso W,
    twoChart_jointlyCovers, left_chart_isOpenImmersion,
    right_chart_isOpenImmersion, left_chart_not_isIso, right_chart_not_isIso,
    actualOverlap_nonempty, left_restriction_not_isIso,
    weakIdeal_top_eq, strongIdeal_top_eq, rigidIdeal_top_eq,
    weakIdeal_left_eq, weakIdeal_right_eq, weakIdeal_overlap_eq,
    weakIdeal_overlap_agrees, strongIdeal_left_eq, strongIdeal_right_eq,
    strongIdeal_overlap_eq, strongIdeal_overlap_agrees,
    weakAmbientIdeal_ne_bot, weakAmbientIdeal_ne_top,
    strongAmbientIdeal_ne_bot, strongAmbientIdeal_ne_top,
    weakIdeal_lt_strongIdeal, rigidAmbientIdeal_ne_bot, rigidAmbientIdeal_ne_top,
    strongIdeal_lt_rigidIdeal, weakImmersion_ker, strongImmersion_ker,
    weakImmersion_zeroLocus, strongImmersion_zeroLocus,
    weakAffineQuotientChart_isIso, strongAffineQuotientChart_isIso,
    weakLocus_nonempty, strongLocus_nonempty, rigidLocus_nonempty,
    weakImmersion_not_isIso, strongImmersion_not_isIso, rigidImmersion_not_isIso,
    z1, z2, z3, z4, z5, z6, z7, z8,
    o1, o2, o3, o4, o5, o6, o7, o8,
    t1, t2, t3, t4, t5, t6, t7, t8,
    lawComparison_isClosedImmersion, lawComparison_immersion,
    lawComparison_not_isIso, strongToRigidComparison_isClosedImmersion,
    strongToRigidComparison_immersion, strongToRigidComparison_not_isIso,
    lawComparison_comp_fires, coefficientChange_not_surjective,
    leftChart_baseChange_isPullback, rightChart_baseChange_isPullback,
    weakIdeal_baseChange, strongIdeal_baseChange, coefficientChanged_ideal_strict,
    coefficientChangedLawComparison_isClosedImmersion,
    coefficientChangedWeakToStrong_lawMap,
    coefficientChangedWeakToStrong_atomMap,
    coefficientChangedLawComparison_not_isIso,
    coefficient_law_comparison_square, coefficientChange_schemeMap_not_isIso⟩


end
end AAT.AG.Examples.StandardGeometryReferenceModels
