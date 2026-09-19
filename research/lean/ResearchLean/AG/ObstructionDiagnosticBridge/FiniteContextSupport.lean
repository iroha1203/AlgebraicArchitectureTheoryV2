import ResearchLean.AG.ObstructionDiagnosticBridge.FiniteCoverGeometry
import Formal.AG.SemanticRepair.Conormal.LawGeneratedBooleanCircleSite
import Mathlib.CategoryTheory.Sites.Continuous
import Formal.Util.AssertStandardAxioms

/-!
# AAT context support for the selected coarse G-125 cover

This module attaches the concrete coarse three-patch geometry to the existing
nondegenerate Boolean-lattice AAT site.  Its selected indices are ordered by
reverse inclusion.  A selected context is sent to the intersection of the
patches in its index; hence readable refinement becomes inclusion of open
supports.

The site's actual admissible three-chart cover is proved to map to the Cycle 9
coarse open cover.  Continuity of the support functor is deliberately not
claimed here: its proof must use this real cover and its base changes, rather
than a degenerate topology with no admissible families.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AAT.AG.ObstructionDiagnosticBridge
namespace SelectedFiniteContextSupport

open SelectedFiniteGeometry

open AAT.AG.SemanticRepair.Conormal.LawGeneratedBooleanCircleSite

/-- The fixed correspondence between Boolean indices and coarse charts. -/
def coarseChartOfFin : Fin 3 → CoarseChart
  | 0 => .c0
  | 1 => .c1
  | 2 => .c2

/-- The inverse index of a coarse chart. -/
def coarseChartIndex : CoarseChart → Fin 3
  | .c0 => 0
  | .c1 => 1
  | .c2 => 2

@[simp]
theorem coarseChartOfFin_index (chart : CoarseChart) :
    coarseChartOfFin (coarseChartIndex chart) = chart := by
  cases chart <;> rfl

@[simp]
theorem coarseChartIndex_ofFin (i : Fin 3) :
    coarseChartIndex (coarseChartOfFin i) = i := by
  fin_cases i <;> rfl

/-- Open support of a selected Boolean-lattice context.

The empty index is the full space and union of indices becomes intersection
of supports.
-/
def coarseSupportOfIndex (s : ContextIndex) : Opens Space :=
  ⨅ i : {i // i ∈ s}, coarsePatch (coarseChartOfFin i)

/-- Reverse inclusion of indices induces inclusion of open supports. -/
theorem coarseSupportOfIndex_mono {s t : ContextIndex}
    (h : t ⊆ s) : coarseSupportOfIndex s ≤ coarseSupportOfIndex t := by
  refine le_iInf fun i => ?_
  exact iInf_le_of_le (⟨i, h i.property⟩ : {j // j ∈ s}) le_rfl

/-- The support of a singleton Boolean index is its selected patch. -/
theorem coarseSupportOfIndex_singleton (i : Fin 3) :
    coarseSupportOfIndex {i} = coarsePatch (coarseChartOfFin i) := by
  apply le_antisymm
  · exact iInf_le_of_le (⟨i, by simp⟩ : {j // j ∈ ({i} : ContextIndex)}) le_rfl
  · refine le_iInf fun j => ?_
    have hj : (j : Fin 3) = i := Finset.mem_singleton.mp j.property
    rw [hj]

/-- The support of a two-element Boolean index is the patch intersection. -/
theorem coarseSupportOfIndex_pair (i j : Fin 3) :
    coarseSupportOfIndex {i, j} =
      coarsePatch (coarseChartOfFin i) ⊓ coarsePatch (coarseChartOfFin j) := by
  apply le_antisymm
  · exact le_inf
      (iInf_le_of_le (⟨i, by simp⟩ : {k // k ∈ ({i, j} : ContextIndex)}) le_rfl)
      (iInf_le_of_le (⟨j, by simp⟩ : {k // k ∈ ({i, j} : ContextIndex)}) le_rfl)
  · refine le_iInf fun k => ?_
    have hk : (k : Fin 3) = i ∨ (k : Fin 3) = j := by
      rcases Finset.mem_insert.mp k.property with hk | hk
      · exact Or.inl hk
      · exact Or.inr (Finset.mem_singleton.mp hk)
    rcases hk with hk | hk
    · rw [hk]
      exact inf_le_left
    · rw [hk]
      exact inf_le_right

/-- The existing nondegenerate Boolean-lattice AAT site. -/
abbrev coarseSite := site

/-- Open support assigned to every object of the selected AAT context category.

Contexts outside the recognized Boolean family have bottom support.  They
have only identity arrows, so they do not affect the selected geometry.
-/
def coarseContextSupportObj (W : coarseSite.category) : Opens Space := by
  classical
  exact if h : Recognized W.ctx then
    coarseSupportOfIndex (indexOf W.ctx)
  else ⊥

/-- Every readable context arrow induces inclusion of assigned supports. -/
theorem coarseContextSupportObj_mono {W V : coarseSite.category}
    (h : W ≤ V) : coarseContextSupportObj W ≤ coarseContextSupportObj V := by
  rcases h with hEq | ⟨s, t, hs, ht, hts⟩
  · cases W
    cases V
    simp_all
  · have hW : Recognized W.ctx := ⟨s, hs⟩
    have hV : Recognized V.ctx := ⟨t, ht⟩
    simp only [coarseContextSupportObj, dif_pos hW, dif_pos hV]
    apply coarseSupportOfIndex_mono
    simpa [hs, ht] using hts

/-- The actual functor from selected AAT contexts to open supports. -/
def coarseSupportFunctor : coarseSite.category ⥤ Opens Space where
  obj := coarseContextSupportObj
  map f := homOfLE (coarseContextSupportObj_mono (leOfHom f))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The base context has empty Boolean index. -/
def coarseBaseContext : coarseSite.category :=
  Site.ContextCategoryObject.of contextPreorder
    (context ∅)

/-- Context representing one coarse chart. -/
def coarseChartContext (chart : CoarseChart) : coarseSite.category :=
  Site.ContextCategoryObject.of contextPreorder
    (context {coarseChartIndex chart})

/-- Context representing one selected coarse pair-overlap. -/
def coarseEdgeContext (edge : CoarseEdge) : coarseSite.category :=
  Site.ContextCategoryObject.of contextPreorder
    (context
      {coarseChartIndex (coarseEdgeLeft edge),
        coarseChartIndex (coarseEdgeRight edge)})

/-- Every coarse chart context maps to the base context. -/
def coarseChartToBase (chart : CoarseChart) :
    coarseChartContext chart ⟶ coarseBaseContext :=
  homOfLE (Or.inr ⟨{coarseChartIndex chart}, ∅, rfl, rfl,
    Finset.empty_subset _⟩)

/-- A coarse edge context restricts to its left chart context. -/
def coarseEdgeToLeft (edge : CoarseEdge) :
    coarseEdgeContext edge ⟶ coarseChartContext (coarseEdgeLeft edge) :=
  homOfLE (Or.inr ⟨
    {coarseChartIndex (coarseEdgeLeft edge),
      coarseChartIndex (coarseEdgeRight edge)},
    {coarseChartIndex (coarseEdgeLeft edge)}, rfl, rfl, by simp⟩)

/-- A coarse edge context restricts to its right chart context. -/
def coarseEdgeToRight (edge : CoarseEdge) :
    coarseEdgeContext edge ⟶ coarseChartContext (coarseEdgeRight edge) :=
  homOfLE (Or.inr ⟨
    {coarseChartIndex (coarseEdgeLeft edge),
      coarseChartIndex (coarseEdgeRight edge)},
    {coarseChartIndex (coarseEdgeRight edge)}, rfl, rfl, by simp⟩)

/-- A singleton chart context has exactly its selected coarse patch support. -/
@[simp]
theorem coarseSupportFunctor_chart (chart : CoarseChart) :
    coarseSupportFunctor.obj (coarseChartContext chart) = coarsePatch chart := by
  classical
  change (if h : Recognized (context {coarseChartIndex chart}) then
      coarseSupportOfIndex (indexOf (context {coarseChartIndex chart}))
    else ⊥) = coarsePatch chart
  rw [dif_pos (recognized_context _), indexOf_context]
  rw [coarseSupportOfIndex_singleton, coarseChartOfFin_index]

/-- A two-chart edge context has exactly the selected pair-overlap support. -/
@[simp]
theorem coarseSupportFunctor_edge (edge : CoarseEdge) :
    coarseSupportFunctor.obj (coarseEdgeContext edge) = coarseOverlap edge := by
  classical
  cases edge <;>
    change (if h : Recognized (context
        {coarseChartIndex (coarseEdgeLeft _),
          coarseChartIndex (coarseEdgeRight _)}) then
        coarseSupportOfIndex (indexOf (context
          {coarseChartIndex (coarseEdgeLeft _),
            coarseChartIndex (coarseEdgeRight _)}))
      else ⊥) = coarseOverlap _ <;>
    rw [dif_pos (recognized_context _), indexOf_context,
      coarseSupportOfIndex_pair] <;>
    rfl

/-- Every patch of the actual admissible AAT cover has its selected coarse support. -/
theorem coarseSupportFunctor_cover_patch (i : cover.Index) :
    coarseSupportFunctor.obj
        (Site.ContextCategoryObject.of contextPreorder (cover.patch i)) =
      coarsePatch (coarseChartOfFin i) := by
  have hpatch : cover.patch i =
      context {coarseChartIndex (coarseChartOfFin i)} := by
    simp [cover, chartContextIndex]
  rw [hpatch]
  exact coarseSupportFunctor_chart (coarseChartOfFin i)

/-- The actual admissible AAT cover maps to the concrete open cover of the space. -/
theorem coarseActualCover_support_covers (x : Space) :
    ∃ i : cover.Index,
      x ∈ coarseSupportFunctor.obj
        (Site.ContextCategoryObject.of contextPreorder (cover.patch i)) := by
  obtain ⟨chart, hchart⟩ := coarse_cover x
  exact ⟨coarseChartIndex chart, by
    rw [coarseSupportFunctor_cover_patch, coarseChartOfFin_index]
    exact hchart⟩

#assert_standard_axioms_only
  AAT.AG.ObstructionDiagnosticBridge.SelectedFiniteContextSupport

end SelectedFiniteContextSupport
end AAT.AG.ObstructionDiagnosticBridge
