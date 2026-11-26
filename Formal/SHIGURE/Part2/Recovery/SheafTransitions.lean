import Formal.SHIGURE.Part2.Recovery.CoverLifts
import Formal.SHIGURE.Part2.Recovery.SheafChartData

/-!
# Transition maps on common relative tests

The comparison of two lifts into the cover is evaluated at their
canonical map to the fiber product. The unit and cocycle equations are
expressed on tests with one, two, or three factorizations.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

noncomputable section

namespace SHIGURE.Copying.SheafCharts

variable {S : Scheme.{u}} {C : Scheme.OpenCover.{u} S} (D : SheafCharts C)
variable {i j l : C.I₀} {T U : Over S}

/-- Transport sections between two charts on a test equipped with both lifts. -/
def transitionAt (a : CoverLift C i T) (b : CoverLift C j T) :
    (D.chart i).val.obj (op a.test) → (D.chart j).val.obj (op b.test) := fun x =>
  (D.chart j).val.map (a.overlapRight b).inv.op
    ((D.transition i j).hom.val.app (op (a.overlapTest b))
      ((D.chart i).val.map (a.overlapLeft b).hom.op x))

/-- The comparison on common tests commutes with restriction along every map of tests. -/
theorem transitionAt_natural (a : CoverLift C i T) (b : CoverLift C j T)
    (a' : CoverLift C i U) (b' : CoverLift C j U) (g : U ⟶ T) (x : (D.chart i).val.obj (op a.test)) :
    D.transitionAt a' b' ((D.chart i).val.map (a.map a' g).op x) =
      (D.chart j).val.map (b.map b' g).op (D.transitionAt a b x) := by
  let p := Limits.pullback.fst (C.f i) (C.f j)
  let q := Limits.pullback.snd (C.f i) (C.f j)
  let h := a.overlapMap b a' b' g
  have left : (a'.overlapLeft b').hom ≫ a.map a' g = (Over.map p).map h ≫ (a.overlapLeft b).hom := by
    apply Over.OverMorphism.ext
    change 𝟙 U.left ≫ g.left = g.left ≫ 𝟙 T.left
    rw [Category.id_comp, Category.comp_id]
  have right : (b.map b' g) ≫ (a.overlapRight b).inv =
      (a'.overlapRight b').inv ≫ (Over.map q).map h := by
    apply Over.OverMorphism.ext
    change g.left ≫ 𝟙 T.left = 𝟙 U.left ≫ g.left
    rw [Category.id_comp, Category.comp_id]
  have hl : (D.chart i).val.map (a'.overlapLeft b').hom.op ((D.chart i).val.map (a.map a' g).op x) =
      (D.chart i).val.map ((Over.map p).map h).op ((D.chart i).val.map (a.overlapLeft b).hom.op x) := by
    rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp, left]
  have hn := FunctorToTypes.naturality _ _ (D.transition i j).hom.val h.op
    ((D.chart i).val.map (a.overlapLeft b).hom.op x)
  change (D.transition i j).hom.val.app (op (a'.overlapTest b'))
      ((D.chart i).val.map ((Over.map p).map h).op ((D.chart i).val.map (a.overlapLeft b).hom.op x)) =
    (D.chart j).val.map ((Over.map q).map h).op ((D.transition i j).hom.val.app (op (a.overlapTest b))
      ((D.chart i).val.map (a.overlapLeft b).hom.op x)) at hn
  unfold transitionAt
  rw [hl, hn]
  rw [← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, ← op_comp, ← op_comp, right]

/-- The diagonal and triple-overlap equations for the chosen comparison isomorphisms. -/
structure Coherent : Prop where
  /-- The diagonal comparison is the identity. -/
  unit {i : C.I₀} {T : Over S} (a : CoverLift C i T) (x : (D.chart i).val.obj (op a.test)) :
    D.transitionAt a a x = x
  /-- Passing through a third chart agrees with the direct comparison. -/
  cocycle {i j l : C.I₀} {T : Over S} (a : CoverLift C i T) (b : CoverLift C j T) (c : CoverLift C l T)
    (x : (D.chart i).val.obj (op a.test)) :
    D.transitionAt b c (D.transitionAt a b x) = D.transitionAt a c x

/-- A section over one chart extends to a section on every inverse-image chart test. -/
def extendChartSection (a : CoverLift C i T) (x : (D.chart i).val.obj (op a.test)) (j : C.I₀) :
    (D.chart j).val.obj (op (coefficientCoverTest C T j)) :=
  let ι := coefficientCoverTestInclusion C T j
  let b := a.pullback ι
  D.transitionAt b (CoverLift.chartLift C T j) ((D.chart i).val.map (a.map b ι).op x)

/-- On a test in an arbitrary chart, extension is restriction followed by transition. -/
theorem restrict_extendChartSection (a : CoverLift C i T) (x : (D.chart i).val.obj (op a.test))
    (b : CoverLift C j U) (g : U ⟶ T) :
    (D.chart j).val.map (b.toChartTest g).op (D.extendChartSection a x j) =
      D.transitionAt (a.pullback g) b ((D.chart i).val.map (a.map (a.pullback g) g).op x) := by
  let ι := coefficientCoverTestInclusion C T j
  let a₀ := a.pullback ι
  let g₀ := b.toChartBase g
  rw [extendChartSection, ← b.map_toChartBase g,
    ← D.transitionAt_natural a₀ (CoverLift.chartLift C T j) (a.pullback g) b g₀,
    ← FunctorToTypes.map_comp_apply, ← op_comp, ← CoverLift.map_comp]
  rw [CoverLift.toChartBase_inclusion]

/-- The extended sections agree on every test factoring through two charts. -/
theorem extendChartSection_agrees (hD : D.Coherent)
    (a : CoverLift C i T) (x : (D.chart i).val.obj (op a.test))
    (b : CoverLift C j U) (c : CoverLift C l U) (g : U ⟶ T) :
    D.transitionAt b c ((D.chart j).val.map (b.toChartTest g).op (D.extendChartSection a x j)) =
      (D.chart l).val.map (c.toChartTest g).op (D.extendChartSection a x l) := by
  rw [D.restrict_extendChartSection, D.restrict_extendChartSection, hD.cocycle]

end SHIGURE.Copying.SheafCharts
