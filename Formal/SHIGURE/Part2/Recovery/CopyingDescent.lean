import Formal.SHIGURE.Part2.Recovery.CechArrows
import Formal.SHIGURE.Part2.Recovery.CopyingRepresentations
import Formal.SHIGURE.Part2.Recovery.StructureDescent

/-!
# Zariski descent of locally split copying models

A coherent family of chart structures glues to a model. The
result recovers the chart models and their transition maps. A
compatible family of their preservation maps has a unique extension.
-/

open AlgebraicGeometry CategoryTheory

universe u

noncomputable section

namespace SHIGURE.Copying

variable {S : Scheme.{u}} {C : Scheme.OpenCover.{u} S} {T : Theory.{u}}

namespace StructureCharts

/-- The glued copying model restricts to the prescribed model on every chart. -/
def glueModelRestrictIso {D : StructureCharts C T.signature} (hD : D.Coherent)
    (models : ∀ i, zariskiCopyingProperty T (C.X i) (D.chart i)) (i : C.I₀) :
    (restrictCopyingCoefficients T (C.f i)).obj (glueModel hD models) ≅ ⟨D.chart i, models i⟩ :=
  (zariskiCopyingProperty T (C.X i)).fullyFaithfulι.preimageIso (D.restrictGlueIso hD i)

/-- The descended model is represented on every primitive object by the glued relative schemes. -/
def glueModelRepresentation {D : StructureCharts C T.signature} (hD : D.Coherent)
    (models : ∀ i, zariskiCopyingProperty T (C.X i) (D.chart i)) :
    CopyingRepresentation (glueModel hD models).obj :=
  CopyingRepresentation.ofSplit (glueModel hD models).property.1

end StructureCharts

/-- Coherent local arrows between copying models descend uniquely as arrows in their semantic category. -/
theorem existsUnique_copyingMap_ofOverlaps (A B : (zariskiCopyingProperty T S).FullSubcategory)
    (localMap : ∀ i, (restrictCopyingCoefficients T (C.f i)).obj A ⟶ (restrictCopyingCoefficients T (C.f i)).obj B)
    (w : ∀ s, SheafArrowsAgreeOnOverlaps (fun i => (localMap i).hom.onSort s)) :
    ∃! m : A ⟶ B, ∀ i, (restrictCopyingCoefficients T (C.f i)).map m = localMap i := by
  obtain ⟨f, hf, hu⟩ := existsUnique_structureMap_ofOverlaps (fun i => (localMap i).hom) w
  refine ⟨ObjectProperty.homMk f, ?_, ?_⟩
  · intro i
    exact ObjectProperty.hom_ext _ (hf i)
  · intro g hg
    apply ObjectProperty.hom_ext
    exact hu g.hom (fun i => congrArg (fun m : (restrictCopyingCoefficients T (C.f i)).obj A ⟶
      (restrictCopyingCoefficients T (C.f i)).obj B => m.hom) (hg i))

end SHIGURE.Copying
