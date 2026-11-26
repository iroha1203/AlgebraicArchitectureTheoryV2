import Formal.SHIGURE.Part2.Schemes.OpenDataRestriction

/-! # Descent comparisons on an open cover

The double overlaps of the descent category coincide with the geometric
overlaps used to glue actual modules in Appendix B.6.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Scheme.Modules TopologicalSpace

noncomputable section

universe u

variable {X : Scheme.{u}} (cover : Scheme.OpenCover.{u} X)
  (data : quasiCoherentModulesPseudofunctor.DescentData cover.f)

private theorem openCover_overlap_right (i j : cover.I₀) :
    overlapRight cover.gluedCover i j = pullback.snd (cover.f i) (cover.f j) := by
  change (pullbackSymmetry _ _).hom ≫ pullback.fst _ _ = pullback.snd _ _
  simp

/-- A quasi-coherent open-cover descent datum supplies actual local module
sheaves and transition isomorphisms on the geometric double overlaps. -/
noncomputable def openDescentGlueData : ModuleGluingData cover.gluedCover where
  module i := (data.obj i).obj
  transition i j := by
    let p := cover.gluedCover.f i j
    let q := overlapRight cover.gluedCover i j
    have same : q ≫ cover.f j = p ≫ cover.f i := by
      show overlapRight cover.gluedCover i j ≫ cover.f j = p ≫ cover.f i
      rw [openCover_overlap_right]
      exact pullback.condition.symm
    exact openDataRestrictIso data (p ≫ cover.f i) p q rfl same

variable {D : Scheme.GlueData.{u}} (i : D.J) (W : D.glued.Opens)
  (inside : W ≤ (D.ι i).opensRange)

/-- Factor an open of the glued scheme through a chart that contains it. -/
def openChartLift : (W : Scheme) ⟶ D.U i :=
  IsOpenImmersion.lift (D.ι i) W.ι (by simpa only [Scheme.Opens.range_ι] using inside)

/-- Composing the chart lift with the chart map gives the original inclusion. -/
theorem openChartLift_fac : openChartLift i W inside ≫ D.ι i = W.ι :=
  IsOpenImmersion.lift_fac _ _ _

instance : IsOpenImmersion (openChartLift i W inside) := by
  haveI : IsOpenImmersion (openChartLift i W inside ≫ D.ι i) := by
    rw [openChartLift_fac]
    infer_instance
  exact IsOpenImmersion.of_comp _ (D.ι i)

/-- An open immersion factored through a larger open has the corresponding inverse image. -/
theorem openLift_image_top {Y Z : Scheme.{u}} (f : Y ⟶ Z) [IsOpenImmersion f]
    (U : Z.Opens) (g : (U : Scheme) ⟶ Y) [IsOpenImmersion g] (fac : g ≫ f = U.ι)
    (inside : U ≤ f.opensRange) : g ''ᵁ ⊤ = f ⁻¹ᵁ U := by
  apply f.image_injective
  change f ''ᵁ (g ''ᵁ ⊤) = f ''ᵁ (f ⁻¹ᵁ U)
  have image : (g ≫ f) ''ᵁ ⊤ = U := by
    rw [Scheme.Hom.image_top_eq_opensRange]
    apply Opens.ext
    change Set.range (g ≫ f) = (U : Set Z)
    rw [fac, U.range_ι]
  rw [← Scheme.Hom.comp_image, image, f.image_preimage_eq_opensRange_inf, inf_eq_right.mpr inside]

/-- The lift has image equal to the inverse image of the original open. -/
theorem openChartLift_image_top : openChartLift i W inside ''ᵁ ⊤ = D.ι i ⁻¹ᵁ W :=
  openLift_image_top (D.ι i) W _ (openChartLift_fac i W inside) inside

/-- Sections on an image open are top sections of the corresponding restricted module. -/
def openTopSectionsIso {T Y : Scheme.{u}} (M : Y.Modules)
    (f : T ⟶ Y) [IsOpenImmersion f] (V : Y.Opens) (image : f ''ᵁ ⊤ = V) :
    Γ(M, V) ≅ Γ(M.restrict f, ⊤) :=
  M.presheaf.mapIso (eqToIso image).op

/-- Sections on the chart inverse image agree with top sections of the restriction to the test open. -/
def openChartTopSectionsIso (M : (D.U i).Modules) :
    Γ(M, D.ι i ⁻¹ᵁ W) ≅ Γ(M.restrict (openChartLift i W inside), ⊤) :=
  openTopSectionsIso M _ _ (openChartLift_image_top i W inside)


end

end SHIGURE.SchemeDescent
