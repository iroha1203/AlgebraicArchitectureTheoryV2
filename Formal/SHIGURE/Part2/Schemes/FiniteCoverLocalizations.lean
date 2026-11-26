import Formal.SHIGURE.Part2.Schemes.FiniteLocalizations
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections

/-! # Localization of sections on a finite open cover

The section maps from a cover to its intersection with an open form a
map of pairwise diagrams. Localization of the component maps implies
localization of the two actual sheaf limits.
-/

namespace SHIGURE.SchemeDescent

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe u

variable {R : Type u} [CommRing R] {X : TopCat.{u}} {ι : Type u}
variable (U : ι → Opens X) (W : Opens X)

private theorem pairwiseInf_le (j : Pairwise ι) :
    (Pairwise.diagram (fun i => U i ⊓ W)).obj j ≤ (Pairwise.diagram U).obj j := by
  cases j with
  | single i => exact inf_le_left
  | pair i j => exact inf_le_inf inf_le_left inf_le_left

private def pairwiseRestrict (F : TopCat.Sheaf (ModuleCat.{u} R) X) :
    (Pairwise.diagram U).op ⋙ F.val ⟶ (Pairwise.diagram (fun i => U i ⊓ W)).op ⋙ F.val where
  app j := F.val.map (homOfLE (pairwiseInf_le U W j.unop)).op
  naturality _ _ f := by
    simp only [Functor.comp_map, ← Functor.map_comp]
    exact congrArg F.val.map (Subsingleton.elim _ _)

private theorem iSupInf_le : (⨆ i, U i ⊓ W) ≤ ⨆ i, U i :=
  iSup_mono fun _ => inf_le_left

/-- If restriction to the intersected cover localizes all charts and
pairwise overlaps, then it localizes the section map on their unions.
This applies the Appendix B.3 compatible-section construction to a finite cover. The local
hypotheses are supplied by the single and double intersections of its principal opens. -/
theorem isLocalizedModule_sectionsRestrict_of_pairwise [Fintype ι] [DecidableEq ι]
    (F : TopCat.Sheaf (ModuleCat.{u} R) X) (S : Submonoid R)
    (localization : ∀ j : Pairwise ι,
      IsLocalizedModule S (F.val.map (homOfLE (pairwiseInf_le U W j)).op).hom) :
    IsLocalizedModule S (F.val.map (homOfLE (iSupInf_le U W)).op).hom := by
  let P := (Pairwise.diagram U).op ⋙ F.val
  let Q := (Pairwise.diagram (fun i => U i ⊓ W)).op ⋙ F.val
  let c := F.val.mapCone (Pairwise.cocone U).op
  let d := F.val.mapCone (Pairwise.cocone (fun i => U i ⊓ W)).op
  have sheaf : TopCat.Presheaf.IsSheaf F.val := F.cond
  let hc : IsLimit c := (sheaf.isSheafPairwiseIntersections (U := U)).some
  let hd : IsLimit d := (sheaf.isSheafPairwiseIntersections (U := fun i => U i ⊓ W)).some
  let e := hc.conePointUniqueUpToIso (limit.isLimit P)
  let e' := hd.conePointUniqueUpToIso (limit.isLimit Q)
  let a := pairwiseRestrict U W F
  let f := F.val.map (homOfLE (iSupInf_le U W)).op
  have equation : f ≫ e'.hom = e.hom ≫ limMap a := by
    apply limit.hom_ext
    intro j
    simp only [Category.assoc, limMap_π]
    rw [show e'.hom ≫ limit.π Q j = d.π.app j from hd.conePointUniqueUpToIso_hom_comp _ j,
      ← Category.assoc, show e.hom ≫ limit.π P j = c.π.app j from hc.conePointUniqueUpToIso_hom_comp _ j]
    change f ≫ F.val.map _ = F.val.map _ ≫ F.val.map _
    simp only [f, ← Functor.map_comp]
    exact congrArg F.val.map (Subsingleton.elim _ _)
  have equal : f = e.hom ≫ limMap a ≫ e'.inv := by
    apply (cancel_mono e'.hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using equation
  letI : IsLocalizedModule S (limMap a).hom :=
    isLocalizedModule_limitMap S a (fun j => localization j.unop)
  change IsLocalizedModule S f.hom
  rw [equal]
  letI : IsLocalizedModule S ((limMap a).hom.comp e.toLinearEquiv.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right S (limMap a).hom e.toLinearEquiv
  exact IsLocalizedModule.of_linearEquiv S
    ((limMap a).hom.comp e.toLinearEquiv.toLinearMap) e'.symm.toLinearEquiv

end

end SHIGURE.SchemeDescent
