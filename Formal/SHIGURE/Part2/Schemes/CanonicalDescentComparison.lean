import Formal.SHIGURE.Part2.Schemes.DescentComparisons
import Formal.SHIGURE.Part2.Schemes.ComposedModulePullback

/-! # The canonical comparison after forgetting quasi-coherence -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite Scheme.Modules

noncomputable section

universe u

private abbrev F := quasiCoherentModulesPseudofunctor

private theorem singleton_ofObj_map_abstract
    {C : Type*} [Category C]
    {G : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat}
    {ι : Type*} {X T : C} {U : ι → C} {f : ∀ i, U i ⟶ X}
    (M : G.obj (.mk (op X))) (c : T ⟶ X) {i j : ι}
    (a : T ⟶ U i) (b : T ⟶ U j) (ha : a ≫ f i = c) (hb : b ≫ f j = c)
    {D : Type*} [Category D] (I : G.obj (.mk (op T)) ⥤ D) :
    I.map ((DescentData.ofObj (F := G) (f := f) M).hom c a b ha hb) =
      I.map ((G.mapComp' (f i).op.toLoc a.op.toLoc c.op.toLoc
        (congrArg (fun g => g.op.toLoc) ha)).inv.toNatTrans.app M) ≫
      I.map ((G.mapComp' (f j).op.toLoc b.op.toLoc c.op.toLoc
        (congrArg (fun g => g.op.toLoc) hb)).hom.toNatTrans.app M) := by
  simp only [DescentData.ofObj_hom, Functor.map_comp]

section OriginalComparison

variable {S U T : Scheme.{u}} (a : U ⟶ S) (r s : T ⟶ U) (base : T ⟶ S)
  (hr : r ≫ a = base) (hs : s ≫ a = base) (M : F.obj (.mk (op S)))

set_option maxHeartbeats 550000 in
/-- The canonical singleton comparison is the composition of the two actual
inverse-image comparisons over the shared base map. -/
theorem singletonCanonicalComparison_forget :
    (quasiCoherentModulesProperty.prop (.mk (op T))).ι.map
      (((F.toDescentData (fun _ : Unit => a)).obj M).hom base (i₁ := ()) (i₂ := ()) r s hr hs) =
    ((pullbackComp r a).hom.app M.obj ≫ (pullbackCongr hr).hom.app M.obj) ≫
      ((pullbackCongr hs.symm).hom.app M.obj ≫ (pullbackComp s a).inv.app M.obj) := by
  exact (singleton_ofObj_map_abstract (G := F) (f := fun _ : Unit => a)
    M base (i := ()) (j := ()) r s hr hs
    (quasiCoherentModulesProperty.prop (.mk (op T))).ι).trans
      (congrArg₂ (· ≫ ·) (quasiCoherentMapComp'_inv r a base hr M)
        (quasiCoherentMapComp'_hom s a base hs M))

end OriginalComparison

private theorem pullbackCongr_chain {S T : Scheme.{u}}
    {a b c d k : T ⟶ S} (h₁ : a = b) (h₂ : b = c) (h₃ : c = d)
    (g₁ : a = k) (g₂ : k = d) (M : S.Modules) :
    (pullbackCongr h₁).hom.app M ≫ (pullbackCongr h₂).hom.app M ≫ (pullbackCongr h₃).hom.app M =
      (pullbackCongr g₁).hom.app M ≫ (pullbackCongr g₂).hom.app M := by
  subst b
  subst c
  subst d
  subst k
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]

set_option maxHeartbeats 700000 in
/-- Compare the two canonical restrictions through chosen representatives
of the two equal composites on the test scheme. -/
theorem singletonCanonicalComparison_along
    {S U T : Scheme.{u}} (a : U ⟶ S) (r s : T ⟶ U)
    (b₀ b₁ b : T ⟶ S) (hr : r ≫ a = b) (hs : s ≫ a = b)
    (h₀ : r ≫ a = b₀) (h₁ : s ≫ a = b₁) (equal : b₀ = b₁)
    (M : F.obj (.mk (op S))) :
    (quasiCoherentModulesProperty.prop (.mk (op T))).ι.map
      (((F.toDescentData (fun _ : Unit => a)).obj M).hom b
        (i₁ := ()) (i₂ := ()) r s hr hs) =
    (pullbackCompositionFor a r b₀ h₀).hom.app M.obj ≫
      (pullbackCongr equal).hom.app M.obj ≫ (pullbackCompositionFor a s b₁ h₁).inv.app M.obj := by
  refine (singletonCanonicalComparison_forget a r s b hr hs M).trans ?_
  let left := (pullbackComp r a).app M.obj
  let right := (pullbackComp s a).app M.obj
  let forward := (pullbackCongr h₀).app M.obj
  let backward := (pullbackCongr h₁.symm).app M.obj
  let middle := (pullbackCongr equal).app M.obj
  let first := (pullbackCongr hr).app M.obj
  let last := (pullbackCongr hs.symm).app M.obj
  change (left.hom ≫ first.hom) ≫ (last.hom ≫ right.inv) =
    (left.hom ≫ forward.hom) ≫ middle.hom ≫ backward.hom ≫ right.inv
  have chain := pullbackCongr_chain h₀ equal h₁.symm hr hs.symm M.obj
  have composite := congrArg (fun k => left.hom ≫ k ≫ right.inv) chain
  simpa only [Category.assoc] using composite.symm


end

end SHIGURE.SchemeDescent
