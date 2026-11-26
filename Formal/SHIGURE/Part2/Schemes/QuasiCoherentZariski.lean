import Formal.SHIGURE.Part2.Schemes.OpenModuleGluing
import Formal.SHIGURE.Part2.Schemes.QuasiCoherentPullback

/-! # Quasi-coherence is local for open covers

The affine presentations in Appendix B can be transported from the
source of an open immersion to the corresponding affine opens of its image.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory Scheme.Modules TopologicalSpace

noncomputable section

universe u

variable {X Y : Scheme.{u}}

/-- The affine presentation of the restriction to an open subscheme also
presents the original module on the corresponding affine open of the base. -/
theorem HasTildeOn.image {f : Y ⟶ X} [IsOpenImmersion f]
    {M : X.Modules} {V : Y.Opens} {hV : IsAffineOpen V}
    {hImage : IsAffineOpen (f ''ᵁ V)} (presentation : HasTildeOn (M.restrict f) hV) :
    HasTildeOn M hImage := by
  let eRing := f.appIso V
  let a := eRing.inv
  have square : Spec.map eRing.hom ≫ hImage.fromSpec = hV.fromSpec ≫ f := by
    rw [show eRing.hom = f.appLE (f ''ᵁ V) V (f.preimage_image_eq V).ge from f.appIso_hom' V]
    exact IsAffineOpen.SpecMap_appLE_fromSpec f hImage hV (f.preimage_image_eq V).ge
  have composite : Spec.map a ≫ (hV.fromSpec ≫ f) = hImage.fromSpec := by
    rw [← square, ← Category.assoc, ← Spec.map_comp]
    change Spec.map (eRing.hom ≫ eRing.inv) ≫ hImage.fromSpec = hImage.fromSpec
    rw [Iso.hom_inv_id, Spec.map_id, Category.id_comp]
  letI : IsIso a := eRing.isIso_inv
  letI : IsOpenImmersion (Spec.map a) := inferInstance
  obtain ⟨N, ⟨e⟩⟩ := presentation
  refine ⟨(ModuleCat.extendScalars a.hom).obj N, ⟨?_⟩⟩
  exact ((tildeRestrictIso a).app N).symm ≪≫
    (restrictFunctor (Spec.map a)).mapIso (e ≪≫
      ((restrictFunctorComp hV.fromSpec f).app M).symm) ≪≫
    ((restrictFunctorComp (Spec.map a) (hV.fromSpec ≫ f)).app M).symm ≪≫
    (restrictFunctorCongr composite).app M

/-- The affine tilde presentations are preserved by isomorphisms of the actual module sheaves. -/
theorem IsQuasiCoherentModule.ofIso {M N : X.Modules} (e : M ≅ N)
    (coherent : IsQuasiCoherentModule M) : IsQuasiCoherentModule N := by
  intro U
  obtain ⟨P, ⟨presentation⟩⟩ := coherent U
  exact ⟨P, ⟨presentation ≪≫ (restrictFunctor U.property.fromSpec).mapIso e⟩⟩

/-- Restriction to an open immersion preserves the affine criterion of Appendix B. -/
theorem IsQuasiCoherentModule.restrict {M : X.Modules} {f : Y ⟶ X} [IsOpenImmersion f]
    (coherent : IsQuasiCoherentModule M) : IsQuasiCoherentModule (M.restrict f) :=
  coherent.pullback.ofIso ((restrictFunctorIsoPullback f).app M).symm

/-- Quasi-coherence can be checked on the components of any open cover.
This is the locality step for the module gluing of Appendix B.3. -/
theorem isQuasiCoherentModule_of_openCover (M : X.Modules) (cover : X.OpenCover)
    (coherent : ∀ i, IsQuasiCoherentModule (M.restrict (cover.f i))) :
    IsQuasiCoherentModule M := by
  let small := cover.ulift
  let I := Σ i : small.I₀, (small.X i).affineOpens
  let U (i : I) : X.affineOpens :=
    ⟨small.f i.1 ''ᵁ i.2.1, i.2.property.image_of_isOpenImmersion _⟩
  apply (isQuasiCoherentModule_iff_affineCover M).mpr
  refine ⟨I, U, ?_, ?_⟩
  · apply top_le_iff.mp
    intro y _
    obtain ⟨i, x, rfl⟩ := small.exists_eq y
    have covered := (iSup_affineOpens_eq_top (small.X i)).ge (Set.mem_univ x)
    obtain ⟨V, hx⟩ := Opens.mem_iSup.mp covered
    exact Opens.mem_iSup.mpr ⟨⟨i, V⟩, Set.mem_image_of_mem _ hx⟩
  · intro i
    exact (coherent (cover.idx i.1) i.2).image

/-- In Appendix B.3 the compatible-section module of Lemma B.6 is quasi-coherent
when the given chart modules are quasi-coherent. -/
theorem ModuleGluingData.compatibleModule_quasiCoherent {D : Scheme.GlueData.{u}}
    (G : ModuleGluingData D) (cocycle : G.Cocycle)
    (coherent : ∀ i, IsQuasiCoherentModule (G.module i)) :
    IsQuasiCoherentModule G.compatibleModule :=
  isQuasiCoherentModule_of_openCover G.compatibleModule D.openCover
    (fun i => (coherent i).ofIso (G.chartIso cocycle i).symm)

end

end SHIGURE.SchemeDescent
