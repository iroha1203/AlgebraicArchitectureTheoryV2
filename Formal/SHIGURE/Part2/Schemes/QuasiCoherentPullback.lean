import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
import Formal.SHIGURE.Part2.Schemes.QuasiCoherentModules

/-! # Pullback of quasi-coherent modules

The pullback along an arbitrary scheme morphism agrees with extension
of scalars whenever its source and target are restricted to affine opens.
Mathlib's full subcategory construction restricts the actual pseudofunctor
of module sheaves to these modules and retains its composition isomorphisms.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Bicategory Scheme.Modules TopologicalSpace

noncomputable section

universe u

variable {X Y : Scheme.{u}}

/-- On affine opens related by a scheme morphism, the actual pulled-back
presentation is the associated module of the extension along the section map. -/
def pullbackTildePresentationIso {f : Y ⟶ X} {M : X.Modules} {U : X.Opens} {V : Y.Opens}
    {hU : IsAffineOpen U} {hV : IsAffineOpen V} (inside : V ≤ f ⁻¹ᵁ U)
    {N : ModuleCat.{u} Γ(X, U)} (e : (tilde.functor Γ(X, U)).obj N ≅ M.restrict hU.fromSpec) :
    (tilde.functor Γ(Y, V)).obj ((ModuleCat.extendScalars (f.appLE U V inside).hom).obj N) ≅
      ((Scheme.Modules.pullback f).obj M).restrict hV.fromSpec := by
  let a := f.appLE U V inside
  have square : Spec.map a ≫ hU.fromSpec = hV.fromSpec ≫ f :=
    IsAffineOpen.SpecMap_appLE_fromSpec f hU hV inside
  exact ((tildePullbackIso a).app N).symm ≪≫
    (Scheme.Modules.pullback (Spec.map a)).mapIso
      (e ≪≫ (restrictFunctorIsoPullback hU.fromSpec).app M) ≪≫
    (pullbackComp (Spec.map a) hU.fromSpec).app M ≪≫
    (pullbackCongr square).app M ≪≫ ((pullbackComp hV.fromSpec f).app M).symm ≪≫
    ((restrictFunctorIsoPullback hV.fromSpec).app ((Scheme.Modules.pullback f).obj M)).symm

/-- On an affine open in the inverse image of an affine open in the base,
pullback of a tilde presentation is given by the actual section ring map. -/
theorem HasTildeOn.pullback {f : Y ⟶ X} {M : X.Modules} {U : X.Opens} {V : Y.Opens}
    {hU : IsAffineOpen U} {hV : IsAffineOpen V} (inside : V ≤ f ⁻¹ᵁ U)
    (presentation : HasTildeOn M hU) : HasTildeOn ((Scheme.Modules.pullback f).obj M) hV := by
  obtain ⟨N, ⟨e⟩⟩ := presentation
  exact ⟨(ModuleCat.extendScalars (f.appLE U V inside).hom).obj N,
    ⟨pullbackTildePresentationIso (hV := hV) inside e⟩⟩

/-- The affine opens lying in an inverse image of a member of an open
cover cover the source of any morphism. -/
theorem iSup_affineOpens_in_preimage_eq_top (f : Y ⟶ X) {ι : Type*} (U : ι → X.Opens)
    (covers : (⨆ i, U i) = ⊤) :
    (⨆ V : {V : Y.affineOpens // ∃ i : ι, V.1 ≤ f ⁻¹ᵁ U i}, (V.val : Y.Opens)) = ⊤ := by
  apply top_le_iff.mp
  intro y _
  obtain ⟨i, hyU⟩ := Opens.mem_iSup.mp (covers.ge (Set.mem_univ (f y)))
  have hyPreimage : y ∈ f ⁻¹ᵁ U i := hyU
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hyPreimage (f ⁻¹ᵁ U i).isOpen
  exact Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, i, hVU⟩, hyV⟩

/-- Pullback along any scheme morphism preserves quasi-coherent modules. -/
theorem IsQuasiCoherentModule.pullback {f : Y ⟶ X} {M : X.Modules}
    (coherent : IsQuasiCoherentModule M) : IsQuasiCoherentModule ((Scheme.Modules.pullback f).obj M) := by
  let I := {V : Y.affineOpens // ∃ U : X.affineOpens, V.1 ≤ f ⁻¹ᵁ U.1}
  apply (isQuasiCoherentModule_iff_affineCover _).mpr
  refine ⟨I, Subtype.val, iSup_affineOpens_in_preimage_eq_top f Subtype.val
    (iSup_affineOpens_eq_top X), ?_⟩
  rintro ⟨V, U, inside⟩
  exact (coherent U).pullback inside

private abbrev modulesPseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{u, u + 1} :=
  Scheme.Modules.pseudofunctor.comp Adj.forget₁

/-- Quasi-coherence as a fiberwise property of the actual scheme-module pseudofunctor. -/
def quasiCoherentModulesProperty : modulesPseudofunctor.{u}.ObjectProperty where
  prop X M := IsQuasiCoherentModule (X := X.as.unop) M

private theorem quasiCoherentModulesProperty_closed :
    quasiCoherentModulesProperty.{u}.IsClosedUnderMapObj where
  map_obj coherent f := IsQuasiCoherentModule.pullback (f := f.as.unop) coherent

/-- The pseudofunctor of quasi-coherent modules and all module morphisms. -/
def quasiCoherentModulesPseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) Cat.{u, u + 1} :=
  letI := quasiCoherentModulesProperty_closed
  quasiCoherentModulesProperty.fullsubcategory


end

end SHIGURE.SchemeDescent
