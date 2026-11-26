import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Formal.SHIGURE.Part2.Schemes.FppfDescentFaithfulness

/-! # Epimorphisms of quasi-coherent module sheaves

## Implementation notes

The ambient cokernel of a quasi-coherent map has local tilde presentations.
After pullback to an fppf chart, an epimorphism cancels against the image of
the cokernel projection. Faithfulness on the original cover then identifies
the ambient cokernel projection with the zero map.
-/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor Opposite Scheme.Modules

noncomputable section

universe u v

variable {X Y : Scheme.{u}}

/-- On an affine open, a cokernel of maps of modules with tilde
presentations is the tilde of the cokernel of the corresponding map. -/
theorem HasTildeOn.cokernel {M N : X.Modules} (f : M ⟶ N) {U : X.Opens} {hU : IsAffineOpen U}
    (m : HasTildeOn M hU) (n : HasTildeOn N hU) : HasTildeOn (cokernel f) hU := by
  obtain ⟨P, ⟨e⟩⟩ := m
  obtain ⟨P', ⟨e'⟩⟩ := n
  let S := restrictFunctor hU.fromSpec
  let T := tilde.functor Γ(X, U)
  let ff := tilde.fullyFaithfulFunctor (R := Γ(X, U))
  let g := ff.preimage (e.hom ≫ S.map f ≫ e'.inv)
  have comm : T.map g ≫ e'.hom = e.hom ≫ S.map f := by
    simp only [g, Functor.FullyFaithful.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact ⟨Limits.cokernel g, ⟨PreservesCokernel.iso T g ≪≫
    cokernel.mapIso (T.map g) (S.map f) e e' comm ≪≫ (PreservesCokernel.iso S f).symm⟩⟩

/-- The ambient sheaf cokernel of a map of quasi-coherent modules is quasi-coherent. -/
theorem IsQuasiCoherentModule.cokernel {M N : X.Modules} (f : M ⟶ N)
    (m : IsQuasiCoherentModule M) (n : IsQuasiCoherentModule N) : IsQuasiCoherentModule (cokernel f) :=
  fun U => HasTildeOn.cokernel f (m U) (n U)

/-- The actual module sheaf pullback preserves epimorphisms along every scheme map. -/
theorem epi_modulePullback {M N : X.Modules} (f : M ⟶ N) (g : Y ⟶ X) [Epi f] :
    Epi ((Scheme.Modules.pullback g).map f) :=
  inferInstance

private abbrev Q := quasiCoherentModulesPseudofunctor.{u}

set_option maxHeartbeats 100000 in
/-- A map between quasi-coherent modules is an epimorphism of sheaves if
its actual pullback is an epimorphism on every original fppf component. -/
theorem epi_of_fppfModulePullbacks {M N : X.Modules} (f : M ⟶ N)
    (m : IsQuasiCoherentModule M) (n : IsQuasiCoherentModule N) (cover : FppfCover.{u,v} X)
    (localEpi : ∀ i, Epi ((Scheme.Modules.pullback (cover.f i)).map f)) : Epi f := by
  let N' : Q.obj (.mk (op X)) := ⟨N, n⟩
  let C : X.Modules := Limits.cokernel f
  let P' : Q.obj (.mk (op X)) := ⟨C, IsQuasiCoherentModule.cokernel f m n⟩
  let K := fppfModuleComparison cover
  let π : N' ⟶ P' := ⟨cokernel.π f⟩
  let z : N' ⟶ P' := ⟨(0 : N ⟶ C)⟩
  haveI : K.Faithful := fppfComparison_faithful cover
  have h : K.map π = K.map z := by
    apply DescentData.hom_ext
    intro i
    let G := Scheme.Modules.pullback (cover.f i)
    haveI : Epi (G.map f) := localEpi i
    have image : G.map (cokernel.π f) = G.map (0 : N ⟶ cokernel f) := by
      apply (cancel_epi (G.map f)).1
      rw [← G.map_comp, ← G.map_comp, cokernel.condition, comp_zero]
    apply ((quasiCoherentModulesProperty.prop (.mk (op (cover.X i)))).ι).map_injective
    exact image
  exact Abelian.epi_of_cokernel_π_eq_zero f (congrArg (fun t : N' ⟶ P' => t.hom) (K.map_injective h))

/-- Being an epimorphism of quasi-coherent sheaves can be checked on the
original components of an arbitrary fppf covering family. -/
theorem epi_iff_fppfModulePullbacks {M N : X.Modules} (f : M ⟶ N)
    (m : IsQuasiCoherentModule M) (n : IsQuasiCoherentModule N) (cover : FppfCover.{u,v} X) :
    Epi f ↔ ∀ i, Epi ((Scheme.Modules.pullback (cover.f i)).map f) :=
  ⟨fun h i => by
      letI := h
      exact epi_modulePullback f (cover.f i),
    epi_of_fppfModulePullbacks f m n cover⟩

end

end SHIGURE.SchemeDescent
