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

/-- Affine presentation API for Appendix B.3. The tilde presentations of
both endpoints on the given affine open determine a coefficient map. Its
cokernel presents the restriction of the actual sheaf cokernel. -/
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

/-- The affine presentation criterion in Appendix B.3 gives quasi-coherence
of the ambient sheaf cokernel from quasi-coherence of both endpoints.
This closure property places the cokernel map in the quasi-coherent fiber
where fppf pullback detects equality of maps. -/
theorem IsQuasiCoherentModule.cokernel {M N : X.Modules} (f : M ⟶ N)
    (m : IsQuasiCoherentModule M) (n : IsQuasiCoherentModule N) : IsQuasiCoherentModule (cokernel f) :=
  fun U => HasTildeOn.cokernel f (m U) (n U)

/-- Preservation direction of the surjectivity criterion of Lemma B.5 on
schemes. The actual sheaf pullback along any scheme map is left adjoint to
pushforward, so it preserves an epimorphism of module sheaves. This uses
the right exactness underlying the affine cokernel comparison in Lemma B.3. -/
theorem epi_modulePullback {M N : X.Modules} (f : M ⟶ N) (g : Y ⟶ X) [Epi f] :
    Epi ((Scheme.Modules.pullback g).map f) :=
  inferInstance

/-- The quasi-coherent module pseudofunctor whose fppf comparison detects equality of sheaf maps. -/
private abbrev Q := quasiCoherentModulesPseudofunctor.{u}

set_option maxHeartbeats 100000 in
/-- Reflection direction of the surjectivity criterion of Lemma B.5 for
an original fppf family as in Appendix B.3. Quasi-coherence of the endpoints
puts the cokernel map in the domain of the faithful comparison for the
given cover. The epimorphism on each chart forces the pullback of that
map to vanish. -/
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

/-- The public surjectivity criterion of Lemma B.5 on the fppf site of
Appendix B.3. A map of quasi-coherent sheaves is an epimorphism exactly
when its pullbacks to the original components are epimorphisms. The preservation direction
works along every scheme morphism. The reflection direction uses both
quasi-coherent endpoints to form the cokernel map in the quasi-coherent
fiber and uses the fppf family to detect equality there. -/
theorem epi_iff_fppfModulePullbacks {M N : X.Modules} (f : M ⟶ N)
    (m : IsQuasiCoherentModule M) (n : IsQuasiCoherentModule N) (cover : FppfCover.{u,v} X) :
    Epi f ↔ ∀ i, Epi ((Scheme.Modules.pullback (cover.f i)).map f) :=
  ⟨fun h i => by
      letI := h
      exact epi_modulePullback f (cover.f i),
    epi_of_fppfModulePullbacks f m n cover⟩

end

end SHIGURE.SchemeDescent
