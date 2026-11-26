import Formal.SHIGURE.Part2.Schemes.DescentCoveringRefinement
import Formal.SHIGURE.Part2.Schemes.FppfCoveringFamily
import Formal.SHIGURE.Part2.Schemes.FppfDescentFaithfulness

/-! # Fppf morphism descent from affine descent -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite
open CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat

noncomputable section

universe u

private abbrev Q := quasiCoherentModulesPseudofunctor.{u}

section MorphismPresheaf

variable {X : Scheme.{u}} (M N : Q.obj (.mk (op X))) (Y : Over X) (R : Sieve Y)

set_option maxHeartbeats 550000 in
/-- Two maps over a test scheme agree if their restrictions to a covering fppf sieve agree. -/
theorem fppfHom_isSeparatedFor (hR : Sieve.overEquiv Y R ∈ fppfTopology Y.left) :
    Presieve.IsSeparatedFor (Q.presheafHom M N) R.arrows := by
  intro x f g hf hg
  obtain ⟨cover, smaller⟩ := fppfTopology_exists_covering_family hR
  let F := fppfModuleComparison cover
  letI : F.Faithful := fppfComparison_faithful cover
  apply F.map_injective
  apply DescentData.Hom.ext
  funext i
  let p := cover.f i
  let k : Over.mk (p ≫ Y.hom) ⟶ Y := Over.homMk p
  have inR : R k := (Sieve.overEquiv_iff R p).1 (smaller p (Sieve.ofArrows_mk _ _ i))
  have equal := (hf k inR).trans (hg k inR).symm
  change pullHom f p (p ≫ Y.hom) (p ≫ Y.hom) rfl rfl =
    pullHom g p (p ≫ Y.hom) (p ≫ Y.hom) rfl rfl at equal
  change (Q.map p.op.toLoc).toFunctor.map f = (Q.map p.op.toLoc).toFunctor.map g
  rw [map_eq_pullHom f p (p ≫ Y.hom) (p ≫ Y.hom) rfl rfl,
    map_eq_pullHom g p (p ≫ Y.hom) (p ≫ Y.hom) rfl rfl, equal]

set_option maxHeartbeats 850000 in
/-- The fppf sheaf condition for morphisms can be checked on the affine opens of each test scheme. -/
theorem fppfHom_isSheafFor_of_affine
    (affineCheck : ∀ (B : CommRingCat.{u}) (S : Sieve (Spec B)),
      S ∈ fppfTopology (Spec B) → Q.IsPrestackFor S.arrows)
    (hR : Sieve.overEquiv Y R ∈ fppfTopology Y.left) :
    Presieve.IsSheafFor (Q.presheafHom M N) R.arrows := by
  let A := Y.left.affineOpenCover
  let Z := A.openCover
  let p (i : Z.I₀) : Over.mk (Z.f i ≫ Y.hom) ⟶ Y := Over.homMk (Z.f i)
  let U := Presieve.ofArrows (fun i => Over.mk (Z.f i ≫ Y.hom)) p
  have zcover : Sieve.overEquiv Y (Sieve.generate U) ∈ Scheme.zariskiTopology Y.left := by
    apply Scheme.zariskiTopology.superset_covering _ (Precoverage.generate_mem_toGrothendieck Z.mem₀)
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro i
    exact (Sieve.overEquiv_iff _ (Z.f i)).2 (Sieve.le_generate U _ (Presieve.ofArrows.mk i))
  letI := quasiCoherentModules_isZariskiStack.{u}
  apply isSheafFor_from_basis_arrows _ U R
  · rw [Presieve.isSheafFor_iff_generate]
    exact (Q.isPrestackFor' _ zcover).isSheafFor' Y M N
  · intro V f
    apply Presieve.IsSheafFor.isSeparatedFor
    apply Pseudofunctor.IsPrestackFor.isSheafFor' V _ M N
    apply Q.isPrestackFor' (J := Scheme.zariskiTopology)
    rw [Sieve.overEquiv_pullback]
    exact Scheme.zariskiTopology.pullback_stable f.left zcover
  · rintro V f ⟨i⟩
    apply Pseudofunctor.IsPrestackFor.isSheafFor' _ _ M N
    rw [Sieve.overEquiv_pullback]
    exact affineCheck (A.X i) _ (fppfTopology.pullback_stable (Z.f i) hR)
  · intro V f
    apply fppfHom_isSeparatedFor
    rw [Sieve.overEquiv_pullback]
    exact fppfTopology.pullback_stable f.left hR

end MorphismPresheaf

set_option maxHeartbeats 675000 in
/-- Covering refinements detect equality after any base change, so morphism
descent on the refinement gives morphism descent on the original sieve. -/
theorem fppf_isPrestackFor_of_covering_refinement {X : Scheme.{u}} {S R : Sieve X}
    (covering : S ∈ fppfTopology X) (smaller : S ≤ R) (base : Q.IsPrestackFor S.arrows) :
    Q.IsPrestackFor R.arrows := by
  apply (Q.isPrestackFor_iff_isSheafFor R).2
  intro M N
  let Y := Over.mk (𝟙 X)
  let small := (Sieve.overEquiv Y).symm S
  let large := (Sieve.overEquiv Y).symm R
  have inclusion : small ≤ large := fun _ f hf => smaller f.left hf
  have sheaf : Presieve.IsSheafFor (Q.presheafHom M N) small.arrows :=
    (Q.isPrestackFor_iff_isSheafFor S).1 base M N
  apply Presieve.isSheafFor_subsieve_aux _ inclusion sheaf
  intro V f _
  apply fppfHom_isSeparatedFor
  rw [Sieve.overEquiv_pullback, Equiv.apply_symm_apply]
  exact fppfTopology.pullback_stable f.left covering

/-- Affine morphism descent, together with the Zariski sheaf condition,
implies the fppf prestack property on arbitrary schemes. -/
theorem quasiCoherentModules_isFppfPrestack_of_affine
    (affineCheck : ∀ (B : CommRingCat.{u}) (S : Sieve (Spec B)),
      S ∈ fppfTopology (Spec B) → Q.IsPrestackFor S.arrows) :
    Q.{u}.IsPrestack fppfTopology where
  isSheaf {X} M N := by
    rw [isSheaf_iff_isSheaf_of_type]
    intro Y R hR
    exact fppfHom_isSheafFor_of_affine M N Y R affineCheck ((fppfTopology.mem_over_iff R).1 hR)

end

end SHIGURE.SchemeDescent
