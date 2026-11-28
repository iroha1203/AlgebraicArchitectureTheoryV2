import Formal.SHIGURE.Part2.Schemes.AffineSingletonFromCoefficients
import Formal.SHIGURE.Part2.Schemes.FiniteFppfMorphismDescent
import Formal.SHIGURE.Part2.Schemes.FppfGlobalMorphismDescent

/-! # Comparing fppf descent along affine refinements -/

namespace SHIGURE.SchemeDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Pseudofunctor Opposite

noncomputable section

universe u

private abbrev Q := quasiCoherentModulesPseudofunctor.{u}

variable {A : CommRingCat.{u}} {cover : FppfCover (Spec A)}

set_option maxHeartbeats 500000 in
/-- The singleton faithfully flat comparison gives the sheaf condition for
arrows of the chosen product map, with its actual scalar algebra structure. -/
theorem AffineRefinement.productMap_isPrestackFor (F : AffineRefinement cover)
    (singleton : ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
      [Module.FaithfullyFlat R S], Nonempty (Q.toDescentData (fun _ : Unit => affineScalarMap R S)).FullyFaithful) :
    Q.IsPrestackFor (Presieve.singleton (Spec.map F.productMap)) := by
  let p := Spec.map F.productMap
  letI : Algebra A F.productRing := F.productAlgebra
  letI : Module.FaithfullyFlat A F.productRing := F.productFaithfullyFlat
  have indexing : Presieve.ofArrows (fun _ : Unit => Spec F.productRing) (fun _ => p) = Presieve.singleton p := by
    rw [Presieve.ofArrows_of_unique]
  change Q.IsPrestackFor (Presieve.singleton p)
  rw [← indexing]
  exact (Q.isPrestackFor_ofArrows_iff (fun _ : Unit => p)).2 (singleton A F.productRing)

set_option maxHeartbeats 700000 in
/-- Fully faithful descent for faithfully flat affine singletons implies
the fppf prestack property, by finite affine refinement and Zariski descent. -/
theorem quasiCoherentModules_isFppfPrestack_of_singleton
    (singleton : ∀ (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
      [Module.FaithfullyFlat R S], Nonempty (Q.toDescentData (fun _ : Unit => affineScalarMap R S)).FullyFaithful) :
    Q.{u}.IsPrestack fppfTopology := by
  apply quasiCoherentModules_isFppfPrestack_of_affine
  intro R T covering
  obtain ⟨cover, subordinate⟩ := fppfTopology_exists_covering_family covering
  let selected := fppfPointSubcover cover
  let F := affineRefinement selected
  have original : Sieve.ofArrows selected.X selected.f ≤ Sieve.ofArrows cover.X cover.f :=
    (fppfPointSubcoverOver cover).sieve₀_le_sieve₀
  exact fppf_isPrestackFor_of_covering_refinement (fppfCover_sieve_mem F.affine.cover)
    (F.sieve_refines.trans (original.trans subordinate))
    (F.affineComponents_isPrestackFor (F.productMap_isPrestackFor singleton))

/-- Quasi-coherent modules satisfy the fppf sheaf condition for all maps. -/
theorem quasiCoherentModules_isFppfPrestack : Q.{u}.IsPrestack fppfTopology := by
  apply quasiCoherentModules_isFppfPrestack_of_singleton
  intro R S _ _ _ _
  letI := affineSingletonFaithfullyFlatDescent (A := R) (B := S)
  exact ⟨Functor.FullyFaithful.ofFullyFaithful _⟩

/-- The actual comparison for any fppf family is fully faithful. -/
def fppfModuleComparison_fullyFaithful {X : Scheme.{u}} (cover : FppfCover X) :
    (fppfModuleComparison cover).FullyFaithful := by
  letI := quasiCoherentModules_isFppfPrestack.{u}
  exact Q.fullyFaithfulToDescentData cover.f (fppfCover_sieve_mem cover)

private theorem existsUnique_preimage {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (ff : F.FullyFaithful) {M N : C} (f : F.obj M ⟶ F.obj N) :
    ∃! g : M ⟶ N, F.map g = f := by
  refine ⟨ff.preimage f, ff.map_preimage f, ?_⟩
  intro g hg
  apply ff.map_injective
  exact hg.trans (ff.map_preimage f).symm

set_option maxHeartbeats 600000 in
/-- Every compatible arrow between pulled-back modules comes from a unique arrow. -/
theorem fppfModuleComparison_existsUnique {X : Scheme.{u}} (cover : FppfCover X)
    {M N : Q.obj (.mk (op X))}
    (f : (fppfModuleComparison cover).obj M ⟶ (fppfModuleComparison cover).obj N) :
    ∃! g : M ⟶ N, (fppfModuleComparison cover).map g = f :=
  existsUnique_preimage (fppfModuleComparison cover) (fppfModuleComparison_fullyFaithful cover) f

end

end SHIGURE.SchemeDescent
