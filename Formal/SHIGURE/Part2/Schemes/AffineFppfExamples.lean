import Formal.SHIGURE.Part2.Schemes.AffineFppfRefinement
import Formal.SHIGURE.Part2.Schemes.FppfGlobalFromAffineSingleton

/-! # A two-component finite affine cover

The two projections of a product of rational fields give disjoint
open immersions. Their images cover the affine spectrum, and either
one alone misses the spectrum of the other factor.
-/

namespace SHIGURE.SchemeDescent.AffineFppfExamples

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

private abbrev base : CommRingCat := .of (Bool → ℚ)
private def rings (_ : Bool) : CommRingCat := .of ℚ

private def component (i : Bool) : Spec (rings i) ⟶ Spec base :=
  Spec.map (CommRingCat.ofHom (Pi.evalRingHom _ i))

private theorem exists_component (x : Spec base) :
    ∃ i, x ∈ Set.range (component i) := by
  obtain ⟨z, hz⟩ := (sigmaSpec rings).surjective x
  obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk (fun i => Spec (rings i))).surjective z
  rw [sigmaMk_mk, ← Scheme.Hom.comp_apply, ι_sigmaSpec] at hz
  exact ⟨i, y, hz⟩

private def cover : Scheme.AffineCover FppfComponent (Spec base) where
  I₀ := Bool
  X := rings
  f := component
  idx x := (exists_component x).choose
  covers x := (exists_component x).choose_spec
  map_prop i := by
    have opened : IsOpenImmersion (component i) :=
      inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Bool => ℚ) i))))
    exact ⟨inferInstance, inferInstance⟩

private def refinement : AffineRefinement cover.cover where
  affine := cover
  over := 𝟙 _
  finite := inferInstanceAs (Finite Bool)
  openImmersion _ := inferInstanceAs (IsOpenImmersion (𝟙 _))

/-- The two actual charts give an algebra to which the faithfully flat equivalence applies. -/
theorem two_components_faithfullyFlat :
    letI := refinement.productAlgebra
    Module.FaithfullyFlat base refinement.productRing :=
  refinement.productFaithfullyFlat

/-- Both of the actual components are needed for the cover. -/
theorem one_component_not_surjective (i : Bool) : ¬ Function.Surjective (component i) := by
  intro surjective
  let other := !i
  letI : Nontrivial (rings other) := inferInstanceAs (Nontrivial ℚ)
  let p : Spec (rings other) := Classical.choice (inferInstance : Nonempty (PrimeSpectrum (rings other)))
  obtain ⟨q, eq⟩ := surjective (component other p)
  have first : sigmaSpec rings (sigmaMk (fun i => Spec (rings i)) ⟨i, q⟩) = component i q := by
    rw [sigmaMk_mk, ← Scheme.Hom.comp_apply, ι_sigmaSpec]
    rfl
  have second : sigmaSpec rings (sigmaMk (fun i => Spec (rings i)) ⟨other, p⟩) = component other p := by
    rw [sigmaMk_mk, ← Scheme.Hom.comp_apply, ι_sigmaSpec]
    rfl
  have same := (sigmaMk (fun i => Spec (rings i))).injective
    ((sigmaSpec rings).homeomorph.injective (first.trans (eq.trans second.symm)))
  have tag := congrArg Sigma.fst same
  change i = !i at tag
  cases i <;> cases tag

/-- Compatible identity maps on the two actual charts have a unique global source. -/
theorem two_components_identity_descends :
    let T := affineTildeFunctor base
    let L := T.obj (ModuleCat.of base base)
    let C := fppfModuleComparison cover.cover
    ∃! g : L ⟶ L, C.map g = C.map (𝟙 L) := by
  dsimp only
  exact fppfModuleComparison_existsUnique cover.cover _

/-- The two-chart comparison retains the distinction between zero and identity. -/
theorem two_components_distinguish_maps :
    let T := affineTildeFunctor base
    let L := ModuleCat.of base base
    let C := fppfModuleComparison cover.cover
    C.map (T.map (𝟙 L)) ≠ C.map (T.map (0 : L ⟶ L)) := by
  dsimp only
  let T := affineTildeFunctor base
  let L := ModuleCat.of base base
  let C := fppfModuleComparison cover.cover
  intro equal
  have same : (𝟙 L : L ⟶ L) = 0 :=
    (affineTildeEquivalence base).fullyFaithfulFunctor.map_injective
      ((fppfModuleComparison_fullyFaithful cover.cover).map_injective equal)
  have value := congrArg (fun f : L ⟶ L => f (1 : base) true) same
  change (1 : ℚ) = 0 at value
  exact one_ne_zero value

end

end SHIGURE.SchemeDescent.AffineFppfExamples
