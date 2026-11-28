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

private instance component_open (i : Bool) : IsOpenImmersion (component i) :=
  inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom
    (Pi.evalRingHom (fun _ : Bool => ℚ) i))))

private theorem component_tag {i j : Bool} {x : Spec (rings i)} {y : Spec (rings j)}
    (h : component i x = component j y) : i = j := by
  have first : sigmaSpec rings (sigmaMk (fun i => Spec (rings i)) ⟨i, x⟩) = component i x := by
    rw [sigmaMk_mk, ← Scheme.Hom.comp_apply, ι_sigmaSpec]
    rfl
  have second : sigmaSpec rings (sigmaMk (fun i => Spec (rings i)) ⟨j, y⟩) = component j y := by
    rw [sigmaMk_mk, ← Scheme.Hom.comp_apply, ι_sigmaSpec]
    rfl
  exact congrArg Sigma.fst ((sigmaMk (fun i => Spec (rings i))).injective
    ((sigmaSpec rings).homeomorph.injective (first.trans (h.trans second.symm))))

private theorem empty_of_ne {Y : Scheme.{0}} {i j : Bool} (hne : i ≠ j)
    (a : Y ⟶ Spec (rings i)) (b : Y ⟶ Spec (rings j))
    (h : a ≫ component i = b ≫ component j) : IsEmpty Y :=
  ⟨fun y => hne (component_tag (i := i) (j := j) (x := a y) (y := b y)
    (congrArg (fun k : Y ⟶ Spec base => k y) h))⟩

private def emptyCover (Y : Scheme.{0}) [IsEmpty Y] : FppfCover.{0,0} Y where
  I₀ := Empty
  X := fun i => nomatch i
  f := fun i => nomatch i
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨fun y => isEmptyElim y, fun i => nomatch i⟩

private theorem empty_hom_ext (Y : Scheme.{0}) [IsEmpty Y]
    {M N : quasiCoherentModulesPseudofunctor.obj (.mk (Opposite.op Y))} (a b : M ⟶ N) : a = b := by
  let E := emptyCover Y
  let G := fppfModuleComparison E
  letI : G.Faithful := fppfComparison_faithful E
  apply G.map_injective
  apply Pseudofunctor.DescentData.Hom.ext
  funext i
  exact Empty.elim i

private def componentwiseHom (D : FppfModuleDescentData cover.cover)
    (φ : ∀ i, D.obj i ⟶ D.obj i) : D ⟶ D where
  hom := φ
  comm := by
    intro Y q i j f₁ f₂ hf₁ hf₂
    by_cases h : i = j
    · subst j
      have same : f₁ = f₂ := (cancel_mono (component i)).1 (hf₁.trans hf₂.symm)
      subst f₂
      subst q
      simp only [D.hom_self, Category.comp_id, Category.id_comp]
    · letI : IsEmpty Y := empty_of_ne h f₁ f₂ (hf₁.trans hf₂.symm)
      exact empty_hom_ext Y _ _

private def qcZero (S : Scheme.{0}) (M :
    ObjectProperty.FullSubcategory (IsQuasiCoherentModule (X := S))) : M ⟶ M :=
  ObjectProperty.homMk (0 : M.obj ⟶ M.obj)

private def piecewiseEnd (D : FppfModuleDescentData cover.cover) : D ⟶ D :=
  componentwiseHom D (fun i => if (show Bool from i) = true then 𝟙 _
    else qcZero (Spec (rings i)) (D.obj i))

private def twoComponentLocalMaps :
    let T := affineTildeFunctor base
    let L := T.obj (ModuleCat.of base base)
    let D := (fppfModuleComparison cover.cover).obj L
    D ⟶ D :=
  piecewiseEnd _

/-- Independently specified zero and identity maps on the two components
satisfy overlap compatibility and descend to a unique global map. -/
theorem two_components_identity_descends :
    let T := affineTildeFunctor base
    let L := T.obj (ModuleCat.of base base)
    let C := fppfModuleComparison cover.cover
    ∃! g : L ⟶ L, C.map g = twoComponentLocalMaps := by
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
