import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryCompatibleSourcePresentationNaturalityF6

/-!
# Structural source-presentation change operations

This module supplies the identity, inverse, and typed binary-composition
operations needed for G-118 C1s coherence.  A source-presentation change is
oriented from its reconstructed input to the input indexing the structure, so
composition takes a second change indexed by the first reconstructed input.
These operations do not assert a strict category structure: reconstructed
whole-input records still require explicit propositional identifications for
arbitrary rebracketing of longer chains.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u v

open CategoryTheory AtomFoundation GeometryTransport CrossStageCoherence
open TransportCoherence

set_option maxHeartbeats 6000000

namespace UpperGeometryCompatibleSourcePresentationChange

variable {U : AtomCarrier.{u}} {ctx : ActiveRefinementBCContext U}
variable {P : FiniteTransportPresentation.{u}} {k : CommRingCat.{v}}
variable {input : UpperGeometryCompatibleProblemInputData ctx P k}

/-- G-118 C1s identity source-presentation change. -/
noncomputable def identity
    (input : UpperGeometryCompatibleProblemInputData ctx P k) :
    UpperGeometryCompatibleSourcePresentationChange input where
  sourceFiber i := input.sourceFiberDiagram.obj ⟨i⟩
  sourceGeometry i := input.sourceGeometry i
  coreIso _ := Iso.refl _
  geometryIso _ := Iso.refl _
  geometryIso_hom_base _ := rfl
  geometryIso_inv_base _ := rfl
  geometryIso_hom_coefficient_id _ := rfl
  geometryIso_inv_coefficient_id _ := rfl

/-- G-118 C1s inverse source-presentation change.  Its source presentation is
the original input and its selected comparisons are the inverses of the given
ones. -/
noncomputable def inverse
    (change : UpperGeometryCompatibleSourcePresentationChange input) :
    UpperGeometryCompatibleSourcePresentationChange change.changedInput where
  sourceFiber i := input.sourceFiberDiagram.obj ⟨i⟩
  sourceGeometry i := input.sourceGeometry i
  coreIso i := (change.coreIso i).symm
  geometryIso i := (change.geometryIso i).symm
  geometryIso_hom_base i := change.geometryIso_inv_base i
  geometryIso_inv_base i := change.geometryIso_hom_base i
  geometryIso_hom_coefficient_id i :=
    change.geometryIso_inv_coefficient_id i
  geometryIso_inv_coefficient_id i :=
    change.geometryIso_hom_coefficient_id i

/-- G-118 C1s typed binary composition.  If `first` runs from its changed
input to `input` and `second` runs from its changed input to the changed input
of `first`, the composite runs from the changed source of `second` directly to
`input`. -/
noncomputable def comp
    (first : UpperGeometryCompatibleSourcePresentationChange input)
    (second : UpperGeometryCompatibleSourcePresentationChange
      first.changedInput) :
    UpperGeometryCompatibleSourcePresentationChange input where
  sourceFiber i := second.sourceFiber i
  sourceGeometry i := second.sourceGeometry i
  coreIso i := second.coreIso i ≪≫ first.coreIso i
  geometryIso i := second.geometryIso i ≪≫ first.geometryIso i
  geometryIso_hom_base i := by
    change
      ((second.geometryIso i).hom.base.comp
        (first.geometryIso i).hom.base) = _
    rw [second.geometryIso_hom_base, first.geometryIso_hom_base]
    rfl
  geometryIso_inv_base i := by
    change
      ((first.geometryIso i).inv.base.comp
        (second.geometryIso i).inv.base) = _
    rw [first.geometryIso_inv_base, second.geometryIso_inv_base]
    rfl
  geometryIso_hom_coefficient_id i := by
    change
      (first.geometryIso i).hom.geometry.coefficientHom.comp
        (second.geometryIso i).hom.geometry.coefficientHom = RingHom.id k
    rw [first.geometryIso_hom_coefficient_id,
      second.geometryIso_hom_coefficient_id]
    ext value
    rfl
  geometryIso_inv_coefficient_id i := by
    change
      (second.geometryIso i).inv.geometry.coefficientHom.comp
        (first.geometryIso i).inv.geometry.coefficientHom = RingHom.id k
    rw [second.geometryIso_inv_coefficient_id,
      first.geometryIso_inv_coefficient_id]
    ext value
    rfl

/-! The pointwise generated route legs depend only on the selected source
object and complete geometry, so these equalities do not require whole-input
record equality. -/

@[simp] theorem identity_changedInput_generatedBaseRouteLegAt
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex) :
    (identity input).changedInput.generatedBaseRouteLegAt i =
      input.generatedBaseRouteLegAt i := by rfl

@[simp] theorem identity_changedInput_generatedPulledRouteLegAt
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex) :
    (identity input).changedInput.generatedPulledRouteLegAt i =
      input.generatedPulledRouteLegAt i := by rfl

@[simp] theorem inverse_changedInput_generatedBaseRouteLegAt
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    change.inverse.changedInput.generatedBaseRouteLegAt i =
      input.generatedBaseRouteLegAt i := by rfl

@[simp] theorem inverse_changedInput_generatedPulledRouteLegAt
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    change.inverse.changedInput.generatedPulledRouteLegAt i =
      input.generatedPulledRouteLegAt i := by rfl

@[simp] theorem comp_changedInput_generatedBaseRouteLegAt
    (first : UpperGeometryCompatibleSourcePresentationChange input)
    (second : UpperGeometryCompatibleSourcePresentationChange
      first.changedInput)
    (i : P.Vertex) :
    (first.comp second).changedInput.generatedBaseRouteLegAt i =
      second.changedInput.generatedBaseRouteLegAt i := by rfl

@[simp] theorem comp_changedInput_generatedPulledRouteLegAt
    (first : UpperGeometryCompatibleSourcePresentationChange input)
    (second : UpperGeometryCompatibleSourcePresentationChange
      first.changedInput)
    (i : P.Vertex) :
    (first.comp second).changedInput.generatedPulledRouteLegAt i =
      second.changedInput.generatedPulledRouteLegAt i := by rfl

/-! ## Coherence of generated exact-core endpoint comparisons -/

/-- The generated base exact-core comparison of the identity change is the
identity. -/
theorem generatedBaseRouteExactCoreIsoAt_identity
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex) :
    (identity input).generatedBaseRouteExactCoreIsoAt i =
      Iso.refl ((identity input).changedInput.generatedBaseRouteGeometryAt i).core := by
  apply Iso.ext
  simp [generatedBaseRouteExactCoreIsoAt, identity, changedInput,
    changedSourceFiberDiagram,
    UpperGeometryCompatibleProblemInputData.generatedBaseRouteCoreIsoAt,
    UpperGeometryCompatibleProblemInputData.sourceTargetGeometryAt,
    ActiveRefinementBCContext.baseCoreDiagram]
  rfl

/-- The generated pulled exact-core comparison of the identity change is the
identity. -/
theorem generatedPulledRouteExactCoreIsoAt_identity
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex) :
    (identity input).generatedPulledRouteExactCoreIsoAt i =
      Iso.refl ((identity input).changedInput.generatedPulledRouteGeometryAt i).core := by
  apply Iso.ext
  simp [generatedPulledRouteExactCoreIsoAt, identity, changedInput,
    changedSourceFiberDiagram,
    UpperGeometryCompatibleProblemInputData.generatedPulledRouteCoreIsoAt,
    UpperGeometryCompatibleProblemInputData.sourceTargetGeometryAt,
    ActiveRefinementBCContext.pulledCoreDiagram]
  rfl

/-- The generated base exact-core comparison of the inverse change is the
inverse comparison. -/
theorem generatedBaseRouteExactCoreIsoAt_inverse
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    change.inverse.generatedBaseRouteExactCoreIsoAt i =
      (change.generatedBaseRouteExactCoreIsoAt i).symm := by
  apply Iso.ext
  simp [generatedBaseRouteExactCoreIsoAt, inverse, changedInput,
    changedSourceFiberDiagram,
    UpperGeometryCompatibleProblemInputData.generatedBaseRouteCoreIsoAt,
    UpperGeometryCompatibleProblemInputData.sourceTargetGeometryAt,
    ActiveRefinementBCContext.baseCoreDiagram]

/-- The generated pulled exact-core comparison of the inverse change is the
inverse comparison. -/
theorem generatedPulledRouteExactCoreIsoAt_inverse
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    change.inverse.generatedPulledRouteExactCoreIsoAt i =
      (change.generatedPulledRouteExactCoreIsoAt i).symm := by
  apply Iso.ext
  simp [generatedPulledRouteExactCoreIsoAt, inverse, changedInput,
    changedSourceFiberDiagram,
    UpperGeometryCompatibleProblemInputData.generatedPulledRouteCoreIsoAt,
    UpperGeometryCompatibleProblemInputData.sourceTargetGeometryAt,
    ActiveRefinementBCContext.pulledCoreDiagram]

/-- Generated base exact-core comparisons preserve typed binary
composition. -/
theorem generatedBaseRouteExactCoreIsoAt_comp
    (first : UpperGeometryCompatibleSourcePresentationChange input)
    (second : UpperGeometryCompatibleSourcePresentationChange
      first.changedInput)
    (i : P.Vertex) :
    (first.comp second).generatedBaseRouteExactCoreIsoAt i =
      second.generatedBaseRouteExactCoreIsoAt i ≪≫
        first.generatedBaseRouteExactCoreIsoAt i := by
  apply Iso.ext
  simp [generatedBaseRouteExactCoreIsoAt, comp, changedInput,
    changedSourceFiberDiagram,
    UpperGeometryCompatibleProblemInputData.generatedBaseRouteCoreIsoAt,
    UpperGeometryCompatibleProblemInputData.sourceTargetGeometryAt,
    ActiveRefinementBCContext.baseCoreDiagram]

/-- Generated pulled exact-core comparisons preserve typed binary
composition. -/
theorem generatedPulledRouteExactCoreIsoAt_comp
    (first : UpperGeometryCompatibleSourcePresentationChange input)
    (second : UpperGeometryCompatibleSourcePresentationChange
      first.changedInput)
    (i : P.Vertex) :
    (first.comp second).generatedPulledRouteExactCoreIsoAt i =
      second.generatedPulledRouteExactCoreIsoAt i ≪≫
        first.generatedPulledRouteExactCoreIsoAt i := by
  apply Iso.ext
  simp [generatedPulledRouteExactCoreIsoAt, comp, changedInput,
    changedSourceFiberDiagram,
    UpperGeometryCompatibleProblemInputData.generatedPulledRouteCoreIsoAt,
    UpperGeometryCompatibleProblemInputData.sourceTargetGeometryAt,
    ActiveRefinementBCContext.pulledCoreDiagram]

/-! ## Coherence of generated complete-geometry endpoint comparisons -/

/-- The generated complete base comparison preserves the identity
source-presentation change. -/
theorem generatedBaseRouteExactGeometryIsoAt_identity
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex) :
    (identity input).generatedBaseRouteExactGeometryIsoAt i =
      Iso.refl (input.generatedBaseRouteGeometryAt i) := by
  apply Iso.ext
  apply (exactGeometryToRefinementGeometry U).map_injective
  let eta := (exactGeometryToRefinementGeometry U).map
    ((identity input).generatedBaseRouteExactGeometryIsoAt i).hom
  let ident := (exactGeometryToRefinementGeometry U).map
    (Iso.refl (input.generatedBaseRouteGeometryAt i)).hom
  let oldLeg := input.generatedBaseRouteLegAt i
  have hafter : eta ≫ oldLeg = ident ≫ oldLeg := by
    dsimp only [eta, ident, oldLeg]
    rw [(identity input).generatedBaseRouteExactGeometryIsoAt_hom_fac]
    rw [identity_changedInput_generatedBaseRouteLegAt]
    simp [identity]
  have hbase : eta.base = ident.base := by
    dsimp only [eta, ident]
    change (exactPackageToRefinement U).map
        ((identity input).generatedBaseRouteExactCoreIsoAt i).hom =
      (exactPackageToRefinement U).map (𝟙 _)
    rw [generatedBaseRouteExactCoreIsoAt_identity]
    rfl
  letI heta := UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
    ident.base eta hbase
  letI hident :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
      ident.base ident rfl
  letI := input.generatedBaseRouteLegAt_isStronglyCartesian i
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (refinementGeometryProjection U) oldLeg.base oldLeg ident.base
  exact hafter

/-- The generated complete pulled comparison preserves the identity
source-presentation change. -/
theorem generatedPulledRouteExactGeometryIsoAt_identity
    (input : UpperGeometryCompatibleProblemInputData ctx P k)
    (i : P.Vertex) :
    (identity input).generatedPulledRouteExactGeometryIsoAt i =
      Iso.refl (input.generatedPulledRouteGeometryAt i) := by
  apply Iso.ext
  apply (exactGeometryToRefinementGeometry U).map_injective
  let eta := (exactGeometryToRefinementGeometry U).map
    ((identity input).generatedPulledRouteExactGeometryIsoAt i).hom
  let ident := (exactGeometryToRefinementGeometry U).map
    (Iso.refl (input.generatedPulledRouteGeometryAt i)).hom
  let oldLeg := input.generatedPulledRouteLegAt i
  have hafter : eta ≫ oldLeg = ident ≫ oldLeg := by
    dsimp only [eta, ident, oldLeg]
    rw [(identity input).generatedPulledRouteExactGeometryIsoAt_hom_fac]
    rw [identity_changedInput_generatedPulledRouteLegAt]
    simp [identity]
  have hbase : eta.base = ident.base := by
    dsimp only [eta, ident]
    change (exactPackageToRefinement U).map
        ((identity input).generatedPulledRouteExactCoreIsoAt i).hom =
      (exactPackageToRefinement U).map (𝟙 _)
    rw [generatedPulledRouteExactCoreIsoAt_identity]
    rfl
  letI heta := UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
    ident.base eta hbase
  letI hident :=
    UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
      ident.base ident rfl
  letI := input.generatedPulledRouteLegAt_isStronglyCartesian i
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (refinementGeometryProjection U) oldLeg.base oldLeg ident.base
  exact hafter

/-- The generated complete base comparison sends an inverse source change to
the inverse endpoint comparison. -/
theorem generatedBaseRouteExactGeometryIsoAt_inverse
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    change.inverse.generatedBaseRouteExactGeometryIsoAt i =
      (change.generatedBaseRouteExactGeometryIsoAt i).symm := by
  apply Iso.ext
  apply (exactGeometryToRefinementGeometry U).map_injective
  let left := (exactGeometryToRefinementGeometry U).map
    (change.inverse.generatedBaseRouteExactGeometryIsoAt i).hom
  let right := (exactGeometryToRefinementGeometry U).map
    (change.generatedBaseRouteExactGeometryIsoAt i).symm.hom
  let oldLeg := change.changedInput.generatedBaseRouteLegAt i
  have hafter : left ≫ oldLeg = right ≫ oldLeg := by
    dsimp only [left, right, oldLeg]
    rw [change.inverse.generatedBaseRouteExactGeometryIsoAt_hom_fac,
      inverse_changedInput_generatedBaseRouteLegAt]
    change input.generatedBaseRouteLegAt i ≫
        (exactGeometryToRefinementGeometry U).map (change.geometryIso i).inv =
      (exactGeometryToRefinementGeometry U).map
          (change.generatedBaseRouteExactGeometryIsoAt i).inv ≫
        change.changedInput.generatedBaseRouteLegAt i
    exact (change.generatedBaseRouteExactGeometryIsoAt_inv_fac i).symm
  have hbase : left.base = right.base := by
    dsimp only [left, right]
    change (exactPackageToRefinement U).map
        (change.inverse.generatedBaseRouteExactCoreIsoAt i).hom =
      (exactPackageToRefinement U).map
        (change.generatedBaseRouteExactCoreIsoAt i).symm.hom
    rw [generatedBaseRouteExactCoreIsoAt_inverse]
  letI hleft := UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
    right.base left hbase
  letI hright := UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
    right.base right rfl
  letI := change.changedInput.generatedBaseRouteLegAt_isStronglyCartesian i
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (refinementGeometryProjection U) oldLeg.base oldLeg right.base
  exact hafter

/-- The generated complete pulled comparison sends an inverse source change
to the inverse endpoint comparison. -/
theorem generatedPulledRouteExactGeometryIsoAt_inverse
    (change : UpperGeometryCompatibleSourcePresentationChange input)
    (i : P.Vertex) :
    change.inverse.generatedPulledRouteExactGeometryIsoAt i =
      (change.generatedPulledRouteExactGeometryIsoAt i).symm := by
  apply Iso.ext
  apply (exactGeometryToRefinementGeometry U).map_injective
  let left := (exactGeometryToRefinementGeometry U).map
    (change.inverse.generatedPulledRouteExactGeometryIsoAt i).hom
  let right := (exactGeometryToRefinementGeometry U).map
    (change.generatedPulledRouteExactGeometryIsoAt i).symm.hom
  let oldLeg := change.changedInput.generatedPulledRouteLegAt i
  have hafter : left ≫ oldLeg = right ≫ oldLeg := by
    dsimp only [left, right, oldLeg]
    rw [change.inverse.generatedPulledRouteExactGeometryIsoAt_hom_fac,
      inverse_changedInput_generatedPulledRouteLegAt]
    change input.generatedPulledRouteLegAt i ≫
        (exactGeometryToRefinementGeometry U).map (change.geometryIso i).inv =
      (exactGeometryToRefinementGeometry U).map
          (change.generatedPulledRouteExactGeometryIsoAt i).inv ≫
        change.changedInput.generatedPulledRouteLegAt i
    exact (change.generatedPulledRouteExactGeometryIsoAt_inv_fac i).symm
  have hbase : left.base = right.base := by
    dsimp only [left, right]
    change (exactPackageToRefinement U).map
        (change.inverse.generatedPulledRouteExactCoreIsoAt i).hom =
      (exactPackageToRefinement U).map
        (change.generatedPulledRouteExactCoreIsoAt i).symm.hom
    rw [generatedPulledRouteExactCoreIsoAt_inverse]
  letI hleft := UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
    right.base left hbase
  letI hright := UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
    right.base right rfl
  letI := change.changedInput.generatedPulledRouteLegAt_isStronglyCartesian i
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (refinementGeometryProjection U) oldLeg.base oldLeg right.base
  exact hafter

/-- Generated complete base comparisons preserve typed binary composition. -/
theorem generatedBaseRouteExactGeometryIsoAt_comp_after
    (first : UpperGeometryCompatibleSourcePresentationChange input)
    (second : UpperGeometryCompatibleSourcePresentationChange
      first.changedInput)
    (i : P.Vertex) :
    (exactGeometryToRefinementGeometry U).map
          ((first.comp second).generatedBaseRouteExactGeometryIsoAt i).hom ≫
        input.generatedBaseRouteLegAt i =
      ((exactGeometryToRefinementGeometry U).map
            (second.generatedBaseRouteExactGeometryIsoAt i).hom ≫
          (exactGeometryToRefinementGeometry U).map
            (first.generatedBaseRouteExactGeometryIsoAt i).hom) ≫
        input.generatedBaseRouteLegAt i := by
  rw [(first.comp second).generatedBaseRouteExactGeometryIsoAt_hom_fac]
  change second.changedInput.generatedBaseRouteLegAt i ≫
      (exactGeometryToRefinementGeometry U).map
        ((second.geometryIso i ≪≫ first.geometryIso i).hom) = _
  rw [show (second.geometryIso i ≪≫ first.geometryIso i).hom =
    (second.geometryIso i).hom ≫ (first.geometryIso i).hom from rfl,
    Functor.map_comp, ← Category.assoc,
    ← second.generatedBaseRouteExactGeometryIsoAt_hom_fac,
    Category.assoc,
    ← first.generatedBaseRouteExactGeometryIsoAt_hom_fac,
    ← Category.assoc]

/-- The two sides of generated base comparison composition lie over the same
exact-core morphism. -/
theorem generatedBaseRouteExactGeometryIsoAt_comp_base
    (first : UpperGeometryCompatibleSourcePresentationChange input)
    (second : UpperGeometryCompatibleSourcePresentationChange
      first.changedInput)
    (i : P.Vertex) :
    ((exactGeometryToRefinementGeometry U).map
        ((first.comp second).generatedBaseRouteExactGeometryIsoAt i).hom).base =
      ((exactGeometryToRefinementGeometry U).map
          (second.generatedBaseRouteExactGeometryIsoAt i).hom ≫
        (exactGeometryToRefinementGeometry U).map
          (first.generatedBaseRouteExactGeometryIsoAt i).hom).base := by
  change (exactPackageToRefinement U).map
      ((first.comp second).generatedBaseRouteExactCoreIsoAt i).hom =
    (exactPackageToRefinement U).map
        (second.generatedBaseRouteExactCoreIsoAt i).hom ≫
      (exactPackageToRefinement U).map
        (first.generatedBaseRouteExactCoreIsoAt i).hom
  rw [generatedBaseRouteExactCoreIsoAt_comp]
  rw [show
      (second.generatedBaseRouteExactCoreIsoAt i ≪≫
        first.generatedBaseRouteExactCoreIsoAt i).hom =
      (second.generatedBaseRouteExactCoreIsoAt i).hom ≫
        (first.generatedBaseRouteExactCoreIsoAt i).hom from rfl,
    Functor.map_comp]

/-- Generated complete base comparisons preserve typed binary composition. -/
theorem generatedBaseRouteExactGeometryIsoAt_comp
    (first : UpperGeometryCompatibleSourcePresentationChange input)
    (second : UpperGeometryCompatibleSourcePresentationChange
      first.changedInput)
    (i : P.Vertex) :
    (first.comp second).generatedBaseRouteExactGeometryIsoAt i =
      second.generatedBaseRouteExactGeometryIsoAt i ≪≫
        first.generatedBaseRouteExactGeometryIsoAt i := by
  apply Iso.ext
  apply (exactGeometryToRefinementGeometry U).map_injective
  rw [show
      (second.generatedBaseRouteExactGeometryIsoAt i ≪≫
        first.generatedBaseRouteExactGeometryIsoAt i).hom =
      (second.generatedBaseRouteExactGeometryIsoAt i).hom ≫
        (first.generatedBaseRouteExactGeometryIsoAt i).hom from rfl,
    Functor.map_comp]
  let left := (exactGeometryToRefinementGeometry U).map
    ((first.comp second).generatedBaseRouteExactGeometryIsoAt i).hom
  let right :=
    (exactGeometryToRefinementGeometry U).map
        (second.generatedBaseRouteExactGeometryIsoAt i).hom ≫
      (exactGeometryToRefinementGeometry U).map
        (first.generatedBaseRouteExactGeometryIsoAt i).hom
  let oldLeg := input.generatedBaseRouteLegAt i
  have hafter : left ≫ oldLeg = right ≫ oldLeg := by
    exact generatedBaseRouteExactGeometryIsoAt_comp_after first second i
  have hbase : left.base = right.base := by
    exact generatedBaseRouteExactGeometryIsoAt_comp_base first second i
  letI hleft := UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
    right.base left hbase
  letI hright := UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
    right.base right rfl
  letI := input.generatedBaseRouteLegAt_isStronglyCartesian i
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (refinementGeometryProjection U) oldLeg.base oldLeg right.base
  exact hafter

/-- Generated complete pulled comparisons preserve typed binary
composition. -/
theorem generatedPulledRouteExactGeometryIsoAt_comp_after
    (first : UpperGeometryCompatibleSourcePresentationChange input)
    (second : UpperGeometryCompatibleSourcePresentationChange
      first.changedInput)
    (i : P.Vertex) :
    (exactGeometryToRefinementGeometry U).map
          ((first.comp second).generatedPulledRouteExactGeometryIsoAt i).hom ≫
        input.generatedPulledRouteLegAt i =
      ((exactGeometryToRefinementGeometry U).map
            (second.generatedPulledRouteExactGeometryIsoAt i).hom ≫
          (exactGeometryToRefinementGeometry U).map
            (first.generatedPulledRouteExactGeometryIsoAt i).hom) ≫
        input.generatedPulledRouteLegAt i := by
  rw [(first.comp second).generatedPulledRouteExactGeometryIsoAt_hom_fac]
  change second.changedInput.generatedPulledRouteLegAt i ≫
      (exactGeometryToRefinementGeometry U).map
        ((second.geometryIso i ≪≫ first.geometryIso i).hom) = _
  rw [show (second.geometryIso i ≪≫ first.geometryIso i).hom =
    (second.geometryIso i).hom ≫ (first.geometryIso i).hom from rfl,
    Functor.map_comp, ← Category.assoc,
    ← second.generatedPulledRouteExactGeometryIsoAt_hom_fac,
    Category.assoc,
    ← first.generatedPulledRouteExactGeometryIsoAt_hom_fac,
    ← Category.assoc]

/-- The two sides of generated pulled comparison composition lie over the
same exact-core morphism. -/
theorem generatedPulledRouteExactGeometryIsoAt_comp_base
    (first : UpperGeometryCompatibleSourcePresentationChange input)
    (second : UpperGeometryCompatibleSourcePresentationChange
      first.changedInput)
    (i : P.Vertex) :
    ((exactGeometryToRefinementGeometry U).map
        ((first.comp second).generatedPulledRouteExactGeometryIsoAt i).hom).base =
      ((exactGeometryToRefinementGeometry U).map
          (second.generatedPulledRouteExactGeometryIsoAt i).hom ≫
        (exactGeometryToRefinementGeometry U).map
          (first.generatedPulledRouteExactGeometryIsoAt i).hom).base := by
  change (exactPackageToRefinement U).map
      ((first.comp second).generatedPulledRouteExactCoreIsoAt i).hom =
    (exactPackageToRefinement U).map
        (second.generatedPulledRouteExactCoreIsoAt i).hom ≫
      (exactPackageToRefinement U).map
        (first.generatedPulledRouteExactCoreIsoAt i).hom
  rw [generatedPulledRouteExactCoreIsoAt_comp]
  rw [show
      (second.generatedPulledRouteExactCoreIsoAt i ≪≫
        first.generatedPulledRouteExactCoreIsoAt i).hom =
      (second.generatedPulledRouteExactCoreIsoAt i).hom ≫
        (first.generatedPulledRouteExactCoreIsoAt i).hom from rfl,
    Functor.map_comp]

/-- Generated complete pulled comparisons preserve typed binary
composition. -/
theorem generatedPulledRouteExactGeometryIsoAt_comp
    (first : UpperGeometryCompatibleSourcePresentationChange input)
    (second : UpperGeometryCompatibleSourcePresentationChange
      first.changedInput)
    (i : P.Vertex) :
    (first.comp second).generatedPulledRouteExactGeometryIsoAt i =
      second.generatedPulledRouteExactGeometryIsoAt i ≪≫
        first.generatedPulledRouteExactGeometryIsoAt i := by
  apply Iso.ext
  apply (exactGeometryToRefinementGeometry U).map_injective
  rw [show
      (second.generatedPulledRouteExactGeometryIsoAt i ≪≫
        first.generatedPulledRouteExactGeometryIsoAt i).hom =
      (second.generatedPulledRouteExactGeometryIsoAt i).hom ≫
        (first.generatedPulledRouteExactGeometryIsoAt i).hom from rfl,
    Functor.map_comp]
  let left := (exactGeometryToRefinementGeometry U).map
    ((first.comp second).generatedPulledRouteExactGeometryIsoAt i).hom
  let right :=
    (exactGeometryToRefinementGeometry U).map
        (second.generatedPulledRouteExactGeometryIsoAt i).hom ≫
      (exactGeometryToRefinementGeometry U).map
        (first.generatedPulledRouteExactGeometryIsoAt i).hom
  let oldLeg := input.generatedPulledRouteLegAt i
  have hafter : left ≫ oldLeg = right ≫ oldLeg := by
    exact generatedPulledRouteExactGeometryIsoAt_comp_after first second i
  have hbase : left.base = right.base := by
    exact generatedPulledRouteExactGeometryIsoAt_comp_base first second i
  letI hleft := UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
    right.base left hbase
  letI hright := UpperGeometryCleavage.refinementGeometryHom_isHomLift_of_base_eq
    right.base right rfl
  letI := input.generatedPulledRouteLegAt_isStronglyCartesian i
  apply CategoryTheory.Functor.IsStronglyCartesian.ext
    (refinementGeometryProjection U) oldLeg.base oldLeg right.base
  exact hafter

end UpperGeometryCompatibleSourcePresentationChange

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
