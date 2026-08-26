import ResearchLean.AG.DoctrineFiberProduct.IndexedBaseChangeRaw
import ResearchLean.AG.DoctrineFiberProduct.SchemaWitnesses
import ResearchLean.AG.TransportCoherence.FinitePresentation

/-!
# A two-cell base-congruence obstruction for indexed base change

Edgewise indexed square transport produces target packages, target total
morphisms, and their strongly cocartesian qualifications.  To reassemble an
arbitrary-source `AdmissibleTransportData`, however, a source two-cell base
equality must also generate equality of the two target path bases.

Pasting the edge squares gives equality only after precomposition by the
vertex transport index.  This module first fixes a finite non-epimorphic
transport index showing that such precomposition cannot be cancelled on the
full `ExtractionInstance` domain.  It then constructs a one-vertex finite
transport presentation, admissible source data, and two actual F0 validated
square leaves whose equal source paths have distinct target paths.  Hence the
fixed full-domain target two-cell base-generation conjunct is refuted.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence
open TransportCoherence

/-- The cancellation law needed to turn pasted edge squares into a target
two-cell base equality at one vertex transport index. -/
def IndexedTargetBaseCongruenceAt {U : AtomCarrier.{u}}
    {source target : ExtractionInstance U} (index : source ⟶ target) : Prop :=
  ∀ (endpoint : ExtractionInstance U) (left right : target ⟶ endpoint),
    index ≫ left = index ≫ right → left = right

/-- The required target base-congruence law is exactly epimorphicity of the
vertex transport index. -/
theorem indexedTargetBaseCongruenceAt_iff_epi {U : AtomCarrier.{u}}
    {source target : ExtractionInstance U} (index : source ⟶ target) :
    IndexedTargetBaseCongruenceAt index ↔ Epi index := by
  simpa [IndexedTargetBaseCongruenceAt] using
    (CategoryTheory.epi_iff_forall_injective index).symm

local instance g111FiniteModelCarrierAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- The generic cancellation law has a positive identity-index instance. -/
theorem indexedTargetBaseCongruenceAt_identity {U : AtomCarrier.{u}}
    (source : ExtractionInstance U) :
    IndexedTargetBaseCongruenceAt (𝟙 source) := by
  rw [indexedTargetBaseCongruenceAt_iff_epi]
  infer_instance

/-- The selected-point-preserving inclusion from the one-source finite
instance into the two-source finite instance. -/
def finiteOneToTwoPresentation :
    CartPresentationBetween finiteOneSourceInstance finiteTwoSourceInstance where
  sourceMap := fun _ => finiteTwoSourceZero
  atomEquiv := AtomPermutationCode.refl
  normalize_eq _ := rfl
  extraction_eq source := by
    change finiteAllAtomPredicate =
      finiteAllAtomPredicate.transport AtomPermutationCode.refl.toEquiv
    rw [AtomPermutationCode.toEquiv_refl]
    simp
  source_eq := rfl

/-- A constant endomorphism of the two-source finite instance fixing its
selected point. -/
def finiteTwoSourceConstantPresentation :
    CartPresentationBetween finiteTwoSourceInstance finiteTwoSourceInstance where
  sourceMap := fun _ => finiteTwoSourceZero
  atomEquiv := AtomPermutationCode.refl
  normalize_eq _ := rfl
  extraction_eq source := by
    change finiteAllAtomPredicate =
      finiteAllAtomPredicate.transport AtomPermutationCode.refl.toEquiv
    rw [AtomPermutationCode.toEquiv_refl]
    simp
  source_eq := rfl

/-- Semantic one-to-two transport index used by the no-go witness. -/
def finiteOneToTwoIndex :
    finiteOneSourceInstance.toSemantic ⟶ finiteTwoSourceInstance.toSemantic :=
  typedPresentationToSemantic finiteOneToTwoPresentation

/-- Semantic identity target path in the no-go witness. -/
def finiteTwoSourceIdentity :
    finiteTwoSourceInstance.toSemantic ⟶ finiteTwoSourceInstance.toSemantic :=
  𝟙 _

/-- Semantic constant target path in the no-go witness. -/
def finiteTwoSourceConstant :
    finiteTwoSourceInstance.toSemantic ⟶ finiteTwoSourceInstance.toSemantic :=
  typedPresentationToSemantic finiteTwoSourceConstantPresentation

/-- The transport index cannot distinguish the identity and constant target
paths after precomposition. -/
theorem finiteOneToTwo_comp_identity_eq_constant :
    finiteOneToTwoIndex ≫ finiteTwoSourceIdentity =
      finiteOneToTwoIndex ≫ finiteTwoSourceConstant := by
  apply ExtInstHom.ext
  apply ExactDoctrineHom.ext
  · rfl
  · apply Equiv.ext
    intro atom
    rfl

/-- The two target paths are nevertheless distinct. -/
theorem finiteTwoSourceIdentity_ne_constant :
    finiteTwoSourceIdentity ≠ finiteTwoSourceConstant := by
  intro equality
  have sourceEquality := congrArg
    (fun hom : finiteTwoSourceInstance.toSemantic ⟶
        finiteTwoSourceInstance.toSemantic =>
      hom.doctrineHom.sourceMap finiteTwoSourceOne) equality
  change finiteTwoSourceOne = finiteTwoSourceZero at sourceEquality
  have downEquality := congrArg
    (fun source : (finiteAllDoctrineCode 2).Source => source.down.val)
    sourceEquality
  norm_num [finiteTwoSourceZero, finiteTwoSourceOne,
    finiteAllDoctrineCode] at downEquality

/-- The finite vertex transport index is not epimorphic in `ExtInst_U`. -/
theorem finiteOneToTwoIndex_not_epi : ¬ Epi finiteOneToTwoIndex := by
  intro epiIndex
  letI : Epi finiteOneToTwoIndex := epiIndex
  exact finiteTwoSourceIdentity_ne_constant
    ((cancel_epi finiteOneToTwoIndex).mp
      finiteOneToTwo_comp_identity_eq_constant)

/-- Full-domain edge-square data cannot supply the cancellation law required
to generate every target two-cell base equality. -/
theorem finiteOneToTwo_no_targetBaseCongruence :
    ¬ IndexedTargetBaseCongruenceAt finiteOneToTwoIndex := by
  rw [indexedTargetBaseCongruenceAt_iff_epi]
  exact finiteOneToTwoIndex_not_epi

/-! ## A target-scoped validated-square counterexample -/

/-- Duplicate every source cell of the reviewed finite doctrine by a Boolean
tag without changing its extracted Atom family. -/
def finiteDuplicatedDoctrine : ExtractionDoctrine FiniteModel.carrier where
  Source := FiniteModel.extractionDoctrine.Source × Bool
  Vocabulary := FiniteModel.extractionDoctrine.Vocabulary
  SemanticReading := FiniteModel.extractionDoctrine.SemanticReading
  Resolution := FiniteModel.extractionDoctrine.Resolution
  vocabulary := FiniteModel.extractionDoctrine.vocabulary
  semanticReading := FiniteModel.extractionDoctrine.semanticReading
  resolution := FiniteModel.extractionDoctrine.resolution
  vocabularyAllows := FiniteModel.extractionDoctrine.vocabularyAllows
  semanticAllows := fun reading source atom =>
    FiniteModel.extractionDoctrine.semanticAllows reading source.1 atom
  resolutionAllows := fun resolution source atom =>
    FiniteModel.extractionDoctrine.resolutionAllows resolution source.1 atom
  sourceSemantics := fun source atom =>
    FiniteModel.extractionDoctrine.sourceSemantics source.1 atom
  normalize := fun source =>
    (FiniteModel.extractionDoctrine.normalize source.1, source.2)

/-- The reviewed package point used as the source of the target counterexample. -/
noncomputable def finiteFixtureInstance : ExtractionInstance FiniteModel.carrier :=
  packagePoint FiniteModel.corePackage

/-- The same selected source in the false-tag copy of the duplicated doctrine. -/
noncomputable def finiteDuplicatedInstance : ExtractionInstance FiniteModel.carrier where
  doctrine := finiteDuplicatedDoctrine
  source := (FiniteModel.ExtractionSource.withoutComponentC, false)

/-- Generated vertex index embedding the reviewed finite instance into the
false-tag copy. -/
noncomputable def finiteDuplicateIndex :
    finiteFixtureInstance ⟶ finiteDuplicatedInstance where
  doctrineHom :=
    { sourceMap := fun source => (source, false)
      atomEquiv := Equiv.refl _
      normalize_eq := fun _ => rfl
      extraction_iff := fun _ _ => Iff.rfl }
  source_eq := rfl

/-- Constant-tag endomorphism of the duplicated target instance. -/
noncomputable def finiteDuplicateConstant :
    finiteDuplicatedInstance ⟶ finiteDuplicatedInstance where
  doctrineHom :=
    { sourceMap := fun source => (source.1, false)
      atomEquiv := Equiv.refl _
      normalize_eq := fun _ => rfl
      extraction_iff := fun _ _ => Iff.rfl }
  source_eq := rfl

/-- Identity target path for the validated-square counterexample. -/
noncomputable def finiteDuplicateIdentity :
    finiteDuplicatedInstance ⟶ finiteDuplicatedInstance :=
  𝟙 _

/-- The vertex index sees identity and constant target paths as equal. -/
theorem finiteDuplicateIndex_comp_identity_eq_constant :
    finiteDuplicateIndex ≫ finiteDuplicateIdentity =
      finiteDuplicateIndex ≫ finiteDuplicateConstant := by
  apply ExtInstHom.ext
  apply ExactDoctrineHom.ext
  · rfl
  · apply Equiv.ext
    intro atom
    rfl

/-- The target identity and constant-tag paths are distinct. -/
theorem finiteDuplicateIdentity_ne_constant :
    finiteDuplicateIdentity ≠ finiteDuplicateConstant := by
  intro equality
  have sourceEquality := congrArg
    (fun hom : finiteDuplicatedInstance ⟶ finiteDuplicatedInstance =>
      hom.doctrineHom.sourceMap
        (FiniteModel.ExtractionSource.withoutComponentC, true)) equality
  change (FiniteModel.ExtractionSource.withoutComponentC, true) =
    (FiniteModel.ExtractionSource.withoutComponentC, false) at sourceEquality
  have tagEquality : true = false := congrArg Prod.snd sourceEquality
  exact Bool.noConfusion tagEquality

/-- Validated square from the source identity edge to the target identity edge. -/
noncomputable def finiteDuplicateIdentitySquare : ValidatedIndexedBaseSquare
    FiniteModel.carrier finiteDuplicateIndex (𝟙 finiteFixtureInstance)
      finiteDuplicateIdentity finiteDuplicateIndex :=
  ValidatedIndexedBaseSquare.ofTerm (.leaf (by simp [finiteDuplicateIdentity]))

/-- Validated square from the same source identity edge to the distinct target
constant edge. -/
noncomputable def finiteDuplicateConstantSquare : ValidatedIndexedBaseSquare
    FiniteModel.carrier finiteDuplicateIndex (𝟙 finiteFixtureInstance)
      finiteDuplicateConstant finiteDuplicateIndex :=
  ValidatedIndexedBaseSquare.ofTerm (.leaf (by
    simpa [finiteDuplicateIdentity] using
      finiteDuplicateIndex_comp_identity_eq_constant.symm))

/-- One vertex with two parallel loop edges and one declared two-cell between
the corresponding one-edge paths. -/
noncomputable def finiteTwoLoopPresentation : FiniteTransportPresentation where
  Vertex := PUnit
  vertexFintype := inferInstance
  Edge := fun _ _ => Bool
  edgeFintype := fun _ _ => inferInstance
  TwoCell := PUnit
  twoCellFintype := inferInstance
  twoSource := fun _ => PUnit.unit
  twoTarget := fun _ => PUnit.unit
  twoLeft := fun _ => .cons false (.nil PUnit.unit)
  twoRight := fun _ => .cons true (.nil PUnit.unit)
  ThreeCell := Empty
  threeCellFintype := inferInstance
  threeSource := fun cell => nomatch cell
  threeTarget := fun cell => nomatch cell
  threeStart := fun cell => nomatch cell
  threeFinish := fun cell => nomatch cell
  threeLeft := fun cell => nomatch cell
  threeRight := fun cell => nomatch cell

/-- The reviewed finite package as an object of the source counterexample fiber. -/
noncomputable def finiteFixtureFiber : CoreFiber finiteFixtureInstance :=
  ⟨FiniteModel.corePackage, rfl⟩

/-- Both source loop edges are the identity total morphism. -/
noncomputable def finiteTwoLoopSourceLift : AdmissibleLiftData
    finiteTwoLoopPresentation FiniteModel.carrier where
  package := fun _ => FiniteModel.corePackage
  edgeLift := fun _ => PackageTotalHom.id FiniteModel.corePackage
  edgeStrong := by
    intro _ _ _
    letI : (packageProjection FiniteModel.carrier).IsHomLift
        (𝟙 finiteFixtureInstance) (Iso.refl FiniteModel.corePackage).hom := by
      change (packageProjection FiniteModel.carrier).IsHomLift
        (𝟙 finiteFixtureInstance) (𝟙 FiniteModel.corePackage)
      exact CategoryTheory.IsHomLift.id
        (p := packageProjection FiniteModel.carrier) rfl
    simpa only using
      (CategoryTheory.Functor.IsStronglyCocartesian.of_iso
        (packageProjection FiniteModel.carrier) (𝟙 finiteFixtureInstance)
        (Iso.refl FiniteModel.corePackage))

/-- Concrete admissible source data: the two source paths have definitionally
equal base maps and the two-cell comparator is identity. -/
noncomputable def finiteTwoLoopSourceData : AdmissibleTransportData
    finiteTwoLoopPresentation FiniteModel.carrier where
  lift := finiteTwoLoopSourceLift
  twoCellBase := by
    intro cell
    cases cell
    rfl
  comparator := fun _ => 1

/-- Target base edge selected by each of the two validated square leaves. -/
noncomputable def finiteTwoLoopTargetBase (edge : Bool) :
    finiteDuplicatedInstance ⟶ finiteDuplicatedInstance :=
  if edge then finiteDuplicateConstant else finiteDuplicateIdentity

/-- The F0 validated square family over the two source identity loops. -/
noncomputable def finiteTwoLoopValidatedSquare (edge : Bool) :
    ValidatedIndexedBaseSquare FiniteModel.carrier finiteDuplicateIndex
      (finiteTwoLoopSourceLift.edgeLift
        (i := PUnit.unit) (j := PUnit.unit) edge).base
      (finiteTwoLoopTargetBase edge) finiteDuplicateIndex := by
  cases edge
  · simpa [finiteTwoLoopSourceLift, finiteTwoLoopTargetBase] using
      finiteDuplicateIdentitySquare
  · simpa [finiteTwoLoopSourceLift, finiteTwoLoopTargetBase] using
      finiteDuplicateConstantSquare

/-- A full-domain K1.5 two-cell base generator at the actual F0 validated
square boundary: equal source paths and two squares must yield equal target
paths. -/
def IndexedValidatedTwoCellBaseGeneration (U : AtomCarrier.{u}) : Prop :=
  ∀ {sourceStart sourceEnd targetStart targetEnd : ExtractionInstance U}
      {sourceLeft sourceRight : sourceStart ⟶ sourceEnd}
      {indexStart : sourceStart ⟶ targetStart}
      {indexEnd : sourceEnd ⟶ targetEnd}
      {targetLeft targetRight : targetStart ⟶ targetEnd},
    sourceLeft = sourceRight →
    ValidatedIndexedBaseSquare U indexStart sourceLeft targetLeft indexEnd →
    ValidatedIndexedBaseSquare U indexStart sourceRight targetRight indexEnd →
    targetLeft = targetRight

/-- The two explicit F0 validated squares refute full-domain target two-cell
base generation. -/
theorem finiteValidatedSquares_refute_twoCellBaseGeneration :
    ¬ IndexedValidatedTwoCellBaseGeneration FiniteModel.carrier := by
  intro generation
  exact finiteDuplicateIdentity_ne_constant
    (generation rfl finiteDuplicateIdentitySquare finiteDuplicateConstantSquare)

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
