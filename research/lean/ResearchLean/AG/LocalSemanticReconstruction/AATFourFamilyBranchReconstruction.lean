import ResearchLean.AG.LocalSemanticReconstruction.CSBranchReconstruction
import ResearchLean.AG.LocalSemanticReconstruction.TagChangeGeneratedCategoryEquivalence
import ResearchLean.AG.LocalSemanticReconstruction.G122FullComparisonTwistedGroup
import Mathlib.CategoryTheory.Category.ULift
import Formal.Util.AssertStandardAxioms

/-!
# One reconstruction declaration for the four mandatory G-124 families

One dependent parameter now selects the tagged generated category, the full
fixed G-122 raw-comparison group, or an arbitrary accepted lens or protocol
input.  Each branch has an independently defined local category, primitive
reading, direct Hom assembler, object realization, both inverse laws, unique
Hom preimages, and a category equivalence.

This module also connects the tagged finite-table reading, the G-122
normalization/kernel coordinates and full-kernel fiber torsor, and the two CS
finite-decoder/Karoubi/Arrow routes in the same declaration.  It is a common
four-family checkpoint.  It does not yet identify these branch categories as
fibers of one non-case-defined realization-category construction.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory
open CategoryTheory.Idempotents
open AAT.AG.RealizationReconstruction
open AAT.AG.RealizationReconstruction.FiniteAxisFoldComparisonRestrictionKernel
open AtomFoundation DoctrineFiberProduct GeometryTransport TransportCoherence
open FullGeometryNormalization
open LocalReconstructionEquivalence

local instance aatBranchFiniteAxisFoldAtomDecidableEq :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

attribute [local instance] uliftCategory

/-- The single parameter declaration selecting every mandatory G-124 family. -/
inductive AATBranchParameter : Type 1
  | tagged
  | g122
  | lens (input : LensFamilyInput)
  | protocol (input : ProtocolFamilyInput)

/-- The admitted global category selected by one four-family parameter. -/
def AATBranchGlobal : AATBranchParameter → Type 1
  | .tagged => ULiftHom.{1} (ULift.{1}
      TagChangeGeneratedCategoryEquivalence.GlobalCategory)
  | .g122 => ULiftHom.{1} (ULift.{1}
      G122FullComparisonTwistedGroup.GlobalCategory)
  | .lens input => ULiftHom.{1} (CSBranchGlobal (.lens input))
  | .protocol input => ULiftHom.{1} (CSBranchGlobal (.protocol input))

/-- The independent local category selected by one four-family parameter. -/
def AATBranchLocal : AATBranchParameter → Type 1
  | .tagged => ULiftHom.{1} (ULift.{1}
      TagChangeGeneratedCategoryEquivalence.LocalCategory)
  | .g122 => ULiftHom.{1} (ULift.{1}
      G122FullComparisonTwistedGroup.LocalCategory)
  | .lens input => ULiftHom.{1} (CSBranchLocal (.lens input))
  | .protocol input => ULiftHom.{1} (CSBranchLocal (.protocol input))

noncomputable instance aatBranchGlobalCategory
    (parameter : AATBranchParameter) :
    Category.{1} (AATBranchGlobal parameter) := by
  cases parameter <;> simp only [AATBranchGlobal] <;> infer_instance

noncomputable instance aatBranchLocalCategory
    (parameter : AATBranchParameter) :
    Category.{1} (AATBranchLocal parameter) := by
  cases parameter <;> simp only [AATBranchLocal] <;> infer_instance

/-- Primitive reading for the selected mandatory family. -/
noncomputable def aatBranchReading (parameter : AATBranchParameter) :
    AATBranchGlobal parameter ⥤ AATBranchLocal parameter := by
  cases parameter with
  | tagged =>
      exact
        (ULiftHom.down (C := ULift.{1}
          TagChangeGeneratedCategoryEquivalence.GlobalCategory)) ⋙
        (ULift.downFunctor
          (C := TagChangeGeneratedCategoryEquivalence.GlobalCategory)) ⋙
        TagChangeGeneratedCategoryEquivalence.reading ⋙
        (ULift.upFunctor
          (C := TagChangeGeneratedCategoryEquivalence.LocalCategory)) ⋙
        (ULiftHom.up (C := ULift.{1}
          TagChangeGeneratedCategoryEquivalence.LocalCategory))
  | g122 =>
      exact
        (ULiftHom.down (C := ULift.{1}
          G122FullComparisonTwistedGroup.GlobalCategory)) ⋙
        (ULift.downFunctor
          (C := G122FullComparisonTwistedGroup.GlobalCategory)) ⋙
        G122FullComparisonTwistedGroup.reading ⋙
        (ULift.upFunctor
          (C := G122FullComparisonTwistedGroup.LocalCategory)) ⋙
        (ULiftHom.up (C := ULift.{1}
          G122FullComparisonTwistedGroup.LocalCategory))
  | lens input =>
      exact
        (ULiftHom.down (C := CSBranchGlobal (.lens input))) ⋙
        csBranchReading (.lens input) ⋙
        (ULiftHom.up (C := CSBranchLocal (.lens input)))
  | protocol input =>
      exact
        (ULiftHom.down (C := CSBranchGlobal (.protocol input))) ⋙
        csBranchReading (.protocol input) ⋙
        (ULiftHom.up (C := CSBranchLocal (.protocol input)))

/-- Directly assemble any coherent local Hom in the selected family. -/
noncomputable def aatBranchAssemble
    (parameter : AATBranchParameter)
    {X Y : AATBranchGlobal parameter}
    (localMorphism : (aatBranchReading parameter).obj X ⟶
      (aatBranchReading parameter).obj Y) : X ⟶ Y := by
  cases parameter with
  | tagged =>
      exact ⟨TagChangeGeneratedLocalModel.actualGeneratedMulEquivLocalSection.symm
        localMorphism.down⟩
  | g122 =>
      exact ⟨G122FullComparisonTwistedGroup.twistedCodeMulEquiv
        localMorphism.down⟩
  | lens input =>
      exact ⟨csBranchAssemble (.lens input) localMorphism.down⟩
  | protocol input =>
      exact ⟨csBranchAssemble (.protocol input) localMorphism.down⟩

/-- Primitive reading after direct four-family assembly is identity. -/
@[simp] theorem aatBranch_read_assemble
    (parameter : AATBranchParameter)
    {X Y : AATBranchGlobal parameter}
    (localMorphism : (aatBranchReading parameter).obj X ⟶
      (aatBranchReading parameter).obj Y) :
    (aatBranchReading parameter).map
        (aatBranchAssemble parameter localMorphism) = localMorphism := by
  cases parameter with
  | tagged =>
      apply ULift.ext
      exact (TagChangeGeneratedLocalModel.actualGeneratedMulEquivLocalSection).apply_symm_apply
        localMorphism.down
  | g122 =>
      apply ULift.ext
      exact (G122FullComparisonTwistedGroup.twistedCodeMulEquiv).symm_apply_apply
        localMorphism.down
  | lens input =>
      apply ULift.ext
      exact csBranch_read_assemble (.lens input) localMorphism.down
  | protocol input =>
      apply ULift.ext
      exact csBranch_read_assemble (.protocol input) localMorphism.down

/-- Direct assembly after primitive reading recovers every admitted global
Hom. -/
@[simp] theorem aatBranch_assemble_read
    (parameter : AATBranchParameter)
    {X Y : AATBranchGlobal parameter} (global : X ⟶ Y) :
    aatBranchAssemble parameter ((aatBranchReading parameter).map global) =
      global := by
  cases parameter with
  | tagged =>
      apply ULift.ext
      exact (TagChangeGeneratedLocalModel.actualGeneratedMulEquivLocalSection).symm_apply_apply
        global.down
  | g122 =>
      apply ULift.ext
      exact (G122FullComparisonTwistedGroup.twistedCodeMulEquiv).apply_symm_apply
        global.down
  | lens input =>
      apply ULift.ext
      exact csBranch_assemble_read (.lens input) global.down
  | protocol input =>
      apply ULift.ext
      exact csBranch_assemble_read (.protocol input) global.down

/-- Construct a global realization from any local object in the selected
family. -/
noncomputable def aatBranchRealize
    (parameter : AATBranchParameter)
    (localObject : AATBranchLocal parameter) : AATBranchGlobal parameter := by
  cases parameter with
  | tagged => exact ULiftHom.objUp (ULift.up (SingleObj.star _))
  | g122 => exact ULiftHom.objUp (ULift.up (SingleObj.star _))
  | lens input =>
      exact ULiftHom.objUp
        (csBranchRealize (.lens input)
          (ULiftHom.objDown (C := CSBranchLocal (.lens input)) localObject))
  | protocol input =>
      exact ULiftHom.objUp
        (csBranchRealize (.protocol input)
          (ULiftHom.objDown (C := CSBranchLocal (.protocol input)) localObject))

/-- Reading the explicit realization recovers every selected local object. -/
noncomputable def aatBranchRealizeIso
    (parameter : AATBranchParameter)
    (localObject : AATBranchLocal parameter) :
    (aatBranchReading parameter).obj
        (aatBranchRealize parameter localObject) ≅ localObject := by
  cases parameter with
  | tagged =>
      exact (ULiftHom.up (C := ULift.{1}
        TagChangeGeneratedCategoryEquivalence.LocalCategory)).mapIso
          (eqToIso (Subsingleton.elim _ _))
  | g122 =>
      exact (ULiftHom.up (C := ULift.{1}
        G122FullComparisonTwistedGroup.LocalCategory)).mapIso
          (eqToIso (Subsingleton.elim _ _))
  | lens input =>
      exact (ULiftHom.up (C := CSBranchLocal (.lens input))).mapIso
        (csBranchRealizeIso (.lens input)
          (ULiftHom.objDown (C := CSBranchLocal (.lens input)) localObject))
  | protocol input =>
      exact (ULiftHom.up (C := CSBranchLocal (.protocol input))).mapIso
        (csBranchRealizeIso (.protocol input)
          (ULiftHom.objDown (C := CSBranchLocal (.protocol input)) localObject))

/-- Separation, Hom assembly, and object assembly for every mandatory family
under the same declaration. -/
noncomputable def aatBranchReconstructionData
    (parameter : AATBranchParameter) :
    ReconstructionData (aatBranchReading parameter) where
  separation :=
    ⟨fun _ _ => ⟨fun first second equality => by
      rw [← aatBranch_assemble_read parameter first, equality,
        aatBranch_assemble_read parameter second]⟩⟩
  homAssembly :=
    { assemble := aatBranchAssemble parameter
      map_assemble := aatBranch_read_assemble parameter }
  objectAssembly :=
    { assembleObject := aatBranchRealize parameter
      readAssembledIso := aatBranchRealizeIso parameter }

/-- The primitive four-family reading is an equivalence in every branch. -/
noncomputable def aatBranchReconstructionEquivalence
    (parameter : AATBranchParameter) :
    AATBranchGlobal parameter ≌ AATBranchLocal parameter :=
  (aatBranchReconstructionData parameter).equivalence

/-- Every coherent local Hom has one unique admitted global preimage. -/
theorem aatBranch_existsUnique_preimage
    (parameter : AATBranchParameter)
    {X Y : AATBranchGlobal parameter}
    (localMorphism : (aatBranchReading parameter).obj X ⟶
      (aatBranchReading parameter).obj Y) :
    ∃! global : X ⟶ Y,
      (aatBranchReading parameter).map global = localMorphism :=
  (aatBranchReconstructionData parameter).existsUnique_preimage localMorphism

/-- The common reconstruction extends to the Arrow category for every
mandatory branch. -/
noncomputable def aatBranchArrowReconstructionEquivalence
    (parameter : AATBranchParameter) :
    Arrow (AATBranchGlobal parameter) ≌ Arrow (AATBranchLocal parameter) :=
  Functor.mapArrowEquivalence (aatBranchReconstructionEquivalence parameter)

/-! ### Connections to accepted family-specific surfaces -/

/-- The common tagged reading is the accepted finite flag/table reading at
every finite index. -/
theorem aatBranchTaggedReadingValue
    {X Y : AATBranchGlobal AATBranchParameter.tagged}
    (morphism : X ⟶ Y) (S : Finset TagChangeGeneratedLocalModel.Index) :
    TagChangeGeneratedLocalModel.value
        (((aatBranchReading
          AATBranchParameter.tagged).map morphism).down) S =
      (TagChangeGeneratedLocalModel.readActualNormalizedFlag morphism.down,
        TagChange.LocalTagTable.read
          (TagChangeGeneratedLocalModel.readActualChoice morphism.down)
          (TagChangeGeneratedLocalModel.normalizationClosure S)) :=
  TagChangeGeneratedLocalModel.actualGeneratedMulEquivLocalSection_localValue
    morphism.down S

/-- Common tagged assembly is the accepted normal-form assembly and actual
evaluation. -/
theorem aatBranchTaggedAssemble_eq_normalForm
    {X Y : AATBranchGlobal AATBranchParameter.tagged}
    (localMorphism :
      (aatBranchReading
        AATBranchParameter.tagged).obj X ⟶
      (aatBranchReading
        AATBranchParameter.tagged).obj Y) :
    (aatBranchAssemble
        AATBranchParameter.tagged localMorphism).down =
      TagChangeGeneratedNormalForm.normalFormMulEquivGenerated
        (TagChangeGeneratedLocalModel.assemble localMorphism.down) := by
  rfl

/-- The common G-122 reading exposes the accepted normalized comparison. -/
theorem aatBranchG122Reading_normalized
    {X Y : AATBranchGlobal AATBranchParameter.g122}
    (raw : X ⟶ Y) :
    (((aatBranchReading
      AATBranchParameter.g122).map raw).down).normalized =
      restrictionHom raw.down := by
  rfl

/-- The common G-122 reading exposes the unique full-kernel displacement from
the accepted canonical section. -/
theorem aatBranchG122Reading_kernel
    {X Y : AATBranchGlobal AATBranchParameter.g122}
    (raw : X ⟶ Y) :
    (MulOpposite.unop
      (((aatBranchReading
        AATBranchParameter.g122).map raw).down).kernel).1 =
      (G122FullComparisonKernelDecomposition.canonicalSectionHom
        (restrictionHom raw.down))⁻¹ * raw.down := by
  rfl

/-- The full-kernel torsor universality remains attached to the same common
G-122 branch. -/
theorem aatBranchG122FullLiftFiber_existsUnique_kernel
    (normalized : NormalizedComparison)
    (lift : AuthoredExactCanonicalComparisonLiftFiber
      finiteAxisFoldBCDatumSquare
      (Discrete.mk DoubleDiamondTwoCell.second)
      Int
      (finiteAxisFoldFixedCoefficientGeometryFamily
        (Discrete.mk DoubleDiamondTwoCell.second))
      finiteCanonicalObjectNormalization_admissible normalized) :
    ∃! kernelValue : G122FullComparisonKernelDecomposition.FullKernelᵐᵒᵖ,
      kernelValue •
          canonicalLift normalized = lift :=
  G122FullComparisonKernelDecomposition.fullLiftFiber_existsUnique_kernel
    normalized lift

/-- Lift the global lens decoder into the common four-family category. -/
noncomputable def aatBranchLensFiniteDecoder
    (input : LensFamilyInput) :
    LensPresentation ⥤ AATBranchGlobal (.lens input) :=
  lensClosedFamilyFiniteDecoder input ⋙
    (ULiftHom.up (C := CSBranchGlobal (.lens input)))

/-- The global lens decoder commutes with the common four-family reading. -/
noncomputable def aatBranchLensFiniteDecoderReadingIso
    (input : LensFamilyInput) :
    aatBranchLensFiniteDecoder input ⋙
        aatBranchReading (.lens input) ≅
      lensFiberFiniteDecoder input ⋙
        (ULiftHom.up (C := CSBranchLocal (.lens input))) :=
  NatIso.ofComponents
    (fun object =>
      (ULiftHom.up (C := CSBranchLocal (.lens input))).mapIso
        ((lensClosedFamilyFiniteDecoderReadingIso input).app object))
    (by
      intro source target morphism
      apply ULift.ext
      rfl)

/-- Lift the global protocol decoder into the common four-family category. -/
noncomputable def aatBranchProtocolFiniteDecoder
    (input : ProtocolFamilyInput) :
    ProtocolPresentation input.schema input.observation ⥤
      AATBranchGlobal (.protocol input) :=
  protocolClosedFamilyFiniteDecoder input ⋙
    (ULiftHom.up (C := CSBranchGlobal (.protocol input)))

/-- The global protocol decoder commutes with the common four-family reading. -/
noncomputable def aatBranchProtocolFiniteDecoderReadingIso
    (input : ProtocolFamilyInput) :
    aatBranchProtocolFiniteDecoder input ⋙
        aatBranchReading (.protocol input) ≅
      protocolObservedFiniteDecoder input ⋙
        (ULiftHom.up (C := CSBranchLocal (.protocol input))) :=
  NatIso.ofComponents
    (fun object =>
      (ULiftHom.up (C := CSBranchLocal (.protocol input))).mapIso
        ((protocolClosedFamilyFiniteDecoderReadingIso input).app object))
    (by
      intro source target morphism
      apply ULift.ext
      rfl)

/-- The accepted lens Karoubi route passes through the common four-family
reconstruction. -/
noncomputable def aatBranchLensKaroubiEquivalence
  (input : LensFamilyInput) :
    Karoubi LensPresentation ≌ AATBranchGlobal (.lens input) :=
  ((lensKaroubiFiberEquivalence input).trans
    (ULiftHom.equiv (C := CSBranchLocal (.lens input)))).trans
    (aatBranchReconstructionEquivalence (.lens input)).symm

/-- The accepted protocol Karoubi route passes through the common four-family
reconstruction. -/
noncomputable def aatBranchProtocolKaroubiEquivalence
  (input : ProtocolFamilyInput) :
    Karoubi (ProtocolPresentation input.schema input.observation) ≌
      AATBranchGlobal (.protocol input) :=
  ((protocolKaroubiObservedRestrictionEquivalence input).trans
    (ULiftHom.equiv (C := CSBranchLocal (.protocol input)))).trans
    (aatBranchReconstructionEquivalence (.protocol input)).symm

/-- The accepted lens Arrow route also passes through the common
reconstruction. -/
noncomputable def aatBranchLensKaroubiArrowEquivalence
  (input : LensFamilyInput) :
    Karoubi (Arrow LensPresentation) ≌
      Arrow (AATBranchGlobal (.lens input)) :=
  ((lensKaroubiFiberArrowEquivalence input).trans
    (Functor.mapArrowEquivalence
      (ULiftHom.equiv (C := CSBranchLocal (.lens input))))).trans
    (aatBranchArrowReconstructionEquivalence (.lens input)).symm

/-- The accepted protocol Arrow route also passes through the common
reconstruction. -/
noncomputable def aatBranchProtocolKaroubiArrowEquivalence
  (input : ProtocolFamilyInput) :
    Karoubi (Arrow
      (ProtocolPresentation input.schema input.observation)) ≌
      Arrow (AATBranchGlobal (.protocol input)) :=
  ((protocolKaroubiObservedRestrictionArrowEquivalence input).trans
    (Functor.mapArrowEquivalence
      (ULiftHom.equiv (C := CSBranchLocal (.protocol input))))).trans
    (aatBranchArrowReconstructionEquivalence (.protocol input)).symm

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction

end AAT.AG.LocalSemanticReconstruction
