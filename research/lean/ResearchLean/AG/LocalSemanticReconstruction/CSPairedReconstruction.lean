import Mathlib.CategoryTheory.Products.Basic
import ResearchLean.AG.LocalSemanticReconstruction.LocalReconstructionEquivalence
import ResearchLean.AG.LocalSemanticReconstruction.LensFiberKaroubiCoherence
import ResearchLean.AG.LocalSemanticReconstruction.ProtocolObservedKaroubiCoherence
import Formal.Util.AssertStandardAxioms

/-!
# Simultaneous reconstruction of the two CS semantic families

This module places the lens and protocol realizations in one product category
and reads them into the product of their independently defined local-model
categories.  The inverse on morphisms is constructed directly from
`LensRealization.ext` and the observed-protocol assembler.  The inverse on
objects is constructed from the product lens and the double-opposite protocol
realization.  Thus neither local object stores a completed realization or an
extension certificate.

The two inverse laws, separation, object assembly, and the resulting category
equivalence are proved on the common product surface.  The same surface also
contains the paired finite decoder, its retract-generation theorem, and the
product Karoubi and Arrow equivalences, so the reconstruction is connected to
the accepted finite-presentation route in this module rather than in a later
wrapper.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory
open CategoryTheory.Idempotents
open AAT.AG.RealizationReconstruction
open LocalReconstructionEquivalence

universe u

/-- The two accepted CS realization families, retained as independent factors. -/
abbrev CSPairedRealization
    (lensInput : LensFamilyInput.{u})
    (protocolInput : ProtocolFamilyInput.{u}) :=
  FamilyRealization.{u, u} (.lens lensInput) ×
    FamilyRealization.{u, u} (.protocol protocolInput)

/-- The two independently defined local-model categories. -/
abbrev CSPairedLocalModel
    (protocolInput : ProtocolFamilyInput.{u}) :=
  FintypeCat.{u} × ProtocolObservedRestrictionModel protocolInput

/-- Simultaneously read a lens on its finite reference fiber and a protocol on
its complete observation-aware finite restriction diagram. -/
noncomputable def csPairedReading
    (lensInput : LensFamilyInput.{u})
    (protocolInput : ProtocolFamilyInput.{u}) :
    CSPairedRealization lensInput protocolInput ⥤
      CSPairedLocalModel protocolInput :=
  (lensFiberValueReading lensInput).prod
    (protocolObservedRestrictionReading protocolInput)

/-- Assemble a pair of local morphisms directly from the primitive lens and
protocol assemblers. -/
noncomputable def csPairedAssemble
    (lensInput : LensFamilyInput.{u})
    (protocolInput : ProtocolFamilyInput.{u})
    {X Y : CSPairedRealization lensInput protocolInput}
    (localMorphism : (csPairedReading lensInput protocolInput).obj X ⟶
      (csPairedReading lensInput protocolInput).obj Y) : X ⟶ Y := by
  rcases X with ⟨lensSource, protocolSource⟩
  rcases Y with ⟨lensTarget, protocolTarget⟩
  cases lensSource with
  | lens lensSource =>
    cases lensTarget with
    | lens lensTarget =>
      cases protocolSource with
      | protocol protocolSource =>
        cases protocolTarget with
        | protocol protocolTarget =>
          exact
            (closedFamilyLensHom
                (LensRealization.ext (fun state => localMorphism.1 state)),
              protocolObservedRestrictionAssemble protocolInput localMorphism.2)

/-- Reading an explicitly assembled pair returns both supplied local
morphisms. -/
@[simp] theorem csPaired_read_assemble
    (lensInput : LensFamilyInput.{u})
    (protocolInput : ProtocolFamilyInput.{u})
    {X Y : CSPairedRealization lensInput protocolInput}
    (localMorphism : (csPairedReading lensInput protocolInput).obj X ⟶
      (csPairedReading lensInput protocolInput).obj Y) :
    (csPairedReading lensInput protocolInput).map
        (csPairedAssemble lensInput protocolInput localMorphism) =
      localMorphism := by
  rcases X with ⟨lensSource, protocolSource⟩
  rcases Y with ⟨lensTarget, protocolTarget⟩
  cases lensSource with
  | lens lensSource =>
    cases lensTarget with
    | lens lensTarget =>
      cases protocolSource with
      | protocol protocolSource =>
        cases protocolTarget with
        | protocol protocolTarget =>
          apply CategoryTheory.Prod.hom_ext
          · apply FintypeCat.hom_ext
            intro state
            exact congrFun (LensRealization.res_ext
              (fun state => localMorphism.1 state)) state
          · exact protocolObservedRestriction_read_assemble
              protocolInput localMorphism.2

/-- Assembling the paired reading of an admitted global morphism returns that
global morphism. -/
@[simp] theorem csPaired_assemble_read
    (lensInput : LensFamilyInput.{u})
    (protocolInput : ProtocolFamilyInput.{u})
    {X Y : CSPairedRealization lensInput protocolInput}
    (global : X ⟶ Y) :
    csPairedAssemble lensInput protocolInput
        ((csPairedReading lensInput protocolInput).map global) = global := by
  rcases X with ⟨lensSource, protocolSource⟩
  rcases Y with ⟨lensTarget, protocolTarget⟩
  cases lensSource with
  | lens lensSource =>
    cases lensTarget with
    | lens lensTarget =>
      cases protocolSource with
      | protocol protocolSource =>
        cases protocolTarget with
        | protocol protocolTarget =>
          apply CategoryTheory.Prod.hom_ext
          · apply ULift.ext
            have semanticEquality :
                (csPairedAssemble lensInput protocolInput
                    ((csPairedReading lensInput protocolInput).map global)).1.down.toSemanticHom =
                  global.1.down.toSemanticHom := by
              exact LensRealization.ext_res global.1.down.toSemanticHom
            calc
              (csPairedAssemble lensInput protocolInput
                  ((csPairedReading lensInput protocolInput).map global)).1.down =
                  LensAATIndependentGeneratedPackageHom.ofSemanticHom
                    ((csPairedAssemble lensInput protocolInput
                      ((csPairedReading lensInput protocolInput).map global)).1.down.toSemanticHom) :=
                (LensAATIndependentGeneratedPackageHom.ofSemanticHom_toSemanticHom
                  _).symm
              _ = LensAATIndependentGeneratedPackageHom.ofSemanticHom
                    global.1.down.toSemanticHom := congrArg _ semanticEquality
              _ = global.1.down :=
                LensAATIndependentGeneratedPackageHom.ofSemanticHom_toSemanticHom _
          · exact protocolObservedRestriction_assemble_read
              protocolInput global.2

/-- The global Hom pair and the coherent local Hom pair are explicitly
equivalent, retaining noninvertible morphisms in both factors. -/
noncomputable def csPairedHomEquiv
    (lensInput : LensFamilyInput.{u})
    (protocolInput : ProtocolFamilyInput.{u})
    (X Y : CSPairedRealization lensInput protocolInput) :
    (X ⟶ Y) ≃
      ((csPairedReading lensInput protocolInput).obj X ⟶
        (csPairedReading lensInput protocolInput).obj Y) where
  toFun := (csPairedReading lensInput protocolInput).map
  invFun := csPairedAssemble lensInput protocolInput
  left_inv := csPaired_assemble_read lensInput protocolInput
  right_inv := csPaired_read_assemble lensInput protocolInput

/-- Assemble a pair of local objects using the product lens and the explicit
observed-protocol realization. -/
noncomputable def csPairedRealize
    (lensInput : LensFamilyInput.{u})
    (protocolInput : ProtocolFamilyInput.{u})
    (localObject : CSPairedLocalModel protocolInput) :
    CSPairedRealization lensInput protocolInput :=
  (FamilyRealization.lens
      (lensFiberModelRealization lensInput localObject.1),
    FamilyRealization.protocol
      (protocolObservedRestrictionRealization protocolInput localObject.2))

/-- Reading the explicitly assembled pair of objects recovers the supplied
local pair up to the componentwise canonical isomorphisms. -/
noncomputable def csPairedRealizeIso
    (lensInput : LensFamilyInput.{u})
    (protocolInput : ProtocolFamilyInput.{u})
    (localObject : CSPairedLocalModel protocolInput) :
    (csPairedReading lensInput protocolInput).obj
        (csPairedRealize lensInput protocolInput localObject) ≅ localObject :=
  Iso.prod
    (lensFiberModelRealizationIso lensInput localObject.1)
    (protocolObservedRestrictionRealizationIso protocolInput localObject.2)

/-- Separation, Hom assembly, and object assembly for the paired primitive
reading, with no equivalence supplied as input data. -/
noncomputable def csPairedReconstructionData
    (lensInput : LensFamilyInput.{u})
    (protocolInput : ProtocolFamilyInput.{u}) :
    ReconstructionData (csPairedReading lensInput protocolInput) where
  separation :=
    ⟨fun _ _ =>
      ⟨(csPairedHomEquiv lensInput protocolInput _ _).injective⟩⟩
  homAssembly :=
    { assemble := csPairedAssemble lensInput protocolInput
      map_assemble := csPaired_read_assemble lensInput protocolInput }
  objectAssembly :=
    { assembleObject := csPairedRealize lensInput protocolInput
      readAssembledIso := csPairedRealizeIso lensInput protocolInput }

/-- The two CS realization families are simultaneously equivalent to their
independently defined local-model categories. -/
noncomputable def csPairedReconstructionEquivalence
    (lensInput : LensFamilyInput.{u})
    (protocolInput : ProtocolFamilyInput.{u}) :
    CSPairedRealization lensInput protocolInput ≌
      CSPairedLocalModel protocolInput :=
  (csPairedReconstructionData lensInput protocolInput).equivalence

/-- The forward functor of simultaneous reconstruction is exactly the paired
primitive reading, rather than a newly chosen equivalent functor. -/
@[simp] theorem csPairedReconstructionEquivalence_functor
    (lensInput : LensFamilyInput.{u})
    (protocolInput : ProtocolFamilyInput.{u}) :
    (csPairedReconstructionEquivalence lensInput protocolInput).functor =
      csPairedReading lensInput protocolInput :=
  rfl

/-- Every coherent local Hom pair has a unique admitted global preimage. -/
theorem csPaired_existsUnique_preimage
    (lensInput : LensFamilyInput.{u})
    (protocolInput : ProtocolFamilyInput.{u})
    {X Y : CSPairedRealization lensInput protocolInput}
    (localMorphism : (csPairedReading lensInput protocolInput).obj X ⟶
      (csPairedReading lensInput protocolInput).obj Y) :
    ∃! global : X ⟶ Y,
      (csPairedReading lensInput protocolInput).map global = localMorphism :=
  (csPairedReconstructionData lensInput protocolInput).existsUnique_preimage
    localMorphism

/-- The paired finite decoder reads both accepted presentation decoders on the
same local-model product surface. -/
noncomputable def csPairedFiniteDecoder
    (lensInput : LensFamilyInput.{u})
    (protocolInput : ProtocolFamilyInput.{u}) :
    (LensPresentation ×
      ProtocolPresentation protocolInput.schema protocolInput.observation) ⥤
      CSPairedLocalModel protocolInput :=
  (lensFiberFiniteDecoder lensInput).prod
    (protocolObservedFiniteDecoder protocolInput)

/-- Every paired local model is a retract of the reading of a pair of finite
presentations. -/
theorem csPairedFiniteDecoder_retractGeneratedBy
    (lensInput : LensFamilyInput.{u})
    (protocolInput : ProtocolFamilyInput.{u}) :
    RetractGeneratedBy (csPairedFiniteDecoder lensInput protocolInput) := by
  intro localObject
  rcases lensFiberFiniteDecoder_retractGeneratedBy lensInput localObject.1 with
    ⟨lensPresentation, lensInsertion, lensRetraction, lensRetract⟩
  rcases protocolObservedFiniteDecoder_retractGeneratedBy protocolInput localObject.2 with
    ⟨protocolPresentation, protocolInsertion, protocolRetraction,
      protocolRetract⟩
  exact ⟨(lensPresentation, protocolPresentation),
    (lensInsertion, protocolInsertion),
    (lensRetraction, protocolRetraction),
    CategoryTheory.Prod.hom_ext lensRetract protocolRetract⟩

/-- The accepted Karoubi reconstructions of both finite presentation
categories act simultaneously on the paired local-model surface. -/
noncomputable def csPairedKaroubiEquivalence
    (lensInput : LensFamilyInput.{u})
    (protocolInput : ProtocolFamilyInput.{u}) :
    Karoubi LensPresentation ×
        Karoubi (ProtocolPresentation protocolInput.schema protocolInput.observation) ≌
      CSPairedLocalModel protocolInput :=
  (lensKaroubiFiberEquivalence lensInput).prod
    (protocolKaroubiObservedRestrictionEquivalence protocolInput)

/-- Restricting simultaneous Karoubi reconstruction to the two finite
presentation categories recovers the paired finite decoder. -/
noncomputable def csPairedKaroubiRestrictionIso
    (lensInput : LensFamilyInput.{u})
    (protocolInput : ProtocolFamilyInput.{u}) :
    ((toKaroubi LensPresentation).prod
        (toKaroubi
          (ProtocolPresentation protocolInput.schema protocolInput.observation))) ⋙
        (csPairedKaroubiEquivalence lensInput protocolInput).functor ≅
      csPairedFiniteDecoder lensInput protocolInput :=
  NatIso.prod
    (lensKaroubiFiberRestrictionIso lensInput)
    (protocolKaroubiObservedRestrictionRestrictionIso protocolInput)

/-- The paired Arrow-level Karoubi reconstruction retains arbitrary local
morphism pairs, not only isomorphisms. -/
noncomputable def csPairedKaroubiArrowEquivalence
    (lensInput : LensFamilyInput.{u})
    (protocolInput : ProtocolFamilyInput.{u}) :
    Karoubi (Arrow LensPresentation) ×
        Karoubi (Arrow
          (ProtocolPresentation protocolInput.schema protocolInput.observation)) ≌
      Arrow FintypeCat.{u} ×
        Arrow (ProtocolObservedRestrictionModel protocolInput) :=
  (lensKaroubiFiberArrowEquivalence lensInput).prod
    (protocolKaroubiObservedRestrictionArrowEquivalence protocolInput)

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction

end AAT.AG.LocalSemanticReconstruction
