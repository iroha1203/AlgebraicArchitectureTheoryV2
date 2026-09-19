import Mathlib.CategoryTheory.Products.Basic
import ResearchLean.AG.LocalSemanticReconstruction.LocalReconstructionEquivalence
import ResearchLean.AG.LocalSemanticReconstruction.LensFiberKaroubiCoherence
import ResearchLean.AG.LocalSemanticReconstruction.ProtocolObservedKaroubiCoherence
import Formal.Util.AssertStandardAxioms

/-!
# A common branch-indexed reconstruction surface for the two CS families

The lens and protocol branches are not merely placed side by side here.  A
single parameter declaration selects a branch and determines its global
realization category, independent local-model category, primitive reading,
and explicit assemblers.  The reconstruction
theorem is quantified over an arbitrary branch parameter.

The finite-presentation route is connected by an explicit global decoder.
Reading that decoder is naturally isomorphic to the accepted local decoder;
the Karoubi restriction and Arrow equivalences are then exposed through the
same branch-indexed surface.  This supplies the common declaration required
for these two mandatory families without claiming that the tagged or G-122
branches have already been added.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory
open CategoryTheory.Idempotents
open AAT.AG.RealizationReconstruction
open LocalReconstructionEquivalence

universe u

/-- The common parameter declaration for the two CS semantic families. -/
inductive CSBranchParameter : Type (u + 1)
  | lens (input : LensFamilyInput.{u})
  | protocol (input : ProtocolFamilyInput.{u})

/-- The global realization category selected by a CS branch parameter. -/
def CSBranchGlobal : CSBranchParameter.{u} → Type (u + 1)
  | .lens input => FamilyRealization.{u, u} (.lens input)
  | .protocol input => FamilyRealization.{u, u} (.protocol input)

/-- The independently defined local-model category selected by a CS branch. -/
def CSBranchLocal : CSBranchParameter.{u} → Type (u + 1)
  | .lens _ => FintypeCat.{u}
  | .protocol input => ProtocolObservedRestrictionModel input

noncomputable instance csBranchGlobalCategory
    (parameter : CSBranchParameter.{u}) : Category (CSBranchGlobal parameter) := by
  cases parameter <;> simp only [CSBranchGlobal] <;> infer_instance

noncomputable instance csBranchLocalCategory
    (parameter : CSBranchParameter.{u}) : Category (CSBranchLocal parameter) := by
  cases parameter <;> simp only [CSBranchLocal] <;> infer_instance

/-- The primitive local reading selected uniformly by the branch parameter. -/
noncomputable def csBranchReading (parameter : CSBranchParameter.{u}) :
    CSBranchGlobal parameter ⥤ CSBranchLocal parameter := by
  cases parameter with
  | lens input => exact lensFiberValueReading input
  | protocol input => exact protocolObservedRestrictionReading input

/-- Directly assemble a local morphism in either CS branch. -/
noncomputable def csBranchAssemble
    (parameter : CSBranchParameter.{u})
    {X Y : CSBranchGlobal parameter}
    (localMorphism : (csBranchReading parameter).obj X ⟶
      (csBranchReading parameter).obj Y) : X ⟶ Y := by
  cases parameter with
  | lens input =>
      cases X with
      | lens source =>
        cases Y with
        | lens target =>
          change finiteLocalValue source.Fiber ⟶
            finiteLocalValue target.Fiber at localMorphism
          exact closedFamilyLensHom
            (LensRealization.ext (fun state => localMorphism state))
  | protocol input =>
      cases X with
      | protocol source =>
        cases Y with
        | protocol target =>
          exact protocolObservedRestrictionAssemble input localMorphism

/-- Reading a branch-indexed assembled morphism returns the supplied local
morphism. -/
@[simp] theorem csBranch_read_assemble
    (parameter : CSBranchParameter.{u})
    {X Y : CSBranchGlobal parameter}
    (localMorphism : (csBranchReading parameter).obj X ⟶
      (csBranchReading parameter).obj Y) :
    (csBranchReading parameter).map
        (csBranchAssemble parameter localMorphism) = localMorphism := by
  cases parameter with
  | lens input =>
      cases X with
      | lens source =>
        cases Y with
        | lens target =>
          change finiteLocalValue source.Fiber ⟶
            finiteLocalValue target.Fiber at localMorphism
          apply FintypeCat.hom_ext
          intro state
          exact congrFun (LensRealization.res_ext
            (fun state => localMorphism state)) state
  | protocol input =>
      cases X with
      | protocol source =>
        cases Y with
        | protocol target =>
          exact protocolObservedRestriction_read_assemble input localMorphism

/-- Assembling a branch-indexed global reading returns the admitted global
morphism. -/
@[simp] theorem csBranch_assemble_read
    (parameter : CSBranchParameter.{u})
    {X Y : CSBranchGlobal parameter}
    (global : X ⟶ Y) :
    csBranchAssemble parameter ((csBranchReading parameter).map global) =
      global := by
  cases parameter with
  | lens input =>
      cases X with
      | lens source =>
        cases Y with
        | lens target =>
          apply ULift.ext
          have semanticEquality :
              (csBranchAssemble (.lens input)
                  ((csBranchReading (.lens input)).map global)).down.toSemanticHom =
                global.down.toSemanticHom := by
            change LensRealization.ext
                (LensRealization.res global.down.toSemanticHom) =
              global.down.toSemanticHom
            exact LensRealization.ext_res global.down.toSemanticHom
          calc
            (csBranchAssemble (.lens input)
                ((csBranchReading (.lens input)).map global)).down =
                LensAATIndependentGeneratedPackageHom.ofSemanticHom
                  ((csBranchAssemble (.lens input)
                    ((csBranchReading (.lens input)).map global)).down.toSemanticHom) :=
              (LensAATIndependentGeneratedPackageHom.ofSemanticHom_toSemanticHom _).symm
            _ = LensAATIndependentGeneratedPackageHom.ofSemanticHom
                  global.down.toSemanticHom := congrArg _ semanticEquality
            _ = global.down :=
              LensAATIndependentGeneratedPackageHom.ofSemanticHom_toSemanticHom _
  | protocol input =>
      cases X with
      | protocol source =>
        cases Y with
        | protocol target =>
          exact protocolObservedRestriction_assemble_read input global

/-- Assemble an arbitrary branch-indexed local object. -/
noncomputable def csBranchRealize
    (parameter : CSBranchParameter.{u})
    (localObject : CSBranchLocal parameter) : CSBranchGlobal parameter := by
  cases parameter with
  | lens input =>
      exact FamilyRealization.lens
        (lensFiberModelRealization input localObject)
  | protocol input =>
      exact FamilyRealization.protocol
        (protocolObservedRestrictionRealization input localObject)

/-- Reading the explicit branch-indexed realization recovers its local object. -/
noncomputable def csBranchRealizeIso
    (parameter : CSBranchParameter.{u})
    (localObject : CSBranchLocal parameter) :
    (csBranchReading parameter).obj
        (csBranchRealize parameter localObject) ≅ localObject := by
  cases parameter with
  | lens input => exact lensFiberModelRealizationIso input localObject
  | protocol input =>
      exact protocolObservedRestrictionRealizationIso input localObject

/-- Explicit separation and assembly for every parameter of the common CS
branch declaration. -/
noncomputable def csBranchReconstructionData
    (parameter : CSBranchParameter.{u}) :
    ReconstructionData (csBranchReading parameter) where
  separation :=
    ⟨fun _ _ => ⟨fun first second equality => by
      rw [← csBranch_assemble_read parameter first,
        equality, csBranch_assemble_read parameter second]⟩⟩
  homAssembly :=
    { assemble := csBranchAssemble parameter
      map_assemble := csBranch_read_assemble parameter }
  objectAssembly :=
    { assembleObject := csBranchRealize parameter
      readAssembledIso := csBranchRealizeIso parameter }

/-- Every CS branch parameter has a primitive-reading category equivalence. -/
noncomputable def csBranchReconstructionEquivalence
    (parameter : CSBranchParameter.{u}) :
    CSBranchGlobal parameter ≌ CSBranchLocal parameter :=
  (csBranchReconstructionData parameter).equivalence

/-- Every coherent branch-local morphism has a unique admitted global
preimage. -/
theorem csBranch_existsUnique_preimage
    (parameter : CSBranchParameter.{u})
    {X Y : CSBranchGlobal parameter}
    (localMorphism : (csBranchReading parameter).obj X ⟶
      (csBranchReading parameter).obj Y) :
    ∃! global : X ⟶ Y,
      (csBranchReading parameter).map global = localMorphism :=
  (csBranchReconstructionData parameter).existsUnique_preimage localMorphism

/-- Insert semantic lenses into their accepted closed-family fiber. -/
def lensSemanticClosedFamilyFunctor (input : LensFamilyInput.{u}) :
    LensRealization input.View input.reference ⥤
      FamilyRealization.{u, u} (.lens input) where
  obj X := FamilyRealization.lens X
  map f := closedFamilyLensHom f
  map_id X := by
    apply ULift.ext
    apply LensAATIndependentGeneratedPackageHom.ext
    funext state
    rfl
  map_comp f g := by
    apply ULift.ext
    apply LensAATIndependentGeneratedPackageHom.ext
    funext state
    rfl

/-- The branch reconstruction itself extends to all arrows on the same local
category, providing the comparison target for the Karoubi Arrow route. -/
noncomputable def csBranchReconstructionArrowEquivalence
    (parameter : CSBranchParameter.{u}) :
    Arrow (CSBranchGlobal parameter) ≌ Arrow (CSBranchLocal parameter) :=
  Functor.mapArrowEquivalence (csBranchReconstructionEquivalence parameter)

/-- Decode a finite lens presentation in the global closed-family fiber before
applying the common branch reading. -/
noncomputable def lensClosedFamilyFiniteDecoder
    (input : LensFamilyInput.{u}) :
    LensPresentation ⥤ FamilyRealization.{u, u} (.lens input) :=
  LensRealization.lensDecoder input.View input.reference ⋙
    lensSemanticClosedFamilyFunctor input

/-- Reading the global lens decoder is naturally the accepted finite-fiber
decoder.  This is the lens commuting comparison with branch reconstruction. -/
noncomputable def lensClosedFamilyFiniteDecoderReadingIso
    (input : LensFamilyInput.{u}) :
    lensClosedFamilyFiniteDecoder input ⋙
        csBranchReading (.lens input) ≅
      lensFiberFiniteDecoder input :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro source target morphism
    apply FintypeCat.hom_ext
    intro state
    rfl)

/-- Decode a finite protocol presentation in the global closed-family fiber
before applying the common branch reading. -/
noncomputable def protocolClosedFamilyFiniteDecoder
    (input : ProtocolFamilyInput.{u}) :
    ProtocolPresentation input.schema input.observation ⥤
      FamilyRealization.{u, u} (.protocol input) :=
  ProtocolPresentation.decoder input.schema input.observation ⋙
    protocolSemanticClosedFamilyFunctor input

/-- Reading the global protocol decoder is naturally the accepted observed
finite decoder. -/
noncomputable def protocolClosedFamilyFiniteDecoderReadingIso
    (input : ProtocolFamilyInput.{u}) :
    protocolClosedFamilyFiniteDecoder input ⋙
        csBranchReading (.protocol input) ≅
      protocolObservedFiniteDecoder input :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro source target morphism
    apply ProtocolObservedRestrictionHom.ext
    apply NatTrans.ext
    funext q
    apply FintypeCat.hom_ext
    intro state
    rfl)

/-- The lens Karoubi reconstruction routed through the common branch
reconstruction rather than merely sharing its codomain. -/
noncomputable def lensKaroubiClosedFamilyViaBranchEquivalence
    (input : LensFamilyInput.{u}) :
    Karoubi LensPresentation ≌
      FamilyRealization.{u, u} (.lens input) :=
  (lensKaroubiFiberEquivalence input).trans
    (csBranchReconstructionEquivalence (.lens input)).symm

/-- The protocol Karoubi reconstruction routed through the common branch
reconstruction. -/
noncomputable def protocolKaroubiClosedFamilyViaBranchEquivalence
    (input : ProtocolFamilyInput.{u}) :
    Karoubi (ProtocolPresentation input.schema input.observation) ≌
      FamilyRealization.{u, u} (.protocol input) :=
  (protocolKaroubiObservedRestrictionEquivalence input).trans
    (csBranchReconstructionEquivalence (.protocol input)).symm

/-- The lens Arrow-level Karoubi route factors through the common branch
Arrow reconstruction. -/
noncomputable def lensKaroubiClosedFamilyArrowViaBranchEquivalence
    (input : LensFamilyInput.{u}) :
    Karoubi (Arrow LensPresentation) ≌
      Arrow (FamilyRealization.{u, u} (.lens input)) :=
  (lensKaroubiFiberArrowEquivalence input).trans
    (csBranchReconstructionArrowEquivalence (.lens input)).symm

/-- The protocol Arrow-level Karoubi route factors through the common branch
Arrow reconstruction. -/
noncomputable def protocolKaroubiClosedFamilyArrowViaBranchEquivalence
    (input : ProtocolFamilyInput.{u}) :
    Karoubi (Arrow
        (ProtocolPresentation input.schema input.observation)) ≌
      Arrow (FamilyRealization.{u, u} (.protocol input)) :=
  (protocolKaroubiObservedRestrictionArrowEquivalence input).trans
    (csBranchReconstructionArrowEquivalence (.protocol input)).symm

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction

end AAT.AG.LocalSemanticReconstruction
