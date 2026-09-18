import ResearchLean.AG.LocalSemanticReconstruction.G122FixedComparisonLocalSlice
import ResearchLean.AG.RealizationReconstruction.G122FiniteTotalRestriction
import ResearchLean.AG.FullGeometryNormalization.ExactBarBetaClassification
import ResearchLean.AG.DoctrineFiberProduct.CanonicalObjectNormalizationAPI
import Formal.Util.AssertStandardAxioms

/-!
# Primitive finite probe for the fixed G-122 comparison image

The fixed comparison slice has two semantic morphisms.  This module detects
them using only two evaluations of the primitive architecture-object map.  The
selected source objects are the inverse `barAlpha` images of two distinct
objects with the same configuration.  The generated target projector applies
canonical normalization, so it identifies their images, while `barAlpha`
retains both objects.

The resulting nonempty finite probe separates the complete morphisms in the
fixed semantic image.  Its primitive restriction defines a reading into the
existing two-valued local model, and the existing assembly map is inverse in
both directions.  Thus the probe, separation theorem, local reconstruction,
and expanded G-122 Hom surface are connected in one construction.

This result concerns the fixed three-comparison image.  It does not claim that
the two selected points separate every complete geometry morphism between the
same endpoints.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory AtomFoundation DoctrineFiberProduct GeometryTransport
open AAT.AG.RealizationReconstruction
open AAT.AG.FullGeometryNormalization

namespace G122PrimitiveComparisonProbe

open G122ClosedFamilyExpansion G122FixedComparisonLocalSlice

noncomputable section

local instance : DecidableEq finiteAxisFoldG122FamilyInput.Carrier.Atom :=
  finiteAxisFoldG122FamilyInput.atomDecidableEq

local instance : CommRing finiteAxisFoldG122FamilyInput.Coefficient :=
  finiteAxisFoldG122FamilyInput.coefficientCommRing

/-- The fixed direct endpoint, named locally for the probe construction. -/
abbrev Direct := finiteAxisFoldDirectObject

/-- The fixed via-base endpoint, named locally for the probe construction. -/
abbrev ViaBase := finiteAxisFoldViaBaseObject

/-- The invertible five-factor comparison used to pull probe points back to
the direct endpoint. -/
noncomputable abbrev comparisonIso : Direct ≅ ViaBase :=
  G122GeneratedGeometryObject.barAlphaIso finiteAxisFoldG122FamilyInput
    finiteAxisFoldG122CellInput

/-- The generated target projector on the via-base endpoint. -/
noncomputable abbrev targetProjector : ViaBase ⟶ ViaBase :=
  G122GeneratedGeometryObject.barD finiteAxisFoldG122FamilyInput
    finiteAxisFoldG122CellInput

/-- On the selected finite-axis-fold input, the target projector is the
canonical normalization of the actual via-base endpoint. -/
theorem targetProjector_eq_endpointNormalization :
    targetProjector =
      (canonicalGeometryFiberNormalization
        (authoredExactViaBaseGeometryAt finiteAxisFoldG122FamilyInput.authored
          finiteAxisFoldG122CellInput.cell
          finiteAxisFoldG122FamilyInput.Coefficient
          (G122CellInput.fixedGeometry finiteAxisFoldG122FamilyInput
            finiteAxisFoldG122CellInput))
        (authoredExactViaBaseGeometryAt_admissible
          finiteAxisFoldG122FamilyInput.authored
          finiteAxisFoldG122CellInput.cell
          finiteAxisFoldG122FamilyInput.Coefficient
          (G122CellInput.fixedGeometry finiteAxisFoldG122FamilyInput
            finiteAxisFoldG122CellInput)
          (finiteAxisFold_idempotentExchange_witnessPacket).2.1)).1 := by
  letI := finiteAxisFoldG122FamilyInput.atomDecidableEq
  exact congrArg Subtype.val
    (authoredExactBarDAt_eq_endpoint_normalization
      finiteAxisFoldG122FamilyInput.authored
      finiteAxisFoldG122CellInput.cell
      finiteAxisFoldG122CellInput.cochain
      finiteAxisFoldG122FamilyInput.Coefficient
      (G122CellInput.fixedGeometry finiteAxisFoldG122FamilyInput
        finiteAxisFoldG122CellInput)
      ⟨(finiteAxisFold_idempotentExchange_witnessPacket).1,
        (finiteAxisFold_idempotentExchange_witnessPacket).2.1⟩)

/-- The generated projector identifies the two distinct same-configuration
objects. -/
theorem targetProjector_collapses_probeObjects :
    targetProjector.base.upper.objectMap finiteAxisFoldUnitObject =
      targetProjector.base.upper.objectMap finiteAxisFoldBoolObject := by
  rw [targetProjector_eq_endpointNormalization]
  change canonicalObjectNormalization
      (ViaBase.package finiteAxisFoldG122FamilyInput).core
        finiteAxisFoldUnitObject =
    canonicalObjectNormalization
      (ViaBase.package finiteAxisFoldG122FamilyInput).core
        finiteAxisFoldBoolObject
  apply canonicalObjectNormalization_eq_of_configuration_eq
  rw [finiteAxisFoldUnitObject_configuration,
    finiteAxisFoldBoolObject_configuration]

/-- The first probe point is the inverse-comparison image of the unit-decorated
object. -/
noncomputable def unitPreimage : ArchitectureObject FiniteModel.carrier :=
  comparisonIso.inv.base.upper.objectMap finiteAxisFoldUnitObject

/-- The second probe point is the inverse-comparison image of the
Boolean-decorated object. -/
noncomputable def boolPreimage : ArchitectureObject FiniteModel.carrier :=
  comparisonIso.inv.base.upper.objectMap finiteAxisFoldBoolObject

/-- The five-factor comparison sends the first probe point back to its chosen
via-base object. -/
theorem barAlpha_unitPreimage :
    finiteAxisFoldBarAlpha.base.upper.objectMap unitPreimage =
      finiteAxisFoldUnitObject := by
  have equality := congrArg
    (fun hom : ViaBase ⟶ ViaBase =>
      hom.base.upper.objectMap finiteAxisFoldUnitObject)
    comparisonIso.inv_hom_id
  exact equality

/-- The five-factor comparison sends the second probe point back to its chosen
via-base object. -/
theorem barAlpha_boolPreimage :
    finiteAxisFoldBarAlpha.base.upper.objectMap boolPreimage =
      finiteAxisFoldBoolObject := by
  have equality := congrArg
    (fun hom : ViaBase ⟶ ViaBase =>
      hom.base.upper.objectMap finiteAxisFoldBoolObject)
    comparisonIso.inv_hom_id
  exact equality

/-- The generated comparison identifies the two probe points because it is
`barAlpha` followed by the target normalization. -/
theorem generatedBarBeta_preimages_eq :
    finiteAxisFoldGeneratedBarBeta.base.upper.objectMap unitPreimage =
      finiteAxisFoldGeneratedBarBeta.base.upper.objectMap boolPreimage := by
  change
    (G122GeneratedGeometryObject.barBeta finiteAxisFoldG122FamilyInput
      finiteAxisFoldG122CellInput).base.upper.objectMap unitPreimage =
    (G122GeneratedGeometryObject.barBeta finiteAxisFoldG122FamilyInput
      finiteAxisFoldG122CellInput).base.upper.objectMap boolPreimage
  rw [G122GeneratedGeometryObject.barBeta_factor]
  change targetProjector.base.upper.objectMap
      (finiteAxisFoldBarAlpha.base.upper.objectMap unitPreimage) =
    targetProjector.base.upper.objectMap
      (finiteAxisFoldBarAlpha.base.upper.objectMap boolPreimage)
  rw [barAlpha_unitPreimage, barAlpha_boolPreimage]
  exact targetProjector_collapses_probeObjects

/-- A two-point primitive probe.  Every other core component is empty. -/
noncomputable def coreProbe : G122FiniteCoreProbe
    finiteAxisFoldG122FamilyInput Direct :=
  { (G122FiniteTotalHomProbe.empty finiteAxisFoldG122FamilyInput Direct
      ViaBase).core with
    objectCard := 2
    objectValue := Fin.cases unitPreimage (fun _ => boolPreimage) }

/-- The core probe is genuinely nonempty. -/
@[simp] theorem coreProbe_objectCard : coreProbe.objectCard = 2 :=
  rfl

/-- The primitive two-point restriction distinguishes generated `barBeta`
from `barAlpha`. -/
theorem coreProbe_generatedBarBeta_ne_barAlpha :
    coreProbe.objectRestriction finiteAxisFoldGeneratedBarBeta ≠
      coreProbe.objectRestriction finiteAxisFoldBarAlpha := by
  intro equality
  have atUnit := congrFun equality (0 : Fin 2)
  have atBool := congrFun equality (1 : Fin 2)
  apply finiteAxisFoldUnitObject_ne_boolObject
  rw [← barAlpha_unitPreimage, ← barAlpha_boolPreimage]
  exact atUnit.symm.trans (generatedBarBeta_preimages_eq.trans atBool)

/-- The same core probe embedded in the complete finite-probe surface. -/
noncomputable def totalProbe : G122FiniteTotalHomProbe
    finiteAxisFoldG122FamilyInput Direct ViaBase :=
  { G122FiniteTotalHomProbe.empty finiteAxisFoldG122FamilyInput Direct
      ViaBase with
    core := coreProbe }

/-- The complete probe agreement proposition fails for the two distinct fixed
comparisons, witnessed solely by its primitive object component. -/
theorem totalProbe_not_agreement_generatedBarBeta_barAlpha :
    ¬ G122FiniteTotalHomProbe.Agreement totalProbe
      finiteAxisFoldGeneratedBarBeta finiteAxisFoldBarAlpha := by
  intro agreement
  exact coreProbe_generatedBarBeta_ne_barAlpha (funext agreement.object)

/-- Read the fixed semantic image using only its two-point primitive object
restriction. -/
noncomputable def primitiveRead (morphism : SemanticImage) : LocalValue := by
  classical
  exact if coreProbe.objectRestriction morphism.1 =
      coreProbe.objectRestriction finiteAxisFoldBarAlpha then
    .alpha
  else
    .generated

/-- The primitive restriction reads `barAlpha` as the shared alpha class. -/
@[simp] theorem primitiveRead_barAlpha :
    primitiveRead ⟨finiteAxisFoldBarAlpha, ⟨.barAlpha, rfl⟩⟩ = .alpha := by
  simp [primitiveRead]

/-- The primitive restriction reads generated `barBeta` as the generated
class. -/
@[simp] theorem primitiveRead_generatedBarBeta :
    primitiveRead
        ⟨finiteAxisFoldGeneratedBarBeta, ⟨.generatedBarBeta, rfl⟩⟩ =
      .generated := by
  classical
  change (if coreProbe.objectRestriction finiteAxisFoldGeneratedBarBeta =
      coreProbe.objectRestriction finiteAxisFoldBarAlpha then
    LocalValue.alpha else LocalValue.generated) = LocalValue.generated
  rw [if_neg coreProbe_generatedBarBeta_ne_barAlpha]

/-- The constant-one comparison has the same primitive reading as
`barAlpha`. -/
@[simp] theorem primitiveRead_identityBarBeta :
    primitiveRead
        ⟨finiteAxisFoldIdentityBarBeta, ⟨.identityBarBeta, rfl⟩⟩ =
      .alpha := by
  rw [show (⟨finiteAxisFoldIdentityBarBeta,
      ⟨FiniteAxisFoldComparisonCode.identityBarBeta, rfl⟩⟩ : SemanticImage) =
        ⟨finiteAxisFoldBarAlpha, ⟨.barAlpha, rfl⟩⟩ by
      apply Subtype.ext
      exact finiteAxisFoldIdentityBarBeta_eq_barAlpha]
  exact primitiveRead_barAlpha

/-- Primitive reading after the existing assembly is the identity. -/
@[simp] theorem primitiveRead_assemble (value : LocalValue) :
    primitiveRead (assemble value) = value := by
  cases value with
  | alpha => exact primitiveRead_barAlpha
  | generated => exact primitiveRead_generatedBarBeta

/-- Existing assembly after primitive reading recovers every morphism in the
fixed semantic image. -/
@[simp] theorem assemble_primitiveRead (morphism : SemanticImage) :
    assemble (primitiveRead morphism) = morphism := by
  rcases morphism with ⟨morphism, ⟨code, equality⟩⟩
  subst morphism
  apply Subtype.ext
  cases code with
  | barAlpha =>
      rw [primitiveRead_barAlpha]
      rfl
  | generatedBarBeta =>
      rw [primitiveRead_generatedBarBeta]
      rfl
  | identityBarBeta =>
      rw [primitiveRead_identityBarBeta]
      exact finiteAxisFoldIdentityBarBeta_eq_barAlpha.symm

/-- The fixed semantic image is reconstructed from the existing finite local
value by a reading that uses only primitive object evaluations. -/
noncomputable def primitiveSemanticEquivLocal : SemanticImage ≃ LocalValue where
  toFun := primitiveRead
  invFun := assemble
  left_inv := assemble_primitiveRead
  right_inv := primitiveRead_assemble

/-- The primitive reading agrees with Cycle 46's semantic classifier on the
whole fixed image. -/
theorem primitiveRead_eq_read (morphism : SemanticImage) :
    primitiveRead morphism = read morphism := by
  rcases morphism with ⟨morphism, ⟨code, equality⟩⟩
  subst morphism
  cases code with
  | barAlpha => rw [primitiveRead_barAlpha, read_barAlpha]
  | generatedBarBeta =>
      rw [primitiveRead_generatedBarBeta, read_generatedBarBeta]
  | identityBarBeta =>
      rw [primitiveRead_identityBarBeta, read_identityBarBeta]

/-- Complete pointwise probe agreement separates every pair in the fixed
semantic image. -/
theorem totalProbe_separates_semanticImage
    (first second : SemanticImage)
    (agreement : G122FiniteTotalHomProbe.Agreement totalProbe
      first.1 second.1) :
    first = second := by
  have restriction_eq : coreProbe.objectRestriction first.1 =
      coreProbe.objectRestriction second.1 := funext agreement.object
  have reading_eq : primitiveRead first = primitiveRead second := by
    simp only [primitiveRead]
    rw [restriction_eq]
  calc
    first = assemble (primitiveRead first) := (assemble_primitiveRead first).symm
    _ = assemble (primitiveRead second) := congrArg assemble reading_eq
    _ = second := assemble_primitiveRead second

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.G122PrimitiveComparisonProbe

end

end G122PrimitiveComparisonProbe

end AAT.AG.LocalSemanticReconstruction
