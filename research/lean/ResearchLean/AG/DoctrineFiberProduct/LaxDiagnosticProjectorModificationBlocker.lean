import ResearchLean.AG.DoctrineFiberProduct.LaxDiagnosticProjectorAdmissibleFiber
import ResearchLean.AG.DoctrineFiberProduct.IdempotentExchangeNormalization
import ResearchLean.AG.DoctrineFiberProduct.CanonicalObjectNormalizationNaturality

/-!
# G-117 canonical-normalization modification blocker

The canonical normalization gives an endomorphism at every object of an
admissible core fiber, and those endomorphisms are idempotent.  To assemble
them into a natural transformation on the full subcategory, the current
morphism interface does not supply the operation-level coherence comparing a
general package total morphism with the dependent cast used by canonical
normalization.

This module isolates that exact residual field.  The characterization below is
a blocker artifact, not an assumption accepted as a discharge of G-117(c).
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation CrossStageCoherence

/-- The sole residual field in total-morphism naturality of canonical
normalization.  It compares the actual operation maps of the two composites;
it is not part of `CanonicalObjectNormalizationAdmissible` or
`SignedExactCoreReadingHom`. -/
def CanonicalNormalizationOperationCoherent
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    (hom : PackageTotalHom P Q)
    (admissibleP : CanonicalObjectNormalizationAdmissible P)
    (admissibleQ : CanonicalObjectNormalizationAdmissible Q) : Prop :=
  HEq
    (@SignedExactCoreReadingHom.operationMap U P Q
      ((canonicalObjectNormalizationTotal P admissibleP).comp hom).upper)
    (@SignedExactCoreReadingHom.operationMap U P Q
      (hom.comp (canonicalObjectNormalizationTotal Q admissibleQ)).upper)

/-- The residual operation-map coherence suffices for total-morphism
naturality.  All other computational fields are discharged by the reviewed
G-116 object naturality and extensionality APIs. -/
theorem canonicalObjectNormalizationTotal_natural_of_operationCoherent
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    (hom : PackageTotalHom P Q)
    (admissibleP : CanonicalObjectNormalizationAdmissible P)
    (admissibleQ : CanonicalObjectNormalizationAdmissible Q)
    (operation_coherent :
      CanonicalNormalizationOperationCoherent hom admissibleP admissibleQ) :
    hom.comp (canonicalObjectNormalizationTotal Q admissibleQ) =
      (canonicalObjectNormalizationTotal P admissibleP).comp hom := by
  symm
  apply PackageTotalHom.ext
  · rfl
  · apply SignedExactCoreReadingHom.ext
    · rfl
    · exact canonicalObjectNormalization_natural hom
    · apply equationSystemExactTransport_hext
      · rfl
      · exact canonicalObjectNormalization_natural hom
      · rfl
      · rfl
      · rfl
    · exact operation_coherent
    · rfl
    · rfl
    · rfl

/-- Total-morphism naturality holds exactly when the residual operation maps
are heterogeneously equal.  This characterizes the proof obligation but does
not generate it from the current morphism laws. -/
theorem canonicalObjectNormalizationTotal_natural_iff_operationCoherent
    {U : AtomCarrier.{u}} {P Q : AATCorePackage U}
    (hom : PackageTotalHom P Q)
    (admissibleP : CanonicalObjectNormalizationAdmissible P)
    (admissibleQ : CanonicalObjectNormalizationAdmissible Q) :
    (hom.comp (canonicalObjectNormalizationTotal Q admissibleQ) =
        (canonicalObjectNormalizationTotal P admissibleP).comp hom) ↔
      CanonicalNormalizationOperationCoherent hom admissibleP admissibleQ := by
  constructor
  · intro equality
    unfold CanonicalNormalizationOperationCoherent
    rw [equality]
  · exact canonicalObjectNormalizationTotal_natural_of_operationCoherent
      hom admissibleP admissibleQ

/-- The residual coherence is inhabited for the identity total morphism.  A
negative example for the fixed universal clause is not claimed here. -/
theorem canonicalNormalizationOperationCoherent_id
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (admissible : CanonicalObjectNormalizationAdmissible P) :
    CanonicalNormalizationOperationCoherent
      (PackageTotalHom.id P) admissible admissible := by
  unfold CanonicalNormalizationOperationCoherent
  rfl

/-- The canonical normalization endomorphism at an admissible fiber object.
This is the proposed component of G-117's `ν`; no naturality is hidden in the
definition. -/
noncomputable def admissibleCanonicalNormalizationComponent
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (P : AdmCoreFiber X) : P ⟶ P :=
  ObjectProperty.homMk
    ⟨canonicalObjectNormalizationTotal P.obj.1 P.property,
      by
        apply CategoryTheory.IsHomLift.of_commsq
          (packageProjection U) (𝟙 X)
          (canonicalObjectNormalizationTotal P.obj.1 P.property)
          P.obj.2 P.obj.2
        rw [packageProjection_map]
        exact Category.id_comp _⟩

/-- The underlying total morphism of the proposed component is the reviewed
G-116 canonical normalization. -/
@[simp] theorem admissibleCanonicalNormalizationComponent_hom_hom
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (P : AdmCoreFiber X) :
    (admissibleCanonicalNormalizationComponent P).hom.1 =
      canonicalObjectNormalizationTotal P.obj.1 P.property :=
  rfl

/-- The proposed fiber component is idempotent, by direct use of the reviewed
G-116 total-category theorem. -/
theorem admissibleCanonicalNormalizationComponent_comp
    {U : AtomCarrier.{u}} {X : ExtractionInstance U}
    (P : AdmCoreFiber X) :
    admissibleCanonicalNormalizationComponent P ≫
        admissibleCanonicalNormalizationComponent P =
      admissibleCanonicalNormalizationComponent P := by
  apply ObjectProperty.hom_ext
  apply CategoryTheory.Functor.Fiber.hom_ext
  exact canonicalObjectNormalizationTotal_comp P.obj.1 P.property

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct

end AAT.AG.DoctrineFiberProduct
