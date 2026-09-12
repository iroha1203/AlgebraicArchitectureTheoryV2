import ResearchLean.AG.FullGeometryNormalization.CanonicalNormalization
import ResearchLean.AG.AtomFoundation.TransportLaws

/-!
# Object-level section for complete-geometry normalization

This module begins the endpoint-section construction required by G-122(D).
An architecture object is presented as an Atom configuration together with a
configuration-independent dependent package of auxiliary data.  Swapping the
selected auxiliary datum in each configuration with one fixed base datum
trivializes these fibers.  Conjugating configuration transport by those swaps
gives the raw object action used to lift normalized automorphisms.

## Implementation notes

The action uses the full auxiliary sigma type, not an equality or an
assumption that all objects with one configuration coincide.  Plain
`transportArchitectureObject` was rejected because it preserves auxiliary
data and therefore need not carry the package-selected object to the selected
object in the transported configuration.  An arbitrary choice of a lift for
each normalized map was also rejected because it would not supply the
identity and composition laws required for a group-homomorphic section.  The
two swaps cancel at intermediate configurations, making those laws structural.
-/

namespace AAT.AG.FullGeometryNormalization

universe u

open AtomFoundation DoctrineFiberProduct

/-- The configuration-independent auxiliary datum carried by an architecture
object. -/
abbrev ArchitectureAuxiliaryData : Type (u + 1) :=
  Σ StructureMaps : Type u,
    Σ SelectedQuantities : Type u, StructureMaps × SelectedQuantities

noncomputable local instance architectureAuxiliaryDataDecidableEq :
    DecidableEq ArchitectureAuxiliaryData.{u} := Classical.decEq _

/-- Architecture objects are exactly configurations paired with their full
dependent auxiliary data. -/
def architectureObjectPresentation
    (U : AtomCarrier.{u}) :
    ArchitectureObject U ≃
      Σ _configuration : AtomConfiguration U, ArchitectureAuxiliaryData.{u} where
  toFun A :=
    ⟨A.configuration,
      ⟨A.StructureMaps, A.SelectedQuantities,
        (A.structureMaps, A.selectedQuantities)⟩⟩
  invFun A :=
    { configuration := A.1
      StructureMaps := A.2.1
      SelectedQuantities := A.2.2.1
      structureMaps := A.2.2.2.1
      selectedQuantities := A.2.2.2.2 }
  left_inv A := by cases A; rfl
  right_inv A := by rcases A with ⟨C, S, Q, s, q⟩; rfl

/-- A fixed base point in the universal auxiliary-data type. -/
def architectureAuxiliaryBase : ArchitectureAuxiliaryData.{u} :=
  ⟨ULift.{u} Unit, ULift.{u} Unit, ULift.up (), ULift.up ()⟩

/-- The auxiliary datum selected by `P` at a configuration. -/
noncomputable def selectedArchitectureAuxiliaryData
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (C : AtomConfiguration U) : ArchitectureAuxiliaryData.{u} :=
  (architectureObjectPresentation U
    (P.reading.objectReading.object C)).2

/-- The involution identifying the selected auxiliary datum at `C` with the
fixed universal base datum. -/
noncomputable def selectedArchitectureAuxiliarySwap
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (C : AtomConfiguration U) :
    ArchitectureAuxiliaryData.{u} ≃ ArchitectureAuxiliaryData.{u} :=
  Equiv.swap architectureAuxiliaryBase
    (selectedArchitectureAuxiliaryData P C)

/-- Each selected auxiliary swap is an involution. -/
theorem selectedArchitectureAuxiliarySwap_self
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (C : AtomConfiguration U) (d : ArchitectureAuxiliaryData.{u}) :
    selectedArchitectureAuxiliarySwap P C
        (selectedArchitectureAuxiliarySwap P C d) = d := by
  unfold selectedArchitectureAuxiliarySwap
  exact Equiv.swap_apply_self _ _ _

/-- Presentation of the package-selected object at a configuration. -/
theorem architectureObjectPresentation_selected
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (C : AtomConfiguration U) :
    architectureObjectPresentation U (P.reading.objectReading.object C) =
      ⟨C, selectedArchitectureAuxiliaryData P C⟩ := by
  apply Sigma.ext (P.reading.objectReading.configuration_eq C)
  rfl

/-- The presentation-level raw object action associated with an Atom
equivalence.  Fiber trivializations at the source and transported
configuration are composed around configuration transport. -/
noncomputable def canonicalNormalizationSectionPresentationMap
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (sigma : U.Atom ≃ U.Atom)
    (A : Σ _configuration : AtomConfiguration U,
      ArchitectureAuxiliaryData.{u}) :
    Σ _configuration : AtomConfiguration U, ArchitectureAuxiliaryData.{u} :=
  ⟨A.1.transport sigma,
    selectedArchitectureAuxiliarySwap P (A.1.transport sigma)
      (selectedArchitectureAuxiliarySwap P A.1 A.2)⟩

/-- Raw architecture-object action used by the normalization section. -/
noncomputable def canonicalNormalizationSectionObjectMap
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (sigma : U.Atom ≃ U.Atom) :
    ArchitectureObject U → ArchitectureObject U :=
  (architectureObjectPresentation U).symm ∘
    canonicalNormalizationSectionPresentationMap P sigma ∘
      architectureObjectPresentation U

/-- The lifted object action transports the full Atom configuration by
`sigma`. -/
theorem canonicalNormalizationSectionObjectMap_configuration
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (sigma : U.Atom ≃ U.Atom) (A : ArchitectureObject U) :
    (canonicalNormalizationSectionObjectMap P sigma A).configuration =
      A.configuration.transport sigma := by
  rfl

/-- The swap trivialization sends the selected datum to the fixed base. -/
theorem selectedArchitectureAuxiliarySwap_selected
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (C : AtomConfiguration U) :
    selectedArchitectureAuxiliarySwap P C
        (selectedArchitectureAuxiliaryData P C) =
      architectureAuxiliaryBase := by
  exact Equiv.swap_apply_right _ _

/-- The swap trivialization sends the fixed base back to the selected datum. -/
theorem selectedArchitectureAuxiliarySwap_base
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (C : AtomConfiguration U) :
    selectedArchitectureAuxiliarySwap P C architectureAuxiliaryBase =
      selectedArchitectureAuxiliaryData P C := by
  exact Equiv.swap_apply_left _ _

/-- The raw action carries the package-selected object to the selected object
at the transported configuration. -/
theorem canonicalNormalizationSectionObjectMap_selected
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (sigma : U.Atom ≃ U.Atom) (C : AtomConfiguration U) :
    canonicalNormalizationSectionObjectMap P sigma
        (P.reading.objectReading.object C) =
      P.reading.objectReading.object (C.transport sigma) := by
  apply (architectureObjectPresentation U).injective
  simp only [canonicalNormalizationSectionObjectMap, Function.comp_apply,
    Equiv.apply_symm_apply]
  rw [architectureObjectPresentation_selected,
    architectureObjectPresentation_selected]
  simp only [canonicalNormalizationSectionPresentationMap]
  rw [selectedArchitectureAuxiliarySwap_selected,
    selectedArchitectureAuxiliarySwap_base]

/-- Applying canonical object normalization after the lifted action forgets
exactly the auxiliary lift and retains the transported selected object. -/
theorem canonicalObjectNormalization_sectionObjectMap
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (sigma : U.Atom ≃ U.Atom) (A : ArchitectureObject U) :
    canonicalObjectNormalization P
        (canonicalNormalizationSectionObjectMap P sigma A) =
      P.reading.objectReading.object (A.configuration.transport sigma) := by
  unfold canonicalObjectNormalization
  rw [canonicalNormalizationSectionObjectMap_configuration]

/-- The presentation action of the identity Atom equivalence is the identity. -/
theorem canonicalNormalizationSectionPresentationMap_refl
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (A : Σ _configuration : AtomConfiguration U,
      ArchitectureAuxiliaryData.{u}) :
    canonicalNormalizationSectionPresentationMap P (Equiv.refl _) A = A := by
  rcases A with ⟨C, d⟩
  simp only [canonicalNormalizationSectionPresentationMap]
  rw [show (Equiv.refl U.Atom : U.Atom → U.Atom) = _root_.id by rfl]
  rw [atomConfiguration_transport_id]
  rw [selectedArchitectureAuxiliarySwap_self]

/-- The raw object action of the identity Atom equivalence is the identity. -/
theorem canonicalNormalizationSectionObjectMap_refl
    {U : AtomCarrier.{u}} (P : AATCorePackage U) :
    canonicalNormalizationSectionObjectMap P (Equiv.refl _) = _root_.id := by
  funext A
  apply (architectureObjectPresentation U).injective
  simpa [canonicalNormalizationSectionObjectMap] using
    canonicalNormalizationSectionPresentationMap_refl P
      (architectureObjectPresentation U A)

/-- Successive presentation actions compose according to transitivity of the
Atom equivalences. -/
theorem canonicalNormalizationSectionPresentationMap_trans
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (sigma tau : U.Atom ≃ U.Atom)
    (A : Σ _configuration : AtomConfiguration U,
      ArchitectureAuxiliaryData.{u}) :
    canonicalNormalizationSectionPresentationMap P tau
        (canonicalNormalizationSectionPresentationMap P sigma A) =
      canonicalNormalizationSectionPresentationMap P (sigma.trans tau) A := by
  rcases A with ⟨C, d⟩
  simp only [canonicalNormalizationSectionPresentationMap]
  rw [atomConfiguration_transport_comp]
  rw [show (tau : U.Atom → U.Atom) ∘ (sigma : U.Atom → U.Atom) =
      (sigma.trans tau : U.Atom → U.Atom) by rfl]
  rw [selectedArchitectureAuxiliarySwap_self]

/-- Raw object actions compose strictly as functions after transitivity of
the Atom equivalences. -/
theorem canonicalNormalizationSectionObjectMap_trans
    {U : AtomCarrier.{u}} (P : AATCorePackage U)
    (sigma tau : U.Atom ≃ U.Atom) :
    canonicalNormalizationSectionObjectMap P tau ∘
        canonicalNormalizationSectionObjectMap P sigma =
      canonicalNormalizationSectionObjectMap P (sigma.trans tau) := by
  funext A
  apply (architectureObjectPresentation U).injective
  simpa [canonicalNormalizationSectionObjectMap, Function.comp_apply] using
    canonicalNormalizationSectionPresentationMap_trans P sigma tau
      (architectureObjectPresentation U A)

#assert_standard_axioms_only AAT.AG.FullGeometryNormalization

end AAT.AG.FullGeometryNormalization
