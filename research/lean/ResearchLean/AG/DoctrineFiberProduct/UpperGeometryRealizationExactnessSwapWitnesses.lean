import ResearchLean.AG.DoctrineFiberProduct.UpperGeometryRealizationExactnessWitnesses
import ResearchLean.AG.AtomFoundation.Transport

/-!
# Structure-preserving negative realization witness

This module replaces the lossy object-normalizing upper map of the G-108
negative fixture by an involution that transports only the configuration of an
arbitrary architecture object.  The complete signed upper map cancels on every
computational field, while its matching total hom retains the same concrete
support-reading obstruction.  Hence exact upper equivalence alone does not
produce realization-exactness.
-/

namespace AAT.AG.DoctrineFiberProduct

open AtomFoundation GeometryTransport
open AAT.AG.ReadingFunctorialityFinite

private theorem structurePreservingSwapEquationTransport_ext
    {U : AtomCarrier.{u}}
    {A B : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A}
    {D : Site.ContextPreorderCategory B}
    {E : ArchitecturalEquationSystem C}
    {G : ArchitecturalEquationSystem D}
    {e : Equiv U.Atom U.Atom}
    {objectMap : ArchitectureObject U → ArchitectureObject U}
    {T S : EquationSystemExactTransport E G e objectMap}
    (hcontext : T.contextEquivalence = S.contextEquivalence)
    (hequation : T.equationEquiv = S.equationEquiv)
    (hobservable : HEq T.observableEquiv S.observableEquiv) : T = S := by
  cases T
  cases S
  cases hcontext
  cases hequation
  cases hobservable
  rfl

private theorem structurePreservingSwapEquationTransport_hext
    {U : AtomCarrier.{u}}
    {A B : ArchitectureObject U}
    {C : Site.ContextPreorderCategory A}
    {D : Site.ContextPreorderCategory B}
    {E : ArchitecturalEquationSystem C}
    {G : ArchitecturalEquationSystem D}
    {e e' : Equiv U.Atom U.Atom}
    {objectMap objectMap' : ArchitectureObject U → ArchitectureObject U}
    {T : EquationSystemExactTransport E G e objectMap}
    {S : EquationSystemExactTransport E G e' objectMap'}
    (he : e = e') (hobjectMap : objectMap = objectMap')
    (hcontext : T.contextEquivalence = S.contextEquivalence)
    (hequation : T.equationEquiv = S.equationEquiv)
    (hobservable : HEq T.observableEquiv S.observableEquiv) : HEq T S := by
  cases he
  cases hobjectMap
  exact heq_of_eq
    (structurePreservingSwapEquationTransport_ext hcontext hequation hobservable)

private theorem structurePreservingSwapConfigurationHom_hext
    {U : AtomCarrier.{u}}
    {C C' D D' : AtomConfiguration U}
    (f : ConfigurationHom C D) (g : ConfigurationHom C' D')
    (hsource : C = C') (htarget : D = D')
    (hatom : f.atomMap = g.atomMap) : HEq f g := by
  cases hsource
  cases htarget
  exact heq_of_eq (ConfigurationHom.ext hatom)

/-- Transport only an object's configuration along the public finite Atom
involution; all opaque structure and selected-quantity data are retained. -/
noncomputable def structurePreservingSwapObjectMap
    (A : ArchitectureObject FiniteModel.carrier) :
    ArchitectureObject FiniteModel.carrier :=
  AtomFoundation.transportArchitectureObject
    nonidentityExactCoreChange.atomEquiv A

theorem structurePreservingSwapAtom_involutive
    (atom : FiniteModel.carrier.Atom) :
    nonidentityExactCoreChange.atomEquiv
        (nonidentityExactCoreChange.atomEquiv atom) = atom := by
  cases atom <;> rfl

@[simp] theorem structurePreservingSwapObjectMap_structureMaps
    (A : ArchitectureObject FiniteModel.carrier) :
    (structurePreservingSwapObjectMap A).StructureMaps = A.StructureMaps :=
  rfl

@[simp] theorem structurePreservingSwapObjectMap_selectedQuantities
    (A : ArchitectureObject FiniteModel.carrier) :
    (structurePreservingSwapObjectMap A).SelectedQuantities =
      A.SelectedQuantities :=
  rfl

@[simp] theorem structurePreservingSwapObjectMap_structureMaps_value
    (A : ArchitectureObject FiniteModel.carrier) :
    HEq (structurePreservingSwapObjectMap A).structureMaps A.structureMaps :=
  HEq.rfl

@[simp] theorem structurePreservingSwapObjectMap_selectedQuantities_value
    (A : ArchitectureObject FiniteModel.carrier) :
    HEq (structurePreservingSwapObjectMap A).selectedQuantities
      A.selectedQuantities :=
  HEq.rfl

theorem structurePreservingSwapObjectMap_involutive
    (A : ArchitectureObject FiniteModel.carrier) :
    structurePreservingSwapObjectMap (structurePreservingSwapObjectMap A) = A := by
  unfold structurePreservingSwapObjectMap
  rw [show nonidentityExactCoreChange.atomEquiv =
      nonidentityExactCoreChange.atomEquiv.symm by
    apply Equiv.ext
    intro atom
    apply nonidentityExactCoreChange.atomEquiv.injective
    rw [structurePreservingSwapAtom_involutive,
      nonidentityExactCoreChange.atomEquiv.apply_symm_apply]]
  exact AtomFoundation.transportArchitectureObject_equiv_symm _ A

noncomputable def structurePreservingSwapUpper :
    SignedExactCoreReadingHom exactSourceCore exactTargetCore where
  atomEquiv := nonidentityExactCoreChange.atomEquiv
  extraction_eq := nonidentityExactCoreChange.extraction_eq
  composition_eq := nonidentityExactCoreChange.composition_eq
  objectMap := structurePreservingSwapObjectMap
  object_formation_eq := by intros; rfl
  configurationMap A :=
    AtomConfiguration.transportHom
      nonidentityExactCoreChange.atomEquiv A.configuration
  configurationMap_atomMap := by intros; rfl
  configuration_eq := by intros; rfl
  equationTransport := {
    contextEquivalence :=
      nonidentityExactCoreChange.equationTransport.contextEquivalence
    equationEquiv :=
      nonidentityExactCoreChange.equationTransport.equationEquiv
    role_eq := nonidentityExactCoreChange.equationTransport.role_eq
    observableEquiv :=
      nonidentityExactCoreChange.equationTransport.observableEquiv
    observable_naturality :=
      nonidentityExactCoreChange.equationTransport.observable_naturality
    violationCoordinate_eq :=
      nonidentityExactCoreChange.equationTransport.violationCoordinate_eq
    equationResidual_eq := by
      intro W A role atom
      simpa [structurePreservingSwapObjectMap,
        AtomFoundation.transportArchitectureObject,
        nonidentityExactCoreChange] using
        nonidentityExactCoreChange.equationTransport.equationResidual_eq
          W A role atom
  }
  detectorCode_eq := nonidentityExactCoreChange.detectorCode_eq
  operationMap := fun op =>
    AtomFoundation.transportConfigurationHom
      nonidentityExactCoreChange.atomEquiv op
  operation_naturality := by
    intro A B op
    apply ConfigurationHom.ext
    funext atom
    cases atom <;> rfl
  invariantMap := id
  invariant_transport := by
    intro i
    cases i
    · exact ⟨Equiv.refl PUnit, fun _ => rfl⟩
    · exact fun _ => Iff.rfl
  axisMap := id
  coordinateEquiv := fun _ => Equiv.refl Nat
  axis_selected_iff := by intro i; cases i; rfl
  coordinate_eq := by intro A i; cases i; rfl

/-- Named residual bridge used by the structure-preserving upper map. -/
theorem structurePreservingSwapUpper_equationResidual_transport
    (W : Site.ContextCategoryObject exactSourceCore.algebra.contextPreorder)
    (A : ArchitectureObject FiniteModel.carrier)
    (role : exactSourceCore.algebra.equationSystem.Index)
    (atom : FiniteModel.carrier.Atom) :
    structurePreservingSwapUpper.equationTransport.observableEquiv W
        (exactSourceCore.algebra.equationSystem.equationResidual W A role atom) =
      exactTargetCore.algebra.equationSystem.equationResidual
        (structurePreservingSwapUpper.equationTransport.contextForward W)
        (structurePreservingSwapObjectMap A)
        (structurePreservingSwapUpper.equationTransport.equationMap role)
        (nonidentityExactCoreChange.atomEquiv atom) :=
  structurePreservingSwapUpper.equationTransport.equationResidual_eq
    W A role atom

/-- The operation bridge is conjugation of configuration homomorphisms by the
same Atom involution. -/
theorem structurePreservingSwapUpper_operation_conjugation
    {A B : ArchitectureObject FiniteModel.carrier}
    (op : exactSourceCore.reading.operationReading.Op A B) :
    structurePreservingSwapUpper.operationMap op =
      AtomFoundation.transportConfigurationHom
        nonidentityExactCoreChange.atomEquiv op :=
  rfl

/-- Named operation-naturality bridge used by the upper constructor. -/
theorem structurePreservingSwapUpper_operation_naturality
    {A B : ArchitectureObject FiniteModel.carrier}
    (op : exactSourceCore.reading.operationReading.Op A B) :
    ConfigurationHom.comp
        (exactTargetCore.reading.operationReading.configurationMap
          (structurePreservingSwapUpper.operationMap op))
        (structurePreservingSwapUpper.configurationMap A) =
      ConfigurationHom.comp
        (structurePreservingSwapUpper.configurationMap B)
        (exactSourceCore.reading.operationReading.configurationMap op) :=
  structurePreservingSwapUpper.operation_naturality op

/-- Named invariant bridge used by the upper constructor. -/
theorem structurePreservingSwapUpper_invariant_transport
    (i : exactSourceCore.reading.invariantReading.Index) :
    Invariant.TransportedAlong
      (exactSourceCore.reading.invariantReading.invariant i)
      (exactTargetCore.reading.invariantReading.invariant
        (structurePreservingSwapUpper.invariantMap i))
      _root_.id structurePreservingSwapObjectMap :=
  structurePreservingSwapUpper.invariant_transport i

theorem structurePreservingSwapUpper_comp_self_atomEquiv :
    (structurePreservingSwapUpper.comp
        structurePreservingSwapUpper).atomEquiv =
      (SignedExactCoreReadingHom.refl exactSourceCore).atomEquiv := by
  apply Equiv.ext
  intro atom
  exact structurePreservingSwapAtom_involutive atom

theorem structurePreservingSwapUpper_comp_self_objectMap :
    (structurePreservingSwapUpper.comp
        structurePreservingSwapUpper).objectMap =
      (SignedExactCoreReadingHom.refl exactSourceCore).objectMap := by
  funext A
  exact structurePreservingSwapObjectMap_involutive A

/-- Dependent equation-transport cancellation for the full upper composite. -/
theorem structurePreservingSwapUpper_comp_self_equationTransport :
    HEq
      (structurePreservingSwapUpper.comp
        structurePreservingSwapUpper).equationTransport
      (SignedExactCoreReadingHom.refl exactSourceCore).equationTransport := by
  apply structurePreservingSwapEquationTransport_hext
    structurePreservingSwapUpper_comp_self_atomEquiv
    structurePreservingSwapUpper_comp_self_objectMap
  · rfl
  · apply Equiv.ext
    intro role
    cases role <;> rfl
  · rfl

/-- Dependent operation-map cancellation for the full upper composite. -/
theorem structurePreservingSwapUpper_comp_self_operationMap :
    HEq
      (@SignedExactCoreReadingHom.operationMap FiniteModel.carrier
        exactSourceCore exactTargetCore
        (structurePreservingSwapUpper.comp structurePreservingSwapUpper))
      (@SignedExactCoreReadingHom.operationMap FiniteModel.carrier
        exactSourceCore exactTargetCore
        (SignedExactCoreReadingHom.refl exactSourceCore)) := by
  apply Function.hfunext rfl
  intro A A' hA
  cases hA
  apply Function.hfunext rfl
  intro B B' hB
  cases hB
  apply Function.hfunext rfl
  intro op op' hop
  cases hop
  apply structurePreservingSwapConfigurationHom_hext
  · exact congrArg ArchitectureObject.configuration
      (congrFun structurePreservingSwapUpper_comp_self_objectMap A)
  · exact congrArg ArchitectureObject.configuration
      (congrFun structurePreservingSwapUpper_comp_self_objectMap B)
  · funext atom
    change nonidentityExactCoreChange.atomEquiv
        (nonidentityExactCoreChange.atomEquiv
          (op.atomMap
            (nonidentityExactCoreChange.atomEquiv
              (nonidentityExactCoreChange.atomEquiv atom)))) =
      op.atomMap atom
    rw [structurePreservingSwapAtom_involutive,
      structurePreservingSwapAtom_involutive]

theorem structurePreservingSwapUpper_comp_self :
    structurePreservingSwapUpper.comp
        structurePreservingSwapUpper =
      SignedExactCoreReadingHom.refl exactSourceCore := by
  apply SignedExactCoreReadingHom.ext
    structurePreservingSwapUpper_comp_self_atomEquiv
    structurePreservingSwapUpper_comp_self_objectMap
  · exact structurePreservingSwapUpper_comp_self_equationTransport
  · exact structurePreservingSwapUpper_comp_self_operationMap
  · rfl
  · rfl
  · rfl

noncomputable def structurePreservingSwapCoreHom :
    PackageTotalHom exactSourceCore exactTargetCore where
  base := NegativeGeometryWitness.coreHom.base
  upper := structurePreservingSwapUpper
  atomEquiv_eq := rfl

noncomputable def structurePreservingSwapExactUpperEquivalence :
    ExactUpperEquivalence exactSourceCore exactTargetCore where
  forward := structurePreservingSwapUpper
  backward := structurePreservingSwapUpper
  forward_backward := structurePreservingSwapUpper_comp_self
  backward_forward := structurePreservingSwapUpper_comp_self

theorem not_hGeom_structurePreservingSwap :
    ¬ Nonempty
      (HGeom NegativeGeometryWitness.package
        structurePreservingSwapCoreHom) := by
  rintro ⟨H⟩
  have hread := H.supportReads NegativeGeometryWitness.base PUnit.unit
    FiniteModel.FiniteAtom.componentA rfl
  change FiniteModel.FiniteAtom.componentB =
    FiniteModel.FiniteAtom.componentA at hread
  exact FiniteModel.FiniteAtom.noConfusion hread

theorem not_realizationExact_structurePreservingSwap :
    ¬ Nonempty
      (RealizationExactUpperEquivalence
        structurePreservingSwapExactUpperEquivalence) := by
  rintro ⟨H⟩
  apply not_hGeom_structurePreservingSwap
  exact ⟨RealizationExactUpperEquivalence.homHGeom
    (G := NegativeGeometryWitness.package) H
    structurePreservingSwapCoreHom rfl⟩

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
