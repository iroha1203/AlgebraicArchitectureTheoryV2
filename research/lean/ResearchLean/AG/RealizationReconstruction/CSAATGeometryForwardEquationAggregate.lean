import ResearchLean.AG.RealizationReconstruction.CSAATGeometryForwardGlobalFunctoriality
import ResearchLean.AG.RealizationReconstruction.CSAATGeometryForwardImage
import Formal.Util.AssertStandardAxioms

/-!
# Equation/raw aggregate laws for forward CS geometry

This file constructs identity and composition for the complete one-way
equation transport, then connects those laws and the transported raw-presheaf
laws to the canonical forward-image records.  Only the canonical constructors
from primitive lens/protocol morphisms are used.

Coverage is deliberately not included in these aggregate laws.  Its current
record is proposition-valued and indexed by the primitive morphism, so proof
irrelevance would not constitute a semantic coverage-composition theorem.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

namespace EndpointEquationForwardTransport

variable {U : AtomCarrier.{u}}

/-- Identity on every context object and induced thin arrow. -/
noncomputable def contextIdentityFunctor (object : ArchitectureObject U) :
    Site.ContextCategoryObject
        (Site.contextMorphismPreorderCategory object) ⥤
      Site.ContextCategoryObject
        (Site.contextMorphismPreorderCategory object) where
  obj W := W
  map h := h
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Identity equation transport, constructed on all computational fields. -/
noncomputable def identity {object : ArchitectureObject U}
    (equation : ArchitecturalEquationSystem
      (Site.contextMorphismPreorderCategory object)) :
    EndpointEquationForwardTransport equation equation where
  contextFunctor := contextIdentityFunctor object
  equationMap := id
  role_eq := fun _ => rfl
  observableHom := fun _ => RingHom.id _
  observable_naturality := by
    intro W V f observable
    rfl
  violationCoordinate_map := by
    intro W index atom
    rfl
  endpointResidual_zero_map := by
    intro W index atom h
    exact h

/-- Composition of equation transports, including sequential residual-zero
transport. -/
noncomputable def comp
    {sourceObject middleObject targetObject : ArchitectureObject U}
    {sourceEquation : ArchitecturalEquationSystem
      (Site.contextMorphismPreorderCategory sourceObject)}
    {middleEquation : ArchitecturalEquationSystem
      (Site.contextMorphismPreorderCategory middleObject)}
    {targetEquation : ArchitecturalEquationSystem
      (Site.contextMorphismPreorderCategory targetObject)}
    (T : EndpointEquationForwardTransport sourceEquation middleEquation)
    (S : EndpointEquationForwardTransport middleEquation targetEquation) :
    EndpointEquationForwardTransport sourceEquation targetEquation where
  contextFunctor := T.contextFunctor ⋙ S.contextFunctor
  equationMap := S.equationMap ∘ T.equationMap
  role_eq := by
    intro index
    exact (S.role_eq (T.equationMap index)).trans (T.role_eq index)
  observableHom := fun W =>
    (S.observableHom (T.contextFunctor.obj W)).comp (T.observableHom W)
  observable_naturality := by
    intro W V f observable
    change S.observableHom (T.contextFunctor.obj W)
        (T.observableHom W (sourceEquation.restrict f observable)) = _
    rw [T.observable_naturality]
    exact S.observable_naturality (T.contextFunctor.map f)
      (T.observableHom V observable)
  violationCoordinate_map := by
    intro W index atom
    change S.observableHom (T.contextFunctor.obj W)
        (T.observableHom W
          (sourceEquation.violationCoordinate W index atom)) = _
    rw [T.violationCoordinate_map]
    exact S.violationCoordinate_map (T.contextFunctor.obj W)
      (T.equationMap index) atom
  endpointResidual_zero_map := by
    intro W index atom h
    exact S.endpointResidual_zero_map (T.contextFunctor.obj W)
      (T.equationMap index) atom
      (T.endpointResidual_zero_map W index atom h)

/-- The context, index, and observable maps determine an equation transport;
all remaining fields are propositions. -/
theorem ext
    {sourceObject targetObject : ArchitectureObject U}
    {sourceEquation : ArchitecturalEquationSystem
      (Site.contextMorphismPreorderCategory sourceObject)}
    {targetEquation : ArchitecturalEquationSystem
      (Site.contextMorphismPreorderCategory targetObject)}
    (T S : EndpointEquationForwardTransport sourceEquation targetEquation)
    (hContext : T.contextFunctor = S.contextFunctor)
    (hEquation : T.equationMap = S.equationMap)
    (hObservable : HEq T.observableHom S.observableHom) : T = S := by
  cases T
  cases S
  cases hContext
  cases hEquation
  cases hObservable
  rfl

end EndpointEquationForwardTransport

namespace LensAATForwardMorphism

/-- The canonical lens equation transport at identity is the constructed
identity transport. -/
@[simp] theorem equationTransport_id {input : LensFamilyInput.{u}}
    (X : LensRealization input.View input.reference) :
    lensAATEndpointEquationForwardTransport input (id X) =
      EndpointEquationForwardTransport.identity
        (lensLawEquationSystem input X.Carrier X.toLensData.toLawStructure) := by
  apply EndpointEquationForwardTransport.ext
  · change (id X).lawContextFunctor =
      EndpointEquationForwardTransport.contextIdentityFunctor
        (lensLawObject input X.Carrier X.toLensData.toLawStructure)
    rw [lawContextFunctor_id]
    rfl
  · funext index
    rcases index with ⟨index⟩
    change ULift.up ((id X).lawIndexMap index) = ULift.up index
    exact congrArg ULift.up (lawIndexMap_id X index)
  · apply heq_of_eq
    funext W
    change (id X).lawCoordinateMap = RingHom.id _
    exact lawCoordinateMap_id X

/-- The canonical lens equation transport respects composition as a full
transport record. -/
@[simp] theorem equationTransport_comp {input : LensFamilyInput.{u}}
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) (g : LensAATForwardMorphism Y Z) :
    lensAATEndpointEquationForwardTransport input (comp f g) =
      EndpointEquationForwardTransport.comp
        (lensAATEndpointEquationForwardTransport input f)
        (lensAATEndpointEquationForwardTransport input g) := by
  apply EndpointEquationForwardTransport.ext
  · exact lawContextFunctor_comp f g
  · funext index
    rcases index with ⟨index⟩
    change ULift.up ((comp f g).lawIndexMap index) =
      ULift.up (g.lawIndexMap (f.lawIndexMap index))
    exact congrArg ULift.up (lawIndexMap_comp f g index)
  · apply heq_of_eq
    funext W
    change (comp f g).lawCoordinateMap =
      g.lawCoordinateMap.comp f.lawCoordinateMap
    exact lawCoordinateMap_comp f g

end LensAATForwardMorphism

namespace ProtocolAATForwardMorphism

/-- The canonical protocol equation transport at identity is the constructed
identity transport. -/
@[simp] theorem equationTransport_id {input : ProtocolFamilyInput.{u}}
    (X : ProtocolRealization input.schema input.observation) :
    protocolAATEndpointEquationForwardTransport input (id X) =
      EndpointEquationForwardTransport.identity
        (protocolLawEquationSystem input X.State X.toLawStructure) := by
  apply EndpointEquationForwardTransport.ext
  · change (id X).lawContextFunctor =
      EndpointEquationForwardTransport.contextIdentityFunctor
        (protocolLawObject input X.State X.toLawStructure)
    rw [lawContextFunctor_id]
    rfl
  · funext index
    rcases index with ⟨index⟩
    change ULift.up ((id X).lawIndexMap index) = ULift.up index
    exact congrArg ULift.up (lawIndexMap_id X index)
  · apply heq_of_eq
    funext W
    change (id X).lawCoordinateMap = RingHom.id _
    exact lawCoordinateMap_id X

/-- The canonical protocol equation transport respects composition as a full
transport record. -/
@[simp] theorem equationTransport_comp {input : ProtocolFamilyInput.{u}}
    {X Y Z : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y)
    (g : ProtocolAATForwardMorphism Y Z) :
    protocolAATEndpointEquationForwardTransport input (comp f g) =
      EndpointEquationForwardTransport.comp
        (protocolAATEndpointEquationForwardTransport input f)
        (protocolAATEndpointEquationForwardTransport input g) := by
  apply EndpointEquationForwardTransport.ext
  · exact lawContextFunctor_comp f g
  · funext index
    rcases index with ⟨index⟩
    change ULift.up ((comp f g).lawIndexMap index) =
      ULift.up (g.lawIndexMap (f.lawIndexMap index))
    exact congrArg ULift.up (lawIndexMap_comp f g index)
  · apply heq_of_eq
    funext W
    change (comp f g).lawCoordinateMap =
      g.lawCoordinateMap.comp f.lawCoordinateMap
    exact lawCoordinateMap_comp f g

end ProtocolAATForwardMorphism

/-! ## Canonical equation/raw aggregate laws

These records are outputs generated from a primitive morphism.  They do not
accept an arbitrary forward-image record or a coverage certificate.
-/

/-- The two substantive canonical lens aggregate equations at identity.
This proposition has no negative instance: the theorem below constructs it for
every realization from the primitive identity laws. -/
structure LensAATForwardEquationRawUnitLaw
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) : Prop where
  equation :
    (lensAATForwardGeometryImage input (LensAATForwardMorphism.id X)).equation =
      EndpointEquationForwardTransport.identity
        (lensLawEquationSystem input X.Carrier X.toLensData.toLawStructure)
  raw :
    (lensAATForwardGeometryImage input (LensAATForwardMorphism.id X)).raw ≫
        eqToHom (LensAATForwardMorphism.rawTarget_id X) =
      𝟙 (lensAATGeometryReadingRawSystem input X).toPresheaf

/-- The two substantive canonical lens aggregate equations for composition.
This proposition has no negative instance: the theorem below constructs it for
every composable pair from the primitive compositor laws. -/
structure LensAATForwardEquationRawCompLaw
    (input : LensFamilyInput.{u})
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) (g : LensAATForwardMorphism Y Z) : Prop where
  equation :
    (lensAATForwardGeometryImage input (LensAATForwardMorphism.comp f g)).equation =
      EndpointEquationForwardTransport.comp
        (lensAATForwardGeometryImage input f).equation
        (lensAATForwardGeometryImage input g).equation
  raw :
    (lensAATForwardGeometryImage input (LensAATForwardMorphism.comp f g)).raw ≫
        eqToHom (LensAATForwardMorphism.rawTarget_comp f g) =
      (lensAATForwardGeometryImage input f).raw ≫
        Functor.whiskerLeft f.lawContextFunctor.op
          (lensAATForwardGeometryImage input g).raw

/-- Canonical lens equation/raw unit law, generated from primitive identity. -/
theorem lensAATForwardEquationRawUnitLaw
    (input : LensFamilyInput.{u})
    (X : LensRealization input.View input.reference) :
    LensAATForwardEquationRawUnitLaw input X where
  equation := LensAATForwardMorphism.equationTransport_id X
  raw := LensAATForwardMorphism.rawForwardHom_id X

/-- Canonical lens equation/raw compositor law. -/
theorem lensAATForwardEquationRawCompLaw
    (input : LensFamilyInput.{u})
    {X Y Z : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) (g : LensAATForwardMorphism Y Z) :
    LensAATForwardEquationRawCompLaw input f g where
  equation := LensAATForwardMorphism.equationTransport_comp f g
  raw := LensAATForwardMorphism.rawForwardHom_comp f g

/-- The two substantive canonical protocol aggregate equations at identity.
This proposition has no negative instance: the theorem below constructs it for
every realization from the primitive identity laws. -/
structure ProtocolAATForwardEquationRawUnitLaw
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) : Prop where
  equation :
    (protocolAATForwardGeometryImage input
      (ProtocolAATForwardMorphism.id X)).equation =
      EndpointEquationForwardTransport.identity
        (protocolLawEquationSystem input X.State X.toLawStructure)
  raw :
    (protocolAATForwardGeometryImage input
      (ProtocolAATForwardMorphism.id X)).raw ≫
        eqToHom (ProtocolAATForwardMorphism.rawTarget_id X) =
      𝟙 (protocolAATGeometryReadingRawSystem input X).toPresheaf

/-- The two substantive canonical protocol aggregate equations for composition.
This proposition has no negative instance: the theorem below constructs it for
every composable pair from the primitive compositor laws. -/
structure ProtocolAATForwardEquationRawCompLaw
    (input : ProtocolFamilyInput.{u})
    {X Y Z : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y)
    (g : ProtocolAATForwardMorphism Y Z) : Prop where
  equation :
    (protocolAATForwardGeometryImage input
      (ProtocolAATForwardMorphism.comp f g)).equation =
      EndpointEquationForwardTransport.comp
        (protocolAATForwardGeometryImage input f).equation
        (protocolAATForwardGeometryImage input g).equation
  raw :
    (protocolAATForwardGeometryImage input
      (ProtocolAATForwardMorphism.comp f g)).raw ≫
        eqToHom (ProtocolAATForwardMorphism.rawTarget_comp f g) =
      (protocolAATForwardGeometryImage input f).raw ≫
        Functor.whiskerLeft f.lawContextFunctor.op
          (protocolAATForwardGeometryImage input g).raw

/-- Canonical protocol equation/raw unit law. -/
theorem protocolAATForwardEquationRawUnitLaw
    (input : ProtocolFamilyInput.{u})
    (X : ProtocolRealization input.schema input.observation) :
    ProtocolAATForwardEquationRawUnitLaw input X where
  equation := ProtocolAATForwardMorphism.equationTransport_id X
  raw := ProtocolAATForwardMorphism.rawForwardHom_id X

/-- Canonical protocol equation/raw compositor law. -/
theorem protocolAATForwardEquationRawCompLaw
    (input : ProtocolFamilyInput.{u})
    {X Y Z : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y)
    (g : ProtocolAATForwardMorphism Y Z) :
    ProtocolAATForwardEquationRawCompLaw input f g where
  equation := ProtocolAATForwardMorphism.equationTransport_comp f g
  raw := ProtocolAATForwardMorphism.rawForwardHom_comp f g

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
