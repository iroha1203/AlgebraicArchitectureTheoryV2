import ResearchLean.AG.RealizationReconstruction.CSAATGeometryRawNaturality
import ResearchLean.AG.RealizationReconstruction.CSAATForwardMorphisms
import Formal.Util.AssertStandardAxioms

/-!
# One-way equation-system transport for the concrete CS readings

The exact geometry API requires equivalences of equation indices, contexts,
and observable rings.  Those hypotheses exclude the noninjective lens and
protocol morphisms required by G-123(E).  This file isolates the genuinely
covariant equation layer instead.

An `EndpointEquationForwardTransport` maps every source context and selected
restriction, every equation index, and every observable-ring element.  It
records naturality and the images of all violation generators, and it derives
preservation of residual vanishing at the two independently constructed
endpoints.  It contains no inverse, target-surjectivity, coverage witness,
completed geometry morphism, or prepackaged lawfulness certificate.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory
open Opposite

universe u

/-- Primitive one-way transport between the equation systems at two fixed
geometry endpoints.  Residual preservation is deliberately stated only for
the mapped source index; target equations outside the image remain independent
target obligations. -/
structure EndpointEquationForwardTransport {U : AtomCarrier.{u}}
    {sourceObject targetObject : ArchitectureObject U}
    (sourceEquation : ArchitecturalEquationSystem
      (Site.contextMorphismPreorderCategory sourceObject))
    (targetEquation : ArchitecturalEquationSystem
      (Site.contextMorphismPreorderCategory targetObject)) where
  contextFunctor :
    Site.ContextCategoryObject
        (Site.contextMorphismPreorderCategory sourceObject) ⥤
      Site.ContextCategoryObject
        (Site.contextMorphismPreorderCategory targetObject)
  equationMap : sourceEquation.Index → targetEquation.Index
  role_eq : ∀ index,
    targetEquation.role (equationMap index) = sourceEquation.role index
  observableHom : ∀ W,
    sourceEquation.Observable W →+*
      targetEquation.Observable (contextFunctor.obj W)
  observable_naturality :
    ∀ {W V} (f : W ⟶ V) (observable : sourceEquation.Observable V),
      observableHom W (sourceEquation.restrict f observable) =
        targetEquation.restrict (contextFunctor.map f)
          (observableHom V observable)
  violationCoordinate_map :
    ∀ W index atom,
      observableHom W
          (sourceEquation.violationCoordinate W index atom) =
        targetEquation.violationCoordinate (contextFunctor.obj W)
          (equationMap index) atom
  endpointResidual_zero_map :
    ∀ W index atom,
      sourceEquation.equationResidual W sourceObject index atom = 0 →
        targetEquation.equationResidual (contextFunctor.obj W)
          targetObject (equationMap index) atom = 0

namespace EndpointEquationForwardTransport

variable {U : AtomCarrier.{u}}
variable {sourceObject targetObject : ArchitectureObject U}
variable {sourceEquation : ArchitecturalEquationSystem
  (Site.contextMorphismPreorderCategory sourceObject)}
variable {targetEquation : ArchitecturalEquationSystem
  (Site.contextMorphismPreorderCategory targetObject)}

/-- The contextwise observable maps form an actual natural transformation of
the complete observable presheaves. -/
noncomputable def observablePresheafHom
    (T : EndpointEquationForwardTransport sourceEquation targetEquation) :
    sourceEquation.observablePresheaf ⟶
      T.contextFunctor.op ⋙ targetEquation.observablePresheaf where
  app W := CommRingCat.ofHom (T.observableHom W.unop)
  naturality := by
    intro W V f
    apply CommRingCat.hom_ext
    ext observable
    exact T.observable_naturality f.unop observable

/-- Required source equations remain required after applying the generated
index map. -/
theorem required_map
    (T : EndpointEquationForwardTransport sourceEquation targetEquation)
    {index : sourceEquation.Index} (h : sourceEquation.Required index) :
    targetEquation.Required (T.equationMap index) := by
  unfold ArchitecturalEquationSystem.Required at h ⊢
  rw [T.role_eq]
  exact h

/-- Vanishing of a source endpoint equation is preserved at every mapped
context, index, and Atom. -/
theorem equationHolds_map
    (T : EndpointEquationForwardTransport sourceEquation targetEquation)
    {index : sourceEquation.Index}
    (h : sourceEquation.EquationHolds index sourceObject) :
    ∀ (W : Site.ContextCategoryObject
        (Site.contextMorphismPreorderCategory sourceObject)) (atom : U.Atom),
      targetEquation.equationResidual (T.contextFunctor.obj W)
        targetObject (T.equationMap index) atom = 0 := by
  intro W atom
  exact T.endpointResidual_zero_map W index atom (h W atom)

end EndpointEquationForwardTransport

/-! ## Raw Law constructors and CS specializations -/

/-- One-way equation transport for arbitrary raw lens Law structures.  The
context rebase depends only on the two endpoint objects; the index, observable,
generator, and residual components use the supplied raw Law morphism.  No
lawfulness of either endpoint is assumed. -/
noncomputable def lensLawEndpointEquationForwardTransport
    (input : LensFamilyInput.{u})
    {Source Target : Type u}
    {source : LensLawStructure input.View Source}
    {target : LensLawStructure input.View Target}
    (f : LensLawHom source target) :
    EndpointEquationForwardTransport
      (lensLawEquationSystem input Source source)
      (lensLawEquationSystem input Target target) where
  contextFunctor := lensLawContextFunctor f
  equationMap := fun index => ULift.up (lensLawIndexMap f index.down)
  role_eq := by
    intro index
    rfl
  observableHom := fun _ => lensLawCoordinateMap input f
  observable_naturality := by
    intro W V contextMap observable
    exact lensLawCoordinateMap_restrict input f contextMap observable
  violationCoordinate_map := by
    intro W index atom
    rcases index with ⟨index⟩
    exact lensLawViolationCoordinate_map input f W index atom
  endpointResidual_zero_map := by
    intro W index atom hzero
    rcases index with ⟨index⟩
    exact lensLawResidual_zero_map_contextFunctor input f W index atom hzero

/-- One-way equation transport for arbitrary raw protocol Law structures.
The context carrier rebase is endpoint-only, while all equation-semantic
components use the complete raw protocol Law morphism. -/
noncomputable def protocolLawEndpointEquationForwardTransport
    (input : ProtocolFamilyInput.{u})
    {Source Target : input.schema.Vertex → Type u}
    {source : ProtocolLawStructure input Source}
    {target : ProtocolLawStructure input Target}
    (f : ProtocolLawHom source target) :
    EndpointEquationForwardTransport
      (protocolLawEquationSystem input Source source)
      (protocolLawEquationSystem input Target target) where
  contextFunctor := protocolLawContextFunctor f
  equationMap := fun index => ULift.up (protocolLawIndexMap f index.down)
  role_eq := by
    intro index
    rfl
  observableHom := fun _ => protocolLawCoordinateMap input f
  observable_naturality := by
    intro W V contextMap observable
    exact protocolLawCoordinateMap_restrict input f contextMap observable
  violationCoordinate_map := by
    intro W index atom
    rcases index with ⟨index⟩
    exact protocolLawViolationCoordinate_map input f W index atom
  endpointResidual_zero_map := by
    intro W index atom hzero
    rcases index with ⟨index⟩
    exact protocolLawResidual_zero_map_contextFunctor input f W index atom hzero

/-- The complete lens Law equation layer is transported from the primitive
get/put-preserving morphism.  No transport field is accepted as input. -/
noncomputable def lensAATEndpointEquationForwardTransport
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :
    EndpointEquationForwardTransport
      (lensLawEquationSystem input X.Carrier X.toLensData.toLawStructure)
      (lensLawEquationSystem input Y.Carrier Y.toLensData.toLawStructure) :=
  lensLawEndpointEquationForwardTransport input f.lawHom

/-- The complete protocol relation/observation equation layer is transported
from every edge and observation square of the primitive protocol morphism. -/
noncomputable def protocolAATEndpointEquationForwardTransport
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) :
    EndpointEquationForwardTransport
      (protocolLawEquationSystem input X.State X.toLawStructure)
      (protocolLawEquationSystem input Y.State Y.toLawStructure) :=
  protocolLawEndpointEquationForwardTransport input f.lawHom

/-- Lens observable transport as a natural transformation on every context and
selected restriction. -/
noncomputable def lensAATEquationObservablePresheafHom
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y) :=
  (lensAATEndpointEquationForwardTransport input f).observablePresheafHom

/-- Protocol observable transport as a natural transformation on every
context and selected restriction. -/
noncomputable def protocolAATEquationObservablePresheafHom
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y) :=
  (protocolAATEndpointEquationForwardTransport input f).observablePresheafHom

/-- Lens residual vanishing for every source Law index is an immediate output
of the fixed-endpoint equation transport. -/
theorem lensAATEndpointEquationHolds_map
    (input : LensFamilyInput.{u})
    {X Y : LensRealization input.View input.reference}
    (f : LensAATForwardMorphism X Y)
    (index : LensLawIndex input.View X.Carrier)
    (h : (lensLawEquationSystem input X.Carrier
      X.toLensData.toLawStructure).EquationHolds (ULift.up index)
        (lensLawObject input X.Carrier X.toLensData.toLawStructure)) :
    ∀ W atom,
      (lensLawEquationSystem input Y.Carrier
        Y.toLensData.toLawStructure).equationResidual
          ((f.lawContextFunctor).obj W)
          (lensLawObject input Y.Carrier Y.toLensData.toLawStructure)
          (ULift.up (f.lawIndexMap index)) atom = 0 :=
  (lensAATEndpointEquationForwardTransport input f).equationHolds_map h

/-- Protocol residual vanishing for every source Law index is likewise
preserved without adding injectivity or surjectivity. -/
theorem protocolAATEndpointEquationHolds_map
    (input : ProtocolFamilyInput.{u})
    {X Y : ProtocolRealization input.schema input.observation}
    (f : ProtocolAATForwardMorphism X Y)
    (index : ProtocolLawIndex X.State)
    (h : (protocolLawEquationSystem input X.State
      X.toLawStructure).EquationHolds (ULift.up index)
        (protocolLawObject input X.State X.toLawStructure)) :
    ∀ W atom,
      (protocolLawEquationSystem input Y.State
        Y.toLawStructure).equationResidual
          ((f.lawContextFunctor).obj W)
          (protocolLawObject input Y.State Y.toLawStructure)
          (ULift.up (f.lawIndexMap index)) atom = 0 :=
  (protocolAATEndpointEquationForwardTransport input f).equationHolds_map h

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
