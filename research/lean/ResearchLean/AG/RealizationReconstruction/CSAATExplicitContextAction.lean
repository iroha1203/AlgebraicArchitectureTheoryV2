import ResearchLean.AG.RealizationReconstruction.CSAATGeneratedContextCarrierEquiv
import Formal.Util.AssertStandardAxioms

/-!
# Representation-preserving context action for the genuine CS transports

The thin context category remembers only that a readable restriction exists.
This file retains the actual `ContextMorphism` before that data is forgotten.
Full-family rebasing then gives genuine equivalences on all three local
carriers, exact reading iff statements, and all three naturality laws by
construction.

The existing `RealizationTransportSupply` observes a freshly selected target
representative instead.  The final section isolates the additional coherence
statement that would be needed to convert this explicit action to that API; it
is not accepted as an input to any constructor here.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory

universe u

/-- An action on full contexts and actual restriction morphisms.  Naturality
is stated against the retained morphism data, not a representative re-selected
from a proposition-valued thin arrow. -/
structure ExplicitFullFamilyContextAction {U : AtomCarrier.{u}}
    (sourceObject targetObject : ArchitectureObject U) where
  contextObj : Site.ArchitectureContext sourceObject →
    Site.ArchitectureContext targetObject
  contextMorphism : ∀ {W V : Site.ArchitectureContext sourceObject},
    Site.ContextMorphism W V →
      Site.ContextMorphism (contextObj W) (contextObj V)
  contextMorphism_isRestriction : ∀ {W V : Site.ArchitectureContext sourceObject}
      (f : Site.ContextMorphism W V), f.IsRestriction →
        (contextMorphism f).IsRestriction
  supportEquiv : ∀ W, W.Support ≃ (contextObj W).Support
  axisEquiv : ∀ W, W.Axis ≃ (contextObj W).Axis
  observableEquiv : ∀ W, W.Observable ≃ (contextObj W).Observable
  supportReads_iff : ∀ W support atom,
    W.minimal.supportReads support atom ↔
      (contextObj W).minimal.supportReads (supportEquiv W support) atom
  axisReads_iff : ∀ W axis,
    W.minimal.axisReads axis ↔
      (contextObj W).minimal.axisReads (axisEquiv W axis)
  observableReads_iff : ∀ W observable,
    W.minimal.observableReads observable ↔
      (contextObj W).minimal.observableReads (observableEquiv W observable)
  support_naturality : ∀ {W V} (f : Site.ContextMorphism W V) support,
    (contextMorphism f).supportMap (supportEquiv W support) =
      supportEquiv V (f.supportMap support)
  axis_naturality : ∀ {W V} (f : Site.ContextMorphism W V) axis,
    (contextMorphism f).axisMap (axisEquiv W axis) =
      axisEquiv V (f.axisMap axis)
  observable_naturality : ∀ {W V} (f : Site.ContextMorphism W V) observable,
    (contextMorphism f).observableRestrict (observableEquiv V observable) =
      observableEquiv W (f.observableRestrict observable)

/-- Full-family rebasing constructs the complete explicit action.  No carrier
map, context action, reading law, or naturality certificate is supplied. -/
def explicitFullFamilyContextAction {U : AtomCarrier.{u}}
    (sourceObject targetObject : ArchitectureObject U)
    (target_all : ∀ atom, targetObject.configuration.family.mem atom) :
    ExplicitFullFamilyContextAction sourceObject targetObject where
  contextObj := fullFamilyContextRebase targetObject target_all
  contextMorphism := fullFamilyContextMorphismRebase targetObject target_all
  contextMorphism_isRestriction :=
    fullFamilyContextMorphismRebase_isRestriction targetObject target_all
  supportEquiv _ := Equiv.refl _
  axisEquiv _ := Equiv.refl _
  observableEquiv _ := Equiv.refl _
  supportReads_iff _ _ _ := Iff.rfl
  axisReads_iff _ _ := Iff.rfl
  observableReads_iff _ _ := Iff.rfl
  support_naturality _ _ := rfl
  axis_naturality _ _ := rfl
  observable_naturality _ _ := rfl

/-- The genuine lens isomorphism endpoints receive the explicit context
action used by their full-family context functor. -/
def lensIsoEndpointExplicitContextAction
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (_e : X ≅ Y) :
    ExplicitFullFamilyContextAction
      (lensLawObject input X.Carrier X.toLensData.toLawStructure)
      (lensLawObject input Y.Carrier Y.toLensData.toLawStructure) :=
  explicitFullFamilyContextAction _ _ (fun _ => trivial)

/-- The genuine protocol isomorphism endpoints receive the explicit context
action used by their full-family context functor. -/
def protocolIsoEndpointExplicitContextAction
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (_e : X ≅ Y) :
    ExplicitFullFamilyContextAction
      (protocolLawObject input X.State X.toLawStructure)
      (protocolLawObject input Y.State Y.toLawStructure) :=
  explicitFullFamilyContextAction _ _ (fun _ => trivial)

/-- Transport an explicit context action through source and target object
provenance equalities. -/
def explicitFullFamilyContextActionCast {U : AtomCarrier.{u}}
    {sourceGenerated sourceEndpoint targetGenerated targetEndpoint :
      ArchitectureObject U}
    (source_eq : sourceGenerated = sourceEndpoint)
    (target_eq : targetGenerated = targetEndpoint)
    (action : ExplicitFullFamilyContextAction sourceEndpoint targetEndpoint) :
    ExplicitFullFamilyContextAction sourceGenerated targetGenerated := by
  cases source_eq
  cases target_eq
  exact action

/-- The action on the actual generated lens core, obtained only from its two
proved object-provenance equalities and the endpoint construction. -/
noncomputable def lensIsoGeneratedExplicitContextAction
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    ExplicitFullFamilyContextAction
      (lensAATCorePackage input X).object
      (lensAATCorePackage input Y).object :=
  explicitFullFamilyContextActionCast
    (lensAATCorePackage_object_eq input X)
    (lensAATCorePackage_object_eq input Y)
    (lensIsoEndpointExplicitContextAction e)

/-- The action on the actual generated protocol core, obtained only from its
two proved object-provenance equalities and the endpoint construction. -/
noncomputable def protocolIsoGeneratedExplicitContextAction
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    ExplicitFullFamilyContextAction
      (protocolAATCorePackage input X).object
      (protocolAATCorePackage input Y).object :=
  explicitFullFamilyContextActionCast
    (protocolAATCorePackage_object_eq input X)
    (protocolAATCorePackage_object_eq input Y)
    (protocolIsoEndpointExplicitContextAction e)

/-! ## Boundary with the current thin representative API -/

/-- A full-family context whose readable predicates allow two different
restriction representatives on the same source and target. -/
def representativeNonuniqueContext {U : AtomCarrier.{u}}
    (object : ArchitectureObject U)
    (object_all : ∀ atom, object.configuration.family.mem atom) :
    Site.ArchitectureContext object where
  minimal := {
    Support := ULift.{u, 0} Bool
    Axis := ULift.{u, 0} PUnit
    Observable := ULift.{u, 0} PUnit
    supportReads := fun _ _ => True
    supportReads_objectFamily := fun _ => object_all _
    axisReads := fun _ => True
    observableReads := fun _ => True }
  Extension := ULift.{u, 0} PUnit
  extension := ULift.up PUnit.unit

/-- Identity is a restriction representative of the nonunique context. -/
def representativeIdentityRestriction {U : AtomCarrier.{u}}
    {object : ArchitectureObject U}
    {object_all : ∀ atom, object.configuration.family.mem atom} :
    Site.ContextMorphism
      (representativeNonuniqueContext object object_all)
      (representativeNonuniqueContext object object_all) where
  supportMap := id
  axisMap := id
  observableRestrict := id

/-- Boolean negation gives a second restriction representative with the same
endpoints. -/
def representativeFlipRestriction {U : AtomCarrier.{u}}
    {object : ArchitectureObject U}
    {object_all : ∀ atom, object.configuration.family.mem atom} :
    Site.ContextMorphism
      (representativeNonuniqueContext object object_all)
      (representativeNonuniqueContext object object_all) where
  supportMap := fun value => ULift.up (Bool.not value.down)
  axisMap := id
  observableRestrict := id

theorem representativeIdentityRestriction_isRestriction {U : AtomCarrier.{u}}
    {object : ArchitectureObject U}
    {object_all : ∀ atom, object.configuration.family.mem atom} :
    (@representativeIdentityRestriction U object object_all).IsRestriction := by
  exact ⟨fun _ => trivial, fun _ => trivial, fun _ => trivial,
    fun {_ atom} _ => object_all atom⟩

theorem representativeFlipRestriction_isRestriction {U : AtomCarrier.{u}}
    {object : ArchitectureObject U}
    {object_all : ∀ atom, object.configuration.family.mem atom} :
    (@representativeFlipRestriction U object object_all).IsRestriction := by
  exact ⟨fun _ => trivial, fun _ => trivial, fun _ => trivial,
    fun {_ atom} _ => object_all atom⟩

/-- Restriction representatives with fixed endpoints are not unique under the
current contract. -/
theorem restrictionRepresentative_not_unique {U : AtomCarrier.{u}}
    {object : ArchitectureObject U}
    {object_all : ∀ atom, object.configuration.family.mem atom} :
    (@representativeIdentityRestriction U object object_all).supportMap ≠
      (@representativeFlipRestriction U object object_all).supportMap := by
  intro h
  have hfalse := congrFun h (ULift.up false)
  have hdown := congrArg ULift.down hfalse
  simp [representativeIdentityRestriction, representativeFlipRestriction] at hdown

/-- The representative re-selected by the target thin preorder. -/
noncomputable def targetChosenMorphism {U : AtomCarrier.{u}}
    {sourceObject targetObject : ArchitectureObject U}
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    {W V : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory sourceObject)} (w : W ⟶ V) :
    Site.ContextMorphism
      ((fullFamilyContextFunctor sourceObject targetObject target_all).obj W).ctx
      ((fullFamilyContextFunctor sourceObject targetObject target_all).obj V).ctx :=
  (Site.contextMorphismPreorderCategory targetObject).morphism
    (leOfHom ((fullFamilyContextFunctor sourceObject targetObject target_all).map w))

/-- The actual source representative, explicitly rebased to the target. -/
noncomputable def explicitlyRebasedChosenMorphism {U : AtomCarrier.{u}}
    {sourceObject targetObject : ArchitectureObject U}
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    {W V : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory sourceObject)} (w : W ⟶ V) :
    Site.ContextMorphism
      ((fullFamilyContextFunctor sourceObject targetObject target_all).obj W).ctx
      ((fullFamilyContextFunctor sourceObject targetObject target_all).obj V).ctx :=
  fullFamilyContextMorphismRebase targetObject target_all
    ((Site.contextMorphismPreorderCategory sourceObject).morphism (leOfHom w))

/-- The explicit representative is a genuine witness of the target-side thin
relation. -/
noncomputable def explicitlyRebasedRelationProof {U : AtomCarrier.{u}}
    {sourceObject targetObject : ArchitectureObject U}
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    {W V : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory sourceObject)} (w : W ⟶ V) :
    (Site.contextMorphismPreorderCategory targetObject).le
      ((fullFamilyContextFunctor sourceObject targetObject target_all).obj W).ctx
      ((fullFamilyContextFunctor sourceObject targetObject target_all).obj V).ctx :=
  ⟨explicitlyRebasedChosenMorphism target_all w,
    fullFamilyContextMorphismRebase_isRestriction targetObject target_all _
      ((Site.contextMorphismPreorderCategory sourceObject).morphism_isRestriction
        (leOfHom w))⟩

/-- Forgetting the explicit representative yields exactly the same thin arrow
as the existing full-family context functor. -/
theorem explicitlyRebasedHom_eq_fullFamilyMap {U : AtomCarrier.{u}}
    {sourceObject targetObject : ArchitectureObject U}
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    {W V : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory sourceObject)} (w : W ⟶ V) :
    homOfLE (explicitlyRebasedRelationProof target_all w) =
      (fullFamilyContextFunctor sourceObject targetObject target_all).map w :=
  Subsingleton.elim _ _

/-- Proof irrelevance identifies the existential proofs passed to choice, but
does not identify the chosen value with the displayed witness. -/
theorem targetChosen_eq_chooseExplicitProof {U : AtomCarrier.{u}}
    {sourceObject targetObject : ArchitectureObject U}
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    {W V : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory sourceObject)} (w : W ⟶ V) :
    targetChosenMorphism target_all w =
      Classical.choose (explicitlyRebasedRelationProof target_all w) := by
  apply congrArg Classical.choose
  exact Subsingleton.elim _ _

/-- The exact additional statement needed to make the old API observe the
retained representative.  This proposition is diagnosed, not assumed by any
constructor in this file. -/
def ChosenRepresentativeCoherence {U : AtomCarrier.{u}}
    {sourceObject targetObject : ArchitectureObject U}
    (target_all : ∀ atom, targetObject.configuration.family.mem atom) : Prop :=
  ∀ {W V : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory sourceObject)} (w : W ⟶ V),
    targetChosenMorphism target_all w = explicitlyRebasedChosenMorphism target_all w

/-- Chosen-representative coherence would imply exactly the three naturality
equations requested by the current supply API. -/
theorem supplyNaturality_of_chosenRepresentativeCoherence
    {U : AtomCarrier.{u}} {sourceObject targetObject : ArchitectureObject U}
    (target_all : ∀ atom, targetObject.configuration.family.mem atom)
    (h : @ChosenRepresentativeCoherence U sourceObject targetObject target_all)
    {W V : Site.ContextCategoryObject
      (Site.contextMorphismPreorderCategory sourceObject)} (w : W ⟶ V) :
    (∀ support,
      (targetChosenMorphism target_all w).supportMap support =
        ((Site.contextMorphismPreorderCategory sourceObject).morphism
          (leOfHom w)).supportMap support) ∧
    (∀ axis,
      (targetChosenMorphism target_all w).axisMap axis =
        ((Site.contextMorphismPreorderCategory sourceObject).morphism
          (leOfHom w)).axisMap axis) ∧
    (∀ observable,
      (targetChosenMorphism target_all w).observableRestrict observable =
        ((Site.contextMorphismPreorderCategory sourceObject).morphism
          (leOfHom w)).observableRestrict observable) := by
  rw [h w]
  exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
