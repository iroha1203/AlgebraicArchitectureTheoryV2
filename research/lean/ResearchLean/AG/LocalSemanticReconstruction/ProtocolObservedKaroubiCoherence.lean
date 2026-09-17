import ResearchLean.AG.LocalSemanticReconstruction.ProtocolObservedRestrictionEquivalence
import ResearchLean.AG.RealizationReconstruction.CSKaroubiReconstruction
import Formal.Util.AssertStandardAxioms

/-!
# Protocol observed-restriction and Karoubi coherence

The protocol fiber of the closed realization category is explicitly equivalent
to the independently defined protocol semantic category.  Composing that
equivalence with the observation-aware restriction equivalence identifies the
accepted finite presentation decoder and Karoubi reconstruction with their
observed local readings.

The finite-table computation rules below apply to decoder objects and maps.
The restriction, retract, and arrow equivalences retain all observation-
compatible semantic morphisms, including noninvertible ones.  This module does
not assert the common `FiniteReading` effectiveness conditions or a computable
extension procedure.
-/

namespace AAT.AG.LocalSemanticReconstruction

open CategoryTheory
open CategoryTheory.Idempotents
open AAT.AG.RealizationReconstruction

universe u

/-- Insert an independently defined protocol realization into the protocol
fiber of the closed realization category. -/
def protocolSemanticClosedFamilyFunctor (input : ProtocolFamilyInput.{u}) :
    ProtocolRealization input.schema input.observation ⥤
      FamilyRealization.{u, u} (.protocol input) where
  obj X := FamilyRealization.protocol X
  map f := closedFamilyProtocolHom f
  map_id X := by
    apply ULift.ext
    apply ProtocolAATIndependentGeneratedPackageHom.ext
    funext vertex state
    rfl
  map_comp f g := by
    apply ULift.ext
    apply ProtocolAATIndependentGeneratedPackageHom.ext
    funext vertex state
    rfl

/-- Eliminate the protocol constructor and read a closed-family morphism back
as its complete semantic natural transformation. -/
def protocolClosedFamilySemanticFunctor (input : ProtocolFamilyInput.{u}) :
    FamilyRealization.{u, u} (.protocol input) ⥤
      ProtocolRealization input.schema input.observation where
  obj X := by
    cases X with
    | protocol realization => exact realization
  map {X Y} f := by
    cases X with
    | protocol source =>
      cases Y with
      | protocol target => exact f.down.toSemanticHom
  map_id X := by
    cases X with
    | protocol realization =>
      apply ProtocolRealization.Hom.ext
      ext q state
      rfl
  map_comp {X Y Z} f g := by
    cases X with
    | protocol source =>
      cases Y with
      | protocol middle =>
        cases Z with
        | protocol target =>
          apply ProtocolRealization.Hom.ext
          ext q state
          rfl

/-- The semantic protocol category and its closed-family fiber are equivalent
by the accepted package/semantic round trips. -/
noncomputable def protocolSemanticClosedFamilyEquivalence
    (input : ProtocolFamilyInput.{u}) :
    ProtocolRealization input.schema input.observation ≌
      FamilyRealization.{u, u} (.protocol input) :=
  CategoryTheory.Equivalence.mk
    (protocolSemanticClosedFamilyFunctor input)
    (protocolClosedFamilySemanticFunctor input)
    (NatIso.ofComponents (fun X => Iso.refl X) (by
      intro X Y f
      simpa [protocolSemanticClosedFamilyFunctor,
        protocolClosedFamilySemanticFunctor, closedFamilyProtocolHom] using
        ProtocolAATIndependentGeneratedPackageHom.toSemanticHom_ofSemanticHom f))
    (NatIso.ofComponents (fun X => by
      cases X with
      | protocol realization => exact Iso.refl _ ) (by
      intro X Y f
      cases X with
      | protocol source =>
        cases Y with
        | protocol target =>
          apply ULift.ext
          simpa [protocolSemanticClosedFamilyFunctor,
            protocolClosedFamilySemanticFunctor, closedFamilyProtocolHom] using
            ProtocolAATIndependentGeneratedPackageHom.ofSemanticHom_toSemanticHom
              f.down))

/-- The semantic protocol category is equivalent to the complete observed
finite-restriction category, using the accepted closed-family reading as the
second leg. -/
noncomputable def protocolSemanticObservedRestrictionEquivalence
    (input : ProtocolFamilyInput.{u}) :
    ProtocolRealization input.schema input.observation ≌
      ProtocolObservedRestrictionModel input :=
  (protocolSemanticClosedFamilyEquivalence input).trans
    (protocolObservedRestrictionEquivalence input)

/-- The forward functor is exactly insertion into the closed protocol fiber
followed by the accepted primitive observed-restriction reading. -/
@[simp] theorem protocolSemanticObservedRestrictionEquivalence_functor
    (input : ProtocolFamilyInput.{u}) :
    (protocolSemanticObservedRestrictionEquivalence input).functor =
      protocolSemanticClosedFamilyFunctor input ⋙
        protocolObservedRestrictionReading input :=
  rfl

/-- Decode finite generator tables and immediately read the resulting semantic
protocol as an observed finite restriction model. -/
noncomputable def protocolObservedFiniteDecoder
    (input : ProtocolFamilyInput.{u}) :
    ProtocolPresentation input.schema input.observation ⥤
      ProtocolObservedRestrictionModel input :=
  ProtocolPresentation.decoder input.schema input.observation ⋙
    (protocolSemanticObservedRestrictionEquivalence input).functor

/-- At a named vertex, the observed decoder has exactly the decoder's finite
state carrier. -/
@[simp] theorem protocolObservedFiniteDecoder_obj_vertex
    (input : ProtocolFamilyInput.{u})
    (P : ProtocolPresentation input.schema input.observation)
    (vertex : input.schema.Vertex) :
    ((protocolObservedFiniteDecoder input).obj P).stateDiagram.obj
        (Opposite.op (Opposite.op (input.schema.vertexObject vertex))) =
      finiteLocalValue
        (((ProtocolPresentation.decoder input.schema input.observation).obj P).State
          vertex) :=
  rfl

/-- A named edge of the observed decoder is the original finite transition
table, up to the decoder's explicit universe lift. -/
@[simp] theorem protocolObservedFiniteDecoder_map_edge
    (input : ProtocolFamilyInput.{u})
    (P : ProtocolPresentation input.schema input.observation)
    {source target : input.schema.Vertex}
    (edge : input.schema.Edge source target)
    (state : ULift.{u} (Fin (P.card source))) :
    ((protocolObservedFiniteDecoder input).obj P).stateDiagram.map
        (input.schema.edgeMorphism edge).op.op state =
      ULift.up (P.edgeTable edge state.down) :=
  rfl

/-- The observed decoder's local observation is exactly the presentation's
displayed observation value. -/
@[simp] theorem protocolObservedFiniteDecoder_observe
    (input : ProtocolFamilyInput.{u})
    (P : ProtocolPresentation input.schema input.observation)
    (vertex : input.schema.Vertex)
    (state : ULift.{u} (Fin (P.card vertex))) :
    ((protocolObservedFiniteDecoder input).obj P).observe.app
        (Opposite.op (Opposite.op (input.schema.vertexObject vertex))) state =
      P.observationValue vertex state.down :=
  rfl

/-- A finite presentation morphism is read at a named vertex as its original
finite component table. -/
@[simp] theorem protocolObservedFiniteDecoder_map_app_vertex
    (input : ProtocolFamilyInput.{u})
    {P Q : ProtocolPresentation input.schema input.observation}
    (f : P ⟶ Q) (vertex : input.schema.Vertex)
    (state : ULift.{u} (Fin (P.card vertex))) :
    ((protocolObservedFiniteDecoder input).map f).stateMap.app
        (Opposite.op (Opposite.op (input.schema.vertexObject vertex))) state =
      ULift.up (f.component vertex state.down) :=
  rfl

/-- The accepted Karoubi reconstruction transported through the observed
restriction equivalence. -/
noncomputable def protocolKaroubiObservedRestrictionEquivalence
    (input : ProtocolFamilyInput.{u}) :
    Karoubi (ProtocolPresentation input.schema input.observation) ≌
      ProtocolObservedRestrictionModel input :=
  ProtocolPresentation.protocolKaroubiReconstructionEquivalence.trans
    (protocolSemanticObservedRestrictionEquivalence input)

/-- Restricting the transported Karoubi reconstruction to finite
presentations recovers the observed finite decoder. -/
noncomputable def protocolKaroubiObservedRestrictionRestrictionIso
    (input : ProtocolFamilyInput.{u}) :
    toKaroubi (ProtocolPresentation input.schema input.observation) ⋙
        (protocolKaroubiObservedRestrictionEquivalence input).functor ≅
      protocolObservedFiniteDecoder input :=
  (Functor.associator
      (toKaroubi (ProtocolPresentation input.schema input.observation))
      ProtocolPresentation.protocolKaroubiReconstructionEquivalence.functor
      (protocolSemanticObservedRestrictionEquivalence input).functor).symm.trans
    (Functor.isoWhiskerRight
      ProtocolPresentation.protocolKaroubiReconstructionRestrictionIso
      (protocolSemanticObservedRestrictionEquivalence input).functor)

/-- Every observed finite restriction model is a retract of the observed
reading of a decoded finite presentation.  The proof uses the explicit local
assembly/readback isomorphism and the accepted semantic retract theorem. -/
theorem protocolObservedFiniteDecoder_retractGeneratedBy
    (input : ProtocolFamilyInput.{u}) :
    RetractGeneratedBy (protocolObservedFiniteDecoder input) := by
  intro Z
  let X := protocolObservedRestrictionRealization input Z
  rcases ProtocolPresentation.protocolRetractGeneratedBy X with
    ⟨P, insertion, retraction, retract⟩
  let localIso := protocolObservedRestrictionRealizationIso input Z
  let F := (protocolSemanticObservedRestrictionEquivalence input).functor
  have mappedRetract :
      F.map insertion ≫ F.map retraction =
        𝟙 (protocolObservedRestrictionObject input X) := by
    simpa only [F.map_comp, F.map_id] using congrArg F.map retract
  refine ⟨P,
    localIso.inv ≫ F.map insertion,
    F.map retraction ≫ localIso.hom, ?_⟩
  calc
    localIso.inv ≫ F.map insertion ≫ F.map retraction ≫ localIso.hom =
        localIso.inv ≫ (F.map insertion ≫ F.map retraction) ≫
          localIso.hom := by simp only [Category.assoc]
    _ = 𝟙 Z := by
      rw [mappedRetract]
      simpa only [Category.comp_id] using localIso.inv_hom_id

/-- Arrow-level Karoubi reconstruction transported to observed local models.
This retains arbitrary observation-compatible transformations, not only
isomorphisms. -/
noncomputable def protocolKaroubiObservedRestrictionArrowEquivalence
    (input : ProtocolFamilyInput.{u}) :
    Karoubi (Arrow (ProtocolPresentation input.schema input.observation)) ≌
      Arrow (ProtocolObservedRestrictionModel input) :=
  ProtocolPresentation.protocolKaroubiArrowReconstructionEquivalence.trans
    (Functor.mapArrowEquivalence
      (protocolSemanticObservedRestrictionEquivalence input))

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction

end AAT.AG.LocalSemanticReconstruction
