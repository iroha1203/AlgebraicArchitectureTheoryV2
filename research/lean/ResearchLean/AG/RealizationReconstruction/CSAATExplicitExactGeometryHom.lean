import ResearchLean.AG.RealizationReconstruction.CSAATGeneratedCoverageTransport
import ResearchLean.AG.RealizationReconstruction.CSAATExplicitRealizationSupply
import Formal.Util.AssertStandardAxioms

/-!
# Exact geometry hom with explicit context action

This parallel hom retains the actual `ContextMorphism` action used by the
generated CS realization supplies.  It combines the constructed authoritative
coverage and overlap with coefficient and typed raw transport; it does not
coerce explicit naturality into the representative-selected
`RealizationTransportSupply` contract.
-/

namespace AAT.AG.RealizationReconstruction

open CategoryTheory
open AtomFoundation
open GeometryTransport

universe u v

/-- All six exact geometry components, with realization naturality indexed by
the actual retained context morphism. -/
structure ExplicitExactGeometryHom {U : AtomCarrier.{u}}
    (G H : GeometryPackage.{u, v} U) where
  base : PackageTotalHom G.core H.core
  coverage : CoverageTransport G H base
  overlap : OverlapTransport G H base
  coefficientHom : G.Coefficient →+* H.Coefficient
  raw : RawAmbientRestrictionSystemExactMapAgainst G.site H.site
    (coreContextInverse base) coefficientHom G.raw H.raw
  realization : ExplicitRealizationTransportSupply G.core H.core base

namespace ExplicitRealizationTransportSupply

/-- Identity supply retains every actual context morphism. -/
def id {U : AtomCarrier.{u}} (P : AATCorePackage U) :
    ExplicitRealizationTransportSupply P P (PackageTotalHom.id P) where
  contextMorphism := fun f => f
  contextMorphism_isRestriction := fun _ hf => hf
  supportEquiv := fun _ => Equiv.refl _
  axisEquiv := fun _ => Equiv.refl _
  observableEquiv := fun _ => Equiv.refl _
  supportReads_iff := fun _ _ _ => Iff.rfl
  axisReads_iff := fun _ _ => Iff.rfl
  observableReads_iff := fun _ _ => Iff.rfl
  support_naturality := fun _ _ => rfl
  axis_naturality := fun _ _ => rfl
  observable_naturality := fun _ _ => rfl

/-- Composition acts successively on the same actual context morphism and
proves all three naturality equations componentwise. -/
def comp {U : AtomCarrier.{u}} {P Q R : AATCorePackage U}
    {f : PackageTotalHom P Q} {g : PackageTotalHom Q R}
    (first : ExplicitRealizationTransportSupply P Q f)
    (second : ExplicitRealizationTransportSupply Q R g) :
    ExplicitRealizationTransportSupply P R (PackageTotalHom.comp f g) where
  contextMorphism h := second.contextMorphism (first.contextMorphism h)
  contextMorphism_isRestriction h hh :=
    second.contextMorphism_isRestriction _
      (first.contextMorphism_isRestriction h hh)
  supportEquiv W := (first.supportEquiv W).trans (second.supportEquiv _)
  axisEquiv W := (first.axisEquiv W).trans (second.axisEquiv _)
  observableEquiv W := (first.observableEquiv W).trans
    (second.observableEquiv _)
  supportReads_iff W support atom :=
    (first.supportReads_iff W support atom).trans
      (second.supportReads_iff _ (first.supportEquiv W support)
        (f.upper.atomEquiv atom))
  axisReads_iff W axis :=
    (first.axisReads_iff W axis).trans
      (second.axisReads_iff _ (first.axisEquiv W axis))
  observableReads_iff W observable :=
    (first.observableReads_iff W observable).trans
      (second.observableReads_iff _ (first.observableEquiv W observable))
  support_naturality h support := by
    simp only [Equiv.trans_apply]
    calc
      _ = second.supportEquiv _
          ((first.contextMorphism h).supportMap
            (first.supportEquiv _ support)) :=
        second.support_naturality (first.contextMorphism h)
          (first.supportEquiv _ support)
      _ = _ := congrArg (second.supportEquiv _)
        (first.support_naturality h support)
  axis_naturality h axis := by
    simp only [Equiv.trans_apply]
    calc
      _ = second.axisEquiv _
          ((first.contextMorphism h).axisMap (first.axisEquiv _ axis)) :=
        second.axis_naturality (first.contextMorphism h)
          (first.axisEquiv _ axis)
      _ = _ := congrArg (second.axisEquiv _)
        (first.axis_naturality h axis)
  observable_naturality h observable := by
    simp only [Equiv.trans_apply]
    calc
      _ = second.observableEquiv _
          ((first.contextMorphism h).observableRestrict
            (first.observableEquiv _ observable)) :=
        second.observable_naturality (first.contextMorphism h)
          (first.observableEquiv _ observable)
      _ = _ := congrArg (second.observableEquiv _)
        (first.observable_naturality h observable)

end ExplicitRealizationTransportSupply

namespace ExplicitExactGeometryHom

noncomputable def id {U : AtomCarrier.{u}} (G : GeometryPackage.{u, v} U) :
    ExplicitExactGeometryHom G G where
  base := PackageTotalHom.id G.core
  coverage := CoverageTransport.id G
  overlap := OverlapTransport.id G
  coefficientHom := RingHom.id G.Coefficient
  raw := RawAmbientRestrictionSystemExactMapAgainst.refl
    G.site G.Coefficient G.raw
  realization := ExplicitRealizationTransportSupply.id G.core

noncomputable def comp {U : AtomCarrier.{u}}
    {G H K : GeometryPackage.{u, v} U}
    (first : ExplicitExactGeometryHom G H)
    (second : ExplicitExactGeometryHom H K) :
    ExplicitExactGeometryHom G K where
  base := PackageTotalHom.comp first.base second.base
  coverage := first.coverage.comp second.coverage
  overlap := first.overlap.comp second.overlap
  coefficientHom := second.coefficientHom.comp first.coefficientHom
  raw := first.raw.trans second.raw
  realization := ExplicitRealizationTransportSupply.comp
    first.realization second.realization

end ExplicitExactGeometryHom

/-- The complete exact lens geometry hom in the actual-restriction API. -/
noncomputable def lensIsoExplicitExactGeometryHom
    {input : LensFamilyInput.{u}}
    {X Y : LensRealization input.View input.reference} (e : X ≅ Y) :
    ExplicitExactGeometryHom (lensAATReadingCore input X)
      (lensAATReadingCore input Y) where
  base := lensIsoPackageTotalHom e
  coverage := lensIsoCoverageTransport e
  overlap := lensIsoOverlapTransport e
  coefficientHom := RingHom.id Int
  raw := lensIsoReadingCoreRawExactMapAgainst e (lensIsoPackageTotalHom e)
  realization := lensIsoExplicitRealizationTransportSupply e

/-- The complete exact protocol geometry hom in the actual-restriction API. -/
noncomputable def protocolIsoExplicitExactGeometryHom
    {input : ProtocolFamilyInput.{u}}
    {X Y : ProtocolRealization input.schema input.observation} (e : X ≅ Y) :
    ExplicitExactGeometryHom (protocolAATReadingCore input X)
      (protocolAATReadingCore input Y) where
  base := protocolIsoPackageTotalHom e
  coverage := protocolIsoCoverageTransport e
  overlap := protocolIsoOverlapTransport e
  coefficientHom := RingHom.id Int
  raw := protocolIsoReadingCoreRawExactMapAgainst e (protocolIsoPackageTotalHom e)
  realization := protocolIsoExplicitRealizationTransportSupply e

#assert_standard_axioms_only AAT.AG.RealizationReconstruction

end AAT.AG.RealizationReconstruction
