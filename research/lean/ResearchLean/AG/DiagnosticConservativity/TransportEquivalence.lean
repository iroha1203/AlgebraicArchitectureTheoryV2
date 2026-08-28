import ResearchLean.AG.DiagnosticConservativity.TransportAdjunction

/-!
# G-113 revision 2 vertexwise transport equivalence

The arbitrary-base adjunction from Cycle 3 has producer-generated invertible
unit and counit.  This module packages those data as an explicit equivalence
and derives the named categorical consequences required by G-113(a).  The
indexed declarations use exactly the F0 push and semantic-global reindexing
functors at the same vertex base arrow.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence

/-! ## Arbitrary-base equivalence -/

/-- Canonical transport and semantic-global reindexing form an equivalence. -/
noncomputable def semanticGlobalTransportEquivalence
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target) : CoreFiber source ≌ CoreFiber target := by
  letI : ∀ sourcePackage,
      IsIso ((semanticGlobalTransportReindexAdjunction baseHom).unit.app
        sourcePackage) :=
    semanticGlobalTransportReindexUnit_app_isIso baseHom
  letI : ∀ targetPackage,
      IsIso ((semanticGlobalTransportReindexAdjunction baseHom).counit.app
        targetPackage) :=
    semanticGlobalTransportReindexCounit_app_isIso baseHom
  exact (semanticGlobalTransportReindexAdjunction baseHom).toEquivalence

/-- The forward functor of the generated equivalence is canonical transport. -/
theorem semanticGlobalTransportEquivalence_functor
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target) :
    (semanticGlobalTransportEquivalence baseHom).functor =
      coreFiberTransportFunctor baseHom :=
  rfl

/-- The inverse functor is exactly G-112 semantic-global reindexing. -/
theorem semanticGlobalTransportEquivalence_inverse
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target) :
    (semanticGlobalTransportEquivalence baseHom).inverse =
      exact_bottom_semantic_global_reindex_functor baseHom :=
  rfl

/-- Canonical transport is an equivalence for every semantic base arrow. -/
theorem semanticGlobalTransport_isEquivalence
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (baseHom : source ⟶ target) :
    (coreFiberTransportFunctor baseHom).IsEquivalence :=
  (semanticGlobalTransportEquivalence baseHom).isEquivalence_functor

/-! ## Indexed equivalence and named categorical producers -/

/-- The explicit G-113(a) equivalence at one indexed vertex. -/
noncomputable def indexedDiagnosticTransportEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) :
    CoreFiber (D.vertex vertex) ≌ CoreFiber (E.vertex vertex) :=
  semanticGlobalTransportEquivalence (hom.app vertex)

/-- The explicit equivalence has the exact F0 push as its forward functor. -/
theorem indexedDiagnosticTransportEquivalence_functor
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) :
    (indexedDiagnosticTransportEquivalence hom vertex).functor =
      indexedDiagnosticTransportPush hom vertex :=
  rfl

/-- The explicit equivalence has the exact F0 reindexing as its inverse. -/
theorem indexedDiagnosticTransportEquivalence_inverse
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) :
    (indexedDiagnosticTransportEquivalence hom vertex).inverse =
      indexedDiagnosticTransportReindex hom vertex :=
  rfl

/-- The indexed diagnostic push is an equivalence. -/
theorem indexedDiagnosticTransportPush_isEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) :
    (indexedDiagnosticTransportPush hom vertex).IsEquivalence :=
  (indexedDiagnosticTransportEquivalence hom vertex).isEquivalence_functor

/-- The indexed diagnostic push is full. -/
theorem indexedDiagnosticTransportPush_full
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) :
    (indexedDiagnosticTransportPush hom vertex).Full := by
  letI : (indexedDiagnosticTransportPush hom vertex).IsEquivalence :=
    indexedDiagnosticTransportPush_isEquivalence hom vertex
  infer_instance

/-- The indexed diagnostic push is faithful. -/
theorem indexedDiagnosticTransportPush_faithful
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) :
    (indexedDiagnosticTransportPush hom vertex).Faithful := by
  letI : (indexedDiagnosticTransportPush hom vertex).IsEquivalence :=
    indexedDiagnosticTransportPush_isEquivalence hom vertex
  infer_instance

/-- The indexed diagnostic push is essentially surjective. -/
theorem indexedDiagnosticTransportPush_essentiallySurjective
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) :
    (indexedDiagnosticTransportPush hom vertex).EssSurj := by
  letI : (indexedDiagnosticTransportPush hom vertex).IsEquivalence :=
    indexedDiagnosticTransportPush_isEquivalence hom vertex
  infer_instance

/-- Every target-fiber object has the explicit counit object isomorphism. -/
noncomputable def indexedDiagnosticTransportObjectIso
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) (targetPackage : CoreFiber (E.vertex vertex)) :
    (indexedDiagnosticTransportPush hom vertex).obj
        ((indexedDiagnosticTransportReindex hom vertex).obj targetPackage) ≅
      targetPackage :=
  (indexedDiagnosticTransportCounitIso hom vertex).app targetPackage

/-- Fullness as an explicit preimage producer for an arbitrary target hom. -/
theorem indexedDiagnosticTransportHom_preimage
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) {first second : CoreFiber (D.vertex vertex)}
    (targetHom :
      (indexedDiagnosticTransportPush hom vertex).obj first ⟶
        (indexedDiagnosticTransportPush hom vertex).obj second) :
    ∃ sourceHom : first ⟶ second,
      (indexedDiagnosticTransportPush hom vertex).map sourceHom = targetHom := by
  letI : (indexedDiagnosticTransportPush hom vertex).Full :=
    indexedDiagnosticTransportPush_full hom vertex
  exact Functor.Full.map_surjective targetHom

/-- Faithfulness as equality reflection for arbitrary source-fiber homs. -/
theorem indexedDiagnosticTransportHom_eq_of_map_eq
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (vertex : G.Vertex) {first second : CoreFiber (D.vertex vertex)}
    {left right : first ⟶ second}
    (map_eq : (indexedDiagnosticTransportPush hom vertex).map left =
      (indexedDiagnosticTransportPush hom vertex).map right) :
    left = right := by
  letI : (indexedDiagnosticTransportPush hom vertex).Faithful :=
    indexedDiagnosticTransportPush_faithful hom vertex
  exact (indexedDiagnosticTransportPush hom vertex).map_injective map_eq

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
