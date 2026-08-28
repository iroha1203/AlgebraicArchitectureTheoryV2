import ResearchLean.AG.DiagnosticConservativity.TransportEquivalence

/-!
# G-113 revision 2 diagnostic endpoint exactness

The vertexwise category equivalence induces an equivalence on the endpoint
automorphism groups of every diagnostic package.  Its forward map is the
reviewed G-111 endpoint action, so injectivity and surjectivity are consequences
of one explicit equivalence rather than additional hypotheses.
-/

namespace AAT.AG.DoctrineFiberProduct

universe u

open CategoryTheory
open AtomFoundation
open CrossStageCoherence
open TransportCoherence

/-- A core-fiber equivalence induces an equivalence of package automorphism groups. -/
noncomputable def coreFiberEquivalencePackageAutMulEquiv
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (equivalence : CoreFiber source ≌ CoreFiber target)
    (sourcePackage : CoreFiber source) :
    PackageFiberAut sourcePackage.1 ≃*
      PackageFiberAut (equivalence.functor.obj sourcePackage).1 :=
  (packageFiberAutCoreFiberEquiv sourcePackage).trans
    ((equivalence.fullyFaithfulFunctor.autMulEquivOfFullyFaithful
      sourcePackage).trans
        (packageFiberAutCoreFiberEquiv
          (equivalence.functor.obj sourcePackage)).symm)

/-- The induced endpoint equivalence has the usual functorial action as forward map. -/
theorem coreFiberEquivalencePackageAutMulEquiv_apply
    {U : AtomCarrier.{u}} {source target : ExtractionInstance U}
    (equivalence : CoreFiber source ≌ CoreFiber target)
    (sourcePackage : CoreFiber source)
    (automorphism : PackageFiberAut sourcePackage.1) :
    coreFiberEquivalencePackageAutMulEquiv equivalence sourcePackage
        automorphism =
      coreFiberFunctorPackageAutHom equivalence.functor sourcePackage
        automorphism := by
  rfl

/-- The explicit endpoint equivalence at one indexed diagnostic vertex. -/
noncomputable def indexedDiagnosticEndpointEquivalence
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex) :
    PackageFiberAut (source.package vertex) ≃*
      PackageFiberAut
        ((hom.transportedInterpretation source).package vertex) :=
  coreFiberEquivalencePackageAutMulEquiv
    (indexedDiagnosticTransportEquivalence hom vertex)
    (source.fiberPackage vertex)

/-- The endpoint equivalence forward map is exactly the revision-1 endpoint action. -/
theorem indexedDiagnosticEndpointEquivalence_apply
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex)
    (automorphism : PackageFiberAut (source.package vertex)) :
    indexedDiagnosticEndpointEquivalence hom source vertex automorphism =
      hom.endpointAction source vertex automorphism := by
  rfl

/-- The revision-1 endpoint action is injective as the forward endpoint equivalence. -/
theorem indexedDiagnosticEndpointAction_injective
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex) :
    Function.Injective (hom.endpointAction source vertex) := by
  intro left right action_eq
  apply (indexedDiagnosticEndpointEquivalence hom source vertex).injective
  simpa only [indexedDiagnosticEndpointEquivalence_apply] using action_eq

/-- The revision-1 endpoint action is surjective as the forward endpoint equivalence. -/
theorem indexedDiagnosticEndpointAction_surjective
    {G : IndexedBaseTwoShape.{u}} {U : AtomCarrier.{u}}
    {D E : IndexedBaseDiagram G U} (hom : IndexedBaseDiagramHom D E)
    (source : IndexedDiagnosticInterpretation D) (vertex : G.Vertex) :
    Function.Surjective (hom.endpointAction source vertex) := by
  intro targetAut
  refine ⟨(indexedDiagnosticEndpointEquivalence hom source vertex).symm
    targetAut, ?_⟩
  rw [← indexedDiagnosticEndpointEquivalence_apply]
  exact (indexedDiagnosticEndpointEquivalence hom source vertex).apply_symm_apply
    targetAut

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
