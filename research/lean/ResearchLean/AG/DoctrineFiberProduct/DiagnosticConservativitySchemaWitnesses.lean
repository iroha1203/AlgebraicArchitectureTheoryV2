import ResearchLean.AG.DoctrineFiberProduct.DiagnosticConservativitySchema
import ResearchLean.AG.DoctrineFiberProduct.IndexedDiagnosticCovarianceWitnesses
import ResearchLean.AG.DoctrineFiberProduct.BCSchemaWitnesses

/-!
# Structural witnesses for the diagnostic-conservativity schema

This module exercises only the G-113 F0 condition surface.  The shared G-111
witness shape has two distinct vertices, two distinct parallel edges, one
declared face, and the nontrivial `FiniteModel.carrier`; it is neither an empty
diagnostic diagram nor a one-object fixture.

The identity fixture satisfies both atomic terms.  The collapse fixture has
noninjective vertex maps, while the square fixture is the existing concrete
non-pullback.  No conservativity, vanishing, or nonvanishing certificate is
stored in any fixture field.

Positive and negative inhabitants of `DiagnosticConservative` are deliberately
not supplied at F0.  A nondegenerate positive requires the K1 identity or
sufficiency theorem.  A negative is exactly the K3/O16 class-exterior witness:
generated target vanishing together with source nonvanishing.  Supplying either
result as fixture data would violate the fixed GOAL's anti-weakening rule.
-/

namespace AAT.AG.DoctrineFiberProduct

open CategoryTheory
open AtomFoundation
open TransportCoherence

local instance finiteModelCarrierAtomDecidableEq_g113 :
    DecidableEq FiniteModel.carrier.Atom := by
  change DecidableEq FiniteModel.FiniteAtom
  infer_instance

/-- The two vertices of the shared G-111 fixture are distinct. -/
theorem diagnosticSchemaFixture_vertices_ne :
    indexedCovarianceSourceVertex ≠ indexedCovarianceTargetVertex := by
  change (SingleDiskVertex.source : IndexedCovarianceVertex) ≠
    SingleDiskVertex.target
  decide

/-- The two parallel edges of the shared G-111 fixture are distinct. -/
theorem diagnosticSchemaFixture_edges_ne :
    indexedCovarianceLeftEdge ≠ indexedCovarianceRightEdge := by
  intro equality
  cases equality

/-- The finite fixture carrier contains two distinct primitive Atoms. -/
theorem diagnosticSchemaFixture_atoms_ne :
    FiniteModel.FiniteAtom.componentA ≠ FiniteModel.FiniteAtom.componentB := by
  decide

/-! ## Identity: both atomic conditions hold -/

/-- Constant indexed diagram on the concrete two-source extraction instance. -/
noncomputable def diagnosticSchemaIdentityDiagram :
    IndexedBaseDiagram indexedCovarianceShape FiniteModel.carrier where
  vertex := fun _ => finiteTwoSourceInstance.toSemantic
  edge := fun _ => 𝟙 _
  relation := by
    intro cell
    change IndexedCovarianceCell at cell
    cases cell
    rfl

/-- Identity diagram hom used as the simultaneous positive structural fixture. -/
noncomputable def diagnosticSchemaIdentityHom :
    IndexedBaseDiagramHom diagnosticSchemaIdentityDiagram
      diagnosticSchemaIdentityDiagram :=
  IndexedBaseDiagramHom.id diagnosticSchemaIdentityDiagram

/-- Every vertex source map of the identity fixture is injective. -/
theorem diagnosticSchemaIdentity_eval_injective :
    DiagnosticClassTerm.eval .vertexwiseSourceMapInjective
      diagnosticSchemaIdentityHom := by
  intro vertex first second equality
  exact equality

/-- Every generated edge square of the identity fixture is a pullback. -/
theorem diagnosticSchemaIdentity_eval_pullback :
    DiagnosticClassTerm.eval .edgewiseSquarePullback
      diagnosticSchemaIdentityHom := by
  intro i j edge
  simpa [diagnosticSchemaIdentityHom, IndexedBaseDiagramHom.id,
    IndexedBaseDiagramHom.edgeSquare, diagnosticSchemaIdentityDiagram] using
      (IsPullback.id_vert (𝟙 finiteTwoSourceInstance.toSemantic))

/-- The conjunction normal form fires on the identity fixture. -/
theorem diagnosticSchemaIdentity_eval_conjunction :
    DiagnosticClassTerm.eval
      (.conjunction .vertexwiseSourceMapInjective .edgewiseSquarePullback)
      diagnosticSchemaIdentityHom :=
  ⟨diagnosticSchemaIdentity_eval_injective,
    diagnosticSchemaIdentity_eval_pullback⟩

/-- The fixed G-113(i) predicate fires on the identity fixture. -/
theorem diagnosticSchemaIdentity_bijective :
    VertexwiseSourceMapBijective diagnosticSchemaIdentityHom := by
  intro vertex
  exact ⟨fun _ _ equality => equality, fun value => ⟨value, rfl⟩⟩

/-- The registered G-113(i) term fires on the same identity fixture. -/
theorem diagnosticSchemaIdentity_fullFaithfulCandidate :
    FullFaithfulCandidate.eval .vertexwiseSourceMapBijective
      diagnosticSchemaIdentityHom :=
  diagnosticSchemaIdentity_bijective

/-- Generated-class membership is inhabited by the conjunction fixture. -/
theorem diagnosticSchemaIdentity_generated :
    GeneratedDiagnosticClass
      (.conjunction .vertexwiseSourceMapInjective .edgewiseSquarePullback)
      diagnosticSchemaIdentityHom :=
  diagnosticSchemaIdentity_eval_conjunction

/-! ## Collapse: injectivity and bijectivity fail -/

/-- Constant source diagram on the two-source extraction instance. -/
noncomputable def diagnosticSchemaCollapseSourceDiagram :
    IndexedBaseDiagram indexedCovarianceShape FiniteModel.carrier where
  vertex := fun _ => finiteTwoSourceInstance.toSemantic
  edge := fun _ => 𝟙 _
  relation := by
    intro cell
    change IndexedCovarianceCell at cell
    cases cell
    rfl

/-- Constant target diagram on the one-source extraction instance. -/
noncomputable def diagnosticSchemaCollapseTargetDiagram :
    IndexedBaseDiagram indexedCovarianceShape FiniteModel.carrier where
  vertex := fun _ => finiteOneSourceInstance.toSemantic
  edge := fun _ => 𝟙 _
  relation := by
    intro cell
    change IndexedCovarianceCell at cell
    cases cell
    rfl

/-- The finite noninjective constant map at both vertices. -/
noncomputable def diagnosticSchemaCollapseHom :
    IndexedBaseDiagramHom diagnosticSchemaCollapseSourceDiagram
      diagnosticSchemaCollapseTargetDiagram where
  app := fun _ =>
    (toSemanticCart finiteConstantPresentation.toPresentation).hom
  naturality := by
    intro i j edge
    change (toSemanticCart finiteConstantPresentation.toPresentation).hom ≫
        𝟙 finiteOneSourceInstance.toSemantic =
      𝟙 finiteTwoSourceInstance.toSemantic ≫
        (toSemanticCart finiteConstantPresentation.toPresentation).hom
    exact Category.comp_id _

/-- The collapse fixture refutes vertexwise source-map injectivity. -/
theorem diagnosticSchemaCollapse_not_eval_injective :
    ¬ DiagnosticClassTerm.eval .vertexwiseSourceMapInjective
      diagnosticSchemaCollapseHom := by
  intro injective
  apply finiteConstantSourceMap_not_injective
  have atSource := injective indexedCovarianceSourceVertex
  simpa [diagnosticSchemaCollapseHom] using atSource

/-- Hence the conjunction normal form fails on the collapse fixture. -/
theorem diagnosticSchemaCollapse_not_eval_conjunction :
    ¬ DiagnosticClassTerm.eval
      (.conjunction .vertexwiseSourceMapInjective .edgewiseSquarePullback)
      diagnosticSchemaCollapseHom := by
  intro conjunction
  exact diagnosticSchemaCollapse_not_eval_injective conjunction.1

/-- The fixed G-113(i) predicate also fails on the collapse fixture. -/
theorem diagnosticSchemaCollapse_not_bijective :
    ¬ VertexwiseSourceMapBijective diagnosticSchemaCollapseHom := by
  intro bijective
  exact diagnosticSchemaCollapse_not_eval_injective
    (fun vertex => (bijective vertex).1)

/-- The registered G-113(i) term fails on the same collapse fixture. -/
theorem diagnosticSchemaCollapse_not_fullFaithfulCandidate :
    ¬ FullFaithfulCandidate.eval .vertexwiseSourceMapBijective
      diagnosticSchemaCollapseHom :=
  diagnosticSchemaCollapse_not_bijective

/-- Generated injectivity-class membership fails on the collapse fixture. -/
theorem diagnosticSchemaCollapse_not_generated :
    ¬ GeneratedDiagnosticClass .vertexwiseSourceMapInjective
      diagnosticSchemaCollapseHom :=
  diagnosticSchemaCollapse_not_eval_injective

/-! ## The pullback atom has an independent concrete negative -/

/-- Source diagram formed by the top side of the existing non-pullback square. -/
noncomputable def diagnosticSchemaNonPullbackSourceDiagram :
    IndexedBaseDiagram indexedCovarianceShape FiniteModel.carrier where
  vertex := fun vertex => by
    change IndexedCovarianceVertex at vertex
    cases vertex
    · exact finiteNonPullbackSquare.northwest
    · exact finiteNonPullbackSquare.northeast
  edge := by
    intro i j edge
    change IndexedCovarianceEdge i j at edge
    cases edge <;> exact finiteNonPullbackSquare.top
  relation := by
    intro cell
    change IndexedCovarianceCell at cell
    cases cell
    rfl

/-- Target diagram formed by the bottom side of the same square. -/
noncomputable def diagnosticSchemaNonPullbackTargetDiagram :
    IndexedBaseDiagram indexedCovarianceShape FiniteModel.carrier where
  vertex := fun vertex => by
    change IndexedCovarianceVertex at vertex
    cases vertex
    · exact finiteNonPullbackSquare.southwest
    · exact finiteNonPullbackSquare.southeast
  edge := by
    intro i j edge
    change IndexedCovarianceEdge i j at edge
    cases edge <;> exact finiteNonPullbackSquare.bottom
  relation := by
    intro cell
    change IndexedCovarianceCell at cell
    cases cell
    rfl

/-- Diagram hom whose generated edge squares are the concrete non-pullback. -/
noncomputable def diagnosticSchemaNonPullbackHom :
    IndexedBaseDiagramHom diagnosticSchemaNonPullbackSourceDiagram
      diagnosticSchemaNonPullbackTargetDiagram where
  app := fun vertex => by
    change IndexedCovarianceVertex at vertex
    cases vertex
    · exact finiteNonPullbackSquare.left
    · exact finiteNonPullbackSquare.right
  naturality := by
    intro i j edge
    change IndexedCovarianceEdge i j at edge
    cases edge <;> exact finiteNonPullbackSquare.commutes

/-- The pullback atom fails on an actual non-pullback generated edge square. -/
theorem diagnosticSchemaNonPullback_not_eval_pullback :
    ¬ DiagnosticClassTerm.eval .edgewiseSquarePullback
      diagnosticSchemaNonPullbackHom := by
  intro pullback
  apply finiteNonPullbackSquare_not_isPullback
  simpa [diagnosticSchemaNonPullbackHom, IndexedBaseDiagramHom.edgeSquare,
    diagnosticSchemaNonPullbackSourceDiagram,
    diagnosticSchemaNonPullbackTargetDiagram] using
      pullback indexedCovarianceLeftEdge

/-- Generated pullback-class membership fails on the same concrete square. -/
theorem diagnosticSchemaNonPullback_not_generated :
    ¬ GeneratedDiagnosticClass .edgewiseSquarePullback
      diagnosticSchemaNonPullbackHom :=
  diagnosticSchemaNonPullback_not_eval_pullback

/-! ## The conservativity quantifier has a concrete nonempty domain -/

/-- The source-interpretation quantifier is inhabited by the nontrivial G-111 witness. -/
theorem diagnosticSchemaInterpretation_nonempty :
    Nonempty (IndexedDiagnosticInterpretation indexedCovarianceDiagram) :=
  ⟨indexedCovarianceSource⟩

end AAT.AG.DoctrineFiberProduct

#assert_standard_axioms_only AAT.AG.DoctrineFiberProduct
