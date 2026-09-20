import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomEquationLaws
import Formal.Util.AssertStandardAxioms

/-!
# Native equation transport assembled from common Hom point conditions

The context equivalence, equation equivalence, and observable family are
constructed from their respective primitive rows. Four point predicates
supply the native role, naturality, violation, and residual fields via the
proved local/native equivalences. No completed transport is an input.
The observable graph code is also connected directly to the existing package
assembler, retaining its reconstructed context index.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.EquationAssembly

noncomputable section

universe u v

open Site CategoryTheory

variable {U : AtomCarrier.{u}} {A B : ArchitectureObject U} {mode : Mode}
variable {C : ContextPreorderCategory A} {D : ContextPreorderCategory B}
variable (s : IndependentEquationPrimitive.Table A) (t : IndependentEquationPrimitive.Table B)
variable (hs : IndependentEquationPrimitive.IsTyped C s) (ht : IndependentEquationPrimitive.IsTyped D t)
variable (hls : IndependentEquationPrimitive.IsLawful s hs) (hlt : IndependentEquationPrimitive.IsLawful t ht)
variable (h : Table.{u, v} U mode)
variable (he : IndependentInverseGraph.IsLawful (IndependentEquationPrimitive.index s)
  (IndependentEquationPrimitive.index t) (InverseRows.equation h A B))
variable (hc : Context.IsLawful C.le D.le (Context.points h A B))
variable (ha : Atom.IsLawful (Atom.upper h)) (hm : CoreLaws.ObjectRows h)
variable (ho : letI := ObservableNatural.rings s hs hls
  letI := ObservableNatural.rings t ht hlt
  Observable.IsLawful h (IndependentEquationPrimitive.observableType s)
    (IndependentEquationPrimitive.observableType t))

/-- The four local preservation predicates compare only primitive responses and Hom point pairs. -/
structure PointLaws : Prop where
  /-- Equation-index points carry role responses. -/
  role : EquationLaws.RolePoints s t h
  /-- Restriction squares compare their six explicit query responses. -/
  naturality : ObservableNatural.PointLaws s t h
  /-- Observable points preserve each symbolic violation response. -/
  violation : EquationLaws.ViolationPoints s t h
  /-- Observable points preserve each residual response over the directed object map. -/
  residual : EquationLaws.ResidualPoints s t h

/-- Assemble every field of the native equation transport directly from the common primitive rows. -/
def assemble (hp : PointLaws s t h) :
    EquationSystemExactTransport
      (IndependentEquationPrimitive.assemble s hs hls) (IndependentEquationPrimitive.assemble t ht hlt)
      (Atom.assemble (Atom.upper h) ha) (CoreLaws.objectMap h hm) := by
  letI := ObservableNatural.rings s hs hls
  letI := ObservableNatural.rings t ht hlt
  exact {
    contextEquivalence := Context.assemble C D (Context.points h A B) hc
    equationEquiv := EquationLaws.equationEquiv s t h he
    role_eq := EquationLaws.role_eq_of_points s t hs ht h he hp.role
    observableEquiv := Observable.assemble C D h hc _ _ ho
    observable_naturality := (ObservableNatural.points_iff_nativeNaturality s t hs ht hls hlt h hc ho).1 hp.naturality ho
    violationCoordinate_eq := EquationLaws.nativeViolation_of_points s t hs ht h he hls hlt hc ha ho hp.violation
    equationResidual_eq := EquationLaws.nativeResidual_of_points s t hs ht h he hls hlt hc ha ho hm hp.residual }

/-- The assembled transport retains exactly the context equivalence constructed from the common context rows. -/
theorem assemble_context (hp : PointLaws s t h) :
    (assemble s t hs ht hls hlt h he hc ha hm ho hp).contextEquivalence =
      Context.assemble C D (Context.points h A B) hc := rfl

/-- The assembled transport retains exactly the independently constructed equation-index equivalence. -/
theorem assemble_equation (hp : PointLaws s t h) :
    (assemble s t hs ht hls hlt h he hc ha hm ho hp).equationEquiv =
      EquationLaws.equationEquiv s t h he := rfl

/-- The native observable component evaluates to the ring equivalence at its true primitive context pair. -/
theorem assemble_observable (hp : PointLaws s t h) (W : ContextCategoryObject C) :
    letI := ObservableNatural.rings s hs hls
    letI := ObservableNatural.rings t ht hlt
    (assemble s t hs ht hls hlt h he hc ha hm ho hp).observableEquiv W =
      Observable.atPair h _ _ ho W.ctx
        (((Context.assemble C D (Context.points h A B) hc).functor.obj W).ctx)
        (Observable.forward_point C D h hc W) := by
  letI := ObservableNatural.rings s hs hls
  letI := ObservableNatural.rings t ht hlt
  exact Observable.assemble_eq_atPair C D h hc _ _ ho W

/-- Reading the assembled equation transport restores every forward and backward context point. -/
theorem read_assemble_context (hp : PointLaws s t h) :
    Context.read C D (assemble s t hs ht hls hlt h he hc ha hm ho hp).contextEquivalence =
      Context.points h A B :=
  Context.read_assemble C D (Context.points h A B) hc

/-- Reading the assembled equation transport restores both equation graphs, including inactive carriers. -/
theorem read_assemble_equation (hp : PointLaws s t h) :
    IndependentInverseGraph.read _ _ (assemble s t hs ht hls hlt h he hc ha hm ho hp).equationEquiv =
      InverseRows.equation h A B :=
  IndependentInverseGraph.read_assemble _ _ (InverseRows.equation h A B) he

/-- The complete candidate observable rows survive native equation-transport assembly and reading. -/
theorem read_assemble_observable (hp : PointLaws s t h) :
    letI := ObservableNatural.rings s hs hls
    letI := ObservableNatural.rings t ht hlt
    (Observable.readingEquiv C D h hc (IndependentEquationPrimitive.observableType s)
      (IndependentEquationPrimitive.observableType t)
      (assemble s t hs ht hls hlt h he hc ha hm ho hp).observableEquiv).val = Observable.points h A B := by
  letI := ObservableNatural.rings s hs hls
  letI := ObservableNatural.rings t ht hlt
  exact Observable.read_assemble C D h hc _ _ ho

/-- Direct graph-code assembly joins the existing package API after native naturality is derived from point rules. -/
def contextObservableCode (hn : ObservableNatural.PointLaws s t h) :
    ContextObservableGraphCoherence.ContextObservableGraphCode
      (IndependentEquationPrimitive.assemble s hs hls) (IndependentEquationPrimitive.assemble t ht hlt) := by
  letI := ObservableNatural.rings s hs hls
  letI := ObservableNatural.rings t ht hlt
  refine ⟨Context.code C D (Context.points h A B) hc,
    ⟨⟨DependentAlgebraicGraphCoherence.IndexedRingEquivGraphCode.read
      (Observable.assemble C D h hc _ _ ho)⟩, ⟨?_⟩⟩⟩
  intro W X f x
  change (DependentAlgebraicGraphCoherence.IndexedRingEquivGraphCode.read
      (Observable.assemble C D h hc _ _ ho)).assemble W _ =
    (IndependentEquationPrimitive.assemble t ht hlt).restrict _
      ((DependentAlgebraicGraphCoherence.IndexedRingEquivGraphCode.read
        (Observable.assemble C D h hc _ _ ho)).assemble X x)
  rw [DependentAlgebraicGraphCoherence.IndexedRingEquivGraphCode.assemble_read]
  exact (ObservableNatural.points_iff_nativeNaturality s t hs ht hls hlt h hc ho).1 hn ho f x

/-- Direct graph-code construction preserves the original common-context code without a new context choice. -/
theorem contextObservableCode_context (hn : ObservableNatural.PointLaws s t h) :
    (contextObservableCode s t hs ht hls hlt h hc ho hn).context =
      Context.code C D (Context.points h A B) hc := rfl

/-- The observable graph-code assembler returns the family constructed from common observable rows. -/
theorem contextObservableCode_observable (hn : ObservableNatural.PointLaws s t h) :
    letI := ObservableNatural.rings s hs hls
    letI := ObservableNatural.rings t ht hlt
    (contextObservableCode s t hs ht hls hlt h hc ho hn).observable.1.observable.assemble =
      Observable.assemble C D h hc _ _ ho := by
  letI := ObservableNatural.rings s hs hls
  letI := ObservableNatural.rings t ht hlt
  exact DependentAlgebraicGraphCoherence.IndexedRingEquivGraphCode.assemble_read _

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.EquationAssembly

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.EquationAssembly
