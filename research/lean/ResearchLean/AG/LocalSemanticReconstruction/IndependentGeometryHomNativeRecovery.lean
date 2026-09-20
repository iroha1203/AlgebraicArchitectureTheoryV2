import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeRows
import Formal.Util.AssertStandardAxioms

/-!
# Native equation and observable recovery and point comparisons

These APIs complete the comparisons needed to use the existing preservation
converses on the common reader. The context and observable projections are
the same ones used by the indexed reader, so recovery uses its existing inverse
law; it does not choose a second observable family.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport

variable {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U} (mode : Mode)
variable (f : PackageTotalHom G.core H.core) (a : G.Coefficient →+* H.Coefficient)
variable (raw : RawQuery G.core.object H.core.object mode → Bool)
variable (realization : RealizationQuery G.core.object H.core.object mode → Bool)

/-- Equation assembly on the complete reader restores the native index equivalence in both directions. -/
theorem readWith_equation_assemble : IndependentInverseGraph.assemble G.core.equationSystem.Index
    H.core.equationSystem.Index
    (InverseRows.equation (readWith mode f a raw realization) G.core.object H.core.object)
    (readWith_equation_rows mode f a raw realization) = f.upper.equationEquiv := by
  have he : (⟨InverseRows.equation (readWith mode f a raw realization) G.core.object H.core.object,
      readWith_equation_rows mode f a raw realization⟩ :
      {p // IndependentInverseGraph.IsLawful G.core.equationSystem.Index H.core.equationSystem.Index p}) =
    ⟨IndependentInverseGraph.read _ _ f.upper.equationEquiv,
      IndependentInverseGraph.read_isLawful _ _ f.upper.equationEquiv⟩ :=
    Subtype.ext (readWith_equation mode f a raw realization)
  exact (congrArg (IndependentInverseGraph.readingEquiv G.core.equationSystem.Index
    H.core.equationSystem.Index).symm he).trans (IndependentInverseGraph.assemble_read _ _ f.upper.equationEquiv)

/-- Observable assembly restores the whole original ring-equivalence family over its original context functor. -/
theorem readWith_observable_assemble_heq : HEq
    (Observable.assemble G.core.contextPreorder H.core.contextPreorder (readWith mode f a raw realization)
      (readWith_context_rows mode f a raw realization)
      (fun W => G.core.equationSystem.Observable ⟨W⟩) (fun V => H.core.equationSystem.Observable ⟨V⟩)
      (readWith_observable_rows mode f a raw realization)) f.upper.equationTransport.observableEquiv := by
  have he : (⟨Observable.points (readWith mode f a raw realization) G.core.object H.core.object,
      readWith_observable_rows mode f a raw realization⟩ :
      {p // IndependentIndexedRingGraph.IsLawful (Observable.contextPoints (indices mode f a))
        (fun W => G.core.equationSystem.Observable ⟨W⟩) (fun V => H.core.equationSystem.Observable ⟨V⟩) p}) =
    Observable.readingEquiv G.core.contextPreorder H.core.contextPreorder (indices mode f a)
      (context_rows mode f a) (fun W => G.core.equationSystem.Observable ⟨W⟩)
      (fun V => H.core.equationSystem.Observable ⟨V⟩) (observableFamily mode f a) :=
    Subtype.ext (readWith_observable mode f a raw realization)
  have hm := (congrArg (Observable.readingEquiv G.core.contextPreorder H.core.contextPreorder
    (indices mode f a) (context_rows mode f a) (fun W => G.core.equationSystem.Observable ⟨W⟩)
    (fun V => H.core.equationSystem.Observable ⟨V⟩)).symm he).trans
      (Observable.assemble_read G.core.contextPreorder H.core.contextPreorder (indices mode f a)
        (context_rows mode f a) (fun W => G.core.equationSystem.Observable ⟨W⟩)
        (fun V => H.core.equationSystem.Observable ⟨V⟩) (observableFamily mode f a))
  exact (heq_of_eq hm).trans (observableFamily_heq mode f a)

/-- Context and its dependent observable family recover together, allowing native preservation equations to be transported. -/
theorem readWith_contextObservable_eq :
    (⟨Context.assemble G.core.contextPreorder H.core.contextPreorder
        (Context.points (readWith mode f a raw realization) G.core.object H.core.object)
        (readWith_context_rows mode f a raw realization),
      Observable.assemble G.core.contextPreorder H.core.contextPreorder (readWith mode f a raw realization)
        (readWith_context_rows mode f a raw realization)
        (fun W => G.core.equationSystem.Observable ⟨W⟩) (fun V => H.core.equationSystem.Observable ⟨V⟩)
        (readWith_observable_rows mode f a raw realization)⟩ :
      Σ E : ContextCategoryObject G.core.contextPreorder ≌ ContextCategoryObject H.core.contextPreorder,
        ∀ W, G.core.equationSystem.Observable W ≃+* H.core.equationSystem.Observable (E.functor.obj W)) =
    ⟨f.upper.equationTransport.contextEquivalence, f.upper.equationTransport.observableEquiv⟩ :=
  Sigma.ext (readWith_context_assemble mode f a raw realization)
    (readWith_observable_assemble_heq mode f a raw realization)

/-- A complete-reader Atom point is true exactly at the original native Atom image. -/
theorem readWith_atom_point_iff (x y : U.Atom) :
    readWith mode f a raw realization (.atom .forward x y) = true ↔ f.upper.atomEquiv x = y := by
  have he := TransportMatch.edge_iff (readWith mode f a raw realization)
    (readWith_atom_rows mode f a raw realization).upper x y
  change _ ↔ Atom.assemble _ _ x = y at he
  rw [readWith_atom_assemble] at he
  exact he

/-- A native equation index pair is represented by precisely its true common point. -/
theorem readWith_equation_point_iff (i : G.core.equationSystem.Index) (j : H.core.equationSystem.Index) :
    readWith mode f a raw realization (.atObjects G.core.object H.core.object
      (.equation .forward (.edge G.core.equationSystem.Index H.core.equationSystem.Index i j))) = true ↔
      f.upper.equationEquiv i = j := by
  have he := congrFun (readWith_equation mode f a raw realization)
    (.forward (.edge G.core.equationSystem.Index H.core.equationSystem.Index i j))
  exact (Iff.of_eq (congrArg (fun b => b = true) he)).trans
    (IndependentCarrierGraph.read_edge _ _ f.upper.equationEquiv i j)

/-- A native directed axis pair is represented by precisely its true common point. -/
theorem readWith_axis_point_iff (i : G.core.algebra.signatureReading.Axis)
    (j : H.core.algebra.signatureReading.Axis) :
    readWith mode f a raw realization (.signatureAxis (.edge G.core.algebra.signatureReading.Axis
      H.core.algebra.signatureReading.Axis i j)) = true ↔ f.upper.axisMap i = j :=
  IndependentCarrierGraph.read_edge _ _ f.upper.axisMap i j

/-- A native coefficient image is represented by precisely its true directed common point. -/
theorem readWith_coefficient_point_iff (x : G.Coefficient) (y : H.Coefficient) :
    readWith mode f a raw realization (.coefficient (.edge G.Coefficient H.Coefficient x y)) = true ↔ a x = y :=
  IndependentCarrierGraph.read_edge _ _ a x y

/-- True forward context points are exactly the objects of the original native context functor. -/
theorem readWith_context_point_iff (W : ArchCtx G.core.object) (V : ArchCtx H.core.object) :
    readWith mode f a raw realization (.atObjects _ _ (.context .forward W V)) = true ↔
      (f.upper.equationTransport.contextEquivalence.functor.obj ⟨W⟩).ctx = V := by
  rw [← readWith_context_assemble mode f a raw realization]
  let c := Context.code G.core.contextPreorder H.core.contextPreorder
    (Context.points (readWith mode f a raw realization) _ _) (readWith_context_rows mode f a raw realization)
  change c.forwardCode.edge ⟨W⟩ ⟨V⟩ = true ↔ (c.forwardCode.assemble ⟨W⟩).ctx = V
  rw [c.forwardCode.edge_eq_true_iff_target_eq]
  constructor
  · exact congrArg ContextCategoryObject.ctx
  · intro he
    cases c.forwardCode.assemble ⟨W⟩
    cases he
    rfl

/-- True backward context points retain the original inverse functor independently. -/
theorem readWith_context_backward_point_iff (W : ArchCtx G.core.object) (V : ArchCtx H.core.object) :
    readWith mode f a raw realization (.atObjects _ _ (.context .backward W V)) = true ↔
      (f.upper.equationTransport.contextEquivalence.inverse.obj ⟨V⟩).ctx = W := by
  rw [← readWith_context_assemble mode f a raw realization]
  let c := Context.code G.core.contextPreorder H.core.contextPreorder
    (Context.points (readWith mode f a raw realization) _ _) (readWith_context_rows mode f a raw realization)
  change c.backwardCode.edge ⟨V⟩ ⟨W⟩ = true ↔ (c.backwardCode.assemble ⟨V⟩).ctx = W
  rw [c.backwardCode.edge_eq_true_iff_target_eq]
  constructor
  · exact congrArg ContextCategoryObject.ctx
  · intro he
    cases c.backwardCode.assemble ⟨V⟩
    cases he
    rfl

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader
