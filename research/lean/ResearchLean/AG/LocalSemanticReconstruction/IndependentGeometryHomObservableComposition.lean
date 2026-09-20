import ResearchLean.AG.LocalSemanticReconstruction.IndependentIndexedInverseComposition
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomCompositionIndices
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomNativeFamilies
import Formal.Util.AssertStandardAxioms

/-!
# Direct observable composition on common context and value points

Implementation notes: primitive forward context rows select the intermediate
context, and the two observable inverse graphs compose at that context.
Native context wrapping and ring-family casts are compared by dependent Sigma
pairs. The native ring-equivalence composition verifies the directly defined
point table, retaining both inverse functions and all candidate rows.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive

noncomputable section

universe u v

open Site CategoryTheory AtomFoundation GeometryTransport IndependentGeometryTableAssembly

namespace Observable

variable {U : AtomCarrier.{u}} {A B E : ArchitectureObject U} {mode : Mode}
variable (C : ContextPreorderCategory A) (D : ContextPreorderCategory B) (F : ContextPreorderCategory E)
variable (h : Table.{u, v} U mode) (hc : Context.IsLawful C.le D.le (Context.points h A B))
variable (S : ArchCtx A → Type u) (M : ArchCtx B → Type u) (T : ArchCtx E → Type u)
variable [∀ W, CommRing (S W)] [∀ V, CommRing (M V)] [∀ Z, CommRing (T Z)]

/-- Observable assembly's context cast preserves the entire underlying inverse-fiber equivalence. -/
theorem assemble_toIndexed_heq (hh : IsLawful h S M) (W : ArchCtx A) : HEq
    (assemble C D h hc S M hh ⟨W⟩).toEquiv
    (IndependentIndexedInverseGraph.assemble (contextPoints h) hc.forward S M (points h A B) hh.graphs W) := by
  have he : (⟨((Context.assemble C D (Context.points h A B) hc).functor.obj ⟨W⟩).ctx,
      assemble C D h hc S M hh ⟨W⟩⟩ : Σ V : ArchCtx B, S W ≃+* M V) =
      ⟨IndependentIndexedCarrierGraph.index (contextPoints h) hc.forward W,
        IndependentIndexedRingGraph.assemble (contextPoints h) hc.forward S M (points h A B) hh W⟩ :=
    Sigma.ext (context_index_eq C D (Context.points h A B) hc W) (cast_heq _ _)
  have hv := congrArg (fun d : Σ V : ArchCtx B, S W ≃+* M V =>
    (⟨d.1, d.2.toEquiv⟩ : Σ V : ArchCtx B, S W ≃ M V)) he
  exact (Sigma.mk.inj hv).2

/-- Reindexing a native observable family changes no underlying inverse-fiber data. -/
theorem toIndexed_toEquiv_heq
    (g : ∀ W : ContextCategoryObject C, S W.ctx ≃+*
      M (((Context.assemble C D (Context.points h A B) hc).functor.obj W).ctx)) (W : ArchCtx A) : HEq
    (((nativeFamilyEquiv C D h hc S M).symm g) W).toEquiv (g ⟨W⟩).toEquiv := by
  have he : (⟨IndependentIndexedCarrierGraph.index (contextPoints h) hc.forward W,
      ((nativeFamilyEquiv C D h hc S M).symm g) W⟩ : Σ V : ArchCtx B, S W ≃+* M V) =
      ⟨((Context.assemble C D (Context.points h A B) hc).functor.obj ⟨W⟩).ctx, g ⟨W⟩⟩ :=
    Sigma.ext (context_index_eq C D (Context.points h A B) hc W).symm (cast_heq _ _)
  have hv := congrArg (fun d : Σ V : ArchCtx B, S W ≃+* M V =>
    (⟨d.1, d.2.toEquiv⟩ : Σ V : ArchCtx B, S W ≃ M V)) he
  exact (Sigma.mk.inj hv).2

variable (hh : IsLawful h S M) (k : Table.{u, v} U mode)
variable (kc : Context.IsLawful D.le F.le (Context.points k B E)) (hk : IsLawful k M T)

/-- Indexed primitive observable composition agrees with native composition at the actual intermediate context. -/
theorem indexed_comp_heq : HEq
    (fun W => (IndependentIndexedInverseGraph.assemble (contextPoints h) hc.forward S M (points h A B) hh.graphs W).trans
      (IndependentIndexedInverseGraph.assemble (contextPoints k) kc.forward M T (points k B E) hk.graphs
        (IndependentIndexedCarrierGraph.index (contextPoints h) hc.forward W)))
    (fun W : ArchCtx A => ((assemble C D h hc S M hh ⟨W⟩).trans
      (assemble D F k kc M T hk ((Context.assemble C D (Context.points h A B) hc).functor.obj ⟨W⟩))).toEquiv) := by
  apply Function.hfunext rfl
  intro W W' hWW'
  cases hWW'
  let V := IndependentIndexedCarrierGraph.index (contextPoints h) hc.forward W
  have hs : (⟨V, IndependentIndexedInverseGraph.assemble (contextPoints h) hc.forward S M (points h A B) hh.graphs W⟩ :
      Σ V : ArchCtx B, S W ≃ M V) =
      ⟨((Context.assemble C D (Context.points h A B) hc).functor.obj ⟨W⟩).ctx,
        (assemble C D h hc S M hh ⟨W⟩).toEquiv⟩ :=
    Sigma.ext (context_index_eq C D (Context.points h A B) hc W).symm
      (assemble_toIndexed_heq C D h hc S M hh W).symm
  have ht : (⟨IndependentIndexedCarrierGraph.index (contextPoints k) kc.forward V,
      IndependentIndexedInverseGraph.assemble (contextPoints k) kc.forward M T (points k B E) hk.graphs V⟩ :
      Σ Z : ArchCtx E, M V ≃ T Z) =
      ⟨((Context.assemble D F (Context.points k B E) kc).functor.obj ⟨V⟩).ctx,
        (assemble D F k kc M T hk ⟨V⟩).toEquiv⟩ :=
    Sigma.ext (context_index_eq D F (Context.points k B E) kc V).symm
      (assemble_toIndexed_heq D F k kc M T hk V).symm
  have ht' := congrArg (fun d : Σ Z : ArchCtx E, M V ≃ T Z =>
    (⟨d.1, (IndependentIndexedInverseGraph.assemble (contextPoints h) hc.forward S M (points h A B) hh.graphs W).trans d.2⟩ :
      Σ Z : ArchCtx E, S W ≃ T Z)) ht
  have hs' := congrArg (fun d : Σ V : ArchCtx B, S W ≃ M V =>
    (⟨((Context.assemble D F (Context.points k B E) kc).functor.obj ⟨d.1⟩).ctx,
      d.2.trans (assemble D F k kc M T hk ⟨d.1⟩).toEquiv⟩ : Σ Z : ArchCtx E, S W ≃ T Z)) hs
  exact (Sigma.mk.inj ht').2.trans (Sigma.mk.inj hs').2

end Observable

namespace NativeReader

variable {U : AtomCarrier.{u}} {G H : GeometryPackage.{u, v} U} (mode : Mode)
variable (f : PackageTotalHom G.core H.core) (a : G.Coefficient →+* H.Coefficient)

/-- The common native reader's indexed inverse family preserves each original observable ring-equivalence component. -/
theorem observableIndexedFamily_heq : HEq
    (fun W => (((Observable.nativeFamilyEquiv G.core.contextPreorder H.core.contextPreorder (indices mode f a)
      (context_rows mode f a) (fun W => G.core.equationSystem.Observable ⟨W⟩)
      (fun V => H.core.equationSystem.Observable ⟨V⟩)).symm (observableFamily mode f a)) W).toEquiv)
    (fun W : ArchCtx G.core.object => (f.upper.equationTransport.observableEquiv ⟨W⟩).toEquiv) := by
  apply Function.hfunext rfl
  intro W W' hWW'
  cases hWW'
  have hs : (⟨Context.assemble G.core.contextPreorder H.core.contextPreorder
      (Context.points (indices mode f a) G.core.object H.core.object) (context_rows mode f a), observableFamily mode f a⟩ :
      Σ E : ContextCategoryObject G.core.contextPreorder ≌ ContextCategoryObject H.core.contextPreorder,
        ∀ W, G.core.equationSystem.Observable W ≃+* H.core.equationSystem.Observable (E.functor.obj W)) =
      ⟨f.upper.equationTransport.contextEquivalence, f.upper.equationTransport.observableEquiv⟩ :=
    Sigma.ext (context_assemble_indices mode f a) (observableFamily_heq mode f a)
  have hv := congrArg (fun d : Σ E : ContextCategoryObject G.core.contextPreorder ≌ ContextCategoryObject H.core.contextPreorder,
      ∀ W, G.core.equationSystem.Observable W ≃+* H.core.equationSystem.Observable (E.functor.obj W) =>
    (⟨(d.1.functor.obj ⟨W⟩).ctx, (d.2 ⟨W⟩).toEquiv⟩ : Σ V : ArchCtx H.core.object,
      G.core.equationSystem.Observable ⟨W⟩ ≃ H.core.equationSystem.Observable ⟨V⟩)) hs
  exact (Observable.toIndexed_toEquiv_heq G.core.contextPreorder H.core.contextPreorder (indices mode f a)
    (context_rows mode f a) (fun W => G.core.equationSystem.Observable ⟨W⟩)
    (fun V => H.core.equationSystem.Observable ⟨V⟩) (observableFamily mode f a) W).trans (Sigma.mk.inj hv).2

end NativeReader

namespace Composition

variable {U : AtomCarrier.{u}} {mode : Mode} (s t r : ObjectData.{u, v} U)
variable (p : InvariantWitness.Local.{u, v}
  (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading mode)
variable (hp : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p).table)
variable (q : InvariantWitness.Local.{u, v}
  (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading mode)
variable (hq : PackageAssembly.PointLaws t.1 r.1 (PackageAssembly.retained t.1 r.1 q).table)

/-- Compose observable point graphs at the first primitive forward-context image. -/
def observableRows : IndependentIndexedInverseGraph.Table.{u + 1, u + 1, u, u}
    (ArchCtx (assemble s).core.object) (ArchCtx (assemble r).core.object) := by
  letI := ObservableNatural.rings (s.1.val.2.2.1.val) (s.1.val.2.2.1.property.choose) (s.1.val.2.2.1.property.choose_spec)
  letI := ObservableNatural.rings (t.1.val.2.2.1.val) (t.1.val.2.2.1.property.choose) (t.1.val.2.2.1.property.choose_spec)
  letI := ObservableNatural.rings (r.1.val.2.2.1.val) (r.1.val.2.2.1.property.choose) (r.1.val.2.2.1.property.choose_spec)
  exact IndependentIndexedInverseGraph.composeRows
    (Observable.contextPoints (PackageAssembly.retained s.1 t.1 p).table) hp.contextRows.forward
    (fun W => (assemble s).core.equationSystem.Observable ⟨W⟩)
    (fun V => (assemble t).core.equationSystem.Observable ⟨V⟩)
    (fun Z => (assemble r).core.equationSystem.Observable ⟨Z⟩)
    (Observable.points (PackageAssembly.retained s.1 t.1 p).table (assemble s).core.object (assemble t).core.object)
    hp.observableRows.graphs (Observable.contextPoints (PackageAssembly.retained t.1 r.1 q).table)
    (Observable.points (PackageAssembly.retained t.1 r.1 q).table (assemble t).core.object (assemble r).core.object)
    hq.observableRows.graphs

/-- The forward context graph of the direct common composition is exactly the observable activation graph. -/
theorem observable_indices (cp : GeometryComponents.CoefficientPoints s t p) :
    IndependentIndexedCarrierGraph.composeIndex (Observable.contextPoints (PackageAssembly.retained s.1 t.1 p).table)
      hp.contextRows.forward (Observable.contextPoints (PackageAssembly.retained t.1 r.1 q).table) =
      Observable.contextPoints (indices s t r p hp q hq cp)
        (A := (assemble s).core.object) (B := (assemble r).core.object) := by
  funext W Z
  exact (NativeReader.liftDependent_active mode _ _ (dependentIndices s t r p hp q hq) (.context .forward W Z)).symm

set_option maxHeartbeats 800000 in
/-- Both directions of each direct observable row equal the common reader of native ring-equivalence composition. -/
theorem observableRows_eq_native (cp : GeometryComponents.CoefficientPoints s t p)
    (cq : GeometryComponents.CoefficientPoints t r q) : observableRows s t r p hp q hq =
    NativeReader.observableRows mode
      (PackageTotalHom.comp (GeometryComponents.base s t p hp) (GeometryComponents.base t r q hq))
      ((GeometryComponents.coefficientMap t r q cq).comp (GeometryComponents.coefficientMap s t p cp)) := by
  letI := ObservableNatural.rings (s.1.val.2.2.1.val) (s.1.val.2.2.1.property.choose) (s.1.val.2.2.1.property.choose_spec)
  letI := ObservableNatural.rings (t.1.val.2.2.1.val) (t.1.val.2.2.1.property.choose) (t.1.val.2.2.1.property.choose_spec)
  letI := ObservableNatural.rings (r.1.val.2.2.1.val) (r.1.val.2.2.1.property.choose) (r.1.val.2.2.1.property.choose_spec)
  let h := (PackageAssembly.retained s.1 t.1 p).table
  let k := (PackageAssembly.retained t.1 r.1 q).table
  let S := fun W => (assemble s).core.equationSystem.Observable ⟨W⟩
  let M := fun V => (assemble t).core.equationSystem.Observable ⟨V⟩
  let T := fun Z => (assemble r).core.equationSystem.Observable ⟨Z⟩
  let pi := Observable.contextPoints h (A := (assemble s).core.object) (B := (assemble t).core.object)
  let qi := Observable.contextPoints k (A := (assemble t).core.object) (B := (assemble r).core.object)
  let ht := Observable.points h (assemble s).core.object (assemble t).core.object
  let kt := Observable.points k (assemble t).core.object (assemble r).core.object
  let ci := IndependentIndexedCarrierGraph.composeIndex pi hp.contextRows.forward qi
  let hi := IndependentIndexedCarrierGraph.composeIndex_total pi hp.contextRows.forward qi hq.contextRows.forward
  let ct := observableRows s t r p hp q hq
  let hc := IndependentIndexedInverseGraph.composeRows_isLawful pi hp.contextRows.forward S M T ht hp.observableRows.graphs qi kt hq.observableRows.graphs
  let f := PackageTotalHom.comp (GeometryComponents.base s t p hp) (GeometryComponents.base t r q hq)
  let a := (GeometryComponents.coefficientMap t r q cq).comp (GeometryComponents.coefficientMap s t p cp)
  have he : ci = Observable.contextPoints (NativeReader.indices mode f a) :=
    (observable_indices s t r p hp q hq cp).trans
      (congrArg (fun h => Observable.contextPoints h (A := (assemble s).core.object) (B := (assemble r).core.object))
        (indices_eq_native s t r p hp q hq cp cq))
  let g := fun W => (((Observable.nativeFamilyEquiv (assemble s).core.contextPreorder (assemble r).core.contextPreorder
      (NativeReader.indices mode f a) (NativeReader.context_rows mode f a) S T).symm
      (NativeReader.observableFamily mode f a)) W).toEquiv
  have hf : HEq (IndependentIndexedInverseGraph.assemble ci hi S T ct hc) g :=
    (IndependentIndexedInverseGraph.assemble_composeRows_heq pi hp.contextRows.forward S M T ht hp.observableRows.graphs
      qi kt hq.observableRows.graphs hq.contextRows.forward).trans
        ((Observable.indexed_comp_heq (assemble s).core.contextPreorder (assemble t).core.contextPreorder (assemble r).core.contextPreorder
          h hp.contextRows S M T hp.observableRows k hq.contextRows hq.observableRows).trans
          (NativeReader.observableIndexedFamily_heq mode f a).symm)
  exact (IndependentIndexedInverseGraph.read_assemble ci hi S T ct hc).symm.trans
    (IndependentIndexedInverseGraph.read_eq_of_heq ci (Observable.contextPoints (NativeReader.indices mode f a))
      hi (NativeReader.context_rows mode f a).forward he S T _ g hf)

end Composition

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Observable
#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.NativeReader
#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition
