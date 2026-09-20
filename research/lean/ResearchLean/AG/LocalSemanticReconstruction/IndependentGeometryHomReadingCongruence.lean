import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomOperationReadings
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomSignatureReadings
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomObservableReadings
import Formal.Util.AssertStandardAxioms

/-!
# Congruence of dependent Hom point readings

These comparison APIs expose the index dependence of the three existing
family readers. Equal activation rows and equal native data give equal full
candidate tables. Other common Hom roles play no part in these readings.
-/

namespace AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ReadingCongruence

noncomputable section

universe u v w z

open Site CategoryTheory

/-- Directed indexed reading depends only on its activation graph and native dependent function. -/
theorem indexed_function {I : Type u} {J : Type v} (p q : I → J → Bool)
    (hp : ∀ i, ∃! j, p i j = true) (hq : ∀ i, ∃! j, q i j = true) (he : p = q)
    (S : I → Type w) (T : J → Type z)
    (f : ∀ i, S i → T (IndependentIndexedCarrierGraph.index p hp i))
    (g : ∀ i, S i → T (IndependentIndexedCarrierGraph.index q hq i)) (hf : HEq f g) :
    IndependentIndexedCarrierGraph.read p hp S T f = IndependentIndexedCarrierGraph.read q hq S T g := by
  cases he
  cases hf
  rfl

/-- Candidate inverse reading depends only on its activation graph and native equivalence family. -/
theorem candidate_inverse (I : Type u) (J : Type v) (p q : I → J → Bool)
    (hp : ∀ i, ∃! j, p i j = true) (hq : ∀ i, ∃! j, q i j = true) (he : p = q)
    (S : I → Type w) (T : J → Type z)
    (f : ∀ i, S i ≃ T (IndependentIndexedCarrierGraph.index p hp i))
    (g : ∀ i, S i ≃ T (IndependentIndexedCarrierGraph.index q hq i)) (hf : HEq f g) :
    IndependentCandidateIndexedInverseGraph.read I J p S T hp f =
      IndependentCandidateIndexedInverseGraph.read I J q S T hq g := by
  cases he
  cases hf
  rfl

/-- Indexed ring reading depends only on its activation graph and native ring-equivalence family. -/
theorem indexed_ring {I : Type u} {J : Type v} (p q : I → J → Bool)
    (hp : ∀ i, ∃! j, p i j = true) (hq : ∀ i, ∃! j, q i j = true) (he : p = q)
    (S : I → Type w) (T : J → Type z) [∀ i, CommRing (S i)] [∀ j, CommRing (T j)]
    (f : ∀ i, S i ≃+* T (IndependentIndexedCarrierGraph.index p hp i))
    (g : ∀ i, S i ≃+* T (IndependentIndexedCarrierGraph.index q hq i)) (hf : HEq f g) :
    IndependentIndexedRingGraph.read p hp S T f = IndependentIndexedRingGraph.read q hq S T g := by
  cases he
  cases hf
  rfl

variable {U : AtomCarrier.{u}} {mode : Mode}

/-- Equal object rows and native operation families yield the same complete operation candidate reading. -/
theorem operation (h k : Table.{u, v} U mode) (hh : CoreLaws.ObjectRows h) (hk : CoreLaws.ObjectRows k)
    (he : ∀ A B, h (.object A B) = k (.object A B))
    (S T : ArchitectureObject U → ArchitectureObject U → Type u)
    (f : ∀ A B, S A B → T (CoreLaws.objectMap h hh A) (CoreLaws.objectMap h hh B))
    (g : ∀ A B, S A B → T (CoreLaws.objectMap k hk A) (CoreLaws.objectMap k hk B)) (hf : HEq f g) :
    (Operation.readingEquiv h hh S T f).val = (Operation.readingEquiv k hk S T g).val := by
  have hp : Operation.endpoints h = Operation.endpoints k := by
    funext p q
    exact congrArg₂ Bool.and (he p.1 q.1) (he p.2 q.2)
  have hm : CoreLaws.objectMap h hh = CoreLaws.objectMap k hk := by
    funext A
    exact ((CoreLaws.objectGraph k hk).target_eq_of_edge
      ((he A _).symm.trans ((CoreLaws.objectGraph h hh).edge_target A))).symm
  apply indexed_function (Operation.endpoints h) (Operation.endpoints k)
    (Operation.endpoints_total h hh) (Operation.endpoints_total k hk) hp (Operation.Fiber S) (Operation.Fiber T)
  apply Function.hfunext rfl
  intro p q hpq
  cases hpq
  apply Function.hfunext rfl
  intro x y hxy
  cases hxy
  have hs : (⟨CoreLaws.objectMap h hh, f⟩ :
      Σ M : ArchitectureObject U → ArchitectureObject U, ∀ A B, S A B → T (M A) (M B)) =
        ⟨CoreLaws.objectMap k hk, g⟩ := Sigma.ext hm hf
  have hv := congrArg (fun d : Σ M : ArchitectureObject U → ArchitectureObject U,
      ∀ A B, S A B → T (M A) (M B) =>
    (⟨d.1, d.2 p.1 p.2 x⟩ : Σ M : ArchitectureObject U → ArchitectureObject U, T (M p.1) (M p.2))) hs
  exact (cast_heq _ _).trans ((Sigma.mk.inj hv).2.trans (cast_heq _ _).symm)

/-- Equal axis rows and native coordinate families yield the same complete candidate inverse reading. -/
theorem signature (h k : Table.{u, v} U mode) (I J : Type u)
    (hh : IndependentCarrierGraph.IsLawful I J (signatureAxis h))
    (hk : IndependentCarrierGraph.IsLawful I J (signatureAxis k)) (he : signatureAxis h = signatureAxis k)
    (S : I → Type u) (T : J → Type u)
    (f : ∀ i, S i ≃ T (Signature.axisMap h I J hh i))
    (g : ∀ i, S i ≃ T (Signature.axisMap k I J hk i)) (hf : HEq f g) :
    (Signature.readingEquiv h I J hh S T f).val = (Signature.readingEquiv k I J hk S T g).val := by
  apply candidate_inverse I J (Signature.axisPoints h I J) (Signature.axisPoints k I J) hh.2 hk.2
    (funext fun i => funext fun j => congrFun he (.edge I J i j)) S T f g hf

/-- Equal context rows and native observable families yield the same complete candidate ring reading. -/
theorem observable {A B : ArchitectureObject U} (C : ContextPreorderCategory A) (D : ContextPreorderCategory B)
    (h k : Table.{u, v} U mode) (hh : Context.IsLawful C.le D.le (Context.points h A B))
    (hk : Context.IsLawful C.le D.le (Context.points k A B)) (he : Context.points h A B = Context.points k A B)
    (S : ArchCtx A → Type u) (T : ArchCtx B → Type u) [∀ W, CommRing (S W)] [∀ V, CommRing (T V)]
    (f : ∀ W : ContextCategoryObject C,
      S W.ctx ≃+* T (((Context.assemble C D (Context.points h A B) hh).functor.obj W).ctx))
    (g : ∀ W : ContextCategoryObject C,
      S W.ctx ≃+* T (((Context.assemble C D (Context.points k A B) hk).functor.obj W).ctx)) (hf : HEq f g) :
    (Observable.readingEquiv C D h hh S T f).val = (Observable.readingEquiv C D k hk S T g).val := by
  have hp : Observable.contextPoints h = Observable.contextPoints k := congrFun he .forward
  have hm : Context.assemble C D (Context.points h A B) hh = Context.assemble C D (Context.points k A B) hk :=
    congrArg (Context.readingEquiv C D).symm (Subtype.ext he)
  apply indexed_ring (Observable.contextPoints h) (Observable.contextPoints k) hh.forward hk.forward hp S T
  apply Function.hfunext rfl
  intro W V hWV
  cases hWV
  have hs : (⟨Context.assemble C D (Context.points h A B) hh, f⟩ :
      Σ E : ContextCategoryObject C ≌ ContextCategoryObject D,
        ∀ W : ContextCategoryObject C, S W.ctx ≃+* T ((E.functor.obj W).ctx)) =
      ⟨Context.assemble C D (Context.points k A B) hk, g⟩ := Sigma.ext hm hf
  have hv := congrArg (fun d : Σ E : ContextCategoryObject C ≌ ContextCategoryObject D,
      ∀ W : ContextCategoryObject C, S W.ctx ≃+* T ((E.functor.obj W).ctx) =>
    (⟨d.1, d.2 ⟨W⟩⟩ : Σ E : ContextCategoryObject C ≌ ContextCategoryObject D, S W ≃+* T ((E.functor.obj ⟨W⟩).ctx))) hs
  exact (cast_heq _ _).trans ((Sigma.mk.inj hv).2.trans (cast_heq _ _).symm)

end

end AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ReadingCongruence

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.ReadingCongruence
