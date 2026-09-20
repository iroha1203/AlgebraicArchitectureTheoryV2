import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomOperationComposition
import ResearchLean.AG.LocalSemanticReconstruction.IndependentGeometryHomFullSeparation
import Formal.Util.AssertStandardAxioms

/-!
# Finite input fragments for common operation composition

The primitive index composition uses one middle index. Its dependent value
composition uses at most two carrier-graph cells. On the common Hom declaration
the endpoint index expands to two object cells, so at most four input cells
suffice for each operation output. The final theorem states this on the actual
finite fragments of the invariant quotient, after auxiliary witness erasure.
-/

namespace AAT.AG.LocalSemanticReconstruction

noncomputable section

universe u v w x y z

namespace IndependentIndexedCarrierGraph

variable {I : Type u} {J : Type v} {K : Type w}
variable (p : I → J → Bool) (hp : ∀ i, ∃! j, p i j = true)
variable (S : I → Type x) (M : J → Type y) (T : K → Type z)
variable (h : Table.{u, v, x, y} I J) (hh : IsLawful p S M h) (k : Table.{v, w, y, z} J K)

/-- Direct dependent composition can use any true first index pair, by uniqueness of that primitive row. -/
theorem composeRows_at_pair (i : I) (j : J) (l : K) (hij : p i j = true) (q : IndependentCarrierGraph.Query.{x, z}) :
    composeRows p hp S M T h hh k (.edge i l q) =
      IndependentCarrierGraph.compose (S i) (M j) (T l) (row h i j) (hh.active i j hij) (row k j l) q := by
  have he := (active_iff p hp i j).1 hij
  subst j
  rfl

/-- One index cell and at most two value cells determine every composed dependent candidate query. -/
theorem composeRows_finite_support (q : Query.{u, w, x, z} I K) :
    ∃ (D : Finset (I × J)) (E : Finset (Query.{u, v, x, y} I J)) (F : Finset (Query.{v, w, y, z} J K)),
      D.card ≤ 1 ∧ E.card + F.card ≤ 2 ∧
      ∀ (p' : I → J → Bool) (hp' : ∀ i, ∃! j, p' i j = true)
        (h' : Table.{u, v, x, y} I J) (hh' : IsLawful p' S M h') (k' : Table.{v, w, y, z} J K),
        (∀ a ∈ D, p a.1 a.2 = p' a.1 a.2) →
        (∀ a ∈ E, h a = h' a) → (∀ a ∈ F, k a = k' a) →
        composeRows p hp S M T h hh k q = composeRows p' hp' S M T h' hh' k' q := by
  classical
  cases q with
  | edge i l q =>
    let j := index p hp i
    have hij : p i j = true := (active_iff p hp i j).2 rfl
    obtain ⟨E, F, hcard, he⟩ := IndependentCarrierGraph.compose_finite_support
      (S i) (M j) (T l) (row h i j) (hh.active i j hij) (row k j l) q
    refine ⟨{(i, j)}, E.image (Query.edge i j), F.image (Query.edge j l), by simp, ?_, ?_⟩
    · exact (Nat.add_le_add Finset.card_image_le Finset.card_image_le).trans hcard
    · intro p' hp' h' hh' k' hD hE hF
      have hij' : p' i j = true := (hD (i, j) (by simp)).symm.trans hij
      have hv := he (row h' i j) (hh'.active i j hij') (row k' j l)
        (fun a ha => hE (.edge i j a) (Finset.mem_image_of_mem _ ha))
        (fun a ha => hF (.edge j l a) (Finset.mem_image_of_mem _ ha))
      exact (composeRows_at_pair p hp S M T h hh k i j l hij q).trans
        (hv.trans (composeRows_at_pair p' hp' S M T h' hh' k' i j l hij' q).symm)

end IndependentIndexedCarrierGraph

namespace IndependentGeometryHomPrimitive.Composition

open Site AtomFoundation GeometryTransport IndependentGeometryTableAssembly

variable {U : AtomCarrier.{u}} {mode : Mode} (s t r : ObjectData.{u, v} U)
variable (p : InvariantWitness.Local.{u, v}
  (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading mode)
variable (hp : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p).table)
variable (q : InvariantWitness.Local.{u, v}
  (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading mode)

/-- At most four common query cells fix each operation-composition output for all lawful comparison inputs. -/
theorem operationRows_finite_support
    (a : IndependentIndexedCarrierGraph.Query.{u + 1, u + 1, u, u}
      (ArchitectureObject U × ArchitectureObject U) (ArchitectureObject U × ArchitectureObject U)) :
    ∃ (D E : Finset (Query.{u, v} U mode)), D.card + E.card ≤ 4 ∧
      ∀ (p' : InvariantWitness.Local.{u, v}
          (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading mode)
        (hp' : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p').table)
        (q' : InvariantWitness.Local.{u, v}
          (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading mode),
        (∀ a ∈ D, (PackageAssembly.retained s.1 t.1 p).table a = (PackageAssembly.retained s.1 t.1 p').table a) →
        (∀ a ∈ E, (PackageAssembly.retained t.1 r.1 q).table a = (PackageAssembly.retained t.1 r.1 q').table a) →
        operationRows s t r p hp q a = operationRows s t r p' hp' q' a := by
  classical
  let h := (PackageAssembly.retained s.1 t.1 p).table
  let k := (PackageAssembly.retained t.1 r.1 q).table
  obtain ⟨D, E, F, hD, hEF, hs⟩ := IndependentIndexedCarrierGraph.composeRows_finite_support
    (Operation.endpoints h) (Operation.endpoints_total h (PackageAssembly.retained s.1 t.1 p).objectRows)
    (Operation.Fiber (assemble s).core.reading.operationReading.Op)
    (Operation.Fiber (assemble t).core.reading.operationReading.Op)
    (Operation.Fiber (assemble r).core.reading.operationReading.Op)
    (Operation.points h) hp.operationRows (Operation.points k) a
  let left : (ArchitectureObject U × ArchitectureObject U) × (ArchitectureObject U × ArchitectureObject U) → Query.{u, v} U mode :=
    fun a => .object a.1.1 a.2.1
  let right : (ArchitectureObject U × ArchitectureObject U) × (ArchitectureObject U × ArchitectureObject U) → Query.{u, v} U mode :=
    fun a => .object a.1.2 a.2.2
  let op : IndependentIndexedCarrierGraph.Query.{u + 1, u + 1, u, u}
      (ArchitectureObject U × ArchitectureObject U) (ArchitectureObject U × ArchitectureObject U) → Query.{u, v} U mode
    | .edge (A, B) (A', B') a => .operation A B A' B' a
  refine ⟨(D.image left ∪ D.image right) ∪ E.image op, F.image op, ?_, ?_⟩
  · have hl := Finset.card_image_le (s := D) (f := left)
    have hr := Finset.card_image_le (s := D) (f := right)
    have he := Finset.card_image_le (s := E) (f := op)
    have hf := Finset.card_image_le (s := F) (f := op)
    have hu := Finset.card_union_le (D.image left) (D.image right)
    have hv := Finset.card_union_le (D.image left ∪ D.image right) (E.image op)
    omega
  · intro p' hp' q' hd he
    apply hs (Operation.endpoints (PackageAssembly.retained s.1 t.1 p').table)
      (Operation.endpoints_total _ (PackageAssembly.retained s.1 t.1 p').objectRows)
      (Operation.points (PackageAssembly.retained s.1 t.1 p').table) hp'.operationRows
      (Operation.points (PackageAssembly.retained t.1 r.1 q').table)
    · intro a ha
      exact congrArg₂ Bool.and
        (hd (left a) (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha))))
        (hd (right a) (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha))))
    · intro a ha
      have hv := hd (op a) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha))
      cases a with
      | edge i j a => exact hv
    · intro a ha
      have hv := he (op a) (Finset.mem_image_of_mem _ ha)
      cases a with
      | edge i j a => exact hv

/-- Actual finite fragments after witness erasure determine each operation output, using at most four cells. -/
theorem operationRows_finite_fragment
    (a : IndependentIndexedCarrierGraph.Query.{u + 1, u + 1, u, u}
      (ArchitectureObject U × ArchitectureObject U) (ArchitectureObject U × ArchitectureObject U)) :
    ∃ (D E : Finset (Query.{u, v} U mode)), D.card + E.card ≤ 4 ∧
      ∀ (p' : InvariantWitness.Local.{u, v}
          (assemble s).core.reading.invariantReading (assemble t).core.reading.invariantReading mode)
        (hp' : PackageAssembly.PointLaws s.1 t.1 (PackageAssembly.retained s.1 t.1 p').table)
        (q' : InvariantWitness.Local.{u, v}
          (assemble t).core.reading.invariantReading (assemble r).core.reading.invariantReading mode),
        InvariantWitness.fragment _ _ p D = InvariantWitness.fragment _ _ p' D →
        InvariantWitness.fragment _ _ q E = InvariantWitness.fragment _ _ q' E →
        operationRows s t r p hp q a = operationRows s t r p' hp' q' a := by
  obtain ⟨D, E, hcard, hs⟩ := operationRows_finite_support s t r p hp q a
  refine ⟨D, E, hcard, ?_⟩
  intro p' hp' q' hD hE
  apply hs p' hp' q'
  · intro a ha
    exact (NativeReader.local_fragment_point _ _ p D ⟨a, ha⟩).symm.trans
      ((congrFun hD ⟨a, ha⟩).trans (NativeReader.local_fragment_point _ _ p' D ⟨a, ha⟩))
  · intro a ha
    exact (NativeReader.local_fragment_point _ _ q E ⟨a, ha⟩).symm.trans
      ((congrFun hE ⟨a, ha⟩).trans (NativeReader.local_fragment_point _ _ q' E ⟨a, ha⟩))

end IndependentGeometryHomPrimitive.Composition

end

end AAT.AG.LocalSemanticReconstruction

#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentIndexedCarrierGraph
#assert_standard_axioms_only AAT.AG.LocalSemanticReconstruction.IndependentGeometryHomPrimitive.Composition
