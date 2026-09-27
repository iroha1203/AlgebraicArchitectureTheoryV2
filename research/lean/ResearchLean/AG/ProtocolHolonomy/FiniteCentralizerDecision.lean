import ResearchLean.AG.ProtocolHolonomy.FiniteDirectDecision
import ResearchLean.AG.ProtocolHolonomy.VerticalCentralizer
import Formal.Util.AssertStandardAxioms

/-!
# Finite centralizers of original named-edge holonomy generators

For supplied root paths, component equality decision, and explicit edge and
root-fiber tables, enumerate all root permutations and check commutation with
every original named-edge B1 generator in one component. The resulting list
contains exactly the B2 centralizer elements at that root. Producing root
paths and component equality decisions from the finite graph tables is a
separate E obligation.
-/

namespace AAT.AG.ProtocolHolonomy

open AAT.AG.RealizationReconstruction

universe u v w

namespace ReversibleData

variable {Q : FixedFDirectedMultigraph.{u, v}}
  (D : ReversibleData.{u, v, w} Q)
  (R : RootedPaths Q) (j : FixedFComponent Q)

abbrev RootCandidateMaps :=
  (D.Fiber (R.root j) → D.Fiber (R.root j)) ×
    (D.Fiber (R.root j) → D.Fiber (R.root j))

def ValidCentralizerCandidate (f : D.RootCandidateMaps R j) : Prop :=
  (∀ x, f.2 (f.1 x) = x) ∧
  (∀ x, f.1 (f.2 x) = x) ∧
  (∀ (e : Q.Edge) (he : fixedFComponentMk Q (Q.source e) = j)
      (x : D.Fiber (R.root j)),
    f.1 (D.edgeMonodromyAt R j e he x) =
      D.edgeMonodromyAt R j e he (f.1 x))

def centralizerOfValidCandidate (f : D.RootCandidateMaps R j)
    (hf : D.ValidCentralizerCandidate R j f) :
    Subgroup.centralizer (D.holonomy R j :
      Set (Equiv.Perm (D.Fiber (R.root j)))) := by
  let a : Equiv.Perm (D.Fiber (R.root j)) :=
    { toFun := f.1, invFun := f.2, left_inv := hf.1,
      right_inv := hf.2.1 }
  refine ⟨a, ?_⟩
  change a ∈ Subgroup.centralizer
    (Subgroup.closure {m | ∃ (e : Q.Edge)
      (he : fixedFComponentMk Q (Q.source e) = j),
      m = D.edgeMonodromyAt R j e he} : Set _)
  rw [Subgroup.centralizer_closure]
  apply Subgroup.mem_centralizer_iff.mpr
  rintro m ⟨e, he, rfl⟩
  apply Equiv.ext
  intro x
  simpa [Equiv.Perm.mul_def, a] using (hf.2.2 e he x).symm

theorem validCentralizerCandidate_of_mem
    (a : Subgroup.centralizer (D.holonomy R j :
      Set (Equiv.Perm (D.Fiber (R.root j))))) :
    D.ValidCentralizerCandidate R j
      ⟨a.1, a.1.symm⟩ := by
  refine ⟨a.1.symm_apply_apply, a.1.apply_symm_apply, ?_⟩
  intro e he x
  have hm := D.edgeMonodromyAt_mem_holonomy R j e he
  have hc := (Subgroup.mem_centralizer_iff.mp a.2) _ hm
  have h := congrArg (fun p : Equiv.Perm (D.Fiber (R.root j)) => p x) hc
  simpa [Equiv.Perm.mul_def] using h.symm

section Finite

variable [Fintype Q.Edge] [Fintype (D.Fiber (R.root j))]
  [DecidableEq (D.Fiber (R.root j))]
  [DecidableEq (FixedFComponent Q)]

instance (f : D.RootCandidateMaps R j) :
    Decidable (D.ValidCentralizerCandidate R j f) := by
  unfold ValidCentralizerCandidate
  infer_instance

def rootCandidateTables
    (fiber : ExplicitEnumeration (D.Fiber (R.root j))) :
    ExplicitEnumeration (D.RootCandidateMaps R j) :=
  (ExplicitEnumeration.pi fiber (fun _ => fiber)).product
    (ExplicitEnumeration.pi fiber (fun _ => fiber))

end Finite

def finiteRootCentralizers
    [DecidableEq Q.Edge]
    [DecidableEq (D.Fiber (R.root j))]
    [DecidableEq (FixedFComponent Q)]
    (edges : ExplicitEnumeration Q.Edge)
    (fiber : ExplicitEnumeration (D.Fiber (R.root j))) :
    List (Subgroup.centralizer (D.holonomy R j :
      Set (Equiv.Perm (D.Fiber (R.root j))))) := by
  letI : Fintype Q.Edge := edges.toFintype
  letI : Fintype (D.Fiber (R.root j)) := fiber.toFintype
  exact (D.rootCandidateTables R j fiber).values.filterMap fun f =>
    if hf : D.ValidCentralizerCandidate R j f then
      some (D.centralizerOfValidCandidate R j f hf)
    else none

theorem centralizer_mem_finiteRootCentralizers
    [DecidableEq Q.Edge]
    [DecidableEq (D.Fiber (R.root j))]
    [DecidableEq (FixedFComponent Q)]
    (edges : ExplicitEnumeration Q.Edge)
    (fiber : ExplicitEnumeration (D.Fiber (R.root j)))
    (a : Subgroup.centralizer (D.holonomy R j :
      Set (Equiv.Perm (D.Fiber (R.root j))))) :
    a ∈ D.finiteRootCentralizers R j edges fiber := by
  let f : D.RootCandidateMaps R j := ⟨a.1, a.1.symm⟩
  have hf : D.ValidCentralizerCandidate R j f :=
    D.validCentralizerCandidate_of_mem R j a
  have heq : D.centralizerOfValidCandidate R j f hf = a := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    rfl
  unfold finiteRootCentralizers
  apply List.mem_filterMap.mpr
  exact ⟨f, (D.rootCandidateTables R j fiber).complete f, by simp [hf, heq]⟩

end ReversibleData
end AAT.AG.ProtocolHolonomy

#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.centralizerOfValidCandidate
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.validCentralizerCandidate_of_mem
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.rootCandidateTables
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.finiteRootCentralizers
#print axioms AAT.AG.ProtocolHolonomy.ReversibleData.centralizer_mem_finiteRootCentralizers
#assert_standard_axioms_only AAT.AG.ProtocolHolonomy
