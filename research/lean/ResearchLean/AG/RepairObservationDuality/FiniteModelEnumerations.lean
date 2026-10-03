import ResearchLean.AG.RepairObservationDuality.FiniteFullCoordinates
import ResearchLean.AG.RelativeRepairComposition.FiniteFunctionEnumeration
import Mathlib.LinearAlgebra.Dimension.Free
/-!
# G-131 D: generating the finite known parameter and whole-source lists

## Implementation notes

Parameter values are enumerated from full basis coordinates and the finite
field list. Every original nonfixed edge and selected whole candidate basis
coordinate occurs in the source list. A finite-dimensional abstract model
can obtain its full basis by Mathlib's existence construction; this is known
model preparation, not online value acquisition. The ensuing finite searches
consume explicit lists and contain no choice of missing replies or answers.
-/
namespace AAT.AG.RepairObservationDuality.FiniteModelEnumerations
open TransportCoherence AbelianLiftingObstruction RelativeRepairComposition
variable {k V : Type*} [Field k] [DecidableEq k] [AddCommGroup V] [Module k V]

/-- D's full finite coordinate index list is generated without quotient-to-list choice. -/
def finEnumeration (d : Nat) : FiniteElimination.Enumeration (Fin d) :=
  ⟨List.finRange d,by intro j; exact List.mem_finRange j⟩

/-- Every original full basis coordinate is present in the generated index list. -/
theorem finEnumeration_mem (d : Nat) (j : Fin d) : j ∈ (finEnumeration d).values :=
  (finEnumeration d).complete j

/-- D enumerates the complete parameter space from known full input coordinates and the field list. -/
def parameterEnumeration (enumK : FiniteElimination.Enumeration k) {d : Nat}
    (coordinate : V ≃ₗ[k] (Fin d → k)) : FiniteElimination.Enumeration V where
  values := ((finEnumeration d).pi (fun _ => enumK)).values.map coordinate.symm
  complete v := List.mem_map.mpr ⟨coordinate v,
    ((finEnumeration d).pi (fun _ => enumK)).complete (coordinate v),coordinate.symm_apply_apply v⟩

omit [DecidableEq k] in
/-- The parameter list covers every full input, not merely those matching a chosen RHS or successful repair. -/
theorem parameterEnumeration_mem (enumK : FiniteElimination.Enumeration k) {d : Nat}
    (coordinate : V ≃ₗ[k] (Fin d → k)) (v : V) :
    v ∈ (parameterEnumeration enumK coordinate).values :=
  (parameterEnumeration enumK coordinate).complete v

/-- D's abstract finite-dimensional model supplies a complete parameter list using a full Mathlib basis. -/
noncomputable def finiteDimensionalParameters [FiniteDimensional k V]
    (enumK : FiniteElimination.Enumeration k) : FiniteElimination.Enumeration V :=
  parameterEnumeration enumK (Module.finBasis k V).equivFun

omit [DecidableEq k] in
/-- Known model preparation discharges parameter-list completeness from finite-dimensionality and the field list. -/
theorem finiteDimensionalParameters_mem [FiniteDimensional k V]
    (enumK : FiniteElimination.Enumeration k) (v : V) :
    v ∈ (finiteDimensionalParameters (V := V) enumK).values :=
  (finiteDimensionalParameters (V := V) enumK).complete v

universe uk uG uA
variable {k' : Type uk} [Field k']
variable {K : FiniteTransportPresentation.{uG}} (M : LocalCoefficients.{uG,uA} K)
variable [∀ v, Module k' (M.A v)]
variable (bases : FiniteFamily.Bases (k := k') M.A) (P : ClosedRegion K)
variable (candidates : Set (EdgeName (K := K))) (S : Set candidates)
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ candidates)] [DecidablePred (· ∈ S)]

/-- D's source list retains all original always coordinates and every complete selected candidate basis coordinate. -/
def fullSourceEnumeration (enumEdges : FiniteElimination.Enumeration (EdgeName (K := K))) :
    FiniteElimination.Enumeration (FiniteFullCoordinates.Index (k := k') M bases P candidates S) where
  values :=
    ((FiniteFamily.indexEnumeration (fun e : EdgeName (K := K) => M.A e.2.1)
      (bases.comap M.A (fun e : EdgeName (K := K) => e.2.1)) Set.univ
        (P.edges ∪ candidates) enumEdges).values.map Sum.inl) ++
    (((enumEdges.subtype (· ∈ candidates)).subtype (· ∈ S)).values.flatMap fun e =>
      (List.finRange (bases.dimension e.1.1.2.1)).map fun j => Sum.inr ⟨e,j⟩)
  complete j := by
    cases j with
    | inl j =>
      apply List.mem_append_left
      exact List.mem_map.mpr ⟨j,(FiniteFamily.indexEnumeration _ _ _ _ enumEdges).complete j,rfl⟩
    | inr j =>
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      exact ⟨j.1,((enumEdges.subtype (· ∈ candidates)).subtype (· ∈ S)).complete j.1,
        List.mem_map.mpr ⟨j.2,List.mem_finRange j.2,rfl⟩⟩

/-- The full generated source list covers every original named correction coordinate. -/
theorem fullSourceEnumeration_mem
    (enumEdges : FiniteElimination.Enumeration (EdgeName (K := K)))
    (j : FiniteFullCoordinates.Index (k := k') M bases P candidates S) :
    j ∈ (fullSourceEnumeration M bases P candidates S enumEdges).values :=
  (fullSourceEnumeration M bases P candidates S enumEdges).complete j

end AAT.AG.RepairObservationDuality.FiniteModelEnumerations
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.FiniteModelEnumerations
