import ResearchLean.AG.RelativeRepairComposition.GeneratedBoundaryRelation
import ResearchLean.AG.RelativeRepairComposition.NativeAffineFiniteInput
import ResearchLean.AG.RelativeRepairComposition.NativeAffineRanges
import ResearchLean.AG.RelativeRepairComposition.NativeAffineCorrection
import ResearchLean.AG.RelativeRepairComposition.SupportedNativeEquation

/-!
# The generated C relation is the actual affine boundary range

The whole original translation kernels use their full standard coordinates.
Private edges are exactly the nonshared always edges. Original candidates remain
public until their zero conditions are imposed and shared projection eliminates
the internal candidates. Every statement quantifies the same allowed range S.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uG
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k] (d : Nat)
variable (K : FiniteTransportPresentation.{uG})
variable (L R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k (Fin d → k))
variable (c : K.TwoCell → (Fin d → k))
variable (hfaces : ∀ f : K.TwoCell,
  (GroupExtension.pathValue K R (K.twoLeft f)).linear =
    (GroupExtension.pathValue K R (K.twoRight f)).linear)
variable (P W : ClosedRegion K)
variable [DecidablePred (· ∈ P.vertices)] [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable [DecidablePred (· ∈ W.edges)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (hfixed : ∀ f ∈ P.faces,
  translation (k := k) (c f) * GroupExtension.pathValue K R (K.twoLeft f) =
    GroupExtension.pathValue K R (K.twoRight f))
variable [DecidableEq K.Vertex] [DecidableEq (EdgeName (K := K))] [DecidableEq K.TwoCell]
variable (ek : FiniteElimination.Enumeration k)
variable (ee : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (ef : FiniteElimination.Enumeration K.TwoCell)
local notation "T" => tower K L R c hfaces
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (tower K L R c hfaces))
local notation "B" => standardBases d K L R c hfaces
local notation "lin" => edge_linear K L R c hfaces
local notation "fix" => fixed_native K L R c hfaces P hfixed
local notation "delta" => ActualEquation.defectFamily (T) P fix

/-- Only nonshared always edges are private; every original candidate is retained before projection. -/
def privateNonshared : Set (EdgeName (K := K)) :=
  {e | e ∉ W.edges ∧ e ∉ P.edges ∧ e ∉ candidates}

local notation "private" => privateNonshared K P W candidates

/-- The full original region has decidable membership at each vertex. -/
local instance allVerticesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).vertices) :=
  fun _ => isTrue trivial
/-- The full original region has decidable membership at each named edge. -/
local instance allEdgesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).edges) :=
  fun _ => isTrue trivial
/-- The full original region has decidable membership at every authored face. -/
local instance allFacesDecidable : DecidablePred (· ∈ (ClosedRegion.all (K := K)).faces) :=
  fun _ => isTrue trivial
/-- Private membership is determined by the three original shared/fixed/candidate conditions. -/
local instance privateEdgesDecidable : DecidablePred (· ∈ privateNonshared K P W candidates) :=
  fun e => inferInstanceAs (Decidable (e ∉ W.edges ∧ e ∉ P.edges ∧ e ∉ candidates))

/-- Every generated boundary coefficient is evaluated in the whole original real translation vector. -/
noncomputable def boundaryVector (u : ∀ e : W.edges, (M).A e.1.2.1) : W.edges → (Fin d → k) :=
  fun e => coefficient K L R c hfaces e.1.2.1 (u e)

/-- Same matrix-generated public C after candidate zero and shared projection, evaluated in actual vectors. -/
def generatedBoundary (allowed : Set (EdgeName (K := K))) : Set (W.edges → (Fin d → k)) :=
  boundaryVector d K L R c hfaces W ''
    FiniteNative.BoundaryRelation (M) B ClosedRegion.all P private lin delta ek ee ef
      W (ClosedRegion.to_all W) candidates allowed

variable (allowed : Set (EdgeName (K := K)))
local notation "fixed" => fixedEdgesForRange P.edges candidates allowed
local notation "Q" => repairEquivalence K L R c hfaces fixed

/-- Independent actual affine repairs and supported original equations have full inverse coordinates. -/
noncomputable def boundaryEquationEquiv : Repair K R c fixed ≃
    SupportedEquation.Objects (M) P ClosedRegion.all candidates allowed delta :=
  (Q).symm.trans (SupportedNativeEquation.repairEquiv (T) P candidates allowed fix)

omit [Fintype k] [DecidableEq k] [DecidablePred (· ∈ P.vertices)]
  [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)] [DecidablePred (· ∈ candidates)]
  [DecidableEq K.Vertex] [DecidableEq (EdgeName (K := K))] [DecidableEq K.TwoCell] in
/-- The same original edge correction is retained by the independent real-to-equation map. -/
theorem boundary_equation_value (s : Repair K R c fixed) (e : EdgeName (K := K)) :
    coefficient K L R c hfaces e.2.1
      ((boundaryEquationEquiv d K L R c hfaces P candidates hfixed allowed s).1.1.1
        ⟨e,Set.mem_univ e⟩) = realCorrection K R c fixed s e := by
  change coefficient K L R c hfaces e.2.1
    ((SupportedNativeEquation.repairEquiv (T) P candidates allowed fix ((Q).symm s)).1.1.1
      ⟨e,Set.mem_univ e⟩) = _
  rw [SupportedNativeEquation.repair_value]
  have h := real_correction_native K L R c hfaces fixed ((Q).symm s) e
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

omit [Fintype k] [DecidableEq k] [DecidablePred (· ∈ P.vertices)]
  [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)] [DecidablePred (· ∈ candidates)]
  [DecidableEq K.Vertex] [DecidableEq (EdgeName (K := K))] [DecidableEq K.TwoCell] in
/-- The inverse equation map reconstructs the complete actual correction at the same original edge. -/
theorem boundary_equation_inverse_value
    (h : SupportedEquation.Objects (M) P ClosedRegion.all candidates allowed delta)
    (e : EdgeName (K := K)) :
    realCorrection K R c fixed
      ((boundaryEquationEquiv d K L R c hfaces P candidates hfixed allowed).symm h) e =
      coefficient K L R c hfaces e.2.1 (h.1.1.1 ⟨e,Set.mem_univ e⟩) := by
  have hv := boundary_equation_value d K L R c hfaces P candidates hfixed allowed
    ((boundaryEquationEquiv d K L R c hfaces P candidates hfixed allowed).symm h) e
  rw [Equiv.apply_symm_apply] at hv
  exact hv.symm

/-- The actual boundary is specified directly by original repaired affine operations. -/
def actualBoundary (s : Repair K R c fixed) : W.edges → (Fin d → k) :=
  fun e => realCorrection K R c fixed s e.1

omit [DecidablePred (· ∈ P.vertices)] [DecidableEq K.Vertex] in
/-- For every S, the same generated C equals exactly the independent actual shared repair values. -/
theorem generated_boundary_actual :
    generatedBoundary d K L R c hfaces P W candidates hfixed ek ee ef allowed =
      Set.range (actualBoundary d K R c P W candidates allowed) := by
  unfold generatedBoundary
  rw [FiniteNative.boundary_relation_range (M) B ClosedRegion.all P private lin delta ek ee ef
    W (ClosedRegion.to_all W) (fun e he hi => hi.1 he) candidates allowed
    (fun e he hi => hi.2.2 he)]
  ext t
  constructor
  · rintro ⟨u, ⟨h,rfl⟩, ht⟩
    refine ⟨(boundaryEquationEquiv d K L R c hfaces P candidates hfixed allowed).symm h, ?_⟩
    calc
      _ = boundaryVector d K L R c hfaces W
          (FiniteNative.supportedBoundary (M) ClosedRegion.all P delta W (ClosedRegion.to_all W)
            candidates allowed h) := by
        funext e
        exact boundary_equation_inverse_value d K L R c hfaces P candidates hfixed allowed h e.1
      _ = t := ht
  · rintro ⟨s,rfl⟩
    let h := boundaryEquationEquiv d K L R c hfaces P candidates hfixed allowed s
    refine ⟨FiniteNative.supportedBoundary (M) ClosedRegion.all P delta W (ClosedRegion.to_all W)
        candidates allowed h, ⟨h,rfl⟩, ?_⟩
    funext e
    exact boundary_equation_value d K L R c hfaces P candidates hfixed allowed s e.1

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.NativeAffine
