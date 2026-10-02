import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedPrivate
import ResearchLean.AG.RelativeRepairComposition.LinearPrivateKernel

/-!
# Independent private differentials on the full actual local coordinates

## Implementation notes

The new private map is computed independently by FiniteNative from its actual
new differential and generated full bases. Its comparison is then proved by
the actual local collapse on every full private value. Face coordinates retain
literal original face names and complete original target bases. All image and
kernel conclusions use that proved identity, with unrestricted supplement.
-/
namespace AAT.AG.RelativeRepairComposition.FiniteNative
open TransportCoherence AbelianLiftingObstruction
universe uk uG uA
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}} (M : LocalCoefficients.{uG,uA} K)
variable [∀ v, Module k (M.A v)]
variable (bases : FiniteFamily.Bases (k := k) M.A) (U P : ClosedRegion K)
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable [DecidablePred (· ∈ U.edges)]
variable (internal : Set (EdgeName (K := K))) [DecidablePred (· ∈ internal)]
variable (hlinear : ∀ {s t : K.Vertex} (e : K.Edge s t) (a : k) (x : M.A s),
  M.edge e (a • x) = a • M.edge e x)

/-- The independent private differential reads the actual full local d1 at zero public value. -/
theorem D_value (x : XIndex M bases U P internal → k) :
    D M bases U P internal hlinear x = coordinate2 M bases U P
      (RelativeCover.d1 M U P ((edgeSplit M bases U P internal).symm (x,0))) := by
  change coordinate2 M bases U P (FiniteCoefficients.differential1 M hlinear U P
    ((edgeSplit M bases U P internal).symm (x,0))) = _
  rw [FiniteCoefficients.differential1_eq]

end AAT.AG.RelativeRepairComposition.FiniteNative

namespace AAT.AG.RelativeRepairComposition.Subdivision.PrivateDifferential
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uG uI uE uB uD vE vB vD
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (factor : Factorization T chosen)
variable [∀ v, Module k (T.toTower.localCoefficients.A v)]
attribute [local instance] LinearCoefficients.coefficientModules
variable (bases : FiniteFamily.Bases (k := k) T.toTower.localCoefficients.A)
variable {I : Type uI} [Fintype I] [DecidableEq I]
variable (U : I → ClosedRegion K) (P : ClosedRegion K)
variable [∀ j, DecidablePred (· ∈ (U j).edges)] [DecidablePred (· ∈ P.edges)]
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (i : I) (hi : chosen ∈ ClosedRegion.privateAlwaysEdges U P candidates i) (j : I)
variable (hlinear : ∀ {s t : K.Vertex} (e : K.Edge s t) (a : k)
  (x : T.toTower.localCoefficients.A s),
  T.toTower.localCoefficients.edge e (a • x) = a • T.toTower.localCoefficients.edge e x)

local notation "Mo" => (T.toTower.localCoefficients)
local notation "Mn" => (TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (originalTower T chosen factor)))
local notation "Bn" => FiniteBases.expandedBases T chosen factor bases
local notation "Un" => expandedRegion K chosen (U j)
local notation "Pn" => expandedRegion K chosen P
local notation "Io" => ClosedRegion.privateAlwaysEdges U P candidates j
local notation "In" => ClosedRegion.privateAlwaysEdges (fun l => expandedRegion K chosen (U l))
  Pn (oldEdgeSet K chosen candidates) j
local notation "Xo" => (FiniteNative.XIndex Mo bases (U j) P Io → k)
local notation "Zo" => (FiniteNative.ZIndex Mo bases (U j) P Io → k)
local notation "Xn" => (FiniteNative.XIndex Mn Bn Un Pn In → k)
local notation "Zn" => (FiniteNative.ZIndex Mn Bn Un Pn In → k)
local notation "R" => localSupplement T chosen factor (U j)


variable [DecidablePred (· ∈ P.faces)]
local notation "Do" => FiniteNative.D Mo bases (U j) P Io hlinear

/-- Independently compute all new private columns from the actual new local differential. -/
noncomputable def newD : Xn →ₗ[k] (FiniteNative.Index2 Mo bases (U j) P → k) := by
  letI := GeneratedPublicReadings.retainedCandidatesDecidable chosen U P candidates i hi
  letI : ∀ l, DecidablePred (· ∈ (expandedRegion K chosen (U l)).edges) :=
    fun l => FiniteIncidence.expandedEdgesDecidable K chosen (U l)
  letI : DecidablePred (· ∈ (Pn).edges) := FiniteIncidence.expandedEdgesDecidable K chosen P
  exact FiniteNative.D Mn Bn Un Pn In (LinearCoefficients.edge_linear T chosen factor hlinear)

/-- The computed new private columns read the full actual differential on every new correction. -/
theorem newD_value (x : Xn) :
    newD T chosen factor bases U P candidates i hi j hlinear x =
    FiniteNative.coordinate2 Mn Bn Un Pn (RelativeCover.d1 Mn Un Pn
      ((GeneratedPrivate.newSplit T chosen factor bases U P candidates i hi j).symm (x,0))) := by
  letI := GeneratedPublicReadings.retainedCandidatesDecidable chosen U P candidates i hi
  letI : ∀ l, DecidablePred (· ∈ (expandedRegion K chosen (U l)).edges) :=
    fun l => FiniteIncidence.expandedEdgesDecidable K chosen (U l)
  letI : DecidablePred (· ∈ (Pn).edges) := FiniteIncidence.expandedEdgesDecidable K chosen P
  exact FiniteNative.D_value Mn Bn Un Pn In
    (LinearCoefficients.edge_linear T chosen factor hlinear) x

omit [Fintype I] [DecidableEq I] [∀ j, DecidablePred (· ∈ (U j).edges)]
  [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ candidates)] in
/-- All new face coordinates retain the same authored face and full target-kernel basis. -/
theorem face_coordinates (c : RelativeCover.C2 Mn Un Pn) :
    FiniteNative.coordinate2 Mn Bn Un Pn c =
      FiniteNative.coordinate2 Mo bases (U j) P (local2Equiv T chosen factor (U j) P c) := rfl

/-- Each independent new private differential equals the old differential of full collapsed values. -/
theorem private_differential (x : Xn) :
    newD T chosen factor bases U P candidates i hi j hlinear x =
      Do (GeneratedPrivate.privateEquiv T chosen factor bases U P candidates i hi j hlinear x).1 := by
  rw [newD_value,face_coordinates,local_d1 T chosen factor (U j) P hi.2.1]
  rw [GeneratedPrivate.private_cochain_collapse,FiniteNative.D_value]

/-- Independently computed whole private images coincide on the same full original face space. -/
theorem private_range :
    LinearMap.range (newD T chosen factor bases U P candidates i hi j hlinear) =
      LinearMap.range Do :=
  LinearPrivateKernel.range_eq
    (GeneratedPrivate.privateEquiv T chosen factor bases U P candidates i hi j hlinear)
    (newD T chosen factor bases U P candidates i hi j hlinear) Do
    (private_differential T chosen factor bases U P candidates i hi j hlinear)

/-- Every independent new private kernel vector retains all old kernel and supplemental freedom. -/
noncomputable def privateKernelEquiv :
    LinearMap.ker (newD T chosen factor bases U P candidates i hi j hlinear) ≃ₗ[k]
      (LinearMap.ker Do × R) :=
  LinearPrivateKernel.equivalence
    (GeneratedPrivate.privateEquiv T chosen factor bases U P candidates i hi j hlinear)
    (newD T chosen factor bases U P candidates i hi j hlinear) Do
    (private_differential T chosen factor bases U P candidates i hi j hlinear)

/-- The complete kernel coordinates use the same full private collapse on every vector. -/
theorem privateKernelEquiv_value
    (x : LinearMap.ker (newD T chosen factor bases U P candidates i hi j hlinear)) :
    ((privateKernelEquiv T chosen factor bases U P candidates i hi j hlinear x).1.1,
      (privateKernelEquiv T chosen factor bases U P candidates i hi j hlinear x).2) =
    GeneratedPrivate.privateEquiv T chosen factor bases U P candidates i hi j hlinear x.1 := rfl

/-- Every old private kernel and supplemental value restore by the same full private inverse. -/
theorem privateKernelEquiv_inverse_value (x : LinearMap.ker Do) (r : R) :
    ((privateKernelEquiv T chosen factor bases U P candidates i hi j hlinear).symm (x,r)).1 =
    (GeneratedPrivate.privateEquiv T chosen factor bases U P candidates i hi j hlinear).symm (x.1,r) := rfl

end AAT.AG.RelativeRepairComposition.Subdivision.PrivateDifferential
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.FiniteNative
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.PrivateDifferential
