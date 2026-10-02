import ResearchLean.AG.RelativeRepairComposition.SubdivisionGeneratedPublicReadings
import ResearchLean.AG.RelativeRepairComposition.LinearPrivateComparison

/-!
# Independently generated whole private spaces under actual subdivision

## Implementation notes

Both private/public splits are applied to the independent original local
families. The full local linear comparison then identifies their zero-public
parts. The general restriction API receives its comparison law here from the
proved actual public reading identity. Every supplemental value is retained;
the construction does not choose a private kernel representative.
-/
namespace AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPrivate
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

/-- The independently computed new split uses membership decisions from the original input. -/
noncomputable def newSplit : RelativeCover.C1 Mn Un Pn ≃ₗ[k] (Xn × Zn) := by
  letI := GeneratedPublicReadings.retainedCandidatesDecidable chosen U P candidates i hi
  letI : ∀ l, DecidablePred (· ∈ (expandedRegion K chosen (U l)).edges) :=
    fun l => FiniteIncidence.expandedEdgesDecidable K chosen (U l)
  letI : DecidablePred (· ∈ (Pn).edges) := FiniteIncidence.expandedEdgesDecidable K chosen P
  exact FiniteNative.edgeSplit Mn Bn Un Pn In

/-- Reading the new split preserves exactly its independently computed full public component. -/
theorem newSplit_public (h : RelativeCover.C1 Mn Un Pn) :
    (newSplit T chosen factor bases U P candidates i hi j h).2 =
      GeneratedPublicReadings.newPublic T chosen factor bases U P candidates i hi j h := rfl

/-- All split coordinates are compared through the full actual local correction equivalence. -/
noncomputable def fullComparison : (Xn × Zn) ≃ₗ[k] ((Xo × Zo) × R) := by
  letI := GeneratedPublicReadings.retainedCandidatesDecidable chosen U P candidates i hi
  letI : ∀ l, DecidablePred (· ∈ (expandedRegion K chosen (U l)).edges) :=
    fun l => FiniteIncidence.expandedEdgesDecidable K chosen (U l)
  letI : DecidablePred (· ∈ (Pn).edges) := FiniteIncidence.expandedEdgesDecidable K chosen P
  exact (newSplit T chosen factor bases U P candidates i hi j).symm.trans
    ((LocalLinear.local1LinearEquiv T chosen factor (U j) P hi.2.1 hlinear).trans
      (LinearEquiv.prodCongr (FiniteNative.edgeSplit Mo bases (U j) P Io) (LinearEquiv.refl k R)))

/-- Full split comparison reads the actual local collapse and the whole supplement. -/
theorem fullComparison_value (h : RelativeCover.C1 Mn Un Pn) :
    fullComparison T chosen factor bases U P candidates i hi j hlinear
      (newSplit T chosen factor bases U P candidates i hi j h) =
    (FiniteNative.edgeSplit Mo bases (U j) P Io
      (local1Equiv T chosen factor (U j) P hi.2.1 h).1,
      (local1Equiv T chosen factor (U j) P hi.2.1 h).2) := by
  letI := GeneratedPublicReadings.retainedCandidatesDecidable chosen U P candidates i hi
  letI : ∀ l, DecidablePred (· ∈ (expandedRegion K chosen (U l)).edges) :=
    fun l => FiniteIncidence.expandedEdgesDecidable K chosen (U l)
  letI : DecidablePred (· ∈ (Pn).edges) := FiniteIncidence.expandedEdgesDecidable K chosen P
  change (FiniteNative.edgeSplit Mo bases (U j) P Io
    (local1Equiv T chosen factor (U j) P hi.2.1
      ((newSplit T chosen factor bases U P candidates i hi j).symm
        (newSplit T chosen factor bases U P candidates i hi j h))).1,
      (local1Equiv T chosen factor (U j) P hi.2.1
        ((newSplit T chosen factor bases U P candidates i hi j).symm
          (newSplit T chosen factor bases U P candidates i hi j h))).2) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The complete public component of the split comparison is the proved original reading. -/
theorem fullComparison_public (xz : Xn × Zn) :
    GeneratedPublic.publicCoordinateEquiv T chosen factor bases U P candidates i hi j xz.2 =
      (fullComparison T chosen factor bases U P candidates i hi j hlinear xz).1.2 := by
  letI := GeneratedPublicReadings.retainedCandidatesDecidable chosen U P candidates i hi
  letI : ∀ l, DecidablePred (· ∈ (expandedRegion K chosen (U l)).edges) :=
    fun l => FiniteIncidence.expandedEdgesDecidable K chosen (U l)
  letI : DecidablePred (· ∈ (Pn).edges) := FiniteIncidence.expandedEdgesDecidable K chosen P
  let h := (newSplit T chosen factor bases U P candidates i hi j).symm xz
  have hs : newSplit T chosen factor bases U P candidates i hi j h = xz :=
    (newSplit T chosen factor bases U P candidates i hi j).apply_symm_apply xz
  rw [← hs,fullComparison_value,newSplit_public]
  exact GeneratedPublicReadings.public_reading_collapse T chosen factor bases U P candidates i hi j h

/-- Each independent new private coordinate has all old private values and unrestricted supplement. -/
noncomputable def privateEquiv : Xn ≃ₗ[k] (Xo × R) :=
  LinearPrivateComparison.equivalence
    (fullComparison T chosen factor bases U P candidates i hi j hlinear)
    (GeneratedPublic.publicCoordinateEquiv T chosen factor bases U P candidates i hi j)
    (fullComparison_public T chosen factor bases U P candidates i hi j hlinear)

/-- The new private values read exactly the complete split comparison on zero public values. -/
theorem privateEquiv_value (x : Xn) :
    privateEquiv T chosen factor bases U P candidates i hi j hlinear x =
    ((fullComparison T chosen factor bases U P candidates i hi j hlinear (x,0)).1.1,
      (fullComparison T chosen factor bases U P candidates i hi j hlinear (x,0)).2) := rfl

/-- Restoring any old private value and any supplement recovers the complete new private value. -/
theorem privateEquiv_inverse_value (x : Xo) (r : R) :
    (privateEquiv T chosen factor bases U P candidates i hi j hlinear).symm (x,r) =
      ((fullComparison T chosen factor bases U P candidates i hi j hlinear).symm ((x,0),r)).1 := rfl

/-- Collapsing every independently restored private correction keeps all old and supplemental values. -/
theorem private_cochain_collapse (x : Xn) :
    local1Equiv T chosen factor (U j) P hi.2.1
      ((newSplit T chosen factor bases U P candidates i hi j).symm (x,0)) =
    ((FiniteNative.edgeSplit Mo bases (U j) P Io).symm
        ((privateEquiv T chosen factor bases U P candidates i hi j hlinear x).1,0),
      (privateEquiv T chosen factor bases U P candidates i hi j hlinear x).2) := by
  let h := (newSplit T chosen factor bases U P candidates i hi j).symm (x,0)
  have hc := fullComparison_value T chosen factor bases U P candidates i hi j hlinear h
  rw [LinearEquiv.apply_symm_apply] at hc
  have he := LinearPrivateComparison.forward_insert
    (fullComparison T chosen factor bases U P candidates i hi j hlinear)
    (GeneratedPublic.publicCoordinateEquiv T chosen factor bases U P candidates i hi j)
    (fullComparison_public T chosen factor bases U P candidates i hi j hlinear) x
  have hh := he.trans hc
  apply Prod.ext
  · apply (FiniteNative.edgeSplit Mo bases (U j) P Io).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (congrArg Prod.fst hh).symm
  · exact (congrArg Prod.snd hh).symm

end AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPrivate
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.GeneratedPrivate
