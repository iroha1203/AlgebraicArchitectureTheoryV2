import ResearchLean.AG.RepairObservationDuality.ActualAffineFamily
import ResearchLean.AG.RepairObservationDuality.FiberSufficiency
import ResearchLean.AG.RelativeRepairComposition.FiniteNativeCoordinates
import ResearchLean.AG.RelativeRepairComposition.GeneratedStrictCover
import ResearchLean.AG.RelativeRepairComposition.StrictCoverRestoration

/-!
# Generated local public feasibility of the same actual input equation

## Implementation notes

G-131 A / n1017 §3.5, §6 fixes the authored finite cover and whole kernel
bases. Generated local relations keep all private variables and require literal
shared original public values. Their common RHS is the negative actual defect,
not an independently supplied feasible relation. G-130's full object maps
preserve every original value; the primitive family supplies the actual RHS.
-/
namespace AAT.AG.RepairObservationDuality.ActualFamilyInterfaces
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary
open AbelianLiftingObstruction RelativeRepairComposition PrimitiveAffineDefect
set_option autoImplicit false
universe uk uV uF uG uE uB uD vE vB vD
variable {k : Type uk} [Field k]
variable {V : Type uV} [AddCommGroup V] [Module k V]
variable {F : Type uF}
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : TowerPresentation K p q)
variable [∀ v, Module k ((T.localCoefficients).A v)]
variable (edgeChange : V →ₗ[k] (C1 (T.localCoefficients)))
variable (comparisonChange : V →ₗ[k] (C2 (T.localCoefficients)))
variable (input : F → OriginalTowerPresentation K p q) (ν : F → V)
variable (hdata : ∀ X : F, (input X).toTower.toTransportData =
  data T (edgeChange (ν X)) (comparisonChange (ν X)))

variable (realize : V → F) (hrealize : ∀ v, ν (realize v) = v)
variable (P : ClosedRegion K)
variable (hfixed : ∀ X : F, ∀ f ∈ P.faces,
  (input X).toTower.upper.pathLift (K.twoLeft f) ≫
    FiberAut.hom ((input X).comparator f) =
  (input X).toTower.upper.pathLift (K.twoRight f))
variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k)
  (x : (T.localCoefficients).A i),
  (T.localCoefficients).edge e (t • x) = t • (T.localCoefficients).edge e x)
variable (bases : FiniteFamily.Bases (k := k) T.localCoefficients.A)
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (houtside : ∀ e ∈ candidates, e ∉ P.edges)
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
attribute [local instance] Classical.propDecidable
local notation "D₀" => OriginalColumns.D (k := k) T.localCoefficients P candidates hlinear
local notation "C" => OriginalColumns.column (k := k) T.localCoefficients P candidates houtside hlinear
local notation "fixed" => ActualAffineFamily.model_fixed T edgeChange comparisonChange input ν hdata realize hrealize P hfixed
local notation "b₀" => RelativeAffineDefect.baseRhs T edgeChange comparisonChange P fixed
local notation "B₀" => RelativeAffineDefect.rhsLinear T hlinear edgeChange comparisonChange P fixed
variable [Fintype k] [DecidableEq k]
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (U : I → ClosedRegion K) (hc : ClosedRegion.IndexedCover U)
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (enumI : FiniteElimination.Enumeration I)
variable (enumK : FiniteElimination.Enumeration k)
variable (enumEdges : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (enumFaces : FiniteElimination.Enumeration K.TwoCell)
include hdata hrealize hfixed


/-- G-131 A / n1017 §3.5, §6 constructor: generated public-compatible local
relations of the original full equation, at the same primitive parameter. -/
noncomputable def generatedObjects (S : Set candidates) (v : V) :=
  GeneratedStrictCover.Objects T.localCoefficients bases P U candidates hlinear
    (-(affineRhs B₀ b₀ v)) enumK enumEdges enumFaces (OriginalRanges.allowed candidates S)

/-- G-131 A / n1017 §3.5, §6 constructor: whole original supported global
values are equivalent to generated compatible local values, keeping all names. -/
noncomputable def globalToGenerated (S : Set candidates) (v : V) :
    SupportedEquation.Objects T.localCoefficients P ClosedRegion.all candidates
      (OriginalRanges.allowed candidates S) (-(affineRhs B₀ b₀ v)) ≃
    generatedObjects T edgeChange comparisonChange input ν hdata realize hrealize P hfixed
      hlinear bases candidates U enumK enumEdges enumFaces S v :=
  (StrictCoverRestoration.objectEquiv T.localCoefficients P U candidates
    (OriginalRanges.allowed candidates S) (-(affineRhs B₀ b₀ v)) enumI hc).trans
    (GeneratedStrictCover.objectEquiv T.localCoefficients bases P U candidates hlinear
      (-(affineRhs B₀ b₀ v)) enumK enumEdges enumFaces (OriginalRanges.allowed candidates S))

include houtside hc enumI

/-- G-131 A / n1017 §3.5, §6: generated public-compatible local feasibility
is exactly the independently defined full correction equation for every S. -/
theorem generated_equation_iff (S : Set candidates) (v : V) :
    Nonempty (generatedObjects T edgeChange comparisonChange input ν hdata realize hrealize P hfixed
      hlinear bases candidates U enumK enumEdges enumFaces S v) ↔
    ∃ h, SelectedCokernel.differential D₀ C S h = affineRhs B₀ b₀ v := by
  have e := globalToGenerated T edgeChange comparisonChange input ν hdata realize hrealize P hfixed
    hlinear bases candidates U hc enumI enumK enumEdges enumFaces S v
  have hn : Nonempty (generatedObjects T edgeChange comparisonChange input ν hdata realize hrealize P hfixed
      hlinear bases candidates U enumK enumEdges enumFaces S v) ↔
      Nonempty (SupportedEquation.Objects T.localCoefficients P ClosedRegion.all candidates
        (OriginalRanges.allowed candidates S) (-(affineRhs B₀ b₀ v))) :=
    ⟨fun ⟨y⟩ => ⟨e.symm y⟩,fun ⟨x⟩ => ⟨e x⟩⟩
  refine hn.trans ?_
  rw [OriginalRanges.objects_nonempty_iff_equation (k := k) T.localCoefficients P candidates
    houtside hlinear (-(affineRhs B₀ b₀ v)) S, neg_neg]
  exact SelectedCokernel.equation_iff D₀ C S (affineRhs B₀ b₀ v)

/-- G-131 A / n1017 §3.5, §6: the same original input has an actual repair
exactly when its generated local public relations are jointly feasible. -/
theorem actual_generated_iff (X : F) (S : Set candidates) :
    Nonempty (SupportedRepair (input X)
      (fixedEdgesForRange P.edges candidates (OriginalRanges.allowed candidates S))) ↔
    Nonempty (generatedObjects T edgeChange comparisonChange input ν hdata realize hrealize P hfixed
      hlinear bases candidates U enumK enumEdges enumFaces S (ν X)) :=
  (ActualAffineFamily.actual_affine_equation_iff T edgeChange comparisonChange input ν hdata
    realize hrealize P hfixed hlinear candidates houtside X S).trans
    (generated_equation_iff T edgeChange comparisonChange input ν hdata realize hrealize P hfixed
      hlinear bases candidates houtside U hc enumI enumK enumEdges enumFaces S (ν X)).symm

end AAT.AG.RepairObservationDuality.ActualFamilyInterfaces
#assert_standard_axioms_only AAT.AG.RepairObservationDuality.ActualFamilyInterfaces
