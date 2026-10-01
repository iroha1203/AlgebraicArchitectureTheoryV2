import ResearchLean.AG.RelativeRepairComposition.AffineConstantCoefficients
import ResearchLean.AG.RelativeRepairComposition.AffineComparisonWords
import ResearchLean.AG.RelativeRepairComposition.RelativeCoverComplex

/-!
# Original full relative differentials use unchanged native transports

## Implementation notes

The same actual full kernel values occur on every original vertex and edge.
Native edge equivalences and all original word linear components are unchanged
under primitive translation updates. Degree-zero and degree-one relative
cochains are therefore identical, before candidate support is imposed.
-/
namespace AAT.AG.RelativeRepairComposition.NativeAffine
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uA uG uV
variable {k : Type uk} [Field k] {A : Type uA} [AddCommGroup A] [Module k A]
variable {V : Type uV} [AddCommGroup V] [Module k V]
variable (K : FiniteTransportPresentation.{uG})
variable (L R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k A)
variable (c : K.TwoCell → A)
variable (θL θR : V →ₗ[k] (EdgeName (K := K) → A)) (η : V →ₗ[k] (K.TwoCell → A))
variable (hf : ∀ f : K.TwoCell,
  (GroupExtension.pathValue K R (K.twoLeft f)).linear =
    (GroupExtension.pathValue K R (K.twoRight f)).linear)
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (tower K L R c hf))
local notation "Tv" v => familyTower K L R c θL θR η hf v
local notation "Mv" v => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (Tv v))
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
variable (P : ClosedRegion K)

/-- Every original relative vertex coboundary is the same full native cochain for every primitive parameter. -/
theorem family_relative_d0 (v : V) (b : RelativeCover.C0 (M) ClosedRegion.all P) :
    RelativeCover.d0 (Mv v) ClosedRegion.all P b = RelativeCover.d0 (M) ClosedRegion.all P b := by
  apply Subtype.ext
  funext e
  change (ClosedRegion.e0 (M) ClosedRegion.all b.1) e.1.2.1 -
    (show (M).A e.1.2.1 from
      (Mv v).edge e.1.2.2 ((ClosedRegion.e0 (M) ClosedRegion.all b.1) e.1.1)) =
    (ClosedRegion.e0 (M) ClosedRegion.all b.1) e.1.2.1 -
    (M).edge e.1.2.2 ((ClosedRegion.e0 (M) ClosedRegion.all b.1) e.1.1)
  exact congrArg (fun E : (M).A e.1.1 ≃+ (M).A e.1.2.1 =>
    (ClosedRegion.e0 (M) ClosedRegion.all b.1) e.1.2.1 -
    E ((ClosedRegion.e0 (M) ClosedRegion.all b.1) e.1.1))
    (same_linear_edge K L R (familyOriginal K L θL v) (familyReference K R θR v)
      c (familyComparisons K c η v) hf (family_aligned K R θR hf v)
      (fun e => translated_linear K R (θR v) e) e.1.2.2)

/-- Every original relative edge differential is the same full native cochain for every primitive parameter. -/
theorem family_relative_d1 (v : V) (h : RelativeCover.C1 (M) ClosedRegion.all P) :
    RelativeCover.d1 (Mv v) ClosedRegion.all P h = RelativeCover.d1 (M) ClosedRegion.all P h := by
  apply Subtype.ext
  funext f
  apply (coefficient K L R c hf (K.twoTarget f.1)).injective
  change coefficient K L R c hf (K.twoTarget f.1)
    (AbelianLiftingObstruction.d1 (Mv v) (ClosedRegion.e1 (M) ClosedRegion.all h.1) f.1) =
    coefficient K L R c hf (K.twoTarget f.1)
    (AbelianLiftingObstruction.d1 (M) (ClosedRegion.e1 (M) ClosedRegion.all h.1) f.1)
  calc
    _ = coefficient K (familyOriginal K L θL v) (familyReference K R θR v)
      (familyComparisons K c η v) (family_aligned K R θR hf v) (K.twoTarget f.1)
      (AbelianLiftingObstruction.d1 (Mv v) (ClosedRegion.e1 (M) ClosedRegion.all h.1) f.1) := rfl
    _ = _ := by
      unfold familyTower
      rw [d1_value, d1_value]
      simp only [familyReference, translated_vector_path]
      rfl

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
