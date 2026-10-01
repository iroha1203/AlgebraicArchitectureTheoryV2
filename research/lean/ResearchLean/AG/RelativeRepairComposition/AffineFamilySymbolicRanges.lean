import ResearchLean.AG.RelativeRepairComposition.AffineFamilySymbolicCover
import ResearchLean.AG.RelativeRepairComposition.GeneratedCoverRanges

/-!
# Actual original range inclusions commute with symbolic evaluation

## Implementation notes

At each primitive value, range relaxation changes only forbidden-candidate
support predicates. The original repair, every full vertex label and all fixed
local generators are the same. The square uses the independently defined actual
range functor and the same symbolic range functor on all coordinates and arrows.
-/
namespace AAT.AG.RelativeRepairComposition
open CategoryTheory

/-- Postcomposing a strict range square with inverse evaluation preserves the same square under evaluation conjugation. -/
theorem strict_inverse_evaluation_square
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    (R : A ⥤ B) (X : A ⥤ C) (Y : B ⥤ D) (J : C ⥤ D)
    (es : E ≌ C) (et : F ≌ D)
    (h : R ⋙ Y = X ⋙ J) (hs : es.inverse ⋙ es.functor = 𝟭 C) :
    R ⋙ (Y ⋙ et.inverse) =
      (X ⋙ es.inverse) ⋙ (es.functor ⋙ J ⋙ et.inverse) := by
  change (R ⋙ Y) ⋙ et.inverse = X ⋙ ((es.inverse ⋙ es.functor) ⋙ J) ⋙ et.inverse
  rw [hs, Functor.id_comp, h]
  exact Functor.assoc X J et.inverse

end AAT.AG.RelativeRepairComposition

namespace AAT.AG.RelativeRepairComposition.NativeAffine
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uG uI uV
variable {k : Type uk} [Field k] [Fintype k] [DecidableEq k] (d : Nat)
variable (K : FiniteTransportPresentation.{uG})
variable (L R : ∀ {i j : K.Vertex}, K.Edge i j → Operations k (Fin d → k))
variable (c : K.TwoCell → (Fin d → k))
variable (hf : ∀ f : K.TwoCell,
  (GroupExtension.pathValue K R (K.twoLeft f)).linear =
    (GroupExtension.pathValue K R (K.twoRight f)).linear)
variable {V : Type uV} [AddCommGroup V] [Module k V]
variable (θL θR : V →ₗ[k] (EdgeName (K := K) → (Fin d → k)))
variable (η : V →ₗ[k] (K.TwoCell → (Fin d → k)))
variable {I : Type uI} [Fintype I] [DecidableEq I]
variable (P : ClosedRegion K) (U : I → ClosedRegion K)
variable [DecidablePred (· ∈ P.edges)] [DecidablePred (· ∈ P.faces)]
variable [∀ i, DecidablePred (· ∈ (U i).vertices)]
variable [∀ i, DecidablePred (· ∈ (U i).edges)] [∀ i, DecidablePred (· ∈ (U i).faces)]
variable (hB : ∀ v : V, ∀ f ∈ P.faces, familyDefectLinear K R θR η v f = 0)
variable (candidates : Set (EdgeName (K := K))) [DecidablePred (· ∈ candidates)]
variable (hfixed : ∀ f ∈ P.faces,
  translation (k := k) (c f) * GroupExtension.pathValue K R (K.twoLeft f) =
    GroupExtension.pathValue K R (K.twoRight f))
variable [Fintype (EdgeName (K := K))] [DecidableEq (EdgeName (K := K))]
variable [Fintype K.TwoCell] [DecidableEq K.TwoCell]
variable (enumK : FiniteElimination.Enumeration k)
variable (enumEdges : FiniteElimination.Enumeration (EdgeName (K := K)))
variable (enumFaces : FiniteElimination.Enumeration K.TwoCell)
variable (enumI : FiniteElimination.Enumeration I) (hc : ClosedRegion.IndexedCover U)
variable (v : V)
variable {S W : Set (EdgeName (K := K))}

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
local notation "T" => familyTower K L R c θL θR η hf v
local notation "M" => TowerPresentation.localCoefficients (OriginalTowerPresentation.toTower (tower K L R c hf))
local notation "bases" => standardBases d K L R c hf
local notation "lin" => edge_linear K L R c hf
local notation "δ₀" => ActualEquation.defectFamily (tower K L R c hf) P (fixed_native K L R c hf P hfixed)
local notation "Δ" => familyRelativeLinear K L R c θR η hf P hB

local notation "δ" => SymbolicNativeLocal.defectFamily (M) P δ₀ Δ v
local notation "N" s => familyNativeEquationEquivalence K L R c θL θR η hf P hB hfixed candidates s v
local notation "G" s => StrictCoverRestoration.equivalence (M) P U candidates s (δ) enumI hc
local notation "C" s => GeneratedCoverAction.equivalence (M) bases P U candidates lin (δ) enumK enumEdges enumFaces s
local notation "E" s => SymbolicCoverAction.equivalence (M) bases P U candidates lin δ₀ Δ enumK enumEdges enumFaces s v
local notation "H" s => familyNativeSymbolicEquivalence d K L R c hf θL θR η P U hB candidates hfixed enumK enumEdges enumFaces enumI hc s v
local notation "actInc" h => ActualRelative.rangeFunctor (T) P candidates h
local notation "J" h => GeneratedRangeInclusion.functor (M) bases P U candidates lin (δ) enumK enumEdges enumFaces h

/-- Each independently defined actual parameter range inclusion retains the same original full generated objects and arrows. -/
theorem family_generated_range_square (h : S ⊆ W) :
    (actInc h) ⋙ (N W).functor ⋙ (G W).functor ⋙ (C W).functor =
      (N S).functor ⋙ (G S).functor ⋙ (C S).functor ⋙ (J h) := rfl

/-- For every allowed range inclusion, actual original repairs and all full labels commute strictly with the same complete symbolic coordinate functor. -/
theorem family_symbolic_range_square (h : S ⊆ W) :
    (actInc h) ⋙ (H W).functor = (H S).functor ⋙
      SymbolicCoverRanges.functor (M) bases P U candidates lin δ₀ Δ enumK enumEdges enumFaces v h := by
  exact strict_inverse_evaluation_square (actInc h)
    ((N S).functor ⋙ (G S).functor ⋙ (C S).functor)
    ((N W).functor ⋙ (G W).functor ⋙ (C W).functor) (J h) (E S) (E W)
    (family_generated_range_square d K L R c hf θL θR η P U hB candidates hfixed
      enumK enumEdges enumFaces enumI hc v h)
    (SymbolicCoverAction.inverse_functor (M) bases P U candidates lin δ₀ Δ
      enumK enumEdges enumFaces S v)

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
