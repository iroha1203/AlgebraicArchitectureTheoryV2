import ResearchLean.AG.RelativeRepairComposition.AffineFamilyEquationBridge
import ResearchLean.AG.RelativeRepairComposition.StrictFunctorComparison

/-!
# Actual parameter repairs retain the complete fixed original equation

## Implementation notes

The forward and inverse maps first use the independent original native repair
correspondence, then identify full cochains and full gauge labels at the same
parameter. Both composites are strict on objects and arrows. Original edge
corrections and original vertex values are retained by the constructed maps.
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
variable (P : ClosedRegion K)

variable (hB : ∀ v : V, ∀ f ∈ P.faces, familyDefectLinear K R θR η v f = 0)
variable (hfixed : ∀ f ∈ P.faces,
  translation (k := k) (c f) * GroupExtension.pathValue K R (K.twoLeft f) =
    GroupExtension.pathValue K R (K.twoRight f))
variable (candidates allowed : Set (EdgeName (K := K)))
local notation "hfixedv" v => fixed_native K (familyOriginal K L θL v) (familyReference K R θR v)
  (familyComparisons K c η v) (family_aligned K R θR hf v) P
  (family_fixed_face K R c θR η hf P.faces hfixed hB v)
local notation "δv" v => ActualEquation.defectFamily (Tv v) P (hfixedv v)
local notation "δa" v => SymbolicNativeLocal.defectFamily (M) P
  (ActualEquation.defectFamily (tower K L R c hf) P (fixed_native K L R c hf P hfixed))
  (familyRelativeLinear K L R c θR η hf P hB) v


set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
local notation "fixed" => fixedEdgesForRange P.edges candidates allowed
local notation "Q" v => familyEquationEquivalence K L R c θL θR η hf P hB hfixed candidates allowed v
local notation "N" v => SupportedNativeEquation.equivalence (Tv v) P candidates allowed (hfixedv v)

/-- The change to the same base equation has strict inverse functors on all supported full arrows. -/
theorem family_equation_functor_inverse (v : V) :
    (Q v).functor ⋙ (Q v).inverse =
      𝟭 (SupportedEquation.Groupoid (Mv v) P ClosedRegion.all candidates allowed (δv v)) :=
  changed_label_functor_inverse
    (familyEquationLabels K L R c θL θR η hf P candidates allowed v).toMultiplicative
    (familyEquationObjects K L R c θL θR η hf P hB hfixed candidates allowed v)
    (family_equation_equivariant K L R c θL θR η hf P hB hfixed candidates allowed v)

/-- The change back to each actual parameter equation is strict on full base arrows as well. -/
theorem family_equation_inverse_functor (v : V) :
    (Q v).inverse ⋙ (Q v).functor =
      𝟭 (SupportedEquation.Groupoid (M) P ClosedRegion.all candidates allowed (δa v)) :=
  changed_label_inverse_functor
    (familyEquationLabels K L R c θL θR η hf P candidates allowed v).toMultiplicative
    (familyEquationObjects K L R c θL θR η hf P hB hfixed candidates allowed v)
    (family_equation_equivariant K L R c θL θR η hf P hB hfixed candidates allowed v)

/-- Every actual parameter repair groupoid has the same original fixed supported equation with its generated affine defect. -/
noncomputable def familyNativeEquationEquivalence (v : V) :
    RepairGroupoid (Tv v) P.vertices fixed ≌
      SupportedEquation.Groupoid (M) P ClosedRegion.all candidates allowed (δa v) :=
  (N v).trans (Q v)

/-- Reconstruction preserves every actual repair and every full native gauge arrow. -/
theorem family_native_equation_functor_inverse (v : V) :
    (familyNativeEquationEquivalence K L R c θL θR η hf P hB hfixed candidates allowed v).functor ⋙
      (familyNativeEquationEquivalence K L R c θL θR η hf P hB hfixed candidates allowed v).inverse =
        𝟭 (RepairGroupoid (Tv v) P.vertices fixed) :=
  strict_trans_functor_inverse (N v) (Q v)
    (SupportedNativeEquation.functor_inverse (Tv v) P candidates allowed (hfixedv v))
    (family_equation_functor_inverse K L R c θL θR η hf P hB hfixed candidates allowed v)

/-- Coordinate reconstruction preserves the entire original supported equation and full vertex-label arrows. -/
theorem family_native_equation_inverse_functor (v : V) :
    (familyNativeEquationEquivalence K L R c θL θR η hf P hB hfixed candidates allowed v).inverse ⋙
      (familyNativeEquationEquivalence K L R c θL θR η hf P hB hfixed candidates allowed v).functor =
        𝟭 (SupportedEquation.Groupoid (M) P ClosedRegion.all candidates allowed (δa v)) :=
  strict_trans_inverse_functor (N v) (Q v)
    (SupportedNativeEquation.inverse_functor (Tv v) P candidates allowed (hfixedv v))
    (family_equation_inverse_functor K L R c θL θR η hf P hB hfixed candidates allowed v)

/-- The actual native repair's full correction is the same value on every original edge after both coordinate maps. -/
theorem family_native_equation_edge_value (v : V) (s : SupportedRepair (Tv v) fixed)
    (e : EdgeName (K := K)) :
    ((familyEquationObjects K L R c θL θR η hf P hB hfixed candidates allowed v)
      (SupportedNativeEquation.repairEquiv (Tv v) P candidates allowed (hfixedv v) s)).1.1.1
      ⟨e,Set.mem_univ e⟩ = (Tv v).solutionCorrection s.1 e := by
  rw [family_equation_edge_value]
  exact SupportedNativeEquation.repair_value (Tv v) P candidates allowed (hfixedv v) s e

/-- Every full original vertex label survives the actual parameter repair correspondence unchanged. -/
theorem family_native_equation_label_value (v : V)
    {s t : RepairGroupoid (Tv v) P.vertices fixed} (b : s ⟶ t) (w : K.Vertex) :
    (((familyNativeEquationEquivalence K L R c θL θR η hf P hB hfixed candidates allowed v).functor.map b).1.toAdd).1.1
      ⟨w,Set.mem_univ w⟩ = b.1.toAdd.1 w :=
  SupportedNativeEquation.functor_label_value (Tv v) P candidates allowed (hfixedv v) b w

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
