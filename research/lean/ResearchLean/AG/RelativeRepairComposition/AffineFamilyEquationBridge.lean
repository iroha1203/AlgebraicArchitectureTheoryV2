import ResearchLean.AG.RelativeRepairComposition.AffineFamilyEquationCoordinates

/-!
# Native affine parameter equation groupoids preserve every original arrow

## Implementation notes

The full supported object and full label coordinates are constructed independently.
Their original-label action commutes by the whole native kernel coordinate maps.
The resulting equivalence retains each label, including all stabilizers.
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
set_option synthInstance.maxHeartbeats 100000
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

/-- The exact original-label action commutes with the change to the reused base equation. -/
theorem family_equation_equivariant (v : V)
    (b : Multiplicative (SupportedEquation.Labels (Mv v) P ClosedRegion.all candidates allowed))
    (y : SupportedEquation.Objects (Mv v) P ClosedRegion.all candidates allowed (δv v)) :
    familyEquationObjects K L R c θL θR η hf P hB hfixed candidates allowed v (b • y) =
      (familyEquationLabels K L R c θL θR η hf P candidates allowed v).toMultiplicative b •
        familyEquationObjects K L R c θL θR η hf P hB hfixed candidates allowed v y := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  funext e
  let y0 := familyEquationObjects K L R c θL θR η hf P hB hfixed candidates allowed v y
  let b0 := familyEquationLabels K L R c θL θR η hf P candidates allowed v b.toAdd
  have hx : y0.1.1.1 e = y.1.1.1 e :=
    family_equation_edge_value K L R c θL θR η hf P hB hfixed candidates allowed v y e.1
  have hb : b0.1 = b.toAdd.1 := by
    apply Subtype.ext
    funext w
    exact family_equation_label_value K L R c θL θR η hf P candidates allowed v b.toAdd w.1
  have hd := congrArg (fun h : RelativeCover.C1 (M) ClosedRegion.all P => h.1 e)
    (family_relative_d0 K L R c θL θR η hf P v b.toAdd.1)
  have hd' : (RelativeCover.d0 (Mv v) ClosedRegion.all P b.toAdd.1).1 e =
      (RelativeCover.d0 (M) ClosedRegion.all P b0.1).1 e :=
    hd.trans (congrArg (fun a : RelativeCover.C0 (M) ClosedRegion.all P =>
      (RelativeCover.d0 (M) ClosedRegion.all P a).1 e) hb.symm)
  let Qv := coefficient K (familyOriginal K L θL v) (familyReference K R θR v)
    (familyComparisons K c η v) (family_aligned K R θR hf v) e.1.2.1
  let Q0 := coefficient K L R c hf e.1.2.1
  have ha :
      @HAdd.hAdd ((Mv v).A e.1.2.1) ((Mv v).A e.1.2.1) ((Mv v).A e.1.2.1) inferInstance
        (y.1.1.1 e) ((RelativeCover.d0 (Mv v) ClosedRegion.all P b.toAdd.1).1 e) =
      @HAdd.hAdd ((M).A e.1.2.1) ((M).A e.1.2.1) ((M).A e.1.2.1) inferInstance
        (y0.1.1.1 e) ((RelativeCover.d0 (M) ClosedRegion.all P b0.1).1 e) := by
    apply Q0.injective
    calc
      _ = Qv (@HAdd.hAdd ((Mv v).A e.1.2.1) ((Mv v).A e.1.2.1) ((Mv v).A e.1.2.1) inferInstance
        (y.1.1.1 e) ((RelativeCover.d0 (Mv v) ClosedRegion.all P b.toAdd.1).1 e)) := rfl
      _ = Qv (y.1.1.1 e) + Qv ((RelativeCover.d0 (Mv v) ClosedRegion.all P b.toAdd.1).1 e) :=
        Qv.map_add _ _
      _ = Q0 (y0.1.1.1 e) + Q0 ((RelativeCover.d0 (M) ClosedRegion.all P b0.1).1 e) :=
        congrArg₂ HAdd.hAdd (congrArg Q0 hx).symm (congrArg Q0 hd')
      _ = _ := (Q0.map_add _ _).symm
  calc
    _ = (b • y).1.1.1 e :=
      family_equation_edge_value K L R c θL θR η hf P hB hfixed candidates allowed v (b • y) e.1
    _ = _ := SupportedEquation.gauge_value (Mv v) P ClosedRegion.all candidates allowed (δv v) b.toAdd y e
    _ = _ := ha
    _ = _ := (SupportedEquation.gauge_value (M) P ClosedRegion.all candidates allowed (δa v) b0 y0 e).symm

set_option synthInstance.maxHeartbeats 200000

/-- All original parameter equations have full native coordinate equivalences to the same fixed linear equation with its generated affine defect. -/
noncomputable def familyEquationEquivalence (v : V) :
    SupportedEquation.Groupoid (Mv v) P ClosedRegion.all candidates allowed (δv v) ≌
      SupportedEquation.Groupoid (M) P ClosedRegion.all candidates allowed (δa v) :=
  changedLabelEquivalence (familyEquationLabels K L R c θL θR η hf P candidates allowed v).toMultiplicative
    (familyEquationObjects K L R c θL θR η hf P hB hfixed candidates allowed v)
    (family_equation_equivariant K L R c θL θR η hf P hB hfixed candidates allowed v)

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
