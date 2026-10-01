import ResearchLean.AG.RelativeRepairComposition.AffineFamilyDifferentials
import ResearchLean.AG.RelativeRepairComposition.AffineConstantCoefficients
import ResearchLean.AG.RelativeRepairComposition.AffineFamilyRelativeDefect
import ResearchLean.AG.RelativeRepairComposition.SupportedNativeEquation
import ResearchLean.AG.RelativeRepairComposition.GeneratedDisplayComparison

/-!
# Original parameter equation coordinates preserve all values and labels

## Implementation notes

The input-generated whole-kernel transport identities prove that degree-zero
and degree-one differentials are the same. Coordinate changes preserve the actual
cochain values and every full original label; only the generated defect changes.
The independent native supported repair correspondence is then composed with
this value-preserving change, for every original allowed candidate range.
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

/-- The full original supported equation has exactly the same predicate at each actual parameter and its generated base affine defect. -/
theorem family_equation_iff (v : V) (h : RelativeCover.C1 (M) ClosedRegion.all P) :
    RelativeCover.d1 (Mv v) ClosedRegion.all P h = -(δv v) ↔
      RelativeCover.d1 (M) ClosedRegion.all P h = -(δa v) := by
  have hd := family_relative_d1 K L R c θL θR η hf P v h
  have hδ := family_native_relative_defect K L R c θL θR η hf P hB hfixed v
  have hn : -(δv v) = -(δa v) := by
    apply Subtype.ext
    funext f
    exact congrArg Neg.neg (congrArg (fun a : RelativeCover.C2 (M) ClosedRegion.all P => a.1 f) hδ)
  constructor
  · intro he
    exact hd.symm.trans (he.trans hn)
  · intro he
    exact hd.trans (he.trans hn.symm)

set_option maxHeartbeats 1000000

/-- Full supported coordinates on each actual parameter tower and the same base equation are mutually inverse with identical original edge values. -/
noncomputable def familyEquationSolutions (v : V) :
    CoverEquation.Solution (Mv v) P (δv v) ClosedRegion.all ≃
      CoverEquation.Solution (M) P (δa v) ClosedRegion.all :=
  Equiv.subtypeEquivRight (family_equation_iff K L R c θL θR η hf P hB hfixed v)

/-- Support is retained on every named original candidate by the full solution comparison. -/
noncomputable def familyEquationObjects (v : V) :
    SupportedEquation.Objects (Mv v) P ClosedRegion.all candidates allowed (δv v) ≃
      SupportedEquation.Objects (M) P ClosedRegion.all candidates allowed (δa v) :=
  Equiv.subtypeEquiv (familyEquationSolutions K L R c θL θR η hf P hB hfixed v)
    (fun _ => Iff.rfl)

/-- The same full original relative gauge subgroup is determined by unchanged original coboundary values. -/
theorem family_equation_labels_eq (v : V) :
    SupportedEquation.Labels (Mv v) P ClosedRegion.all candidates allowed =
      SupportedEquation.Labels (M) P ClosedRegion.all candidates allowed := by
  ext b
  constructor
  · intro hb e he
    have h := hb e he
    rw [family_relative_d0 K L R c θL θR η hf P v] at h
    exact h
  · intro hb e he
    rw [family_relative_d0 K L R c θL θR η hf P v]
    exact hb e he

/-- Every full original relative gauge label is retained, with the same original vertex values and supported coboundary. -/
noncomputable def familyEquationLabels (v : V) :
    SupportedEquation.Labels (Mv v) P ClosedRegion.all candidates allowed ≃+
      SupportedEquation.Labels (M) P ClosedRegion.all candidates allowed :=
  AddEquiv.addSubgroupCongr
    (family_equation_labels_eq K L R c θL θR η hf P candidates allowed v)

/-- Both directions preserve every full original edge-cochain value. -/
theorem family_equation_edge_value (v : V)
    (y : SupportedEquation.Objects (Mv v) P ClosedRegion.all candidates allowed (δv v))
    (e : EdgeName (K := K)) :
    (familyEquationObjects K L R c θL θR η hf P hB hfixed candidates allowed v y).1.1.1 ⟨e,Set.mem_univ e⟩ =
      y.1.1.1 ⟨e,Set.mem_univ e⟩ := rfl

/-- The native parameter-label comparison retains every actual original vertex value. -/
theorem family_equation_label_value (v : V)
    (b : SupportedEquation.Labels (Mv v) P ClosedRegion.all candidates allowed) (w : K.Vertex) :
    (familyEquationLabels K L R c θL θR η hf P candidates allowed v b).1.1 ⟨w,Set.mem_univ w⟩ =
      b.1.1 ⟨w,Set.mem_univ w⟩ := rfl

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
