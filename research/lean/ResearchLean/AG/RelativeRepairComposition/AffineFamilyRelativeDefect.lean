import ResearchLean.AG.RelativeRepairComposition.AffineFamilyLaws
import ResearchLean.AG.RelativeRepairComposition.SymbolicNativeLocal

/-!
# The primitive affine family supplies the symbolic native relative defect

## Implementation notes

The parameter term is generated from the actual comparison and reference-word
translations through the whole native kernel coordinate inverse. Its zero value
on the original fixed faces produces a relative cochain. Pointwise equality
identifies every parameter's actual native defect with this same affine cochain
family; it is not an assumed right-hand-side certificate.
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
variable (P : ClosedRegion K)
variable (hB : ∀ v : V, ∀ f ∈ P.faces, familyDefectLinear K R θR η v f = 0)

/-- The actual full affine defect's generated linear term is a cochain on the same original fixed-part relative space. -/
noncomputable def familyRelativeLinear : V →ₗ[k] RelativeCover.C2 (M) ClosedRegion.all P where
  toFun v := ⟨fun f => (linearCoefficient K L R c hf (K.twoTarget f.1)).symm
    (familyDefectLinear K R θR η v f.1),by
      intro f hfixed
      apply (linearCoefficient K L R c hf (K.twoTarget f.1)).injective
      rw [LinearEquiv.apply_symm_apply, hB v f.1 hfixed, map_zero]⟩
  map_add' v w := by
    apply Subtype.ext
    funext f
    change (linearCoefficient K L R c hf _).symm (familyDefectLinear K R θR η (v + w) f.1) = _
    rw [map_add]
    exact (linearCoefficient K L R c hf _).symm.map_add _ _
  map_smul' t v := by
    apply Subtype.ext
    funext f
    change (linearCoefficient K L R c hf _).symm (familyDefectLinear K R θR η (t • v) f.1) = _
    rw [map_smul]
    exact (linearCoefficient K L R c hf _).symm.map_smul t _

/-- Every full original face value of the generated native parameter cochain is its primitive vector update. -/
theorem family_relative_linear_value (v : V) (f : K.TwoCell) :
    coefficient K L R c hf (K.twoTarget f)
      ((familyRelativeLinear K L R c θR η hf P hB v).1 ⟨f,Set.mem_univ f⟩) =
        familyDefectLinear K R θR η v f :=
  (linearCoefficient K L R c hf (K.twoTarget f)).apply_symm_apply _

variable (hfixed : ∀ f ∈ P.faces,
  translation (k := k) (c f) * GroupExtension.pathValue K R (K.twoLeft f) =
    GroupExtension.pathValue K R (K.twoRight f))

/-- Every parameter's actual whole native defect is precisely the same base relative defect plus the input-generated linear cochain. -/
theorem family_native_relative_defect (v : V) :
    ActualEquation.defectFamily (familyTower K L R c θL θR η hf v) P
      (fixed_native K (familyOriginal K L θL v) (familyReference K R θR v)
        (familyComparisons K c η v) (family_aligned K R θR hf v) P
        (family_fixed_face K R c θR η hf P.faces hfixed hB v)) =
      SymbolicNativeLocal.defectFamily (M) P
        (ActualEquation.defectFamily (tower K L R c hf) P (fixed_native K L R c hf P hfixed))
        (familyRelativeLinear K L R c θR η hf P hB) v := by
  apply Subtype.ext
  funext f
  apply (coefficient K L R c hf (K.twoTarget f.1)).injective
  change coefficient K L R c hf (K.twoTarget f.1)
    ((familyTower K L R c θL θR η hf v).toTower.defect f.1) =
      coefficient K L R c hf (K.twoTarget f.1)
        ((tower K L R c hf).toTower.defect f.1 +
          (linearCoefficient K L R c hf (K.twoTarget f.1)).symm (familyDefectLinear K R θR η v f.1))
  have hcoord := (linearCoefficient K L R c hf (K.twoTarget f.1)).apply_symm_apply
    (familyDefectLinear K R θR η v f.1)
  change coefficient K L R c hf (K.twoTarget f.1)
    ((linearCoefficient K L R c hf (K.twoTarget f.1)).symm (familyDefectLinear K R θR η v f.1)) =
      familyDefectLinear K R θR η v f.1 at hcoord
  rw [map_add, hcoord, real_defect_native]
  exact family_defect_native K L R c θL θR η hf v f.1

end AAT.AG.RelativeRepairComposition.NativeAffine
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition
