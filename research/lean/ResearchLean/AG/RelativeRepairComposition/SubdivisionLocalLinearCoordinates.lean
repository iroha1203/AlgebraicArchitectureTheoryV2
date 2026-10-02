import ResearchLean.AG.RelativeRepairComposition.SubdivisionLocalEquations
import ResearchLean.AG.RelativeRepairComposition.SubdivisionLinearCochains

/-!
# Linear local coordinates on the same actual subdivision kernels

## Implementation notes

The local supplemental carrier remains the actual fresh projection kernel with
its incidence condition. Scalars preserve that condition. Linearity is proved
on the already constructed full additive comparisons; no new comparison law is
supplied. Degreewise extension is used only as a linear map of families.
-/
namespace AAT.AG.RelativeRepairComposition.Family
universe uk ui ua
variable {k : Type uk} [Field k]
variable {I : Type ui} (A : I → Type ua)
variable [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)]

/-- Degreewise zero extension respects the same pointwise scalars. -/
theorem extend_smul (s : Set I) (t : k) (b : ∀ i : s, A i.1) :
    extend A s (t • b) = t • extend A s b := by
  funext i
  by_cases hi : i ∈ s
  · rw [extend_on A s (t • b) i hi]
    change t • b ⟨i,hi⟩ = t • extend A s b i
    rw [extend_on A s b i hi]
  · rw [extend_off A s (t • b) i hi]
    change 0 = t • extend A s b i
    rw [extend_off A s b i hi,smul_zero]

end AAT.AG.RelativeRepairComposition.Family

namespace AAT.AG.RelativeRepairComposition.Subdivision.LocalLinear
open CategoryTheory TransportCoherence TransportCoherence.Arbitrary AbelianLiftingObstruction
universe uk uG uE uB uD vE vB vD
variable {k : Type uk} [Field k]
variable {K : FiniteTransportPresentation.{uG}}
variable {E : Type uE} {B : Type uB} {D : Type uD}
variable [Category.{vE} E] [Category.{vB} B] [Category.{vD} D]
variable {p : E ⥤ B} {q : B ⥤ D}
variable (T : OriginalTowerPresentation K p q) (chosen : EdgeName (K := K))
variable (F : Factorization T chosen)
variable [∀ v, Module k (T.toTower.localCoefficients.A v)]
attribute [local instance] LinearCoefficients.coefficientModules
variable (U P : ClosedRegion K) (hp : chosen ∉ P.edges)

/-- Pointwise scalars preserve the full-or-zero actual local supplement. -/
noncomputable instance supplementSMul : SMul k (localSupplement T chosen F U) where
  smul t r := ⟨t • r.1,by
    intro hu
    rw [localSupplement_zero T chosen F U hu r,smul_zero]⟩

/-- The local supplement inherits the complete actual fresh coefficient module. -/
noncomputable instance supplementModule : Module k (localSupplement T chosen F U) :=
  Function.Injective.module k (localSupplement T chosen F U).subtype
    Subtype.val_injective (fun _ _ => rfl)

/-- A supplemental scalar has exactly the original actual kernel value. -/
theorem supplement_smul_value (t : k) (r : localSupplement T chosen F U) :
    (t • r).1 = t • r.1 := rfl

variable (hlinear : ∀ {i j : K.Vertex} (e : K.Edge i j) (t : k)
  (x : T.toTower.localCoefficients.A i),
  T.toTower.localCoefficients.edge e (t • x) = t • T.toTower.localCoefficients.edge e x)

include hlinear in
/-- The whole old correction and whole first value respect actual scalars. -/
theorem local1_smul (t : k)
    (h : RelativeCover.C1 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P)) :
    local1Equiv T chosen F U P hp (t • h) =
      t • local1Equiv T chosen F U P hp h := by
  apply Prod.ext
  · apply Subtype.ext
    funext e
    rw [local1Equiv_old]
    change collapseCorrection T chosen F (Family.extend _ _ (t • h.1)) e.1 =
      t • (local1Equiv T chosen F U P hp h).1.1 e
    rw [Family.extend_smul,LinearCochains.collapse_smul T chosen F hlinear]
    rw [local1Equiv_old]
    rfl
  · apply Subtype.ext
    rw [local1Equiv_first]
    change Family.extend (fun e : EdgeName (K := presentation K chosen) =>
      (originalTower T chosen F).toTower.localCoefficients.A e.2.1)
      (expandedRegion K chosen U).edges (t • h.1) (firstEdgeName K chosen) =
      t • (local1Equiv T chosen F U P hp h).2.1
    rw [Family.extend_smul]
    rw [local1Equiv_first]
    rfl

/-- Linear local degree one uses the same actual collapse and unrestricted first value. -/
noncomputable def local1LinearEquiv :
    RelativeCover.C1 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P) ≃ₗ[k]
    (RelativeCover.C1 T.toTower.localCoefficients U P × localSupplement T chosen F U) where
  toAddEquiv := local1Equiv T chosen F U P hp
  map_smul' t h := local1_smul T chosen F U P hp hlinear t h

/-- The linear degree-one comparison has the unchanged complete additive value. -/
theorem local1LinearEquiv_value
    (h : RelativeCover.C1 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P)) :
    local1LinearEquiv T chosen F U P hp hlinear h = local1Equiv T chosen F U P hp h := rfl

/-- All old labels and the actual fresh displacement respect the original scalars. -/
theorem local0_smul (t : k)
    (b : RelativeCover.C0 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P)) :
    local0Equiv T chosen F U P hp (t • b) =
      t • local0Equiv T chosen F U P hp b := by
  apply Prod.ext
  · apply Subtype.ext
    funext v
    rfl
  · apply Subtype.ext
    change (displacementLocal0 T chosen F U P (t • b)).1 =
      t • (displacementLocal0 T chosen F U P b).1
    by_cases hu : chosen ∈ U.edges
    · rw [displacementLocal0_in T chosen F U P (t • b) hu,
        displacementLocal0_in T chosen F U P b hu]
      change t • b.1 ⟨.inr (),hu⟩ -
        rho1AddEquiv T chosen F (t • b.1 ⟨.inl chosen.1,(U.edge_closed _ hu).1⟩) = _
      rw [LinearCoefficients.rho1_smul,smul_sub]
    · rw [displacementLocal0_out T chosen F U P (t • b) hu,
        displacementLocal0_out T chosen F U P b hu,smul_zero]

/-- Linear local degree zero retains all original labels and all allowed displacement. -/
noncomputable def local0LinearEquiv :
    RelativeCover.C0 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P) ≃ₗ[k]
    (RelativeCover.C0 T.toTower.localCoefficients U P × localSupplement T chosen F U) where
  toAddEquiv := local0Equiv T chosen F U P hp
  map_smul' t b := local0_smul T chosen F U P hp t b

/-- The linear label comparison keeps exactly its full additive label coordinates. -/
theorem local0LinearEquiv_value
    (b : RelativeCover.C0 (originalTower T chosen F).toTower.localCoefficients
      (expandedRegion K chosen U) (expandedRegion K chosen P)) :
    local0LinearEquiv (k := k) T chosen F U P hp b = local0Equiv T chosen F U P hp b := rfl

end AAT.AG.RelativeRepairComposition.Subdivision.LocalLinear
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Family
#assert_standard_axioms_only AAT.AG.RelativeRepairComposition.Subdivision.LocalLinear
