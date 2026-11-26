import Formal.SHIGURE.Part2.Descent.ScalarExtensionInsertion
import Formal.SHIGURE.Part2.Descent.ScalarOverlapMaps

/-! # Inserting the ordered double overlap into a triple chart -/

namespace SHIGURE.CoefficientDescent

open CategoryTheory ModuleCat TensorProduct

noncomputable section

universe u

variable {A B T : Type u} [CommRing A] [CommRing B] [CommRing T] [Algebra A B]
  {M : ModuleCat.{u} B} [Module A M] [IsScalarTower A B M]

attribute [local instance] doubleModule

local notation "D₂" => B ⊗[A] B
local notation "f₀" => firstScalarEmbedding A B
local notation "f₁" => secondScalarEmbedding A B

/-- The coefficient map for the right side of the double overlap followed by its ordered insertion
in B.4. -/
private abbrev rightComposite (k : (B ⊗[A] B) →+* T) : B →+* T :=
  @RingHom.comp B (B ⊗[A] B) T _ _ _ k (secondScalarEmbedding A B)

variable {g : (B ⊗[A] B) →+* T} {r : B →+* T} (equal : rightComposite (A := A) (B := B) g = r)
  {V : ModuleCat.{u} T} (chart : (extendScalars (R := B) (S := T) r).obj M ≅ V)

set_option maxHeartbeats 850000 in
/-- Insert a vector in the right-hand double-overlap module into a chart
for a further scalar extension. -/
def orderedOverlapInsertion : ModuleCat.of D₂ (B ⊗[A] M) ⟶
    (restrictScalars (R := D₂) (S := T) g).obj V := by
  let E : ModuleCat.{u} B ⥤ ModuleCat.{u} D₂ := extendScalars (R := B) (S := D₂) f₁
  let R : ModuleCat.{u} T ⥤ ModuleCat.{u} D₂ := restrictScalars (R := D₂) (S := T) g
  let e : E.obj M ≅ ModuleCat.of D₂ (B ⊗[A] M) :=
    rightOverlapExtensionIso (A := A) (B := B) (N := M)
  let k : E.obj M ⟶ R.obj V :=
    @scalarExtensionInsert B D₂ T _ _ _ f₁ g r equal M V chart
  exact e.inv ≫ k

set_option maxRecDepth 2048 in
set_option maxHeartbeats 750000 in
/-- The linearity of the insertion transfers a coefficient in the first
tensor slot by precisely the pair projection's coefficient map. -/
theorem orderedOverlapInsertion_tmul (b : B) (x : M) :
    (orderedOverlapInsertion (g := g) (r := r) equal chart) (b ⊗ₜ[A] x) =
      g (b ⊗ₜ[A] (1 : B)) • chart.hom ((extendRestrictScalarsAdj r).unit.app M x) := by
  let R := rightOverlapExtensionIso (A := A) (B := B) (N := M)
  let F := orderedOverlapInsertion (g := g) (r := r) equal chart
  let P := ModuleCat.of D₂ (B ⊗[A] M)
  let y : P := (1 : B) ⊗ₜ[A] x
  let z := (extendRestrictScalarsAdj f₁).unit.app M x
  have right : R.hom z = y := rightOverlapExtensionIso_unit (A := A) (B := B) x
  have inv : R.inv (R.hom z) = z :=
    congrArg (fun k : (extendScalars f₁).obj M ⟶ (extendScalars f₁).obj M => k z) R.hom_inv_id
  have unit : F y = chart.hom ((extendRestrictScalarsAdj r).unit.app M x) := by
    change scalarExtensionInsert f₁ g equal chart (R.inv y) = _
    rw [← right, inv]
    exact scalarExtensionInsert_unit f₁ g equal chart x
  have pure_coefficient : (b ⊗ₜ[A] (1 : B)) • y = b ⊗ₜ[A] x := by
    change (b ⊗ₜ[A] (1 : B)) • ((1 : B) ⊗ₜ[A] x) = b ⊗ₜ[A] x
    rw [double_smul, smul_eq_mul, mul_one, one_smul]
  have h := F.hom.map_smul (b ⊗ₜ[A] (1 : B)) y
  change F ((b ⊗ₜ[A] (1 : B)) • y) = g (b ⊗ₜ[A] (1 : B)) • (F y : V) at h
  exact (congrArg (fun z : P => F z) pure_coefficient.symm).trans
    (h.trans (congrArg (fun z : V => g (b ⊗ₜ[A] (1 : B)) • z) unit))

set_option maxHeartbeats 750000 in
/-- A pulled comparison on a unit is the original ordered overlap followed
by insertion in the target chart. -/
theorem scalarOverlapPullHomAt_unit {r₀ : B →+* T} (equal₀ : @RingHom.comp B D₂ T _ _ _ g f₀ = r₀)
    (δ : (extendScalars f₀).obj M ≅ (extendScalars f₁).obj M) (x : M) :
    chart.hom (scalarExtensionPullHomAt f₀ f₁ g equal₀ equal δ.hom
      ((extendRestrictScalarsAdj r₀).unit.app M x)) =
      (orderedOverlapInsertion (g := g) (r := r) equal chart) (scalarOverlapIso (A := A) δ (x ⊗ₜ[A] (1 : B))) := by
  let R := rightOverlapExtensionIso (A := A) (B := B) (N := M)
  let y := δ.hom ((extendRestrictScalarsAdj f₀).unit.app M x)
  have step := scalarExtensionPullHomAt_on_unit f₁ g equal f₀ equal₀ δ.hom chart x
  have value : scalarOverlapIso (A := A) δ (x ⊗ₜ[A] (1 : B)) = R.hom y :=
    scalarOverlapIso_unit (A := A) δ x
  have inv : R.inv (R.hom y) = y :=
    congrArg (fun k : (extendScalars f₁).obj M ⟶ (extendScalars f₁).obj M => k y) R.hom_inv_id
  refine step.trans ?_
  rw [value]
  change scalarExtensionInsert f₁ g equal chart y =
    scalarExtensionInsert f₁ g equal chart (R.inv (R.hom y))
  rw [inv]

end

end SHIGURE.CoefficientDescent
