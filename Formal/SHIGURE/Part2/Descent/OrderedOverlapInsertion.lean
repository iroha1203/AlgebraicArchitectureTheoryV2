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

/-- Insert a vector in the right-hand double-overlap module into a chart
for a further scalar extension. -/
def orderedOverlapInsertion : ModuleCat.of D₂ (B ⊗[A] M) ⟶
    (restrictScalars (R := D₂) (S := T) g).obj V :=
  (rightOverlapExtensionIso (A := A) (B := B) (N := M)).inv ≫
    @scalarExtensionInsert B D₂ T _ _ _ f₁ g r equal M V chart

private theorem mod_comp_apply {R : Type u} [CommRing R] {X Y Z : ModuleCat.{u} R}
    (u : X ⟶ Y) (v : Y ⟶ Z) (x : X) : (u ≫ v) x = v (u x) := rfl

private theorem mod_inv_hom_apply {R : Type u} [CommRing R] {X Y : ModuleCat.{u} R}
    (e : X ≅ Y) (x : X) : e.inv (e.hom x) = x :=
  congrArg (fun k : X ⟶ X => k x) e.hom_inv_id

private theorem restrict_map_smul {R S : Type u} [CommRing R] [CommRing S] (h : R →+* S)
    {X : ModuleCat.{u} R} {Y : ModuleCat.{u} S}
    (f : X ⟶ (restrictScalars h).obj Y) (c : R) (x : X) :
    f (c • x) = h c • (f x : Y) :=
  f.hom.map_smul c x

private theorem orderedOverlapInsertion_apply (z : ModuleCat.of D₂ (B ⊗[A] M)) :
    (orderedOverlapInsertion (g := g) (r := r) equal chart) z =
      @scalarExtensionInsert B D₂ T _ _ _ f₁ g r equal M V chart
        ((rightOverlapExtensionIso (A := A) (B := B) (N := M)).inv z) :=
  mod_comp_apply _ _ z

set_option maxRecDepth 2048 in
/-- The linearity of the insertion transfers a coefficient in the first
tensor slot by precisely the pair projection's coefficient map. -/
theorem orderedOverlapInsertion_tmul (b : B) (x : M) :
    (orderedOverlapInsertion (g := g) (r := r) equal chart) (b ⊗ₜ[A] x) =
      g (b ⊗ₜ[A] (1 : B)) • chart.hom ((extendRestrictScalarsAdj r).unit.app M x) := by
  let R := rightOverlapExtensionIso (A := A) (B := B) (N := M)
  let F := orderedOverlapInsertion (g := g) (r := r) equal chart
  have unit : F ((1 : B) ⊗ₜ[A] x) = chart.hom ((extendRestrictScalarsAdj r).unit.app M x) := by
    rw [orderedOverlapInsertion_apply, ← rightOverlapExtensionIso_unit (A := A) (B := B) x,
      mod_inv_hom_apply R]
    exact scalarExtensionInsert_unit f₁ g equal chart x
  have pure_coefficient :
      ((b ⊗ₜ[A] (1 : B)) : D₂) • (((1 : B) ⊗ₜ[A] x) : ModuleCat.of D₂ (B ⊗[A] M)) = b ⊗ₜ[A] x := by
    rw [double_smul, smul_eq_mul, mul_one, one_smul]
  have h := restrict_map_smul g F (b ⊗ₜ[A] (1 : B)) ((1 : B) ⊗ₜ[A] x)
  exact (congrArg (fun z : ModuleCat.of D₂ (B ⊗[A] M) => F z) pure_coefficient.symm).trans
    (h.trans (congrArg (fun z : V => g (b ⊗ₜ[A] (1 : B)) • z) unit))

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
  refine step.trans ?_
  rw [value, orderedOverlapInsertion_apply, mod_inv_hom_apply R]

end

end SHIGURE.CoefficientDescent
