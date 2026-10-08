import ResearchLean.AG.AtlasCoefficientFiber.CarrierFunctor
import ResearchLean.AG.AtlasCoefficientFiber.ConstantLimit
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# G-135 A：実carrierに沿う順像係数

## Implementation notes

順像を原始Mから生成したcarrierのpointwise右Kan拡張として作る。
任意の中間加群を先に選ぶ案は、comma極限という構成経路を満たさないため採らない。
有限性はfineセルとcoarse射の有限表示から導き、係数の有限次元性を追加仮定しない。
Φ・Γ・Λへの成分同定は、ここで作る実comma圏について後続で証明する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision CategoryTheory
universe u

/-- 有限対象と局所有限な射から、実comma対象の有限性を導く。 -/
instance structuredArrowFinite {J K : Type u} [Category.{u} J] [Category.{u} K]
    [Finite J] [∀ k l : K, Finite (k ⟶ l)] (φ : J ⥤ K) (k : K) :
    Finite (StructuredArrow k φ) := by
  apply Finite.of_surjective
    (fun j : (Σ x : J, k ⟶ φ.obj x) => StructuredArrow.mk j.2)
  intro j
  refine ⟨⟨j.right, j.hom⟩, ?_⟩
  apply StructuredArrow.obj_ext _ _ rfl
  simp

/-- 有限commaの連結成分も有限である。 -/
instance commaConnectedComponentsFinite {J K : Type u} [Category.{u} J] [Category.{u} K]
    [Finite J] [∀ k l : K, Finite (k ⟶ l)] (φ : J ⥤ K) (k : K) :
    Finite (ConnectedComponents (StructuredArrow k φ)) := by
  change Finite (Quotient _)
  infer_instance

/-- 実comma極限の成分同型から係数の有限次元性を導く。 -/
instance coefficientPushforwardFiniteDimensional {J K : Type u}
    [Category.{u} J] [Category.{u} K] [Finite J] [∀ k l : K, Finite (k ⟶ l)]
    (φ : J ⥤ K) (k : K) : FiniteDimensional ℚ ((coefficientPushforward φ).obj k) := by
  letI : FiniteDimensional ℚ (ULift.{u} ℚ) :=
    (ULift.moduleEquiv.symm : ℚ ≃ₗ[ℚ] ULift.{u} ℚ).finiteDimensional
  letI : FiniteDimensional ℚ ((constantRationalCone (StructuredArrow k φ)).pt) := by
    change FiniteDimensional ℚ (ConnectedComponents (StructuredArrow k φ) → ULift.{u} ℚ)
    infer_instance
  exact FiniteDimensional.of_injective (coefficientCellIso φ k).hom.hom
    (coefficientCellIso φ k).toLinearEquiv.injective

variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}

/-- Aの支持逆像から生成する、実carrierに沿う順像係数。 -/
def pushforwardCoefficients (M : IncidenceSupportedComparison qc qf h Nc Nf)
    (A : Set qc.Target) : Inc Nc A ⥤ ModuleCat.{u} ℚ :=
  coefficientPushforward (Carrier.preimageFunctor M A)

/-- 実Mの右Kan係数射は、全comma成分で原incidenceの前合成値になる。 -/
theorem pushforwardCoefficients_map_component_eval
    (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)
    {σ τ : Inc Nc A} (f : σ ⟶ τ) (z : (pushforwardCoefficients M A).obj σ)
    (c : CategoryTheory.ConnectedComponents (StructuredArrow τ (Carrier.preimageFunctor M A))) :
    (coefficientCellIso (Carrier.preimageFunctor M A) τ).hom
      ((pushforwardCoefficients M A).map f z) c =
    (coefficientCellIso (Carrier.preimageFunctor M A) σ).hom z
      ((StructuredArrow.map f).mapConnectedComponents c) :=
  coefficientPushforward_map_component_eval (Carrier.preimageFunctor M A) f z c

/-- 実順像のcounit。 -/
def pushforwardCounit (M : IncidenceSupportedComparison qc qf h Nc Nf)
    (A : Set qc.Target) :
    Carrier.preimageFunctor M A ⋙ pushforwardCoefficients M A ⟶
      constantRational (Inc Nf (comparisonFactor qc qf h ⁻¹' A)) :=
  coefficientCounit (Carrier.preimageFunctor M A)

/-- 実Mから生成した順像は標準右Kanの普遍性を持つ。 -/
instance pushforwardIsRightKanExtension
    (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target) :
    (pushforwardCoefficients M A).IsRightKanExtension (pushforwardCounit M A) :=
  inferInstanceAs ((coefficientPushforward (Carrier.preimageFunctor M A)).IsRightKanExtension
    (coefficientCounit (Carrier.preimageFunctor M A)))

/-- 実順像の各セル係数は有限次元である。 -/
instance pushforwardCoefficientFiniteDimensional
    (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target) (σ : Inc Nc A) :
    FiniteDimensional ℚ ((pushforwardCoefficients M A).obj σ) :=
  inferInstanceAs (FiniteDimensional ℚ
    ((coefficientPushforward (Carrier.preimageFunctor M A)).obj σ))

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.structuredArrowFinite
#print axioms AAT.AG.AtlasCoefficientFiber.commaConnectedComponentsFinite
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientPushforwardFiniteDimensional
#print axioms AAT.AG.AtlasCoefficientFiber.pushforwardCoefficients
#print axioms AAT.AG.AtlasCoefficientFiber.pushforwardCoefficients_map_component_eval
#print axioms AAT.AG.AtlasCoefficientFiber.pushforwardCounit
#print axioms AAT.AG.AtlasCoefficientFiber.pushforwardIsRightKanExtension
#print axioms AAT.AG.AtlasCoefficientFiber.pushforwardCoefficientFiniteDimensional
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
