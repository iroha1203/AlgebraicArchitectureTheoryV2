import ResearchLean.AG.AtlasCoefficientFiber.PhiComma
import ResearchLean.AG.AtlasCoefficientFiber.GammaComma
import ResearchLean.AG.AtlasCoefficientFiber.FiberComma
import ResearchLean.AG.AtlasCoefficientFiber.PushforwardUnit

/-!
# G-135 C：単一局所成分から原係数写像の同型を生成

## Implementation notes

標準右Kan stalkの既存成分同型を用い、定数写像をmathlibのpiUniqueへ同定する。
局所連結性からH¹消滅を推論せず、係数の次数別同型だけをここで得る。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
universe u

/-- 単一index上の定数写像は、成分同型と標準piUniqueから同型になる。 -/
theorem constantCoefficient_bijective {I V : Type u} [AddCommGroup V] [Module ℚ V]
    (e : V ≃ₗ[ℚ] (I → ℚ)) (f : ℚ →ₗ[ℚ] V)
    (he : ∀ q i, e (f q) i = q) (hN : Nonempty I) (hS : Subsingleton I) :
    Function.Bijective f := by
  letI := hS
  letI : Unique I := uniqueOfSubsingleton (Classical.choice hN)
  have hf : f = e.symm.toLinearMap.comp
      (LinearEquiv.piUnique ℚ (fun _ : I => ℚ)).symm.toLinearMap := by
    apply LinearMap.ext
    intro q
    apply e.injective
    funext i
    rw [he]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply]
    rfl
  rw [hf]
  exact e.symm.bijective.comp (LinearEquiv.piUnique ℚ (fun _ : I => ℚ)).symm.bijective

variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 原chart定数係数は実Φの各成分で同じ値を取る。 -/
theorem phiCoefficientConstant_apply (c : Nc.ChartInTargetSubset A) (q : ℚ)
    (i : ConnectedComponents (PhiInc M A c)) :
    phiCoefficientEquiv M A c
      (coefficientConstant (Carrier.preimageFunctor M A) (.chart c) q) i = q := by
  rw [phiCoefficientEquiv_apply, coefficientConstant_eval]

/-- 原辺定数係数は実Γの各成分で同じ値を取る。 -/
theorem gammaCoefficientConstant_apply (e : Nc.EdgeInTargetSubset A) (q : ℚ)
    (i : ConnectedComponents (GammaInc M A e)) :
    gammaCoefficientEquiv M A e
      (coefficientConstant (Carrier.preimageFunctor M A) (.edge e) q) i = q := by
  rw [gammaCoefficientEquiv_apply, coefficientConstant_eval]

/-- 原面定数係数は実Λの各持ち上げで同じ値を取る。 -/
theorem lambdaCoefficientConstant_apply (F : Nc.FaceInTargetSubset A) (q : ℚ)
    (i : LambdaFace M A F) :
    lambdaCoefficientEquiv M A F
      (coefficientConstant (Carrier.preimageFunctor M A) (.face F) q) i = q := by
  rw [lambdaCoefficientEquiv_apply, coefficientConstant_eval]

/-- Φの成分が一つなら原chart係数写像は同型である。 -/
theorem chartCoefficientConstant_bijective (c : Nc.ChartInTargetSubset A)
    (hN : Nonempty (ConnectedComponents (PhiInc M A c)))
    (hS : Subsingleton (ConnectedComponents (PhiInc M A c))) :
    Function.Bijective (coefficientConstant (Carrier.preimageFunctor M A) (.chart c)) :=
  constantCoefficient_bijective (phiCoefficientEquiv M A c) _
    (phiCoefficientConstant_apply M A c) hN hS

/-- Γの成分が一つなら原辺係数写像は同型である。 -/
theorem edgeCoefficientConstant_bijective (e : Nc.EdgeInTargetSubset A)
    (hN : Nonempty (ConnectedComponents (GammaInc M A e)))
    (hS : Subsingleton (ConnectedComponents (GammaInc M A e))) :
    Function.Bijective (coefficientConstant (Carrier.preimageFunctor M A) (.edge e)) :=
  constantCoefficient_bijective (gammaCoefficientEquiv M A e) _
    (gammaCoefficientConstant_apply M A e) hN hS

/-- Λの持ち上げが一つなら原面係数写像は同型である。 -/
theorem faceCoefficientConstant_bijective (F : Nc.FaceInTargetSubset A)
    (hN : Nonempty (LambdaFace M A F)) (hS : Subsingleton (LambdaFace M A F)) :
    Function.Bijective (coefficientConstant (Carrier.preimageFunctor M A) (.face F)) :=
  constantCoefficient_bijective (lambdaCoefficientEquiv M A F) _
    (lambdaCoefficientConstant_apply M A F) hN hS

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.constantCoefficient_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.phiCoefficientConstant_apply
#print axioms AAT.AG.AtlasCoefficientFiber.gammaCoefficientConstant_apply
#print axioms AAT.AG.AtlasCoefficientFiber.lambdaCoefficientConstant_apply
#print axioms AAT.AG.AtlasCoefficientFiber.chartCoefficientConstant_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.edgeCoefficientConstant_bijective
#print axioms AAT.AG.AtlasCoefficientFiber.faceCoefficientConstant_bijective
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
