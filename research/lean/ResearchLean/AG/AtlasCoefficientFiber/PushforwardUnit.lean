import ResearchLean.AG.AtlasCoefficientFiber.PushforwardComplex

/-!
# G-135 A：粗係数から順像係数への定数写像

## Implementation notes

各comma成分に同じ有理数を置き、極限同型の逆で順像の元を生成する。
ηを実比較uから逆算する案は、順像と二射の独立した構成を失うため採らない。
係数射の前合成評価から自然性を証明し、セル微分との可換性へ使う。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision CategoryTheory TwoPhase
universe u

/-- 各comma成分へ同じ有理数を置く、独立生成された係数写像。 -/
def coefficientConstant {J K : Type u} [Category.{u} J] [Category.{u} K]
    (φ : J ⥤ K) (k : K) : ℚ →ₗ[ℚ] (coefficientPushforward φ).obj k :=
  (coefficientCellIso φ k).inv.hom.comp
    (LinearMap.pi fun _ => (ULift.moduleEquiv.symm : ℚ ≃ₗ[ℚ] ULift.{u} ℚ).toLinearMap)

/-- 定数係数写像の全成分での評価。 -/
theorem coefficientConstant_eval {J K : Type u} [Category.{u} J] [Category.{u} K]
    (φ : J ⥤ K) (k : K) (q : ℚ) (c : ConnectedComponents (StructuredArrow k φ)) :
    (coefficientCellIso φ k).hom (coefficientConstant φ k q) c = ULift.up q := by
  change ((coefficientCellIso φ k).toLinearEquiv
    ((coefficientCellIso φ k).toLinearEquiv.symm (fun _ => ULift.up q))) c = ULift.up q
  rw [LinearEquiv.apply_symm_apply]

/-- 係数射は成分上の定数値を保存する。 -/
theorem coefficientConstant_naturality {J K : Type u} [Category.{u} J] [Category.{u} K]
    (φ : J ⥤ K) {k l : K} (f : k ⟶ l) (q : ℚ) :
    (coefficientPushforward φ).map f (coefficientConstant φ k q) =
      coefficientConstant φ l q := by
  apply (coefficientCellIso φ l).toLinearEquiv.injective
  change (coefficientCellIso φ l).hom (_) = (coefficientCellIso φ l).hom (_)
  funext c
  refine Quotient.inductionOn c ?_
  intro j
  rw [coefficientPushforward_map_eval, coefficientConstant_eval, coefficientConstant_eval]

variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- ηのchart成分。 -/
def unit0 : (Nc.targetSubsetComplex A).C0 →ₗ[ℚ] (pushforwardComplex M A).C0 :=
  LinearMap.pi fun c => (coefficientConstant (Carrier.preimageFunctor M A) (.chart c)).comp
    (LinearMap.proj c)

/-- ηの辺成分。 -/
def unit1 : (Nc.targetSubsetComplex A).C1 →ₗ[ℚ] (pushforwardComplex M A).C1 :=
  LinearMap.pi fun e => (coefficientConstant (Carrier.preimageFunctor M A) (.edge e)).comp
    (LinearMap.proj e)

/-- ηの面成分。 -/
def unit2 : (Nc.targetSubsetComplex A).C2 →ₗ[ℚ] (pushforwardComplex M A).C2 :=
  LinearMap.pi fun f => (coefficientConstant (Carrier.preimageFunctor M A) (.face f)).comp
    (LinearMap.proj f)

/-- ηのchart生成式。 -/
theorem unit0_apply (z : (Nc.targetSubsetComplex A).C0) (c : Nc.ChartInTargetSubset A) :
    unit0 M A z c = coefficientConstant (Carrier.preimageFunctor M A) (.chart c) (z c) := rfl

/-- ηの辺生成式。 -/
theorem unit1_apply (z : (Nc.targetSubsetComplex A).C1) (e : Nc.EdgeInTargetSubset A) :
    unit1 M A z e = coefficientConstant (Carrier.preimageFunctor M A) (.edge e) (z e) := rfl

/-- ηの面生成式。 -/
theorem unit2_apply (z : (Nc.targetSubsetComplex A).C2) (f : Nc.FaceInTargetSubset A) :
    unit2 M A z f = coefficientConstant (Carrier.preimageFunctor M A) (.face f) (z f) := rfl

/-- 定数係数写像は端点差分と可換である。 -/
theorem unit_comm0 (z : (Nc.targetSubsetComplex A).C0) :
    unit1 M A ((Nc.targetSubsetComplex A).d0 z) =
      (pushforwardComplex M A).d0 (unit0 M A z) := by
  funext e
  rw [unit1_apply, pushforwardComplex_d0_apply, unit0_apply, unit0_apply,
    Nc.targetSubsetComplex_d0_apply, map_sub]
  erw [coefficientConstant_naturality (Carrier.preimageFunctor M A)
    (IncHom.chartEdge (Nc.targetSubsetEdgeRight A e) e true rfl),
    coefficientConstant_naturality (Carrier.preimageFunctor M A)
      (IncHom.chartEdge (Nc.targetSubsetEdgeLeft A e) e false rfl)]

/-- 定数係数写像は三辺の符号付き和と可換である。 -/
theorem unit_comm1 (z : (Nc.targetSubsetComplex A).C1) :
    unit2 M A ((Nc.targetSubsetComplex A).d1 z) =
      (pushforwardComplex M A).d1 (unit1 M A z) := by
  funext f
  rw [unit2_apply, pushforwardComplex_d1_apply, unit1_apply, unit1_apply, unit1_apply,
    Nc.targetSubsetComplex_d1_apply, map_add, map_sub]
  erw [coefficientConstant_naturality (Carrier.preimageFunctor M A)
    (IncHom.edgeFace (Nc.targetSubsetFaceEdge0 A f) f 0 rfl),
    coefficientConstant_naturality (Carrier.preimageFunctor M A)
      (IncHom.edgeFace (Nc.targetSubsetFaceEdge1 A f) f 1 rfl),
    coefficientConstant_naturality (Carrier.preimageFunctor M A)
      (IncHom.edgeFace (Nc.targetSubsetFaceEdge2 A f) f 2 rfl)]

/-- 原始Mの実順像に対するη cochain Hom。 -/
def unitHom : ThreeCochainComplex.Hom (Nc.targetSubsetComplex A) (pushforwardComplex M A) where
  f0 := unit0 M A
  f1 := unit1 M A
  f2 := unit2 M A
  comm0 := unit_comm0 M A
  comm1 := unit_comm1 M A

/-- η Homの同じ次数0成分を返す定義所有者API。 -/
@[simp] theorem unitHom_f0 : (unitHom M A).f0 = unit0 M A := rfl

/-- η Homの同じ次数1成分を返す定義所有者API。 -/
@[simp] theorem unitHom_f1 : (unitHom M A).f1 = unit1 M A := rfl

/-- η Homの同じ次数2成分を返す定義所有者API。 -/
@[simp] theorem unitHom_f2 : (unitHom M A).f2 = unit2 M A := rfl

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientConstant
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientConstant_eval
#print axioms AAT.AG.AtlasCoefficientFiber.coefficientConstant_naturality
#print axioms AAT.AG.AtlasCoefficientFiber.unit0
#print axioms AAT.AG.AtlasCoefficientFiber.unit1
#print axioms AAT.AG.AtlasCoefficientFiber.unit2
#print axioms AAT.AG.AtlasCoefficientFiber.unit0_apply
#print axioms AAT.AG.AtlasCoefficientFiber.unit1_apply
#print axioms AAT.AG.AtlasCoefficientFiber.unit2_apply
#print axioms AAT.AG.AtlasCoefficientFiber.unit_comm0
#print axioms AAT.AG.AtlasCoefficientFiber.unit_comm1
#print axioms AAT.AG.AtlasCoefficientFiber.unitHom
#print axioms AAT.AG.AtlasCoefficientFiber.unitHom_f0
#print axioms AAT.AG.AtlasCoefficientFiber.unitHom_f1
#print axioms AAT.AG.AtlasCoefficientFiber.unitHom_f2
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
