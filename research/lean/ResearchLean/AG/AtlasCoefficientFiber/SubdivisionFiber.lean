import ResearchLean.AG.AtlasCoefficientFiber.PhiInterval
import ResearchLean.AG.FaceRelationSubdivision.EdgeSubdivision

/-!
# 原辺分割の全部分台Φとfiber零性

Implementation notes: 全原セルと支持を保ったcollapseから唯一の退化辺cを読む。
元辺の台が空でもcの台は始点台であり、同じ全Aの証明で扱う。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber.SubdivisionFiber
open CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
universe u
variable {Source : Type u} {q : Reading Source}
variable (N : TargetSupportedNerve.{u,u} q) (e : N.nerve.EdgeComponent) (A : Set q.Target)

/-- 同じ原辺分割で退化する辺はcだけ。全出現対角辺はsome eに写る。 -/
theorem vertical_name (c : N.ChartInTargetSubset A)
    (v : PhiEdge (EdgeSubdivision.collapse N e) A c) :
    v.1.1 = Sum.inr (Sum.inl false) := by
  have hm := v.2.1
  change EdgeSubdivision.edgeImage N e v.1.1 = none at hm
  rcases h : v.1.1 with a | (b | o)
  · simp [h, EdgeSubdivision.edgeImage] at hm
  · cases b <;> simp [h, EdgeSubdivision.edgeImage] at hm ⊢
  · simp [h, EdgeSubdivision.edgeImage] at hm

/-- 原Option表から全AのΦ辺単一性を導く。 -/
theorem edge_subsingleton (c : N.ChartInTargetSubset A) :
    Subsingleton (PhiEdge (EdgeSubdivision.collapse N e) A c) :=
  ⟨fun v w => Subtype.ext (Subtype.ext ((vertical_name N e A c v).trans
    (vertical_name N e A c w).symm))⟩

/-- cの二端点は原old/freshタグで異なる。 -/
theorem endpoints_ne (c : N.ChartInTargetSubset A)
    (v : PhiEdge (EdgeSubdivision.collapse N e) A c) :
    phiEndpoint (EdgeSubdivision.collapse N e) A v true ≠
      phiEndpoint (EdgeSubdivision.collapse N e) A v false := by
  intro hh
  have hv := congrArg (fun v => v.1.1) hh
  change (EdgeSubdivision.nerve N e).edgeRight v.1.1 =
    (EdgeSubdivision.nerve N e).edgeLeft v.1.1 at hv
  rw [vertical_name N e A c v] at hv
  exact Sum.inr_ne_inl hv

/-- 全Aの原Φは点またはc区間であり、実H¹は零。 -/
theorem phiH1_zero (c : N.ChartInTargetSubset A) :
    Subsingleton (phiComplex (EdgeSubdivision.collapse N e) A c).H1 := by
  letI := edge_subsingleton N e A c
  exact phiH1_subsingleton_of_interval _ A c (endpoints_ne N e A c)

/-- 原κは同じ全Φ chain/cochain双対から零。 -/
theorem kappa_zero : kappa (EdgeSubdivision.collapse N e) A = 0 :=
  kappa_zero_of_phiH1_zero _ A (phiH1_zero N e A)
/-- 同じ原κ*も全Φ H¹零から零。 -/
theorem kappaStar_zero : kappaStar (EdgeSubdivision.collapse N e) A = 0 := by
  letI (c : N.ChartInTargetSubset A) := phiH1_zero N e A c
  exact LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero]; rfl
/-- 同じ原κ*核Rは全部分台で零空間。 -/
theorem R_zero : Subsingleton (R (EdgeSubdivision.collapse N e) A) := by
  letI (c : N.ChartInTargetSubset A) := phiH1_zero N e A c
  infer_instance
/-- 原標準接続射τは同じ全部分台Rから零。 -/
theorem tau_zero : connectingTau (EdgeSubdivision.collapse N e) A = 0 := by
  letI := R_zero N e A
  exact LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero]; rfl

end AAT.AG.AtlasCoefficientFiber.SubdivisionFiber

#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionFiber.vertical_name
#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionFiber.edge_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionFiber.endpoints_ne
#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionFiber.phiH1_zero
#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionFiber.kappa_zero
#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionFiber.kappaStar_zero
#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionFiber.R_zero
#print axioms AAT.AG.AtlasCoefficientFiber.SubdivisionFiber.tau_zero
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber.SubdivisionFiber
