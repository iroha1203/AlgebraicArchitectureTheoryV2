import ResearchLean.AG.AtlasCoefficientFiber.DualRestriction
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# G-135 B：実chain homologyの双対とcochain homology

体上のdualRestrict全射性と、微分双対の実像を使う。
同型は閉路代表の評価を保存する。

## Implementation notes

閉cochainの制限とquotient liftを使い、dualRestrict全射性とdualMap像の定理で
標準H¹商への同型を作る。同型を証明fieldとして受け取る案は採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
universe u
section Duality
variable {X0 X1 X2 : Type u} [AddCommGroup X0] [AddCommGroup X1] [AddCommGroup X2]
variable [Module ℚ X0] [Module ℚ X1] [Module ℚ X2]
variable [FiniteDimensional ℚ X0] [FiniteDimensional ℚ X1] [FiniteDimensional ℚ X2]
variable (a : X1 →ₗ[ℚ] X0) (v : X2 →ₗ[ℚ] X1) (hv : a.comp v = 0)

/-- 実第二微分の閉路への余域制限。 -/
def chainBoundaryToCycles : X2 →ₗ[ℚ] LinearMap.ker a :=
  v.codRestrict _ (fun x => LinearMap.congr_fun hv x)

/-- 実微分から作る一次chain homology。 -/
abbrev ChainFirstHomology := LinearMap.ker a ⧸ LinearMap.range (chainBoundaryToCycles a v hv)

/-- 同じ二微分を双対化した三項cochain複体。 -/
abbrev chainDualComplex : ThreeCochainComplex ℚ where
  C0 := Module.Dual ℚ X0
  C1 := Module.Dual ℚ X1
  C2 := Module.Dual ℚ X2
  d0 := a.dualMap
  d1 := v.dualMap
  d1_comp_d0 := by
    intro z
    apply LinearMap.ext
    intro x
    change z (a (v x)) = 0
    rw [show a (v x) = 0 from LinearMap.congr_fun hv x, map_zero]

/-- 閉cochainを閉路代表で評価する、実homology双対への写像。 -/
def cocycleHomologyEvaluation : LinearMap.ker v.dualMap →ₗ[ℚ]
    Module.Dual ℚ (ChainFirstHomology a v hv) where
  toFun z := (LinearMap.range (chainBoundaryToCycles a v hv)).liftQ
    ((LinearMap.ker a).dualRestrict z.1) (by
      rintro x ⟨y, rfl⟩
      exact LinearMap.congr_fun z.2 y)
  map_add' x y := by
    apply LinearMap.ext
    intro z
    induction z using Submodule.Quotient.induction_on with
    | _ z => rfl
  map_smul' r x := by
    apply LinearMap.ext
    intro z
    induction z using Submodule.Quotient.induction_on with
    | _ z => rfl

omit [FiniteDimensional ℚ X0] [FiniteDimensional ℚ X1] [FiniteDimensional ℚ X2] in
/-- 評価写像は同じ原閉路の値を読む。 -/
@[simp] theorem cocycleHomologyEvaluation_mk (z : LinearMap.ker v.dualMap) (x : LinearMap.ker a) :
    cocycleHomologyEvaluation a v hv z (Submodule.Quotient.mk x) = z.1 x.1 := rfl

omit [FiniteDimensional ℚ X0] [FiniteDimensional ℚ X1] [FiniteDimensional ℚ X2] in
/-- 任意のhomology汎関数を原chain cochainへ延長することで全射性を導く。 -/
theorem cocycleHomologyEvaluation_surjective : Function.Surjective (cocycleHomologyEvaluation a v hv) := by
  intro z
  let w := z.comp (LinearMap.range (chainBoundaryToCycles a v hv)).mkQ
  obtain ⟨f, hf⟩ := Subspace.dualRestrict_surjective (W := LinearMap.ker a) w
  have hc : v.dualMap f = 0 := by
    apply LinearMap.ext
    intro y
    change f (v y) = 0
    have hh := LinearMap.congr_fun hf (chainBoundaryToCycles a v hv y)
    change f (v y) = w (chainBoundaryToCycles a v hv y) at hh
    rw [hh]
    change z (Submodule.Quotient.mk (chainBoundaryToCycles a v hv y)) = 0
    have hz : Submodule.Quotient.mk (chainBoundaryToCycles a v hv y) =
        (0 : ChainFirstHomology a v hv) :=
      (Submodule.Quotient.mk_eq_zero (LinearMap.range (chainBoundaryToCycles a v hv))).mpr ⟨y, rfl⟩
    rw [hz, map_zero]
  refine ⟨⟨f, hc⟩, ?_⟩
  apply LinearMap.ext
  intro x
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    exact LinearMap.congr_fun hf x

/-- 閉路で零評価となる閉cochainは、同じ第一微分の双対像そのものである。 -/
theorem cocycleHomologyEvaluation_ker :
    LinearMap.ker (cocycleHomologyEvaluation a v hv) =
      LinearMap.range (chainDualComplex a v hv).boundaryToCycles := by
  ext z
  constructor
  · intro hz
    have hza : z.1 ∈ (LinearMap.ker a).dualAnnihilator := by
      rw [Submodule.mem_dualAnnihilator]
      intro x hx
      have hh := LinearMap.congr_fun (show cocycleHomologyEvaluation a v hv z = 0 from hz) (Submodule.Quotient.mk (⟨x, hx⟩ : LinearMap.ker a))
      exact hh
    rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hza
    obtain ⟨f, hf⟩ := hza
    exact ⟨f, Subtype.ext hf⟩
  · rintro ⟨f, rfl⟩
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      change f (a x.1) = 0
      rw [x.2, map_zero]

/-- 同じ双対三項cochain H¹とchain H₁双対の両方向同型。 -/
def chainHomologyDualEquiv : (chainDualComplex a v hv).H1 ≃ₗ[ℚ]
    Module.Dual ℚ (ChainFirstHomology a v hv) :=
  (Submodule.quotEquivOfEq _ _ (cocycleHomologyEvaluation_ker a v hv).symm).trans
    ((cocycleHomologyEvaluation a v hv).quotKerEquivOfSurjective
      (cocycleHomologyEvaluation_surjective a v hv))

/-- 同型は同じ閉cochain・閉chain代表の評価を保つ。 -/
@[simp] theorem chainHomologyDualEquiv_mk (z : LinearMap.ker (chainDualComplex a v hv).d1)
    (x : LinearMap.ker a) :
    chainHomologyDualEquiv a v hv (Submodule.Quotient.mk z) (Submodule.Quotient.mk x) = z.1 x.1 := rfl

end Duality
end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.chainBoundaryToCycles
#print axioms AAT.AG.AtlasCoefficientFiber.ChainFirstHomology
#print axioms AAT.AG.AtlasCoefficientFiber.chainDualComplex
#print axioms AAT.AG.AtlasCoefficientFiber.cocycleHomologyEvaluation
#print axioms AAT.AG.AtlasCoefficientFiber.cocycleHomologyEvaluation_mk
#print axioms AAT.AG.AtlasCoefficientFiber.cocycleHomologyEvaluation_surjective
#print axioms AAT.AG.AtlasCoefficientFiber.cocycleHomologyEvaluation_ker
#print axioms AAT.AG.AtlasCoefficientFiber.chainHomologyDualEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.chainHomologyDualEquiv_mk
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
