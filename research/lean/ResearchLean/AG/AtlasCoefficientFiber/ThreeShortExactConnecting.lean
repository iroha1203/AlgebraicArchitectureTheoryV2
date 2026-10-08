import ResearchLean.AG.AtlasCoefficientFiber.HomologyRepresentatives
import Mathlib.Algebra.Homology.HomologySequence

/-!
# G-135 B：三項零延長の同じ標準δの代表API

## Implementation notes

標準ShortExact.δ_eqを原三項代表へ戻す。補助定理の短完全性・lift等式は
方向仮定であり、適用では原filtrationから生成したものだけを渡す。
連結射を代表の期待値から定義する案は採用しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory Limits TwoPhase AtlasDefectComposition
universe u
variable {C D E : ThreeCochainComplex.{0,u} ℚ}

/-- 同じ零延長二射の標準δは、原lift微分の類を返す。 -/
theorem threeShortExact_connecting_representative
    (f : ThreeCochainComplex.Hom C D) (g : ThreeCochainComplex.Hom D E)
    (hzero : zeroExtensionMap f ≫ zeroExtensionMap g = 0)
    (hS : (ShortComplex.mk (zeroExtensionMap f) (zeroExtensionMap g) hzero).ShortExact)
    (q : LinearMap.ker E.d1) (w : D.C1) (p : C.C2)
    (hq : g.f1 w = q.1) (hp : f.f2 p = D.d1 w) :
    hS.δ (1 : ℤ) 2 (by rfl) (oldH1Equiv E (Submodule.Quotient.mk q)) =
      oldH2Equiv C (Submodule.Quotient.mk p) := by
  let x₃ : ModuleCat.of ℚ (ULift.{u} ℚ) ⟶ (zeroExtension E).X (1 : ℤ) := elementArrow q.1
  let x₂ : ModuleCat.of ℚ (ULift.{u} ℚ) ⟶ (zeroExtension D).X (1 : ℤ) := elementArrow w
  let x₁ : ModuleCat.of ℚ (ULift.{u} ℚ) ⟶ (zeroExtension C).X (2 : ℤ) := elementArrow p
  have hx₃ : x₃ ≫ (zeroExtension E).d 1 2 = 0 := by
    rw [show x₃ = elementArrow q.1 from rfl, elementArrow_comp]
    have hz : (zeroExtension E).d 1 2 q.1 = 0 := q.2
    rw [hz, elementArrow_zero]
  have hx₂ : x₂ ≫ (ShortComplex.mk (zeroExtensionMap f) (zeroExtensionMap g) hzero).g.f 1 = x₃ := by
    change elementArrow w ≫ (zeroExtensionMap g).f 1 = elementArrow q.1
    rw [elementArrow_comp]
    exact congrArg (elementArrow (X := (zeroExtension E).X 1)) hq
  have hx₁ : x₁ ≫ (ShortComplex.mk (zeroExtensionMap f) (zeroExtensionMap g) hzero).f.f 2 =
      x₂ ≫ (zeroExtension D).d 1 2 := by
    rw [show x₁ = elementArrow p from rfl, show x₂ = elementArrow w from rfl,
      elementArrow_comp, elementArrow_comp]
    exact congrArg (elementArrow (X := (zeroExtension D).X 2)) hp
  have hh := hS.δ_eq (1 : ℤ) 2 (by rfl) x₃ hx₃ x₂ hx₂ x₁ hx₁ 3 (by simp)
  have he := congrArg (fun f => f (ULift.up (1 : ℚ))) hh
  have hxp : x₁ ≫ (zeroExtension C).d 2 3 = 0 := by
    have hz := zeroExtension_d_zero C 2 (by decide) (by decide)
    have hz' : (zeroExtension C).d 2 3 = 0 := by simpa using hz
    rw [hz']
    simp only [comp_zero]
  change hS.δ (1 : ℤ) 2 (by rfl)
    ((zeroExtension E).homologyπ 1
      ((zeroExtension E).liftCycles x₃ 2 (by simp) hx₃ (ULift.up (1 : ℚ)))) =
    (zeroExtension C).homologyπ 2
      ((zeroExtension C).liftCycles x₁ 3 (by simp) hxp (ULift.up (1 : ℚ))) at he
  rw [zeroExtension_liftCycles_H1_apply, zeroExtension_liftCycles_H2_apply] at he
  have hq1 : (ConcreteCategory.hom x₃) (ULift.up (1 : ℚ)) = q.1 := elementArrow_one _
  have hp1 : (ConcreteCategory.hom x₁) (ULift.up (1 : ℚ)) = p := elementArrow_one _
  simpa only [hq1, hp1] using he

/-- 同じ標準δの0→1式は、原閉chart値と閉辺lift微分の類を返す。 -/
theorem threeShortExact_connecting_representative_zero
    (f : ThreeCochainComplex.Hom C D) (g : ThreeCochainComplex.Hom D E)
    (hzero : zeroExtensionMap f ≫ zeroExtensionMap g = 0)
    (hS : (ShortComplex.mk (zeroExtensionMap f) (zeroExtensionMap g) hzero).ShortExact)
    (q : LinearMap.ker E.d0) (w : D.C0) (p : LinearMap.ker C.d1)
    (hq : g.f0 w = q.1) (hp : f.f1 p.1 = D.d0 w) :
    hS.δ (0 : ℤ) 1 (by rfl) (oldH0Equiv E q) =
      oldH1Equiv C (Submodule.Quotient.mk p) := by
  let x₃ : ModuleCat.of ℚ (ULift.{u} ℚ) ⟶ (zeroExtension E).X (0 : ℤ) := elementArrow q.1
  let x₂ : ModuleCat.of ℚ (ULift.{u} ℚ) ⟶ (zeroExtension D).X (0 : ℤ) := elementArrow w
  let x₁ : ModuleCat.of ℚ (ULift.{u} ℚ) ⟶ (zeroExtension C).X (1 : ℤ) := elementArrow p.1
  have hx₃ : x₃ ≫ (zeroExtension E).d 0 1 = 0 := by
    rw [show x₃ = elementArrow q.1 from rfl, elementArrow_comp]
    have hz : (zeroExtension E).d 0 1 q.1 = 0 := q.2
    rw [hz, elementArrow_zero]
  have hx₂ : x₂ ≫ (ShortComplex.mk (zeroExtensionMap f) (zeroExtensionMap g) hzero).g.f 0 = x₃ := by
    change elementArrow w ≫ (zeroExtensionMap g).f 0 = elementArrow q.1
    rw [elementArrow_comp]
    exact congrArg (elementArrow (X := (zeroExtension E).X 0)) hq
  have hx₁ : x₁ ≫ (ShortComplex.mk (zeroExtensionMap f) (zeroExtensionMap g) hzero).f.f 1 =
      x₂ ≫ (zeroExtension D).d 0 1 := by
    rw [show x₁ = elementArrow p.1 from rfl, show x₂ = elementArrow w from rfl,
      elementArrow_comp, elementArrow_comp]
    exact congrArg (elementArrow (X := (zeroExtension D).X 1)) hp
  have hxp : x₁ ≫ (zeroExtension C).d 1 2 = 0 := by
    rw [show x₁ = elementArrow p.1 from rfl, elementArrow_comp]
    have hz : (zeroExtension C).d 1 2 p.1 = 0 := p.2
    rw [hz, elementArrow_zero]
  have hh := hS.δ_eq (0 : ℤ) 1 (by rfl) x₃ hx₃ x₂ hx₂ x₁ hx₁ 2 (by simp)
  have he := congrArg (fun f => f (ULift.up (1 : ℚ))) hh
  change hS.δ (0 : ℤ) 1 (by rfl)
    ((zeroExtension E).homologyπ 0
      ((zeroExtension E).liftCycles x₃ 1 (by simp) hx₃ (ULift.up (1 : ℚ)))) =
    (zeroExtension C).homologyπ 1
      ((zeroExtension C).liftCycles x₁ 2 (by simp) hxp (ULift.up (1 : ℚ))) at he
  rw [zeroExtension_liftCycles_H0_apply, zeroExtension_liftCycles_H1_apply] at he
  have hq1 : (ConcreteCategory.hom x₃) (ULift.up (1 : ℚ)) = q.1 := elementArrow_one _
  have hp1 : (ConcreteCategory.hom x₁) (ULift.up (1 : ℚ)) = p.1 := elementArrow_one _
  simpa only [hq1, hp1] using he

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.threeShortExact_connecting_representative
#print axioms AAT.AG.AtlasCoefficientFiber.threeShortExact_connecting_representative_zero
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
