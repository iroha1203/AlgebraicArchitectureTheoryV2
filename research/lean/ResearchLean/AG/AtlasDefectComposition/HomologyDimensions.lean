import ResearchLean.AG.AtlasDefectComposition.EndpointHomology
import ResearchLean.AG.AtlasDefectComposition.ConeExactSequence
import Formal.Util.AssertStandardAxioms
/-! # 有限三項複体のhomologyの次元

実核・実像・標準homologyの次元をrank-nullityと商次元から結ぶ。
-/
noncomputable section
open CategoryTheory HomologicalComplex
namespace AAT.AG.AtlasDefectComposition
open TwoPhase
universe w
/-- 同じ線形射のcodRestrictは実像の次元を保つ。 -/
theorem finrank_range_codRestrict {A B : Type w} [AddCommGroup A] [Module ℚ A]
    [AddCommGroup B] [Module ℚ B] (f : A →ₗ[ℚ] B) (p : Submodule ℚ B)
    (h : ∀ x, f x ∈ p) :
    Module.finrank ℚ (LinearMap.range (f.codRestrict p h)) =
      Module.finrank ℚ (LinearMap.range f) := by
  let e : LinearMap.range (f.codRestrict p h) ≃ₗ[ℚ] LinearMap.range f :=
  { toFun := fun x => ⟨x.val.val,by obtain ⟨a,ha⟩:=x.property; exact ⟨a,congrArg Subtype.val ha⟩⟩
    invFun := fun y => ⟨⟨y.val,by
      obtain ⟨a,ha⟩ := y.property
      rw [← ha]
      exact h a⟩,by
      obtain ⟨a,ha⟩:=y.property
      exact ⟨a,Subtype.ext ha⟩⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }
  exact e.finrank_eq
/-- 既存H¹商の次元と二微分の実像次元は次数1の次元へ加算される。 -/
theorem oldH1_dimension (C : ThreeCochainComplex.{0,w} ℚ) :
    Module.finrank ℚ C.H1 + Module.finrank ℚ (LinearMap.range C.d0) +
      Module.finrank ℚ (LinearMap.range C.d1) = Module.finrank ℚ C.C1 := by
  have hq := Submodule.finrank_quotient_add_finrank (LinearMap.range C.boundaryToCycles)
  have hd := C.d1.finrank_range_add_finrank_ker
  have hb : Module.finrank ℚ (LinearMap.range C.boundaryToCycles) =
      Module.finrank ℚ (LinearMap.range C.d0) :=
    finrank_range_codRestrict C.d0 _ (fun x => C.d1_comp_d0 x)
  change Module.finrank ℚ C.H1 + _ = _ at hq
  rw [hb] at hq
  omega
/-- 標準H⁰は元の次数0核の次元を持つ。 -/
theorem standardH0_dimension (C : ThreeCochainComplex.{0,w} ℚ) :
    Module.finrank ℚ ((zeroExtension C).homology 0) +
      Module.finrank ℚ (LinearMap.range C.d0) = Module.finrank ℚ C.C0 := by
  rw [← (oldH0Equiv C).finrank_eq]
  change Module.finrank ℚ (LinearMap.ker C.d0) + _ = _
  have h := C.d0.finrank_range_add_finrank_ker
  omega
/-- 標準H¹は既存H¹の次元を持つ。 -/
theorem standardH1_dimension (C : ThreeCochainComplex.{0,w} ℚ) :
    Module.finrank ℚ ((zeroExtension C).homology 1) +
      Module.finrank ℚ (LinearMap.range C.d0) +
      Module.finrank ℚ (LinearMap.range C.d1) = Module.finrank ℚ C.C1 := by
  rw [← (oldH1Equiv C).finrank_eq]
  exact oldH1_dimension C
/-- 標準H²は元の終端商の次元を持つ。 -/
theorem standardH2_dimension (C : ThreeCochainComplex.{0,w} ℚ) :
    Module.finrank ℚ ((zeroExtension C).homology 2) +
      Module.finrank ℚ (LinearMap.range C.d1) = Module.finrank ℚ C.C2 := by
  rw [← (oldH2Equiv C).finrank_eq]
  change Module.finrank ℚ (C.C2 ⧸ LinearMap.range C.d1) + _ = _
  exact Submodule.finrank_quotient_add_finrank _
end AAT.AG.AtlasDefectComposition
#assert_standard_axioms_only AAT.AG.AtlasDefectComposition
