import ResearchLean.AG.AtlasCoefficientFiber.CarrierFiltration
import ResearchLean.AG.AtlasCoefficientFiber.DegenerateChain

/-!
# G-135 B：carrier次元鎖部分複体の標準零延長

## Implementation notes

原部分空間への微分制限を使い、包含を同じsupportedChainへ生成する。
0次は元K′₀でありL₀ではない。部分複体・mono・square-zeroを入力fieldに
する案は採用しない。すべて原微分の制限と包含の単射性から証明する。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target) (p : ℕ)

/-- 原carrier部分空間の辺から元全chartへの実微分。 -/
def carrierBoundary1 : carrierChain1 M A p →ₗ[ℚ] K0 Nf (comparisonFactor qc qf h ⁻¹' A) :=
  (chainD1 Nf _).comp (carrierChain1 M A p).subtype

/-- 原carrier面部分空間から辺部分空間への実微分。 -/
def carrierBoundary2 : carrierChain2 M A p →ₗ[ℚ] carrierChain1 M A p :=
  (chainD2 Nf _).restrict (fun x hx => carrierChain2_boundary_le M A p ⟨x, hx, rfl⟩)

/-- 辺微分は元の同じchain上の値。 -/
@[simp] theorem carrierBoundary1_apply (x : carrierChain1 M A p) :
    carrierBoundary1 M A p x = chainD1 Nf _ x.1 := rfl

/-- 面微分は元の同じchain上の値。 -/
@[simp] theorem carrierBoundary2_val (x : carrierChain2 M A p) :
    (carrierBoundary2 M A p x).1 = chainD2 Nf _ x.1 := rfl

/-- 原square-zeroが部分複体のsquare-zeroを生成する。 -/
theorem carrierBoundary_square : (carrierBoundary1 M A p).comp (carrierBoundary2 M A p) = 0 := by
  apply LinearMap.ext
  intro x
  exact LinearMap.congr_fun (chainD1_comp_chainD2 Nf _) x.1

/-- 部分複体の全整数次数の加群。 -/
def carrierDegreeObject (n : ℤ) : ModuleCat.{u} ℚ :=
  if n = 0 then ModuleCat.of ℚ (K0 Nf (comparisonFactor qc qf h ⁻¹' A))
  else if n = 1 then ModuleCat.of ℚ (carrierChain1 M A p)
  else if n = 2 then ModuleCat.of ℚ (carrierChain2 M A p)
  else ModuleCat.of ℚ PUnit.{u+1}

/-- 次数外の加群は零加群。 -/
theorem carrierDegreeObject_out (n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) (h2 : n ≠ 2) :
    carrierDegreeObject M A p n = ModuleCat.of ℚ PUnit.{u+1} := by
  simp [carrierDegreeObject, h0, h1, h2]

/-- 部分複体の実二微分を標準次数へ置く。 -/
def carrierDegreeDifferential (n : ℤ) : carrierDegreeObject M A p (n + 1) ⟶ carrierDegreeObject M A p n :=
  if h0 : n = 0 then by subst n; exact ModuleCat.ofHom (carrierBoundary1 M A p)
  else if h1 : n = 1 then by subst n; exact ModuleCat.ofHom (carrierBoundary2 M A p)
  else 0

/-- 全整数次数のsquare-zero。 -/
theorem carrierDegreeDifferential_square (n : ℤ) :
    carrierDegreeDifferential M A p (n + 1) ≫ carrierDegreeDifferential M A p n = 0 := by
  by_cases h0 : n = 0
  · subst n
    change ModuleCat.ofHom (carrierBoundary2 M A p) ≫ ModuleCat.ofHom (carrierBoundary1 M A p) = 0
    exact ModuleCat.hom_ext (carrierBoundary_square M A p)
  · by_cases h1 : n = 1
    · subst n; simp [carrierDegreeDifferential]
    · simp [carrierDegreeDifferential, h0, h1]

/-- 原carrier次元≤pが生成した同じ鎖部分複体。 -/
def carrierChain : ChainComplex (ModuleCat.{u} ℚ) ℤ :=
  ChainComplex.of (carrierDegreeObject M A p) (carrierDegreeDifferential M A p)
    (carrierDegreeDifferential_square M A p)

/-- 原K′への包含は0次恒等、1/2次subtype。 -/
def carrierDegreeInclusion (n : ℤ) :
    carrierDegreeObject M A p n ⟶ chainDegreeObject Nf (comparisonFactor qc qf h ⁻¹' A) n :=
  if h0 : n = 0 then by subst n; exact 𝟙 _
  else if h1 : n = 1 then by subst n; exact ModuleCat.ofHom (carrierChain1 M A p).subtype
  else if h2 : n = 2 then by subst n; exact ModuleCat.ofHom (carrierChain2 M A p).subtype
  else 0

/-- 次数外の包含は零射。 -/
theorem carrierDegreeInclusion_out (n : ℤ) (h0 : n ≠ 0) (h1 : n ≠ 1) (h2 : n ≠ 2) :
    carrierDegreeInclusion M A p n = 0 := by
  simp [carrierDegreeInclusion, h0, h1, h2]

/-- 実微分制限から元K′への可換性を導く。 -/
theorem carrierDegreeInclusion_comm (n : ℤ) :
    carrierDegreeInclusion M A p (n + 1) ≫ chainDegreeDifferential Nf _ n =
      carrierDegreeDifferential M A p n ≫ carrierDegreeInclusion M A p n := by
  by_cases h0 : n = 0
  · subst n
    change ModuleCat.ofHom (carrierChain1 M A p).subtype ≫ ModuleCat.ofHom (chainD1 Nf _) =
      ModuleCat.ofHom (carrierBoundary1 M A p) ≫ 𝟙 _
    rw [Category.comp_id]
    rfl
  · by_cases h1 : n = 1
    · subst n
      apply ModuleCat.hom_ext
      exact LinearMap.ext fun x => (carrierBoundary2_val M A p x).symm
    · rw [chainDegreeDifferential_out Nf _ n h0 h1]
      simp [carrierDegreeDifferential, h0, h1]

/-- carrier部分複体から同じ原supportedChainへの標準包含。 -/
def carrierChainInclusion : carrierChain M A p ⟶ supportedChain Nf (comparisonFactor qc qf h ⁻¹' A) :=
  ChainComplex.ofHom _ _ _ _ _ _ (carrierDegreeInclusion M A p) (carrierDegreeInclusion_comm M A p)

/-- 標準包含の実次数成分。 -/
@[simp] theorem carrierChainInclusion_f (n : ℤ) :
    (carrierChainInclusion M A p).f n = carrierDegreeInclusion M A p n := rfl

/-- 原部分空間の包含は標準chain圏でも単射。 -/
instance carrierChainInclusion_mono : Mono (carrierChainInclusion M A p) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  rw [carrierChainInclusion_f]
  apply (ModuleCat.mono_iff_injective _).mpr
  by_cases h0 : n = 0
  · subst n
    exact Function.injective_id
  · by_cases h1 : n = 1
    · subst n
      exact (carrierChain1 M A p).injective_subtype
    · by_cases h2 : n = 2
      · subst n
        exact (carrierChain2 M A p).injective_subtype
      · rw [carrierDegreeInclusion_out M A p n h0 h1 h2]
        change Function.Injective (0 : carrierDegreeObject M A p n →ₗ[ℚ] chainDegreeObject Nf _ n)
        haveI : Subsingleton (carrierDegreeObject M A p n) := by
          rw [carrierDegreeObject_out M A p n h0 h1 h2]
          infer_instance
        intro x y _
        exact Subsingleton.elim x y

end AAT.AG.AtlasCoefficientFiber

#print axioms AAT.AG.AtlasCoefficientFiber.carrierBoundary1
#print axioms AAT.AG.AtlasCoefficientFiber.carrierBoundary2
#print axioms AAT.AG.AtlasCoefficientFiber.carrierBoundary1_apply
#print axioms AAT.AG.AtlasCoefficientFiber.carrierBoundary2_val
#print axioms AAT.AG.AtlasCoefficientFiber.carrierBoundary_square
#print axioms AAT.AG.AtlasCoefficientFiber.carrierDegreeObject
#print axioms AAT.AG.AtlasCoefficientFiber.carrierDegreeObject_out
#print axioms AAT.AG.AtlasCoefficientFiber.carrierDegreeDifferential
#print axioms AAT.AG.AtlasCoefficientFiber.carrierDegreeDifferential_square
#print axioms AAT.AG.AtlasCoefficientFiber.carrierChain
#print axioms AAT.AG.AtlasCoefficientFiber.carrierDegreeInclusion
#print axioms AAT.AG.AtlasCoefficientFiber.carrierDegreeInclusion_out
#print axioms AAT.AG.AtlasCoefficientFiber.carrierDegreeInclusion_comm
#print axioms AAT.AG.AtlasCoefficientFiber.carrierChainInclusion
#print axioms AAT.AG.AtlasCoefficientFiber.carrierChainInclusion_f
#print axioms AAT.AG.AtlasCoefficientFiber.carrierChainInclusion_mono
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
