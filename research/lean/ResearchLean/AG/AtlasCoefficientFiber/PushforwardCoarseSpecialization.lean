import ResearchLean.AG.AtlasCoefficientFiber.DefectShortExact

/-!
# G-135 C：原Pを粗係数に選ぶ補助特殊化

## Implementation notes

元T0の粗複体Cとηを変更しない。補助比較では同じ原Pを始域に選び、unitを恒等、
直接射を原εとする。原εH¹単射性と同じ五項列から核零/余核kerτを得る。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision TwoPhase
open AtlasDefectComposition
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf) (A : Set qc.Target)

/-- 補助粗係数を同じ原Pに選んだ場合の恒等unit。 -/
def pushforwardCoarseUnit : ThreeCochainComplex.Hom (pushforwardComplex M A) (pushforwardComplex M A) :=
  cochainId (pushforwardComplex M A)

/-- 同じ原Pから細複体への直接比較は原εである。 -/
def pushforwardCoarseComparison := evaluationHom M A

/-- 補助恒等unitの全三次数は標準恒等Homに一致する。 -/
theorem pushforwardCoarseUnit_eq : pushforwardCoarseUnit M A = cochainId (pushforwardComplex M A) := rfl

/-- 補助比較を原εへ読む全Hom等号。 -/
theorem pushforwardCoarseComparison_eq : pushforwardCoarseComparison M A = evaluationHom M A := rfl

/-- 補助P粗係数の実直接比較は原εと恒等unitの全Hom合成である。 -/
theorem pushforwardCoarse_factorization : pushforwardCoarseComparison M A =
    cochainComp (pushforwardCoarseUnit M A) (evaluationHom M A) := by
  rw [pushforwardCoarseComparison_eq, pushforwardCoarseUnit_eq]
  apply cochain_ext <;> rfl

/-- 同じ補助unitの零延長は全整数次数の恒等射。 -/
theorem pushforwardCoarseUnit_standard : zeroExtensionMap (pushforwardCoarseUnit M A) =
    𝟙 (zeroExtension (pushforwardComplex M A)) := by
  rw [pushforwardCoarseUnit_eq, zeroExtensionMap_id]

/-- 同じP粗係数比較の標準H¹核は原εの単射性により零。 -/
theorem pushforwardCoarseH1_kernel : LinearMap.ker
    (HomologicalComplex.homologyMap (zeroExtensionMap (pushforwardCoarseComparison M A)) (1 : ℤ)).hom = ⊥ := by
  rw [pushforwardCoarseComparison_eq]
  exact LinearMap.ker_eq_bot.mpr (evaluationH1_injective M A)

/-- 同じ補助比較の余核は原制限により同じkerτと両方向同型。 -/
def pushforwardCoarseCokernelEquiv :
    ((zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology (1 : ℤ) ⧸
      LinearMap.range (HomologicalComplex.homologyMap
        (zeroExtensionMap (pushforwardCoarseComparison M A)) (1 : ℤ)).hom) ≃ₗ[ℚ]
      LinearMap.ker (connectingTau M A) := evaluationCokernelTauKernelEquiv M A

/-- 補助余核同型は全商代表を同じ原fiber制限値へ送る。 -/
@[simp] theorem pushforwardCoarseCokernelEquiv_mk_val
    (x : (zeroExtension (Nf.targetSubsetComplex (comparisonFactor qc qf h ⁻¹' A))).homology (1 : ℤ)) :
    (pushforwardCoarseCokernelEquiv M A (Submodule.Quotient.mk x)).1 =
      fiberRestrictionH1 M A x := evaluationCokernelTauKernelEquiv_mk_val M A x

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.pushforwardCoarseUnit
#print axioms AAT.AG.AtlasCoefficientFiber.pushforwardCoarseComparison
#print axioms AAT.AG.AtlasCoefficientFiber.pushforwardCoarseUnit_eq
#print axioms AAT.AG.AtlasCoefficientFiber.pushforwardCoarseComparison_eq
#print axioms AAT.AG.AtlasCoefficientFiber.pushforwardCoarse_factorization
#print axioms AAT.AG.AtlasCoefficientFiber.pushforwardCoarseUnit_standard
#print axioms AAT.AG.AtlasCoefficientFiber.pushforwardCoarseH1_kernel
#print axioms AAT.AG.AtlasCoefficientFiber.pushforwardCoarseCokernelEquiv
#print axioms AAT.AG.AtlasCoefficientFiber.pushforwardCoarseCokernelEquiv_mk_val
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
