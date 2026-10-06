import ResearchLean.AG.FaceRelationSubdivision.MixedSubsetHom
import ResearchLean.AG.FaceRelationSubdivision.SubsetComposition

/-!
# 同じ実subset射の対象等号移送

## Implementation notes

部分集合の原始等号は複体全体の等号に持ち上げ、同じHomの成分を保つ。
異なる型の射を非公式に同一視する案は採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
universe u

/-- source複体全体の等号に沿う同じHomの移送。 -/
def subsetSourceTransportHom {C D E : ThreeCochainComplex.{0,u} ℚ} (h : C = D)
    (f : ThreeCochainComplex.Hom C E) : ThreeCochainComplex.Hom D E := h ▸ f
/-- source等号移送のrefl評価。 -/
@[simp] theorem subsetSourceTransportHom_rfl {C E : ThreeCochainComplex.{0,u} ℚ}
    (f : ThreeCochainComplex.Hom C E) : subsetSourceTransportHom rfl f = f := rfl

variable {Source : Type u} {qc qf : Reading Source}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
namespace RawChainEquivalence
variable (P : RawChainEquivalence Nc Nf) (Ac : Set qc.Target) (Af Bf : Set qf.Target)
variable (hA : qf.read ⁻¹' Af = qc.read ⁻¹' Ac) (hAf : Af = Bf)

/-- 全target型の等号移送で同じ原始R射を保持する。 -/
theorem targetRHom_transport :
    subsetTransportHom (congrArg Nf.targetSubsetComplex hAf) (P.targetRHom Ac Af hA) =
      P.targetRHom Ac Bf (hAf ▸ hA) := by
  subst Bf
  rw [AAT.AG.FaceRelationSubdivision.transportHom_rfl]

/-- 全source型の等号移送で同じ原始S射を保持する。 -/
theorem targetSHom_transport :
    subsetSourceTransportHom (congrArg Nf.targetSubsetComplex hAf) (P.targetSHom Ac Af hA) =
      P.targetSHom Ac Bf (hAf ▸ hA) := by
  subst Bf
  rw [subsetSourceTransportHom_rfl]

end RawChainEquivalence
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
