import ResearchLean.AG.AtlasCoefficientFiber.SupportFiber

/-!
# G-135 D：空台に対する元Pとliteral Rの制限

## Implementation notes

原Selectedの支持証拠から空台に選択セルがないことを示す。
元Pの三次数と全Φ表示をそのまま使い、非空台の仮定を導入しない。
-/
noncomputable section
namespace AAT.AG.AtlasCoefficientFiber
open CategoryTheory CanonicalResolution ResolutionInvariance FaceRelationSubdivision
universe u
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve.{u,u} qc} {Nf : TargetSupportedNerve.{u,u} qf}
variable (M : IncidenceSupportedComparison qc qf h Nc Nf)

/-- 原支持セルは空台には存在しない。 -/
theorem supportSelected_empty {T I : Type u} (s : I → Set T) (i : Selected s ∅) : False := by
  obtain ⟨t, ht, ha⟩ := i.2
  exact ha

/-- 原P次数0の空台への実制限は零写像。 -/
theorem supportPushforward0_empty (B : Set qc.Target) :
    supportPushforward0 M (Set.empty_subset B) = 0 := by
  apply LinearMap.ext
  intro z
  funext c
  exact (supportSelected_empty Nc.chartSupport c).elim

/-- 原P次数1の空台への実制限は零写像。 -/
theorem supportPushforward1_empty (B : Set qc.Target) :
    supportPushforward1 M (Set.empty_subset B) = 0 := by
  apply LinearMap.ext
  intro z
  funext c
  exact (supportSelected_empty Nc.edgeSupport c).elim

/-- 原P次数2の空台への実制限は零写像。 -/
theorem supportPushforward2_empty (B : Set qc.Target) :
    supportPushforward2 M (Set.empty_subset B) = 0 := by
  apply LinearMap.ext
  intro z
  funext c
  exact (supportSelected_empty Nc.faceSupport c).elim

/-- 空台のliteral Rは同じ原全Φ表示の零部分空間である。 -/
theorem supportFiberR_empty_subsingleton : Subsingleton (R M ∅) := by
  constructor
  intro z w
  apply Subtype.ext
  funext c
  exact (supportSelected_empty Nc.chartSupport c).elim

/-- 空台へのliteral Rの実制限も零写像となる。 -/
theorem supportFiberR_empty (B : Set qc.Target) : supportFiberR M (Set.empty_subset B) = 0 := by
  letI := supportFiberR_empty_subsingleton M
  apply LinearMap.ext
  intro z
  exact Subsingleton.elim _ _

end AAT.AG.AtlasCoefficientFiber
#print axioms AAT.AG.AtlasCoefficientFiber.supportSelected_empty
#print axioms AAT.AG.AtlasCoefficientFiber.supportPushforward0_empty
#print axioms AAT.AG.AtlasCoefficientFiber.supportPushforward1_empty
#print axioms AAT.AG.AtlasCoefficientFiber.supportPushforward2_empty
#print axioms AAT.AG.AtlasCoefficientFiber.supportFiberR_empty_subsingleton
#print axioms AAT.AG.AtlasCoefficientFiber.supportFiberR_empty
#assert_standard_axioms_only AAT.AG.AtlasCoefficientFiber
