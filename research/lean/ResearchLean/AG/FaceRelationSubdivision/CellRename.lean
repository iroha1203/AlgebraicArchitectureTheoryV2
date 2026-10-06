import ResearchLean.AG.FaceRelationSubdivision.ReadingPullback
import Formal.Util.AssertStandardAxioms

/-!
# 原始セル名の取り直し

## Implementation notes

有限性は旧セルと名前全単射から移す。端点・面の三辺・台を旧表から生成するため、
表示同型のincidenceを入力に要求しない。任意の新しい名前型を許す。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision
open CanonicalResolution ResolutionInvariance AtlasDefectComposition Cohomology
universe u
namespace CellRename
variable {Source : Type u} {q : Reading Source} (N : TargetSupportedNerve q)
variable {V E F : Type u} (cv : V ≃ N.nerve.Chart) (ce : E ≃ N.nerve.EdgeComponent)
variable (cf : F ≃ N.nerve.FaceComponent)

/-- 原始名前全単射で生成したnerve表。 -/
def nerve : CoverNerve.{u} where
  Chart := V
  EdgeComponent := E
  FaceComponent := F
  edgeLeft e := cv.symm (N.nerve.edgeLeft (ce e))
  edgeRight e := cv.symm (N.nerve.edgeRight (ce e))
  faceEdge0 f := ce.symm (N.nerve.faceEdge0 (cf f))
  faceEdge1 f := ce.symm (N.nerve.faceEdge1 (cf f))
  faceEdge2 f := ce.symm (N.nerve.faceEdge2 (cf f))
  edgeOverlapComponent e := N.nerve.edgeOverlapComponent (ce e)
  faceTripleOverlapComponent f := N.nerve.faceTripleOverlapComponent (cf f)
  edgeOverlapComponent_holds e := N.nerve.edgeOverlapComponent_holds (ce e)
  faceTripleOverlapComponent_holds f := N.nerve.faceTripleOverlapComponent_holds (cf f)

/-- 名前の取り直しで台を保持するsupported nerveを生成する。 -/
def supported : TargetSupportedNerve q where
  nerve := nerve N cv ce cf
  chartFintype := Fintype.ofEquiv _ cv.symm
  edgeFintype := Fintype.ofEquiv _ ce.symm
  faceFintype := Fintype.ofEquiv _ cf.symm
  chartSupport v := N.chartSupport (cv v)
  chartSupport_nonempty v := N.chartSupport_nonempty (cv v)
  faceEdge0_left f := by
    change cv.symm (N.nerve.edgeLeft (ce (ce.symm (N.nerve.faceEdge0 (cf f))))) =
      cv.symm (N.nerve.edgeLeft (ce (ce.symm (N.nerve.faceEdge1 (cf f)))))
    simp only [Equiv.apply_symm_apply, N.faceEdge0_left]
  faceEdge0_right f := by
    change cv.symm (N.nerve.edgeRight (ce (ce.symm (N.nerve.faceEdge0 (cf f))))) =
      cv.symm (N.nerve.edgeLeft (ce (ce.symm (N.nerve.faceEdge2 (cf f)))))
    simp only [Equiv.apply_symm_apply, N.faceEdge0_right]
  faceEdge1_right f := by
    change cv.symm (N.nerve.edgeRight (ce (ce.symm (N.nerve.faceEdge1 (cf f))))) =
      cv.symm (N.nerve.edgeRight (ce (ce.symm (N.nerve.faceEdge2 (cf f)))))
    simp only [Equiv.apply_symm_apply, N.faceEdge1_right]

/-- 名前の取り直しのchart台。 -/
@[simp] theorem chartSupport (v : V) : (supported N cv ce cf).chartSupport v = N.chartSupport (cv v) := rfl
/-- 名前の取り直しの左端点。 -/
@[simp] theorem edgeLeft (e : E) : (supported N cv ce cf).nerve.edgeLeft e = cv.symm (N.nerve.edgeLeft (ce e)) := rfl
/-- 名前の取り直しの右端点。 -/
@[simp] theorem edgeRight (e : E) : (supported N cv ce cf).nerve.edgeRight e = cv.symm (N.nerve.edgeRight (ce e)) := rfl
/-- 名前の取り直しの第0辺。 -/
@[simp] theorem faceEdge0 (f : F) : (supported N cv ce cf).nerve.faceEdge0 f = ce.symm (N.nerve.faceEdge0 (cf f)) := rfl
/-- 名前の取り直しの第1辺。 -/
@[simp] theorem faceEdge1 (f : F) : (supported N cv ce cf).nerve.faceEdge1 f = ce.symm (N.nerve.faceEdge1 (cf f)) := rfl
/-- 名前の取り直しの第2辺。 -/
@[simp] theorem faceEdge2 (f : F) : (supported N cv ce cf).nerve.faceEdge2 f = ce.symm (N.nerve.faceEdge2 (cf f)) := rfl

/-- 原始名前から生成した表示同型、全incidence条件を放電する。 -/
def presentation : CellPresentationEquiv q q (Reading.coarserThan_refl q) N (supported N cv ce cf) where
  chartEquiv := cv
  edgeEquiv := ce
  faceEquiv := cf
  edge_left e := by rw [edgeLeft]; exact cv.apply_symm_apply _
  edge_right e := by rw [edgeRight]; exact cv.apply_symm_apply _
  face_edge0 f := by rw [faceEdge0]; exact ce.apply_symm_apply _
  face_edge1 f := by rw [faceEdge1]; exact ce.apply_symm_apply _
  face_edge2 f := by rw [faceEdge2]; exact ce.apply_symm_apply _
  chartSupport_eq v := by rw [chartSupport, comparisonFactor_self]; rfl

end CellRename
namespace CellPresentationEquiv
variable {Source : Type u} {qc qf : Reading Source} {h : qc.CoarserThan qf}
variable {Nc : TargetSupportedNerve qc} {Nf : TargetSupportedNerve qf}
/-- 指定したchart像が台逆像と矛盾する場合、そのdataに表示同型は存在しない。 -/
theorem no_presentation_with_incompatible_chart (v : Nf.nerve.Chart) (w : Nc.nerve.Chart)
    (t : qf.Target) (ht : t ∈ Nf.chartSupport v)
    (hw : comparisonFactor qc qf h t ∉ Nc.chartSupport w) :
    ¬ ∃ E : CellPresentationEquiv qc qf h Nc Nf, E.chartEquiv v = w := by
  rintro ⟨E, he⟩
  rw [E.chartSupport_eq v, Set.mem_preimage, he] at ht
  exact hw ht
end CellPresentationEquiv
end AAT.AG.FaceRelationSubdivision
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision
