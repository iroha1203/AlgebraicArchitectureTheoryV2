import ResearchLean.AG.FaceRelationSubdivision.WitnessTwoAInput
import ResearchLean.AG.FaceRelationSubdivision.WitnessThreePeriods
import Mathlib.LinearAlgebra.Isomorphisms
import Formal.Util.AssertStandardAxioms

/-!
# W2a の異なる二支持から得る同じ loop period

## Implementation notes

alpha は共通支持点による全三成分同定を使い、beta は実際に選ばれた a,k 上で商を計算する。
二支持を全台へ変更する方式や、次元から同じ比較を推定する方式は採らない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision.WitnessTwoA
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
open ConnectedFaceWitness (q laws adequate label)
/-- chart 台が違っても同じ原始 incidence の名付き三項表である。 -/
def incidenceEquiv : ThreeCochainComplex.CochainEquiv (namedComplex N) (namedComplex WitnessThree.N) where
  e0 := LinearEquiv.refl ℚ _
  e1 := LinearEquiv.refl ℚ _
  e2 := LinearEquiv.refl ℚ _
  comm0 _ := rfl
  comm1 _ := rfl
/-- alpha の同じ実 singleton 複体と原始名付き表の全三成分同定。 -/
def alphaEquiv := pointSubsetNamedEquiv N false alpha_common
/-- alpha の実 H¹ 商における k period。 -/
def alphaPeriod := alphaEquiv.h1Equiv.trans (incidenceEquiv.h1Equiv.trans WitnessThree.namedH1Equiv)
/-- alpha の同じ period を全三成分同定の生成 H¹ 写像で読む。 -/
@[simp] theorem alphaPeriod_apply (x : (N.targetSubsetComplex {false}).H1) :
    alphaPeriod x=WitnessThree.namedH1Equiv
      (incidenceEquiv.toHom.h1Map (alphaEquiv.toHom.h1Map x)) := by
  simp only [alphaPeriod,LinearEquiv.trans_apply,ThreeCochainComplex.CochainEquiv.h1Equiv_apply]
/-- alpha の実選択 k 辺。 -/
def alphaK := pointSelected N.edgeSupport false (commonPoint_edge N false alpha_common) (3 : Fin 4)
/-- alpha period は同じ実代表の k 値を読む。 -/
@[simp] theorem alphaPeriod_mk (z : LinearMap.ker (N.targetSubsetComplex {false}).d1) :
    alphaPeriod ((LinearMap.range (N.targetSubsetComplex {false}).boundaryToCycles).mkQ z)=z.val alphaK := by
  rw [alphaPeriod_apply,ThreeCochainComplex.Hom.h1Map_mk,ThreeCochainComplex.Hom.h1Map_mk,
    WitnessThree.namedH1Equiv_mk,ThreeCochainComplex.Hom.cyclesMap_apply,
    ThreeCochainComplex.Hom.cyclesMap_apply]
  exact pointSubsetNamedEquiv_e1 N false alpha_common z.val (3 : Fin 4)
/-- beta の実選択辺 a。 -/
def betaA : N.EdgeInTargetSubset {true} := ⟨1,⟨true,by rw [edge_support]; trivial,rfl⟩⟩
/-- beta の実選択辺 k。 -/
def betaK : N.EdgeInTargetSubset {true} := ⟨3,⟨true,by rw [edge_support]; trivial,rfl⟩⟩
/-- beta の選択辺は a,k だけである。 -/
theorem beta_edge_cases (e : N.EdgeInTargetSubset {true}) : e=betaA ∨ e=betaK := by
  have h := (singleton_selected_iff _ true).mp e.property
  rw [edge_support] at h
  rcases e with ⟨e,he⟩
  fin_cases e
  · exact False.elim (Bool.false_ne_true h.symm)
  · exact Or.inl (Subtype.ext rfl)
  · exact False.elim (Bool.false_ne_true h.symm)
  · exact Or.inr (Subtype.ext rfl)
/-- beta は元の面 F を選ばない。 -/
theorem beta_face_empty (f : N.FaceInTargetSubset {true}) : False := by
  have h := (singleton_selected_iff _ true).mp f.property
  rw [face_support] at h
  exact Bool.false_ne_true h.symm
/-- beta の実 cocycle 商の同じ k 値。 -/
def betaLoopPeriod : LinearMap.ker (N.targetSubsetComplex {true}).d1 →ₗ[ℚ] ℚ where
  toFun z := z.val betaK
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- beta period の実代表評価。 -/
@[simp] theorem betaLoopPeriod_apply (z : LinearMap.ker (N.targetSubsetComplex {true}).d1) :
    betaLoopPeriod z=z.val betaK := rfl
/-- beta period が零なら実頂点 potential に戻せる。 -/
theorem betaLoopPeriod_kernel : LinearMap.ker betaLoopPeriod=
    LinearMap.range (N.targetSubsetComplex {true}).boundaryToCycles := by
  ext z
  constructor
  · intro hz
    have hk : z.val betaK=0 := hz
    refine ⟨fun v => if v.val=(2 : Fin 3) then z.val betaA else 0,?_⟩
    apply Subtype.ext
    funext e
    rw [ThreeCochainComplex.boundaryToCycles_apply,N.targetSubsetComplex_d0_apply]
    rcases beta_edge_cases e with rfl | rfl
    · simp only [N.targetSubsetEdgeRight_val,N.targetSubsetEdgeLeft_val,
        ConnectedFaceWitness.edgeRight,ConnectedFaceWitness.edgeLeft]
      simp [betaA]
    · simp only [N.targetSubsetEdgeRight_val,N.targetSubsetEdgeLeft_val,
        ConnectedFaceWitness.edgeRight,ConnectedFaceWitness.edgeLeft]
      simp only [betaK,Matrix.cons_val_one,Matrix.cons_val_zero,Matrix.head_cons]
      simp
      exact hk.symm
  · rintro ⟨c,rfl⟩
    rw [LinearMap.mem_ker,betaLoopPeriod_apply,ThreeCochainComplex.boundaryToCycles_apply,
      N.targetSubsetComplex_d0_apply]
    exact sub_self _
/-- beta の k 単独 cochain を原始選択セルで作る。 -/
def betaLoopOnly (a : ℚ) : LinearMap.ker (N.targetSubsetComplex {true}).d1 :=
  ⟨fun e => if e.val=(3 : Fin 4) then a else 0,by funext f; exact False.elim (beta_face_empty f)⟩
/-- beta の単独 cochain は同じ k 値を持つ。 -/
@[simp] theorem betaLoopPeriod_loopOnly (a : ℚ) : betaLoopPeriod (betaLoopOnly a)=a := by
  change (if (3 : Fin 4)=3 then a else 0)=a
  exact if_pos rfl
/-- 同じ k 単独 cochain による全射。 -/
theorem betaLoopPeriod_surjective : Function.Surjective betaLoopPeriod := fun a => ⟨betaLoopOnly a,betaLoopPeriod_loopOnly a⟩
/-- beta の実 H¹ 商の k period 同定。 -/
def betaPeriod : (N.targetSubsetComplex {true}).H1 ≃ₗ[ℚ] ℚ :=
  (Submodule.quotEquivOfEq _ _ betaLoopPeriod_kernel.symm).trans
    (betaLoopPeriod.quotKerEquivOfSurjective betaLoopPeriod_surjective)
/-- beta の商同定は同じ実代表の k 値を読む。 -/
@[simp] theorem betaPeriod_mk (z : LinearMap.ker (N.targetSubsetComplex {true}).d1) :
    betaPeriod ((LinearMap.range (N.targetSubsetComplex {true}).boundaryToCycles).mkQ z)=z.val betaK := rfl
/-- beta の k 単独1の実類は非零。 -/
theorem beta_loop_nonzero :
    (LinearMap.range (N.targetSubsetComplex {true}).boundaryToCycles).mkQ (betaLoopOnly 1)≠0 := by
  intro h
  have he := congrArg betaPeriod h
  rw [betaPeriod_mk,map_zero] at he
  have hp := betaLoopPeriod_loopOnly (1 : ℚ)
  exact one_ne_zero (hp.symm.trans he)
end AAT.AG.FaceRelationSubdivision.WitnessTwoA
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision.WitnessTwoA
