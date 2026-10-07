import ResearchLean.AG.FaceRelationSubdivision.WitnessOneComparison
import Mathlib.LinearAlgebra.Isomorphisms
import Formal.Util.AssertStandardAxioms
/-!
# W1 の原始 period と実 cocycle 商

## Implementation notes

period 零の cocycle は v=0,w=z(e1),v'=z(c) の具体 potential で回復する。
商の同定はこの核と原始単独 cochain の全射性から構成し、rank を使わない。
-/
noncomputable section
namespace AAT.AG.FaceRelationSubdivision.WitnessOne
open CanonicalResolution ResolutionInvariance TwoPhase AtlasDefectComposition
/-- 粗実 cocycle の k period。 -/
def oldPeriod : LinearMap.ker (namedComplex N).d1 →ₗ[ℚ] ℚ where
  toFun z := z.val (1 : Fin 2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- plus 実 cocycle の同じ k period。 -/
def plusPeriod : LinearMap.ker (namedComplex plus).d1 →ₗ[ℚ] ℚ where
  toFun z := z.val (.inl (1 : Fin 2))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
/-- 面だけなしの実 cocycle は k と三辺の二 period を持つ。 -/
def minusPeriod : LinearMap.ker (namedComplex minus).d1 →ₗ[ℚ] (ℚ × ℚ) where
  toFun z := (z.val (.inl (1 : Fin 2)), z.val (.inr false) - z.val (.inl (0 : Fin 2)) + z.val (.inr true))
  map_add' z w := by
    apply Prod.ext
    · rfl
    · change (z.val (.inr false)+w.val (.inr false))-(z.val (.inl (0 : Fin 2))+w.val (.inl (0 : Fin 2)))+
        (z.val (.inr true)+w.val (.inr true)) =
        (z.val (.inr false)-z.val (.inl (0 : Fin 2))+z.val (.inr true))+
        (w.val (.inr false)-w.val (.inl (0 : Fin 2))+w.val (.inr true))
      ring
  map_smul' a z := by
    apply Prod.ext
    · rfl
    · change (a*z.val (.inr false))-(a*z.val (.inl (0 : Fin 2)))+(a*z.val (.inr true)) =
        a*(z.val (.inr false)-z.val (.inl (0 : Fin 2))+z.val (.inr true))
      ring
/-- 粗 period の公開式。 -/
@[simp] theorem oldPeriod_apply (z) : oldPeriod z = z.val (1 : Fin 2) := rfl
/-- plus period の公開式。 -/
@[simp] theorem plusPeriod_apply (z) : plusPeriod z = z.val (.inl (1 : Fin 2)) := rfl
/-- minus 二 period の公開式。 -/
@[simp] theorem minusPeriod_apply (z) : minusPeriod z =
    (z.val (.inl (1 : Fin 2)),z.val (.inr false)-z.val (.inl (0 : Fin 2))+z.val (.inr true)) := rfl
/-- plus の cocycle 条件は三辺 period の零性。 -/
theorem plus_cycle_iff (z : plus.nerve.EdgeComponent → ℚ) :
    z ∈ LinearMap.ker (namedComplex plus).d1 ↔ z (.inr false)-z (.inl (0 : Fin 2))+z (.inr true)=0 := by
  constructor
  · intro hz
    exact (plus_d1_apply z (.inr PUnit.unit)).symm.trans (congrFun hz (.inr PUnit.unit))
  · intro hz
    funext f
    rw [plus_d1_apply,hz]
    rfl
/-- plus cocycle の原始三辺関係。 -/
theorem plus_cycle_relation (z : LinearMap.ker (namedComplex plus).d1) :
    z.val (.inr false)-z.val (.inl (0 : Fin 2))+z.val (.inr true)=0 := (plus_cycle_iff z.val).mp z.property
/-- 粗 period 零の cocycle は原始 potential から生成する。 -/
theorem oldPeriod_kernel : LinearMap.ker oldPeriod = LinearMap.range (namedComplex N).boundaryToCycles := by
  ext z
  constructor
  · intro hz
    have hk : z.val (1 : Fin 2)=0 := hz
    refine ⟨![0,z.val (0 : Fin 2)],?_⟩
    apply Subtype.ext
    funext e
    rw [ThreeCochainComplex.boundaryToCycles_apply,d0_apply]
    fin_cases e <;> simp
    all_goals linarith
  · rintro ⟨c,rfl⟩
    rw [LinearMap.mem_ker,oldPeriod_apply,ThreeCochainComplex.boundaryToCycles_apply,d0_apply]
    simp
/-- plus period 零の cocycle は同じ具体頂点 potential から生成する。 -/
theorem plusPeriod_kernel : LinearMap.ker plusPeriod = LinearMap.range (namedComplex plus).boundaryToCycles := by
  ext z
  constructor
  · intro hz
    have hk : z.val (.inl (1 : Fin 2))=0 := hz
    have hf := plus_cycle_relation z
    refine ⟨Sum.elim ![0,z.val (.inl (0 : Fin 2))] (fun _ => z.val (.inr false)),?_⟩
    apply Subtype.ext
    funext e
    rw [ThreeCochainComplex.boundaryToCycles_apply]
    cases e with
    | inl e =>
        rw [plus_d0_old]
        fin_cases e <;> simp
        all_goals linarith
    | inr e =>
        cases e <;> simp only [plus_d0_c,plus_d0_e2,Sum.elim_inl,Sum.elim_inr] <;> simp
        all_goals linarith
  · rintro ⟨c,rfl⟩
    rw [LinearMap.mem_ker,plusPeriod_apply,ThreeCochainComplex.boundaryToCycles_apply,plus_d0_old]
    simp
/-- minus の二 period 零は同じ端点 potential の像と一致する。 -/
theorem minusPeriod_kernel : LinearMap.ker minusPeriod = LinearMap.range (namedComplex minus).boundaryToCycles := by
  ext z
  constructor
  · intro hz
    have hp : minusPeriod z=0 := hz
    have hk : z.val (.inl (1 : Fin 2))=0 := congrArg Prod.fst hp
    have hf : z.val (.inr false)-z.val (.inl (0 : Fin 2))+z.val (.inr true)=0 := congrArg Prod.snd hp
    refine ⟨Sum.elim ![0,z.val (.inl (0 : Fin 2))] (fun _ => z.val (.inr false)),?_⟩
    apply Subtype.ext
    funext e
    rw [ThreeCochainComplex.boundaryToCycles_apply]
    cases e with
    | inl e =>
        rw [minus_d0_old]
        fin_cases e <;> simp
        all_goals linarith
    | inr e =>
        cases e <;> simp only [minus_d0_c,minus_d0_e2,Sum.elim_inl,Sum.elim_inr] <;> simp
        all_goals linarith
  · rintro ⟨c,rfl⟩
    rw [LinearMap.mem_ker,minusPeriod_apply]
    apply Prod.ext
    · simp only [Prod.fst_zero]
      rw [ThreeCochainComplex.boundaryToCycles_apply,minus_d0_old]; simp
    · simp only [Prod.snd_zero]
      simp only [ThreeCochainComplex.boundaryToCycles_apply,minus_d0_c,minus_d0_old,minus_d0_e2]
      simp
/-- k 上だけ a の粗 cocycle。 -/
def oldLoopOnly (a : ℚ) : LinearMap.ker (namedComplex N).d1 :=
  ⟨![0,a],by funext f; exact Empty.elim f⟩
/-- k 上だけ a の plus cocycle。 -/
def plusLoopOnly (a : ℚ) : LinearMap.ker (namedComplex plus).d1 :=
  ⟨Sum.elim ![0,a] (fun _ => 0),by rw [plus_cycle_iff]; simp⟩
/-- minus では k=x と e2=y の単独 cochain が独立二 period を与える。 -/
def minusSection (a : ℚ × ℚ) : LinearMap.ker (namedComplex minus).d1 :=
  ⟨Sum.elim ![0,a.1] (fun b => if b then a.2 else 0),by funext f; exact Empty.elim f⟩
/-- 粗単独 loop の period。 -/
@[simp] theorem oldPeriod_loop (a : ℚ) : oldPeriod (oldLoopOnly a)=a := rfl
/-- plus 単独 loop の period。 -/
@[simp] theorem plusPeriod_loop (a : ℚ) : plusPeriod (plusLoopOnly a)=a := rfl
/-- minus 単独二 cochain の period は指定対そのもの。 -/
@[simp] theorem minusPeriod_section (a : ℚ × ℚ) : minusPeriod (minusSection a)=a := by
  apply Prod.ext <;> simp [minusPeriod_apply,minusSection]
/-- 粗 period 全射を原始 loop から得る。 -/
theorem oldPeriod_surjective : Function.Surjective oldPeriod := fun a => ⟨oldLoopOnly a,rfl⟩
/-- plus period 全射を同じ原始 loop から得る。 -/
theorem plusPeriod_surjective : Function.Surjective plusPeriod := fun a => ⟨plusLoopOnly a,rfl⟩
/-- minus 二 period 全射を具体単独 cochain から得る。 -/
theorem minusPeriod_surjective : Function.Surjective minusPeriod := fun a => ⟨minusSection a,minusPeriod_section a⟩
/-- 同じ粗 H¹ 商の k period 同定。 -/
def oldH1Period : (namedComplex N).H1 ≃ₗ[ℚ] ℚ :=
  (Submodule.quotEquivOfEq _ _ oldPeriod_kernel.symm).trans (oldPeriod.quotKerEquivOfSurjective oldPeriod_surjective)
/-- 同じ plus H¹ 商の k period 同定。 -/
def plusH1Period : (namedComplex plus).H1 ≃ₗ[ℚ] ℚ :=
  (Submodule.quotEquivOfEq _ _ plusPeriod_kernel.symm).trans (plusPeriod.quotKerEquivOfSurjective plusPeriod_surjective)
/-- 同じ minus H¹ 商の二 period 同定。 -/
def minusH1Period : (namedComplex minus).H1 ≃ₗ[ℚ] (ℚ × ℚ) :=
  (Submodule.quotEquivOfEq _ _ minusPeriod_kernel.symm).trans (minusPeriod.quotKerEquivOfSurjective minusPeriod_surjective)
/-- 粗商同定の代表式。 -/
@[simp] theorem oldH1Period_mk (z) : oldH1Period ((LinearMap.range (namedComplex N).boundaryToCycles).mkQ z)=oldPeriod z := rfl
/-- plus 商同定の代表式。 -/
@[simp] theorem plusH1Period_mk (z) : plusH1Period ((LinearMap.range (namedComplex plus).boundaryToCycles).mkQ z)=plusPeriod z := rfl
/-- minus 商同定の代表式。 -/
@[simp] theorem minusH1Period_mk (z) : minusH1Period ((LinearMap.range (namedComplex minus).boundaryToCycles).mkQ z)=minusPeriod z := rfl
/-- e2 上だけ1の同じ cochain の plus 面微分は1である。 -/
theorem e2_plus_d1_one : (namedComplex plus).d1 (minusSection (0,1)).val (.inr PUnit.unit)=1 := by
  rw [plus_d1_apply]
  simp [minusSection]
/-- e2 上だけ1の同じ cochain は plus では cocycle ではない。 -/
theorem e2_not_plus_cycle : (minusSection (0,1)).val ∉ LinearMap.ker (namedComplex plus).d1 := by
  rw [plus_cycle_iff]
  simp [minusSection]
end AAT.AG.FaceRelationSubdivision.WitnessOne
#assert_standard_axioms_only AAT.AG.FaceRelationSubdivision.WitnessOne
