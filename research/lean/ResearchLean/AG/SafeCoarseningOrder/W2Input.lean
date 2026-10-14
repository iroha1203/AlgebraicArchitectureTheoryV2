import ResearchLean.AG.SafeCoarseningOrder.W1FiniteEvaluation

/-! # W2 原始六角形と真のjoin

## Implementation notes

六点をa=0からf=5へ符号化し、元六有向辺と指定二点合併を保持する。関係包含から真のjoinを証明する。期待rankを合併表へ埋める代替は候補を仮定するため採用しない。
-/
noncomputable section
namespace AAT.AG.SafeCoarseningOrder.W2
open CanonicalResolution ResolutionInvariance TwoPhase
/-- 指定六点の閉じた関係検査に使うmathlibの計算可能な等号。 -/
local instance zmodSixDecEq : DecidableEq (ZMod 6) := ZMod.decidableEq 6
/-- 指定Bool/id・a=0,b=1,c=2,d=3,e=4,f=5の六有向辺・全台の同じT0入力。 -/
abbrev input : PrimitiveInput Bool Bool (ZMod 6) := Cycle.input 6 (by decide)
/-- aとcだけを同色にする元六点の五色表。 -/
def acMap (v : ZMod 6) : Fin 5 := ![0,1,0,2,3,4] v
/-- dとfだけを同色にする元六点の五色表。 -/
def dfMap (v : ZMod 6) : Fin 5 := ![0,1,2,3,4,3] v
/-- a/c、d/fを併合しb/eを保持する元四色表。 -/
def joinMap (v : ZMod 6) : ZMod 4 := ![0,1,0,2,3,2] v
/-- target等号・a/cだけchart合併の指定粗化。 -/
def ac : Coarsening Bool (ZMod 6) := (⊥,Setoid.ker acMap)
/-- target等号・d/fだけchart合併の指定粗化。 -/
def df : Coarsening Bool (ZMod 6) := (⊥,Setoid.ker dfMap)
/-- 元二対合併色表から作る候補join。真のjoinとの等号は別に証明する。 -/
def joined : Coarsening Bool (ZMod 6) := (⊥,Setoid.ker joinMap)
/-- 指定a/c商関係の元色等号を公開する。 -/
theorem ac_relation (v w : ZMod 6) : ac.2.r v w ↔ acMap v=acMap w := Iff.rfl
/-- 指定d/f商関係の元色等号を公開する。 -/
theorem df_relation (v w : ZMod 6) : df.2.r v w ↔ dfMap v=dfMap w := Iff.rfl
/-- 二対合併候補の元色等号を公開する。 -/
theorem joined_relation (v w : ZMod 6) : joined.2.r v w ↔ joinMap v=joinMap w := Iff.rfl
/-- a/c指定関係は二対合併関係へ包含される。 -/
theorem ac_le_joined : ac ≤ joined := by
  constructor
  · exact le_refl _
  · intro v w h
    rw [ac_relation] at h
    rw [joined_relation]
    fin_cases v <;> fin_cases w <;> first | assumption | contradiction | decide +kernel
/-- d/f指定関係は二対合併関係へ包含される。 -/
theorem df_le_joined : df ≤ joined := by
  constructor
  · exact le_refl _
  · intro v w h
    rw [df_relation] at h
    rw [joined_relation]
    fin_cases v <;> fin_cases w <;> first | assumption | contradiction | decide +kernel
/-- 原始関係包含と反射性からT0のjoinを二対合併表へ同定する。 -/
theorem specified_join : ac ⊔ df=joined := by
  apply le_antisymm (sup_le ac_le_joined df_le_joined)
  constructor
  · exact le_sup_left
  · intro v w h
    rw [joined_relation] at h
    fin_cases v <;> fin_cases w <;>
      first | exact (ac ⊔ df).2.refl _ |
        exact (show ac.2≤(ac ⊔ df).2 from le_sup_left) (by rw [ac_relation]; decide +kernel) |
        exact (show df.2≤(ac ⊔ df).2 from le_sup_right) (by rw [df_relation]; decide +kernel) |
        exact ((by decide +kernel : ¬ joinMap _=joinMap _) h).elim

/-- 二対合併表の全四色は元六点から発生する。 -/
theorem joinMap_surjective : Function.Surjective joinMap := by
  intro c
  fin_cases c
  · exact ⟨0,by decide +kernel⟩
  · exact ⟨1,by decide +kernel⟩
  · exact ⟨3,by decide +kernel⟩
  · exact ⟨4,by decide +kernel⟩
/-- 元六有向辺のsuccessor評価を公開する。 -/
theorem input_edge_iff (v w : ZMod 6) : input.edge v w ↔ w=v+1 := Cycle.input_edge_iff 6 (by decide) v w
/-- 元readingは指定Bool恒等写像である。 -/
theorem input_read (s : Bool) : input.read s=s := Cycle.input_read 6 (by decide) s
/-- 元六chartは指定全target台を持つ。 -/
theorem input_support (v : ZMod 6) : input.support v=Set.univ := Cycle.input_support 6 (by decide) v
/-- a/c合併は指定二点だけで、他の六点を余計に同一視しない。 -/
theorem ac_specified_relation (v w : ZMod 6) :
    ac.2.r v w ↔ v=w ∨ (v=0 ∧ w=2) ∨ (v=2 ∧ w=0) := by
  rw [ac_relation]
  fin_cases v <;> fin_cases w <;> decide +kernel
/-- d/f合併は指定二点だけで、他の六点を余計に同一視しない。 -/
theorem df_specified_relation (v w : ZMod 6) :
    df.2.r v w ↔ v=w ∨ (v=3 ∧ w=5) ∨ (v=5 ∧ w=3) := by
  rw [df_relation]
  fin_cases v <;> fin_cases w <;> decide +kernel
/-- 元a→bだけ1、他の五辺は0の指定cochain。 -/
def specifiedSpike : (Cycle.fullComplex 6 (by decide)).C1 := Cycle.spike 6 (by decide)
/-- 指定cochainの元六辺periodは1である。 -/
theorem specifiedSpike_period : Cycle.period 6 (by decide) specifiedSpike=1 :=
  Cycle.period_spike 6 (by decide)
/-- 指定cochainは元既存H1商で非零。 -/
theorem specifiedSpike_nonzero : Cycle.classOf 6 (by decide) specifiedSpike≠0 :=
  Cycle.spike_nonzero 6 (by decide)
end AAT.AG.SafeCoarseningOrder.W2

#assert_standard_axioms_only AAT.AG.SafeCoarseningOrder
