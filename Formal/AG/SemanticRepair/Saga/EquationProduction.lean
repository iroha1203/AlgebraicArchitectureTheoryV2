import Formal.AG.SemanticRepair.Saga.EquationRealization

/-!
# Issue #3734: equation-system production route for the SAGA equation inputs

* `SupportAtomEquationSelection`: X.命題6.1A の selected 対応 `λ ↦ (i_λ, A_λ)`
  を、support Atom を通じて factor する特殊形に**制限して**受ける selected
  datum(X.定義5.1 / III.定義11.3 の displayed Atom/equation coordinate 語彙。
  本文の定義形そのものではない — structure docstring の限定を見よ)。field は
  選択 data のみで、certificate・結論相当の field を持たない。
* `SupportAtomEquationSelection.realization`: `EquationSemanticRealization` の
  production constructor。命題6.1A の唯一の条件「restriction と可換する」を
  supplied field ではなく証明で放電する: support Atom を通じた factoring は
  `projection_natural` + `occRestrict_atom`(occurrence の台 Atom 保存)により
  restriction 可換性の十分条件である。命題6.1A の一般面は従来どおり
  `EquationSemanticRealization` が担い、本 constructor はそれを置き換えない
  (すべての realization がこの形で得られるとは主張しない)。
* `SupportAtomEquationSelection.displayedSource`: produced realization が読む
  displayed Atom/equation coordinate 族を**含む、より広い chart 族**を
  III.定義11.3 の Lean 実体の instance として束ねた生成物。defect は field
  ではなく生成される(#3733)。
* `realization_chiE_eq_interpret` と派生 vanishing 補題: produced `χ^E` の値は
  III.定理11.4 の generated interpretation(X.定義5.1 の `int_E`)と定義的に
  一致する。したがって #3732/#3733 の生成 chain(`witnessIdeal` →
  `obstructionIdeal` → quotient zero、fulfillment 経路)がそのまま適用され、
  再証明しない。
* `displayedSource_defect_restrict` / `realization_chiE_restrict_eq_defect_class`:
  restriction 面の #3732/#3733 接続。face に沿った defect の restriction は
  #3733 の `restrict_defect`、`χ^E` の restriction は #3732 の
  `obstructionQuotientRestrict_mk` で宣言名追跡できる。
* `LiftFiberData.equationLiftSystem`: X.定義5.3 の幾何側入力規律
  「equation system は coefficient `Q_E` を生成し、base reading と local lifts
  は解こうとする局所 equation-lift problem を選ぶ」のうち、本文が「典型例」と
  呼ぶ short exact sequence 経路の named surface。実体は C2 `liftSystem` の
  alias であり新規の型・証明を作らない(`equationLiftSystem_eq_liftSystem` が
  `rfl`)。lift-fiber datum(short exact sequence と base reading)は X.§1
  入力6(R0 §4.6)のとおり selected のまま。定義5.3 の一般面(任意の
  `Q_E`-affine local-state system)は従来どおり
  `AffineCoefficientLiftSystem` が担う。
* `equationSelfLiftFiber` / `equationSelfLiftAtlas`: X.定義5.3 典型例の
  **退化** instance(`B_E = 0`)。equation system の生成物 `Q_E` だけから
  構成でき、`equationLiftSystem` と C2 residual engine を型どおり発火させる
  (`equationSelfLiftAtlas_residual`、residual は零 atlas の帰結として恒等的
  に零)。lift problem の非自明な内容(非零 base reading)は発火しない —
  Implementation notes に申告。
* `SagaEquationPacket.ofProduction`: 定理1.1 入力束を production route から
  組み立てる束ね constructor。旧 `Law.holds`、manual equation core、
  membership certificate、結論相当 field は入力に取らない。

Claim boundary: `P_E` 本体と local lift atlas、semantic 側入力(`P_sem` /
repair atlas)、state correspondence `β` は X.§1 の
selected/generated/proved 三分類のとおり selected のまま受け取る。
empty-overlap normalization(入力8)は X.§7 のとおり comparison core の
仮定に含まれないため packet に束ねない。
`equationSelfLiftFiber` は「P_E が生成できる」ことを主張しない: 生成できるのは
この特定の self-lift instance だけであり、どの lift problem を解くかの選択は
本文どおり selected のままである。
凍結 G-06 route(`LawEquationGeneratedPair` / `SagaComparison`)には依存しない。

Implementation notes(`lean_quality_standard.md` §2.5 申告):

`displayedSource` の定義形(`Chart := IntersectionIndex 𝒰 × U.Atom`、
`chart q := q.1.ctx`、`LocalInput := PUnit`)は、`realization_chiE_eq_interpret`
が `rfl` で成立するように選んである(interpret の値式と `chiE` の値式が字面
一致する chart 添字)。III.定義11.3 本文との差は4点あり、いずれも申告する:
(i) 本文は添字集合を有限に取るが、Lean 側 `DisplayedEquationSource`(#3733)は
有限性 field を持たず(既存設計)、本構成の `Chart` は一般に無限。
(ii) 本文の cover-indexed 形は `D := I`(cover chart 添字)を指定し「別の
skeleton を置かない」とするが、本構成は intersection × Atom の直積添字の
別 skeleton である(equation choice は `sel` 一つから導出され、「二つ目の
chart-indexed equation choice」は置いていない)。
(iii) 本文の cover-indexed 形は local context を cover chart に取るが、
本構成は intersection context を取る。
(iv) 本文は base context `W_base` と各 local context の構造射
`W_q → W_base` を固定するが、Lean 側 `DisplayedEquationSource`(#3733、
既存設計)は共通 base も構造射も field に持たず、本構成もそれを継承する。
再利用する III.定理11.4 の結論(generated interpretation、membership 同値、
fulfillment 零化、residual restriction)はすべて chart 単位の主張で有限性も
cover-indexing も使わないため、これらの差は再利用結果を弱めない。また
`LocalInput := PUnit` は local-input presentation 層を退化させた instance で
あり、`Chart` は produced realization が実際に読む coordinate 族
(occurrence projection の像)より広い。
退けた代替案: `Chart := 𝒰.Index`(本文の cover-indexed 形)は per-chart の
display Atom 選択を追加で要求し χ^E との per-atom 一致が壊れるため、
`Chart := (σ : IntersectionIndex 𝒰) × SupportedAtom σ.ctx`(読む族と同一)は
`SupportedAtom : Type v` が `Chart : Type u` の universe 制約と衝突するため、
それぞれ退けた。

`zeroSitePresheaf` / `equationSelfLiftFiber` の設計選択: `B := PUnit`(零
presheaf)、`incl := id`、`base := 0` の self-lift fiber は X.定義5.3 典型例
`0 → Q_E → L_E → B_E → 0` の `L_E = Q_E`、`B_E = 0` という**最も自明な
member** であり、(a) exactness / injectivity は自明に充足され、(b) 構成は
`S.equationSystem` の内容を係数スロット以外で使わず(任意の
`SitePresheafData` でも同型に成立する)、(c) 零 atlas の生成 residual は
恒等的に零である。これは「生成 data のみから `equationLiftSystem` を型どおり
発火させられる」ことの witness であって、lift problem の非自明な内容
(非零 base reading、非零 residual)の発火 witness ではない。非自明な lift
problem の選択は本文どおり selected 側にあり、この instance では行われない。
-/

noncomputable section

namespace AAT.AG
namespace SemanticRepair
namespace Saga

universe u v x

variable {U : AtomCarrier.{u}} {A : ArchitectureObject U} {S : Site.AATSite A}
variable {R : AtomOccurrenceReading S}
variable {𝒰 : MonomorphicOrderedCover S}

/-!
## X.命題6.1A: support-Atom factored selected 対応と realization の生成
-/

/--
X.命題6.1A の selected 対応 `λ ↦ (i_λ, A_λ)` を、X.定義5.1 / III.定義11.3 の
displayed Atom/equation coordinate 語彙 `(A, i, a)` を **support Atom を通じて
factor する特殊形に制限して**受ける selected datum。本文の定義形そのもの
ではない: III.定義11.3 / X.定義5.1 の coordinate は chart 添字 `q` ごとに
独立選択され、Atom の関数として factor するという条件は本文にない。この制限は
命題6.1A の restriction 可換性を証明で放電するための Lean 側の十分条件である
(`realization` を見よ)。required 性は `RequiredIndex` subtype で選択と同時に
固定する(#3733 と同じ規約)。
-/
structure SupportAtomEquationSelection (S : Site.AATSite A) : Type (u + 1) where
  /-- 各 Atom に selected required equation index `i_a` を対応させる。 -/
  equationIndex : U.Atom -> S.equationSystem.RequiredIndex
  /-- 各 Atom に selected local architecture reading `A_a` を対応させる。 -/
  archReading : U.Atom -> ArchitectureObject U

namespace SupportAtomEquationSelection

variable (sel : SupportAtomEquationSelection S)
variable {P : SemanticRepairPresentation.{u, v} S R}

/--
X.命題6.1A の production constructor: support Atom を通じて factoring された
selected 対応から `EquationSemanticRealization` を生成する。命題6.1A の条件
「これらが restriction と可換する」は field として供給せず、
`projection_natural`(定義3.1 の occurrence projection の naturality)と
`occRestrict_atom`(restriction が台 Atom を保存すること)から証明する。

support Atom factoring は restriction 可換性の**十分条件**であり、命題6.1A の
一般面(factoring しない restriction-compatible な選択)は従来どおり
`EquationSemanticRealization` を直接構成して受ける。すべての realization が
本 constructor 経由で得られるとは主張しない。
-/
def realization (P : SemanticRepairPresentation.{u, v} S R)
    (𝒰 : MonomorphicOrderedCover S) :
    EquationSemanticRealization P 𝒰 where
  lawIndex σ l :=
    (sel.equationIndex (P.atomData.projection σ.ctx l.1).atom).1
  lawIndex_required σ l :=
    (sel.equationIndex (P.atomData.projection σ.ctx l.1).atom).2
  lawIndex_natural {σ τ} f l := by
    show (sel.equationIndex (P.atomData.projection σ.ctx
        (P.atomData.restrictAtom f.hom l.1)).atom).1 =
      (sel.equationIndex (P.atomData.projection τ.ctx l.1).atom).1
    rw [P.atomData.projection_natural f.hom l.1, R.occRestrict_atom]
  archReading σ l :=
    sel.archReading (P.atomData.projection σ.ctx l.1).atom
  archReading_natural {σ τ} f l := by
    show sel.archReading (P.atomData.projection σ.ctx
        (P.atomData.restrictAtom f.hom l.1)).atom =
      sel.archReading (P.atomData.projection τ.ctx l.1).atom
    rw [P.atomData.projection_natural f.hom l.1, R.occRestrict_atom]

/-- Produced realization の selected equation index は Atom 単位選択の読み出し。
simp normal form: 左辺(生成物の field)を右辺(選択の読み出し)へ展開する。 -/
@[simp] theorem realization_lawIndex (σ : IntersectionIndex 𝒰)
    (l : P.atomData.SupportedAtom σ.ctx) :
    (sel.realization P 𝒰).lawIndex σ l =
      (sel.equationIndex (P.atomData.projection σ.ctx l.1).atom).1 :=
  rfl

/-- Produced realization の architecture reading は Atom 単位選択の読み出し。
simp normal form: 左辺(生成物の field)を右辺(選択の読み出し)へ展開する。 -/
@[simp] theorem realization_archReading (σ : IntersectionIndex 𝒰)
    (l : P.atomData.SupportedAtom σ.ctx) :
    (sel.realization P 𝒰).archReading σ l =
      sel.archReading (P.atomData.projection σ.ctx l.1).atom :=
  rfl

/--
X.命題6.1A: produced `χ^E` の値式
`χ^E_V(λ) = [ε_{V,A_λ,i_λ,π_V(λ)}]`(#3732 の `equationResidual` +
`obstructionIdeal` からの生成、定義的一致)。
-/
theorem realization_chiE_apply (σ : IntersectionIndex 𝒰)
    (l : P.atomData.SupportedAtom σ.ctx) :
    (sel.realization P 𝒰).chiE.chi σ l =
      Ideal.Quotient.mk (S.equationSystem.obstructionIdeal σ.ctx)
        (S.equationSystem.equationResidual σ.ctx
          (sel.archReading (P.atomData.projection σ.ctx l.1).atom)
          (sel.equationIndex (P.atomData.projection σ.ctx l.1).atom).1
          (P.atomData.projection σ.ctx l.1).atom) :=
  rfl

/-!
## III.定義11.3 / X.定義5.1: produced realization が読む displayed source
-/

/--
III.定義11.3 の Lean 実体 `DisplayedEquationSource`(#3733)の instance として、
selected 対応の displayed coordinate 族を束ねた生成物。chart index は
intersection × Atom、defect は #3733 のとおり field ではなく生成される。

module header の Implementation notes を見よ: 定義形は
`realization_chiE_eq_interpret` が `rfl` で成立するよう target-fitting して
あり、`Chart` は一般に無限(本文の有限添字 `D` より広い)、`LocalInput` は
`PUnit` へ退化、`Chart` は produced realization が実際に読む coordinate 族
(occurrence projection の像)より広い。
-/
def displayedSource (sel : SupportAtomEquationSelection S)
    (𝒰 : MonomorphicOrderedCover S) :
    LawAlgebra.DisplayedEquationSource S.equationSystem where
  Chart := IntersectionIndex 𝒰 × U.Atom
  chart q := q.1.ctx
  LocalInput _ := PUnit
  input _ := PUnit.unit
  objectOfLocalInput q _ := sel.archReading q.2
  equationIndex q := sel.equationIndex q.2
  supportAtom q := q.2

/--
X.定義5.1 / III.定理11.4: produced `χ^E` の値は displayed defect の generated
interpretation `int_E` と定義的に一致する。#3732 の interpretation 面が
そのまま新 route の値になる。
-/
theorem realization_chiE_eq_interpret (σ : IntersectionIndex 𝒰)
    (l : P.atomData.SupportedAtom σ.ctx) :
    (sel.realization P 𝒰).chiE.chi σ l =
      LawAlgebra.LawEquationDefectSource.interpret (sel.displayedSource 𝒰)
        (σ, (P.atomData.projection σ.ctx l.1).atom) :=
  rfl

/--
III.定理11.4(#3732 の再利用): produced `χ^E` の値の零化は displayed defect の
generated obstruction ideal 所属と同値。
-/
theorem realization_chiE_eq_zero_iff_defect_mem_obstructionIdeal
    (σ : IntersectionIndex 𝒰) (l : P.atomData.SupportedAtom σ.ctx) :
    (sel.realization P 𝒰).chiE.chi σ l = 0 ↔
      (sel.displayedSource 𝒰).defect
          (σ, (P.atomData.projection σ.ctx l.1).atom) PUnit.unit ∈
        S.equationSystem.obstructionIdeal σ.ctx := by
  rw [sel.realization_chiE_eq_interpret σ l]
  exact LawAlgebra.LawEquationDefectSource.interpret_eq_zero_iff_defect_mem_obstructionIdeal
    (sel.displayedSource 𝒰) (σ, (P.atomData.projection σ.ctx l.1).atom)

/--
III.定義6.1 の帰結(#3732 の `witnessIdeal_le_obstructionIdeal` の再利用):
selected required equation の witness ideal に displayed defect が入れば
produced `χ^E` の値は零(obstruction ideal は required witness ideal の和と
して定義されるため)。
-/
theorem realization_chiE_eq_zero_of_defect_mem_witnessIdeal
    (σ : IntersectionIndex 𝒰) (l : P.atomData.SupportedAtom σ.ctx)
    (hmem :
      (sel.displayedSource 𝒰).defect
          (σ, (P.atomData.projection σ.ctx l.1).atom) PUnit.unit ∈
        S.equationSystem.witnessIdeal σ.ctx
          (sel.equationIndex (P.atomData.projection σ.ctx l.1).atom).1) :
    (sel.realization P 𝒰).chiE.chi σ l = 0 := by
  rw [sel.realization_chiE_eq_zero_iff_defect_mem_obstructionIdeal σ l]
  exact S.equationSystem.witnessIdeal_le_obstructionIdeal σ.ctx
    (sel.equationIndex (P.atomData.projection σ.ctx l.1).atom).2 hmem

/--
III.定理11.4(#3733 の fulfillment 経路の再利用): selected equation の
fulfillment は produced `χ^E` の値を零にする。
-/
theorem realization_chiE_eq_zero_of_equationHolds
    (σ : IntersectionIndex 𝒰) (l : P.atomData.SupportedAtom σ.ctx)
    (hholds : S.equationSystem.EquationHolds
      (sel.equationIndex (P.atomData.projection σ.ctx l.1).atom).1
      (sel.archReading (P.atomData.projection σ.ctx l.1).atom)) :
    (sel.realization P 𝒰).chiE.chi σ l = 0 := by
  rw [sel.realization_chiE_eq_interpret σ l]
  exact LawAlgebra.DisplayedEquationSource.equationHolds_defect_quotient_eq_zero
    (sel.displayedSource 𝒰) (σ, (P.atomData.projection σ.ctx l.1).atom)
    PUnit.unit hholds

/--
III.定理11.4(#3733 の `restrict_defect` の再利用): displayed defect の
restriction 面。face に沿った equation-system restriction は displayed defect
を chart を移した displayed defect へ送る。
-/
theorem displayedSource_defect_restrict
    (σ τ : IntersectionIndex 𝒰) (f : Face 𝒰 σ τ) (a : U.Atom) :
    S.equationSystem.restrict f.hom
        ((sel.displayedSource 𝒰).defect (τ, a) PUnit.unit) =
      (sel.displayedSource 𝒰).defect (σ, a) PUnit.unit :=
  (sel.displayedSource 𝒰).restrict_defect (τ, a) PUnit.unit f.hom

/--
III.定理11.4(#3732 の `obstructionQuotientRestrict_mk` の再利用): produced
`χ^E` の restriction は restrict した displayed defect の class。生成 chain の
restriction 面が #3732/#3733 の宣言(`obstructionQuotientRestrict_mk` /
`restrict_defect`)で宣言名追跡できることを固定する。
-/
theorem realization_chiE_restrict_eq_defect_class
    (σ τ : IntersectionIndex 𝒰) (f : Face 𝒰 σ τ)
    (l : P.atomData.SupportedAtom τ.ctx) :
    (equationCoefficient S 𝒰).restrict f ((sel.realization P 𝒰).chiE.chi τ l) =
      Ideal.Quotient.mk (S.equationSystem.obstructionIdeal σ.ctx)
        (S.equationSystem.restrict f.hom
          ((sel.displayedSource 𝒰).defect
            (τ, (P.atomData.projection τ.ctx l.1).atom) PUnit.unit)) := by
  show S.equationSystem.obstructionQuotientRestrict f.hom
      (Ideal.Quotient.mk (S.equationSystem.obstructionIdeal τ.ctx)
        (S.equationSystem.equationResidual τ.ctx
          (sel.archReading (P.atomData.projection τ.ctx l.1).atom)
          (sel.equationIndex (P.atomData.projection τ.ctx l.1).atom).1
          (P.atomData.projection τ.ctx l.1).atom)) = _
  rw [S.equationSystem.obstructionQuotientRestrict_mk]
  rfl

end SupportAtomEquationSelection

/-!
## X.定義5.3: 生成 `Q_E` 上への幾何側入力規律
-/

namespace LiftFiberData

/--
X.定義5.3: 「equation system は coefficient `Q_E` を生成し、base reading と
local lifts は解こうとする局所 equation-lift problem を選ぶ」のうち、本文の
「典型例」(short exact sequence の lift fiber)経路の named surface。
**実体は C2 `liftSystem` の alias である**: 型は引数 `D` の
`LiftFiberData (equationSitePresheaf S) L B` の時点で既に生成 `Q_E` に固定
されており、本宣言は新しい型も証明も作らない
(`equationLiftSystem_eq_liftSystem` が `rfl`)。lift problem 自体は
X.§1 入力6(R0 §4.6)のとおり selected のまま。定義5.3 の一般面(任意の
`Q_E`-affine local-state system)は `AffineCoefficientLiftSystem` が担う。
生成 data だけから作れる instance は `equationSelfLiftFiber` を見よ
(退化 instance である旨の申告は module header の Implementation notes)。
-/
def equationLiftSystem {L B : SitePresheafData.{u, u} S}
    (D : LiftFiberData (equationSitePresheaf S) L B)
    (𝒰 : MonomorphicOrderedCover S) :
    AffineCoefficientLiftSystem.{u, u, u} (equationCoefficient S 𝒰) :=
  D.liftSystem 𝒰

/-- `equationLiftSystem` は C2 `liftSystem` engine の適用そのもの(再実装しない
ことの証拠)。simp には載せない: production route の normal form は
`equationLiftSystem` 側に保つ。 -/
theorem equationLiftSystem_eq_liftSystem
    {L B : SitePresheafData.{u, u} S}
    (D : LiftFiberData (equationSitePresheaf S) L B)
    (𝒰 : MonomorphicOrderedCover S) :
    D.equationLiftSystem 𝒰 = D.liftSystem 𝒰 :=
  rfl

end LiftFiberData

/-!
## X.定義5.3 典型例の生成 instance: 生成 `Q_E` の self-lift fiber
-/

/-- 恒等的に消える site 全域 presheaf(X.定義5.3 典型例の `B_E = 0` 読み)。 -/
def zeroSitePresheaf (S : Site.AATSite A) : SitePresheafData.{u, u} S where
  carrier _ := PUnit
  addCommGroup _ := inferInstance
  restrict _ := 0
  restrict_id _ _ := rfl
  restrict_comp _ _ _ := rfl

/--
X.定義5.3 典型例の**退化** instance: short exact sequence
`0 → Q_E → Q_E → 0 → 0` と零 base reading による self-lift fiber。equation
system が生成する `Q_E`(#3732 の `ObstructionQuotient`)だけから構成され、
追加の selected data を取らない。`equationLiftSystem` を型どおり発火させる
instance を与えるが、`B_E = 0` のため lift problem の非自明な内容(非零
base reading による問題の選択)は発火しない(module header の
Implementation notes に詳細を申告)。

これは「`P_E` が生成できる」ことを意味しない: 生成できるのはこの退化
self-lift instance だけであり、どの lift problem を解くかの選択は X.§1
入力6 のとおり selected のままである(module header の claim boundary)。
-/
def equationSelfLiftFiber (S : Site.AATSite A) :
    LiftFiberData (equationSitePresheaf S) (equationSitePresheaf S)
      (zeroSitePresheaf S) where
  incl _ := AddMonoidHom.id _
  incl_natural _ _ := rfl
  proj _ := 0
  proj_natural _ _ := rfl
  incl_injective _ _ h := h
  exact_at_middle _ l := ⟨fun _ => ⟨l, rfl⟩, fun _ => rfl⟩
  base _ := 0
  base_natural _ := rfl

/-- Self-lift fiber の零 local lift atlas(X.§1 入力6 の selected local lift
atlas(R0 §4.9 の入力6b)を零 lift に取った instance)。 -/
def equationSelfLiftAtlas (S : Site.AATSite A) (𝒰 : MonomorphicOrderedCover S) :
    CoefficientLiftAtlas ((equationSelfLiftFiber S).equationLiftSystem 𝒰) where
  localLift _ := ⟨0, rfl⟩

/--
X.定義5.3 の差生成が生成 `Q_E` 上で走ることの確認: self-lift fiber の零
atlas から C2 residual engine(`leftOn` / `rightOn` / `diffAt`)が生成する
`r_E` は零 cochain(零 atlas の正しい帰結であり、非自明な residual の発火
witness ではない)。補題5.4 本体(cocycle 性・選択非依存性)の named surface
は既存 `SagaEquationPacket.equationResidualCochain_cocycle` /
`equationResidualClass_choice_independent` が担う。
-/
theorem equationSelfLiftAtlas_residual (S : Site.AATSite A)
    (𝒰 : MonomorphicOrderedCover S) (p : KeptPair 𝒰) :
    (equationSelfLiftAtlas S 𝒰).residual p = 0 := by
  have h : (equationSelfLiftAtlas S 𝒰).rightOn p =
      (equationSelfLiftAtlas S 𝒰).leftOn p := by
    apply Subtype.ext
    show (equationSitePresheaf S).restrict (𝒰.pairSnd p.fst p.snd) 0 =
      (equationSitePresheaf S).restrict (𝒰.pairFst p.fst p.snd) 0
    rw [map_zero, map_zero]
  show ((equationSelfLiftFiber S).equationLiftSystem 𝒰).diffAt (.pair p)
      ((equationSelfLiftAtlas S 𝒰).leftOn p)
      ((equationSelfLiftAtlas S 𝒰).rightOn p) = 0
  rw [h]
  exact ((equationSelfLiftFiber S).equationLiftSystem 𝒰).diffAt_self _ _

/-!
## R0 §4.9: 定理1.1 入力束の production 組み立て
-/

namespace SagaEquationPacket

/--
R0 §4.9: 定理1.1 入力束を production route から組み立てる。equation 側は
`SupportAtomEquationSelection`(入力3(R0 §4.3)の correspondence の生成源への
selected 入力)と selected lift-fiber datum(入力6a の生成源、R0 §4.6)から
`realization` / `equationLiftSystem` で生成し、semantic 側入力(入力1・5、
R0 §4.1・§4.5)、lift atlas(入力6 の selected local lift atlas、R0 §4.9 の
入力6b)、`β`(入力7、R0 §4.7)は X.§1 の三分類のとおり selected のまま
受け取る。completeness 対(入力4、R0 §4.4)は従来どおり bundle に入れず
定理仮定として受ける。normalization(入力8、R0 §4.8)は X.§7 のとおり
comparison core の仮定に含まれないため packet に束ねず、本 constructor も
受け取らない。

universe 境界: `equationSitePresheaf S : SitePresheafData.{u, u}` と
`LiftFiberData` の同一 universe 制約により、本 constructor が組める packet は
`SagaEquationPacket.{u, v, x, u}`(lift state universe `y := u`)に限られる。
R0 §1 が `y` の instantiation として想定する `Type (u+1)` の lift state には
この経路では届かない(一般 packet は従来どおり直接構成で受ける)。

claim boundary: 本宣言が固定するのは定理1.1 入力束の production 組み立て
**面**(型)である。導入時点(#3734)では本 constructor を具体 site へ
適用した packet instance は存在しなかった(circle witness の `liftSystem`
は `LiftFiberData` 形でないため流せない — この事実は不変)。初の具体
instance は C7.5(#3803)の `DescentWitness.descentPacket` が与える。
-/
def ofProduction
    (R : AtomOccurrenceReading S) (𝒰 : MonomorphicOrderedCover S)
    (P : SemanticRepairPresentation.{u, v} S R)
    (sel : SupportAtomEquationSelection S)
    (Psem : AffineSemanticRepairSystem.{u, v, x} P 𝒰)
    (repairAtlas : SemanticRepairAtlas Psem)
    {L B : SitePresheafData.{u, u} S}
    (fiber : LiftFiberData (equationSitePresheaf S) L B)
    (liftAtlas : CoefficientLiftAtlas (fiber.equationLiftSystem 𝒰))
    (stateCorrespondence :
      PrimaryStateCorrespondence (sel.realization P 𝒰).chiE Psem
        (fiber.equationLiftSystem 𝒰)) :
    SagaEquationPacket.{u, v, x, u} S where
  occurrenceReading := R
  cover := 𝒰
  presentation := P
  realization := sel.realization P 𝒰
  repairSystem := Psem
  repairAtlas := repairAtlas
  liftSystem := fiber.equationLiftSystem 𝒰
  liftAtlas := liftAtlas
  stateCorrespondence := stateCorrespondence

variable (R : AtomOccurrenceReading S) (𝒰 : MonomorphicOrderedCover S)
  (P : SemanticRepairPresentation.{u, v} S R)
  (sel : SupportAtomEquationSelection S)
  (Psem : AffineSemanticRepairSystem.{u, v, x} P 𝒰)
  (repairAtlas : SemanticRepairAtlas Psem)
  {L B : SitePresheafData.{u, u} S}
  (fiber : LiftFiberData (equationSitePresheaf S) L B)
  (liftAtlas : CoefficientLiftAtlas (fiber.equationLiftSystem 𝒰))
  (stateCorrespondence :
    PrimaryStateCorrespondence (sel.realization P 𝒰).chiE Psem
      (fiber.equationLiftSystem 𝒰))

/-- 組み立てた packet の realization は production constructor の生成物。
simp normal form: 左辺(packet field)を右辺(生成物)へ展開する。 -/
@[simp] theorem ofProduction_realization :
    (ofProduction R 𝒰 P sel Psem repairAtlas fiber liftAtlas
        stateCorrespondence).realization =
      sel.realization P 𝒰 :=
  rfl

/-- 組み立てた packet の lift system は生成 `Q_E` 上の典型例 instantiation。
simp normal form: 左辺(packet field)を右辺(`equationLiftSystem` 適用)へ
展開する(`equationLiftSystem_eq_liftSystem` は simp 非登録なのでここで安定)。 -/
@[simp] theorem ofProduction_liftSystem :
    (ofProduction R 𝒰 P sel Psem repairAtlas fiber liftAtlas
        stateCorrespondence).liftSystem =
      fiber.equationLiftSystem 𝒰 :=
  rfl

end SagaEquationPacket

end Saga
end SemanticRepair
end AAT.AG
