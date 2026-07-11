# AAT semantic repair-gluing 複体の据え方 — genius unlock への設計図

研究 GOAL [`G-aat-quality-surface-01`](../../research/goals/G-aat-quality-surface-01.md) の本丸 (open genius target)
である **semantic repair-gluing obstruction theorem** を、過大主張せずに有限から積み上げる
ための設計考察ノート。これはメモであり、正本 (`docs/aat/algebraic_geometric_theory/`) でも
研究レポート (`research/reports/`) でもない。確定した成果ではなく、これから PRD 化して
Codex の `$research-loop` に Lean 実装を渡すための **図面**である。

source note: [aat_quality_surface.md](aat_quality_surface.md) / 成果台帳:
[research/reports/G-aat-quality-surface-01.md](../../research/reports/G-aat-quality-surface-01.md)

---

## 0. 要旨

Cycle 1-106 は、品質 certificate geometry の **必要性・検出・不変性**側を Lean で sorry なしに
積み切った。残る本丸は、層コホモロジーでいう **descent(局所→大域)** の品質版:

> 各 chart で local repair が成立していても、overlap の semantic residual obstruction が
> nonzero なら、それらは単一の global repair へ貼り合わない。逆に obstruction が vanish すれば
> 貼り合う。

本ノートの主張は三つ。

1. **必要性と十分性をはっきり分ける。** Codex 案の「弱い有限版」と「Čech-style 版」は、どちらも
   *global repair が存在する ⇒ obstruction vanish*(= **必要性 / 検出器の健全性**)の同じ向き
   である。本丸 (genius unlock) はその**逆向き** *obstruction vanish ⇒ global repair 実在*
   (= **十分性 / 完全性 / 本当の descent**) であり、rival が原理的に取れない新規性もここに宿る。
2. **有限 Čech 設定では、逆向きの難所はコホモロジー代数ではなく semantic faithfulness。**
   `δ⁰x = c` は有限の組合せ系で「解ける ⟺ `[c]=0`」はほぼ定義通り。本当の content は
   「`δ⁰` の原像 `x` が、形式解ではなく**正真正銘の global repair certificate** であること」。
   この橋は既に Cycle 77 / 78 / 83 / 85 の faithfulness 補題群が用意している。
3. **複体は最初から cochain 形で建てる。** 必要性だけ刈り取って後で複体を建て直す、をしない。
   `GlobalRepairCoherent` を**大域存在**として定義することで Stage 1 を非自明化し、
   かつ Stage 2 / 3 がその構造をそのまま再利用できるようにする。

到達段階の見立て:**Stage 1 = 次サイクルで proved-in-research 可能**、**Stage 2 = 設計すれば十分可能**、
**Stage 2.5(本丸の逆向き)= faithfulness bridge 次第で地続き**、**Stage 3(本物の `H^1` 昇格)= 次か次々フェーズの大定理**。

---

## 1. 現状認識: 何が積まれ、何が欠けているか

### 1.1 積み切った側(必要性・検出・不変性)

すでに `research/lean/ResearchLean/AG/QualitySurface/` に sorry なし・独自 axiom なしで存在する材料:

| 役割 | 既存 artifact | Cycle |
| --- | --- | --- |
| 障害の生 cochain と cut-noise 商 | `ResidualCutCochain`, `CutNoiseEquivalent`(`SemanticResidualObstructionClass.lean`) | 92 |
| gauge 不変(same-carrier edge noise) | `SemanticResidualAtlasGauge.lean` | 93 |
| atlas map 下の cut-locus 移送 | `pushResidualCutCochain`, `ResidualCutLocusEmbedding/Equivalence`(`SemanticResidualAtlasMorphism.lean`) | 94-95 |
| 修復 hitting の必要性 | residual cut/status-drop の vanishing は hit を要求 | 96-104 |
| 有限 scanner の exactness | `firstResidualStatusDrop?_none_iff_listedClear` 等 | 101, 104 |
| source↔target アラーム整合 | unhit-to-target scanner bridge | 105 |
| target hit の source 由来 | generated target scanner provenance | 106 |
| **cocycle witness の原型** | `SemanticRepairCocycleWitness.lean`(local-pass / residual-fail) | 77 |
| **十分性のための faithfulness** | projection kernel(78)/ component faithfulness(83)/ transport naturality(85) | 77-85 |
| **逆向きの検算用 witness** | `VisibleLocalSemanticGluingObstruction.lean`(visible/local では gluing exactness を反映できない有限例) | 80 |

### 1.2 欠けている側(本物の定理に必要な三つ)

1. **本物の coboundary 商**: いまは cut-locus support の preclass(cut-noise 同値で割った degree-one
   準クラス)であって、`H^1 = Z^1/B^1` の `B^1`(coboundary)を持たない。
2. **圏的関手性**: 移送は**選ばれた** cut-preserving map に対して。任意 refinement 圏上の関手として
   intrinsic(cover 非依存)になっていない。Cycle 93 の gauge 不変はその同一 carrier 版にすぎない。
3. **十分性(構成的存在)**: 全サイクルが明記して避けてきた *vanish ⇒ global repair が実在する*。
   これが descent の「貼り合わせる」方向であり、genius unlock の核。

### 1.3 核心の非対称性(本ノートの主眼)

```text
必要性:  GlobalRepairCoherent A  →  ObstructionClass A = 0     [Stage 1, 2 で達成可能]
         対偶: ObstructionNonzero A → ¬ GlobalRepairCoherent A
十分性:  ObstructionClass A = 0   →  GlobalRepairCoherent A     [Stage 2.5 = genius unlock]
```

Codex 案の「missing center(global repair → vanish)」は **必要性側**。これは健全な検出器を
作るだけでも価値があるが、**それ単独では descent の同値ではない**。「`H^1` が品質貼り合わせを
**ちょうど**捉える」は十分性まで行って初めて言える。

---

## 2. 問い(採否の判定規律)

この設計を採るかどうかは、次の問いに照らして判定する。各 Stage はこの問いのどれを前進させるかで
SCORE と昇格可否を読む。

> **Q1(非自明性).** `GlobalRepairCoherent` を「全 overlap が clear」の論理積ではなく
> **大域証明書の存在**として定義したとき、Stage 1 は「大域切断の restriction は overlap で
> 必ず clear」という descent の片割れになり、定義からの自明 (`弱すぎて自明`) を回避できるか。

> **Q2(faithfulness の十分性).** 有限 Čech 複体で `[c]=0`(coboundary)から得た `δ⁰` の原像が、
> Cycle 77/78/83/85 の補題によって**正真正銘の global repair certificate** であることを示せるか。
> 形式解と semantic repair の同一視が、新たな公理なしに既存材料から強制されるか。

> **Q3(検算の通過).** 建てた複体を Cycle 80 の visible/local gluing obstruction witness に当てたとき、
> `H^1 ≠ 0`(障害が消えない)になるか。なるなら複体は自明化していない。ならないなら `δ⁰` の設計が
> 緩すぎる。

候補が Q1 を満たさなければ四審判 A(厳密性)で落ち、Q3 を満たさなければ A の自明化監査で落ちる。
Q2 を満たした時点で初めて genius unlock を主張してよい。

---

## 3. 複体の設計

### 3.1 対象: semantic repair atlas

固定 architecture `A` の有限 profile における品質 atlas を、次の有限データとして置く。
**新しい抽象は最小にし、residual / cut-locus / hitting は既存定義を再利用する。**

- `Chart`(有限): 計測の chart(selected cover の cell)。
- `Overlap c c'`(有限): chart 間の重なり。各 overlap は supplied transition law と residual reading を持つ。
- `localRepairCert : Chart → Type`: chart ごとの local repair 証明書(= `0-cochain` の住人)。
- `residual : (c c' : Chart) → Overlap c c' → ResidualCutCochain`: overlap 上の semantic residual
  (= `1-cochain`)。**既存の `ResidualCutCochain` をそのまま住まわせる。**
- `restrict`: local repair 証明書を overlap 側の reading へ落とす制限。これが `δ⁰` の素になる。

### 3.2 微分 δ⁰ = restriction 差

```text
C^0 = Π_c localRepairCert c          (chart ごとの local repair の割当)
C^1 = Π_{c,c'} ResidualCutCochain    (overlap ごとの residual)

(δ⁰ g)(c,c') := restrict_c (g c)  −  restrict_{c'} (g c')    （overlap での食い違い）
```

`δ⁰` は「ある大域候補 `g` が overlap でどれだけ食い違うか」を測る。`δ¹∘δ⁰ = 0`(有限なので
直接計算)を満たすように三重 overlap の整合を置く。**ここで `δ⁰` を勝手に設計しない。**
Cycle 85(residual support transport iff source/target closure equivalent)が「restrict は
residual closure と可換であるべき」という形を強制し、Cycle 77 の cocycle witness が
`δ⁰` の値域の形を与える。`δ⁰` は既存の意味論から**縛られて決まる**。

### 3.3 障害クラス

```text
Z^1 := { c ∈ C^1 | δ^1 c = 0 }        (cut-noise 同値で割った既存 preclass を昇格)
B^1 := im δ^0                          (大域候補から来る食い違い = 「貼り合わせ可能なズレ」)
H^1 := Z^1 / B^1                       (本物の coboundary 商)
ObstructionClass A := [residual] ∈ H^1
```

Cycle 92 の `CutNoiseEquivalent` は `Z^1` 側の同値、新しく要るのは `B^1`(`δ⁰` の像)だけ。
**preclass → 本物のクラスへの差分は `B^1` の一点に集約される。**

### 3.4 大域証明書(自明化ガードの心臓)

```text
GlobalRepairCoherent A :=
  ∃ g : (∀ c, localRepairCert c),  CompatibleOnAllOverlaps A g
```

**論理積ではなく大域存在**。これにより Stage 1 は「大域 `g` の restriction は全 overlap で
residual を消す」という非自明命題になる(問い Q1)。

---

## 4. 段階定理

### Stage 1 — 弱い有限版(必要性)`[次サイクルで proved-in-research 可能]`

> **定理 (Stage 1).** `ObstructionNonzero A → ¬ GlobalRepairCoherent A`。
> 同値に `GlobalRepairCoherent A → 全 overlap で residual cut / status-drop が clear`。

`H^1` を持ち出さず、residual transition cut / status-drop の言葉で証明する。証明は既存 scanner
tower をほぼそのまま使う:大域 `g` の restriction が overlap を clear にする →
`firstResidualStatusDrop?_none_iff_listedClear`(C101)で scanner none → canonical vanish。
**report には必ず「これは必要性側・健全な検出器であって descent 同値ではない」と明記する**(過大主張ガード)。

### Stage 2 — Čech-style 有限版(必要性を複体語で)`[設計すれば十分可能]`

> **定理 (Stage 2).** `B^1 ⊆ ker`(大域から来るズレは障害を作らない)。すなわち
> `GlobalRepairCoherent A → ObstructionClass A = 0` を `H^1` の言葉で言い直す。

Stage 1 を §3 の複体に載せ替える。新規部分は `δ⁰` と `B^1` の定義、および `δ¹∘δ⁰=0`。

### Stage 2.5 — 逆向き = genius unlock(十分性)`[本命 / faithfulness bridge 次第で地続き]`

> **定理 (Stage 2.5).** `ObstructionClass A = 0 → GlobalRepairCoherent A`。
> 有限ゆえ `[c]=0` は `c = δ⁰ x` なる `x` の存在を与える。その `x` が **CompatibleOnAllOverlaps を
> 満たす本物の global repair certificate** であることを、Cycle 78(projection kernel)/ 83
> (component faithfulness)/ 85(transport naturality)の faithfulness 補題で示す(問い Q2)。

ここが新規性の核。**コホモロジー代数は有限ゆえ易しく、難所は「形式 primitive ↔ semantic repair」
の同一視**であり、その材料は既にある。これが通れば「`H^1` が品質貼り合わせをちょうど捉える」を
有限 atlas 上で初めて主張できる。

### Stage 3 — 本物の AAT cohomology 昇格 `[次/次々フェーズの大定理]`

site / coefficient object に載せ、refinement 圏上の関手として cover 非依存の intrinsic
`H^1` obstruction にする。Cycle 93 gauge 不変 → 任意 refinement への一般化、Cycle 94-95 の
cut-locus transport → 関手性。本文 (`docs/aat/algebraic_geometric_theory/` Part IV/V/VIII)
への昇格判断はループ外の人間が行う。

### 双対(landing を綺麗にする系)`[Cycle 64-69 の延長]`

overlap-obstruction-basis ↔ repair-transversal の双対(Cycle 66-69)を Stage 2.5 の系として
回収できれば、「障害が最小修復を指定し、修復が障害を証す」両面定理になる。優先度は Stage 2.5 の後。

---

## 5. 自明化ガードと検算

- **Q1 ガード**: `GlobalRepairCoherent` は大域存在で定義する。論理積定義は禁止(Stage 1 が自明化)。
- **Q3 検算**: 各 Stage の Lean に、Cycle 80 `VisibleLocalSemanticGluingObstruction` の witness を
  当てる test 定理を必ず一本入れ、`H^1 ≠ 0` を要求する。緑になったら `δ⁰` が緩い。
- **過大主張ガード**: Stage 1/2 の report 記載は「necessity / 検出器健全性」と明示。十分性 (Stage 2.5)
  を証明するまで「descent 同値」「`H^1` がちょうど捉える」とは書かない。
- **公理ガード**: 既存同様、`propext`/`Quot.sound` のみ。`δ⁰`・`B^1`・faithfulness bridge の導入で
  `Classical.choice` や新 axiom を呼ばないこと(有限なので decidable で済むはず)。

---

## 6. Lean skeleton(Stage 1 を最初に切る形)

```lean
import ResearchLean.AG.QualitySurface.SemanticResidualObstructionClass
import ResearchLean.AG.QualitySurface.SemanticResidualStatusDropScanner
import ResearchLean.AG.QualitySurface.SemanticResidualTransportNaturality
-- 既存 residual / cut-locus / scanner / faithfulness を再利用する

namespace ResearchLean.AG.QualitySurface

structure SemanticRepairAtlas where
  Chart           : Type
  Overlap         : Chart → Chart → Type
  localRepairCert : Chart → Type
  -- δ⁰ の素: local 証明書を overlap reading へ制限する
  restrict        : ∀ {c c'}, Overlap c c' → localRepairCert c → (overlap reading)
  -- 1-cochain: 既存 ResidualCutCochain をそのまま住まわせる
  residual        : ∀ {c c'}, Overlap c c' → ResidualCutCochain
  -- 三重 overlap 整合 (δ¹∘δ⁰ = 0 を保証)
  cocycle         : ...

/-- 大域存在として定義(論理積にしない = Q1 ガード)。 -/
def GlobalRepairCoherent (A : SemanticRepairAtlas) : Prop :=
  ∃ g : (∀ c, A.localRepairCert c), CompatibleOnAllOverlaps A g

def ObstructionNonzero (A : SemanticRepairAtlas) : Prop := ...   -- [residual] ≠ 0 in H¹

/-- Stage 1: 必要性(健全な検出器)。descent 同値ではない。 -/
theorem no_global_repair_of_nonzero_obstruction (A : SemanticRepairAtlas) :
    ObstructionNonzero A → ¬ GlobalRepairCoherent A := by
  ...

/-- Stage 2.5(本命): 十分性。faithfulness bridge が core。 -/
theorem global_repair_of_vanishing_obstruction (A : SemanticRepairAtlas) :
    ¬ ObstructionNonzero A → GlobalRepairCoherent A := by
  ...  -- [c]=0 → c = δ⁰ x → (C78/83/85) x は本物の global repair

/-- Q3 検算: Cycle 80 witness で H¹ ≠ 0 を要求。 -/
theorem visibleLocalWitness_obstructionNonzero :
    ObstructionNonzero visibleLocalGluingWitnessAtlas := by
  ...

end ResearchLean.AG.QualitySurface
```

---

## 7. 推奨実行順序と PRD 化

1. **Part I = Stage 1 のみ**にスコープを絞る。acceptance:
   - `GlobalRepairCoherent` が大域存在で定義されている(Q1)。
   - `no_global_repair_of_nonzero_obstruction` が sorry なし・独自 axiom なしで通る。
   - Cycle 80 witness の `ObstructionNonzero` 検算定理が通る(Q3)。
   - report に「必要性側」明記。
2. Stage 1 が proved-in-research で固定できたら、Part II = Stage 2(複体語への載せ替え + `B^1`)。
3. Part III = Stage 2.5(faithfulness bridge)。**ここで初めて genius unlock を狙う。** 失敗したら
   「`H^1` は必要だが二次障害が残る」可能性を orientation-evidence として固定するのも可(それも成果)。
4. Stage 3(本物の昇格)は別フェーズ。

各 PRD は冒頭に本ノート §2 の問いを置き、四審判の判定規律として機能させる。
実装は Codex の `$research-loop G-aat-quality-surface-01` に渡す。

---

## 8. 非主張(claim boundary)

このノートと派生 PRD は、次を**主張しない**。

- 実コード全体の品質判定、source extraction / ArchMap observation の完全性、AI の理解可能性限界。
  これらは tooling(ArchSig)/ ArchMap author / SFT 側の contract であり、AAT 内へ持ち込まない。
- Stage 1/2 の時点での descent 同値、および「`H^1` がちょうど捉える」。十分性 (Stage 2.5) を証明する
  までは necessity(検出器健全性)に留める。
- 本物の site/sheaf 上の `H^1` への昇格。Stage 3 まではあくまで有限 Čech-quotient の近似であり、
  本文 (`docs/aat/algebraic_geometric_theory/`) への昇格はループ外の人間判断。
- repair の十分性を超えた global minimality / repair synthesis sufficiency / target-wide order
  canonicity(Stage 2.5 は「貼り合う repair が存在する」までで、最小修復の構成は別問題)。

主張するのは一貫して、**有限 atlas・supplied semantic atoms・supplied transition laws・
supplied residual readings** の上での命題だけである。
