# Research GOALs

GOAL とは、研究で成し遂げたい能力や到達像である。通常は証明したい定理の一覧ではない。定義と改訂は人間の判断による。`$research-loop` は、active な GOAL に対して候補を探索し、四審判、Lean 検証または証拠固定、SCORE 監査、PR レビューを通して、GOAL の能力がどれだけ増えたかを積み上げる。`research mode: target-theorem` の GOAL では、GOAL の能力を代表する一つの大定理をカードに定義し、その証明を完了条件にしてよい。

各 GOAL の静的定義、固定 target statement、完了条件は、このディレクトリの GOAL カードを正本とする。active な GOAL は、サイクルの先頭で `$research-loop` または `$target-theorem-loop` が `goal defect` を検査する。必要な項目は末尾の「GOAL カードの型」にまとめる。カードの中に現れる NT 番号や大定理 G1-G8 は、[docs/note の AG 版考察ノート](../../docs/note/aat_ag_porting_bridges_grand_theorems.md)で定義する。

active threshold、current SCORE、proof state、サイクル履歴などの実行状態は、GOAL ごとの GitHub tracking Issue を正本とする。ループ実行中は GOAL カードを編集せず、改訂が必要なら tracking Issue または別 Issue に提案を残す。

## 命名規則

GOAL id は `G-<NNN>-<領域>-<テーマ>` とする。`<NNN>` は 101 から始まる3桁の
グローバル通し番号(領域をまたいで単調増加)、`<領域>` は `aat` / `sft` 等、
`<テーマ>` は短い kebab-case。略称には `G-<NNN>` を用いる。
旧形式 `G-<領域>-<テーマ>-<連番>` のカードは改名しない。

## active

- [G-117-aat-lax-diagnostic-projector](G-117-aat-lax-diagnostic-projector.md)
  (G-116 後続。冪等 modification `ν` と診断選択子の lax law。G-114 refinement mate /
  G-115 `upperDecisionSolution` の同型判定を (i) として引き受ける)
- [G-aat-quality-surface-01](G-aat-quality-surface-01.md)
- [G-sft-conway-01](G-sft-conway-01.md)
- [G-aat-quality-surface-04](G-aat-quality-surface-04.md)

## draft（人間の確認待ち）

- [G-119-aat-realization-comparison-idempotents](G-119-aat-realization-comparison-idempotents.md)
  (n1010 S1。比較と冪等完備化の交換、AAT三段への接続、canonical正規化の関手)
- [G-aat-quality-surface-03](G-aat-quality-surface-03.md)
- [G-sft-law-transport-01](G-sft-law-transport-01.md)
- [G-sft-deformation-01](G-sft-deformation-01.md)
- [G-sft-ensemble-01](G-sft-ensemble-01.md)

## completed

- [G-118-aat-diagnostic-descent-transport](G-118-aat-diagnostic-descent-transport.md)
  (`target-theorem-proved`。入力表示変更に自然な比較分類、fixed firing、
  mixed transport、係数観測による情報損失を確定)
- [G-101-aat-atom-foundation](G-101-aat-atom-foundation.md)
- [G-102-aat-two-phase-obstruction](G-102-aat-two-phase-obstruction.md)
- [G-103-aat-canonical-resolution](G-103-aat-canonical-resolution.md)
- [G-104-aat-resolution-invariance](G-104-aat-resolution-invariance.md)
- [G-106-aat-transport-coherence](G-106-aat-transport-coherence.md)
- [G-107-aat-uniform-invariance-characterization](G-107-aat-uniform-invariance-characterization.md)
- [G-108-aat-geometry-reading-transport](G-108-aat-geometry-reading-transport.md)
- [G-109-aat-cross-stage-coherence](G-109-aat-cross-stage-coherence.md)
- [G-110-aat-doctrine-fiber-product](G-110-aat-doctrine-fiber-product.md)
- [G-111-aat-indexed-base-change-schema](G-111-aat-indexed-base-change-schema.md)
- [G-112-aat-exact-bottom-coverage](G-112-aat-exact-bottom-coverage.md)
- [G-113-aat-diagnostic-conservativity](G-113-aat-diagnostic-conservativity.md)
- [G-114-aat-refinement-base-change](G-114-aat-refinement-base-change.md)
  (`target-theorem-proved`。Gr4 O8–O9)
- [G-115-aat-upper-stage-lift](G-115-aat-upper-stage-lift.md)
  (`target-theorem-proved`。Gr4 O10–O11。upper solution の `IsIso` 決定は
  G-117 (i2) へ)
- [G-116-aat-idempotent-exchange-structure](G-116-aat-idempotent-exchange-structure.md)
  (`target-theorem-proved`。exchange 反例の背後の冪等正規化、raw failure
  classification、fixed finite witness。Gr4 を閉じるカードは作らない。G-114 /
  G-115 成分の同型判定は G-117 (i) へ)
- [G-aat-quality-surface-02](G-aat-quality-surface-02.md)
- [G-aat-quality-surface-05](G-aat-quality-surface-05.md)
- [G-aat-quality-surface-06](G-aat-quality-surface-06.md)
- [G-aat-quality-surface-07](G-aat-quality-surface-07.md)

## inactive

- [G-105-aat-structural-cover-invariance](G-105-aat-structural-cover-invariance.md)
  (`target-refuted`。改訂裁定待ち — 反証記録と salvage reading はカードを参照)

## GOAL カードの型

モードごとに型を分ける。`score-phase`（省略時のモード）の必須項目と欠陥判定は
[探索型カードの検査基準](../../.codex/skills/research-loop/references/goal-card-contract.md)を参照する。
以下は新規の`target-theorem`カードの記載基準である。

### 適用範囲

この基準がmainへ導入された後に新規作成するtarget-theoremカードへ適用する。
導入前から存在するdraft・active・completedカードには、移行・削減・再監査を要求しない。
新基準への不適合を既存カードの`goal defect`としない。改名や既存draftのactive化を
新規作成とは扱わない。形式の判別と適用版の記録手順は
[targetカードの読み取り手順](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md)にある。

### 必須の内容

**GOALカードは研究目標を書く場であり、実装の詳細設計ではない。**
何を明らかにし、何を構成・証明すれば達成となるかを定める。

カードは、研究目標の達成を判定するための次の5項目を持つ。見出しの表記は固定せず、
内容を統合して書ける。draftはactive化までに内容を確定する。

| 項目 | 書く内容 |
| --- | --- |
| 基本情報 | `id`、`status`、`research mode: target-theorem`、tracking Issueへの参照 |
| 研究目的 | 明らかにしたいことと、既存成果から進む点 |
| 固定target | 入力、対象の制限、量化対象・量化順、構成義務、結論 |
| 前提・構成台帳 | 前提の役割、必要な構成・証拠、その出所と使用先 |
| 完了条件 | 全義務の確定、必要な成果物と置き場所、固有のwitness条件、達成として認める結果、共通完了基準への参照 |

証明方針の概略、目標を特定する既存宣言の参照表、研究背景は必要な場合だけ追加する。`research aim`、
`core tension`、`rival`を独立の必須節にせず、研究目的で一度だけ説明する。
SCORE用項目と`not-applicable`、独立した`target proof strategy`は要求しない。

### 要求を一か所で定義する

各要求は一か所で定義し、成果物一覧・台帳・監査からは条項番号などで参照する。
targetを成果物欄へ全文再掲せず、台帳を第二の本文にしない。同じ条件を肯定形・禁止形・
停止条件として繰り返さない。レビューfindingは、その要求の定義箇所へ反映する。

共通の監査・anti-weakening・レビュー・停止規則は、読み取り手順が示す共通基準への
参照で適用する。カードには、このGOALで追加の特定が必要な条件だけを書く。
共通基準の適用版を追跡し、後日の更新で走行中の要求を暗黙に変えない。

### 固定targetの精度

各条項で、入力として受け取るもの、入力から構成するもの、独立に構成した結果について
証明することを区別する。等式・同型・保存・反映・存在・分類の違いを保持し、
一般定理と名前付き対象での具体的決定との接続を示す。

数学的な構成経路そのものが研究対象なら、その経路を固定する。同じ数学的要求を満たす
別の証明方法まで禁止しない。補題の分割・探索順、内部API、データ構造、実装手順などの
詳細設計はIssue／report側に置く。既存宣言やデータを固定targetの指示対象として
特定することと、その実装方法を指定することを区別する。

### 前提・構成台帳

| 対象・対応条項 | 役割 | 必要な構成・証拠 | 出所・使用先 |
| --- | --- | --- | --- |
| 前提や構成と、それを使う条項 | 入力として保持／一般定理の仮定／構成・放電義務 | targetの該当箇所を参照 | 何から得て、どの構成・保存則・結論で使うか |

同じ前提でも定理・経路ごとに役割が異なれば行を分ける。一般定理の仮定と、具体例で
その仮定を証明する義務を区別する。結論との循環が疑われる前提には理由と必要な確認を
書くが、全行へ定型的な「結論相当でない理由」を追記しない。
proof-useは対応する構成・保存則・結論へ指定し、全前提を全最終定理で直接使うことを
要求しない。既存の監査roleとの対応は読み取り手順で扱う。

### witnessと達成として認める結果

witnessを要求するときは、固定するデータと選択してよいデータ、評価する写像・成分・作用、
同じ例で同時に成立させる条件、一般定理との接続を特定する。「非退化な例」だけでは
足りない。作用元の非恒等性と作用の非恒等性などを区別し、独立の現象を理由なく
一つのwitnessへ束ねない。

命題の証明・反証のいずれも達成として認める条項は、成立と不成立それぞれに必要な
具体的証拠を事前に定める。不成立については反例の構成なのか非存在の証明なのかも書く。
それ以外の固定主張への反例は共通の反証停止規則で扱う。

### 実行記録の所在

承認・改訂・棄却の経緯、旧target、サイクル、blocker、放電状況、完了日、CI、査読結果、
merge記録、同期予定、後続研究の割当て・進行状態はIssue／reportへ置く。
台帳の実際の宣言対応もreportで記録する。先行成果の定義・宣言・参照版など、
固定targetを特定する情報はカードに残せる。棄却の経験から得た条件は、現在の要求として
一度だけ書く。ループ中にtargetを改める必要がある場合は人間の判断を求める。

### 追記とレビュー

文やfieldを追加するときは、次を確認する。

1. これがないと、どの誤読・誤判定が可能になるか。
2. 同じ要求がカードまたは共通基準に既にないか。
3. 要求を満たしたことを、何の証拠で判定できるか。
4. 研究目標の特定に必要な条件か、実装側で扱う詳細設計か。後者はカードへの追記を要求しない。

過去の発火実績は判断材料であり、発火の有無だけで採否を決めない。防ぎたい誤判定、
検出証拠、正当な研究の反復を不必要に止めないかを評価する。候補選定の時系列などの
特別な制約はanti-weakeningから自動的に追加せず、目的・固定時点・修正可能範囲を明記する。
行数上限は設けない。固有の数学的条件の不足と要求の多重掲載の両方を確認する。
