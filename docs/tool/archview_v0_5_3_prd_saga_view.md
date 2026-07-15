# ArchView v0.5.3 PRD — SAGA ビュー波(診断階段の可視化 + vendoring)

- 状態: 起草(2026-07-15)
- 対象 Issue: #3422(PRD 固定)。実装 tracking は PRD 受理後に別 Issue を切る
- 実装: Codex prd-loop。1 PR = 1 実装 Issue
- 関連文書(現行 source of truth):
  - [ArchView gluing geometry contract](archview_gluing_geometry_contract.md) — viewer 忠実性契約の正本(本波で SAGA ビュー条項を追記する。§R7)
  - [ArchView 計測駆動幾何 設計ノート](../note/archview_measured_geometry_design.md) — AG 視覚言語の正本(§9)
  - [ArchView AI 時代コード理解支援 構想ノート](../note/archview_ai_code_understanding_hypothesis.md) — 本波をドッグフーディング実験の前提として位置づける(§6)

---

## 問い

**packet が実測した SAGA の診断階段(前提成立 → residual class → 転送・比較 → gate 決定)を、ArchView は人が追える一つの幾何の物語として描けているか。**

この問いを採否の判定規律として使う。

- 「描けている」と判定するのは、golden fixture(§R6)上で
  **診断階段の各段が viewer の視覚要素と1対1に対応する対応表**が成立し、
  かつ**沈黙している段(silence_by_design)が沈黙として見える**ときに限る。
- フィールドを viewer-data に投影しただけでは「描けている」に数えない。
  投影は手段であり、判定対象は階段としての可読性である。
- 逆に、階段の可読性を理由に packet に無い値を viewer 側で合成することは
  却下条件(§却下条件-1)である。物語は実測の並べ方で作り、捏造で作らない。

## 背景と現状診断

- v0.5.1(LawPolicy Stage 2)+ v0.5.2(SAGA 完全対応)の完了と是正全消化
  (2026-07-15 検証)により、SAGA 計測が完備した。M→V gating
  (計測が先、可視化が従)の「M」が揃い、SAGA の可視化が解禁された状態である。
- 一方、viewer 側の SAGA 区画はゼロである。`archsig-atom-viewer-data/v0.5.2` の
  emitter(`tools/archsig/src/ag_measurement.rs`)にも viewer
  (`tools/archview/archview.html`)にも saga 系フィールドは存在しない。
  packet には実測済みの SAGA 区画(下記)が在るのに、viewer は全面沈黙している。
- packet / gate report に実測済みで、viewer が沈黙している SAGA 区画:
  - grounding 段: saga-grounded の structural verdict 行(premise の holdsCriterion
    生値、reason token `MEASURED_LAW_DEFECT_AT_CHART` /
    `DISPLAYED_LAWS_HOLD_ON_SELECTED_CHARTS`、detector 件数)
  - descent 計測段: `saga-descent:residual-class`(class 値と非零性)、
    `saga-descent:boundary-membership`、`saga-descent:closure-diagnostics`、
    harmonic-debt invariant(`essentialRepairLowerBound`、cost model 供給状態)
  - 転送・比較段: `saga-comparison:h1-transfer`(六フィールド契約:
    incidenceBridgeKind / h1ComparisonDataKind / normalizedComplexFingerprint /
    classPrerequisite / targetClassComputed / contractChecked、status、
    conclusionCode、silence reason、whatNext)
  - gate 段: gate report(`archsig-gate-report/v0.5.2`)の decision と
    ruleOutcomes の appliedMapping(action = pass / pass_with_boundary / block、
    boundaryOverrideApplied)
- Three.js が unpkg CDN 参照のまま(`archview.html` の import map)であり、
  ネットワーク遮断環境や外部リポジトリでのドッグフーディングで viewer が
  空表示になる。旧 V-A の随伴残件。
- 旧設計の実装 wave 定義(V-A〜V-C)は
  `docs/archive/2026-07-archsig-v0.5.0-completed/design/design_archview.md` に
  退避済みで現行 source of truth ではない。本 PRD が V-C 相当の設計判断を
  現行正本群への参照とともに再固定する。旧 V-B2(schema slash 命名・`schema`
  キー統一)は版数一斉更新の波で消化済みであり、本波の対象ではない。

## 設計原則

1. **M→V gating(不変)**: viewer-data と viewer は packet / gate report の
   実測フィールドからの投影だけを描く。視覚的な豊かさは新しい verdict ではない。
2. **沈黙は描く**: silence_by_design の行は非表示にせず、「この段は沈黙している。
   次に何を供給すれば語れるか(whatNext)」を沈黙の視覚語彙で描く。
   レビュワーにとって沈黙の所在は情報である(構想ノート §3)。
3. **階段が単位**: 判定は「フィールド網羅率」ではなく「段の可読性」で行う。
   段⇔視覚要素の対応表(§AC1)が完了証拠の中心である。
4. **高さの意味はシーンごとに宣言する**: SAGA ビューの高さ = 次数
   (H⁰ / H¹ / H² 鉛直三層)はこのシーン限定であり、HUD で宣言する。
   他シーンの高さ = posetDepth と暗黙に混線させない。
5. **恒久契約は正本へ**: SAGA ビューの投影規則・沈黙表示規則・gate 入力契約の
   正本は gluing geometry contract に置き、本 PRD は作業項目と参照だけを持つ。

## 改修

### R1 — Three.js vendoring(ドッグフーディング前提整備)

- Three.js(現行 0.164.1)を `tools/archview/vendor/` へ vendoring し、
  `archview.html` の import map を相対参照へ切り替える。
- 閲覧手順の正は「`archview.html` + `vendor/` の同時コピー」とし、
  `tools/archview/README.md` と `examples/seam-ignition/build-sequence.sh` を同型へ更新する。
- release packaging(`.github/workflows/archsig-release.yml`)と
  cli.rs の packaging 契約テストを vendor 同梱へ同期する。
- 受け入れ条件: ネットワーク遮断環境で viewer が全シーンを描画できる。

### R2 — viewer-data への sagaDescent 区画投影

`archsig-atom-viewer-data` に `sagaDescent` 区画を追加し、
診断階段の4段構成で packet / 実測フィールドから投影する。

- (i) grounding 段: saga-grounded verdict 行(premise holds / fails の生値、
  reason token、detector 件数)。
- (ii) descent 計測段: residual class(値と非零性)、boundary membership、
  closure diagnostics、harmonic-debt(下界値と cost model 供給状態)。
- (iii) 転送・比較段: `saga-comparison:h1-transfer` の status /
  conclusionCode / 六フィールド契約 / silence reason / whatNext。
- (iv) 沈黙行: silence_by_design 行は status・reason・whatNext を保持したまま
  投影する。省略・非表示化・error への格上げをしない。
- 全 leaf は packet フィールドへの対応表(§AC6)を持つ。packet に無い値の
  合成・派生スコア化をしない。未計測は null / absent とする。
- schema catalog への登録と viewer-data validation の同期を含む。

### R3 — 版数一斉更新(v0.5.3)

- viewer-data 契約の変更に伴い、単一契約版数(受理完全一致)の規律に従って
  全 schema 文字列を `<name>/v0.5.3` へ一斉更新する。fixture・catalog・
  contract テスト・docs・website の同期を含む。
- **同期対象リストに CLAUDE.md / AGENTS.md の検証コマンド例を明示的に含める。**
  fixture 改名で記載コマンドが実行不能になる漏れが2回連続で起きている
  (v0.5.1 → Issue #3328 項目3、v0.5.2 → Issue #3418)。本波では
  「rg で旧版数文字列ゼロ + 記載コマンドの verbatim 実行」を AC5 として固定する。

### R4 — SAGA ビュー(1シーン)

- 診断階段を一つの幾何の物語として描く単一シーンを `archview.html` に追加する。
- 高さ = 次数(H⁰ / H¹ / H² 鉛直三層)はこのシーン限定とし、HUD で
  高さの意味を宣言する(設計原則4)。
- 各段は R2 の投影フィールドと1対1対応する視覚要素を持つ。
  段の間は診断の依存方向(前提 → 計測 → 比較 → gate)を視覚的に接続する。
- 沈黙の段は沈黙の視覚語彙(専用の表示様式 + whatNext の提示)で描く。
  「描かない」ことと「沈黙を描く」ことを区別する。

### R5 — gate 段(任意の第二入力)

- viewer が gate report(`archsig-gate-report/v0.5.3`)を任意の第二入力として
  受理し、階段の最終段に decision と per-row の action
  (pass / pass_with_boundary / block)、boundaryOverrideApplied を表示する。
- gate report 未供給時は gate 段を沈黙として描く(error にしない)。
- schema 不一致・packet との対応不整合は fail-closed
  (読み込み拒否と明示エラー)とする。

### R6 — golden fixture 固定

次の4系統の analyze 出力(viewer-data)を golden fixture としてロックし、
cli.rs の契約テストで固定する。

- (a) circle nerve residual class 非零(3-chart 三角 nerve、既存 fixture 系)
- (b) lawful firing(全 law hold、`DISPLAYED_LAWS_HOLD_ON_SELECTED_CHARTS`)
- (c) faithfulness supplied(descent 計測段まで到達)
- (d) faithfulness none(計測段以降が silence_by_design)

(a) の Lean witness 帰属(3辺形 = Lean proved / 2頂点形 = 本文仕様)は
既存の帰属注記(v0.5.2 R13 で固定済み)を参照し、本波で重複記述しない。

### R7 — 忠実性契約の正本更新

- `docs/tool/archview_gluing_geometry_contract.md` に SAGA ビューの投影規則・
  沈黙表示規則・gate 入力契約を追記する。恒久契約の正本はこちらであり、
  本 PRD は受理後 archive される(docs/guideline.md の PRD lifecycle)。

### R8 — docs / website 同期

- `tools/archview/README.md`、`docs/tool/README.md`、該当 docs
  (gate policy / compare の viewer 言及箇所)を同期する。
- website の archview 該当ページ(live demo / manual)に SAGA ビューの
  導線と説明を追加する。無制限 claim(「コードベース全体が分かる」型)を
  書かない(構想ノート §3 の規律)。

## 却下条件(反例駆動)

次のいずれかが実装に現れた場合、該当 PR を却下する。

1. **viewer 捏造**: packet / gate report に無い値・合成スコア・推測補完を描く
   (M→V gating 違反)。
2. **網羅偽装**: フィールドを投影しただけで、段⇔視覚要素の対応表が
   成立しない。投影の存在を「描けている」の証拠に数えない。
3. **沈黙の消去**: silence_by_design 行の非表示化・省略により
   「問題なし」に見せる。
4. **宣言落とし**: gate 未供給や faithfulness none を error 扱いにする。
   沈黙は失敗ではない。
5. **高さ意味の混線**: 高さ = 次数を SAGA ビュー外へ暗黙適用する、
   または HUD 宣言なしで導入する。

## Implementation Plan(PR 分割)

| PR | 内容 | 依存 |
| --- | --- | --- |
| PR-1 | R1 vendoring + packaging 同期 | 独立(先行可) |
| PR-2 | R2 sagaDescent 投影 + R3 版数一斉更新(v0.5.3) | PR-1 と独立 |
| PR-3 | R4 SAGA ビュー + R6 golden fixture 固定 | PR-2 |
| PR-4 | R5 gate 段入力 + R7 契約正本更新 + R8 docs / website 同期 | PR-3 |

各 PR は 1 実装 Issue に対応し、敵対レビュー(tool-review)を通す。

## Acceptance Criteria

- **AC1(問いの中心)**: 4 golden fixture すべてで、診断階段の各段⇔視覚要素の
  1対1対応表が成立し、cli.rs の契約テストでロックされている。
- **AC2**: faithfulness none fixture で計測段以降が沈黙として描かれ、
  whatNext が viewer 上で読める。
- **AC3**: gate report 供給時に最終段が decision と per-row action を表示し、
  未供給時は沈黙。schema 不一致は fail-closed。
- **AC4**: ネットワーク遮断環境で viewer が全シーンを描画できる(R1)。
- **AC5**: 全 schema 文字列が v0.5.3 で、旧 v0.5.2 文字列が rg でゼロ。
  CLAUDE.md / AGENTS.md の記載コマンドが verbatim で実行可能。
- **AC6**: sagaDescent 区画の全 leaf が packet フィールドへの対応表を持ち、
  対応の無い leaf が契約テストで検出される(捏造ゼロの機械検査)。
- **AC7**: 既存シーン・既存 fixture の回帰ゼロ(既存 cli テスト green)。

## Non-Goals

- compare の時系列表示(refinement zero-transport、TWO_PROFILES の viewer 表示)。
  run 2つを跨ぐ入力契約の拡張はドッグフーディングの実需が出てから扱う。
- 探索 UI(検索・フィルタ・近傍航行・source anchor)。構想ノートの実験
  (コードに戻らされた事由ログ)を待って再スコープする。
- 旧 V-B1 のシーン群(site-order / cover-nerve / gluing-h1 / locus-repair /
  law-conflict)の追加。同上。
- SAGA evaluator・packet 側の意味論変更。本波は投影と描画のみ。
- AAT 数学本文・Lean 形式化の変更。
