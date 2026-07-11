# ArchSig v0.5.0 PRD-1 — レガシー破棄(前半)と契約基盤

対象は ArchSig v0.4.0 リポジトリの「孤児コード・v0 世代 dead code の全削除」と
「単一契約版数 `<name>/v0.5.0` + 決定論 digest という artifact 契約基盤の敷設」
(統合ノートのロードマップ P0〜P2)。
本 PRD は v0.5.0 PRD 5 本の第 1 弾である(PRD-2: P3-P4 artifact/CI、PRD-3: P5-P6 v1 破棄+同期、
PRD-4: P7-P8 LawPolicy Stage 1 + SAGA Stage 1、PRD-5: P9 ArchMap SKILL)。

関連(設計の正本):

- [ArchSig v0.5.0 再設計ノート](../note/archsig_v0_5_0_redesign_note.md) — §2(レガシー破棄)、§5(契約基盤)、
  §8 裁定7(単一契約版数)・裁定10(後方互換の全面不採用)、§9(ロードマップ)
- [design_legacy-triage](../note/archsig_v0_5_0/design_legacy-triage.md) — 削除対象の完全リストと根拠
- [design_artifacts](../note/archsig_v0_5_0/design_artifacts.md) — §3.0/§3.0.1(命名規約・digest / 決定論基盤)
- [責務憲章](archmap_lawpolicy_archsig_responsibility_charter.md) — 三層責務の理論的根拠

## 問い

**この変更は、どの責務境界の回復か。**

本 PRD の全作業項目はこの問いに答えられなければならない。帰属先は次の 3 軸のみとし、
各要件(R 番号)に軸タグを付す。

- **A軸(層越境の除去)**: v0 LawPolicy DSL(`obstructionCircuitDefinitions` /
  `signatureAxisDefinitions` / `spectrumMeasurementProfile` / `part4DistanceProfile` 等の手書き)は、
  責務憲章「LawPolicy が書かないもの」(計算手続き・測定実装)への実際の層越境である。
  その型・検証・fixture の削除は制度選択層の境界回復である。
- **B軸(到達不能経路の除去)**: コンパイルすらされない孤児と、CLI から到達不能なまま
  ≈35,000 行が居座る v0 世代は、「このリポジトリの計測経路は
  `archmap + 選択された制度 → measurement packet` だけである」という単一 path 宣言の反証物である。
  その除去は宣言を検査可能にする前提である。
- **C軸(契約基盤の敷設)**: 単一契約版数(裁定7)・`schema` キー統一・決定論 digest・`toolVersion` は、
  境界の一括払いを artifact 契約の水準で支える基盤であり、以降の PRD(packet 新形 / gate /
  compare / law surface)がすべてこの上に立つ。

採否の判定規律:

- **(採用条件)** 3 軸のいずれかに帰属できる削除・敷設だけを採用する。
- **(却下条件)** 軸に帰属できない作業は、たとえ有益でも本 PRD では却下する。とくに:
  v1 path の削除・AG path 内の判定語残滓掃除(`witness-counting@1`、registry の判定語 predicate 3 件)は
  PRD-3 の管轄、packet の形状変更は PRD-2 の管轄であり、本 PRD に入れない。
  また、互換窓・dual-emit・専用 removal error 等の**互換機構の追加はいかなる形でも却下**する(裁定10)。
- **(claim 規律)** 削除の意義は上の軸の言葉で書く。v0 削除に「憲章が名指しした mismatch 破損の回復」等の
  earned でない claim を負わせない(mismatch 混入は v2/AG 側の事象であり、観測純化 PRD が回復済み)。

## Core Thesis

v0.4.0 の実態は三世代 + 孤児の四層構造である(src 66,477 行の実測。統合ノート §0)。

| 層 | 実体 | 行数 | 到達性 |
| --- | --- | ---: | --- |
| v0(dead) | analysis packet builder + 全部入り LawPolicy DSL | ≈35,000 | CLI 不達(unit test のみが生存理由) |
| 孤児 | `src/reports/` ほか | ≈5,000 | mod 宣言なし。コンパイル外 |
| v1(legacy) | typed evaluator + pr-review | ≈11,000 | 現行 runtime(削除は PRD-3) |
| AG(current) | archmap v2 + profile → measurement packet | ≈13,000 | 現行一次。v0/v1 とコード独立 |

本 PRD は上 2 層(≈40,000 行)を削除し、残る全 artifact に単一契約版数と決定論 digest を敷く。
v1 層は受け皿(PRD-2 の gate / compare)が立ってから PRD-3 で削除する。

## 現状診断(証拠)

記載の行番号は設計時点の実測(design_legacy-triage / design_artifacts)。実装時に再確認する。

1. **孤児**: `tools/archsig/src/reports/`(4,120 行)、`src/cli/atom_viewer.rs`(658 行)、
   `src/cli/detail_index.rs`(230 行)はどの mod 宣言からも不参照。
2. **v0 dead**: `src/archsig_analysis_packet.rs`(15,416 行、`src/analysis/` 13,226 行を include!)、
   `src/schema/analysis_packet.rs`(2,931 行、`ArchSig*V0` 型 ≈130 個)。CLI から到達不能で、
   unit test 66 個 + `law_policy/tests.rs` 15 個 + `#[ignore]` CLI テスト 21 個だけが参照する。
3. **v0 LawPolicy DSL(A軸の物証)**: `src/schema/law_policy.rs:235-587` の `LawPolicyDocumentV0`
   (obstructionCircuitDefinitions / signatureAxisDefinitions / spectrumMeasurementProfile /
   homotopyMeasurementProfile / part4DistanceProfile を含む全部入り)。
4. **検証コマンド例が既に壊れている**: CLAUDE.md:84-87 / AGENTS.md:122-125 の `archsig analyze` 例は
   v0 fixture(`tests/fixtures/minimal/`)を参照し、現時点で
   `--input must have schemaVersion archmap/v1` で fail する(実行確認済み)。
5. **表記の三様化**: schema 識別子が `x/v1` と `x-v1`、キーが `schema` と `schemaVersion` で混在。
   run manifest は 3 様式(v1 成功 / v2 成功 / 失敗時)。`Cargo.toml` は `version = "0.1.0"` のまま。
6. **evaluator id の二重版数**: `ag.cech-obstruction@1` の `@1` は、コンパイル内蔵 evaluator の実体を
   一意に決める toolVersion と二重の版数である(裁定7)。

## Design Principles

1. **単一契約版数(裁定7)**: schema 文字列はすべて `<artifact-name>/v0.5.0`。
   「ArchSig v0.5.0 の artifact contract に適合する」の宣言であり、artifact 個別版数は消える。
   出力は常に自リリース版数で emit(schema 版数 = `toolVersion`)。
2. **受理は現行版数の完全一致のみ**: 互換窓・`since` 範囲・受理レンジは実装しない。
   旧 schema は一般 validation fail(エラー文言が現行契約名を名指す程度。専用 removal error は作らない)。
3. **互換ゼロ(裁定10)**: 受理・変換レイヤ・dual-emit・graceful degradation・バックフィルを一切作らない。
   過去 schema の正本は git tag v0.4.0(archive は Git history)。
4. **決定論**: 同一入力 → byte 同一出力。runId は入力 digest から決定的に導出し、
   タイムスタンプ・乱数を既定で含まない(`--stamp` opt-in)。
5. **Rust / Lean 非対応**: 本 PRD は Lean 塔に触れない(Lean guardrail 3 本の削除は PRD-3 に同梱)。
6. **PRD 間の中間状態**: PRD-1〜5 はすべて v0.5.0 リリース(タグ)前に積まれるため、
   PRD-4 が law-policy の形状を変えても schema 文字列は `law-policy/v0.5.0` のままでよい
   (リリース前の形状変更に互換の告知義務はない — 裁定10)。

## 改修(本体)

### P0 群 — 即着手(B軸)

- **R1 [B]** 孤児 3 点の削除: `src/reports/`(mod.rs / pr_review.rs / summary.rs /
  codebase_inspection.rs / detail_index.rs)、`src/cli/atom_viewer.rs`、`src/cli/detail_index.rs`。
  削除前に不参照(mod 宣言なし)を再確認する。cargo test の結果は変化しないこと。
- **R2 [B]** CLAUDE.md / AGENTS.md の `archsig analyze` 検証コマンド例を
  `tests/fixtures/ag_measurement/archmap_v2.json + law_policy_ag.json`(analyze 成功を確認済み)へ
  差し替える。R4 の fixture 削除に先行すること。`tools/archsig/README.md` の CLI Quick Start も
  同じ fixture 参照へ現行化する。

### P1 群 — v0 世代の全削除(A軸 + B軸)

- **R3 [A/B]** v0 dead コードの削除(完全リストは design_legacy-triage §3.2 Phase B が正):
  `src/archsig_analysis_packet.rs`、`src/analysis/` 全体、`src/schema/analysis_packet.rs`、
  `src/schema/archmap.rs:358-716`(`ArchMapDocumentV0` 系)+ `:9,15` の v0 import
  (`ArchMapSourceInventoryInput` / `ArchMapSourceInventoryV0`)、
  `src/schema/law_policy.rs:235-587`(v0 DSL 型)、`src/archmap.rs:938-1916`(v0 検証群)、
  `src/law_policy/measurement_policy.rs`・`fixture.rs`・`constants.rs`・`validate.rs:444-911`、
  `src/law_policy/tests.rs`(15 テスト全てが `LawPolicyDocumentV0` 依存。存置すべき検証があれば
  validate.rs 系テストとして書き直し)、`src/schema/viewer.rs`・`src/schema/run_manifest.rs` の
  v0 typed 型、`src/lib.rs` の v0 pub export、unit test 81 個 + `#[ignore]` 21 個。
- **R4 [B]** v0 fixture 10 ディレクトリの削除: `minimal/`・`negative/`・`coupon_rounding/`・
  `homotopy_report/`・`expressiveness/`・`acts_spectrum/`・`atom_generated_acceptance/`・
  `large_repo_summary/`・`inspection/`・`complete_archmap_acceptance/`。
  schema catalog の canonical fixture(`schema_version_catalog.json`)は後継を
  `ag_measurement/` 側に新設してから旧を消す。
- **R5 [B]** schema-catalog から v0 エントリ 3 件(`archmap-observation-map-v0` / `law-policy-v0` /
  `archsig-analysis-packet-v0`)を削除。catalog は現行 artifact のみを列挙する(deprecated 区分も置かない)。
- **R6 [B]** FieldSig の v0 受理削除: `tools/fieldsig/src/archmap.rs:189-196` 付近の
  `archsig-analysis-packet-v0` 受理、`signature_trajectory_report.rs:68-70` の v0 参照、
  `tools/fieldsig/docs/commands.md` 等の v0 記述の同期。
  **v1 `--analysis-packet` 受理はこの PRD では削除しない**
  (lean.yml:164-195 の v1 e2e 区間との二重依存。削除は PRD-3 で lean.yml 改稿と同一 PR)。

### P2 群 — 契約基盤の敷設(C軸)

- **R7 [C]** schema 文字列の統一: 全 artifact を `<name>/v0.5.0` 形式・トップレベルキー `schema` に統一する
  (`schemaVersion` キーと hyphen 版数 `x-vN` の全廃。viewer data も例外にしない)。
  ArchView(`tools/archview/archview.html`)の受理を新文字列**のみ**に更新する(旧版の併記受理はしない。
  旧出力 artifact は analyze 再実行で再生成する)。lean.yml e2e の schema 文字列断言も同期する。
  対象範囲は src / tests / fixtures / skills の references 内文字列 / lean.yml。
  docs 本文の全面改稿は PRD-3 の管轄(R2 で現行化した実行例を除く)。
- **R8 [C]** evaluator id の `@N` 廃止: `ag.cech-obstruction@1` → `ag.cech-obstruction`。
  registry manifest・law-policy validation・fixture・packet 出力・summary・viewer data・
  ArchView の verdictRef parse(`structuralVerdict/{evaluator}/{law}/{method_status}` の
  evaluator segment)を同期する。計算実体の版は `toolVersion` が一意に担う。
- **R9 [C]** 受理規則: 入力 artifact の schema 版数は現行リリース版数との完全一致のみ受理
  (fail-closed。エラーは現行契約名を名指す)。互換窓・`since` 範囲は実装しない。
- **R10 [C]** run manifest の単一様式化: 成功・失敗で同一 schema(`archsig-run-manifest/v0.5.0`)、
  `mode: "measurement" | "validation-failure"`、失敗時は `conclusionCode:
  "VALIDATION_FAILED_BEFORE_MEASUREMENT"`。3 様式問題を解消する(design_artifacts §3.9 の形。
  ただし `artifacts` 区画の authoring 欄など PRD-2 以降の項目は空でよい)。
- **R11 [C]** digest / 決定論基盤(design_artifacts §3.0.1 が正):
  `sha2` を archsig / fieldsig の Cargo.toml に追加。正規化は serde_json::Value 経由
  (BTreeMap キー辞書順)+ compact 再直列化 + SHA-256(生バイト digest は不採用。RFC 8785 非準拠でよい)。
  全出力 artifact の共通ヘッダに `toolVersion` + `inputDigests`(archmap / lawPolicy /
  profileFingerprint)。`siteCoverDigest` は normalized archmap の contexts / covers /
  導出 nerve のみを対象。runId は
  `run:<sha256(archmapDigest ∥ lawPolicyDigest ∥ toolVersion) 先頭 12hex>` の決定的導出
  (`--stamp` で時刻 suffix opt-in)。既知入力 → 既知 digest の canonical fixture で lock する。
- **R12 [C]** バージョン表記の同期: `Cargo.toml` を `version = "0.5.0"` に。
  `tools/archsig/README.md` / `docs/tool/guideline.md` の「v0.4.0」表記を同時更新。
- **R13 [C]** `tests/cli.rs`(17,346 行)の schema 文字列断言(150 箇所超)は機械置換スクリプトで
  R7/R8 と同一 PR 群にて更新する。置換は独立 diff として隔離し、意味論的変更と混ぜない。
- **R14 [C]** SKILL references 内のハードコード文字列の同期(全面改稿は PRD-3):
  archsig-reader の `SKILL.md` + `references/output-reading-guide.md`、
  law-policy-creater の `references/schema-guide.md` に残る `schemaVersion` キー・hyphen 版数・
  `@N` evaluator id・旧 artifact 名を新契約の文字列に置換する。
- **R15 [C]** 統合ノートの整合修正 1 行: `docs/note/archsig_v0_5_0_redesign_note.md` §9 P2 行の
  「schema catalog の `since` 受理規則」を裁定10(完全一致のみ)に同期する。

## Changed / Removed Fields

- **Removed(型・schema・fixture)**: `ArchSig*V0` 全型、`LawPolicyDocumentV0`(DSL フィールド込み)、
  `ArchMapDocumentV0` 系、v0 fixture 10 ディレクトリ、catalog の v0 エントリ 3 件、
  FieldSig の v0 受理コード、孤児 3 点。
- **Changed(契約)**: 全 schema 文字列 → `<name>/v0.5.0` + `schema` キー、evaluator id から `@N` 除去、
  run manifest 単一様式、全出力に `toolVersion` + `inputDigests`、runId 決定的導出、Cargo 0.5.0。
- **Not changed**: archmap の形状(フィールド)、measurement packet の 6 区画(形状変更は PRD-2)、
  v1 path の runtime(削除は PRD-3)、LawPolicy の形状(PRD-4)、`doctrine:aat-canonical@1`
  (単一契約版数の対象外 — 裁定7 carve-out)。

## Failure Contract

- 旧 schema 文字列(`archmap/v1` / `archmap/v2` / `law-policy/v1` / `x-vN` / `schemaVersion` キー)の
  入力は一般 validation fail。エラーは「expected `<name>/v0.5.0`」の形で現行契約名を名指す。
  専用の認識・案内・変換は行わない。
- digest 不一致・正規化不能入力は fail-closed。補完・推測はしない。

## Implementation Plan

各 PR の完了条件は `cargo test --manifest-path tools/archsig/Cargo.toml` と
`cargo test --manifest-path tools/fieldsig/Cargo.toml` と CI(lean.yml)の green、
および `git diff --check` + hidden Unicode scan。

| PR | 内容 | 対応 R |
| --- | --- | --- |
| PR-1 | 孤児 3 点削除 | R1 |
| PR-2 | CLAUDE.md / AGENTS.md / README の analyze 例差し替え | R2 |
| PR-3 | v0 dead 一式 + fixture + catalog v0 エントリ + FieldSig v0 受理削除 | R3-R6 |
| PR-4 | 命名・版数統一 + `@N` 廃止 + ArchView 受理文字列 + lean.yml 断言 + cli.rs 機械置換 + SKILL 文字列同期 | R7-R9, R13, R14 |
| PR-5 | run manifest 単一様式 + digest / 決定論基盤 + toolVersion / Cargo 0.5.0 + ノート 1 行修正 | R10-R12, R15 |

順序は PR-1 → PR-2 → PR-3 → PR-4 → PR-5。PR-4 と PR-5 は入れ替え可(独立)。

## Acceptance Criteria

1. **残存ゼロ検査(rg)**: `archsig-analysis-packet-v0` / `law-policy-v0` / `archmap-observation-map-v0` /
   `obstructionCircuitDefinitions` / `signatureAxisDefinitions` / `spectrumMeasurementProfile` /
   `part4DistanceProfile` が src / tests / fixtures / skills / lean.yml に残存しない
   (docs/archive と git history は除く)。
2. **表記統一検査(rg)**: `schemaVersion` キー、hyphen 版数(`-v0` / `-v1` / `-v2`)、
   evaluator `@1` 形式が src / tests / fixtures / skills references / lean.yml に残存しない。
3. **検証コマンド例の実測**: CLAUDE.md / AGENTS.md / README の analyze 例が exit 0 で完走し、
   出力 artifact の schema 文字列がすべて `<name>/v0.5.0` 形式である。
4. **決定論**: 同一入力での 2 回の analyze が byte 同一の出力を生む(golden lock)。
   既知入力 → 既知 digest の canonical fixture がテストで固定されている。
5. **受理の完全一致**: 旧 schema 文字列の入力が validation fail し、エラー文言が現行契約名を含む。
   互換受理の経路がコード上存在しない。
6. **テスト**: archsig / fieldsig の cargo test 全 green、lean.yml e2e green(v1 区間は本 PRD では不変)。
7. **規模の参考値**(合否条件ではなく確認値): src 削減 ≈40,000 行(孤児 ≈5,000 + v0 ≈35,000)。
8. **問いへの遡及**: 各 PR の説明に、変更が A/B/C のどの軸の境界回復かが 1 行で書かれている。

## Non-Goals

- v1 path(typed evaluator / pr-review / `--strict-distance`)の削除 — PRD-3(受け皿 = PRD-2 の gate / compare が先)。
- AG path 内の判定語残滓掃除(registry の `tripleMismatch` 等 3 件、`witness-counting@1` 廃止)— PRD-3。
- measurement packet の形状変更・gate / compare の新設 — PRD-2。
- LawPolicy / measurement-profile の形状変更(basisLedger / finiteBounds / law surface)— PRD-4。
- SKILL の全面改稿(本 PRD は参照文字列の同期のみ)— PRD-3 / PRD-5。
- 互換機構の追加(受理窓・dual-emit・removal error・バックフィル)— 裁定10 により恒久的に非目標。
- `Formal/Arch` の archive・Lean guardrail 3 本の削除 — 前者は別件、後者は PRD-3 に同梱。
