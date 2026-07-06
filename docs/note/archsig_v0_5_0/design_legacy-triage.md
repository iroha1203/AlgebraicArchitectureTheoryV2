> [!NOTE]
> 本文書は ArchSig v0.5.0 再設計の次元別詳細設計(2026-07-04、並列設計+3レンズ敵対査読の改訂版)。
> 6文書間で食い違う箇所は [統合ノート](../archsig_v0_5_0_redesign_note.md) §8 の統合裁定を正とする。

# ArchSig v0.5.0 設計ノート — 設計次元1: 古典 AAT レガシーの破棄(triage)

作成日: 2026-07-04(査読反映改訂: 同日)
担当: legacy-triage 設計
入力: reader_archsig-code.md / reader_archmap-lawpolicy.md / reader_philosophy.md / reader_measurement-notes.md / reader_skills-workflow.md / reader_saga.md(全読)+ 現物確認(src 構成、main.rs、lean.yml、docs/tool・tools/archsig/docs 一覧、Cargo.toml、registry.rs、ag_measurement.rs、第X部 §7-8)

---

## 1. 目的

ArchSig v0.4.0 に混在する古典 AAT 系レガシー(v0 analysis packet 世代、v1 typed evaluator + Part IV distance 経路、およびそれらに付随する schema / CLI / fixture / skills / docs / CI / Lean guardrail)を特定し、v0.5.0 で

1. **何を削除するか**(完全リストと削除順序)、
2. **何を AG path に移植するか**(curvature / monodromy / homotopy 系の処遇)、
3. **何を新規に据えるか**(破棄で失われる機能の AG 版代替)、
4. **破壊をどう告知するか**、
5. **削除後の単一 path 構成**、

を確定する。本ノートは調査・設計のみであり実装しない。PRD 化は別途。

**得られる結果(先に結論)**: src 66.5 千行のうち約 5.1 万行(孤児 ≈5.0k + v0 dead ≈35.0k + v1 path ≈11k)を 3 フェーズで削除し、残る src 約 1.5 万行を `archmap/v2 + law-policy(measurementProfiles) → archsig-measurement-packet/v1` の単一 AG path に純化する(tests/cli.rs 17.3 千行も v0/v1 系テストの削除で縮小。従来引用してきた「83.8 千行」は src + tests/cli.rs の合算値)。第 1 世代計測ファミリ(monodromy / ACTS / homotopy Stokes)は **AG 語彙への再実装をしない**。それらの理論的核は AG 本文と既存の `ag.*` evaluator 11 種に吸収済みであり、後継が無いのは「transport 不在時は沈黙が正しい」領域だけである。v1 専用機能で唯一実質を失うのは `pr-review` で、これは AG 版 PR review(base/after 二重計測 + verdict 遷移表)として新設する。

---

## 2. 現状の問題

### 2.1 三世代構造(docs の「2 path」記述は実態と不一致)

| 世代 | 入力 → 出力 | 実体 | 到達性 | 概算行数 |
| --- | --- | --- | --- | ---: |
| v0(dead) | `archmap-observation-map-v0 + law-policy-v0 → archsig-analysis-packet-v0` | `archsig_analysis_packet.rs`(15,416 行、`analysis/` 13,226 行を include!)、`schema/analysis_packet.rs`(2,931 行)、v0 検証群、v0 fixture 8 系統 | **CLI 不達**。lib export・unit test(archsig_analysis_packet.rs 66 個 + law_policy/tests.rs 15 個)・`#[ignore]` CLI テスト 21 個のみ | ≈35,000 |
| 孤児 | — | `src/reports/`(4,120 行)、`src/cli/atom_viewer.rs`(658 行)、`src/cli/detail_index.rs`(230 行) | **コンパイルすらされない**(mod 宣言なし) | ≈5,000 |
| v1(legacy) | `archmap/v1 + law-policy/v1 → typed evaluator → architecture-distance → summary/viewer/manifest` | `typed_evaluator.rs`(8,528 行)、`pr-review` コマンド全体、normalizer/archmap/registry の v1 部 | 現行 runtime。ただし predicate 5 語ハードコード・basis 2 種で**現実リポジトリの記述力が事実上ない** | ≈11,000 |
| AG(current) | `archmap/v2 + measurement-profile/v1 → archsig-measurement-packet/v1` | `ag_measurement.rs`(11,840 行)+ v2 検証 + measurement schema | 現行一次。**v0/v1 とコード独立**(use 文実測。v1 削除でコンパイルは壊れない) | ≈13,000 |

### 2.2 レガシー並存が引き起こしている具体的問題

1. **AG path 自身の残存ドリフト(判定混入の残滓)**: 責務憲章が「破損の現状そのもの」と名指しした判定混入(`predicate:"mismatch"` 系)は **v2/AG 側の fixture**(`archmap_v2_cech_h1_visible.json` 等)で起きた破損であり、観測純化 PRD(R1-R4)により v2 検証の hard-error(archmap.rs の `diagnostic_shortcut_token`)として回復済みである。ただし残滓が AG path 自身に残る: registry の **ag.\* evaluator manifest** に判定語 predicate 名 3 件(`coherence.legacy-coherence-token` @ registry.rs:284 / `boundary-residue.legacy-boundary-token` @ :318 / `section-factorization.legacy-section-token` @ :388)、判定語 atom を消費する最後のコードである `legacy-counting-invariant` invariant(§3.2 の残存ドリフト掃除)、README の観測純化 PRD「提案中」記述。これらは v0/v1 の問題ではなく、AG path 内部の掃除対象である。
2. **v0/v1 の層越境(削除の境界的意義)**: v0/v1 の削除が回復する境界は mismatch 語彙とは別軸にある。v0 LawPolicy DSL(`obstructionCircuitDefinitions` / `signatureAxisDefinitions` / `spectrumMeasurementProfile` 等の手書き)は、責務憲章「LawPolicy が書かないもの」(計算手続き・測定実装)への**実際の層越境**である。v1 `pr-review` の authored `archmap-delta-v0` は、差分計算という計算層の責務を観測者(ArchMap author)へ**転嫁**する構図である。なお v1 の archmap predicate 5 語(`placesOrder` / `checksInventoryWith` / `dependsOn` / `implements` / `calls`、archmap.rs:869-874)は中立であり、v0/v1 schema に mismatch 語彙は存在しない。
3. **SKILL 間の版数ねじれ**: archmap-creater は v2 一次なのに archsig-reader / archsig-pr-reviewer は v1 前提。**v2 で閉じる creater → reader → pr-review ループが存在しない**。これは「ArchMap 検出精度を SKILL で上げる」方針の前提を欠く。
4. **CI・テスト・docs の保守コストが v1/v0 に傾斜**: CI e2e 前半(lean.yml:49-201 の v1 区間)、tests/cli.rs の v1 系 40+ 箇所と v0 `#[ignore]` 21 個、golden_corpus.md の過半、tools/archsig/docs/commands.md:3-6 の「The current route is: archmap/v1」記述。さらに CLAUDE.md / AGENTS.md の検証コマンド例(analyze)が v0 fixture(`tests/fixtures/minimal/`)を参照しており、**現時点で既に「--input must have schemaVersion archmap/v1」で fail する**(実行確認済み)。
5. **artifact 表記の三様化**: run manifest が v1 成功=`schemaVersion: archsig-run-manifest-v1`、v2 成功=`schemaVersion: archsig-run-manifest-v2`、失敗時=`schema: archsig-run-manifest/v1` と 3 様式。`x/v1` と `x-v1` の混在も全域。
6. **`--strict-distance` の二義性**: v1 では distance readings 検査、v2 では非終端 verdict 検査という別物が同じフラグ名に同居(main.rs:905, 917, 1005-1036 実測)。
7. **Cargo.toml が `version = "0.1.0"` のまま**(README は v0.4.0 と自称)。

---

## 3. 設計案

### 3.1 triage の判定規律

各資産を次の 3 問で判定する。判定規律を先に固定するのは、削除リストを恣意でなく検査可能にするため。

- **Q1(経路)**: `archmap/v2 + measurement-profile/v1 → archsig-measurement-packet/v1` の計算に寄与するか。
- **Q2(理論 anchor)**: AG 本文(第III/IV/V/VI/VIII/X部)に定義・定理番号で anchor できるか。古典語彙(law universe / signature axes / zero-reflecting distance / witness completeness 型同値定理)しか anchor がないものは「AG 準拠でない」。
- **Q3(境界)**: 責務憲章の三層分離(観測は "X is the case" のみ / 判定は ArchSig 独占 / doctrine 固定)に適合するか。

判定結果は三値:

- **DELETE**: Q1 = no。AG path に寄与しない(v0 世代・孤児・v1 専用)。
- **KEEP**: Q1 = yes かつ Q3 = yes(AG path 本体、共有 infrastructure)。
- **REPLACE**: Q1 = no だが提供していた**機能**に現場価値があり、AG 語彙で新設すべきもの(pr-review が唯一の該当。§3.4)。

「AG 語彙へ移植」という第四の選択肢は、第 1 世代計測ファミリについて**採らない**(§3.3 で理由を示す)。

### 3.2 削除対象の完全リストと削除順序

削除は 3 フェーズ。各フェーズ末で `cargo test --manifest-path tools/archsig/Cargo.toml` と CI が green であることをフェーズ完了条件とする。

#### Phase A — 孤児削除(runtime 影響ゼロ、1 PR)

| 対象 | 行数 | 根拠 |
| --- | ---: | --- |
| `tools/archsig/src/reports/`(mod.rs, pr_review.rs, summary.rs, codebase_inspection.rs, detail_index.rs) | 4,120 | どの mod 宣言からも不参照。コンパイル外 |
| `tools/archsig/src/cli/atom_viewer.rs` | 658 | 同上 |
| `tools/archsig/src/cli/detail_index.rs` | 230 | 同上 |

#### Phase B — v0 dead 一式(FieldSig 同期込み、archsig 1 PR + fieldsig 1 PR)

**コード**:

| 対象 | 内容 |
| --- | --- |
| `src/archsig_analysis_packet.rs` + `src/analysis/`(distance 8 ファイル、validation 2 ファイル) | v0 packet builder 実体 ≈28,600 行 |
| `src/schema/analysis_packet.rs` | `ArchSig*V0` 型 ≈130 個、2,931 行 |
| `src/schema/archmap.rs:358-716` | `ArchMapDocumentV0` 系型 |
| `src/schema/law_policy.rs:235-587` | `LawPolicyDocumentV0` 系型(spectrumMeasurementProfile / homotopyMeasurementProfile / part4DistanceProfile / obstructionCircuitDefinitions / signatureAxisDefinitions 等の全部入り DSL) |
| `src/archmap.rs:938-1916` | v0 検証群 |
| `src/archmap.rs:9,15` 冒頭部 | `ArchMapSourceInventoryInput` 型と `ArchMapSourceInventoryV0` import(v0 検証群の列挙範囲 :938-1916 の**外**にある v0 依存) |
| `src/law_policy/measurement_policy.rs`(815 行)、`fixture.rs`(668 行)、`constants.rs`(32 行)、`validate.rs:444-911` | v0 専用(measurement_policy.rs は名前に反し AG 用ではない) |
| `src/law_policy/tests.rs` | 15 テスト全てが `static_law_policy()`(→ `LawPolicyDocumentV0`、fixture.rs)に依存。fixture.rs 削除と同時に削除する(v1 対象で存置すべき検証があるかは削除時に仕分けし、必要なら validate.rs 系テストとして書き直す) |
| `src/schema/viewer.rs`、`src/schema/run_manifest.rs` | v0 typed 型(現行は json! 構築で未使用) |
| `src/lib.rs` の v0 pub export(`build_archsig_analysis_packet` 等) | export 削除 |
| src 内 unit test 81 個(archsig_analysis_packet.rs 66 + law_policy/tests.rs 15)+ `tests/cli.rs` の `#[ignore = "legacy v0 ..."]` 21 個 | テスト削除 |

**fixture**(ディレクトリごと削除):

`minimal/`(v0 + canonical schema catalog fixture。catalog fixture は後継を ag_measurement/ 側に新設。**CLAUDE.md / AGENTS.md の検証コマンド例が参照しているため、例の差し替え(下記 docs 表)を同 PR か先行 PR で行う**)、`negative/`、`coupon_rounding/`、`homotopy_report/`、`expressiveness/`、`acts_spectrum/`、`atom_generated_acceptance/`、`large_repo_summary/`、`inspection/`、`complete_archmap_acceptance/`(v0 snapshot 系。sanitized large-repo fixture としての価値は認めるが v0 語彙のまま保持する理由がない。大規模 v2 fixture の不在は ArchMap SKILL 検証 corpus 側の新設課題として設計次元「ArchMap SKILL」へ引き継ぐ)。

**schema-catalog**: legacy 役割の v0 エントリ 3 件(archmap-observation-map-v0 / law-policy-v0 / archsig-analysis-packet-v0)を削除し、canonical fixture(`schema_version_catalog.json`)を新カタログで置換。

**FieldSig 同期**(同一マイルストーン内の別 PR):

- `tools/fieldsig/src/archmap.rs:189-196` 付近の `archsig-analysis-packet-v0` 受理を削除する。**v1 `--analysis-packet` 受理はこの段では削除しない**。lean.yml:164-195 の v1 e2e handoff(archsig v1 raw artifacts → `archsig-analysis-sft-input --analysis-packet` + `schema-compatibility` ステップ)が現に green で走っており、その削除は Phase C(v1 raw packet 発行の削除・lean.yml v1 区間削除)の所管であるため、v1 受理の削除も同じ Phase C の PR(PR-C2)まで遅らせる。これで「各フェーズ末で CI green」条件と矛盾しない。
- `signature_trajectory_report.rs:68-70` の v0 参照を削除。
- `tools/fieldsig/docs/commands.md` 等の「Legacy `archsig-analysis-packet/v1` and `archsig-analysis-packet-v0` remain accepted」記述を各削除段に同期(v0 分は本 PR、v1 分は PR-C2)。
- 同時に、FieldSig が `dependsOnAssumptions`(R2 行レベル assumption 依存)を読まず保守 fail-fast のまま(fieldsig/src/archmap.rs:1086-1089)という既知残件を、artifact 再設計次元の入力として記録(本 triage では削除のみ行い挙動変更しない)。

#### Phase C — v1 path 一式(受け皿新設と同一マイルストーン、複数 PR)

**コード**:

| 対象 | 内容 |
| --- | --- |
| `src/typed_evaluator.rs` 全体 | 8,528 行。evaluate_typed_v1 / architecture-distance / summary-v1 / viewer-v1 / raw packet v1 / detail index / llm-interpretation-packet |
| `src/main.rs` | pr-review コマンド定義(:82-107)+ 実装(:565-710)+ helper(:173-518)、analyze v1 分岐(:915-1040)、`--emit-raw-artifacts` フラグ(v1 概念)、`ARCHMAP_V1_SCHEMA` preflight 分岐(→ §3.5 の removal error に置換) |
| `src/cli/analyze.rs` | v1 run manifest 構築 |
| `src/normalizer.rs` v1 部 | `normalize_archmap_v1`、`molecule_memberships`、`ArchMapAtomConstructorV1` |
| `src/archmap.rs:581-937` | v1 検証(predicate 5 語ハードコード含む) |
| `src/schema/archmap.rs` | `ArchMapDocumentV1` / `ArchMapAtomV1` / `ArchMapMoleculeV1` / `NormalizedArchMapV1` / `ArchMapValidationReportV1`。**`ArchMapSourceV1` は v2 が共用するため残置し、Rust 内部名を `ArchMapSource` にリネーム**(schema 文字列には影響しない) |
| `src/schema/law_policy.rs:172-231` | TypedEvaluatorResults / ReplacementRegistry 系型 |
| `src/law_policy/registry.rs` | **分離が必要**。solid 5 種 + `domain.no-direct-infra-dependency@1` の manifest、replacement_manifests(v0 削除フィールド 6 種の置換機構)、distance profile 2 種(`distance-profile:architecture-default@1` / `distance-profile:practical-rust-service@1`)を削除。`ag.*` 11 evaluator の manifest(語彙検証用)は `law_policy/registry/ag.rs` へ分離して存置。`is_known_v1_evaluator` → `is_known_evaluator` に改名 |
| `src/law_policy/validate.rs` | distance profile checker(:228)、replacement registry check(:388)を削除 |
| LawPolicy schema | `distanceProfileRef` フィールド削除、pack `solid@1` と basis registry(`policy-basis:solid` / `policy-basis:layering`)の登録抹消。**schema をどう版上げするか(law-policy/v2 化を含む)は LawPolicy 再設計次元の所管**。本 triage は「消えるフィールドと登録」だけを確定する |
| `--strict-distance` | `--strict` に改名し v2 意味(非終端 verdict 行 / not_computed invariant / violated assumption で exit 1)のみに単純化 |
| `Cargo.toml` | `version = "0.5.0"` に更新 |

**fixture**: `archmap_v1/`、`pr_review/`(archmap-delta-v0 含む)、`sharded/`(v1 前提構想の fixture。bundle/export 未実装)をディレクトリごと削除。`examples/practical-rust-service/` は v2 化済みのため存置(replacement registry からの古い参照はレジストリ削除で自然消滅)。

**tests**: `tests/cli.rs` の archmap_v1_root / pr_review_root 使用テスト(≈40 箇所)+ strict-distance v1 テスト群を削除。残る AG 系テスト(90 個超)を機に `tests/cli.rs`(17,346 行)を `tests/cli_analyze.rs` / `tests/cli_prreview.rs` / `tests/cli_validation.rs` 程度に分割することを推奨(必須ではない)。

**CI**: `.github/workflows/lean.yml:49-201` の v1 e2e 区間(v1 analyze、raw artifacts、FieldSig legacy handoff(:164-180)、schema-compatibility(:182-192))を削除。**FieldSig 側の v1 `--analysis-packet` 受理削除はこの lean.yml 改稿と同一 PR(PR-C2)で行う**(Phase B で先に消すと C 完了まで CI が恒常 fail するため。§5.2 リスク表)。後半の v2 measurement handoff 区間を唯一の e2e とし、新 pr-review v2 の e2e を追加。

**skills**:

- `archsig-pr-reviewer`: v1 専用のため全面書き換え(新 pr-review v2 に対応。§3.4)。references の `retired source diff reference.md`(delta-v0 authoring 手順)は廃止。
- `archsig-reader`: 「Turn a supplied archmap/v1 …」の v1 前提を v2 native に全面改稿。読解対象を measurement packet / summary v2 / insight report に差し替え。references/default_law_policy.json を `solid@1` pack から ag.* baseline profile に差し替え。
- `archmap-creater`: v1 フォールバック条項(「明示要求時のみ v1」)を削除。
- `law-policy-creater`: distanceProfileRef / solid pack の記述を削除。

**docs**(実配置は `docs/tool/` と `tools/archsig/docs/` の二箇所に分かれている。表の場所指定は現物確認済み):

| 文書 | 場所 | 処遇 |
| --- | --- | --- |
| `commands.md`(:3-6 に「The current route is: archmap/v1」)/ `artifacts-and-boundaries.md` | `tools/archsig/docs/` | v2 単一 path 前提で改稿(v1 現行記述・legacy 歴史節を削除) |
| `sharded-archmap.md` | `tools/archsig/docs/` | `docs/archive/` へ移動 |
| `README.md` / `golden_corpus.md` / `llm_native_e2e_workflow.md` / `atom_handoff.md` / `law_policy.md` | `docs/tool/` | v2 単一 path 前提で改稿(v1 節・legacy v0 歴史節・distanceProfileRef 記述を削除)。README の観測純化 PRD「提案中」記述を実装完了に更新。FieldSig 段落の「packet does not encode row-level assumption dependencies」という実装より古い記述を是正 |
| `archsig_analysis_packet.md` / `archsig_v1_migration_note.md` / `archmap_v1_output_replacement_gap_ledger.md` / 第 1 世代 PRD+validation 6 本(monodromy / curvature spectrum / homotopy stokes) | `docs/tool/` | `docs/archive/` へ移動。gap ledger の partial 項目(unknown/unmeasured first-class 生成、PR review structural diagnosis 等)は v1 面の補修であり**追わない** |
| `archsig_v0_4_0_*` PRD 3 本 / `archmap_observation_purity_prd.md` / `archmap_minimal_observation_contract_prd.md` / 責務憲章 | `docs/tool/` | 存置(現行経路の由来記録) |
| `archmap_store.md` | `docs/tool/` | 存置するが「schema は v0 語彙のまま、v2 contexts/covers の delta 型未定義」の注記を追加し、artifact 再設計次元へ引き継ぐ |
| CLAUDE.md / AGENTS.md の検証コマンド例 | リポジトリルート | analyze 例が `tests/fixtures/minimal/`(v0)参照で**既に fail する**。`ag_measurement/archmap_v2.json + law_policy_ag.json`(v2、analyze 成功を実行確認済み)へ差し替え。fixture 削除(PR-B1)と同時か先行 |
| `tools/fieldsig/docs/commands.md` 等 | `tools/fieldsig/docs/` | legacy `--analysis-packet` 受理記述を各削除段に同期(v0 分は PR-B2、v1 分は PR-C2) |
| `tools/archsig/README.md` | `tools/archsig/` | 移行表 + v0.5.0 表記(§3.5) |

**残存ドリフト掃除**(Phase C に同梱): AG path 内部に残る判定語の残滓 2 系統を消す。これは v0/v1 削除とは独立の、観測純化 PRD の仕上げである。

1. registry の ag.* manifest の判定語 predicate 3 件(registry.rs:284 / :318 / :388)を中立語彙(実装の実入力語彙 `sectionValue` / `support` / `cooccurrence`)に同期。
2. **`legacy-counting-invariant` invariant の measurement packet からの廃止**。これは残置 helper 1 個の削除ではなく packet 可視の契約変更である: `witness_violation_support_refs`(ag_measurement.rs:10454-10461)は :6094-6095 で呼ばれ、emission ブロック :6252-6262 で五値 verdict(measured_zero/measured_nonzero)・`violationCount`・`supportAtomRefs` を駆動する生きたコードであり、tests/cli.rs:1143 が `violationCount: 0` をロックしている。R3 hard-error(archmap.rs の predicate "violation" 系 validation fail)により有効入力では常に count=0 → 恒常 measured_zero の vacuous verdict であり、判定語 atom を消費する最後の残滓である。**代替ソースは用意せず invariant を丸ごと廃止する**(vacuous な verdict を無理に生かす理由がない)。削除範囲は helper・呼び出し・emission ブロック・関連 fixture / golden / test lock の更新を含み、該当 fixture 更新を PR-C3 の green 条件に含める。

**docs/note(ユーザー確認事項)**: 第 1 世代理論ノート 4 本(`path_monodromy_obstruction_theorem.md` / `boundary_holonomy_conjecture.md` / `curvature_transfer_spectrum_theorem.md` / `homotopy_holonomy_stokes.md`)は docs/archive への移動を提案する。理論的核は AG 本文(第IV/VI/VIII部)に吸収済みで、現行 source of truth ではない。ただし docs/note はユーザーの成果物であり、移動はユーザー判断(§6)。

**Lean guardrail 3 本(ユーザー確認事項)**: `Formal/Arch/Signature/{MonodromyMeasurement,CurvatureTransferSpectrum,HomotopyHolonomyStokes}.lean` は v1 reading families の claim boundary を支える目的で作られたもので、Phase C 後は守る対象が消滅する。推奨は「Formal.lean から import を外しファイル削除、`lean_theorem_index_classical_aat.md` の該当節を archive」だが、Lean 塔の変更は tooling contract と独立の可視 surface なので単独の確認事項とする(§6)。Rust 側の削除は Lean 側の決定を**待たない**(Rust/Lean 対応は要求されない)。

#### 削除順序の根拠

- A → B → C の順は「リスク昇順」: A はコンパイル外、B は CLI 不達(FieldSig 同期は v0 受理分のみ。v1 受理は C へ)、C は現行 runtime の変更で skills/docs/CI の同時改稿が必要。
- Phase C 内の順序: **C-1** 新 pr-review v2 の骨格実装(受け皿。§3.4)→ **C-2** v1 analyze 分岐 + typed_evaluator + registry 分離の削除 + lean.yml v1 区間削除 + FieldSig v1 受理削除 → **C-3** skills / docs 改稿 + ドリフト掃除 → **C-4** LawPolicy schema 整理(LawPolicy 再設計次元と結合)。C-1 を先行させるのは、PR review 機能の空白期間を作らないためだが、v1 pr-review の実用価値は predicate 5 語の制約でほぼ理論値であるため、C-1 と C-2 の順序交換(削除先行)も許容する。**推奨は C-1 先行**(CI 連携を見据える v0.5.0 の主目的物を先に立てる)。

### 3.3 生き残る計測の triage — curvature / monodromy / homotopy 系は「移植しない」

第 1 世代 3 ファミリの定理はいずれも 5〜6 個の強仮定(witness completeness / axis exactness / zero-reflecting)つきの古典 AAT 型同値命題で、AG 経路の「有限 site 上で無仮定に F2 計算し、assumption ledger で条件を明示する」様式と証明様式が異なる。AG 本文がすでに各概念を吸収しており、**AG 経路に後継が存在するか、後継が無いのは沈黙が正しい領域**である。よって AG 語彙への再実装は行わない。

| 第 1 世代ファミリ | 理論的核 | AG 側の現状 | v0.5.0 処遇 |
| --- | --- | --- | --- |
| path monodromy / AMI | 経路の交換不能性(局所零曲率でも大域 obstruction) | 第VI部 定義10.4/10.6 が吸収。AG 経路では transport data 不在時は**沈黙が正しい**(忠実性マップ分類) | DELETE。transport data が artifact 化された将来の新 evaluator 候補として在庫記録のみ |
| boundary holonomy 予想 | obstruction の境界局在 | `ag.boundary-residue@1`(Mayer-Vietoris δ、F2 rank)実装済み | DELETE(後継実在。何も失われない) |
| ACTS spectrum | 曲率の循環モード検出 | `ag.sheaf-laplacian@1`(proxy 明示)+ analytic overlay(M14)実装済み。Flat_U 同値定理型主張は AG 様式と衝突するため**持ち込まない** | DELETE。スペクトル系は analytic reading として存続済み |
| homotopy Stokes | Stokes 監査、穴と曲率の分離 | `ag.period-stokes@1` / `ag.period-stokes-audit@1` 実装済み。「architectural hole」reading は nerve の b₁(第IV部 系12.3、`ag.cech-obstruction@1` が計算)に大部分包摂 | DELETE。hole reading の残余価値(filler evidence の不在の名指し)は「選ばれた cover / witness family における evidence 不在」= 既存の `unmeasured_support` boundary statement で表現可能 |
| Part IV distance ファミリ(architecture-distance/v1) | 距離的読み | 第VIII部 定義3.3 が analytic reading として位置づけ済み(distance は lawfulness ではない)。AG packet の `analyticReadings[]` が受け皿 | DELETE。distance profile 概念(コンパイル内蔵 2 種)ごと廃止 |

**AG 拡張の新規在庫**(本 triage の対象外だが、削除と混同しないため明記): SAGA(第X部)対応 evaluator、Margin / Dehn function / persistence barcode(忠実性ノートの意図的見送り在庫)、LawConflict Tor の拡張は「AG 分析の充実」次元の設計対象であり、レガシー移植ではなく新設である。既存構造(evaluator + profile 検証 + assumption 定理参照の 3 点セット)が受け皿になる。

### 3.4 破棄で失われる機能と v0.5.0 の代替

#### (1) pr-review → AG 版 PR review(唯一の REPLACE)

v1 `pr-review` は base/after/path の v1 スナップショット + 手作業 authoring の `archmap-delta-v0` を入力に距離移動を報告していた。AG 版は次の形に置き換える(schema の最終形は artifact 再設計次元の所管。ここでは triage として最小契約を固定する):

```bash
archsig pr-review \
  --base-archmap base_archmap.json \      # archmap/v2
  --after-archmap after_archmap.json \    # archmap/v2
  --law-policy law_policy.json \          # 同一 LawPolicy を両測定に適用
  --out-dir .tmp/archsig-pr-review
```

- **delta の authored artifact を廃止する**。v1 で authored delta が必要だったのは PR ごとの全量再 authoring が高価だったからだが、archmap-creater SKILL が base/after 両 ArchMap を保守する運用では、**二つの supplied artifact の差分計算は観測ではなく計算**であり、責務憲章上 ArchSig(計算層)が担当できる。ArchSig が `archmap-diff/v1`(atoms/contexts/covers/sources の added/removed/modified、決定的 JSON 比較)を出力する。
- 出力は 3 点: base 側 measurement packet、after 側 measurement packet、`archsig-pr-review-report/v2`。report の中心は **verdict 遷移表**:

```json
{
  "schema": "archsig-pr-review-report/v2",
  "basePacketRef": "base/archsig-measurement-packet.json",
  "afterPacketRef": "after/archsig-measurement-packet.json",
  "archmapDiffRef": "archmap-diff.json",
  "verdictTransitions": [
    { "evaluator": "ag.cech-obstruction@1", "law": "...",
      "baseVerdict": "measured_zero", "afterVerdict": "measured_nonzero" }
  ],
  "conclusion": "NO_VERDICT_REGRESSION_UNDER_PROFILE",
  "boundaryStatements": [
    { "kind": "silence_by_design",
      "reason": "cross_run_class_identification_requires_comparison_data",
      "text": "base/after の非零 class を同一障害として同定するには第X部 定義7.1 の H^1 comparison data の supply が必要であり(無条件比較の不成立は定理8.4/8.5)、本 report は供給されていないため二測定の並記に留まる。" },
    { "kind": "cover_changed_between_runs",
      "text": "この profile 行の selected cover は base と after で異なる(archmap-diff 参照)。verdict 遷移は architectural change ではなく測定面の変更に由来しうる。" }
  ]
}
```

- **verdict の相対化**: verdictTransitions は profile だけでなく**各側の supplied ArchMap(cover/atoms)にも相対的**である(第VIII部の verdict 規律: verdict は selected finite data 全体に相対)。base/after では ArchMap が異なるため、遷移は architectural change だけでなく cover の再 authoring(chart 分割の変更等)だけでも発生しうる。そこで最小契約として: `archmap-diff/v1` が計算する covers の added/removed/modified を用い、**selected cover が base/after で異なる profile 行の verdictTransition には `kind: cover_changed_between_runs` の boundary statement を付し、その行は `--strict` の exit 1 判定から除外する**(測定面の変更を architecture 劣化に丸めない)。report にも「archmap-diff が cover/context の変更を示す場合、遷移は測定面の変更に由来しうる」旨の相対化注記を含める。conclusion 名(`NO_VERDICT_REGRESSION_UNDER_PROFILE` 型の肯定形)は変えないが、その読みが profile + 両側 supplied ArchMap に相対であることをこの注記が固定する。boundary statement の schema 最終形は artifact 再設計次元の所管であり、本 triage は**この条件の存在だけ**を契約として固定する。
- **理論境界**: 五値 verdict の遷移表は「同一 profile 下の二測定の並記」として安全である(cover が変化した行は上記の通り並記でしかない)。一方「base の非零 class と after の非零 class が同じ障害か」という class 水準の追跡は、**第X部 定義7.1 の H^1 comparison data が supplied されない限り語れない**。無条件比較の不成立は定理8.4(full sheaf comparison is data)/ 定理8.5(refinement naturality is data)が外周境界として確定している(「比較可能性はデータである。これが SAGA 比較定理の外周である」)。命題4.10 の refinement pullback が使えるのは after の cover が base の cover の refinement という特殊ケースのみで、一般の base/after ArchMap は互いの refinement ではない。したがって将来の comparison data artifact は refinement 形ではなく**定義7.1 の形**(次数 0/1/2 の両方向写像 + 差保存 + 微分可換、結論を格納しない)を目標形とし、supplied 時の比較は定理7.2(comparison is a theorem under supplied data)が保証する。導入は artifact 再設計次元へ引き継ぐ(§6-4)。
- CI 連携の exit code 規律: `--strict` 時、**cover 不変の行**における `measured_zero → measured_nonzero` の遷移で exit 1。cover が変化した行、および `unmeasured` / `unknown` / `not_computed` への遷移は fail に丸めない(verdict boundary の CI 版)。

#### (2) `--strict-distance` → `--strict`

v2 意味のみ(非終端 verdict 行 / not_computed invariant / violated assumption で exit 1)。distance という古典語彙をフラグ名から除去する。

#### (3) summary/v1 の verdict 語彙 → summary/v2(既存)

`SELECTED_VIOLATION_MEASURED_UNDER_EVIDENCE_CONTRACT` 等の v1 語彙は、summary/v2 の conclusion-first 語彙(`MEASURED_H1_OBSTRUCTION_UNDER_PROFILE` / `NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE` / `AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE` 等)が既に代替している。追加実装は不要。

#### (4) skills ループの v2 完結

archsig-reader(v2 native 化)+ 新 archsig-pr-reviewer(pr-review v2 対応)により、creater → reader → pr-reviewer が v2 で初めて閉じる。SKILL 本文の書式は既存慣行(description のトリガー列挙 / release-bundle 自立性 / binary 解決順序 / 停止条件明文列挙 / Recommended phrasing/Avoid / 肯定的結論先頭)を踏襲する。

#### (5) FieldSig handoff の単線化

v1 raw packet 経由(`--emit-raw-artifacts` + `--analysis-packet`)を廃し、`fieldsig archsig-analysis-sft-input --measurement-packet` の既実装ルートに一本化。完結は PR-C2(lean.yml v1 区間削除・FieldSig v1 受理削除と同一 PR)。

#### (6) 代替を用意しないもの(明示)

replacement registry(v0 → v1 移行案内機構)、`archmap-delta-v0`、molecules、signature axes、obstruction circuits、`dataState` kind 名、distance profile 2 種、v1 viewer data、legacy-counting-invariant invariant(§3.2 残存ドリフト掃除: 有効入力では恒常 vacuous)。これらは AG path に対応概念が無いか(molecules → contexts/covers が既に置換)、移行案内としての役目を終えている。

### 3.5 互換性の扱いと破壊の告知

方針: **根拠のない互換性維持はしない**(AGENTS.md)。v0/v1 の受理・変換レイヤは一切残さない。告知は次の 4 点に限定し、削除物の長大な列挙を docs の主役にしない。

1. **狙い撃ち removal error(v0.5.x の間のみ)**: preflight は v1 schema 文字列の認識だけを残し、受理はしない。

   ```text
   $ archsig analyze --archmap old_v1.json --law-policy lp.json --out-dir out
   error: schema "archmap/v1" was removed in ArchSig v0.5.0.
     Author an archmap/v2 with the archmap-creater skill.
     The v0.4.0 surface is archived at git tag v0.4.0.
   ```

   一般 parse error に落とさず後継を名指しして停止する(補完も変換もしない)。これは互換性維持ではなく停止条件の手続き化であり、v0.6.0 で除去してよい。

2. **移行表 1 枚**(tools/archsig/README.md の v0.5.0 節): 「削除された surface → 現行の対応物」だけを載せる。

   | 削除 | 現行の対応物 |
   | --- | --- |
   | archmap/v1(molecules) | archmap/v2(contexts/covers)+ archmap-creater SKILL |
   | law-policy/v1 の distanceProfileRef / solid pack | measurementProfiles + ag.* evaluator 選択 |
   | archsig-analysis-packet/v1(raw) | archsig-measurement-packet/v1 |
   | architecture-distance/v1 | packet の analyticReadings[] |
   | pr-review(v1 + delta-v0) | pr-review(v2 base/after 二重計測) |
   | --strict-distance | --strict |
   | FieldSig --analysis-packet | FieldSig --measurement-packet |

3. **schema-catalog は現行 artifact のみ**: legacy 役割エントリを持たない。過去 schema の正本は git tag `v0.4.0`(archive は Git history、というリポジトリ既定の扱いに従う)。

4. **バージョンの明示**: Cargo.toml を 0.5.0 に。docs/tool/guideline.md・README の「v0.4.0」表記を同時更新(同期義務)。

### 3.6 v0.5.0 の単一 path 構成図

```text
[観測層: ArchMap author + evidence contract]        [制度選択層]
  archmap/v2                                          law-policy(measurementProfiles[],
  (sources / atoms(subject,axis) /                     policies[ag.*], measurementProfileRef)
   contexts 有限poset / covers)                              |
        |                                                    |
        +-------------------+--------------------------------+
                            v
                  [計算層: archsig analyze]
                            |
        +-------------------+--------------------------------------------+
        | archmap-validation-report/v2   law-policy-validation-report    |
        | normalized-archmap/v2                                          |
        | archsig-measurement-packet/v1                                  |
        |   profile / structuralVerdict(五値) / computedInvariants /     |
        |   analyticReadings / assumptions / boundaryStatements(6種) /   |
        |   nonConclusions                                               |
        | archsig-analysis-summary/v2(conclusion-first)                  |
        | archsig-insight-report/v1 + archsig-insight-brief.md           |
        | archsig-atom-viewer-data/v2(gluingGeometry)  --> ArchView      |
        | archsig-run-manifest/v2(表記統一は artifact 再設計次元)         |
        +----------------------------------------------------------------+
                            |
        [archsig pr-review] base/after 二重計測 + archmap-diff/v1
                            + archsig-pr-review-report/v2  --> CI exit code
                            |
        [fieldsig archsig-analysis-sft-input --measurement-packet]  --> SFT
```

**モジュール構成(削除後の再配置)**: v1/v0 削除で `ag_measurement.rs`(11,840 行)の単一ファイル肥大が残る最後の構造問題になる。Phase C 完了後の follow-up として次の分割を推奨する(AG 充実次元の新 evaluator 追加の前提整備。dispatch の if-else チェーンも evaluator trait + 登録テーブルに置換):

```text
src/
  main.rs            # dispatch: analyze / pr-review / archmap / law-policy / schema-catalog
  archmap.rs         # v2 検証のみ
  normalizer.rs      # v2 正規化のみ
  law_policy/
    registry/ag.rs   # ag.* manifest(語彙検証)
    validate.rs      # v1(現行)検証のみ
  measurement/
    profile.rs       # MeasurementProfile 検証
    evaluators/      # ag.* 各 evaluator(1 ファイル 1 evaluator)
    packet.rs        # packet 構築+検証
    summary.rs / insight.rs / viewer.rs
  prreview.rs        # pr-review v2
  schema/            # v2 + measurement 型のみ
```

---

## 4. 境界規律との整合

- **削除は境界回復として書ける — ただし正確な系譜で**: 責務憲章 121-139 が名指しした判定混入(mismatch predicate 系 fixture)は **v2/AG 側の破損**であり、観測純化 PRD R1-R4 が既に回復済み。本設計の残存ドリフト掃除(ag.* manifest の判定語 3 件 + legacy-counting-invariant invariant)は**その残滓の除去**である。一方 v0/v1 削除の境界的意義は別軸にある: v0 LawPolicy DSL(obstructionCircuitDefinitions 等)は憲章「LawPolicy が書かないもの」への層越境の除去、v1 pr-review の authored `archmap-delta-v0` は観測者への計算責務転嫁の除去。v0.5.0 の PRD 化の際は「問い」を**この二軸に分けて**接続する。v0/v1 削除に「憲章が名指しした mismatch 破損の回復」という earned でない claim を負わせない。
- **観測境界の一括払い**: 削除後の ArchSig は入力補完・推測・fallback を一切持たない(removal error は補完ではなく停止)。ArchMap の抽出精度改善は SKILL(観測層)の仕事として別次元に配置され、ArchSig 側に観測ヘッジを持ち込まない。
- **肯定的結論中心**: 破壊の告知は移行表 1 枚 + removal error に限定し、「削除されたものの長い一覧」を README や catalog の主役にしない。pr-review v2 の conclusion も `NO_VERDICT_REGRESSION_UNDER_PROFILE` 型の肯定形を先頭に置く(その読みは profile + 両側 supplied ArchMap に相対。§3.4)。
- **verdict boundary の CI 版**: pr-review v2 / `--strict` の exit code 写像で `unmeasured` / `unknown` / `not_computed` を fail に丸めず、cover が変化した行の遷移も architecture 劣化に丸めない(丸め込み禁止の保存)。
- **無制限 claim の不導入**: cross-run の class 追跡は第X部 定義7.1 の comparison data supplied 時のみ(無条件比較の不成立は定理8.4/8.5 の外周境界)。「レガシー削除により何かの完全性が保証される」とは書かない。extraction completeness は本 triage のどの完了条件にも現れない。
- **Rust/Lean 対応の非要求**: Lean guardrail 3 本の処遇は Rust 側削除と独立に決める。Rust の削除完了条件に Lean 変更を含めない。
- **theory 由来 / tool 選択の区別**: 「第 1 世代を移植しない」は AG 本文の吸収状況(theory 由来の事実)+ 証明様式の不一致(tool 設計上の選択)の複合判断であり、PRD 化の際は憲章 52-56 と同じ精度で両者を分けて書く。

---

## 5. 移行とリスク

### 5.1 PR 分割案

| # | 内容 | 依存 | green 条件 |
| --- | --- | --- | --- |
| PR-A | 孤児 3 点削除 | なし | cargo test 変化なし |
| PR-B1 | v0 dead コード + fixture + schema-catalog legacy + テスト削除 + CLAUDE.md / AGENTS.md analyze 例の v2 差し替え | PR-A | cargo test(残テスト全 green)、schema-catalog fixture 更新 |
| PR-B2 | FieldSig の `archsig-analysis-packet-v0` 受理削除(**v1 `--analysis-packet` 受理は存置**)+ fieldsig docs の v0 記述同期 | PR-B1 | fieldsig cargo test、lean.yml の legacy handoff 区間(v1 packet)が green のまま |
| PR-C1 | pr-review v2 骨格(archmap-diff/v1 + 二重計測 + report/v2 + cover_changed_between_runs 規約)+ e2e | PR-B1 | 新 fixture での pr-review e2e |
| PR-C2 | v1 path 削除(typed_evaluator / analyze v1 分岐 / registry 分離 / --strict 改名 / Cargo 0.5.0 / removal error)+ **lean.yml v1 e2e 区間(:49-201)削除 + FieldSig v1 `--analysis-packet` 受理削除**(同一 PR) | PR-C1 | cargo test(archsig + fieldsig)、CI v2-only e2e |
| PR-C3 | skills 2 本改稿 + docs 改稿 + archive 移動 + ドリフト掃除(ag.* manifest 3 件 + legacy-counting-invariant 廃止) | PR-C2 | docs 参照整合(拡大 rg 検査。§5.2)、legacy-counting-invariant 廃止に伴う golden / fixture 更新込みで cargo test green、hidden Unicode scan |
| PR-C4 | LawPolicy schema 整理 | LawPolicy 再設計次元の PRD | 同 PRD の受け入れ条件 |

### 5.2 リスク表

| リスク | 影響 | 緩和 |
| --- | --- | --- |
| registry 分離ミスで ag.* 語彙検証が壊れる | analyze v2 が law-policy validation で fail | Phase C-2 で registry の ag manifest を先に別ファイルへ移してから v1 manifest を消す 2 段コミット。既存 AG テスト 90 個超が検出網 |
| `ArchMapSourceV1` の共用を見落として v2 が壊れる | archmap/v2 の deserialize 失敗 | リネーム(`ArchMapSource`)を削除より先に行い、型参照をコンパイラに追わせる |
| pr-review 機能の空白期間 | PR review workflow の中断 | C-1 先行(推奨)。ただし v1 pr-review の実用価値は predicate 5 語制約でほぼ無く、空白許容も選択肢 |
| FieldSig 側の削除順序ずれ | lean.yml:164-195 の v1 handoff 区間は archsig v1 raw artifacts と fieldsig `--analysis-packet` 受理の**両方**に依存する。PR-B2 で v1 受理まで消すと Phase C 完了まで CI が恒常 fail し、「各フェーズ末で CI green」条件と自己矛盾する | PR-B2 は v0 受理削除に限定し、v1 受理削除は lean.yml v1 区間削除と同一 PR(PR-C2)で行う(採用)。代替案: lean.yml の legacy handoff + schema-compatibility ステップ削除を PR-B2 に前倒し(v1 raw artifacts の e2e 検証が Phase C 完了前に痩せるため非推奨) |
| docs の改稿漏れ(v1 を current と記す記述の残存) | 三世代目のドリフト(現に tools/archsig/docs/commands.md:3-6 が「current route は archmap/v1」と記載) | C-3 完了条件に `rg -n "archmap/v1\|law-policy/v1\|typed evaluator\|distanceProfileRef\|molecule\|analysis-packet" docs/tool tools/archsig/docs tools/fieldsig/docs tools/archsig/skills tools/archsig/README.md CLAUDE.md AGENTS.md` の残存ゼロ検査(archive 内と移行表を除く)を含める |
| golden corpus の v1 削除で回帰検出網が痩せる | AG 側の退行検出漏れ | AG 側は evaluator ごとの executable lock(7 fixture + companion regression)が既に主役。削除対象の v1 lock は v1 経路自体の消滅により無意味化するため純減にならない |
| removal error 自体が「互換レイヤ」化して残り続ける | 二世代先の掃除課題 | v0.6.0 での除去を移行表に明記(時限措置) |

### 5.3 削除規模の見積り

| フェーズ | src 削減 | tests/fixtures 削減 |
| --- | ---: | --- |
| A | ≈5,000 行 | — |
| B | ≈35,000 行 | fixture 10 ディレクトリ、テスト 102 個(unit 66 + 15、`#[ignore]` 21) |
| C | ≈11,000 行 | fixture 3 ディレクトリ、テスト ≈40 箇所 |
| 合計 | ≈51,000 行(src 66.5 千行の 77%) | — |

残る src ≈15,000 行(AG path + 共有 infrastructure + 新 pr-review)。`tests/cli.rs`(17.3 千行)は v0 `#[ignore]` 21 個と v1 系 ≈40 箇所の削除で縮小する(削除行数は実装時に確定)。従来引用の「83.8 千行」は src(66,477 行)+ tests/cli.rs(17,346 行)の合算値であり、本表は src のみで数える。

---

## 6. 未決事項

1. **Lean guardrail 3 本の処遇**(推奨: Formal.lean から import 除去 + ファイル削除 + classical index の該当節 archive。Lean 塔の変更なのでユーザー確認必須)。
2. **第 1 世代理論ノート 4 本の docs/note → docs/archive 移動**(ユーザー判断。本文は歴史的価値のみで現行 source of truth ではない)。
3. **LawPolicy schema の版上げ形**(distanceProfileRef 削除を law-policy/v1 のフィールド削除として行うか、law-policy/v2 新設に含めるか。LawPolicy 再設計次元と結合。deny_unknown_fields のため旧文書は自然に fail する点は両案共通)。
4. **pr-review v2 の schema 最終形**(verdictTransitions の粒度、`archmap-diff/v1` のフィールド確定、`cover_changed_between_runs` boundary statement の schema 形、conclusion の supplied ArchMap への相対化注記の置き場、comparison data artifact の導入時期。comparison data は第X部 定義7.1 の形 — 次数 0/1/2 の両方向写像 + 差保存 + 微分可換、結論を格納しない — を目標形とする。artifact 再設計次元へ handoff)。
5. **run manifest / schema 表記の統一**(`x/vN` + key `schema` への一本化。v1 削除で 3 様式のうち 1 つが消えるが、統一自体は artifact 再設計次元の所管)。
6. **sharded-archmap 構想の再興の要否**(archive 後、v2 contexts/covers 前提で必要になった時点で新規設計。ArchMapStore の v2 化と同件)。
7. **C-1(受け皿先行)と C-2(削除先行)の最終順序**(推奨は C-1 先行だが、v1 pr-review の実用価値の低さから逆順も可)。
8. **removal error の保持期間**(提案: v0.5.x の間のみ、v0.6.0 で除去)。

---

## 査読対応

全 10 件を検証のうえ採用した。各指摘の裏取りは registry.rs(:284/:318/:388 の ag.* manifest と archmap.rs:869-874 の中立 predicate 5 語)、ag_measurement.rs(:10454-10461 / :6094-6095 / :6252-6262)、tests/cli.rs:1143、lean.yml:164-195、docs 実配置(tools/archsig/docs/ と docs/tool/)、CLAUDE.md:84-87 / AGENTS.md:122-125、第X部 §7-8(定義7.1 / 定理7.2 / 命題4.10 / 定理8.4 / 8.5)、law_policy/tests.rs(15 テスト・static_law_policy 使用 18 箇所)、src 実測 66,477 行 + tests/cli.rs 17,346 行、で個別に確認済み。CLAUDE.md 例の差し替え先(ag_measurement/archmap_v2.json + law_policy_ag.json)は analyze 成功を実行確認した。

1. **[boundary] mismatch 系譜の誤帰属 — 採用**。§2.2 を「1. AG path 自身の残存ドリフト」「2. v0/v1 の層越境」に書き分け、§4 冒頭 bullet を二軸(残滓除去 / 層越境・責務転嫁の除去)に改稿。PRD の「問い」接続もこの正確な系譜に置き、v0/v1 削除に earned でない「憲章名指し破損の回復」claim を負わせない旨を明記した。
2. **[boundary] witness_violation_support_refs の過小記述 — 採用**(指摘 8 と同一事象のため統合対応)。§3.2 残存ドリフト掃除を「legacy-counting-invariant invariant の packet からの廃止」に書き直し、削除範囲(helper / 呼び出し / emission ブロック / tests/cli.rs:1143 lock 含む fixture・golden 更新)と「判定語 atom を消費する最後の残滓」という根拠を明記。PR-C3 の green 条件に fixture 更新を追加した。
3. **[boundary] 「無条件に安全」の言い過ぎ — 採用**。「同一 profile 下の二測定の並記として安全」に弱め、`cover_changed_between_runs` boundary statement の規約(archmap-diff の covers added/removed/modified を利用、該当行は `--strict` exit 1 から除外)を最小契約として §3.4(1) に固定。schema 最終形は §6-4 の handoff に含めた。
4. **[theory] 定理8.5 の直接根拠化の不正確 — 採用**。boundary statement 例文と理論境界 bullet を「定義7.1 の H^1 comparison data が supplied されない限り語れない(無条件比較の不成立は定理8.4/8.5 が外周境界)」に改稿。命題4.10 の refinement pullback は特殊ケースのみである旨と、comparison data artifact の目標形(次数 0/1/2 両方向写像 + 差保存 + 微分可換、結論非格納)を §3.4(1) と §6-4 に明記した。
5. **[theory] conclusion の profile 単独相対化 — 採用**。§3.4(1) に「verdict の相対化」bullet を新設し、verdictTransitions が各側の supplied ArchMap にも相対的であること、archmap-diff が cover/context 変更を示す場合の相対化注記を report に含めることを最小契約化。conclusion 名は指摘の通り変更せず、§6-4 の handoff に相対化を含めた。指摘 3 の cover_changed_between_runs 規約と一体で実現する。
6. **[feasibility/major] PR-B2 と lean.yml の順序矛盾 — 採用(提案 (1) を採択)**。PR-B2 を v0 packet 受理削除に限定し、FieldSig の v1 `--analysis-packet` 受理削除は lean.yml v1 区間削除と同一 PR(PR-C2)に移した。提案 (2)(lean.yml 前倒し削除)は v1 raw artifacts の e2e 検証が Phase C 完了前に痩せるため非推奨代替としてリスク表に記録。リスク表の該当行に lean.yml:164-195 の二重依存を明記した。
7. **[feasibility/major] docs 場所指定と rg 範囲のずれ — 採用**。docs 表に「場所」列を追加して tools/archsig/docs/ と docs/tool/ を書き分け、CLAUDE.md / AGENTS.md の analyze 例差し替え(既に fail する v0 fixture 参照。PR-B1 に同梱)と tools/fieldsig/docs/commands.md の同期を改稿対象に追加。C-3 の rg 検査範囲を docs/tool, tools/archsig/docs, tools/fieldsig/docs, tools/archsig/skills, tools/archsig/README.md, CLAUDE.md, AGENTS.md に拡大し、検査語に analysis-packet を追加した。
8. **[feasibility] legacy-counting-invariant の分類誤り — 採用**(指摘 2 と統合)。「残置コード削除」分類を撤回し「invariant の廃止(packet 内容変更、fixture ロック更新込み)」とした。廃止か代替ソース存置かは本設計で確定する: 有効入力では恒常 vacuous な verdict であり、代替ソースを用意せず丸ごと廃止する(§3.4(6) の「代替を用意しないもの」にも追加)。
9. **[feasibility] 行数ラベルの齟齬 — 採用**。§1 の結論を「src 66.5 千行のうち ≈51k 削除、残 src ≈15k」に訂正し、「83.8 千行」が src + tests/cli.rs の合算である旨を §1 と §5.3 に明記。§5.3 の合計行を「src 66.5 千行の 77%」に修正し、tests/cli.rs の縮小は削除行数未実測として分離した。Phase B のテスト個数も 87 → 102(unit 66 + 15、ignore 21)に訂正(指摘 10 の law_policy/tests.rs 15 個を反映)。
10. **[feasibility] Phase B 削除リストの取りこぼし — 採用**。`src/law_policy/tests.rs`(15 テスト全てが static_law_policy = LawPolicyDocumentV0 依存。仕分けの上削除)と `src/archmap.rs:9,15` の `ArchMapSourceInventoryInput` / v0 import(列挙範囲 :938-1916 の外)を Phase B コード表に追記し、§2.1 の unit test 数の内訳表記も更新した。
