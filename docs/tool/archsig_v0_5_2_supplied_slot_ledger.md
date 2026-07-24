# ArchSig v0.5.2 supplied slot 台帳

この台帳は ArchSig v0.5.2 R1 の受け入れ表である。supplied はこの表の artifact を入力として読み、対応する validator が pass した場合に限り、右端の語彙を解禁する。global な列挙完全性や sheaf 条件のように有限検査で放電できないものは、assumption ledger に記録する。

## R13 witness 帰属

- 3-chart の circle nerve は `circleSimplex` / `circleNext`、係数 `Z/(2)` に対応する Lean witness として扱う。
- 2頂点・逆向き2辺の circle nerve は本文の例9.2 / 付録 B.9 の worked example を固定する補助 fixture `tests/fixtures/ag_measurement/circle_nerve_two_vertex_body_v052.json` として扱う。この形を Lean proved witness として帰属させない。

| supplied 成分 | 理論典拠 | artifact の置き場 | validator | fixture | 解禁される語彙 | 実装段 |
| --- | --- | --- | --- | --- | --- | --- |
| 観測(atoms / contexts / covers) | Current tooling contract / 第X部 (A) | `archmap/v0.5.2` | ArchMap R1-R3 | `tests/fixtures/ag_measurement/archmap_v2.json` | 層 B の生値 | PR-1済 |
| repair primitives(C⁰ / δ⁰ / supp) | Current tooling contract / 定義3.1 (B) | `archsig-repair-plan/v0.5.2` | restriction-difference / overlap bijection | `tests/fixtures/ag_measurement/repair_plan_complete_support.json` | 境界所属 | PR-1済 |
| faithfulness data(zero primitive / Q / faithfulness law) | Current tooling contract / 定義4.6 | RepairPlan `faithfulness.mode=supplied` | 3点参照整合 + finite support Q(r) 集合整合 | `tests/fixtures/ag_measurement/repair_plan_supplied_faithfulness.json` | complete-support 以外の肯定的大域整合 | PR-1済 |
| component-local cocycle + additive 係数 | Current tooling contract / 定義4.2 / 補題4.5 | residual support component の `complex.tripleOverlaps` + `coefficient` | additive / δ¹∘δ⁰=0 / δ¹(0)=0。component に triple が無い場合は `automatic-c2-zero` 認証を出力する | `tests/fixtures/ag_measurement/repair_plan_component_aware_one_cent.json` | 層 C の class 語彙 | #3784 |
| true sheaf certificate | Current tooling contract / 定義4.7 | RepairPlan `trueSheafCertificate` | cover membership + global condition の assumption 記録。residual class 認証では certificate の cover / memberCharts が residual support component と完全一致する | `tests/fixtures/ag_measurement/repair_plan_component_aware_one_cent.json` | 定理4.8 package 読み | #3784でcomponent帰属を固定 |
| gluing data | Current tooling contract / 第X部 定理7.3 | RepairPlan `gluingData` | declared overlap subset + sectionRef の一対一対応検査。residual class 認証では subset が residual support component の overlap 集合と完全一致し、各 sectionRef は対応overlapから導くcanonical `section:<overlap suffix>` と一致する | `tests/fixtures/ag_measurement/repair_plan_component_aware_one_cent.json` | grounded gluing refs | #3784でcomponent帰属を固定 |
| comparison data(incidence bridge + H¹ comparison) | Current tooling contract / 定義7.1 / 定理6.4 | RepairPlan `comparison` + `h1-comparison-data/v0.5.2` | chart-indexed 集合一致または canonical explicit refs (`complex:repair` / `complex:cech` / `comparison:cochain-map`) + source/target fingerprint + target cochain support の `Z¹/B¹` 再計算。explicit は `cochainMap` の次数0/1/2有限基底写像表と次数2 `zeroImage` から、次数1両側逆・差保存・次数2零保存・微分可換を再計算し、宣言booleanは受けない | `tests/fixtures/ag_measurement/repair_plan_comparison.json` | 層 D の転送 invariant | PR-2済 |
| law equation grounded surface | Current tooling contract / 定義5.1 / 定義11.3 | `law-equation-surface/v0.5.2` (`skeleton` / `defectSources[].holdsCriterion` / `quotientSheafCondition`) | Stage 3 shape + law/axis/predicate resolution; analyze 時の atom/chart/cover 解決; single-context-theorem の単元性検査 | CLI Stage 3 正系 fixture + `law_surface_ag_v052.json` runtime path | 層 E の10結論を後続 evaluator に供給する grounded surface | PR-3実装済 |
| saga-grounding / 10結論 packet | Current tooling contract / 定義5.1 / 定理7.5・8.1・8.2・11.5 | RepairPlan `grounding.kind=saga-grounding` + `archsig-saga-conclusions/v0.5.2` | grounding/profile/surface/cover の参照整合、F₂ additive、有限上限、holdsCriterion 生値、witnessVariables / forbiddenSupportGenerators からの quotient 生成、nested packet validator、detector | `cli_analyze_v2_saga_grounded_emits_split_packet_and_detector` | lawDependent / lawIndependent の10結論、degree-zero寄与、chart detector、生成商 provenance | PR-4 corrective follow-up実装済 |
| diagnostic ceiling / policy profileRef | Current tooling contract | `measurement-profile/v0.5.2.diagnosticCeiling` + `policies[].profileRef` | registered ceiling stage、policy profile ID 解決、未到達時の `silence_by_design`、site/cover validator | `measurement_profile_*` CLI negative/positive locks | 選択診断段の boundary contract | PR-3実装済 |
| cost model(Lipschitz L + harmonic resolution) | Current tooling contract / 第VIII部 系8.7 | `measurement-profile/v0.5.2` analytic 宣言 | innerProduct weights + costModel kind/L/resolution、assumption ledger 記録 | `tests/fixtures/ag_measurement/measurement_profile_harmonic_debt.json` | harmonicDebtNorm、cost model供給時のみrepair下界行、未供給時は invariant / analytic reading の `whatNext` を一致させた typed silence | PR-5実装済 |
| refactor morphism(site 射 + law / coefficient / witness 互換) | Current tooling contract / 第VIII部 定理7.3 | `refactor-morphism/v0.5.2` | site / cover / law / coefficient / finite witness compatibility の fail-closed 検査 | `tests/fixtures/ag_measurement/refactor_morphism.json` | validated artifact + witness による analytic verdict transport | PR-6実装済 |
| refinement data(粗→細) | Current tooling contract / 命題4.10 | `refinement-comparison/v0.5.2` | coarse-to-fine direction + `zeroTransport.checked` + coarse/fine `complexFingerprint` と base/head の `inputDigests.siteCoverDigest.sha256` の突合 | `tests/fixtures/ag_measurement/refinement_comparison.json`（`cli_refinement_fixture_binds_to_generated_run_fingerprints`でrun-bound lock） | compare の coarse-zero → fine-zero 引き継ぎ(`CLASS_ZERO_TRANSPORTED_UNDER_CHECKED_REFINEMENT`) | Issue #3377是正済 |

## 台帳外入力の扱い

結論相当の値、商水準の同一視、zero class、law の成立宣言を supplied slot に追加しない。未知フィールド、結論語を含む supplied block、または台帳に対応しない supplied 成分は fail-closed とする。供給されていない slot に依存する evaluator は verdict 行を立てず、PRD の Failure Contract に従う `silence_by_design` 行を生成する。

## 検証責務

この文書は入力台帳であり、実装の完了根拠ではない。各行の validator の assertion と fixture の内容は、対応する PR の tests と生成 packet を実読して確認する。slot の列挙完全性と global sheaf condition は `assumed_by: author` の assumption ledger 行として残す。
