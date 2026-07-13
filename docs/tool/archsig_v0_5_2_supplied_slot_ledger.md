# ArchSig v0.5.2 supplied slot 台帳

この台帳は `docs/tool/archsig_v0_5_2_prd_saga_full.md` R1 の受け入れ表である。supplied はこの表の artifact を入力として読み、対応する validator が pass した場合に限り、右端の語彙を解禁する。global な列挙完全性や sheaf 条件のように有限検査で放電できないものは、assumption ledger に記録する。

| supplied 成分 | 理論典拠 | artifact の置き場 | validator | fixture | 解禁される語彙 | 実装段 |
| --- | --- | --- | --- | --- | --- | --- |
| 観測(atoms / contexts / covers) | PRD R1 / 第X部 (A) | `archmap/v0.5.2` | ArchMap R1-R3 | `tests/fixtures/ag_measurement/archmap_v2.json` | 層 B の生値 | PR-1済 |
| repair primitives(C⁰ / δ⁰ / supp) | PRD R1 / 定義3.1 (B) | `archsig-repair-plan/v0.5.2` | restriction-difference / overlap bijection | `tests/fixtures/ag_measurement/repair_plan_complete_support.json` | 境界所属 | PR-1済 |
| faithfulness data(zero primitive / Q / faithfulness law) | PRD R2 / 定義4.6 | RepairPlan `faithfulness.mode=supplied` | 3点参照整合 + finite support Q(r) 集合整合 | `tests/fixtures/ag_measurement/repair_plan_supplied_faithfulness.json` | complete-support 以外の肯定的大域整合 | PR-1済 |
| triple + additive 係数 | PRD R3 / 定義4.2 / 補題4.5 | RepairPlan `complex.tripleOverlaps` + `coefficient` | additive / δ¹∘δ⁰=0 / δ¹(0)=0 | `tests/fixtures/ag_measurement/repair_plan_supplied_coefficient.json` | 層 C の class 語彙 | PR-1済 |
| true sheaf certificate | PRD R3 / 定義4.7 | RepairPlan `trueSheafCertificate` | cover membership + global condition の assumption 記録 | `tests/fixtures/ag_measurement/repair_plan_true_sheaf.json` | 定理4.8 package 読み | PR-1済 |
| gluing data | PRD R3 / 第X部 定理7.3 | RepairPlan `gluingData` | selected overlap 集合 + sectionRef の一対一対応検査 | `tests/fixtures/ag_measurement/repair_plan_gluing_data.json` | grounded global gluing refs | PR-1済 |
| comparison data(incidence bridge + H¹ comparison) | PRD R4 / 定義7.1 / 定理6.4 | RepairPlan `comparison` + `h1-comparison-data/v0.5.2` | 両側逆・差保存・zero保存・微分可換 | `tests/fixtures/ag_measurement/repair_plan_comparison.json` | 層 D の転送 | PR-2予定 |
| law equation grounded surface | PRD R5 / 定義5.1 / 定義11.3 | `law-equation-surface/v0.5.2` | 5点組適合 + 単元 context 検査 | `tests/fixtures/ag_measurement/law_surface_ag_v052.json` | 層 E の10結論 | PR-3予定 |
| cost model(Lipschitz L + harmonic resolution) | PRD R7 / 第VIII部 系8.7 | `measurement-profile/v0.5.2` analytic 宣言 | 宣言検査 + assumption ledger | `tests/fixtures/ag_measurement/measurement_profile_harmonic_debt.json` | repair 下界行 | PR-5予定 |
| refactor morphism(site 射 + law / coefficient / witness 互換) | PRD R8 / 第VIII部 定理7.3 | `refactor-morphism/v0.5.2` | 互換データ検査 | `tests/fixtures/ag_measurement/refactor_morphism.json` | 版間 verdict transport | PR-6予定 |
| refinement data(粗→細) | PRD R8 / 命題4.10 | `refinement-comparison/v0.5.2` | 粗→細方向検査 | `tests/fixtures/ag_measurement/refinement_comparison.json` | compare の zero 引き継ぎ | PR-6予定 |

## 台帳外入力の扱い

結論相当の値、商水準の同一視、zero class、law の成立宣言を supplied slot に追加しない。未知フィールド、結論語を含む supplied block、または台帳に対応しない supplied 成分は fail-closed とする。供給されていない slot に依存する evaluator は verdict 行を立てず、PRD の Failure Contract に従う `silence_by_design` 行を生成する。

## 検証責務

この文書は入力台帳であり、実装の完了根拠ではない。各行の validator の assertion と fixture の内容は、対応する PR の tests と生成 packet を実読して確認する。slot の列挙完全性と global sheaf condition は `assumed_by: author` の assumption ledger 行として残す。
