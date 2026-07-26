# Claim-to-evidence matrix(正本)

> 論文(正本=`en/main.tex` 一式、日本語草稿=`zenodo_saga_draft.md`)の各 claim を
> 一次証拠へ対応させる監査表。P0-6 final review はこの表を照合基準として実行する。
> 「状態」列が `TODO(tag)` の行は release identity(release tag・CI run・deposit path)
> 確定時に埋める。それ以外の行は 2026-07-26 時点で照合済み。
> deposit bundle への同梱は deposit 時に裁定する(同梱する場合は TODO 消化後の版)。

## A. Mathematics(第3〜5章)

検証方法の正本: 草稿管理付録C の canonical 対応表(paper 番号 ↔ 第X部ほか)。
canonical 数学本文 = `docs/aat/algebraic_geometric_theory/`(第X部 =
`part_10_semantic_repair_descent_saga.md`)。レビュー履歴 = PR #3828(Codex 2巡)、
PR #3832/#3836(検算含む多レーン)、PR #3845(移設時の claim 不変監査)。

| ID | 論文の箇所 | Claim | 一次証拠 | 状態 |
| --- | --- | --- | --- | --- |
| M1 | §3.1〜§3.9 | 基礎定義(Atom、equation system、site、presheaf、witness/obstruction ideal)の self-contained な再構成が canonical と一致 | 第I〜III部の対応 statement(草稿付録C 対応表の基礎定義表) | 照合済み |
| M2 | §3.10 | displayed source から生成される `Q_E`、quotient zero criterion(条項5) | 第III部 定義11.3、定理11.4 | 照合済み |
| M3 | 第4章 | 二複体(semantic 側 `C•_sem`・equation 側)の構成、torsor 読み、residual と choice independence | 第X部 定義2.1/3.1〜3.5/4.1/4.2、定理4.4、系4.5 | 照合済み |
| M4 | 定理5.1(i) | presentation exactness と係数同型 `Φ`(soundness は導出、completeness 対のみ仮定) | 第X部 命題6.1A、定理6.3、系6.7 | 照合済み |
| M5 | 定理5.1(ii) | cochain 比較 `κ` の可換性、`H¹` 同型、residual class 対応 | 第X部 定理7.2/7.4/7.5 | 照合済み |
| M6 | 定理5.1(iii)/定理5.2 | true sheaf 条件下の grounded gluing と三項同値 | 第X部 定理8.2、系8.3、定理1.1 | 照合済み |
| M7 | 補題5.2A | ordered matching completion(thin 文脈) | 第X部 補題2.1A | 照合済み |
| M8 | §5.3 | 三条件それぞれを外した有限反例(soundness / completeness / generation) | 第X部 例6.6 | 照合済み |
| M9 | 例5.3 | 4-cycle circle witness(cycle-without-a-face、非零類) | 第X部 例10.2、付録B.9 | 照合済み |
| M10 | §5.7・付録A | `H¹` の cover 相対性、Leray 型比較の非主張、thin 開示、仮定の帰属 | 第X部該当節+論文付録A(消費表) | 照合済み |

## B. Lean(第6章)

| ID | 論文の箇所 | Claim | 一次証拠 | 状態 |
| --- | --- | --- | --- | --- |
| L1 | §6.2 表 | 全行 `proved`(paper claim ↔ Lean declaration 18本の対応) | `Formal/AG/SemanticRepair/Saga/` の宣言実在(2026-07-26 全18本 grep 確認)+ CI の full `lake build` | 照合済み |
| L2 | §6.2 表 | axiom 健全性(標準3公理のみ) | `Formal/AG/AxiomAudit.lean`(4311宣言 standard axioms only、CI 強制)+ 中心チェーン13宣言の `#print axioms` 独立実行(2026-07-26) | 照合済み |
| L3 | §6.2 表・仮定列 | 各行の仮定(selected packet、completeness 対、Fintype、thin、true sheaf 条件)が Lean statement と一致 | Lean statement 実読(PR #3828 F6)+ PR #3843 の入力8 field 除去(packet 面と §5.2 の整合) | 照合済み |
| L4 | §6.2 末尾 | 未移植は非 thin site gluing のみ | §6.2 末尾の明示記録+`unported` 台帳 | 照合済み |
| L5 | §6 冒頭 | release snapshot の同定(対象 commit hash・release CI run) | release tag と tag 上の CI run | **TODO(tag)** |

## C. Measurement / Empirical(第7章+付録C)

証拠束の正本 = `docs/reports/train_ticket_dogfooding/`(本文 `saga_diagnosis.md`、
証拠 `evidence/saga/`)。ArchSig = `tools/archsig`(toolVersion 0.5.4、
RepairPlan schema v0.5.7)。

| ID | 論文の箇所 | Claim | 一次証拠 | 状態 |
| --- | --- | --- | --- | --- |
| E1 | §7.1 | 対象 = train-ticket(FudanSELab)commit `313886e99bef`、42 services | report(README/trial/fullbuild)での commit pin+shallow 再取得による典拠確認記録 | 照合済み |
| E2 | §7.1 | 3流儀(cancel の丸め文字列化 / inside-payment の BigDecimal / order の素通し)が実ソースに実在し ArchMap の section value として観測 | `saga_diagnosis.md`「発見」節の source 同定+ArchMap の観測 atom refs | 照合済み |
| E3 | §7.1 | 数値 witness(12.33 → 9.86 vs 9.864、remainder 0.004)は source 水準の検算で、packet 計算対象外 | 論文内の計算表示+report の同計算。packet 非出現は E6 の契約から従う | 照合済み |
| E4 | §7.2 | head 診断: `MEASURED_NONGLUING_RESIDUAL`、grounding `measured_zero`、`inB1: false`、`run:78c31d6a3172` | `evidence/saga/out/head/`(measurement packet、run manifest、validation)。runId・conclusionCode 一致は 2026-07-26 再確認 | 照合済み |
| E5 | §7.2 | repaired 診断: `REPAIR_GLUES_WITHIN_SELECTED_COMPLEX`、`inB1: true`、`run:6685bab8db21`、gate BLOCKED→PASS | `evidence/saga/out/repaired/`・`out/compare/`+gate 出力 | 照合済み |
| E6 | §7.4 | **中心 claim**: 結論(residual・boundary membership・gate)は観測+選択方程式系から決定論的に導出され、結論を運ぶ入力は契約に存在しない。fail-closed が執行 | ArchSig source+cargo test 233本(2026-07-26 全 pass。重複 overlap の fail-closed 回帰 #3804 系を含む)+RepairPlan v0.5.7 schema(選択複体のみ) | 照合済み |
| E7 | §7.4 | 定理5.1 の有限 instantiation は計測の範囲外(第6章 Lean が担う) | 契約の範囲定義そのもの+condition matrix(E8)に比較段が無いこと | 照合済み |
| E8 | 付録C.3 | condition matrix 各行(computed / checked / assumed / unmeasured)の種別と記録 | 正本 = `saga_diagnosis.md` condition matrix(#3829 で canonical anchor 再帰属済み)↔ packet assumption ledger・validation reports | 照合済み |
| E9 | 付録C.2 | 供給工程: 機械層/読解層分離、scope 承認、2パス調停、audit、モデル記録(2,118 atoms / 42 services を軽量モデル run で作成) | authoring SKILL 本体+scope manifest+調停記録+run のモデル記録(fullbuild report) | 照合済み |
| E10 | 付録C.4 | 再現: 固定入力からの `analyze`×2 / `compare` / `gate`×2 で runId・gate 判定一致、`inputDigests` は canonical digest と一致 | `saga_diagnosis.md` 再現節+builder script。**deposit 相対 path・command 一式・expected output** | **TODO(tag)** |

## D. Related Work / novelty(第8章)

| ID | 論文の箇所 | Claim | 一次証拠 | 状態 |
| --- | --- | --- | --- | --- |
| R1 | §8.1 | Young 2026 の報告値(Lean 1,259行、375 benchmarks)は「当該論文の報告」として引用。artifact 非公開のため source 比較は対象外 | `zenodo_saga_related_work.md` §2.7 原典確認+2026-07-26 arXiv 再実査(v1 のまま) | 照合済み |
| R2 | §8.1 表 | SAGA の新規性 = 比較表下2行(domain-specific construction / discharged obligations)であり、一般機構は claim しない | M4〜M6 の canonical 証明+§5.1「三段の性格」の帰属 | 照合済み |
| R3 | 第8章全体 | 書誌・年次・出版状態(2026年文献3点含む) | `zenodo_saga_references.bib`(確定調査値)+2026-07-26 実査記録(草稿付録A) | 照合済み |

## E. Summary claims(要旨・§1・§9・§10)

| ID | 論文の箇所 | Claim | 一次証拠 | 状態 |
| --- | --- | --- | --- | --- |
| S1 | 要旨・§1・§10 | 中心2式(`H¹_sem(𝒰) ≅ Ȟ¹(𝒰,Q_E)`、三項同値)と「証明・機械検証 status・再現計測の三層」 | M5/M6(数学)、L1〜L4(Lean)、E4〜E6(計測) | 照合済み |
| S2 | 要旨・§1.3 | 三層が同一 release identity を参照する | release tag・version DOI・bundle manifest の相互参照 | **TODO(tag)** |
| S3 | 第9章 | 展望(Rising Sea、SFT、反実仮想等)は vision であり evidence を要する claim ではない(本文中で明示) | — (非対象) | 非対象 |

## 状態集計

- 照合済み: 26 行
- **TODO(tag)**: 3 行 — L5(第6章 tag/CI run)、E10(付録C.4 deposit path)、S2(release identity 相互参照)。いずれも release tag 確定後の同一作業で消化する
- 非対象: 1 行(S3、vision 節)
