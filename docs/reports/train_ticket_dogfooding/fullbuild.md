# フルビルド: 全サービス完全抽出と cech 計測

## 実験概要

- **対象**: FudanSELab/train-ticket、commit `313886e99bef`(試運転と同一 checkout)。
  全42サービス+ts-common の Java main ソース+設定、440 sources / 28.5kLOC
- **手順**: archmap-creater SKILL の正規フロー。scope-manifest(承認記録付き)→
  full-dual 独立2パス(22 chunks × 2)→ extraction-diff → 全件調停(ソース再読)→ 統合 →
  coverage ledger → authoring audit 全16検査 → LawPolicy(money / status 各3点+bundle)→
  analyze ×2 → gate ×2 → ArchView browser 実走確認
- **実施日**: 2026-07-18(JST)
- **実施主体・モデル**: 統合・contexts/covers 設計・調停最終裁定は integrator(親セッション Claude)。
  **作業サブエージェント(抽出・調停)は全機 Sonnet 固定** — 「ArchMap は軽量モデルで作成できる」
  という製品条件の実測として
- **対応 Issue**: #3545(第1コメントが起草時の一次記録)

## 結果

| 項目 | 値 |
| --- | --- |
| ArchMap | 2,118 atoms / 43 contexts / 3 covers / 440 sources |
| sectionValue | 31 個を初回から統合(money-amount 24 contexts / order-status-code 7 contexts、cover ごと単一 section 規律) |
| 調停 | matched 294 / 調停 2,819 件(merged 1,903・adopted 887・not-adopted 29)+ integrator 正準化記録 1,178 件。matchRate 0.094(記録であり合否ではない) |
| analyze(money) | `NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE`(`run:856b95734cf7`) |
| analyze(status) | `NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE`(`run:ad99b1fd221a`) |
| gate | money / status とも `PASS_WITHIN_GATE_POLICY` |
| 供給コスト | 約1時間57分 ≈ **4.1分/kLOC**(wall clock、並列込み。試運転 8分/kLOC の約半分)。内訳: 抽出2パス 42分(44機)/ 調停 49分(22機、全件ソース再読)/ 統合+audit 10分 / LawPolicy+analyze+gate+viewer 16分 |

### 計測結果の中身

- **money**: witness 6辺中5辺で金額規約の mismatch を実測
  (string-passthrough / string→double+DecimalFormat / string→BigDecimal / double 直列 /
  double→文字列連結 / map-lookup が実在)。1-skeleton が森(サイクルなし)のため F₂ 類は 0 =
  「局所リラベルで貼り合わせ可能なドリフト」という読み。
- **status**: cancel–order–execute–order-other の実サイクル上で mismatch 2辺
  (ts-order-service だけ enum accessor + InitData 生リテラル 0 の混在)。サイクル上の和が
  偶数のため類 0。
- ドリフトは辺単位で実測され ArchView で可視(`evidence/fullbuild/archview-money.png`)。
  大域 H¹ 障害は測られていない — cech 検出器の設計どおりの語り。

## 実証したこと

1. **供給のスケール成立**: 28.5kLOC・440 sources の完全抽出で全工程が通り、
   authoring audit 全16検査 pass、analyze validation pass。
2. **軽量モデル条件の成立(条件付き)**: 全作業サブエージェント Sonnet で、品質は
   dual-pass+全件調停により担保された(440 sources 全件 read・skip 0、not-adopted 29 は
   全件ソース再読による正当棄却)。コストは試運転比で改善したが、matchRate 低下(0.28→0.094)→
   調停量増という形でコストが移転しており、subject 正規形・粒度規約の追加(所見1・2)が
   軽量モデル運用の実質的な前提となる。
3. **cech 検出器の実データ実働**: 規約 mismatch を辺単位で実測した上で、位相
   (森 / 偶パリティ)を根拠に類 0 と語った。「mismatch の実在」と「大域障害の不在」を
   区別して報告する設計が実データで機能した。
4. **中立表現規律の定着**: 禁止トークン混入は 5,441 候補 atoms 中 1 件
   (試運転は 8 packet 中 4)。試運転是正(PR #3504 系)の効果の実測。

## 実証していないこと

1. **この2 run では H¹ 非零は観測されていない。** money は森、status は偶パリティで、
   いずれも類 0。非零類の観測は次段(SAGA フル診断階段、[saga_diagnosis.md](saga_diagnosis.md))の
   対象である。
2. **matchRate 改善は見込みであり実測ではない。** 所見1(subject 命名ドリフトが不一致の約9割)への
   規約追加の効果は本実験では測っていない。
3. **コスト・品質の実測は train-ticket 1 repo。** 他言語・他規模への一般化は主張しない。
4. sectionValue の set 一括比較は語彙適用範囲の差だけで機械的 mismatch になるため、
   money / status を別 ArchMap 変種+別 analyze run に分離して回避した。セクション名ごとの
   比較への tooling 改良は設計論点として残る(結論の限定であり、本実験の未完了ではない)。

## 体験所見(是正候補、起草時記録の要約)

1. subject 命名ドリフトが不一致の約9割(最重要。prompt-pack への正規形規定で改善見込み)
2. 粒度規約の欠落(per-verb vs 束ね等で両パスが系統的に分岐)
3. candidate-packet 必須フィールド欠落時の下流エラーが不親切(既定表 fail-soft 補完は
   `evidence/fullbuild/integrator-fixups.json` に記録)
4. integrator 正準化と provenance closure の断絶(正準化記録は
   `evidence/fullbuild/subject-normalization-log.json`)
5. sectionValue set 一括比較の設計論点(上記)
6. 中立表現の定着を確認
7. not-adopted 29件はすべて正当な棄却

所見1–3 の是正は鍵収束 PRD → PR #3558 で消化済み。

## 証拠束と再現

- 供給: `evidence/fullbuild/scope-manifest.json`、`reader-instructions.md`、
  `adjudication-instructions.md`、`chunks.json`、統合スクリプト(`build_integrate.py`・`build_final.py`)
- ArchMap: `evidence/fullbuild/archmap.json`(統合版)+ `archmap-money-variant.json` /
  `archmap-status-variant.json`(analyze 入力。`inputDigests` と canonical digest 一致を検証済み)
- 品質記録: `extraction-consistency.json`(2パス差分)、`adjudication/`(22機の調停記録)、
  `coverage-ledger.json`、`integrator-fixups.json`、`subject-normalization-log.json`、
  `atoms-per-service.json`
- law: `evidence/fullbuild/law/`(money / status 各系列)
- 一次出力: `evidence/fullbuild/analyze-money/`、`analyze-status/`
- 再現コマンドは [README.md](README.md) のとおり(2026-07-19 に runId 一致まで確認済み)
