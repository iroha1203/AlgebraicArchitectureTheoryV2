# 試運転: cancel/refund スライスのワンショット e2e

## 実験概要

- **対象**: FudanSELab/train-ticket、commit `313886e99bef`。cancel/refund 業務フロー周辺の
  6 サービス、7.4kLOC
- **手順**: archmap-creater / law-policy-creater SKILL の公開手順どおり。
  clone → scope-manifest → full-dual 抽出(4 chunk × 2 パス並列)→ extraction-diff →
  調停(5並列、全件ソース再読)→ 統合 → authoring audit 全16検査 → LawPolicy 3点+bundle →
  `archsig analyze` → gate → ArchView 表示確認
- **実施日**: 2026-07-17〜18(JST)。実施は Claude(親セッション)+抽出・調停サブエージェント並列。
  使用モデルは正本記録に明記なし
- **対応 Issue**: #3498(完了コメントが起草時の一次記録)。発見6件の是正は #3499 系
  (PR #3504–#3507 マージ済み)

## 結果

| 項目 | 値 |
| --- | --- |
| ArchMap | 431 atoms / 16 contexts / 7 covers / 77 sources |
| 調停 | matched 166 / merged 310 / adopted 110 / not-adopted 6(matchRate 0.28 — 記録であり合否ではない) |
| analyze 結論(当時) | `NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE`(`run:0dab4af827e5`、validation pass) |
| analyze 結論(発見3是正後) | `AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE`(同一入力・同一 runId。PR #3504 マージ後の再実行) |
| gate | `PASS_WITHIN_GATE_POLICY`(当時 run に対して) |
| ArchView | SAGA シーン沈黙表示・gate 第二入力表示を browser 実走で確認 |
| 供給コスト | 約59分(wall clock、並列込み)≈ 8分/kLOC。内訳: 抽出2パス 22分 / 調停 10分 / 統合+検証 12分 / LawPolicy+analyze+gate+viewer 5分 |

フェーズ別の時刻は `evidence/trial/dogfood_timelog.txt`。

## 実証したこと

1. **供給成立のワンショット証拠**: 公開ワークフローだけで、外部 OSS に対する
   ArchMap 供給 → LawPolicy → analyze → gate → ArchView 表示の全工程が通る。
2. **fail-closed 検証の実働**: envelope 意味論の判定語混入(8 packet 中 4)を validator が
   正しく拒否した。独立2パスが同じ場所で同じ転び方をしたことも記録され、
   prompt-pack の表現例追記(PR #3504 系)につながった。
3. **供給コストの実測1点**: 7.4kLOC を約59分。

## 実証していないこと

1. **H¹ の実測はしていない。** 本試運転では sectionValue 観測を供給しておらず、witness 宣言辺は
   0 値 cochain として計測された(発見3: vacuous zero)。結論
   `NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE` は「供給した観測の範囲で障害が測られなかった」以上を
   意味しない。この設計論点は PR #3504 で是正され、未観測 witness 辺は沈黙に落ちる。是正後の
   現行ツールで同一入力を再実行すると結論は `AG_MEASUREMENT_FOUNDATION_READY_UNDER_PROFILE` になる
   (`evidence/trial/analyze-postfix/`。強すぎた結論文字列が是正された対比証拠)。
   sectionValue を初回から含める運用は次段フルビルドで導入した。
2. **供給コストの一般化。** 1 repo・1 フロー・1点の実測である。
3. gate policy artifact は実体未保存(`evidence/trial/analyze/archsig-gate-report.json` の
   `inputDigests.gatePolicy` に digest のみ)。gate 判定の再現には同等 policy の再供給が必要。

## 証拠束と再現

- 入力: `evidence/trial/archmap.json`(431 atoms)、`evidence/trial/law/`(LawPolicy 3点+bundle)。
  いずれも `evidence/trial/analyze/archsig-analysis-summary.json` の `inputDigests` と
  canonical digest 一致を検証済み
- 一次出力: `evidence/trial/analyze/`(当時 run。summary・packet・gate report・insight brief・
  run manifest・validation)、`evidence/trial/analyze-postfix/`(PR #3504 是正後の同一入力再実行)
- 供給品質の記録: `evidence/trial/adjudications/`+`evidence/trial/adjudication-rubric.md`
- 再現(analyze。現行ツールでは `analyze-postfix/` 側の結論・同一 runId が再現される。2026-07-19 確認済み):

```bash
EV=docs/reports/train_ticket_dogfooding/evidence
cargo run --manifest-path tools/archsig/Cargo.toml -- analyze \
  --archmap $EV/trial/archmap.json \
  --law-policy $EV/trial/law/law_policy.json \
  --law-surface $EV/trial/law/law_surface.json \
  --measurement-profile $EV/trial/law/measurement_profile.json \
  --out-dir .tmp/reports-repro/trial
```
