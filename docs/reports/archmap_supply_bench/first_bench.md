# 供給ベンチ第1報: 規約 v2 の再現性・精度ベースライン(独立 3 run 対)

## 実験概要

- **対象**: ArchMap 供給(archmap-creater SKILL、収束規約 v2)の再現性・精度。
  corpus は FudanSELab/train-ticket(commit `313886e99befb94be6cd45f085c98e0019f59829`)の
  3 chunks / 60 sources / 5,084 LOC — tuned = chunk-04・chunk-13(規約チューニングに
  使用歴あり)、prompt-literal-disjoint = chunk-01(prompt-pack コードリテラルとの
  交差ゼロを機械検査で確認済み。規約開発からの独立は主張しない)
- **手順**: 供給ベンチ正本(`docs/tool/archmap_supply_bench.md`)の実行プロトコル。
  比較系列 key と pairing((run-1,2)(run-3,4)(run-5,6))を**抽出開始前に登録**
  (`evidence/run1/series-key.json`)→ 独立 6 run(fresh session、他 run 成果物の
  参照禁止)→ extraction-diff ×9 → merge グループ付き全件調停 ×9(909 行、全件
  ソース再読)→ reference-alignment ×9(参照裁定スライス v1、完全性・一意性
  fail-closed)→ `archsig supply-bench` ×3(chunk 毎3ペア)
- **実施日**: 2026-07-21(JST)
- **実施主体・モデル**: 読者・調停・alignment サブエージェントは全機 Sonnet
  (claude-sonnet-5)。integrator(統合・機械検査・fixup・最終裁定)は親セッション。
  比較系列 key の全8要素は series-key.json に記録
- **対応 Issue**: #3673(供給ベンチ PRD 実装 tracking)

## 結果

runId: `supply-bench:train-ticket-chunk-04-v1` / `...-chunk-13-v1` / `...-chunk-01-v1`
(証拠束 `evidence/run1/out/`、canonical digest は `evidence/run1/digests.json`)

各指標は独立 3 run 対の最小 / 最大 / 平均(記述統計。分布・有意性は主張しない):

| 指標 | chunk-04 (tuned) | chunk-13 (tuned) | chunk-01 (disjoint) |
| --- | --- | --- | --- |
| 鍵収束率 | 0.570 / 0.811 / **0.680** | 0.475 / 0.722 / **0.573** | 0.818 / 0.886 / **0.845** |
| 機械 matchRate(@2) | 0.310 / 0.483 / 0.385 | 0.257 / 0.446 / 0.324 | 0.552 / 0.729 / 0.641 |
| 参照回収率(裁定) | 0.869 / 0.893 / **0.881** | 0.880 / 0.944 / **0.914** | 0.756 / 0.807 / **0.790** |
| 参照回収率(機械下限) | 0.333 / 0.357 / 0.345 | 0.481 / 0.509 / 0.491 | 0.348 / 0.348 / 0.348 |
| 過剰生成率 | 0.000 / 0.056 / 0.029 | 0.022 / 0.121 / 0.088 | 0.000 / 0.000 / 0.000 |

- **決定論**: 同一入力に対する `supply-bench` 出力はペア引数順を逆にしても
  byte 一致(実測確認)。
- **調停の組成**: 909 裁定行のうち not-adopted は 12(1.3%)。両 pass の内容不一致は
  希少で、不一致の主因は表現(鍵)の揺れ。過剰生成率の中身も大半が「既 matched 事実の
  述語レンズ違い重複」であり、ソースに反する捏造系は 12 行に留まる。
- **供給コスト**(記録): 抽出は 5.3〜16.0 agent-分/kLOC(run 毎、中央値 ≈ 7.7。
  1 run に API 中断→再開があり最大値はそれを含む)。総 agent 時間は
  読者 274.8 分+調停 100.6 分+alignment 125.5 分。
- **integrator fixup**(2件、`evidence/run1/integrator-fixups.json`):
  (1) alignment prefill の行内 id 重複の除去(両 pass が同一 atom id を独立生成した
  衝突に起因)、(2) onlyIn の同一 id 衝突 6 件の `#pass-a`/`#pass-b` 曖昧性除去。
  いずれもツールの fail-closed 検査が検出し、機械修正を記録した。

## 実証したこと

1. **ベンチ自体の成立**: PRD の反例1〜7 を消した状態で初回実測が完走した。
   corpus・手順・計量・参照は全て fixture / 正本に固定され、第三者が同じ測定を
   再実行できる(下記再現手順)。決定論部分は byte 一致を実測。
2. **「内容は再現し、表現が揺れる」の分散付き定量化**: 裁定込み参照回収率は
   9 点全てで 0.756〜0.944(平均 0.79〜0.91)と安定し、not-adopted 1.3% と
   合わせて「独立 run が同じ事実を見ている」ことを示す。一方、鍵収束率は
   0.475〜0.886 と run 対で大きく揺れ、機械表現の収束が現時点の主要な変動源で
   あることを分離して示した。
3. **prompt-literal-disjoint チャンクの成績**: 鍵収束率は disjoint チャンクが
   3 対とも最高値(0.818〜0.886)かつ最小分散で、tuned チャンクを上回った。
   規約リテラルへの過適合だけでは説明できない(admin 系の定型構造が収束を
   助けている読みが自然)。tuned/disjoint の分離報告が、この種の構図を
   隠さず語れることを実証した。
4. **揺れの主因の特定**: 調停記録上、merge の支配的パターンは capability の
   述語レンズ(`exposesEndpoint` 対 `handlesCommand`/`servesQuery`)と粒度
   (束ね対 per-endpoint / per-method)であり、PR #3558 の系統分解で残った
   「語彙レンズの判断残余」が、規約 v2 でも最大の不一致源として定量的に残る
   ことを確認した。後続の規約改善 PRD の主対象がここになる。
5. **参照の系統的欠落の発見**: alignment の novel-correct(参照改訂候補)は
   ServiceImpl レベルの capability 層に集中して 9 対全てで再現した。参照 v1 が
   controller endpoint 粒度しか持たない箇所を、独立 run が一貫して細粒度で
   観測している。参照 v2 の改訂候補として記録した。

## 実証していないこと

1. **値の一般化**: 全数値は比較系列 key(corpus v1・参照 v1・claude-sonnet-5・
   規約 v2・記録済み調停者)に相対する記録である。他言語・他規模・他モデル・
   他規約版への一般化は主張しない。
2. **source-level recall**: 参照回収率は凍結 candidate union 由来の参照
   裁定スライス v1 に対する回収率であり、source に存在する事実全体への
   再現率ではない。両 pass がともに見落とす事実は測れていない。
3. **統計的推論**: n=3 の最小・最大・平均は記述統計であり、検定・信頼区間の
   主張はしない。悪化検出の閾値・許容帯の制定は後続 PRD の仕事である。
4. **調停の再現性**: 裁定値系指標は記録された調停の関数であり、調停記録込みで
   計算の再検証はできるが、調停そのものを別の調停者が再現したときの一致率は
   測っていない(正本の反証可能性の成立範囲どおり)。
5. **禁止トークン混入ゼロの検査は packet validator の通過をもって確認**した
   (全 18 packets が fail-closed 検査を通過)。それ以上の表現品質は本実験の
   対象外。

## 証拠束と再現手順

証拠束(`evidence/run1/`、canonical JSON digest は `digests.json`):

- `series-key.json` — 抽出開始前に登録した比較系列 key と pairing
- `packets/` — 18 candidate packets(6 run × 3 chunks、raw)
- `consistency/` — 9 extraction-consistency(merge グループ付き全件調停を結合済み)
- `alignment/` — 9 reference-alignment + 9 機械 prefill
- `out/` — 3 supply-bench 出力(本報告の数値の一次 artifact)
- `integrator-fixups.json` — 機械修正の全記録
- `reader-instructions.md` / `adjudicator-instructions.md` / `alignment-instructions.md`
  — 各サブエージェントへの指示書(パスは placeholder 化)
- `train-ticket-313886e9.bundle` — corpus の git bundle(上流消滅時の復元経路)

再現手順は [README.md](README.md) のとおり。決定論部分(計量)は packets と
調停・alignment 記録から `archsig supply-bench` で数値まで再計算でき、
供給部分(抽出・調停)は指示書と系列 key の下で再実行できる(値は調停者・
モデル snapshot に相対)。
