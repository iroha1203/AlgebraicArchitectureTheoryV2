# SAGA フル診断階段: presentation-generated one-cent 類 → BLOCKED → repair 事前検証 → PASS

## 実験概要

- **対象**: フルビルド成果物(money 変種 ArchMap)を土台に、law を SAGA フルスタックへ拡張し、
  train-ticket(commit `313886e99bef`)の実データで診断階段を一周した
- **再計測日**: 2026-07-25(JST)
- **実施主体・モデル**: Claude 直接(Fable)。典拠確認には同一 commit の shallow 再取得を使用
- **対応 Issue**: #3785（presentation-generated comparison は #3783、component-aware class 認証は #3784 を前提にする）

## 発見: one-cent 構造が train-ticket に実在する

cancel–inside-payment–order の実呼び出し三角形上で、金額規約が3流儀とも異なる
(いずれも実ソースで確認、ArchMap の sectionValue として観測):

- **cancel**: `Double.parseDouble(order.getPrice()) * 0.8` → `DecimalFormat("0.00")` で丸めて文字列化
  (`CancelServiceImpl.calculateRefund`)
- **inside-payment**: `new BigDecimal(order.getPrice())` の正確算術(`InsidePaymentServiceImpl`)
- **order**: `private String price` の素通し保管(`Order.java`)

さらに、3サービスの金額を同時に照合するサイトがコード上に存在しない = triple overlap が正直に空。
閉ループ上の奇パリティ+面なしで**非零 F₂ 残差類**が立つ。丸め剰余(0.8×価格の1セント未満)は
どのチャートにも記帳されていない。「3流儀 × 1-サイクル = H¹」というデモの設計原理
(ArchSig example「1セントのドリフト」)が、合成例ではなく実在 OSS で観測された。

## law 構成

- law cover `cover:money-settlement-loop`(6チャート): 三角形 {cancel, inside-payment, order} +
  託送料金領域 {preserve, consign, consign-price}
- law surface 3本: `surface:cech-surface-v052`(closed-equational、witness 4辺)/
  `law:money-settlement-convention`(ag.saga-grounded、skeleton 6頂点 + defectSources)/
  `law:money-repair-descent`(descent、ag.saga-descent)
- repair-plan: source-grounded repair cover に chart / overlap / triple の有限 presentation cell を置く。
  diagnostic component は cancel–inside-payment–order の3 chart・3 overlap であり、
  `C²=0` の `automatic-c2-zero` をその component 自身の認証として出力する。
  `trueSheafCertificate` と `gluingData` も同じ component にだけ対応付ける
- comparison: 各 cell の semantic generator、repair/equation relation 行列、generator map、
  restriction、equation lift atlas から `χ / Φ / κ` を有限検査で生成する。
  head の `drift:refund-rounding` は三角形3辺、repaired は零 cochain として計測する
- repaired 変種: 三角形3チャートを BigDecimal scale-2 HALF_EVEN 統一規約に置換した仮修理 ArchMap

## 条件種別と comparison cochain map の来歴

`presentation packet` は有限データとして実施者が author する入力である。ここでいう
`generated` / `computed` / `checked` は、その入力を越えた結論を供給したという意味ではなく、
入力を受け取った ArchSig が下表の有限計算・検査を行ったことを表す。head / repaired の両 packet
で同じ区別を記録した。

| 条件種別 | one-cent packet の対象 | packet 上の確認箇所・扱い |
| --- | --- | --- |
| `supplied` | source-grounded presentation cells、semantic / equation generators、relation 行列、generator map、restriction、equation lift atlas、residual cochain、`trueSheafCertificate`、`gluingData` | RepairPlan の authored 入力。たとえば residual と各 overlap support は `kind: supplied` であり、ArchSig が source から自動発見したものとは扱わない |
| `assumed` | selected quotient sheaf condition と true sheaf global condition | packet `assumptions`、および `trueSheafCertificate.globalCondition: assumed`。この仮定を結論や generated data と取り違えない |
| `computed` | presentation からの `χ / Φ / κ`、semantic / equation residual、quotient-level H¹ transfer、target support | `generatedCochainMap` の各 local `Φ` は generator map を relation で割った有限計算から導出。`generatedQuotientTransfer` は source / target class の零判定を記録する |
| `checked` | presentation exactness、generator completeness、restriction naturality、degree 0/1 cochain 可換性、degree 2 cell の finite atlas、comparison contract、component cocycle、canonical input digest | `presentationExactness: true`、`generatorCompleteness: true`、`restrictionNaturality: true`、`degreeZeroCommutative: true`、`degreeOneCommutative: true`、`contractChecked: true` と input digest の一致で固定する |

comparison cochain map は外部から matrix を `supplied` する経路ではない。互換性上
`suppliedCochainMap` と名付けられた出力欄も、今回の値は `kind: presentation-generated` であり、
実体は `generatedCochainMap` が presentation から導出した local `Φ` である。したがって
comparison の来歴は **supplied cochain matrix → presentation-generated / checked cochain map** に移った。
この移行の確定条件は、有限 presentation の exactness・generator completeness・restriction
naturality・degree 0/1 可換性と degree 2 atlas を検査したうえで、head の
`SAGA_COMPARISON_GENERATED_FROM_PRESENTATIONS` と `contractChecked: true` を出力することである。

### #3781 §7 用 condition matrix

次表は #3781 が §7 の本文へ転記するための行別の正本である。`supplied` は authored input、
`assumed` は packet が外部から受け取る数学的前提、`computed` は入力からの有限計算、
`checked` は ArchSig が有限 artifact に対して検査した条件を表す。特に input にある
`enumerationComplete: true` は列挙の完全性そのものを証明する flag ではなく、author の
`assumed` condition として扱う。

| Condition | Kind | Status | Evidence |
| --- | --- | --- | --- |
| finite cover | finite artifact property | `checked` | head / repaired packet の `finite site` は `checked`、`siteCoverDigest` は normalized contexts・covers・derived finite cover nerve から `computed` |
| residual support | authored finite cochain | `supplied` | RepairPlan `residual.kind: supplied` と各 overlap support。head は `drift:refund-rounding` を診断3辺へ与える |
| repair-plan complex enumeration completeness | author assertion | `assumed` | RepairPlan `complex.enumerationComplete: true` に対し、packet は `repair-plan complex enumeration completeness` を `assumed` と記録する |
| target quotient presentation enumeration completeness | repair-plan と同じ authored presentation cell 集合 | `assumed` for cell enumeration; `checked` for generation | target は別の supplied complex ではない。同じ cells から組み立て、cell 列挙は上行の author assertion に依存する一方、`generatorCompleteness: true` がその列挙から target quotient が生成されることを検査する |
| faithfulness law | authored mathematical assumption | `supplied` / `assumed` | RepairPlan `faithfulness.mode: supplied`。packet は `faithfulness law supplied` を `assumed` として依存関係へ残す |
| global sheaf condition | mathematical assumption | `assumed` | `trueSheafCertificate.globalCondition: assumed` と packet の `global sheaf condition` assumption |
| comparison cochain map | presentation-derived finite map | `computed` / `checked` | `generatedCochainMap` の local `Φ`、exactness・generation・naturality・degree 0/1 可換性、head の `SAGA_COMPARISON_GENERATED_FROM_PRESENTATIONS` と `contractChecked: true` |
| boundary membership / residual class | finite quotient calculation | `computed` | head は `saga-descent:boundary-membership.inB1: false` と `MEASURED_NONGLUING_RESIDUAL_CLASS`、repaired は零類・`REPAIR_GLUES_WITHIN_SELECTED_COMPLEX` |
| repaired ArchMap | hypothetical repair input | `supplied` / hypothetical | `archmap-saga-repaired.json` は BigDecimal scale-2 HALF_EVEN 統一を表す仮説 variant。`PASS_WITHIN_GATE_POLICY` は実装済み修理を示さない |
| runtime monetary magnitude | empirical measurement | unmeasured | harmonic-debt を供給せず沈黙。頻度・金額を結論に含めない |

## 結果(診断階段)

| 幕 | 結果 |
| --- | --- |
| head analyze | `MEASURED_NONGLUING_RESIDUAL_CLASS`(`run:8d4b5849eb52`) |
| └ grounding | `measured_zero` — 各チャートは自分の法を守っている(それが罠) |
| └ descent 残差類 | `measured_nonzero`(diagnostic component、`automatic-c2-zero`、三角形3辺 support) |
| └ comparison h1-transfer | `SAGA_COMPARISON_GENERATED_FROM_PRESENTATIONS`（exactness / generation / naturality / `κ` / atlas witness を検査） |
| gate head | `BLOCKED_BY_GATE_POLICY` |
| repaired analyze | `REPAIR_GLUES_WITHIN_SELECTED_COMPLEX`(`run:503e65b25714`) |
| compare head→repaired | `MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE` |
| gate repaired | `PASS_WITHIN_GATE_POLICY` |

harmonic-debt は runtime 実測数値が無いため供給せず、沈黙(供給する場合は実走の払い戻し照合が必要)。

## 実証したこと

1. **AAT 中心主張の実データ着地**: 非零類の成立条件が「3流儀の衝突」だけでなく
   「三者同時照合サイトの不在」だったこと。各チャート単独は完全に筋の通った金額の扱いをしており
   (grounding = `measured_zero` が計測でそれを言う)、ペアごとの受け渡しも各々は成立している。
   障害はループを一周したときだけ現れ、それを埋める面(triple)がコードに存在しないから類として残る。
   「局所的には合法、大域的に貼り合わない」という構造が、こちらが仕込んだのではない実在 OSS で
   観測された。デモは「この構造なら H¹ が立つ」の実演だったが、本実験は
   「この構造は現実に生じる」の証拠である。
2. **診断階段の全段が実データで機能**: presentation の exactness / generator completeness /
   restriction naturality / cochain 可換性 / atlas witness を検査して導出した H¹ transfer と、
   component-aware class 認証を含め、非零類の計測 → gate BLOCKED → 修理計画の事前検証 →
   compare による障害消滅の記録 → gate PASS まで一周した。
3. **数学的規律の拒否が正しく働いた**: ドリフトの立つ三角形自体を triple として申告すると
   cocycle 条件で拒否される(数学的に正当)。典拠の無い residual ref は fail した
   (初回 run は未解決 ref で正しく失敗)。実データで負荷をかけて規律が守られた。
4. **語れないことへの沈黙**: harmonic-debt は runtime 実測が無い状態では供給せず沈黙した。

## 実証していないこと

1. **検出の新規性は cech 段にある。** SAGA residual 供給(三角形3辺への `drift:refund-rounding`)は
   実施者が書いた authored model であり、計測が発見したものではない。規約 mismatch の検出自体は
   フルビルドの cech law が既に行っていた。SAGA 段が足したのは、grounding の罠の明示・
   修理計画の事前検証・h1-transfer・gate の一貫した診断であって、
   「SAGA が新しい障害を発見した」という主張は過大である。
2. **repaired は仮修理。** section を書き換えた仮説状態の ArchMap であり、
   `PASS_WITHIN_GATE_POLICY` が示すのは「この修理案なら貼り合う」という事前検証の機構である。
   修理が train-ticket に実装可能であること・実装されたことは実証していない。
3. **残差の実害規模は未計量。** 「丸め剰余が記帳されない」は静的に確実だが、実際に非零になるのは
   0.8×価格が2桁で割り切れない場合だけで、頻度・金額は測っていない(harmonic-debt を
   沈黙させたのはこのため)。
4. **presentation packet は authored input である。** source-grounded finite cell、relation 行列、
   generator map、restriction、equation lift atlas は実施者が供給した。generated なのは、
   それらからの `χ / Φ / κ`、exactness と quotient-level witness の導出である。
5. **供給 UX は未整備。** presentation cell を含む RepairPlan の authoring は builder を直接読む必要がある。
   ArchMap 供給における archmap-creater と同水準の抽象化(repair 対象のループを指せば
   artifact 一式が組み上がる SKILL)は未着手であり、本実験の builder スクリプトと供給所見2件が
   その設計素材になる。

## 体験所見(供給契約)

1. residual-class 認証は residual component ごとに行う。diagnostic triangle は triple cell を持たないため
   `C²=0` を明示した `automatic-c2-zero` を出力し、非連結な triple や supplied data に依存しない。
2. residual atom の refs は sources 解決必須。静的観測しか無い場合は src ファイル参照のみが正直な形。

## 証拠束と再現

- 入力: `evidence/saga/` — ArchMap 変種(head / repaired)、law surface / policy / profile /
  gate policy、repair-plan(head / repaired)、builder(`build_saga_artifacts.py`)。
  すべて一次出力の `inputDigests` と canonical digest 一致を検証済み
- 一次出力: `evidence/saga/out/`(head / repaired の analyze 出力、compare、gate ×2)
- 再現(2026-07-25 に runId・comparison code・gate 判定一致まで確認済み):

```bash
EV=docs/reports/train_ticket_dogfooding/evidence
C=tools/archsig/Cargo.toml
cargo run --manifest-path $C -- analyze \
  --archmap $EV/saga/archmap-saga-head.json \
  --law-policy $EV/saga/law-policy-saga.json \
  --law-surface $EV/saga/law-surface-saga.json \
  --measurement-profile $EV/saga/measurement-profile-saga.json \
  --repair-plan $EV/saga/repair-plan-head.json \
  --out-dir .tmp/reports-repro/saga-head
cargo run --manifest-path $C -- analyze \
  --archmap $EV/saga/archmap-saga-repaired.json \
  --law-policy $EV/saga/law-policy-saga.json \
  --law-surface $EV/saga/law-surface-saga.json \
  --measurement-profile $EV/saga/measurement-profile-saga.json \
  --repair-plan $EV/saga/repair-plan-repaired.json \
  --out-dir .tmp/reports-repro/saga-repaired
cargo run --manifest-path $C -- compare \
  --base-run .tmp/reports-repro/saga-head \
  --head-run .tmp/reports-repro/saga-repaired \
  --out-dir .tmp/reports-repro/saga-compare
cargo run --manifest-path $C -- gate \
  --packet .tmp/reports-repro/saga-head/archsig-measurement-packet.json \
  --policy $EV/saga/gate-policy-saga.json \
  --out .tmp/reports-repro/gate-head.json
cargo run --manifest-path $C -- gate \
  --packet .tmp/reports-repro/saga-repaired/archsig-measurement-packet.json \
  --policy $EV/saga/gate-policy-saga.json \
  --comparison .tmp/reports-repro/saga-compare/archsig-comparison-report.json \
  --out .tmp/reports-repro/gate-repaired.json
```
