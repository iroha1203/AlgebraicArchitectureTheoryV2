# SAGA フル診断階段: 実在 one-cent 三角形の非零類 → BLOCKED → repair 事前検証 → PASS

## 実験概要

- **対象**: フルビルド成果物(money 変種 ArchMap)を土台に、law を SAGA フルスタックへ拡張し、
  train-ticket(commit `313886e99bef`)の実データで診断階段を一周した
- **実施日**: 2026-07-19(JST)
- **実施主体・モデル**: Claude 直接(Fable)。典拠確認には同一 commit の shallow 再取得を使用
- **対応 Issue**: #3545(第2コメントが起草時の一次記録、第3コメントに実施者所見メモ)

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

- cover `cover:money-settlement-loop`(6チャート): 三角形 {cancel, inside-payment, order} +
  託送料金領域 {preserve, consign, consign-price}
- law surface 3本: `surface:cech-surface-v052`(closed-equational、witness 4辺)/
  `law:money-settlement-convention`(ag.saga-grounded、skeleton 6頂点 + defectSources)/
  `law:money-repair-descent`(descent、ag.saga-descent)
- repair-plan: overlaps 6(三角形3 + 託送3)。triple は託送料金領域のみ(preserve の予約で
  consign が consign-price から料金取得・記帳する実フロー、無ドリフト)、
  zero-primitive = consign–consign-price、residual 変数 `drift:refund-rounding` を三角形3辺に supply
- repaired 変種: 三角形3チャートを BigDecimal scale-2 HALF_EVEN 統一規約に置換した仮修理 ArchMap

## 結果(診断階段)

| 幕 | 結果 |
| --- | --- |
| head analyze | `MEASURED_NONGLUING_RESIDUAL_CLASS`(`run:7a94d68ac5d7`) |
| └ grounding | `measured_zero` — 各チャートは自分の法を守っている(それが罠) |
| └ descent 残差類 | `measured_nonzero`(inB1: false、三角形3辺 support) |
| └ comparison h1-transfer | `established` |
| gate head | `BLOCKED_BY_GATE_POLICY` |
| repaired analyze | `REPAIR_GLUES_WITHIN_SELECTED_COMPLEX`(`run:1f657023d7e8`) |
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
2. **診断階段の全段が実データで機能**: 非零類の計測 → gate BLOCKED → 修理計画の事前検証 →
   compare による障害消滅の記録 → gate PASS まで、一貫した artifact 契約の下で一周した。
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
4. **zero-triple の充足は診断三角形と非連結。** class 認証(非空 tripleOverlaps、cocycle-zero)は
   託送料金領域の正直な実フローで充足したが、この triple は診断対象の三角形と complex 上で
   非連結であり、診断には寄与していない。認証が「どこかに triple があること」しか要求しない現状の
   検査力は設計論点として記録する。
5. **供給 UX は未整備。** tripleOverlaps 要件の把握に evaluator の Rust ソース読解を要した。
   ArchMap 供給における archmap-creater と同水準の抽象化(repair 対象のループを指せば
   artifact 一式が組み上がる SKILL)は未着手であり、本実験の builder スクリプトと供給所見2件が
   その設計素材になる。

## 体験所見(供給契約)

1. residual-class 認証は非空 tripleOverlaps(cocycle-zero)が必須。ドリフトの立つ三角形自体は
   triple にできないため、実データでは「無ドリフトの正直な triple」を実フローから別途発掘する
   必要がある。見つからないコードベースでは residual-class 段は沈黙で終わる。
2. residual atom の refs は sources 解決必須。静的観測しか無い場合は src ファイル参照のみが正直な形。

## 証拠束と再現

- 入力: `evidence/saga/` — ArchMap 変種(head / repaired)、law surface / policy / profile /
  gate policy、repair-plan(head / repaired)、builder(`build_saga_artifacts.py`)。
  すべて一次出力の `inputDigests` と canonical digest 一致を検証済み
- 一次出力: `evidence/saga/out/`(head / repaired の analyze 出力、compare、gate ×2)
- 再現(2026-07-19 に runId・gate 判定一致まで確認済み):

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
  --out .tmp/reports-repro/gate-head.json   # BLOCKED は非零 exit code
cargo run --manifest-path $C -- gate \
  --packet .tmp/reports-repro/saga-repaired/archsig-measurement-packet.json \
  --policy $EV/saga/gate-policy-saga.json \
  --comparison .tmp/reports-repro/saga-compare/archsig-comparison-report.json \
  --out .tmp/reports-repro/gate-repaired.json
```
