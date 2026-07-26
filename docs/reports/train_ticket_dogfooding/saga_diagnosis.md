# SAGA フル診断階段: 導出 residual の one-cent 類 → BLOCKED → repair 事前検証 → PASS

## 実験概要

- **対象**: フルビルド成果物(money 変種 ArchMap)を土台に、law を SAGA フルスタックへ拡張し、
  train-ticket(commit `313886e99bef`)の実データで診断階段を一周した
- **再計測日**: 2026-07-26(JST、供給 slot の沈黙化後、導出 residual の入力面で再計測)
- **実施主体・モデル**: Claude 直接(Fable)。典拠確認には同一 commit の shallow 再取得を使用
- **対応 Issue**: #3822(residual 導出は #3820、repair cochain 導出は #3821 を前提にする)
- **入力面**: RepairPlan v0.5.7 は選択複体(charts / overlaps / enumerationComplete)だけを宣言する。
  residual は analyze が観測(選択 cover の cech sectionValue 比較)と法曲面の witness 束縛から導出し、
  provenance を `saga-descent:residual-derivation` に記録する。residual・係数・faithfulness・
  certificate・comparison・grounding の供給 slot はすべて退役した(#3817 返済系列)

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
- law surface 3本: `surface:cech-surface-v052`(closed-equational、witness 6辺)/
  `law:money-settlement-convention`(ag.saga-grounded、skeleton 6頂点 + defectSources)/
  `law:money-repair-descent`(descent、ag.saga-descent)
- repair-plan(v0.5.7): 選択複体だけを宣言する。charts は観測 cover の 6 チャートそのもの、
  overlaps は観測された restriction 6 辺(三角形 3 + consign–consign-price +
  preserve–consign + preserve–order)、triple-overlap は観測に存在しないので宣言しない
- 導出 residual(head): 三角形 3 辺と preserve 2 辺で sectionValue が不一致、
  consign–consign-price は一致。三角形一周の奇パリティは δ⁰ で解けず、類が非零に立つ
- repaired 変種: 三角形3チャートを BigDecimal scale-2 HALF_EVEN 統一規約に置換した仮修理 ArchMap。
  残る preserve 残差は δ⁰(preserve のみ反転)で解けるため類は零

## 条件種別と residual の来歴

residual は author が書く入力ではない。analyze が観測(選択 cover の cech sectionValue 比較)と
法曲面の witness 束縛から導出し、`saga-descent:residual-derivation` に辺ごとの値・witness・
観測 atom refs の provenance を記録する。ここでいう `computed` / `checked` / `assumed` /
`automatic` は、その導出と検査の種別を表す。head / repaired の両 packet で同じ区別を記録した。

### #3781 §7 用 condition matrix

次表は #3781 が §7 の本文へ転記するための行別の正本である。`assumed` は author が宣言し
packet が assumption ledger に記録する前提、`computed` は入力からの有限計算、`checked` は
ArchSig が有限 artifact に対して検査した条件、`automatic` は selected complex の形から
自動成立する条件を表す。供給時代に `supplied` だった行(residual support、faithfulness law、
global sheaf condition、comparison cochain map、presentation packet)は、#3820–#3822 の返済で
導出化されるか、slot ごと沈黙した。沈黙した語彙は行ごと消えており、assumption ledger による
代替も置いていない。

| Condition | Kind | Status | Evidence |
| --- | --- | --- | --- |
| finite cover | finite artifact property | `checked` | head / repaired packet の `finite site` は `checked`、`siteCoverDigest` は normalized contexts・covers・derived finite cover nerve から `computed` |
| residual derivation | observed section comparison | `computed` | `saga-descent:residual-derivation` が overlap ごとに両端 chart の観測 sectionValue 集合を比較した F₂ 値と、法曲面 witness 束縛(`e_cancel_insidepay` 等)・観測 atom refs の provenance を記録する。head は三角形 3 辺+preserve 2 辺が mismatch |
| witness binding | law-surface declaration | `checked` | mismatch 辺は法曲面の witness variable 束縛を要求する(未束縛 mismatch は fail-closed で `not_computed`)。束縛は instance の値を運ばない edge 選択の宣言 |
| coefficient | law-side selection | `checked` | 係数は選択 MeasurementProfile の `coefficient: F2`。RepairPlan は係数を運ばない |
| repair-plan complex enumeration completeness | author assertion | `assumed` | RepairPlan `complex.enumerationComplete: true` に対し、packet は `repair-plan complex enumeration completeness` を `assumed` と記録する |
| triple absence / cocycle 条件 | selected complex shape | `automatic` / `assumed` | 選択複体に triple-overlap が無いので selected `C²=0`、cocycle 条件は自動成立(`certificateKind: automatic-c2-zero` / `cocycle.checked: false`)。「三者同時照合サイトの不在」自体は観測事実だが、成分の 1-骨格にグラフ三角形が存在する場合でも triple 宣言不在なら自動認証となる点は author assertion(`U_ijk` 空)に依存する |
| boundary membership / residual class | finite quotient calculation | `computed` | head は `saga-descent:boundary-membership.inB1: false` と `MEASURED_NONGLUING_RESIDUAL_CLASS`、repaired は零類・`REPAIR_GLUES_WITHIN_SELECTED_COMPLEX` |
| residual class agreement(head↔repaired) | derived run-pair reading | `computed` | compare の `residualClassAgreement` は両 run の導出 residual の差 δ⁰h 可解性を comparability ゲート下で計算する。本対は `not_cohomologous`(修理は類を非零→零に変える)。修理成功の読みは repaired 側の零 residual と gate が担う |
| repaired ArchMap | hypothetical repair input | `supplied` / hypothetical | `archmap-saga-repaired.json` は BigDecimal scale-2 HALF_EVEN 統一を表す仮説 variant。`PASS_WITHIN_GATE_POLICY` は実装済み修理を示さない |
| runtime monetary magnitude | empirical measurement | unmeasured | harmonic-debt を供給せず沈黙。頻度・金額を結論に含めない |

## 結果(診断階段)

| 幕 | 結果 |
| --- | --- |
| head analyze | `MEASURED_NONGLUING_RESIDUAL_CLASS`(`run:fd1b393a80e6`) |
| └ grounding | `measured_zero` — 各チャートは自分の法を守っている(それが罠) |
| └ residual derivation | 三角形 3 辺+preserve 2 辺で mismatch、consign–consign-price は一致(全て観測から導出) |
| └ descent 残差類 | `measured_nonzero`(単一連結成分、`automatic-c2-zero`) |
| gate head | `BLOCKED_BY_GATE_POLICY` |
| repaired analyze | `REPAIR_GLUES_WITHIN_SELECTED_COMPLEX`(`run:f9666ddb2aca`。preserve 残差は B¹ 内) |
| compare head→repaired | `MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE`、`residualClassAgreement: not_cohomologous` |
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
2. **診断階段の全段が二系統入力だけで機能**: 観測(ArchMap)と法・方程式(law surface /
   profile)から導出した residual による非零類の計測 → gate BLOCKED → 修理計画(repaired
   ArchMap)の事前検証 → compare による障害消滅の記録と residual class agreement → gate PASS
   まで、authored な residual・証書・比較データを一切供給せずに一周した。
3. **数学的規律の拒否が正しく働いた**: ドリフトの立つ三角形自体を triple として申告すると
   cocycle 条件で拒否される(数学的に正当)。典拠の無い residual ref は fail した
   (初回 run は未解決 ref で正しく失敗)。実データで負荷をかけて規律が守られた。
4. **語れないことへの沈黙**: harmonic-debt は runtime 実測が無い状態では供給せず沈黙した。

## 実証していないこと

1. **検出の新規性は cech 段にある。** 規約 mismatch の検出自体はフルビルドの cech law が
   既に行っていた。導出化後の SAGA 段が足したのは、同じ観測を選択複体上の residual class として
   読む descent 読解、grounding の罠の明示、修理計画の事前検証、run 対の residual class
   agreement、gate の一貫した診断であって、「SAGA が新しい障害を発見した」という主張は過大である。
2. **repaired は仮修理。** section を書き換えた仮説状態の ArchMap であり、
   `PASS_WITHIN_GATE_POLICY` が示すのは「この修理案なら貼り合う」という事前検証の機構である。
   修理が train-ticket に実装可能であること・実装されたことは実証していない。
   また repaired 側にも preserve 系の実 mismatch が残る(B¹ 内なので類は零)。
3. **残差の実害規模は未計量。** 「丸め剰余が記帳されない」は静的に確実だが、実際に非零になるのは
   0.8×価格が2桁で割り切れない場合だけで、頻度・金額は測っていない(harmonic-debt を
   沈黙させたのはこのため)。
4. **定理5.1 の有限 instantiation は本証拠束の対象外である。** presentation packet /
   comparison slot は #3822 で沈黙し、有限 instantiation の家は Lean(`Formal/`)である。
   供給時代の presentation 検査(#3805 の整数係数 exactness / generation 負例)は
   git 履歴と当時の報告に記録が残る。
5. **automatic-c2-zero は triple 宣言不在に相対的である。** 「三者同時照合サイトの不在」は
   観測事実だが、selected complex に triple を宣言しない限り cocycle 条件は自動成立として
   扱われる。成分 1-骨格に三角形が存在する本ケースでは、この自動性は author の
   `U_ijk` 空 assertion に依存する(condition matrix の該当行を参照)。

## 体験所見(導出契約)

1. residual-class の読みは residual support component ごとに行う。導出 residual が
   preserve 辺で複数成分を接続したため、本再計測では選択複体全体が単一成分になった。
2. mismatch 辺の witness 束縛は法曲面の宣言であり、束縛が無い mismatch は fail-closed に
   `not_computed` へ落ちる。観測を広げるときは法曲面の witness も同時に広げる。

## 証拠束と再現

- 入力: `evidence/saga/` — ArchMap 変種(head / repaired)、law surface / policy / profile /
  gate policy、repair-plan(head / repaired)、builder(`build_saga_artifacts.py`)。
  すべて一次出力の `inputDigests` と canonical digest 一致を検証済み
- 一次出力: `evidence/saga/out/`(head / repaired の analyze 出力、compare、gate ×2)
- 再現(2026-07-26 に head 一次出力の byte 一致を確認済み。`inputDigests` は `input:` 安定 ref を
  使うため out-dir の場所に依存しない)。`gate` は BLOCKED のとき非零 exit code を返すので、
  `set -e` 下では途中停止する:

```bash
EV=docs/reports/train_ticket_dogfooding/evidence
C=tools/archsig/Cargo.toml
cargo run --manifest-path $C -- analyze \
  --archmap $EV/saga/archmap-saga-head.json \
  --law-policy $EV/saga/law-policy-saga.json \
  --law-surface $EV/saga/law-surface-saga.json \
  --measurement-profile $EV/saga/measurement-profile-saga.json \
  --repair-plan $EV/saga/repair-plan-head.json \
  --out-dir .tmp/reports-repro/head
cargo run --manifest-path $C -- analyze \
  --archmap $EV/saga/archmap-saga-repaired.json \
  --law-policy $EV/saga/law-policy-saga.json \
  --law-surface $EV/saga/law-surface-saga.json \
  --measurement-profile $EV/saga/measurement-profile-saga.json \
  --repair-plan $EV/saga/repair-plan-repaired.json \
  --out-dir .tmp/reports-repro/repaired
cargo run --manifest-path $C -- compare \
  --base-run .tmp/reports-repro/head \
  --head-run .tmp/reports-repro/repaired \
  --out-dir .tmp/reports-repro/compare
cargo run --manifest-path $C -- gate \
  --packet .tmp/reports-repro/head/archsig-measurement-packet.json \
  --policy $EV/saga/gate-policy-saga.json \
  --out .tmp/reports-repro/gate-head.json
cargo run --manifest-path $C -- gate \
  --packet .tmp/reports-repro/repaired/archsig-measurement-packet.json \
  --policy $EV/saga/gate-policy-saga.json \
  --comparison .tmp/reports-repro/compare/archsig-comparison-report.json \
  --out .tmp/reports-repro/gate-repaired.json
```
