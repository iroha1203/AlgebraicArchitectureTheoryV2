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
  preserve–consign + preserve–order)、triple-overlap は宣言しない(三者同時照合サイトの不在は観測から読めない author assertion — 実証していないこと5)
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
自動成立する条件を表す。括弧書きの canonical anchor は本 report が Part X statement の
実読で再検証した帰属である(#3829)。凍結証拠束内の `theoremRef` は tool v0.5.4 の
記録値であり、enumeration completeness 行の記録値 `part10/3.1` は本表の裁定
(canonical 対応物なし)と異なる。tool 側の theoremRef 改訂は #3842 で扱い、
凍結済み artifact は変更しない。供給時代に `supplied` だった行(residual support、faithfulness law、
global sheaf condition、comparison cochain map、presentation packet)は、#3820–#3822 の返済で
導出化されるか、slot ごと沈黙した。沈黙した語彙は行ごと消えており、assumption ledger による
代替も置いていない。

| Condition | Kind | Status | Evidence |
| --- | --- | --- | --- |
| finite cover | finite artifact property | `checked` | head / repaired packet の `finite site` は `checked`、`siteCoverDigest` は normalized contexts・covers・derived finite cover nerve から `computed` |
| residual derivation | observed section comparison | `computed` | `saga-descent:residual-derivation` が overlap ごとに両端 chart の観測 sectionValue 集合を比較した F₂ 値と、法曲面 witness 束縛(`e_cancel_insidepay` 等)・観測 atom refs の provenance を記録する。head は三角形 3 辺+preserve 2 辺が mismatch |
| witness binding | law-surface declaration | `checked` | mismatch 辺は法曲面の witness variable 束縛を要求する(未束縛 mismatch は fail-closed で `not_computed`)。束縛は instance の値を運ばない edge 選択の宣言 |
| coefficient | law-side selection | `checked` | 係数は選択 MeasurementProfile の `coefficient: F2`。RepairPlan は係数を運ばない |
| repair-plan complex enumeration completeness(canonical anchor なし — 選択複体の列挙完全性は measurement 契約条件であり Part X に対応 statement を持たない) | author assertion | `assumed` | RepairPlan `complex.enumerationComplete: true` に対し、packet は `repair-plan complex enumeration completeness` を `assumed` と記録する |
| triple absence / class 語彙(part10/定義3.4 Semantic repair complex — `H¹_sem` は triple face を含む three-term complex 上で定義される) | author assertion | `assumed`(class 語彙は不解禁) | 選択複体は triple-overlap を宣言しない。「三者同時照合サイトの不在」はツールが観測できない author assertion であり、ArchSig は class 語彙を解禁せず(`saga-descent:class-vocabulary-boundary`、named boundary statement)、読みを 1-骨格の boundary membership に留める |
| boundary membership | finite F₂ calculation(part10/系4.5 Zero class と matching correction の δ⁰-可解性条項) | `computed` | head は `saga-descent:boundary-membership.inB1: false` と `MEASURED_NONGLUING_RESIDUAL`、repaired は `inB1: true`・`REPAIR_GLUES_WITHIN_SELECTED_COMPLEX` |
| U-adequate cover(part8/4.2) | profile-supplied assumption | `assumed` | 選択 cover の U-adequacy は profile 由来の assumption ledger 行 |
| Leray / acyclicity comparison(part8/B.8.2) | profile-supplied assumption | `assumed` | cover 相対の Čech 読みを層係数コホモロジーと比較するための前提。ledger 行として開示され、本 report はこの比較を主張しない |
| torsor / adjustment / coefficient descent(part4/11.1 ×3) | profile-supplied assumption | `assumed` | ledger の 3 行。局所法 section の Ob_U-torsor 性・作用の固定性・係数の descent |
| restriction surjectivity(part4/12.4) | profile-supplied assumption | `assumed` | ledger 行 |
| forest nerve(part4/12.4) | profile-supplied assumption | `assumed`(**本 packet では不成立**) | ledger は `selected Cech nerve is a forest with no triple-overlap faces` を assumed と記録するが、同じ packet の nerve 計算は forest ではない(閉路 1)ことを computed で示す。この profile 由来行は当 run では成立していない前提の開示であり、head の非零読みはこの行に依存しない |
| quotient sheaf condition(part10/系8.3 Equation-side global lift の仮定「`P_E` も選ばれた topology 上の sheaf」) | law-surface declaration | `assumed` | law surface の `quotientSheafCondition: assumed` を ledger 行として開示 |
| residual class agreement(head↔repaired) | derived run-pair reading | `computed` | compare の `residualClassAgreement` は両 run の導出 residual の差 δ⁰h 可解性を comparability ゲート下で計算する。本対は `not_cohomologous`(field 語彙であり class 語彙の解禁ではない。読みは run 対の residual 差の δ⁰ 非可解)。修理成功の読みは repaired 側の `inB1: true` と gate が担う |
| repaired ArchMap | hypothetical repair input | `supplied` / hypothetical | `archmap-saga-repaired.json` は BigDecimal scale-2 HALF_EVEN 統一を表す仮説 variant。`PASS_WITHIN_GATE_POLICY` は実装済み修理を示さない |
| runtime monetary magnitude | empirical measurement | unmeasured | harmonic-debt を供給せず沈黙。頻度・金額を結論に含めない |

## 結果(診断階段)

| 幕 | 結果 |
| --- | --- |
| head analyze | `MEASURED_NONGLUING_RESIDUAL`(`run:78c31d6a3172`) |
| └ grounding | `measured_zero` — 各チャートは自分の法を守っている(それが罠) |
| └ residual derivation | 三角形 3 辺+preserve 2 辺で mismatch、consign–consign-price は一致(全て観測から導出) |
| └ descent boundary membership | `measured_nonzero`(単一連結成分。triple 宣言不在のため class 語彙は不解禁 — named boundary statement で明示) |
| gate head | `BLOCKED_BY_GATE_POLICY` |
| repaired analyze | `REPAIR_GLUES_WITHIN_SELECTED_COMPLEX`(`run:6685bab8db21`。preserve 残差は B¹ 内) |
| compare head→repaired | `MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE`、`residualClassAgreement: not_cohomologous` |
| gate repaired | `PASS_WITHIN_GATE_POLICY` |

harmonic-debt は runtime 実測数値が無いため供給せず、沈黙(供給する場合は実走の払い戻し照合が必要)。

## 実証したこと

1. **AAT 中心主張の実データ着地**: 非零類の成立条件が「3流儀の衝突」だけでなく
   「三者同時照合サイトの不在」だったこと。各チャート単独は完全に筋の通った金額の扱いをしており
   (grounding = `measured_zero` が計測でそれを言う)、ペアごとの受け渡しも各々は成立している。
   障害はループを一周したときだけ現れ、それを埋める面(triple)がコードに存在しない。
   ツールの読みは選択 1-骨格上の boundary membership(非境界 residual)であり、
   類語彙は triple 宣言不在のため解禁されない(実証していないこと5)。
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
   既に行っていた。導出化後の SAGA 段が足したのは、同じ観測を選択 1-骨格上の boundary
   membership として読む descent 読解、grounding の罠の明示、修理計画の事前検証、run 対の
   residual class agreement、gate の一貫した診断であって、「SAGA が新しい障害を発見した」
   という主張は過大である。
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
5. **class 語彙は解禁していない。** 「三者同時照合サイトの不在」(`U_ijk` 空)はツールが
   観測できない author assertion である。成分 1-骨格に三角形が存在する本ケースでは、
   ArchSig は class 語彙を出さず(named boundary statement で明示)、読みを boundary
   membership に留めた。class 語彙が立つのは triple を宣言して cocycle パリティ検査が
   実際に走る場合だけである(condition matrix の該当行を参照)。

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

## 訂正(2026-07-26、Issue #3830)

本文はマージ時点の記録として凍結し、次を訂正する。

- triple overlap が宣言されていないため、本証拠束が計測した head の結果は、選択 1-骨格における
  `MEASURED_NONGLUING_RESIDUAL` と `saga-descent:boundary-membership.inB1: false` である。
  本文中の「非零 F₂ 残差類」「H¹」「非零類」「類は零」「residual-class」および同趣旨の表現は、
  本証拠束から導出された class / cohomology claim として読まない。
- v0.5.6 の run 対 artifact は `residualDifferenceReading` を用いる。本対の status は
  `difference_not_in_B1` であり、両 run の導出 residual の差が共有 overlap complex の
  `B¹` に入らないことだけを記録する。本文中の `residualClassAgreement`、
  `not_cohomologous`、`residual class agreement` はこの読みへ置き換える。
- #3830 では既存 head / repaired run を入力に compare と repaired gate を再計測した。
  `archmap-diff.json`、run-local analyze 出力、head gate は不変で、compare の field / status /
  schema / theoremRef と repaired gate の comparison digest だけを更新した。
