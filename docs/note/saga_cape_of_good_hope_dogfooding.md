# SAGA の喜望峰到達 — train-ticket ドッグフーディング成果ノート

_作成: 2026-07-19 / ドッグフーディング第2段(Issue #3545)の成果記録と解釈。実測の正本は
[Issue #3545 コメント](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/3545)、
本ノートはその意味づけを固定する設計考察ノートである。_

関連:

- [SAGA 定理 proof record](aat_saga_theorem_proof_record.md) — Lean proved の側
- 数学本文 第X部・第III部 §11(SAGA 診断階段の理論)
- one-cent drift デモ(`tools/archsig/examples/practical-rust-service`、PR #3592)— 合成例の側
- Issue #3545 — フルビルド実測と体験所見の一次記録

---

## 問い

**SAGA 定理の前提を満たす構造は、誰も AAT を知らずに書いた現実のコードに実在するか。**

SAGA 連鎖(局所合法 + 貼り合わせデータ + 面の欠落 + 奇パリティ → 非零残差類)は
Lean proved であり、真であることは形式化の時点で確定している。形式化された定理の残る
リスクは偽であることではなく**空虚であること** — 前提を満たす対象が数学の中にしか
存在しないこと — である。one-cent デモは「この構造なら H¹ が立つ」の実演だったが、
その構造が現実に生じるかは別の問いであり、実データでしか答えられない。

## 発見: one-cent 構造は実在する

対象は FudanSELab/train-ticket(commit 313886e9、フルビルド #3545 と同一 checkout)。
money 変種 ArchMap(24 contexts)の実呼び出しグラフ上で、
**cancel–inside-payment–order の実三角形**が次の構造を持つ:

| チャート | 金額規約(実ソース典拠) |
| --- | --- |
| ts-cancel-service | `Double.parseDouble(order.getPrice()) * 0.8` → `DecimalFormat("0.00")` で丸めて文字列化(`CancelServiceImpl.calculateRefund`) |
| ts-inside-payment-service | `new BigDecimal(order.getPrice())` の正確算術(`InsidePaymentServiceImpl`) |
| ts-order-service | `private String price` の素通し保管(`Order.java`) |

3流儀が三角形の3辺すべてで衝突し(奇パリティ)、かつ
**3サービスの金額を同時に照合するサイトがコード上に存在しない**(triple overlap が
正直に空 = 面の欠落)。したがって非零 F₂ 残差類が立つ。払い戻しの丸め剰余
(0.8×価格の1セント未満)はどのチャートにも記帳されていない。

重要なのは、この構造をこちらが仕込んでいないことである。デモでは設計した前提の束が、
普通のマイクロサービスの普通の実装判断の積み重ねとして既に存在していた。

## 計測: 診断階段のフル一周

law を SAGA フルスタック(cech law + saga-grounded law + descent law、
cover `money-settlement-loop` 6チャート)へ拡張し、階段を一周した:

| 幕 | 結果 |
| --- | --- |
| head analyze | `MEASURED_NONGLUING_RESIDUAL_CLASS` |
| └ grounding | `measured_zero` — 各チャートは自分の法を守っている(それが罠) |
| └ descent 残差類 | `measured_nonzero`(inB1: false) |
| └ comparison h1-transfer | `established` |
| gate head | `BLOCKED_BY_GATE_POLICY` |
| repaired analyze(BigDecimal scale-2 統一の仮修理) | `REPAIR_GLUES_WITHIN_SELECTED_COMPLEX` |
| compare head→repaired | `MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE` |
| gate repaired | `PASS_WITHIN_GATE_POLICY` |

zero-triple(residual-class 認証に必要な無ドリフト三重領域)は
preserve–consign–consign-price の託送料金領域(実フロー)で充足した。
harmonic-debt は runtime 実測数値が無いため供給せず、正直に沈黙させた。

## 解釈: 何が確かめられたか

1. **前提の実在証明。** SAGA 定理の前提空間に現実のコードが住んでいる。定理は
   「証明済みだが実例は合成のみ」から「証明済みで実例が野生に在る」へ移った。
2. **忠実性契約の耐久試験。** 計測器が敵対的な実データに初めて触れ、含意の連鎖
   (grounding zero → 残差類非零 → 修理で貼り合う)が Lean 側の連鎖と同じ順序・
   同じ条件で発火した。ツールの拒否もすべて正当だった(ドリフト三角形の triple 申告は
   cocycle 条件で拒否される、典拠なき residual ref は fail する)。
3. **定理の教訓の最小実例。** 「全チャートが局所的に正しくても大域は貼り合わない、
   そしてそれはどの一箇所のせいでもない」という SAGA の核心が、grounding =
   `measured_zero` と残差類非零の同時成立として計測の言葉で観測された。

## 名前について

喜望峰の発見が意味したのは「インドに着いた」ではなく「この航路は実在する」だった。
本成果も同じである: 製品価値(実務エンジニアにとっての有用性)にはまだ達していないが、
AAT という航路が数学の中だけの海ではなく、現実のコードという海につながっていることが
自分の目で確認された。発見物そのものは1セント未満の丸め剰余という嵐のように地味な
代物であり、価値の本体は発見物ではなく航路への希望にある(嵐の岬が喜望峰と
改名された理由と同じ)。

## 境界(このノートが主張しないこと)

- **SAGA が新しい障害を検出したのではない。** 規約 mismatch の検出自体は cech 段
  (フルビルドの money run)が既に行っていた。SAGA 階段が足したのは、grounding の罠の
  明示・修理計画の事前検証・h1-transfer・gate という診断の物語であり、residual 供給は
  authored model である。
- **repaired は仮修理。** section を書き換えた仮説状態であり、PASS が示すのは
  「この修理案なら貼り合う」という事前検証の機構であって、修理の実装可能性ではない。
- **残差の実害規模は未計量。** 「剰余が記帳されない」は静的に確実だが、実際に非零に
  なる頻度・金額は測っていない(harmonic-debt の沈黙はこの規律の帰結)。
- zero-triple は complex 上で三角形と非連結であり、診断には寄与していない。class 認証
  ゲートが構造的に無関係な triple で充足できることは検査の弱さの可能性として
  記録する(設計論点、Issue #3545 所見参照)。

## 航路の続き

岬の先の海は**供給の UX**である。本 run では evaluator の Rust ソースを読んで供給契約
(非空 tripleOverlaps、residual ref の sources 解決など)を突き止めたが、これは実ユーザーに
要求できる手順ではない。

- SAGA 供給の SKILL 化(archmap-creater と同じ抽象化: repair 対象のループを指せば
  artifact 一式が組み上がる)。本 run の builder スクリプトと所見2件が設計素材
- 鍵収束 PRD の続き(AC1 ゲート裁定)と、外部 OSS ドッグフーディング
- ArchSig 記事は本 run を中心素材に据える(前提の実在証明という観点)

成果物(archmap 変種・law 一式・repair-plan・全出力)はローカル scratchpad にあり
コミットしない。正本記録は Issue #3545 コメント、意味づけは本ノートで固定する。
