# G-104 係数生成契約の考察 — 条件Cハント(#3912)の裁定とカード改訂の根拠

- 日付: 2026-08-07
- 位置づけ: Issue #3912(条件Cハント、off-loop 計算探索)の停止条件B判定を受理し、
  `research/goals/G-104-aat-resolution-invariance.md` を改訂するための設計根拠ノート。
- 依拠する artifact: `research/experiments/g104-condition-hunt/`(PR #3913)。
  off-loop 探索 artifact であり、本ノートも含め G-104 の完了根拠ではない。
  ハント結果は独立再現済み(回帰テスト5件、full run の `results.json` SHA-256 一致)。

## 1. ハントが確定させた事実

ハントの核心は探索結果ではなく、次の2点分離論法である。

同一の nerve・nerve 射・reading pair・Target 台の上で、係数データだけを変えた
3つの比較を作れる:

| データ | 比較写像 |
| --- | --- |
| 全 cell 係数次元1 | 同型 |
| fiber edge の係数次元だけ 0(support hole) | 非単射 |
| fine 側係数座標を2コピー(複製) | 非全射 |

条件Cの候補条項(C0–C5、self-loop endpoint reflection、Quillen A 型 comma-fiber、
face-mediated coherence を含む)はすべて incidence データと Target 台のみから
計算されるため、この3つを区別できない。したがって**係数を自由に宣言できる
モデルでは、incidence レベルの条件Cをどう強めても comparison map の同型性は
制御できない**。これは探索範囲に依存しない一般論法であり、停止条件B
(構造的否定)の判定は正当である。

同時にハントは、この否定が law 由来係数への反証ではないことを明記している。
複製や support hole が law descent から生成できるかは未確認である。

## 2. カードの現行語彙との対応 — 自由度はどこに実在するか

ハントの反例2種は、現行カードの入力語彙の中に対応する自由度を持つ。

1. **support hole ← 台の containment 宣言**。現行カードは nerve の台を
   「edge の台は端点 chart の台の交わり**に含まれる**、face の台は boundary
   edge の台の交わり**に含まれる**」と包含(⊆)で宣言させる。この自由度を使うと、
   端点の台を保ったまま fiber edge の台だけを空に宣言でき、係数次元 0 の
   support hole がカードの適法な入力として構成できる。条件Cは chart 台
   (C0)しか見ないため、これを検出できない。
2. **複製 ← 座標 basis の index 生成規則の未固定**。現行カードは law 由来係数を
   「descend した law evaluation が chart 台上に取る値から生成した座標 basis で
   張る」と書くが、basis の index 集合の生成規則を固定していない。細側だけ
   座標を二重に取る構成を排除する条項がどこにもない。

つまりハントの帰結は「条件Cの条項不足」ではなく「係数生成仕様の過小決定」であり、
是正は条件C側ではなく係数生成側に置くのが正しい。

## 3. 係数生成契約(K0 / K1)

改訂カードでは、law 由来係数の生成を次の2条項の契約として一次仕様化する。
(G-102 の「E1 と同水準の生成的構成」の E1 と紛れないよう K を使う。)

- **K0(座標 index の共有生成)**: 各 law の係数座標の index 集合は、descend した
  law evaluation が cell の台上に取る値から、粗側・細側で**同一の規則**により
  生成する。比較写像の座標対応は宣言せず、descend の π-可換
  (`ResearchLean/AG/ResolutionInvariance/ComparisonData.lean` の
  `lawDescend_comparisonFactor`)から生成する。宣言による座標の追加・複製・
  省略は認めない。
- **K1(cell 台の導出)**: edge の台は端点 chart の台の交わり**に等しい**、
  face の台は boundary edge の台の交わり**に等しい**とする(包含から等式へ)。
  宣言入力として残る台は chart 台だけであり、edge / face の台は導出データになる。

この契約の下で、ハントの反例2種は入力として構成不能になる(構成上の帰結であり、
追加の theorem を要さない): 複製は K0 が index 生成規則を両 reading で共有する
ため表現できず、support hole は K1 が edge / face 台を導出するため表現できない。

K0 の index 生成規則の Lean 上の具体形(値集合を index に取るか、law ごとに
値写像を係数化するか)は実装時に固定してよい。カードが要求するのは「両 reading で
同一規則」「比較対応は descend 可換から生成」「宣言自由度なし」の3点である。

なお ComparisonData.lean の `lawDescend` は law family の index(`laws.Law`)ごとに
canonical に生成され、`lawDescend_unique` で一意、`lawDescend_comparisonFactor` で
π-可換が theorem 化済みである。K0 はこの既存機構の係数複体側への延長であり、
新しい選択を持ち込まない。

## 4. 条件Cの改訂 — C6 の追加

`LoopLiftObstruction.lean`(三度目の反証)への応答として、ハントの Round 1 候補
`C*` の R 条項を C6 として条件Cに加える。

- **C6(self-loop endpoint reflection)**: 両端点が同一の粗側 chart に落ちる
  粗側 edge(self-loop)へ nerve 射の edge 対応で写る各細側 edge は、それ自身
  self-loop である(両端点が同一の細側 chart に落ちる)。

ハントの R 条項の文面は「一意な fine lift」を主語にするが、列挙器の実装
(`condition_hunt.py` の `R_self_loop_endpoint_reflection`)は self-loop へ写る
**すべての** nondegenerate lift を検査しており、C5 に依存しない。カードは実装側の
独立定式化を採る(C5 だけを外した条項独立性の検査が意味を持つため)。

根拠: C0–C5 だけでは、粗側 self-loop の一意 lift が同一 fiber 内の異なる chart を
結ぶことを許し、粗側 loop 類が細側で coboundary に落ちて非単射になる
(`comparisonH1Map_not_injective`)。C6 はこの機構を incidence レベルで塞ぐ。

ハントの定数座標層では、C0–C6 は bounded 全数探索(6,086件)で反例を持たず、
7条項の独立反例と手証明スケッチ(fiber 潰しの relative complex 経由)がある。
これは K0 / K1 の下での不変性 (ii) の証明可能性を示唆する参考情報であって
証明ではない。cell 台が非自明に変わる law 由来構成での C0–C6 の十分性は未証明
であり、それを判定するのが改訂後のループの仕事である。

## 5. カード改訂の項目対応

| 改訂箇所 | 内容 |
| --- | --- |
| comparison data | edge / face の台を包含宣言から導出(K1)へ |
| law 由来係数 | K0 / K1 を契約として明文化、比較対応の生成元を明記 |
| 条件C | C6 追加、(ii) 以下の参照を C0–C6 へ更新 |
| (v) 発火 witness | C6 の非空虚発火(粗側 self-loop の存在)を追加 |
| dullness filter | C6 が空虚成立するだけの発火を追加で弾く |
| proof strategy | LoopLiftObstruction を再利用 map に追加、ハント手証明スケッチを参考として記載 |
| premise ledger | `nerve / 台` と `law 由来係数の生成` の記述を K0 / K1 と同期 |
| anti-weakening | K0 / K1 の premise 化(座標対応や台の一致を仮定で受ける)を禁止 |
| frontier | 自由係数反例の law 実現可能性の判定を追加(実現可能なら (iv) 素材、不能なら K0 / K1 の裏付け) |

## 6. 残リスクと次の判定点

- **十分性のリスク**: K0 / K1 の下でも、chart 台が chart ごとに異なる構成で
  C0–C6 が不変性に足りない可能性は残る。その場合は failure policy に従い
  4度目の反証として条項改訂案を返す(cohomological 条項への差し替えは不可)。
- **発火可能性のリスク**: (v) に C6 非空虚発火(粗側 self-loop)を足すことで
  witness 構成が難化する。ハントの探索空間は self-loop を含み反例ゼロなので
  構成可能と見込むが、構成不能と判明した場合は (v) の当該項目だけを別 witness に
  分離する改訂を提案する。
- **K0 の具体化**: Lean 実装時に index 生成規則を固定した時点で、その規則が
  「選択の余地のない canonical な生成」であることをレビューで確認する
  (route integrity gate の provenance 追跡対象)。
