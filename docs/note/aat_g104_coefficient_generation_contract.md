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
計算されるため、この3つを区別できない。したがって、**非退化正例を一つでも
受理する incidence-only の条件Cは、係数を自由に宣言できるモデルでは、その
正例と同一 incidence の係数変更例(複製・support hole)との区別に失敗する**。
これは「無条件にいかなる条件も不可能」ではなく条件付き no-go だが、非退化
正例の受理はカードの (v) が要求する成功条件なので、目的に対しては十分な
否定である。探索範囲に依存しない一般論法であり、停止条件B(構造的否定)の
判定は正当である。

同時にハントは、この否定が law 由来係数への反証ではないことを明記している。
複製や support hole が law descent から生成できるかは未確認である。

## 2. カードの現行語彙との対応 — 自由度はどこに実在するか

ハントの反例2種は、現行カードの入力語彙の中に対応する自由度を持つ。

1. **support hole**。ハント artifact の support hole は Target 台とは別層の
   係数座標台(`SupportedNerve` の `edge_supports`)に置かれており、Round 2 の
   3 fixture の Target 台はすべて全域である(このノートの初版は帰属を Target
   台側と誤記していた。Codex レビュー P1-2 で是正)。カードの語彙では係数
   次元は cell の台上の descend 値から生成されるため、同じ機構は二つの経路で
   現れる: (a) 台の containment 宣言(⊆)で fiber edge の台だけを空に宣言
   する経路(K1 で閉じる)、(b) K1 の導出台の下でも、粗側 chart の値を複数の
   細側 chart へ分配すると fiber 内 edge の導出台(交わり)が空になる経路
   (**K1 では閉じない**。§5)。条件Cは chart 台(C0)しか見ないため、
   どちらも検出できない。
2. **複製 ← 座標 basis の index 生成規則の未固定**。現行カードは law 由来係数を
   「descend した law evaluation が chart 台上に取る値から生成した座標 basis で
   張る」と書くが、basis の index 集合の生成規則を固定していない。細側だけ
   座標を二重に取る構成を排除する条項がどこにもない。

つまりハントの帰結は「条件Cの条項不足」ではなく「係数生成仕様の過小決定」で
あり、是正は二層になる: 宣言自由度に由来する機構(複製、台宣言による hole)は
係数生成側(K0 / K1)で潰し、K1 の導出台の下でも残る値分配由来の derived hole
は条件C側の座標 subnerve 相対化(§5)で扱う。

## 3. 係数生成契約(K0 / K1)

改訂カードでは、law 由来係数の生成を次の2条項の契約として一次仕様化する。
(G-102 の「E1 と同水準の生成的構成」の E1 と紛れないよう K を使う。)

- **K0(座標 index の固定)**: 各 cell の係数座標の index 集合は対 `(law, 値)`
  の集合とする。`値` は descend した当該 law evaluation がその cell の台
  (K1 の導出台)上に取る**相異なる値**であり、値の Target 上の出現回数や
  台の要素数を index にしない(多重度は値ごとに1)。比較写像の座標対応は
  宣言せず、`(law, 値)` 上の恒等対応として descend の π-可換
  (`ResearchLean/AG/ResolutionInvariance/ComparisonData.lean` の
  `lawDescend_comparisonFactor`)から生成する。宣言による座標の追加・複製・
  省略は認めない。係数体(`ℚ` 固定)・関数空間・restriction / differential・
  block 分解まで含めた生成契約の完結形は、§5 の追加是正とカード本文を正と
  する。
- **K1(cell 台の導出)**: edge の台は端点 chart の台の交わり**に等しい**、
  face の台は boundary edge の台の交わり**に等しい**とする(包含から等式へ)。
  宣言入力として残る台は chart 台だけであり、edge / face の台は導出データになる。

この契約の下で、複製は K0 が多重度を値ごとに1へ固定するため構成不能になり、
台宣言による support hole は K1 が edge / face 台を導出するため構成不能になる。
ただし K0 / K1 だけでは十分でない: 値の分配による導出 support hole が残る
(§5。条件C側の相対化で対処する)。

なお、このノートの初版は K0 を「両 reading で同一の生成規則」とだけ要求し、
具体形(値集合か値写像か)を実装時選択に残していた。Codex レビュー P1-1 が
この選択で真偽が分岐することを示した: 「値の Target 上の出現回数を index に
取る」規則も"同一規則"だが、π で潰れる粗側 target に対して細側の出現が複数に
なり、ハントの複製反例と同じ機構で非全射になる。index 対象は上記のとおり
`(law, 相異なる値)` へ数学的に固定した(definitional escape の余地を残さない)。

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

## 5. Codex レビュー(PR #3915)と条件Cの値ごと相対化

固定 head 261a4c9a への Codex 独立レビュー(Major revisions)は、K0 の
真偽分岐(P1-1、§3 で是正)に加え、**K1 では閉じない導出 support hole**
(P1-2)を有限反例で示した: K1 の導出台と `(law, 相異なる値)` index の
最直接の canonical 具体化の下でも、粗側 chart の値を複数の細側 chart へ
分配すると、C0(合併条件)と C1(incidence fiber 連結)は成立したまま
fiber 内 edge の導出台が空になり、comparison map が非単射になる。
Claude も exact engine 上で独立再現した。再計算可能な全データを次に固定する
(committed engine `research/experiments/g104-condition-hunt/condition_hunt.py`
の `SupportedNerve` / `analyze_supported_h1` / `condition_vector` を使用。
係数体は `ℚ`):

- incidence: `supported_incidence_morphism()`(coarse: 3 chart / 5 edge /
  1 face、fine: 4 chart / 6 edge / 1 face、`vertex_map = (0,0,1,2)`、
  `edge_map = (none,0,1,2,3,4)`、`face_map = (0,)`。fine edge 0 =
  fiber 内 edge)
- 係数座標(値)宇宙: {a, b}。coarse 側は全 cell 台 {a, b}
  (`full_supported_nerve(coarse, coordinate_count=2)`)
- fine chart 台: chart 0 = {a}、chart 1 = {b}、chart 2 = {a, b}、
  chart 3 = {a, b}(coarse chart 0 の fiber = {0, 1} へ値を分配。
  `π`-像の合併 = {a, b} = coarse chart 0 の台で C0 成立)
- K1 導出: fine edge 台 = 端点台の交わり = (∅, {a}, {a}, {a,b}, {b}, {a})、
  fine face(boundary = edge 1,2,3)台 = {a}。fiber 内 edge の導出台が空
  (derived support hole)
- `coordinate_map = (0, 1)`(K0 の `(law, 値)` 恒等対応)
- 結果: C0(値合併)成立、C1–C6 は**改訂前の whole-nerve 条件として評価して
  全成立**(この incidence に self-loop はなく C6 は空虚)、
  coarse `dim H¹` = 4 / fine `dim H¹` = 1 / comparison rank = 1、非単射
- 相対化後の判定: a-subnerve では coarse edge 3(唯一の lift = fine edge 4、
  台 {b})が subnerve 内 lift を欠き C2 が破れる。b-subnerve では
  coarse edge 0(唯一の lift = fine edge 1、台 {a})で同様に C2 が破れる。
  よって相対化した C はこの例を受理しない

Codex の fixture は self-loop / face / fiber edge を含み C0–C6 が非空虚に
発火する変種で、coarse `dim H¹` = 2 / fine `dim H¹` = 1 / rank 1 の非単射
(機構は同一)。

是正は条件C側の再定式化で行う(ユーザー裁定 2026-08-07):

- 係数の restriction と比較の係数写像は K0 により座標ごとの零 / 恒等写像
  なので、`H^1` と comparison map は係数座標 `(law, 値)` ごとの block へ
  直和分解する。
- 各 block は、その座標を持つ cell が成す**座標 subnerve** 上の定数係数
  (1次元)比較にちょうど還元される。
- したがって条件Cが本来語るべき対象は座標 subnerve であり、**C1–C4 を各
  座標 subnerve ごとに課す**(C0 は合併条件として全体で、C5・C6 は全体で
  課せば subnerve への制限が従う)。ハントの定数座標層の探索 6,086 件
  無反例と手証明スケッチは、この block 分解の各成分にそのまま適用できる
  形になる。

Codex の反例と Claude の再現例は、いずれも当該値の座標 subnerve で C2
(subnerve 内の edge lift)が破れるため、相対化した C の下で正しく除外
される。

レビューの他の指摘も同時に是正した: 一般 nerve の face boundary に端点
整合を要求し `d₁d₀ = 0` を theorem 化(P1-3。`Formal/AG/Cohomology/CoverNerve.lean`
の `FiniteNerveCochainComplex` が `d1_comp_d0` を field で受けている既存
欠陥は Formal 側の別課題であり、本カードの nerve 定義には持ち込まない)、
ledger の「条件Cと不変性」を direction-hypothesis / witness / theorem の
3項へ分離(P2-4)。

### 再レビュー(固定 head ddc30bf8)での追加是正

Codex の2巡目レビューは4件の残欠陥を指摘し、すべて有効と判定して是正した。

1. **係数体の固定**: `ThreeCochainComplex` は体に多相なため theorem の強さが
   確定していなかった。係数体を `ℚ` に固定した(ハント engine =
   `fractions.Fraction`、既存 obstruction fixture = `ℚ` と整合。他の体への
   一般化は claim に含めない)。
2. **生成契約の完結**: K0 は index の固定だけでは閉じない(`ThreeCochainComplex`
   は任意の `d₀` / `d₁` を収容する)。各次数を `(cell, law, 値)` 上の
   `ℚ`-値関数空間とし、restriction / differential は同一 label 恒等・label
   不在零・端点差と boundary 交代和で生成、`d₁d₀ = 0`・cochain map 可換性・
   block 直和分解はこの規則から theorem として導く、をカードに明文化した。
3. **C3 と anti-weakening の衝突**: C3(fiber の閉路が internal face で
   張られる)は `ℚ`-係数の fiber 1-homology 消滅と同値であり、「cohomology
   条項の禁止」と名称上でなく内容上衝突していた。C3 を**局所 fiber
   acyclicity の明示の例外**として承認し、禁止規則を「comparison map・
   粗側複体・両側の global `H^1` に関する条項の禁止」へ精密化、結論相当で
   ない理由(個々の chart fiber の内部データのみに依存する Leray 型局所
   非輪状仮定)を ledger に固定した。
4. **no-go の量化と証拠固定**: §1 の no-go を条件付き(非退化正例を受理する
   条件に対する2点分離)へ量化し、§2 の是正の二層構造を同期し、値分配
   反例の再計算可能な全データを上に固定した。report の Cycle 1–4 packet が
   改訂前 statement への歴史証拠であることも report 側に注記した。

## 6. カード改訂の項目対応

| 改訂箇所 | 内容 |
| --- | --- |
| comparison data | edge / face の台を包含宣言から導出(K1)へ+face boundary の端点整合を要求し `d₁d₀ = 0` を theorem 化 |
| law 由来係数 | K0(`(law, 値)` index・`ℚ`-値関数空間・零 / 恒等 restriction・導出 differential・block 分解の生成契約)/ K1 を明文化、比較対応の生成元を明記 |
| 条件C | C6 追加+C1–C4 の座標 subnerve 相対化(block 直和分解が数学的根拠)。C3 は局所 fiber acyclicity の明示例外 |
| (v) 発火 witness | C6 の非空虚発火(粗側 self-loop)と座標 subnerve 相対化の非空虚発火(値分配の実在)を追加 |
| dullness filter | C6 空虚発火・座標 subnerve 相対化が空虚に全体条項へ一致するだけの発火を追加で弾く |
| proof strategy | LoopLiftObstruction を再利用 map に追加、block 還元+ハント手証明スケッチを参考として記載 |
| premise ledger | `nerve / 台` と `law 由来係数の生成` を K0 / K1 と同期、`条件Cと不変性` を hypothesis / witness / theorem の3項へ分離 |
| anti-weakening | K0 / K1 の premise 化(座標対応や台の一致を仮定で受ける)を禁止 |
| frontier | 自由係数反例の law 実現可能性の判定を追加(実現可能なら (iv) 素材、不能なら K0 / K1 の裏付け) |

## 7. 残リスクと次の判定点

- **十分性のリスク**: 相対化した C0–C6 でも不変性の一般証明は未達であり、
  座標 block をまたぐ現象や高次の incidence coherence が要る可能性は残る。
  その場合は failure policy に従い反証として条項改訂案を返す
  (cohomological 条項への差し替えは不可)。
- **発火可能性のリスク**: (v) に C6 非空虚発火(粗側 self-loop)と値分配の
  実在(ある座標 subnerve が全体と一致しない)を足したことで witness 構成が
  難化する。分配しつつ各 subnerve が C を満たす正例は手検査で構成可能と
  見込むが、構成不能と判明した場合は (v) の当該項目だけを別 witness に
  分離する改訂を提案する。
- **座標 subnerve の Lean 具体化**: subnerve とその上の fiber グラフ・
  条項 C1–C4 の Lean 定義が、K0 / K1 の導出データだけから定まり選択を
  持ち込まないことをレビューで確認する(route integrity gate の
  provenance 追跡対象)。
