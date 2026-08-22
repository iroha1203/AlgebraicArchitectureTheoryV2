# Atlas 定理の補強計画 — 観測解像度の理論として CS へ開く

本ノートは考察ノートである。新しい公理・定義・定理は導入せず、証明済み定理の
statement(G-104 / G-107 の fixed statement)を変更しない。目的は、Atlas 定理
(G-104 の Diagnostic Resolution Invariance Theorem と、その位置を定める G-107 の
Uniform Invariance Defect Semantics and Nonfactorization Theorem。以下まとめて
**Atlas**)の現在価値を **AAT 内部**と **CS 一般**に分けて測り、CS に届く補強の
項目・優先順位・判定規準を固定することである。

補強は既存 statement の改訂ではなく後継 GOAL として起票する。本ノートに書く
数学的主張のうち G-104 / G-107 の report に無いものは、すべて**未証明の
candidate**(手証明・有限例の機械裏取りのみ、Lean 未検証)であり、採否は
ユーザー裁定に従う。lifecycle の経緯(PR・Issue・裁定日)は各 report と
tracking Issue を正本とし、本ノートには持ち込まない。

## 要旨

1. Atlas の対象は一つしかない。比較写像 `f_A : H¹(粗い観測) → H¹(細かい観測)`
   と、その欠損 `J_A = (dim ker, dim coker) = (phantom, hidden)` である。死角・
   誤警報・観測すべき解像度・観測の分割で落ちる診断・構造的衛生規則・局所観測の
   限界は、すべてこの一つの写像についての定理として統一される(§1.1)。AAT
   内部では測定器の解像度理論として必須である。
2. CS 一般への貢献は、単独ではまだ薄い。大域不変量が局所観測で決まらないのは
   理論 CS には予想どおりであり、十分条件は構造的衛生規則の精密化に見え、
   還元は関手性の帰結に見える。弱さの正体は定理の弱さではなく**位置の未確定**
   である: 枠が工程語(レビュー)で語られ観測の理論として置かれていない、
   最近接先行との差分が未記述、実システムでの深さマップが未測定、計算量・合成・
   半径一般化が frontier のまま、係数体(ℚ と F₂)が測定器と揃っていない(§1.3)。
3. 枠は「コード観測の解像度理論」へ置き直す(§2)。観測は変わり、診断が不変か
   を問う。解像度はスカラーでなく poset であり、観測者には半径と幅の二軸がある。
   比喩の出所は計測器の解像度と標本化であり、レビューの経験則ではない。
4. 補強の候補のうち、CS の外に一文で通じる**定理水準の candidate** は四つある
   (§4): (a) 比較写像の Leray 帳簿と、そこから出る**初めての必要条件**
   「一様不変 ⟹ 各粗 chart の位相的 fiber の `H¹` が零」(R8)、(b) **最粗の
   安全な読みは一意でない**(零 locus は共通粗化でも区間でも閉じない。抽象解釈の
   complete shell・最粗双模倣・最小十分統計量の一意性との対照。R10)、(c) 一様
   判定は **coNP 完全**、観点固定の pointwise 判定は **P**(R4a)、(d) 観測者の
   **半径と幅**の二軸の限界(R3)。いずれも小〜中規模。
5. 必須は R2(差分表の充填)と R1(実システムの多解像度観測)。R1 は決定論的
   静的抽出で service / class / method の三段を複数系で測り、深さマップが**領域
   ごと・欠損源ごと**に割れるかを事前登録の問いで見る。前提確認 R0(係数体の
   裁定・decider の一回実行・観測クラスの確認)を最初に置く。優先順位は
   R0 > R2 > R8 > R1a > R10 > R3-w > R4a > R9 > R1c > R11 > R3-r > R4b > R5 ≫ R7
   (§5)。R12(エージェント読解)と R13(方法論論文)は別トラック。
6. 「CS に届いた」の判定規準は三つ(§6): 差分表の各行が肯定形で埋まる、実測で
   深さマップが領域ごと・源ごとに割れる、R8 / R10 / R4a / R3-r のいずれかが
   定理として立つ。揃わなければ Atlas は「AAT の測定器の校正理論」として正確に
   主張し、それ以上を名乗らない。

## 参照

**正本**(事実関係の判定基準):

- [G-104 カード](../../research/goals/G-104-aat-resolution-invariance.md) /
  [G-104 report](../../research/reports/G-104-aat-resolution-invariance.md)
  (claim (i)–(v)、条件 C0–C6、K0 / K1)
- [G-107 カード](../../research/goals/G-107-aat-uniform-invariance-characterization.md) /
  [G-107 report](../../research/reports/G-107-aat-uniform-invariance-characterization.md)
  (還元・decider・位置・非必要性・非分解性、frontier)
- Lean: `research/lean/ResearchLean/AG/UniformInvariance/UniformPresentationDecider.lean`
  (decider は `List.sublists` で全部分集合を列挙)、同 `ExecutableRationalRank.lean`
  (rank は列選択の全探索)、`Formal/Util/AssertStandardAxioms.lean`
  (`Lean.ofReduceBool` = `native_decide` を拒否)
- ArchSig: `tools/archsig/src/saga.rs`(SAGA の係数は `F2` 固定)
- [研究の全体目標](../research_goal.md)(禁忌 4・5・6・7 が本計画の停止規則)

**上流考察ノート**(正本ではない):

- [解像度診断の設計ノート](n1003_aat_resolution_diagnostic_design.md)
  (observation factorization、成果物の四分法、`J_L` と `J_A`)
- [Semantic Geometry of Architecture 測量台帳](n1005_aat_semantic_geometry_route_after_g107.md)
  (§4 登路、§7 論文への含意)
- [Atom Is All You Need 考察ノート](n1001_atom_is_all_you_need_discussion.md)
  (§7.7 差分と評価規準、§12 論文ロードマップと実証節計画)

---

## 1. 現在地 — Atlas は何か

### 1.1 一つの対象と統一表

Atlas の証明済み内容は、すべて比較写像 `f : H¹(粗) → H¹(細)` と欠損
`J_A(f) = (dim ker, dim coker)`(領域 `A` ごと)についての主張である。現場で
別々に語られてきた現象は、この一つの写像の核と余核に畳まれる。

| 観測の現象 | Atlas での正体 | 宣言(正本は各 report) |
| --- | --- | --- |
| 粗い観測で診断が消える(死角) | `coker`(hidden) | G-104 (iv)(b) `fixed_claim_iv_b` |
| 粗い観測で診断が湧く(エイリアシング) | `ker`(phantom) | G-104 (iv)(a) `fixed_claim_iv_a` |
| この解像度で観測してよいか | `J_A = (0, 0)` の領域 | G-107 (i) `uniformInvariance_iff_allNonemptyASubnerveDefect_eq_zero` |
| 判定は計算で決まる | sound / complete decider | G-107 (ii) `uniformPresentationCheck_eq_true_iff` |
| 観測すべき解像度は規約の中身でなく足跡で決まる | law 全量化 → 領域 `A` への還元 | G-107 (i) `uniformInvariance_iff_allNonemptyASubnerveH1Bijective` |
| 関心事ごとに分けて観測すると落ちる診断 | `A` は概念の集合で効く(単独概念に還元しない) | 還元の量化域そのもの(§7 の玩具 変種 B が例示) |
| 解像度を保証する構造条件 | 条件 C は十分、各条項は非必要 | G-104 (ii) `generatedComparisonH1Map_bijective`、G-107 (iii)(iv) `conditionC_of_conditionCAllA`、`ConditionC0NonnecessityWitness`〜`C6` |
| 過剰な精細化は診断を増やさない | No-New-Diagnostics Corollary | G-104 (iii) `overresolution_no_new_diagnostic_classes` |
| 局所観測だけでは解像度の妥当性を決定できない | 零 locus が半径1観測を通して分解しない | G-107 (v) `uniformPresentation_not_factors_through_obsG` |

統一されているのは表の右列が一本であることであり、左列のどれか一つを取り出すと
「普段やっていること」に見えるのは当然である。新しいのは一つの機構から全部が
出ることである。

係数について一点。Atlas は ℚ 係数で固定されている(G-104 claim boundary)。
ArchSig の SAGA 実装は F₂ 係数である(`saga.rs`)。両端の `H¹` を「SAGA と同じ
対象」と言えるのは係数を揃えたときであり、F₂ は ℚ より多くの類を見うる(有限
nerve に ℤ/2 torsion が実在しうる)。どちらで測定の鎖を回すかは理論側の裁定
事項である(R0)。

### 1.2 構造像(candidate): 比較写像の Leray 帳簿

比較写像は「粗側の係数から押し出し係数への unit 射」と「Leray の edge map」の
合成に分かれる:

```text
f_A = (edge map) ∘ H¹(unit),   unit : ℚ_{N_A} → φ_* ℚ_{N'_A}
0 → H¹(N_A; φ_*ℚ) → H¹(N'_A; ℚ) → ⊕_c H¹(Φ_c^A) → H²(N_A; φ_*ℚ) → …
```

ここで `Φ_c` は粗 chart `c` の**位相的 fiber**(`c` 上の細 chart と、退化宣言
された辺・面だけから成る部分複体)である。現行の観測クラス(面は全辺 mapped か
全辺退化のどちらか)では接続写像 `d₂` が恒等的に零になる見込みがあり、そのとき

```text
phantom_A = dim ker H¹(unit)
hidden_A  = dim coker H¹(unit) + Σ_c dim H¹(Φ_c^A)
```

欠損の源は四枚の層(unit の核 `K`、余核 `Q`、`R¹φ_*`、`d₂`)で尽き、条件 C の
各条項はその茎の消滅に対応する(`K`: C0 / C2 / C4、`Q` at chart: C1 ∧ C6、
`Q` at edge: C5、`R¹`: C3 の位相的部分)。n1003 §4 の「機構カタログ」はこの四枚で
構造化できる。

この帳簿から二つの candidate が出る。

- **必要条件 C3′**: 一様不変 ⟹ 全非空 `A`・全粗 chart `c` で `H¹(Φ_c^A; ℚ) = 0`。
  `R¹` は chart に集中し、`d₂ = 0` の下では大域コホモロジーで相殺されない唯一の
  源だからである(零拡張の cochain 論法)。G-107 の C3 非必要性 witness は、G-104
  の C3 が self-loop の lift を fiber 辺に数える定義上の過剰部分を突いており、
  位相的 fiber の非輪状性は破っていない。これは G-107 の地図(C0–C6 はどれも
  必要でない)と矛盾せず、**必要条件側の一枚を初めて足す**。ただしこの必要性は
  混在 face(R9)を許すと `d₂ ≠ 0` がありえて壊れる。観測モデルの選び方で
  必要条件が生まれたり消えたりすること自体が定理水準の観測である。
- **押し出し系**: 粗い観測者が自前の係数を作らず細かい観測の押し出し `φ_*F` を
  係数に採れば phantom は恒等的に零で、hidden は fiber 内部の輪だけになる。幻の
  診断は「粗い観測者が集計でなく再観測をする」ことの代償である。

### 1.3 AAT 内部の価値

- ArchSig の抽出粒度の選択に定理の warrant を与える(第VIII部測定理論の錨)。
- reading 圏上の関手化(G-107 frontier)は program context / 意味のモジュライの
  種であり、登路(n1005 §4)の土台に接続する。
- 論文A 実証節の第三段(解像度スイープ)の theorem 側の錨である(n1001 §12)。

### 1.4 CS 一般から見た現在の弱さ

定理が常識と一致する部分は説明すれば「普段やっていること」になる。発見として
立つのは常識と食い違う部分だけである。証明済みの食い違いを強い順に並べる。

1. 局所をいくら丁寧に観測しても解像度の妥当性は決まらない(G-107 (v))。
2. 関心事で分けて観測すると、関心事をまたぐ輪は誰にも見えない(`A` が集合)。
3. 観測すべき深さは規約の中身でなく足跡で決まる(還元)。
4. 粗い観測は隠すだけでなく湧かせる(phantom)。
5. 構造的衛生規則をすべて破っても安全な配線がある(非必要性)。

candidate(witness の Lean 化後に昇格する):

6. 最粗の安全な読みは一意でない。安全な併合を二つ合わせると輪が隠れる(R10)。
7. 途中まで細かくすると幻が湧き、降り切ると消える。欠損は精細化に沿って単調で
   ない(R10)。
8. 幅 `k` の観測(概念 `k` 個までの領域を見る)は `k+1` 概念をまたぐ輪を
   見落とす(R3-w)。
9. 幻は、粗い観測者が集計でなく再観測をするところから生まれる(R8 押し出し系)。
10. 観点を固定すれば判定は多項式、全観点では coNP 完全(R4a)。

そのうえで、CS 一般にまだ届かない理由は五つある。

- **枠**: レビューという工程語で語られ、観測の理論として置かれていない。
- **差分**: 抽象解釈の exactness / completeness、CEGAR、Leray 型写像定理、
  persistence、「局所 ⟹ 大域 iff 非輪状」族、lumpability、SE の lifting 系列、
  有限モデル理論の局所性との差分が未記述である(§3)。
- **実測**: 実システムで深さマップが領域ごとに割れることが示されていない。
  玩具規模では輪は目で見えるため、計算で出ることに価値が立たない。
- **frontier**: 計算量・合成・半径一般化が G-107 の frontier のままである。
  decider は存在定理であり、一度も実行されていない。
- **係数体**: 測定器(F₂)と定理(ℚ)が揃っていない。

## 2. 枠の置き直し — コード観測の解像度理論

- **観測**とは、解像度を選んでコードを読み、nerve と台を得る行為である。人間の
  レビュー、エージェントのコード読み、ArchMap の抽出は同じ行為の三つの担い手で
  ある。問いは「観測の解像度を変えたとき、どの診断が安定で、欠損はいくらか」
  であり、これは計測理論の問いである。
- 形式側は既に観測の言葉で書かれている(G-103 の reading、G-107 の `Obs_G` と
  observation factorization、n1003 の題)。「レビュー」は現場向けの皮であり、
  剥がすと理論の語彙と一致する。
- **二軸**: 軸1 = 読みの解像度(reading `q`、画素サイズに相当。スカラーでなく
  **poset** であり、同じ粒度で区切りを変える zoning と、粒度を変える scale の
  両方を含む)。軸2 = 観測者の視野(certificate / grammar の半径 `r` と、同時に
  見る概念の幅 `k`)。G-107 (v) は軸2・半径1の限界、R3 は二軸の地平を描く。
- 比喩の出所は計測器の解像度・標本化・エイリアシングである。許可する語 =
  分解能、エイリアシング(機構として)、masking、系統誤差(`J_A` は決定論的で
  不確かさではない)、誤差予算、トレーサビリティ(核まで)、校正曲線(相対)。
  定義を伴わない限り題にも節名にも使わない語 = Nyquist の閾値定理、不確かさ
  (抽出分散を測らない限り)、renormalization / universality、contextuality、
  rate–distortion、resolution limit(network science の語。別機構)。
- 命名の注意: 変わるのは観測、不変(または欠損)なのは診断である。定理の主語は
  「診断の安定性」のままとし、「観測が不変」と読める名は使わない(G-104 の
  命名記録どおり)。
- 位置づけの規律: 否定形のメタ記述(「新しい数学ではない」「AI 生成ではない」
  等)は書かない。最近接の先行を引き、足した分だけを肯定形で具体に書く
  (n1001 §7.7 の規律と同じ)。統一は宣言せず、§1.1 の表で見せる。
- 応用節は三つ: 人間のレビュー(どこまで降りるか)、エージェントのコード読み
  (どの粒度で読めば診断を誤らないか)、ArchSig の抽出粒度選択(正当化)。

## 3. 最近接先行との差分(肯定形で埋めるべき表)

各行の書誌は執筆時に外部 API で突合する(本ノートは著者・年の水準に留め、確信
の無いものには「要確認」を付す)。

### 3.1 抽象化の精度理論

| 先行 | 彼らの問い・結果 | Atlas が足すもの |
| --- | --- | --- |
| strong preservation / exactness(Ranzato–Tapparo 2004 / 2007)、may / must 抽象(Dams–Gerth–Grumberg 1997) | 抽象が性質を強保存する条件。spurious(may)と見落とし(must) | Atlas は completeness より **exactness の instance**。`J` は may / must の両側欠損を一つの線形写像の核・余核で数える包装 |
| completeness(Giacobazzi–Ranzato–Scozzari 2000)、complete shell / core | complete 領域の族は閉じ、最粗の完全精細化が一意に存在 | **対照**: Atlas の零 locus は共通粗化で閉じず、最粗の安全な読みは一意でない(R10、candidate)。サイクル一つで壊れる |
| local completeness(Bruni–Giacobazzi–Gori–Ranzato 2021)、partial completeness(Campion–Dalla Preda–Giacobazzi 2022) | 入力ごとの completeness、距離で測る片側の不完全さ | 一様 / pointwise = global / local。有限 Target ゆえ有限基底が存在(還元)。両側の次元 |
| CEGAR | spurious counterexample を見つけて精細化 | spurious(`ker`)と見落とし(`coker`)を精細化の前に数える decider。精細化は欠損を単調に減らさない(R10) |

### 3.2 写像定理・persistence

| 先行 | 彼らの問い・結果 | Atlas が足すもの |
| --- | --- | --- |
| Leray / Grothendieck 合成関手スペクトル系列 | 写像に沿う押し出しと higher direct image | G-104 (ii) はその有限・局所係数・次数1版の系。Atlas の固有分 = law 係数の block 分解で座標ごとに適用、退化宣言つき部分写像の Lean 固定、位置(非必要性7枚+非分解性)、decider、**必要条件 C3′**(R8、現行クラス限定) |
| Vietoris–Begle、Quillen Theorem A、McCord 1966、poset fiber theorems(Björner–Wachs–Welker 2005) | 局所非輪状 ⟹ 同型 | 条件 C は VB 型の incidence 十分条件であり、self-loop について真に強い(C の下では座標 subnerve 内の粗 self-loop は `H¹`-neutral にしかなれない)。弱化した局所十分条件 C^loc(R8) |
| persistence(Zomorodian–Carlsson 2005)、rank invariant、interleaving 安定性(Chazal–de Silva–Glisse–Oudot 2016、Bauer–Lesnick 2015)、zigzag(Carlsson–de Silva 2010)、Möbius 反転(Patel 2018、Kim–Mémoli 2021、要確認) | 解像度 poset 上の module と barcode | 鎖上の rank invariant = `J`、barcode = 深さマップ(hidden = birth、phantom = death)。概念方向は被覆 `{N_t}` の Mayer–Vietoris(関心事で分けると見えない輪 = 連結準同型の像)。安定性は入れ子の観測者族に限る。一手の編集で `J_A` は各成分 ≤ 1 しか動かない(R7 の下界補題) |
| cellular sheaf(Curry 2014、Hansen–Ghrist 2019) | 一般の制限写像、Laplacian | 押し出し係数の再定式化は採用(R8)。一般の制限写像は A-還元を壊すので、「法則 = subnerve 上の定数層の直和」という特別なクラスが還元を可能にしていると明言する。Laplacian は計算・表示手段に限り、量としては presentation 依存で不採用(禁忌 6) |

### 3.3 「局所 ⟹ 大域」の定理族

| 先行 | 彼らの問い・結果 | Atlas が足すもの |
| --- | --- | --- |
| Vorob'ev 1962、Beeri–Fagin–Maier–Yannakakis 1983、Fagin 1983、Abramsky–Brandenburger 2011(Čech `H¹` 版は Abramsky–Mansfield–Barbosa 2011) | 「対ごとの整合 ⟹ 大域整合」が全インスタンスで成り立つ iff スキーマ hypergraph が非輪状。データ非依存・反復還元で決定可能 | 問いは `H⁰`(大域切断の存在)と `H¹` の解像度比較で別。定理の**型**が同じ: 大域性質 / 局所十分条件 = 非輪状 / データ非依存 / 決定可能。C3(位相的 fiber 非輪状)が非輪状性の対応物で、C は十分のみ、半径1には iff なし。positioning の主軸候補 |
| lumpability(Kemeny–Snell 1960、weak は Rubino–Sericola 要確認)、bisimulation 最粗商(Paige–Tarjan、Larsen–Skou 1991) | strong / weak lumpability。最粗の正確な商が一意に存在 | strong / weak = 一様 / pointwise。**対照**: 最粗の一様読みは一意でない(R10) |
| rough set(Pawlak 1982)、reduct(Skowron–Rauszer 1992) | 定義可能集合、下近似、reduct は多数 | 定義可能性 = adequacy(G-103 `factors_iff_kernel`)、下近似 = descend 可能部分族の診断。Atlas は定義可能な係数の上で導出不変量が不変でないことを扱う |
| Herlihy–Wing 1990 の locality、connected information(Schneidman et al. 2003)、十分統計量 / IB(Tishby et al. 1999) | 成分ごとの検査で全体が決まるか。最小十分は一意 | 一様性は概念ごとでは決まらない(幅の非分解性、R3-w)。最粗の一様読みは一意でない |

### 3.4 SE の観測と粒度

| 先行 | 彼らの問い・結果 | Atlas が足すもの |
| --- | --- | --- |
| lifting 演算子(Feijs–Krikhaar–van Ommering 1998、Relation Partition Algebra 1999、Holt 1998) | part-of 階層で uses 関係を上位へ lift する | これが粗視化 `π` の直接の先祖。彼らは lift したグラフを計算する。Atlas は lift の `H¹` への誘導写像の核・余核を領域別に出す |
| Melton–Tempero 2007、Laval et al. 2011 / 2012、Oyetoyan et al. 2015、Al-Mutawa et al. 2014 | class 水準の輪の量、package 輪の細粒度分析。**containment の位置は有害 / 無害の判別基準にならない** | Atlas の予言: 判別するのは containment の位置でなく概念 `A` 上の fiber 連結性(C1)。無害な package 輪 ≈ phantom、という検証可能な仮説 |
| 階層化 reflexion model(Koschke–Simon 2003、水準間の食い違い事例は要確認)、Lutellier et al. 2015 / 2017、Pruijt et al. 2017、Arcan(要確認) | 階層 mapping。観測(辺の種類・ツール)の差で結果が変わる | 観測の差が診断に効くのは `J` を変える場所だけ。辺種類の粗視化が chart 集約の形に乗るかは別途検討 |
| 注意 | SE の輪文献は**有向**輪 | Atlas の `H¹` は無向の貼り合わせ輪。R2 の表と論文に区別を明記する |

### 3.5 局所性・計算・検証

| 先行 | 彼らの問い・結果 | Atlas が足すもの |
| --- | --- | --- |
| Hanf 1965、Gaifman 1982、Fagin–Stockmeyer–Vardi 1995、Cai–Fürer–Immerman 1992、1-WL(Morris et al. 2019、Xu et al. 2019)、LOCAL(Linial 1992) | 有界半径の局所論理・局所アルゴリズムの表現力 | (v) はその instance。R3-r で任意半径の族へ上げる。**理論 CS の下界とは名乗らず**、AAT の限界定理として置き、系「一様不変性は有界次数上 FO 非定義・1-WL 非不変」とだけ書く |
| Monotone 3-SAT(Gold 1978)、ℚ-rank ∈ NC²(Mulmuley 1987) | — | 一様判定 coNP 完全 / pointwise ∈ P の candidate(R4a) |
| certifying algorithms(McConnell–Mehlhorn–Näher–Schweitzer 2011、Alkassar et al. 2014)、LRAT / GRAT(Cruz-Filipe et al. 2017、Lammich 2017、Heule et al. 2017、Tan–Heule–Myreen 2021)、CompCert、seL4 | 証書検査の検証 | 証書が証すのが rank でなく law 全量化の意味論的性質であること(還元・決定可能性定理を通して)、二段の信頼水準、観測側の非検証性の明示(R11) |
| 大規模形式化報告(Equational Theories Project、PFR、LTE。いずれも要確認) | 既知定理の形式化 | 反証ループ下の statement 発見と、核が弾けない欠陥の分類学(R13) |

### 3.6 「同じでない」と先に書く行、導入の hook

- Fortunato–Barthélemy 2007 の resolution limit(目的関数の artifact。hidden と
  語は同じで別機構)、spectral coarsening(Loukas 2019。計量が無いので近似版は
  輸入しない)、繰り込み(flow・固定点が無い)、rate–distortion(重みを発明
  しない)。
- MAUP(Openshaw 1984)・ecological fallacy・Simpson は related work でなく
  **導入の hook** に置く。Atlas は決定論的・組合せ的で標本誤差を持たないと冒頭で
  言う。「数の一致は診断の一致でない」(dim の差 = phantom − hidden の打ち消し)は
  恒等式であり、R1 の測定規律として扱う(定理の名を与えない)。

## 4. 補強項目

各項目に、内容・産物・登路上の位置(幹 / 横の稜線 / 土台補強)・判定規準を付す。
見積もりは規模感のみ(小 / 中 / 大)。

### R0 前提確認(極小、最初に)

- (a) **係数体の裁定**: ℚ で統一して ArchSig / harness に ℚ rank を持たせるか、
  F₂ 版 Atlas を別途立てるか。「同じ `H¹`」の文言はこの裁定まで留保。
- (b) **decider の一回実行**: `#eval` で `uniformPresentationCheck` を T3 等に
  走らせ、現 decider(`2^|Target|` × rank 全探索)の実行可能性と kernel `decide`
  の挙動を実測する。`native_decide` は公理監査で禁止されている。
- (c) **観測クラスの確認**: 現行クラスは混在 face(2 者が同一 chart、1 者が外)を
  排除していること、G-104 の fiber graph(self-loop lift を含む)と位相的 fiber の
  定義差を固定する(R8 / R9 の前提)。
- (d) 玩具の pullback は辺の向きが揃う前提で符号を付けていない。一般の分割を
  扱うときは符号付き版にする(R10 の witness 計算に要る)。

### R1 実システムの多解像度観測(必須。三分割)

- **R1a 構造深さマップ**: 決定論的な静的抽出器(LLM 抽出でない。深さマップは
  配線と足跡だけから決まり、law の値を要らないため)で service / class / method
  の三段を読み、概念語彙(10 前後を PRD で固定)の領域ごとに `J_A` を計算する。
  v1 は graph 水準(面なし。C3 / C4 は空虚と明記)。対象は train-ticket を含む
  5 系以上(できれば 2 言語)。既存の train-ticket 資産から読める事前観測:
  service ↔ class の深さマップは**平坦**(41 / 42 サービスでサービス内 class
  依存が木)になる公算が高く、phantom は class ↔ method に現れる見込み。これは
  LLM 抽出の下界に基づく事前登録予測であり、外れても資産。
  事前登録する問い: P1 存在(phantom > 0 と hidden > 0 の領域が各 1 以上)/
  P2 非一様(`J = 0` と `J ≠ 0` の領域の共存)/ **P3 概念またぎ**(`|A| ≥ 2` で
  `J_A ≠ 0` かつ各単独概念で `J = 0` の領域)/ P4 還元検算 / P5 機構帰属
  (`J ≠ 0` で破れる条項の分布、`J = 0` で C が破れる割合 = C の偽警報率)/
  P6 梯子の安定化(どの段で `J` が止まるか)。
  測定規律: `(phantom, hidden)` を領域ごとに別々に報告し差を指標にしない、
  両側 dim が一致しながら `J ≠ 0` の打ち消し例の有無、欠損ごとの幅
  `min{|A| : J_A ≠ 0}`、鎖 (s,m)・(m,f)・(s,f) の三対で非単調が出るか、同じ
  粒度で区切りを変えた二つの分割(repo 単位と deploy 単位)による zoning 例、
  欠損源の内訳(`K` / `Q` / fiber 由来)。pointwise(law 固定)モードを主、
  一様モードは小部分系で。
  産物: 実証節 PRD(問い節で事前固定)、`docs/reports` の凍結規律に従う測定
  artifact、ArchSig の多解像度入力(`π` は観測なので ArchMap の context に
  `refines` を持たせ、深さマップは ArchSig の計算)。
- **R1b law 係数の還元検算**: 既存 sectionValue 証拠で直接計算が値クラス和に
  一致することを確認する(定理上必ず一致。不一致は抽出 / 実装バグの検出器)。
- **R1c 面の導入**: 「三者が同じ共有型・定数・スキーマを参照する三つ組」を面と
  する。混在 face を扱うには R9 が先。
- 位置: 土台補強。論文A 実証節計画(n1001 §12)の第三段と同一対象であり、二重に
  作らない。査読者が納得する条件: 5 系以上・決定論抽出+digest 固定・統計
  (service 水準の輪の x % が phantom、class 水準の輪の y % が hidden、概念またぎ
  z 件)・外部結果への接続(修正履歴、ツール間不一致が `J ≠ 0` 領域に集中するか、
  R12 の下流タスク)。
- 判定: 深さマップが**領域ごとに、かつ源ごとに**割れること。全域 `J ≠ 0` なら
  一様モードの情報量が無いことを記録し pointwise へ重心を移す。全域 `J = 0`
  (service ↔ class が平坦)なら失敗ではなく「この系ではその粒度の読みが安全」
  という結果として記録し、method 水準と他系へ進む。どちらも葬らない(禁忌 3)。
- 規模: R1a 中(抽出器は一度、以後は系ごとの限界費用小)、R1b 小、R1c 中。

### R2 最近接先行との差分表の充填(必須、R1 の PRD より先)

- 内容: §3 の各行を書誌突合つきで埋める。有向 / 無向の区別、辺種類の粗視化が
  定理の形に乗るかの検討を含む。
- 判定: 粒度依存の直接の定量実証は無い(最近接は lifting 系列)と見られるため、
  CS hook の主軸は「集約アーティファクトを概念領域ごとに `(ker, coker)` で厳密に
  勘定し、機構を名指しし、判定を計算に置く」に限る。positioning の主軸候補は
  exactness(3.1)と「局所 ⟹ 大域 iff 非輪状」族(3.3)。
- 規模: 小。

### R3 観測者の視野の限界(半径と幅の二軸)

- **R3-r 半径**(中): 任意の固定半径 `r` に対する有限 presentation 対の族。
  構成案: `T_n` = chart 1 つに self-loop `n` 本と面 `(i, i+1, i+2) mod n`。一様 ⟺
  `6 ∤ n`(粗側 `H¹` は循環行列 `1 − x + x²` の核で決まる)。`T_{2n}` と
  `T_n ⊔ T_n`(`n ≡ 3 mod 6`、`n > 2r + 1`)は cell 数が同じで全ての `r`-typed ball
  が一致し、前者は非一様・後者は一様(`J` の直和加法性)。grammar は半径 `r` の
  typed ball だけを読む最小のものに定義し直す(`G_local-v1` の成分を一般化しない)。
  anti-answer-encoding の規律(n1003 §8)を保つ。名乗りは「有界局所の証明書は
  存在しない」(AAT の限界定理)。
- **R3-w 幅**(小): 幅 `≤ k` の全ての `A` で `J_A = 0` が一致しながら一様性が
  異なる対。witness 候補: `k+1` 概念をまたぐ fiber 内の交互多角形(chart の台
  `{c_{i−1}, c_i}`、辺の台 `{c_i}`)。幅 `≤ k` は全零、幅 `k+1` で hidden = 1。
  `k = 1, 2, 3` は玩具の線形代数で裏取り済み。Mayer–Vietoris で「`A ∪ B` の `J` は
  `J_A`、`J_B` と両方に触る cell 上の接続写像で決まる」を説明に使う。R4a の
  構造問題(どの `A` の族で足りるか)への否定回答(有界幅の族では足りない)。
- 産物: 後継 GOAL(R3-w を先に)。二軸の地平 `(r, k)` と欠損の(長さ、幅)の
  図を論文の一枚にする。上界方向の鋭い閾値は主張しない(Leray 帳簿の「局所 +
  fiber 層のコホモロジー」が exact な上界の型。R8)。
- 位置: 横の稜線(G-107 frontier の完了)。

### R4 一様判定の計算量(二分割)

- **R4a 与えられた対の判定**(中): candidate = **UNIFORM は coNP 完全**
  (所属: `A` を証拠に有理 rank は多項式。困難性: Monotone 3-SAT からの帰着案 —
  target = 変数、粗側に長い輪、正節を辺の台、負節ごとに cone を立て、`A` が充足
  割当のときだけ輪が生き残る。gadget の well-formedness は未検証)、
  **pointwise(law 固定)は P**。構造: 台-連結 `A` で足りる(支持超グラフが非連結
  なら `N_A` が直和分解し `J` が加法的)、incidence 型の同値類で `2^{#型}` に落ちる、
  しかし instance 非依存の族は全 `2^n − 1` 通り必要(任意の部分集合族が defect
  集合として実現される。単調性・劣モジュラ性は無い)。C3′ は fiber 局所なので
  安価な前検査に使える。
- **R4b 最粗の一様粗化の構造と計算量**(中〜大): 「chart 数 `≤ m` の一様粗化が
  存在するか」の計算量(困難性を予想、根拠なし)。構造の半分は R10。
- 位置: 横の稜線。CS に可読な問いであり、かつツールの量化域の設計(一様モードの
  実現可能性)に直結する。
- 判定: 多項式アルゴリズム+正当性、または困難性証明のいずれか。

### R5 reading 圏上の関手化と条件 C の合成閉

- 内容: 有限 reading と refinement の圏 `Read_L` 上で `q ↦ H¹(q)`、`f ↦ H¹(f)` が
  関手であること、零欠損射が wide subcategory を成すこと、**条件 C を満たす射の
  合成閉性**(証明、または反例と正確な追加条件。C^loc の合成閉は VB 型で自明、
  C 自身は別問で、C3 は fiber 内 face の lift 条項を足して初めて合成する可能性)。
  否定半分「零 locus は共通粗化でも区間でも閉じない」(R10)と対にする。
- 位置: 幹寄りの土台(program context / 意味のモジュライの種。persistence
  module を成す前提として R5 は整地以上の役目を持つ)。
- 判定: 関手性と零欠損の閉性は整地であり看板にしない。内容があるのは条件 C の
  合成閉性と否定半分。「compositional verification」と名乗らない(禁忌 4・5)。
- 規模: 小〜中。

### R6 defect の合成計算(R8 に吸収)

- 合成射の `J_A` を各段の核・余核から計算する完全列は、Leray 帳簿(R8)の鎖に
  沿う低次項として得られる。blame(どの段で何を失ったか)と差分更新(K1 の
  局所性により、変更 cell の台と交わる `A` の block だけ再計算)は論文の一節と
  ツールの更新則に置く。独立の定理として看板にしない。

### R7 最小精細化の合成(MIN-ATLAS-REFINE)

- 内容: 非零の `J_A` と許容 elementary modification(cell の追加・除去、台の
  精細化、reading の精細化、law 保存の分割、lift 追加・fiber 連結・fiber 面追加・
  平行 lift の同一視 = 「茎を殺す手」)を入力に、全 `J_A = 0` にする最小コストの
  変形を合成する。決定問題版、計算量、Lean 検証 checker、edit ごとの更新則。
  下界補題: 一手の編集で `J_A` は各成分 ≤ 1 しか動かないので、零 locus までの
  編集距離 `≥ max_A max(phantom_A, hidden_A)`、かつ `≥ max_A Σ_c dim H¹(Φ_c^A)`。
  R4b(最大粗化)と双対なので問題定義ノートは一本にする。
- 位置: 横の稜線(大)。本計画では**問題定義の固定まで**。起票は Atlas 論文の後。

### R8 Leray 帳簿・必要条件 C3′・C^loc・押し出し系(最優先の後継 GOAL)

- 内容: §1.2 の帳簿を有限 2 次元・退化宣言つき部分写像で固定する。成果として
  数えるのは (i) **必要条件 C3′** の theorem(零拡張の cochain 論法。Lean は
  小〜中)、(ii) 弱化十分条件 C^loc(L0 各粗 cell が lift を持つ / L1 各位相的
  fiber が非空連結 / L2 各粗辺の lift が一意 / L3 各位相的 fiber の `H¹ = 0`)と
  `C ⊊ C^loc ⊆ 零 locus ⊆ {C3′}` の包含(strictness witness は G-107 の C3
  witness が候補。C0 / C2 / C4 / C5 の成立は要確認)、(iii) 押し出し系
  (粗係数 = `φ_*F` なら phantom ≡ 0)、(iv) **誤差予算不等式**(`dim ker ≤
  Σ_c (b₀(Φ_c^A) − 1) + #{反射しない self-loop}`、`dim coker ≤ Σ_c b₁(Φ_c^A) +
  Σ_e (b₀(辺 fiber) − 1) + #{lift を持たない粗 face}`。項の正確な形は要固定。
  条件 C = 予算ゼロで G-104 (ii) が系として出る。等号例・緩み例を witness で対に
  する)。帳簿全体(5 項完全列の Lean 化。Mathlib にスペクトル系列は実用水準で
  無いと見られ、有限次元線形代数で直接書く)は同カードの frontier。
- なぜ CS の外が気にするか: 「箱の中の輪は外から決して見えず、隠れる診断の個数は
  箱ごとの `H¹` の和以上」「幻の診断は集計でなく再観測から生まれる」の二文が
  定理で言える。計測の読者には誤差予算、SE の読者には blame、CS には有限 Leray 型
  不等式。
- 既知との関係: 帳簿は Leray / Grothendieck の系であり新規性なし。必要条件は
  失敗しえた主張(混在 face で失敗する)なので定理を名乗れる。
- 位置: 幹寄りの土台(反例史 = coarse-anchored visibility / presentation
  sensitivity を「層の台の位置」として一元的に読み直す)。R6 を吸収。
- 判定: 必要条件 C3′ と strictness witness が Lean で立つ。帳簿は「古典の AAT
  帳簿化」と書き、新定理と売らない(禁忌 5)。
- 規模: 必要条件 小〜中、帳簿全体 中〜大。

### R9 観測モデルの拡張 — 混在 face(後継カード)

- 内容: 細 face が粗側の退化 2 単体(`s₀E`、`s₁E`)へ写ること(2 者が同一 chart、
  1 者が外の三者合意)を許す。cochain map の可換は normalized cochain で成立
  (`c(e₀) − c(e₁) + c(e₂) = 0 − c(E) + c(E)`)、hereditary 規則は「boundary の像と
  整合する単体が存在する」に一般化される。`d₂` が生きるので帳簿は `− rank d₂` を
  持ち、必要条件 C3′ は「外との合意で吸収されない限り」に条件付きになる。
- なぜ必要か: 実システムでは混在 face が普通にあり、現行クラスでは捨てるか不正な
  comparison data になる。R1c の前提。
- 位置: 土台補強(G-104 の fixed statement は変えず新カード)。
- 規模: 中。

### R10 最粗の安全な読みの非一意性(witness。小)

- 内容: 細読み `q'` と粗化の規約(商 nerve の作り方 — 平行辺の同一視、fiber 内辺の
  退化、face の扱い。R1 の抽出規約と同一物)を固定し、`U = {q ≤ q' : 一様}` に
  ついて (a) **共通粗化で閉じない**: 6 角形 `a…f` で `{a, c}` 併合・`{d, f}` 併合は
  それぞれ `J = (0, 0)`、同時併合で hidden = 1、(b) **区間で閉じない**: 経路
  `a–b–c–d` で `{a, d}` 併合は phantom = 1、全併合は `(0, 0)`(非空虚版は正方形 +
  pendant 経路で `(0,0) → (1,0) → (0,0)`)、(c) 4-cycle の辺縮約 4 本は `U` の
  極大元の反鎖、(d) よって貪欲併合は失敗する。いずれも玩具の線形代数で裏取り済み
  (証拠ではない)。
- なぜ CS の外が気にするか: 抽象解釈には最粗の完全精細化が常にあり、bisimulation
  と lumpability には最粗の正確な商が、十分統計量には最小十分が一意にある。Atlas は
  「一意でない側」に立ち、理由は `H¹` が商で湧きも消えもする構造にある。実務の
  問い「どこまで降りるか」の答えが一点でなく稜線だと言い切れる。
- 位置: 横の稜線(R4b の構造半分、R5 の否定半分)。
- 判定: witness の Lean 化。「H¹ は閉包作用素でないから当然」という読みに対しては、
  失われた束的性質を GRS の証明と対置して一文で言う。
- 規模: 小。

### R11 検証済み証書パイプライン

- 内容: ArchSig / harness が各 `A` の rank 証書(下界 = 選んだ小行列とその逆行列、
  上界 = 全列を選択列の線形結合で表す係数。行列積だけで検査でき行列式を要しない)
  を出し、Lean が soundness を証明した checker が検査する。Tier 1 = `lake exe`
  (compile 済み、全規模)、Tier 2 = 小部分系で kernel `decide`。検証される範囲は
  presentation から先(nerve → `H¹` → `J_A` と G-104 / G-107 の意味論への接続)で
  あり、source → ArchMap → presentation の観測の忠実性は設計上検証しない(ArchMap
  author の責務。CompCert が C の意味論を信頼するのと同じ位置)。差分テスト
  (ランダム presentation で harness と checker を突合)を実験設計に含める。
- 規律: 「Lean で検査済み」を ArchSig の正当化に転用しない。checker は AAT 側の
  監査器であり、badge は第三の artifact として出す。
- 位置: 土台補強。規模: Lean 2〜4k 行、harness 数百行。リスク: 係数体(R0)、
  `decide` の詰まり、一様モードの `2^|Target|`(R4a)。
- 判定: 実システムの数値(R1)と、checker が harness の誤りを弾いた実績の両方。

### R12 エージェント読解(別 PRD / 別論文)

- 内容: 深さマップを「規約整合診断に対する解像度安全な読み方針」として使い、
  粗い文脈 / 細い文脈全域 / 深さマップ誘導(粗で読み `J_A ≠ 0` の領域だけ降りる)/
  同一トークン予算の既存戦略(Agentless、HCP、RepoGraph 系)を比較する。正解は
  実コードへの注入(fiber を切って phantom 形、内部三角形を足して hidden 形)で統制。
  予言: FP は phantom 領域、FN は hidden 領域に集中し、`J = 0` 領域では粗 ≈ 細。
  観測起因の誤り(理論が天井を決める)と推論起因の誤り(モデル性能)を分離する
  評価枠。
- 名乗り: 「安全な文脈圧縮の定理」とは言わない(禁忌 4)。venue は AI4SE(ASE /
  FSE / ICSE の枠)。
- 位置: 横の稜線。規模: 中。

### R13 方法論論文(別トラック)

- 内容: 「AI が書いた 35 万行の数学に機械の門を立てた」を論文にする条件は三つ:
  GOAL ごとの statement 改訂数・反証数・cycle 数・指摘分類のデータ、核が弾けない
  欠陥の分類学(空虚な真、structure-field escape、answer-encoding、premise 密輸、
  定義の言い換え)とそれを塞いだ装置(premise ledger、anti-weakening、dullness
  filter、公理監査)、外部が気にする定理が一つあること(= Atlas + R1)。データで
  書けなければ出さない。
- 位置: 横の稜線(執筆トラック)。

## 5. 優先順位と配分

- 優先順位: **R0 > R2 > R8 > R1a > R10 > R3-w > R4a > R9 > R1c > R11 > R3-r > R4b
  > R5 ≫ R7**。R12・R13 は別トラック。R1a は Codex 並走で理論項目と同時に進む。
- Atlas 論文(2 本目)の骨格: 枠 = コード観測と解像度(§2)/ 対象 = 比較写像
  と欠損 / 主定理 = 安定性(G-104)+ 還元と decider(G-107 (i)(ii))+ 局所観測
  の限界(G-107 (v))+ 必要条件 C3′ と押し出し系(R8)/ 実測 = R1a / 差分 = R2 /
  応用節 = 三担い手。R10・R4a・R3 は改訂で取り込み、R5・R6 は節として置く。
- 後継 GOAL の単位: R8、R10、R3-w、R4a、R9、R3-r、R5 をそれぞれ 1 カード(採番は
  起票時)。G-104 / G-107 の fixed statement は変更しない。active GOAL と並走可能
  かはコスト基準で裁定する。
- 論文A との関係: R1 は論文A 実証節計画の第三段と同一対象であり、Atlas 論文が
  先行して測り、論文A はその結果を参照する。
- 止め方: R2 の判定で実証研究が無く、R1 の深さマップが全域非零なら、Atlas は
  「AAT の測定器の校正理論」として正確に主張し、CS hook は exactness と「局所 ⟹
  大域」族の差分表のみで戦う。全域零なら method 水準と他系へ進む。どちらの結果も
  資産として記録する。

## 6. 判定規準 — 「CS に届いた」の定義

次の三つが揃ったとき、Atlas は AAT の外に貢献したと言う。

1. §1.1 の統一表の各行に、§3 の外部先行との差分が肯定形で書けている(R2)。
2. 実システムで深さマップが領域ごと・欠損源ごとに割れ、phantom と hidden の両方に
   実例がある(R1a)。概念またぎ(P3)と打ち消し例は必答の問いとして報告する。
3. R8 の必要条件 C3′、R10 の非一意性、R4a の計算量、R3-r の半径族のいずれかが
   定理として立っている(R3-w は補助定理と数え、単独では数えない)。

揃わない場合の主張は「AAT の測定器の校正理論」であり、それ以上を名乗らない。
本計画の停止規則は研究の全体目標の禁忌に従う: 比喩に定理の代役をさせない(4)、
関手性・合成閉・rank–nullity のような言い換えに定理の名を与えない(5)、`J_A` と
そこから導かれる整数(幅など)以外の数を並べない(6)、計測に降りない定理を積まない
(7)。

## 7. 説明素材 — 還元の玩具計算

[`research/experiments/atlas-reduction-toy/depth_map_toy.py`](../../research/experiments/atlas-reduction-toy/depth_map_toy.py)
は、還元(G-107 (i))を外部ライブラリなしの ℚ 線形代数で見せる玩具である
(証拠ではない。定理の正本は G-107 report と Lean)。

- 系 A: 4 サービス 11 モジュール 3 概念。配線だけから領域ごとの
  `(phantom, hidden)` を出し、観点(law)を 4 種入れて直接計算しても深さマップ
  の値の和に分解されること、各領域 `A` が指示 law の 1 クラスとして実現できる
  ことを確認する。
- 系 B: サービス内部の輪が 2 概念にまたがる変種。単独概念の領域では欠損が
  消え、2 概念の和集合で現れる — `A` が集合で効くことの例示(§1.4 の 2)。
- 簡略化: 概念は両水準で同じ(canonical factor は恒等)、サービス内部の辺は
  すべて退化、混在 face なし、pullback は辺の向きが揃う前提で符号なし。計算の
  形は本物と同じで、細側の領域が `π⁻¹(A)` になる点と、一般の分割では符号付き
  pullback が要る点が異なる。
- R3-w・R10 の witness(交互多角形、6 角形の併合、経路の距離 3 併合、4-cycle の
  辺縮約)は同じ線形代数で再導出できる。カード起票時に Lean の witness として
  固定する。

統一表の各行を玩具で動かして見せる用途(論文の付録・記事・登壇)に限る。

## 8. 範囲・規律

- 本ノートは正本ではない。G-104 / G-107 の事実関係は各 report を、証明義務を
  持つ statement の固定はカード起票時を正とする。
- §1.2・§4 の R3 / R4 / R8 / R10 に書いた数学(Leray 帳簿、必要条件 C3′、C^loc、
  coNP 完全性、`T_n` 族、非一意性 witness)はすべて candidate であり、手証明と
  有限例の機械裏取りしか無い。Lean で立つまで、本文・記事・カードの statement に
  事実として書かない。
- 本計画は G-104 / G-107 の fixed statement を変更しない。補強はすべて後継
  GOAL・PRD・論文の側で行う。
- 命名: Atlas は G-104 の固有名であり、正式名は維持する。観測の枠への置き直しは
  定理名の変更を伴わない。
- 隊列は指針であり、採否・順序はユーザー裁定を正とする。運用上の状態は GOAL
  カードと tracking Issue が正本である。
