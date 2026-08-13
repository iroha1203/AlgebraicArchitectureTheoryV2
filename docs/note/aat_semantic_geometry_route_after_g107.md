# Semantic Geometry of Architecture — 測量台帳と行程表

本ノートは考察ノートである。新しい公理・定義・定理は導入せず、証明済み定理の
statement を変更しない。目的は、研究プログラム
**Semantic Geometry of Architecture**(命名規律: 本リポジトリでは略さない)の
全体地図の上に現在地を固定し、進むべき道を評価することである。

将来の statement はすべて未証明の candidate であり、隊列の採否はユーザー
裁定に従う。lifecycle の経緯(PR・Issue・裁定日)は各 report と tracking
Issue を正本とし、本ノートには持ち込まない。

## 要旨

1. AAT には二つの頂が立った。SAGA(修復の意味論)と G-107(診断の意味論)で
   ある。G-105 の反証は失敗ではなく、係数選択の理論という主題の実在を示す
   証拠になった。
2. 意味のモジュライへの問いを台帳にすると、静力学(存在・修復・座標・決定
   可能性・位置・観測限界)は定理で埋まり、未測量域はすべて「射」の側に
   ある。プログラムの重心は点の理論から射の理論へ移る。
3. 二頂を結ぶ大定理候補が統合正方形である。前提整備 S0 と定理候補 S1–S5 に
   分解した。単一正方形は G-106 の完成を待たずに詰められる見込みがある。
4. 登路の第一手は G-106 である。理由は唯一の着手可能 draft であり、どの
   裁定でも投資が死なないこと。山頂(Semantic Scheme Representability、
   呼び名 SHIGURE)はまだ素描であり、幹は「台帳の行を埋める作業の、山頂
   方向への整列」として設計する。
5. 並走作業は、統合定理の設計ノート、論文A(実証節 PRD と本文執筆)。後続
   draft は G6 → 係数 base change → G-105 後継 → Gr4 の優先順とする。

## 参照

参照は二区分する。**正本**(事実関係の判定基準):

- [G-107 report](../../research/reports/G-107-aat-uniform-invariance-characterization.md)(完了判定)
- [G-105 report](../../research/reports/G-105-aat-structural-cover-invariance.md)(反証)
- [G-106 カード](../../research/goals/G-106-aat-transport-coherence.md)
- [第X部 Semantic Repair / Descent / SAGA](../aat/algebraic_geometric_theory/part_10_semantic_repair_descent_saga.md)

**上流考察ノート**(定義・分割の初出。正本ではない):

- [表示的意味論ノート](aat_denotational_semantics_of_architecture.md)(プログラム定義=§11、山頂 candidate=§10)
- [解像度診断の設計ノート](aat_resolution_diagnostic_design.md)(observation factorization、成果物の四分法)
- [Atom Is All You Need 考察ノート](atom_is_all_you_need_discussion.md)(§3.5 達成階梯、§10 スキームへの橋、§12 論文ロードマップ)
- [G-104 係数生成契約ノート](aat_g104_coefficient_generation_contract.md)(K0 / K1 契約の設計経緯)

---

## 1. 現在地 — 二つの頂と一つの反証

### 1.1 二つの頂

**SAGA 定理系列(第X部)は修復の意味論である。** semantic repair 側
(Atom と局所 state)と代数幾何側(equation system と Čech complex)を、
presentation exactness の下で係数同型 `M_sem ≃ Q_E` により結ぶ。両側で独立に
作った residual class は `κ_*([r_sem]) = [r_E]` で対応し、true sheaf 条件
込みで次が立つ(第X部定理8.2 Grounded Global Gluing ほか)。

```text
[r_sem] = 0  ⟺  actual global repair が存在する
```

障害類が「実際の大域修復可能性」を意味することの保証であり、存在論を担う。

**G-107(証明済み)は診断の意味論である。** Uniform Invariance Defect
Semantics and Nonfactorization Theorem は次の五つを固定した。

- (i) law 全量化の一様不変性を、有限 block の defect profile
  `J_A = (dim ker, dim coker)` の零判定へ還元する。
- (ii) computable presentation 上の sound / complete decider を立て、判定の
  正本を計算に置く。
- (iii)(iv) 幾何述語 `ConditionCAllA` により Atlas 定理の位置を定める。
  `Condition-C locus ⊊ uniform locus` が包含+真性(7 witness)で立つ。
- (v) 半径1観測 grammar `G_local-v1` 相対で、零判定が観測を factor しない
  (T3 / T6 分離)。

真理へのアクセス可能性と限界、すなわち認識論を担う。(v) は観測 grammar
相対の非表現性定理としては AAT 初である。反証定理や不可能 witness
(G-105 の発火不能定理など)とは種類を区別する。

分業を一行で言えばこうなる。**SAGA が修復障害の意味を与え、G-107 がその
意味を診断・比較できる範囲を与える。** 両者は直交し、互いの価値を毀損
しない。

### 1.2 一つの反証 — G-105 と saturation

G-105(Structural Cover Base Invariance Theorem)は `target-refuted` で
ある。生成された all-complex が anchor cone 化により H¹ 恒零となり
(`generatedAllComplex_h1Zero`)、非零診断の発火 witness が原理的に不能に
なった(`generated_firing_witness_impossible`)。これは表示的意味論ノート
§10 の candidate「semantic saturation — 情報を無差別に充填すると診断幾何が
消える」を、生成 nerve の系統で定理水準に固定した結果である。

この反証は失敗ではない。**law-selected nerve・係数選択の必要性**という設計
テーゼの、生成 nerve 系統における最初の Lean 水準の証拠である。なお同
ノート §10 の saturation candidate の記述は、この同じ Lean 結果の再読で
あって独立の2例目ではない。宣言 nerve 系統での2例目はまだ存在せず、
定理化が「未」である理由もここにある。

診断幾何は「何を観測に含めるか」の選択によってのみ非自明になる。この選択の
理論こそ本プログラムの主題であり、反証は主題の実在を示す。反証までに放電
された Cycle 資産(I0–I3b: canonical nerve 生成、構造 nerve 等式、全 Atom
nerve 可変性、係数生成と naturality、構造局在)は有効成果として保持され、
生成構成の改訂路線は後継カードで固定する。

### 1.3 前例の測量

G-107 (v) の分離論法(局所同一・大域相違)には系譜がある。有限モデル理論の
Hanf / Gaifman 局所性(T3 / T6 型の単一 cycle 対はこの系譜の例)、1-WL
テスト(教科書例は頂点数を揃えた C6 vs 2×C3。T3 / T6 とは同型ではなく暗合の
水準)、分散計算の locally checkable labeling である。

一方、次の三点の組み合わせには既知の前例が見つかっていない: (a) 性質自体は
決定可能なのに局所観測不能というペア構成、(b) 局所性型非表現性の機械検証、
(c) ソフトウェア設計理論の内製不可能性定理。論文化の際は系統的文献調査を
前提とし、系譜への接続を明示した上で新規性を主張する。

---

## 2. 測量台帳 — 意味のモジュライの問いと現況

表示的意味論ノート §9–11 の構想(意味はモジュライ空間を持ち、その幾何を
研究する)に対し、各問いの現況を一枚に登録する。

表の読み方を先に二つ。「証明済み」は各正本の受理判定を指し、G-10x 系は
Research-proved(数学本文へは unported)、第X部系は数学本文の証明である。
`Z_univ` は uniform locus(一様不変性の零 locus)の program 水準表記なので、
証明済み行の表記は uniform locus に統一する。

| モジュライの問い | 内容 | 現況 |
| --- | --- | --- |
| 存在 | 大域表示の存在 ⟺ 障害類消滅 | 証明済み(第X部定理8.2、conormal descent) |
| 選択の自由度 | 大域表示は `H^0` torsor | 証明済み(conormal descent package 第3項) |
| 修復の意味 | `[r] = 0` ⟺ actual global repair | 証明済み(SAGA、第X部定理8.2) |
| 解像度不変性 | 条件 C 下の H¹ 保存+反例3種 | 証明済み(G-104 Atlas 定理) |
| 座標 | semantic 座標 `J_L` ⟺ computational 座標 `J_A` | 証明済み(G-107 (i)) |
| 決定可能性 | 零判定の sound / complete decider | 証明済み(G-107 (ii)) |
| 既知の安全域の位置 | `Condition-C locus ⊊ uniform locus` | 証明済み(G-107 (iii)(iv)) |
| 観測限界 | uniform locus は `G_local-v1` で定義不能 | 証明済み(G-107 (v)、grammar 相対) |
| 飽和 | 無差別充填で診断幾何が消える | Lean 確定1例(G-105 反証)。定理化は未 |
| 輸送の整合 | 二経路輸送・三者調停の 2-cocycle 障害 | 未(G-106) |
| cover–nerve 辞書 | SAGA の cover と G-107 の nerve の形式的対応 | 未 formal 化(S0。S1 / S2 の前提整備) |
| SAGA 前提の安定性 | exactness / true sheaf の `CoarserThan` 安定性 | 未(S2。非対称の見立てあり) |
| 底空間の安定性 | 構造台 nerve が「安定な底空間」を供給する | 供給者空席(旧候補9 = G-105 refuted。後継カードで再建) |
| 変形 | modification の `J_A` への作用 | 未(設計ノート §4 / §7 素材) |
| 底の base change | doctrine 圏の fiber product | 未(階梯 Gr4、Atom ノート §10 ギャップ2) |
| 表現可能性 | `Sem_{A,r}(R) ≃ Hom(Spec R, M_{A,r})` | 未(山頂 candidate、呼び名 SHIGURE) |
| 動力学(SFT) | 意味のモジュライ上の軌道・場 | 範囲外(プログラム定義 §11 の座) |
| 計算への換金 | decider の ArchSig 搭載など | 範囲外(実証節 PRD・ArchSig 改修系列) |

読みどころは三つある。

第一に、**静力学の上半分が定理で埋まった**。意味の空間は「存在が判定でき、
既知の安全地帯の位置が確定し、観測限界線まで引かれた」測量済み地帯を持つ。

第二に、**未測量域はすべて「射」の側にある**。輸送・変形・表現可能性は、
意味の空間の点ではなく射(reading 変更、modification、係数変更)の振る舞いを
問う。プログラムの重心は点の理論から射の理論へ移る局面にある。

第三に、飽和の証拠は、係数選択の理論(何を観測するかの幾何)が独立の問いで
あることを示す。

### 台帳の裏面 — 飽和回避の設計原理

G-105 の反証と G-104 / G-107 の成功を並べると、一つの設計原理が浮かぶ。
**どの層を宣言に残し、どの層を生成するかの分割線が、診断 cohomology の
生死を左右する。**

正確な機構は三段である。空間の生成述語と係数の label 述語を同一の述語から
取ると(G-105 では `extracts`)、各 label の supported tuple が全充填される。
全充填の下で台非空から apex が選べると、各 block が cone 化して H¹ が
消える。G-104 / G-107 が飽和を免れたのは条項の巧妙さではなく、空間(宣言
incidence)と係数(law 値)の生成源が最初から別データだったからである。
「構造が空間を運び、意味が係数を運ぶ」テーゼの反面教師的裏付けと言える。

ただし適用には apex 条件が要る。同一生成源でも tuple を選別する規則は
cone 化しないので、無条件の標語としては読まない。G-106 が 2-cell を宣言
入力に置く設計は、この原理の H² 版(全 parallel pair への無差別 2-cell
充填の回避)として読める。

定理化素材は「apex 条件付き cone 化定理+law-selected 非零 witness」の対で
ある。cone 化定理単体は古典事実の再証明に近く、対にして初めて設計定理に
なる。§5 の後継カード素材に含める。

---

## 3. 統合正方形 — 二頂を結ぶ大定理候補

SAGA(横)と reading comparison(縦)の関係を candidate statement 水準で
固定する。記法の正本は第X部(SAGA 側)と G-107 カード(comparison 側)で
あり、以下の見立ては一次資料の突合に基づくが、いずれも未放電である。

**設定。** comparison geometry `f`(読み対 `q ≤ q'`、canonical `π`、K1
導出台つき nerve 対、nerve 射 `φ`)を G-107 の語彙で固定する。SAGA 側は
各読みの cover `U` 上で、presentation exactness と true sheaf 条件の下に
係数同型 `M_sem ≃ Q_E`、`κ : H¹_sem(U) ≅ Ȟ¹(U, Q_E)`、residual 対応
`κ_*([r_sem]) = [r_E]` を持つ。正方形は次である(比較写像の向きは G-107 に
合わせ粗 → 細)。

```text
H¹_sem(U_fine)   ── κ_fine ──▶   Ȟ¹(U_fine, Q_E)
      ▲                                ▲
      │ τ_sem(未構成)                  │ f*(refinement 写像。S3 参照)
      │                                │
H¹_sem(U_coarse) ── κ_coarse ──▶ Ȟ¹(U_coarse, Q_E)
```

candidate は前提整備1本+定理候補5本に分解した。一覧:

| 記号 | 名前 | 一行で | 難所 |
| --- | --- | --- | --- |
| S0 | cover–nerve 辞書 | 二つの形式系を結ぶ橋の建設 | 橋がどこにも存在しない。最初の関門 |
| S1 | `Q_E` 実現 | SAGA 係数を law-generated 係数で実現 | 文字通りには不成立。class 宣言+直和因子へ後退 |
| S2 | 前提の解像度安定性 | SAGA 前提を両読みに置く方法 | 転送は両向き不安定。ambient 化が本線 |
| S3 | 自然性 | 正方形の可換性 | 実質は「比較写像 = refinement 写像」の同定 |
| S4 | 粗視化診断の信頼性 | 粗の零 ⟺ 細の零+接地 | 二段構成の明示 |
| S5 | jump の修復論的意味 | 非零 defect の分類 | coker 枝は素朴には実現不能(no-go) |

### S0 — cover–nerve 辞書

SAGA 側の cover(`S_X` の context 圏上の `Int_{≤2}(𝒰)`: chart・pairwise・
triple)と、G-107 側の台つき宣言 nerve(K1 導出台、`q.Target` 部分集合)を
結ぶ形式的対応。**両形式系を結ぶ橋は現状どこにも formal 化されていない。**
独立な二系統の精査が同じ欠落へ到達し、SAGA 証明記録も nerve を selected
simplicial data と明記して atom 水準交叉からの生成を主張していない。

設計上の注意は三点ある。

1. 「chart ↦ 台、empty-overlap normalization ↦ 台非空性」は素朴には iff に
   ならない。target 影の交わりが非空でも context overlap は空でありうる
   ため、K1 導出で edge 台を作ると、SAGA が除いた空 overlap の位置に非空台
   edge が生える。辞書は「overlap 空 ⟺ 導出台空」が成立する cover class への
   制限を statement に含める。
2. 辞書の像は G-107 nerve class の真部分である。monomorphic cover の Čech
   complex は self-loop・平行辺を持たないが、G-107 の defect 機構と witness
   群(free-pair、digon、ternary cycle)はそれらに依存する。G-107 の判定
   装置の SAGA 側適用は、像 class 上の一様不変性に制限される。
3. 辞書は「reading ↦ cover 割当」の関手性(粗 reading に粗 cover を
   割り当てる規則の自然性)まで含めて、初めて S1–S3 の前提になる。

### S1 — `Q_E` 実現

文字通りの形(`Q_E ≅` ある `L_E` の K0 / K1 生成係数)は成立しない見込みが
高い。`Q_E = O_E / I_Ob^E` は context ごとの可換群で torsion を持ちうる
(第X部 例 10.2 の canonical circle example に `ℤ/2`。構成は第III部に
基づく)一方、K0 / K1 は係数体 `ℚ` に固定されているからである。

そこで二段構えにする。

**(H_Q) — class の宣言。** `Q_E` が「A-subnerve 上定数 `ℚ`、restriction は
label 対角」の有限直和に分解する equation system の class を宣言する。宣言は
per-cover ではなく ambient(`S_X` 上の presheaf として分解)で行う。粗細
それぞれに独立に宣言すると、比較写像が block を保つこと(intertwining)が
出ず、直和因子論法が閉じないからである。「係数環 `ℚ` の regime」の意味も
宣言時に固定する — `O_E` を `ℚ` 上で取る実装制約か、`− ⊗ ℚ` の係数拡大
込みか。後者なら拡大と H¹ 比較の可換性が追加の証明義務になる。

(H_Q) は K0 / K1 の弱化ではなく `Q_E` 側の対象 class の宣言であることを
ledger 区分で明示する。ただし書式だけでは anti-weakening 批判を回避でき
ないため、**class の非空性 witness(toy でない SAGA instance 1点の所属
証明)を放電義務に含める**。

**S1′ — 直和因子定理。** (H_Q) の下で、indicator law family の有限直和
`L_E` は両読みに adequate になる(indicator は粗 target 経由で定義される
ため adequacy が構成的に自動 — G-107 の `indicatorLawFamily_adequate_both`
の直和延長)。このとき `Q_E` 係数の Čech H¹ 比較は、`L_E` の K0 / K1 生成
H¹ 比較の直和因子と同型になる。complement block の混入は、一様不変性が全
非空 `A` を量化するため無害である。系として「一様不変 ⟹ SAGA 障害の H¹
水準の保存」が従う。class 外の `ℤ/2` 例は scope 外証人として固定する。

### S2 — SAGA 前提の解像度安定性

見立ての答えは、対称な転送定理ではなく非対称である。

**presentation exactness は両向き不安定。** 粗→細は completeness に、細→粗は
generation に、それぞれ反例の芽がある。soundness だけは local state が
非空な context で補題 6.2A から自動になるが、非空性が落ちる context では
その限りでない。安定な置き場は転送ではなく **ambient 化**である — 前提を
ambient に一度だけ置き、両読みをその instance として得る。第X部の定理 6.3
第二節と系 8.3 が既にこの形を採っている。ただし全 `S_X` への量化は過剰で
ありうる。正方形が実際に消費するのは両 cover の intersection diagram の
合併までなので、量化域をそこへ絞る選択肢を statement 設計に含める。

**true sheaf 条件は片方向だけ安定。** cover 非依存部分(sheaf 性・作用)が
支配的で、cover 所属は細⟹粗が sieve 単調性から証明可能。粗⟹細は fiberwise
covering(C0\* 型条件の cover 水準版)を要する条件付きになる。

したがって S2 は「転送が一般には不成立であることの負例2種+ambient 化で
十分であることの定理」の対として立てる。負例の受理条件は material 入力
class(第X部定義 3.1 の semantic repair presentation+equation system)内で
の実現とする。抽象群 presentation だけの構成は証拠にならない。

### S3 — 自然性

主張は `κ_fine ∘ τ_sem = f* ∘ κ_coarse`。`τ_sem` には cochain 水準の直接
実装候補がある。粗 atlas `(p_c)` の制限で細 atlas `p_d := p_{π(d)}|_{U_d}`
を取ると、細 residual は粗 residual の引き戻しと cochain 水準で一致し、
fiber 内成分は torsor 差の一意性で消える。さらに ambient 化(S2)を採ると、
`κ_coarse` と `κ_fine` は単一の `Φ : M_sem ≅ Q_E` から誘導されるため、
可換性は `Φ` の自然性一本に還元される見込みである。

二つの帰結に注意する。

第一に、右縦の `f*` は S0–S1 成立前には `Ȟ¹(U, Q_E)` 間の写像として型が
合わない。SAGA 内在的には cover refinement 写像として定義できるので、
**S3 の実質は「G-107 比較写像 = refinement 写像」の同定 theorem** にある。

第二に、この設計の下では `[r_fine] = τ_sem [r_coarse]` が class 水準で
`J_A` の値と無関係に成立する(定理 7.5 型の torsor 論法)。つまり **S4 の
「粗零 ⟹ 細零」方向は一様不変性なしで出る**。一様不変性が本当に消費される
のは逆方向(単射性 = 粗の見かけ障害の排除)である。

この経路なら、単一正方形の可換性は G-106 を待たずに詰められる。G-106 が
要るのは、正方形の族の合成整合(functor 水準)と stack 経路である。

### S4 — 粗視化診断の信頼性

二段で述べる。

**一段目(零類同値)**: S0–S3 と一様不変性の下で
`[r_sem, coarse] = 0 ⟺ [r_sem, fine] = 0`。⟹ は S3 から無条件に出て、⟸ が
一様不変性を消費する。

**二段目(actual repair への接地)**: 細側の grounding(true sheaf+cover
所属 = S2 の fiberwise covering 脚)を追加消費して、初めて「粗い読みの修復
診断が actual global repair 可能性について信頼できる」に到達する。

S4 の固有内容はこの二段目にある。二段構成を明示することが「最終目的地」の
看板を正確にする。

### S5 — jump の修復論的意味

非零 `J_A` の下での residual の関係を分類する。三部構成とする。

1. **kernel 枝(粗の見かけ障害が細で消える)**は、同一修復問題の residual
   対で実現可能である。
2. **cokernel 枝(細の障害を粗が見逃す)は、固定 `P_sem` の下では residual
   対によって実現不能である。** S3 の torsor 論法により `[r_fine]` は常に
   `τ_sem` の像に入るからである。この no-go 自体を lemma として固定する
   (S3 と S5 の素朴な両立不能の解消)。
3. cokernel の修復論的意味は、reading 依存の `P_sem`(細分で新しい
   mismatch が出現する設定。この場合 S3 の単一 `Φ` 設計は二本の `Φ`+係数
   比較へ改訂される)か、modification による問題変形の下でのみ立つ。
   modification calculus(後継 certificate 素材)との接続点はここにある。

### 依存関係と failure policy

S0 が全ての前提整備である。S1・S2 は S0 の辞書の上で互いに独立で、いずれも
G-106 に依存しない。S3 の単一正方形は S0–S2 と atlas-restriction 経路で
G-106 非依存に詰められる見込み。G-106 に依存するのは正方形の族の合成整合と
stack 経路のみ。S4 は S0–S3 と G-107 (i)(ii) に、S5 の第三部は modification
calculus に依存する。

したがって並走計画の実質は「G-106 が走る間に S0 → S1 / S2 を放電可能な形
まで固める」ことであり、統合定理の可行性は当初見立てより高い。左列は
G-106 の完成を待たない。

failure policy の素描:

- (H_Q) の非空性 witness が立たない場合、`Q_E` の filtration の graded
  piece が subnerve 上定数になる形の直接比較定理へ後退する。G-107 は
  graded piece ごとの判定装置として間接利用する。
- S1 の中心障害(torsion vs `ℚ` 固定)は係数 base change(`ℚ` → R)が解消
  しうる。base change 側の進捗次第で (H_Q) の迂回自体が不要になる可能性を
  統合設計に織り込む。
- S2 の転送不成立は failure ではなく設計である(ambient 化が本線)。
  fiberwise covering が立たない場合は片行 SAGA の非対称形に弱める。S4
  一段目の片方向は残る。
- S3 の反例は統合定理の refuted ではなく、`τ_sem` の輸送設計(G-106 の
  2-cell 語彙)の改訂材料として扱う。

この正方形は、G-107 カードの program context(reading 圏 `Read_L` 上の
診断 local-system)が予告した functor 水準の正確化と同一の山である。

---

## 4. 登路 — 山頂への幹と支線

### 4.1 山頂と、統合定理の正直な位置

山頂は Semantic Scheme Representability(表示的意味論ノート §10 のカード
草案)である。呼び名は **SHIGURE**(Semantic–Hom Identification:
Geometric Universal Representability Equivalence)— backronym が statement
`Sem_{A,r}(R) ≃ Hom(Spec R, M_{A,r})` の同定・普遍性・自然同値に対応し、
片時雨(局所では別々の雨、空は一つ)が descent 貼り合わせの写し絵になる。
GAGA → SAGA の系譜の先に日本語の名を置く。呼び名の地位は山頂 candidate の
それであり、正式名は維持し、証明前の昇格はしない(Atlas 定理の命名規律を
踏襲)。草案の着手条件は二つ: (a) K0 / K1 係数生成契約の base change
(`ℚ` 固定から R-代数へ)、(b) set 値 / groupoid 値の裁定。groupoid 値なら
目標は stack 表現可能性に上がり、輸送の 2-cell 整合が前提に入る。

先に正直な記録を一つ。**統合定理(§3)は山頂草案の依存リストにも着手条件
にも入っていない。** 統合は台帳の「粗視化診断の信頼性」行を埋める、幹沿いの
隣接作業であり、山頂への必要条件ではない。

### 4.2 第一手 G-106 の位置

G-106 は、梯子(Gr3 核)・統合族・lax 表示プログラムに対する要石である。
山頂に対しては stack 裁定条件付きであり、set 値に裁定されれば山頂前提から
外れる。それでも第一手に置く実理由は、唯一の statement レビュー収束済み
draft であり、どの裁定でも投資が死なないことである。合流する四系統:

1. **統合正方形の族の合成整合**(§3)。単一正方形は G-106 に先行して
   詰められる見込みだが、族が reading の合成と両立すること(functor 水準)は
   G-106 の 2-cell 整合の領分。
2. **山頂の stack 版前提**(条件付き)。
3. **lax 表示プログラム**。破れの 2-cell 化、gauge orbit、H¹ → H² の表示
   次数階段。
4. **G-105 改訂との接続**。G-106 の確定事項に syzygy 整合が
   direction-hypothesis として入っており、G-105 の反証が要求する生成構成の
   改訂と語彙を共有する。

```text
現在地               第一手(Gr3 核)        隣接大定理          山頂前提                山頂
SAGA + G-107 ──▶ G-106 輸送整合 ──┬▶ SAGA×G-107 統合   係数 base change(ℚ→R) ──▶ Semantic Scheme /
(二頂+測量台帳)  (2-cell)          │  (S0–S5。山頂非依存) + 底の base change         Stack Representability
                                  └─────────────────▶ (doctrine fiber product
                                                       = Gr4、EGA 的相対性)

支線: 後継 certificate 素材+modification calculus
      (機構カタログ4点組 → repair 変形理論。第V部 repair 系譜と接続)
```

### 4.3 Gr4 の素描

Gr4(底の base change 完備)の証明義務は5層に分解できる。

- **(A) `Doct_U` の fiber product の構成と普遍性。** 終対象を置かない原理に
  より、絶対積ではなく本質的に相対的な引き戻しのみを立てる。集合論的
  引き戻し+成分構造で「定義展開」に堕ちる dullness リスクが高い。真部分
  fiber 条件の witness と、identity cone に制限しない普遍性で防ぐ。
- **(B) cartesian lift。** `sourceMap` が非可逆なので、存在自体が無条件かは
  開いている。成果物形式は「構成」ではなく「存在条件の同定+存在しない
  反例」とする。存在が条件付きなら (C)(D) はその条件を継承する。
- **(C) Beck–Chevalley 型交換。** fiber product square 上の押し出し・
  引き戻し交換の canonical 比較射とその同型性。ただし fiber 側データが
  Set 的 family fibration に還元される場合、交換は古典的に無条件成立して
  「集合論的 Beck–Chevalley の再証明」に堕ちる。交換が破れる非 pullback /
  lax square の negative witness を対で要求して、初めて数学的本体と呼べる。
- **(D) 診断の base change 可換性。** 無条件では成立しない見込みで、成立
  条件の同定自体が定理になる。「不変性+条件+反例」型で G-104 / G-107 の
  方法論資産が効く、カードの数学的重心。語彙の注意: 「flat base change
  類似」の flat は lawful locus の既存命名 `Flat_U(X)` と衝突するため、
  起票前に語彙を裁定する。先行考察はスキーム射幾何ノートの fiber product・
  derived fiber product・functor of points の各節を素材とする。
- **(E) 閉性。** pullback square の貼り合わせ。G-106 の合成 coherence に
  依存する唯一の層。

前提状況は「doctrine 圏の定義自体が先行課題」から大きく縮小している。
G-101 が圏 `Doct_U`・`ExtInst_U`・opcartesian 普遍性
(`transportAlongHom_isStronglyCocartesian`)まで建設済みで、残るは極限構造の
不在、refinement 射の圏化、どの圏の fiber product を心臓と呼ぶかの裁定の
3点である。リスクの筆頭は Boolean regime の零次元性により fiber product が
集合論的交わりへ退化すること — 非自明性は (C) の negative witness と (D) に
置く。G-106 依存は (E) に局所化できるため、Gr4 の大部分は G-106 と並走
可能である。

### 4.4 登路の空席と隠れ依存

スキーム橋(Atom ノート §10)の供給表と突合すると、幹に未登録の項目が残る。

1. **底空間の供給者が空席。** 「安定な底空間 ← 候補9」の供給が G-105 反証で
   失われた。§5 の G-105 後継カードは、この空席の再建として幹に位置づく。
2. **affine 被覆の存在(橋のギャップ3)に担い手がない。** 山頂の実質は
   cover 上の descent 貼り合わせだが、貼り合わせるべき affine 被覆の存在は
   定理化も公理化も未裁定である(最近傍は候補6(b)、Loader 型決定不能性
   リスクあり)。このギャップには、山頂カード昇格前に定理化か公理化かの
   裁定を要求する**昇格 blocker** の地位を与える。
3. **G6(blame moduli と gauge 自己同型)は set / groupoid 裁定の証拠供給者
   である。** 山頂 statement の型を決めるため、base change 段と並走で前倒し
   する価値がある。
4. **候補13 と候補8 が担い手不在。** comonadicity(descent 適格被覆の特徴
   づけ)と係数忠実性(`ℚ → R` の R 選択規準)は幹の暗黙前提であり、統合
   ノートまたは base change カード起草時に引き受け先を裁定する。
5. **G-106 の syzygy 整合は仮定である。** direction-hypothesis なので、統合
   定理が G-106 の H² 語りを使う場合はこの仮定が statement へ伝播する。
   仮定つきで明示するか、仮定を落とせる部分核だけ使うかを統合ノートで
   裁定する。

### 4.5 山頂改訂耐性

山頂草案は statement 固定もレビューも経ていない素描であり、最大リスクと
して循環定義が草案自身に記録されている。山頂が改訂・後退した場合の幹の
生存性は次の通り。

- G-106 — 梯子(Gr3 核)・統合族・lax プログラムの価値で生存
- Gr4 — 梯子の価値で生存
- G-105 後継 — 台帳「底空間」行の価値で生存
- 統合定理 — 台帳「粗視化診断の信頼性」行の価値で生存
- 山頂専用の投資 — stack 版準備と係数 base change の一部のみ

つまり幹は「山頂前提の全逆算」ではなく、**台帳の行を埋める作業の、山頂
方向への整列**であり、sunk cost 構造は良好である。

### 4.6 Atom 基礎論の梯子との重なり — 正確な範囲

Atom Is All You Need 考察ノート §3.5 の階梯(Gr0 比喩 → Gr1 statement 化 →
Gr2 構成実例 → Gr3 擬関手的整合 → Gr4 base change 完備)と幹は、**G-106 の
区間を共有する二本の登路**である。

正確に言う。G-106 は Gr3 の 2-障害核である。Gr3 の定義に含まれる「段横断
の」合成整合は G-106 の boundary 外(frontier の観察止まり)なので、
**G-106 完遂 = Gr3 達成ではない**。Gr3 の完成には段横断整合の後続カードを
要する。Gr4(doctrine 圏の fiber product による**底の** base change 完備。
「EGA 的な意味の相対性に届くのは Gr4」)は、山頂前提の**係数** base change
(`ℚ` → R)とは別軸であり、山頂草案の相対的視点要求を埋める。逆に山頂には
梯子が要求しない義務(functor 独立定義の非退化性、affine 被覆の存在、
descent 貼り合わせ)が残る。

両登路は中央区間を共有し、両端で分岐する。この正確な範囲を記録することが、
G-106 完遂を Gr3 達成として誤記する将来の事故を防ぐ。

### 4.7 支線

後継 certificate 素材と modification calculus は幹と独立に価値を持つ。
ただし設計ノート §7 の規律(機構カタログを先に整備してから後継 certificate
を設計する)に従うと、幹より準備コストが高い。幹の G-106 は statement
レビュー収束済みの draft であり、G-105 を predecessor として参照しないため
その反証の影響も受けない。着手可能性で勝る。

---

## 5. 隊列 — 幹優先の路線

採用路線は幹優先である。順序と成果物:

**1. G-106 active 化。** 成果物は三つ — カード `status: draft → active`
同期(statement 変更なし)、README の draft → active 移動、tracking Issue
起票+起動待ち記録。同期後に `$target-theorem-loop` を起動する。選定理由は
§4.2 の通り readiness である。同時 active の研究系 loop は1本を上限とする。

**2. 並走: 統合定理の設計ノート起草。** S0 辞書は単独で独立レビュー可能な
重さがあるため、「S0 辞書ノート」と「S1 / S2 / S3 設計ノート」の2分割も可
(起草時に判断)。目次案:

1. cover–nerve 辞書(S0)の形式化方針 — cover class 制限・像 class 制限・
   reading ↦ cover 関手性
2. S1 の ambient (H_Q) class 宣言と放電経路 — 非空性 witness 義務、`ℚ`
   regime の意味の固定、indicator 直和 family、直和因子論法、`ℤ/2` scope 外
   証人
3. S2 の ambient 化 statement と、material class 内の転送負例2種
4. atlas-restriction による `τ_sem` の cochain 実装、「比較写像 =
   refinement 写像」同定 theorem、S5 coker 枝の no-go lemma
5. G-106 への要求逆算 — 正方形の族の合成整合、syzygy 整合仮定の伝播の扱い
6. 統合定理カード素描(採番は起票時)

完成後にカード起票判断へ。

**3. 並走: 論文A — 実証節 PRD の起草と本文執筆。** 投稿 gate は充足済みで
あり、隣接する近接研究(sheaf-cohomological program analysis 系)が既に
公開されている以上、証明済み成果の非公開期間の延伸は先取権リスクである。
執筆・PRD は loop と資源競合しない。PRD は規律(冒頭「問い」節+候補複数
提示)に従う。

**4. 後続 draft 候補(優先順)。**

1. **G6 換金カード**(blame moduli と gauge 自己同型)— set / groupoid
   裁定の証拠供給者であり、幹(山頂 statement)の型を決めるため最優先。
   mode は証拠供給という性格上 score-phase の可能性があり、起票時に裁定。
2. **係数 base change カード**(`ℚ` → R)— 山頂着手条件 (a) そのもの。
   S1 の torsion 障害を解消しうるシナジーを持つため、統合ノートの完成を
   待たずに起草可能。R の選択規準は候補8(係数忠実性)を判定規律として
   引き受ける。
3. **G-105 後継カード**(底空間供給者の再建)— Cycle 資産(I0–I3b)の
   構造 nerve の上に、係数 label を `source` から `(law, 値)` へ替えた
   law-selected 係数を載せる一点変更で発火を狙う。飽和回避の設計原理
   (§2)の正例側 lemma を route integrity gate として同居させる
   (saturation の独立カード化は裁定事項)。law 語彙と TwoPhase 語彙の
   橋渡し方式も起草時の候補提示事項。target-theorem mode の必須項目を
   満たせる見込みが最も具体的な一枚。
4. **Gr4 カード**(doctrine fiber product)— G-106 依存は閉性層 (E) のみに
   局所化できるため並走可能(§4.3 を claim 素材に)。ただし (D) の成立条件
   同定は起票時に target statement を固定できないリスクがあるため、mode の
   裁定を素描段階で行う。
5. **Gr3 完成カード**(段横断合成整合)— G-106 は Gr3 の 2-障害核であり
   (§4.6)、段横断の一般合成は boundary 外。完成には (0) 塔上層
   (CoreRead → geometry 段)の輸送データの Lean 建設、(i) 段横断合成
   比較射と擬関手的整合、(ii) 段内障害の押し出しと段間障害の合成、が
   要る — (0) は G-101 が意図的に後回しにした上層 lift であり、G-106 の
   2-cell 語彙とは別種の建設なので同一カードに同居させない。起草は
   G-106 の frontier 観察(段横断への拡張・cartesian 相互作用)を見て
   からとし、素描の精度をそこで上げる。

**5. 保留。** 後継 certificate 素材(採番は起票時)+ modification calculus
(機構カタログ整備後)。

路線の理由: G-106 は唯一の即時着手可能 draft であり、set / groupoid の
どちらの裁定でも投資が死なない。統合定理・base change・Gr4 は相互に独立に
進められる部分が大きく、S0–S2 は G-106 と並走できる。ノート・PRD・執筆は
loop と資源が競合しない。後継 certificate 素材は G-106 成果の後のほうが
設計精度が上がる(modification calculus の対象 `J_A` の輸送的性質が固まる
ため)。

---

## 6. 論文・発信への含意

- **論文A(基礎論)**: 実証節 PRD は起草可能(Atom ノート §12)。第三段の
  解像度スイープは、G-107 により「adequate 範囲内の H¹ 安定」の判定が
  decider の定理裏打ち計算になり、測定の地位が上がった。本文執筆は §5 の
  並走項目(先取権リスクの評価込み)。
- **論文B「連合する読み」**: Gr3 系(G-106)と Gr4 が候補17 ほかの核候補を
  供給する。幹の進行がそのまま論文Bの素材蓄積になる。
- **論文C「診断の認識論」**: G-107 (v) がその非自明核(観測と正当化の限界
  定理)を与える。ロードマップ上の投機性評価は改訂対象。G-107 単独の短報
  (機械検証を主役に ITP / CPP 系へ)も選択肢に入る。その場合、短報は
  A → D → B → C の推奨順序の外側の別トラックとして扱い、ロードマップ本体の
  順序は変えない(§1.3 の系統的文献調査を先行させる)。
- **outreach**: 技術系速報記事(Hashnode / Zenn)では 1-WL の C6 vs 2×C3
  との対比が掴みの素材になる(同型ではなく暗合として使う)。思想系
  (Medium)のエッセイ候補は「観測は構造を作らない」— 層論的 contextuality
  との対比(同じ H¹ が、量子では先在する大域構造の不在を、設計では先在する
  構造と観測の限界を測る)を中盤の山に置く。

---

## 7. 範囲・規律

- 本ノートは正本ではない。G-107 / G-105 の事実関係は各 report を正本と
  する。プログラムの定義は表示的意味論ノート §11 に、成果物の分割は設計
  ノート §4 の四分法に従う(いずれも上流考察ノートであり、hard rule の
  正本ではない)。
- §3 の統合正方形・§4 の登路は candidate であり、証明義務を持つ statement の
  固定はカード起票時に行う。
- SFT(意味の空間の上の動力学)と tooling への換金(decider の ArchSig
  搭載など)は本ノートの範囲外とする。前者はプログラム定義 §11 の座を、
  後者は論文A実証節 PRD と ArchSig 改修系列を正本とし、台帳 §2 の末尾2行は
  その座位だけを記録する。
- 命名規律を再掲する: Semantic Geometry of Architecture は略さない。
- 隊列は指針であり、採否・順序はユーザー裁定を正とする。
