# AAT代数幾何版 拡張考察: 先行ノートからの移植・他分野への橋・大定理候補

- 対象: `docs/aat/algebraic_geometric_theory/`(第I〜VIII部+付録A/B、2026-06-12 時点)
- 比較対象: `docs/aat/algebraic_geometric_theory/`、`docs/note/` の先行体系定理ノート4本、`Formal/Arch/` の先行体系 Lean 資産
- 実施日: 2026-06-12
- 位置づけ: フルレビュー(`aat_algebraic_geometric_theory_full_review.md`、2026-06-11)とその反映(#1900 数学本文補強、#1901 計測理論=第VIII部追加)を前提に、次の三問に答える。
  1. 先行ノートから移植できる要素は何か
  2. 代数幾何から解析などへ、実コードを効果的に解析できる橋は架けられるか
  3. 複数分野に橋をかけ、コードベース構造に新しいインサイトを与える大定理を発見できるか

本ノートの主張ラベルは本文の規律に従う。`[証明可能]` は有限 regime で標準的手法により証明が書けると判断したもの、`[輸入]` は外部分野の既知定理の decoration で得られるもの、`[候補]` は証明設計が必要なもの、`[プログラム]` は定式化自体に設計が残るものを指す。

---

## 0. 要旨

- 移植: 先行ノートには AG 版が**まだ持っていない計測の量的核**が眠っている。最重要は4点 — (P1) ホモトピー生成元族(π₁^AAT の表示を与え、第VI部の ill-defined 性を解消する)、(P2) 計測モノドロミー μ_x / AMI(Lean 形式化済み資産ごと第VI×VIII部に接続)、(P3) 状態遷移代数(AG 版に不在の temporal 層の実体)、(P4) 距離・充填幾何の量的核(margin 安定性、観測ギャップ下界、Dehn 関数、bi-Lipschitz 忠実性)。
- 橋: 第VIII部が用意した有限 regime(有限 poset site + square-free + cellular sheaf)は**ハブ**であり、そこから Hodge 理論、最適輸送、離散 Morse 理論、スペクトル理論、力学系へ**スポーク**が架かる。どの橋も「実コードで何が新しく測れるか」を一つずつ持つ。
- 大定理: 提案の筆頭は **G1 有限アーキテクチャ計測の基本定理**(AAT-GAGA)— 「有限 regime において、コードベースの代数的負債幾何は、数値線形代数によって忠実かつ安定に読める」を5条項(比較・分解・会計・位相・安定)に分けた束。うち4条項は今すぐ証明可能で、各条項が単独でも実務的な読みを持つ。G2(位相的負債定理)と G3(調和的負債分解)は特に、「**分解の形そのものが隠れ結合の容量を決める**」「**局所修正では消えない本質負債の質量が一意に定まる**」という、既存のどの計測ツールも出していない結論を出す。

---

## 1. 現状認識: 第VIII部追加後も残る弱点

フルレビュー後の2コミットで、critical 6件は修正され(定理9.3 の zero-reflecting 集約化、scheme gluing の locally ringed 化、定理11.1 の abelian effective torsor 化+証明、第V部 transfer の support-localized 再構築、smooth/singular の DefTest 単一条件化)、第VIII部が計測 profile・verdict 規律・有限計算可能性・Stanley-Reisner/Alexander 双対・sheaf Laplacian・common ambient・support-localized transfer を整備した。これは大きな前進である。その上で、「実コード適用・計測がまだ弱い」原因は次の6点に特定できる。

```text
W1. 本丸の定理が candidate のまま:
    安定性 (VIII 定理候補6.3)、LawConflict base change (9.2)、transfer 下界 (10.4)。
    計測値のノイズ耐性は依然「証明対象が明示された」段階。

W2. monodromy 経路が未開通:
    第VI部の pi_1^AAT は構成が選択依存のまま (operation homotopy は付録B台帳で
    future design obligation)。VIII 原則7.4 自身が
    「no operation groupoid -> no monodromy measurement」と認めている。

W3. temporal / dynamics 層の不在:
    state transition、event sourcing、replay は AG 版に名前 (State_A, temporal law,
    trace topos) しかない。時間発展を測る数学が本文にない。

W4. 解析読みと構造判定の間の定理不足:
    Laplacian の residual norm や distance は analytic reading として定義された
    (VIII §8) が、構造的 verdict との間に「最小性」「下界」「分解」の定理がない。
    near-flat != lawful という非主張だけでは、解析値を判断に使えない。

W5. worked example がコード断片起点でない:
    付録B は擬円周+抽象 witness (p,q,r) であり、第I部 例1.4 のコード断片から
    付録B の pipeline までを貫く例がまだない (レビュー E1 の半残)。

W6. 先行体系 Lean 資産が AG 台帳に未接続:
    MonodromyMeasurement / HomotopyHolonomyStokes / CurvatureTransferSpectrum /
    DistanceGeometry は guardrail として存在するが、AG 版の theorem label とは
    無関係のまま。AG 有限 regime ならこれらの「仮定として持ち込まれた不等式」を
    本物の定理に昇格できる。
```

以下、移植(§2)が W2/W3/W4/W5/W6 を、橋(§3)と大定理(§4)が W1/W4 を狙う。

---

## 2. 問1: 先行ノートからの移植プラン

先行ノートと AG 版の差分を取った。第I部(Atom 公理系、コード断片からの抽出例 1.4 を含む)はほぼ全量移植済み。**未移植の本体は先行体系の後半部に集中しており、それはちょうど「計算・例・距離」**、つまりユーザーが弱いと感じている部分である。これは偶然ではない: AG 化の過程で「構造の階層」(site/sheaf/ideal/cohomology)が先に運ばれ、「量の幾何」(距離・コスト・スペクトル・状態遷移)が後回しになった。

### 2.1 移植インベントリ(優先度順)

| # | 先行ノートの要素 | 移植先 | 規模 | 何が変わるか |
| --- | --- | --- | --- | --- |
| P1 | ホモトピー生成元族(II 定義11.1: independent square / same contract replacement / repair filler / identity / associativity) | 第VI部 §9 | 中 | π₁^AAT を「selected generator 族による operation groupoid の表示」として再定義。レビュー指摘(π₁ が群にならない)の解消経路 |
| P2 | 計測モノドロミー(II §12: Cont_x、μ_x、AMI、命題12.4/12.5)+ Lean 資産 | 第VI部 §10–11、第VIII部 | 中 | Mon を「測れる2-cell(square)上の有限 Gauss-Manin」として先に定義。`MonodromyMeasurement.*` の proved 定理を AG 台帳に接続 |
| P3 | 状態遷移代数(III §7–8: transition law、replay/roundtrip/compensation/migration naturality) | 新節(第VII部付録 or 第IX部) | 大 | site 上の「遷移モノイドの層」St_A を置き、temporal law を trace category 上の law として実体化。付録A.6 の Temporal law スロットと付録B 台帳の trace topos obligation を充足 |
| P4 | 距離・充填幾何の量的核(IV 命題4.5/4.6、定義5.5、命題7.3、定義7.4、定義8.1/8.2) | 第VII部 §8–12、第VIII部 | 中 | margin 安定性・観測ギャップ下界・Dehn 関数・bi-Lipschitz 忠実性。G3(c) のコスト接続と新不変量 Dehn_X を供給 |
| P5 | グラフ/行列表現の定理群(III 命題1.3/2.4/3.3/3.5/4.2/4.4: 冪零性↔非巡回性、walk count、spectral radius) | 第VII部 §3 | 小 | R_graph、R_matrix を「定義済み functor + 証明済み preservation/reflection 実例」に格上げ。枠組み宣言(C判定)だった §3 に実体を入れる |
| P6 | Operation-Invariant Galois 対応(II 定理6.9) | 第VI部 §12 | 小 | Ops ⊣ Inv の Galois 接続を refactor groupoid の部分 groupoid と保存 invariant 族の間の随伴に格上げ。橋 B4(抽象解釈)とも同じ語彙になる |
| P7 | 修復停止性・健全性(II 命題8.3/8.4) | 第V部 §8、第VIII部 | 小 | well-founded な comparison profile の下で repair 戦略の停止性。**Lean 化候補の筆頭**(decidable・有限) |
| P8 | 拡張公式・境界ホロノミー予想(II 定義7.5、予想7.6) | 第IV部 §8–9 の系 | 小 | κ_U(B) = κ_U(A) + κ_U(f) + Hol_U(∂) を Mayer-Vietoris 長完全列の系として読み直し、`boundary_holonomy_conjecture.md` を AG 版でクローズ |
| P9 | ドメイン worked example(III §9–13: User model、Coupon 拡張、static-flat-semantic-obstruction、repair transfer、SOLID 反例) | 付録B §B.8 | 中 | 例1.4 のコード断片 → site → I_Ob → H¹ → Tor → period → verdict を**一気通貫**で計算(W5 解消、レビュー E1 完遂) |
| P10 | ACTS(III 定義6.6: curvature transfer spectrum)+ `CurvatureTransferSpectrum.lean` | 第VIII部 §8 | 中 | (support × axis) グラフ上の transfer 作用素とそのスペクトル半径読み。橋 B9/B11 の足場 |

### 2.2 移植の要諦4点(詳説)

**P1: ホモトピー生成元族が π₁^AAT を治す。**
第VI部の現行構成は「operation category → 可逆化 → selected operation homotopy で商 → 基点選択」だが、「selected operation homotopy」が何かを与えるデータがどこにもない。旧II部 §11 はまさにそれを持っている:

```text
homotopy generator family H:
  independent square        (独立な2操作の交換)
  same contract replacement (同一契約の置換)
  repair filler             (修復の充填)
  identity insertion/deletion
  associativity reassociation
```

AG 版での正しい置き場所は「**表示(presentation)**」である。operation graph を 1-骨格、selected generator 族 H の各関係を 2-cell とする presentation 2-complex K_H(X,U) を作り、

```text
pi_1^AAT(X, U, H) := edge-path group of K_H(X,U)
```

と定義する。これで (i) 群であることが構成から従い、(ii) H への相対化が明示され(本文の規律と整合)、(iii) 有限 regime では有限表示群として計算対象になり、(iv) μ_x(P2)が「2-cell で埋まらない square の検出器」として位置づく。レビュー提案 T9 の具体化であり、第VI部の Monodromy Debt 定理が型1/型3病から脱出する最短路である。

**P2: モノドロミーは「測れる版」を正典にする。**
旧II部 §12 の μ_x(f,g;A) = d_x(Cont_x(g∘f), Cont_x(f∘g)) は、square という最小ループ上のモノドロミー欠陥であり、有限・計算可能・Lean guardrail 済み(`AxisDefect.observationDiff_of_nonzero` 等は proved)である。AG 版では:

```text
square = K_H の生成 2-cell の境界 loop
mu_x(square) = その loop に沿う係数層の transport のずれの selected reading
AMI_X = 重み付き総和 (VIII の measurement packet の analytic reading)
```

として、第VI部の Gauss-Manin 系(定義10.2)の**最小実例**に位置づける。一般の rho_U が「与えられていれば」の仮定付き対象である一方、square-level transport は P1 の表示から構成できる。これにより VIII 原則7.4 の「no groupoid → no monodromy measurement」が「P1 の groupoid があるので測れる」に転じ、W2 が解消する。旧 Lean 資産は台帳(`lean_theorem_index.md`)経由で AG ラベルに対応行を持たせる(W6)。

**P3: 状態遷移代数は AG 版の「時間」になる。**
AG 版は空間方向(context の貼り合わせ)は豊かだが、時間方向(状態と効果の発展)は名前しかない。旧III部 §7–8 の遷移代数

```text
replay(e, replay(e, s)) = replay(e, s)
decode . encode ~= id
compensate . action ~= id
migrate ; project_old = project_new ; migrateEvents
```

は、site 上の層として持ち込める: 各 context W に「W 上で見える状態空間と遷移モノイド」St_A(W) を割り当て、遷移 law を St_A 上の関係式(= 可換図式)として読む。temporal law(付録A.6)は「trace category 上の subfunctor」と宣言されているが、その trace category の最小モデルが St_A の自由圏である。Event Sourcing / Saga / migration naturality が AG の言葉(naturality = 図式可換 = H⁰ 零)で読め、しかも μ_x(P2)の主要な軸(semantic / effect 軸)の実体を供給する。

**P4: 距離・充填幾何は「解析読みの定理化」の素材である。**
旧IV部には、AG 版第VII部が枠組み宣言で終わっている部分の量的中身が既にある。特に:

```text
命題4.6 Margin Stability:
  length_signature(P) < margin(A_0) なら、測定済み軸 scope で P は Safe を出ない。

命題7.3 Observation Gap Lower Bound:
  観測 O が filling generator に対し L-Lipschitz で d_obs(O(P),O(Q)) = delta なら
  fill_cost(P . Q^{-1}) >= delta / L。

定義7.4 Architectural Dehn Function:
  Dehn_A(n) = max { minimal filling area of loop l | boundary_length(l) <= n }。
```

Margin Stability は「安定性」という語の入った**証明可能な最初の主張**(三角不等式だけで出る)。Observation Gap Lower Bound は G3(c) の修復コスト下界の供給源。Dehn 関数は幾何学的群論からの新不変量で、「局所的なずれを局所的に直せる architecture か、大域 rewrite を要求する architecture か」を一つの増大度関数で表す — P1 の表示 2-complex K_H 上で定義でき、π₁ の語の問題・等周不等式の理論と直結する。

### 2.3 移植しなくてよいもの

- 旧 I 部(Atom 公理系、抽出例): 移植済み。
- 旧 II 部 §1–5(flatness model、zero curvature、三層 flatness): AG 版第III部の lawful locus と第I部定理9.3(修正版)が上位互換。三層 flatness の「層間非含意」だけは P9 の例に残す価値がある。
- 旧 IV 部 §9–10(DistanceValue、bounded diagnostic conclusion): 第VII部 §9・第VIII部 measurement packet として移植済み。

---

## 3. 問2: 他分野への橋 — ハブ&スポーク設計

レビューの B1–B8 のうち、B1(組合せ可換代数)と B2(TDA)と B3(cellular sheaf Laplacian)は第VIII部が入口まで建設した。ここでは**橋の全体設計**を提案し、新しい橋 B9–B12 を加える。

### 3.1 設計原理: 一つのハブ、多くのスポーク

すべての橋は同じハブを通る。

```text
ハブ (第VIII部の有限 regime が既に用意):
  cover nerve 多重グラフ N(U)        (chart = 頂点, overlap 成分 = 辺, 三重 = 面)
  Stanley-Reisner 複体 Delta_U       (square-free witness regime)
  monomial Tor 加群 LawConflict_i    (common ambient)
  cellular sheaf model (C^n, d_n)    (内積付き有限線形代数)
  presentation 2-complex K_H         (P1 が追加)

スポーク (各分野が読むもの):
  B1  組合せ可換代数   : Hochster 公式, Alexander 双対, lcm-lattice
  B2  TDA             : persistence barcode, interleaving 安定性
  B3+ Hodge 理論      : 調和分解, スペクトル, 距離   (→ G1, G3)
  B9  最適輸送        : 負債移送コスト, Wasserstein 距離 (新規)
  B10 離散 Morse 理論  : 臨界胞体, 修復 = collapse 列   (新規)
  B11 スペクトルギャップ: Cheeger 型不等式, hotspot 局在  (新規)
  B12 力学系 / SFT    : Lyapunov 関数, 散逸場, アトラクタ (新規)
  B6  証明複雑性      : NSdepth = PC degree, 下界技術   (レビューどおり)
```

要点は、**抽出は一度、解析は多面**ということである。ArchSig 実験(`archsig_private_python_repo_aat_structural_readings.md`)が示したとおり、実リポジトリで高くつくのは観測(ArchMap 構築と coverage)であり、ハブの組合せ対象さえ作れば、スポーク側は既製ツール(Macaulay2、GUDHI/Ripser、LAPACK、LP ソルバ)が走る。

### 3.2 B3+ Hodge 理論の橋を渡り切る `[証明可能]`

第VIII部 §8 は Laplacian と residual norm を定義したが、W4 のとおり「解析値が構造について何を保証するか」の定理がない。渡り切るのに必要なのは有限次元 Hodge 理論そのもの:

```text
C^n = im d_{n-1}  ⊕  Harm^n  ⊕  im d_n^*       (直交直和)
Harm^n = ker L_n ≅ H^n(X_M, Ob_M)
```

これが §4 の G3(調和的負債分解)に直結する。実コードで新しく測れるもの: **mismatch の「局所修正で消える成分 / 本質成分」への一意直交分解**と、本質成分のノルム(= どれだけ局所 patch を重ねても残る負債の質量)。さらにスペクトルギャップ λ_min(L_1 の非零最小固有値)は「いま H¹ が零でも、どれだけ小さな摂動で非零になりうるか」の頑健性指標になる(B11)。

### 3.3 B9 最適輸送: 負債は消えない、移送される — を距離にする `[輸入]`

旧IV部 §6.3 の curvature transport と第V部の transferred obstruction は「移る」ことを述べるが、「どれだけのコストで移るか」を測る距離がない。obstruction measure Ω_U(A)(support 上の非負測度)に対し、support グラフ(= N(U) または K_H の 1-骨格)上の最短路距離を ground metric とする Wasserstein 距離

```text
W_1(Omega_U(A), Omega_U(op(A)))
```

を transport cost と定義する。有限なので Kantorovich 双対は線形計画で厳密に解ける。狙う定理(候補):

```text
Transfer Cost Lower Bound:
  repair op が axis x の負債質量 m を support s から消すとき、
  全 axis 総質量が保存される profile では、W_1 >= m * dist(s, 最近接の吸収可能 support)。
```

実コードで測れるもの: 「この修復は負債を消したのか、隣のモジュールに 2 ホップ移しただけか」が**数値**になる。ArchSig 実験で観測された pressure chain(request-authority → transaction → domain-artifact → AI-surface)は、まさに transport 経路の観測例である。

### 3.4 B10 離散 Morse 理論: 修復計画 = collapse 列 `[輸入]`

第VIII部 §5 の Alexander 双対は minimal repair hitting set(どの witness を打てば良いか)を与えるが、「どの順に打つか」は与えない。Δ_U 上の離散 Morse 関数 / acyclic matching を選ぶと:

- 臨界胞体 = 既約な obstruction パターン(打っても複体の型が変わらない本質部分)
- matching に沿う collapse 列 = ホモトピー型を保ったまま複体を縮める「安全な簡約順序」

が得られ、persistence 計算(B2)の前処理としても標準的に効く。狙う読み: **repair route(第VII部 §12)の組合せ的実体は Δ_U の collapse 列であり、structural repair の最小手数は臨界胞体数で下から押さえられる**。

### 3.5 B12 力学系 / SFT: 進化の幾何 `[プログラム]`

`Grothendieck_Derived_AAT-SFT.md` の構想(evolution family π: 𝔛 → B、field、force、ForecastCone)のうち、いま数学にできる最小核は:

```text
commit 列 = 有限力学系:  A_0 -> A_1 -> ...   (force = 射)
CI/review policy = 散逸場: 許される force を omega 非増加に制限する場
Phi_U = omega_U (または harmonic mass ||h(g)||) を Lyapunov 候補とする
```

P7(停止性)+ zero-reflecting 集約(定理9.3 修正版)から、「散逸場の下で軌道は有限時間で停留し、停留点で Phi が局所最小」までは初等的に出る。その先(Flat への到達可能性、ForecastCone の H¹ 障害 = Force Integrability)はプログラムとして第IX部候補に置く。実務読み: **CI ポリシー設計 = Lyapunov 関数設計**という語彙が得られる。

### 3.6 橋ごとの「実コードで新しく測れるもの」一覧

| 橋 | 測れるもの | 既製ツール | 前提 |
| --- | --- | --- | --- |
| B1 | β_{i,j}(I_Ob)(絡まり方の高次構造)、minimal repair set | Macaulay2 | square-free regime |
| B2 | 負債の barcode(law 強度・時系列に沿う寿命) | GUDHI/Ripser | filtration 選択 |
| B3+ | 本質負債質量、スペクトルギャップ、harmonic hotspot | LAPACK | 内積選択 |
| B9 | 負債移送コスト W_1、修復の「移しただけ」検出 | LP ソルバ | 測度・ground metric 選択 |
| B10 | 既約 obstruction パターン、安全な簡約順序 | 自前(小規模) | Δ_U |
| B11 | 整合性の頑健性(near-miss 検出)、ボトルネック境界 | LAPACK | B3+ |
| B12 | policy の散逸性、軌道の停留保証 | なし(理論) | P7 |
| B6 | 修復不能性証明書の深さ NSdepth | Gröbner/SAT | Boolean regime |

---

## 4. 問3: 大定理候補

方針: 「大きい」とは、(i) 複数分野を一つの主張で束ね、(ii) 実コード計測に直接降り、(iii) 既存本文の語彙(site / I_Ob / H^n / Tor / period / profile)で述べられること。誇大主張を避けるため、各定理に証明経路と状態を付す。**G2〜G6 は今すぐ証明に着手できる**。

### G1. 有限アーキテクチャ計測の基本定理(AAT-GAGA)`[束: 条項ごとに証明可能〜候補]`

> **主張(束)**: 有限計測 regime M(有限 poset site、module 係数、内積固定)において、コードベースの代数的負債幾何は数値線形代数によって忠実かつ安定に読める。すなわち:
>
> ```text
> (1) 比較   : H^n_alg(U_M, Ob_M) ≅ Harm^n = ker L_n     [証明可能: 有限 Hodge]
> (2) 分解   : C^n = im d ⊕ Harm^n ⊕ im d^*、調和代表元は
>              各 cohomology 類のノルム最小元                [証明可能]
> (3) 会計   : <delta(b), gamma> = <b, ∂gamma>             [証明可能: 随伴性]
> (4) 位相   : dim H^1 の容量は nerve の組合せ量で制御される   [証明可能: G2]
> (5) 安定   : d_interleaving(H^*(F), H^*(F')) <= d_wit(F,F') [単調系: 輸入で証明可能 /
>                                                             zigzag: 候補]
> ```

名前の由来: GAGA が「代数的 = 解析的」の比較定理であるように、(1)–(2) は「代数的 obstruction 類 ↔ 調和的(解析的)代表元」の比較である。意義: 第VIII部の verdict 規律に「**解析読みが構造判定の忠実な代理になる条件と限界**」という定理的裏づけを与え、W1/W4 を一括で塞ぐ。各条項は以下 G2〜G7 として単独でも価値を持つ。

### G2. 位相的負債定理(形が負債を強制する / 局所レビュー十分性)`[証明可能]`

有限 poset regime で cover U = {W_i → W} を取り、overlap 成分を辺、三重 overlap 成分を面とする **nerve 多重グラフ/複体 N(U)** を作る(付録B の擬円周は頂点2・平行辺2、b_1 = 1)。

> **(a) 容量下界(無条件)**:
> ```text
> dim_k H^1(U, F) >= Σ_辺 dim F(W_e) − Σ_頂点 dim F(W_v) − Σ_面 dim F(W_t)
> ```
> (rank-nullity のみ。restriction 写像の中身に依存しない。)
>
> **(b) 定数係数の等式**: F = 定数層 k なら H^1(U, k) ≅ H^1(N(U); k)、次元は b_1(N(U))。
>
> **(c) 局所レビュー十分性(消滅定理)**: N(U) が森(b_1 = 0、三重 overlap なし)で、
> すべての restriction F(W_i) → F(W_e) が全射なら、H^1(U, F) = 0。
> すなわち**互換な局所 lawful family は、この形の分解の下では必ず大域に貼り合う** —
> どの module 係数読みに対しても同時に。
>
> **(d) χ 保存則**: χ(U, F) = Σ (−1)^n dim C^n は (nerve, stalk 次元) のみで決まる。
> cover の形と stalk 次元を保つ refactor は、負債を次数間で動かせても
> 交代和を変えられない。

証明経路: (a)(d) は線形代数、(b) は定数係数 Čech の標準事実、(c) は木上の貪欲解法(根から伝播)。すべて有限で Lean 化候補。

橋: グラフ理論(cycle rank)↔ 層係数 cohomology ↔ レビュープロセス設計。

実務インパクト: **b_1(N(U)) = 「統合レビューが必要な独立ループの本数」**という、分解(モジュール境界の引き方)だけから計算できる数が得られる。b_1 = 0 + 全射 restriction なら局所レビューで大域 lawfulness が保証され、b_1 > 0 なら隠れ結合類の置き場がちょうど b_1 次元ぶん**構造的に存在する**(中身のコードと無関係に)。マイクロサービスの「境界は増えたのに統合バグが減らない」現象は、b_1 が分解で増大したことの帰結として説明できる。原則4.4(群の非零 ≠ 類の非零)とも整合する: (b) は容量、定理7.1 系は実弾、という分業になる。

### G3. 調和的負債分解定理(本質修復下界)`[証明可能 + コスト接続は移植仮定付き]`

cellular sheaf model(VIII §8)で mismatch 1-cocycle g(定義5.2 の gluing mismatch)を取る。

> **(a) 分解**: g は一意に g = d_0 c + h(g) + d_1^* e と直交分解し、h(g) は [g] の調和代表元。
>
> **(b) 残差最小性**:
> ```text
> min_{c in C^0} || g − d_0 c || = || h(g) ||
> ```
> 局所調整(0-cochain の張り替え)で到達できる残差の最小値は調和部分のノルムであり、
> 最小化子は調和代表元で達成される。
>
> **(c) 本質修復下界**: || h(g) || > 0 なら、profile(site・stalk・law ideal)を変えない
> いかなる局所調整列も mismatch を消せない。さらに P4 の観測ギャップ下界
> (cost が cochain ノルムに対し L-Lipschitz)を仮定すれば、大域 lawfulness に至る
> 任意の修復計画の cost は || h(g) || / L 以上。

証明経路: (a)(b) は有限次元 Hodge 理論(= 線形代数)。(c) 前半は (b) の系、後半は P4 移植の Lipschitz 公理を仮定に置いた certified bounded inference。

橋: Hodge 理論 ↔ Čech cohomology ↔ 修復コスト幾何。

実務インパクト: hotspot リストが「**局所 patch で消える成分**」と「**境界を跨ぐ作業なしには絶対に消えない本質成分**」に数値で割れる。`||h(g)||` は「本質負債質量」という単一スカラーだが、原則4.3(cohomology is not a metric)に反しない — これは類 [g] の測度であり、類そのものは保持される。第VIII部 distance-to-flatness 読み(定義8.3)に「その距離の下界は調和質量」という定理が付く。

### G4. 周期Stokes会計恒等式(負債の複式簿記)`[証明可能]`

有限 poset homology model(VII 定義5.2A)と Mayer-Vietoris 接続準同型 δ(IV 定義8.3)に対し:

> **主張(随伴性)**: cochain-chain pairing の下で
> ```text
> <delta(b), gamma> = <b, ∂gamma>
> <d omega, gamma>  = <omega, ∂gamma>
> ```
> 特に: feature 境界の mismatch section b の holonomy 類 δ(b) を release ループ γ で
> 読んだ period は、γ の境界に沿って測った局所 mismatch の符号付き和に等しい。

証明経路: 単体的 Stokes(随伴性)そのもの。有限なので完全に初等的。VII 例5.2B / 付録B.6 の pairing 計算(Per = r_sync − r_async)はこの恒等式の実例。先行体系 `HomotopyHolonomyStokes.lean` では Stokes 不等式が「仮定フィールド(boundedStokes)」として持ち込まれていたが、AG 有限 regime では**仮定でなく定理**に昇格する(W6 の模範例)。

橋: 微分幾何の Stokes ↔ Čech/単体 cohomology ↔ 計測監査。

実務インパクト: **監査恒等式**になる。「release サイクル一周で測った drift」=「期間中に記録した境界 mismatch の総和」が**恒等的に**成り立つはずなので、両辺の食い違いはそのまま witness coverage の穴の検出器になる(unmeasured ≠ zero を、規律ではなく**検算**で運用できる)。命名するなら: 負債の複式簿記(double-entry bookkeeping of architecture debt)。

### G5. 法則干渉のHilbert級数恒等式(独立性監査)`[証明可能]`

monomial regime(R = k[E]、graded ideal I_U, I_V)で:

> **主張**: graded Hilbert 級数について
> ```text
> H_{R/I_U}(t) · H_{R/I_V}(t) / H_R(t)
>   = Σ_{i>=0} (−1)^i H_{LawConflict_i(U,V)}(t)
> ```
> したがって干渉級数を
> ```text
> Int_{U,V}(t) := H_{R/(I_U+I_V)}(t) − H_{R/I_U}(t) H_{R/I_V}(t) / H_R(t)
>              = H_{Tor_1}(t) − H_{Tor_2}(t) + ...
> ```
> と定義すると、「二つの law universe が独立だった場合の期待値」からの joint lawful
> coordinate ring のずれは、**交代 Tor 質量で厳密に勘定される**。

証明経路: graded 自由分解の Euler 標数(標準)。Macaulay2 で即計算可能。

橋: 交叉理論(Serre 重複度の graded 版)↔ derived 代数 ↔ ポリシー監査。

実務インパクト: 二つのポリシー(例: layering と authority)の「独立性からのずれ」が**次数別のスペクトル**として出る。次数 k の係数は「witness k 個の組合せサイズで起きる干渉量」を局在化する。第V部の「Tor は衝突の構造を読む」という標語が、検証可能な数値恒等式になる。

### G6. 集約5項完全列(尺度安定負債)`[証明可能]`

集約写像(module → package のような粒度変更)を有限 site の射 π : X_fine → X_coarse とすると、Leray 5項完全列:

> ```text
> 0 → H^1(coarse, π_* Ob) → H^1(fine, Ob) → H^0(coarse, R^1 π_* Ob)
>   → H^2(coarse, π_* Ob) → H^2(fine, Ob)
> ```
> 読み: 細かい尺度の隠れ結合類は、(i) 粗い尺度でも見える成分と、(ii) 集約単位の内部に
> 局在する成分(R^1 π_*)に**完全列の精度で**分配される。粗い尺度での修復を細かい尺度へ
> 持ち上げる障害は H^2(coarse) に住む。
> **尺度安定負債** := selected な集約族すべてについて H^1(coarse) 側から来る類
> (= Leray スペクトル系列の E_∞ まで生き残る類)。

証明経路: 有限 poset 射の Grothendieck/Leray スペクトル系列(標準)。`AAT_Grothendieck.md` の scale-stable debt 構想の厳密化。

実務インパクト: 「この負債はズームレベルの取り方の産物か、どの粒度でも見える構造か」を完全列で判定。レビュー A.2.1 の coverage 比較射(検証材料が3件未証明のまま)に、最初の証明済みインスタンスを与える。

### G7. 安定性定理(VIII 定理候補6.3 の昇格)`[単調系: 輸入で証明可能 / zigzag: 候補]`

> **主張(単調系)**: 単一 forbidden support の挿入 F → F ∪ {S} は単体的包含
> Δ_{F∪{S}} ⊆ Δ_F を誘導し、filtration step 計量での interleaving について
> ```text
> d_bottleneck(barcode(F), barcode(F')) <= d_wit(F, F')
> ```

証明経路: 挿入1回 = filtration の1段 = 1-interleaving、あとは persistence 安定性定理(Chazal et al.)の decoration。zigzag(挿入と削除の混在)は Botnan–Lesnick の zigzag interleaving を輸入する設計が必要で、候補のまま。

実務インパクト: T1(レビュー筆頭提案)の単調ケースが定理になり、「commit 1個分の witness 変化で barcode は1ステップ以上動かない」というノイズ耐性保証が初めて立つ。

### G8. SFT 力学定理(可積分性・散逸)`[プログラム]`

P7(停止性)+ G3(Lyapunov 候補 ||h(g)||)+ `Grothendieck_Derived_AAT-SFT.md` の Force Integrability(ob(f) ∈ H¹ ≠ 0 なら force は大域進化に積分不可)を束ね、「CI/review 場の設計 = 散逸構造の設計」を定理群にする。第IX部(Evolution Geometry)として独立させる価値があるが、P1〜P4 と G1〜G6 の後で着手すべき(定式化の自由度がまだ大きい)。

### 大定理候補の相互関係

```text
        P1 (pi_1 表示)──→ P2 (測れる monodromy)──→ G4 (Stokes 会計)
                                                      │
W4 ──→ B3+ (Hodge)──→ G3 (調和分解)──→ G1 (基本定理) ←┤
                                          ↑           │
        G2 (位相的負債) ──────────────────┘           │
        G7 (安定性) ←── B2 (TDA) ─────────────────────┘
        G5 (干渉級数) ←── B1 (可換代数)
        G6 (尺度安定) ←── Leray
        G8 (SFT) ←── P7 + G3
```

---

## 5. 推奨実行順序

各フェーズは独立に価値が出る。レビューのロードマップ(修正1〜10)は概ね消化済みなので、これはその次の計画である。

| フェーズ | 内容 | 規模 | 充足するもの |
| --- | --- | --- | --- |
| 1. 即時の定理化 | G2(a)(c)(d)、G3(a)(b)、G4、G5、G6 を本文化(第IV/V/VIII部の系・新節)。証明はすべて有限線形代数・標準輸入 | 中 | W1/W4 の過半、レビュー T4/T6/T11 の一部 |
| 2. 移植・第一波 | P7(停止性、**Lean 第1号候補**)、P5(graph/matrix 実例)、P8(境界ホロノミー予想のクローズ)、P9(coupon 一気通貫例 → 付録B.8) | 中 | W5、E1 完遂、旧予想ノート1本回収 |
| 3. 移植・第二波 | P1 → P2(π₁ 表示と測れる monodromy、Lean 資産接続)、P4(距離核)、P10(ACTS) | 大 | W2/W6、レビュー T9、G4 の前提 |
| 4. 安定性と輸送 | G7 単調系(T1 解決)、B9 輸送下界、B10 Morse 簡約 | 大 | W1 残り |
| 5. 時間と進化 | P3(状態遷移代数 = temporal 層)、G8(第IX部 Evolution Geometry) | 大 | W3、SFT 接続 |

Lean 化の優先順位(`proof_obligations.md` に積む順): P7 停止性 → G2(a)(d) → G4 随伴性 → G3(a)(b) → G2(c)。いずれも有限・decidable で、AG 版 theorem label が台帳に初めて載ることになる(現状 0 件)。

---

## 6. 非主張(claim boundary)

- 本ノートの `[証明可能]` は「有限 regime で標準的手法により証明が書ける」という執筆者の判断であり、証明が書かれるまで本文の定理にはならない。
- G1〜G8 はいずれも selected profile(site、cover、係数、内積、witness family、cost model、集約族)に相対化される。profile の外側の law・axis・尺度について zero / lawful / stable を主張しない。
- G2(c) の「局所レビュー十分性」は選ばれた abelian 係数読みと全射 restriction の仮定の下の主張であり、non-abelian 層(torsor/gerbe、第VI部)の貼り合わせ失敗を排除しない。
- G4 の監査恒等式は構成済み AAT geometry 内部の数学であり、source 抽出の完全性や ArchSig 実装の正しさを主張しない(VIII 原則2.2 と同じ境界)。
- 橋 B9〜B12 の「実コードで測れるもの」は、ハブの組合せ対象が実コードから構成済みであること(= ArchMap/抽出層の責務)を前提とする。ArchSig 実験で確認された coverage gap(per-file semantic、runtime trace、permission audit 等)はこの前提側の課題であり、本ノートの定理群では解消されない。
