# G-107-aat-uniform-invariance-characterization — 一様不変性の十分性と非局所性(Atlas 定理の拡張と特徴づけ限界)

- `id`: `G-107-aat-uniform-invariance-characterization`
- `status`: `active`
- `priority`: `medium`
- `research mode`: `target-theorem`
- `target status`: `target-refuted`(2026-08-11、v2 再査読で (ii)
  十分性への exact 有限反例 `PROPER-CHAIN3-PLUS-BRIDGE-DIGON` が成立、
  `target failure policy` の (ii) 反例条項を適用)。経緯: 初版 statement
  (一様不変性 ⟺ C\* の必要十分特徴づけ)は `CONTRACTIBLE-TRIANGLE` で
  反証 → hunt 後継 round(v4・v5 も invalid)と人間裁定(選択肢1:
  許容観測 grammar `G_local-v1` の固定)を経てハントは **Stop B**
  (verdict `CSTAR-not-expressible-in-G_local-v1`)で終端(Issue #3948
  closed / COMPLETED)→ v2(十分性+非局所性の二本柱、ユーザー裁定)へ
  改訂 → v2 の (ii) も上記反例で反証(改訂記録=条項系 C\* 節)。現登録
  C\*(CERTIFIED-v3 + support-active)は**両方向とも** exact 反例を
  持つ。存続しうる theorem family((i) 還元・恒久 grammar に対する
  (iii) 非局所性・(iv) C 非必要性地図)の保持範囲と、C\* 後継 candidate
  (criticality-reflection 型条項の追加など。新 semantic ID の事前登録と
  独立再査読を要する)の有無は**人間裁定待ち**。裁定・statement 改訂・
  新 fixed head の正式再査読を経るまで target-theorem loop は起動
  しない。runtime state は tracking Issue #3954。
- `predecessor`: G-104(Diagnostic Resolution Invariance Theorem、
  `target-theorem-proved`。report
  [research/reports/G-104-aat-resolution-invariance.md](../reports/G-104-aat-resolution-invariance.md))。
  comparison data / K0・K1 生成係数 / 条件 C / block 直和分解の確定
  artifact(`research/lean/ResearchLean/AG/ResolutionInvariance/` 配下)を
  正本として参照する。加えて off-loop 必要性地図ハント(Issue
  [#3948](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/3948)
  closed / COMPLETED、**Stop B 終端**、恒久 artifact
  `research/experiments/g104-necessity-map/`)を**証拠**として参照する
  (R1 必要性反例群、C\* 候補系譜 v1–v5 と反例 fixture 群、`G_local-v1`
  恒久 contract、T3 / T6 の2点分離。証明根拠ではない)。
- `tracking issue`: [#3954](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/3954)
  (active 昇格はユーザー裁定 2026-08-09、成立はカード同期 PR のマージを
  もって)。
- `source note`: [research/experiments/g104-necessity-map/hunt-report.md](../experiments/g104-necessity-map/hunt-report.md)
  (§R0 一般手証明、§R2 候補系譜、blocker、Stop-B 終端)、
  `research/experiments/g104-necessity-map/results-stop-b-summary.json`
  (2点分離の恒久証拠と `G_local-v1` 恒久 contract)
- `research aim`: G-104 の Atlas 定理は「条件 C ⟹ H¹ comparison 全単射」の
  十分条件定理である。本 GOAL は当初その必要十分化(一様不変性 ⟺ C\*)を
  target としたが、初版 statement は exact 有限反例で `target-refuted` と
  なり、後継ハントは Stop B(`CSTAR-not-expressible-in-G_local-v1`)で
  終端した(経緯は `target status` と条項系 C\* 節の改訂記録)。statement
  v2 は、この帰結を二本柱の定理として固定する。第一柱=**十分性**:
  入力の incidence / support データだけから決定可能な条項系 **C\***
  (hunt が固定した candidate の theorem 化)が成立すれば、comparison
  data は**一様不変**(係数側を adequate な law family 全体で量化した
  H¹ comparison の全単射性)である。第二柱=**非局所性**: 半径1の登録
  観測 grammar `G_local-v1` で表現可能な**いかなる**条項系も一様不変性を
  特徴づけない(T3 / T6 2点分離の Lean 化。grammar 相対)。あわせて、
  law 量化を有限対象(粗側 Target の非空部分集合)へ落とす**値部分集合
  還元**を theorem として固定する。これにより「どの解像度比較が診断を
  保つか」に対し、決定可能な十分条件の一般定理と、同じ観測言語内での
  特徴づけ不可能性の両方が定理水準で確定し、なぜ Atlas 定理が十分条件の
  定理に**とどまるのか**が構造的説明を持つ。本定理は、reading 圏上の
  診断 local-system 構想(`program context`)における **universal
  zero-jump 領域の内側近似と観測限界**として位置づく。(注記
  2026-08-11: v2 の (ii) は再査読の exact 反例で反証済み — `target
  status` と条項系 C\* 節の改訂記録2を参照。存続 family の再構成は
  人間裁定待ち。)
- `program context`(上位構図、2026-08-11 追記。同日レビューで
  zero-jump locus / jump locus の層を是正): 本カードの二本柱定理は
  次の構想の pair 水準の核である — 各 adequate law family `L` を固定した
  読みの圏 `Read_L` 上で診断 `D_L(q) := H¹` を functor として構成し、
  一般の射に jump data `J_L := (dim ker, dim coker)` を付け、reading
  空間を plateau と jump locus を持つ有限 poset persistence module として
  読む。G-107 の一様不変性は law family を全量化するため、本カードが
  特徴づけるのは単一 `D_L` の同型領域ではなく、law 非依存の comparison
  geometry の射 `f`(読み対 `q ≤ q'` と canonical `π`)を共通定義域と
  して先に固定し、全 law family にわたり交差した **universal zero-jump
  領域**
  `Z_univ := { f | ∀ L, Adequate L q → Adequate L q' → J_L(f) = (0, 0) }`
  である(`Adequate` は reading 相対なので、両端の adequacy を仮定側で
  束縛する。`Read_L` ごとの射をそのまま交差するのではない)。この
  `Z_univ` 表記は pairwise の program 水準 candidate であり、本カードの
  claim は (ii) の全単射形と (iii) の分離形のみ — `J_L = (0, 0)` と
  `Function.Bijective` を結ぶ有限次元 bridge を含む functor 水準の
  正確化は後続カードで固定する。functor 水準の主張(射の合成整合、圏上の
  局所定数性、jump data の一般論)は本カードでは claim しない。合成整合は
  輸送の 2-cell 整合(G-106 の領分)に接続するため、後続カードで固定する。
  この構図の下で v2 の二本柱は次のように置かれる。十分性 (ii) は
  `C*-locus ⊆ Z_univ`(C\* 領域では jump が起きない = 内側近似)を、
  反証 fixture 群(CONTRACTIBLE-TRIANGLE / TERNARY-CYCLE-3。いずれも
  `Z_univ \ C*` の universal zero-jump 点)は包含の真性を、非局所性
  (iii) は「`Z_univ` とその補集合の分離は半径1の局所観測 grammar の
  どの条項系にも不可能」であることを固定する。(ii) の反例(C\* ∧ ¬uniform)が
  現れた場合は `C* \ Z_univ` の真の jump であり `target-refuted` と
  なる。一般の nonuniform 射は law-indexed jump profile のデータと
  なる。関連考察は表示的意味論ノート
  [docs/note/aat_denotational_semantics_of_architecture.md](../../docs/note/aat_denotational_semantics_of_architecture.md)
  §10(Resolution Diagnostic Local-System)。
- `core tension`: 三つの稜線がある。第一に**十分性の中心補題**: 固定
  半径の局所 certificate(SLOT / KILL)の反射推移閉包から、free pair を
  持たない任意の retained face-chain 構造の上で lift 差 cycle の大域的
  消滅を導く一般帰納が閉じるか。ここが計算探索の停滞点
  (blocker `PB-R2-NONFREE-GLOBAL-FACE-CHAIN`: 有限の
  linear / branching / cyclic / mixed / multichart fixture は全て閉じたが
  一般手証明が無い)であり、本 GOAL が定理化で埋めるべき本体である。
  C\* が cohomology 語彙を密輸すれば十分性は恒真化に堕ちるため、C\* は
  FaceTwin 類・one-pass free-pair 除去・cycle-critical cell・SLOT / KILL
  certificate という有限 syntactic データだけを読む条項系である
  (G-104 anti-weakening の継承)。第二に**非局所性の忠実性**: (iii) の
  分離定理は、Lean 側の観測写像 `Obs_G` が登録済み恒久 contract の
  grammar と一致して初めて意味を持つ。転写を粗くすれば分離は自明化し
  (別の弱い grammar についての定理に堕ちる)、細かくすれば偽になる。
  忠実転写の構成要素対応表と、T3 / T6 の label を登録 ledger の参照では
  なく Lean 内の有限計算((i) 経由)で再導出する規律が、この定理を
  「登録 artifact の言い換え」から theorem へ隔てる。第三に**ずれの
  幾何**: 十分性は `C*-locus ⊆ Z_univ` を、反証 fixture 群は包含の
  真性を、非局所性はそのずれ(`Z_univ \ C*-locus`)が半径1観測から
  不可視であることを与える。三つが揃って初めて「Atlas 定理の位置」—
  何が証明でき、なぜこの観測言語では iff に届かないか — が定理水準で
  固定される。
- `rival`: Čech 理論の Leray 型定理(局所非輪状性という十分条件のみで、
  特徴づけの限界を語らない)、CEGAR 型の抽象化精細化(健全性方向のみ)、
  hunt の有限 zero-result(定理を伴わない計算的証拠)、有限モデル理論の
  局所性定理(Hanf / Gaifman 型。一般論の局所性 rank であり、特定領域の
  登録観測 grammar への具体的分離を扱わない)。差は「decidable な十分
  条件の一般定理と、同じ観測言語内での特徴づけ不可能性(2点分離)を、
  同一有限モデル上の Lean witness つきで**対に**固定する」点に置く。
- `claim boundary`: G-104 カードの claim boundary を継承する: 有限 Source、
  G-103 の確定定義(`Reading` / `FiniteLawFamily` / `Adequate` /
  `CoarserThan`)、well-formed な comparison data(K1 導出台つき有限
  nerve・face boundary の端点整合・退化宣言の hereditary 性・chart 台の
  π-両立)、K0 / K1 に従う law 由来係数、係数体 `ℚ` 固定。Source と
  両読みの Target の非空性は ambient に仮定する(空 regime は claim に
  含めず、`A = q.Target` scope はこの仮定の下で well-defined)。量化対象は
  **一様不変性**であり、pointwise の必要性(単一 law family での
  全単射 ⟹ C)は主張しない(G-104 期の探索で不成立が確定済み)。C\* の
  評価 scope はカード固定(C1\*–C4\* は各非空 `A` の A-subnerve ごと、
  C0\*・C5\*・C6\* は support-active な全体 scope = `A = q.Target` の
  A-subnerve で1回。導出台が空の cell はどの scope にも現れない)。
  含めない: 無限 regime、
  係数の一般化、doctrine 間 comparison、C\* の最簡性・条項系の一意性の
  主張、hunt の bound 拡張(off-loop 探索の再開)そのもの、
  **一様不変性の必要条件の主張(C\* または他条項による)**、
  **`G_local-v1` 以外の grammar への不可能性・絶対的不可能性・
  半径 `r ≥ 2` への一般化**(`T_n` 族の `n > 2r+1` 論法は frontier)。
- `capability categories`: sufficiency、reduction、
  certificate-closure、nonlocality、counterexample。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に
  置き、固定 statement と completion criteria だけで完了判定する。
- `portfolio constraint`: 十分性(ii)だけ、または非局所性(iii)だけで完了
  扱いしない。還元(i)・両柱・現行 C の非必要性 witness(iv)・非退化
  正例(v)の全面の Lean artifact 接続を要求する。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、反証なら
  `target-refuted`、全完了条件と final review を満たした場合だけ
  `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各 cycle は
  proof obligation delta で評価する。
- `dullness filter`: 次を弾く。単一 chart・critical cell 空・retained
  FaceTwin 類空で C\* が空虚に成立するだけの発火、両側 H¹ 零で全単射が
  vacuous に成立する witness、free-pair 除去が全 face を消して C5\*・C6\*
  が空虚化した witness、有限 zero-result(hunt の登録 case 群)を (ii) の
  証明根拠と称すること、C\* の言い換え(同値な条項の再命名)だけの
  「改訂」、反例が型不一致だけで成立する構成、一様不変性の検査を有限個の
  law family の標本に置き換える弱化、(v) の発火項目を共通条件(一様
  不変・非零 H¹・critical 非空)を満たさない fixture へ分離して充足と
  数える構成、`Obs_G` を登録 grammar より粗く転写して観測等値 (iii)(a)
  を自明化する構成、T3 / T6 の label を assumption・axiom・登録 ledger
  参照で済ませる構成、非局所性 (iii) を条項系候補の有限列挙の全滅で
  代用する弱化。
- `frontier`: C\* 条項独立性の witness 目録(各条項を外すと十分性が破れる
  有限例の系統的整備。hunt の UnkilledTwin は C5\* の独立性素材)、C\* の
  最簡化(条項の冗長性判定)、G-104 の条件 C と C\* の含意関係の判定
  (C ⟹ C\* か。十分条件としての強弱比較)、blocker 帰納の被覆拡張
  (lift 数無制限・cross-chart nonloop incidence)、定量版(非全単射
  block の次元下界)、第VIII部測定理論・論文Aへの
  「十分条件+観測限界」の対としての接続、**半径 `r` 一般化**(任意固定
  半径の typed ball が一致する `T_n` 対の構成、`n > 2r+1` 局所一致
  論法。(iii) の witness 族化)、**拡張 grammar での特徴づけ再挑戦**
  (neutral cycle 長などの大域不変量を1成分追加した grammar での iff。
  後続 G-108 候補であり本カードでは主張しない)、reading 圏 `Read_L`
  上の functor 化と C\*-locus 上の局所定数性(local-system 化。
  `program context` の後続カード素材)、一般射の
  `(dim ker, dim coker)` jump data(前掲の定量版の圏水準版)、
  persistence module 読みの有限計算可能性。
- `spine`(仮説的道筋。壊してよい): U0 値部分集合還元の Lean 化 →
  U1 前処理(FaceTwin / free-pair / critical)の定義と free-pair 除去の
  H¹ 比較不変性 → U2 CertifiedSwap 閉包の cycle 消滅補題(blocker の
  定理化。retained face-chain 構造上の帰納)→ U3 十分性 → U4 非局所性
  (`Obs_G` 定義 → T3 / T6 転写 → 観測等値の decidable 計算 →
  (i) 経由の label 導出 → 分離 theorem)→ U5 witnesses。

- `target theorem`: **Uniform Invariance Sufficiency and Nonlocality
  Theorem**(一様不変性の十分性・非局所性定理)。G-104 カードの
  comparison data 構成から
  law family に依存しない部分 — 読み対 `q ≤ q'`(`CoarserThan`)、粗さ
  から G-103 factorization で誘導される canonical factor `π`
  (`comparisonFactor`。supplied factor は認めない)、K1 導出台つき
  nerve 対、nerve 射 `φ`、hereditary 退化宣言、π-両立 — を
  **comparison geometry** として固定し、K0 / K1 生成係数の生成規則を
  そのまま使い、次の定義群をカードで固定する。
  - **一様不変性**: comparison data(comparison geometry = 読み対
    `q ≤ q'`・factor `π`・nerve 対・nerve 射 `φ`・chart 台)を固定した
    述語として定義する: comparison data が一様不変であるとは、**任意の**
    `FiniteLawFamily` `laws` と、`laws` が `q`・`q'` の双方について
    adequate であることの任意の証明とについて、その K0 / K1 生成係数の
    生成 comparison map(G-104 (i) の canonical 写像)が H¹ の全単射を
    誘導することをいう。law family と adequacy 証明は本述語の**内部で
    量化される束縛変数と domain condition** であり、target theorem の
    外側の固定 premise ではない(固定した単一 family に対する pointwise
    bijectivity は一様不変性ではない)。
  - **A-subnerve**: 非空 `A ⊆ q.Target` に対し、粗側は K1 導出台が `A` と
    交わる cell、細側は導出台が `π⁻¹(A)` と交わる cell が成す supported
    部分 nerve(台は `A` / `π⁻¹(A)` との交わりへ制限して読む)。係数は
    定数 `ℚ`。
  - **前処理(reduction。各評価 scope — C1\*–C4\* は各 A-subnerve、
    C0\*・C5\*・C6\* は `A = q.Target` の support-active 全体 scope — の
    粗側・細側で別々に行う。導出台が空の cell はどの scope にも属さず、
    前処理にも条項にも読まれない)**:
    1. **FaceTwin 類**: exact な ordered boundary triple と K1 導出台が
       ともに等しい face の同値類。
    2. **one-pass free-pair 除去**: self-loop `e` と類 `(e,e,e)` の対で、
       `e` が他の FaceTwin 類の boundary に現れないものを、FaceTwin 類
       構成直後の snapshot に対し**全て同時に1回だけ**除去する(反復・
       選択順序・結果依存の再適用はしない)。残った edge / FaceTwin 類を
       retained と呼ぶ。
    3. **cycle-critical edge**: retained edge のうち、self-loop、または
       当該 edge を除いた **retained edge だけ**の無向グラフで両端点間に
       path が残るもの(free-pair 除去済みの edge は path に使えない)。
       **critical chart**: cycle-critical edge の端点、または retained
       FaceTwin 類の boundary edge の端点。
    4. **active fine chart / port**: mapped 像が cycle-critical 粗側 edge
       である retained 細側 edge の端点、または mapped 像が retained
       粗側 FaceTwin 類の member である retained 細側 face の boundary
       端点。critical 粗側 chart `c` の **port** は `φ`-fiber が `c` の
       active fine chart 全体。
  - **条項系 C\***(incidence / support レベル。評価 scope: C1\*–C4\* は
    各非空 `A` の A-subnerve ごと、C0\*・C5\*・C6\* は `A = q.Target` の
    support-active 全体 scope で1回):
    - **C0\***: 各 critical 粗側 chart の台は、その port に属する細側
      chart 台の `π`-像の合併に等しい。
    - **C1\***: 各 critical 粗側 chart の port は非空であり、両端点が
      port に属する scope 内細側 edge 全体の無向グラフで連結である。
    - **C2\***: 各 cycle-critical 粗側 edge は、mapped 像がそれである
      retained 細側 edge(lift)を持つ。
    - **C3\*(局所 fiber acyclicity。明示の例外条項)**: 各粗側 chart
      fiber で、retained かつ退化宣言された fiber 内 edge が張る任意の
      `ℚ`-係数 1-cycle は、**退化宣言された member を少なくとも一つ持つ
      retained FaceTwin 類で、boundary 3辺すべてが当該 fiber の当該
      edge 集合にあるもの**の boundary の `ℚ`-線形結合で張られる。
    - **C4\***: 各 retained 粗側 FaceTwin 類は、mapped 像がその類の
      member である retained 細側 face を少なくとも一つ持つ。
    - **CertifiedDirect**(同一 cycle-critical 粗側 edge へ写る retained
      lift の対 `u ≠ v` で edge 導出台が等しいものの間の関係):
      - **SLOT**: 同一 retained 粗側 FaceTwin 類へ写る2つの retained
        細側 face が、ordered boundary の同一 slot 1箇所だけで `u` / `v`
        に差し、他の2辺は cell として同一、face 導出台も等しい。
      - **KILL**: retained 細側 face `f` の boundary が `(u, v, z)` または
        `(v, u, z)`、別の retained 細側 face `g` の boundary が
        `(z, z, z)` であり、`f`・`g` は退化宣言でなく、その粗側像が
        それぞれ `(E, E, Z)`・`(Z, Z, Z)`(`E` = 当該粗側 edge、`Z` = `z`
        の粗側像)の retained 類 member であり、`u`・`v`・`z` の edge
        導出台と `f`・`g` の face 導出台がそれぞれ等しい。
      - **CertifiedSwap**: SLOT または KILL の無向関係の反射推移閉包。
    - **C5\***: 各 cycle-critical 粗側 edge の retained lift 全体は高々
      一つの CertifiedSwap 類を成す。
    - **C6\***: critical 粗側 self-loop の各 CertifiedSwap 類は細側
      self-loop の代表を持つ。
    C\* には、comparison map・粗側複体・両側 global H¹ の同型・消滅・
    rank 一致と同値または片方向に近い条項、およびその `A`-量化を含めない
    (明示の例外は C3\* の局所 fiber acyclicity のみ。G-104 の C3 と同じ
    理由の範囲で許し、拡張しない)。本カードの C\* は hunt 登録 candidate
    `R2-CSTAR-CERTIFIED-v3` に対し、**support-active 全体 scope 化**
    (登録評価器は導出台が空の cell も全体 scope の前処理と lift 母集団に
    含めていた)という明示差分1点を加えて固定する。この差分は、どの
    law-generated 係数からも不可視な cell を条項が読む経路 — A-block
    水準の一様不変性判定と一致しない読み — を塞ぐ是正であり、
    対応関係は anti-weakening rule の改訂記録規則で管理する。
    **改訂記録(2026-08-11、`target-refuted`)**: この C\*
    (CERTIFIED-v3 + support-active)は初版 statement の必要性 claim
    (旧 (iii))の exact 有限反例
    `CONTRACTIBLE-TRIANGLE` で反証された。fixture = 非零 H¹ の
    self-loop 成分と H¹-neutral な filled triangle 成分の直和、粗側
    Target 2点・細側 Target 3点、`π = (0, 0, 1)`(`fine = id` と取れば
    `comparisonFactor_unique` により supplied factor ではなく canonical
    factor として実現される)。全非空 `A`(`{0}` = 1→1 rank 1、
    `{1}` = 0→0 rank 0、`{0,1}` = 1→1 rank 1)で比較は同型 = 一様
    不変だが、C0\*・C1\*・C2\*・C4\* が破れる。機構 = one-pass
    free-pair 除去は `(e, e, e)` 型のみを読むため、boundary 3辺が相異なる
    filled triangle の H¹-neutral な retained face 構造を還元できない。
    fixture の正本は Issue #3948 required catalog(exact normal form
    登録済み)。後継 candidate v4(`SUPPORT-ACTIVE-JOINT-COLLAPSE`)・
    v5(`COORDINATE-DOUBLED-CYCLE`)も invalid(Issue #3948 Round 14 /
    15)。**statement v2 での位置(2026-08-11)**: ハント終端(Stop B:
    `CSTAR-not-expressible-in-G_local-v1`)を受け、v2 は C\* を
    必要十分候補ではなく十分条件としてのみ主張する形へ改訂された。
    十分性方向の証拠は CERTIFIED-v3 の最終 bounded population
    (2,166 case)における反例ゼロだが、これは bounded 証拠であり、
    候補系譜には Chain3(v1)・UnkilledTwin(v2)という十分性方向の
    反例史がある。
    **改訂記録2(2026-08-11、v2 も `target-refuted`)**: v2 の十分性
    (ii) も exact 有限反例 `PROPER-CHAIN3-PLUS-BRIDGE-DIGON` で反証
    された。fixture = Chain3 成分と「粗側 bridge 1本(`E = (1,2)`)/
    細側 parallel lift 2本(`u`、`v`)」の直和。Source = Bool、細側
    read = 恒等、粗側 read = 定数(Target 1点)、canonical
    `π = (0, 0)`(`comparisonFactor_unique` により canonical 実現)、
    退化宣言なし、粗側台 `{0}`・細側台 `{0,1}`。唯一の非空 `A = {0}`
    で粗側 H¹ = 1・細側 H¹ = 2・比較 rank 1 = 非全射(非一様)だが、
    C0\*–C6\* は全条項成立する。機構 = 粗側 `E` は bridge であり
    cycle-critical でないため現 C\* はその lift を C2\* / C5\* の対象に
    しないが、細側では `u − v` の digon が新しい H¹ 類を作る — 現 C\*
    は「粗側 cycle の解像」を検査するが「非 critical 領域上の細側
    cycle の新規生成」を検査しない。定数 law family は両読みに
    adequate なので (i) に依存しない直接反例である。検証=レビュー側
    exact evaluator+Claude の engine 再現・独立有理線形代数(全符号
    規約で細側 H¹ > 比較 rank)・機構手検証の三重。純 incidence 条項
    での改訂素材として criticality-reflection 型(mapped retained
    細側 cycle-critical edge の粗側像も cycle-critical)が挙がって
    いるが、これを足すだけで十分性が回復する証明はない。C\* 後継は
    新 semantic ID の事前登録と独立再査読を経る。H¹・rank・
    `NoNewFineCycle` のような結論相当 field を C\* または comparison
    入力へ密輸しない。
  - **観測写像 `Obs_G`(半径1 grammar `G_local-v1` の忠実転写)**:
    量化域と型を signature 水準で固定する —
    `FiniteComparisonPresentation`(`DecidableEq` 有限 target / cell・
    `Finset` support・実行可能 factor を備えた computable
    presentation)、`toGeometry : FiniteComparisonPresentation →
    comparison geometry`、`computedFactor` と canonical
    `comparisonFactor` の一致 theorem、presentation 非依存の観測値型
    `GLocalV1ObsValue`、`UniformPresentation P := 一様不変
    (P.toGeometry)`、そして `obsG : FiniteComparisonPresentation →
    GLocalV1ObsValue`。`obsG` は恒久 grammar の**独立転写**であり、本
    カード (ii) の条項系(`CStarV3SupportActive`: CERTIFIED-v3 +
    support-active の one-pass reduction 上)とは**別型・別述語**として
    固定する。恒久 grammar の semantics は登録 contract に従う:
    `GLocalV1V5Reduction`(v5 reduction の全 irreducible terminal と
    removal DAG)の上で、(1) terminal 全体で読む条項 conjunction
    vector `GLocalV1ConditionVector`(C0 / C5 / C6 と C1–C4。
    `CStarV3SupportActive` との一般同値は主張しない — T3 / T6 上の
    数値一致は同値の証拠ではない)、(2) removal DAG の全 path に現れる
    packet-kind union、(3) 全 terminal の rooted typed incidence ball
    (半径1)の aggregation を `A`-label を捨てた clip2(`0 / 1 / ≥2`)
    histogram で読む成分、(4) 登録 boolean flag 群、(5) `π`-preserving
    target relabel orbit 上の最小化。定義は登録済み恒久 contract
    (`G-local-v1-permanent-structural-contract-v1`、canonical SHA-256
    `5a14faf44049b8906200d5dbd052bc9fd5669ff84dfb6452e6137e98dfbd51c8`)
    の観測成分の**忠実転写**であり、成分の省略・追加・truncation 変更を
    しない(構成要素対応表を artifact に固定する)。忠実転写の義務は
    定義水準(全成分の定義+対応表)と T3 / T6 上の評価であり、packet
    rewrite の一般論(合流性など)は義務に含めない(T3 / T6 では packet
    成分は空集合と評価される)。uniformity label・terminal 列挙・条項
    bit・supplied factor を presentation の field として受け取ることは
    放電と数えない。
  この設定で次を証明する。
  1. **(i) 値部分集合還元**: comparison data が一様不変であることと、
     すべての非空 `A ⊆ q.Target` について A-subnerve の定数 `ℚ` 係数 H¹
     比較が全単射であることは同値である。証明は hunt-report §R0 の
     一般手証明の Lean 化であり、既存の block 直和分解
     (`lawGeneratedH1BlockEquiv`)・block 自然性
     (`generatedComparisonH1Map_block_naturality`)・descend の π-可換
     (`lawDescend_comparisonFactor`)を再利用し、残る3 conjunct
     (law-value block と A-subnerve 複体の同定、global 全単射と
     blockwise 全単射の同値、indicator law family による任意非空 `A` の
     実現と adequacy)を新規に theorem 化する。
  2. **(ii) 十分性**: C\* が成立するならば comparison data は一様不変で
     ある。(i) により各 A-block の定数係数比較へ還元し、free-pair 除去の
     H¹ 比較不変性と CertifiedSwap 閉包による lift 差 cycle の消滅補題
     (blocker `PB-R2-NONFREE-GLOBAL-FACE-CHAIN` の定理化。free pair を
     持たない任意の retained face 構造に対する一般帰納)を経由する。
  3. **(iii) 非局所性(radius-1 inexpressibility)**: `G_local-v1` で
     表現可能ないかなる条項系も一様不変性を特徴づけない。正確には、
     witness 対 `T3`(`TERNARY-CYCLE-3`)・`T6`(`TERNARY-CYCLE-6`)を
     hunt の登録 structural input から Lean へ転写し、次の4 theorem で
     固定する: **(a) 観測等値** `obsG T3 = obsG T6`(computable
     presentation 上の決定可能計算)、**(b)** `T3` は
     `UniformPresentation`((i) 経由の有限 A-block 判定。全非空 `A` で
     1→1 / 0→0 / 1→1)、**(c)** `T6` は `UniformPresentation` でない
     (`A = {0}` の block で粗側 H¹ 次元 3・細側 1 の非全単射)、
     **(d) 分離**: `∀ p : GLocalV1ObsValue → Prop, ¬ ∀ P :
     FiniteComparisonPresentation, (p (obsG P) ↔ UniformPresentation
     P)`((a)–(c) の帰結だが、量化形を theorem として固定する)。
     (d) の量化は **computable presentation 全体に限定**する — abstract
     comparison geometry 全体への量化は presentation 存在定理と
     presentation 変更不変性を要するため本カードでは主張しない。主張は
     `G_local-v1` **相対**であり、他 grammar・絶対的不可能性・半径
     一般化を含まない。Round 15 の登録 label と Stop-B checker の結果は
     転写の照合先(証拠)であり、(a)–(c) の証明根拠ではない。
  4. **(iv) 現行条件 C の非必要性地図**: G-104 の C0–C6 の**各条項**に
     ついて、一様不変(全非空 `A` で比較が全単射)だが当該条項が破れる
     有限 witness を固定する(7 witness)。非退化性の scope は条項の型
     ごとに固定する: **座標 subnerve 相対条項(G-104 の C1–C4)**は、
     **同じ非空 `A`**(indicator 実現)で条項破れと両側 H¹ 非零が同時に
     成立すること。**nerve 全体条項(G-104 の C0・C5・C6)**は、全体
     scope での破れに加えて、その破れを構成するデータ(台差分の
     target、または lift 対の導出台)と交わる非空 `A` の block で両側
     H¹ 非零が成立すること。hunt の R1 witness 群
     (`results-summary.json` に固定済みの完全 fixture)を Lean へ転写
     してよい。これは Atlas 定理の条件 C のどの条項も必要でないことの
     theorem 水準の地図であり、(iii) とあわせて「十分条件は与えられるが
     この観測言語では必要十分に届かない」構図を固定する。
  5. **(v) 非退化発火 witness portfolio**: 発火 witness の portfolio を
     固定する。**各 witness に共通で要求する条件**: C\* 全条項と一様
     不変性が成立、`π` 非単射、**同一 witness 内**のある非空 `A` で両側
     H¹ 非零、cycle-critical edge と retained FaceTwin 類がともに非空。
     その上で、**portfolio 全体として**次の各項目を少なくとも一つの
     witness で非空虚に発火させる: KILL certificate の実使用かつ
     CertifiedSwap の推移閉包が direct 隣接を真に超えること
     (Chain3 型)、SLOT certificate の実使用、C3\* の非空虚な発火
     (retained な退化宣言 fiber 内 edge の非零 cycle が実際に face
     boundary で張られる)、C6\* の非空虚な発火(critical 粗側
     self-loop の、大きさ2以上の CertifiedSwap 類が細側 self-loop 代表を
     持つ)、one-pass free-pair 除去が実際に少なくとも1対を除去する
     こと。発火項目を、共通条件を満たさない fixture(H¹ 零・critical
     集合空など)へ分離して充足と数えることは認めない。
  (i)(ii) は一般の有限 Source と well-formed comparison data について
  証明する(law family と adequacy は一様不変性の内部量化であり、
  theorem の外側で固定しない)。(iii) は `Obs_G` の定義と witness 対の
  転写により固定し、分離 theorem (d) の data 量化は一般とする。witness
  ((iii) の T3 / T6、(iv)(v))は hunt artifact の固定 fixture
  (`results-summary.json` / `results-stop-b-summary.json`)の転写
  または新設で具体化してよい。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/UniformInvariance/` 配下。
  `ResolutionInvariance/`(G-104)・`CanonicalResolution/`(G-103)・
  `TwoPhase/`(G-102)と `Formal/AG` は参照のみ(再定義しない)。
  `research/experiments/g104-necessity-map/` は fixture 素材・転写照合先・
  戦略参照のための証拠 artifact であり、証明根拠として引用しない(engine /
  checker 実装への依存も持ち込まない)。G-107 の完了面は (i)–(v) まで。
  非局所性 (iii) は登録恒久 contract の grammar **相対**であり、他の観測
  grammar への不可能性・絶対的不可能性・半径 `r ≥ 2` への一般化は主張
  しない。C\* の最簡性・一意性、hunt bound の拡張探索、論文A本文の
  変更は主張しない。
- `target proof artifacts`: 一様不変性の定義、A-subnerve 定数係数比較の
  定義、値部分集合還元 theorem(indicator law family の構成 def と
  adequacy theorem、block ≅ A-subnerve 同定 theorem、global ⟺ blockwise
  同値 theorem を含む)、前処理(FaceTwin / one-pass free-pair 除去 /
  cycle-critical / port)の定義、free-pair 除去の H¹ 比較不変性 theorem、
  CertifiedDirect(SLOT / KILL)と CertifiedSwap の定義、certificate
  閉包の cycle 消滅補題、条項系 C\* の定義、**C\* の決定手続**(有限
  入力から構成する `Decidable (CStar data)` instance、または boolean
  checker とその sound / complete theorem。非構成的な古典 instance で
  済ませない。入力は `DecidableEq` を持つ有限 target / cell・`Finset`
  support・実行可能な factor 計算を備えた computable presentation として
  定義し、既存 comparison geometry への sound / complete 対応 theorem を
  伴う)、十分性 theorem、**観測写像 `Obs_G` の定義と恒久 contract 構成
  要素対応表**、T3 / T6 fixture 定義(登録 structural input との対応
  記録つき)、観測等値 theorem (iii)(a)、T3 一様不変 theorem (iii)(b)・
  T6 非一様 theorem (iii)(c)、分離 theorem (iii)(d)、現行 C 非必要性
  witness 7種、非退化発火 witness portfolio、
  report `research/reports/G-107-aat-uniform-invariance-characterization.md`。
- `target proof strategy`: U0 値部分集合還元(hunt-report §R0 の conjunct
  対応表に従う)→ U1 前処理定義と free-pair 除去の比較不変性 → U2
  certificate 閉包の cycle 消滅補題(blocker の定理化)→ U3 十分性 →
  U4 非局所性(`Obs_G` 定義 → T3 / T6 転写 → 観測等値の decidable
  計算 → (i) 経由の label 導出 → 分離 theorem)→ U5 witnesses。
  既存成果の利用 map:
  `ResolutionInvariance/ComparisonData.lean`(`comparisonFactor_commutes` /
  `lawDescend_unique` / `lawDescend_comparisonFactor`)、
  `ResolutionInvariance/LawGeneratedComplex.lean`(K0 / K1 生成複体)、
  `ResolutionInvariance/LawValueCoordinateSubnerve.lean`
  (`block_cell_injective` / `exists_block_coordinate_cell_iff`)、
  `ResolutionInvariance/LawValueBlockDecomposition.lean`
  (`cochainBlockEquiv` / intertwining)、
  `ResolutionInvariance/LawValueBlockCohomology.lean`
  (`lawGeneratedH1BlockEquiv`)、
  `ResolutionInvariance/LawValueBlockComparison*.lean`(block comparison
  と naturality)、`CanonicalResolution/Reading.lean`(`FiniteLawFamily` /
  `Adequate`)、G-102 の `ThreeCochainComplex` / `H1` / `h1Map`。hunt
  artifact の固定 fixture(R1 witness 7種・Chain3・UnkilledTwin ほか、
  `results-summary.json` の完全データ)は witness 素材として転写して
  よい(engine 実装への依存は持ち込まない)。(iii) の転写照合先は
  Stop-B 恒久 artifact(`g_local_v1.py` の観測成分定義・T3 / T6
  structural input・`results-stop-b-summary.json`)とする(同前、
  checker 実装への依存は持ち込まない)。固定 statement と完了条件は
  本カードのみを正本とする。
- `target theorem completion criteria`: 全 artifact が sorry なしで
  `ResearchLean` に受理され、axiom / placeholder audit が clean である
  こと。ledger の `discharge-required` を放電し、T3 audit で provenance、
  proof-use、structure-field escape、route integrity を監査すること。
  Lean / report / tracking Issue を同期し、final review packet を作り、
  `$math-lean-review research/goals/G-107-aat-uniform-invariance-characterization.md G-107-aat-uniform-invariance-characterization`
  の4査読がすべて `No major findings` であること。
- `target premise discharge policy`: 入力に残せるのは comparison
  geometry の構成データ(有限非空 Source、読み対 `q ≤ q'` の
  `CoarserThan` witness、nerve / nerve 射 / chart 台)だけである。factor
  `π` は粗さから誘導される canonical `comparisonFactor` のみを指し、
  supplied factor・compatibility certificate を入力として受け取ることは
  放電と数えない。law family と adequacy は一様不変性の
  内部量化であり、入力・premise として固定した family に対する pointwise
  定理を completion と数えない。値部分集合還元、前処理の well-definedness、
  free-pair 除去の比較不変性、certificate 閉包補題、十分性・非局所性の
  両柱、witness の非退化性はすべて completion までに生成・証明する。
  C\* の成立・一様不変性・全単射性を theorem argument、typeclass、
  structure field、certificate field で受け取るだけでは放電と数えない。
- `target material premise ledger`:
  - `有限非空 Source / 読み対と粗さ順序(comparison geometry)`:
    `ambient-boundary`。G-103 確定 artifact(`Reading` / `CoarserThan` /
    `factorsThrough_iff_coarserThan`)の参照のみ。Target の非空性を
    含む。factor `π` は canonical `comparisonFactor` として導出し、
    supplied factor を入力幾何に含めない。
  - `law family と adequacy`: premise ではない。一様不変性の**内部量化**
    (束縛変数と domain condition)としてのみ現れる。`ambient-boundary`
    として受け取り固定 family の pointwise bijectivity theorem を作る
    ことは、本カードが除外した pointwise 必要性への弱化であり completion
    と数えない。
  - `comparison data(nerve / nerve 射 / K1 導出台 / hereditary 退化宣言 /
    π-両立)`: `ambient-boundary`(入力幾何)。well-formedness は G-104 の
    定義を継承する。
  - `K0 / K1 生成係数と block 機構`: `ambient-boundary`。G-104 / G-102 の
    review 済み artifact の参照のみ(再定義しない)。
  - `値部分集合還元 (i)`: `discharge-required`。indicator law family の
    構成と adequacy、block ≅ A-subnerve 同定、global ⟺ blockwise 同値の
    3 conjunct を theorem 化する。fixture 上の数値一致で代用しない。
  - `前処理の well-definedness`: `discharge-required`。FaceTwin 類・
    one-pass 同時除去の決定性(順序非依存)・scope ごとの再計算を定義に
    固定する。
  - `free-pair 除去の H¹ 比較不変性`: `discharge-required`。除去前後で
    A-block 比較の全単射性が同値であることを theorem 化する。
  - `CertifiedSwap 閉包の cycle 消滅補題`: `discharge-required`。本 GOAL の
    中心補題(blocker `PB-R2-NONFREE-GLOBAL-FACE-CHAIN` の定理化)。free
    pair を持たない任意の retained face 構造への一般帰納で証明し、有限
    fixture 族の全数検証で代用しない。
  - `条項系 C\*`: (ii) の `direction-hypothesis`(含意の仮定側)。
    (iii) の観測成分は `GLocalV1ConditionVector`(恒久 grammar の
    all-terminal 条項 vector)であり、本条項系
    (`CStarV3SupportActive`)とは**別型・別述語**として固定する
    (一般同値を主張しない)。結論相当
    premise ではない理由: C\* は有限 incidence / support データと退化
    宣言だけから決定可能な条項系であり、comparison map・両側 H¹・rank を
    参照しない(明示の例外は C3\* の局所 fiber acyclicity のみで、
    G-104 の C3 と同じく個々の chart fiber の内部データだけに依存する)。
  - `C\* の決定手続`: `discharge-required`。有限入力からの decision
    procedure(`Decidable` instance または bool checker + sound /
    complete theorem)を構成する。非構成的な古典 instance(`Classical.dec`
    等)で済ませることは放電と数えない。既存 API の chart 台は `Set`、
    canonical factor は `Classical.choose` 由来であり、そのままでは
    計算可能な equality / membership を供給しないため、`DecidableEq` を
    持つ有限 target / cell・`Finset` support・実行可能な factor を備えた
    **computable presentation** を定義し、既存 comparison geometry との
    sound / complete(または同値)対応 theorem を併せて放電する。
    presentation の導入だけで対応 theorem を欠く checker は放電と
    数えない。
  - `Obs_G の忠実転写 (iii)`: `discharge-required`。登録恒久 contract
    (canonical SHA-256
    `5a14faf44049b8906200d5dbd052bc9fd5669ff84dfb6452e6137e98dfbd51c8`)
    の観測成分5種と Lean 定義の構成要素対応表を artifact に固定する。
    成分の省略・追加・truncation 変更(粗視化・細密化)は放電と数えない。
    義務は定義水準+T3 / T6 上の評価であり、packet rewrite の一般論は
    含めない。
  - `T3 / T6 witness の転写と label (iii)`: `discharge-required`。登録
    structural input(name-free semantic SHA)との対応を記録し、
    T3 の一様不変・T6 の非一様を **(i) 経由の Lean 内有限計算**で証明
    する。Round 15 ledger・Stop-B checker 結果の参照だけで label を
    立てることは放電と数えない。
  - `分離 theorem (iii)(d)`: `discharge-required`。factorization 論法
    (観測値上の任意述語 `p` に対する反証)で証明し、条項系候補の有限
    列挙で代用しない。
  - `現行 C 非必要性 witness 7種 (iv)`: `discharge-required`。存在
    witness。(iv) の scope 規定(相対条項は同一 `A` での同時発火、全体
    条項は破れ関与データと交わる `A` での両側非零)を満たす。型不一致
    vacuity・零 H¹ だけの破れは不可。
  - `非退化発火 witness portfolio (v)`: `discharge-required`。各 witness の
    共通条件(C\*・一様不変・`π` 非単射・同一 witness 内の非零 H¹・
    critical 非空)と、portfolio 全体の発火項目(KILL 推移閉包・SLOT・
    C3\*・C6\*・free-pair 除去)を (v) の規定どおり満たす。route
    integrity audit で使う。
- `target anti-weakening rule`: C\* に cohomological 条項(comparison
  map・粗側複体・両側 global H¹ の同型・消滅・rank 一致と同値または
  片方向に近い条項、およびその `A`-量化)を追加しない(C3\* の例外を
  拡張しない)。(ii) を「事前登録済み bound 内で反例ゼロ」へ、(i) を
  fixture 検証へ、一様不変性を有限個の law family の標本検査へ弱めない。
  law family を theorem 外側の固定 premise へ移して一様量化を pointwise
  化しない。(iii) について: `Obs_G` を登録 grammar より粗く(成分省略・
  truncation 粗大化)定義して観測等値を自明化しない。逆に禁止情報
  (exact cycle 長・H¹・rank・raw ID 等)を成分へ追加しない。T3 / T6 の
  label を assumption・axiom・structure field 化しない。非局所性を
  grammar 非相対の絶対主張へ強めない(過大主張の禁止)。証明の途中で
  C\* の条項を黙って変えない — 変更が必要になった場合は
  `target failure policy` 経由でカード改訂として扱い、hunt の
  candidate SHA(`R2-CSTAR-CERTIFIED-v3` =
  `cbb02677a055c69ecf0bb50a5de884fb55bbd4b4b59b75d256815eae69ec4daa`)
  との対応関係を改訂記録に残す。本カード時点の登録 candidate との差分は
  support-active 全体 scope 化の1点だけ(条項系 C\* 節に固定)であり、
  hunt を再開する場合は新 semantic ID として事前登録し直す。結論相当
  データを theorem argument、typeclass、structure field、certificate
  field へ移さない。
- `target route integrity gate`: 両柱の theorem・witness の provenance を
  law family、読みの比較射(G-103 factorization)、nerve 構成データ、
  review 済み predecessor、および hunt の登録 fixture(name-free semantic
  SHA)へ追跡する。(iii) の witness provenance は登録 structural input の
  semantic SHA と恒久 contract SHA へ追跡する。恒等比較・零 H¹・critical
  cell 空・空虚 certificate だけの発火、proof 後の GOAL 読み替えを
  completion に使わない。
- `target failure policy`: fail-closed を原則とする — カードが固定した
  subclaim((ii)、(iii)(a)–(c)、(iv)、(v))のいずれかが偽と確定した
  場合、まず `target-refuted` を記録する。artifact / statement の改訂は
  その後の別操作であり、記録を先送りする理由にしない。(ii) の反例
  (C\* 成立かつ非全単射 A-block)は `target-refuted` とし、反例
  fixture を固定した上で、同じ syntactic 文法(FaceTwin / free-pair /
  critical / certificate)内での C\* 改訂案を返す — cohomological 条項
  への差し替えは改訂案として認めない。(iii) は記録後の原因切り分けを
  層別に行う: 忠実転写した `obsG` の下で観測等値 (a) が不成立、または
  (b)(c) の label が hunt 登録値と食い違う場合、対応表を監査して転写の
  欠陥(modeling)なら転写をやり直し、対応表どおりでも不一致が残る
  場合は登録恒久 artifact 側の欠陥として Issue を起こして Stop-B 証拠の
  再検証まで `target-blocked` を重ねる。分離 (d) は (a)–(c) からの
  論理的帰結であり独立の反例を持たない。(i) の破れ(還元の反証)は
  一様不変性の量化定義の欠陥として本 GOAL を停止し、GOAL 改訂提案を
  返す(優先度は最上位)。
  補助補題(free-pair 除去の比較不変性・certificate 閉包補題)への反例は
  それだけでは `target-refuted` にしない — 補題を経由しない別経路が
  ありうるため proof strategy(spine)の撤回・改訂として扱い、(ii)
  本体と (iii)(a)–(c) の固定 subclaim の反証だけを `target-refuted` の
  根拠にする。(iv)(v) は witness 構成が成功条件であり、hunt fixture の
  転写不一致(Lean 側判定と食い違う)は modeling 欠陥として witness を
  作り直す — ただしカードが固定した witness subclaim 自体が偽と確定
  した場合は前掲の fail-closed 原則に従いまず記録する。ある条項について「一様不変 ⟹
  当該条項」が theorem として成立した場合(witness 不存在の証明)は、
  当該条項が実は必要だったという発見として、(iv) の当該項目を削除し
  C\* との関係を再検討する GOAL 改訂案を返す。(v) の発火項目の一部が
  共通条件と両立不能と判明した場合は、当該項目を別 witness へ分離する
  GOAL 改訂案を返す(G-104 の witness 分離改訂の先例に従う)。
  中心補題(certificate 閉包)を含む同じ blocker が二 cycle 続けば
  `target-blocked` とし、bounded 版(lift 数や face-chain 長で切った弱い
  定理)を成功と繰り上げない。claim boundary 外の機構が必要と判明した
  場合は本 GOAL を拡張せず、GOAL 改訂提案として返す。
