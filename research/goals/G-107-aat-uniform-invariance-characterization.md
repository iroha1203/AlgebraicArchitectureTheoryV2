# G-107-aat-uniform-invariance-characterization — 一様不変性の特徴づけ(Atlas 定理の必要十分化)

- `id`: `G-107-aat-uniform-invariance-characterization`
- `status`: `active`
- `priority`: `medium`
- `research mode`: `target-theorem`
- `predecessor`: G-104(Diagnostic Resolution Invariance Theorem、
  `target-theorem-proved`。report
  [research/reports/G-104-aat-resolution-invariance.md](../reports/G-104-aat-resolution-invariance.md))。
  comparison data / K0・K1 生成係数 / 条件 C / block 直和分解の確定
  artifact(`research/lean/ResearchLean/AG/ResolutionInvariance/` 配下)を
  正本として参照する。加えて off-loop 必要性地図ハントの Stop C
  checkpoint(Issue
  [#3948](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/3948)、
  PR #3952、artifact `research/experiments/g104-necessity-map/`)を
  **証拠地図**として参照する(1,918 semantic case の二方向反例ゼロと
  必要性反例群。証明根拠ではない)。
- `tracking issue`: [#3954](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/3954)
  (active 昇格はユーザー裁定 2026-08-09、成立はカード同期 PR のマージを
  もって)。
- `source note`: [docs/prd/aat_g104_necessity_map_hunt_prd.md](../../docs/prd/aat_g104_necessity_map_hunt_prd.md)
  (「停止後の接続」)、
  [research/experiments/g104-necessity-map/hunt-report.md](../experiments/g104-necessity-map/hunt-report.md)
  (§R0 一般手証明、§R2 候補系譜、blocker)
- `research aim`: G-104 の Atlas 定理は「条件 C ⟹ H¹ comparison 全単射」の
  十分条件定理である。本 GOAL はその逆向きを埋め、**一様不変性**
  (係数側を adequate な law family 全体で量化した H¹ comparison の
  全単射性)を、入力の incidence / support データだけから決定可能な条項系
  **C\***(hunt が固定した candidate `R2-CSTAR-CERTIFIED-v3` の theorem 化)
  で**必要十分に特徴づける**。これにより「どの解像度比較が診断を保つか」が
  comparison data から決定可能になり、Atlas 定理は十分条件の定理から
  特徴づけ定理へ昇格する。あわせて、law 量化を有限対象(粗側 Target の
  非空部分集合)へ落とす**値部分集合還元**を theorem として固定する。
  本定理は、reading 圏上の診断 local-system 構想(`program context`)に
  おける**同型領域の特徴づけ**として位置づく。
- `program context`(上位構図、2026-08-11 追記): 本カードの特徴づけ定理は
  次の構想の pair 水準の核である — law family 量化を固定した読みの圏
  `Read_L` 上で診断 `D_L(q) := H¹` を functor として構成し、C\* を満たす
  射は同型へ写り(本カード (ii)(iii) が pair 水準で固定する内容)、一般の
  射には `(dim ker, dim coker)` の jump data を付け、reading 空間を
  plateau と jump locus を持つ有限 poset persistence module として読む。
  functor 水準の主張(射の合成整合、圏上の局所定数性、jump data の一般論)
  は本カードでは claim しない。合成整合は輸送の 2-cell 整合(G-106 の
  領分)に接続するため、後続カードで固定する。この構図の下では、(iii) の
  反例は特徴づけの失敗ではなく jump locus のデータとして換金される
  (`target failure policy` の受理構図と整合)。関連考察は表示的意味論
  ノート
  [docs/note/aat_denotational_semantics_of_architecture.md](../../docs/note/aat_denotational_semantics_of_architecture.md)
  §10(Resolution Diagnostic Local-System)。
- `core tension`: 三つの稜線がある。第一に**特徴づけの実質**: C\* が
  cohomology 語彙を密輸すれば「全 A で全単射」の恒真化に堕ちる。C\* は
  FaceTwin 類・one-pass free-pair 除去・cycle-critical cell・SLOT / KILL
  certificate という有限 syntactic データだけを読む条項系であり、この
  資格制限(G-104 anti-weakening の継承)の下で必要十分が成り立つことが
  主張の中身である。第二に**十分性の中心補題**: 固定半径の局所
  certificate(SLOT / KILL)の反射推移閉包から、free pair を持たない
  任意の retained face-chain 構造の上で lift 差 cycle の大域的消滅を導く
  一般帰納が閉じるか。ここが計算探索の停滞点
  (blocker `PB-R2-NONFREE-GLOBAL-FACE-CHAIN`: 有限の
  linear / branching / cyclic / mixed / multichart fixture は全て閉じたが
  一般手証明が無い)であり、本 GOAL が定理化で埋めるべき本体である。
  第三に**必要性方向**: 各条項の破れから、indicator law の値 fiber が
  誘導する A-block 上の非全単射を実際に構成できるか。hunt の 1,918 case
  零結果は証明ではなく、bound 外の反例が存在すれば本 GOAL は
  `target-refuted` となる — その反例自体が C\* 改訂の一級素材であり、
  負の結果も換金される構図に置く。
- `rival`: Čech 理論の Leray 型定理(局所非輪状性という**十分**条件のみで
  特徴づけを与えない)、CEGAR 型の抽象化精細化(健全性方向のみ)、
  hunt の有限 zero-result(定理を伴わない計算的証拠)。差は「量化された
  不変性(一様不変性)を、有限 incidence / support データ上の decidable
  条項で**必要十分**に特徴づけ、両方向と還元を同一有限モデル上の Lean
  witness つきで固定する」点に置く。
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
  主張、hunt の bound 拡張(off-loop 探索の再開)そのもの。
- `capability categories`: characterization、reduction、
  certificate-closure、necessity-witness、counterexample。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に
  置き、固定 statement と completion criteria だけで完了判定する。
- `portfolio constraint`: 十分性(ii)だけ、または必要性(iii)だけで完了扱い
  しない。還元(i)・両方向・現行 C の非必要性 witness(iv)・非退化正例(v)の
  全面の Lean artifact 接続を要求する。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、反証なら
  `target-refuted`、全完了条件と final review を満たした場合だけ
  `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各 cycle は
  proof obligation delta で評価する。
- `dullness filter`: 次を弾く。単一 chart・critical cell 空・retained
  FaceTwin 類空で C\* が空虚に成立するだけの発火、両側 H¹ 零で全単射が
  vacuous に成立する witness、free-pair 除去が全 face を消して C5\*・C6\*
  が空虚化した witness、有限 zero-result(hunt の 1,918 case)を (iii) の
  証明根拠と称すること、C\* の言い換え(同値な条項の再命名)だけの
  「改訂」、反例が型不一致だけで成立する構成、一様不変性の検査を有限個の
  law family の標本に置き換える弱化、(v) の発火項目を共通条件(一様
  不変・非零 H¹・critical 非空)を満たさない fixture へ分離して充足と
  数える構成。
- `frontier`: C\* 条項独立性の witness 目録(各条項を外すと十分性が破れる
  有限例の系統的整備。hunt の UnkilledTwin は C5\* の独立性素材)、C\* の
  最簡化(条項の冗長性判定)、blocker 帰納の被覆拡張(lift 数無制限・
  cross-chart nonloop incidence)、定量版(非全単射 block の次元下界)、
  第VIII部測定理論・論文Aへの特徴づけ定理としての接続、hunt bound の
  拡張探索との相互フィード(反例が出た場合の C\* 改訂ループ)、
  reading 圏 `Read_L` 上の functor 化と C\*-locus 上の局所定数性
  (local-system 化。`program context` の後続カード素材)、一般射の
  `(dim ker, dim coker)` jump data(前掲の定量版の圏水準版)、
  persistence module 読みの有限計算可能性。
- `spine`(仮説的道筋。壊してよい): U0 値部分集合還元の Lean 化 →
  U1 前処理(FaceTwin / free-pair / critical)の定義と free-pair 除去の
  H¹ 比較不変性 → U2 CertifiedSwap 閉包の cycle 消滅補題(blocker の
  定理化。retained face-chain 構造上の帰納)→ U3 十分性 → U4 必要性
  (条項別の対偶構成)→ U5 witnesses。

- `target theorem`: **Uniform Invariance Characterization Theorem**
  (一様不変性の特徴づけ定理)。G-104 カードの comparison data 構成から
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
    law-generated 係数からも不可視な cell を条項が読む経路 — 必要性
    (iii) の A-block 反証経路と一致しない読み — を塞ぐ是正であり、
    対応関係は anti-weakening rule の改訂記録規則で管理する。
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
  3. **(iii) 必要性**: comparison data が一様不変ならば C\* が成立する。
     対偶で、各条項の破れから、その破れに関与する非空 `A` の A-block 上で
     H¹ 比較の非単射または非全射を構成する(support-active 化により、
     条項が読む cell は必ずいずれかの非空 `A` に可視である。条項別の
     構成。hunt の反例
     機構分析 — Chain3 の swap 推移連鎖・UnkilledTwin の差 cochain
     非消滅 — を構成の指針にしてよい。hunt artifact は証明根拠ではない)。
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
     してよい。これは C から C\* への置き換えが必要だったことの theorem
     水準の裏づけである。
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
  (i)(ii)(iii) は一般の有限 Source と well-formed comparison data に
  ついて証明する(law family と adequacy は一様不変性の内部量化であり、
  theorem の外側で固定しない)。witness((iv)(v))は hunt artifact の
  固定 fixture(`results-summary.json`)の転写または新設で具体化してよい。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/UniformInvariance/` 配下。
  `ResolutionInvariance/`(G-104)・`CanonicalResolution/`(G-103)・
  `TwoPhase/`(G-102)と `Formal/AG` は参照のみ(再定義しない)。
  `research/experiments/g104-necessity-map/` は fixture 素材と戦略参照の
  ための証拠 artifact であり、証明根拠として引用しない。G-107 の完了面は
  (i)–(v) まで。C\* の最簡性・一意性、hunt bound の拡張探索、論文A本文の
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
  済ませない)、十分性 theorem、必要性 theorem、現行 C 非必要性
  witness 7種、非退化発火 witness portfolio、
  report `research/reports/G-107-aat-uniform-invariance-characterization.md`。
- `target proof strategy`: U0 値部分集合還元(hunt-report §R0 の conjunct
  対応表に従う)→ U1 前処理定義と free-pair 除去の比較不変性 → U2
  certificate 閉包の cycle 消滅補題(blocker の定理化)→ U3 十分性 →
  U4 必要性(条項別対偶構成)→ U5 witnesses。既存成果の利用 map:
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
  よい(engine 実装への依存は持ち込まない)。固定 statement と完了条件は
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
  free-pair 除去の比較不変性、certificate 閉包補題、十分性・必要性の
  両方向、witness の非退化性はすべて completion までに生成・証明する。
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
  - `条項系 C\*`: (ii) では `direction-hypothesis`(含意の仮定側)、
    (iii) では結論側。結論相当 premise ではない理由: C\* は有限
    incidence / support データと退化宣言だけから決定可能な条項系であり、
    comparison map・両側 H¹・rank を参照しない(明示の例外は C3\* の局所
    fiber acyclicity のみで、G-104 の C3 と同じく個々の chart fiber の
    内部データだけに依存する)。
  - `C\* の決定手続`: `discharge-required`。有限入力からの decision
    procedure(`Decidable` instance または bool checker + sound /
    complete theorem)を構成する。非構成的な古典 instance(`Classical.dec`
    等)で済ませることは放電と数えない。
  - `必要性の条項別構成 (iii)`: `discharge-required`。各条項の破れから
    非全単射 A-block を構成する。hunt の零結果を証明根拠にしない。
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
  拡張しない)。(iii) を「事前登録済み bound 内で反例ゼロ」へ、(i) を
  fixture 検証へ、一様不変性を有限個の law family の標本検査へ弱めない。
  law family を theorem 外側の固定 premise へ移して一様量化を pointwise
  化しない。証明の途中で C\* の条項を黙って変えない — 変更が必要になった
  場合は `target failure policy` 経由でカード改訂として扱い、hunt の
  candidate SHA(`R2-CSTAR-CERTIFIED-v3` =
  `cbb02677a055c69ecf0bb50a5de884fb55bbd4b4b59b75d256815eae69ec4daa`)
  との対応関係を改訂記録に残す。本カード時点の登録 candidate との差分は
  support-active 全体 scope 化の1点だけ(条項系 C\* 節に固定)であり、
  hunt を再開する場合は新 semantic ID として事前登録し直す。結論相当
  データを theorem argument、typeclass、structure field、certificate
  field へ移さない。
- `target route integrity gate`: 両方向の theorem・witness の provenance を
  law family、読みの比較射(G-103 factorization)、nerve 構成データ、
  review 済み predecessor、および hunt の登録 fixture(name-free semantic
  SHA)へ追跡する。恒等比較・零 H¹・critical cell 空・空虚 certificate
  だけの発火、proof 後の GOAL 読み替えを completion に使わない。
- `target failure policy`: (ii) の反例(C\* 成立かつ非全単射 A-block)
  または (iii) の反例(一様不変かつ C\* 破れ)は `target-refuted` とし、
  反例 fixture を固定した上で、同じ syntactic 文法(FaceTwin / free-pair /
  critical / certificate)内での C\* 改訂案を返す — これは hunt の後継
  探索(bound 拡張)の一級素材であり、負の成果として受理可能である。
  cohomological 条項への差し替えは改訂案として認めない。(i) の破れ
  (還元の反証)は一様不変性の量化定義の欠陥として本 GOAL を停止し、
  GOAL 改訂提案を返す(hunt PRD の R0-fail 相当。優先度は最上位)。
  補助補題(free-pair 除去の比較不変性・certificate 閉包補題)への反例は
  それだけでは `target-refuted` にしない — 補題を経由しない別経路が
  ありうるため proof strategy(spine)の撤回・改訂として扱い、(ii)(iii)
  本体の反例だけを `target-refuted` の根拠にする。(iv) は witness 構成が
  成功条件であり、hunt fixture の転写不一致(Lean 側判定と食い違う)は
  modeling 欠陥として witness を作り直す。ある条項について「一様不変 ⟹
  当該条項」が theorem として成立した場合(witness 不存在の証明)は、
  当該条項が実は必要だったという発見として、(iv) の当該項目を削除し
  C\* との関係を再検討する GOAL 改訂案を返す。(v) の発火項目の一部が
  共通条件と両立不能と判明した場合は、当該項目を別 witness へ分離する
  GOAL 改訂案を返す(G-104 の witness 分離改訂の先例に従う)。
  中心補題(certificate 閉包)を含む同じ blocker が二 cycle 続けば
  `target-blocked` とし、bounded 版(lift 数や face-chain 長で切った弱い
  定理)を成功と繰り上げない。claim boundary 外の機構が必要と判明した
  場合は本 GOAL を拡張せず、GOAL 改訂提案として返す。
