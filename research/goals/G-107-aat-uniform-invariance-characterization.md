# G-107-aat-uniform-invariance-characterization — 一様不変性の defect 意味論と Atlas 定理の位置

- `id`: `G-107-aat-uniform-invariance-characterization`
- `status`: `active`
- `priority`: `medium`
- `research mode`: `target-theorem`
- `target status`: `statement-v3`(2026-08-11 改訂、4 lane 正式再査読
  待ち。受理までは target-theorem loop を起動しない)。改訂史: 初版
  (一様不変性 ⟺ C\* の必要十分特徴づけ)は `CONTRACTIBLE-TRIANGLE` で
  `target-refuted` → hunt 後継 round(v4・v5 も invalid)と人間裁定
  (選択肢1: 許容観測 grammar `G_local-v1` の固定)を経てハントは
  **Stop B**(verdict `CSTAR-not-expressible-in-G_local-v1`)で終端
  (Issue #3948 closed / COMPLETED)→ v2(C\* 十分性+非局所性)へ改訂
  → v2 の十分性も exact 反例 `PROPER-CHAIN3-PLUS-BRIDGE-DIGON` で
  `target-refuted`(改訂記録=歴史節)。現登録 C\*(CERTIFIED-v3 +
  support-active)は**両方向とも** exact 反例を持ち、v3 では active
  claim から除外して研究史・mechanism artifact として保存する。v3 は
  設計ノート
  [docs/note/aat_resolution_diagnostic_design.md](../../docs/note/aat_resolution_diagnostic_design.md)
  (observation factorization 構図・成果物の四分法)を設計根拠として、
  **defect 還元と決定可能性/Atlas positioning/observation
  nonfactorization の三本柱**で固定する(ユーザー裁定+Codex 設計相談
  2026-08-11)。**v3 再査読(2026-08-11、Major revisions)**: (iii) の
  現記述(G-104 条件 C からの新 premise なし持ち上げ)は Lean 実体
  (`ConditionC` は law-indexed、C1–C4 が `LawValueLabel` 量化)と
  不整合で導出不能と確定((i)(ii)(iv)(v) は独立再現で維持、反例
  なし)。**scope 裁定(2026-08-11、案b採用)**: (iii) を幾何述語
  `ConditionCAllA` + bridge theorem の2段構成へ改稿した(claim (iii)
  参照)。新 fixed head の 4 lane 正式再査読を経るまで target-theorem
  loop は起動しない。runtime state は tracking Issue #3954。
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
- `source note`: [docs/note/aat_resolution_diagnostic_design.md](../../docs/note/aat_resolution_diagnostic_design.md)
  (v3 の設計根拠正本: factorization 構図・機構分類・四分法)、
  [research/experiments/g104-necessity-map/hunt-report.md](../experiments/g104-necessity-map/hunt-report.md)
  (§R0 一般手証明、§R2 候補系譜、blocker、Stop-B 終端)、
  `research/experiments/g104-necessity-map/results-stop-b-summary.json`
  (2点分離の恒久証拠と `G_local-v1` 恒久 contract)
- `research aim`: G-104 の Atlas 定理は「条件 C ⟹ H¹ comparison 全単射」の
  十分条件定理である。本 GOAL は当初その必要十分化を、次いで C\* 十分性を
  target としたが、いずれも exact 有限反例で反証され、ハントは Stop B で
  終端した(経緯は `target status`)。v3 は設計ノートの observation
  factorization 構図に従い、**Atlas 定理が semantic zero-locus のどこに
  位置するか**を三本柱で定理水準に固定する。第一柱=**defect 還元と
  決定可能性**: exact defect profile `J_A := (dim ker H¹(f_A),
  dim coker H¹(f_A))` を定義し、**一様不変性**(係数側を adequate な
  law family 全体で量化した H¹ comparison の全単射性)⟺ `∀ 非空 A,
  J_A = (0, 0)` という還元定理と、computable presentation 上の
  sound / complete decider を固定する — 一様不変性の判定の正本を条項系
  ではなく計算に置く。第二柱=**Atlas positioning**: 幾何述語
  `ConditionCAllA`(条件 C の A-subnerve 読み替え)⟹ 零 defect を、
  bridge theorem((i) の block ≅ A-subnerve 同定の再利用)+ G-104
  受理済み pointwise theorem の2段で固定し、C0–C6 の各条項が個別には
  必要でないこと(7 witness)とあわせ
  `Condition-C locus ⊊ uniform locus` の包含と真性を定める。第三柱=
  **observation nonfactorization**: 半径1の登録観測 grammar
  `G_local-v1` を通して零判定が factor しないこと(T3 / T6 2点分離の
  Lean 化。grammar 相対)。三本で「計算・certificate・観測限界を混同
  せずに Atlas 定理の正確な位置を定める」ことが v3 の到達像である。
  条項系による判定の再現(iff)も新しい十分条件(C\* 後継)も v3 では
  主張しない(後者は機構カタログ整備後の G-108 以降)。本定理は、
  reading 圏上の診断 local-system 構想(`program context`)における
  **universal zero-jump 領域の座標・位置・観測限界**として位置づく。
- `program context`(上位構図、2026-08-11 追記。同日レビューで
  zero-jump locus / jump locus の層を是正): 本カードの三本柱定理は
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
  claim は block 水準の defect profile と分離形のみ — `J_L = (0, 0)` と
  `Function.Bijective` を結ぶ有限次元 bridge を含む functor 水準の
  正確化は後続カードで固定する。functor 水準の主張(射の合成整合、圏上の
  局所定数性、jump data の一般論)は本カードでは claim しない。合成整合は
  輸送の 2-cell 整合(G-106 の領分)に接続するため、後続カードで固定する。
  この構図の下で v3 の三本柱は次のように置かれる。`Z_univ` は defect
  意味論 `J` の零 locus であり、(i)(ii) はその座標(law 量化の semantic
  座標 `J_L` と有限 block の computational 座標 `J_A` の同値)と決定
  可能性を、(iii)(iv) は `Condition-C locus ⊊ Z_univ` という Atlas
  定理の位置を、(v) は「`Z_univ` とその補集合の分離は半径1の局所観測
  grammar のどの条項系にも不可能」という観測限界を固定する。一般の
  nonuniform 射は law-indexed jump profile のデータとなる。関連考察は
  設計ノート
  [docs/note/aat_resolution_diagnostic_design.md](../../docs/note/aat_resolution_diagnostic_design.md)
  と表示的意味論ノート
  [docs/note/aat_denotational_semantics_of_architecture.md](../../docs/note/aat_denotational_semantics_of_architecture.md)
  §10(Resolution Diagnostic Local-System)。
- `core tension`: 三つの稜線がある。第一に**還元と decider の正本性**:
  一様不変性は law family の全量化を含む semantic 述語であり、これを
  有限 block の `J_A` 零判定へ落とす還元定理(hunt-report §R0 手証明の
  Lean 化)と、computable presentation 上の sound / complete decider が
  立って初めて「判定の正本は計算」と言える。engine の `is_uniform()` は
  exact evidence であって正本ではない — この差を theorem で埋めるのが
  第一柱である。第二に**bridge の実質**: `ConditionCAllA` から任意 law
  の law-indexed `ConditionC`(Lean 実体は C1–C4 が `LawValueLabel`
  量化)を導く bridge が、(i) の block ≅ A-subnerve 同定の再利用で
  閉じるか。label の値 fiber と `A` の対応は (i) の機構そのものだが、
  C1–C4 の各条項が同定を通して transport できることは条項ごとの検証を
  要する — ここが positioning 柱を G-104 の再宣言から隔てる本体である
  (v3 初稿の「条件 C は law 非言及」前提は Lean 実体と不整合で導出
  不能と確定し、scope 裁定(案b)で本形へ改稿、2026-08-11)。第三に
  **非分解性の忠実性**: (v) の分離定理は、Lean 側の観測写像 `Obs_G` が登録済み恒久
  contract の grammar と一致して初めて意味を持つ。転写を粗くすれば分離は
  自明化し(別の弱い grammar についての定理に堕ちる)、細かくすれば偽に
  なる。忠実転写の構成要素対応表と、T3 / T6 の label を登録 ledger の
  参照ではなく Lean 内の有限計算((i)(ii) 経由)で再導出する規律が、
  この定理を「登録 artifact の言い換え」から theorem へ隔てる。三本が
  揃って初めて「Atlas 定理の位置」— 判定は計算で決定可能、条件 C は
  真に狭い十分域、零 locus は半径1観測から定義不能 — が定理水準で
  固定される。
- `rival`: Čech 理論の Leray 型定理(局所非輪状性という十分条件のみで、
  位置も限界も語らない)、CEGAR 型の抽象化精細化(健全性方向のみ)、
  hunt の有限 zero-result(定理を伴わない計算的証拠)、有限モデル理論の
  局所性定理(Hanf / Gaifman 型。一般論の局所性 rank であり、特定領域の
  登録観測 grammar への具体的分離を扱わない)、answer-encoding による
  自明な「特徴づけ」(判定結果をそのまま観測に含める構成。観測限界の
  主張を無内容化する rival であり、grammar の資格制限への相対化で
  排除する)。差は「decidable な零判定の正本と、既証明十分条件の位置
  (包含+真性)と、同じ観測言語内での分離不可能性を、同一有限モデル上の
  Lean witness つきで**一組に**固定する」点に置く。
- `claim boundary`: G-104 カードの claim boundary を継承する: 有限 Source、
  G-103 の確定定義(`Reading` / `FiniteLawFamily` / `Adequate` /
  `CoarserThan`)、well-formed な comparison data(K1 導出台つき有限
  nerve・face boundary の端点整合・退化宣言の hereditary 性・chart 台の
  π-両立)、K0 / K1 に従う law 由来係数、係数体 `ℚ` 固定。Source と
  両読みの Target の非空性は ambient に仮定する(空 regime は claim に
  含めず、`A = q.Target` scope はこの仮定の下で well-defined)。量化対象は
  **一様不変性**であり、一様量化を pointwise 化する弱化(単一 law
  family に対する定理を completion と数えること)は認めない(pointwise
  必要性の不成立は G-104 期に確定済み)。歴史記録の C\* の評価 scope は
  歴史節の記載を正とする。
  含めない: 無限 regime、
  係数の一般化、doctrine 間 comparison、hunt の bound 拡張(off-loop
  探索の再開)そのもの、**一様不変性の必要条件・iff・新しい十分条件
  (C\* 後継 certificate)の主張**(certificate 再設計と modification
  calculus は G-108 以降)、**`G_local-v1` 以外の grammar への
  不可能性・絶対的不可能性・半径 `r ≥ 2` への一般化**(`T_n` 族の
  `n > 2r+1` 論法は frontier)。
- `capability categories`: reduction、decidability、positioning、
  nonfactorization、counterexample。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に
  置き、固定 statement と completion criteria だけで完了判定する。
- `portfolio constraint`: 還元(i)だけ、decider(ii)だけ、または非分解性
  (v)だけで完了扱いしない。三本柱((i)(ii) / (iii)(iv) / (v))の全面の
  Lean artifact 接続を要求する。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、反証なら
  `target-refuted`、全完了条件と final review を満たした場合だけ
  `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各 cycle は
  proof obligation delta で評価する。
- `dullness filter`: 次を弾く。両側 H¹ 零で全単射が vacuous に成立する
  だけの fixture を (iii)(iv) の非退化根拠と数える構成、有限
  zero-result(hunt の登録 case 群)を theorem の証明根拠と称すること、
  反例・witness が型不一致だけで成立する構成、一様不変性の検査を有限個の
  law family の標本に置き換える弱化、decider を fixture 集合上の一致
  検査で代用する構成(sound / complete theorem を欠く checker)、
  `Obs_G` を登録 grammar より粗く転写して観測等値 (v)(a) を自明化する
  構成、T3 / T6 の label を assumption・axiom・登録 ledger 参照で
  済ませる構成、非分解性 (v) を条項系候補の有限列挙の全滅で代用する
  弱化、判定結果の answer-encoding を観測成分へ持ち込み (v) を無内容化
  する構成、(iii) の bridge を fixture 全数検証・型変換 wrapper で
  済ませる構成、`ConditionCAllA` を law 全量化 premise へ畳んで幾何
  決定可能性を失わせる構成。
- `frontier`: **structural certificate の再設計**(設計ノート §4 の
  機構カタログ4点組の整備 → criticality-reflection 型条項を含む後継
  certificate。G-108 候補であり本カードでは主張しない)、
  **modification calculus**(cell 追加・除去・refinement・合成の `J_A`
  への作用。第V部 repair 系譜との接続)、blocker
  `PB-R2-NONFREE-GLOBAL-FACE-CHAIN` の定理化(certificate 再設計の
  中心補題素材)、**半径 `r` 一般化**(任意固定半径の typed ball が
  一致する `T_n` 対の構成、`n > 2r+1` 局所一致論法。(v) の witness
  族化)、**observer 階層と拡張 grammar**(大域不変量1成分追加で特徴
  づけに届くかの判定。未証明 candidate であり成功見込みとして前提化
  しない)、定量版(`J_A` の次元下界・jump profile の分類)、第VIII部
  測定理論・論文Aへの「零判定の正本+Atlas の位置+観測限界」としての
  接続、reading 圏 `Read_L` 上の functor 化と zero-locus 上の局所
  定数性(local-system 化。`program context` の後続カード素材)、
  persistence module 読みの有限計算可能性。
- `spine`(仮説的道筋。壊してよい): U0 `J_A` の定義と値部分集合還元の
  Lean 化((i))→ U1 computable presentation と sound / complete
  decider((ii))→ U2 `ConditionCAllA` 定義+bridge theorem+G-104
  適用((iii))→ U3 C 非必要性 witness 7種((iv))→ U4 非分解性
  (`Obs_G` 定義 → T3 / T6 転写 → 観測等値の decidable 計算 →
  (i)(ii) 経由の label 導出 → 分離 theorem。(v))→ U5 report。

- `target theorem`: **Uniform Invariance Defect Semantics and
  Nonfactorization Theorem**(一様不変性の defect 意味論・非分解性
  定理)。G-104 カードの
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
  - **defect profile `J_A`**: 非空 `A ⊆ q.Target` に対し、A-subnerve の
    定数 `ℚ` 係数 H¹ 比較写像 `f_A` の `J_A(f) := (dim ker H¹(f_A),
    dim coker H¹(f_A))`。coker は `codomain ⧸ LinearMap.range f_A`、
    次元は `Module.finrank ℚ` で固定する。零判定 `J_A = (0, 0)` と当該
    block の比較全単射性の同値は自明扱いせず、独立 theorem
    `blockDefect_eq_zero_iff_bijective` として放電する(有限次元 bridge。
    ledger 参照)。`program context` の law 量化座標
    `J_L` とは (i) の還元で結ばれる(semantic 座標と computational
    座標)。
  - **歴史記録: 前処理と条項系 C\*(v3 で active claim から除外)**:
    続く**2項目(前処理・条項系 C\*)のみ**が、初版〜v2 の条項系候補
    (`CStarV3SupportActive`)の記録である。v3 の claim には現れず、
    両方向の exact 反例を持つ研究史・mechanism artifact として保存する
    (改訂記録は条項系 C\* 項の末尾)。その後の **`Obs_G` は active
    定義**である。後継 certificate の設計は G-108 以降。
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
    十分性方向の証拠は、登録 CERTIFIED-v3 の checkpoint 時点 population
    (1,918 case)における二方向反例ゼロだが、これは bounded 証拠で
    あり、support-active 差分つき現行変種を全登録 population で事前登録
    評価した artifact は存在しない。候補系譜には UnkilledTwin(v2)と
    いう十分性方向の反例史がある(Chain3(v1)は必要性方向 —
    uniform だが直接隣接 graph が path で条項破れ)。
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
    GLocalV1ObsValue`。`obsG` は恒久 grammar の**独立転写**であり、
    歴史記録の条項系(`CStarV3SupportActive`: CERTIFIED-v3 +
    support-active の one-pass reduction 上)とは**別型・別述語**として
    固定する。恒久 grammar の semantics は登録 contract に従う:
    full support-active scope 1回+全非空 `A`-scope(順序なし全件)を
    読み、各 scope では `GLocalV1V5Reduction`(v5 reduction の全
    irreducible terminal。removed cell・certificate argument は観測
    しない)の上で次の成分を取る — (1) retained cell を root とする
    半径1 typed incidence ball(slot / 符号、radius 外 stub は cell
    type と slot へ切り詰め)、(2) critical / guard / port / bridge /
    self-loop / FaceTwin の6 flag、(3) scoped support とその `π` 像
    (いずれも**集合値**)、(4) **map-status**(None / mapped の独立な
    二値成分)、(5) 全 reachable collapse path に現れる
    packet kind の和集合、(6) stub・neighbor descriptor・rooted ball・
    equal A-record 個数の clip2(`0 / 1 / ≥2`)histogram、(7) 条項
    conjunction vector `GLocalV1ConditionVector`(whole C0 / C5 / C6 と
    `A` ごとの C1–C4 とその AND。`CStarV3SupportActive` との一般同値は
    主張しない — T3 / T6 上の数値一致は同値の証拠ではない)、(8) `π`
    を保つ target relabel による最小化。raw cell ID・`A` label・
    fixture 名・semantic hash・2超の exact 個数・global cycle 長・
    H¹ / rank / uniformity truth は観測しない(登録済み C3 局所例外
    のみ)。**成分の正確な定義は hunt-report §`G_local-v1` と恒久
    contract を正本**とし、本要約との差異は正本が優先する(対応表は
    正本に対して固定する)。定義は登録済み恒久 contract
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
  1. **(i) defect 還元(値部分集合還元の `J`-版)**: comparison data が
     一様不変であることと、すべての非空 `A ⊆ q.Target` について
     `J_A = (0, 0)`(A-subnerve の定数 `ℚ` 係数 H¹ 比較の全単射性)で
     あることは同値である。証明は hunt-report §R0 の
     一般手証明の Lean 化であり、既存の block 直和分解
     (`lawGeneratedH1BlockEquiv`)・block 自然性
     (`generatedComparisonH1Map_block_naturality`)・descend の π-可換
     (`lawDescend_comparisonFactor`)を再利用し、残る3 conjunct
     (law-value block と A-subnerve 複体の同定、global 全単射と
     blockwise 全単射の同値、indicator law family による任意非空 `A` の
     実現と adequacy)を新規に theorem 化する。
  2. **(ii) 決定可能性**: `FiniteComparisonPresentation` 上の
     `J_A` 計算と零判定の sound / complete decider を構成する
     (`Decidable (UniformPresentation P)` instance または bool
     checker + sound / complete theorem。`toGeometry` 対応と
     `computedFactor = comparisonFactor` 一致 theorem を含む。非構成的な
     古典 instance で済ませない)。一様不変性の判定の正本を条項系では
     なく本 decider に置く。
  3. **(iii) Atlas positioning(包含)**: 幾何述語 **`ConditionCAllA`**
     — G-104 の C0・C5・C6(Lean 実体で law 非依存の条項)と、C1–C4 の
     law-value label-block 評価を**全非空 `A` の A-subnerve 評価へ
     移した**読み替え条項との conjunction — が成立するならば、
     comparison data は一様不変(`∀ 非空 A, J_A = (0, 0)`)である。
     証明は2段: **bridge theorem** `ConditionCAllA M → ∀ laws hcoarse
     hfine, M.ConditionC laws hcoarse hfine`(law-value label の block
     と値部分集合 `A`(label の値 fiber)の対応 = (i) の block ≅
     A-subnerve 同定の再利用。C1–C4 の条項ごとの transport)+ G-104
     受理済み pointwise theorem(`generatedComparisonH1Map_bijective`)
     の各 law への適用。`Condition-C locus` は `{ M | ConditionCAllA
     M }` として**幾何決定可能**に固定され、(iv) の witness により包含は
     真(`Condition-C locus ⊊ uniform locus`)。bridge は新しい axiom /
     premise ではなく discharge-required theorem である(scope 裁定
     2026-08-11 = 案b採用。law 全量化 premise 化
     (`ConditionCForAllAdequate` 型)への弱化は認めない)。
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
     theorem 水準の地図であり、(iii) の包含に真性を与え、(v) とあわせて
     「既証明の十分域は真に狭く、この観測言語では必要十分に届かない」
     構図を固定する。
  5. **(v) observation nonfactorization**: `G_local-v1` で
     表現可能ないかなる条項系も一様不変性を特徴づけない。正確には、
     witness 対 `T3`(`TERNARY-CYCLE-3`)・`T6`(`TERNARY-CYCLE-6`)を
     hunt の登録 structural input から Lean へ転写し、次の4 theorem で
     固定する: **(a) 観測等値** `obsG T3 = obsG T6`(computable
     presentation 上の決定可能計算)、**(b)** `T3` は
     `UniformPresentation`((i)(ii) 経由の有限 A-block 判定。全非空
     `A` で 1→1 / 0→0 / 1→1)、**(c)** `T6` は `UniformPresentation` でない
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
  (i) は一般の有限 Source と well-formed comparison data について
  証明する(law family と adequacy は一様不変性の内部量化であり、
  theorem の外側で固定しない)。(ii) は computable presentation 上で
  構成する。(iii) は G-104 の受理済み artifact だけを根拠とする。(v) は
  `Obs_G` の定義と witness 対の転写により固定し、分離 theorem (d) の
  量化は presentation 全体とする。witness((iv)、(v) の T3 / T6)は
  hunt artifact の固定 fixture(`results-summary.json` /
  `results-stop-b-summary.json`)の転写または新設で具体化してよい。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/UniformInvariance/` 配下。
  `ResolutionInvariance/`(G-104)・`CanonicalResolution/`(G-103)・
  `TwoPhase/`(G-102)と `Formal/AG` は参照のみ(再定義しない)。
  `research/experiments/g104-necessity-map/` は fixture 素材・転写照合先・
  戦略参照のための証拠 artifact であり、証明根拠として引用しない(engine /
  checker 実装への依存も持ち込まない)。G-107 の完了面は (i)–(v) まで。
  非分解性 (v) は登録恒久 contract の grammar **相対**であり、他の観測
  grammar への不可能性・絶対的不可能性・半径 `r ≥ 2` への一般化は主張
  しない。新しい structural certificate(C\* 後継)・modification
  calculus・hunt bound の拡張探索・論文A本文の変更は主張しない。
- `target proof artifacts`: 一様不変性の定義、A-subnerve 定数係数比較と
  `J_A` の定義、defect 還元 theorem(indicator law family の構成 def と
  adequacy theorem、block ≅ A-subnerve 同定 theorem、global ⟺ blockwise
  同値 theorem を含む)、**`FiniteComparisonPresentation`**(`DecidableEq`
  を持つ有限 target / cell・`Finset` support・実行可能な factor 計算)と
  `toGeometry` 対応・`computedFactor = comparisonFactor` 一致 theorem、
  **有限次元 defect bridge** `blockDefect_eq_zero_iff_bijective`
  (`J_A = (0, 0) ⟺ Function.Bijective f_A`。coker = quotient・
  `Module.finrank ℚ` 固定)、**零判定 decider**
  (`Decidable (UniformPresentation P)` instance
  または bool checker + sound / complete theorem。kernel / range /
  quotient rank 計算の soundness theorem を含む。非構成的な古典
  instance で済ませない)、**`ConditionCAllA` の定義**(C0 / C5 / C6 +
  C1–C4 の A-subnerve 評価。law family・H¹ を参照しない幾何述語)、
  **bridge theorem**(`ConditionCAllA M → ∀ laws hcoarse hfine,
  M.ConditionC laws hcoarse hfine`)、**Atlas positioning theorem**
  (bridge + G-104 適用による `ConditionCAllA → 一様不変`)、
  **観測写像 `Obs_G` の定義と恒久 contract 構成
  要素対応表**、T3 / T6 fixture 定義(登録 structural input との対応
  記録つき)、観測等値 theorem (v)(a)、T3 一様不変 theorem (v)(b)・
  T6 非一様 theorem (v)(c)、分離 theorem (v)(d)、現行 C 非必要性
  witness 7種、
  report `research/reports/G-107-aat-uniform-invariance-characterization.md`。
- `target proof strategy`: U0 `J_A` 定義と defect 還元(hunt-report §R0
  の conjunct 対応表に従う)→ U1 `FiniteComparisonPresentation` と
  sound / complete decider → U2 `ConditionCAllA` の定義と bridge
  theorem(C1–C4 の label-block 評価を (i) の block ≅ A-subnerve 同定で
  A-subnerve 評価へ transport、条項ごとに証明)→ G-104 pointwise
  theorem(`generatedComparisonH1Map_bijective`)の適用で Atlas
  positioning theorem を得る → U3 C
  非必要性 witness 7種 → U4 非分解性
  (`Obs_G` 定義 → T3 / T6 転写 → 観測等値の decidable 計算 →
  (i)(ii) 経由の label 導出 → 分離 theorem)→ U5 report。
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
  `Adequate`)、G-102 の `ThreeCochainComplex` / `H1` / `h1Map`、
  Atlas positioning は bridge theorem 経由で G-104 の main theorem
  (`generatedComparisonH1Map_bijective`)受理済み artifact を適用する。hunt
  artifact の固定 fixture(R1 witness 7種ほか、
  `results-summary.json` の完全データ)は witness 素材として転写して
  よい(engine 実装への依存は持ち込まない)。(v) の転写照合先は
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
  定理を completion と数えない。defect 還元、decider の sound /
  complete、bridge theorem と Atlas positioning、witness の非退化性、
  非分解性の忠実転写と分離はすべて completion までに生成・証明する。
  一様不変性・全単射性・零判定の結果を theorem argument、typeclass、
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
  - `defect 還元 (i)`: `discharge-required`。indicator law family の
    構成と adequacy、block ≅ A-subnerve 同定、global ⟺ blockwise 同値の
    3 conjunct を theorem 化する。fixture 上の数値一致で代用しない。
  - `有限次元 defect bridge`: `discharge-required`。
    `blockDefect_eq_zero_iff_bijective`(`J_A = (0, 0) ⟺` 当該 block
    比較の全単射性。coker = `codomain ⧸ LinearMap.range f_A`、次元 =
    `Module.finrank ℚ`)を独立 theorem として放電する。「有限次元だから
    自明」を放電と数えない。(ii) の decider はこの bridge を経由して
    soundness を得る。
  - `零判定 decider (ii)`: `discharge-required`。既存 API の chart 台は
    `Set`、canonical factor は `Classical.choose` 由来であり、そのままでは
    計算可能な equality / membership を供給しないため、`DecidableEq` を
    持つ有限 target / cell・`Finset` support・実行可能な factor を備えた
    **`FiniteComparisonPresentation`** を定義し、`toGeometry` 対応・
    `computedFactor = comparisonFactor` 一致 theorem・`J_A` 計算の
    sound / complete(または同値)対応 theorem を併せて放電する。
    presentation の導入だけで対応 theorem を欠く checker、非構成的な
    古典 instance(`Classical.dec` 等)は放電と数えない。uniformity
    label・条項 bit・supplied factor を presentation field として
    受け取ることも放電と数えない。
  - `ConditionCAllA (iii)`: `direction-hypothesis`(含意の仮定側の幾何
    述語)。C0・C5・C6 と C1–C4 の A-subnerve 評価だけから成り、law
    family・comparison map・H¹・rank を参照しない(C3 系局所例外は
    G-104 と同範囲)。結論相当 premise ではない理由: 有限幾何データ上の
    decidable 条項であり、(iv) の witness が示すとおり一様不変性より
    真に強い。
  - `bridge theorem (iii)`: `discharge-required`。`ConditionCAllA M →
    ∀ laws hcoarse hfine, M.ConditionC laws hcoarse hfine` を、(i) の
    block ≅ A-subnerve 同定を通した C1–C4 の条項ごとの transport で
    証明する。fixture 全数検証・law 全量化 premise 化
    (`ConditionCForAllAdequate` 型)・単なる型変換 wrapper で代用
    しない。G-104 側の定義は参照のみ(再定義しない)。
  - `歴史記録の条項系 C\*(CStarV3SupportActive)`: premise ではない。
    v3 の claim に現れず、研究史・mechanism artifact としてのみ保持
    する。(v) の観測成分は `GLocalV1ConditionVector`(恒久 grammar の
    all-terminal 条項 vector)であり、本条項系とは**別型・別述語**
    (一般同値を主張しない)。
  - `Obs_G の忠実転写 (v)`: `discharge-required`。登録恒久 contract
    (canonical SHA-256
    `5a14faf44049b8906200d5dbd052bc9fd5669ff84dfb6452e6137e98dfbd51c8`)
    の**全構成要素**(恒久 `G_LOCAL_V1_SPEC` の成分表を正本とする)と
    Lean 定義の1対1構成要素対応表を artifact に固定する。カード内の
    成分要約は概要であり、対応表の網羅性判定には使わない。
    成分の省略・追加・truncation 変更(粗視化・細密化)は放電と数えない。
    義務は定義水準+T3 / T6 上の評価であり、packet rewrite の一般論は
    含めない。
  - `T3 / T6 witness の転写と label (v)`: `discharge-required`。登録
    structural input(name-free semantic SHA)との対応を記録し、
    T3 の一様不変・T6 の非一様を **(i)(ii) 経由の Lean 内有限計算**で
    証明する。Round 15 ledger・Stop-B checker 結果の参照だけで label を
    立てることは放電と数えない。
  - `分離 theorem (v)(d)`: `discharge-required`。factorization 論法
    (観測値上の任意述語 `p` に対する反証)で証明し、条項系候補の有限
    列挙で代用しない。
  - `現行 C 非必要性 witness 7種 (iv)`: `discharge-required`。存在
    witness。(iv) の scope 規定(相対条項は同一 `A` での同時発火、全体
    条項は破れ関与データと交わる `A` での両側非零)を満たす。型不一致
    vacuity・零 H¹ だけの破れは不可。(iii) の包含真性の根拠を兼ねる。
- `target anti-weakening rule`: (i) を fixture 検証へ、一様不変性を
  有限個の law family の標本検査へ弱めない。law family を theorem 外側の
  固定 premise へ移して一様量化を pointwise 化しない。(ii) の decider を
  fixture 集合上の一致検査へ、sound / complete theorem なしの checker へ
  弱めない。(iii) の `ConditionCAllA` を law-indexed 述語・law 全量化
  premise(`ConditionCForAllAdequate` 型)・H¹ / rank 参照条項へ差し替え
  ない。bridge theorem を fixture 検証・型変換 wrapper で済ませない。
  (v) について: `Obs_G` を
  登録 grammar より粗く(成分省略・truncation 粗大化)定義して観測等値を
  自明化しない。逆に禁止情報(exact cycle 長・H¹・rank・raw ID・判定
  結果の answer-encoding 等)を成分へ追加しない。T3 / T6 の label を
  assumption・axiom・structure field 化しない。非分解性を grammar
  非相対の絶対主張へ強めない(過大主張の禁止)。歴史記録の C\*
  (hunt candidate SHA `R2-CSTAR-CERTIFIED-v3` =
  `cbb02677a055c69ecf0bb50a5de884fb55bbd4b4b59b75d256815eae69ec4daa`
  + support-active 差分)を active claim へ黙って復帰させない — 後継
  certificate は G-108 以降で新 semantic ID として事前登録する。結論相当
  データを theorem argument、typeclass、structure field、certificate
  field へ移さない。
- `target route integrity gate`: 三本柱の theorem・witness の provenance
  を law family、読みの比較射(G-103 factorization)、nerve 構成データ、
  review 済み predecessor(Atlas positioning は bridge 経由で G-104
  main theorem)、
  および hunt の登録 fixture(name-free semantic SHA)へ追跡する。
  (v) の witness provenance は登録 structural input の semantic SHA と
  恒久 contract SHA へ追跡する。恒等比較・零 H¹ だけの vacuous witness、
  proof 後の GOAL 読み替えを completion に使わない。
- `target failure policy`: fail-closed を原則とする — カードが固定した
  subclaim((iii)、(iv)、(v)(a)–(c))のいずれかが偽と確定した場合、
  まず `target-refuted` を記録する。artifact / statement の改訂はその後の
  別操作であり、記録を先送りする理由にしない。層別の扱い: (i) の破れ
  (還元の反証)は一様不変性の量化定義の欠陥として本 GOAL を停止し、
  GOAL 改訂提案を返す(優先度は最上位)。(ii) の decider の欠陥
  (unsound / incomplete)は反証ではなく実装・対応 theorem の不備として
  是正する — ただし `J_A` の定義自体の矛盾が出た場合は (i) と同格の
  GOAL 改訂事案。(iii) の反例(`ConditionCAllA` 成立かつ非一様)は
  fail-closed 原則どおりまず `target-refuted` を記録し、その後に破れの
  層を切り分ける: 反例の witnessing law について law-indexed
  `ConditionC` も成立していれば **G-104 本体の反証**として最優先で
  G-104 の review 体制へ escalate、law-indexed `ConditionC` が不成立
  なら **bridge の反例**であり (iii) の幾何評価 scope の欠陥として
  GOAL 改訂案(A-subnerve 読み替えの再設計)を返す。bridge theorem が
  反例なしに証明として閉じないだけの場合は blocker として扱う(下記の
  二 cycle 規則)。(v) は
  記録後の原因切り分けを層別に行う: 忠実転写した `obsG` の下で観測等値
  (a) が不成立、または (b)(c) の label が hunt 登録値と食い違う場合、
  対応表を監査して転写の欠陥(modeling)なら転写をやり直し、対応表
  どおりでも不一致が残る場合は登録恒久 artifact 側の欠陥として Issue を
  起こして Stop-B 証拠の再検証まで `target-blocked` を重ねる。分離 (d)
  は (a)–(c) からの論理的帰結であり独立の反例を持たない。(iv) は
  witness 構成が成功条件であり、hunt fixture の転写不一致(Lean 側判定と
  食い違う)は modeling 欠陥として witness を作り直す — ただしカードが
  固定した witness subclaim 自体が偽と確定した場合は前掲の fail-closed
  原則に従いまず記録する。ある条項について「一様不変 ⟹ 当該条項」が
  theorem として成立した場合(witness 不存在の証明)は、当該条項が実は
  必要だったという発見として、(iv) の当該項目を削除し (iii) の包含
  真性の根拠を再検討する GOAL 改訂案を返す。同じ blocker が二 cycle
  続けば `target-blocked` とし、bounded 版(fixture 集合で切った弱い
  定理)を成功と繰り上げない。claim boundary 外の機構が必要と判明した
  場合は本 GOAL を拡張せず、GOAL 改訂提案として返す。
