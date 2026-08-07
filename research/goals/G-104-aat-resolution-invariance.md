# G-104-aat-resolution-invariance — 診断の解像度不変性

- `id`: `G-104-aat-resolution-invariance`
- `status`: `active`
- `priority`: `high`
- `research mode`: `target-theorem`
- `tracking issue`: [#3902](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/3902)
- `source note`: [docs/note/atom_is_all_you_need_discussion.md](../../docs/note/atom_is_all_you_need_discussion.md)(§5、§8 候補4)
- `research aim`: 二つの `L`-adequate な読み `q ≤ q'`(G-103 の粗さ順序
  `CoarserThan`)に対し、law 由来の係数で計算した障害類が、読みの比較射が
  誘導する comparison map の下で canonical に同型になる条件を特定し、
  「adequate な範囲内では解像度の選択は診断を変えない」を theorem にする。
  系として過剰解像度の無益性(必要以上に細かく測っても診断は増えない)を
  導き、対として adequate でない粗化では偽の類の発生または真の類の隠蔽が
  実際に起きる有限反例を固定する。ArchSig の粒度選択が暗黙に依存している
  事実の定理化である。
- `core tension`: 直観的根拠は「係数は law が生成し、law は潰された区別を
  見ない」だが、被覆の像の振る舞い(粗化で chart / overlap がどう写るか)
  に条件が要り、その条件 C の正体こそが定理の中身である。C が自明に常時
  成立するなら定理は定義の言い換えであり、C が強すぎて実例が持てないなら
  定理は空である。C の成立正例と、C なしで同型が破れる反例の稜線が核心。
  特に coarse face の fine lift(C4)は外せない: これを欠く C は、filling
  face 付きの粗側 nerve と face-free の細側 cycle で `H^1` が一致しない
  有限反例を許す。同一粗側 edge への fine lift の一意性(C5)も外せない:
  これを欠く C は、C0–C4 が成立しても、どの細側 face にも含まれない
  parallel lift が追加の非零 `H^1` 類を残す有限反例を許す(C0–C4 は同一
  粗側 edge に写る複数 fine lift 間の cycle を制御しない)。粗側 self-loop の
  endpoint reflection(C6)も外せない: これを欠く C は、C0–C5 が成立しても、
  self-loop の一意な fine lift が同一 fiber 内の異なる chart を結び、粗側
  loop 類が細側 coboundary へ落ちて非単射になる有限反例を許す。退化宣言の
  hereditary 性も外せない: 退化 face 宣言の条件を「boundary edge がすべて
  fiber 内 edge」に緩めると、fiber 内 edge が粗側 self-loop へ非退化に
  写る場合に、その edge を boundary triple の3位置に持つ退化 face の零 pullback が
  degree-one pullback の boundary 交代和(`1 − 1 + 1`)と衝突し、生成規則の
  comparison 成分が cochain map にならない((i) の構成自体が破れる)
  有限反例を許す。さらに
  off-loop の計算探索(artifact は target proof strategy 参照)は、係数を
  宣言で自由に変えられるモデルでは、非退化正例を一つでも受理する
  incidence-only の条件が、同一 incidence 上の座標複製と support hole に
  よる2点分離により、その正例の係数変更例と区別できないことを固定した
  (条件付き no-go であり、law 由来係数への反証ではない)。
  さらに K1 の導出台の下でも、粗側 chart の値を複数の細側 chart へ分配
  すると fiber 内 edge の導出台(交わり)が空になり、nerve 全体への
  C0–C6 だけでは非同型が残る有限例がある。したがって同型の制御は係数生成
  契約 K0 / K1(座標 index の固定・cell 台の導出)と条件 C の分担であり、
  C1–C4 は係数座標ごとの台 subnerve へ相対化して課す(`H^1` と comparison
  map は座標 block へ直和分解するため、各 block の定数係数比較への還元が
  相対化の数学的根拠である)。残る稜線は、この相対化した C0–C6 が十分か、
  さらに高次の incidence coherence が要るかの判定である。
- `rival`: 抽象解釈の粒度選択(Galois 接続の合成で精度が単調に変わる
  一般論)、モデル検査の抽象化精細化(CEGAR)、Čech 理論の被覆精細化と
  Leray 型定理(古典的先例。差は adequacy を law family 相対で固定する
  点)、既存の第VIII部測定理論。差は「adequacy を law family 相対で固定し、
  障害類の canonical 同型とその破れを同一有限モデル上の Lean witness で
  固定する」点に置く。
- `claim boundary`: 有限 Source、law evaluation 族(G-103 の
  `FiniteLawFamily`)、G-103 の確定定義
  (`research/lean/ResearchLean/AG/CanonicalResolution/Reading.lean` の
  `Reading` / `Kernel` / `Factors` / `CoarserThan` / `Adequate`)による
  reading / adequacy / 粗さ順序、reading の Target に chart 台を宣言する
  有限 nerve(edge / face の台は K1 で導出)、K0 / K1 に従う law 由来係数の
  有限被覆複体を対象とする。係数体は `ℚ` に固定する(線形機構は G-102 の
  `ThreeCochainComplex` / `H1` / `h1Map` を `ℚ` で instantiate して再利用。
  他の係数体への一般化は claim に含めない)。無限
  regime、係数の一般論(semi-module 化)、doctrine 間 comparison(blame
  輸送)、doctrine / Atom carrier 機構そのもの、接地 certificate、`q_L` の
  representability は含めない。
- `capability categories`: comparison-map、invariance、
  coefficient-generation、counterexample、corollary-derivation。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に
  置き、固定 statement と completion criteria だけで完了判定する。
- `portfolio constraint`: 正例(不変性 theorem)だけ、または反例
  (inadequate 粗化の病理)だけで完了扱いしない。両面の Lean artifact
  接続を要求する。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、反証なら
  `target-refuted`、全完了条件と final review を満たした場合だけ
  `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各 cycle は
  proof obligation delta で評価する。
- `dullness filter`: 次を弾く。`q = q'`(恒等比較)だけの発火、両側の
  `H^1` が零で同型が vacuous に成立する witness、law が定数で係数が
  退化する例、粗さ順序が自明(単元 Source)な例、単一 chart の nerve で
  条件 C が空虚に成立する例、粗側 nerve が face を持たず C4 が空虚に
  成立するだけの発火、細側 nerve が退化成分として宣言された fiber 内
  edge を持たず C5 の一意性が
  細側=粗側の自明な edge 対応で成立するだけの発火、粗側 nerve が
  self-loop を持たず C6 が空虚に成立するだけの発火、全 cell が同一の
  係数座標集合を持ち座標 subnerve 相対化が空虚に全体条項へ一致するだけの
  発火、comparison map を
  同型と仮定して不変性を導く
  循環、law ラベルを貼っただけの定数係数(annotation)を law 由来係数と
  称する構成、反例が型不一致だけで成立する構成。
- `frontier`: 条件 C の必要性方向の特徴づけ(C0–C6 各条項の独立性・
  弱化可能性の、law 由来係数と K0 / K1 の下での再検討)、off-loop ハントの
  自由係数反例(座標複製・support hole)の law 実現可能性の判定(実現可能
  なら (iv) の反例素材、不能なら K0 / K1 の canonical 性の裏付け)、
  定量化(inadequate 粗化で失われる類の個数・次元の下界)、
  接地条件との交差(接地可能な解像度だけに制限した不変性)、
  資源制約下の最適解像度選択の観察、論文Aの実証節(解像度スイープ)への
  theorem 側の錨の供給。

- `target theorem`: **Diagnostic Resolution Invariance Theorem**。
  有限 Source・law family `L`(G-103 の `FiniteLawFamily`)の上で次を
  構成する。
  - **comparison data**: `L`-adequate な読みの対で `q` が `q'` より粗い
    もの(`q.CoarserThan q'`)、および粗さから誘導される一意の factor
    写像 `π : q'.Target → q.Target`(存在は G-103 の
    `factorsThrough_iff_coarserThan`、一意性は `q'` の全射性から証明
    する)。粗側・細側それぞれの Target に台を持つ有限 nerve `N`, `N'`
    (**K1(cell 台の導出)**: 宣言するのは chart への非空台割当だけとし、
    edge の台は端点 chart の台の交わり、face の台は boundary edge の台の
    交わりとして導出する。cell ごとの独立な台宣言は持たない)。nerve の
    well-formedness として、各 face の boundary triple `(e₀, e₁, e₂)` は
    ある chart `A, B, C` について `e₀ : A → B`、`e₁ : A → C`、`e₂ : B → C`
    の端点整合を満たすことを要求する(`d₁ ∘ d₀ = 0` はこの整合から
    theorem として導き、structure field や premise で受けない)。さらに
    nerve 射 `φ : N' → N`。nerve 射は chart / edge / face の対応で
    endpoint / boundary と可換であることを要求する。ただし両端点が同一
    fiber に落ちる細側 edge(fiber 内 edge)は、粗側対応物を持たない
    退化成分として宣言してよい。細側 face を退化成分として宣言できる
    のは、その3本の boundary edge がすべて退化成分として宣言されている
    場合に限る(**退化宣言の hereditary 性**。boundary edge が fiber 内
    edge であっても、粗側 edge へ写ると宣言されているなら、その edge を
    boundary に持つ face は退化成分にできない)。cochain map の構成では
    退化成分上の pullback を零とする(退化 face の boundary pullback は
    hereditary 性によりすべて零であり、零 pullback が degree-one 側の
    boundary 交代和と衝突しない)。chart 台は `π` と両立する(細側 chart の台の
    `π`-像が対応する粗側 chart の台に含まれる)ことを要求する。
  - **law 由来係数(生成契約 K0)**: 係数体は `ℚ` に固定する。各 reading の
    係数複体は、その reading を通して descend した law evaluation(存在・
    一意は G-103 の `factors_iff_kernel`)から、次の生成規則 K0 で
    構成する。
    - **座標 index**: 各 cell の係数座標は対 `(law, 値)` とする。`値` は
      descend した当該 law evaluation がその cell の台(K1 の導出台)上に
      取る相異なる値である。値の Target 上の出現回数(occurrence)や台の
      要素数を index にしない(多重度は常に値ごとに1)。
    - **各次数の空間**: `C⁰` は {(chart, law, 値)} 上、`C¹` は
      {(edge, law, 値)} 上、`C²` は {(face, law, 値)} 上の `ℚ`-値関数空間と
      する。
    - **differential の生成**: `d₀` の `(edge, law, 値)` 成分は両端点 chart の
      同一 `(law, 値)` 成分の差(right − left)とする(edge の値集合は K1 に
      より両端点の値集合に含まれるため、同一 label の恒等対応で
      well-defined)。`d₁` の `(face, law, 値)` 成分は boundary triple の
      同一 `(law, 値)` 成分の交代和(`e₀ − e₁ + e₂`)とする。同一 label は
      恒等、label 不在は零であり、これ以外の座標写像は生成しない。
      `d₁ ∘ d₀ = 0` は face の端点整合から label ごとの計算で theorem と
      して導く。
    - **comparison map の生成**: 比較の係数写像は宣言せず、`(law, 値)` 上の
      恒等対応として descend の `π`-可換
      (`ResolutionInvariance/ComparisonData.lean` の
      `lawDescend_comparisonFactor`)から生成する(細側 cell が当該座標を
      持たない成分と退化成分上は零写像)。cochain map
      (`ThreeCochainComplex.Hom`)の可換性と、`H^1` の `(law, 値)` ごとの
      block 直和分解は、この生成規則から theorem として導き、theorem
      argument や structure field で受けない。
    宣言による座標の追加・複製・省略は認めない。複体・`H^1`・誘導写像は
    G-102 の `ThreeCochainComplex` / `H1` / `h1Map`
    (`research/lean/ResearchLean/AG/TwoPhase/CoefficientComplex.lean`、
    `CohomologyComparison.lean`)を `ℚ` で instantiate して再利用する。
    law ラベルだけの定数係数 annotation は law 由来係数と認めない
    (G-102 E1 と同水準の生成的構成)。
  - **条件 C(被覆像の適合条件。incidence / support レベルの候補式として
    固定)**: 各係数座標 `(law, 値)` に対し、その座標を係数に持つ cell
    (descend した当該 law evaluation が K1 の導出台上にその値を取る cell)が
    成す部分 nerve を**座標 subnerve** と呼ぶ。座標 subnerve は K0 / K1 の
    導出データだけから定まり、粗側・細側の両方で取る。C0・C5・C6 は nerve
    全体で課し(C5・C6 の subnerve への制限は全体での成立から従う)、
    C1–C4 は各座標 subnerve ごとに課す(subnerve 上の fiber グラフ =
    粗側 chart `c` に対し、頂点 = `φ` で `c` に写る subnerve 内の細側
    chart、辺 = 両端点がその fiber に属する subnerve 内の細側 edge):
    - **C0(被覆像の合致)**: 各粗側 chart の台は、その fiber に属する
      細側 chart 台の `π`-像の合併に等しい。
    - **C1**: 各座標 subnerve で、subnerve に属する各粗側 chart の
      fiber グラフは非空かつ連結である。
    - **C2**: 各座標 subnerve で、subnerve に属する各粗側 edge は
      subnerve 内に `φ`-lift を持つ。
    - **C3(局所 fiber acyclicity。明示の例外条項)**: 各座標 subnerve で、
      fiber グラフ上の任意の有理 1-cycle(`ℚ`-係数)は、boundary edge が
      すべて fiber 内にある subnerve 内の細側 face の boundary の
      `ℚ`-線形結合で張られる。これは fiber の `ℚ`-係数 1-homology 消滅と
      同値な局所条件であり、下記の禁止規則の明示の例外として許す。
    - **C4(coarse-face lift)**: 各座標 subnerve で、subnerve に属する
      各粗側 face は `φ` の face 対応で写る subnerve 内の細側 face を
      少なくとも一つ持つ。nerve 射の boundary 可換性により、その細側
      face の3本の boundary edge は対応する粗側 boundary edge へ写る。
    - **C5(unique coarse-edge lift)**: 各粗側 edge の `φ`-fiber は高々
      一元である(C2 と合わせ、係数座標を持つ各粗側 edge へ `φ` の edge
      対応で写る細側 edge はちょうど一つ)。退化成分として宣言された
      edge は粗側対応物を持たないためこの条項の対象外であり、fiber 内の
      多重性は制限しない(fiber 内 edge であっても粗側 edge へ写ると
      宣言された edge は `φ`-fiber に数える)。
    - **C6(self-loop endpoint reflection)**: 両端点が同一の粗側 chart に
      落ちる粗側 edge(self-loop)へ `φ` の edge 対応で写る各細側 edge は、
      それ自身 self-loop である(両端点が同一の細側 chart に落ちる)。
      C5 と独立に定式化する(C5 の一意 lift に条件を課す形にしない)。
    C には、comparison map・粗側複体・両側の global `H^1` に関する同型・
    消滅と同値または片方向に近い条項を含めない(incidence / support
    レベルの条項に限る。座標 subnerve は K0 / K1 の導出データであり、
    その上の incidence 条項はこの制限に適合する)。**明示の例外は C3 の
    局所 fiber acyclicity のみ**とする: C3 は個々の chart fiber の内部
    データ(fiber 内 edge / face)だけに依存し、comparison map・粗側複体・
    両側の `H^1` を参照しない、Čech 理論の Leray 型局所非輪状仮定に相当
    する局所条件である。global comparison の同型やどちらか一側の `H^1`
    消滅を条項化することは引き続き禁止する。
    係数の restriction と比較の係数写像は座標ごとの零 / 恒等写像なので、
    `H^1` と comparison map は座標 block へ直和分解し、各 block は当該
    座標 subnerve 上の定数係数(1次元)比較に還元される。C1–C4 の
    相対化は、この block 分解の各成分に対する条項である。
  この設定で次が成り立つ。
  1. **(i) comparison map**: `φ` と係数 descend の両立から cochain map
     (`ThreeCochainComplex.Hom`)を構成し、`h1Map` により粗側 `H^1` から
     細側 `H^1` への canonical 写像を誘導する。写像は比較データから構成
     し、同型性を field や premise で受けない。
  2. **(ii) 不変性**: 条件 C(C0–C6)の下で、(i) の comparison map は `H^1`
     障害類の同型を誘導する。
  3. **(iii) 系(過剰解像度の無益性)**: adequate な範囲内の精細化は
     診断(障害類の集合)を増やさない。(ii) の同型から系として導出する。
  4. **(iv) 反例対(存在 witness)**: adequate でない粗化 `q` の診断は、
     `q` を通して descend 可能な law 部分族(G-103 の `Factors` が成り立つ
     law の部分集合。選択の余地のない canonical な部分族)による係数複体の
     `H^1` として計算する。この固定の下で: (a) 粗側に発生するが細側に
     対応物のない非零類(偽の類の発生)の有限反例。(b) 細側の非零類が
     粗側で見えなくなる(真の類の隠蔽)有限反例。(c) adequate な対で
     条件 C が破れ、(ii) の同型が実際に破れる有限反例。3種とも存在
     witness に留め、定量化は frontier に置く。
  5. **(v) 発火 witness**: (ii) の成立正例において、非恒等な粗化
     (`π` が非単射)、非零 `H^1`(両側)、係数が実際に law evaluation の
     descend から生成されること、ある粗側 chart の fiber が2元以上を持ち
     C1 が非空虚に働くこと、粗側 nerve が少なくとも一つ face を持ち
     C4 が非空虚に働くこと、細側 nerve が少なくとも一つ退化成分として
     宣言された fiber 内 edge を持ち C5 の一意性が細側=粗側の自明な
     edge 対応で成立するのでないこと、粗側 nerve が少なくとも一つ self-loop を持ち
     C6 が非空虚に働くこと、少なくとも一つの係数座標の subnerve が nerve
     全体と一致しない(値の分配が実際に起き、C1–C4 の座標 subnerve
     相対化が空虚に全体条項へ一致するのでない)こと、を theorem として
     確認する。
  (i)(ii)(iii) は一般の有限 Source / `L` / adequate pair / comparison
  data について証明する。witness((iv)(v))は G-103 の witness 素材
  (six-source law family)の再利用または新設の有限 Source / law family /
  nerve で具体化してよい(doctrine / Atom carrier への接続は要求しない —
  係数が law 由来であり、本カードの claim boundary が doctrine 機構を
  含まないため)。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/ResolutionInvariance/` 配下。`Formal/AG`
  と review 済み predecessor(G-102 TwoPhase / G-103 CanonicalResolution)
  は参照のみ。G-104 の完了面は (i)–(v) まで。
- `target proof artifacts`: reading の Target に台を持つ nerve の定義
  (K1 の台導出・face boundary の端点整合を含む)と `d₁d₀ = 0` の導出
  theorem、nerve 射(incidence 可換+hereditary な退化成分宣言)と
  `π`-両立性の定義、
  law 由来係数の生成 def(K0: `(law, 値)` index・`ℚ`-値関数空間・
  零 / 恒等 restriction・導出 differential・比較の座標対応の生成)、
  descend 可換補題(粗側 descend と細側 descend の `π`-両立)、
  comparison cochain map の構成 def、`H^1` の座標 block 直和分解
  theorem、座標 subnerve の定義、条件 C
  (C0–C6、C1–C4 は座標 subnerve 相対化)の定義、
  不変性 theorem、系 theorem、descend 可能部分族による inadequate 側診断の
  定義、反例3種 witness、発火 witness、
  report `research/reports/G-104-aat-resolution-invariance.md`。
- `target proof strategy`: H0 comparison data(nerve / nerve 射 / K1 の
  台導出)と law 由来係数の生成(K0)、descend 可換補題 -> H1 条件 C
  (C0–C6、C1–C4 は座標 subnerve 相対化)の定義と不変性(`H^1` の座標
  block 直和分解で各 block を座標 subnerve 上の定数係数比較へ還元し、
  fiber subcomplex を潰した relative complex 経由の手証明スケッチ =
  off-loop artifact
  `research/experiments/g104-condition-hunt/hunt-report.md` §4 を block
  ごとに参考にしてよい。off-loop artifact は証明根拠ではない。さらに高次の
  incidence coherence の要否をここで検査し、不足なら failure policy で
  返す)->
  H2 系の導出 -> H3 反例3種 -> H4 発火 witness。既存成果の
  利用 map: G-103 `CanonicalResolution/Reading.lean`(`Reading` /
  `FiniteLawFamily` / `Adequate` / `CoarserThan` / `factors_iff_kernel` /
  `factorsThrough_iff_coarserThan`)、G-103 witness 素材(six-source law
  family。再利用は任意)、G-102 `TwoPhase/CoefficientComplex.lean` +
  `CohomologyComparison.lean`(`ThreeCochainComplex` / `Hom` / `H1` /
  `h1Map`)、
  `ResolutionInvariance/ComparisonData.lean`(canonical comparison
  factor / law descend とその可換・一意性。review 済み、再定義しない)、
  `ResolutionInvariance/LawGeneratedComplex.lean`(K0 / K1 の生成複体:
  `TargetSupportedNerve`・K1 導出台・`(cell, law, 値)` 座標・`ℚ` 上の
  generated differential・`d₁d₀ = 0`・`ThreeCochainComplex` 構成。
  review 済み、再定義しない)、
  `ResolutionInvariance/FaceLiftObstruction.lean`(C4 が破れる有限
  witness。(iv)(c) の素材として転用可)、
  `ResolutionInvariance/EdgeFiberObstruction.lean`(C5 が破れる有限
  witness。(iv)(c) の素材として転用可)、
  `ResolutionInvariance/LoopLiftObstruction.lean`(C6 が破れる有限
  witness。(iv)(c) の素材として転用可)、
  `ResolutionInvariance/DegenerateFaceComm1Obstruction.lean`(hereditary
  性を欠く退化 face 宣言規則の下で生成 comparison 成分が cochain map に
  ならない有限 witness。本カードの退化宣言規則の根拠であり、改訂後の
  well-formed な comparison data ではないため (iv) の素材ではない)。
  固定 statement と完了条件は
  本カードのみを正本とする。
- `target theorem completion criteria`: 全 artifact が sorry なしで
  `ResearchLean` に受理され、axiom / placeholder audit が clean である
  こと。ledger の `discharge-required` を放電し、T3 audit で provenance、
  proof-use、structure-field escape、route integrity を監査すること。
  Lean / report / tracking Issue を同期し、final review packet を作り、
  `$math-lean-review research/goals/G-104-aat-resolution-invariance.md G-104-aat-resolution-invariance`
  の4査読がすべて `No major findings` であること。
- `target premise discharge policy`: 入力(有限 Source、law evaluation 族、
  adequate pair、nerve / nerve 射の構成データ)だけを残せる。comparison
  map の well-definedness、係数生成の descend 由来性、条件 C の成立正例、
  不変性、反例はすべて completion までに生成・証明する。同型相当のデータを
  certificate や structure field で受け取るだけでは放電と数えない。
- `target material premise ledger`:
  - `有限 Source / law family`: `ambient-boundary`。(i)–(iii) は任意の
    有限 Source と `FiniteLawFamily`、witness は G-103 素材の再利用または
    新設で具体化する。
  - `reading / adequacy / 粗さ順序`: `ambient-boundary`。G-103 の完了
    artifact(`CanonicalResolution/Reading.lean`)の参照のみ。再定義
    しない。
  - `係数複体の線形機構(ThreeCochainComplex / H1 / h1Map)`:
    `ambient-boundary`。G-102 の review 済み artifact の参照のみ。
  - `nerve / nerve 射 / 台両立`: `ambient-boundary`(入力幾何)。宣言できる
    のは chart 台までであり、edge / face の台は K1 で導出する(cell ごとの
    独立な台宣言は入力幾何に含めない)。well-formedness(face boundary の
    端点整合・退化宣言の hereditary 性・`π`-両立)は定義に含め、witness で
    実例を与える。
    `d₁ ∘ d₀ = 0` は端点整合から theorem として導く(structure field で
    受けた場合は未放電仮定として数える)。
  - `law 由来係数の生成`: `discharge-required`。係数複体(`ℚ` 上の
    `(cell, law, 値)` 関数空間・零 / 恒等 restriction・導出 differential・
    `d₁d₀ = 0`)と comparison cochain map・`H^1` の block 直和分解を、
    K0 / K1 の生成規則から構成・証明する。descend の存在・一意を G-103
    factorization へ、比較の座標対応を `lawDescend_comparisonFactor` へ
    追跡する。law ラベルだけの定数係数 annotation、宣言による座標の追加・
    複製・省略、生成規則の theorem argument / structure field 化は放電と
    数えない。
  - `descend 可換補題`: `discharge-required`。粗側 descend =
    細側 descend ∘ (`π`-対応)を theorem で証明する。
  - `comparison map`: `discharge-required`。比較データから構成し、同型性を
    field に入れない。
  - `条件 C(C0–C6、座標 subnerve 相対化込み)`: `direction-hypothesis`。
    (ii) の含意の仮定側。incidence / support レベルの条項に固定し、
    global comparison の同型相当の条項を含めない。C3(局所 fiber
    acyclicity、`ℚ` 係数)だけを明示の例外として含む。結論相当でない
    理由: C3 は個々の chart fiber の内部データだけに依存する局所条件で
    あり、comparison map・粗側複体・両側の global `H^1` を参照しない
    (Leray 型局所非輪状仮定に相当)。
  - `条件 C の非退化成立 witness`: `discharge-required`。C を満たし (v) の
    発火条件をすべて伴う正例を構成する。
  - `不変性 theorem`: `discharge-required`。C から (i) の canonical map の
    同型を導く theorem を証明し、C の破れ反例((iv)(c))とセットで
    要求する。
  - `inadequate 側診断の固定`: `discharge-required`。descend 可能 law
    部分族(`Factors` 判定)による係数複体として定義し、選択依存の
    構成を持ち込まない。
  - `反例3種`: `discharge-required`。存在 witness。型不一致 vacuity は
    不可。
  - `発火 witness`: `discharge-required`。route integrity audit で使う。
- `target anti-weakening rule`: 不変性を「ある同型が存在する」へ弱めない
  (comparison map が誘導する canonical 射について主張する)。条件 C に、
  comparison map・粗側複体・両側の global `H^1` に関する同型・消滅と同値
  または片方向に近い条項を移さない(incidence / support レベルの条項に
  限る。座標 subnerve への相対化は K0 / K1 の導出データ上の incidence
  条項であり可。明示の例外は C3 の局所 fiber acyclicity のみで、条件C節と
  ledger に固定した理由の範囲を超えて拡張しない)。
  adequate の定義(G-103 の `Adequate`)を反例が立つように事後調整
  しない。係数生成を law ラベル annotation へ退化させない。係数生成契約
  K0 / K1 を premise 化しない(座標対応の全単射性や台の一致を仮定・
  certificate で受けず、生成規則から theorem として導く)。結論相当
  データを theorem argument、typeclass、structure field、certificate
  field へ移さない。statement を claim boundary 外(無限化・doctrine 間
  comparison・係数一般論)の主張と読み替えない。
- `target route integrity gate`: comparison map・条件 C・係数生成・反例の
  provenance を law evaluation 族、読みの比較射(G-103 factorization)、
  nerve 構成データ、review 済み predecessor へ追跡する。恒等比較・
  零 `H^1`・定数 law・単一 chart nerve だけの発火、proof 後の GOAL
  読み替えを completion に使わない。
- `target failure policy`: (ii) の反例(C0–C6 と K0 / K1 の下で同型が
  破れる)は `target-refuted` とし、C の改訂案(同じ incidence レベルの
  条項)、comparison map 構成の改訂案、または係数生成契約(K0 / K1)の
  改訂案を返す。cohomological 条項への差し替えは改訂案として認めない。
  (v) の C6 非空虚発火または座標 subnerve 相対化の非空虚発火(値分配)が
  他の発火条件と同一 witness で構成不能と判明した場合は、当該項目を
  別 witness へ分離する GOAL 改訂案を返す。(iv) は反例構成が成功条件であり、「adequate で
  ない粗化でも診断が常に保たれる」と証明された場合は adequacy 定義の
  仕様欠陥として GOAL 改訂案を返す。同じ blocker が二 cycle 続けば
  `target-blocked`。claim boundary 外の機構が必要と判明した場合は本 GOAL
  を拡張せず、GOAL 改訂提案として返す。
