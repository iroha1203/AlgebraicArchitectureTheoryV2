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
  reading / adequacy / 粗さ順序、reading の Target に台を持つ宣言された
  有限 nerve、law 由来係数の有限被覆複体(線形機構は G-102 の
  `ThreeCochainComplex` / `H1` / `h1Map` を再利用)を対象とする。無限
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
  条件 C が空虚に成立する例、comparison map を同型と仮定して不変性を導く
  循環、law ラベルを貼っただけの定数係数(annotation)を law 由来係数と
  称する構成、反例が型不一致だけで成立する構成。
- `frontier`: 定量化(inadequate 粗化で失われる類の個数・次元の下界)、
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
    する)。粗側・細側それぞれの Target に台(chart への非空台割当。
    edge の台は端点 chart の台の交わりに、face の台は boundary edge の
    台の交わりに含まれる)を持つ宣言された有限 nerve `N`, `N'` と、
    nerve 射 `φ : N' → N`。nerve 射は chart / edge / face の対応で
    endpoint / boundary と可換であることを要求する。ただし両端点が同一
    fiber に落ちる細側 edge(fiber 内 edge)と、boundary edge がすべて
    fiber 内 edge である細側 face は、粗側対応物を持たない
    退化成分として宣言してよい(cochain map の構成では退化成分上の
    pullback を零とする)。chart 台は `π` と両立する(細側 chart の台の
    `π`-像が対応する粗側 chart の台に含まれる)ことを要求する。
  - **law 由来係数**: 各 reading の係数複体は、その reading を通して
    descend した law evaluation(存在・一意は G-103 の
    `factors_iff_kernel`)が chart 台上に取る値から生成した座標 basis で
    張る。複体・`H^1`・誘導写像は G-102 の `ThreeCochainComplex` /
    `H1` / `h1Map`
    (`research/lean/ResearchLean/AG/TwoPhase/CoefficientComplex.lean`、
    `CohomologyComparison.lean`)を再利用する。law ラベルだけの定数係数
    annotation は law 由来係数と認めない(G-102 E1 と同水準の生成的
    構成)。
  - **条件 C(被覆像の適合条件。incidence レベルの候補式として固定)**:
    `φ` の fiber グラフ(粗側 chart `c` に対し、頂点 = `φ` で `c` に写る
    細側 chart、辺 = 両端点がその fiber に属する細側 edge)について:
    - **C0(被覆像の合致)**: 各粗側 chart の台は、その fiber に属する
      細側 chart 台の `π`-像の合併に等しい。
    - **C1**: 各粗側 chart の fiber グラフは非空かつ連結である。
    - **C2**: 各粗側 edge の `φ`-fiber は非空である。
    - **C3**: fiber グラフ内の辺の閉路は、boundary edge がすべて fiber
      内にある細側 face で張られる。
    C には cohomology・同型・消滅と同値または片方向に近い条項を含めない
    (incidence / support レベルの条項に限る)。
  この設定で次が成り立つ。
  1. **(i) comparison map**: `φ` と係数 descend の両立から cochain map
     (`ThreeCochainComplex.Hom`)を構成し、`h1Map` により粗側 `H^1` から
     細側 `H^1` への canonical 写像を誘導する。写像は比較データから構成
     し、同型性を field や premise で受けない。
  2. **(ii) 不変性**: 条件 C の下で、(i) の comparison map は `H^1`
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
     C1 が非空虚に働くこと、を theorem として確認する。
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
- `target proof artifacts`: reading の Target に台を持つ nerve の定義、
  nerve 射(incidence 可換+退化成分宣言)と `π`-両立性の定義、law 由来
  係数の生成 def、descend 可換補題(粗側 descend と細側 descend の
  `π`-両立)、comparison cochain map の構成 def、条件 C(C0–C3)の定義、
  不変性 theorem、系 theorem、descend 可能部分族による inadequate 側診断の
  定義、反例3種 witness、発火 witness、
  report `research/reports/G-104-aat-resolution-invariance.md`。
- `target proof strategy`: H0 comparison data(nerve / nerve 射 / 台
  両立)と law 由来係数の生成、descend 可換補題 -> H1 条件 C(C0–C3)の
  定義と不変性 -> H2 系の導出 -> H3 反例3種 -> H4 発火 witness。既存成果の
  利用 map: G-103 `CanonicalResolution/Reading.lean`(`Reading` /
  `FiniteLawFamily` / `Adequate` / `CoarserThan` / `factors_iff_kernel` /
  `factorsThrough_iff_coarserThan`)、G-103 witness 素材(six-source law
  family。再利用は任意)、G-102 `TwoPhase/CoefficientComplex.lean` +
  `CohomologyComparison.lean`(`ThreeCochainComplex` / `Hom` / `H1` /
  `h1Map`)。固定 statement と完了条件は本カードのみを正本とする。
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
  - `nerve / nerve 射 / 台両立`: `ambient-boundary`(入力幾何)。ただし
    well-formedness(台の交わり条件・`π`-両立)は定義に含め、witness で
    実例を与える。
  - `law 由来係数の生成`: `discharge-required`。座標 basis を descend
    した law evaluation の値から生成し、descend の存在・一意を G-103
    factorization へ追跡する。law ラベルだけの定数係数 annotation は放電と
    数えない。
  - `descend 可換補題`: `discharge-required`。粗側 descend =
    細側 descend ∘ (`π`-対応)を theorem で証明する。
  - `comparison map`: `discharge-required`。比較データから構成し、同型性を
    field に入れない。
  - `条件 C と不変性`: `discharge-required`。C は C0–C3(incidence
    レベル)で固定し、同型相当の条項を含めない。C の成立正例と破れ反例
    ((iv)(c))をセットで要求する。
  - `inadequate 側診断の固定`: `discharge-required`。descend 可能 law
    部分族(`Factors` 判定)による係数複体として定義し、選択依存の
    構成を持ち込まない。
  - `反例3種`: `discharge-required`。存在 witness。型不一致 vacuity は
    不可。
  - `発火 witness`: `discharge-required`。route integrity audit で使う。
- `target anti-weakening rule`: 不変性を「ある同型が存在する」へ弱めない
  (comparison map が誘導する canonical 射について主張する)。条件 C に
  同型・消滅・cohomology と同値または片方向に近い条項を移さない(fiber の
  cohomological 条件への置き換えも不可。incidence レベルの条項に限る)。
  adequate の定義(G-103 の `Adequate`)を反例が立つように事後調整
  しない。係数生成を law ラベル annotation へ退化させない。結論相当
  データを theorem argument、typeclass、structure field、certificate
  field へ移さない。statement を claim boundary 外(無限化・doctrine 間
  comparison・係数一般論)の主張と読み替えない。
- `target route integrity gate`: comparison map・条件 C・係数生成・反例の
  provenance を law evaluation 族、読みの比較射(G-103 factorization)、
  nerve 構成データ、review 済み predecessor へ追跡する。恒等比較・
  零 `H^1`・定数 law・単一 chart nerve だけの発火、proof 後の GOAL
  読み替えを completion に使わない。
- `target failure policy`: (ii) の反例(C0–C3 の下で同型が破れる)は
  `target-refuted` とし、C の改訂案(同じ incidence レベルの条項)または
  comparison map 構成の改訂案を返す。cohomological 条項への差し替えは
  改訂案として認めない。(iv) は反例構成が成功条件であり、「adequate で
  ない粗化でも診断が常に保たれる」と証明された場合は adequacy 定義の
  仕様欠陥として GOAL 改訂案を返す。同じ blocker が二 cycle 続けば
  `target-blocked`。claim boundary 外の機構が必要と判明した場合は本 GOAL
  を拡張せず、GOAL 改訂提案として返す。
