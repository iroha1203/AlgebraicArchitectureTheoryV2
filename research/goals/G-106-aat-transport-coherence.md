# G-106-aat-transport-coherence — 輸送整合の2-障害族

- `id`: `G-106-aat-transport-coherence`
- `status`: `active`
- `priority`: `medium`
- `research mode`: `target-theorem`
- `predecessor`: G-101(Atom 輸送の opcartesian lift 定理)の
  proved-in-research artifact(`Doct_U` / `transportAlong` / opcartesian
  普遍性。`research/lean/ResearchLean/AG/AtomFoundation/` 配下、
  unported)を土台として参照する。確定事項4点(下記)は固定済み。
- `tracking issue`: [#3998](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/3998)
  (active 昇格はユーザー裁定、成立はカード同期 PR のマージをもって)
- `source note`: [docs/note/n1001_atom_is_all_you_need_discussion.md](../../docs/note/n1001_atom_is_all_you_need_discussion.md)(§3.5、§8 候補17)
- `確定事項`: 次の4点を固定した(active 昇格はユーザー裁定済み。成立は
  カード同期 PR のマージをもって)。
  (1) **2-障害の係数系(有限 presentation 上の次数契約)**: 図式は
    **有限 presentation** とする — 0-cell = doctrine 対象、1-cell = 射、
    **2-cell = 平行な path 対の宣言関係**(底で合成が一致する二つの有限
    path)、**3-cell = 宣言 syzygy の有限族**(2-cell の貼り合わせ対。
    境界 pasting・向きは宣言データに含める入力幾何であり、theorem で
    生成しない)。菱形は単一 2-cell、三角形(合成関係)も 2-cell の
    instance であり、合成可能三つ組の結合比較は2つの 2-cell の貼り合わせ
    として表す。データの置き場:
    - **1-cell**: opcartesian lift(確定事項 (4))。path の lift は
      辺 lift の合成(opcartesian の合成は opcartesian)。
    - **2-cell**: 入力の **comparator** `u` = 宣言翻訳の fiber 同型
      (2-cell の両 path lift の間。確定事項 (4))。同じ底射の
      opcartesian lift の間には普遍性(G-101)から **canonical 一意比較
      同型** `φ` があり、**raw defect** `δ := u ∘ φ⁻¹` を 2-cell の終点
      package の fiber 内自己同型として測る。raw 2-cochain は
      **2-cell 上**に住む(次数一致。bare 菱形も単一 2-cell として raw
      defect の定義域に入るが、witness shape は確定事項 (5) に従う)。
    - **3-cell**: **cocycle 等式(syzygy 整合)は theorem ではなく
      条件である** — 局所資格(opcartesian lift・fiber 同型 comparator)
      だけからは導けない(単一 2-cell の comparator を `g ∘ φ` に取れば
      局所資格を満たしたまま境界積が `g ≠ 1` になる)。したがって
      **syzygy 整合を direction-hypothesis** として立て、cocycle 等式の
      theorem・class(coboundary 剰余の H² 読み)の語りはこの仮定下で
      のみ行う。raw defect・reselection 作用・orbit 述語は無条件に
      定義する。
    - **reselection(coboundary)**: **1-cell ごと**の fiber 自己同型割当
      (lift の再自明化)。path 評価の書き換えを通じ、δ には両 path に
      沿う transport 差として作用する(Čech 型 coboundary。共役だけで
      なく defect を実際に動かす)。**2-cell comparator の直接書き換えは
      gauge に含めない** — それを許すと任意の同型 comparator 族が
      canonical 族へ送れて障害が恒等的に自明化するためである。
    **消滅は raw 2-cochain が辺 reselection 作用の orbit で恒等 cochain に
    到達すること**として、coherent 化可能とは独立の述語で定義する —
    (iii) は定義展開ではなく、この orbit 述語と(書き換え後の族に対する)
    coherence 等式系の同時可解の同値として証明する。**(iii)(iv) は
    orbit-相対の claim** である(絶対的不可能性ではなく、宣言 comparator
    族が許容 gauge orbit 内で coherent 化可能かを問う)。
    可換化した不変量は採らない — 可換化で消える非可換情報が (c) 三者
    調停 witness の実質になりうるためである。gerbe / 一般 pseudofunctor
    coherence 理論は経由しない(mathlib の一般論は個別補題の流用に限る)。
  (2) **消滅同値の regime**: 一般 carrier `U` 上の**有限 presentation**
    (菱形・三角形とその有限貼り合わせ、宣言 syzygy 族込み)で
    「消滅 ⟺ coherent 化可能」を主張する
    (claim boundary の対象範囲と同一。carrier の有限性は要求しない —
    同値の両方向は与えられた coboundary データの書き換えで立ち、fiber の
    有限性を要しない見込みのため)。witness は `FiniteModel` へ具体化する。
    無限図式への拡張は frontier に置く。
  (3) **完了面**: 最小完了面 = (b)(c) の witness+統一機構。(a) は正例
    (canonical cleavage の整合)として完了面に含める。
  (4) **admissible 比較データ**: 各辺の lift は **opcartesian** である
    ことを定義に含めて要求する(局所資格。非 opcartesian lift による
    authored inconsistency の持ち込みを排除する)。障害の自由度は lift
    ではなく、**2-cell ごとに外部から与えられる comparator の族**(宣言
    翻訳)に置く。comparator は
    両 path lift の間の**底可換な fiber 同型**(可逆)であることを定義に
    含める — G-101 の一般 `PackageTotalHom` は可逆と限らず、自己同型群値
    の差が定義できないためである(可逆性を弱める場合は同型性を別
    theorem で導出する契約に差し替えるが、既定は同型要求)。gauge で
    動かせるのは
    **辺ごとの** fiber 自己同型割当が誘導する reselection のみで
    (確定事項 (1) の次数契約)、lift の opcartesian 性と底射影は固定
    する。canonical 比較への強制置換(witness の消去)は認めない。
    これが「局所的には正当(2-cell ごとに同型で翻訳可能)だが大域
    coherence が gauge orbit 内で回復できない場合がある」中間クラスの
    固定である。
  (5) **witness shape(閉配置)**: disk 上の単一 2-cell の defect は境界
    辺の gauge で吸収できる(この事実は (i) 系の正例側に置き、theorem と
    して固定する)。したがって (iv) の非消滅 witness は**閉じた 2-cell
    配置**で構成する — 最小形は同一 path 対上の**2枚の 2-cell**(二つの
    宣言翻訳。defect の比は辺 gauge の作用で共役でしか動かず、非自明な
    共役類が gauge 不変量になる)。(iv-c) の三者調停は3つの pairwise
    2-cell の三角貼り合わせとして自然に閉じる。単一 2-cell だけの
    「非消滅」主張は認めない。
- `research aim`: 輸送の比較射の合成が閉じない障害を 2-cocycle 型の
  不変量として立て、二つの障害現象 — (b) doctrine 圏の菱形の
  二経路輸送の食い違い、(c) 三つ以上の reading の pairwise 調停の
  非結合性(pairwise には翻訳可能なのに三者整合の共通語彙が組めない)—
  を同一機構(pseudofunctor coherence)の現れとして統一的に扱う。
  (a) 塔の cleavage の段間合成は障害現象としてではなく**正例側**で
  扱う: opcartesian 普遍性から導かれる canonical な輸送選択が単一射影
  内で coherent(擬関手的に整合)であることを証明し((i))、障害が
  立つのは選択が canonical でない・比較データが外から与えられる場合で
  あることを切り分ける(段横断の一般合成障害は claim boundary 外。
  source note 候補17 の (a) の一般形は frontier の段横断拡張に置く)。
- `core tension`: 普遍性から取った canonical cleavage は自動的に
  coherent である — したがって障害の実質は「与えられた比較射の族が
  canonical 選択と食い違う」場面にしかない。障害をどの自由度(lift の
  再選択で消せる部分)で割るかの設計を誤ると、不変量が自明(常に零)
  または無内容(何でも非零)になる。coboundary(再選択)で割った後に
  残る非自明な 2-障害の witness が実在するかが核心であり、(c) の三者
  調停 witness は pairwise 翻訳の存在と三者非整合を同時に要求する
  非自明な構成になる。
- `rival`: fibred category / pseudofunctor coherence の一般論(mathlib の
  `CategoryTheory` 系を含む)、gerbe / 非可換 H^2 の一般理論、
  dependency hell・diamond problem の folklore 的記述。差は「AAT の
  doctrine 圏と package 輸送に即した 2-障害を定義し、菱形食い違いと
  三者調停非結合の有限 witness まで Lean で固定する」点に置く。一般論の
  instantiation で済む部分は流用してよい。
- `claim boundary`: 固定した一般 carrier `U`、G-101 の `Doct_U` /
  `ExtInst_U` / package 総圏 / `transportAlong`、その上の**有限 2-complex
  図式**(0-cell = 対象、1-cell = 射、2-cell = 平行 path 対の宣言関係、
  3-cell = 宣言 syzygy の有限族。菱形・三角形はその instance)と
  admissible 比較データを対象とする。carrier を動かす主張、
  bifibration 化(cartesian 側)、base change(fiber product)、gerbe の
  一般分類、無限図式、ArchMap 調停 SKILL の実装変更は含めない。
- `capability categories`: coherence、two-obstruction、
  cocycle-invariant、counterexample、unification。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に
  置き、固定 statement と completion criteria だけで完了判定する。
- `portfolio constraint`: 正例(canonical coherence)だけ、または障害
  witness だけで完了扱いしない。正例・障害定義・witness・統一の四面の
  Lean artifact 接続を要求する。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、反証なら
  `target-refuted`、全完了条件と final review を満たした場合だけ
  `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各 cycle は
  proof obligation delta で評価する。
- `dullness filter`: 次を弾く。恒等射・単一 doctrine だけの図式での発火、
  再選択で消える障害を非自明と数えること(coboundary 剰余を取らない
  不変量)、消滅述語を coherent 化可能の言い換えとして定義し (iii) を
  定義展開で放電する構成、canonical 比較への強制置換で witness を消す
  構成、非 opcartesian lift・非可逆 comparator の持ち込みで障害を捏造
  する構成、2-cell comparator の直接書き換えを gauge に数えて障害を
  自明化する構成、2-cell(宣言関係)を持たない図式で raw defect が
  空虚に消える発火、3-cell 族が空で cocycle 等式が空虚に成立するだけの
  発火、単一 2-cell のみの非消滅主張(確定事項 (5) の閉配置要求違反)、
  比較射の族を空にして vacuous に「閉じない」とする構成、
  pairwise 翻訳が実在しない三者 witness(非結合ではなく単なる翻訳
  不能)、(v) を共通 schema への収納だけで済ませ一致 theorem を欠く
  成果、一般 pseudofunctor coherence の再証明だけで AAT 側の接続を
  欠く成果。
- `frontier`: cartesian 側 lift との相互作用の観察、段横断(塔の複数段)
  への拡張の観察、ArchMap 調停への含意(pairwise 調停の原理的限界)の
  記述、H^2 語彙との接続の観察。

- `target theorem`: **Transport Coherence Two-Obstruction Theorem**。
  G-101 の設定の上で:
  1. **(i) canonical coherence(正例)**: opcartesian 普遍性から導かれる
     canonical 輸送選択について、合成比較射
     `transportAlong (τ ∘ σ) P ≅ transportAlong τ (transportAlong σ P)`
     が構成でき、隣接合成の整合(coherence 等式)が成り立つ。あわせて、
     disk 上の単一 2-cell defect が辺 gauge で吸収できることを正例側の
     theorem として固定する(確定事項 (5)。witness shape の閉配置要求の
     根拠)。
  2. **(ii) 2-障害の定義**: 有限 presentation 上の admissible 比較データ
     (確定事項 (4))に対し、2-cell 上の raw defect(canonical 一意比較
     同型との差 `δ = u ∘ φ⁻¹`。確定事項 (1) の次数契約)・辺 reselection
     (coboundary)作用・消滅の orbit 述語(coherent 化可能と独立の
     定義)を**無条件に**定義・構成し、cocycle 等式(3-cell 上)は
     **syzygy 整合仮定付き**の theorem とする(確定事項 (1))。
  3. **(iii) 消滅と整合の同値(orbit-相対)**: 一般 carrier `U` 上の
     有限 2-complex(確定事項 (2))で、(ii) の orbit 述語による
     2-障害の消滅と、許容 gauge orbit 内での coherent な再選択の存在が
     同値である(定義展開による放電は認めない)。
  4. **(iv) 障害 witness 2種(orbit-相対・閉配置)**: (b) 菱形上の
     閉じた 2-cell 配置(最小形 = 同一 path 対上の2枚の宣言翻訳)が
     許容 gauge orbit 内で消えない食い違い(defect 比の非自明共役類)を
     持つ有限 witness、(c) pairwise 翻訳 comparator(2-cell)が実在する
     のに、許容 gauge orbit 内で三者整合(3つの 2-cell の三角貼り合わせ)
     が回復できない有限 witness。
  5. **(v) 統一**: (i)–(iv) が同一の coherence 機構の instance として
     接続されること。共通 schema への収納だけでは完了と数えず、菱形・
     三者図式それぞれの specialized な raw obstruction・class・非消滅が、
     統一定義の instance 化と**一致する theorem** を要求する。
  witness は既存 `FiniteModel` の carrier へ具体化する。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/TransportCoherence/` 配下。`Formal/AG` は
  参照のみ、G-101 artifact は research 内参照(unported のまま)。
  G-106 の完了面は (i)–(v) まで。bifibration・base change・段横断の
  一般合成は主張しない。
- `target proof artifacts`: 合成比較射の構成と coherence theorem、
  2-障害の定義と cocycle / coboundary theorem、消滅同値 theorem、
  菱形 witness、三者調停 witness、統一接続、
  report `research/reports/G-106-aat-transport-coherence.md`。
- `target proof strategy`: J0 合成比較射と canonical coherence ->
  J1 2-障害の定義と同値関係 -> J2 消滅同値 -> J3 菱形・三者 witness ->
  J4 統一接続。既存成果の利用 map:
  `research/lean/ResearchLean/AG/AtomFoundation/`(`Doct_U` 圏則、
  `transportAlong`、opcartesian 普遍性、lift 一意性 — proved-in-research、
  unported)、mathlib の pseudofunctor / cocartesian 系 API、
  `Formal/AG/Examples/FiniteModel.lean`(witness 素材)。
- `target theorem completion criteria`: 全 artifact が sorry なしで
  `ResearchLean` に受理され、axiom / placeholder audit が clean である
  こと。ledger の `discharge-required` を放電し、T3 audit を通し、
  Lean / report / tracking Issue を同期し、
  `$math-lean-review research/goals/G-106-aat-transport-coherence.md G-106-aat-transport-coherence`
  の4査読がすべて `No major findings` であること。
- `target premise discharge policy`: 入力(doctrine 図式、与えられた
  lift / 比較射の族)だけを残せる。coherence、cocycle 条件、消滅同値、
  witness の非自明性はすべて completion までに生成・証明する。整合・
  消滅相当のデータを certificate や structure field で受け取るだけでは
  放電と数えない。
- `target material premise ledger`:
  - `carrier U / FiniteModel`: `ambient-boundary`。
  - `図式 geometry(0 / 1 / 2 / 3-cell・境界 pasting・向き)`:
    `ambient-boundary`(入力幾何。3-cell = 宣言 syzygy 族を含み、
    theorem で生成しない)。
  - `Doct_U / transportAlong / opcartesian 普遍性`: `ambient-boundary`
    (G-101 の proved-in-research artifact の参照のみ。unported である
    ことを本カードは変更しない)。
  - `syzygy 整合(cocycle 条件)`: `direction-hypothesis`。cocycle 等式・
    class(H² 読み)の語りの仮定側。結論相当でない理由: 個々の 3-cell の
    境界上の局所等式であり、図式大域の消滅・coherent 化可能性を参照
    しない。
  - `admissible 比較データ`: `direction-hypothesis`(入力データだが、
    各辺 lift の opcartesian 資格と comparator の fiber 同型性という実質的
    方向仮定を含むため。定義に含め、witness で実例を与える。
    非 opcartesian lift・非可逆 comparator は入力として認めない。
    確定事項 (4))。結論相当でない理由: 資格は辺・対ごとの局所条件で
    あり、図式大域の coherence・消滅を参照しない。
  - `合成比較射と canonical coherence`: `discharge-required`。普遍性から
    導出し、coherence を field に入れない。
  - `2-障害の定義`: `discharge-required`。2-cell 上の fiber 内自己同型群値
    raw defect(canonical 一意比較同型 `φ` との差)・辺ごとの reselection
    作用・消滅の orbit 述語は無条件に(確定事項 (1) の次数契約)、
    3-cell 上の cocycle 等式は syzygy 整合仮定付きの theorem として。
    `φ` の存在・一意性は G-101 普遍性から導出する。coboundary
    剰余を定義に含め、消滅述語は coherent 化可能と独立に定義する。
  - `消滅同値`: `discharge-required`。一般 carrier 上の有限図式で主張する
    (確定事項 (2))。定義展開による放電は認めない。
  - `菱形 witness / 三者調停 witness`: `discharge-required`。再選択で
    消える障害・pairwise 翻訳不在の構成は放電と数えない。
  - `統一接続`: `discharge-required`。
- `target anti-weakening rule`: (iii) の同値を片方向(消滅 ⟸ 整合)へ
  弱めない。消滅述語を coherent 化可能の言い換えへ差し替えない(orbit
  述語として独立に定義する)。(iii)(iv) の orbit-相対 claim を絶対的
  不可能性の主張へ読み替えない(逆に、orbit-相対であることを理由に
  witness の gauge 検査を省かない)。2-障害を coboundary 剰余なしの生データへ
  弱めない(自明化・無内容化の両方を排除する)。(iv) の witness 条件
  (再選択不変の食い違い・pairwise 翻訳の実在)を落とさない。(v) を
  共通 schema への収納へ弱めない(一致 theorem を要求する)。結論相当データを theorem
  argument、typeclass、structure field、certificate field へ移さない。
  statement を claim boundary 外(bifibration・base change・段横断合成)の
  主張と読み替えない。
- `target route integrity gate`: 比較射の族・障害・witness の provenance
  を doctrine 図式の構成データ、canonical 構成、review 済みまたは
  proved-in-research の predecessor へ追跡する。比較射族が外部与件として
  明示宣言されたデータであること(opaque field 経由でないこと)と、
  各辺 lift の opcartesian 資格の放電を追跡対象に含める。恒等図式・
  空族・退化 doctrine だけの発火を completion に使わない。
- `target failure policy`: (i) の反例(canonical 選択が coherent で
  ない)は `target-refuted` とし、G-101 の輸送構成へ差し戻す重大所見と
  して報告する。(iv) は witness 構成が成功条件であり、「再選択で常に
  消える(2-障害が恒等的に自明)」と証明された場合は不変量設計の仕様
  欠陥として GOAL 改訂案を返す。同じ blocker が二 cycle 続けば
  `target-blocked`。claim boundary 外の機構が必要と判明した場合は本 GOAL
  を拡張せず、GOAL 改訂提案として返す。
