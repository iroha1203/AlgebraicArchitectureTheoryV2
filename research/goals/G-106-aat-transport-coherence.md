# G-106-aat-transport-coherence — 輸送整合の2-障害族

- `id`: `G-106-aat-transport-coherence`
- `status`: `draft`
- `priority`: `medium`
- `research mode`: `target-theorem`
- `predecessor`: G-101(Atom 輸送の opcartesian lift 定理)の
  proved-in-research artifact(`Doct_U` / `transportAlong` / opcartesian
  普遍性。`research/lean/ResearchLean/AG/AtomFoundation/` 配下、
  unported)を土台として参照する。G-102 系の消化状況を見て、人間の
  判断で active へ昇格する。
- `tracking issue`: 未起票(active 昇格時に起票する)
- `source note`: [docs/note/atom_is_all_you_need_discussion.md](../../docs/note/atom_is_all_you_need_discussion.md)(§3.5、§8 候補17)
- `昇格前確定事項(スケルトン注記)`: 本カードは骨格 draft である。
  次の3点は昇格前に固定する。(1) 2-障害の係数の正確な型(fiber 内
  自己同型群に値を取る非可換 2-cocycle か、可換化した不変量か)。
  (2) 「消滅 ⟺ coherent 化可能」の同値をどの有限 regime で主張するか。
  (3) 三実現 (a)(b)(c) のうち完了面に含める範囲 — 最小完了面を
  (b)(c) の witness と統一機構に置き、(a) は正例(canonical cleavage の
  整合)として扱う案を既定とする。
- `research aim`: 輸送の比較射の合成が閉じない障害を 2-cocycle 型の
  不変量として立て、三つの現象 — (a) 塔の cleavage の段間合成(段ごとに
  lift が在っても end-to-end で失敗しうる)、(b) doctrine 圏の菱形の
  二経路輸送の食い違い、(c) 三つ以上の reading の pairwise 調停の
  非結合性(pairwise には翻訳可能なのに三者整合の共通語彙が組めない)—
  を同一機構(pseudofunctor coherence)の現れとして統一的に扱う。
  正例側では、opcartesian 普遍性から導かれる canonical な輸送選択が
  coherent(擬関手的に整合)であることを証明し、障害が立つのは選択が
  canonical でない・比較データが外から与えられる場合であることを
  切り分ける。
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
  `ExtInst_U` / package 総圏 / `transportAlong`、その上の比較射の族と
  有限図式(菱形・三角形)を対象とする。carrier を動かす主張、
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
  不変量)、比較射の族を空にして vacuous に「閉じない」とする構成、
  pairwise 翻訳が実在しない三者 witness(非結合ではなく単なる翻訳
  不能)、一般 pseudofunctor coherence の再証明だけで AAT 側の接続を
  欠く成果。
- `frontier`: cartesian 側 lift との相互作用の観察、段横断(塔の複数段)
  への拡張の観察、ArchMap 調停への含意(pairwise 調停の原理的限界)の
  記述、H^2 語彙との接続の観察。

- `target theorem`: **Transport Coherence Two-Obstruction Theorem**
  (骨格)。G-101 の設定の上で:
  1. **(i) canonical coherence(正例)**: opcartesian 普遍性から導かれる
     canonical 輸送選択について、合成比較射
     `transportAlong (τ ∘ σ) P ≅ transportAlong τ (transportAlong σ P)`
     が構成でき、隣接合成の整合(coherence 等式)が成り立つ。
  2. **(ii) 2-障害の定義**: 有限図式上の与えられた lift / 比較射の族に
     対し、合成の閉じなさを測る 2-cocycle 型不変量を定義し、cocycle
     条件と、lift 再選択(coboundary)による同値を証明する。
  3. **(iii) 消滅と整合の同値**: 有限 regime(範囲は昇格前確定事項 (2))
     で、2-障害の消滅と coherent な再選択の存在が同値である。
  4. **(iv) 障害 witness 2種**: (b) 菱形の二経路輸送が再選択で消えない
     食い違いを持つ有限 witness、(c) pairwise 翻訳射が実在するのに
     三者整合が不可能な有限 witness。
  5. **(v) 統一**: (i)–(iv) が同一の coherence 機構の instance として
     接続されること(菱形・三者図式が同じ 2-障害定義で読めること)。
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
  (詳細分割は昇格時に確定する。)
- `target proof strategy`(骨格): J0 合成比較射と canonical coherence ->
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
- `target material premise ledger`(骨格。昇格時に精密化する):
  - `carrier U / FiniteModel`: `ambient-boundary`。
  - `Doct_U / transportAlong / opcartesian 普遍性`: `ambient-boundary`
    (G-101 の proved-in-research artifact の参照のみ。unported である
    ことを本カードは変更しない)。
  - `合成比較射と canonical coherence`: `discharge-required`。普遍性から
    導出し、coherence を field に入れない。
  - `2-障害の定義`: `discharge-required`。昇格前確定事項 (1)。coboundary
    剰余を定義に含める。
  - `消滅同値`: `discharge-required`。昇格前確定事項 (2)。
  - `菱形 witness / 三者調停 witness`: `discharge-required`。再選択で
    消える障害・pairwise 翻訳不在の構成は放電と数えない。
  - `統一接続`: `discharge-required`。
- `target anti-weakening rule`: (iii) の同値を片方向(消滅 ⟸ 整合)へ
  弱めない。2-障害を coboundary 剰余なしの生データへ弱めない(自明化・
  無内容化の両方を排除する)。(iv) の witness 条件(再選択不変の
  食い違い・pairwise 翻訳の実在)を落とさない。結論相当データを theorem
  argument、typeclass、structure field、certificate field へ移さない。
  statement を claim boundary 外(bifibration・base change・段横断合成)の
  主張と読み替えない。
- `target route integrity gate`: 比較射の族・障害・witness の provenance
  を doctrine 図式の構成データ、canonical 構成、review 済みまたは
  proved-in-research の predecessor へ追跡する。恒等図式・空族・退化
  doctrine だけの発火を completion に使わない。
- `target failure policy`: (i) の反例(canonical 選択が coherent で
  ない)は `target-refuted` とし、G-101 の輸送構成へ差し戻す重大所見と
  して報告する。(iv) は witness 構成が成功条件であり、「再選択で常に
  消える(2-障害が恒等的に自明)」と証明された場合は不変量設計の仕様
  欠陥として GOAL 改訂案を返す。同じ blocker が二 cycle 続けば
  `target-blocked`。claim boundary 外の機構が必要と判明した場合は本 GOAL
  を拡張せず、GOAL 改訂提案として返す。
