# G-108-aat-geometry-reading-transport — 塔上層(geometry 段)輸送の opcartesian lift 定理

- `id`: `G-108-aat-geometry-reading-transport`
- `status`: `active`
- `priority`: `high`
- `research mode`: `target-theorem`
- `program context`: 登路上の位置は **Gr3 前半**(n1005 §5-4-5 の (0)、
  G-101 が意図的に後回しにした塔上層 lift の建設)。Gr3 系列は本カード →
  G-109(段横断整合)の2枚構成であり、**本カード完遂は Gr3 達成では
  ない**(n1005 §4.6)。隊列裁定(2026-08-15、Gr3/Gr4 系列先行)の第一手。
- `predecessor`: G-101(Atom 輸送の opcartesian lift 定理)の
  proved-in-research artifact(`Doct_U` / `ExtInst_U` / package 総圏 /
  `transportAlong` / opcartesian 普遍性。
  `research/lean/ResearchLean/AG/AtomFoundation/` 配下、unported)を
  土台として参照する。
- `tracking issue`: 未起票
  (active 昇格はユーザー裁定済み 2026-08-15。成立は本カード同期 PR の
  マージをもって。起票はマージ後、`$target-theorem-loop` 起動前に行う)
- `source note`: [docs/note/n1001_atom_is_all_you_need_discussion.md](../../docs/note/n1001_atom_is_all_you_need_discussion.md)(§3.3 塔、§3.5 仕様)、
  [docs/note/n1005_aat_semantic_geometry_route_after_g107.md](../../docs/note/n1005_aat_semantic_geometry_route_after_g107.md)(§5-4-5 Gr3 分解)
- `research aim`: reading の塔
  `ObProblem -> GeomRead -> CoreRead -> ExtInst -> Doct`(n1001 §3.3)の
  うち、G-101 が建設した core 段(`AATCorePackage` の輸送)の一段上、
  **geometry 段(`ReadingCore` 相当: site・topology・係数・raw restriction
  system)の総圏と輸送**を Lean で建設する。exact doctrine 射に沿う
  geometry data の輸送を opcartesian lift として構成・特徴づけ、site /
  topology / 係数 / raw system の輸送が一本の構成から供給されることを示す。
- `core tension`: G-101 と同型の緊張が一段上で再現するかが核心である。
  geometry 段の輸送データは型としては存在するが、それが core 段輸送から
  **生成される標準構成**なのか、手で与えるデータの束なのかは未決である。
  さらに geometry 段固有の失敗がある — site・係数は doctrine 射だけからは
  生えない(n1001 §3.3)ため、lift が失敗する位置と、失敗が要求する追加
  供給データの正体を段の水準で特定できるかが非自明性の核。core 段で lift
  できても geometry 段で止まる射の実在が、塔を段に分けた設計の存在理由を
  定理水準で裏づける。
- `rival`: fibred category の一般論(mathlib `CategoryTheory` 系)、
  G-101 の core 段 fibration 単体、`Formal/AG/ReadingFunctoriality` の
  既存 reading 間比較。差は「geometry data(site・係数)を fiber に持つ
  具体的 fibration を core 段 fibration の上に積み、lift の失敗段を
  geometry 固有の供給条件として特定する」点に置く。一般論の
  instantiation で済む部分は流用してよい。
- `claim boundary`: 固定した一般 carrier `U`、G-101 の `Doct_U` /
  `ExtInst_U` / package 総圏 / `transportAlong` を土台とし、その上の
  geometry 段(site・topology・係数・raw restriction system を成分に
  持つ geometry package)を対象とする。carrier を動かす主張、段横断の
  合成整合(G-109)、2-cell / 2-障害語彙(G-106 の領分)、`ObProblem`
  段(class の naturality)、doctrine 圏の fiber product(G-110)、
  nerve / cover との接続(S0 辞書)は含めない。
- `capability categories`: transport、fibration、counterexample、
  component-supply。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に
  置き、固定 statement と completion criteria だけで完了判定する。
- `portfolio constraint`: 正例(輸送構成と opcartesian 性)だけ、または
  負例(lift 失敗)だけで完了扱いしない。構成・普遍性・一意性・負例・
  成分供給の五面の Lean artifact 接続を要求する。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、反証なら
  `target-refuted`、全完了条件と final review を満たした場合だけ
  `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各 cycle は
  proof obligation delta で評価する。
- `dullness filter`: 次を弾く。identity 射だけでの発火、geometry data が
  退化(site 空・係数零・raw system 空)して輸送が vacuous に立つ構成、
  opcartesian 性・射影可換性を structure field で受け取る構成、G-101
  定理の名前替え re-export(geometry 成分が実質関与しない「拡張」)、
  負例を欠く正例のみの完了、追加仮定 `H_geom` を結論同値の言い換えで
  立てる構成、Formal 側既存補題の再証明だけで塔接続を欠く成果。
- `frontier`: `ObProblem` 段(class naturality)への拡張の観察、cartesian
  側 lift との相互作用、G-106 の 2-cell 語彙を geometry 段に載せる場合の
  次数契約の観察、S0 辞書(cover–nerve)への含意の記述。

- `target theorem`: **Geometry Reading Transport Opcartesian Lift
  Theorem**。G-101 の設定の上で:
  1. **(i) geometry 段総圏と射影**: geometry package(core package +
     site・topology・係数・raw restriction system)を対象とする総圏
     `GeomRead_U` と、core 段(G-101 package 総圏)への忘却射影 functor を
     構成し、圏則を証明する。
  2. **(ii) 輸送構成と opcartesian 性**: exact 射 `σ` と geometry package
     `G` から輸送 `geomTransportAlong σ G` を構成し、tautological hom が
     射影の上の opcartesian であること、および core 段への射影が G-101 の
     `transportAlong` と可換であること(射影可換)を証明する。
  3. **(iii) 一意性**: opcartesian lift の同型を除く一意性と fiber 内
     同型の記述を証明する。
  4. **(iv) 成分供給**: site・topology・係数・raw restriction system の
     各成分輸送等式が (ii) の一本の構成から導出されることを standalone
     等式群として証明する。
  5. **(v) 負例と追加仮定**: core 段では lift が存在するのに geometry
     段で lift が存在しない射を `FiniteModel` の carrier 上で構成し、
     lift に必要な追加供給仮定 `H_geom` を同定して、その十分性定理と
     負例上の `¬H_geom` を証明する。あわせて非自明性 witness
     (non-identity 射で site / 係数の輸送が実際に発火する例)を構成する。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/GeometryTransport/` 配下(新設)。
  `Formal/AG` は参照のみ(import 方向規律に従う)。geometry package の
  成分構成(site・topology・係数・raw restriction system の型)は既存
  `ReadingCore` 系の語彙に整合させるが、Research 側の定義を正とする。
  完了面は (i)–(v) まで。段横断合成・2-障害・bifibration・fiber
  product・nerve 接続は主張しない。
- `target proof artifacts`: geometry package の定義、総圏 `GeomRead_U` と
  圏則、core 段への射影 functor と functor 則、`geomTransportAlong` の
  構成、tautological hom、opcartesian 性 theorem、射影可換 theorem、
  factorization 一意性 theorem、fiber 内同型記述つき lift 一意性
  theorem、成分供給の standalone 等式群、負例 witness(任意の輸送先への
  非存在の Lean 証明)、`H_geom` の同定・十分性定理・負例上の `¬H_geom`、
  非自明性 witness、report
  `research/reports/G-108-aat-geometry-reading-transport.md`。
- `target proof strategy`: E0 geometry package と総圏・射影の構築 ->
  E1 `geomTransportAlong` 構成と tautological hom・射影可換 ->
  E2 opcartesian 性と一意性 -> E3 負例と `H_geom` の抽出・十分性・
  `¬H_geom` -> E4 成分供給等式と非自明性 witness。既存成果の利用 map:
  G-101 の `transportAlong` / `transportAlongHom_isStronglyCocartesian` /
  `transportAlong_liftUniqueUpToFiberIso`(core 成分と factor 対象)、
  `Formal/AG/ReadingFunctoriality` の reading 型群(ambient 素材)、
  `FiniteModel`(witness 計算)。固定 statement と完了条件は本カードのみを
  正本とする。
- `target theorem completion criteria`: 全 artifact が sorry なしで
  `ResearchLean` に受理され、axiom / placeholder audit が clean である
  こと。下記 ledger の `discharge-required` を構成・証明・Lean finite
  witness で放電し、audit で provenance、proof-use、structure-field
  escape、route integrity を監査すること。Lean / report / tracking Issue を
  同期し、final review packet を作り、`$math-lean-review` の4査読が
  すべて `No major findings` であること。
- `target premise discharge policy`: 入力(doctrine 対、射の構成データ、
  geometry package)だけを残せる。圏則、射影可換、輸送の
  well-definedness、opcartesian 性、一意性、負例の非存在証明、`H_geom`
  の十分性、成分供給、非自明性はすべて completion までに生成・証明する。
  lift 結論相当データを certificate や structure field で受け取るだけでは
  放電と数えない。
- `target material premise ledger`:
  - `carrier U / FiniteModel`: `ambient-boundary`。定理は一般 `U` で証明し、
    FiniteModel は witness の計算のみに使う。
  - `G-101 core 段 artifact(Doct_U / ExtInst_U / package 総圏 /
    transportAlong と普遍性)`: `ambient-boundary`。reviewed 済み定理の
    参照のみ。geometry 段の opcartesian 性・well-definedness を G-101 の
    statement に含めない(本カードで導出する)。
  - `geometry package の成分型(site / topology / 係数 / raw restriction
    system)`: `ambient-boundary`。`Formal/AG` の既存語彙への整合参照。
    輸送の存在・等式を型の field に入れない。
  - `総圏・射影の圏則 / functor 則`: `discharge-required`。artifact は
    圏則 theorem 群。
  - `geomTransportAlong の well-definedness と射影可換`:
    `discharge-required`。provenance は exact `σ` と `G` の構成データのみ。
  - `opcartesian 性と一意性`: `discharge-required`。G-101 と同じく普遍性
    から証明し、field に入れない。
  - `負例と H_geom`: `discharge-required`。負例は FiniteModel 上の
    非存在 Lean 証明、`H_geom` は十分性定理+負例上の否定で挟む。
  - `成分供給等式`: `discharge-required`。(ii) の構成からの導出のみを
    認める。
- `target anti-weakening rule`: 結論相当の仮定(opcartesian 性、射影
  可換、成分供給等式、`H_geom` の十分性)を theorem argument、typeclass、
  structure field、certificate field へ移して成功扱いしない。
  `ambient-boundary` に残せるのは入力幾何(carrier、G-101 reviewed
  artifact、成分型)だけである。`H_geom` を「lift が存在する」と同値な
  述語で立てることを禁じる(供給データの条件として立て、十分性を定理で
  結ぶ)。
- `target failure policy`: geometry 段の lift が exact 射に対しても
  一般に存在しない(追加仮定なしの (ii) が不成立)と判明した場合は
  `target-refuted` ではなく statement を「存在条件の同定+条件付き
  構成」形へ改訂提案する(G-110 (B) と同じ成果物形式)。構成が
  `H_geom` の同定に至らず停滞する場合は `target-blocked`。claim
  boundary 外の機構(段横断・2-cell)が必要と判明した場合は本 GOAL を
  改訂せず G-109 へ送る。
