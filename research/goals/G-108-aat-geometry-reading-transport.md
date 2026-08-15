# G-108-aat-geometry-reading-transport — 塔上層(geometry 段)輸送の opcartesian lift 定理

- `id`: `G-108-aat-geometry-reading-transport`
- `status`: `active`
- `priority`: `high`
- `research mode`: `target-theorem`
- `program context`: 登路上の位置は **Gr3 前半**(n1005 §5「隊列」
  第5項 Gr3 完成カードの分解 (0)、G-101 が意図的に後回しにした塔上層
  lift の建設)。Gr3 系列は本カード → G-109(段横断整合)の2枚構成で
  あり、**本カード完遂は Gr3 達成ではない**(n1005 §4.6)。隊列裁定
  (2026-08-15、Gr3/Gr4 系列先行)の第一手。本カードは n1005 §2 の
  測量台帳に対応行を持たず、達成階梯(n1001 §3.5 の Gr3)の帳簿に
  専属する(帳簿の二重性の明示)。
- `predecessor`: G-101(Atom 輸送の opcartesian lift 定理)の
  proved-in-research artifact を土台として参照する。accepted snapshot =
  PR [#3889](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/3889)
  マージ済み(final `$math-lean-review` 全4レーン `No major findings`)。
  再利用する宣言: `Doct_U` の exact 射(`ExactDoctrineHom`)、
  `ExtInst_U`、package 総圏(`packageTotalCategory` /
  `packageProjection` / `PackageTotalHom`)、`transportAlong` /
  `transportAlongHom`、`transportAlongHom_isStronglyCocartesian`、
  `transportAlong_liftUniqueUpToFiberIso`
  (`research/lean/ResearchLean/AG/AtomFoundation/` 配下、unported)。
- `tracking issue`: 未起票
  (active 昇格はユーザー裁定済み 2026-08-15。成立は本カード同期 PR の
  マージをもって。起票はマージ後、`$target-theorem-loop` 起動前に行う)
- `source note`: [docs/note/n1001_atom_is_all_you_need_discussion.md](../../docs/note/n1001_atom_is_all_you_need_discussion.md)(§3.3 塔、§3.5 仕様)、
  [docs/note/n1005_aat_semantic_geometry_route_after_g107.md](../../docs/note/n1005_aat_semantic_geometry_route_after_g107.md)(§5 隊列第5項の Gr3 分解)
- `research aim`: reading の塔
  `ObProblem -> GeomRead -> CoreRead -> ExtInst -> Doct`(n1001 §3.3)の
  うち、G-101 が建設した core 段(`AATCorePackage` の輸送)の一段上、
  **geometry 段(`ReadingCore` 相当: site・係数・raw restriction
  system)の総圏と輸送**を Lean で建設する。core 段の射に沿う geometry
  data の輸送を opcartesian lift として構成・特徴づけ、site / 係数 /
  raw system の輸送(および導出データである topology の生成位相対応)が
  一本の構成から供給されることを示す。あわせて、lift の障害の正体を
  段の水準で同定する — realization 互換以外の全成分は常に輸送可能で
  あること(成分輸送可能性)と、realization 互換の供給 `H_geom` が
  lift を制御することを、正例・負例の対で固定する。
- `core tension`: G-101 と同型の緊張が一段上で再現するかが核心である。
  geometry 段の輸送データは型としては存在するが、それが core 段輸送から
  生成される標準構成なのか、手で与えるデータの束なのかは未決である。
  段固有の見立て(n1001 §3.3)はこうである — geometry 成分の多く
  (座標族・関係族・被覆要件・係数・raw system)は core 射が運ぶ
  context 圏同値に沿って再インデックス可能と見込まれる一方、**site の
  realization との両立だけは core 射が運ばない**。正確に言う: core 射は
  `contextEquivalence` 自体は運ぶが、その圏同値が両端 package の
  realization(context 射の可読化と非生成条件)と両立するという条件は
  運ばない。したがって lift の失敗が実在するなら、その実質は
  realization 互換性にあり、係数は失敗を担えない見込みである(係数は
  輸送先に持ち回れるため)。この見立てが正しく、core 段で lift できても
  geometry 段で止まる射が実在すれば、塔を段に分けた設計の存在理由が
  定理水準で裏づけられることになる。逆に全ての射で lift が構成できて
  しまうなら、それは本カードの仕様欠陥(hom 契約が realization を実質
  参照していない)か、塔設計の簡約定理かのどちらかであり、failure
  policy で区別する。
- `rival`: fibred category の一般論(mathlib `CategoryTheory` 系)、
  G-101 の core 段 fibration 単体、`Formal/AG/ReadingFunctoriality` の
  既存 reading 間比較。差は「geometry data(site・係数)を fiber に持つ
  具体的 partial op-cleavage を core 段 fibration の上に積み、lift の
  障害を realization 互換の供給条件として同定する」点に置く。一般論の
  instantiation で済む部分は流用してよい。
- `claim boundary`: 固定した一般 carrier `U`、G-101 の `Doct_U` /
  `ExtInst_U` / package 総圏 / `transportAlong` を土台とし、その上の
  geometry 段(site・係数・raw restriction system を成分に持ち、site
  realization を参照する geometry package)を対象とする。topology は
  成分ではなく導出データとして扱う(`AATSite` の生成位相)。宇宙は
  固定対 `{u, v}`(carrier 側 `u`、係数側 `v`)の上で構成し、全定理を
  同一宇宙対内で述べる(宇宙横断の主張はしない)。係数 regime は
  `ReadingCore.Coefficient`(単一 `CommRing`)水準であり、context-
  indexed presheaf 水準の係数(`obstructionQuotientCoefficient` 等)は
  本カードの対象外(frontier)。carrier を動かす主張、段横断の合成整合
  (G-109)、2-cell / 2-障害語彙(G-106 の領分)、`ObProblem` 段
  (class の naturality)、doctrine 圏の fiber product(G-110)、
  nerve / cover との接続(S0 辞書)は含めない。
- `geometry hom contract`: geometry 段の hom
  `GeomReadHom G H over f`(`f : P -> Q` は core 総圏射)のデータ仕様を
  次で**本カードが固定**し、loop 中に変更しない(変更が必要と判明した
  場合は failure policy の改訂経路のみ)。
  (1) **site 成分**: `G` の被覆要件・overlap を `f` の
  `contextEquivalence` に沿って**前進保存**する(反映は要求しない)。
  (2) **係数成分**: 係数環の `RingHom`(前進向き。可逆性は要求しない。
  fiber 内同型の記述でのみ `RingEquiv` を使う)。
  (3) **raw 成分**: `contextEquivalence` の backward functor による
  reindex と係数 `RingHom` に沿った base change の両立等式(依存型を
  跨ぐため index 付き等式または cast 経由の形を許す)。
  (4) **realization 互換**: `f` の `contextEquivalence` が `G` の site
  realization(context 射の可読化と非生成条件)を `H` の realization へ
  写すという **Prop 条件**。これは hom が持ち込む外部データではなく、
  `f` と両端 package の間の両立条件である。
  (5) **topology**: hom の条件に含めない。(iv) の比較定理の結論形を
  「輸送された被覆要件・overlap の生成位相の covering sieve が押し出し
  と一致する iff」で固定する。
  (6) **identity / composition 則**を持ち、総圏の圏則はここから証明する。
  各項の強さ(等号か同型か片方向か)は上記の通り固定済みであり、
  強める・弱める変更はどちらも statement 改訂として扱う。
- `capability categories`: transport、fibration、counterexample、
  component-supply、obstruction-identification。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に
  置き、固定 statement と completion criteria だけで完了判定する。
- `portfolio constraint`: 正例(輸送構成と opcartesian 性)だけ、または
  負例(lift 失敗)だけで完了扱いしない。構成・普遍性・一意性・障害
  同定(正負対)・成分供給の五面の Lean artifact 接続を要求する。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、反証なら
  `target-refuted`、全完了条件と final review を満たした場合だけ
  `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各 cycle は
  proof obligation delta で評価する。
- `dullness filter`: 次を弾く。identity 射だけでの発火、geometry data が
  退化(site 空・cover なし・係数零環・raw system 空)して輸送が
  vacuous に立つ構成、opcartesian 性・射影可換性を structure field で
  受け取る構成、G-101 定理の名前替え re-export(geometry 成分が実質
  関与しない「拡張」)、負例を欠く正例のみの完了、**負例を空 fiber・
  空 hom 空間・成分型の型不一致・退化 geometry data の vacuity で満たす
  構成**、**非可住な(どの入力でも成立しない)`H_geom` による十分性と
  否定の同時放電**、追加仮定 `H_geom` を結論の言い換えで立てる構成、
  witness の発火を値が恒等に落ちる輸送で主張する構成、hom 契約の強度を
  事後変更して lift / no-lift のどちらかへ寄せる構成、Formal 側既存
  補題の再証明だけで塔接続を欠く成果。
- `frontier`: `ObProblem` 段(class naturality)への拡張の観察、cartesian
  側 lift との相互作用、G-106 の 2-cell 語彙を geometry 段に載せる場合の
  次数契約の観察、S0 辞書(cover–nerve)への含意の記述、topology の
  導出を超える独立位相データの要否の観察、**law 由来係数の presheaf
  水準(`obstructionQuotientCoefficient` / Čech 係数)への typed bridge**
  (scalar `CommRing` と context-indexed presheaf の橋。owner 裁定
  2026-08-15 により本カードの claim から外し、S0 辞書・G-110 (D) 接続の
  素材としてここに置く)。

- `target theorem`: **Geometry Reading Transport Opcartesian Lift
  Theorem**。G-101 の設定と上記 geometry hom contract の上で:
  1. **(i) geometry 段総圏と射影**: geometry package(core package +
     site・係数・raw restriction system。site realization を参照する)を
     対象とし、`GeomReadHom` を射とする総圏 `GeomRead_U` と、core 段
     (G-101 package 総圏)への忘却射影 functor を構成し、圏則を証明
     する。
  2. **(ii) 輸送構成と opcartesian 性**: exact 射 `σ` と geometry package
     `G` から canonical 輸送 `geomTransportAlong σ G` を構成し、
     tautological hom が **(i) の射影の上、底射 = G-101 の canonical
     lift `transportAlongHom σ`** の opcartesian lift であることを、
     tail の全称域 = 任意の core 総圏射の上の hom で証明する。本カードが
     主張するのは**選択された底射上の partial op-cleavage** であり、
     全底射に対する lift の存在(full opfibration)は主張しない。core 段
     への射影が G-101 の `transportAlong` と一致すること(射影可換)は
     provenance 等式として固定する(定義により `rfl` で成立する場合も
     成功と数える — 価値は構成の provenance にある。G-101 (iv) と同じ
     扱い)。
  3. **(iii) 一意性**: opcartesian lift の同型を除く一意性と fiber 内
     同型の記述を証明する。fiber 内同型の記述は geometry 固有の自由度
     (係数環の環同型・関係族の表示替え同型)を陽に扱う。fiber が
     rigid(同型 = 等号)と証明される場合は、その rigidity theorem を
     成果と数える。
  4. **(iv) 成分供給**: site・係数・raw restriction system の各成分
     輸送等式が (ii) の一本の構成から導出されることを standalone
     等式群(依存型を跨ぐ成分は cast 演算子経由または index 付き等式の
     形を許す)として証明する。topology については geometry hom
     contract (5) の結論形(生成位相の covering sieve iff)で比較定理を
     立てる。あわせて **instantiation witness** — `FiniteModel` 上で、
     **非退化 raw restriction system の Formal 有限実例**
     (`RawPresheafFiniteExample` 系)を成分に持つ geometry package の
     所属証明 — を構成し、成分型が Formal の実データの受け皿である
     ことを接地する(law 由来係数の presheaf 水準 bridge は frontier —
     owner 裁定 2026-08-15)。
  5. **(v) 障害の同定(正負対)**: 次の五点を対で構成・証明する。
     (a) **成分輸送可能性 theorem**: realization 互換以外の全成分
     (site 要件・係数・raw system)は任意の core 総圏射に沿って常に
     輸送可能である(「係数は失敗を担えない」の定理化)。
     (b) **`H_geom` の定義**: `f` に対する realization transport の
     供給 — `f` の `contextEquivalence` の下で `G` の realization を
     輸送先の realization へ写すデータと非生成条件の保存 — を、lift の
     存在を参照しない低レベル field-content の structure / Prop として
     固定する。
     (c) **十分性 theorem**: `H_geom f G` ならば `f` の上の geometry
     lift が存在する。**positive witness**: 非退化・非恒等の入力
     (FiniteModel 上)で `H_geom` が成立し lift が発火する例を構成し、
     `H_geom` の可住性を証明する。
     (d) **必要性の判定**: 非退化 geometry package と exact `σ` 上の
     core 総圏射のクラス上で `lift 存在 -> H_geom` を証明するか、反例で
     否定する。否定された場合、`H_geom` は「十分な供給条件の一つ」で
     あることを statement の scope 限定として claim mapping に記録する
     (これは審査上、弱化ではなく同定結果の報告として扱う)。
     (e) **負例 witness**: exact 射 `σ` の上の core 総圏射
     `f : P -> Q`(core 段の lift としては存在する非 tautological な
     射 — tautological hom と等しくないことを証明する)であって、`P`
     上の geometry package からの `f` の上の hom が任意の輸送先
     geometry package へ存在しないものを `FiniteModel` の carrier 上で
     構成し(realization が両立しない `Q` の構成)、負例上の `¬H_geom`
     を証明する。あわせて非自明性 witness — non-identity 射で **site の
     対象集合または cover 族、および raw system の値が輸送前後で実際に
     不一致となることの Lean 証明**を伴う例 — を構成する(係数の
     非恒等輸送は canonical 構成では原理的に生じないため発火要求に
     含めない。係数非恒等は hom データ水準の fiber 同型例として (iii)
     側で扱う)。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/GeometryTransport/` 配下(新設)。
  `Formal/AG` は参照のみ(import 方向規律に従う)。geometry package の
  成分型は Formal の `ReadingCore` 系(`SelectedGeometryReading` /
  係数 / `RawAmbientRestrictionSystem`)を再利用し、Research 側で新設
  するのは hom・総圏・輸送・定理に限る(成分型の再定義はしない)。
  完了面は (i)–(v) まで。段横断合成・2-障害・bifibration・fiber
  product・nerve 接続・presheaf 水準係数は主張しない。
- `target proof artifacts`: geometry package の定義(Formal 成分型の
  組+realization 参照)、`GeomReadHom`(geometry hom contract の
  実装)、総圏 `GeomRead_U` と圏則、core 段への射影 functor と functor
  則、`geomTransportAlong` の構成、tautological hom、opcartesian 性
  theorem(底射 = `transportAlongHom σ`、tail 全称域 = 任意の core 総圏
  射)、射影可換の provenance 等式、factorization 一意性 theorem、
  fiber 内同型記述つき lift 一意性 theorem(係数環 iso・表示替え iso を
  陽に含む。rigid の場合は rigidity theorem)、成分供給の standalone
  等式群と topology 生成位相比較定理(covering sieve iff)、
  instantiation witness(非退化 raw 有限実例の所属証明)、成分輸送
  可能性 theorem、`H_geom` の定義(realization transport 供給
  structure)・十分性定理・positive witness(可住性+発火)・必要性
  theorem または反例+scope 限定記録、負例 witness(core 総圏射 `f` の
  non-tautological 性と core 段 lift 存在の証明、任意の輸送先への
  非存在の Lean 証明、輸送先候補クラスの非空性証明、負例上の
  `¬H_geom`)、非自明性 witness(site / raw system の値変化の Lean
  証明つき)、report
  `research/reports/G-108-aat-geometry-reading-transport.md`。
- `target proof strategy`: E0 geometry package・`GeomReadHom`・総圏・
  射影の構築(hom contract と宇宙対 `{u,v}` はカード固定に従う)->
  E1 `geomTransportAlong` 構成と tautological hom・射影可換 ->
  E2 opcartesian 性と一意性 -> E3 成分輸送可能性・`H_geom` 定義・
  十分性・positive witness・必要性判定・負例 -> E4 成分供給等式・
  topology 比較・instantiation witness・非自明性 witness。既存成果の
  利用 map: G-101 の `transportAlong` /
  `transportAlongHom_isStronglyCocartesian` /
  `transportAlong_liftUniqueUpToFiberIso`(core 成分と factor 対象)、
  `Formal/AG` の `ReadingCore` / `SelectedGeometryReading` /
  `RawAmbientRestrictionSystem`(成分型)、
  `Formal/AG/Examples/FiniteModel.lean` と
  `Formal/AG/LawAlgebra/RawPresheafFiniteExample.lean`(witness 素材)。
  固定 statement と完了条件は本カードのみを正本とする。
- `target theorem completion criteria`: 全 artifact が sorry なしで
  `ResearchLean` に受理され、axiom / placeholder audit が clean である
  こと。下記 ledger の `discharge-required` を構成・証明・Lean finite
  witness で放電し、audit で provenance、proof-use、structure-field
  escape、route integrity を監査すること。Lean / report / tracking Issue を
  同期し、final review packet を作り、
  `$math-lean-review research/goals/G-108-aat-geometry-reading-transport.md G-108-aat-geometry-reading-transport`
  の4査読がすべて `No major findings` であること。
- `target premise discharge policy`: 入力(doctrine 対、射の構成データ、
  geometry package)だけを残せる。圏則、射影可換、輸送の
  well-definedness、opcartesian 性、一意性、成分輸送可能性、`H_geom` の
  十分性・可住性・必要性判定、負例の非存在証明、成分供給、
  instantiation witness、非自明性はすべて completion までに生成・証明
  する。入力の非退化性(site 非空・実 cover・非零係数・非空 raw
  system)も supplied premise ではなく witness 構成からの証明で放電
  する。lift 結論相当データを certificate や structure field で受け取る
  だけでは放電と数えない。
- `target material premise ledger`:
  - `carrier U / FiniteModel`: `ambient-boundary`(唯一の無条件
    ambient)。定理は一般 `U` で証明し、FiniteModel は witness の計算
    のみに使う。
  - `G-101 core 段 artifact(predecessor 節の宣言一覧)`:
    `ambient-boundary`。accepted snapshot(PR #3889)の reviewed 済み
    定理の参照のみ。geometry 段の opcartesian 性・well-definedness を
    G-101 の statement に含めない(本カードで導出する)。
  - `geometry package の成分型(Formal の ReadingCore 系)`:
    `ambient-boundary`。Formal reviewed **型**の再利用のみ(再定義
    しない)。輸送の存在・等式・非退化性を型の資格に含めない。
  - `入力資格(exact σ・source geometry package・負例射 f)`:
    `discharge-required`。witness で使う非退化性(site 非空・実 cover・
    係数が零環でない・raw system 非空)は concrete witness の構成から
    証明する。`f` の non-tautological 性(tautological hom との不等)と
    core 段 lift の存在も Lean 証明で固定する。
  - `GeomReadHom 契約の実装と総圏・射影の圏則 / functor 則`:
    `discharge-required`。hom contract の各項(前進保存・RingHom・raw
    両立・realization 互換 Prop・id / comp)を実装し、圏則を証明する。
  - `geomTransportAlong の well-definedness と射影可換`:
    `discharge-required`。provenance は exact `σ` と `G` の構成データのみ。
  - `opcartesian 性と一意性`: `discharge-required`。G-101 と同じく普遍性
    から証明し、field に入れない。
  - `成分輸送可能性 theorem`: `discharge-required`。realization 互換
    以外の成分が任意の core 総圏射に沿って輸送可能であることの証明。
  - `H_geom(定義・十分性・positive witness・必要性判定)`:
    `discharge-required`。定義は lift 非参照の低レベル field-content。
    可住性(positive witness)を欠く十分性・否定の同時放電は認めない。
    必要性が反例で否定された場合の scope 限定は claim mapping への
    記録を義務とする。
  - `負例と非存在証明`: `discharge-required`。FiniteModel 上の非存在
    Lean 証明で、空 fiber・空 hom 空間・成分型の型不一致・退化
    geometry data による vacuity を放電と数えない。輸送先候補クラスの
    非空性を witness の一部として証明する。
  - `成分供給等式と topology 比較`: `discharge-required`。(ii) の構成
    からの導出のみを認める。topology は covering sieve iff の結論形。
  - `instantiation witness(非退化 raw 有限実例)`:
    `discharge-required`。provenance は Formal の
    `RawPresheafFiniteExample` 系。成分型が Formal 実データの受け皿で
    あることの接地であり、これを省いた完了は認めない。
  - `非自明性 witness`: `discharge-required`。provenance は FiniteModel
    上の具体構成。site / raw system の値の不一致の Lean 証明を要求し、
    値が恒等に落ちる輸送での発火主張を放電と数えない。
- `target anti-weakening rule`: 結論相当の仮定(opcartesian 性、射影
  可換、成分供給等式、成分輸送可能性、`H_geom` の十分性・可住性)を
  theorem argument、typeclass、structure field、certificate field へ
  移して成功扱いしない。`ambient-boundary` に残せるのは carrier、
  G-101 accepted artifact、Formal 成分**型**だけである(入力の非退化性は
  含めない — witness から証明する)。`H_geom` を「lift が存在する」と
  同値**または片方向に近い**述語で立てることを禁じる(realization
  transport の供給データ条件として立て、十分性を定理で結ぶ。構造的
  条件として立てた結果、lift 存在との同値が**定理として**後から成立
  することは違反ではない — G-107 条件 C の前例に従い、その場合は同値
  定理を成果と数える)。非可住な `H_geom` による放電を禁じる(positive
  witness 義務)。geometry hom contract の各項の強度を loop 中に変更
  して lift / no-lift のどちらかへ寄せることを禁じる。opcartesian
  普遍性の全称域(任意の core 総圏射の上の hom)を縮めない。総圏の
  hom equality を商・Setoid へ粗視化して一意性を自明化しない。負例を
  空 fiber・空 hom 空間・成分型の型不一致・退化 geometry data の
  vacuity で満たさない。
- `target route integrity gate`: geometry package・`GeomReadHom`・
  `geomTransportAlong`・`H_geom`・負例・witness の provenance を G-101
  accepted artifact、Formal 成分型、canonical 構成、opcartesian 普遍性、
  concrete witness へ追跡する。identity 射だけ・退化 geometry data
  (site 空・cover なし・係数零環・raw system 空)だけの発火、
  one-way-as-equivalence、proof 後の GOAL 読み替えを completion に
  使わない。
- `target failure policy`: 次の三分岐で扱う。
  (1) 追加仮定なしの (ii)(canonical 輸送の無条件構成)の不成立が
  `FiniteModel` 上の Lean 反例で証明された場合に限り、statement の
  「存在条件の同定+条件付き構成」形(G-110 (B) と同じ三点セット)への
  改訂を**ユーザー裁定へ**提案する。改訂はカード再固定と tracking
  Issue 記録を経るまで発効せず、この経路自体を改訂前後いずれの
  statement の `target-theorem-proved` にも数えない。geometry hom
  contract の強度変更が必要と判明した場合も同じ経路のみを許す。
  (2) 仕様した射クラス(exact `σ` 上の core 総圏射)の**全て**に対して
  geometry lift が存在すると証明された場合(= (v)(e) の負例が存在
  しない)、それは本カードの仕様欠陥(hom 契約が realization を実質
  参照していない)または塔設計の簡約定理のどちらかであり、lift 常時
  存在定理を成果として固定した上で GOAL 改訂案(hom 契約の
  realization 参照強化を含む)をユーザーへ返す。この場合も完了とは
  数えない。
  (3) 構成が `H_geom` の同定に至らず停滞する場合は `target-blocked`。
  claim boundary 外の機構(段横断・2-cell)が必要と判明した場合は
  本 GOAL を改訂せず G-109 へ送り、本カードは `target-blocked` として
  完了に数えない。
