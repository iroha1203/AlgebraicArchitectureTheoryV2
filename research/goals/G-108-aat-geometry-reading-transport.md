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
  proved-in-research artifact(`Doct_U` / `ExtInst_U` / package 総圏 /
  `transportAlong` / opcartesian 普遍性。
  `research/lean/ResearchLean/AG/AtomFoundation/` 配下、unported)を
  土台として参照する。
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
  一本の構成から供給されることを示す。あわせて、lift が失敗する射の
  クラスと、失敗が要求する追加供給データの正体を段の水準で特定する。
- `core tension`: G-101 と同型の緊張が一段上で再現するかが核心である。
  geometry 段の輸送データは型としては存在するが、それが core 段輸送から
  生成される標準構成なのか、手で与えるデータの束なのかは未決である。
  段固有の見立て(n1001 §3.3)はこうである — geometry 成分の多く
  (座標族・関係族・被覆要件)は core 射が運ぶ圏同値に沿って再インデックス
  可能と見込まれる一方、**site の realization(context 射の可読化と
  非生成条件)だけは core 射が運ばない**。したがって lift の失敗が実在
  するなら、その実質は realization 互換性にあり、係数は失敗を担えない
  見込みである(係数は輸送先に持ち回れるため)。この見立てが正しく、
  core 段で lift できても geometry 段で止まる射が実在すれば、塔を段に
  分けた設計の存在理由が定理水準で裏づけられることになる。逆に全ての
  射で lift が構成できてしまうなら、それは本カードの仕様欠陥(hom 定義が
  realization を参照していない)か、塔設計の簡約定理かのどちらかであり、
  failure policy で区別する。
- `rival`: fibred category の一般論(mathlib `CategoryTheory` 系)、
  G-101 の core 段 fibration 単体、`Formal/AG/ReadingFunctoriality` の
  既存 reading 間比較。差は「geometry data(site・係数)を fiber に持つ
  具体的 fibration を core 段 fibration の上に積み、lift の失敗を
  geometry 固有の供給条件(realization 互換)として特定する」点に置く。
  一般論の instantiation で済む部分は流用してよい。
- `claim boundary`: 固定した一般 carrier `U`、G-101 の `Doct_U` /
  `ExtInst_U` / package 総圏 / `transportAlong` を土台とし、その上の
  geometry 段(site・係数・raw restriction system を成分に持ち、site
  realization を参照する geometry package)を対象とする。topology は
  成分ではなく導出データとして扱う(`AATSite` の生成位相)。carrier を
  動かす主張、段横断の合成整合(G-109)、2-cell / 2-障害語彙(G-106 の
  領分)、`ObProblem` 段(class の naturality)、doctrine 圏の fiber
  product(G-110)、nerve / cover との接続(S0 辞書)は含めない。
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
  退化(site 空・cover なし・係数零環・raw system 空)して輸送が
  vacuous に立つ構成、opcartesian 性・射影可換性を structure field で
  受け取る構成、G-101 定理の名前替え re-export(geometry 成分が実質
  関与しない「拡張」)、負例を欠く正例のみの完了、**負例を空 fiber・
  空 hom 空間・成分型の型不一致・退化 geometry data の vacuity で満たす
  構成**、追加仮定 `H_geom` を結論の言い換えで立てる構成、witness の
  発火を値が恒等に落ちる輸送で主張する構成、Formal 側既存補題の
  再証明だけで塔接続を欠く成果。
- `frontier`: `ObProblem` 段(class naturality)への拡張の観察、cartesian
  側 lift との相互作用、G-106 の 2-cell 語彙を geometry 段に載せる場合の
  次数契約の観察、S0 辞書(cover–nerve)への含意の記述、topology の
  導出を超える独立位相データの要否の観察。

- `target theorem`: **Geometry Reading Transport Opcartesian Lift
  Theorem**。G-101 の設定の上で:
  1. **(i) geometry 段総圏と射影**: geometry package(core package +
     site・係数・raw restriction system。site realization を参照する)を
     対象とする総圏 `GeomRead_U` と、core 段(G-101 package 総圏)への
     忘却射影 functor を構成し、圏則を証明する。geometry 段の hom は
     成分比較に加えて **site realization 互換**(hom の context 対応が
     両端 package の realization と両立する条件)をデータ仕様に含める。
  2. **(ii) 輸送構成と opcartesian 性**: exact 射 `σ` と geometry package
     `G` から canonical 輸送 `geomTransportAlong σ G` を構成し、
     tautological hom が **(i) の射影の上、底射 = G-101 の canonical
     lift `transportAlongHom σ`** の opcartesian lift であることを、
     tail の全称域 = 任意の core 総圏射の上の hom で証明する。core 段
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
     形を許す)として証明する。topology については、輸送された被覆
     要件・overlap が生成する位相と covering sieve の押し出しの対応を
     比較定理として立てる。あわせて **instantiation witness** —
     `FiniteModel` 上で、係数が実際の law 由来係数である実例1点の
     geometry package 所属証明 — を構成し、成分型が Formal の診断機構
     (Čech / law 係数)の instance であることを固定する。
  5. **(v) 負例と追加仮定**: **exact 射 `σ` の上の core 総圏射
     `f : P -> Q`(core 段の lift としては存在する非 tautological な
     射)**であって、`P` 上の geometry package から `f` の上の hom が
     任意の輸送先 geometry package へ存在しないものを `FiniteModel` の
     carrier 上で構成する(realization が両立しない `Q` の構成)。lift に
     必要な追加供給仮定 `H_geom` を **site realization transport の供給
     データ条件**として同定し、その十分性定理と負例上の `¬H_geom` を
     証明する。あわせて非自明性 witness — non-identity 射で **site の
     対象集合または cover 族、および raw system の値が輸送前後で実際に
     不一致となることの Lean 証明**を伴う例 — を構成する(係数の
     非恒等輸送は canonical 構成では原理的に生じないため発火要求に
     含めない。係数非恒等は hom データ水準の fiber 同型例として (iii) 側で
     扱う)。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/GeometryTransport/` 配下(新設)。
  `Formal/AG` は参照のみ(import 方向規律に従う)。geometry package の
  成分型は Formal の `ReadingCore` 系(`SelectedGeometryReading` /
  係数 / `RawAmbientRestrictionSystem`)を再利用し、Research 側で新設
  するのは hom・総圏・輸送・定理に限る(成分型の再定義はしない)。
  完了面は (i)–(v) まで。段横断合成・2-障害・bifibration・fiber
  product・nerve 接続は主張しない。
- `target proof artifacts`: geometry package の定義(Formal 成分型の
  組+realization 参照)、総圏 `GeomRead_U` と圏則、core 段への射影
  functor と functor 則、`geomTransportAlong` の構成、tautological
  hom、opcartesian 性 theorem(底射 = `transportAlongHom σ`、tail 全称
  域 = 任意の core 総圏射)、射影可換の provenance 等式、factorization
  一意性 theorem、fiber 内同型記述つき lift 一意性 theorem(係数環
  iso・表示替え iso を陽に含む。rigid の場合は rigidity theorem)、
  成分供給の standalone 等式群と topology 生成位相比較定理、
  instantiation witness(law 由来係数の実例1点)、負例 witness
  (core 総圏射 `f` と、任意の輸送先への非存在の Lean 証明。輸送先
  候補クラスの非空性と `f` の core 段 lift 存在の証明を含む)、
  `H_geom` の同定(realization transport 供給 structure)・十分性
  定理・負例上の `¬H_geom`、非自明性 witness(site / raw system の
  値変化の Lean 証明つき)、report
  `research/reports/G-108-aat-geometry-reading-transport.md`。
- `target proof strategy`: E0 geometry package と総圏・射影の構築
  (universe 規律をここで固定する — `ReadingCore` 系は 2 宇宙
  `{u, v}` を持つため、総圏の `Category` instance の宇宙を先に確定
  する)-> E1 `geomTransportAlong` 構成と tautological hom・射影可換
  -> E2 opcartesian 性と一意性 -> E3 負例と `H_geom` の抽出・十分性・
  `¬H_geom` -> E4 成分供給等式・topology 比較・instantiation witness・
  非自明性 witness。既存成果の利用 map: G-101 の `transportAlong` /
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
  well-definedness、opcartesian 性、一意性、負例の非存在証明、`H_geom`
  の十分性、成分供給、instantiation witness、非自明性はすべて
  completion までに生成・証明する。lift 結論相当データを certificate や
  structure field で受け取るだけでは放電と数えない。
- `target material premise ledger`:
  - `carrier U / FiniteModel`: `ambient-boundary`。定理は一般 `U` で証明し、
    FiniteModel は witness の計算のみに使う。
  - `G-101 core 段 artifact(Doct_U / ExtInst_U / package 総圏 /
    transportAlong と普遍性)`: `ambient-boundary`。reviewed 済み定理の
    参照のみ。geometry 段の opcartesian 性・well-definedness を G-101 の
    statement に含めない(本カードで導出する)。
  - `geometry package の成分型(Formal の ReadingCore 系)`:
    `ambient-boundary`。Formal reviewed 型の再利用のみ(再定義しない)。
    輸送の存在・等式を型の field に入れない。witness で使う水準の
    非退化要件(site 非空・cover 構造あり・係数が零環でない・raw
    system 非空)を ambient の資格条件とする。
  - `総圏・射影の圏則 / functor 則`: `discharge-required`。artifact は
    圏則 theorem 群。
  - `geomTransportAlong の well-definedness と射影可換`:
    `discharge-required`。provenance は exact `σ` と `G` の構成データのみ。
  - `opcartesian 性と一意性`: `discharge-required`。G-101 と同じく普遍性
    から証明し、field に入れない。
  - `負例と H_geom`: `discharge-required`。負例は FiniteModel 上の
    非存在 Lean 証明で、空 fiber・空 hom 空間・成分型の型不一致・退化
    geometry data による vacuity を放電と数えない。輸送先候補クラスの
    非空性(および `f` の core 段 lift の存在)を witness の一部として
    証明する。`H_geom` は十分性定理+負例上の否定で挟む。
  - `成分供給等式と topology 比較`: `discharge-required`。(ii) の構成
    からの導出のみを認める。
  - `instantiation witness(law 由来係数の実例)`: `discharge-required`。
    provenance は Formal の FiniteModel / 有限 raw system 実例。成分型が
    診断機構の instance であることの接地であり、これを省いた完了は
    認めない。
  - `非自明性 witness`: `discharge-required`。provenance は FiniteModel
    上の具体構成。site / raw system の値の不一致の Lean 証明を要求し、
    値が恒等に落ちる輸送での発火主張を放電と数えない。
- `target anti-weakening rule`: 結論相当の仮定(opcartesian 性、射影
  可換、成分供給等式、`H_geom` の十分性)を theorem argument、typeclass、
  structure field、certificate field へ移して成功扱いしない。
  `ambient-boundary` に残せるのは入力幾何(carrier、G-101 reviewed
  artifact、Formal 成分型)だけである。`H_geom` を「lift が存在する」と
  同値**または片方向に近い**述語で立てることを禁じる(realization
  transport の供給データ条件として立て、十分性を定理で結ぶ。構造的
  条件として立てた結果、lift 存在との同値が**定理として**後から成立
  することは違反ではない — G-107 条件 C の前例に従い、その場合は同値
  定理を成果と数える)。opcartesian 普遍性の全称域(任意の core 総圏
  射の上の hom)を縮めない。総圏の hom equality を商・Setoid へ粗視化
  して一意性を自明化しない。負例を空 fiber・空 hom 空間・成分型の
  型不一致・退化 geometry data の vacuity で満たさない。
- `target route integrity gate`: geometry package・`geomTransportAlong`・
  負例・witness の provenance を G-101 reviewed artifact、Formal 成分型、
  canonical 構成、opcartesian 普遍性へ追跡する。identity 射だけ・退化
  geometry data(site 空・cover なし・係数零環・raw system 空)だけの
  発火、one-way-as-equivalence、proof 後の GOAL 読み替えを completion に
  使わない。
- `target failure policy`: 次の三分岐で扱う。
  (1) 追加仮定なしの (ii)(canonical 輸送の無条件構成)の不成立が
  `FiniteModel` 上の Lean 反例で証明された場合に限り、statement の
  「存在条件の同定+条件付き構成」形(G-110 (B) と同じ三点セット)への
  改訂を**ユーザー裁定へ**提案する。改訂はカード再固定と tracking
  Issue 記録を経るまで発効せず、この経路自体を改訂前後いずれの
  statement の `target-theorem-proved` にも数えない。
  (2) 仕様した射クラス(exact `σ` 上の core 総圏射)の**全て**に対して
  geometry lift が存在すると証明された場合(= (v) の負例が存在しない)、
  それは本カードの仕様欠陥(hom 定義が realization を実質参照して
  いない)または塔設計の簡約定理のどちらかであり、lift 常時存在定理を
  成果として固定した上で GOAL 改訂案(hom 定義の realization 参照
  強化を含む)をユーザーへ返す。この場合も完了とは数えない。
  (3) 構成が `H_geom` の同定に至らず停滞する場合は `target-blocked`。
  claim boundary 外の機構(段横断・2-cell)が必要と判明した場合は
  本 GOAL を改訂せず G-109 へ送り、本カードは `target-blocked` として
  完了に数えない。
