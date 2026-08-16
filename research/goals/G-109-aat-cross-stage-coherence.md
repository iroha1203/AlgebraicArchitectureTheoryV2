# G-109-aat-cross-stage-coherence — 段横断輸送整合と障害合成

- `id`: `G-109-aat-cross-stage-coherence`
- `status`: `active`
- `priority`: `high`
- `research mode`: `target-theorem`
- `program context`: 登路上の位置は **Gr3 後半(Gr3 完成)**(n1005
  §5「隊列」第5項の Gr3 分解)。G-106 は Gr3 の 2-障害核、G-108 は塔
  上層の建設であり、**本カード完遂をもって初めて Gr3(擬関手的整合)
  達成と記録する**(n1005 §4.6 の分割)。隊列裁定(2026-08-15、
  Gr3/Gr4 系列先行)の第二手。依存先 G-108 は完遂済み
  (`target-theorem-proved`、2026-08-16。fixed GOAL 無改訂のまま完走
  したため下記の伝播規定は発動していない)であり、着手条件は満たされて
  いる。**G-108 の
  statement が改訂された場合、本カードは draft へ差し戻して再固定
  する**(依存カードの伝播規定)。本カードは n1005 §2 の測量台帳に
  対応行を持たず、達成階梯(Gr3)の帳簿に専属する(帳簿の二重性の
  明示)。
- `predecessor`: G-101(core 段輸送と opcartesian 普遍性。
  `research/lean/ResearchLean/AG/AtomFoundation/` 配下、unported)、
  G-108(geometry 段輸送。**完遂済み = `target-theorem-proved`、
  2026-08-16**。実装 PR
  [#4015](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4015)
  マージ済み(merge commit
  `12c3e6c2df266a108a43b66da785a1a369dcb896`、final reviewed head
  `a1d70d01`、standard+独立 formal の各4レーン全
  `No major findings`)、完了同期 PR #4016。再利用する宣言:
  `GeomRead_U` 総圏と `GeomReadHom`(固定7項 geometry hom contract —
  comparison family・cross-context read-preservation)、
  `geometryProjection`、`geomTransportAlong` / `geomTransportAlongHom`
  (canonical 輸送)、`geomTransportAlongHom_base`(射影可換)、
  `geomTransportAlongHom_isStronglyCocartesian`(partial op-cleavage)、
  `geomTransportAlong_liftUniqueUpToFiberIso`
  (`research/lean/ResearchLean/AG/GeometryTransport/` 配下、
  unported))、G-106
  (Transport Coherence Two-Obstruction Theorem: canonical
  comparator・raw defect・reselection orbit・消滅同値。
  `research/lean/ResearchLean/AG/TransportCoherence/` 配下、unported)。
- `tracking issue`: 未起票
  (active 昇格はユーザー裁定済み 2026-08-16。成立は本カード同期 PR の
  マージをもって。起票はマージ後、`$target-theorem-loop` 起動前に行う)
- `source note`: [docs/note/n1001_atom_is_all_you_need_discussion.md](../../docs/note/n1001_atom_is_all_you_need_discussion.md)(§3.3 塔、§3.5 達成階梯)、
  [docs/note/n1005_aat_semantic_geometry_route_after_g107.md](../../docs/note/n1005_aat_semantic_geometry_route_after_g107.md)(§4.6、§5 隊列第5項)、
  [G-106 report](../reports/G-106-aat-transport-coherence.md)(frontier
  観察の消化記録: 段横断拡張は「cartesian 相互作用・段横断合成」を
  frontier に留めたのみで、statement 設計を変える新観察はなかった —
  2026-08-16 確認。witness 構成法(S3 非可換核・閉配置)は Cycle 4/5 の
  FiniteWitnesses を本カードの素材として引き継ぐ)
- `確定事項`: 次の5点を固定する(G-106 の確定事項様式に従う)。
  (1) **上段障害語彙の建設義務**: 押し出しの始域となる geometry 段の
  障害語彙は既存カードのどれも建設していないため、**本カードが建設
  する** — G-108 の総圏 `GeomRead_U` の上に、G-106 と同じ次数契約
  (有限 presentation、2-cell = 平行 path 対の宣言関係、3-cell = 宣言
  syzygy の有限族、reselection = 辺ごとの fiber 自己同型割当)で
  admissible 比較データ・raw defect・orbit 述語を定義する。G-106 の
  core 段語彙は参照のみで改変しない。
  (2) **押し出しの型**: 段射影に沿って上段の raw defect を下段の
  fiber 自己同型へ写す写像として構成し、canonical comparator の保存と
  edge reselection(coboundary)作用との両立を証明義務に含める。
  (3) **合成公式は等式**: 全体障害 = 段間障害と押し出された段内障害の
  合成(積の順序は温度順で固定し、カード内で一意に読めるよう statement
  時に明記する)。**段横断消滅述語の唯一の provenance は「押し出し
  cochain の全体 orbit 所属」**であり、これ以外の conjunct の混入を
  audit 対象とする。
  (4) **段の範囲**: 非自明 fiber を持つ段2段(geometry 段+core 段)を
  対象の下限とする。`ExtInst_U -> Doct_U` の fiber は離散
  (`ExtInstHom` は `doctrineHom` で完全決定)であり障害語彙が恒等的に
  自明化するため、witness にも claim にも数えない。
  (5) **witness shape**: G-106 確定事項 (5) の閉配置要求を継承する
  (単一 2-cell のみの非消滅主張は認めない)。
- `research aim`: 輸送が**塔の段をまたいで**合成することを定理にする。
  G-106 は単一射影(core 段)内の輸送合成 coherence と 2-障害を固定した。
  本カードはこれを塔 `GeomRead -> CoreRead -> ExtInst -> Doct` の複数段へ
  拡張する — (i) 段横断の canonical 輸送合成が擬関手的に整合すること
  (正例)、(ii) 段内 2-障害が段射影に沿って押し出され、段間の障害と
  合成して全体障害を与えること(合成公式)、(iii) 各段内では消える
  障害が段横断合成でのみ非消滅となる witness の実在。これで「輸送が
  段横断に合成する」(Gr3 の定義、n1001 §3.5)が比喩から定理になる。
- `core tension`: 段ごとの canonical 選択が各段内で coherent であること
  (G-101 / G-106 / G-108)と、それらが**段をまたいで**整合することの
  間には、押し出しの自然性という新しい証明義務が挟まる。障害の押し出しが
  coboundary 作用(reselection)と両立しなければ orbit 語彙が段横断で
  壊れ、両立するなら「どの段で障害が発生したかを常に特定できる」
  (n1001 §3.3 の設計目標)が障害語彙込みで成立する。段内消滅・段横断
  非消滅の witness は、pairwise 可能・joint 不可能(G-106 三角形)の
  段方向版であり、その実在が塔設計の非自明性を担う。なお witness に
  非離散上段が**論理的に必要**である理由は確定事項 (4) の ExtInst 段
  離散性にある — これが本カードが G-108(geometry 段)の完遂に依存する
  実質的根拠である。
- `rival`: pseudofunctor / lax functor の合成整合の一般論(mathlib の
  2-圏系)、G-106 単体(単一射影内)、fibration の合成に関する古典
  事実。差は「AAT の塔の具体的な段射影の族に対し、障害の押し出し・
  合成公式・段横断 witness まで Lean で固定する」点に置く。
- `claim boundary`: G-101 / G-108 で建設済みの塔の段(geometry 段・
  core 段・`ExtInst` / `Doct`)と、その間の射影 functor、G-106 の有限
  presentation・admissible 比較データ・raw defect・reselection orbit を
  対象とする。`ObProblem` 段(class の naturality)、carrier を動かす
  主張、doctrine 圏の fiber product(G-110)、nerve / cover 接続、
  無限段の塔は含めない。syzygy 整合は G-106 と同じく
  direction-hypothesis として扱い、無条件化しない。
- `capability categories`: coherence、obstruction-pushforward、
  composition-formula、counterexample、unification。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に
  置き、固定 statement と completion criteria だけで完了判定する。
- `portfolio constraint`: 正例(段横断 canonical coherence)だけ、または
  witness だけで完了扱いしない。正例・押し出し・合成公式・witness の
  四面の Lean artifact 接続を要求する。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、反証なら
  `target-refuted`、全完了条件と final review を満たした場合だけ
  `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各 cycle は
  proof obligation delta で評価する。
- `dullness filter`: 次を弾く。単一段だけの図式での発火(G-106 の
  再証明)、**非自明 fiber を持つ段が2段未満の図式での発火**(離散段の
  水増しによる「段横断」主張を含む)、押し出しを identity 射影に
  取って合成公式が自明化する構成、
  障害の押し出しを structure field で受け取る構成、段横断 witness が
  実は単一段内で既に非消滅である構成(G-106 witness の再ラベル)、
  2-cell を持たない図式での vacuous な整合、syzygy 整合を暗黙に無条件
  使用する構成、押し出しと reselection の両立を主張せず合成公式だけ
  立てる成果、一般 pseudofunctor 合成の再証明だけで塔接続を欠く成果。
- `frontier`: 段横断の H² 語彙の観察、`ObProblem` 段への拡張
  (class naturality と G-110 (D) への接続)、統合正方形の族の合成整合
  (n1005 §3)への供給、cartesian 側 lift との相互作用。

- `target theorem`: **Cross-Stage Transport Coherence and Obstruction
  Composition Theorem**。G-101 / G-106 / G-108 の設定の上で:
  1. **(i) 段横断 canonical coherence(正例)**: 隣接する段射影の対に
     対し、canonical 輸送(G-101 `transportAlong`・G-108
     `geomTransportAlong`)の段内合成と段間持ち上げの canonical 比較
     同型を構成し、三段までの隣接合成 coherence(擬関手的整合)を
     opcartesian 普遍性から証明する。
  2. **(ii) 上段障害語彙の建設と押し出し**: 確定事項 (1) に従い、
     geometry 段(G-108 の `GeomRead_U`)上の有限 presentation・
     admissible 比較データ・raw 2-cell defect・reselection orbit を
     **本カードで定義**した上で、段射影に沿った押し出し写像(上段
     raw defect → 下段 fiber 自己同型)を構成し、それが canonical
     comparator を保ち、edge reselection(coboundary)作用と両立する
     ことを証明する。
  3. **(iii) 合成公式(等式)**: 全体障害 = 段間障害と押し出された
     段内障害の合成、を**等式**として証明する(積の温度順は statement
     固定時に一意に明記する。片方向包含への弱化は改訂扱い)。段横断
     消滅述語は**「押し出し cochain の全体 orbit 所属」のみから定義**
     し(確定事項 (3) の唯一 provenance)、定義展開で放電しない。
  4. **(iv) 段横断 witness**: 各段内では reselection orbit で消滅する
     (段内 coherent 化可能)が、段横断合成では非消滅となる閉配置
     witness を `FiniteModel` の carrier 上で構成する。あわせて
     canonical 選択のみの図式では段横断でも消滅すること(正例側)を
     対で固定する。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/CrossStageCoherence/` 配下(新設)。
  G-106 の TransportCoherence モジュール・G-108 の GeometryTransport
  モジュールは参照のみ(改変しない)。完了面は (i)–(iv) まで。段数は
  有限(claim は三段までの隣接合成で固定し、一般有限段は frontier)。
  syzygy 整合の無条件化・`ObProblem` 段・fiber product は主張しない。
- `target proof artifacts`: geometry 段障害語彙の定義一式(有限
  presentation・admissible 比較データ・raw defect・orbit。確定事項
  (1))とその非自明性 witness、段横断比較同型の構成と coherence
  theorem、押し出し写像の定義と canonical comparator 保存 theorem、
  押し出しと reselection の両立 theorem、合成公式 theorem(等式)、
  段横断消滅述語の定義(全体 orbit 所属のみから)、
  段内消滅・段横断非消滅 witness(FiniteModel 上、非恒等輸送・非空
  2-cell 幾何)、canonical 図式の段横断消滅(正例)theorem、report
  `research/reports/G-109-aat-cross-stage-coherence.md`。
- `target proof strategy`: F0 段射影対の固定と段間持ち上げの型付け ->
  F1 段横断 canonical 比較同型と coherence(G-106 J0 の方法の段横断化)
  -> F2 押し出し写像と保存・両立 -> F3 合成公式と段横断消滅述語 ->
  F4 witness 対(非消滅+正例)。既存成果の利用 map: G-101 opcartesian
  一意性(比較同型の生成)、G-106 `canonicalTwoCellComparator` /
  `rawTwoCellDefect` / `InReselectionOrbit` /
  `transportObstructionVanishes_iff_coherentizable`(障害語彙と同値の
  素材)、G-108 `geomTransportAlongHom_base`(射影可換、段間持ち上げの
  整合)、G-106
  `FiniteWitnesses` の S3 witness 構成法(witness 素材)。固定
  statement と完了条件は本カードのみを正本とする。
- `target theorem completion criteria`: 全 artifact が sorry なしで
  `ResearchLean` に受理され、axiom / placeholder audit が clean である
  こと。下記 ledger の `discharge-required` を放電し、audit で
  provenance、proof-use、structure-field escape、route integrity を監査
  すること。Lean / report / tracking Issue を同期し、final review packet を
  作り、
  `$math-lean-review research/goals/G-109-aat-cross-stage-coherence.md G-109-aat-cross-stage-coherence`
  の4査読がすべて `No major findings` であること。**完遂時に Gr3
  達成を report へ記録する**(G-106+G-108+本カードの三点セット。
  n1005 §4.6 の誤記予防)。
- `target premise discharge policy`: 入力(塔の段データ、doctrine 図式、
  admissible 比較データ)だけを残せる。比較同型、coherence、押し出しの
  well-definedness と両立、合成公式、witness はすべて completion までに
  生成・証明する。syzygy 整合だけを direction-hypothesis として残す
  (G-106 の扱いを継承)。
- `target material premise ledger`:
  - `carrier U / FiniteModel`: `ambient-boundary`。witness 計算のみ。
  - `G-101 / G-108 の輸送と普遍性`: `ambient-boundary`。reviewed 済み
    定理の参照のみ。段横断の coherence を各段の statement に含めない。
  - `G-106 の障害語彙(raw defect / reselection / orbit / 消滅同値)`:
    `ambient-boundary`。参照のみ、改変しない。押し出しの存在・両立を
    G-106 側の field に入れない。
  - `syzygy 整合(SyzygyCompatible)`: `direction-hypothesis`。3-cell
    cocycle 語りにのみ使用し、(i)–(iv) の主定理はこれに依存させない
    (依存する系は仮定明示で分離する)。
  - `geometry 段障害語彙の建設(確定事項 (1))`: `discharge-required`。
    定義(有限 presentation・admissible 比較データ・raw defect・
    orbit)と、その非自明性 witness(退化 presentation での vacuous
    発火を認めない)を本カードで放電する。
  - `段横断比較同型と coherence`: `discharge-required`。opcartesian
    普遍性からの生成のみを認める。
  - `押し出しの保存・両立 / 合成公式(等式)`: `discharge-required`。
  - `段横断消滅述語の provenance`: `discharge-required`。定義は
    「押し出し cochain の全体 orbit 所属」のみから立てる(確定事項
    (3) の唯一 provenance)。これと独立な追加 conjunct の混入、および
    orbit 述語の言い換えを審査対象にする。
  - `witness 対`: `discharge-required`。段内消滅の明示 gauge と段横断
    非消滅の証明を両方含める。
- `target anti-weakening rule`: 結論相当の仮定(coherence、押し出しの
  両立、合成公式、witness の非消滅)を theorem argument、typeclass、
  structure field、certificate field へ移して成功扱いしない。段横断
  消滅述語を「各段で消滅」の連言として定義することを禁じる(それは
  (iv) の witness が排除すべき混同そのもの)。(iii) の合成公式を
  片方向の包含へ弱めた場合は改訂として扱い、成功に数えない。
- `target route integrity gate`: geometry 段障害語彙・押し出し写像・
  合成公式・witness の provenance を G-106 / G-108 reviewed artifact、
  canonical 構成、opcartesian 普遍性、concrete witness へ追跡する。
  離散段の水増し・identity 射影だけの発火・退化 presentation だけの
  発火、one-way-as-equivalence、proof 後の GOAL 読み替えを completion に
  使わない。
- `target failure policy`: (ii) の押し出しが reselection と両立しない
  ことが証明された場合は `target-refuted` ではなく、両立する部分語彙
  (共役類水準など)への statement 改訂を提案する(G-106 の class
  語彙が下位互換の受け皿)。(iv) の witness が構成できず、段横断合成が
  常に段内消滅へ還元されると証明された場合は、その還元定理を成果として
  `target-refuted` を宣言する(塔設計の簡約という負の大発見として
  記録)。停滞は `target-blocked`。
