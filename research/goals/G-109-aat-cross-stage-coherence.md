# G-109-aat-cross-stage-coherence — 段横断輸送整合と障害合成

- `id`: `G-109-aat-cross-stage-coherence`
- `status`: `active`
- `priority`: `high`
- `research mode`: `target-theorem`
- `program context`: 登路上の位置は **Gr3 後半(Gr3 完成)**(n1005
  §5「隊列」第5項の Gr3 分解)。G-106 は Gr3 の 2-障害核、G-108 は塔
  上層の建設であり、**本カード完遂をもって初めて Gr3(擬関手的整合)
  達成と記録する**(分割の正本 = n1005 §5 隊列第5項、§4.6 は
  誤記予防の出典)。隊列裁定(2026-08-15、
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
  [G-106 report](../reports/G-106-aat-transport-coherence.md)
  (G-106 カードの frontier 記述と report を突合し、段横断に関する
  statement 設計を変える観察が report 側に存在しないことを 2026-08-16
  に確認。witness 構成法(S3 非可換核・閉配置)は Cycle 4/5 の
  FiniteWitnesses を本カードの素材として引き継ぐ。G-108 カード
  frontier の次数契約観察は確定事項 (1) で消化)
- `確定事項`: 次の5点を固定する(G-106 の確定事項様式に従う)。
  (1) **上段障害語彙の建設義務と次数契約**: 押し出しの始域となる
  geometry 段の障害語彙は既存カードのどれも建設していないため、**本
  カードが建設する**。所属は**合成射影 `GeomRead_U -> ExtInst_U` の
  ファイバー**に置く — 2-cell 比較データの base 等式は ExtInst 水準
  (平行 path の core 合成の `ExtInstHom` base の一致のみを要求し、
  core 合成自体の一致は要求しない)、comparator / raw defect の値は
  **合成ファイバー自己同型群**(geometry 段の `Aut` に base 条件
  `α.hom.base.base = 𝟙` を課した subgroup。本カードで新設)に取る。
  これにより部分群系列「段内群(core 恒等条件 `α.hom.base = 𝟙`)⊂
  合成群」と、押し出し先 core 段 `packageFiberAutSubgroup` が成立し、
  (2) の押し出しが非自明でありうる。G-106 の厳密 core ファイバー
  (base = 恒等)への字義的複製は押し出しが恒等定数に退化するため
  **採らない**(G-108 カード frontier「2-cell 語彙を geometry 段に
  載せる場合の次数契約の観察」の消化 — 2026-08-16 裁定)。有限
  presentation・2-cell = 平行 path 対の宣言関係・3-cell = 宣言 syzygy
  の有限族・reselection = 辺ごとの fiber 自己同型割当という次数骨格は
  G-106 に従う。あわせて **strict 段内語彙**を **proper
  sub-presentation** として建設する — 2-cell base 等式を
  `PackageTotalHom` 水準に強めた strict sub-presentation 上の `H_G`
  値 defect と `H_G` gauge orbit(G-106 の字義的な geometry 段版。
  押し出しが恒等になるのはこの語彙の構造であり欠陥ではない)。
  **同一 data 解釈は採らない** — total と同じ comparator / raw
  cochain に strict 消滅を適用すると `H_G ↪ C_G` の包含で joint 消滅
  が従い、負例が不可能になる。proper sub-presentation 解釈の空虚化を
  防ぐため、**bridge package を建設義務に含める**: 埋め込み
  `StrictTwoCell ↪ TotalTwoCell`、path / comparator / raw の
  restriction theorem、両 gauge 作用の equivariance、strict 部分の
  非空・閉・非退化性 witness(strict 側に非恒等 defect が実在し、
  その消滅が実仕事であること)、coverage 条件(total の 2-cell が
  strict 部分と core-active 部分で覆われ、joint failure が両部分の
  相互作用に局在すること)。strict 語彙は (iv) の pairwise 判定の
  geometry 成分に使い、`C_G` 語彙は合成公式と joint 判定に使う
  (役割分離)。admissible 比較データは**二層**とする — edge ごとに
  geometry 段(`geometryProjection`)と core 段(`packageProjection`)
  の両方の強 opcartesian 証書を入力として持つ(入力データの資格条件で
  あり、結論の仮定化ではない)。**geometry 段の消滅同値 theorem は
  section-相対で建設する** — stage-local obstruction は total cochain
  ではなく (3-b) の section 相対 inner cochain(段内障害、`H_G` 値)
  であり、orbit 述語と独立な **`SectionRelativeCoherentAt`**
  (section 座標で authored comparator が左右 path lift を実際に
  factor する path equation。量化順は statement で固定)を定義した
  上で、その成立 ⟺ `H_G` gauge orbit 消滅を cancellation /
  opcartesian uniqueness による**非定義的 theorem** として証明する
  (`Iff.rfl` 級の定義的同値は放電と認めない。G-106 (iii)
  `transportObstructionVanishes_iff_coherentizable` の相対版)。total
  cochain への直訳は `H_G ⊂ C_G` の orbit 包含により (iv) の witness
  と両立しないため採らない。これを欠くと orbit 述語が 2-障害を名乗る
  意味論的な錨を持たない。G-106 の core 段語彙は参照のみで
  改変しない。
  (2) **押し出しと群拡大の型**: 群の記号を固定する — `C_G` :=
  合成ファイバー自己同型群((1))、`H_G` := 段内群(core 恒等条件
  `α.hom.base = 𝟙`)、`B_G` := core 段 `packageFiberAutSubgroup`、
  `p : C_G →* B_G` := `geometryProjection` が誘導する群準同型
  (押し出し)。定義より `H_G = ker p` であり、群拡大
  `1 -> H_G -> C_G -> p(C_G) -> 1` が成立する。したがって
  「`H_G` 値の障害の押し出しは恒等」は欠陥ではなく構造であり、押し
  出しが運ぶのは `C_G` 値の全体障害、合成公式は (3) の二部構成で
  立てる(採る型 = kernel-coset with supplied section。crossed-module
  一般論は建てない)。`p` の構成、canonical comparator の保存、edge
  reselection(coboundary)作用との両立を証明義務に含める。**`p` の
  非恒等性は一般量化側((ii)(iii))には含めない** — 群拡大は
  `p(C_G) = 1` の presentation を契約上排除しないため、一般側は `p`
  の構成・`H_G = ker p`・像への exactness・保存 theorem までとし、
  非恒等性は (iv) の fixture 存在 witness に限定する。core gauge の
  geometry への持ち上げ(`p` の section)は一般には仮定せず、(3-b)
  の辺水準 section family としてのみ扱う。あわせて**合成射影の型を
  固定する** — 合成射影 `geometryProjection ⋙ packageProjection` を
  宣言し、二層 local 強 opcartesian 証書から合成射影の強 opcartesian
  性を導く theorem、edge から path への composite closure、そこから
  生成する `C_G` canonical comparator を建設義務に含める(合成証書の
  input field 化は禁止のまま)。
  (3) **合成公式は二部構成・三項の定義固定**: 乗法規約を先に固定する
  — defect の積は G-106 実装規約(`rawTwoCellDefect = u * φ⁻¹`、
  underlying は `φ.inv ≫ u.hom`)をそのまま使う。**全体障害** :=
  `u * φ⁻¹`(authored 比較データ `u` と合成 canonical comparator `φ`
  の差、`C_G` 値)。**段間障害** := 射影されたデータに対する core 段
  (G-106 語彙そのまま)の raw defect(`B_G` 値)。
  **(3-a) 射影公式(無条件)**: `p(全体障害) = 段間障害` を `B_G`
  上の等式として証明する(defect の射影 functoriality)。
  **(3-b) kernel 分解(供給条件付き)**: 供給 datum は**辺水準の
  section family** — **型付けした core 辺値の族 `b_e`**(core 射影の
  辺データとして型を持つ)と、各辺の fixed-endpoint geometry 持ち上げ
  `m_e ∈ C_G`・射影等式 `p(m_e) = b_e` の族(**本カード新設の明示
  datum**。G-108 の `HGeom` は forward supply であり fixed-endpoint
  invertible lift を直接は与えないため、供給根拠に流用しない)。
  2-cell 水準の `m` は辺 family の pasting で生成する。alignment は
  辺 data だけからは導けない(authored `u` を `g * u`(`p(g) ≠ 1`)に
  替えても辺 data は不変)ため、supply に **core alignment 述語**
  `CoreAlignmentAt` を含める — 射影された authored comparator が core
  辺 gauge `b` に沿って射影 edge lift を実際に factor するという
  category-level の path equation(orbit 述語・結論と独立)。そこから
  opcartesian uniqueness により各 2-cell で `p(m) = p(u)` を
  **theorem として**導く(これが「段内障害 ∈ `H_G`」と
  「`p(s(段間障害)) = 段間障害`」の双方の型を放電する。`p(m) = p(u)`
  を conclusion-equivalent field として直接受け取ること、および
  `m := u` と取って段内障害を自明化する経路は completion に数え
  ない)。kernel 分解は alignment が成立する `(u, b)` 対の範囲で
  主張する。`s(段間障害)` := `m * φ⁻¹`、**段内障害** := `u * m⁻¹`
  (`H_G` 値に落ちることは alignment 由来の `p(m) = p(u)` theorem
  から従う)と独立の comparator
  差で定義した上で、
  `全体障害 = 段内障害 * s(段間障害)` を `C_G` 上の**等式**として
  証明する(因子順は乗法規約から `u φ⁻¹ = (u m⁻¹)(m φ⁻¹)` として
  一意に決まる)。section family の取替えは**同じ `b` を持ち上げる
  family の間**に量化し、その取替えは辺 generated な
  `H_G`-coboundary であり、段横断 gauge orbit 所属を変えないこと
  (well-definedness theorem。**辺水準に制限するからこそ coboundary
  性が theorem になる** — 任意 2-cochain 水準の取替え不変は主張
  しない)を証明義務に含める。**一般形は供給条件付きだが、canonical
  route と (iv) の正例側 fixture では section family と alignment を
  具体構成して放電する — 仮定付き分解だけを Gr3 完成根拠にしない。
  負例 fixture には section の存在を要求しない(非持ち上げが機構で
  あるため — 確定事項 (5))**。(3-b) の
  pasting 等式単独は成果に数えない — 内容は (3-a)・kernel 所属・
  well-definedness・(iv) witness が担う。
  **(3-c) 条件付き cocycle(候補17 の「2-障害込み」の閉包)**:
  geometry / 合成水準の typed pasting evaluator を建設し、
  `SyzygyCompatible` 条件付きの total cocycle theorem(G-106
  `rawDefect_cocycle_of_syzygy` の `C_G` 版)と、`p` が pasting /
  cocycle 等式を保存する theorem を証明する(syzygy 整合は G-106 と
  同じく direction-hypothesis のまま。一般 H² 分類は frontier)。
  **段横断消滅述語の唯一の provenance は「全体障害 cochain の段横断
  gauge orbit 所属」**(`C_G` 水準)とする。段横断 gauge = 辺ごとの
  `C_G` 割当(その押し出しが core 辺 gauge を与える)。これ以外の
  conjunct の混入、および三項の逆算定義(各項の独立 provenance —
  authored data / supplied section family / canonical — を欠く導入)を
  audit 対象とする。
  (4) **段の範囲と量化域**: 非自明 fiber を持つ段2段(geometry 段+
  core 段)を対象の下限とする。`ExtInst_U -> Doct_U` の fiber は離散
  (`ExtInstHom` は `doctrineHom` で完全決定)であり障害語彙が恒等的に
  自明化するため、witness にも claim にも数えない。(ii)(iii) は一般
  carrier `U` 上の段横断有限 presentation 全体で量化し、witness
  ((iv))のみ `FiniteModel` 具体化とする(G-106 確定事項 (2) の
  regime 様式)。
  (5) **witness shape**: G-106 確定事項 (5) の閉配置要求を継承する
  (単一 2-cell のみの非消滅主張は認めない)。witness fixture は
  geometry 段 fiber 自己同型群の非自明元を要する(既存 fixture には
  存在しないため、対称 carrier を持つ geometry package の新 fixture
  建設を含む。非恒等 base による水増しは (1) の base 条件が排除)。
  消滅述語の**完全型**を先に固定する:
  `CoreVanishes` := 段間障害が core 段 `B_G` gauge orbit(G-106
  語彙)で消滅。
  `InnerVanishesAt m` := aligned section `m` に相対な段内障害が
  `H_G` gauge orbit で消滅。
  `JointVanishes` := total cochain が段横断 `C_G` gauge orbit で
  消滅。
  `CompatiblePairwiseVanishes` := ある core trivializer `b`・それを
  持ち上げる aligned section `m`・`InnerVanishesAt m` が**同時に**
  存在。
  正例 theorem は **`JointVanishes ⟺ CompatiblePairwiseVanishes`**
  (joint gauge の分解と合成、両方向とも非自明)。**注意**:
  `InnerVanishesAt m` は section gauge との逐次合成(G-106 の
  reselection は厳密に合成する)により `JointVanishes` を含意する
  ため、**負例の pairwise 成分に使うことは禁じる**。同じ理由で
  total cochain 自体の `H_G` orbit 消滅を「段内消滅」と定義する
  ことも禁じる(`H_G ⊂ C_G` の orbit 包含)。負例の pairwise の
  geometry 成分は **section 非依存の strict 段内語彙**((1) の
  proper sub-presentation、bridge package で total と接続)で測る。
  joint compatibility failure は **trivializer の fiber product** で
  直接測る — `CoreTrivializers`(段間障害を消す `B_G` gauge の集合)
  と `StrictTrivializers`(strict restriction 上の `H_G` gauge の
  集合)が**個別には inhabited** でありながら、compatible lift の
  fiber product(`CompatiblePairs`)が**空**であること。
  `CompatiblePairwiseVanishes` はこの fiber product の非空性として
  定義し、正例 theorem `JointVanishes ⟺ CompatiblePairwiseVanishes`
  と整合させる。負例 witness の形は
  **`CoreVanishes ∧ strict 段内消滅(strict restriction 上、非空虚)
  ∧ ¬JointVanishes`** とし、機構は**非 liftable core trivializer** —
  同一 fixture 上で、すべての core trivializer に aligned section が
  存在しないことの有限検査と、それが `¬JointVanishes` へ接続する
  theorem を**必須**とする(optional にしない)。fixture は
  **`段間障害 ≠ 1`** を満たす(恒等 gauge を trivializer から排除
  し、恒等 core trivializer の恒等 lift による機構崩壊を防ぐ)。この
  負例 fixture に core killer の aligned `C_G` section を同時要求
  してはならない。**witness
  義務は同一 fixture に結合する**: 押し出し非恒等性・pairwise 消滅
  (`CoreVanishes`+strict 段内消滅)・`¬JointVanishes`(全 core
  trivializer の aligned section 非存在の有限検査込み)は、同一の閉
  fixture 上で同時に成立させる(strict 段内消滅はその strict
  restriction 上で判定し、(1) の bridge package で total と接続
  する)。fixture は実 cover・非零係数・非退化
  raw system を持つ(site・係数を含む Gr3 記録の資格。係数を identity
  scalar map で保つ場合はその scope を fixture 資格に明記する)。
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
  core 段・`ExtInst` / `Doct`)と、段射影(`geometryProjection` /
  `packageProjection`)および `ExtInst -> Doct` の忘却 functor
  (Lean に不在のため本カードの新設建設義務、離散 fiber theorem
  込み — (i))、G-106 の有限
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
  立てる成果、(3-b) の pasting 等式単独を合成公式の成果として数える
  構成、一般 pseudofunctor 合成の再証明だけで塔接続を欠く成果。
- `frontier`: 段横断の H² 語彙の観察、`ObProblem` 段への拡張
  (class naturality と G-110 (D) への接続)、統合正方形の族の合成整合
  (n1005 §3)への供給、cartesian 側 lift との相互作用。

- `target theorem`: **Cross-Stage Transport Coherence and Obstruction
  Composition Theorem**。G-101 / G-106 / G-108 の設定の上で:
  1. **(i) 段横断擬関手的整合(正例)**: 底射は
     `∀ {X Y : ExtInst_U} (σ : X ⟶ Y)`(= `ExtInstHom`)で量化する
     — `σ.doctrineHom` と `σ.source_eq` の proof-use を statement で
     明示し、裸の `ExactDoctrineHom`+source object から canonical
     target を生成する既存 transport との比較は**別 theorem** として
     固定する。各底射に対する fiber 間 transport functor
     (canonical lift の vertical morphism への作用を含む)を構成し、
     compositor / unitor を **natural isomorphism** として与え、その
     自然性・associativity coherence(底射3本の pentagon 相当)・
     左右 unit triangle を opcartesian 普遍性から証明する(cleavage
     から誘導される pseudofunctor 構造の geometry 段版)。**底と
     fiber の型を固定する** — pseudofunctor の底は `ExtInst_U`
     (射 = `ExtInstHom`。`ExactDoctrineHom` 単独では pointed target
     が決まらないため)、fiber は合成射影 `GeomRead -> ExtInst` の
     fiber とし、transport functor の source / target fiber・
     compositor / unitor・projection comparison の domain / codomain
     をこの型で固定する(core 側 pseudofunctor も同じ底で取る)。あわせて
     **塔としての pseudonatural compatibility** を証明する — 各段
     fiber の射影 functor `P` と各底射 `σ` について、比較 natural
     isomorphism `P ∘ T^Geom_σ ≅ T^Core_σ ∘ P`(対象と vertical
     morphism の両方で自然)を構成し、この比較が compositor / unitor
     と整合すること(射影像の一致を含む)まで固定する。canonical
     lift 一本の base equality では代用しない。
     `ExtInst -> Doct` の忘却 functor(`obj := doctrine`、
     `map := doctrineHom`)と離散 fiber theorem を新設宣言として建設
     し、塔 `GeomRead -> Doct` の射影列を Lean 上で閉じる(離散段は
     非自明性計数に含めない — 確定事項 (4))。「三段まで」は底射の
     合成本数を指し、段射影の本数ではない。
  2. **(ii) 上段障害語彙の建設と押し出し**: 確定事項 (1) に従い、
     合成ファイバー上の有限 presentation・二層 admissible 比較
     データ・raw 2-cell defect・reselection orbit・**section-相対の
     消滅同値(相対 obstruction theorem)**を**本カードで定義・証明**
     した上で、確定事項 (2) の
     群拡大 `1 -> H_G -> C_G -> p(C_G) -> 1`・合成射影と合成強
     opcartesian theorem・composite closure を Lean 上で固定し、
     押し出し `p` が canonical comparator を保ち、edge reselection
     (coboundary)作用と両立することを証明する(`p` の非恒等性は
     ここでは主張しない — (iv)(c) の fixture 存在 witness に限定、
     確定事項 (2))。strict 段内語彙((1))もここで建設する。
  3. **(iii) 合成公式(二部構成+条件付き cocycle)**: 確定事項 (3)
     の三項定義と乗法規約の下で、**(3-a) 射影公式**
     `p(全体障害) = 段間障害` を `B_G` 上の無条件等式として、
     **(3-b) kernel 分解** `全体障害 = 段内障害 * s(段間障害)` を
     辺水準 section family の下での `C_G` 上の等式として証明する
     (因子順は乗法規約 `u φ⁻¹ = (u m⁻¹)(m φ⁻¹)` で一意。片方向
     包含への弱化は改訂扱い)。段内障害の `H_G` 所属 theorem と、
     section family 取替え(辺 generated `H_G`-coboundary)に対する
     well-definedness theorem(段横断 gauge orbit 所属の不変性)を
     含める。**(3-c)** typed pasting evaluator・`SyzygyCompatible`
     条件付き total cocycle theorem・`p` の pasting / cocycle 保存
     theorem を証明する。段横断消滅述語は**「全体障害 cochain の
     段横断 gauge orbit 所属」のみから定義**し(確定事項 (3) の唯一
     provenance)、定義展開で放電しない。
  4. **(iv) 段横断 witness(同一 fixture)**: 確定事項 (5) の完全型
     に従う。負例 fixture(単一の閉 fixture)上で、(a) **pairwise
     消滅** — `CoreVanishes` かつ strict 段内消滅((1) の strict
     語彙、section 非依存)、(b) **joint 不可能** —
     `¬JointVanishes` を、**すべての core trivializer に aligned
     section が存在しないことの有限検査**とその orbit 接続 theorem で
     証明する(必須。この fixture に core killer の aligned section
     を同時要求しない)、(c) 押し出し `p` の非恒等性(fixture 存在
     witness)、(d) `NontrivialSyzygyAt`(左右が異なる非空 pasting・
     実 2-cell face 使用・反射的 3-cell の排除を固定する Lean 述語)
     を満たす syzygy を含み、(3-c) の cocycle theorem が
     `SyzygyCompatible` を実使用して非空に発火する、を**同時に**固定
     する。正例側では、canonical 図式で `JointVanishes ⟺
     CompatiblePairwiseVanishes` を非空に発火させ((5) の正例
     theorem の非空検査)、(3-b) の section family と alignment を
     具体構成する(負例 fixture には要求しない)。canonical 選択のみ
     の図式では段横断でも消滅すること(正例側)を同一設定で対に
     する。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/CrossStageCoherence/` 配下(新設)。
  G-106 の TransportCoherence モジュール・G-108 の GeometryTransport
  モジュールは参照のみ(改変しない)。完了面は (i)–(iv) まで。段数は
  有限(claim は三段までの隣接合成で固定し、一般有限段は frontier)。
  syzygy 整合の無条件化・`ObProblem` 段・fiber product は主張しない。
- `target proof artifacts`: geometry 段障害語彙の定義一式(合成
  ファイバー上の有限 presentation・二層 admissible 比較データ・
  群 `C_G` / `H_G` / `B_G` と群拡大・raw defect・orbit。確定事項
  (1)(2))とその非自明性 witness、strict 段内語彙一式、
  `SectionRelativeCoherentAt` と `H_G` orbit 消滅の非定義的同値
  theorem(相対 obstruction theorem)、`CoreAlignmentAt` 述語と
  alignment 由来 `p(m) = p(u)` theorem(opcartesian uniqueness
  経由)、消滅述語の完全型4本(`CoreVanishes` / `InnerVanishesAt` /
  `JointVanishes` / `CompatiblePairwiseVanishes`)と正例 theorem
  `JointVanishes ⟺ CompatiblePairwiseVanishes`(fiber product 読み
  込み)、合成射影の宣言・二層証書からの合成強 opcartesian theorem・
  composite closure、strict 段内語彙の bridge package(埋め込み・
  restriction・equivariance・非空/閉/非退化性・coverage)、
  pseudofunctor–障害語彙一致 theorem 群(compositor 対象成分 =
  `C_G` canonical comparator・`p` 像 = core compositor・specialized
  = 一般 instance)、`ExtInstHom` 底射と canonical-target transport の
  比較 theorem、`NontrivialSyzygyAt` 述語、
  fiber 間 transport functor と compositor / unitor(natural iso)・
  pentagon 相当・unit triangle の各 theorem、段射影との pseudonatural
  compatibility theorem(fiber 射影 functor との比較 natural iso・
  vertical 自然性・compositor / unitor 整合)、`ExtInst -> Doct` 忘却
  functor と離散 fiber theorem、
  押し出し群準同型 `p` の定義と canonical comparator 保存 theorem、
  押し出しと reselection の両立 theorem、押し出し非恒等性 witness、
  三項定義と射影公式 theorem(3-a)・kernel 分解 theorem(3-b)・
  `H_G` 所属 theorem・well-definedness theorem、typed pasting
  evaluator と条件付き total cocycle theorem・`p` の pasting /
  cocycle 保存 theorem(3-c)、辺水準 section family と alignment の
  具体構成(canonical route・正例側 fixture)、段横断消滅述語の定義
  (段横断 gauge orbit 所属のみから)、負例 fixture 上の
  `CoreVanishes ∧ strict 段内消滅 ∧ ¬JointVanishes` witness
  (FiniteModel 上、geometry 段 fiber 自己同型群の非自明元・実
  cover・非零係数・非退化 raw・`NontrivialSyzygyAt` syzygy・
  `段間障害 ≠ 1` を持つ新 fixture、非空
  2-cell 幾何。`¬JointVanishes` は全 core trivializer の aligned
  section 非存在の有限検査+orbit 接続 theorem)、canonical 図式の
  段横断消滅と `JointVanishes ⟺ CompatiblePairwiseVanishes` の非空
  発火(正例)、report
  `research/reports/G-109-aat-cross-stage-coherence.md`。
- `target proof strategy`: F0 段射影対の固定と段間持ち上げの型付け
  (忘却 functor・離散 fiber theorem 含む) ->
  F1 fiber 間 transport functor と compositor / unitor・coherence law
  +段射影との pseudonatural compatibility
  (G-106 J0 の方法の段横断化+pseudofunctor 構造化)
  -> F2 群拡大・押し出し `p` と保存・両立 -> F3 射影公式(3-a)・
  kernel 分解(3-b)・well-definedness・条件付き cocycle(3-c)と
  段横断消滅述語 ->
  F4 同一 fixture の witness 対(非消滅+正例)。既存成果の利用 map: G-101 opcartesian
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
  達成を report へ記録する**(G-106+G-108+本カードの三点セット、
  分割の正本 = n1005 §5 隊列第5項、n1005 §4.6 の誤記予防)。記録には
  範囲根拠を併記する — Gr3 は輸送部分塔 `GeomRead -> Doct`(site・
  係数を含む段横断整合、n1001 の Gr3 註釈)についての達成であり、
  `ObProblem` 段(class naturality)と一般有限段は frontier に残る。
- `target premise discharge policy`: 入力として残せるのは次の一覧のみ
  (ledger と一対一対応): 塔の段データ・doctrine 図式・exact 底射
  (ambient-boundary)、二層 admissible 比較データ
  (direction-hypothesis、入力資格)、辺水準 section family
  (direction-hypothesis、**conclusion-equivalent risk あり** —
  canonical route と witness では具体構成して放電し、仮定付き一般形
  だけを完成根拠にしない)、syzygy 整合 `SyzygyCompatible`
  (direction-hypothesis、(3-c) と (iv)(d) にのみ使用)。比較同型、
  coherence、
  pseudonatural compatibility、押し出しの well-definedness と両立、
  射影公式、kernel 分解、cocycle theorem、witness はすべて completion
  までに生成・証明する。
- `target material premise ledger`:
  - `carrier U / FiniteModel`: `ambient-boundary`。witness 計算のみ。
  - `G-101 / G-108 の輸送と普遍性`: `ambient-boundary`。reviewed 済み
    定理の参照のみ。段横断の coherence を各段の statement に含めない。
  - `G-106 の障害語彙(raw defect / reselection / orbit / 消滅同値)`:
    `ambient-boundary`。参照のみ、改変しない。押し出しの存在・両立を
    G-106 側の field に入れない。
  - `syzygy 整合(SyzygyCompatible)`: `direction-hypothesis`。依存を
    許すのは **(iii)(3-c) と (iv)(d) のみ**(fixture 内では具体
    witness で放電し、proof-use を台帳に記録する)。(i)・(ii)・
    (iii)(3-a)(3-b)・(iv)(a)–(c) はこれに依存させない(依存する系は
    仮定明示で分離する)。
  - `geometry 段障害語彙の建設(確定事項 (1))`: `discharge-required`。
    定義(合成ファイバー上の有限 presentation・二層 admissible 比較
    データ・fiber 自己同型群と部分群系列・raw defect・orbit)と
    strict 段内語彙・消滅述語の完全型4本と正例 theorem・
    `SectionRelativeCoherentAt` 相対 obstruction theorem
    (非定義的)、
    その非自明性 witness(退化 presentation での vacuous 発火を
    認めない)を本カードで放電する。
  - `段横断比較同型と coherence`: `discharge-required`。opcartesian
    普遍性からの生成のみを認める。
  - `二層 admissible 入力(edge ごとの geometry / core 強 opcartesian
    証書・ExtInst 水準 base 等式・authored comparator)`:
    `direction-hypothesis`。入力データの資格条件として残す。合成強
    opcartesian 証書・canonical comparator 保存・reselection 両立・
    射影公式・kernel 分解を structure field で受けることは
    conclusion-equivalent escape として禁じる。
  - `辺水準 section family+core alignment(kernel 分解 (3-b) の
    供給 datum)`: `direction-hypothesis`。本カード新設の明示 datum
    (core 辺値 `b_e`・fixed-endpoint 持ち上げ `m_e ∈ C_G`・射影
    等式、および `CoreAlignmentAt` path equation)。
    **conclusion-equivalent risk を明示する** — canonical route と
    (iv) の正例側 fixture では具体構成して放電し、仮定付き一般形
    だけを Gr3 完成根拠にしない。負例 fixture には section の存在を
    要求しない(非持ち上げが機構)。(3-a) 射影公式・(i)・(iv) の非消滅
    側はこれに依存させない(依存する系は仮定明示で分離する)。
    G-108 `HGeom` は forward supply であり本 datum の供給根拠に
    しない。`replacement_is_coboundary` 相当を入力 field に置くことは
    certificate escape として禁じる(coboundary 性は辺水準制限からの
    theorem)。
  - `条件付き cocycle(3-c)`: `discharge-required`。typed pasting
    evaluator・`SyzygyCompatible` 条件付き total cocycle theorem・
    `p` の pasting / cocycle 保存 theorem を放電する(syzygy 整合
    自体は direction-hypothesis のまま)。witness の syzygy は
    `NontrivialSyzygyAt`(左右が異なる非空 pasting・実際の 2-cell
    face 使用・`threeLeft = threeRight` 型の反射的 3-cell の排除を
    固定する Lean 述語)を満たし、cocycle theorem の証明が
    `SyzygyCompatible` を実使用すること(proof-use 監査)を要求
    する。
  - `pseudofunctor と障害語彙の一致(unification)`:
    `discharge-required`。canonical cleavage を presentation へ
    instantiate したとき、`C_G` canonical comparator = compositor の
    対象成分、その `p` 像 = core compositor の対象成分、specialized
    raw cochain / orbit = 一般障害語彙の instance、となる一致
    theorem 群を放電する(G-106 (v) の specialized / unified 一致
    定理と同型の要求。両者を別々に証明するだけでは接続に数えない)。
  - `strict 段内語彙の bridge package(確定事項 (1))`:
    `discharge-required`。埋め込み・restriction theorem・gauge
    equivariance・非空/閉/非退化性 witness・coverage 条件を放電
    する。
  - `押し出しの保存・両立・非恒等性 / 三項定義と二部合成公式`:
    `discharge-required`。三項の定義は確定事項 (3) で固定した独立
    provenance(authored data / supplied section family / canonical)
    のみを
    認め、逆算定義(合成公式を定義的に真にする構成)を審査対象に
    する。
  - `段横断消滅述語の provenance`: `discharge-required`。定義は
    「全体障害 cochain の段横断 gauge orbit 所属」のみから立てる
    (確定事項 (3) の唯一 provenance)。これと独立な追加 conjunct の
    混入、および orbit 述語の言い換えを審査対象にする。
  - `witness 対`: `discharge-required`。段内消滅の明示 gauge と段横断
    非消滅の証明を両方含める。
- `target anti-weakening rule`: 結論相当の仮定(coherence、押し出しの
  両立、合成公式、witness の非消滅)を theorem argument、typeclass、
  structure field、certificate field へ移して成功扱いしない。段横断
  消滅述語を「各段で消滅」の連言として定義することを禁じる(それは
  (iv) の witness が排除すべき混同そのもの)。(iii) の合成公式を
  片方向の包含へ弱めた場合は改訂として扱い、成功に数えない。押し出し
  が恒等定数に退化する次数契約への差し替え(確定事項 (1) の base
  条件の変更)、段間障害・全体障害の逆算定義、および (3-b) の因子順の
  付け替え(共役への読み替え)も同様に改訂として扱う。段内消滅を
  total cochain の `H_G` orbit として定義すること(確定事項 (5) の
  禁止事項)、`p(m) = p(u)` を field として受け取ること、`m := u` に
  よる段内障害の自明化も成功に数えない。
- `target route integrity gate`: geometry 段障害語彙・押し出し写像・
  合成公式・witness の provenance を G-106 / G-108 reviewed artifact、
  canonical 構成、opcartesian 普遍性、concrete witness へ追跡する。
  離散段の水増し・identity 射影だけの発火・退化 presentation だけの
  発火、one-way-as-equivalence、proof 後の GOAL 読み替えを completion に
  使わない。
- `target failure policy`: 固定 target の中心 conjunct((i) の
  compositor / unitor 自然性・pentagon / triangle・tower
  compatibility、押し出しの保存・reselection 両立、射影公式、kernel
  分解、条件付き cocycle、witness の非消滅)の反証は
  `target-refuted` とする。段横断合成が常に段内消滅へ還元される
  universal reduction theorem の成立も `target-refuted` とする(塔
  設計の簡約という負の大発見として記録。ただし押し出し非恒等性
  witness の先行構成を要し、型選択の artifact による恒等退化還元は
  refute に数えない — それは goal defect であり loop 前に是正する)。
  両立する部分語彙(共役類水準など、G-106 の class 語彙が下位互換の
  受け皿)への改訂は、refute 判定の後に人間が再固定する別判断として
  分離する。停滞のみ `target-blocked`。
