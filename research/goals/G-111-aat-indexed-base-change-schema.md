# G-111-aat-indexed-base-change-schema — indexed base-change calculus と coherent diagnostic assembly の分類

- `id`: `G-111-aat-indexed-base-change-schema`
- `status`: `completed`
- `completion result`: `target-theorem-proved`。Indexed Base-Change
  Calculus and Coherent Diagnostic Assembly Classification Theorem の
  固定 target (a)–(g)(担当義務 O1–O4)を全放電
  ($target-theorem-loop Cycle 1–20、2026-08-26)。主要成果:
  (a) 全 `ExtractionInstance`・全 base 射・全可換 square を量化する
  diagnostic-free raw syntax(validated decoder 付き)と generated
  action、identity / composition・水平垂直 pasting・projection
  compatibility・path evaluation coherence、
  (b) canonical cleavage `coreFiberLift` との comparison(id / comp /
  paste coherence)+`indexedSquareTotalMap_isStronglyCocartesian`
  による strongly cocartesian 保存、
  (c) 診断語彙を含まない `IndexedBaseDiagram` /
  `IndexedBaseDiagramHom` と category API(path naturality は
  generating edge square から帰納生成)、
  (d) coherent diagram morphism 全域・source-fiber incidence 仮定
  なしの (d1)–(d6)(生成 target interpretation・endpoint
  `MonoidHom`・relation-relative data・mapped reselection・
  coherence 保存・vanishing 保存)、
  (e) G-110 実経路との C0–C3 制限比較(walking-arrow 化、direct /
  via-base functor と Beck–Chevalley mate の同定、成分三角形)、
  (f) 二層 raw-family 分類 — `uniformTargetBaseLiftableAt_iff_epi` の
  local iff、support-indexed vertexwise-epi sufficiency producer、
  非 epi coherent 正例、Cycle 7 non-liftable 負例、
  (g) named nontrivial diagnostic witness(非恒等 participating
  action・initial raw defect・source reselection、identity action と
  の具体成分差、同一 cell での (d4)–(d6) 発火)。
  standard PR review は fixed head で `Mergeable`
  ([PR #4181 コメント](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4181#issuecomment-5423215464))、
  same-head final packet
  ([PR #4181 コメント](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4181#issuecomment-5423250471))、
  独立 formal completion review(`$math-lean-review`)は4 lane 全て
  `No major findings`、formal completion ledger は全 completion gate
  pass・root recheck pass
  ([PR #4181 コメント](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4181#issuecomment-5423321232))、
  exact-head CI 7/7。tracking Issue の完了記録は
  [#4158 完了記録コメント](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4158#issuecomment-5423329411)
  で固定。fixed GOAL blob SHA `6541ee42`(SHA-256
  `cd372006a408707a262c24b81b590760ffb50ccc76f46f8ed80845cd60b7b3e4`)、
  final head `87278945`、完了 PR
  [#4181](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4181)
  (merge `8850a5b4`)。実装 PR 系列と cycle 履歴は tracking Issue
  #4158 を正本とする。公理監査は各 module の focused Lean check で
  standard axioms のみ pass、345件の宣言 map elaboration pass
  (Research aggregate / full build は hard rule に従い未実行)。
  **達成の記録の限定**: target `twoCellBase` は declared base
  relation(direction hypothesis)の canonical realization であり、
  raw family からの生成成果に数えない。(d1)–(d6) は source 側仮定
  (package・reselection・coherence・vanishing)相対の順方向定理。
  coherent domain は epi-only でない(非 epi 正例)が、arbitrary raw
  square family の自動 assembly は主張しない(Cycle 7 負例が分類の
  必須負枝)。**Gr4 達成の記録は本カードでは行わない** — 担当は
  O1–O4(Gr4 完遂 gate 第一項前半)のみで、coverage 分類・
  diagnostic conservativity / reflection・refinement 系統・上段
  lift・IsIso 水準 exchange-failure 存否決定は G-112〜G-116 に残る
  (program context)。`Formal/AG` への移植は未実施
  (porting status: `unported`)。
- `completed at`: `2026-08-26 JST`
- `priority`: `high`
- `research mode`: `target-theorem`
- `program context`: Gr4 完遂 gate 第一項前半の担当カード(担当義務 =
  O1–O4。義務台帳の正本は G-116、設計の source note は n1007
  §3–§5)。G-110 の finite-presentation BC を、(i) 全 base 射・全可換
  square 上の pointwise indexed calculus、(ii) coherent base diagram
  morphism 上の declared base relation に相対的な
  incidence-independent diagnostic assembly、(iii) raw
  square family の持上げ可能性分類へ展開する。G-113 へは本カードが
  定義する `IndexedBaseDiagramHom` とその diagnostic transport API を
  量化域として供給し、G-113 は再定義しない。O2 の cocartesian lift と
  G-112 の strong cartesian lift(O7)は別義務である。新設語彙
  `IndexedBaseDiagram` / `IndexedBaseDiagramHom` の命名権は本カード
  専属。G-111 の statement 改訂は G-113 と G-116 へ伝播する。
- `predecessor`: G-110(DoctrineFiberProduct、完遂済み
  `target-theorem-proved`)、G-101(opcartesian 普遍性)、G-106(raw
  defect / reselection 語彙)、G-109(core pseudofunctor API)。
- `tracking issue`: #4158(runtime state、cycle 履歴、fixed head、
  次 proof obligation の正本)
- `source note`: [n1007](../../docs/note/n1007_aat_sakura_gr4_completion_design.md)
  (§3–§5)、[n1005](../../docs/note/n1005_aat_semantic_geometry_route_after_g107.md)
  (§4.3 (D))、[G-110](G-110-aat-doctrine-fiber-product.md)。
- `research aim`: pointwise transport の全域性と、diagramwise
  diagnostic assembly の成立域を混同せずに Gr4 の O1–O4 を閉じる。
  任意の base 射・可換 square には indexed action と strongly
  cocartesian 保存を与える。一方、複数 square の target path relation
  を組み立てる入力は diagnostic-free な coherent diagram morphism と
  して明示し、その全域で (d1)–(d6) を証明する。target
  `twoCellBase` は target diagram の declared base relation の canonical
  realization であり、raw square family から生成したとは数えない。
  独立な raw square family から relation を一様に持ち上げる追加問題は、
  epi 条件の必要
  十分性・正例・負例で分類する。
- `core tension`: Cycle 7 は、等しい source path と二つの validated
  square だけから target path equality を一様生成できないことを有限
  反例で確定した。この反証は pointwise indexed calculus を否定せず、
  diagramwise coherence を raw square family から自動生成する主張を
  否定する。したがって target diagram の relation を診断 data の field
  や caller-supplied certificate に移さず、診断語彙を含まない base
  diagram geometry の direction hypothesis として provenance 付きで
  固定する必要がある。この相対性を diagnostic data の全生成と表示しない。
- `rival`: indexed category / Grothendieck fibration の一般論。差は、
  doctrine 塔の具体的な pointwise calculus、coherent diagram 上の診断
  assembly、raw-family liftability の epi 分類、G-110 実経路比較を
  一つの Lean package として固定する点に置く。
- `claim boundary`: 固定した一般 carrier `U`、`ExtInst_U`、
  `CoreFiber`、package 総圏の上で語る。係数、carrier、終対象、絶対積、
  cross-universe exact reindexing、`J_A` defect profile、derived 系は
  動かさない。保守性・反射・検出は G-113、strong cartesian lift は
  G-112 の担当。任意の独立 raw square family が target diagram morphism
  をなすとは主張しない。
- `capability categories`: schema-construction、base-change、
  diagnostic-covariance、classification、closure。
- `threshold policy`: SCORE は使わない。固定 statement と completion
  criteria だけで判定し、runtime state は tracking Issue に置く。
- `portfolio constraint`: pointwise schema だけ、epi 分類だけ、
  (d1)–(d3)だけでは完了としない。O1–O4、C0–C3、(d1)–(d6)、非 epi
  coherent positive、Cycle 7 負例、非自明 diagnostic witness を全て
  要求する。非 epi positive は coherent domain が epi-only でないこと
  だけを支え、非 epi 性が diagnostic 発火の原因であるとは主張しない。
  diagnostic witness は別義務であり、両者を相互代替しない。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、
  反証なら `target-refuted`、全完了条件と final review を満たした場合
  だけ `target-theorem-proved`。
- `reward rubric`: `not-applicable (target-theorem mode)`。
- `dullness filter`: diagnostic-free diagram を
  `AdmissibleTransportData` や `DiagnosticPackageTotalAction` の
  wrapper として定義する構成、target diagnostic data・coherence・
  vanishing を field で受ける構成、identity action の包み直し、
  arbitrary functor family の供給、pointed square 族への量化域制限、
  paste を comp の定義同値に潰す構成、C0–C3 を `Iff.rfl` 級で済ませる
  構成、非 epi positive を空 graph / identity action だけで満たす構成、
  空診断・
  恒等 defect・恒等 reselection だけの witness を弾く。
- `frontier`: G-113 の保守性分類、係数 base change、`J_A` 枝、
  indexed schema の H² 方向。

- `target theorem`: **Indexed Base-Change Calculus and Coherent
  Diagnostic Assembly Classification Theorem**。G-110 の設定の上で:
  1. **(a) pointwise indexed calculus (O1)**: 全
     `ExtractionInstance`、全 base 射、全可換 square を量化する
     diagnostic-free raw syntax と generated action を構成する。base /
     total / fiber action、identity、composition、horizontal / vertical
     pasting、projection compatibility、path evaluation coherence を
     theorem として与える。authored input は base 射・可換 square の
     有限 syntax に限り、functor や action の値を含めない。
  2. **(b) cocartesian lifted action (O2)**: 同じ generated action について
     (b1) canonical cleavage `coreFiberLift` との comparison と id /
     comp / paste coherence、(b2) strongly cocartesian total morphism の
     保存を証明する。両命題を別々に放電する。
  3. **(c) coherent base-diagram category**: 診断 import を持たない module
     に `IndexedBaseDiagram G U` を定義する。vertex は
     `ExtractionInstance`、generating edge は base 射、declared
     2-cell は二つの base path とその equality からなる。
     `IndexedBaseDiagramHom D E` は vertex index と generating-edge
     square を持ち、各 declared 2-cell の二経路を target の declared
     2-cell へ送る path naturality を満たす。identity・composition・
     horizontal / vertical pasting と category laws を証明する。この
     structure は package、edge lift、comparator、defect、reselection、
     coherence、vanishing を含まない。
  4. **(d) coherent diagnostic assembly (O4)**: source / target の
     diagnostic-free diagram と `IndexedBaseDiagramHom D E` を、ordinary
     source diagnostic interpretation より先に固定する。target
     `twoCellBase` は hom の path naturality が送る target declared base
     relationから canonical に実現する **direction hypothesis 由来成分**
     であり、raw square family から生成した成果とは数えない。その上で
     target package、edge lift と strongly cocartesian 資格、comparator、
     mapped reselection を同一 pointwise action から生成し、source-fiber
     incidence 仮定なしに (d1) interpretation、(d2) endpoint 群準同型、
     (d3) relation-relative transported data、(d4) mapped reselection、
     (d5) coherence 保存、(d6) vanishing 保存を証明する。target 側で
     input に残せるのは diagnostic-free declared base relation と path
     naturality だけであり、package、edge、comparator、reselection、
     coherence、vanishing は全て output / theorem とする。
  5. **(e) G-110 制限比較 (O3)**: pointed pullback square 由来の coherent
     diagram morphism に制限し、(C0) generated direct / via-base functor、
     (C1) package・edge・two-cell base・comparator、(C2) endpoint action・
     reselection・edge/path law、(C3) indexed→direct・indexed→via・
     G-110 comparison の三角形を成分等式、または指定した canonical
     iso と coherence 等式で比較する。
  6. **(f) raw square-family liftability classification**:
     **量化順を二層に固定する。** 第一に一つの index `i` について
     `UniformTargetBaseLiftableAt i` を「全 endpoint と全 right legs
     `left right` に対し、`i ≫ left = i ≫ right` なら
     `left = right`」と定義し、
     `UniformTargetBaseLiftableAt i ↔ Epi i` を証明する。これは既存
     `IndexedTargetBaseCongruenceAt i` の正確な scope であり、固定有限
     family の偶発的 liftability との同値ではない。第二に有限 raw
     family `F` の support を「`F` の generating square または declared
     cell の source として実際に現れる vertex」と定義し、
     `∀ v ∈ support F, Epi (index v)` から coherent diagram morphism を
     構成する vertexwise-epi producer を与える。この family theorem は
     十分性であり、未使用 vertex を含む global necessity は主張しない。
     加えて (i) source vertex index が epi でない named declared 2-cell
     と、構文的に異なる平行 path、少なくとも一つの非恒等 participating
     action を持つ finite coherent positive を与え、coherent domain が
     epi-only でないことを示す。この witness は non-epi 性と diagnostic
     発火の因果性を主張しない。(ii) Cycle 7 の有限 validated
     non-liftable raw family を保持する。後者は arbitrary raw family の
     自動 assembly を否定する分類の負枝であり、(d) の coherent domain
     の反例ではない。
  7. **(g) diagnostic witness portfolio**: (f)(i) とは別に、named
     declared 2-cell `β : p ⇒ q` とその connected subdiagram を固定する。
     `p/q` は構文的に異なり、participating action・initial raw defect・
     source reselection は非恒等で、その同じ cell の像で (d4)–(d6) を
     発火させる。少なくとも一成分で generated action と identity action
     の具体像が異なることを示す。`β` の source index は epi / non-epi
     のどちらでもよく、(f)(i) の代替証拠には数えない。

- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下の新 module。
  G-110 / G-109 / G-106 / G-101 の reviewed module は参照のみ。完了面は
  (a)–(g)。G-113 の逆方向性質、G-112 の coverage / strong cartesian
  lift、上段 liftは含めない。universe 契約は F0 の型突合で確定する。
- `target proof artifacts`: pointwise raw syntax と action API、
  cocartesian comparison / preservation theorem、diagnostic-free
  `IndexedBaseDiagram` / `IndexedBaseDiagramHom` と category API、
  coherent assembly と (d1)–(d6)、C0–C3、local uniform-liftability
  iff epi theorem、support-indexed vertexwise-epi producer、非 epi
  coherent positive、Cycle 7 負例、
  named nontrivial witness、report
  `research/reports/G-111-aat-indexed-base-change-schema.md`。
- `target proof strategy`: F0 diagnostic-free diagram / hom typing →
  K0 pointwise calculus と既存 Cycle 4–6 API の接続 → K1 diagram category
  と path naturality → K2 coherent diagnostic assembly → K3 (d1)–(d6) →
  K4 C0–C3 → K5 epi iff・正負 witness → K6 final packet。既存成果:
  `IndexedBaseHom` / `IndexedBaseSquare`、`indexedFiberAction`、
  `indexedTotalLift`、identity / composition / pasting coherence、
  `indexedSquareTotalMap_isStronglyCocartesian`、
  `indexedTargetBaseCongruenceAt_iff_epi`、
  `finiteValidatedSquares_refute_twoCellBaseGeneration`、
  G-110 direct / via-base API を再利用する。
- `target theorem completion criteria`: 全 artifact が sorry なしで
  focused ResearchLean check に受理され、axiom / placeholder audit が
  clean であること。下記 `discharge-required` を放電し、provenance、
  proof-use、structure-field escape、route integrity を監査する。各実装
  PR の fixed-head `$review-pr` と、completion candidate の独立
  `$math-lean-review` 4査読全 `No major findings`、CI、merge、Issue
  同期を通過した場合だけ完了する。
- `target premise discharge policy`: 入力として残せるのは
  diagnostic-free source / target base diagram と hom
  (declared base relation / path naturality を含む)、source diagnostic
  interpretation、witness fixture だけ。target `twoCellBase` は declared
  base relation の canonical realizationとしてのみ許し、raw family
  からの生成放電に数えない。target package、edge、comparator、
  reselection、coherence / vanishing certificate、action の値は供給不可。
- `target material premise ledger`:
  - `G-110 reviewed artifact`: `ambient-boundary`。固定錨 =
    PR #4153 final head `a1471483`、merge `315a2537`。支える結論 =
    C0–C3 の比較対象。provenance = reviewed predecessor。proof-use =
    direct / via-base comparison。結論相当でない理由 = 比較される既存
    経路であり、新しい coherent assembly の成立を供給しない。
  - `G-109 / G-101 core lift API`: `ambient-boundary`。canonical
    cleavage と opcartesian 普遍性の入力。provenance = 各 reviewed
    predecessor の固定錨。proof-use = O1/O2 の generated action と
    comparison。結論相当でない理由 = 入力幾何の普遍性だけを供給する。
  - `Cycle 4–6 pointwise indexed calculus`: `discharge-required`
    (reviewed predecessor により放電済み)。discharge artifact =
    PR #4165 head `329f14756d8281d612409c5a2848099a9c8a190b` /
    merge `e08c82663ce0f63a173528b06625ca1849a52da2`、PR #4166
    reviewed head `f90a1e2a4132504e73f0af7c59650942e4652fa8` /
    merge `200401e9c2f6ca9adb29bb4e0c946ed49ba32aa8`、PR #4167
    reviewed head `0040adab3b2926f4c206ba5e85d0f3862ed90494` /
    merge `d552c4b57c12b523cb2f94dc093b892f60abfdd8`。支える結論 =
    O1/O2。proof-use = diagram edge action と assembly engine。
    remaining = diagramwise path relation と diagnostic assembly。
  - `diagnostic-free diagram / hom input`:
    `conclusion-equivalent-risk`。target boundary に残す
    direction hypothesis。支える結論 = coherent domain の量化域と
    target `twoCellBase` の relation-relative realization。
    provenance = authored base graph、base path equality、vertex index、
    edge square。proof-use = target two-cell base の canonical
    realization。監査 artifact =
    diagnostic-free import / field audit と、source index が非 epi、
    parallel path が構文的に異なり、participating action が非恒等である
    named coherent positive。diagnostic 発火は独立な
    `named nontrivial witness` の監査 artifact だけで要求する。
    結論相当でない理由 = target base relation を方向仮定として
    **明示的に残す**相対定理であり、その relation を生成済みと数えない。
    base path naturality だけを表し、package、
    comparator、defect、reselection、coherence、vanishing を含まない。
  - `source diagnostic interpretation`: `direction-hypothesis`。
    source package / edge / comparator、(d4) の source reselection、
    (d5) の source coherence、(d6) の source vanishing に限り消費。
    provenance = ordinary authored source data。proof-use = 各対応 theorem。
    結論相当でない理由 = 順方向定理の source 側仮定であり target data
    を供給しない。
  - `diagnostic-free diagram category`: `discharge-required`。
    discharge artifact = module import / field audit、identity /
    composition / pasting / path naturality theorem。provenance =
    G-101/G-109 API と base category laws。proof-use = K2–K5 全域。
  - `coherent diagnostic assembly と (d1)–(d6)`:
    `discharge-required`。discharge artifact = declared relation の
    `twoCellBase` realization、残る target diagnostic data の生成 theorem、
    6定理。provenance = 同一 diagram hom と generated pointwise action。
    proof-use = witness と G-113 供給 API。declared relation の realization
    は direction hypothesis の使用であり、discharge credit を与えない。
  - `C0–C3`: `discharge-required`。discharge artifact = G-110 の実経路
    との4層比較と三角形 coherence。provenance = canonical restriction。
    proof-use = named pointed-square regression。
  - `raw-family classification`: `discharge-required`。discharge
    artifact = `UniformTargetBaseLiftableAt i ↔ Epi i` の local theorem、
    finite family support 定義、support-indexed vertexwise-epi
    sufficiency producer、非 epi coherent positive、Cycle 7 負例。
    fixed-family liftability iff や未使用 vertex を含む global necessity
    は主張しない。proof-use = local iff 両方向、producer の各 support
    vertex、coherent domain が epi-only でないことの有限正例。
  - `named nontrivial witness`: `discharge-required`。discharge
    artifact = named cell / connected subdiagram に、構文的に異なる
    path、非恒等 participating action、非恒等 defect / reselection、
    identity action との差を持つ有限 fixture。provenance = concrete
    finite data。proof-use = 同じ cell における (d4)–(d6) の非空虚性。
    non-epi positive とは別義務であり、相互に credit を移さない。
- `target route integrity gate`: diagnostic-free module は G-101 /
  G-109 と圏論 API のみ import し、diagnostic module が一方向に import
  する。`IndexedBaseDiagram` / `Hom` の定義展開閉包に package、
  comparator、defect、reselection、coherence、vanishing を入れない。
  (d5)(d6) の proof term は source 仮定を実消費する。同一 generated
  action を (a)–(e) で共有する。source / target diagram と hom は
  diagnostic interpretation と witness の選定前に固定し、declared
  relation の provenance を report に記録する。raw-family の target
  path equality を target-fitting に後付けして raw-family producer の
  放電と数えない。raw-family classification は local uniform iff と
  support-indexed family sufficiency の量化順を signature で分離する。
  diagnostic witness では named cell、participating path edge、defect /
  reselection、(d4)–(d6) proof の incidence を declaration 引数と
  proof-use で監査する。
- `target anti-weakening rule`: coherent domain を epi-only に狭めない。
  arbitrary raw family を coherent hom と同一視しない。declared base
  relation からの `twoCellBase` realization を生成成果と表示しない。共変性、
  cocartesian 性、coherence、vanishing を theorem argument、typeclass、
  structure field、well-formedness predicate へ移さない。
- `target failure policy`: diagnostic-free diagram / hom が要求した
  意味論で型付け不能なら `goal-defect`。coherent diagram hom 上の
  assembly または (d1)–(d6) の反例が出たら `target-refuted`。
  epi iff のどちらかが反証された場合も `target-refuted`。Cycle 7 の
  raw-family 負例は本 target の必須分類 artifact であり失敗ではない。
  反例も証明もなく中心義務が停滞した場合は `target-blocked`。
  fixed target の変更は人間裁定とする。
