# G-111-aat-indexed-base-change-schema — indexed base-change calculus と coherent diagnostic assembly の分類

- `id`: `G-111-aat-indexed-base-change-schema`
- `status`: `active`
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
  coherent nontrivial 正例、Cycle 7 負例を全て要求する。非 epi 正例と
  非自明 finite witness は同一 fixture の同一 named 2-cell / connected
  subdiagram でなければならない。
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
  構成、非 epi vertex を診断発火と無関係な直和成分へ隔離した
  pseudo-positive、空診断・
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
  6. **(f) raw square-family liftability classification**: 等しい source
     path と可換 square の raw family から target path equality を
     **全 right legs に一様生成できることと source index が `Epi` で
     あることの必要十分性**を証明する。vertexwise epi な raw family から
     coherent diagram morphism を構成する producer を与える。加えて
     (i) named declared 2-cell `α : p ⇒ q` を一つ固定し、`p` と `q` は
     構文的に異なる平行 path、`α` の source vertex index は epi でなく、
     `p` または `q` に現れる少なくとも一つの edge の generated action は
     非恒等である具体的 coherent diagram morphism の有限正例を与える。
     同じ `α` とその連結部分図式に非恒等 defect / reselection を置き、
     その同じ cell の像で (d4)–(d6) を発火させる。(ii) Cycle 7
     の有限 validated non-liftable raw family を保持する。後者は
     arbitrary raw family の自動 assembly を否定する分類の負枝であり、
     (d) の coherent domain の反例ではない。
  7. **(g) witness portfolio**: (f)(i) の**同一 named cell `α` / 同一
     connected subdiagram**で (d4)–(d6)を発火させ、`α` の path に参加する
     少なくとも一つの generated action と identity action の具体像が
     異なることを示す。孤立した非 epi vertex と別の epi diagnostic
     component の直和、または別 fixture への非自明性移送を認めない。

- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下の新 module。
  G-110 / G-109 / G-106 / G-101 の reviewed module は参照のみ。完了面は
  (a)–(g)。G-113 の逆方向性質、G-112 の coverage / strong cartesian
  lift、上段 liftは含めない。universe 契約は F0 の型突合で確定する。
- `target proof artifacts`: pointwise raw syntax と action API、
  cocartesian comparison / preservation theorem、diagnostic-free
  `IndexedBaseDiagram` / `IndexedBaseDiagramHom` と category API、
  coherent assembly と (d1)–(d6)、C0–C3、epi iff theorem、
  vertexwise-epi producer、非 epi coherent nontrivial 正例、Cycle 7 負例、
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
    diagnostic-free import / field audit と、named cell の source index
    が非 epi でその同じ connected subdiagram が発火する正例。
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
  - `raw-family classification`: `discharge-required`。epi iff、
    vertexwise-epi producer、非 epi coherent nontrivial 正例、Cycle 7 負例を
    finite constructions から固定する。proof-use = iff 両方向と
    coherent domain 非退化監査。
  - `named nontrivial witness`: `discharge-required`。discharge
    artifact = raw-family classification の非 epi coherent 正例と同一の
    named cell / connected subdiagram に、構文的に異なる path、非恒等
    participating action、非恒等 defect / reselection、identity action
    との差を持つ有限 fixture。provenance = concrete finite data。
    proof-use = 同じ cell における (d4)–(d6) の非空虚性。
- `target route integrity gate`: diagnostic-free module は G-101 /
  G-109 と圏論 API のみ import し、diagnostic module が一方向に import
  する。`IndexedBaseDiagram` / `Hom` の定義展開閉包に package、
  comparator、defect、reselection、coherence、vanishing を入れない。
  (d5)(d6) の proof term は source 仮定を実消費する。同一 generated
  action を (a)–(e) で共有する。source / target diagram と hom は
  diagnostic interpretation と witness の選定前に固定し、declared
  relation の provenance を report に記録する。raw-family の target
  path equality を target-fitting に後付けして raw-family producer の
  放電と数えない。non-epi witness では named cell、source vertex index、
  participating path edge、defect / reselection、(d4)–(d6) proof の
  incidence を declaration 引数と proof-use で監査し、直和成分への
  隔離を禁止する。
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
