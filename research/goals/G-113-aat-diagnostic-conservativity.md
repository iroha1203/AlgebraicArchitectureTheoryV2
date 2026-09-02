# G-113-aat-diagnostic-conservativity — indexed 診断輸送の同値性と orbit exactness

- `id`: `G-113-aat-diagnostic-conservativity`
- `revision`: `2`
- `revision approved`: `2026-08-28`
- `status`: `completed`
- `completion result`: `target-theorem-proved`(revision 2)。Indexed
  Diagnostic Transport Equivalence and Orbit Exactness Theorem の固定
  target (a)–(i)(担当義務 O13–O18・O20)を全放電
  ($target-theorem-loop Cycle 1–28、2026-08-28)。主要成果:
  (a) push / reindex の typed alignment
  (`indexedDiagnosticTransport_vertexIndex_decode` と push / reindex の
  外延一致定理)、G-110 reviewed cocartesianness の selected-lift bridge
  (`indexedDiagnosticTransportSelectedLift_isStronglyCocartesian`)、
  universal property から構成した unit / counit natural iso と左右
  triangle(`indexedDiagnosticTransportAdjunction`)、explicit
  equivalence(`indexedDiagnosticTransportEquivalence`)と `Full` /
  `Faithful` / `EssentiallySurjective` / `IsEquivalence` の producer
  (premise 供給なし)、
  (b) endpoint 明示 equivalence
  (`indexedDiagnosticEndpointEquivalence`)と revision 1 endpoint
  action との外延一致 — injective / surjective はその系、
  (c) reselection forward / inverse transport
  (`indexedDiagnosticReselectionEquivalence` /
  `inverseTransportedReselection`)の左右逆・基準 reselection 保存・
  mapped reselection 往復、
  (d) coherence iff(`indexedCoherentAt_transport_iff` /
  `indexedCoherentAt_inverseTransport_iff`)、
  (e) obstruction vanishing iff
  (`indexedTransportObstructionVanishes_iff`)と class 条件なしの全 hom
  系(`diagnosticConservative_all_via_transportEquivalence` /
  `no_diagnosticConservativityCounterexample_via_transportEquivalence`)、
  (f) raw-defect cochain 明示 equivalence
  (`indexedDiagnosticDefectCochainEquivalence`)と `rawDefectCochain`
  との両方向可換・cochain 値の eq / ne 双方向反射、
  (g) orbit membership iff(`indexedDiagnosticInReselectionOrbit_iff` と
  逆方向)、
  (h) identity / composition / whole-unit / whole-pentagon /
  path-square / horizontal-pasting の transport coherence package
  (square 水準は `indexedDiagnosticTwoCellPastingCube` 等の commuting
  theorem で固定、downstream (d)–(g) への伝播込み)、
  (i) 全 hom / vertex の base-`IsIso` 非依存 equivalence
  (`indexedDiagnosticTransport_isEquivalence_arbitraryBase`)と `IsIso`
  base corollary、非恒等 `¬ IsIso` 有限 base component 上の converse
  反証(`finiteNonIsoDiagnostic_converse_refutation`)と同一 witness の
  非退化性(`finiteNonIsoDiagnostic_sameWitness_nondegeneracy`。非恒等
  defect / reselection の往復保存4本)。
  Lean artifact は `DiagnosticConservativity` 配下の revision 2 新設
  27 module。standard exact-head PR gate は `Mergeable`
  ([PR #4233 コメント](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4233#issuecomment-5453692797)、
  [PR #4234 コメント](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4234#issuecomment-5453887137))、
  same-merge-head final packet は
  [PR #4234 コメント](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4234#issuecomment-5453953468)、
  独立 final math-lean-review は数学 A/B・Lean A/B 全て
  `No major findings`、completion ledger は全 gate pass・残 obligation /
  blocker / unchecked central claim なし・root recheck pass
  ([PR #4234 コメント](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4234#issuecomment-5454070326))、
  exact-head CI は PR #4233・#4234 とも 7/7。tracking Issue の完了記録は
  [#4204 完了記録コメント](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4204#issuecomment-5454074795)
  で固定(Issue #4204 は user policy で OPEN 維持)。fixed GOAL blob SHA
  `d490685ece406d5b17ccc63b3d35ff990bc34c5d`(SHA-256
  `beb27f46da767f0fef80eed45b502698c28f1651c6325fe19041944d84436e47`)、
  完了 PR
  [#4233](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4233)
  (head `76e58611`、merge `7083db0d`)+report / Issue 同期 PR
  [#4234](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4234)
  (head `cb1aefb4`、merge `f737a470`、exact final tree `fe63d929`)。
  実装 PR 系列(#4205–#4232)と cycle 履歴は tracking Issue #4204 を
  正本とする。公理監査は `DiagnosticConservativity` 全27 source module の
  focused Lean check で standard axioms のみ pass(focused hash
  `63ba0894` 再現。Research aggregate / full build は hard rule に従い
  未実行)。Cycle 28 completion packet は独立レビューで revision 1
  reflection 経路の混入2件((d)(e) の proof-use)を是正した後に受理
  (是正履歴は report の review_history)。
  **達成の記録の限定**: 量化域は claim boundary の通り固定一般 carrier
  `U`、G-111 `IndexedBaseDiagramHom`、G-111 生成 diagnostic
  interpretation に限る。係数は動かさない。carrier change・独立 raw
  square family・G-109 段射影 `p` 沿い effectivity 反射・`J_A` defect
  profile・終対象/絶対積は域外。(i2) により fiber transport equivalence
  は base `IsIso` を反射しない(equivalence 成立域は `IsIso` base より
  真に広い)。revision 1 の class syntax / candidate head /
  normalization artifact は歴史証拠のみで completion credit を持たない
  (語彙参照のみ)。**Gr4 達成の記録は本カードでは行わない** — 担当は
  O13–O18・O20 のみで、refinement 系統・上段 lift・IsIso 水準
  exchange-failure 存否決定・capstone 記録は G-114〜G-116 に残る
  (program context)。`Formal/AG` への移植は未実施(porting status:
  `unported`)。
- `completed at`: `2026-08-28 JST`
- `priority`: `high`
- `research mode`: `target-theorem`
- `program context`: Gr4 完遂 gate 第五項の担当カード(担当義務 =
  O13–O18・O20。義務台帳の正本は G-116、設計の source note は n1007
  §3–§5)。G-111 が構成した covariant indexed diagnostic action と、
  G-112 が構成した contravariant semantic-global cartesian reindexing を
  同一の `IndexedBaseDiagramHom` 上で突合し、両者の同値性、診断値の
  反射、reselection orbit exactness を一枚の theorem package として
  固定する。diagram / hom / diagnostic interpretation の型は G-111、
  semantic-global cleavage / reindexing の型は G-112 の reviewed API を
  参照し、本カードで再定義しない。新設語彙の命名権は
  `IndexedDiagnosticTransportEquivalence` に置き、既存の
  `DiagnosticConservative` はその系として保持する。本カードの改訂は
  G-116 の達成記録要件へ伝播する。
- `revision provenance`: revision 1 の固定 target(blob
  `89d47851711f9335bf42d312c8522db01c7718ba`)は、全 hom 上の
  `DiagnosticConservative` と endpoint action の全射性を Lean で証明した
  ことにより、O16 が要求した「class 外で診断が消える作用」と両立しない
  と確定した。PR #4203 の exact head
  `9966fb6ca4516b3601460079c288fa46f70f30dc`、merge
  `da95789a5dbaca926554d461f89cc2c7273ac934`、および
  `diagnosticConservative_all` / `no_diagnosticConservativityCounterexample`
  は revision 1 の `target-refuted` 証拠として保存する。revision 2 は
  revision 1 の穴埋めではなく、obstruction が非零から零へ消える枝の反証と
  G-110 の package-projection 固有 ambidextrous theorem を新しい出発点として、
  G-111 / G-112 の診断同値性を問う固定 target である。revision 1 単独から
  injectivity、Full / Faithful、cochain / orbit equivalence が従うとは数えない。
  completion は revision 2 を最初から再監査し、
  revision 1 の class syntax、candidate head、normalization artifact、
  finite fixture を revision 2 の義務放電として数えない。
- `predecessor`: G-111(完遂済み。PR #4181 exact head
  `87278945e24f48fba5b9b8154e6979800bde0cd6`、merge
  `8850a5b4d2c03458f1f1f5af6bf2017d79ad1567`。`indexedFiberAction`、
  coherent diagnostic assembly、identity / composition / path-square /
  horizontal-pasting API)、G-112(完遂済み。PR #4197 exact head
  `bf882573945a45780b022bc811754f8444846c53`、merge
  `e9f891b8b0d763c6c29cb2d8b6e723b43a6bb9bb`。
  `strongCartesianLiftOfTarget`、semantic-global cleavage / reindexing
  functor と coherence)、G-113 revision 1 の reviewed reflection package、
  G-110 の arbitrary-target
  `strongCartesianLiftOfTarget_isStronglyCocartesian` と realized-arrow unit /
  counit iso(PR #4153 exact head
  `a1471483aca30c3d9d6e942deb38688401a8fed0`、merge
  `315a2537cea51e1f8ea131351f4de9ef22b21145`)、G-106 の raw defect /
  reselection orbit 語彙、G-109 の core pseudofunctor API。
- `tracking issue`: [#4204](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4204)
  (revision 2 の runtime state、cycle 履歴、fixed head、次 proof obligation の
  正本)。[#4198](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4198)
  は revision 1 の `target-refuted` 履歴として保持し、本 revision の runtime
  state を追記しない。
- `source note`: [docs/note/n1007_aat_sakura_gr4_completion_design.md](../../docs/note/n1007_aat_sakura_gr4_completion_design.md)
  (§3 義務台帳、§4 G-113、§5 判定線1・3)、
  [G-116 カード](G-116-aat-idempotent-exchange-structure.md)(旧 id `G-116-aat-gr4-capstone`。O13–O18・O20 の義務台帳は Gr4 を閉じるカードへ移す)、
  [revision 1 report](../reports/G-113-aat-diagnostic-conservativity.md)
  (revision 1 の refutation candidate / proof ledger。最終 `target-refuted` の
  資格は上記 PR #4203 の exact / merge anchor、Lean 宣言、Issue #4198 に置く)。
- `research aim`: indexed base change に沿う診断輸送を、単なる順方向の
  保存や消滅反射としてではなく、G-111 の covariant action と G-112 の
  contravariant reindexing が作る同値として捉える。その同値が endpoint、
  reselection、coherence、raw-defect cochain、orbit membership の各水準を
  exact に運ぶことを示し、Gr4 の indexed diagnostic geometry を閉じる。
- `core tension`: G-111 と G-112 は向きと構成原理が異なる。前者は
  coherent base-diagram hom から fiber action と診断輸送を組み、後者は
  arbitrary target に対する strongly cartesian lift から reindexing を組む。
  両 API の型が並ぶだけでは quasi-inverse、unit / counit、diagnostic
  naturality は得られない。最大のリスクは、同値性を typeclass / structure
  field として入力し直すこと、G-110 の realized finite-code sector だけで
  全 indexed domain を代表させること、vanishing iff だけで orbit / cochain
  exactness を完了扱いすることである。
- `rival`: conservative functor、Grothendieck fibration / bifibration、
  Beck–Chevalley と local system の一般論。差は、AAT の生成診断に対して
  covariant action と semantic-global cartesian reindexing の明示的な
  quasi-inverse、raw-defect と reselection orbit の exactness、coherence
  までを Lean の同一 package に固定する点に置く。
- `claim boundary`: 固定した一般 carrier `U`、G-111 の
  `IndexedBaseDiagramHom` とその declared base relation に相対して生成された
  diagnostic interpretation を量化域とする。係数は動かさない。任意の独立
  raw square family、carrier change、G-109 の段射影 `p` に沿う effectivity
  反射、`J_A` defect profile、終対象・絶対積は域外。G-112 の
  semantic-global lift は同じ indexed hom の target data から生成する。
  G-111 の domain 外の診断 interpretation を本カードで追加しない。
- `capability categories`: equivalence、reflection、orbit-exactness、
  coherence、nonvacuity。
- `threshold policy`: SCORE は使わない。runtime state は revision 2 の
  tracking Issue に置き、固定 statement と completion criteria だけで
  完了判定する。
- `portfolio constraint`: fiber functor の同値だけで完了扱いしない。
  endpoint、reselection、coherence、vanishing、raw-defect cochain、orbit
  membership、identity / composition / pasting coherence、有限非退化 witness
  の全 artifact を要求する。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、固定
  target の反例なら `target-refuted`、同じ blocker が二 cycle 続けば
  `target-blocked`、全 completion criteria と final review を満たした場合だけ
  `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各 cycle は proof
  obligation delta で評価する。
- `dullness filter`: 恒等 hom だけの witness、`IsEquivalence` / `Full` /
  `Faithful` を theorem premise・typeclass・structure field として供給する
  構成、G-110 の realized finite-code sector だけに量化域を縮める構成、
  vanishing iff だけを exactness 全体と呼ぶ構成、arbitrary target diagnostic
  interpretation を G-111 の生成域外から持ち込む構成、revision 1 の class /
  candidate syntax を再導入して同値性を条件化する構成を弾く。
- `frontier`: 係数 base change 下の transport equivalence、段射影 `p` の
  effectivity との合成、derived / higher fiber への拡張、一般 bifibration
  としての抽象化。

- `target theorem`: **Indexed Diagnostic Transport Equivalence and Orbit
  Exactness Theorem**。G-111 / G-112 の reviewed setting の上で、次を同一
  package として証明する。
  1. **(a) vertexwise transport equivalence (O13)**: 各
     `IndexedBaseDiagramHom` と各 vertex について、G-111 の
     `indexedFiberAction` と、G-112 の semantic-global reindexing から同じ
     hom / target data に対して得る functor を、向きを揃えた明示的な
     quasi-inverse として組む。unit / counit natural isomorphism と triangle
     identity を構成し、`Full`、`Faithful`、`EssentiallySurjective`、
     `IsEquivalence` および明示的 equivalence を named declarations に固定
     する。これらを premise として受け取らない。
  2. **(b) endpoint exactness (O13)**: diagnostic endpoint action を明示的
     equivalence として構成し、その forward map が revision 1 の endpoint
     action と外延一致することを証明する。injective / surjective はこの
     equivalence の系とする。
  3. **(c) reselection exactness (O15)**: reselection の forward transport
     と inverse transport を構成し、左右逆、基準 reselection の保存、
     mapped reselection の往復を証明する。
  4. **(d) coherence exactness**: source diagnostic coherence と transported
     target diagnostic coherence の iff を証明する。順方向は G-111 の
     coherence preservation を消費し、逆方向は (a)–(c) の inverse transport
     と自然性から導く。
  5. **(e) obstruction exactness (O14)**: obstruction vanishing の iff を
     証明する。`DiagnosticConservative` と
     `no_diagnosticConservativityCounterexample` はその系として全 hom 上に
     named declarations を保持し、class 条件を課さない。
  6. **(f) raw-defect cochain exactness (O20)**: cochain transport を明示的
     equivalence として構成し、forward / inverse の双方が
     `rawDefectCochain` と可換することを証明する。従って任意 cochain 値の
     等値と相異を双方向に反射する。
  7. **(g) orbit exactness (O15)**: `InReselectionOrbit` membership の iff を
     source / target 間で証明する。単一の基準 cochain との相異保存だけでは
     この義務を放電したと数えない。
  8. **(h) transport coherence (O17)**: identity、vertical composition、
     path-square naturality、horizontal pasting に対し、(a)–(g) の
     equivalence が G-111 / G-112 の unitor・compositor・triangle・pentagon
     と可換することを証明する。水平演算が square 水準である場合は新しい
     hom 演算を捏造せず、その square-level commuting theorem を固定する。
  9. **(i) categorical decomposition and nondegeneracy (O16・O18)**:
     `Full` / `Faithful` / `EssentiallySurjective` の各 producer が入力 data
     から生成される proof-use route を固定する。base `IsIso` との関係は次の
     二定理で固定する。(i1) 任意の indexed hom / vertex で base component の
     `IsIso` を仮定せず fiber transport equivalence が成立し、従って
     `IsIso` base から同じ equivalence を得る named corollary を持つ。
     (i2) converse「fiber transport equivalence なら base component は
     `IsIso`」を、非恒等かつ `¬ IsIso` の有限 base component 上で fiber /
     diagnostic equivalence が発火する named witness theorem により反証する。
     同じ witness 上で非恒等 defect と非恒等 reselection が往復で失われない
     ことも証明する。これは revision 1 の不可能な「診断を消す class 外
     witness」に代わる、同値性の非退化性 witness である。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/DiagnosticConservativity/` 配下の revision 2
  新 module。G-111、G-112、G-113 revision 1 の reviewed modules は参照のみ。
  revision 1 の class syntax / normalization declarations は削除せず歴史成果と
  して残すが、revision 2 main spine に import / premise として不要なら接続
  しない。量化は一般 carrier、一般 indexed hom、G-111 が生成する全
  diagnostic interpretation に対して行う。有限 witness だけを `Fin` 等で
  固定してよい。
- `target proof artifacts`:
  - vertexwise quasi-inverse、unit / counit natural iso、triangle identity、
    `Full` / `Faithful` / `EssentiallySurjective` / explicit equivalence の Lean
    declarations。
  - endpoint / reselection / raw-defect cochain equivalence、coherence iff、
    vanishing iff、orbit membership iff の Lean declarations。
  - identity / composition / path-square / horizontal-pasting coherence package。
  - 全 indexed hom / vertex 上の base-`IsIso` 非依存 equivalence theorem、
    `IsIso` base からの named corollary、fiber equivalence が base `IsIso` を
    反射しないことを示す finite named counterexample theorem。
  - 非恒等 `¬ IsIso` base component、非恒等 defect、非恒等 reselection を持つ
    finite nondegenerate witness と、その全 conjunct の producer theorem。
  - revision 2 report
    `research/reports/G-113-r2-aat-diagnostic-transport-equivalence.md`。revision 1
    report は上書きしない。
- `target proof strategy`: F0 = G-111 / G-112 の type・universe・variance を
  突合し、push / reindex alignment の exact Lean statement を固定する。K0 =
  revision 1 の endomorphism reflection を arbitrary fiber hom へ一般化し、
  Full / Faithful producer を構成する。K1 = G-112 の arbitrary-target strongly
  cartesian lift と、G-110
  `strongCartesianLiftOfTarget_isStronglyCocartesian` を実消費し、realized-arrow
  unit / counit は構成前例に限定して、一般 indexed domain の essential
  surjectivity、unit / counit、equivalence を構成する。K2 = endpoint /
  reselection equivalence、coherence iff、vanishing iff。
  K3 = raw-defect cochain equivalence と orbit membership iff。K4 = identity /
  composition / square / pasting coherence と finite nondegenerate witness。
  G-110 の realized-arrow theorem は構成前例であり、一般 indexed conclusion
  の代替にはしない。
- `target theorem completion criteria`: (a)–(i) の全 artifact が sorry なしで
  `ResearchLean` に受理され、対象全 declarations の `#print axioms`、placeholder、
  hidden / BiDi Unicode、privacy、import direction が clean であること。下記
  ledger の全 `discharge-required` を入力 data からの theorem / construction、
  reviewed predecessor theorem、または finite witness で放電すること。
  statement の量化・方向・結論強度、certificate provenance、material premise
  proof-use、structure-field escape、route integrity、nonvacuity、dependency DAG
  を監査すること。各実装 PR の exact fixed head を標準 `$review-pr` に渡し、
  report / tracking Issue を同期すること。completion candidate では同一 fixed
  GOAL に対する final review packet を作成し、別の独立
  `$math-lean-review` 数学2本・Lean2本がすべて正確に
  `No major findings` であること。CI green、merge、定理名の存在、revision 1
  artifact の再利用だけでは completion としない。
- `target premise discharge policy`: carrier、indexed diagram / hom、declared
  base relation、G-111 が生成する diagnostic interpretation だけを入力境界に
  残す。同値性、Full / Faithful / EssentialSurjective、unit / counit、反射、
  orbit exactness、cochain map の injectivity / surjectivity、coherence を theorem
  argument、typeclass、structure / certificate field として供給してはならず、
  completion までに producer theorem で放電する。
- `target material premise ledger`:
  - `G-111 reviewed indexed diagnostic action`: `ambient-boundary`。固定錨 =
    PR #4181 exact head / merge(上記)。支える結論 = covariant action と forward
    diagnostic naturality。結論相当でない理由 = inverse、essential surjectivity、
    iff、orbit exactness は G-111 単独からは与えられない。
  - `G-112 reviewed semantic-global reindexing`: `ambient-boundary`。固定錨 =
    PR #4197 exact head / merge(上記)。支える結論 = arbitrary-target strongly
    cartesian lift と contravariant reindexing。結論相当でない理由 = G-111 の
    action との alignment と diagnostic naturality は未構成である。
  - `G-113 revision 1 reflection package`: `ambient-boundary`。固定錨 =
    PR #4203 exact head / merge(上記)。支える結論 = 全 hom の vanishing 反射と
    endpoint surjectivity。結論相当でない理由 = explicit fiber / reselection /
    cochain equivalence と orbit membership iff を主張しない。
  - `G-110 arbitrary-target lift cocartesianness`: `discharge-required`。固定錨 =
    PR #4153 exact head / merge(上記)の
    `strongCartesianLiftOfTarget_isStronglyCocartesian`。支える結論 = (a)(i) の
    counit / essential surjectivity。discharge artifact = reviewed predecessor
    theorem を一般 indexed hom の selected lift に適用する named bridge。
    proof-use = G-112 の cartesian lift と同じ射について cocartesian uniqueness
    を実消費する。realized-arrow unit / counit の一般域への外挿は不可。
  - `push / reindex type and variance alignment`: `discharge-required`。支える
    結論 = (a)。artifact = 同じ hom / target data から両 functor を組む typed
    comparison と外延一致 theorem。provenance = G-111 / G-112 producer data。
  - `Full and Faithful producers`: `discharge-required`。支える結論 = (a)(i)。
    artifact = arbitrary fiber hom に対する preimage / equality reflection theorem。
    proof-use = unit / counit または lift uniqueness を実消費する。
  - `EssentiallySurjective producer`: `discharge-required`。支える結論 = (a)(i)。
    artifact = arbitrary target object からの strongly cartesian lift、同じ lift の
    G-110 cocartesianness bridge、object iso。proof-use = G-112 の arbitrary-target
    theorem と上記 G-110 reviewed theorem の双方を実消費する。
  - `unit / counit and triangle identities`: `discharge-required`。支える結論 =
    (a)。artifact = natural isomorphisms と左右 triangle。caller-supplied iso 不可。
  - `endpoint and reselection inverse maps`: `discharge-required`。支える結論 =
    (b)(c)。artifact = forward / inverse producer と左右逆 theorem。
  - `coherence and vanishing inverse direction`: `discharge-required`。支える
    結論 = (d)(e)。artifact = inverse transport から導く named iff theorems。
  - `raw-defect cochain equivalence`: `discharge-required`。支える結論 = (f)。
    artifact = explicit equivalence と `rawDefectCochain` commuting theorems。
  - `orbit membership inverse direction`: `discharge-required`。支える結論 =
    (g)。artifact = reselection / cochain inverse を実消費する membership iff。
  - `identity / composition / square / pasting coherence`: `discharge-required`。
    支える結論 = (h)。artifact = G-111 / G-112 coherence API と可換する theorem
    package。output coherence の caller 供給不可。
  - `finite non-IsIso nondegenerate witness raw data`: `conclusion-equivalent-risk`。
    支える結論 = (i)。base component、defect、reselection の値だけを fixture
    data として許し、`¬ IsIso`、非恒等性、equivalence、保存を field にしない。
  - `finite witness firing`: `discharge-required`。支える結論 = (i)。artifact =
    raw fixture から `¬ IsIso`、非恒等 defect / reselection、往復保存を別々に
    証明する named theorems。
  - `base IsIso relation`: `discharge-required`。支える結論 = (i1)(i2)。
    artifact = 全 hom / vertex の base-`IsIso` 非依存 equivalence theorem、
    `IsIso` base corollary、同一 finite witness による converse 反証 theorem。
    proof-use = universal equivalence producer と finite witness firing を実消費し、
    relation の caller-supplied decision を受け取らない。
  - `revision 1 class syntax / candidate head`: `not-applicable`。歴史 artifact。
    revision 2 の premise、route、completion evidence として使用しない。
- `target anti-weakening rule`: (a)–(i) の結論相当性質を theorem argument、
  typeclass、structure / certificate field、opaque membership、revision 1 class
  conditionへ移さない。量化域を恒等 hom、IsIso base、realized finite-code
  sector、単一 fixture に縮めない。片方向 map、injective / surjective の片方、
  vanishing iff だけを explicit equivalence / orbit exactness と読み替えない。
- `target route integrity gate`: push / reindex comparison、unit / counit、inverse
  endpoint / reselection / cochain map、finite witness の各 route について、どの
  G-111 / G-112 入力 data、universal property、lift uniqueness、reviewed theorem、
  raw finite fixture から生成されたかを declaration map と proof-use audit に
  固定する。target-fitting selection、空型 / singleton / identity への退化、
  conclusion-side law の field 埋め込み、G-110 realized sector から一般域への
  無根拠な外挿を `rejected` とする。
- `target failure policy`: revision 2 の universal equivalence、raw-defect
  commuting、orbit membership iff のいずれかに concrete counterexample または
  不可能定理を固定した場合は `target-refuted`。type / universe / variance の
  不一致により statement 自体が定式化不能、または固定 target の改訂が必要な
  場合は `goal defect` として止め、人間承認なしに class 条件や弱い反射定理へ
  fallback しない。有用な package は得たが未放電 premise / coverage / review
  gap が残る場合は `target-proof-checkpoint`。同じ blocker が二 cycle 続けば
  `target-blocked`、二 cycle 連続で受理可能な proof DAG / premise / blocker delta
  がなければ `proof stagnation` とする。tracking Issue は人間の明示指示なしに
  close しない。
