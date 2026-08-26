# G-112-aat-exact-bottom-coverage — exact-bottom coverage と全域分類

- `id`: `G-112-aat-exact-bottom-coverage`
- `status`: `active`
- `priority`: `high`
- `research mode`: `target-theorem`
- `program context`: Gr4 完遂 gate 第一項後半の担当カード(担当義務 =
  O5–O7。義務台帳の正本は G-116 カード、設計の source note は n1007
  §3–§5)。cartesian lift・coverage 側の分類カードであり、G-111
  (診断・cocartesian 側)と対をなす — **cocartesian 保存 lift(O2 =
  G-111)と strong cartesian lift(O7 = 本カード)は別の lift であり、
  この分界を本カードと G-111 の双方で明記する**(n1007 §5 判定線2)。
  **本カードの statement は G-111 の宣言を消費しない** — 昇格順は隊列
  運用として G-111 先行だが、G-111 改訂の伝播は受けない(依存は観察
  水準)。本カードの分類結果は G-113 / G-114 / G-115 の量化域を変更
  しない(各カードは G-110 固定の realization 付き入力上で立つ)。
  改訂は G-116 の達成記録要件へ伝播する。依存する reviewed カード
  (G-110)の statement が改訂された場合、本カードは draft へ差し戻し
  て再固定する(伝播規定)。report は coverage 到達段と確定枝を
  G-116 の範囲併記へ突合可能な形で記録する(供給契約)。
  **O7 の位置付け(実装実査 2026-08-26)**: G-110 reviewed 内部宣言
  `strongCartesianLiftOfTarget`(CartesianTarget.lean)は、
  realization 資格なしの任意 `CartSemanticInput` と任意 target
  package に対して strong cartesian lift を既に構成している(G-110
  固定 statement `globalCartesianLift` はその realization 制限)。
  したがって O7 は未決の帰趨決定ではなく、この reviewed 定理の
  semantic-global fixed statement への昇格・proof-use audit・記録を
  義務とする(下記 (c))。
  **O6 量化域(人間裁定済み 2026-08-26)**: 第二段の二枝 disjunction
  は**有限 Source 制限なしの sector 全域**で量化し、両枝の量化域は
  一致させる(排他性様式の保護)。負枝の特徴付け述語はこの裁定では
  固定しない — (b) の閉じた条件言語から選ぶ term として固定し、資格
  条項5項の審査にかける。有限 Source 条件は述語の第一候補として記録
  するに留める。
  **head 分離**: (b) は3つの fixed head を分けて tracking Issue に
  記録する — language head(closed syntax・evaluator・rebase)、
  predicate-term head(固定済み syntax から選んだ term)、branch
  artifact head(term を消費する payload)。条件言語そのものの設計を
  F0 以後へ持ち込むことは `goal-defect` とする(F0 で行うのはカード
  constructor 表の Lean 転写であり、新語彙の発明ではない)。
  **候補遷移規則(三層状態)**: 述語候補列と順序は F0 で事前登録し、
  predicate-term head は先頭候補の機械的採用とする(K0 以降の証明
  結果を選定に使わない)。状態は三層で記録する — candidate state
  (tracking Issue の local state)、cycle result(loop 契約の正式
  語彙 = `proof-obligation-discharged` / `blocker-fixed` /
  `proof-checkpoint` / `rejected`)、GOAL state
  (`target-proof-checkpoint` / `target-refuted` /
  `target-blocked`)。資格条項の反例固定・十分性の反例固定 =
  candidate state を refuted とし、再利用可能な refutation artifact
  を固定して cycle result = `blocker-fixed`、GOAL state =
  `target-proof-checkpoint`、次 = 事前登録列の次候補とする —
  **候補の反証は固定 target の反証ではない**(`target-refuted` は
  (a)(d)(e) 等、固定 target statement 自体への反例に限る)。proof
  未完成・反例なし = cycle result `proof-checkpoint`(候補は破棄
  しない)。同一 blocker が2 cycle 継続 = `target-blocked`。次候補
  への移行は事前登録列の次項、または人間承認による。proof 結果を
  見た新述語の発明は target 改訂(人間裁定)であり、証明サイクル内
  では行わない。
- `predecessor`: G-110(完遂済み。(B) 左枝 = **realization 付き入力上
  の**全域 strong cartesian lift、presentation schema (s1)–(s6)、閉性
  constructor。左枝の内部構成 `strongCartesianLiftOfTarget` は
  realization 資格なしの semantic-global lift を与える。固定錨は下記
  ledger 行)。
- `tracking issue`: [#4184](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4184)(runtime state、cycle 履歴、fixed head、
  次 proof obligation の正本)
- `source note`: [docs/note/n1007_aat_sakura_gr4_completion_design.md](../../docs/note/n1007_aat_sakura_gr4_completion_design.md)(§3 義務台帳、§4 G-112)、
  [G-110 カード](G-110-aat-doctrine-fiber-product.md)(gate (i)・frontier の coverage 二段)
- `research aim`: G-110 は realization 像(有限 presentation 付き底層
  射)上の subcalculus を立てた。本カードは像と sector 全域の間を分類
  する — (第一段)有限 carrier・有限 Source 上では全 semantic
  exact-bottom 射が同型まで像に入ることを証明し、(第二段)sector
  全域については成立か、成立域の特徴付けと反例かを決定する。あわせて
  G-110 reviewed 内部定理が与える semantic-global strong cartesian
  lift(realization 資格なし)を Gr4 正本の fixed statement へ昇格・
  監査・記録し、coverage 成立域の閉性と生成 lift の coherence を証明
  する。「相対的視点の全操作が閉じる」(n1001 §3.5)の coverage 面の
  忠実な転写である。
- `core tension`: 設計事実として、(s1) の有限 Source 固定により無限
  Source を端点に持つ semantic 射は原理的に像外であり、第二段の負枝が
  構造的に近い。したがって本カードの数学的重心は負枝の**特徴付け**が
  本質を欠く言い換えへ退化しないことにある — 「realization 像の定義の言い換え」述語や
  cardinality 反例のみの放電は分類ではない。成立域の特徴付け述語には
  G-110 `H_cart` と同水準の資格条項(下記 (b) の5項)を課す。
- `rival`: (a)(b) は有限表示対象(finitely presentable objects)と
  ind-completion の一般論 — 差は「具体 doctrine 圏での coverage の
  実証明と、資格条項付きの成立域特徴付けを Lean で固定する」点。
  (c)(e) は Grothendieck fibration / cleavage-to-pseudofunctor の
  一般論 — 差は「AAT の `packageProjection` 上で、reviewed
  semantic-global lift から caller 供給なしに cleavage・reindexing・
  coherence を Lean で生成する」点に置く。
- `claim boundary`: 固定した一般 carrier `U`、G-110 の presentation /
  semantic 二層の上で語る。係数は動かさない。終対象・絶対積は導入
  しない。第一段は有限 carrier・有限 Source に限定。第二段と O7 の
  量化は semantic 層の exact-bottom 射(realization 資格なし)に
  及ぶが、carrier change・係数 base change・derived 系は域外(G-116
  カードの域外リストを継承)。診断側(G-111 / G-113)の量化域は変更
  しない。
- `capability categories`: coverage、classification、cartesian-lift、
  closure。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に
  置き、固定 statement と completion criteria だけで完了判定する。
- `portfolio constraint`: 第一段 coverage だけで完了扱いしない。第二段の
  帰趨決定・O7 正本 wrapper と proof-use audit・coverage closure・
  global lift coherence の全面に Lean artifact を要求する。負枝で確定
  する場合は資格条項を満たす特徴付け述語と同型閉包外反例の対を要求
  する。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、反証
  なら `target-refuted`、全完了条件と final review を満たした場合だけ
  `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各 cycle は
  proof obligation delta で評価する。
- `dullness filter`: 次を弾く。第二段負枝を「有限 presentation を持つ
  射」という像の定義の言い換え述語(Skolem 化を含む)で立てる構成、
  無限 Source による cardinality 反例のみの放電、**「同型まで」を
  端点別同型(square 可換性なし)で読んで射自体を実現せずに coverage
  を放電する構成**、第一段 coverage を単一 fixture の列挙で代替する
  構成、(c) の正本 wrapper を新規証明成果として計上する構成
  (reviewed predecessor discharge として記録する — 計上規律)、
  (d) を membership の閉性と十分性の再適用だけで放電する構成
  (coverage witness の実消費・構成なし)、(e) を合成入力への lift の
  再生成(存在の再提示)だけで放電する構成、閉性が恒等成分で vacuous
  に立つ構成、**特徴付け述語を「同型まで恒等射」等の退化 class で
  立てる構成**(下記 (b) の資格条項 (v) 像包含が排除。言い換え述語の
  排除は (b) の閉じた条件言語が担う)。
- `frontier`: 第二段の特徴付け述語の最簡化・decider 化(G-107
  decider 前例との比較観察 — 必要性は (b) の外延一致から従うため
  独立 frontier としない)、可算 Source への拡張観察、係数 base
  change カードとの接続点。

- `target theorem`: **Exact-Bottom Coverage Classification and Global
  Lift Coherence Theorem**。G-110 の設定の上で:
  1. **(a) 第一段 coverage**: `U.Atom` が有限で、source / target 両
     endpoint の `Source` が有限な全 semantic exact-bottom 射
     (`CartSemanticInput`)が、同型まで realization 像に入ることを
     証明する。**「同型まで」は arrow 圏の同型で読む** — coverage
     witness は **object anchor 相対の構造化 witness** で立てる:
     object anchor = 有限 code とその `toSemantic` から object への
     semantic iso の対(`CoveredObjectWitness` 様式)、arrow の
     coverage witness = source / target の anchor 対と、その code 間の
     `CartPresentationBetween`+可換等式(`CoverageWitnessOver` 様式
     — `CartSemanticInputIso` の square 可換性と同水準)。端点別同型
     では放電と数えない。この anchored witness 型は (b) の像包含・
     反例と (d) の閉性で共有する(existential 形だけの witness は
     `compPresentation` / pullback constructor の中間 code 共有要求に
     接続できないため採らない)。`Finite` / `Fintype` の割当と
     `DecidableEq U.Atom` の置き場は F0 の型突合で確定し fixed head に
     記録する。
  2. **(b) 第二段の帰趨決定**: sector 全域(有限 Source 制限なし —
     program context の O6 量化域裁定)について、「全域 coverage
     theorem」または「成立域の特徴付け+同型閉包外反例」の**二枝
     disjunction 単一命題**を証明する(G-110 (B) の分岐固定様式:
     排他性は反例が供給 — 反例が正枝を反証することを同時に証明する。
     網羅性は主張しない)。disjunction は carrier 大域一本で立て、
     述語と十分性は carrier に一様とする(per-carrier 分岐は採らない
     — G-110 (B) 様式)。「同型まで」の読みと coverage witness 型は
     (a) と共有する。**閉じた条件言語(constructor 完全列挙)**:
     特徴付け述語は G-110 `CartConditionSyntax` 様式の閉じた syntax
     型の term として立てる。constructor は次の5つに限る(operand
     なし・数値定数なし・集合定数なし) —
     `sourceFinite`(source endpoint の `Source` が有限)、
     `targetFinite`(target endpoint の `Source` が有限)、
     `allSourceExtractionsFiniteOrCofinite`(source endpoint の全抽出
     述語が finite または cofinite — 一つの原子式とし、
     conjunction-only の下で表現力を確保する)、
     `allTargetExtractionsFiniteOrCofinite`(target 側同上)、
     `conjunction`(結合子はこれのみ)。hom 成分の
     `atomEquivFiniteSupport` 型条件は採用しない —
     `CartSemanticInputIso` が無限 support 置換の endpoint iso を許す
     ため資格条項 (iii)(同型不変性)を満たさない。評価意味は
     constructor ごとに
     `Prop` 水準の `Finite` / finite-or-cofinite 述語で固定する
     (`Fintype` データ・`Nat.card` は評価意味に用いない。無限型上
     では単に不成立)。arbitrary `Prop` callback・fixture 値・
     external constant・任意 `Finset` operand・coverage helper 述語・
     presentation code 型・realization 関数・有限 code / 表データの
     存在量化・「同型な像元の存在」への言及(その Skolem 化を含む)
     は syntax に持ち込めない。F0 の language head はこの表の Lean
     転写であり(universe parameter と dependent type の表現のみ設計
     余地)、条件言語の意味の設計ではない。述語は一つの authored
     template を base carrier で固定し、canonical rebase
     (`rebaseCartCondition` 前例様式)で全 carrier へ移す。branch
     artifact は全 carrier で同一 template の rebase を使うことを
     等式で保証する。syntax・evaluator・rebase の transitive
     dependency audit(依存 helper 経由で結論 / realization を読む
     経路の禁止)を discharge artifact に含める。constructor・結合子・
     量化形の追加は target 改訂扱いとする。述語の ambient 型は量化域
     型と同一とする(部分型上で立てない)。負枝の特徴付け述語には
     資格条項5項を課す — (i) 探索前固定(language head /
     predicate-term head の手続き)、(ii) 結論(coverage / lift)非
     参照、(iii) 同型不変性、(iv) **covered object / 共有 anchor に
     相対化した** id / comp / pullback 閉性((d) と同じ anchor 相対の
     型で読む — wide morphism class の閉性は要求しない)、(v)
     **像包含と非空発火** — 述語は realization 像を(同型まで)包含
     し、非恒等・非可逆成分と相異なる非同型 instance を含む
     パラメトリック正例族で strict 像の外(同型閉包の内でよい)にも
     非空に発火する(正例族は固定 base carrier 上に置き、template
     のみ全 carrier へ rebase する — G-110 前例)。正例族の raw data
     は幾何のみ(parameter 型・distinguished parameter・authored
     endpoint / arrow)とし、`Holds` 成立・strict 像外性・非同型対・
     非可逆性・coverage witness・lift・資格 certificate を field に
     持たせない — 発火と非退化は theorem として生成する(ledger の
     分離行)。特徴付けは十分性
     theorem(述語 → coverage)を要求する。適法な述語は像包含・同型
     不変性・十分性から coverage 成立域と外延一致するため、必要性
     (coverage → 述語)は独立成果に数えない。
  3. **(c) O7 semantic-global strong cartesian lift**: 任意の
     `CartSemanticInput`(realization 資格なし)と任意の target
     package に対する strong cartesian lift の存在を Gr4 正本の fixed
     statement として固定し、G-110 reviewed 宣言
     `strongCartesianLiftOfTarget` による reviewed predecessor
     discharge として放電する。義務は正本 wrapper theorem・proof-use
     audit(G-110 左枝 `globalCartesianLift` との制限関係の明示を
     含む)・G-116 範囲併記への記録であり、新規証明成果としては計上
     しない(計上規律)。
  4. **(d) coverage closure**: branch-independent な coverage regime を
     固定する — `Holds : CartSemanticInput U → Prop` と、membership
     から coverage witness を与える producer を持つ構造(G-110
     `CartesianRegime` / `cartesianRegimeOfDisjunction` 様式)と、
     (b) の二枝 payload からの regime producer(正枝 = `Holds` 全域、
     負枝 = 固定述語)を completion artifact とする。閉性はこの
     regime を index に、**object anchor 相対**で立てる —
     (id) covered object 上の identity: `CoveredObjectWitness X` から
     `𝟙 X` の anchored coverage witness を構成する(全 object への
     wide 読みは採らない — 無限 `Source` object の identity は
     coverage locus 外)、(comp) 共有 anchor: `f` の target anchor と
     `g` の source anchor が同一のとき合成の anchored witness を構成
     する、(pullback) 同一 base anchor を共有する covered cospan の
     **両脚** membership から pullback object anchor と両 projection
     の anchored witness を構成する(片脚のみの pullback 安定性は
     主張しない)。いずれも operand の membership と anchored
     coverage witness を実消費し、output の membership と anchored
     witness を構成する producer で証明する — output 側の caller
     供給、および membership の閉性と十分性の再適用だけの放電は
     不可。(b) 資格条項 (iv) の述語閉性とは別 artifact とする(流用を
     計上しない)。
  5. **(e) global lift coherence**: (c) の semantic-global lift の
     pseudofunctor coherence に限定して証明する — (i)
     `strongCartesianLiftOfTarget` から semantic-global cleavage を
     構成し、(ii) cleavage から semantic-global reindexing functor を
     構成、(iii) identity の unitor natural iso、(iv) composition の
     compositor natural iso、(v) triangle coherence、(vi) pentagon
     coherence を theorem として与える。比較は reindexing functor 間の
     natural iso 水準で固定し、合成入力への lift の再生成(存在の再
     提示)では放電と数えない。**O12 との分界**: BC mate の `IsIso`
     水準 exchange と authored lax square の exchange は主張しない
     (G-116 / O12 の担当)。pullback / pasting square 水準の要求は本
     conjunct に含めない。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下の新
  module。reviewed module は参照のみ。完了面は (a)–(e) まで。二枝の
  payload は G-110 `DisjunctionArtifact` 様式の構造化 artifact で立て、
  payload の caller 供給を放電と数えない。universe 契約は二段階で固定
  する — (1) O6 の反例 fixture は per-universe 固定(= 各 universe に
  おける witness 族の構成であり、単一 universe への固定ではない)の
  symbolic contract を先に試み、具体的 Lean universe constraint と
  して型不能を固定・記録できた場合に限り、事前許可済みの枝条件付き
  endpoint 契約へ移る(無限 carrier 反例は有限 fixture の内部生成
  lift による universe 移送が使えず、cross-universe reindexing は域外
  のため — G-116 カード台帳注記の universe 規律の適用第一号)。
  endpoint 固定の許容範囲は反例 fixture の居住 universe のみとする。
  (2) endpoint 契約も型不能の場合、または特徴付け述語・十分性・閉性
  まで endpoint 固定へ弱める必要が出た場合は `goal-defect` とする。
  特徴付け述語・十分性・資格 theorem 群・(d)(e) は
  universe-polymorphic に立てる((c) は reviewed 宣言の universe
  契約を継承する)。
- `target proof artifacts`: anchored coverage witness 型(object
  anchor / arrow witness)、第一段 coverage theorem(arrow 圏同型
  水準・anchored 構造化 witness)、閉じた条件言語(constructor 表の
  syntax 型・evaluator・canonical rebase・同一 template 等式・
  transitive dependency audit)、第二段二枝確定 artifact(正枝
  theorem または資格条項付き特徴付け述語+同型閉包外反例+正枝
  反証)、O7 正本 wrapper theorem と proof-use audit、
  branch-independent coverage regime と二枝 payload からの regime
  producer、anchor 相対 coverage closure producer、semantic-global
  cleavage / reindexing functor と unitor・compositor・triangle・
  pentagon coherence theorem 群、特徴付け述語の資格 theorem 群
  (同型不変性・anchor 相対閉性・像包含・raw family data からの発火 /
  非退化生成 theorem)、report
  `research/reports/G-112-aat-exact-bottom-coverage.md`。
- `target proof strategy`: F0 typing(language head = カード
  constructor 表の Lean 転写、述語候補列と順序の事前登録(先頭 =
  `sourceFinite ∧ targetFinite`)、(a) の有限性割当と anchored
  coverage witness 型(object anchor / `CartSemanticInputIso` 系)、
  二枝 payload 構造と coverage regime 型、universe 契約を固定)→
  K0 第一段 coverage →
  K1 predicate-term head = 事前登録列の先頭を機械的に採用し第二段
  帰趨(K0 の証明結果を選定に使わない)→ K2 O7 正本 wrapper と
  proof-use audit → K3 coverage regime と closure → K4 global lift
  coherence → K5 監査。既存成果
  の利用 map: `strongCartesianLiftOfTarget` / `GlobalCartesianLift` /
  `CartesianRegime` / `cartesianRegimeOfDisjunction`(semantic-global
  lift と左枝定理の錨)、`cartesianLiftNonexistence_isEmpty`(枝
  整合)、`CartConditionSyntax` / `rebaseCartCondition`(条件言語の
  設計前例)、`CartSemanticInputIso`(coverage witness 型)、
  presentation 閉性 constructor 4種、`FiniteModel`(witness 計算)。
- `target theorem completion criteria`: 全 artifact が sorry なしで
  `ResearchLean` に受理され、axiom / placeholder audit が clean で
  あること。下記 ledger の `discharge-required` を放電し、audit で
  provenance、proof-use、structure-field escape、route integrity を監査
  すること。二段 review gate(各実装 PR の標準 fixed-head
  `$review-pr`、completion candidate での Lean / report / tracking
  Issue 同期と final review packet 作成、独立 `$math-lean-review`
  4査読全 `No major findings`)と CI・merge・最終 Issue 同期を通過
  した場合だけ完了する(正本 = target-goal-contract.md)。
- `target premise discharge policy`: 入力として残せるのは semantic
  射・witness fixture と、用途を限定した presentation(condition
  evaluator への入力、および closure operand が既に持つ anchored
  coverage witness の一部)だけである。(a)(b) の output presentation
  と closure の output presentation / anchor は必ず生成する。
  coverage・lift 存在・特徴付けの結論相当データの供給は放電と数え
  ない。
- `target material premise ledger`:
  - `G-110 reviewed artifact`: `ambient-boundary`。参照のみ、改変
    しない。固定錨: DoctrineFiberProduct = 完了 PR #4153(final head
    `a1471483`、merge `315a2537`)。G-101 / G-106 / G-109 と
    `FiniteModel` 系 witness 基盤の固定錨は G-110 カード ledger の錨を
    継承する。支える結論 = 全 conjunct の設定・左枝定理・
    `strongCartesianLiftOfTarget`。proof-use = (a)–(e) の設定・(c) の
    discharge・witness 計算。結論相当でない理由 = 入力幾何と既証明の
    環境であり、本カードの coverage 結論は供給しない。
  - `閉じた条件言語(syntax / evaluator / rebase)`:
    `discharge-required`。支える結論 = (b) 資格条項 (i)(ii)。
    discharge artifact = カードの完全列挙と一致する閉じた syntax 型・
    evaluator・canonical rebase・全 carrier 同一 template 等式・
    transitive dependency audit。provenance = カード列挙の Lean 転写
    (language head)。proof-use = predicate-term と branch artifact
    が消費する。結論相当でない理由 = 条件の表現手段であり coverage
    結論を含まない。
  - `第一段 coverage theorem`: `discharge-required`。支える結論 =
    (a)。discharge artifact = 構造化 coverage witness(presentation
    +`CartSemanticInputIso`)の構成証明。provenance = 生成した
    presentation と同型対・square 可換性の証明。proof-use = (a) の
    放電と (b) 像包含審査の参照点。結論相当でない理由 = witness は
    構成して証明する。
  - `第二段二枝確定`: `discharge-required`。支える結論 = (b)。
    discharge artifact = 正枝 theorem、または資格5項を満たす特徴付け
    述語+十分性+同型閉包外反例+正枝反証。provenance =
    predicate-term head で固定した term と、生成した十分性証明・
    反例。proof-use = 反例は payload の実消費で結ぶ。結論相当でない
    理由 = 閉じた条件言語が結論参照を排除し、十分性・反例は証明する。
  - `O7 semantic-global strong cartesian lift`: `discharge-required`
    (reviewed predecessor により放電済み)。支える結論 = (c)。
    discharge artifact = G-110 reviewed 宣言
    `strongCartesianLiftOfTarget`(CartesianTarget.lean、上記 G-110
    固定錨)+本カードの正本 wrapper theorem と proof-use audit。
    provenance = reviewed predecessor。proof-use = (c) の fixed
    statement と (e) の生成 lift。結論相当でない理由 = reviewed 済み
    定理の昇格・監査であり、新規仮定を置かない。
  - `branch-independent coverage regime`: `discharge-required`。支える
    結論 = (d) の index surface。discharge artifact = regime 構造
    (`Holds` と membership→witness producer)と二枝 payload からの
    regime producer(正枝 = 全域 `Holds`、負枝 = 固定述語)。
    provenance = G-110 `CartesianRegime` /
    `cartesianRegimeOfDisjunction` 様式の転写。proof-use = (d)
    closure の index と (b) payload の実消費。結論相当でない理由 =
    二枝確定の再包装であり、新しい coverage を供給しない。
  - `coverage closure`: `discharge-required`。支える結論 = (d)。
    discharge artifact = anchor 相対の id / comp / pullback producer
    (covered-object identity・共有 anchor 合成・共有 base anchor
    両脚 pullback。(b) 資格条項 (iv) とは別 artifact)。provenance =
    閉性 constructor の成立域版構成。proof-use = coverage regime と
    (a)(b) 共有の anchored witness 型を実消費する。結論相当でない
    理由 = output 側の anchor と witness は構成して証明し、(iv) の
    流用を計上しない。
  - `global lift coherence`: `discharge-required`。支える結論 = (e)。
    discharge artifact = semantic-global cleavage・reindexing
    functor・unitor / compositor natural iso・triangle / pentagon
    coherence theorem 群(BC mate exchange と lax square exchange は
    域外 — O12)。provenance = (c) の生成 lift。proof-use = 比較の
    両辺を実構成して結ぶ(再生成の存在提示は不可)。結論相当でない
    理由 = coherence は証明する。
  - `O6 coverage 反例 raw data`: `conclusion-equivalent-risk`。支える
    結論 = (b) 負枝の排他性(正枝反証)。provenance = proof
    obligation 選定時に固定する authored 有限 data(universe 契約は
    boundary の二段階規則に従う)。proof-use = 同型閉包外性と正枝
    反証の証明で実消費する。監査 artifact = 選定時固定の記録(証明後
    の target-fitting 選択の禁止)。結論相当でない理由 = raw data は
    入力幾何であり、反証の証明は生成する。
  - `資格条項 (v) raw family data`: `conclusion-equivalent-risk`。
    支える結論 = (b) 資格条項 (v) の非空発火。provenance = 固定 base
    carrier 上の authored raw 幾何のみ(parameter 型・distinguished
    parameter・authored endpoint / arrow。`Holds` 成立・strict 像外
    性・非同型対・非可逆性・coverage witness・lift・資格 certificate
    を field に持たせない)。proof-use = 発火 / 非退化 theorem の
    入力として実消費する。監査 artifact = structure-field escape
    audit。結論相当でない理由 = raw 幾何のみで、資格の証明は生成
    する。
  - `資格条項 (v) firing / nondegeneracy theorem`:
    `discharge-required`。支える結論 = (b) 資格条項 (v)。discharge
    artifact = 発火・strict 像外性・相異なる非同型 instance・非可逆
    成分の生成 theorem 群(G-110 `ParametricCartPositiveFamily` の
    field を theorem 出力へ移した形)。provenance = raw family data と
    固定述語。proof-use = (v) の放電で実消費する。結論相当でない
    理由 = 全て証明で生成し、certificate 供給を認めない。
  - `成立域 membership 証拠`: `direction-hypothesis`。支える結論 =
    (d)。provenance = (b) で確定した成立域の operand membership
    (`H f`・`H g`)と operand の anchored coverage witness(comp は
    共有 anchor、pullback は共有 base anchor)。proof-use = closure
    producer の operand 仮定として実消費する。結論相当でない理由 =
    operand 側の入力仮定であり、output membership・output anchor・
    output witness は構成して証明する(caller 供給禁止)。
- `target route integrity gate`: 特徴付け述語は language head で固定
  した閉じた syntax の term として立て、fixture 値・checker 出力・
  target 結果由来の定数を持ち込まない。反例 fixture は proof
  obligation 選定時に固定する。二枝 payload は構造化 artifact で
  立て、caller 供給を認めない。禁止経路 — 像の定義の言い換え
  (Skolem 化を含む)、cardinality のみの放電、端点別同型 coverage、
  証明後の target-fitting 選択、(e) の lift 再生成による放電。
- `target anti-weakening rule`: coverage・lift 存在・成立域所属を
  theorem argument、typeclass、structure field、certificate field、
  opaque class membership へ移して成功扱いしない((d) の operand
  membership は ledger の direction-hypothesis 行として明示的に許可
  し、output membership・output witness の供給は禁止する)。特徴付け
  述語と結論の**定義的同値**(定義展開・Skolem 化で結論に一致する
  述語)・単一 fixture 等式型を禁じる — 適法述語の外延一致((b)
  末尾)は違反ではなく、必要性は独立成果に数えない。
  `ambient-boundary` に残せるのは入力幾何だけである。
- `target failure policy`: fail-closed を原則とする。(a) の反例は中心
  conjunct 反証 = `target-refuted`。(d)(e) の反例(成立域上の閉性 /
  coherence の反証)も `target-refuted`。(b) は二枝 disjunction で
  ありどちらの枝の確定も成功、両枝とも閉じない場合は
  `target-blocked`。(c) の wrapper が fixed statement で型不能、
  または reviewed 宣言との不一致が判明した場合は人間裁定へ差し戻す。
  述語候補の遷移は program context の候補遷移規則に従う。F0 での型
  不能・statement 不足は `goal-defect`。witness の停滞は
  `target-blocked`。fixed target の変更は人間の別判断とする。
