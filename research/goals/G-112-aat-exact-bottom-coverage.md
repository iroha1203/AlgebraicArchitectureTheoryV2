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
  **O6 量化域(人間裁定済み 2026-08-26)**: 第二段の二枝 disjunction
  は**有限 Source 制限なしの sector 全域**で量化し、両枝の量化域は
  一致させる(排他性様式の保護 — (b)(c) の双方に適用)。負枝の特徴
  付け述語はこの裁定では固定しない — (b) の条件言語規律の範囲で F0
  で確定し、fixed head として tracking Issue に記録して資格条項5項の
  審査にかける。有限 Source 条件は述語の第一候補として記録するに
  留める。述語の変更は資格条項審査の finding だけを事由として許す
  (finding の引用を tracking Issue に記録する)。十分性証明の失敗は
  変更事由にしない — その場合は候補の破棄と新候補の起草として全履歴
  を記録する。変更ごとに述語の fixed head を更新し、資格 theorem
  群・十分性・反例・閉性を更新後述語で全て再放電する。「探索前
  固定」は当該 fixed head の証明サイクル開始前の固定と読み、同一
  head の証明結果を見た差し替えを禁ずる。
- `predecessor`: G-110(完遂済み。(B) 左枝 = **realization 付き入力上
  の**全域 strong cartesian lift、presentation schema (s1)–(s6)、閉性
  constructor。固定錨は下記 ledger 行)。
- `tracking issue`: 未起票(昇格 PR マージ後に起票し、本行を Issue
  番号へ更新する)
- `source note`: [docs/note/n1007_aat_sakura_gr4_completion_design.md](../../docs/note/n1007_aat_sakura_gr4_completion_design.md)(§3 義務台帳、§4 G-112)、
  [G-110 カード](G-110-aat-doctrine-fiber-product.md)(gate (i)・frontier の coverage 二段)
- `research aim`: G-110 は realization 像(有限 presentation 付き底層
  射)上の subcalculus を立てた。本カードは像と sector 全域の間を分類
  する — (第一段)有限 carrier・有限 Source 上では全 semantic
  exact-bottom 射が同型まで像に入ることを証明し、(第二段)sector 全域については成立か、
  成立域の特徴付けと反例かを決定する。あわせて G-110 左枝(全域
  lift)の realization 資格外への帰趨を決定する。「相対的視点の全操作
  が閉じる」(n1001 §3.5)の coverage 面の忠実な転写である。
- `core tension`: 設計事実として、(s1) の有限 Source 固定により無限
  Source を端点に持つ semantic 射は原理的に像外であり、第二段の負枝が
  構造的に近い。したがって本カードの数学的重心は負枝の**特徴付け**が
  安価に堕ちないことにある — 「realization 像の定義の言い換え」述語や
  cardinality 反例のみの放電は分類ではない。成立域の特徴付け述語には
  G-110 `H_cart` と同水準の資格条項(下記 (b) の5項)を課す。
- `rival`: 有限表示対象(finitely presentable objects)と ind-completion
  の一般論。差は「具体 doctrine 圏での coverage の実証明と、資格条項
  付きの成立域特徴付け・全域 lift の帰趨決定を Lean で固定する」点に
  置く。
- `claim boundary`: 固定した一般 carrier `U`、G-110 の presentation /
  semantic 二層の上で語る。係数は動かさない。終対象・絶対積は導入
  しない。第一段は有限 carrier・有限 Source に限定。第二段・全域 lift
  の量化は semantic 層の exact-bottom 射(realization 資格なし)に
  及ぶが、carrier change・係数 base change・derived 系は域外(G-116
  カードの域外リストを継承)。診断側(G-111 / G-113)の量化域は変更
  しない。
- `capability categories`: coverage、classification、cartesian-lift、
  closure。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に
  置き、固定 statement と completion criteria だけで完了判定する。
- `portfolio constraint`: 第一段 coverage だけで完了扱いしない。第二段の
  帰趨決定・全域 lift の帰趨・拡張域閉性の全面に Lean artifact を要求
  する。負枝で確定する場合は資格条項を満たす特徴付け述語と同型閉包外
  反例の対を要求する。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、反証
  なら `target-refuted`、全完了条件と final review を満たした場合だけ
  `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各 cycle は
  proof obligation delta で評価する。
- `dullness filter`: 次を弾く。第二段負枝を「有限 presentation を持つ
  射」という像の定義の言い換え述語で立てる構成、無限 Source による
  cardinality 反例のみの放電、**「同型まで」を端点別同型(可換等式
  なし)で読んで射自体を実現せずに coverage を放電する構成**、第一段
  coverage を単一 fixture の列挙で代替する構成、拡張域閉性が恒等成分で
  vacuous に立つ構成、O6 正枝確定時に O7 を左枝定理の同型輸送の系で
  独立放電と数える構成(系として記録する — 計上規律)、**特徴付け
  述語を「同型まで恒等射」等の退化 class で立てる構成**(下記 (b) の
  資格条項 (v) 像包含が排除。言い換え述語の排除は (b) の条件言語
  規律が担う)。
- `frontier`: 第二段の特徴付け述語の最簡化・decider 化(G-107
  decider 前例との比較観察 — 必要性は (b) の外延一致から従うため
  独立 frontier としない)、可算 Source への拡張観察、係数 base
  change カードとの接続点。

- `target theorem`: **Exact-Bottom Coverage and Global Lift
  Classification Theorem**。G-110 の設定の上で:
  1. **(a) 第一段 coverage**: 有限 carrier・有限 Source 上の全 semantic
     exact-bottom 射が同型まで realization 像に入ることを証明する。
     **「同型まで」は arrow 圏の同型で読む** — 端点の semantic 同型対
     と可換等式(`toSemanticCart P ≫ i_target = i_source ≫ f` 型)を
     同時に要求し、端点別同型では放電と数えない。
  2. **(b) 第二段の帰趨決定**: sector 全域(有限 Source 制限なし —
     program context の O6 量化域裁定)について、「全域 coverage
     theorem」または「成立域の特徴付け+同型閉包外反例」の**二枝
     disjunction 単一命題**を証明する(G-110 (B) の分岐固定様式:
     排他性は反例が供給 — 反例が正枝を反証することを同時に証明する。
     網羅性は主張しない)。disjunction は carrier 大域一本で立て、
     述語と十分性は carrier に一様とする(per-carrier 分岐は採らない
     — G-110 (B) 様式)。「同型まで」の読みは (a) の arrow 圏同型で
     (b)(c) と (v) にも統一する。**条件言語規律**: 述語の許容原子式
     は semantic 入力(端点 instance と semantic 射)の構造データ上の
     条件に限る(例: Source の有限性・cardinality、抽出述語の有限性、
     射成分の有限 support 性)。presentation code 型・realization
     関数・有限 code / 表データの存在量化・「同型な像元の存在」への
     言及(その Skolem 化を含む)は原子式として禁止し、確定した条件
     言語への以後の原子式・量化形の追加は target 改訂扱いとする
     (G-110 `H_cart` の条件言語固定規律の転写)。述語の ambient 型は
     量化域型と同一とする(部分型上で立てない)。負枝の特徴付け述語
     には資格条項5項を課す — (i) 探索前固定の条件言語(上記規律と
     program context の fixed-head 手続き)、(ii) 結論(coverage /
     lift)非参照、(iii) 同型不変性、(iv) id / comp / pullback 閉性
     (pasting は (d) の square 水準で扱う)、(v) **像包含と非空
     発火** — 述語は realization 像を(同型まで)包含し、非恒等・
     非可逆成分と相異なる非同型 instance を含むパラメトリック正例族で
     strict 像の外(同型閉包の内でよい)にも非空に発火する(退化
     class は像包含が、言い換え述語は条件言語規律が排除する)。特徴
     付けは十分性 theorem(述語 → coverage)を要求する。適法な述語は
     像包含・同型不変性・十分性から coverage 成立域と外延一致するため、
     必要性(coverage → 述語)は独立成果に数えない。
  3. **(c) 全域 lift の帰趨**: G-110 左枝(realization 付き入力上の
     全域 strong cartesian lift)の realization 資格外への拡張に
     ついて、成立 theorem または「成立域の特徴付け+反例」の二枝
     disjunction 単一命題を証明する(様式は (b) と同一: 排他性は反例が
     供給、網羅性は主張しない。両枝の量化域一致・条件言語規律・特徴
     付け述語の資格条項も (b) と同一に適用する)。**計上規律**: O6
     正枝確定時に本 conjunct が左枝定理の系として従う場合は系として
     記録する(独立放電と数えない)。O6 負枝確定時に本 conjunct の
     十分性が (b) の十分性と左枝定理の系として従う場合も系として記録
     し、本 conjunct の独立実質は反例(lift 不在証明)側に置く。
  4. **(d) 拡張域閉性**: 確定した成立域での id / comp / pullback /
     pasting 閉性を証明する。中身は成立域上の coverage / lift 証拠の
     合成・引き戻し・貼り合わせ整合(G-110 presentation 閉性
     constructor の拡張域版)であり、(b) 資格条項 (iv) の述語閉性とは
     別 artifact とする(流用を計上しない)。成立域 membership は
     direction hypothesis として消費してよいが、合成後 membership との
     整合は証明する。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下の新
  module。reviewed module は参照のみ。完了面は (a)–(d) まで。二枝の
  payload は G-110 `DisjunctionArtifact` 様式の構造化 artifact で立て、
  payload の caller 供給を放電と数えない。反例枝の witness は
  per-universe 固定(= 各 universe における witness 族の構成であり、
  単一 universe への固定ではない)または枝条件付き endpoint 契約で
  立てる(無限 carrier 反例は有限 fixture の内部生成 lift による
  universe 移送が使えず、cross-universe reindexing は域外のため —
  G-116 カード台帳注記の universe 規律の適用第一号)。endpoint 契約の
  選択は F0 で symbolic universe の型不能を記録した場合に限り
  (G-116 台帳注記の前提条件を継承)、endpoint 固定の許容範囲は反例
  fixture の居住 universe のみとする。特徴付け述語・十分性・資格
  theorem 群・(d) の閉性は universe-polymorphic に立てる。
- `target proof artifacts`: 第一段 coverage theorem(arrow 圏同型
  水準)、第二段二枝確定 artifact(正枝 theorem または資格条項付き
  特徴付け述語+同型閉包外反例+正枝反証)、全域 lift 帰趨 artifact、
  拡張域閉性 theorem、特徴付け述語の資格 theorem 群(同型不変性・
  閉性・像包含・非空発火族)、report
  `research/reports/G-112-aat-exact-bottom-coverage.md`。
- `target proof strategy`: F0 typing(特徴付け述語の条件言語 —
  有限 Source 条件を第一候補として資格審査 — と二枝 payload 構造・
  universe 契約を固定)→
  K0 第一段 coverage → K1 第二段帰趨 → K2 全域 lift 帰趨 → K3 閉性と
  監査。既存成果の利用 map: `GlobalCartesianLift` / `CartesianRegime` /
  `cartesianRegimeOfDisjunction`(左枝定理の錨)、
  `cartesianLiftNonexistence_isEmpty`(枝整合)、presentation 閉性
  constructor 4種、`FiniteModel`(witness 計算)。
- `target theorem completion criteria`: 全 artifact が sorry なしで
  `ResearchLean` に受理され、axiom / placeholder audit が clean で
  あること。下記 ledger の `discharge-required` を放電し、audit で
  provenance、proof-use、structure-field escape、route integrity を監査
  すること。二段 review gate(各実装 PR の標準 fixed-head
  `$review-pr`、completion candidate での Lean / report / tracking
  Issue 同期と final review packet 作成、独立 `$math-lean-review`
  4査読全 `No major findings`)と CI・merge・最終 Issue 同期を通過
  した場合だけ完了する(正本 = target-goal-contract.md)。
- `target premise discharge policy`: 入力(presentation・semantic 射・
  witness fixture)だけを残せる。coverage・lift 存在・特徴付けの結論
  相当データの供給は放電と数えない。
- `target material premise ledger`:
  - `G-110 reviewed artifact`: `ambient-boundary`。参照のみ、改変
    しない。固定錨: DoctrineFiberProduct = 完了 PR #4153(final head
    `a1471483`、merge `315a2537`)。G-101 / G-106 / G-109 と
    `FiniteModel` 系 witness 基盤の固定錨は G-110 カード ledger の錨を
    継承する。支える結論 = 全 conjunct の設定と左枝定理。proof-use =
    (a)–(d) の設定・左枝錨の同型輸送・witness 計算。結論相当でない
    理由 = 入力幾何と既証明の環境であり、本カードの coverage / 帰趨
    は供給しない。
  - `第一段 coverage theorem`: `discharge-required`。支える結論 =
    (a)。discharge artifact = arrow 圏同型水準の coverage 証明。
    provenance = 構成した presentation と同型対・可換等式の生成証明。
    proof-use = (a) の放電と (b) 像包含審査の参照点。結論相当でない
    理由 = 同型対と可換等式は構成して証明する。
  - `第二段二枝確定`: `discharge-required`。支える結論 = (b)。
    discharge artifact = 正枝 theorem、または資格5項を満たす特徴付け
    述語+十分性+同型閉包外反例+正枝反証。provenance = (b) の条件
    言語規律内で F0 固定した述語と、生成した十分性証明・反例。
    proof-use = 反例は payload の実消費で結ぶ。結論相当でない理由 =
    条件言語規律が結論参照を排除し、十分性・反例は証明する。
  - `全域 lift 帰趨`: `discharge-required`。支える結論 = (c)。
    discharge artifact = 成立 theorem、または特徴付け+反例+正枝反証
    (様式・資格は (b) と同一)。provenance = G-110 左枝錨と生成した
    lift 構成 / lift 不在証明。proof-use = (c) の計上規律(正枝時・
    負枝時の系記録)に従って結ぶ。結論相当でない理由 = lift 存在の
    caller 供給を認めない。
  - `拡張域閉性`: `discharge-required`。支える結論 = (d)。discharge
    artifact = 成立域上の合成・引き戻し・貼り合わせ整合 theorem
    ((b) 資格条項 (iv) とは別 artifact)。provenance = 閉性
    constructor の拡張域版構成。proof-use = (b)(c) の成立域定理を実
    消費する。結論相当でない理由 = 閉性は証明し、(iv) の流用を計上
    しない。
  - `反例 / witness fixture`: `conclusion-equivalent-risk`。支える
    結論 = (b)(c) の排他性と資格条項 (v) の発火族。provenance =
    proof obligation 選定時に固定する authored 有限 data。proof-use =
    正枝反証と (v) の非空発火で実消費する。監査 artifact = 選定時
    固定の記録(証明後の target-fitting 選択の禁止)と非退化条項
    (非恒等・非可逆成分、相異なる非同型 instance)。結論相当でない
    理由 = fixture は入力幾何であり、反証・発火の証明は生成する。
  - `成立域 membership 証拠`: `direction-hypothesis`。支える結論 =
    (d)。provenance = (b)(c) で確定した成立域の述語成立証明。
    proof-use = 閉性 theorem の仮定として実消費する。結論相当でない
    理由 = membership は入力仮定だが、合成後 membership との整合は
    証明する。
- `target route integrity gate`: 特徴付け述語は探索前固定の条件言語で
  立て、fixture 値・checker 出力・target 結果由来の定数を持ち込ま
  ない。反例 fixture は proof obligation 選定時に固定する。二枝
  payload は構造化 artifact で立て、caller 供給を認めない。禁止経路 —
  像の定義の言い換え、cardinality のみの放電、端点別同型 coverage、
  証明後の target-fitting 選択。
- `target anti-weakening rule`: coverage・lift 存在・成立域所属を
  theorem argument、typeclass、structure field、certificate field、
  opaque class membership へ移して成功扱いしない。特徴付け述語と
  結論の**定義的同値**(定義展開・Skolem 化で結論に一致する述語)・
  単一 fixture 等式型を禁じる — 適法述語の外延一致((b) 末尾)は
  違反ではなく、必要性は独立成果に数えない。`ambient-boundary` に
  残せるのは入力幾何だけである。
- `target failure policy`: fail-closed を原則とする。(a) の反例は中心
  conjunct 反証 = `target-refuted`。(d) の反例(成立域上の閉性の
  反証)も `target-refuted`。(b)(c) は二枝 disjunction であり
  どちらの枝の確定も成功、両枝とも閉じない場合は `target-blocked`。
  F0 での型不能・statement 不足は `goal-defect`。witness の停滞は
  `target-blocked`。fixed target の変更は人間の別判断とする。
