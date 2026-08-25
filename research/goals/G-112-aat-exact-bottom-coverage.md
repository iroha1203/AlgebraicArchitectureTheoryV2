# G-112-aat-exact-bottom-coverage — exact-bottom coverage と全域分類

- `id`: `G-112-aat-exact-bottom-coverage`
- `status`: `draft`
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
  て再固定する(伝播規定)。**昇格前の裁定事項**: 第二段(O6)の
  量化域(有限 Source 制限の有無)— ただし**両枝の量化域は一致させ
  る**: 制限ありを選ぶ場合、その帰結は正枝ではなく負枝の特徴付け
  (述語 = 有限 Source 条件)として計上する(排他性様式の保護)。
- `predecessor`: G-110(完遂済み。(B) 左枝 = **realization 付き入力上
  の**全域 strong cartesian lift、presentation schema (s1)–(s6)、閉性
  constructor。固定錨は下記 ledger 行)。
- `tracking issue`: 未起票(active 昇格時に起票)
- `source note`: [docs/note/n1007_aat_sakura_gr4_completion_design.md](../../docs/note/n1007_aat_sakura_gr4_completion_design.md)(§3 義務台帳、§4 G-112)、
  [G-110 カード](G-110-aat-doctrine-fiber-product.md)(gate (i)・frontier の coverage 二段)
- `research aim`: G-110 は realization 像(有限 presentation 付き底層
  射)上の subcalculus を立てた。本カードは像と sector 全域の間を分類
  する — (第一段)有限 carrier 上では全 semantic exact-bottom 射が
  同型まで像に入ることを証明し、(第二段)sector 全域については成立か、
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
  する。負枝で確定する場合は資格条項を満たす特徴付け述語と像外反例の
  対を要求する。
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
  資格条項 (v) が排除)。
- `frontier`: 第二段の特徴付け述語の必要十分化(成立域の完全分類)、
  特徴付け述語と decider の関係(G-107 decider 前例との比較観察)、
  可算 Source への拡張観察、係数 base change カードとの接続点。

- `target theorem`: **Exact-Bottom Coverage and Global Lift
  Classification Theorem**。G-110 の設定の上で:
  1. **(a) 第一段 coverage**: 有限 carrier・有限 Source 上の全 semantic
     exact-bottom 射が同型まで realization 像に入ることを証明する。
     **「同型まで」は arrow 圏の同型で読む** — 端点の semantic 同型対
     と可換等式(`toSemantic P ≫ i_target = i_source ≫ f` 型)を同時に
     要求し、端点別同型では放電と数えない。
  2. **(b) 第二段の帰趨決定**: sector 全域について、「全域 coverage
     theorem」または「成立域の特徴付け+像外反例」の**二枝 disjunction
     単一命題**を証明する(G-110 (B) の分岐固定様式: 排他性は反例が
     供給 — 反例が正枝を反証することを同時に証明する。網羅性は主張
     しない)。負枝の特徴付け述語には資格条項5項を課す — (i) 探索前
     固定の条件言語、(ii) 結論(coverage / lift)非参照、(iii) 同型
     不変性、(iv) id / comp / pullback / pasting 閉性、(v) **像包含と
     非空発火** — 述語は realization 像を(同型まで)包含し、非恒等・
     非可逆成分を含むパラメトリック正例族で像の外にも非空に発火する
     (退化 class・言い換え述語の排除)。特徴付けは十分性 theorem
     (述語 → coverage)を要求し、必要十分化は frontier とする。
  3. **(c) 全域 lift の帰趨**: G-110 左枝(realization 付き入力上の
     全域 strong cartesian lift)の realization 資格外への拡張に
     ついて、成立 theorem または「成立域の特徴付け+反例」の二枝
     disjunction 単一命題を証明する(様式は (b) と同一: 排他性は反例が
     供給、網羅性は主張しない。特徴付け述語の資格条項も (b) と同一)。
     **計上規律**: O6 正枝確定時に本 conjunct が左枝定理の系として従う
     場合は系として記録する(独立放電と数えない)。
  4. **(d) 拡張域閉性**: 確定した成立域での id / comp / pullback /
     pasting 閉性を証明する。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下の新
  module。reviewed module は参照のみ。完了面は (a)–(d) まで。二枝の
  payload は G-110 `DisjunctionArtifact` 様式の構造化 artifact で立て、
  payload の caller 供給を放電と数えない。反例枝の witness は
  per-universe 固定または枝条件付き endpoint 契約で立てる(無限
  carrier 反例は有限 fixture の内部生成 lift による universe 移送が
  使えず、cross-universe reindexing は域外のため — G-116 カード台帳
  注記の universe 規律の適用第一号)。
- `target proof artifacts`: 第一段 coverage theorem(arrow 圏同型
  水準)、第二段二枝確定 artifact(正枝 theorem または資格条項付き
  特徴付け述語+像外反例+正枝反証)、全域 lift 帰趨 artifact、拡張域
  閉性 theorem、特徴付け述語の資格 theorem 群(同型不変性・閉性・像
  包含・非空発火族)、report
  `research/reports/G-112-aat-exact-bottom-coverage.md`。
- `target proof strategy`: 昇格レビュー(O6 量化域の裁定)→ F0 typing
  (特徴付け述語の条件言語・二枝 payload 構造・universe 契約を固定)→
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
  4査読全 `No major findings`)を通過すること(正本 =
  target-goal-contract.md)。
- `target premise discharge policy`: 入力(presentation・semantic 射・
  witness fixture)だけを残せる。coverage・lift 存在・特徴付けの結論
  相当データの供給は放電と数えない。
- `target material premise ledger`:
  - `G-110 reviewed artifact`: `ambient-boundary`。参照のみ、改変
    しない。固定錨: DoctrineFiberProduct = 完了 PR #4153(final head
    `a1471483`、merge `315a2537`)。G-101 / G-106 の固定錨は G-110
    カード ledger の錨を継承する(支える結論 = 全 conjunct の設定と
    左枝定理。結論相当でない理由 = 入力幾何と既証明の環境)。
  - `第一段 coverage theorem`: `discharge-required`(支える結論 =
    (a)。discharge artifact = arrow 圏同型水準の coverage 証明。結論
    相当でない理由 = 同型対と可換等式は構成して証明する)。
  - `第二段二枝確定`: `discharge-required`(支える結論 = (b)。
    discharge artifact = 正枝 theorem、または資格5項を満たす特徴付け
    述語+十分性+像外反例+正枝反証。proof-use = 反例は payload の
    実消費で結ぶ)。
  - `全域 lift 帰趨`: `discharge-required`(支える結論 = (c)。O6 正枝
    時の系計上規律を含む)。
  - `拡張域閉性`: `discharge-required`(支える結論 = (d))。
- `target route integrity gate`: 特徴付け述語は探索前固定の条件言語で
  立て、fixture 値・checker 出力・target 結果由来の定数を持ち込ま
  ない。反例 fixture は proof obligation 選定時に固定する。二枝
  payload は構造化 artifact で立て、caller 供給を認めない。禁止経路 —
  像の定義の言い換え、cardinality のみの放電、端点別同型 coverage、
  証明後の target-fitting 選択。
- `target anti-weakening rule`: coverage・lift 存在・成立域所属を
  theorem argument、typeclass、structure field、certificate field へ
  移して成功扱いしない。特徴付け述語と結論の論理同値・単一 fixture
  等式型を禁じる。`ambient-boundary` に残せるのは入力幾何だけである。
- `target failure policy`: fail-closed を原則とする。(a) の反例は中心
  conjunct 反証 = `target-refuted`。(b)(c) は二枝 disjunction であり
  どちらの枝の確定も成功、両枝とも閉じない場合は `target-blocked`。
  F0 での型不能・statement 不足は `goal-defect`。witness の停滞は
  `target-blocked`。fixed target の変更は人間の別判断とする。
