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
  依存は G-111(schema 基盤)。本カードの分類結果は G-113 / G-114 /
  G-115 の量化域を変更しない(各カードは G-110 固定の realization 付き
  入力上で立つ)。改訂は G-116 の達成記録要件へ伝播する。**昇格前の
  裁定事項**: 第二段(O6)正枝の量化域(有限 Source 制限の有無)。
- `predecessor`: G-110(完遂済み。(B) 左枝 = 全域 strong cartesian
  lift、presentation schema (s1)–(s6)、閉性 constructor。固定錨は
  G-111 カード ledger と同じ)、G-111(indexed schema — draft、昇格
  順で先行)。
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
  G-110 `H_cart` と同水準の資格条項(探索前固定の条件言語・結論非
  参照・同型不変性・閉性)を課す。
- `rival`: 有限表示対象(finitely presentable objects)と ind-completion
  の一般論。差は「具体 doctrine 圏での coverage の実証明と、資格条項
  付きの成立域特徴付け・全域 lift の帰趨決定を Lean で固定する」点に
  置く。
- `claim boundary`: 固定した一般 carrier `U`、G-110 の presentation /
  semantic 二層の上で語る。第一段は有限 carrier・有限 Source に限定。
  第二段・全域 lift の量化は semantic 層の exact-bottom 射(realization
  資格なし)に及ぶが、carrier change・係数・derived 系は域外(G-116
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
  cardinality 反例のみの放電、第一段 coverage を単一 fixture の列挙で
  代替する構成、拡張域閉性が恒等成分で vacuous に立つ構成、O6 正枝
  確定時に O7 を左枝定理の同型輸送の系で独立放電と数える構成(系と
  して記録する — 計上規律)。
- `frontier`: 第二段の特徴付け述語と decider の関係(G-107 decider 前例
  との比較観察)、可算 Source への拡張観察、係数 base change カードとの
  接続点。

- `target theorem`: **Exact-Bottom Coverage and Global Lift
  Classification Theorem**。G-110 の設定の上で:
  1. **(a) 第一段 coverage**: 有限 carrier・有限 Source 上の全 semantic
     exact-bottom 射が同型まで realization 像に入ることを証明する
     (有限 carrier では全抽出述語が有限集合で全置換が有限 support を
     持つ、という G-110 カードの観察を実証明化する)。
  2. **(b) 第二段の帰趨決定**: sector 全域について、「全域 coverage
     theorem」または「成立域の特徴付け+像外反例」の**二枝 disjunction
     単一命題**を証明する(G-110 (B) の分岐固定様式: 排他性は反例が
     供給、網羅性は主張しない)。負枝の特徴付け述語には資格条項
     (探索前固定の条件言語・結論非参照・同型不変性・閉性)を課す。
  3. **(c) 全域 lift の帰趨**: G-110 左枝(全域 strong cartesian
     lift)の realization 資格外への拡張について、成立 theorem または
     「成立域の特徴付け+反例」の二枝 disjunction 単一命題を証明する。
     O6 正枝確定時に本 conjunct が左枝定理の系として従う場合は系として
     記録する(独立放電と数えない)。
  4. **(d) 拡張域閉性**: 確定した成立域での id / comp / pullback /
     pasting 閉性を証明する。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下の新
  module。reviewed module は参照のみ。完了面は (a)–(d) まで。反例枝の
  witness は per-universe 固定または枝条件付き endpoint 契約で立てる
  (無限 carrier 反例は有限 fixture の内部生成 lift による universe
  移送が使えず、cross-universe reindexing は域外のため — n1007 §5
  universe 設計規則の適用第一号)。
- `target proof artifacts`: 第一段 coverage theorem、第二段二枝確定
  artifact(正枝 theorem または資格条項付き特徴付け述語+像外反例)、
  全域 lift 帰趨 artifact、拡張域閉性 theorem、特徴付け述語の資格
  theorem 群(同型不変性・閉性)、report
  `research/reports/G-112-aat-exact-bottom-coverage.md`。
- `target proof strategy`: F0 typing(特徴付け述語の条件言語・二枝
  disjunction の universe 契約を固定)→ K0 第一段 coverage → K1 第二段
  帰趨 → K2 全域 lift 帰趨 → K3 閉性と監査。既存成果の利用 map:
  `GlobalCartesianLift` / `CartesianRegime` /
  `cartesianRegimeOfDisjunction`(左枝定理の錨)、
  `cartesianLiftNonexistence_isEmpty`(枝整合)、presentation 閉性
  constructor 4種、`FiniteModel`(witness 計算)。
- `target theorem completion criteria`: 全 artifact が sorry なしで
  `ResearchLean` に受理され、axiom / placeholder audit が clean である
  こと。下記 ledger の `discharge-required` を放電し、audit で
  provenance、proof-use、structure-field escape、route integrity を監査
  すること。二段 review gate(各実装 PR の標準 fixed-head `$review-pr`
  +completion 時の独立 `$math-lean-review` 4査読全 `No major
  findings`)を通過すること(正本 = target-goal-contract.md)。
- `target premise discharge policy`: 入力(presentation・semantic 射・
  witness fixture)だけを残せる。coverage・lift 存在・特徴付けの結論
  相当データの供給は放電と数えない。
- `target material premise ledger`:
  - `G-110 reviewed artifact`: `ambient-boundary`。参照のみ(固定錨は
    G-111 カード ledger と同一)。
  - `G-111 indexed schema`: `ambient-boundary`(完遂後に final head を
    固定して昇格する — 昇格条件)。
  - `第一段 coverage theorem`: `discharge-required`。
  - `第二段二枝確定`: `discharge-required`。負枝は資格条項を満たす
    特徴付け述語+像外反例の対で放電する。
  - `全域 lift 帰趨`: `discharge-required`(O6 正枝時の系計上規律を
    含む)。
  - `拡張域閉性`: `discharge-required`。
- `target route integrity gate`: 特徴付け述語は探索前固定の条件言語で
  立て、fixture 値・checker 出力・target 結果由来の定数を持ち込ま
  ない。反例 fixture は proof obligation 選定時に固定する。禁止経路 —
  像の定義の言い換え、cardinality のみの放電、証明後の target-fitting
  選択。
- `target anti-weakening rule`: coverage・lift 存在・成立域所属を
  theorem argument、typeclass、structure field、certificate field へ
  移して成功扱いしない。特徴付け述語と結論の論理同値・単一 fixture
  等式型を禁じる。
- `target failure policy`: fail-closed を原則とする。(a) の反例は中心
  conjunct 反証 = `target-refuted`。(b)(c) は二枝 disjunction であり
  どちらの枝の確定も成功、両枝とも閉じない場合は `target-blocked`。
  fixed target の変更は人間の別判断とする。
