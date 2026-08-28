# G-114-aat-refinement-base-change — refinement 圏化と refinement base change

- `id`: `G-114-aat-refinement-base-change`
- `status`: `draft`
- `priority`: `high`
- `research mode`: `target-theorem`
- `program context`: Gr4 完遂 gate 第二項の担当カード(担当義務 =
  O8–O9。義務台帳の正本は G-116 カード、設計の source note は n1007
  §3–§5)。依存は G-110 のみであり、G-111 系と並走可能。**供給契約**:
  本カードの成果物は G-116 gate (iv) の refinement regime 型
  (または退化定理という帰趨)を供給する — G-116 は regime を新設建設
  しないため、この供給は成果物形式の義務である(退化枝で確定した場合の
  G-116 側の扱いは G-116 カードの量化域規律に従う)。**新設語彙の
  命名権**: refinement 圏の命名は本カード専属。本カードの改訂は
  G-116 の達成記録要件へ伝播する。依存する reviewed カード(G-110 /
  G-101)の statement が改訂された場合、本カードは draft へ差し戻して
  再固定する(伝播規定)。
- `predecessor`: G-110(完遂済み。(A) fiber product・pointed 化・
  presentation 閉性。固定錨は下記 ledger 行)、G-101
  (`RefinementDoctrineHom` の定義元。
  `research/lean/ResearchLean/AG/AtomFoundation/` 配下、unported)。
- `tracking issue`: 未起票(active 昇格時に起票)
- `source note`: [docs/note/n1007_aat_sakura_gr4_completion_design.md](../../docs/note/n1007_aat_sakura_gr4_completion_design.md)(§3 義務台帳、§4 G-114)、
  [G-110 カード](G-110-aat-doctrine-fiber-product.md)(gate (ii)・frontier の refinement 圏化)
- `research aim`: exact hom の圏 `Doct_U` の外にいる refinement 射
  (`RefinementDoctrineHom` — 抽出の保存のみで反射を要求しない緩い射)
  を圏として立て、G-110 の fiber product がこの緩い射をどう扱えるかを
  決定する。refinement base change が成立するなら Gr4 の相対性は緩い
  射まで届き、退化するならその成立域の特徴付けと退化 witness が記録に
  なる。
- `core tension`: refinement 射は lax であり、G-101 opcartesian 輸送も
  G-110 の cartesian lift 理論も適用外である — refinement base change
  の成立は開いた問いであり、正枝を無条件には主張できない(だから二枝
  disjunction で立てる)。また比較 functor の方向は構造的に固定されて
  いる — `RefinementDoctrineHom` は `extraction_forward`(順方向保存)
  のみを field に持ち、逆方向の埋め込みは抽出の反射を要求するため型に
  載らない(反射不能の witness 定理が strict 性を実証する)。方向を
  誤ると F0 で型が立たない。
- `rival`: lax / oplax morphism と 2-categorical limit の一般論。差は
  「具体 doctrine 圏の refinement 射で成立・退化のどちらかを Lean で
  決定する(資格条項付きの成立域特徴付け込み)」点に置く。
- `claim boundary`: 固定した一般 carrier `U`、`RefinementDoctrineHom`
  (既存 reviewed 宣言 — 再定義しない)と G-110 fiber product の上で
  語る。係数は動かさない。終対象・絶対積は導入しない。**square の形を
  固定する**: (A) の exact cospan の pullback `P = D₁ ×_B D₂` に対し、
  refinement 射は引き戻される脚として与える(`f : D₁' → D₁` を pull
  して `P' → P` を得る配置)。exact 脚の refinement 置換は主張しない
  (配置の型可能性は F0 で確認し、配置の変更は改訂扱い)。carrier
  change・係数 base change・derived 系は域外(G-116 カードの域外
  リストを継承)。refinement 射の意味論の変更・強化はしない。
- `capability categories`: categorification、base-change、
  regime-construction、counterexample。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に
  置き、固定 statement と completion criteria だけで完了判定する。
- `portfolio constraint`: 圏化だけで完了扱いしない。二枝の帰趨確定・
  regime 型(正枝時)または資格条項付き成立域特徴付け+非退化 witness
  (退化枝時)・非退化 witness の全面に Lean artifact を要求する。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、反証
  なら `target-refuted`、全完了条件と final review を満たした場合だけ
  `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各 cycle は
  proof obligation delta で評価する。
- `dullness filter`: 次を弾く。圏化が hom の再ラベルに堕ちる構成
  (合成の非自明性 witness を要求する)、refinement pullback が恒等
  成分で vacuous に立つ構成、regime 型を supplied certificate で受ける
  構成、比較 functor を逆方向(反射を要求する向き)で仮定する構成、
  **退化枝を単一反例の存在命題だけで「退化定理」と呼ぶ構成**(成立域
  特徴付けを欠く形)、**G-110 既決 mate 正例の再包装による regime
  正枝放電**。
- `frontier`: refinement 圏の 2-cell(refinement 間の変形)の観察、
  refinement と indexed 診断輸送 exactness(G-113)の相互作用の観察、係数 base change
  カードとの接続点。

- `target theorem`: **Refinement Category and Refinement Base-Change
  Theorem**。G-101 / G-110 の設定の上で:
  1. **(a) refinement 圏の構成**: `RefinementDoctrineHom` を射とする圏
     構造(恒等・合成・結合律)を証明し、**`Doct_U` からの比較
     functor `Doct_U ⥤ Refin_U`**(exact hom を refinement として
     埋める方向)を構成する。逆方向の埋め込みは `extraction_forward`
     のみの field 構成上型に載らず(strict 性の witness =
     `finiteExtractionRefinement_not_reflecting`)、主張しない —
     方向をこの形で固定する。
  2. **(b) refinement base change の帰趨決定**: **二枝 disjunction
     単一命題**として、「claim boundary の固定配置で fiber product が
     refinement 射を pullback で安定に持ち上げ、refinement に沿った
     BC 比較射と mate 比較が定義される **regime 型**(reindexing・
     随伴相当の装置)が建設できる」または「**退化の分類** — 資格条項
     付きの成立域特徴付け(G-112 (b) と同一の資格5項: 探索前固定の
     条件言語・結論非参照・同型不変性・閉性・像包含と非空発火)+
     持ち上げ不能の非退化反例(非恒等 refinement 射・非自明 fiber
     product 上)」のどちらかを証明する(排他性は反例側が供給、網羅性
     は主張しない)。
  3. **(c) 非退化 witness**: 恒等でない refinement 射の pullback が非
     自明に立つ有限 fixture を構成する(正枝時。退化枝の場合は (b) の
     非退化反例がこれを兼ねる)。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下の新
  module(refinement 圏の宣言は本カードの命名権)。
  `RefinementDoctrineHom` と AtomFoundation の reviewed module は参照
  のみ。完了面は (a)–(c) まで。二枝の payload は G-110
  `DisjunctionArtifact` 様式の構造化 artifact で立て、payload の
  caller 供給を放電と数えない。refinement 射の圏の 2-cell 構造・
  refinement 診断は主張しない。
- `target proof artifacts`: refinement 圏の instance 一式と結合律
  theorem、比較 functor `Doct_U ⥤ Refin_U` と functor law、二枝確定
  artifact(正枝: pullback 安定性 theorem+BC 比較射+regime 型/
  退化枝: 資格条項付き成立域特徴付け+十分性+非退化反例)、非退化
  witness、report
  `research/reports/G-114-aat-refinement-base-change.md`。
- `target proof strategy`: F0 typing(圏 instance と比較 functor の
  signature、二枝 payload 構造、regime 型の候補 signature)→ K0 圏化と
  比較 functor → K1 pullback 安定性の判定 → K2 帰趨確定(regime 建設
  または退化分類)→ K3 witness と監査。既存成果の利用 map:
  `RefinementDoctrineHom`(射の定義)、`finiteExtractionRefinement`
  系(witness 素材と strict 性の実証)、G-110 (A) fiber product・
  `pointedPullback_isPullback`・presentation 閉性 constructor。
- `target theorem completion criteria`: 全 artifact が sorry なしで
  `ResearchLean` に受理され、axiom / placeholder audit が clean で
  あること。下記 ledger の `discharge-required` を放電し、audit で
  provenance、proof-use、structure-field escape、route integrity を監査
  すること。二段 review gate(各実装 PR の標準 fixed-head
  `$review-pr`、completion candidate での Lean / report / tracking
  Issue 同期と final review packet 作成、独立 `$math-lean-review`
  4査読全 `No major findings`)を通過すること(正本 =
  target-goal-contract.md)。
- `target premise discharge policy`: 入力(refinement 射・fixture)だけ
  を残せる。pullback 安定性・regime・退化の結論相当データの供給は放電
  と数えない。
- `target material premise ledger`:
  - `G-110 reviewed artifact`: `ambient-boundary`。参照のみ、改変
    しない。固定錨: DoctrineFiberProduct = 完了 PR #4153(final head
    `a1471483`、merge `315a2537`)(支える結論 = fiber product と
    pointed 化の設定。結論相当でない理由 = 既証明の環境)。
  - `RefinementDoctrineHom / finiteExtractionRefinement 系`:
    `ambient-boundary`。参照のみ、改変しない(G-101 の reviewed
    artifact — 固定錨は G-110 カード ledger の G-101 錨を継承。
    proof-use = 射の定義と strict 性 witness)。
  - `refinement 圏構造と比較 functor`: `discharge-required`(支える
    結論 = (a)。discharge artifact = 圏 instance+結合律+functor
    law。結論相当でない理由 = 構成して証明する)。
  - `二枝の帰趨確定`: `discharge-required`(支える結論 = (b)。
    discharge artifact = 正枝は安定性 theorem+regime 型、退化枝は
    資格条項付き特徴付け+十分性+非退化反例。proof-use = 反例は
    payload の実消費で結ぶ)。
  - `非退化 witness`: `discharge-required`(支える結論 = (c))。
- `target route integrity gate`: 比較 functor・BC 比較射・regime は
  refinement 射の定義と G-110 普遍性からのみ生成する。witness fixture
  は proof obligation 選定時に固定する。二枝 payload は構造化
  artifact で立て、caller 供給を認めない。禁止経路 — regime の
  certificate 供給、逆方向埋め込みの仮定、恒等成分での vacuous 発火、
  既決 mate 正例の再包装。
- `target anti-weakening rule`: pullback 安定性・mate 定義可能性・退化
  を theorem argument、typeclass、structure field、certificate field へ
  移して成功扱いしない。`ambient-boundary` に残せるのは入力幾何だけで
  ある。
- `target failure policy`: fail-closed を原則とする。(b) は二枝
  disjunction でありどちらの枝の確定も成功(退化枝も帰趨確定として
  G-116 カードの成立条件を満たす)。両枝とも閉じない場合は
  `target-blocked`。(a) の圏化が型不能・statement 不足は
  `goal-defect`。witness の停滞は `target-blocked`。fixed target の
  変更は人間の別判断とする。
