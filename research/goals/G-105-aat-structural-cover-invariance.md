# G-105-aat-structural-cover-invariance — 構造被覆の底不変性

- `id`: `G-105-aat-structural-cover-invariance`
- `status`: `active`
- `priority`: `medium`
- `research mode`: `target-theorem`
- `predecessor`: G-102(二相係数の障害 support 定理、`target-theorem-proved`。
  report
  [research/reports/G-102-aat-two-phase-obstruction.md](../reports/G-102-aat-two-phase-obstruction.md))。
  依存 profile / 二相分解 / Atom-indexed 係数複体の確定 artifact
  (`research/lean/ResearchLean/AG/TwoPhase/` 配下)を正本として参照する。
- `tracking issue`: [#3950](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/3950)
- `source note`: [docs/note/atom_is_all_you_need_discussion.md](../../docs/note/atom_is_all_you_need_discussion.md)(§2 幾何対応仮説、§8 候補9)
- `research aim`: 「構造が空間を運び、意味が係数を運ぶ」を theorem に
  する。構造 Atom の定義(依存 profile が宣言変形族に不感)から、構造
  Atom が張る被覆 nerve は語用論的 doctrine 変更(変形族内の semantic
  成分の取り替え)で不変であり、取り替えで動くのは係数側だけであることを
  導く。これにより、異なる言語ゲーム(semantic 変種)の障害類が**同一
  複体上の類**として比較可能になることを固定する。二相分解が単なる分類
  ではなく、doctrine 間比較の well-definedness の前提条件であることを
  示す。
- `core tension`: 「構造 Atom は変形族不変」は定義そのものであり、nerve
  不変性の核が定義の言い換え(tautology)に堕ちる危険が本カード最大の
  リスクである。実質は二つの対比に置く。第一に、**全 Atom で張った
  nerve は変形族内で実際に変わる**(semantic Atom の出入りが chart /
  overlap を変える)有限反例 — 構造 nerve の不変性はこの対比があって
  はじめて内容を持つ。第二に、nerve が不変でも**係数(semantic 成分)は
  実際に動く** — 同一複体上で障害類が変種ごとに異なる有限例。不変な
  空間と動く係数の分離こそが主張である。
- `rival`: 静的解析の「構文情報は設定に依らない」という folklore、
  既存の二相を持たない単相 nerve 構成(第II部・第IV部)。差は「不変性を
  依存 profile から導出し、不変が破れる側(全 Atom nerve)との対比と、
  同一複体上の障害類比較の well-definedness までを Lean witness で固定
  する」点に置く。
- `claim boundary`: 固定した一般 carrier `U`、G-102 の確定定義による宣言
  変形族(`TwoPhase/DependencyProfile.lean` の `DeclaredSemanticFamily`:
  semantic 成分の取り替え `SemanticVariant.replaceSemantic` の族、他成分
  固定)、その `Structural` / `Semantic` 判定(variant ごとの `extracts`
  真偽から導出。phase field 宣言は認めない)による構造 / 意味 pair、Atom
  データから被覆 nerve を生成する明示構成(カード内で定義)、Atom-indexed
  係数複体(`TwoPhase/CoefficientComplex.lean` の
  `AtomIndexedNerveData` / `AtomIndexedCoefficientComplex`)を対象とする。
  量化の有限性境界を分ける: **(i)(ii) は一般 carrier で主張する。
  (iii)(iv)(v) は有限 regime**(`U.Atom` と `D.Source` の Fintype、
  decidable な extracts。G-102 複体の Fintype 要求と整合する入力有限性)を
  ambient として仮定する。係数体は `ℚ` に固定する。台の族が Source を
  覆うことは要求しない(「被覆」の語は nerve 構成の慣用として使い、
  covering 性をどの主張にも使わない)。
  doctrine の構文成分(vocabulary / resolution / normalize)を動かす変形、
  carrier を動かす主張、blame の gauge 理論(coboundary 移動の分類)、
  係数の同型分類、台の包含を持たない variant 対の間の comparison は
  含めない。
- `capability categories`: invariance、cover-generation、
  coefficient-localization、comparability、counterexample。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に
  置き、固定 statement と completion criteria だけで完了判定する。
- `portfolio constraint`: 不変性の正例だけで完了扱いしない。対比反例
  2種(全 Atom nerve の可変性・係数の実変動)を必須とする。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、反証なら
  `target-refuted`、全完了条件と final review を満たした場合だけ
  `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各 cycle は
  proof obligation delta で評価する。
- `dullness filter`: 次を弾く。変形族が空・単元で不変性が自明化する例、
  全 Atom が構造的(semantic pair 不在)で対比が消える例、nerve 生成
  構成が定数(Atom に依らない)で不変性が構成の退化から従う例、係数の
  「変動」が零複体間の自明差である例、(v) の変動が同一類の代表差・
  cochain 値差にすぎない発火、定義の言い換えだけで対比反例を
  欠く完了主張。
- `frontier`: blame の doctrine 間比較(gauge 側)の予備観察、構文成分
  まで動かした場合に何が壊れるかの観察、nerve 生成構成の変種(relation
  Atom 主導 / component Atom 主導)の比較。

- `target theorem`: **Structural Cover Base Invariance Theorem**。
  固定した一般 carrier `U` 上、G-102 の意味の doctrine `D` と宣言変形族
  `fam`(`DeclaredSemanticFamily`)に対し、被覆 nerve の canonical 生成
  構成 `nerveOf` を次で固定する(supplied incidence は認めない):
  - 各 atom `a` の**台** `supp(a) := {s | extracts s a}`。構造版は
    `supp_struct(a) := {s | extracts s a ∧ fam.Structural (s, a)}`。
  - chart = 台が非空な atom、edge = 台の交わりが非空な atom 対、face =
    台の三重交わりが非空な atom triple(台の族の Čech nerve)。
  - **phase 分類は base `D` と `fam` の `Structural` で一度だけ**取り、
    variant 側で再分類しない。`D[γ] := γ.replaceSemantic` の nerve は
    `D[γ].extracts` で台を取り直して同一規則で生成する。
  この設定で次を証明する。
  1. **(i) 構造 nerve の不変性**: 構造版 `nerveOf_struct` は、すべての
     `γ ∈ fam` について `D[γ]` と `D` で**等式**として一致する
     (canonical equality。`replaceSemantic` は Source / Atom 型を変えず、
     `Structural` pair の extracts 真偽不変から構造台の等式が従う)。
     同型への弱化は認めない。
  2. **(ii) 全 Atom nerve の可変性(対比反例)**: 全 pair 版
     `nerveOf_all` が `fam` 内の取り替えで実際に変わる有限反例。
  3. **(iii) 係数の局在**: 係数複体は variant ごとに、次の**係数生成
     規則**で抽出データから構成する(G-102 の
     `AtomIndexedCoefficientComplex` は構成済み複体を受ける容れ物で
     あり constructor ではないため、生成は本カードが固定する。生成した
     複体を G-102 型へ instance 化して接続し、`all` を結論相当データと
     して先渡ししない):
     - **座標 index**: 各 cell の係数 basis は対 `(cell, s)`。`s` は
       cell の**導出台**上の点(chart の台 = `supp_γ`、edge / face の
       台は端点 / boundary の台の交わりとして導出。独立な台宣言は
       持たない)。係数体は `ℚ`。
     - **differential**: 同一 label `s` の恒等対応による Čech 交代和
       (`d₀` = 端点差、`d₁` = boundary 交代和)。label 不在は零。
     - **phase**: chart basis `(a, s)` の phase = `fam.Structural (s, a)`
       (base 分類の共有)。edge / face basis は関与する全 chart で
       structural のとき structural。構造部分複体 = structural basis の
       span。
     各 variant の `ConditionE` 成立は仮定側に置く。このとき構造部分
     複体は (i) の等式の下で**全 variant で同一**であり、変形族内の
     取り替えは商(semantic)側の係数だけを動かす。
  4. **(iv) 比較可能性(包含対)**: 台の包含を持つ variant 対
     (すべての atom で `supp_γ(a) ⊆ supp_γ'(a)`)に対し、label-wise の
     制限(projection)`all_γ' → all_γ` が cochain map であることを
     生成規則から theorem として導き(導出台の交わり構造により制限が
     differential と可換になる)、それが誘導する障害類の comparison が
     同一の構造 nerve 上で well-defined であることを示す(comparison を
     opaque field や仮定で受けない)。包含を持たない一般対の comparison
     は claim しない(frontier)。
  5. **(v) 発火 witness**: 非恒等な取り替え(包含対)で、nerve は不変の
     まま障害類が実際に変わる有限 witness。**(iv) の comparison の下で
     類そのものが異なる — 差が coboundary に落ちない — こと**を要求し、
     同一類の代表差・cochain 値差だけの発火は数えない。両相非空を要求
     する。
  (i)(ii) は一般の `D` / `fam`、(iii)(iv) は有限 regime の `D` / `fam` に
  ついて証明する。witness((ii)(v))は既存 `FiniteModel` の carrier へ
  具体化する。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/StructuralCover/` 配下。`Formal/AG` は
  参照のみ。G-105 の完了面は (i)–(v) まで。blame 代表の移動・gauge
  fixing・doctrine 間の複体 comparison の一般論は主張しない。
- `target proof artifacts`: `nerveOf` 生成構成(台 Čech nerve)の定義、
  構造 nerve 不変性(等式)theorem、全 Atom nerve 可変性反例、
  係数生成規則(座標・導出台・differential・phase)の def と G-102 型への
  instance 化、包含対の制限 cochain map の構成 def とその cochain 性
  theorem、係数局在 theorem、比較可能性 theorem、類差発火 witness、
  report `research/reports/G-105-aat-structural-cover-invariance.md`。
- `target proof strategy`: I0 nerve 生成構成の定義 -> I1 構造 nerve
  不変性 -> I2 全 Atom nerve 可変性反例 -> I3 係数局在と比較可能性 ->
  I4 発火 witness。既存成果の利用 map:
  `research/lean/ResearchLean/AG/TwoPhase/DependencyProfile.lean`
  (`DeclaredSemanticFamily` / `Structural` / `Semantic` /
  `FiniteDependencyProfile`。review 済み、再定義しない)、
  `research/lean/ResearchLean/AG/TwoPhase/CoefficientComplex.lean`
  (`AtomIndexedNerveData` とその `expandedNerve`、
  `AtomIndexedCoefficientComplex` / `ConditionE` / `structuralComplex` /
  `semanticComplex`。本カードの `nerveOf` は Atom データからの生成構成と
  して新設し、`expandedNerve` との関係(再利用または対比)を I0 で明示
  する)、`research/lean/ResearchLean/AG/TwoPhase/FiniteWitnesses.lean`
  (witness 素材の再利用は任意)、
  `Formal/AG/Cohomology/CoverNerve.lean` の `CoverNerve` 型(参照のみ)、
  `Formal/AG/Examples/FiniteModel.lean`(witness 素材)。固定 statement と
  完了条件は本カードのみを正本とする。
- `target theorem completion criteria`: 全 artifact が sorry なしで
  `ResearchLean` に受理され、axiom / placeholder audit が clean である
  こと。ledger の `discharge-required` を放電し、T3 audit を通し、
  Lean / report / tracking Issue を同期し、
  `$math-lean-review research/goals/G-105-aat-structural-cover-invariance.md G-105-aat-structural-cover-invariance`
  の4査読がすべて `No major findings` であること。
- `target premise discharge policy`: 入力に残せるのは doctrine と変形族
  だけである。nerve 生成構成はカード固定の canonical 構成(台 Čech
  nerve)であり、incidence を入力データとして受け取らない。不変性、
  可変性反例、係数局在、比較可能性、variant 間 comparison はすべて
  completion までに生成・証明する。不変性・同型相当のデータを
  certificate や structure field で受け取るだけでは放電と数えない。
  各 variant の `ConditionE` だけは (iii)(iv) の仮定側に置ける。
- `target material premise ledger`:
  - `carrier U / FiniteModel`: `ambient-boundary`。(iii)(iv)(v) では
    有限 regime(`Fintype`・decidable extracts)を入力有限性として含む。
  - `依存 profile / 二相分解`: `ambient-boundary`(G-102 の確定 artifact
    `TwoPhase/DependencyProfile.lean` の参照のみ。再定義しない)。
  - `nerve 生成構成`: `discharge-required`。カード固定の台 Čech nerve
    構成を定義し、退化(定数構成)でないことを witness で示す。
  - `構造 nerve 不変性`: `discharge-required`。構造 pair の `fam`-不変性
    から**等式**として導出する。不変性を構成の field に入れない。
  - `全 Atom nerve 可変性`: `discharge-required`。有限反例。型不一致
    vacuity は不可。
  - `係数生成規則と variant 間 comparison`: `discharge-required`。
    カード固定の生成規則(`(cell, s)` 座標・導出台・Čech differential・
    base phase 分類)から各 variant の複体を構成して G-102 型へ
    instance 化し、構造部分複体の全 variant 同一性と、包含対の制限
    cochain map の cochain 性を theorem 化する。`all` complex や
    comparison を opaque field で受けることは放電と数えない。
  - `各 variant の ConditionE`: `direction-hypothesis`。(iii)(iv) の
    含意の仮定側。結論相当でない理由: 単一 variant 内部の構造 support
    保存条件(G-102 で特定済みの条件 E)であり、variant 間 comparison・
    障害類の一致を参照しない。
  - `係数局在と比較可能性`: `discharge-required`。構造部分複体の固定と
    semantic 側だけの変動を theorem で示す。
  - `類差発火 witness`: `discharge-required`。(iv) の comparison の下で
    類が異なることまで含む。route integrity audit で使う。
- `target anti-weakening rule`: (i) を「nerve の濃度が等しい」等の弱い
  不変量や明示同型へ弱めない(等式で主張する)。(ii) を
  欠いた不変性だけの完了を認めない。(iii) の局在を「係数が変わりうる」
  の存在主張へ弱めない(構造部分の固定を含む)。(iv) の comparison を
  同型の仮定・opaque field で先取りしない。(v) を代表差・cochain 値差へ
  弱めない(comparison の下の類の差で主張する)。結論相当データを
  theorem argument、typeclass、structure field、certificate field へ
  移さない。
- `target route integrity gate`: nerve 生成・不変性・反例・witness の
  provenance を doctrine 構成データ、変形族、生成構成、review 済み
  predecessor へ追跡する。変形族退化・全 Atom 構造的・定数生成構成に
  よる発火を completion に使わない。
- `target failure policy`: (i)(iii)(iv) の反例(構造 nerve が変形族内で
  変わる等)は `target-refuted` とし、依存 profile または nerve 生成構成の
  改訂案を返す — これは二相分解の設計欠陥の検出として価値がある。
  (ii) は反例構成が成功条件であり、「全 Atom nerve も常に不変」と証明
  された場合は生成構成が Atom を読んでいない仕様欠陥として GOAL 改訂案を
  返す。同じ blocker が二 cycle 続けば `target-blocked`。
