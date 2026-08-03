# G-103-aat-canonical-resolution — ambient canonical resolution と representability

- `id`: `G-103-aat-canonical-resolution`
- `status`: `active`
- `priority`: `high`
- `research mode`: `target-theorem`
- `tracking issue`: [#3897](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/3897)
- `source note`: [docs/note/atom_is_all_you_need_discussion.md](../../docs/note/atom_is_all_you_need_discussion.md)(§5–6、§7.1、§8 候補6、§12 スライス d)
- `research aim`: 有限 Source 上の law family `L` に対して ambient
  joint-kernel quotient `q_L`(`x ~_L y ⟺ ∀ l ∈ L, eval_l x = eval_l y`)を
  構成し、最粗の `L`-adequate reading であること(普遍性)と有限 regime
  での実効的計算可能性を証明する。そのうえで、宣言された admissible
  reading class の中での `q_L` の representability の正例と負例を有限
  instance で固定する。canonical resolution の非存在を「選んだ admissible
  class における representability failure」として読む二段構え(ambient
  存在+class 相対の表現可能性)を Lean artifact にする。
- `core tension`: ambient には `q_L` が常に存在する(joint-kernel 商は
  Set の世界で自明に取れる)。理論的重心は存在ではなく **representability
  の稜線**にある — 宣言された admissible class(抽出 doctrine が誘導する
  readings)の中に、L-adequate な reading は在るのに最粗のものが `q_L` に
  一致しない・あるいは `q_L` がどの doctrine でも実現されない状況が
  実在するか。負例が立てば「instance designer の選択が残る理由」の
  記述になり、正例しか立たなければ admissible class の定義が広すぎる
  ことの兆候として設計へ跳ね返る。負例が型不一致や class の空虚さで
  成立してしまえば定理は空洞になる — 負例の非退化条件の設計が核心。
- `rival`: 表示的意味論の full abstraction(Milner の項モデル商構成=
  ambient 存在の先例、Loader 型決定不能性=一般特徴づけの防御)、
  Myhill–Nerode 型の最小商(観測で分離する最粗の合同)、bisimulation の
  partition refinement 算法、抽象解釈の complete shell。差は「reading を
  抽出 doctrine が誘導する対象として固定し、representability の正負を
  同一有限モデル上の Lean witness で固定する」点に置く。既知算法・既知
  構成の instantiation で済む部分は流用してよいが、正負 witness と
  admissible class の定義は AAT 入力から構成する。
- `claim boundary`: 有限 Source(`Fintype` + `DecidableEq` regime)、
  有限 index 集合上の law evaluation 族 `eval_l : Source -> Value_l`
  (各 `Value_l` は `DecidableEq`)、reading = Source 上の商(kernel 同値で
  比較)、adequacy =「各 `eval_l` が reading を通して factor する」、
  admissible class = カード内で明示定義する doctrine 誘導 readings の
  有限族(族の各 doctrine の `Source` 成分は固定した有限 Source と一致
  する)を対象とする。無限 Source、
  一般 representability の特徴づけ(Goldblatt 型双条件)、決定不能性
  結果、concept lattice の一般論、二入口(方程式系先行 / Atom 先行)の
  合流 theorem、adequacy shell の一般存在、接地 certificate の分類は
  含めない。
- `capability categories`: ambient-quotient、universal-property、
  effective-computation、representability、obstruction。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に
  置き、固定 statement と completion criteria だけで完了判定する。
- `portfolio constraint`: 証明対象4面(ambient 構成と普遍性・実効計算・
  representability 正例・負例)がすべて Lean artifact で接続されること。
  正例だけ、または負例だけで完了扱いしない。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、反証なら
  `target-refuted`、全完了条件と final review を満たした場合だけ
  `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各 cycle は
  proof obligation delta で評価する。
- `dullness filter`: 次を弾く。空 `L`・単元 Source・全 law が定数で
  `q_L` が自明(全潰し・恒等)になる例だけの発火、admissible class が
  空・または L-adequate reading を一つも含まないことによる vacuous 負例、
  恒等(離散)reading の常時 adequacy だけを vacuity 排除の witness に
  立てる負例、Source の濃度・型の不一致だけで成立する負例、普遍性を「`q_L` より粗い
  adequate reading がない」の有限探索だけに弱めた確認、partition
  refinement の実装だけで正当性 theorem を欠く成果、既存 Myhill–Nerode
  類似の再証明で AAT 側の接続(doctrine 誘導 readings)を欠く成果。
- `frontier`: adequacy shell(representable でない場合の、与えられた
  reading を含む最粗の L-adequate 精細化)の有限 regime での構成の観察、
  `Expr(q)`(reading が表現できる law 族)の計算、L-gauge(`q_L` を通して
  恒等へ降りる source 変形)の観察、二入口合流条件の予備観察。

- `target theorem`: **Finite Canonical Resolution Representability
  Theorem**。有限 Source と law evaluation 族 `L` の上で次を構成する。
  - **reading と adequacy**: reading は Source 上の商(surjection または
    同値関係)とし、粗さは kernel の包含で比較する。reading `q` が
    `L`-adequate であるとは、各 `eval_l` が `q` を通して factor すること。
  - **admissible class**: 宣言された有限 doctrine 族が誘導する readings の
    族。族の各 doctrine は `Source` 成分が固定した有限 Source と一致する
    ものに限る(`ExtractionDoctrine` は `Source` を内部型として持つため、
    共有 Source なしには「同一 Source 上の商」を誘導できない)。doctrine
    `D` が誘導する reading は、抽出集合の一致
    `x ~_D y ⟺ {a | D.extracts x a} = {a | D.extracts y a}` が定める
    Source 上の商とする。representable とは、`q_L` がこの族のある
    reading と kernel 同値であること。
  この設定で次が成り立つ。
  1. **(i) ambient 存在と普遍性**: `q_L` は `L`-adequate であり、最粗で
     ある: 任意の `L`-adequate reading `q` に対し `q_L` は `q` を通して
     factor し、factor する写像は商の同型を除いて一意である。
  2. **(ii) 実効計算**: 有限 regime で `~_L` を計算する実効的構成
     (partition refinement 型でよい)を与え、その出力が (i) の `q_L` と
     kernel 同値であることを theorem として証明する。実効性は claim
     boundary の decidable 入力(有限 index の `L`・`DecidableEq` な
     `Value_l`)の上での computable 構成として主張する。
  3. **(iii) representability 正例**: 宣言された admissible class の中に
     `q_L` と kernel 同値な reading が実在する有限 instance。
  4. **(iv) representability 負例**: admissible class が `L`-adequate な
     reading を少なくとも一つ含む(vacuity 排除)にもかかわらず、class の
     どの reading も `q_L` と kernel 同値でない有限 instance。vacuity
     排除の witness に立てる adequate reading は**非離散**(非自明な
     同一視を少なくとも1組含む)であることを要求する — 恒等 reading は
     任意の `L` に対して常時 adequate であり、それだけでは負例が
     「class に `q_L` を入れなかった」という fiat 選択に退化するからで
     ある。すなわち非離散な adequate readings は在るが最粗のものが
     class 内で表現できない状況の Lean witness。
  5. **(v) 発火 witness**: (iii)(iv) の instance で `L` が非空・非定数、
     `q_L` が恒等でも全潰しでもなく、admissible class が2元以上を持つ
     ことを theorem として確認する。
  (i)(ii) は有限 Source と任意の `L` について証明する。witness((iii)–(v))
  のみ既存 `FiniteModel` の Atom carrier へ具体化する。既存に固定するのは
  Atom carrier のみであり、witness 用の有限 Source と doctrine 族は新設
  してよい(既存 `extractionDoctrine` の 2 元 Source 上では商が恒等か
  全潰しの二択となり (v) が実現不可能なため)。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/CanonicalResolution/` 配下。`Formal/AG` は
  参照のみ。full abstraction の一般理論、無限状態、決定不能性、concept
  lattice、接地 certificate は本 target に現れない。G-103 の完了面は
  (i)–(v) まで。
- `target proof artifacts`: reading / adequacy / 粗さ順序の定義、`~_L` と
  `q_L` の構成、adequacy theorem、普遍性(factorization と一意性)
  theorem、実効的構成とその正当性 theorem、admissible class の定義
  (doctrine 誘導 readings)、representability の定義、正例 witness、
  負例 witness(vacuity 排除条件つき)、発火 witness、
  report `research/reports/G-103-aat-canonical-resolution.md`。
- `target proof strategy`: F0 reading / adequacy / 順序の定義 -> F1 `q_L`
  構成と普遍性 -> F2 実効計算と正当性 -> F3 admissible class 定義と
  正例 -> F4 負例と発火 witness。既存成果の利用 map:
  `Formal/AG/Atom/Axioms.lean` の `ExtractionDoctrine` / `extracts`
  (admissible class の素材)、`Formal/AG/Examples/FiniteModel.lean`
  (witness 素材)。固定 statement と完了条件は本カードのみを正本と
  する。
- `target theorem completion criteria`: 全 artifact が sorry なしで
  `ResearchLean` に受理され、axiom / placeholder audit が clean である
  こと。下記 ledger の `discharge-required` を構成・証明・Lean finite
  witness で放電し、T3 audit で provenance、proof-use、structure-field
  escape、route integrity を監査すること。Lean / report / tracking Issue を
  同期し、final review packet を作り、
  `$math-lean-review research/goals/G-103-aat-canonical-resolution.md G-103-aat-canonical-resolution`
  の4査読がすべて `No major findings` であること。
- `target premise discharge policy`: 入力(有限 Source、law evaluation 族、
  admissible class を定義する doctrine 族)だけを残せる。adequacy、普遍性、
  実効計算の正当性、representability の正負、非退化はすべて completion
  までに生成・証明する。普遍性・representability に相当するデータを
  certificate や structure field で受け取るだけでは放電と数えない。
- `target material premise ledger`:
  - `有限 Source / FiniteModel`: `ambient-boundary`。(i)(ii) は任意の有限
    Source、witness は既存 `FiniteModel` の Atom carrier 上に新設する
    有限 Source / doctrine 族で具体化する(既存に固定するのは Atom
    carrier のみ)。
  - `ExtractionDoctrine と extracts`: `ambient-boundary`。review 済み
    `Formal/AG/Atom/Axioms.lean` の参照のみ。doctrine 誘導 reading の
    定義は新規に research 側へ置く。
  - `reading / adequacy / 粗さ順序`: `discharge-required`。provenance は
    本カードの定義のみ。artifact は定義と基本補題群。
  - `q_L の構成と普遍性`: `discharge-required`。joint kernel から構成し、
    adequacy・factorization・一意性を theorem で証明する。普遍性を
    structure field で受けない。
  - `実効計算の正当性`: `discharge-required`。実効的構成の出力と `q_L` の
    kernel 同値を theorem で証明する。実装のみは放電と数えない。
  - `representability 正例`: `discharge-required`。admissible class 内の
    reading と `q_L` の kernel 同値の Lean witness。
  - `representability 負例`: `discharge-required`。class 内に**非離散な**
    adequate reading が存在することの witness と、全 class 元の非同値の
    証明。恒等 reading の常時 adequacy による vacuity 排除、
    型・濃度不一致だけの構成は放電と数えない。
  - `非退化(発火)witness`: `discharge-required`。`L` 非空・非定数、
    `q_L` 非自明、class 2元以上。route integrity audit で使う。
- `target anti-weakening rule`: 普遍性の全称域(任意の `L`-adequate
  reading)を縮めない。一意性を商の粗視化で自明化しない。adequacy を
  「ある law が factor する」へ弱めない。representability を kernel 同値
  より弱い比較(濃度一致・次元一致)へ置き換えない。負例の vacuity
  排除条件(class 内の非離散 adequate reading の実在)を落とさない・
  恒等 reading で代替しない。実効計算の decidability を `Classical` 選択で
  供給して computable 構成を僭称しない。結論相当
  データ(普遍性・同値・非同値)を theorem argument、typeclass、
  structure field、certificate field、opaque membership へ移さない。
  statement を claim boundary 外(無限化・一般特徴づけ・合流)の主張と
  読み替えない。
- `target route integrity gate`: `q_L`・admissible class・正負 witness の
  provenance を law evaluation 族、doctrine の構成データ、review 済み
  predecessor へ追跡する。定数 law・空 class・退化 Source だけの発火、
  proof 後の GOAL 読み替えを completion に使わない。
- `target failure policy`: (i)(ii) の反例は `target-refuted` とし、reading /
  adequacy / 順序の定義への改訂案を返す。(iv) は負例構成が成功条件で
  あり、逆に「宣言した admissible class では `q_L` が常に representable」
  と証明された場合は class の定義が広すぎる仕様欠陥として GOAL 改訂案を
  返す。同じ blocker が二 cycle 続けば `target-blocked`。claim boundary 外
  の機構が必要と判明した場合は本 GOAL を拡張せず、GOAL 改訂提案として
  返す。
