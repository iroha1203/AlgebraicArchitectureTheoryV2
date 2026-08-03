# G-102-aat-two-phase-obstruction — 二相係数の障害 support 定理

- `id`: `G-102-aat-two-phase-obstruction`
- `status`: `completed`
- `completion result`: `target-theorem-proved`。Two-Phase Obstruction Support
  Theorem の (i)–(v) を全放電し、fixed head での final formal review は全4レーン
  `No major findings`(veto なし)、CI 7件 green。実装 PR は
  [#3895](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/3895)
  でマージ済み。`Formal/AG` への移植は未実施(porting status: `unported`)。
- `completed at`: `2026-08-03 JST`
- `priority`: `high`
- `research mode`: `target-theorem`
- `tracking issue`: [#3892](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/3892) closed as `COMPLETED`.
- `report`: [research/reports/G-102-aat-two-phase-obstruction.md](../reports/G-102-aat-two-phase-obstruction.md)
- `source note`: [docs/note/atom_is_all_you_need_discussion.md](../../docs/note/atom_is_all_you_need_discussion.md)(§2、§8 候補1)
- `research aim`: Atom の構造 / 意味の二相を kind ラベルではなく抽出の依存
  profile(宣言された semantic-reading 変形族に対する `extracts` 真偽の
  不変性)から導出的に定義し、有限被覆の係数複体を二相の短完全列
  `0 -> F_struct -> F_all -> F_sem -> 0` に分解して、
  `H^1(F_struct) = 0` の regime では非零障害類が意味成分で必ず検出される
  (`H^1(F_all) -> H^1(F_sem)` が単射)ことを証明する。同時に、構造係数
  だけでも `H^1` が非零になる有限反例を構成し、無条件版(「非零障害類は
  常に意味 Atom 上に support される」)が偽であることを固定する。
- `core tension`: 二相分解が実質を持つかは二点にかかる。第一に、分解が
  依存 profile から**導出**されること — AtomKind 相当のラベル分割の
  再ラベルなら定理は空洞になる。第二に、短完全列が立つための実質条件
  (係数複体の全写像が構造部分空間を保つこと。以下**条件 E**)の特定 —
  E が常に成立するなら仮定は幻であり、E が滅多に成立しないなら定理は
  使えない。E の成立正例と E が破れる有限反例の稜線、および消滅仮定
  `H^1(F_struct) = 0` の実質性(破れる有限反例)が、この定理の中身である。
- `rival`: 既存の第IV部定理12.4(forest 消滅)と系12.3(定数係数 nerve
  読み)は単相の消滅機構であり、Lean 実装(`Formal/AG/Cohomology/
  CoverNerve.lean` の `localGluingSufficiency` / `forestVanishing`)も
  review 済みである。一般ホモロジー代数の短完全列 -> コホモロジー完全列は
  mathlib 系の標準機構である。本 GOAL の差分は (a) 分解を抽出 doctrine の
  依存 profile から導出する点、(b) 消滅機構と二相分解の**積**として
  support 単射を立てる点、(c) 正則 regime だけでなく構造係数の descent
  失敗反例まで固定する点に置く。標準機構の instantiation で済む部分は
  流用してよいが、既存消滅定理の再証明は成果に数えない。
- `claim boundary`: 固定した一般 carrier `U : AtomCarrier`、
  `ExtractionDoctrine U` とその selected semantic reading を含む宣言された
  非空 semantic-reading 変形族、既存 `CoverNerve` /
  `FiniteNerveCochainComplex` 型の有限被覆複体、体 `k` 係数の abelian
  regime を対象とする。non-abelian torsor / gerbe / stack、無限被覆、
  依存 profile の全次数(深度 filtration・スペクトル系列)、doctrine 間
  comparison(blame 輸送)、L-adequacy / canonical resolution、
  carrier を動かす主張は含めない。
- `capability categories`: two-phase-derivation、exact-sequence、
  obstruction-support、counterexample、corollary-derivation。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に
  置き、固定 statement と completion criteria だけで完了判定する。
- `portfolio constraint`: 証明対象4面(分解の導出・短完全列・support
  単射・反例2種)がすべて Lean artifact で接続されること。正例(単射
  定理)だけ、または反例だけで完了扱いしない。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、反証なら
  `target-refuted`、全完了条件と final review を満たした場合だけ
  `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各 cycle は
  proof obligation delta で評価する。
- `dullness filter`: 次を弾く。変形族が空・単元で全 Atom が自明に構造的に
  なる分解、`F_struct = 0` または `F_sem = 0` の自明分割、依存 profile と
  無関係な fiat 分割(kind ラベルの再ラベル)、既存 forest 消滅定理の
  再証明、`H^1(F_all) = 0` が同時に成立して単射が `0 ↪` で自明化する
  regime だけの witness、係数空間の次元不一致・型不一致だけで成立する
  反例、空 nerve・零係数複体上の vacuity、部分空間が well-defined に
  ならないこと(E 不成立)だけを消滅反例と数える混同。
- `frontier`: 深度 filtration の2段以上への拡張の観察(スペクトル系列の
  本証明は範囲外)、face が loop を埋める regime(系12.3 の face 補正)での
  変種、semi-module 等の係数一般化の観察、E を弱めた block-triangular
  regime の分類。

- `target theorem`: **Two-Phase Obstruction Support Theorem**。
  固定した一般 carrier `U : AtomCarrier` 上で次を構成する。
  - **依存 profile と二相分解**: doctrine `D : ExtractionDoctrine U` と、
    `D` 自身の semantic 成分を含む宣言された非空変形族 `fam`(semantic
    reading の値と semantic 許容述語の**対**の族。`D` の他成分 —
    Source・vocabulary・resolution・normalize・sourceSemantics — は固定)
    に対し、semantic 成分だけを `γ ∈ fam` に取り替えた doctrine 変種
    `D[γ]` を定義する。pair `(s, a)` が **structural**(`fam`-不変)で
    あるとは、すべての `γ ∈ fam` で `D[γ].extracts s a` の真偽が `D` と
    一致すること。**semantic** はその否定(`fam` 内で真偽が動くこと)。
    この分解は宣言された `fam` に相対的であり、絶対分類は主張しない。
  - **二相係数複体**: Atom-indexed basis を持つ有限被覆係数複体
    (chart / edge 成分ごとの有限 Atom 台と、その上の `k` 値関数空間、
    宣言された Atom 対応が誘導する restriction / 差分写像)に対し、
    structural pair が張る部分空間の族を `F_struct` とする。
    **条件 E(構造 support 保存)**: 複体のすべての restriction / 差分
    写像が `F_struct` を保つ。E の下で `F_struct` は部分複体、
    `F_sem` は商複体になる。
  この設定で次が成り立つ。
  1. **(i) 短完全列**: 条件 E の下で、各次数で
     `0 -> F_struct^n -> F_all^n -> F_sem^n -> 0` が exact であり、
     複体の射としても短完全列をなす。
  2. **(ii) support 単射**: (i) から誘導されるコホモロジー比較列は
     `H^1(F_struct) -> H^1(F_all) -> H^1(F_sem)` の中央で exact であり、
     したがって `H^1(F_struct) = 0` ならば標準射
     `H^1(F_all) -> H^1(F_sem)` は単射である。単射は商複体への標準射に
     ついて主張し、任意の単射の存在に弱めない。
  3. **(iii) 非輪状系**: nerve が forest かつ triple overlap face を
     持たず、**`F_struct` 側の** restriction が全射である regime では、
     (ii) と review 済み消滅定理の instantiation(`F_struct` の複体
     data への適用)により「非零障害類は意味成分への像が非零」が系と
     して従う
     (読み: この regime では結合欠陥はすべて意味的に検出される。
     対偶: 構造サイクルは意味成分に映らない結合欠陥の必要条件)。
     消滅部分は既存 theorem の適用であり再証明しない。
  4. **(iv) 反例2種**: (a) **E 破れ**: 宣言された変形族と係数複体で、
     restriction / 差分写像が structural pair の像を semantic 側へ運び、
     E が成立しない有限反例。(b) **構造 descent 失敗**: E は成立するが
     構造側 nerve が 1-サイクルを持ち `H^1(F_struct) ≠ 0` となる有限
     反例。これにより消滅仮定が material であること、および無条件版
     (「非零障害類は常に意味 Atom 上に support される」)が偽である
     ことを固定する。
  5. **(v) 発火 witness**: 両相が非空(structural pair と semantic pair が
     どちらも実在)で、`F_struct` が `0` でも全体でもなく、
     `H^1(F_all) ≠ 0` の類の `H^1(F_sem)` への像が実際に非零になる有限
     witness。`H^1(F_all) = 0` による vacuous 成立を witness に数えない。
  (i)(ii) は `U` 上の全 `D` / `fam` / E を満たす係数複体について証明する。
  witness(反例・発火)のみ `FiniteModel` の carrier へ具体化する。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/TwoPhase/` 配下。`Formal/AG` は参照のみ。
  site / coverage topology の一般論、係数の semi-module 一般化、
  doctrine 間の複体 comparison は本 target に現れない。G-102 の完了面は
  (i)–(v) まで。スペクトル系列・全次数 profile・blame 輸送は主張しない。
- `target proof artifacts`: doctrine 変種 `D[γ]` と依存 profile の定義、
  structural / semantic pair の定義と両相非空 witness、Atom-indexed
  係数複体の定義、条件 E の定義、部分複体 / 商複体構成、各次数
  exactness theorem、コホモロジー比較列の中央 exactness theorem、
  support 単射 theorem、非輪状系 theorem(既存消滅定理の instantiation)、
  E 破れ有限反例、`H^1(F_struct) ≠ 0` 有限反例、発火 witness、
  report `research/reports/G-102-aat-two-phase-obstruction.md`。
- `target proof strategy`: E0 依存 profile と二相分解の定義・両相非空
  witness -> E1 Atom-indexed 係数複体・条件 E・短完全列 -> E2 比較列
  exactness と support 単射 -> E3 非輪状系の instantiation -> E4 反例
  2種と発火 witness。既存成果の利用 map:
  `Formal/AG/Atom/Axioms.lean` の `ExtractionDoctrine` /
  `extracts`(doctrine 変種の素材)、`Formal/AG/Cohomology/CoverNerve.lean`
  の `CoverNerve` / `FiniteNerveCochainComplex` / `forestVanishing` /
  `localGluingSufficiency`(複体型と消滅機構、参照のみ)、
  `Formal/AG/Cohomology/FiniteExamples.lean` と
  `Formal/AG/Examples/FiniteModel.lean`(witness 素材)。固定 statement と
  完了条件は本カードのみを正本とする。
- `target theorem completion criteria`: 全 artifact が sorry なしで
  `ResearchLean` に受理され、axiom / placeholder audit が clean である
  こと。下記 ledger の `discharge-required` を構成・証明・Lean finite
  witness で放電し、T3 audit で provenance、proof-use、structure-field
  escape、route integrity を監査すること。Lean / report / tracking Issue を
  同期し、final review packet を作り、
  `$math-lean-review research/goals/G-102-aat-two-phase-obstruction.md G-102-aat-two-phase-obstruction`
  の4査読がすべて `No major findings` であること。
- `target premise discharge policy`: 入力(doctrine、宣言された変形族、
  Atom-indexed 係数複体の構成データ)だけを残せる。二相分解の導出、
  条件 E の成立(正例側)、短完全列 exactness、比較列 exactness、単射、
  非輪状系、反例2種、発火はすべて completion までに生成・証明する。
  exactness・消滅・単射に相当するデータを certificate や structure field で
  受け取るだけでは放電と数えない。
- `target material premise ledger`:
  - `carrier U / FiniteModel`: `ambient-boundary`。一般構成は任意 `U`、
    反例と発火 witness のみ既存 `FiniteModel` で具体化する。
  - `ExtractionDoctrine と extracts`: `ambient-boundary`。review 済み
    `Formal/AG/Atom/Axioms.lean` の参照のみ。semantic reading 成分の
    取り替えは新規定義として research 側に置く。
  - `CoverNerve / FiniteNerveCochainComplex / forest 消滅`:
    `ambient-boundary`。review 済み `Formal/AG/Cohomology` の参照のみ。
    消滅は (iii) で instantiation として使い、再証明しない。消滅結論を
    構成の field に入れない。
  - `依存 profile と二相分解`: `discharge-required`。provenance は
    doctrine と宣言された変形族のみ。artifact は structural / semantic の
    定義 theorem 群と両相非空 witness。ラベル分割での代替は放電と
    数えない。
  - `条件 E`: `discharge-required`。provenance は係数複体の構成データと
    二相分解。artifact は E の定義、E 成立の正例(一般仮定としての使用)、
    E が破れる有限反例。E に exactness・消滅・単射相当の条項を含めない。
  - `短完全列 exactness`: `discharge-required`。E から各次数 exactness を
    証明する。exactness を構成の field で受けない。
  - `比較列 exactness と support 単射`: `discharge-required`。短完全列
    から中央 exactness を証明し、消滅仮定下の単射を導出する。
  - `非輪状系`: `discharge-required`。(ii) と既存消滅定理の instantiation
    から導出する。既存定理の再証明を成果に数えない。
  - `構造 descent 失敗反例`: `discharge-required`。E 成立下で
    `H^1(F_struct) ≠ 0` となる有限 witness。次元・型の不一致だけの
    構成は放電と数えない。
  - `発火 witness`: `discharge-required`。`H^1(F_all) ≠ 0` の類の像が
    非零になる有限例。route integrity audit で使う。
- `target anti-weakening rule`: 単射を「単射な線形写像が存在する」へ
  弱めない(商への標準射について主張する)。中央 exactness の全称域
  (任意の類)を縮めない。E に消滅・exactness・単射と同値または片方向に
  近い条項を移さない。二相分解を依存 profile から切り離した宣言的
  ラベルへ置き換えない。(iii) を `H^1(F_all) = 0` が同時に従う regime へ
  退避して vacuous に満たさない。反例を空複体・零係数・型不一致で
  満たさない。結論相当データ(exactness・消滅・単射・比較列)を theorem
  argument、typeclass、structure field、certificate field、opaque
  membership へ移さない。statement を claim boundary 外(スペクトル
  系列・doctrine 間比較等)の主張と読み替えない。
- `target route integrity gate`: 二相分解・条件 E・反例・発火 witness の
  provenance を doctrine の構成データ、宣言された変形族、係数複体の
  構成データ、review 済み predecessor へ追跡する。変形族の退化
  (空・単元)だけの発火、vacuous regime(`H^1(F_all) = 0`)の witness、
  proof 後の GOAL 読み替えを completion に使わない。
- `target failure policy`: (i)(ii) の反例(E と消滅の下で単射が破れる等)は
  `target-refuted` とし、二相分解・条件 E・複体構成の定義への改訂案を
  返す。(iv) は反例構成が成功条件であり、逆に「E は常に成立する」
  「`H^1(F_struct) ≠ 0` は構成不可能」のいずれかが証明された場合は本カード
  の仕様欠陥として GOAL 改訂案を返す。同じ blocker が二 cycle 続けば
  `target-blocked`。claim boundary 外の機構が必要と判明した場合は本 GOAL を
  拡張せず、GOAL 改訂提案として返す。
