# G-104-aat-resolution-invariance — 診断の解像度不変性

- `id`: `G-104-aat-resolution-invariance`
- `status`: `draft`
- `priority`: `high`
- `research mode`: `target-theorem`
- `predecessor`: G-103(canonical resolution)の reading / adequacy / 粗さ
  順序の定義を正本として参照する。G-103 の完了後に本カードの語彙を
  その確定定義へ同期してから active へ昇格する。
- `tracking issue`: 未起票(active 昇格時に起票する)
- `source note`: [docs/note/atom_is_all_you_need_discussion.md](../../docs/note/atom_is_all_you_need_discussion.md)(§5、§8 候補4)
- `昇格前確定事項(スケルトン注記)`: 本カードは骨格 draft である。
  次の3点は G-103 の確定定義と G-102 の係数複体設計を見て昇格前に固定
  する。(1) 「law 由来係数」の型 — law evaluation から係数空間を生成する
  構成の正確な形。(2) 条件 C(被覆の像の振る舞い)の候補式。
  (3) 反例側(偽の類の発生・真の類の隠蔽)を存在 witness に留めるか
  定量化まで含めるか。
- `research aim`: 二つの `L`-adequate な読み `q ≤ q'`(粗さ順序)に対し、
  law 由来の係数で計算した障害類が、読みの比較射が誘導する comparison
  map の下で canonical に同型になる条件を特定し、「adequate な範囲内では
  解像度の選択は診断を変えない」を theorem にする。系として過剰解像度の
  無益性(必要以上に細かく測っても診断は増えない)を導き、対として
  adequate でない粗化では偽の類の発生または真の類の隠蔽が実際に起きる
  有限反例を固定する。ArchSig の粒度選択が暗黙に依存している事実の
  定理化である。
- `core tension`: 直観的根拠は「係数は law が生成し、law は潰された区別を
  見ない」だが、被覆の像の振る舞い(粗化で chart / overlap がどう写るか)
  に条件が要り、その条件 C の正体こそが定理の中身である。C が自明に常時
  成立するなら定理は定義の言い換えであり、C が強すぎて実例が持てないなら
  定理は空である。C の成立正例と、C なしで同型が破れる反例の稜線が核心。
- `rival`: 抽象解釈の粒度選択(Galois 接続の合成で精度が単調に変わる
  一般論)、モデル検査の抽象化精細化(CEGAR)、既存の第VIII部測定理論。
  差は「adequacy を law family 相対で固定し、障害類の canonical 同型と
  その破れを同一有限モデル上の Lean witness で固定する」点に置く。
- `claim boundary`: 有限 Source、law evaluation 族、G-103 の意味での
  reading / adequacy / 粗さ順序、law 由来係数の有限被覆複体を対象と
  する。無限 regime、係数の一般論(semi-module 化)、doctrine 間
  comparison(blame 輸送)、接地 certificate、q_L の representability は
  含めない。
- `capability categories`: comparison-map、invariance、
  coefficient-generation、counterexample、corollary-derivation。
- `threshold policy`: SCORE は使わない。runtime state は tracking Issue に
  置き、固定 statement と completion criteria だけで完了判定する。
- `portfolio constraint`: 正例(不変性 theorem)だけ、または反例
  (inadequate 粗化の病理)だけで完了扱いしない。両面の Lean artifact
  接続を要求する。
- `phase boundary criteria`: 未証明なら `target-proof-checkpoint`、反証なら
  `target-refuted`、全完了条件と final review を満たした場合だけ
  `target-theorem-proved` とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。各 cycle は
  proof obligation delta で評価する。
- `dullness filter`: 次を弾く。`q = q'`(恒等比較)だけの発火、両側の
  `H^1` が零で同型が vacuous に成立する witness、law が定数で係数が
  退化する例、粗さ順序が自明(単元 Source)な例、comparison map を
  同型と仮定して不変性を導く循環、反例が型不一致だけで成立する構成。
- `frontier`: 定量化(inadequate 粗化で失われる類の個数・次元の下界)、
  接地条件との交差(接地可能な解像度だけに制限した不変性)、
  資源制約下の最適解像度選択の観察。

- `target theorem`: **Diagnostic Resolution Invariance Theorem**(骨格)。
  有限 Source・law family `L`・law 由来係数の有限被覆複体の上で:
  1. **(i) comparison map**: `L`-adequate な読み `q ≤ q'` の比較射から、
     被覆・複体・障害類の comparison map を構成する。
  2. **(ii) 不変性**: 条件 C(被覆の像の振る舞いに関する明示仮定。
     昇格前に固定)の下で、comparison map は `H^1` 障害類の canonical
     同型を誘導する。
  3. **(iii) 系(過剰解像度の無益性)**: adequate な範囲内の精細化は
     診断(障害類の集合)を増やさない。
  4. **(iv) 反例対**: adequate でない粗化で (a) 偽の類が発生する、
     または (b) 真の類が隠蔽される有限反例。および条件 C なしで (ii) の
     同型が破れる有限反例。
  5. **(v) 発火 witness**: 非恒等な `q < q'`、非零 `H^1`、係数が実際に
     law から生成される有限 witness。
  (i)(ii) は一般の有限 Source / `L` / adequate pair について証明する。
  witness は既存 `FiniteModel` の carrier へ具体化する。
- `target theorem boundary`: Lean 置き場所は
  `research/lean/ResearchLean/AG/ResolutionInvariance/` 配下。`Formal/AG` は
  参照のみ。G-104 の完了面は (i)–(v) まで。
- `target proof artifacts`: comparison map の構成 def、条件 C の定義、
  不変性 theorem、系 theorem、反例対 witness、C 破れ反例、発火 witness、
  report `research/reports/G-104-aat-resolution-invariance.md`。
  (詳細分割は昇格時に確定する。)
- `target proof strategy`(骨格): H0 comparison map の構成 -> H1 条件 C の
  抽出と不変性 -> H2 系の導出 -> H3 反例対 -> H4 発火 witness。既存成果の
  利用 map: G-103 の reading / adequacy / `q_L`(確定後に参照)、G-102 の
  係数複体設計(Atom-indexed basis)、`Formal/AG/Examples/FiniteModel.lean`
  (witness 素材)。
- `target theorem completion criteria`: 全 artifact が sorry なしで
  `ResearchLean` に受理され、axiom / placeholder audit が clean である
  こと。ledger の `discharge-required` を放電し、T3 audit を通し、
  Lean / report / tracking Issue を同期し、
  `$math-lean-review research/goals/G-104-aat-resolution-invariance.md G-104-aat-resolution-invariance`
  の4査読がすべて `No major findings` であること。
- `target premise discharge policy`: 入力(有限 Source、law evaluation 族、
  adequate pair の構成データ)だけを残せる。comparison map の
  well-definedness、条件 C の成立正例、不変性、反例はすべて completion
  までに生成・証明する。同型相当のデータを certificate や structure
  field で受け取るだけでは放電と数えない。
- `target material premise ledger`(骨格。昇格時に精密化する):
  - `有限 Source / FiniteModel`: `ambient-boundary`。
  - `reading / adequacy / 粗さ順序`: `ambient-boundary`(G-103 の確定
    artifact を参照する。未完了のうちは本カードを active にしない)。
  - `law 由来係数の生成`: `discharge-required`。昇格前確定事項 (1)。
  - `comparison map`: `discharge-required`。比較射から構成し、同型性を
    field に入れない。
  - `条件 C と不変性`: `discharge-required`。C に同型相当の条項を
    含めない。C の成立正例と破れ反例をセットで要求する。
  - `反例対`: `discharge-required`。型不一致 vacuity は不可。
  - `発火 witness`: `discharge-required`。
- `target anti-weakening rule`: 不変性を「ある同型が存在する」へ弱めない
  (comparison map が誘導する canonical 射について主張する)。条件 C に
  同型・消滅と同値または片方向に近い条項を移さない。adequate の定義を
  反例が立つように事後調整しない。結論相当データを theorem argument、
  typeclass、structure field、certificate field へ移さない。
- `target route integrity gate`: comparison map・条件 C・反例の provenance
  を law evaluation 族、読みの比較射、review 済み predecessor へ追跡
  する。恒等比較・零 `H^1`・定数 law だけの発火を completion に使わない。
- `target failure policy`: (ii) の反例(C の下で同型が破れる)は
  `target-refuted` とし、C または comparison map 構成の改訂案を返す。
  (iv) は反例構成が成功条件であり、「adequate でない粗化でも診断が常に
  保たれる」と証明された場合は adequacy 定義の仕様欠陥として GOAL
  改訂案を返す。同じ blocker が二 cycle 続けば `target-blocked`。
