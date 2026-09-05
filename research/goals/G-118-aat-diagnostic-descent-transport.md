# G-118-aat-diagnostic-descent-transport — 比較を保つ変更の分類と移送

- `id`: `G-118-aat-diagnostic-descent-transport`
- `status`: `active`
- `priority`: `high`
- `research mode`: `target-theorem`
- `tracking issue`: #4367
- `source note`: [n1008 §4.2・§6.4](../../docs/note/n1008_aat_idempotent_exchange_structure_program.md)。
- `program context`: [研究の全体目標](../../docs/research_goal.md)の reading 間の輸送と
  変形に対し、意味構造の比較を変更後にも使う条件を与える。比較射に沿って運べる
  端点変更、その選択の自由度、別の表示への移送を一つの theorem package にする。
  観測で失われる比較情報は、この分類から導く。意味のモジュライの同一視、実現関手が
  保持すべき比較データ、輸送理論の論文の構成に数学的な入力を与える。
- `predecessor`: G-115 の上段比較・生成された route transport・comparator descent の
  正負例、G-116 の冪等正規化と transport identity-reflection classification は研究上の参照。
  本カードの直接の proof dependency は下記 source map の G-115 geometry 宣言とする。
  G-117 の反証記録は、対象の admissibility から全射との両立を推論できないことの
  参照にする。G-117 は
  [最終記録](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4359#issuecomment-5545065231)
  と PR #4365 の merge `9edc30aae6cd7a6345300874fa810d8c8fa3bbf8` を参照する。
  `no_taggedAdmissibleCanonicalNormalizationNatTrans` により (c) が `target-refuted`。
  (a)(b)、pointwise 冪等性、operation-coherence iff、h2 の既証明部分は参照成果、
  (d)–(i) の未完了部分は未証明として扱う。G-115 (i2) は B2 で引き受け、
  G-114 mate の同型判定・selector・cancellation は本カードの引受け対象にしない。
- `research aim`: AAT が生成する比較射について、資格を満たす可逆な端点変更の
  移送可能性と選択の自由度を特徴づけ、その分類が指定した表示変更・移送の下で
  どう保たれるかを確定する。さらに、係数の観測がこの分類のどの情報を失うかを示す。
- `core tension`: 各端点で許される変更が、比較射を越えても許される変更になるとは
  限らない。存在、一意性、自由度を生成データから導き、その答えを別表示へ運べるか。
  可換式を移送先へ送る保存と、移送先から元の成立を取り戻す反映を区別する。
- `rival`: arrow category の自己同型群、群準同型の像・核・fiber、共役による
  stabilizer の移送。差分は、AAT の Support / Axis / Observable と資格条件を含む
  実比較から分類を導くこと、必要な移送を既存の生成経路から構成すること、係数で
  不可視な正負の分離を移送後まで追跡することに置く。
- `claim boundary`: 以下の量化域を固定する。`u,v` は任意の universe。
  - 一般構造 A: `U : AtomCarrier.{u}`、`G H : GeometryPackage.{u,v} U` と
    `c : GeometryTotalHom G H` は任意。資格は既存の `CompositeFiberAut`、すなわち
    `hom.base.base = 𝟙 (packagePoint G.core)`。係数恒等はこの資格に含めず D で別に取る。
  - 実比較 B/C: 任意の `ctx : ActiveRefinementBCContext U`、
    `P : FiniteTransportPresentation.{u}`、`k : CommRingCat.{v}`、
    `I : UpperGeometryCompatibleProblemInputData ctx P k`、`i : P.Vertex`。
    `S_i := (I.sourceGeometry i).package`、`B_i := I.generatedBaseRouteGeometryAt i`、
    `P_i := I.generatedPulledRouteGeometryAt i`、
    `c_i := I.generatedCompatibleUpperGeometryMateAt i` とする。
    source-only input の root / rootPath / source diagram / sourceGeometry /
    sourceTransport を入力とし、solution や intertwining certificate を入力に追加しない。
  - Atom、Law、coverage、raw system、reading はこの入力が指定するもの。有限なのは
    presentation の cell family であり、package の全 carrier や全自己同型群を有限としない。
    C の経路内では同じ係数 `k` を保持する。
  - 固定 decision datum は `UpperDecisionWitness.problem.data`、頂点 `PUnit.unit`、
    edge `UpperDecisionWitness.DecisionEdge.twist`、cell
    `UpperDecisionWitness.DecisionCell.comparison`、係数 `Int`。
    `c_* := UpperDecisionWitness.solution.component PUnit.unit` は
    `upperDecisionSolution.component PUnit.unit` と同じ生成物である。
- `capability categories`: classification、transport、obstruction、interpretation。
- `threshold policy`: SCORE は使わない。実行状態は tracking Issue に置く。
- `portfolio constraint`: 一般群論の packaging、正負例の再登録、抽象的な可換正方形の
  保存だけでは完了としない。実比較の分類、生成された移送との接続、観測の分離を要求する。
- `phase boundary criteria`: 人間による active 化後に固定した statement を実行する。
  全 completion criteria が満たされるまでは checkpoint とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。
- `dullness filter`: 両立条件を新しい predicate に移すだけの iff、結論を field に持つ
  certificate、恒等移送だけの検証、既存正負例の引用だけの非因子化、抽象群論だけの
  分類を弾く。非自明な自由度が存在するという結論も先取りしない。
- `frontier`: 観測に追加すべき情報の十分性、variable-comparator の圏、regular comparison、
  restriction category、coherence height、SHIGURE の実現関手と表現可能性。
  これらの構成は本カードの完了条件とは別に設定する。

- `target theorem`: **Qualified Comparison Transport and Diagnostic Information Loss
  Theorem**。次の A–D を、上記の量化域で一つの構成と分類として接続する。
  分類枝を許すのは B2 と C3 の明記した決定だけである。

  - **(A) 比較を保つ変更とその自由度**

  `c : X ⟶ Y`、`A_X := CompositeFiberAut X`、`A_Y := CompositeFiberAut Y` とする。
  以下は通常の関数合成順 `∘` を用いる。`c ∘ b = p ∘ c` は Lean では
  `(CompositeFiberAut.hom b).comp c = c.comp (CompositeFiberAut.hom p)`。
  群の積は既存の `Aut` instance に従い、式中の合成順から勝手に推定しない。

  ```text
  Γ_c    := { (b,p) ∈ A_X × A_Y | c ∘ b = p ∘ c }
  L_c(b) := { p ∈ A_Y | c ∘ b = p ∘ c }
  K_Y(c) := { k ∈ A_Y | k ∘ c = c }
  K_X(c) := { h ∈ A_X | c ∘ h = c }
  ```

  `Γ_c` の群構造と両射影を構成する。射影の像を移送可能な変更、核を比較を通すと
  消える変更として同定する。`L_c(b)` が非空のとき、`K_Y(c)` の左作用
  `(k,p) ↦ k ∘ p` が自由かつ推移的であることを証明する。非空性から一点を選んだ
  座標表示と、選択に依存しない作用の statement を区別する。反対側も対称に扱う。

  `c` が同型なら、既存の `CompositeFiberAut.conjugationMulEquiv` により
  `c A_X c⁻¹ = A_Y` が得られる。この資格群に対する対応は既証明の一般補題であり、
  再証明を新しい義務にしない。これを使って `Γ_c` を共役のグラフと同定し、
  両射影を両端の資格群全体との同型として構成する。

  - **(B) AAT の実比較での分類**

    **B1: 生成された変更の完全な所属条件**。全 `I,i` について、既存の準同型
    `H_B := I.generatedBaseCompositeFiberAutHomAt i`、
    `H_P := I.generatedPulledCompositeFiberAutHomAt i` を使う。
    `A_S := CompositeFiberAut S_i` とし、任意の `a,d : A_S` に対して
    `R_i(a,d) :↔ (H_B(a),H_P(d)) ∈ Γ_(c_i)` と置く。
    source の任意の自己同型 `a` について `R_i(a,a)` を生成された route leg と mate
    triangle から証明する。既存 theorem の authored comparator 一個への specialization
    から、任意の `a` へ量化を広げる部分は新しい義務である。

    `J_i := H_P⁻¹(K_(P_i)(c_i))` を部分群として構成し、
    `R_i(a,d) ↔ H_P(d) ∘ H_P(a)⁻¹ ∈ K_(P_i)(c_i)` を証明する。
    既存 `Aut` の積は `hom(a*b) = hom(a) ∘ hom(b)` なので、
    `R_i(a,d) ↔ d*a⁻¹ ∈ J_i ↔ ∃ j : J_i, d = j*a` を要求する。
    これで全解を右剰余類 `J_i*a` として固定する。`J_i` の正規性や商群は仮定しない。

    `J_i` は membership の言い換えだけで済ませず、生成 route の入力写像から得る
    次のデータ条件として特徴づける: core の pointed 部分、`atomEquiv`、`objectMap`、
    `equationTransport` の計算データ(`contextEquivalence` / `equationEquiv` /
    `observableEquiv`)、`operationMap` / `invariantMap` / `axisMap` / `coordinateEquiv`
    の等式、係数写像の等式、および各 context 上の
    supportComp / axisComp / observableComp の像での固定条件。
    `SignedExactCoreReadingHom.ext` が要求する `objectMap` の等式と
    `equationTransport` の `HEq` を含む全条件を放電し、core 射の一致を確定する。
    その後、同じ core 射上で overlap の同一視を thin context の一意性により放電し、
    `GeomReadHom.ext` と `GeometryTotalHom.ext` へ接続して条件の必要十分性を示す。
    この特徴づけと下記の実 decision を同じ proof chain にする。
    生成像 `H_B,H_P` の分類と、A の全端点群の分類の範囲を区別する。

    **B2: 固定比較の決定**。`c_*`、その両端の全 `CompositeFiberAut` を固定し、
    `IsIso c_*`、`K_X(c_*) = {1}`、`K_Y(c_*) = {1}`、および両射影
    `π_X : Γ_(c_*) → A_X`、`π_Y : Γ_(c_*) → A_Y` の全射性をそれぞれ決定する。
    正枝は実 inverse / preimage の構成または核の全称的な自明性の証明、負枝は
    非同型 theorem、非恒等な核の元、または相手が存在しない名前付き端点変更を要求する。
    `IsIso c_*` の正枝では既存の共役同値を A のグラフ同定へ接続する。
    既存の injectivity theorem だけから全 geometry の同型性を推論しない。

    必須評価対は `b_* := I.generatedBaseRouteComparator cell` と
    `p_* := I.generatedPulledRouteComparator cell`(上記固定 datum で評価)。
    `(b_*,p_*) ∈ Γ_(c_*)`、`(b_*,1) ∉ Γ_(c_*)` を A/B の API へ接続する。
    後者だけでは `b_*` に相手が存在しないとは言えず、射影非全射の証拠にしない。
    核の決定から、この非空 fiber が一意か複数かを導く。

  - **(C) 分類の移送**

    **C1: complete geometry の表示変更**。全 `I,i` に対し、
    `u_i := I.canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt i`、
    `v_i := I.canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt i` を使う。
    domain は canonical-authored route、codomain は generated route。
    source 比較は `I.canonicalCompanionUpperRefinementBCSolution.component i`、
    target 比較は `c_i`。`canonicalSolutionForwardAt_exact_normalization` と
    `generatedSolutionBackwardAt_exact_normalization`、companion の forward 等式から
    `c_i = v_i ∘ c_can ∘ u_i⁻¹` を示す。
    `CompositeFiberAut.conjugationMulEquiv` の準同型・逆写像・資格保存を使い、
    `Γ_(c_can) ≅ Γ_(c_i)`、両射影、核、非空 fiber の作用の対応を構成する。
    係数写像は両方向で恒等であることを既存 exact-iso theorem から使う。

    このカードの presentation replacement はこの二つの complete upper presentation
    の変更と逆変更に固定する。`BCPresentationReplacement.lean` の「同一 decoded
    BC input を持つ任意の有限表示」は別の型の一般化であり、C1 の量化域に混ぜない。

    **C2: 実 edge reselection**。全 `I` と任意の
    `r_B : GeneratedBaseCoefficientTrivialUpperEdgeReselection I`、
    `r_P : GeneratedPulledCoefficientTrivialUpperEdgeReselection I` に対し、
    各 edge の終点 `j` で `(r_B(edge),r_P(edge)) ∈ Γ_(c_j)` を判定する。
    その全 edge にわたる積が既存の
    `CoefficientTrivialUpperReselectionEndpointIntertwining` と同値であることを示す。
    r_B を固定したときの非空な相手 r_P の族には、各 edge の `K_(P_j)(c_j) ∩ ker κ_(P_j)` の積が自由かつ
    推移的に作用することを構成する。係数恒等という reselection の条件を落とさない。

    B1 の source coefficient-trivial edge family を `H_B,H_P` で送る生成経路について、
    qualification と所属を theorem で供給し、既存の reselected edge / path /
    authored-comparator pasting / raw-cochain API へ接続する。
    arbitrary paired input の保存補題と、source から paired input を作る存在 theorem を
    分ける。移送する predicate は `Γ_(c_j)` の所属であり、独立に再選択した raw defect
    値の不変性を要求するものではない。

    必須非恒等 witness は固定 datum の
    `generatedBaseComparatorCoefficientTrivialUpperReselection` と
    `generatedPulledComparatorCoefficientTrivialUpperReselection` の対、および pulled
    を identity にした負対。`DecisionEdge.twist` 上で評価し、C1 の逆表示変更後にも
    正負と非恒等性を追跡する。

    **C3: 基底の生成移送での保存と反映**。全 `I,i` の対写像
    `T_i : A_S × A_S → A_(B_i) × A_(P_i)`、`(a,d) ↦ (H_B(a),H_P(d))` に固定する。
    source predicate は `Γ_(𝟙 S_i)`、すなわち `a=d`、target predicate は `Γ_(c_i)`。
    B1 から保存を証明し、反映の正確な条件
    `(∀ a d, R_i(a,d) → a=d) ↔ J_i={1}` を証明する。
    `J_i` の入力写像による特徴づけと接続し、固定 datum の `J_*={1}` を決定する。
    正枝は全称的な反映 theorem、負枝は実 `a≠d` と `R_*(a,d)` の反例 theorem。
    faithfulness や `J_i={1}` を入力 certificate として受けて実 decision を済ませない。

    閉包は C1 の恒等・逆・型の合う有限合成、C2 の pointwise 積と有限 path の連結、
    C3 に C1 の表示変更を前後合成したもの。source の対角関係に型が一致する
    C1 だけを C3 の前に合成する。任意の別 context の C3 同士の合成は量化しない。
    各閉包で移送写像の恒等・合成則、Γ の保存、反映条件、係数観測との両立を証明する。
    C1 は全射・全単射、C3 は生成像への写像として記録する。

  - **(D) 係数で不可視な比較情報**

    全 `G : GeometryPackage U` に対し
    `κ_G : CompositeFiberAut G →* Aut (CommRingCat.of G.Coefficient)` を構成する。
    forward map は `(CompositeFiberAut.hom a).geometry.coefficientHom`、inverse map
    は `(CompositeFiberAut.inv a).geometry.coefficientHom`。係数 projection の
    恒等・合成則から inverse law と準同型則を証明し、値域の積の向きを `Aut` と揃える。
    `ker κ_G` と A の比較の射影核を別に構成する。

    B2 の固定 datum で `Q_* := A_X × A_Y`、
    `O_*(b,p) := (κ_X(b),κ_Y(p))`、`D_*(b,p) :↔ (b,p)∈Γ_(c_*)` と置く。
    既存の正負対から
    `O_*(b_*,p_*)=O_*(b_*,1)` と `D_*(b_*,p_*)` と `¬D_*(b_*,1)` を示し、
    `¬∃ d, ∀ q : Q_*, D_*(q) ↔ d(O_*(q))` を証明する。
    正側の coefficient identity は `generatedPulledRouteTransport.comparator_coefficient_id`、
    負側は `generatedPulledIdentityComparator_coefficient_id` から供給する。
    Int の環自己同型が自明でも、whole geometry の対の差はそのまま判定対象に残る。

    C1 の全 finite chain に沿い `Q_*` の対を共役し、観測の可換性・Γ の iff・
    正負分離・上記非因子化を一つの theorem に接続する。C2 の固定 edge 対でも同じ
    評価を行う。C3 に対しては B1 の全 `a,d` の係数観測の保存を証明し、
    正負分離の反映は C3 の `J` 条件に従う。C3 後に任意の負対が負のままと仮定しない。

- `target theorem boundary`: 上記の G-115 geometry 段を対象とする。Lean は
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下の新 module に置く。
  先行 reviewed module は参照し、既存定理の再証明を独立成果として数えない。
- `target proof artifacts`: A の群・作用・像核の theorem、B の実写像による分類と B2 / J_* の正負決定、
  C の移送構成・保存反映・合成整合、D の観測写像と移送された分離対。
  report は `research/reports/G-118-aat-diagnostic-descent-transport.md` に作成し、
  declaration-level evidence map、決定枝、入力の provenance と proof-use を記録する。
- `target proof strategy`: F0 typing(固定された宣言の universe と cast の照合のみ) → A の基礎 API →
  B の具体的分類 → C の生成移送と合成 → D の分離の移送 → completion audit。
  B/C に失敗があれば、先に固定した分類枝に従って記録する。
- `target theorem completion criteria`: 固定した A–D の全義務を sorry なしの Lean theorem または
  あらかじめ許容した具体的反証枝の sorry なしの Lean theorem で確定する。focused check の静的チェック通過と、
  statement 一致、axiom / placeholder audit、material premise discharge、provenance、
  proof-use、structure-field escape、route integrity、非空虚性の監査を分けて記録する。
  各実装 PR の fixed-head `$review-pr`、report / tracking Issue 同期、final_review_packet、
  別工程の `$math-lean-review` 4 独立査読の全 `No major findings` を要求する。
  詳細は [target-goal-contract](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md)。
- `target premise discharge policy`: 入力幾何と先行 theorem を参照として残す。
  移送可能性、資格の保存、共役対応、反映、観測の可換性は導出対象。
  一般補題の方向仮定と、名前付き対象でその仮定を証明する義務を区別する。

- `target material premise ledger`:
  各 discharge artifact は入力構成または先行 theorem から proof term を生成し、その宣言が
  最終定理に使われることを evidence map に記録する。

  | premise | role | 支える結論・artifact・結論相当でない理由 |
  | --- | --- | --- |
  | G-115 の入力幾何と reviewed theorem | ambient-boundary | route / component と既存正負対。新しい分類・移送 theorem は含まれず、宣言単位で参照する |
  | G-115 の exact endpoint iso / conjugationMulEquiv | ambient-boundary | 全資格群の同値は既証明。Γ・核・fiber・観測を含む C1 の統合は新しい theorem とし、既存宣言を proof-use する |
  | `L_c(b)` の非空性、`c` の同型性 | direction-hypothesis | A の条件付き群論。B の名前付き対象では存在・同型性を独立に決定する |
  | 像・核・fiber の実写像による特徴づけ | discharge-required | B の分類 theorem。membership を受け取るだけの field は証拠にならない |
  | 端点同型による Γ・核・fiber の対応 | discharge-required | C1 の統合。既存 exact iso と資格群の共役から導き、比較の actual equality を proof-use する |
  | 両立性の反映・移送の合成整合 | discharge-required | C の固定枝と coherence。faithfulness や可換式を caller から供給しない |
  | 係数観測の carrier・準同型則・移送との可換性 | discharge-required | D の核と移送後の分離。実 coefficient map から構成する |
  | 固定正負対の移送後の所属・非所属 | discharge-required | D の非因子化。先行 witness と C の theorem の両方を proof-use する |

- `target route integrity gate`: `upperDecisionSolution`、
  `upperDecisionSolution_comparatorDescentAt`、
  `generatedBaseIdentityPair_not_comparatorDescentAt`、
  `generatedPulledIdentityComparator_coefficient_id` を必須の接続点とする。
  関連 module は `UpperGeometryCompatibleDecisionFixtures.lean`、
  `UpperGeometryCompatibleComparatorIncoherence.lean`、
  `UpperGeometryPairedCoefficientTrivialReselection.lean`、
  `UpperGeometryFullPairedReselection.lean`。宣言 map は下記の fixed source map に固定する。
  結論に合わせた fixture 差し替え、移送族の後追い選択、paired 条件を受けるだけの
  構成を存在分類と数えること、一般群論による A だけの完了を禁止する。
- `target anti-weakening rule`: A–D の結論を仮定、typeclass、certificate、opaque
  membership に移さない。非空性と非自明性、保存と反映、有限の決定と一般の分類を
  区別する。同型の共役補題で一般移送を代替しない。
- `target failure policy`: active 化後の固定構成義務に具体的反例が立てば
  `target-refuted`。事前固定した分類枝の具体的決定は当該義務の成果とする。
  型不能・指示対象欠落は `goal-defect`、未証明は `target-proof-checkpoint`、
  同一 blocker が二 cycle 続けば `target-blocked`。対象・仮定・結論の改訂は人間の判断による。
  B2 / C3 の枝選択を `Classical.em`、`not_forall`、choice のみで済ませず、
  指定したデータ上の構成または計算と実写像の証明を要求する。

- `fixed source map`: 以下は `research/lean/ResearchLean/AG/` に相対的な module 名。
  source snapshot は `9edc30aae6cd7a6345300874fa810d8c8fa3bbf8`。
  F0 はこれらの宣言の対象を差し替える工程ではなく、固定 statement を型付けする工程。

  | 義務 | module / 既存宣言 | 新しく証明する接続 |
  | --- | --- | --- |
  | A / D | `CrossStageCoherence/ObstructionGroups` / `CompositeFiberAut`、`GeometryTransport/Categories` / `GeometryTotalHom`、`GeomReadHom` | Γ の群・作用、coefficient Aut 準同型 |
  | B1 / C3 | `DoctrineFiberProduct/UpperGeometryCompatibleComparatorMapLaws` / `generatedBaseCompositeFiberAutHomAt`、`generatedPulledCompositeFiberAutHomAt` | 任意 source 自己同型での mate 両立、J の特徴づけと反映 |
  | B1 | `DoctrineFiberProduct/UpperGeometryCompatibleComparatorGeometry` / `generatedBaseCompositeFiberAutAt_fac`、`generatedPulledCompositeFiberAutAt_fac` | source の任意 a,d と実 carrier 条件の接続 |
  | B2 / C3 | `DoctrineFiberProduct/UpperGeometryCompatibleDecisionFixtures` / `UpperDecisionWitness.problem`、`solution`、`upperDecisionSolution` | c_* の同型・両核・両射影全射・J_* の決定 |
  | C1 | `DoctrineFiberProduct/UpperGeometryCompatibleEndpointExactIsos` / `canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt`、`canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt` と `_coefficient_id` 群 | 全資格群・Γ・核・fiber の共役対応 |
  | A / C1 | `DoctrineFiberProduct/UpperGeometryCanonicalAuthoredTransportLaws` / `conjugationMulEquiv`、`canonicalSolutionForwardAt_exact_normalization`、`generatedSolutionBackwardAt_exact_normalization` | 既存共役・exact等式を Γ の移送へ接続 |
  | C1 | `DoctrineFiberProduct/UpperGeometryCompatibleSolutionEquivalence` / `canonicalGeneratedUpperRefinementBCSolutionEquiv`、`canonicalCompanionUpperRefinementBCSolution` | c_can と c_i の exact total equality |
  | C2 | `DoctrineFiberProduct/UpperGeometryPairedCoefficientTrivialReselection` / `generatedComparatorUpperReselections_endpointIntertwining_fires`、`generatedBaseComparatorPulledIdentity_not_endpointIntertwining` | edgewise Γ と係数核の作用、非恒等な移送対 |
  | D | `DoctrineFiberProduct/UpperGeometryCompatibleComparatorIncoherence` / `upperDecisionSolution_comparatorDescentAt`、`generatedBaseIdentityPair_not_comparatorDescentAt` | C1 を経た非因子化 |
