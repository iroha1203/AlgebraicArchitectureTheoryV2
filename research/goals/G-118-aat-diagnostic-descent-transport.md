# G-118-aat-diagnostic-descent-transport — 入力表示変更に自然な比較分類と診断情報損失

- `id`: `G-118-aat-diagnostic-descent-transport`
- `status`: `active`
- `priority`: `high`
- `research mode`: `target-theorem`
- `tracking issue`: #4367
- `revision`: 2。2026-09-05、人間の指示により、移送元の完全幾何の表示変更と
  生成移送の自然性を固定 target に追加した。改訂前の C1-before-C3 の型欠落と
  PR #4382 の `goal-defect` 判定は tracking Issue の履歴として保持する。
- `revision review`: accepted。PR #4383 の固定 head に対する独立数学/Lean査読を通過し、
  merge `7d4080a28fbb7d0e20189709c2fbcc59f74809c3` で確定した。
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
  移送可能性と選択の自由度を特徴づける。移送元の完全幾何を表示変更して入力を
  作り直した後にも、生成された比較・移送・分類がその表示変更に沿って自然に対応する
  ことを確定する。さらに、係数の観測がこの分類のどの情報を失うかを示す。
- `core tension`: 各端点で許される変更が、比較射を越えても許される変更になるとは
  限らない。さらに、生成後の自己同型群だけを動かしても、入力表示変更に対する生成器の
  自然性にはならない。移送元の diagram・edge・comparator・transport を完全幾何の
  表示変更から作り直し、生成前に表示を変える経路と生成後に端点を移す経路が一致するか。
  可換式を移送先へ送る保存と、移送先から元の成立を取り戻す反映を区別する。
- `rival`: arrow category の自己同型群、群準同型の像・核・fiber、共役による
  stabilizer の移送、fibred category の cartesian lift の一意性。差分は、AAT の
  Support / Axis / Observable と資格条件を含む source-only input を完全幾何の表示変更から
  再構成し、実際の二段の生成経路がその変更に自然であることを証明する点に置く。
  比較分類、生成像、残余核、係数で不可視な正負の分離まで同じ自然性へ接続する。
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
  - source 表示変更 C1s: 同じ `ctx,P,k` と固定入力 `I` に対し、各頂点で同じ
    `CoreFiber (ctx.configuration.targetPointAt ctx.source)` に属する別の object `Q'_i`、
    その上の `FixedCoefficientGeometryAt Q'_i.1 k`、`Q'_i` から元の
    `I.sourceFiberDiagram.obj ⟨i⟩` への selected `CoreFiber` iso `ω_i`、およびその
    underlying core iso の上にある selected exact complete-geometry iso
    `w_i : S'_i ≅ S_i` を量化する。`w_i.hom.base` / `w_i.inv.base` が `ω_i.hom.1` /
    `ω_i.inv.1` に一致する投影等式を持ち、係数写像を両方向で恒等に保つ。変更後の
    `sourceFiberDiagram`、edge、comparator、`sourceTransport`、およびそれらの資格・
    two-cell・係数則は入力 field として受け取らず、`I` と `w_i` から構成する。
    変更後の入力を `I^w` と書き、その生成物を `S'_i,B'_i,P'_i,c'_i,H'_B,H'_P,T'_i,J'_i`
    と書く。
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
  保存だけでは完了としない。変更後の入力を既存生成器から独立に生成し、実際の二段の
  strongly-cartesian 因子化から自然性を導く。出力側の同型や可換式を入力 certificate として
  受け取る構成、または `T'_i` を自然性式から定義する構成は完了根拠にしない。
- `phase boundary criteria`: 人間による active 化後に固定した statement を実行する。
  全 completion criteria が満たされるまでは checkpoint とする。
- `reward rubric`: `not-applicable (target-theorem mode)`。
- `dullness filter`: 両立条件を新しい predicate に移すだけの iff、結論を field に持つ
  certificate、恒等移送だけの検証、既存正負例の引用だけの非因子化、抽象群論だけの
  分類を弾く。source 自己同型群の対だけを途中から共役して入力再構成を省くこと、
  変更後の出力・比較・自然性を caller-supplied field にすること、自分自身の range への
  全射だけで生成像の対応を済ませることも弾く。非自明な自由度が存在するという結論は
  先取りしない。
- `frontier`: 観測に追加すべき情報の十分性、variable-comparator の圏、regular comparison、
  restriction category、coherence height、SHIGURE の実現関手と表現可能性。
  これらの構成は本カードの完了条件とは別に設定する。

- `target theorem`: **Source-Presentation-Natural Qualified Comparison Transport and
  Diagnostic Information Loss Theorem**。次の A–D を、上記の量化域で一つの構成と
  分類として接続する。
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

  - **(C) 入力表示変更に自然な分類の移送**

    以下では二種類の表示変更を分ける。`C1s` は生成前の source-only input 全体の
    表示変更、`C1t` は生成後の canonical-authored / generated endpoint 間の既存表示変更で
    ある。同じ C1 量化域として混ぜない。

    **C1s: source complete-geometry presentation change と入力再構成**。全 `I` に対し、
    各頂点 `i` の別の `CoreFiber` object `Q'_i`、その上の `FixedCoefficientGeometryAt`、
    selected `CoreFiber` iso `ω_i : Q'_i ≅ I.sourceFiberDiagram.obj ⟨i⟩`、およびその
    underlying core iso の上にある selected exact complete-geometry iso
    `w_i : S'_i ≅ S_i` を持つ typed change data を量化する。field はこれらの object / iso、
    core への投影等式、両方向の coefficient identity に限る。この data は変更後の
    diagram、edge、comparator、transport、生成端点、生成比較、または自然性等式を field に
    持たない。

    通常の関数合成順で、元の source edge を `L_e : S_i → S_j`、cell の target comparator
    を `q_σ : S_t ≅ S_t` と書くと、

    ```text
    L^w_e := w_j⁻¹ ∘ L_e ∘ w_i
    q^w_σ := w_t⁻¹ ∘ q_σ ∘ w_t
    ```

    により変更後の `sourceFiberDiagram`、`sourceGeometry`、`sourceTransport` を構成し、
    `I^w : UpperGeometryCompatibleProblemInputData ctx P k` を得る。functor の恒等・合成則、
    edge の core-fiber 投影等式、geometry/core 両段の strong-cocartesian 性、`twoCellBase`、
    edge/comparator の coefficient identity をすべて `I`、`w_i`、同型と strongly-cocartesian
    lift の合成安定性から証明する。これらを caller-supplied certificate にしない。
    `root`、`rootPath`、`P`、`ctx`、`k` は元の入力からそのまま保持する。

    source change の identity、inverse、型の合う有限合成を構成し、`I^1 = I` と、連続する
    表示変更から構成した入力が合成表示変更から構成した入力に一致することを、
    `UpperGeometryCompatibleProblemInputData` の equality として示す。proof-field の差だけを
    残した pointwise equality や、後続 theorem ごとの ad hoc comparison で済ませない。

    **C1t: generated endpoint complete-geometry presentation change**。全 `I,i` に対し、
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

    C1t の presentation replacement はこの二つの complete upper presentation の変更と
    逆変更に固定する。`BCPresentationReplacement.lean` の「同一 decoded BC input を持つ
    任意の有限表示」は別の型の一般化であり、C1s/C1t の量化域に混ぜない。

    **C2: 実 edge reselection**。全 `I` と任意の
    `r_B : GeneratedBaseCoefficientTrivialUpperEdgeReselection I`、
    `r_P : GeneratedPulledCoefficientTrivialUpperEdgeReselection I` に対し、
    各 edge の終点 `j` で `(r_B(edge),r_P(edge)) ∈ Γ_(c_j)` を判定する。
    その全 edge にわたる積が既存の
    `CoefficientTrivialUpperReselectionEndpointIntertwining` と同値であることを示す。
    r_B を固定したときの非空な相手 r_P の族には、各 edge の
    `K_(P_j)(c_j) ∩ ker κ_(P_j)` の積が自由かつ推移的に作用することを構成する。
    係数恒等という reselection の条件を落とさない。

    B1 の source coefficient-trivial edge family を `H_B,H_P` で送る生成経路について、
    qualification と所属を theorem で供給し、既存の reselected edge / path /
    authored-comparator pasting / raw-cochain API へ接続する。
    arbitrary paired input の保存補題と、source から paired input を作る存在 theorem を
    分ける。移送する predicate は `Γ_(c_j)` の所属であり、独立に再選択した raw defect
    値の literal equality を要求しない。

    必須非恒等 witness は固定 datum の
    `generatedBaseComparatorCoefficientTrivialUpperReselection` と
    `generatedPulledComparatorCoefficientTrivialUpperReselection` の対、および pulled
    を identity にした負対。`DecisionEdge.twist` 上で評価し、C1t の逆表示変更後にも
    正負と非恒等性を追跡する。

    **C3: 生成移送の保存・反映と source 表示変更自然性**。全 `I,i` の対写像
    `T_i : A_(S_i) × A_(S_i) → A_(B_i) × A_(P_i)`、
    `(a,d) ↦ (H_B(a),H_P(d))` に固定する。source predicate は `Γ_(𝟙 S_i)`、すなわち
    `a=d`、target predicate は `Γ_(c_i)`。B1 から保存を証明し、反映の正確な条件
    `(∀ a d, R_i(a,d) → a=d) ↔ J_i={1}` を証明する。
    `J_i` の入力写像による特徴づけと接続し、固定 datum の `J_*={1}` を決定する。
    正枝は全称的な反映 theorem、負枝は実 `a≠d` と `R_*(a,d)` の反例 theorem。
    faithfulness や `J_i={1}` を入力 certificate として受けて実 decision を済ませない。

    C1s の `I^w` を既存の G-115 生成器へ独立に適用して
    `B'_i,P'_i,c'_i,H'_B,H'_P,T'_i,J'_i` を得る。source change から、実際の package 段と
    geometry 段の strongly-cartesian 因子化および一意性を使って、selected exact
    complete-geometry iso

    ```text
    η_B,i : B'_i ≅ B_i
    η_P,i : P'_i ≅ P_i
    ```

    を構成する。`η_B,i`、`η_P,i`、その inverse、または次の可換式を input field / theorem
    argument にしない。比較成分について

    ```text
    η_P,i ∘ c'_i = c_i ∘ η_B,i
    ```

    を証明する。`Θ_S,i := Ad_(w_i) × Ad_(w_i)`、
    `Θ_BP,i := Ad_(η_B,i) × Ad_(η_P,i)` とするとき、中心自然性

    ```text
    T_i ∘ Θ_S,i = Θ_BP,i ∘ T'_i
    ```

    を、両辺を独立に構成した後の theorem として示す。`T'_i` をこの等式から定義しない。
    C1s の identity、inverse、有限合成に対する `η_B,η_P` と自然性の unitality / composition
    coherence、および各 `I` の C1t との合成順序の整合も証明する。

    この自然性から、`Θ_BP,i(Γ_(c'_i)) = Γ_(c_i)`、両射影・核・非空 fiber と作用の対応、
    `Ad_(w_i)(J'_i) = J_i`、従って `J'_i={1} ↔ J_i={1}` を導く。生成像は自分自身の
    range への全射ではなく、

    ```text
    Θ_BP,i(Set.range T'_i) = Set.range T_i
    ```

    として同定する。C1s/C1t の前後合成後にも、対応する transported generated image との
    equality を保つ。係数観測は `w_i,η_B,i,η_P,i` の coefficient identity から両成分で
    可換することを証明する。

    閉包は C1s の恒等・逆・型の合う有限合成、C1t の恒等・逆・型の合う有限合成、C2 の
    pointwise 積と有限 path の連結、および `C1s ; C3 ; C1t` の型の合う合成に固定する。
    任意の別 context の C3 同士の合成は量化しない。各閉包で移送写像の恒等・合成則、
    Γ の保存、反映条件、係数観測との両立を証明する。C1s/C1t は全単射、C3 は上記で
    同定した生成像への写像として記録する。

    固定 datum では `w_* := UpperDecisionWitness.swap01Iso` を source の complete-geometry
    自己同型表示変更、その qualified automorphism を
    `g_* := UpperDecisionWitness.compositeSwap01`、動かす source 自己同型を
    `a_* := UpperDecisionWitness.compositeSwap12` とする。両者が complete geometry の
    自己同型で係数恒等を保つことを既存 transport から接続し、
    local Support / Axis / Observable の少なくとも一つの `Fin 4` 評価で

    ```text
    (Ad_(w_*) × Ad_(w_*)) (a_*, 1) ≠ (a_*, 1)
    ```

    を証明する。`g ≠ 1` だけから induced action の非恒等性を推論しない。この source
    change に対して変更後の入力、生成自然性、生成像、`J`、係数観測、D の正負分離が
    実際に移送されることを一つの finite witness packet にする。

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

    C1t の全 finite chain に沿い `Q_*` の対を共役し、観測の可換性・Γ の iff・
    正負分離・上記非因子化を一つの theorem に接続する。C1s については固定 finite
    source change から変更後の入力を構成し、C3 の自然性で正負対と観測 equality を移す。
    元の固定例の decision を、変更後の例に同名の decision field を置くことで済ませない。
    C2 の固定 edge 対でも同じ評価を行う。C3 に対しては B1 の全 `a,d` の係数観測の保存を
    証明し、正負分離の反映は C3 の `J` 条件に従う。C3 後に任意の負対が負のままと
    仮定しない。

- `target theorem boundary`: 上記の G-115 geometry 段を対象とする。Lean は
  `research/lean/ResearchLean/AG/DoctrineFiberProduct/` 配下の新 module に置く。
  先行 reviewed module は参照し、既存定理の再証明を独立成果として数えない。
- `target proof artifacts`: A の群・作用・像核の theorem、B の実写像による分類と B2 / J_* の正負決定、
  C1s の typed source change data と certificate-free な変更後 input constructor、C1t の
  endpoint transport、C3 の generated endpoint iso・中心自然性・生成像/J/係数の対応・
  identity/inverse/finite-composition coherence、C2 の reselection closure、D の観測写像と
  移送された分離対、`compositeSwap01/compositeSwap12` の induced-action finite witness packet。
  report は `research/reports/G-118-aat-diagnostic-descent-transport.md` に作成し、
  declaration-level evidence map、決定枝、入力の provenance と proof-use を記録する。
- `target proof strategy`: 改訂 F0s(source change の型、変更後 input constructor、両段の
  strong-cocartesian 資格、生成された `η_B/η_P` の構成可能性を先に判定) → A/B と既存
  C1t/C2/C3/D の reviewed 成果を新しい固定 statement へ再監査 → C1s の入力再構成 →
  生成比較と `T` の中心自然性 → Γ/J/生成像/係数と C1t/C2/D の接続 → fixed finite firing →
  completion audit。改訂前 cycle の受理を自動継承せず、宣言単位で statement match と
  proof-use を再確認する。F0s で exact geometry iso または二段生成自然性が構成不能なら、
  後続の群閉包を追加せず exact blocker を固定する。
- `target theorem completion criteria`: 固定した A–D の全義務を sorry なしの Lean theorem または
  あらかじめ許容した具体的反証枝の sorry なしの Lean theorem で確定する。focused check の静的チェック通過と、
  statement 一致、axiom / placeholder audit、material premise discharge、provenance、
  proof-use、structure-field escape、route integrity、非空虚性の監査を分けて記録する。
  各実装 PR の fixed-head `$review-pr`、report / tracking Issue 同期、final_review_packet、
  別工程の `$math-lean-review` 4 独立査読の全 `No major findings` を要求する。
  C1s では変更後 input の全 structure field が `I,w` から構成され、C3 では `I^w` に既存
  generator を独立適用した `T'_i` と出力を使うことを theorem body / dependency audit で
  確認する。`η_B/η_P`、比較可換式、中心自然性、生成像 equality、`J` 対応を受け取る
  certificate / structure field がないこと、finite witness が induced pair action を実際に
  発火させることを確認する。
  詳細は [target-goal-contract](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md)。
- `target premise discharge policy`: 入力幾何と先行 theorem を参照として残す。
  C1s の別 source geometry、selected `CoreFiber` iso `ω_i`、その上の selected exact iso
  `w_i`、および両方向 coefficient-id 条件は statement の量化対象として残す。変更後の
  diagram / transport / qualification、
  generated endpoint iso、移送可能性、自然性、共役対応、反映、生成像 equality、観測の
  可換性は導出対象。
  一般補題の方向仮定と、名前付き対象でその仮定を証明する義務を区別する。

- `target material premise ledger`:
  各 discharge artifact は入力構成または先行 theorem から proof term を生成し、その宣言が
  最終定理に使われることを evidence map に記録する。

  | premise | role | 支える結論・artifact・結論相当でない理由 |
  | --- | --- | --- |
  | G-115 の入力幾何と reviewed theorem | ambient-boundary | route / component と既存正負対。新しい分類・移送 theorem は含まれず、宣言単位で参照する |
  | G-115 の exact endpoint iso / conjugationMulEquiv | ambient-boundary | 全資格群の同値は既証明。Γ・核・fiber・観測を含む C1t の統合は新しい theorem とし、既存宣言を proof-use する |
  | C1s の別 source complete geometry、`ω_i`、`w_i` | ambient-boundary | 表示変更の量化対象。`CoreFiber` iso、exact geometry iso の投影等式、両方向 coefficient identity だけを持ち、変更後 input、生成出力、自然性、分類対応は含まない |
  | `I^w` の source diagram / edge / comparator / transport | discharge-required | `I,w` からの input constructor。functor laws、投影等式、両段 strong-cocartesian、two-cell base、係数則を caller field にせず導く |
  | generated `η_B,i,η_P,i` | discharge-required | `I` と `I^w` に既存二段 generator を独立適用し、cartesian factorization と一意性から exact complete-geometry iso を構成する。iso 自体を入力しない |
  | `η_P,i ∘ c'_i = c_i ∘ η_B,i` と `T_i ∘ Θ_S,i = Θ_BP,i ∘ T'_i` | discharge-required | C3 の中心自然性。可換式を field / argument にせず actual generated definitions を展開または既存生成則へ接続して証明する |
  | source change の identity / inverse / finite composition coherence | discharge-required | C1s と generated `η/T` の typed coherence。proof-field irrelevance だけの equality や pointwise wrapper では済ませない |
  | `Θ_BP,i(Set.range T'_i) = Set.range T_i` | discharge-required | C3 の生成像 correspondence。generic `rangeRestrict_surjective` は自分自身の像への全射なので代替にならない |
  | `Ad_(w_i)(J'_i)=J_i` と triviality iff | discharge-required | 反映条件の表示独立性。`J` の自明性や faithfulness を入力 certificate にしない |
  | `L_c(b)` の非空性、`c` の同型性 | direction-hypothesis | A の条件付き群論。B の名前付き対象では存在・同型性を独立に決定する |
  | 像・核・fiber の実写像による特徴づけ | discharge-required | B の分類 theorem。membership を受け取るだけの field は証拠にならない |
  | 端点同型による Γ・核・fiber の対応 | discharge-required | C1t の統合。既存 exact iso と資格群の共役から導き、比較の actual equality を proof-use する |
  | 両立性の反映・移送の合成整合 | discharge-required | C の固定枝と coherence。faithfulness や可換式を caller から供給しない |
  | 係数観測の carrier・準同型則・移送との可換性 | discharge-required | D の核と移送後の分離。実 coefficient map から構成する |
  | 固定正負対の移送後の所属・非所属 | discharge-required | D の非因子化。先行 witness と C の theorem の両方を proof-use する |
  | fixed induced-action firing | discharge-required | `compositeSwap01` と `compositeSwap12` の actual local `Fin 4` evaluation から pair action の非恒等性を示す。作用元の `≠ 1` だけでは放電しない |

- `target route integrity gate`: `upperDecisionSolution`、
  `upperDecisionSolution_comparatorDescentAt`、
  `generatedBaseIdentityPair_not_comparatorDescentAt`、
  `generatedPulledIdentityComparator_coefficient_id` を必須の接続点とする。
  C1s の input reconstruction では `UpperGeometryCompatibleProblemInputData` の source-only
  constructor、`FixedCoefficientTwoLayerTransportOver` の全 field、source edge の geometry/core
  両段の strongly-cocartesian 性と同型合成での保存を必須経路とする。C3 の generated
  endpoint iso では、実際の G-115 base/pulled reverse-route leg の strongly-cartesian 性、
  `baseCompositeLegAt_naturality` / `pulledCompositeLegAt_naturality`、底射同型に沿う domain
  comparison とその factorization、refinement geometry iso の exactification を必須経路とする。
  `I^w` を独立入力として
  受けること、`η_B/η_P` または自然性可換式を入力すること、自然性式から `T'_i` を定義する
  こと、source group の内共役だけを直接 C3 前に置いて input reconstruction を省くことを
  禁止する。
  関連 module は `UpperGeometryCompatibleDecisionFixtures.lean`、
  `UpperGeometryCompatibleComparatorIncoherence.lean`、
  `UpperGeometryPairedCoefficientTrivialReselection.lean`、
  `UpperGeometryFullPairedReselection.lean`。宣言 map は下記の fixed source map に固定する。
  結論に合わせた fixture 差し替え、移送族の後追い選択、paired 条件を受けるだけの
  構成を存在分類と数えること、一般群論による A だけの完了を禁止する。固定 firing は
  `compositeSwap01`、`compositeSwap12` と既存 local Support / Axis / Observable evaluation を
  使い、別の都合のよい有限群を追加しない。
- `target anti-weakening rule`: A–D の結論を仮定、typeclass、certificate、opaque
  membership に移さない。非空性と非自明性、保存と反映、有限の決定と一般の分類を
  区別する。同型の共役補題で生成器の自然性を代替しない。C1s の input constructor、
  `η_B/η_P`、中心自然性、生成像 equality、`J` 対応のいずれかを caller data に移した
  package は未放電仮定とする。作用元の非恒等性を induced action の非恒等性と数えない。
- `target failure policy`: active 化後の固定構成義務に具体的反例が立てば
  `target-refuted`。事前固定した分類枝の具体的決定は当該義務の成果とする。
  型不能・指示対象欠落は `goal-defect`、未証明は `target-proof-checkpoint`、
  同一 blocker が二 cycle 続けば `target-blocked`。対象・仮定・結論の改訂は人間の判断による。
  B2 / C3 の枝選択を `Classical.em`、`not_forall`、choice のみで済ませず、
  指定したデータ上の構成または計算と実写像の証明を要求する。

- `fixed source map`: 以下は `research/lean/ResearchLean/AG/` に相対的な module 名。
  revision 2 の source base は `4f8ba8f8396ce3bbdd00c581941acee73967096b`。
  改訂 F0s はこれらの宣言の対象を差し替える工程ではなく、新しい source change と
  generated naturality の構成可能性を固定 statement の型で判定する工程。

  | 義務 | module / 既存宣言 | 新しく証明する接続 |
  | --- | --- | --- |
  | C1s F0 | `DoctrineFiberProduct/UpperGeometryCompatibleInput` / `UpperGeometryCompatibleProblemInputData`、`UpperRefinementBCProblem` / `FixedCoefficientTwoLayerTransportOver`、`UpperRefinementBCGeometry` / `FixedCoefficientGeometryAt` | 別 source geometry と selected exact iso だけから変更後 diagram / edge / comparator / transport と全 structure field を構成 |
  | C1s source-edge qualification | mathlib `CategoryTheory.Functor.IsStronglyCocartesian.of_iso` / `.comp`、`DoctrineFiberProduct/UpperGeometryCompatibleDecisionFixtures` / `swap01_geometryStrong`、`swap01_coreStrong` | edge 共役後の geometry/core 両段 strongly-cocartesian qualification。cocartesian API はこの source-edge constructor にだけ使う |
  | C1s generated lower naturality | `DoctrineFiberProduct/UpperRefinementBCSolution` / `ActiveRefinementBCContext.baseCompositeLegAt_naturality`、`pulledCompositeLegAt_naturality` | `ω_i` に沿って新旧 reverse-route の底射を比較し、generated domain comparison の base factorization を作る |
  | C1s generated endpoint iso | `DoctrineFiberProduct/UpperGeometryCompatibleInput` / `generatedBaseRouteLegAt_isStronglyCartesian`、`generatedPulledRouteLegAt_isStronglyCartesian`、mathlib `CategoryTheory.Functor.IsStronglyCartesian.domainIsoOfBaseIso` / `.fac`、`DoctrineFiberProduct/UpperGeometryCompatibleEndpointGeometryIsos` / 既存 endpoint comparison pattern、`UpperGeometryFiniteGeometryExactification` / `exactGeometryHomOfRefinement`、`UpperGeometryCompatibleEndpointExactIsos` / refinement-to-exact iso の既存 pattern | reverse-route leg の strongly-cartesian domain comparison から generated refinement geometry iso と factorizationを構成し、selected exact `η_B,η_P` へ exactifyする。cocartesian lift uniqueness で代替しない |
  | A / D | `CrossStageCoherence/ObstructionGroups` / `CompositeFiberAut`、`GeometryTransport/Categories` / `GeometryTotalHom`、`GeomReadHom` | Γ の群・作用、coefficient Aut 準同型 |
  | B1 / C3 | `DoctrineFiberProduct/UpperGeometryCompatibleComparatorMapLaws` / `generatedBaseCompositeFiberAutHomAt`、`generatedPulledCompositeFiberAutHomAt` | 任意 source 自己同型での mate 両立、J の特徴づけと反映 |
  | B1 | `DoctrineFiberProduct/UpperGeometryCompatibleComparatorGeometry` / `generatedBaseCompositeFiberAutAt_fac`、`generatedPulledCompositeFiberAutAt_fac` | source の任意 a,d と実 carrier 条件の接続 |
  | B2 / C3 | `DoctrineFiberProduct/UpperGeometryCompatibleDecisionFixtures` / `UpperDecisionWitness.problem`、`solution`、`upperDecisionSolution` | c_* の同型・両核・両射影全射・J_* の決定 |
  | C1t | `DoctrineFiberProduct/UpperGeometryCompatibleEndpointExactIsos` / `canonicalAuthoredBaseToGeneratedRouteExactGeometryIsoAt`、`canonicalAuthoredPulledToGeneratedRouteExactGeometryIsoAt` と `_coefficient_id` 群 | 全資格群・Γ・核・fiber の共役対応 |
  | A / C1t | `DoctrineFiberProduct/UpperGeometryCanonicalAuthoredTransportLaws` / `conjugationMulEquiv`、`canonicalSolutionForwardAt_exact_normalization`、`generatedSolutionBackwardAt_exact_normalization` | 既存共役・exact等式を Γ の移送へ接続 |
  | C1t | `DoctrineFiberProduct/UpperGeometryCompatibleSolutionEquivalence` / `canonicalGeneratedUpperRefinementBCSolutionEquiv`、`canonicalCompanionUpperRefinementBCSolution` | c_can と c_i の exact total equality |
  | C2 | `DoctrineFiberProduct/UpperGeometryPairedCoefficientTrivialReselection` / `generatedComparatorUpperReselections_endpointIntertwining_fires`、`generatedBaseComparatorPulledIdentity_not_endpointIntertwining` | edgewise Γ と係数核の作用、非恒等な移送対 |
  | C3 source naturality | `DoctrineFiberProduct/UpperGeometryCompatibleComparatorMapLaws` / `generatedBaseCompositeFiberAutHomAt`、`generatedPulledCompositeFiberAutHomAt`、`DoctrineFiberProduct/UpperGeometryCompatibleEndpointNaturality` / `canonicalAuthoredBaseToGeneratedRouteGeometryIsoAt_naturality`、`canonicalAuthoredPulledToGeneratedRouteGeometryIsoAt_naturality`、`DoctrineFiberProduct/QualifiedComparisonEndpointTransport` / endpoint conjugation API | independently generated `T'_i` と `T_i` の中心自然性、Γ/J/生成像/係数の対応。既存 endpoint naturality は証明形の先例であり、source-input naturality の代替ではない |
  | fixed C1s firing | `DoctrineFiberProduct/UpperGeometryCompatibleDecisionFixtures` / `swap01Iso`、`compositeSwap01`、`compositeSwap12`、`source_edge_local_support_fires`、`source_edge_local_axis_fires`、`source_edge_local_observable_fires`、`authored_comparator_local_support_fires`、`authored_comparator_local_axis_fires`、`authored_comparator_local_observable_fires` | induced simultaneous conjugation が concrete `Fin 4` pair を動かし、変更後 input の分類と D を発火 |
  | D | `DoctrineFiberProduct/UpperGeometryCompatibleComparatorIncoherence` / `upperDecisionSolution_comparatorDescentAt`、`generatedBaseIdentityPair_not_comparatorDescentAt` | C1s/C1t を経た非因子化 |
