# Rising Sea — 数学内容の棚卸し

[論文構成マスター](paper-structure.md)の第1〜8章について、収録する定義・構成・定理・反例、
成立条件、章間の接続と一次資料を整理する。AAT 数学本文の全10部と付録、
基礎・診断・輸送・比較・再構成の研究成果を素材とする。CS 対応はその中に配置する。

## 読み方と照合範囲

- 各表の番号は棚卸し項目の識別子であり、論文の定理番号ではない。
- 「構成・定理」は記載した入力・仮定の下での結果、「反例・不可能性」はその量化域での否定を表す。
  「接続項目」は、論文の一つの体系として述べるために、対応する構成や証明を揃える数学的な仕事である。
- 数学本文の命題、Lean 宣言、GOAL の要求、report の到達範囲を区別する。
  source 欄は対応する証拠への入口であり、候補命題や未接続の要求を証明済みに数えない。
  既存証明の全行再査読・Lean 再検証は、この棚卸しの確認範囲に含めない。
- 数学資料の照合版は commit
  [`b0a2d4b2`](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/tree/b0a2d4b2690a1aabdf64f033c9fc6ca975f7445e)
  とする。特に局所再構成は、この版の [G-124 report][r124] の Cycle 68 と「未完了 ledger」までを照合した。
  以下の証拠範囲はこの固定版について述べる。
- n1012・n1015 を含むノートは参考資料とし、章立ては構成マスター、数学の定義・証明は一次資料に従う。
  合成は `gf=g∘f` と書く。Lean の `f ≫ g` はこの `gf` に対応する。

| 章 | 棚卸しの中心 | 後続へ渡すもの |
| --- | --- | --- |
| 1 | Atom・Law・operation・reading、相対的な対象・射・site | core と幾何の共通入力、射影の塔 |
| 2 | Law algebra、lawful locus、具体的な貼り合わせ障害、SAGA | 係数と障害類の生成経路 |
| 3 | 標準解像度、表示可能性、診断不変性の十分条件と一般判定 | 比較写像と、診断が保存される正確な条件 |
| 4 | core・幾何の輸送、普遍性、合成と二層の障害 | 関手・比較同型・再選択の作用 |
| 5 | doctrine の積、exact / refinement 基底変換、上段比較 | 型と生成元の揃った二経路と比較射 |
| 6 | 冪等正規化、像、Karoubi 実現、自然性の反例 | raw 比較と像の比較、正規化関手 |
| 7 | 比較保存群、観測と正規化、変更の持ち上げ、CS 共通分類 | 核・像・section・fiber と情報損失の判定 |
| 8 | 有限表示、局所表示、対象・射の再構成、有限決定性 | 回復できる構造と、回復に必要な情報 |

## 第1章 相対的アーキテクチャの構成

### 1.1 基礎対象と幾何の入力

| 項目 | 種類・数学内容 | 入力・成立条件と受け渡し | 主な一次資料 |
| --- | --- | --- | --- |
| 1-A Atom と抽出 | 公理・構成。typed Atom、family、support、抽出 doctrine、`Atomize_D(s)` の存在一意性 | 語彙、意味 reading、resolution、source semantics、normalization を固定する。一意性は同じ抽出述語の外延性から導く | [本文 I §§1–3][math-i]、[Atom 公理・抽出][atom-axioms] |
| 1-B configuration と対象 | 構成。有限 family から relation・identification を持つ configuration、さらに structure maps・selected quantities を持つ architecture object | composition reading と object reading が入力 family / configuration を保持する。configuration が等しくても object が等しいとは限らない | [本文 I §§4–5][math-i]、[core の生成][core] |
| 1-C operation と生成 core | 構成・閉性。実 configuration hom を持つ operation、invariant、signature、基点対象から到達する operation-closed algebra | operation そのものの同一性と configuration への作用を保持する。作用が等しい二つの operation を同一視しない | [本文 I §§6・10][math-i]、[ObjectAlgebra][object-algebra]、[core の生成][core] |
| 1-D Law と有限 detector | 定義・条件付き対応。equation index / role、環値 presheaf、symbolic coordinate `ν`、object-dependent residual `ε`、signed-query circuit | Lawfulness は required residual の同時消滅。detector の soundness と completeness は別の条件。`ν` と `ε` の役割を第2章へ渡す | [本文 I §§7–9][math-i]、[LawfulnessZero][lawfulness] |
| 1-E context と被覆 | 構成。Support・Axis・Observable、context の射、coverage requirements、選択した pullback overlap、生成 Grothendieck topology | 要件を満たす cover の族から topology を生成する。生成 topology の cover であることと、必要な座標・witness を読む adequate cover であることを区別する | [本文 II §§2–8][math-ii]、[Coverage][coverage]、[Topology][topology] |
| 1-F sheaf と幾何 | 構成。presheaf、matching family、sheaf、sheafification、site の幾何 | raw presheaf と true sheaf の貼り合わせを区別する。係数環・raw restriction system・局所実現の入力を明示する | [本文 II §§9–13][math-ii]、[ReadingCore][reading-core]、[GeometryPackage の基礎][geometry-basic] |
| 1-G 対象と射の塔 | 圏・関手。`E_geom → E_core → B`、`B=ExtractionInstance`、exact doctrine 射と pointed 射 | exact 射の Atom 成分は同値、source map は一般写像。core 射と geometry 射が保存する全成分を定め、各射影が何を忘れるか示す | [core 総圏][atom-categories]、[幾何総圏][geometry-categories]、[三段の投影][three-stage] |

依存順は `Atom / doctrine → family → configuration → object / operation → context / equation / signature
→ coverage / overlap → site → coefficient / raw system` とする。Law や観測によって Atom の存在を生成しない。
`AATCorePackage` の生成と `GeometryPackage` の選択データを、この順に一度ずつ導入する。

**接続項目。** 数学本文の相対パラメータ、`Formal` の `ReadingCore`、研究側の `GeometryPackage`
は同じ成分表で照合する。後者は `ReadingCore` の略記だが、各圏の射の条件まで略記だけで
一致するとは扱わない。CS の一般の意味保存写像を Atom の同値へ直接置き換えず、
型・操作名と状態 carrier の役割を分けて構成する。

### 1.2 モデル同期の独立な意味論

view の集合 `V` と基準値 `v₀` を固定し、状態集合 `C`、読取り `g:C→V`、
更新 `p:C×V→C` を持つ全域 lens を扱う。対象条件は次の三法則と、
基準 fiber `K_L={c∈C | g(c)=v₀}` の有限性とする。`V` 自体は無限でもよい。

\[
 p(c,g(c))=c,\qquad g(p(c,v))=v,\qquad p(p(c,v),w)=p(c,w).
\]

固定 view 上の一般の意味保存射は、`g'h=g`、`h(p(c,v))=p'(h(c),v)` を満たす関数 `h` とする。
三法則から `c↦(g(c),p(c,v₀))` による積表示 `C≃V×K_L` を与え、
基準 fiber への制限と、任意の写像 `t:K_L→K_L'` の延長

\[
 \operatorname{ext}(t)(c)=p'\bigl(t(p(c,v_0)),g(c)\bigr)
\]

が互いに逆になることを示す。この対応により有限集合間の table から一般射を回復する。

可視変更 `u:V≃V` に追随する可逆変更 `h:C≃C'` には、同じ `h,u` による
`g'h=ug` と `h(p(c,v))=p'(h(c),u(v))` の同時成立を要求する。
積表示での形 `h(v,k)=(u(v),φ(k))` により、変更を一つの補完の全単射 `φ` で記述する。
`u` は `v₀` を固定する必要がない。

`V=K=Bool` の積 lens で `h(v,k)=(v,k⊕v)` を取る例を導入に置く。
この変更は get を保つが put を保たず、可視変更を恒等に固定したとき、
get のみを保つ変更 4 個のうち get・put を共に保つものは 2 個になる。
この差を、第7章の変更分類と第8章の有限決定性へつなぐ。

一次資料: [LensSemantics][lens-semantics]、[一般射の有限 fiber 表示][lens-finite]、
[可逆変更と共通分類の対応][lens-connection]。保存図式の一次資料は §4.2、有限例は §7.2 を参照。
ここでの積表示は第7章の可逆変更分類と、第8章の一般射の再構成の共通の出発点となる。

### 1.3 プロトコルの独立な意味論

有限有向多重グラフ `Q` と有限個の経路等式 `L` から実行圏 `C_Q` を定める。
観測先の関手 `O:C_Q→Set` を固定し、各制御点の状態が有限である関手 `X:C_Q→Set` と
自然変換 `o:X→O` を実現とする。一般射 `a:X→Y` は観測を保つ自然変換とし、
非可逆な adapter も含める。観測値の集合は無限でもよい。

有限表示は、制御点ごとの状態 table、名前付き生成辺の作用、各状態の観測値、
経路等式から構成する。一般射は、生成辺 `e:v→w` ごとの
`a_w X(e)=Y(e)a_v` と `o_Y(v)a_v=o_X(v)` を満たす頂点 table から回復し、
経路帰納によって全実行へ延長する。異なる操作名は、状態写像が同じ場合にも保持する。

adapter `q:X→Y` と `q':X'→Y'` に対する変更 `a:X→X'`、`b:Y→Y'` の条件を
`b∘q=q'∘a` とする。各頂点でのこの等式と操作保存から、全実行との整合を示す。
可逆変更の分類では `a,b` を同型に制限し、adapter 自体は一般射のまま扱う。
操作名を変える版では、グラフ自己同型と経路等式・観測の輸送を別の入力として定める。

一次資料: [ProtocolSchema][protocol-schema]、[ProtocolSemantics][protocol-semantics]、
[ProtocolFinitePresentation][protocol-presentation]、[観測付き一般射の有限表示][protocol-finite]。
操作を隠れ状態上で恒等とする場合の可逆変更は [共通分類との対応][protocol-connection]、
adapter の保存図式は §4.2、有限例は §7.2 の一次資料へ対応させる。
経路圏の射は無限にあり得る。有限なのは制御点・生成辺・宣言関係・各状態 carrier であり、
全実行の列挙を有限表示の入力にしない。

## 第2章 Law の幾何と局所整合性

### 2.1 方程式から幾何・係数へ

| 項目 | 種類・数学内容 | 入力・成立条件と結論 | 主な一次資料 |
| --- | --- | --- | --- |
| 2-A ambient Law algebra | 構成。`O_raw(W)=k[Coord(W)]/J_struct(W)`、restriction、ring sheaf | 構造関係からの商と Law witness ideal による商を分ける。observable ring の表示同型と restriction の整合を保持する | [本文 III §§2–4][math-iii]、[AmbientAlgebra][ambient-algebra]、[StructureSheaf][structure-sheaf] |
| 2-B obstruction ideal | 構成。`I_i=(ν_{i,a})`、required index の和 `I_Ob`、ideal subpresheaf と sheaf-image | generator の restriction 則から ideal の包含を導く。optional / all-index 版を required 版と区別する | [本文 III §§5–6][math-iii]、[WitnessIdeal][witness-ideal]、[ObstructionIdeal][obstruction-ideal] |
| 2-C affine chart と lawful locus | 構成・表現可能性。raw configuration functor の affine 表現、`V(I_Ob)`、chart の貼り合わせ | underlying `Spec` は通常の prime spectrum。scheme atlas には open immersion と cocycle が必要で、ringed topos だけから scheme 性を結論しない | [本文 III §§7–10][math-iii]、[付録 A.3–A.8][math-app]、[AffineChart][affine-chart]、[StandardScheme][standard-scheme] |
| 2-D equation / ideal 対応 | 条件付き定理。required residual 消滅、section に沿う extension ideal の零性、lawful locus への因子化の同値 | equation-generated scheme realization、generator / localization の生成定理、ideal の和との可換性、zero locus の普遍性を使う | [本文 III 定理5.2C・11.1][math-iii]、[Correspondence][law-correspondence] |
| 2-E 障害係数の二つの生成 | 構成。商係数 `Q_E=O_E/I_Ob` と residual class、および circuit → witness ideal → 選択係数の写像 | 商で零になる symbolic generator 自身を failure detector にしない。後者の自然な `ρ:I_i→Ob`、no-cancellation、検出性は採用する係数ごとに示す | [本文 III 定理11.4–11.5][math-iii]、[本文 IV §2][math-iv]、[ObstructionSheaf][obstruction-sheaf] |
| 2-F Čech 障害 | 構成・条件付き定理。local mismatch の cocycle と類 `[g]`、local flatness gap、補正後の global section | abelian coefficient、実際の mismatch、cocycle 則、effective local adjustment / torsor と descent を固定する | [本文 IV §§3–7・11][math-iv]、[GluingMismatch][gluing-mismatch]、[FlatnessCriterion][flatness] |
| 2-G 障害空間の次元・検出・消滅 | 定理・条件付き系。Topological Debt Capacity、定数係数の Betti 数、Euler Accounting、forest 消滅、boundary residue、period–Stokes、二相係数の support 単射 | 次元には有限次元性、Betti 数には選択した nerve との比較を使う。forest 消滅には triple face 不在・restriction 全射、二相には条件 E・構造側 `H¹=0` を使う | [本文 IV §§8–13][math-iv]、[CoverNerve][cover-nerve]、[二相比較][two-phase-h1]、[forest 系][two-phase-forest] |
| 2-H semantic repair と SAGA | 構成・条件付き同型。独立に生成した semantic 係数と equation 係数の比較、residual class 対応、actual global repair | 有限 monomorphic cover、relation / generator completeness、equivariant local-state map、local atlas、empty-overlap normalization、true sheaf を明示する | [本文 X][math-x]、[EquationProduction][saga-production]、[KappaComparison][saga-kappa]、[TrueSheafDescent][saga-descent]、[Saga][saga] |

### 2.2 主要命題の強さを揃える

方程式から幾何へ進む中心線は、適用する scheme realization の条件の下で

\[
 \operatorname{EquationLawful}_E(s)
 \iff s^*I_{\mathrm{Ob}}^E=0
 \iff s\text{ factors through }V(I_{\mathrm{Ob}}^E)
\]

とする。`Flat` はここでは lawful locus の記号であり、平坦射の意味の flatness と区別する。
一つの環での生成イデアル、site 上の ideal sheaf、scheme 上の extension ideal は、
それぞれの比較写像を通して結ぶ。

2-F では一般の abelian torsor の貼り合わせと、AAT の lawfulness への帰結を分ける。
後者には [本文 IV 定理11.1][math-iv]の E-adequate cover、obstruction の soundness・completeness、
axis exactness、witness coverage を課し、表の effective な調整作用・torsor・descent と併せて用いる。

2-G の次元に関する結果は短い命題・系として収録する。有限次元の cochain complex に対する
Topological Debt Capacity は

\[
 \dim_k H^1\geq\dim_k C^1-\dim_k C^0-\dim_k C^2
\]

である。定数係数と標準的な restriction を持つ被覆では、選択した nerve との比較
`H¹(𝒰,k)≅H¹(N(𝒰),k)` を与え、`dim_k H¹(𝒰,k)=b₁(N(𝒰))` を得る。
Euler Accounting は有限複体の交代和 `χ=Σ_n(-1)^n dim_k Cⁿ` を扱う。
各次数の cochain 次元を保つ変更は `χ` を保つ。個々の `H¹` や指定障害類の不変性とは分ける。
[CoverNerve][cover-nerve]では、容量下界を `topologicalDebtCapacity_fromComplex`、
Betti 数との対応を `ConstantCoefficientNerveReading.dimH1_eq_b1`、
0・1・2 次の交代和とその保存を `EulerCochainAccounting` に照合する。
定数係数の形式化は比較同型を入力に取るため、採用する被覆からその比較を与える構成も明示する。

二相分解では、抽出の真偽が宣言された意味変形族に対して不変かどうかで structural / semantic を定める。
restriction と differential が structural 部分を保つ条件 E の下で

\[
 0\longrightarrow F_{\rm struct}\longrightarrow F_{\rm all}
 \longrightarrow F_{\rm sem}\longrightarrow0,
 \qquad
 H^1(F_{\rm struct})=0
 \Longrightarrow H^1(F_{\rm all})\hookrightarrow H^1(F_{\rm sem})
\]

を得る。E が破れる例と、E が成立しても構造側 `H¹` が非零となる例を
[有限 witness][two-phase-witness]から対で収録する。AtomKind のラベルだけの分割に置き換えない。

SAGA では、`M_sem` と `Q_E`、二つの複体、二つの residual を独立に構成した後、
自然同型 `Φ:M_sem≅Q_E`、cochain 同型 `κ`、`κ_*[r_sem]=[r_E]` を示す。
local atlas を独立に選んだ場合は、cochain の一致ではなく明示的 coboundary を隔てた class の一致となる。
零類から actual repair へ進む最後の段は true sheaf の貼り合わせを使う。

**接続項目。** 論文では「イデアルによる Law の読み」と「選択係数による障害類の読み」を、
2-D・2-E・2-H の写像を用いて接続する。`H¹` 群が非零であること、与えた局所データの類が
非零であること、補正が実現可能であることを別の命題にする。
二つの小例は、forest / cycle と独立な semantic / equation 表示で十分かを検討し、
大きなシステム設定を加えない。

## 第3章 標準解像度と診断不変性

### 3.1 解像度・係数・被覆の比較

| 項目 | 種類・数学内容 | 入力・成立条件と結論 | 主な一次資料 |
| --- | --- | --- | --- |
| 3-A 標準解像度 | 構成・普遍性。`x∼_L y ⇔ ∀ℓ, eval_ℓ(x)=eval_ℓ(y)` による商 `q_L` | `L`-adequate reading のうち最粗。任意の adequate 商を通る factor と一意性を示す | [JointKernel][joint-kernel]、[G-103 固定命題][g103] |
| 3-B 実効計算と表示可能性 | 定理・正負例。有限 partition の計算と `q_L` の kernel 同値、doctrine 誘導の admissible class での表示 | 有限 Source・有限 Law index・値の等号判定が計算の入力。ambient 商の存在と、指定 class 内での representability を区別する | [Effective][resolution-effective]、[Admissible][resolution-admissible]、[NegativeWitness][resolution-negative] |
| 3-C 診断比較の生成 | 構成。adequate pair、canonical factor `π`、supported nerve 射から cochain map を生成 | 係数は `ℚ`、座標は `(Law,相異なる評価値)`。chart の台から edge / face の台を交わりで導き、退化 face の hereditary 条件を課す | [LawGeneratedComplex][law-complex]、[GeneratedComparisonMap][diagnostic-map] |
| 3-D Atlas の不変性 | 十分条件定理。条件 C の下で実比較が `H¹` 同型を誘導 | C0–C6 を下記の意味で保つ。adequacy だけで診断不変性を主張しない | [ResolutionInvarianceConditions][atlas-conditions]、[block 比較の全単射][atlas-bijective]、[診断不変性の系][atlas-corollary] |
| 3-E 一様不変性の判定 | 必要十分条件・decider。全非空値部分集合 `A` の比較の kernel / cokernel defect が零 | law-value block と A-subnerve の同定、indicator Law による逆方向を使う。計算可能性は明示的 finite presentation 上で述べる | [UniformityReduction][uniform-reduction]、[DefectSemantics][uniform-defect]、[UniformPresentationDecider][uniform-decider] |
| 3-F 十分域と観測限界 | 反例・不可能性。C 各条項の非必要性、同じ局所観測でも異なる一様不変性 | `ConditionCAllA` は一様不変域の真部分。`G_local-v1` の非因子化はその固定観測言語に相対化する | [AtlasPositioning][atlas-position]、[G-107 固定命題][g107]、[GLocalV1Nonfactorization][local-nonfactor] |
| 3-G 構造台の不変性と係数選択 | 定理と反証。意味変形下で構造 nerve が等式として一致し、全 Atom nerve は変わり得る。一方、固定 source-label 生成係数の `H¹` は常に零 | G-105 の非零障害を要求する発火命題は反証済み。成立した nerve・restriction・局在化の結果と分ける | [NerveGeneration][struct-nerve]、[StructuralLocalization][struct-local]、[GeneratedH1Vanishing][struct-zero]、[G-105 report][r105] |

### 3.2 不変性の仮定と正負例

Atlas の条件 C は、C0: 被覆像の合致、C1: 各座標 subnerve の非空連結な chart fiber、
C2: edge lift、C3: fiber 内の有理 1-cycle を内部 face boundary が張ること、C4: face lift、
C5: coarse edge lift の一意性、C6: coarse self-loop に写る edge の self-loop 性からなる。
C0・C5・C6 は nerve 全体、C1〜C4 はすべての Law-value 座標の部分 nerve について課す。
C2・C4 の lift は同じ座標ラベルを保つものとする。
C3 の局所非輪状性を含む十分条件であり、一般の必要十分条件ではない。

条件 C の[非退化な正例][atlas-firing]を本論に置く。単射でない粗化、非自明な座標 fiber、
両側の非零 `H¹` 類があり、実際に生成した比較写像は全単射となる。
粗い側の指定した非零類が細かい側の非零類へ送られることを示し、
情報を落とす変更でも条件 C の下で診断を保てることを説明する。
一次資料の `fixed_claim_v` に入力・条件・類・実比較が同時に現れる。

一様判定では、`J_A=(dim ker H¹(φ_A), dim coker H¹(φ_A))` として

\[
 \text{すべての adequate Law 族に対する不変性}
 \iff \forall\varnothing\ne A\subseteq q.\mathrm{Target},\quad J_A=(0,0)
\]

を使う。固定 Law 族の条件 C と、全非空 `A` に条件を課す `ConditionCAllA` の間には
[条項ごとの bridge][atlas-all-a-bridge]が要る。

`ConditionCAllA` の[非退化な正例][atlas-all-a-firing]では `firing_conditionCAllA` と
有限表示 `pFire` の `pFire_conditionCAllACheck` を対応させる。
[checker の正しさ][atlas-all-a-checker]は、有限表示から生成した幾何について
`conditionCAllACheck = true ↔ ConditionCAllA` を述べる。正例の有限表と checker の詳細は付録Bに置く。

最小限の反例枠は、admissible class 内での最粗 reading の非表示、非 adequate 粗化による
偽の類・真の類の隠蔽、adequate でも被覆条件が破れる例、観測等値な T3 / T6 の対とする。
非表示例は [G-103 の反例][resolution-negative]、粗化・被覆の例は [G-104 の正負例][g104]、
局所観測が一致する対は [G-107 の証拠][g107]に対応させる。

**接続項目。** 第2章の一般の `Ob` / `Q_E` と、この章の K0・K1 による law-value 係数は
入力も生成規則も異なる。診断不変性を第2章の特定の障害へ適用する箇所では、
係数・nerve・比較写像の同定を明示する。source-label 係数での消滅を、他の係数や
すべての AAT 障害の消滅へ拡張しない。

[本文 VIII §7 の Class Transport][math-viii]は、この係数比較の説明へ統合する。
選択した site の射 `ρ:X→Y`、環・標準 obstruction ideal・selected measurement ideal の比較、
係数比較 `ρ⁻¹Ob_Y→Ob_X` を固定し、被覆上の cochain 比較から障害類を運ぶ写像を与える。
site の同値、環・両 ideal・係数の比較同型、witness・axis の reading の保存の下で、
対応する類の零性の同値を述べる。
第4〜5章との接続では、採用する輸送・基底変換がこの site・係数比較を与える箇所を示す。
付録Bの有限計算では、本文 VIII §11 の Measurement Packet のうち、入力・係数・成立条件・
出力が表す数学的対象を記載する。これらは各計算の仕様としてまとめる。

## 第4章 輸送と合成の整合性

### 4.1 輸送の存在・普遍性・障害

| 項目 | 種類・数学内容 | 入力・成立条件と結論 | 主な一次資料 |
| --- | --- | --- | --- |
| 4-A exact core 輸送 | 構成・普遍性。`transportAlong σ P` と strongly opcartesian lift、一意な factor、同型を除く lift 一意性 | 固定 Atom carrier、exact doctrine 射、package のみから family・configuration・equation・detector 等を運ぶ。任意の tail とその合成上の射を量化する | [Transport][core-transport]、[Opcartesian][core-opcartesian]、[LiftUniqueness][core-unique] |
| 4-B refinement の失敗 | 反例・条件付き供給。抽出の前進保存だけでは exact core lift が存在しない | Atom map が全単射でも extraction 反映が失われる例。有限な拡張 family・operation・equation の追加供給から得るのは positive core 射であり、exact lift とは区別する | [RefinementObstruction][core-refinement-no]、[RefinementSupply][core-refinement-supply]、[G-101][g101] |
| 4-C 幾何の輸送 | 構成・普遍性。canonical core lift 上の geometry lift、全成分の輸送、一意性 | `E_geom→E_core` の選択された底射に沿う partial op-cleavage。一般 core 射については局所 realization の三比較族と read-preservation を表す `H_geom` が必要 | [幾何の Opcartesian][geom-opcartesian]、[Factorization][geom-factorization]、[LiftUniqueness][geom-unique]、[Supply][geom-supply]、[G-108][g108] |
| 4-D 合成と射影 | 定理。fiber 間 transport functor、compositor / unitor、単位・三重合成の整合、塔の pseudonatural compatibility | 底を pointed `ExtractionInstance` に揃え、対象と vertical 射の両方で証明する | [CorePseudofunctor][core-pseudo]、[Pseudofunctor][geom-pseudo]、[TowerCompatibility][tower-coherence] |
| 4-E authored 比較の障害 | 構成・同値。raw 2-cell defect、辺 reselection の作用、障害消滅と coherent な再選択の存在 | 有限 presentation と許容比較を固定。raw defect は無条件に定義し、3-cell の cocycle 則には syzygy compatibility を使う | [PastingObstruction][transport-pasting]、[VanishingCoherence][transport-vanishing]、[UnifiedObstruction][transport-unified] |
| 4-F 段横断の障害 | 構成・条件付き分解。core への射影、kernel、辺水準 section、全体障害と段内・段間障害の関係 | 因子順を保つ。各段の消滅と joint な coherentization を区別し、alignment の失敗を扱う | [SectionDecomposition][section-decomposition]、[GlobalVanishing][global-vanishing]、[FiniteWitnesses][cross-witness] |

raw defect の比較式を `δ=uφ⁻¹` とすると、辺から生成した中間比較 `m` に対して
`uφ⁻¹=(um⁻¹)(mφ⁻¹)` となる。段内項が kernel に入ることは、alignment と射影の
等式から導く。非可換な積を単純な可換和や、係数未指定の ordinary `H²` と同一視しない。

小例は、単一 disk の defect を辺で吸収する正例と、閉じた二面配置・三者貼り合わせで
許容 orbit 内の食い違いが残る例を候補とする。前者と後者が同じ再選択作用を使うことを示す。

### 4.2 CS の操作保存と比較図式

型・役割・操作名を Atom 側、状態 carrier と実行値を Source・対象・局所実現側に置き、
第1章の独立な意味論と保存則を AAT の射へ対応させる。非単射な状態写像や補完 table も
一般の意味保存射として保持する。

lens の同時保存は、get・put の二つの可換図式を余積を用いて一つにまとめ、射
`c_L:C⊔(C×V)→V⊔C` と、連動する端点変更 `h⊔(h×u)`、`u⊔h` の可換図式で表す。
同じ状態 carrier が現れる箇所に同じ `h` を作用させる条件を、許容変更の部分群として保持する。
プロトコルでは名前付き操作の可換図式と adapter の `bq=q'a` を保持し、合成の保存を示す。
一次資料は [lens の相対操作図式][lens-squares]、[protocol の adapter 図式][protocol-squares]。

**接続項目。** 上記の操作図式、底を固定する資格、完全幾何の保存則は別々に照合する。
完全幾何へ進むには context・coverage・overlap・係数・raw restriction・Support・Axis・Observable を
具体的に構成する。充満忠実関手に沿う[比較群輸送][cs-comparison]は、その関手と許容射を
構成した範囲で使う。四族を同じ実現・局所モデルへ結ぶ要求は §8.4 にまとめる。

## 第5章 基底変換と生成比較

### 5.1 二経路を構成する数学

| 項目 | 種類・数学内容 | 入力・成立条件と結論 | 主な一次資料 |
| --- | --- | --- | --- |
| 5-A doctrine fiber product | 構成・普遍性。exact cospan から compatible source pair の doctrine を生成 | 全 cone を量化し、Atom 成分を恒等に制限しない。pointed 版は選択した compatible point を用いる | [DoctrinePullback][doctrine-pullback]、[PointedDoctrinePullback][pointed-pullback] |
| 5-B cartesian reindexing | 構成・普遍性。任意の exact semantic 底射と target package への strong cartesian lift、cleavage と合成整合 | finite code の存在とは独立の semantic-global な構成。G-110 の表示付き入力への制限と G-112 の全域の結論を対応させる | [CartesianTarget][cartesian-target]、[ExactBottomGlobalLift][global-lift]、[同 coherence][global-lift-coherence] |
| 5-C exact-bottom の有限 code coverage | 分類。端点同型を含む arrow 圏の coverage | 両 Source の有限性と、target の全抽出述語の有限／余有限性による成立域。固定 code 間の Hom の充満性とは別問題 | [ExactBottomCoverageClassification][coverage-classification]、[G-112][g112]；第8章へ |
| 5-D canonical Beck–Chevalley mate | 構成・同型。pointed exact pullback square の push / pull 二経路と canonical mate | 普遍性から生成する mate、authored 比較との一致、後の projector を含む比較を区別する | [CoreBeckChevalleyMate][bc-mate]、[PackageProjectionBeckChevalleyExactness][bc-exact]、[G-110][g110] |
| 5-E indexed assembly | 構成・条件分類。底の頂点・辺・関係から action、輸送データ、reselection、coherence / vanishing 保存を生成 | coherent base diagram 上の結論。任意の raw square family が自動的に組み上がるわけではない。全 right legs についての一様な関係反映は index の epi 性と同値 | [IndexedBaseDiagram][indexed-diagram]、[IndexedDiagnosticAssembly][indexed-assembly]、[IndexedRawFamilyClassification][indexed-raw-classification]、[G-111][g111] |
| 5-F 診断輸送の同値 | 定理。push / reindex 同値、endpoint・cochain・reselection の両逆、coherence・消滅・orbit membership の反映 | 指定した indexed diagram と生成 interpretation 上で、係数を固定する。底射の同型性を仮定せず、輸送同値から底射の同型性も従わない | [TransportEquivalence][diagnostic-equivalence]、[OrbitExactness][diagnostic-orbit]、[BaseIsoIndependence][base-iso] |
| 5-G refinement base change | 構成・必要十分条件。forward pullback と、package が実現する台での逆輸送 | `Nonempty(RefinementCartesianCleavage r) ⇔ RealizedLocusExtractionReflecting r`。各 compatible source で組み上げる条件と、実現台の移送を証明する | [RefinementBaseChange/Classification][refinement-classification]、[RealizedSupport][refinement-realized]、[Qualification][refinement-qualification]、[G-114][g114] |
| 5-H geometry-refinement 比較 | 構成・条件付き同値。lower が lax refinement の完全幾何の射、二つの reverse route、upper mate、solution と orbit の輸送 | 任意 authored 入力では一方向比較。明示的 transport から生成する compatible locus で双方向の比較と comparator descent を扱う | [G-115][g115]、[UpperGeometryCompatibleMateNaturality][upper-mate]、[G-118][g118] |

### 5.2 比較の種類と後続への接続

この章では、二経路 `D,V`、canonical な可逆比較 `α:D≅V`、診断が選ぶ成分を含む
生成比較 `β` を別の記号で追う。authored comparator と canonical mate の不一致は、
それだけでは `α` の非可逆性を意味しない。第6章では `β=Eα` の `E` を構成し、
`β` の可逆性を判定する。

refinement の小例は、target package が実在する forward-only と reverse-transport の対を使う。
空の target fiber では全対象への lift 要求が空虚に成立し得るため、
[G-114 の三種の witness][g114]から active な二例と inactive な対照の役割を明記する。

**接続項目。** 第4章の opcartesian 輸送、第5章の cartesian reindexing、
finite code coverage、診断同値にはそれぞれ固有の量化域がある。
一つの「base change 定理」に統合する場合も、適用する square・射影・係数・入力表示を
消さず、生成経路と可換図式を共通化する。完全幾何での実比較の一致は第6章の結果へ接続する。

## 第6章 冪等正規化と実現

### 6.1 正規化・像・比較の配置

| 項目 | 種類・数学内容 | 入力・成立条件と結論 | 主な一次資料 |
| --- | --- | --- | --- |
| 6-A configuration descent | 構成・普遍性。`π(x)=x.configuration`、`s_P`、`n_P=s_Pπ`、固定点と configuration の同値 | `πs_P=1`。任意の値型への写像について `fn_P=f` と configuration を通る一意因子化が同値 | [ConfigurationDescent][configuration-descent]、[G-116][g116] |
| 6-B total 射の冪等性 | 定理。admissibility の下で package 射 `N_P²=N_P`、cell projector `E²=E` | residual / coordinate と operation の保存を含む。object 写像の冪等性から total 射の等号を省略しない | [BCAuthoredCanonicalObjectNormalization][core-normalization]、[IdempotentExchangeNormalization][idempotent-normalization]、[IdempotentExchangeCellProjector][cell-projector] |
| 6-C 生成比較の像 | 定理・反例。`β=Eα`、`IsIso β ⇔ E=1`、Karoubi 内の明示的同型、元の total 圏内での split 不可能性 | arbitrary configuration 上の相異なる object を使う。選択 residual / coordinate が保存されても raw 比較は非同型となり得る | [Karoubi image][karoubi-image]、[RawFailureLocus][raw-failure]、[InternalNormalizationSplitNoGo][split-no-go] |
| 6-D 比較と冪等完備化 | 一般定理。`Kar(Arr(E))≃Arr(Kar(E))`、関手に対する自然性、三段の投影との整合 | arbitrary 圏の結果を、実際の AAT 比較とその冪等対へ適用する。最大亜群にも非可逆な比較を対象として残す | [KaroubiArrowEquivalence][kar-arrow]、[FunctorNaturality][kar-naturality]、[MaximalSubgroupoid][comparison-groupoid]、[G116KaroubiPlacement][kar-placement]、[ThreeStageProjection][three-stage] |
| 6-E 正規化関手と片側自然性 | 構成・定理。admissible な core の充満部分圏から sandwich 射の圏への充満関手 `N(f)=fe_P` | `e_Qfe_P=fe_P` を全成分で証明。Karoubi 内の包含 `i:KN→J` は自然。逆向きの射影の自然性は追加の operation coherence と同値 | [NormalizationCategory][normalization-category]、[CanonicalNormalizationAbsorption][normalization-absorption]、[NormalizationNaturalityFailure][normalization-failure] |
| 6-F 自然性の反例 | 反例。configuration に見えない Bool operation tag によって `fe_P≠e_Qf` | full admissible 圏の実射で成立。G-117 の全域 modification 要求の反証を、object-map naturality や 6-E の否定と混同しない | [ModificationCounterexample][normalization-counterexample]、[G-117 report][r117] |
| 6-G 完全幾何の正規化 | 構成・定理。`n_G²=n_G`、底・係数への像は恒等、`N_geom` の充満性、core 正規化との可換性 | admissible core を持つ geometry の全射について片側吸収を示す。Support・Axis・Observable、coverage、overlap、raw の各成分を保持する | [CanonicalNormalization][geom-normalization]、[G-122 A][g122] |
| 6-H 完全幾何での実比較 | 定理・非可逆例。実生成 `barAlpha` の core mate への射影、`barBeta=bar d barAlpha`、Karoubi 同型と可逆性分類 | 同じ square・cell・cochain・係数・source geometry から両経路を生成する。G-116 と G-118 の接続を endpoint triangle で証明する | [ExactDerivedBarAlphaTriangle][bar-alpha]、[ExactBarBetaClassification][bar-beta]、[ExactBarBetaFiniteWitness][bar-beta-witness] |

### 6.2 一本の比較について保つ式

等号判定を備えた Atom carrier、authored BC square、その cell `z`、cochain `ω`、
可換係数環 `k` と support core 上の geometry / raw data を固定する。
`χ_z := (ω(z)≠1) ∧ CanonicalObjectNormalizationAdmissible(P_z)` とする。
完全幾何の実生成経路では

\[
 \bar\beta_z=\bar d_z\bar\alpha_z,\qquad
 \bar e_z=\bar\alpha_z^{-1}\bar d_z\bar\alpha_z,\qquad
 \bar\beta_z:(G_z,\bar e_z)\xrightarrow{\sim}(H_z,\bar d_z)
 \quad\text{in }\operatorname{Kar}(E_{\rm geom}),
\]

\[
 \operatorname{IsIso}_{E_{\rm geom}}(\bar\beta_z)
 \iff\bar d_z=1\iff\neg\chi_z
\]

となる。`χ_z` が成立する場合、両端の冪等射は canonical 正規化となる。
固定 finite axis-fold、生成 cochain、cell `second`、係数 `ℤ` の例で非可逆性を実現する。

**接続項目。** object 上の固定点、total 圏での非分裂、Karoubi 内の分裂像、
sandwich 射の圏を別の対象として説明する。G-117 の未証明な lax selector / modification の
全体を結果表へ転記せず、成立した admissibility 保存・個別の伝播則と自然性の反例だけを
[report][r117]と実宣言に対応させる。後続へ渡すのは 6-E・6-G の実際の関手である。

## 第7章 比較を保つ変更と情報

[Period Separation の有限例][period-separation]を導入に置く。
同じ graph reading を持つ二つの対象でも semantic / effect reading が異なることを示し、
何を忘れる観測なのかを説明して 7-C の観測の核へ進む。
ここでの period は broad reading であり、第2章の homology–cohomology pairing と区別する。

### 7.1 一般分類と AAT の実生成比較

| 項目 | 種類・数学内容 | 入力・成立条件と結論 | 主な一次資料 |
| --- | --- | --- | --- |
| 7-A 比較保存群 | 構成・分類。`Γ_c={(u,v) ∣ vc=cu}`、両射影の像・核・非空 fiber の torsor | 任意の完全幾何比較と底を固定する端点群。`c` が同型なら共役のグラフになり、両射影は同型 | [QualifiedComparisonStabilizer][qualified-stabilizer]、[G-118 A][g118] |
| 7-B 生成変更と入力表示変更 | 定理。source の変更の二経路像の適合条件、残余核、表示を変えて再生成した比較との自然性 | 完成した出力比較の共役だけで済ませず、source geometry・edge・comparator・transport を入力表示から再構成する | [QualifiedComparisonGeneratedClassification][qualified-generated]、[source 表示の自然性][source-naturality]、[G-118 B–C][g118] |
| 7-C 観測での判定 | 必要十分条件。`O:Q→R` と `Γ≤Q` に対し、所属判定が O を通ることと `ker O≤Γ` の同値 | O の全射性は不要。`O⁻¹(OΓ)=Γ ker O`、観測 fiber 内の適合部分、基点付き剰余類を構成する | [ObservationKernel][observation-kernel]、[G-120 A][g120] |
| 7-D 係数観測への適用 | 分類・反例。生成された可逆比較の観測 kernel と、同じ係数観測を持つ適合・不適合対 | `K/L` は剰余類集合として扱う。正規性を仮定して商群へ置き換えない。source 表示変更との整合を保つ | [EndpointKernelClassification][endpoint-kernel]、[FixedWitness][information-witness]、[G-120 B][g120] |
| 7-E 冪等像への制限 | 一般定理。中心化群から像の端点群への制限、比較保存、反映条件、lift と kernel torsor | 比較保存群への制限の核と ambient な核を区別する。lift の存在は適合する像への所属で判定する | [KaroubiRestriction][kar-restriction]、[GroupHomRestriction][group-restriction]、[KaroubiRestrictionFiniteWitness][kar-restriction-witness] |
| 7-F AAT 正規化の分類 | 構成・定理。G-122 の実比較の制限準同型に群準同型の section、分裂短完全列、各 lift fiber の torsor | 選択子の二場合と canonical 正規化を分ける。全端点群と底を固定する群の双方で、section が底・係数成分を保持する | [ExactBarBetaComparisonSection][beta-section]、[ExactBarBetaComparisonExactness][beta-exactness]、[底固定版][beta-bottom] |
| 7-G 反映が失われる機構 | 構成・反例。非恒等な ambient kernel 元 `τ` から `(τ,1)` を作り、像では適合、元では不適合 | 同じ生成比較と実際の完全幾何自己同型を用いる。section の存在と反映の失敗は同時に成立する | [AmbientKernelComparisonWitness][ambient-witness]、[G-122 D][g122] |
| 7-H 比較対象の自己同型群 | 群同型。恒等冪等で埋め込んだ比較対象の、底を固定する自己同型群と `Γ_c` の同定。G-118 の実生成 mate への特殊化 | 任意の完全幾何比較 `c` を `Arr(Kar(E_geom))` の最大亜群の対象として扱う。同定は両端射影と可換。底を固定する条件は端点変更に課し、比較 `c` 自身の底への像は恒等に制限しない | [QualifiedComparisonGroup][comparison-object-group]、[GeneratedQualifiedComparison][generated-comparison-object-group]、[G-119 B][g119] |
| 7-I core 正規化による比較群の移送 | 構成・保存定理。raw 比較保存部分群から正規化後の比較保存部分群への準同型と、底を固定する両部分群への制限 | `C` を admissible core の充満部分圏とし、任意の比較 `c:P→Q` に第6章の正規化関手 `N` を適用する。包含 `V:C→E_core` と底への射影に対する `π_N N=πV` から底資格の保存を導く | [NormalizationComparisonGroup][normalization-comparison-group]、[NormalizationProjection][normalization-projection]、[G-119 D][g119] |

7-H は 6-D の比較の圏から 7-A の比較保存群を取り出す同定であり、
7-I は 6-E の正規化関手から比較保存群への準同型を構成する結果である。
後者が与えるのは比較と底資格の保存である。比較の反映や適合する lift の存在には、
7-E 以降の条件と個別の分類を用いる。

観測による情報損失では `K=ker O`、`L=K∩Γ` と置く。任意の適合する `γ∈Γ` に対し、
その観測 fiber は `γK`、適合する部分は `γL` となる。基点付き剰余類集合 `K/L` が一点であることと、
比較への適合性を観測だけで判定できることが同値である。

反映の一般判定は、端点群上の `r:H→R`、raw 比較群 `Γ₀≤H`、像の比較群 `Δ≤R` について、
比較の保存 `r(Γ₀)⊆Δ` の下で

\[
 r^{-1}(\Delta)=\Gamma_0
 \iff \bigl(\ker r\le\Gamma_0\ \land\ r(\Gamma_0)=\Delta\cap\operatorname{im}r\bigr)
\]

とする。適合する lift の fiber に作用するのは `ker(r|Γ₀)` である。
G-122 の実生成比較では次の分類を同じ入力の上で得る。

| 正規化の選択 | 比較の保存 | 比較の反映 | 適合する lift |
| --- | --- | --- | --- |
| 選択子が不成立 | 成立 | 成立 | 群準同型の section を持つ |
| 選択子が成立 | 成立 | 不成立 | 群準同型の section を持つ |
| admissible な入力の canonical 正規化 | 成立 | 不成立 | 群準同型の section を持つ |

canonical 正規化の行の一次資料は [section の構成][alpha-canonical-section]と
[短完全列・lift fiber の分類][alpha-canonical-exactness]である。

証明済みの一般有限集合の反例から、定値冪等射での反映失敗と、サイズの違う fiber を交換できないための
lift 非存在を収録候補とする。AAT の生成比較に section があることは、これらの一般反例と両立する。

### 7.2 モデル同期とプロトコルで共有する変更分類

共通定理の入力は、有向多重グラフ `Q=(V,E,s,t)`、隠れ状態の集合 `K`、
許容する可視変更群 `H≤Aut(Q)` とする。状態は `V×K`、観測は `(v,k)↦v`、
各名前付き辺 `e:v→w` の操作は `(v,k)↦(w,k)` と定める。

`u∈H` 上の観測保存変更は、頂点ごとの置換を用いて `h(v,k)=(u_V(v),φ_v(k))` と一意に書ける。
操作保存は各辺での `φ_{s(e)}=φ_{t(e)}` と同値になり、向きを忘れた連結成分 `π₀(Q)`
ごとの置換族へ降下する。操作も保つ組 `(u,h)` の群を `A_Q` とすると、

\[
 1\longrightarrow\prod_{j\in\pi_0(Q)}\operatorname{Sym}(K)
 \longrightarrow A_Q\longrightarrow H\longrightarrow1
\]

は、隠れ状態を変えない変更を section として分裂する。
各 `u` 上の変更の集合は核の torsor であり、`V,K` が有限なら個数は
`(|K|!)^{|π₀(Q)|}` になる。`H` の連結成分への作用を合成に含め、半直積として記述する。

積 lens はすべての view 間の put を辺とする連結な入力であり、核は `Sym(K)` となる。
プロトコルには、各制御点の状態を同じ `K`、各生成辺の状態作用を恒等とする
セッションモデルを代入し、連結成分ごとに独立な補完の変更を得る。
この共通分類の適用範囲は、ここに定めた辺の作用を持つ入力とする。

基準補完 `k₀` を保つ版では `Sym(K)` を `k₀` の固定部分群に置き換える。
lens 側では、`g(s(v))=v`、`p(s(v),w)=s(w)` を満たす選択 section `s:V→C` の保存に対応する。
`V=Bool`、`K={0,1,2}`、`k₀=0` の有限例では、get と選択値を保つ変更 4 個のうち
put も保つものは 2 個になる。ここでも可視変更は恒等に固定する。
プロトコルの有限例は、頂点 `{0,1,2,3}`、辺 `0→1` と `2→3`、`K=Bool` とする。
可視変更を恒等に固定すると、観測保存変更 16 個のうち操作も保つものは 4 個であり、
二つの辺を交換する可視変更の上でも追随変更は 4 個となる。

一次資料: [連結成分による分類][fixed-components]、[分裂と torsor][fixed-split]、
[fiber の個数][fixed-cardinality]、[有限例][fixed-examples]。
lens・protocol の一般射を定義した圏から、ここで用いる可逆変更族と
許容可視群を取り出す箇所を明示する。例の個数計算は、この一般定理の短い評価として使う。

**接続項目。** CS の操作保存部分群、AAT の底固定部分群、正規化の中心化群はそれぞれ
別の条件である。対応する関手・端点評価と部分群への制限を揃えてから、7-A〜7-G の
どの群・section・核・fiber を CS 側へ運んだかを記載する。

## 第8章 表示・局所再構成・有限決定性

[本文 VII §15 の Representation Completeness][math-vii]を、章を横断する説明として導入に置く。
第3章の診断保存、第7章の比較適合性の反映・観測による検出、
この章の射を区別する忠実性・局所データからの再構成を、何を保証する性質かによって比較する。
対象・射・係数・観測族を各結果に合わせて指定し、これらを一列の強弱関係として扱わない。

### 8.1 有限表示から回復する対象と射

| 項目 | 種類・数学内容 | 入力・成立条件と結論 | 主な一次資料 |
| --- | --- | --- | --- |
| 8-A 有限例外 code の意味 | 定理。離散 D の一点コンパクト化 `D⁺` について `Code(D)≃C(D⁺,Bool)` | code は既定値と有限例外集合。D が無限なら D 上の評価は単射。D が有限なら同じ評価に二つの既定値 code がある | [OnePointCode][one-point-code]、[EvaluationClassification][code-evaluation]、[CodeFibers][code-fibers] |
| 8-B 底射 coverage の位相的特徴 | 必要十分条件。両 Source の有限性と、target 抽出述語の連続延長が anchored coverage を特徴づける | 離散 Source の compactness と有限性を接続。端点の意味同型を選べる coverage と、固定端点間の表示を区別する | [CoverageTopology][coverage-topology]、[DiscreteCompactness][discrete-compactness]、[G-121 B][g121] |
| 8-C 固定 code 間の Hom | 必要十分条件・正規化。Atom 置換の有限 support と既定値の保存、decoder の忠実性、有限 carrier での正規化後の充満忠実性 | `R_fin` は既定値 false に揃え、decode 後の自然同型を与える。raw code の等号とは区別する | [FixedArrowClassification][fixed-arrow]、[FiniteFullSubcategory][finite-full]、[FiniteCodeNormalization][code-normalization]、[FiniteNormalizationRealizationIso][normalization-realization-iso] |
| 8-D 有限構文の限界 | 反例・不可能性。意味が同型でも元 code 間に射がない例、無限 support 置換、可算 decoder の非全射性 | 固定自己同型群に `P(ℕ)` を埋める。可算構文に対する主張であり、任意の無限パラメータ参照を許す構文全般の不可能性ではない | [FinOneCounterexample][fin-one]、[NatAdjacentSwap][nat-swap]、[NatSubsetSwaps][nat-subset-swaps]、[CountableSyntaxObstruction][countable-syntax] |
| 8-E CS の有限再構成 | 構成・圏同値。lens の有限基準 fiber、protocol の有限生成 table から対象・一般射を回復 | operation・Law・観測を保つ一般射を扱う。Karoubi、retract、Arr への拡張を同じ制限・延長と整合させる | [CSKaroubiReconstruction][cs-karoubi]、[LensFiberModelEquivalence][lens-model]、[ProtocolObservedRestrictionEquivalence][protocol-model] |
| 8-F 一般局所再構成原理 | 条件付き一般定理。Hom 分離、Hom 組立て、対象組立てから reading functor の圏同値を構成 | 三条件を独立に述べる。対象は読み取りが局所モデルと同型になる実現を構成し、射は制限・組立ての両逆を示す | [LocalReconstructionEquivalence][local-equivalence] |
| 8-G タグ族の局所回復 | 構成・分類。source-choice 群、全有限 Bool table の整合族、正規化による情報損失、正規化を含む生成部分圏 | 全 source-choice 族と一様 flip を保持する。正規化後の単一像から全 source-choice を分離できるとはしない | [TagChangeFiniteReadingRecovery][tag-recovery]、[TagChangeNormalizedChoiceKernel][tag-kernel]、[TagChangeExactGeometryLocalModel][tag-model] |
| 8-H 完全幾何の成分読み取り | 構成・分離。原始 Bool graph、全計算成分を読む graph functor、同値・環準同型・依存する同値族の組立て | 全 Hom の分離と成分ごとの組立てを確認。任意の整合 bundle からの完全 Hom 組立ては §8.4 の接続項目 | [CompleteGeometryFunctionGraphSeparation][graph-separation]、[CompleteGeometryGraphCategory][graph-category]、[DependentAlgebraicGraphCoherence][dependent-graph] |
| 8-I G-122 比較の回復 | 構成・部分的接続。raw 比較の normalized 座標と full restriction-kernel 座標への分解、complete graph による分離 | 受理済み座標の両逆と、任意の独立な局所構文からその座標を組み立てる要求を分ける | [G122FullComparisonKernelDecomposition][full-kernel]、[G122CompleteGraphKernelReconstruction][graph-kernel]、[G-124 report][r124] |

有限 decoder `D₀` の固定 code `P,Q` 間で、`b_P(s)` を source normalization 後の
抽出 code の既定値、`s_f` を source map、`σ_f` を Atom 置換とすると、射の分類は

\[
 \exists h:P\to Q,\quad D_0(h)=f
 \iff \operatorname{Finite}(\operatorname{supp}\sigma_f)
 \ \land\ \forall s,\ b_Q(s_f(s))=b_P(s)
\]

とする。無限 Atom carrier では既定値条件が意味の exactness から従う。
有限 carrier ではこの条件を落とすと、同じ意味を持つ code 間の非充満性が現れる。
これは「対象を表示できる」「端点同型込みで射を覆える」「固定表示の間の任意の射を表示できる」
という三つの問いを分ける例として使う。

### 8.2 局所再構成で必要な三つの証明

`N:R→M` に対して、(i) 各 Hom の読み取りが単射、(ii) 独立な整合条件を満たす任意の
局所 Hom を組み立てられる、(iii) 任意の局所対象を同型まで実現できる、を示す。
(i)(ii) は充満忠実性、(iii) は本質的全射性を与え、圏同値へ接続する。

CS の二族では、lens の fiber 上の任意の写像、protocol の観測と生成辺を保つ頂点写像が
この構成の具体的な入力になる。有限表示との一致は
[lens の Karoubi 整合][lens-karoubi]と [protocol の Karoubi 整合][protocol-karoubi]で追う。
比較保存群は[充満忠実関手による輸送][cs-comparison]を通して回復する。

対象が同じであるだけ、射が分離されるだけ、完成した全域射の像を局所モデルと定義するだけでは、
(ii)(iii) の証明にならない。この区別を、完全幾何への適用にも同じまま用いる。

### 8.3 有限決定性と CS への帰結

有限読み取りには次の三性質を別々に定める。

| 性質 | 意味と、CS の帰結として示すこと |
| --- | --- |
| 区別 | 読み取りが対象とする射・変更の集合上で単射であり、同じ有限データから異なる射を取り違えない |
| 延長 | 有限片の独立な整合条件を満たす任意のデータから、全域の射・変更を構成できる |
| 実効性 | 列挙可能な有限入力と必要な等号判定を指定し、整合判定と延長を計算できる |

一般射の層では、lens は基準 fiber の任意の table が意味保存射へ延長する。
プロトコルは、全頂点・状態の table における型、生成辺、観測の整合条件から延長する。
どちらも制限・延長の両逆を示す。実効性には状態・生成辺の列挙と必要な等号判定を
入力として指定し、有限性の存在命題から計算手続きを得たことにはしない。

§7.2 の可逆変更族では、可視変更 `u` を固定し、有限頂点集合 `S⊆V` で隠れた置換を読む。
`|K|≥2` のもとで、次の同じ判定を両方の CS 問題へ適用する。

- 区別の必要十分条件は、`S` が全連結成分と交わることである。
- 延長の必要十分条件は、同じ連結成分にある `S` の任意の二頂点が、`S` 上の誘導グラフでも
  結ばれることである。局所整合条件は、両端が `S` にある辺での置換の一致とする。
- 区別と延長を満たす有限決定集合が存在する必要十分条件は、`π₀(Q)` の有限性である。
  各成分から一頂点を選べば決定集合となる。

この判定で数えるのは読み取る頂点であり、一つの読み取りの値は `K` 上の置換全体である。
有限量の table による決定には、さらに `K` の有限性を明示する。
lens では基準 fiber 上の置換 table、上記セッションモデルでは各成分の代表頂点における
置換 table が変更を決める。有限の頂点・辺・隠れ状態を明示的に列挙した入力では、
整合判定と延長の計算も示す。一般のプロトコル射には、前段の頂点・生成辺 table による
再構成を適用する。

同一定義で扱うタグ変更族では、二元巡回群 `C₂` を用いて、全有限制限の整合族との群同型

\[
 C_2^{\Omega}\cong\varprojlim_{S\subseteq_{\mathrm{fin}}\Omega}C_2^S
\]

を与える。
`Ω` が無限なら、どの有限集合の外でも変更を残せるため有限読み取りによる区別は成立しない。
全有限片からの再構成と有限決定性の違いを、lens・プロトコルの成立条件と並べて説明する。

一次資料: [一般 lens 射][lens-finite]、[一般 protocol 射][protocol-finite]、
[lens の可逆変更][lens-invertible]、[protocol の可逆変更][protocol-invertible]、
[有限決定集合と成分][finite-components]、[タグの全有限読み取りの群同型][tag-group-reconstruction]。

### 8.4 固定版で個別結果と共通再構成を分ける箇所

| 入力族・接続 | 照合できる結果 | 一つの共通主定理へ残る接続 |
| --- | --- | --- |
| lens / protocol | 一般 Hom の制限・延長、各枝の対象組立てと圏同値、有限 table、Karoubi / retract / Arr 整合 | 同じ `Σ,D,Λ` の原始読み取りと、枝ごとの同値の一致 |
| タグ付き operation | source-choice の全有限制限、actual 射への忠実な実現、正規化を含む生成部分圏の局所同値 | represented image の外を含む、共通の保存条件で定めた全 Hom・全局所対象の組立て |
| G-122 固定生成比較 | 三比較の primitive probe、full 比較群の kernel 座標分解、complete graph による全 raw 比較の分離 | full kernel の任意の元の独立な局所表示、完全幾何の整合条件からの joint assembly |
| 完全幾何一般 | raw graph 圏、reading の忠実性、代数的な graph 条件と一部の依存成分の両逆 | context 関手の射作用、operation・invariant・Support・Axis・Observable・raw naturality 等を含む整合条件と完全 Hom の組立て |
| 四族の共通入力 | 必須の各入力・既存結果と一般再構成原理を特定できる | decoder 非依存の一つのデータ条件、共通局所モデル、投影・正規化・全比較群の回復を同じ同値へ接続する証明 |

根拠は [G-123 report][r123]、[G-124 の固定要求][g124]と [report の未完了 ledger][r124]。
個別に構成された圏同値・分離・分類を収録し、四族を貫く主同値や全比較群の局所組立ては、
この表の接続を満たす証拠と対応させる。個別の成果から G-123・G-124 の全要求の成立は推論しない。

## 全10部・付録の収録先と補足候補

構成マスターの八章に対し、数学本文の部番号は一対一に対応しない。
第V〜IX部にも独立の内容があり、後半の研究成果だけで基礎論文を置き換えない。
次は本論に必要な定義と、補足・発展へ回す内容の配置案である。

| 素材 | 八章への配置・残す数学 | 追加構造・扱い |
| --- | --- | --- |
| [本文 I][math-i] | 第1章の公理・生成・operation・Law、第6章の configuration descent | 有限 detector の検出条件と operation 自体の同一性を保持 |
| [本文 II][math-ii] | 第1章の context / site、第2章の sheaf / descent、第4章の幾何輸送 | overlap と生成 topology の依存を統一 |
| [本文 III][math-iii] | 第2章の代数・ideal・scheme・lawful locus。square-free witness と Stanley–Reisner 表示は本文 VIII §5 の Alexander dual と一体で付録Bに置く | closed / open / constructible Law の型を分ける。Architecture Nullstellensatz の候補を一般確定定理にしない |
| [本文 IV][math-iv] | 第2章の mismatch / boundary residue / forest / Stokes、Topological Debt Capacity・Betti 数・Euler Accounting、第3章の診断比較 | Scale-Stable Debt（§14）は第3章に関連する展望に置く。higher overlap、Mayer–Vietoris・Leray の候補は、採用する条件と形式化済み特殊形を別途対応づける |
| [本文 V][math-v] | 第2章の補足に derived tensor product、`Tor_i(O/I_U,O/I_V)` による Law conflict、共有因子の repair 反例を置く。Transferred Obstruction（§10）・Derived Repair Criterion（§11）・本文 VIII §10 の support と pairing の基本条件は一つの修復の補足にまとめる | 同一 ambient、selected conflict class、repair direction、transfer pairing と修復の比較条件を指定する。Tor の非零性と特定 repair の非零転送を分け、修復条件の定義を一般の修復存在定理と区別する。Hilbert 計算・well-founded repair は補足候補 |
| [本文 VI][math-vi] | 第2章の補足に Architecture Stratum、smoothness、Architecture Singularity、Singularity Criterion、God Object の再解釈（§§2・4–5、定理6.1、§7）を配置。第1・4章の operation / groupoid 語彙も補う | 特異性の補足では Law、deformation test、必要な tangent / cotangent complex を固定し、指定障害類の非零性に相対化した結論を保つ。複体の一般構成、square-zero lifting、monodromy、stack / gerbe は発展候補とし、各構成の入力・成立条件を個別に示す |
| [本文 VII][math-vii] | 第3・7章の表現の保存・反映と情報損失。Period Separation（§6）は第7章冒頭の小例、Representation Completeness as a Spectrum（§15）は第8章導入で第3・7章とつなぐ説明にする。period pairing は第2章の補足 | strict な homology–cohomology pairing と broad reading を区別。metric / cost は追加 enrichment、repair margin / filling cost は補足候補 |
| [本文 VIII][math-viii] | Class Transport（§7）は第3章の係数比較へ統合し、第4〜5章とは実比較を与える箇所で接続。第8章の実効性、付録Bの有限計算・Alexander dual（§5）・Measurement Packet（§11）の入力・係数・仮定・出力の意味を収録 | 有限な site と係数アルゴリズムを指定し、selected measurement ideal と標準 obstruction ideal を分ける。Support-Localized Transfer Measurement（§10）の基本条件は本文 V の補足へ、norm・support weight・Wasserstein 型の拡張は展望へ置く。Hodge / Tor base change の条件を保持し、stability の候補は候補として記す |
| [本文 IX][math-ix] | 第4章の操作合成への補足、結びの時間方向への展開 | measurement profile に従属する trace / product site / temporal coefficient。temporal descent、散逸、Lyapunov / force の条件付き reading を一般輸送定理へ同一視しない |
| [本文 X][math-x] | 第2章の SAGA 比較を主要結果として収録 | semantic repair と equation geometry の独立生成、class 対応、true sheaf による actual repair |
| [付録 A–B][math-app] | 第1章の相対パラメータ、第2章の通常の scheme との関係、補足の有限計算 | 付録Bで square-free ideal と Alexander dual の minimal hitting set を一つの有限例として扱い、実際の修復操作には別途意味論を与える。monomial Tor・period・circle nerve 上の独立表示は、必要な局所例を選ぶ |

補足の Lean 照合先は [Derived][formal-derived]、[SingularityMonodromyStack][formal-singularity]、
[RepresentationAnalysis][formal-representation]、[Measurement][formal-measurement]、[Evolution][formal-evolution]。
各入口には抽象的な interface と、その条件を満たす具体例が混在するため、本文に採用する命題では
実際の仮定を個別に展開する。集約 module の存在を、数学本文の全候補命題の証明と読まない。

## 章をまたぐ数学の接続項目

| 接続 | 論文で明示する内容 | 根拠・残る仕事 |
| --- | --- | --- |
| 第1→2章 | 同じ equation system から symbolic ideal、residual、係数、実 section 評価を生成する | 2-D・2-E・2-H の写像と成立条件を一つの図式へ整理 |
| 第2→3章 | 選択した障害係数と law-value 診断係数の関係 | 対応がある範囲で比較を構成。一般の自動同定は置かない |
| 第3→8章 | ambient な存在と、指定した表示体系内での実現可能性を分ける | `q_L` の admissible 表示、底の code coverage、固定 Hom、局所組立てという別々の普遍性を説明 |
| 第4→5→6章 | 輸送の普遍性から二経路・実比較・正規化因子へ進む | `α`、authored comparator、`β`、`barAlpha`、`barBeta` の端点と生成元を揃える |
| 第6→7→8章 | 正規化関手、比較保存群、局所モデルでの回復を結ぶ | 6-D→7-H の群同定、6-E→7-I の比較群準同型と底への射影を接続。局所モデルへの移送では、採用する充満忠実関手ごとに資格部分群、section・核・fiber の対応を確認 |
| 第2章と第8章の「局所」 | site の被覆上の descent と、原始読み取りの整合族による reconstruction の関係 | 添字圏・制限・overlap・係数・assembly の比較を与える場合に限り接続。一般 `H¹` による同一の障害理論は追加の課題 |
| 第1・4・7・8章の CS | 独立な意味論 → 入力構成 → 操作保存 → 共通分類 → 再構成・有限決定 | lens と protocol の各段の対応命題を揃える。操作が hidden state を恒等に運ぶ特殊形の結論を一般 protocol に広げない |

記号では、doctrine の source normalization、object の canonical 正規化、finite code の既定値正規化を
別記号にする。有限性についても、Atom family、Source、cover / presentation、状態 fiber、
一つの局所値、読み取り添字全体を区別する。

既存数学への帰属は、商の普遍性、sheaf / Čech、Beck–Chevalley、Karoubi、群の核と torsor、
lens の三法則と積表示、schema の関手意味論について原典を確認する。
AAT 固有の寄与は、入力からの生成、仮定の導出、実比較との一致、同じ定理を通した帰結の箇所で示す。
本書の一次資料リンクはリポジトリ内の数学的照合先であり、外部文献調査の完了を表さない。

[math-i]: ../../../docs/aat/algebraic_geometric_theory/part_1_atoms_objects_laws.md
[math-ii]: ../../../docs/aat/algebraic_geometric_theory/part_2_architecture_geometry_sites_sheaves.md
[math-iii]: ../../../docs/aat/algebraic_geometric_theory/part_3_law_algebra_obstruction_ideal_lawful_locus.md
[math-iv]: ../../../docs/aat/algebraic_geometric_theory/part_4_obstruction_cohomology.md
[math-v]: ../../../docs/aat/algebraic_geometric_theory/part_5_derived_law_geometry_repair.md
[math-vi]: ../../../docs/aat/algebraic_geometric_theory/part_6_singularity_monodromy_stack.md
[math-vii]: ../../../docs/aat/algebraic_geometric_theory/part_7_representation_periods_analysis.md
[math-viii]: ../../../docs/aat/algebraic_geometric_theory/part_8_measurement_theory.md
[math-ix]: ../../../docs/aat/algebraic_geometric_theory/part_9_evolution_geometry.md
[math-x]: ../../../docs/aat/algebraic_geometric_theory/part_10_semantic_repair_descent_saga.md
[math-app]: ../../../docs/aat/algebraic_geometric_theory/appendix.md
[atom-axioms]: ../../../Formal/AG/Atom/Axioms.lean
[core]: ../../../Formal/AG/Atom/AATCore.lean
[object-algebra]: ../../../Formal/AG/Atom/ObjectAlgebra.lean
[lawfulness]: ../../../Formal/AG/Atom/LawfulnessZero.lean
[coverage]: ../../../Formal/AG/Site/Coverage.lean
[topology]: ../../../Formal/AG/Site/Topology.lean
[reading-core]: ../../../Formal/AG/ReadingFunctoriality/Core.lean
[ambient-algebra]: ../../../Formal/AG/LawAlgebra/AmbientAlgebra.lean
[structure-sheaf]: ../../../Formal/AG/LawAlgebra/StructureSheaf.lean
[witness-ideal]: ../../../Formal/AG/LawAlgebra/WitnessIdeal.lean
[obstruction-ideal]: ../../../Formal/AG/LawAlgebra/ObstructionIdeal.lean
[affine-chart]: ../../../Formal/AG/LawAlgebra/AffineChart.lean
[standard-scheme]: ../../../Formal/AG/LawAlgebra/StandardScheme.lean
[law-correspondence]: ../../../Formal/AG/LawAlgebra/Correspondence.lean
[obstruction-sheaf]: ../../../Formal/AG/Cohomology/ObstructionSheaf.lean
[gluing-mismatch]: ../../../Formal/AG/Cohomology/GluingMismatch.lean
[flatness]: ../../../Formal/AG/Cohomology/FlatnessCriterion.lean
[cover-nerve]: ../../../Formal/AG/Cohomology/CoverNerve.lean
[saga-production]: ../../../Formal/AG/SemanticRepair/Saga/EquationProduction.lean
[saga-kappa]: ../../../Formal/AG/SemanticRepair/Saga/KappaComparison.lean
[saga-descent]: ../../../Formal/AG/SemanticRepair/Saga/TrueSheafDescent.lean
[saga]: ../../../Formal/AG/SemanticRepair/Saga.lean
[formal-derived]: ../../../Formal/AG/Derived.lean
[formal-singularity]: ../../../Formal/AG/SingularityMonodromyStack.lean
[formal-representation]: ../../../Formal/AG/RepresentationAnalysis.lean
[period-separation]: ../../../Formal/AG/RepresentationAnalysis/PeriodSeparation.lean
[formal-measurement]: ../../../Formal/AG/Measurement.lean
[formal-evolution]: ../../../Formal/AG/Evolution.lean
[geometry-basic]: ../../../research/lean/ResearchLean/AG/GeometryTransport/Basic.lean
[atom-categories]: ../../../research/lean/ResearchLean/AG/AtomFoundation/Categories.lean
[geometry-categories]: ../../../research/lean/ResearchLean/AG/GeometryTransport/Categories.lean
[three-stage]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/ThreeStageProjection.lean
[lens-semantics]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/LensSemantics.lean
[lens-connection]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/FixedFLensConnection.lean
[lens-finite]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/LensSemanticFiniteDetermination.lean
[protocol-semantics]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/ProtocolSemantics.lean
[protocol-schema]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/ProtocolSchema.lean
[protocol-presentation]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/ProtocolFinitePresentation.lean
[protocol-connection]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/FixedFProtocolConnection.lean
[protocol-finite]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/ProtocolObservedFiniteDetermination.lean
[two-phase-h1]: ../../../research/lean/ResearchLean/AG/TwoPhase/CohomologyComparison.lean
[two-phase-forest]: ../../../research/lean/ResearchLean/AG/TwoPhase/ForestSupport.lean
[two-phase-witness]: ../../../research/lean/ResearchLean/AG/TwoPhase/FiniteWitnesses.lean
[joint-kernel]: ../../../research/lean/ResearchLean/AG/CanonicalResolution/JointKernel.lean
[resolution-effective]: ../../../research/lean/ResearchLean/AG/CanonicalResolution/Effective.lean
[resolution-admissible]: ../../../research/lean/ResearchLean/AG/CanonicalResolution/Admissible.lean
[resolution-negative]: ../../../research/lean/ResearchLean/AG/CanonicalResolution/NegativeWitness.lean
[law-complex]: ../../../research/lean/ResearchLean/AG/ResolutionInvariance/LawGeneratedComplex.lean
[diagnostic-map]: ../../../research/lean/ResearchLean/AG/ResolutionInvariance/GeneratedComparisonMap.lean
[atlas-conditions]: ../../../research/lean/ResearchLean/AG/ResolutionInvariance/ResolutionInvarianceConditions.lean
[atlas-bijective]: ../../../research/lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparisonBijectivity.lean
[atlas-corollary]: ../../../research/lean/ResearchLean/AG/ResolutionInvariance/ResolutionInvarianceCorollary.lean
[atlas-firing]: ../../../research/lean/ResearchLean/AG/ResolutionInvariance/ResolutionInvarianceFiringWitness.lean
[uniform-reduction]: ../../../research/lean/ResearchLean/AG/UniformInvariance/UniformityReduction.lean
[uniform-defect]: ../../../research/lean/ResearchLean/AG/UniformInvariance/DefectSemantics.lean
[uniform-decider]: ../../../research/lean/ResearchLean/AG/UniformInvariance/UniformPresentationDecider.lean
[atlas-position]: ../../../research/lean/ResearchLean/AG/UniformInvariance/AtlasPositioning.lean
[local-nonfactor]: ../../../research/lean/ResearchLean/AG/UniformInvariance/GLocalV1Nonfactorization.lean
[struct-nerve]: ../../../research/lean/ResearchLean/AG/StructuralCover/NerveGeneration.lean
[struct-local]: ../../../research/lean/ResearchLean/AG/StructuralCover/StructuralLocalization.lean
[struct-zero]: ../../../research/lean/ResearchLean/AG/StructuralCover/GeneratedH1Vanishing.lean
[atlas-all-a-bridge]: ../../../research/lean/ResearchLean/AG/UniformInvariance/ConditionCAllABridge.lean
[atlas-all-a-firing]: ../../../research/lean/ResearchLean/AG/UniformInvariance/ConditionCAllAFiring.lean
[atlas-all-a-checker]: ../../../research/lean/ResearchLean/AG/UniformInvariance/ConditionCAllAChecker.lean
[core-transport]: ../../../research/lean/ResearchLean/AG/AtomFoundation/Transport.lean
[core-opcartesian]: ../../../research/lean/ResearchLean/AG/AtomFoundation/Opcartesian.lean
[core-unique]: ../../../research/lean/ResearchLean/AG/AtomFoundation/LiftUniqueness.lean
[core-refinement-no]: ../../../research/lean/ResearchLean/AG/AtomFoundation/RefinementObstruction.lean
[core-refinement-supply]: ../../../research/lean/ResearchLean/AG/AtomFoundation/RefinementSupply.lean
[geom-opcartesian]: ../../../research/lean/ResearchLean/AG/GeometryTransport/Opcartesian.lean
[geom-factorization]: ../../../research/lean/ResearchLean/AG/GeometryTransport/Factorization.lean
[geom-unique]: ../../../research/lean/ResearchLean/AG/GeometryTransport/LiftUniqueness.lean
[geom-supply]: ../../../research/lean/ResearchLean/AG/GeometryTransport/Supply.lean
[core-pseudo]: ../../../research/lean/ResearchLean/AG/CrossStageCoherence/CorePseudofunctor.lean
[geom-pseudo]: ../../../research/lean/ResearchLean/AG/CrossStageCoherence/Pseudofunctor.lean
[tower-coherence]: ../../../research/lean/ResearchLean/AG/CrossStageCoherence/TowerCompatibility.lean
[transport-pasting]: ../../../research/lean/ResearchLean/AG/TransportCoherence/PastingObstruction.lean
[transport-vanishing]: ../../../research/lean/ResearchLean/AG/TransportCoherence/VanishingCoherence.lean
[transport-unified]: ../../../research/lean/ResearchLean/AG/TransportCoherence/UnifiedObstruction.lean
[section-decomposition]: ../../../research/lean/ResearchLean/AG/CrossStageCoherence/SectionDecomposition.lean
[global-vanishing]: ../../../research/lean/ResearchLean/AG/CrossStageCoherence/GlobalVanishing.lean
[cross-witness]: ../../../research/lean/ResearchLean/AG/CrossStageCoherence/FiniteWitnesses.lean
[lens-squares]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/CSAATLensRelativeOperationSquares.lean
[protocol-squares]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/CSAATProtocolAdapterSquares.lean
[cs-comparison]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/CSAATFullyFaithfulComparisonTransport.lean
[doctrine-pullback]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/DoctrinePullback.lean
[pointed-pullback]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/PointedDoctrinePullback.lean
[cartesian-target]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/CartesianTarget.lean
[global-lift]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/ExactBottomGlobalLift.lean
[global-lift-coherence]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/ExactBottomGlobalLiftCoherence.lean
[coverage-classification]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/ExactBottomCoverageClassification.lean
[bc-mate]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/CoreBeckChevalleyMate.lean
[bc-exact]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/PackageProjectionBeckChevalleyExactness.lean
[indexed-diagram]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/IndexedBaseDiagram.lean
[indexed-assembly]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/IndexedDiagnosticAssembly.lean
[indexed-raw-classification]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/IndexedRawFamilyClassification.lean
[diagnostic-equivalence]: ../../../research/lean/ResearchLean/AG/DiagnosticConservativity/TransportEquivalence.lean
[diagnostic-orbit]: ../../../research/lean/ResearchLean/AG/DiagnosticConservativity/OrbitExactness.lean
[base-iso]: ../../../research/lean/ResearchLean/AG/DiagnosticConservativity/BaseIsoIndependence.lean
[refinement-classification]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/Classification.lean
[refinement-realized]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/RealizedSupport.lean
[refinement-qualification]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/Qualification.lean
[upper-mate]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleMateNaturality.lean
[configuration-descent]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/ConfigurationDescent.lean
[idempotent-normalization]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeNormalization.lean
[core-normalization]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/BCAuthoredCanonicalObjectNormalization.lean
[cell-projector]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeCellProjector.lean
[karoubi-image]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeKaroubiImage.lean
[raw-failure]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeRawFailureLocus.lean
[split-no-go]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/InternalNormalizationSplitNoGo.lean
[kar-arrow]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/KaroubiArrowEquivalence.lean
[kar-naturality]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/FunctorNaturality.lean
[comparison-groupoid]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/MaximalSubgroupoid.lean
[kar-placement]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/G116KaroubiPlacement.lean
[comparison-object-group]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/QualifiedComparisonGroup.lean
[generated-comparison-object-group]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/GeneratedQualifiedComparison.lean
[normalization-comparison-group]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/NormalizationComparisonGroup.lean
[normalization-projection]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/NormalizationProjection.lean
[normalization-category]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/NormalizationCategory.lean
[normalization-absorption]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/CanonicalNormalizationAbsorption.lean
[normalization-failure]: ../../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/NormalizationNaturalityFailure.lean
[normalization-counterexample]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/LaxDiagnosticProjectorModificationCounterexample.lean
[geom-normalization]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/CanonicalNormalization.lean
[bar-alpha]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactDerivedBarAlphaTriangle.lean
[bar-beta]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaClassification.lean
[bar-beta-witness]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaFiniteWitness.lean
[qualified-stabilizer]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonStabilizer.lean
[qualified-generated]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonGeneratedClassification.lean
[source-naturality]: ../../../research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleSourcePresentationNaturalityF16.lean
[observation-kernel]: ../../../research/lean/ResearchLean/AG/ComparisonInformationLoss/ObservationKernel.lean
[endpoint-kernel]: ../../../research/lean/ResearchLean/AG/ComparisonInformationLoss/EndpointKernelClassification.lean
[information-witness]: ../../../research/lean/ResearchLean/AG/ComparisonInformationLoss/FixedWitness.lean
[kar-restriction]: ../../../research/lean/ResearchLean/AG/ComparisonInformationLoss/KaroubiRestriction.lean
[group-restriction]: ../../../research/lean/ResearchLean/AG/ComparisonInformationLoss/GroupHomRestriction.lean
[kar-restriction-witness]: ../../../research/lean/ResearchLean/AG/ComparisonInformationLoss/KaroubiRestrictionFiniteWitness.lean
[beta-section]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaComparisonSection.lean
[beta-exactness]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaComparisonExactness.lean
[beta-bottom]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarBetaBottomQualifiedClassification.lean
[alpha-canonical-section]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarAlphaCanonicalComparisonSection.lean
[alpha-canonical-exactness]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/ExactBarAlphaCanonicalComparisonExactness.lean
[ambient-witness]: ../../../research/lean/ResearchLean/AG/FullGeometryNormalization/AmbientKernelComparisonWitness.lean
[fixed-components]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/FixedFComponentClassification.lean
[fixed-split]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/FixedFSplitExactSequenceAndTorsor.lean
[fixed-cardinality]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/FixedFFiberCardinality.lean
[fixed-examples]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/FixedFFiniteExamples.lean
[one-point-code]: ../../../research/lean/ResearchLean/AG/FiniteDecoderRepresentability/OnePointCode.lean
[code-evaluation]: ../../../research/lean/ResearchLean/AG/FiniteDecoderRepresentability/EvaluationClassification.lean
[code-fibers]: ../../../research/lean/ResearchLean/AG/FiniteDecoderRepresentability/CodeFibers.lean
[coverage-topology]: ../../../research/lean/ResearchLean/AG/FiniteDecoderRepresentability/CoverageTopology.lean
[discrete-compactness]: ../../../research/lean/ResearchLean/AG/FiniteDecoderRepresentability/DiscreteCompactness.lean
[fixed-arrow]: ../../../research/lean/ResearchLean/AG/FiniteDecoderRepresentability/FixedArrowClassification.lean
[finite-full]: ../../../research/lean/ResearchLean/AG/FiniteDecoderRepresentability/FiniteFullSubcategory.lean
[code-normalization]: ../../../research/lean/ResearchLean/AG/FiniteDecoderRepresentability/FiniteCodeNormalization.lean
[normalization-realization-iso]: ../../../research/lean/ResearchLean/AG/FiniteDecoderRepresentability/FiniteNormalizationRealizationIso.lean
[fin-one]: ../../../research/lean/ResearchLean/AG/FiniteDecoderRepresentability/FinOneCounterexample.lean
[nat-swap]: ../../../research/lean/ResearchLean/AG/FiniteDecoderRepresentability/NatAdjacentSwap.lean
[nat-subset-swaps]: ../../../research/lean/ResearchLean/AG/FiniteDecoderRepresentability/NatSubsetSwaps.lean
[countable-syntax]: ../../../research/lean/ResearchLean/AG/FiniteDecoderRepresentability/CountableSyntaxObstruction.lean
[cs-karoubi]: ../../../research/lean/ResearchLean/AG/RealizationReconstruction/CSKaroubiReconstruction.lean
[lens-model]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/LensFiberModelEquivalence.lean
[protocol-model]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/ProtocolObservedRestrictionEquivalence.lean
[local-equivalence]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/LocalReconstructionEquivalence.lean
[tag-recovery]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeFiniteReadingRecovery.lean
[tag-group-reconstruction]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeFiniteGroupReconstruction.lean
[tag-kernel]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeNormalizedChoiceKernel.lean
[tag-model]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeExactGeometryLocalModel.lean
[graph-separation]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/CompleteGeometryFunctionGraphSeparation.lean
[graph-category]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/CompleteGeometryGraphCategory.lean
[dependent-graph]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/DependentAlgebraicGraphCoherence.lean
[full-kernel]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/G122FullComparisonKernelDecomposition.lean
[graph-kernel]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/G122CompleteGraphKernelReconstruction.lean
[lens-karoubi]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/LensFiberKaroubiCoherence.lean
[protocol-karoubi]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/ProtocolObservedKaroubiCoherence.lean
[lens-invertible]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/LensFiniteDetermination.lean
[protocol-invertible]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/ProtocolFiniteDetermination.lean
[finite-components]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/FiniteDeterminingComponents.lean
[g101]: ../../../research/goals/G-101-aat-atom-foundation.md
[g103]: ../../../research/goals/G-103-aat-canonical-resolution.md
[g104]: ../../../research/goals/G-104-aat-resolution-invariance.md
[g107]: ../../../research/goals/G-107-aat-uniform-invariance-characterization.md
[g108]: ../../../research/goals/G-108-aat-geometry-reading-transport.md
[g110]: ../../../research/goals/G-110-aat-doctrine-fiber-product.md
[g111]: ../../../research/goals/G-111-aat-indexed-base-change-schema.md
[g112]: ../../../research/goals/G-112-aat-exact-bottom-coverage.md
[g114]: ../../../research/goals/G-114-aat-refinement-base-change.md
[g115]: ../../../research/goals/G-115-aat-upper-stage-lift.md
[g116]: ../../../research/goals/G-116-aat-idempotent-exchange-structure.md
[g118]: ../../../research/goals/G-118-aat-diagnostic-descent-transport.md
[g119]: ../../../research/goals/G-119-aat-realization-comparison-idempotents.md
[g120]: ../../../research/goals/G-120-aat-comparison-information-loss.md
[g121]: ../../../research/goals/G-121-aat-finite-decoder-representability.md
[g122]: ../../../research/goals/G-122-aat-full-geometry-normalization.md
[g124]: ../../../research/goals/G-124-aat-local-semantic-reconstruction.md
[r105]: ../../../research/reports/G-105-aat-structural-cover-invariance.md
[r117]: ../../../research/reports/G-117-aat-lax-diagnostic-projector.md
[r123]: ../../../research/reports/G-123-aat-realization-reconstruction.md
[r124]: ../../../research/reports/G-124-aat-local-semantic-reconstruction.md
