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
- 初版は G-125 の障害・診断比較と G-124 A・B の共通入力・局所再構成を収録する。
  C–E の接続と有限決定性の体系化は改訂版に収録する。
  個別結果の配置は §8.3、形式化との対応は §8.4、改訂版の内容は §8.5 に置く。
- 既存の数学資料の照合版は commit
  [`b0a2d4b2`](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/tree/b0a2d4b2690a1aabdf64f033c9fc6ca975f7445e)
  とする。G-125 の実装と G-124 の既存の個別結果は
  [`c245b49b`](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/tree/c245b49b0825f653307f396f4dc9f76e1ecad44a)
  に照合する。G-124 A・B の共通入力・局所再構成と既存結果への接続は、
  [`b738623a`](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/tree/b738623af29f015ab2d12e11c94411c74f26d311)
  の実装に照合する。量化と対象は固定 GOAL の A・B、
  証明済みの構成と定理は §8.4 の Lean 宣言に対応づける。
- n1012・n1015 を含むノートは参考資料とし、章立ては構成マスター、数学の定義・証明は一次資料に従う。
  合成は `gf=g∘f` と書く。Lean の `f ≫ g` はこの `gf` に対応する。

| 章 | 棚卸しの中心 | 後続へ渡すもの |
| --- | --- | --- |
| 1 | Atom・Law・operation・reading、相対的な対象・射・site | core と幾何の共通入力、射影の塔 |
| 2 | Law algebra、lawful locus、具体的な貼り合わせ障害、SAGA、整数係数のアフィン局所データ | 係数と既存 Čech 障害類の生成経路 |
| 3 | 標準解像度、表示可能性、診断不変性、同じ入力の障害・診断比較 | 指定類の対応、零性判定、reading 変更に沿う可換平方と零性不変性 |
| 4 | core・幾何の輸送、普遍性、合成と二層の障害 | 関手・比較同型・再選択の作用 |
| 5 | doctrine の積、exact / refinement 基底変換、上段比較 | 型と生成元の揃った二経路と比較射 |
| 6 | 冪等正規化、像、Karoubi 実現、自然性の反例 | raw 比較と像の比較、正規化関手 |
| 7 | 比較保存群、観測と正規化、変更の持ち上げ、CS 共通分類 | 核・像・section・fiber と情報損失の判定 |
| 8 | 有限表示、共通入力宣言、原始読み取り、対象・射の局所再構成 | 主同値と四族への適用、個別結果の補足 |

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
この差を、第7章の変更分類と第8章の意味保存射の再構成へつなぐ。

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
| 2-I 診断へ渡す指定障害 | 構成・定理。生成子関係の整数係数 sheaf、lawful な chart state と実 restriction、アフィン比較から既存の Čech 障害類を生成 | 選定した点・生成子の共通 Atom 入力、3 chart / 4 chart の被覆、任意の chart state・edge transition。異なる三つの chart の交差が空であることを被覆から証明 | [共通 Atom 入力][bridge-atoms]、[実被覆][bridge-covers]、[アフィン局所データ][bridge-affine]、[既存障害との一致][bridge-existing] |

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

### 2.3 第3章へ渡す整数係数のアフィン障害

2-I は、第2章から第3章へ整数係数の障害を渡す構成である。
有限 Source と有限 Law 族から生成子 `g=(ℓ,s)` を取り、Law-value を保つ原始関係 `R` を宣言する。
関係の連結成分集合を `B` とすると、整数係数の群とその標準形は

\[
 M_R=\mathbb Z[\{(\ell,s)\}]/\langle g-h\mid gRh\rangle
 \cong\mathbb Z^{(B)}
\]

となる。[presentation group の構成][bridge-presentation]でこの同型を証明する。
局所定数な `M_R` 値関数の sheaf を、AAT context から開集合への連続な support 関手で
引き戻し、既存の `ObstructionSheaf` とする。選定した点と生成子の共通 Atom carrier について、
support 関手の連続性、chart と overlap の非空性・連結性、実際の被覆と restriction を構成する。
異なる三 chart の交差は空であり、幾何から定める完全な face 添字も空になる。
これにより次数0・1は chart・edge 上の `M_R` 値、次数2は零として、
実際の Čech 複体を表示する。[係数 sheaf][bridge-sheaf]、[support の連続性][bridge-continuity]、
[有限被覆の幾何][bridge-cover-geometry]、[Čech 座標表示][bridge-cech]に対応する。

局所データ `x=(ξ,p)` は edge 上の遷移 `ξ` と chart 上の状態 `p` である。重なりでの比較を

\[
 o_q(x)_e=\xi_e+\operatorname{res}_{j,e}(p_j)
                    -\operatorname{res}_{i,e}(p_i),\qquad
 o_q(x)=\xi+d^0_{\rm ob}p
\]

とする。chart state は多項式環 `ℤ[X_g]` の整数値評価を定め、原始関係から生成する ideal
`(X_g-X_h \mid gRh)` を零へ送る。実 restriction と右状態のアフィン移動についても
lawfulness を示す。重なりの `Ob` 値の左右状態と遷移から比較値を計算し、
`GluingMismatchData`、`descentCocycle`、`descentObstructionClass` へ接続する。
`existingDescentAdditiveClass_eq_actualClass` は、その既存障害類の加法的表示が
上の cocycle の類に等しいことを述べる。

局所状態を `p+h` に変えると mismatch は `d⁰_ob h` だけ変わり、障害類は不変である。
ここから第3章へ渡すのは、同じ `x` から生成した具体的な類 `[o_q(x)]` とその係数・被覆である。

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
| 3-H 障害係数と診断複体の比較 | 構成・定理。`M_R` から有理 Law-value 係数への写像、次数0–2の cochain 比較、加法的 H¹ 準同型 | 2-I の実 Čech 複体と同じ Law・台から生成する `lawGeneratedComplex` を比較し、二つの微分平方を証明 | [係数比較][bridge-coefficient]、[Čech cochain 比較][bridge-cech]、[H¹ 写像][bridge-h1]、[選定入力][bridge-input] |
| 3-I 指定障害類の対応 | 定理。任意の許容局所データ `x` について `Φ_q([o_q(x)])=[a_q(x)]` と零性の保存 | 障害は 2-I の実 restriction と遷移から、診断は同じデータの Law 評価から生成する | [既存障害との一致][bridge-existing]、[選定入力での類の対応][bridge-classes] |
| 3-J 指定類の零性反映 | 定理。`R_q` と各 label の全 chart 共通代表の下で `[a_q(x)]=0 ⇔ [o_q(x)]=0` | 有理補正の辺差から整数補正を構成。両条件は選定入力の粗細双方で証明済み | [整数化][bridge-integral]、[反映の一般証明][bridge-reflection]、[選定入力での放電][bridge-selected-reflection] |
| 3-K reading 変更と障害判定 | 定理。比較平方、局所データと指定類の輸送、Atlas の条件 C による障害零性の不変性 | 選定した粗細 reading・3 chart / 4 chart の実 refinement。同じ nerve 射の `generatedComparisonH1Map` を診断側に使用 | [実 refinement][bridge-refinement]、[比較の自然性][bridge-naturality]、[条件 C と不変性][bridge-condition-c] |
| 3-L 同一入力の零・非零例 | 有限例・定理。非零 mismatch を持つ零障害例と、非零障害例を粗細両側で判定 | 非単射の canonical factor、両端の反映条件、条件 C を固定し、遷移のみを変える | [SelectedFiniteObstructionExamples][bridge-examples]、[G-125 の固定要求][g125]・[成果対応][r125] |

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

### 3.3 障害の読み取りと診断比較

3-H〜3-L は、同じ入力から生じる障害と診断の比較として初版へ収録する。採用入力は
`Source=Bool×Bool`、第一成分を評価する一つの Law、粗い reading `q_c=pr₁` と
細かい reading `q_f=id` である。原始関係には `(0,0)–(0,1)` と `(1,0)–(1,1)` の二辺を
両向きに宣言する。両 reading の adequacy、同じ Law-value の生成子がこの関係で結ばれること、
canonical factor `pr₁` の非単射性を [PointAtomLawInput][bridge-laws]で証明している。
幾何の点とこれらの生成子を一つの Atom carrier に収め、§2.3 の実被覆と係数を使う。
以下の結論は、各 reading で任意の遷移・chart state `x=(ξ,p)` について述べる。

**係数から cochain・類への比較。** Law-value label の集合を `L_val` と書く。
生成子の類をその label の有理 delta 関数へ送る加法的な写像
`ε_R:M_R→(L_val→ℚ)` を構成する。実 Čech 座標と Law-value 座標の対応から

\[
 \phi_q^n:C_{\rm ob}^n(q)\longrightarrow C_{\rm diag}^n(q)\quad(n=0,1,2),\qquad
 \phi_q^{n+1}d_{\rm ob}^n=d_{\rm diag}^n\phi_q^n\quad(n=0,1)
\]

を得る。cocycle と coboundary の保存から加法的な準同型
`Φ_q:H¹_ob(q)→H¹_diag(q)` を構成する。障害側は整数 presentation 係数、診断側は
有理数値の `lawGeneratedComplex` である。
同じ局所データの診断を独立な生成式

\[
 a_q(x)=\phi_q^1(\xi)+d^0_{\rm diag}\phi_q^0(p)
\]

で定め、cochain 平方から `φ_q¹(o_q(x))=a_q(x)`、従って
`Φ_q([o_q(x)])=[a_q(x)]` を証明する。§2.3 の既存障害類との一致を通して、
これは第2章から受け取った指定障害類の対応になる。

**零性を反映する条件と証明。** `R_q` は、同じ Law-value label を持つ任意の生成子対が
原始関係で連結される条件とする。この条件から `B≃L_val` と `ε_R` の単射性を得る。
加えて、各 label の値を持つ一つの target がすべての chart support に属する条件
`CommonLabelChartSupport` を用いる。選定入力では、粗い側の代表を `value`、
細かい側の代表を `(value,false)` として、この条件も証明する。

診断類が零なら有理数値の0-cochainによる補正を取り、共通代表の座標で読み、
`R_q` によって各整数 block 係数を回収する。辺差が整数なので、座標ごとに整数部分を取ると
同じ辺差を持つ整数0-cochainが得られる。それを実 Čech section へ戻すことで

\[
 [a_q(x)]=0\quad\Longleftrightarrow\quad[o_q(x)]=0
\]

を示す。整数部分はこの補正を構成するために用いる。係数準同型の逆として扱わない。
補足には、同じ label を持つ二生成子を関係で結ばない場合に係数比較が単射でなくなる
[反例][bridge-coefficient]も置き、構造条件の役割を示す。

**reading 変更に沿う可換性と不変性。** 粗い被覆の一つの chart を二つへ分ける
3 chart から4 chartへの refinement を用いる。障害側は実 restriction による引戻しを使い、
細かい側の内部辺 `k` には零 section を対応させる。これにより `T_ob` を構成し、
診断側の同じ nerve 射から生成する `T_diag` との間で

\[
 \Phi_{q_f}T_{\rm ob}=T_{\rm diag}\Phi_{q_c},\qquad
 T_{\rm ob}[o_{q_c}(x)]=[o_{q_f}(x_f)],\qquad
 T_{\rm diag}[a_{q_c}(x)]=[a_{q_f}(x_f)]
\]

を証明する。`x_f` は粗い側の遷移と状態をこの refinement で運んだデータである。
同じ入力について Atlas の条件 C0–C6 を証明し、既存の診断比較の全単射定理を適用する。
両端の零性反映と併せて `[o_{q_c}(x)]=0 ⇔ [o_{q_f}(x_f)]=0` を得る。

**二つの具体例。** `u` は生成子 `(唯一の Law,(false,false))` の `M_R` における類であり、
対応する診断座標での値が `1` なので非零である。chart state を零に固定する。

| 局所データ | 粗い側の遷移（ab, bc, ac） | 細かい側の遷移（k, ab, bc, ac） | 障害類・診断類 |
| --- | --- | --- | --- |
| 零障害例 | `(u,-u,0)=d⁰(0,u,0)` | `(0,u,-u,0)` | 粗細の両側で零。mismatch 自体は両側で非零 |
| 非零障害例 | `(u,0,0)` | `(0,u,0,0)` | 粗細の両側で非零 |

粗い三辺の向き付き和 `ξ_ab+ξ_bc−ξ_ac` は任意の coboundary で零になり、非零例では
`u` になる。この計算と類の対応・零性反映・reading 輸送により表の結論を得る。
被覆・係数・Law を同じに保ったまま、局所データの違いを障害判定へ戻す例として本論に置く。

**付録への対応。** 付録Aでは次の宣言に対応させる。宣言の共通 namespace は
`AAT.AG.ObstructionDiagnosticBridge` である。

| 論文の内容 | 宣言・一次資料 |
| --- | --- |
| 2-I の既存障害の生成 | [ExistingObstructionBridge][bridge-existing] の `GeneratorPresentation.ActualCechAffineLocalData` 内の `ActualAffineOverlapData.comparison_eq_actualMismatch`、`gluingMismatchCochain_eq_actualMismatch`、`existingDescentAdditiveClass_eq_actualClass` |
| 3-H の cochain・H¹ 比較 | [FaceEmptyCechNormalization][bridge-cech] の `GeneratorPresentation.actualCechCoefficient_comm0`・`actualCechCoefficient_comm1`、[CombinedAtomH1Input][bridge-input] の `coarseCochainMap`・`fineCochainMap`・`coarseH1Map`・`fineH1Map` |
| 3-I の既存指定類の対応 | [CombinedAtomSpecifiedObstruction][bridge-classes] の `coarse_h1_map_existing_obstruction_class_eq_diagnostic_class` と `fine_h1_map_existing_obstruction_class_eq_diagnostic_class` |
| 3-J の零性同値 | [CombinedAtomSpecifiedReflection][bridge-selected-reflection] の `coarse_diagnostic_class_eq_zero_iff_existing_obstruction_class_eq_zero` と `fine_diagnostic_class_eq_zero_iff_existing_obstruction_class_eq_zero` |
| 3-K の比較平方と指定類の輸送 | [CombinedAtomReadingNaturality][bridge-naturality] の `h1_comparison_square`、`actualH1Map_existingObstructionClass`、`diagnosticH1Map_diagnosticClass` |
| 3-K の条件 C と障害不変性 | [SelectedReadingConditionC][bridge-condition-c] の `conditionC`、`diagnosticH1Map_bijective`、`existing_obstruction_class_eq_zero_iff_mapped_existing_obstruction_class_eq_zero` |
| 3-L の有限例 | [SelectedFiniteObstructionExamples][bridge-examples] の `canonical_factor_not_injective`、`coarse_reflectionCondition`・`fine_reflectionCondition`、`selected_conditionC`、`existing_zero_example_outcomes`・`existing_nonzero_example_outcomes` |

付録Bには原始関係、被覆と全交差、微分・refinement の計算表、整数補正と二例の計算を置く。
付録Cには冒頭の実装固定版と [G-125 report][r125] の検証・独立査読記録を対応づける。

### 3.4 他の係数・輸送結果との対応

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
| 4-D 合成と射影 | 定理。fiber 間 transport functor、compositor / unitor、単位・三重合成の整合、塔の pseudonatural compatibility | 標準core輸送と標準幾何輸送を用い、底をpointed ExtractionInstanceに揃える。対象とvertical射、compositor・unitorを同じ構成で扱う | [CorePseudofunctor][core-pseudo]、[Pseudofunctor][geom-pseudo]、[TowerCompatibility][tower-coherence] |
| 4-E authored 比較の障害 | 構成・同値。raw 2-cell defect、辺 reselection の作用、障害消滅と coherent な再選択の存在 | Coreの有限比較図式、抽出の底に関して強い辺lift、底の二道の一致、指定自己同型を固定。Cocycle則には指定syzygyの整合を要求 | [PastingObstruction][transport-pasting]、[VanishingCoherence][transport-vanishing]、[UnifiedObstruction][transport-unified] |
| 4-F 段横断の障害 | 構成・条件付き分解。core への射影、kernel、辺水準 section、全体障害と段内・段間障害の関係 | 幾何の辺はp-strong、射影はq-strong。底の二道の一致と同じ整列したedge sectionの下で、順序を保つ分解と同時消滅を扱う | [SectionDecomposition][section-decomposition]、[GlobalVanishing][global-vanishing]、[FiniteWitnesses][cross-witness] |

raw defect の比較式を `δ=uφ⁻¹` とすると、辺から生成した中間比較 `m` に対して
`uφ⁻¹=(um⁻¹)(mφ⁻¹)` となる。段内項が kernel に入ることは、alignment と射影の
等式から導く。非可換な積を単純な可換和や、係数未指定の ordinary `H²` と同一視しない。

小例は、単一 disk の defect を辺で吸収する正例と、閉じた二面配置・三者貼り合わせで
許容 orbit 内の食い違いが残る例を候補とする。前者と後者が同じ再選択作用を使うことを示す。

### 4.2 CS の操作保存と比較図式

型・役割・操作名を Atom 側、状態 carrier と実行値を Source・対象・局所実現側に置き、
第1章の独立な意味論と保存則を AAT の射へ対応させる。非単射な状態写像や補完 table も
一般の意味保存射として保持する。

本文4.36–4.38と同じく、共通のview・基準viewを持ち、三法則を満たし、
基準fiberが有限なlensを扱う。state・view・read・writeの四役割にそれぞれ
`h,u,h,h×u` を割り当て、get・putの二つの可換図式で操作保存を表す。
読取りの入力、更新の入力の状態成分、更新の出力に同じ状態写像 `h` を使う。
この対象・仮定の下で、固定viewの射との対応と、可逆な状態写像・可視写像を備えた変更との対応を扱う。
プロトコルでは名前付き操作の可換図式と adapter の `bq=q'a` を保持し、合成の保存を示す。
一次資料は [lens の相対操作図式][lens-squares]、[protocol の adapter 図式][protocol-squares]。

**接続項目。** 上記の操作図式、底を固定する資格、完全幾何の保存則は別々に照合する。
完全幾何へ進むには context・coverage・overlap・係数・raw restriction・Support・Axis・Observable を
具体的に構成する。充満忠実関手に沿う[比較群輸送][cs-comparison]は、その関手と許容射を
構成した範囲で使う。四族を同じ実現・局所モデルへ結ぶ内容は §8.2、形式化との対応は §8.4 にまとめる。

## 第5章 基底変換と生成比較

### 5.1 二経路を構成する数学

| 項目 | 種類・数学内容 | 入力・成立条件と結論 | 主な一次資料 |
| --- | --- | --- | --- |
| 5-A doctrine fiber product | 構成・普遍性。exact cospan から compatible source pair の doctrine を生成 | 全 cone を量化し、Atom 成分を恒等に制限しない。pointed 版は選択した compatible point を用いる | [DoctrinePullback][doctrine-pullback]、[PointedDoctrinePullback][pointed-pullback] |
| 5-B cartesian reindexing | 構成・普遍性。任意の exact semantic 底射と target package への strong cartesian lift、cleavage と合成整合 | 一般のexact射のcore liftは有限codeを仮定しない。合成・単位の整合性は存在定理から固定した標準選択について述べる | [CartesianTarget][cartesian-target]、[ExactBottomGlobalLift][global-lift]、[同 coherence][global-lift-coherence] |
| 5-C exact-bottom の有限 code coverage | 分類。端点同型を含む arrow 圏の coverage | 両Sourceの有限性とtarget全抽出の有限・余有限性。Code射は正規化後の既定値・例外集合の輸送等号を要求。固定code間のHomと端点同型を許すcoverageを区別 | [ExactBottomCoverageClassification][coverage-classification]、[G-112][g112]；第8章へ |
| 5-D canonical Beck–Chevalley mate | 構成・同型。pointed exact pullback square の push / pull 二経路と canonical mate | Atomの等号判定とBCPresentation。有限codeのcospan、compatibleな選択source、有限診断図式から生成した平方でmate・可逆性・lift選択変更を比較 | [CoreBeckChevalleyMate][bc-mate]、[PackageProjectionBeckChevalleyExactness][bc-exact]、[G-110][g110] |
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
| 6-H 完全幾何での実比較 | 定理・非可逆例。実生成 `barAlpha` の core mate への射影、`barBeta=bar d barAlpha`、Karoubi 同型と可逆性分類 | AuthoredBCDatumSquareの有限codeによる同じ平方、図式のcore・強い辺、各面の終点と底の二道、指定比較、同じ面・cochain・係数・元幾何。既存の有限witnessと本文の別入力を区別 | [ExactDerivedBarAlphaTriangle][bar-alpha]、[ExactBarBetaClassification][bar-beta]、[ExactBarBetaFiniteWitness][bar-beta-witness] |

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
各 `u` 上の変更の集合は核の右torsorであり、`V,K` が有限なら個数は
`(|K|!)^{|π₀(Q)|}` になる。積の再添字式、分裂短完全列、section、fiberの全単射と個数を記述する。

積lensでは、基準viewと有限集合 `K` を固定し、同じ `V×K` の自己変更を扱う。
一つの可視置換 `u` に追随してget/putを保つ変更は、`Sym(K)` と全単射に対応する。
プロトコルには、各制御点の状態を同じ `K`、各生成辺の状態作用を恒等とする
セッションモデルを代入し、連結成分ごとに独立な補完の変更を得る。

基準補完 `k₀` を保つ版では `Sym(K)` を `k₀` の固定部分群に置き換える。
積lens側では、選択section `s(v)=(v,k₀)` の保存に対応する。
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

## 第8章 表示と局所再構成

初版の主結果は、完全幾何の原始読み取りによる局所再構成とする。
§8.1 の有限表示と再構成原理から §8.2 の主同値へ進み、形式化との対応を §8.4 に置く。
原稿は AAT の主定理、行内送金などの設計変更への適用、既存 CS への適用の順に構成する。
有限なモデルでの情報の十分性・検査手順・計算費用を扱い、無限対象に依存する反例は補足に置く。

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
| 8-D 表示方式と無限対象の反例 | 意味が同型でも固定 code 間に射がない有限例と、無限 support 置換・可算 decoder の非全射性 | 有限例は本論、無限対象の例は補足に置く。有限例外表による表示と有限規則による記述を区別。`P(ℕ)` の埋込みは計算可能性を制限しない全自己同型を対象とし、有限資源下の実装や任意の無限パラメータ参照を許す構文全般の不可能性とはしない | [FinOneCounterexample][fin-one]、[NatAdjacentSwap][nat-swap]、[NatSubsetSwaps][nat-subset-swaps]、[CountableSyntaxObstruction][countable-syntax] |
| 8-E CS の有限再構成 | 構成・圏同値。lens の有限基準 fiber、protocol の有限生成 table から対象・一般射を回復 | operation・Law・観測を保つ一般射を扱う。Karoubi、retract、Arr への拡張を同じ制限・延長と整合させる | [CSKaroubiReconstruction][cs-karoubi]、[LensFiberModelEquivalence][lens-model]、[ProtocolObservedRestrictionEquivalence][protocol-model] |
| 8-F 一般局所再構成原理 | 条件付き一般定理。Hom 分離、Hom 組立て、対象組立てから reading functor の圏同値を構成 | 三条件を独立に述べる。対象は読み取りが局所モデルと同型になる実現を構成し、射は制限・組立ての両逆を示す | [LocalReconstructionEquivalence][local-equivalence] |
| 8-G タグ族の局所回復 | 構成・分類。source-choice 群、全有限 Bool table の整合族、正規化による情報損失、正規化を含む生成部分圏 | 全 source-choice 族と一様 flip を保持する。正規化後の単一像から全 source-choice を分離できるとはしない | [TagChangeFiniteReadingRecovery][tag-recovery]、[TagChangeNormalizedChoiceKernel][tag-kernel]、[TagChangeExactGeometryLocalModel][tag-model] |
| 8-H 完全幾何の成分読み取り | 構成。原始 Bool graph、完全 Hom の分離、lawful graph code からの Hom 組立てと成分別合成 | package で添字づけた対象間の射を再構成する。対象を含む共通宣言からの構成は §8.2、形式化との対応は §8.4 に置く | [CompleteGeometryFunctionGraphSeparation][graph-separation]、[Hom の組立て][graph-assembly]、[直接定めた局所圏][graph-direct] |
| 8-I G-122 比較の回復の材料 | 補足の既存構成。raw 比較の normalized 座標と full restriction-kernel 座標への分解、complete graph による分離 | 個別の座標表示として採用。主同値と投影・正規化・群分類との整合は §8.5 の改訂版へ | [G122FullComparisonKernelDecomposition][full-kernel]、[G122CompleteGraphKernelReconstruction][graph-kernel]、[G-124 report][r124] |
| 8-J 共通入力と原始読み取り | 構成・証明済み。`Σ,D,Λ`、全構造保存射を持つ `R_Θ`、有限に組み立てた局所値と読み取り | 一つの宣言の任意のパラメータ `Θ`。タグ・固定生成比較・lens・プロトコルの必須四族を収録し、各法則の有限 support を原始評価へ接続 | [共通の原始読み取り][primitive-common]、[幾何][primitive-geometry-category]、[lens][primitive-lens]、[protocol][primitive-protocol]。固定要求は [G-124 A][g124] |
| 8-K 共通の局所再構成 | 定理・証明済み。独立な整合式から `M_Θ` を構成し、原始読み取り `N_Θ` を圏同値にする | A のデータから分離・Hom 組立て・対象組立てを証明。任意端点間の非可逆射を含む全許容 Hom で両逆・存在一意性を示し、同型・恒等・合成・評価との整合を保つ | [共通の再構成と主同値][primitive-common]、[一般再構成原理][local-equivalence]。固定要求は [G-124 B][g124] |

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

### 8.2 共通入力からの局所再構成

Atom の集合と完全幾何の射の方式を固定するパラメータ `Θ`、
Atom・Law・operation・完全幾何のデータ条件 `D_Θ`、局所読み取りの宣言を構成する。条件 `D_Θ` を
満たす実現と、指定した構造を保つすべての写像から圏 `R_Θ` を定める。
保持する carrier・係数環などの型と由来、評価、各成分の保存等式を入力宣言に記す。
実現と許容射は、原始構造と保存条件によって独立に定める。

読み取りの添字 `Λ_Θ` と各局所値を、型付き図式・table・パラメータ参照から構成する。
operation の両端と作用、Law の添字・評価・残差、raw 座標と restriction、context、
coverage・overlap、Support・Axis・Observable を原始評価で読む。
一つの局所片は有限に組み立て、その値に完成した全域対象・全域射を保持しない。
無限の carrier は宣言した型参照として保持でき、読み取り添字と整合族全体には無限を許す。

同じ `Θ` に対し、局所対象と局所射を、制限・overlap・operation 輸送・Law・係数の
局所等式を満たす族として定め、成分ごとの恒等・合成から `M_Θ` を構成する。
原始読み取りは関手 `N_Θ:R_Θ→M_Θ` を与える。次の証明を個別に置く。

1. **分離。** 読み取りが対象・射を区別し、特に各 Hom の読み取りが単射である。
2. **射の組立て。** 独立な整合式を満たす任意の局所射を全域の構造保存射へ組み立てる。
3. **対象の組立て。** 任意の局所モデル対象に対し、読み取りがそれと同型になる実現を構成する。

一般原理ではこの分離・組立てを仮定して圏同値を証明する。AAT への適用では、
上で構成したデータ条件と局所等式からこれらを証明し、

\[
 N_\Theta:\mathcal R_\Theta\simeq\mathcal M_\Theta,\qquad
 \operatorname{Hom}_{\mathcal R_\Theta}(X,Y)
 \underset{\operatorname{asm}}{\overset{\operatorname{read}}{\rightleftarrows}}
 \operatorname{Hom}_{\mathcal M_\Theta}(N_\Theta X,N_\Theta Y),\qquad
 \operatorname{read}\operatorname{asm}=1,\quad
 \operatorname{asm}\operatorname{read}=1
\]

を主要定理にする。同型・恒等・合成・評価との整合を同じ構成で示す。
整合式は局所データ間の等式として定め、全域の射の存在や延長可能性をその条件に含めない。

| 収録する入力族 | 構成・収録する対象と射 |
| --- | --- |
| タグ付き operation | `taggedOperationPackage`、canonical 正規化、一様 flip、source-choice 族の全元 |
| 固定生成比較 | `finiteAxisFoldBCDatumSquare` と `finiteAxisFoldFixedCoefficientGeometryFamily`、cell `second`、係数 `ℤ` の生成比較・正規化・端点自己同型 |
| lens | get/put の三法則と有限基準 fiber を持つ実現、および独立に指定した意味保存射の全範囲 |
| プロトコル | 商経路圏上の観測を持つ有限 carrier 実現、および観測を保つ自然変換の全範囲 |

原稿では、タグ族と固定生成比較を完全幾何の主定理の適用として置く。
CS の二族の入力と局所モデルは、その後の適用節で定義する。
独立した意味論の対象・全許容射について分離と組立てを証明し、一般再構成原理から圏同値を得る。
さらに、lens の基準 fiber 上の任意の写像、protocol の観測と生成辺を保つ
頂点写像の有限表による再構成を示す。
完全幾何の主定理と CS の系を合わせた収録範囲を [G-124 A・B][g124]に対応させ、
その証明を[共通の原始再構成][primitive-common]へ対応づける。

形式化では、一つの `Parameter` が representative geometry、explicit geometry、lens、protocol の
圏と原始読み取りを指定する。上表の必須四族のうち、タグ族は explicit geometry、固定生成比較は
representative geometry に収録される。局所対象・局所射の条件を満たす有限片の整合族から、
各枝の組立てを用いて一つの `reconstructionData` を構成し、一般再構成原理を一度適用する。
主同値の前向き関手が原始読み取りそのものであることは `equivalence_functor` で確認する。

### 8.3 初版の例・系・補足に使う個別結果

以下の個別結果は、指定した読み取り方式とともに例・系・補足へ配置する。
lens の有限基準 fiber、protocol の観測付き読み取りと、有限 decoder・retract・Karoubi・Arr の
経路は、A・B の主同値へ接続済みであり、§8.4 に対応を記す。各経路の既存結果は
[lens の Karoubi 整合][lens-karoubi]と [protocol の Karoubi 整合][protocol-karoubi]にある。
同じ局所読み取りによる有限決定性と、比較群・section・核・fiber までの統合は §8.5 の改訂版で扱う。
比較群の一般的な輸送は [充満忠実関手による輸送][cs-comparison]に対応する。

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

タグ変更族の個別結果では、二元巡回群 `C₂` を用いて、全有限制限の整合族との群同型

\[
 C_2^{\Omega}\cong\varprojlim_{S\subseteq_{\mathrm{fin}}\Omega}C_2^S
\]

を与える。
`Ω` が有限なら全体表から族を決定できる。無限なら、どの有限集合の外でも変更を残せるため、
一つの有限片による区別は成立しない。この無限例は原稿の補足に置く。
有限なモデルでは、全体表と選んだ部分の情報の十分性、明示的な列挙と等号判定による検査手順、
計算費用を区別する。全有限片からの再構成だけで、実用的な検査の費用は結論しない。

一次資料: [一般 lens 射][lens-finite]、[一般 protocol 射][protocol-finite]、
[lens の可逆変更][lens-invertible]、[protocol の可逆変更][protocol-invertible]、
[有限決定集合と成分][finite-components]、[タグの全有限読み取りの群同型][tag-group-reconstruction]。

### 8.4 形式化との対応

第8章の構成要素を、共通主同値の証明に使う順で一次資料へ対応づける。
以下の原始構成と接続は、冒頭に記した `b738623a` に照合する。

| 構成要素 | 数学的な内容 | 一次資料 |
| --- | --- | --- |
| 有限片と制限 | 型付き query の有限部分集合ごとの値、包含に沿う整合、singleton からの貼り合わせと制限の両逆。query 全体には無限を許す | [IndependentFiniteFragments][primitive-fragments] の `fragment_finite`、`glue_fragments`、`fragments_glue` |
| 幾何の局所対象 | Atom・core・幾何の原始評価を有限片に制限し、独立な構造条件から対象を組み立てる。raw の型参照・有限多項式・変数像も保持する | [幾何の原始宣言][primitive-geometry-declaration]、[対象の組立て][primitive-geometry-assembly]、[有限片からの回復][primitive-geometry-fragments]、[独立 raw 検証][independent-raw] |
| 幾何の圏と全 Hom | representative / explicit の両形で原始局所対象・局所 Hom の圏を定め、対象の分離、端点を揃えた Hom の読取り・組立て、恒等・合成・原始評価の一致を証明 | [IndependentGeometryCategoryReconstruction][primitive-geometry-category] の `representativeReadObject_injective` / `explicitReadObject_injective`、`representativeReadingHomEquiv` / `explicitReadingHomEquiv`、`representativeReconstructionData` / `explicitReconstructionData` |
| lens の原始構成 | state 型、get/put graph、三法則、有限な基準 fiber の list cover から対象を構成。map graph と二保存則から非可逆射を含む全 Hom を構成 | [IndependentLensPrimitiveReconstruction][primitive-lens] の `Object`、`Hom`、`readingFunctor`、`reconstructionData`。有限 fiber との既存同値は [LensFiberModelEquivalence][lens-model] |
| protocol の原始構成 | 頂点ごとの state 型、生成辺・観測 graph、経路等式・観測 square、有限 list cover から対象を構成。辺・観測を保つ頂点 map から全 Hom を構成 | [IndependentProtocolPrimitiveReconstruction][primitive-protocol] の `Object`、`Hom`、`readingFunctor`、`reconstructionData`。既存の観測付き同値は [ProtocolObservedRestrictionEquivalence][protocol-model] |

次の表の宣言は、特記した一般原理を除き、[IndependentAATPrimitiveReconstruction][primitive-common]
の同名 namespace にある。

| 共通構成・証明 | 対応する宣言と数学的な役割 |
| --- | --- |
| 入力・局所値・読み取り | `Parameter`、`NativeCategory`、`LocalCategory`、`ObjectQuery`、`Query`、`Value`、`reading`。対象の query と、始域・終域・Hom の役割を持つ query、その値型・原始読み取りを指定 |
| 独立な局所条件 | `ObjectTableLaws`、`LawfulObjectFamily`、`HomTableCertificate`、`LawfulHomFamily`。幾何の Hom は保持成分・補助成分の有限片の族と局所法則をデータとして保持し、CS の Hom は原始 graph と保存式の証拠を用いる |
| 整合族と局所圏の対応 | `localObjectFamilyEquiv`、`localHomFamilyEquiv`。独立な条件を満たす共通有限片の族と、各局所圏の対象・Hom が両方向に対応 |
| 対象・Hom の組立て | `assembleObjectFamily`、`readAssembledObjectIso`、`assembleHomFamily`。対象は読み取り後の同型、Hom は元の端点間の射として回復 |
| Hom の両逆・分離・存在一意性 | `localHomFamily_read_assemble`、`assembleHomFamily_read`、`homSeparation`、`lawfulHomFamily_existsUnique_preimage`、`existsUnique_preimage`。任意の端点間の全許容 Hom に適用 |
| 主同値 | `reconstructionData` から [一般原理][local-equivalence]の `ReconstructionData.equivalence` を適用。`equivalence`、`equivalence_functor`、`homEquiv` が主同値・その前向き関手・Hom の両逆を与える |
| タグ族の収録 | `taggedNativeObject`、`taggedSourceChoiceNativeHom`、`taggedNormalizationNativeHom`。全 source-choice、一様 flip、canonical 正規化の原始評価と既存 reader との比較を保持 |
| 固定生成比較の収録 | `finiteAxisFoldOriginalNativeObject`、`finiteAxisFoldDirectNativeObject`、`finiteAxisFoldViaBaseNativeObject`、`finiteAxisFoldBarAlphaNativeHom`、`finiteAxisFoldBarBetaNativeHom`。生成 cochain と定数 1 cochain、左右の冪等射、`finiteAxisFoldRawComparisonInclusion` による両端自己同型の収録 |
| CS の既存読み取りとの一致 | `lensFiberComparisonIso`、`protocolObservedComparisonIso` とその成分評価。主同値からの読み取りが既存の有限 fiber・観測付き読み取りと自然同型で対応 |
| CS の有限表示との接続 | `lensFiniteDecoder_retractGeneratedBy` / `protocolFiniteDecoder_retractGeneratedBy`、`lensKaroubiEquivalence` / `protocolKaroubiEquivalence`、`lensKaroubiArrowEquivalence` / `protocolKaroubiArrowEquivalence`。既存の decoder・retract・Karoubi・Arr を主同値へ接続し、各経路の比較自然同型を与える |
| 既存の四族総圏との一致 | [四族の総圏][four-family-total]への接続。`cycle79TaggedTotalReading_common`、`cycle79G122TotalReading_common` が同じ Hom の評価一致、CS の `cycle79LensPrimitiveFiniteDecoderReadingIso` / `cycle79ProtocolPrimitiveFiniteDecoderReadingIso` などが既存経路との自然同型を与える |
| 条件と全 Hom の具体例 | `lensHomTableCertificate_mismatched_carrier_rejected` などの型・graph・法則違反の拒否、`lensConstantFalseNativeHom_family_recovery` / `protocolTwoToOneNativeHom_family_recovery` による非単射 Hom の回復、`explicitCoefficientProjection_commonReading_distinct` による同じ底作用を持つ異なる Hom の区別 |

有限 support の共通宣言への接続は、`geometryFormula_evaluate_iff_of_commonSupport`、
`lensHomFormula_evaluate_iff_of_commonSupport`、`protocolHomFormula_evaluate_iff_of_commonSupport`
などに対応する。これらは support 上の原始評価の一致から法則の評価一致を与える。
CS の各 module の `objectFormula_support_finite` / `homFormula_support_finite` も併せて用いる。
局所片の有限性と、有限個の読み取りで全体が決まる有限決定性は分けて扱う。

付録A・Cには、本文の命題・入力構成・前提の証明・主同値での使用先と、Lean 宣言・版を対応づける。

### 8.5 改訂版で加える投影・比較群・有限決定性（C–E）

初版の展望には、§8.2 の対象・関手から次の問いを述べる。
改訂版では、それぞれを定理・証明・具体的帰結として展開する。A・B は完了しているが、
G-124 全体は C–E が未完了の `proof-checkpoint` である。

| 条項 | 改訂版で収録する内容 | 初版から受け取るもの |
| --- | --- | --- |
| C | 底・観測・係数投影の自然な対応、任意の比較 `c` の `Γ_c≅Γ_{N_Θ(c)}`、底固定・許容部分群への制限と正規化・Karoubi・Arr との整合。固定 G-122 例の可逆性・反映、section、分裂短完全列、核と全 lift fiber の回復 | 第6〜7章の比較・分類、8-K の主同値と固定例の収録 |
| D | §8.3 の区別・延長・実効性の定義を、A・B の局所読み取りと具体例へ共通に適用する。操作系の連結成分による必要十分条件と、明示的有限入力上の決定・延長計算 | 共通局所読み取りと §7.2 の操作系・変更分類 |
| E1 | 全 source-choice 族の群同型と全有限片からの回復を主同値による回復と同定し、同じ定義で有限決定不能性と一様 flip の性質を示す | タグ族の収録、§8.3 の個別結果 |
| E2 | A・B で接続した CS の有限再構成・Karoubi / retract / Arr を基に、同じ読み取りによる有限決定性と可逆変更の連結成分判定を統合し、比較群・section・核・fiber も回復する | CS の独立な意味論、主同値と有限表示の比較自然同型、§8.3 の個別結果 |

第7章の分類定理と §8.3 の個別結果は、それぞれの成立条件で初版にも収録できる。
この表は、それらを共通の局所再構成と結ぶ改訂版の追加内容を定める。

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
| [本文 VIII][math-viii] | Class Transport（§7）は第3章の係数比較へ統合し、第4〜5章とは実比較を与える箇所で接続。§8.3 の個別結果に用いる有限計算と実効性、付録Bの有限計算・Alexander dual（§5）・Measurement Packet（§11）の入力・係数・仮定・出力の意味を収録 | 有限な site と係数アルゴリズムを指定し、selected measurement ideal と標準 obstruction ideal を分ける。Support-Localized Transfer Measurement（§10）の基本条件は本文 V の補足へ、norm・support weight・Wasserstein 型の拡張は展望へ置く。Hodge / Tor base change の条件を保持し、stability の候補は候補として記す |
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
| 第2→3章 | 同じ Atom・Law・被覆入力の既存 Čech 障害と law-value 診断 | G-125 の 2-I・3-H〜3-L を収録。cochain 比較、既存指定類の対応、零性反映、reading 平方・輸送・不変性と二例を対応づける |
| 第3→8章 | ambient な存在と、指定した表示体系内での実現可能性を分ける | `q_L` の admissible 表示、底の code coverage、固定 Hom、局所組立てという別々の普遍性を説明 |
| 第4→5→6章 | 輸送の普遍性から二経路・実比較・正規化因子へ進む | `α`、authored comparator、`β`、`barAlpha`、`barBeta` の端点と生成元を揃える |
| 第6→7→8章 | 正規化と比較保存群の既存分類、その比較・変更を含む入力の局所再構成 | 初版は 6-D→7-H、6-E→7-I の分類と、A・B による対象・全許容射の回復を収録。共通主同値と投影・正規化・section・核・fiber の整合は §8.5 の C へ |
| 第2章と第8章の「局所」 | site の被覆上の descent と、原始読み取りの整合族による reconstruction の関係 | 添字圏・制限・overlap・係数・assembly の比較を与える場合に限り接続。一般 `H¹` による同一の障害理論は追加の課題 |
| 第1・4・7・8章の CS | 独立な意味論 → 入力構成 → 操作保存 → 共通分類・局所再構成 | 初版は lens と protocol の対応命題と A・B の適用を揃える。有限決定と同じ主同値との整合は §8.5 の D・E へ。操作が hidden state を恒等に運ぶ特殊形の分類は、その入力を明記する |

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
[r124]: ../../../research/reports/G-124-aat-local-semantic-reconstruction.md
[g125]: ../../../research/goals/G-125-aat-obstruction-diagnostic-bridge.md
[r125]: ../../../research/reports/G-125-aat-obstruction-diagnostic-bridge.md
[bridge-atoms]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/PointGeneratorAtomInput.lean
[bridge-laws]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/PointAtomLawInput.lean
[bridge-presentation]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/PresentationGroup.lean
[bridge-sheaf]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/AATLocallyConstantObstruction.lean
[bridge-continuity]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/CombinedAtomContextContinuity.lean
[bridge-cover-geometry]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/FiniteCoverGeometry.lean
[bridge-covers]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/CombinedAtomActualNerve.lean
[bridge-cech]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/FaceEmptyCechNormalization.lean
[bridge-affine]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/SpecifiedAffineObstruction.lean
[bridge-existing]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/ExistingObstructionBridge.lean
[bridge-coefficient]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/CoefficientComparison.lean
[bridge-h1]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/ActualCechH1Comparison.lean
[bridge-input]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/CombinedAtomH1Input.lean
[bridge-classes]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/CombinedAtomSpecifiedObstruction.lean
[bridge-integral]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/IntegralReflection.lean
[bridge-reflection]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/SpecifiedClassReflection.lean
[bridge-selected-reflection]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/CombinedAtomSpecifiedReflection.lean
[bridge-refinement]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/SelectedReadingRefinement.lean
[bridge-naturality]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/CombinedAtomReadingNaturality.lean
[bridge-condition-c]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/SelectedReadingConditionC.lean
[bridge-examples]: ../../../research/lean/ResearchLean/AG/ObstructionDiagnosticBridge/SelectedFiniteObstructionExamples.lean
[graph-assembly]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/CompleteGeometryGraphAssembly.lean
[graph-direct]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/CompleteGeometryDirectCategory.lean
[four-family-total]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/AATFourFamilyTotalReconstruction.lean
[independent-raw]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentRawLocalValidation.lean
[primitive-fragments]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentFiniteFragments.lean
[primitive-geometry-declaration]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentGeometryPrimitiveDeclaration.lean
[primitive-geometry-assembly]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentGeometryPrimitiveAssembly.lean
[primitive-geometry-fragments]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentGeometryFiniteFragments.lean
[primitive-geometry-category]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentGeometryCategoryReconstruction.lean
[primitive-lens]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentLensPrimitiveReconstruction.lean
[primitive-protocol]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentProtocolPrimitiveReconstruction.lean
[primitive-common]: ../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/IndependentAATPrimitiveReconstruction.lean
