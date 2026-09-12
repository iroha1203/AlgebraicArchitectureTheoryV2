# n1013: 完全幾何の正規化と変更の持ち上げ — S4の事前設計

[n1010 §7.1・§9.5](n1010_aat_post_annapurna_conjectures_research_plan.md) のS4を、
一つのtarget-theorem GOALへ切り出すための設計である。研究目標を次に置く。

> AATの生成された比較を、完全幾何の可逆比較と冪等正規化として構成し、
> 正規化後の比較を保つ変更の持ち上げと、正規化によって失われる変更を決定する。

以下のA–Dを一つの主定理の構成部分とする。入力、接続する既存の射、結論は固定し、
補題の分け方や構成の実装は探索に残す。新しい主張はすべて**未証明の定理候補**である。
参照したLean sourceの型・定義との照合と、独立した端点・構成案の点検を行った段階であり、
新規Lean宣言の型検査やGOALの完了判定は行っていない。

## 1. 共通入力をcellごとに固定する

任意のAtom carrier `U` と必要なuniverseを固定する。既存のG-116と同じ
`[DecidableEq U.Atom]` を用い、Atom carrierの有限性は要求しない。入力は次とする。

| 入力 | 意味 |
| --- | --- |
| `A : AuthoredBCDatumSquare U` | G-116の有限表示、実現されたBC square、authoredなdiagnosticデータ |
| `z : A.context.Category` | 有限離散supportのcell。`P_z := A.context.supportPackage z.as` |
| `ω : DefectCochain A.toTransportData` | 既存の選択子が読むcochain |
| `k : Type v`、`[CommRing k]` | 両経路で固定する係数環 |
| `g_z : FixedCoefficientGeometryAt P_z k` | 元のcore上のselected geometryとraw restriction data |

一般の `ω` について構成し、生成比較への適用では必ず
`ω := initialRawDefectCochain A.toTransportData` とする。全cellの主張は
`∀ z, FixedCoefficientGeometryAt P_z k` を与えて上の構成をまとめる。
以下では、このデータから組み立てた `g_z.package` も `g_z` と略記する。

元のsquareを次の向きで書く。記号はdoctrineだけでなく、選択されたsource pointを
含む対応するfiberを表す。

\[
\begin{array}{ccc}
\mathrm{NW}&\xrightarrow{\pi_2}&\mathrm{NE}\\
{\scriptstyle\pi_1}\downarrow&&\downarrow{\scriptstyle\sigma_2}\\
\mathrm{SW}&\xrightarrow{\sigma_1}&\mathrm{SE}.
\end{array}
\qquad
D_z=(\pi_2)_!(\pi_1)^*P_z,\quad
V_z=(\sigma_2)^*(\sigma_1)_!P_z.
\]

G-116の `α_z : D_z ≅ V_z` はcanonical mateであり、対象とするraw比較は
`β_z = α_z ≫ E_z` である。以降、数式の積は通常の合成順 `gf=g∘f` を使う。
既存の選択子の条件を

\[
\chi_z := \bigl(\omega(z)\ne1\bigr)\ \land\
 \mathrm{CanonicalObjectNormalizationAdmissible}(P_z)
\]

と書く。support上の射は `χ_z` が成立するとcanonical正規化、成立しなければ恒等である。

**接続する対象はこのcellごとの比較である。** G-116は全diagnostic vertexが同一fiberに
あることや、指定rootからの到達性を仮定していない。元のdiagnostic全体をG-118のroot付き
source diagramへそのまま代入することはしない。各 `g_z` から必要なG-118入力を内部構成する。
元の全edge・全comparatorにわたる二段transportの同定は、n1010 §7.3の後続課題である。

## 2. 一つの主定理を構成する四つの部分

### A. canonical正規化を完全幾何で構成する

任意の `G : GeometryPackage U` と
`adm : CanonicalObjectNormalizationAdmissible G.core` に対して、
次の完全幾何の射を構成する。

\[
 n_G:G\to G,\qquad n_G^2=n_G,\qquad
 \rho(n_G)=\mathrm{canonicalObjectNormalizationTotal}(G.\mathrm{core},adm),
 \qquad \kappa(n_G)=1.
\]

`ρ` はgeometryからcoreへの投影、`κ` は係数の写像である。
`n_G` のcontext・Atom・equation・axisの添字写像は恒等なので、係数と
Support・Axis・Observableの比較写像を恒等から構成する。coverage、overlap、
raw compatibility、読取り則、自然性をすべて証明し、最後に `GeometryTotalHom` の
等式として冪等性を示す。完成済みの `GeomReadHom` を入力fieldに置かない。

admissibleなcoreを持つgeometryの充満部分圏を `C_geom` とする。
`C_geom` の任意の射 `f:G→H` に対し、片側吸収

\[
 n_H f n_G=f n_G
\]

を証明する。これにより、対象を `(G,n_G)`、射をすべてのsandwich射とする圏への
正規化関手 `N_geom` を構成する。射の作用は `N_geom(f)=f n_G` であり、
底と係数への投影、G-119のcore正規化との可換性、充満性を証明する。
Karoubiの対象・射と比較群にはG-119の構成を使う。

ここで任意の射 `f` に対する `n_H f=f n_G` は要求しない。
G-117の反例が示すように、object写像の可換性だけでは完全な射の可換性にならない。

### B. G-116とG-118を実際の生成経路で接続する

G-116の経路を完全幾何へ持ち上げ、元の `g_z` から

\[
 G_z=(\pi_2)_!(\pi_1)^*g_z,\qquad
 H_z=(\sigma_2)^*(\sigma_1)_!g_z
\]

を生成する。ここでgeometry上の `h_!`、`h^*` は構成すべき関手である。
既存のcanonicalなgeometry transport・cleavageを使い、coreの関手への投影等式、
射への作用、恒等・合成、単位・余単位の完全幾何での同型と係数恒等を証明する。

G-118の入力は、元のsquareから次のexact refinementとして作る。
`σ₁`、`σ₂`、`𝟙 SE` は選択点を含む射であり、表の `fst`・`snd`・`refinement` には
そのdoctrine成分を使う。

| `RefinementBCConfiguration` のfield | 構成する値 |
| --- | --- |
| `sOnePrime` | SWのdoctrine |
| `sOne`、`bottom` | SEのdoctrine |
| `sTwo` | NEのdoctrine |
| `fst` | `(𝟙 SE).doctrineHom` |
| `snd` | `σ₂.doctrineHom` |
| `refinement` | `exactToRefinement σ₁.doctrineHom` |
| target core package | `Q_z := (σ₁)_! P_z` |

compatible source pointを元のsquareから作り、選択点を含むrefinementを
`PointedRefinementHom.ofExact σ₁` と対応させる。そのactive conditionを既存の
`realizedReflection_ofExact σ₁` で放電する。target geometryを `q_z := (σ₁)_!g_z` とする。
生成pullbackと元のsquareの比較

\[
 \mathrm{SW}\times_{\mathrm{SE}}\mathrm{NE}\cong\mathrm{NW},\qquad
 \mathrm{SE}\times_{\mathrm{SE}}\mathrm{NE}\cong\mathrm{NE}
\]

を、選択点とcleavageの比較まで含めて構成する。この同型に沿った記法では、
G-118の生成mate `m_z:B_z→T_z` は次の完全幾何の二対象の間にある。

\[
 B_z=(\pi_1)^*(\sigma_1)^*q_z,\qquad
 T_z=(\pi_2)^*(\sigma_2)^*q_z.
\]

必要な `UpperGeometryCompatibleProblemInputData` は、生成したtarget geometryを使う
singleton presentationから内部構成できる見込みがある。root、path、edge、comparatorの
各fieldもここで構成する。別の実装としてpointwiseな `upperGeometryMate` から出発してよいが、
最終的に既存の `generatedCompatibleUpperGeometryMateAt` と一致させる。

`m_z` の同型性だけではG-116のmateとの一致は出ない。新しく構成する端点同型を

\[
 a_z:G_z\xrightarrow{\sim}(\pi_2)_!B_z,
 \quad a_z=(\pi_2)_!(\pi_1)^*(\eta^{\sigma_1}_{g_z}),
 \qquad
 b_z:(\pi_2)_!T_z\xrightarrow{\sim}H_z,
 \quad b_z=\varepsilon^{\pi_2}_{H_z}
\]

と書く。式には上記pullback・cleavage比較を挿入する。
完全幾何の可逆比較 `\bar\alpha_z` を構成し、

\[
 \bar\alpha_z=b_z\,(\pi_2)_!(m_z)\,a_z,
 \qquad \rho(\bar\alpha_z)=\alpha_z,\qquad
 \kappa(\bar\alpha_z)=1
\]

を証明する。`ρ(G_z)≅D_z`、`ρ(H_z)≅V_z` も生成し、それに沿って投影等式を述べる。
既存G-116のmateは異なる単位・余単位の展開を持つため、**mateの一致が中心的な新規義務**になる。
G-118の既存endpoint isoはG-114とG-118の比較であり、ここで必要な同型を代替しない。

さらに、`P_z` がadmissibleなら、この実際のexact transportに沿うadmissibility保存と

\[
 h_!(n_G)=n_{h_!G},\qquad h^*(n_H)=n_{h^*H},\qquad
 n_{H_z}\bar\alpha_z=\bar\alpha_z n_{G_z}
\]

を証明する。射の等式に必要なcleavage比較も含める。
任意のpackage同型に沿うadmissibility保存や、任意の射との可換性を仮定する方法は使わない。

### C. 同じ生成比較の因子化・非可逆性・像を決定する

`g_z` 上で既存の選択条件 `χ_z` に従って `n_{g_z}` または恒等を取り、
via-base経路で運んで `\bar d_z:H_z→H_z` を生成する。次を構成する。

\[
 \rho(\bar d_z)=E_z,\quad \bar d_z^2=\bar d_z,\quad\kappa(\bar d_z)=1,
 \qquad
 \bar e_z=\bar\alpha_z^{-1}\bar d_z\bar\alpha_z,\quad
 \bar\beta_z=\bar d_z\bar\alpha_z,\quad \rho(\bar\beta_z)=\beta_z.
\]

完全幾何で `\bar e_z²=\bar e_z` と
`\bar\beta_z\bar e_z=\bar\beta_z=\bar d_z\bar\beta_z` を示し、
実際の射 `\bar\beta_z` を持つKaroubi同型

\[
 (G_z,\bar e_z)\cong(H_z,\bar d_z)
\]

を構成する。投影はG-116の既存Karoubi同型、比較の圏での位置はG-119と一致させる。
Bの輸送則から、`χ_z` が成立すると `(\bar e_z,\bar d_z)=(n_{G_z},n_{H_z})`、
成立しなければ両方が恒等となることを示す。従って次を目標にする。

\[
 \operatorname{IsIso}(\bar\beta_z)
 \quad\Longleftrightarrow\quad \bar d_z=1
 \quad\Longleftrightarrow\quad \neg\chi_z.
\]

非可逆性の具体例には、G-116の `finiteAxisFoldBCDatumSquare`、生成cochain、
cell `second` を保つ。係数を `ℤ` とし、その元のcore上にgeometry・raw dataを構成して、
同じ生成経路で `\bar\beta_z` が非同型であることを示す。firingとadmissibilityを仮定として
残さず、既存の具体例で放電する。S4で固定する入力族が空でないことも、この例で示す。

### D. 比較を保つ変更のliftと反映を判定する

この部分でraw比較として固定するのは可逆な `c:=\bar\alpha_z` である。
`a:=\bar\beta_z:(G_z,\bar e_z)≅(H_z,\bar d_z)` を像の比較とする。
`Γ_c` は `vc=cu` を満たす端点自己同型対 `(u,v)` の群である。
像の自己同型群は `Kar(GeomReadCategory U)` で取る。

まずn1010 §4.1の中心化群版を完全幾何に適用する。

\[
 H^{\mathrm{cent}}=\operatorname{Cent}_{\operatorname{Aut}(G_z)}(\bar e_z)
  \times\operatorname{Cent}_{\operatorname{Aut}(H_z)}(\bar d_z),
 \quad \Gamma_c^{\mathrm{cent}}=H^{\mathrm{cent}}\cap\Gamma_c,
\]
\[
 r:H^{\mathrm{cent}}\longrightarrow
 \operatorname{Aut}(G_z,\bar e_z)\times\operatorname{Aut}(H_z,\bar d_z),
 \qquad (u,v)\longmapsto(\bar e_z u\bar e_z,\bar d_z v\bar d_z).
\]

`r` を比較群へ制限した `\bar r:Γ_c^cent→Γ_a` について、
**群準同型のsection** `s:Γ_a→Γ_c^cent`、`\bar r s=id` を構成する。
反映は `r⁻¹(Γ_a)=Γ_c^cent` という別の主張として判定する。

次に `P_z` がadmissibleなとき、Aのcanonical関手を全自己同型群へ適用し、
`r_N:(u,v)↦(N_geom(u),N_geom(v))` と
`\bar r_N:Γ_c→Γ_{N_geom(c)}` を使う。ここでもsectionを構成し、反映を判定する。
期待する結論を次に固定する。

| 対象とする正規化 | 比較の保存 | 比較の反映 | 比較を保つ変更のlift |
| --- | --- | --- | --- |
| G-116の選択子、`¬χ_z` | 成立 | 成立 | 群準同型のsectionを持つ |
| G-116の選択子、`χ_z` | 成立 | 不成立 | 群準同型のsectionを持つ |
| canonical `N_geom`、`P_z` admissible | 成立 | 不成立 | 群準同型のsectionを持つ |

最後の行はcochainと無関係にcanonical正規化を施すため、選択子が恒等の行とは異なる。
底 `πρ` への写像が恒等である自己同型の部分群も扱う。
中心化群版では全群内／底を固定する群内の中心化群、canonical版では全群／底を固定する群で、
それぞれこの表を証明する。
sectionは入力自己同型の底・係数写像を保持する構成にする。

sectionから、各制限準同型の分裂短完全列と、各liftのfiber上の核の自由かつ推移的な作用を
G-120に接続する。反映が不成立となる行では、端点の準同型の核に実際の非恒等な
完全幾何自己同型を構成し、比較と両立しない対を示す。
これは自己同型群の準同型の分裂であり、G-116が否定したraw圏内での冪等射自体の分裂とは別の命題である。

比較の取り違えを防ぐため、中心化群版では次の等式も明記する。

\[
 r^{-1}(\Gamma_a)=H^{\mathrm{cent}}\cap\Gamma_{\bar\beta_z}.
\]

`\bar\beta_z` 自身のsandwich条件からこの等式が出るので、これだけを反映の成功とは数えない。
問うのは、右辺が元の可逆比較の `Γ_c^cent` と等しいかどうかである。

## 3. sectionと非自明な核を構成する道筋

Dの全射性は、Aの充満性からは従わない。候補となる追加の構成を次のように絞る。
この節は証明方針であり、同じ入力と結論を保つ別の構成を探索してよい。

固定したadmissibleな `G` について、`ArchitectureObject` の定義から

\[
 \mathrm{ArchitectureObject}(U)\cong
 \mathrm{AtomConfiguration}(U)\times\mathcal D,
 \qquad
 \mathcal D=\sum_{S:\mathrm{Type}\ u}\sum_{Q:\mathrm{Type}\ u}(S\times Q)
\]

を作れる。`d(C)∈𝒟` をpackageの選択対象の付加データ、`d₀∈𝒟` を固定した基準とし、
`t_C` を `d₀` と `d(C)` の交換とする。
正規化像の自己同型 `b` が誘導するAtom同値を `σ` として、raw対象上の作用を

\[
 F_\sigma(C,d)=
 \bigl(C.\mathrm{transport}\,\sigma,
 t_{C.\mathrm{transport}\,\sigma}(t_C(d))\bigr)
\]

と置く。これは選択対象を保つ配置ごとの共役作用であり、`t_C²=id` から合成則を証明する。
sandwich条件とobject formationの法則を使い、`b(A)=n_G(F_σ(A))` を示す。
operationの出力を、admissibilityの型等式

\[
 \mathrm{Op}(F_\sigma A,F_\sigma B)
 =\mathrm{Op}(n_GF_\sigma A,n_GF_\sigma B)
\]

の逆向きのcastで戻す。equation transportのcontext・equation等の計算データは保持し、
objectMapに依存するresidual則を再証明する。operation naturality、invariant、coordinateの
法則も再構成する。geometryはcontext等の計算データを保って構成し、係数と三つの局所比較を保持する。

これにより、次のsectionを目指す。

\[
 s_G:\operatorname{Aut}_{Kar(C_{geom})}(G,n_G)
 \longrightarrow\operatorname{Cent}_{\operatorname{Aut}(G)}(n_G),
 \qquad r_Gs_G=\mathrm{id}.
\]

castを含む群則、逆射、完全幾何の等式まで証明する必要がある。
底が恒等なら `σ=id` となり、同じ構成を底を固定する部分群へ制限できる。
sectionは固定した `G` と付加データの同一視に相対的であり、異なるgeometry間の自然性は要求しない。

非自明な核は、同じconfiguration上で、選択された対象以外の二対象を交換することで構成する。
三つの異なる付加データを先に構成すれば、選択対象を避ける二つを選べる。
既存の「同じconfiguration上の異なる二対象」だけではこの二つを確保したことにならない。
operationは同様のcastで運び、底・係数・局所比較を恒等にして、
`k≠1`、`kn_G=n_Gk`、`N_geom(k)=1` を完全幾何で示す。

固定した可逆比較 `c:G≅H` に対しては、sourceのlift `s_G(u)` と
`c s_G(u)c⁻¹` を組にして比較群のsectionを作る。sourceの核の元 `k≠1` を使う
対 `(k,1)` は正規化後に比較を保ち、元の `c` とは両立しない。
この構成が中心化条件と底の資格を保つことをBの輸送則から証明する。
任意の非可逆比較への同じ結論は、この構成からは主張しない。

## 4. 入力と構成義務を分ける

| 項目 | 分類 | 扱い |
| --- | --- | --- |
| `A,z,ω,k,g_z` | `data` | §1の元データ。geometry上の完成済み射は含まない |
| `CanonicalObjectNormalizationAdmissible P` | `direction-hypothesis` | canonical版の対象条件。選択子版では条件分岐に使い、具体例では放電する |
| exact refinementのactive condition | `discharge-required` | 元squareと `realizedReflection_ofExact` から構成 |
| geometryの正規化、transport、単位・余単位 | `discharge-required` | coverageから局所比較の自然性まで証明 |
| endpoint iso、mate一致、投影一致 | `discharge-required` | 元の生成経路と既存の名前付き射へ接続 |
| admissibilityのtransport保存、正規化との可換性 | `discharge-required` | 実際に用いるexact transportについて証明 |
| section、非自明な核、反映の成否 | `discharge-required` | 全群・底を固定する群の両方で証明 |
| finite axis-foldのgeometryと非可逆な生成比較 | `discharge-required` | 元のcore・生成cochain・cellを維持して構成 |

G-121の有限decoderは先行成果として接続可能だが、S4のgeometryをdecoderの像に限定する
根拠にはしない。任意carrier上の全自己同型を扱うDには、有限support制約を加えない。
表示から有限コードを計算する問題と、独立な実現圏の構成はS5で扱う。

## 5. GOALカードと実行単位

カードの題名案は **「完全幾何における生成比較の正規化と変更の持ち上げ」** とする。
固定targetには§1の入力、A–Dの結論、必須の具体例、下の完了・停止条件を書く。
§3の付加データによる構成や、module・補題・PRの分割はこの設計ノートと実行reportで扱う。

初期の探索は、同じGOAL内で次の順に進めるのがよい。

1. 任意のadmissible geometry上の `n_G` を構成し、完全な射として冪等性・吸収を証明する。
2. exact-derived G-118入力の端点を実装し、G-116のmateとの一致を先に調べる。
3. geometryの経路・投影・正規化の輸送を統合し、同じfinite axis-foldで因子化を確認する。
4. endpoint自己同型のsectionと核を構成し、同じ比較の群に適用してA–Dを閉じる。

各段の成果は小さなproof obligationやPRにできる。Aだけの成功、一般群論への適用、
型検査の成功はGOAL全体の完了にはしない。

**完了条件**は、A–Dの全称命題と固定例が名前付きLean宣言でつながり、
入力fieldへ移された構成義務がなく、既存G-116・G-118・G-119・G-120へのproof-useが追えること。
最終的な宣言・前提・公理・投影・依存の確認と、Math 2本・Lean 2本の独立最終査読を行う。

**停止条件**は、固定入力と結論の型不整合、またはA–Dの固定命題への具体的な反証である。
必要なgeometry homやmate一致がまだ作れないだけなら未証明として探索を続ける。
反証が得られた場合は該当する入力・成分・式を固定し、目標を弱めて証明済みとはしない。
命題や入力族の改訂は、その反証を示したうえで別の判断として行う。

## 6. 既存成果との接続点

| 役割 | 参照するsource | ここで新しく必要なこと |
| --- | --- | --- |
| geometryの射の全field | [GeometryTransport/Categories](../../research/lean/ResearchLean/AG/GeometryTransport/Categories.lean)、[raw transport](../../research/lean/ResearchLean/AG/GeometryTransport/Basic.lean) | Aの射・吸収の完全な等式 |
| canonical正規化の条件 | [BCAuthoredCanonicalObjectNormalization](../../research/lean/ResearchLean/AG/DoctrineFiberProduct/BCAuthoredCanonicalObjectNormalization.lean) | geometryへの持ち上げ、実際のtransportでの保存 |
| G-116の入力・mate | [BCRelativeSchema](../../research/lean/ResearchLean/AG/DoctrineFiberProduct/BCRelativeSchema.lean)、[BCAuthoredSupportCanonicalMate](../../research/lean/ResearchLean/AG/DoctrineFiberProduct/BCAuthoredSupportCanonicalMate.lean) | 元の端点と完全幾何の端点の一致 |
| exact mateの展開 | [CoreBeckChevalleyMate](../../research/lean/ResearchLean/AG/DoctrineFiberProduct/CoreBeckChevalleyMate.lean)、[単位・余単位の同型性](../../research/lean/ResearchLean/AG/DoctrineFiberProduct/PackageProjectionBeckChevalleyExactness.lean) | BのG-118生成mateとの一致 |
| G-118の入力・生成geometry | [UpperGeometryCompatibleInput](../../research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleInput.lean)、[UpperGeometryCleavage](../../research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCleavage.lean)、[exact qualification](../../research/lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/Qualification.lean) | exact-derived入力とpullback比較の内部構成 |
| G-118の同型比較 | [UpperGeometryCompatibleMateNaturality](../../research/lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleMateNaturality.lean)、[QualifiedComparisonFixedDecision](../../research/lean/ResearchLean/AG/DoctrineFiberProduct/QualifiedComparisonFixedDecision.lean) | 同じ生成射をBの式で使用 |
| G-116の選択子・非可逆性 | [IdempotentExchangeTransportIdentityClassification](../../research/lean/ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeTransportIdentityClassification.lean)、[IdempotentExchangeWitnessPacket](../../research/lean/ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeWitnessPacket.lean) | Cの完全幾何版と同じ生成例 |
| G-119の正規化関手 | [CanonicalNormalizationAbsorption](../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/CanonicalNormalizationAbsorption.lean)、[NormalizationCategory](../../research/lean/ResearchLean/AG/RealizationComparisonIdempotents/NormalizationCategory.lean) | 全geometry homについての吸収と投影一致 |
| G-120の反映・liftの一般論 | [CanonicalNormalizationRestriction](../../research/lean/ResearchLean/AG/ComparisonInformationLoss/CanonicalNormalizationRestriction.lean) | DのAATでのsection・核・成否の決定 |
| raw対象の付加データ | [ArchitectureObject](../../Formal/AG/Atom/ArchitectureObject.lean)、[SignedExactCoreReadingHom](../../Formal/AG/ReadingFunctoriality/Core.lean) | §3の自己同型を全fieldまで構成 |

G-119・G-120・G-121の完了は先行定理の使用を可能にする。S4で未構成のgeometryの射や
新しいsectionが存在する証拠は、ここで列挙した新規義務の証明によって得る。
