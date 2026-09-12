# G-122-aat-full-geometry-normalization — 完全幾何における生成比較の正規化と変更の持ち上げ

- `id`: `G-122-aat-full-geometry-normalization`
- `status`: `active`
- `research mode`: `target-theorem`
- `tracking issue`: [#4485](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4485)
- `source note`: [n1013 §1・§2・§4–§6](../../docs/note/n1013_aat_full_geometry_normalization_design.md)、[n1010 §7.1・§9.5](../../docs/note/n1010_aat_post_annapurna_conjectures_research_plan.md)

## 研究目的

AATの生成された比較を、完全幾何の可逆比較と冪等正規化として構成し、
正規化後の比較を保つ変更の持ち上げと、正規化によって失われる変更を決定する。
G-116のcellごとの比較をG-118の生成geometryへ接続し、G-119の正規化関手と
G-120の比較群の一般論を、同じ完全幾何の射に適用する。

これはn1010のS4に対応する一つの研究目標である。A–Dを一つの主定理の構成部分とし、
固定する生成経路と結論を保ちながら、補題の分け方や実装方法を探索する。

## 固定target

任意のAtom carrier `U` と既存宣言に必要なuniverseを量化し、
`[DecidableEq U.Atom]` を用いる。Atom carrierの有限性や自己同型の有限supportは仮定しない。
`E_geom = GeomReadCategory U`、coreへの投影を `ρ = geometryProjection`、
底への投影を `π = packageProjection`、係数の写像を `κ` と書く。
数式の合成順は `gf=g∘f` とする。Leanの `f ≫ g` はこの `gf` に対応する。

B–Dの共通入力は、次の順に量化する。

| 入力 | 意味 |
| --- | --- |
| `A : AuthoredBCDatumSquare U` | G-116の有限表示、実現されたBC square、authoredなdiagnosticデータ |
| `z : A.context.Category` | 有限離散supportのcell。`P_z := A.context.supportPackage z.as` |
| `ω : DefectCochain A.toTransportData` | 既存の選択子が読むcochain |
| `k : Type v`、`[CommRing k]` | 両経路で固定する係数環 |
| `g_z : FixedCoefficientGeometryAt P_z k` | 元のcore上のselected geometryとraw restriction data |

一般の `ω` について構成し、必ず生成cochain
`ω := initialRawDefectCochain A.toTransportData` にも適用する。
全cellについては `∀ z, FixedCoefficientGeometryAt P_z k` を与えて構成をまとめる。
以下では組み立てた `g_z.package` も `g_z` と略記する。
元のsquareとcoreの端点を、選択されたsource pointを含めて次の向きで書く。

\[
\begin{array}{ccc}
\mathrm{NW}&\xrightarrow{\pi_2}&\mathrm{NE}\\
{\scriptstyle\pi_1}\downarrow&&\downarrow{\scriptstyle\sigma_2}\\
\mathrm{SW}&\xrightarrow{\sigma_1}&\mathrm{SE},
\end{array}
\qquad D_z=(\pi_2)_!(\pi_1)^*P_z,\quad
V_z=(\sigma_2)^*(\sigma_1)_!P_z.
\]

`α_z : D_z ≅ V_z` はG-116のcanonical mate、`β_z=E_z α_z` は同じG-116のraw比較とする。
既存の選択条件を

\[
\chi_z:=\bigl(\omega(z)\ne1\bigr)\land
\mathrm{CanonicalObjectNormalizationAdmissible}(P_z)
\]

と書く。`E_z` は、support上で `χ_z` が成立するとcanonical正規化、
成立しなければ恒等を取り、via-base経路で運ぶ既存の射である。
接続はcellごとに行い、元の全diagnostic vertexが同一fiberにあることや、
指定rootからの到達性を入力へ加えない。

次の既存宣言を接続先とする。詳細な参照表はn1013 §6にある。

| 対象 | 既存宣言・所在 |
| --- | --- |
| 完全幾何の圏と射 | [GeometryTransport/Categories.lean](../lean/ResearchLean/AG/GeometryTransport/Categories.lean) の `GeomReadCategory`、`GeometryTotalHom` |
| canonical正規化 | [BCAuthoredCanonicalObjectNormalization.lean](../lean/ResearchLean/AG/DoctrineFiberProduct/BCAuthoredCanonicalObjectNormalization.lean) の `CanonicalObjectNormalizationAdmissible`、`canonicalObjectNormalizationTotal` |
| G-116の可逆比較 | [BCAuthoredSupportCanonicalMate.lean](../lean/ResearchLean/AG/DoctrineFiberProduct/BCAuthoredSupportCanonicalMate.lean) の `authoredSupportCanonicalMate` |
| G-118の生成比較 | [UpperGeometryCompatibleMateNaturality.lean](../lean/ResearchLean/AG/DoctrineFiberProduct/UpperGeometryCompatibleMateNaturality.lean) の `generatedCompatibleUpperGeometryMateAt` |
| exact refinementの資格 | [RefinementBaseChange/Qualification.lean](../lean/ResearchLean/AG/DoctrineFiberProduct/RefinementBaseChange/Qualification.lean) の `realizedReflection_ofExact` |
| 固定例 | [IdempotentExchangeWitnessPacket.lean](../lean/ResearchLean/AG/DoctrineFiberProduct/IdempotentExchangeWitnessPacket.lean) の `finiteAxisFold_idempotentExchange_witnessPacket` |
| 正規化と比較の圏 | [NormalizationCategory.lean](../lean/ResearchLean/AG/RealizationComparisonIdempotents/NormalizationCategory.lean)、[CanonicalNormalizationRestriction.lean](../lean/ResearchLean/AG/ComparisonInformationLoss/CanonicalNormalizationRestriction.lean) のG-119・G-120の構成 |

### A. 完全幾何のcanonical正規化と関手

任意の `G : GeometryPackage U` と
`adm : CanonicalObjectNormalizationAdmissible G.core` に対して、
完全幾何の射 `n_G:G→G` を構成し、

\[
n_G^2=n_G,\qquad
\rho(n_G)=\mathrm{canonicalObjectNormalizationTotal}(G.\mathrm{core},adm),
\qquad\pi\rho(n_G)=1,\quad\kappa(n_G)=1
\]

を証明する。係数とSupport・Axis・Observableの比較写像を恒等から構成し、
coverage、overlap、raw compatibility、読取り則、自然性を含む全fieldを証明する。
等式は `GeometryTotalHom` 全体の等式とする。

admissibleなcoreを持つgeometryの充満部分圏を `C_geom` とする。
任意の `f:G→H` in `C_geom` について片側吸収 `n_H f n_G=f n_G` を証明する。
対象をlabel付きの `(G,n_G)`、射をすべてのsandwich射
`h=n_H h n_G`、恒等射を `n_G` とする圏への正規化関手

\[
N_{geom}(G)=(G,n_G),\qquad N_{geom}(f)=f n_G
\]

を構成する。関手則、充満性、底・係数への投影の保持、G-119のcore正規化との可換性を
証明し、G-119のKaroubi対象・射と比較群の構成へ接続する。
ここで固定する一般の射の法則は片側吸収であり、Bでは実生成経路について可換性を求める。

### B. G-116とG-118の生成mateの一致

元のsquareのpointed exact homに沿う完全幾何の関手 `h_!`、`h^*` を構成し、
既存core関手への投影、射への作用、恒等・合成、単位・余単位の同型と係数恒等を証明する。
既存のcanonicalなgeometry transport・cleavageを使って、

\[
G_z=(\pi_2)_!(\pi_1)^*g_z,\qquad
H_z=(\sigma_2)^*(\sigma_1)_!g_z,\qquad
Q_z=(\sigma_1)_!P_z,\quad q_z=(\sigma_1)_!g_z
\]

を生成する。G-118の `RefinementBCConfiguration` を次の値から構成する。

| field | 値 |
| --- | --- |
| `sOnePrime` | SWのdoctrine |
| `sOne`、`bottom` | SEのdoctrine |
| `sTwo` | NEのdoctrine |
| `fst` | `(𝟙 SE).doctrineHom` |
| `snd` | `σ₂.doctrineHom` |
| `refinement` | `exactToRefinement σ₁.doctrineHom` |
| target core package | `Q_z` |

compatible source pointを元のsquareから作り、選択点を含むrefinementを
`PointedRefinementHom.ofExact σ₁` と対応させ、active conditionを
`realizedReflection_ofExact σ₁` から放電する。生成pullbackの比較

\[
\mathrm{SW}\times_{\mathrm{SE}}\mathrm{NE}\cong\mathrm{NW},\qquad
\mathrm{SE}\times_{\mathrm{SE}}\mathrm{NE}\cong\mathrm{NE}
\]

を選択点・cleavageまで含めて構成する。この比較に沿った記法で、G-118の生成mateは

\[
m_z:B_z\to T_z,\qquad
B_z=(\pi_1)^*(\sigma_1)^*q_z,\quad
T_z=(\pi_2)^*(\sigma_2)^*q_z
\]

となる。必要な `UpperGeometryCompatibleProblemInputData` のroot・path・edge・comparatorを
含む全データを `q_z` から内部構成し、`m_z` を既存の
`generatedCompatibleUpperGeometryMateAt` と一致させる。

上記pullback・cleavage比較を挿入して、単位・余単位による端点同型

\[
a_z:G_z\xrightarrow{\sim}(\pi_2)_!B_z,
\quad a_z=(\pi_2)_!(\pi_1)^*(\eta^{\sigma_1}_{g_z}),\qquad
b_z:(\pi_2)_!T_z\xrightarrow{\sim}H_z,
\quad b_z=\varepsilon^{\pi_2}_{H_z}
\]

を構成する。完全幾何の可逆比較 `\bar\alpha_z:G_z≅H_z` について

\[
\bar\alpha_z=b_z\,(\pi_2)_!(m_z)\,a_z,\qquad
\rho(\bar\alpha_z)=\alpha_z,\quad\kappa(\bar\alpha_z)=1
\]

を証明する。投影等式は、同時に生成する `ρ(G_z)≅D_z`、`ρ(H_z)≅V_z` に沿って述べる。
G-116の異なる単位・余単位によるcanonical mateと、この式の一致自体を構成・証明義務とする。

`P_z` がadmissibleなら、この実際のexact transportに沿うadmissibility保存と

\[
h_!(n_G)=n_{h_!G},\qquad h^*(n_H)=n_{h^*H},\qquad
n_{H_z}\bar\alpha_z=\bar\alpha_z n_{G_z}
\]

を、射の等式に必要なcleavage比較を含めて証明する。

### C. 同じ生成比較の因子化・非可逆性・像

`g_z` 上で `χ_z` に従って `n_{g_z}` または恒等を取り、via-base経路で運んで
`\bar d_z:H_z→H_z` を生成する。次を構成・証明する。

\[
\rho(\bar d_z)=E_z,\quad\bar d_z^2=\bar d_z,\quad\kappa(\bar d_z)=1,
\qquad\bar e_z=\bar\alpha_z^{-1}\bar d_z\bar\alpha_z,\quad
\bar\beta_z=\bar d_z\bar\alpha_z,\quad\rho(\bar\beta_z)=\beta_z.
\]

`\bar e_z²=\bar e_z`、`\bar\beta_z\bar e_z=\bar\beta_z=\bar d_z\bar\beta_z` を示し、
実際の射 `\bar\beta_z` を持つKaroubi同型 `(G_z,\bar e_z)≅(H_z,\bar d_z)` とその逆射を構成する。
投影をG-116の既存Karoubi同型、比較の圏での位置をG-119の構成と一致させる。
Bの輸送則から、`χ_z` が成立すると `(\bar e_z,\bar d_z)=(n_{G_z},n_{H_z})`、
成立しなければ両方が恒等であることと、分類

\[
\operatorname{IsIso}(\bar\beta_z)
\quad\Longleftrightarrow\quad\bar d_z=1
\quad\Longleftrightarrow\quad\neg\chi_z
\]

を証明する。canonical正規化の非単射性は既存の
`canonicalObjectNormalization_not_injective` から得る。

必須の具体例は `finiteAxisFoldBCDatumSquare`、その生成cochain、cell `second`、係数 `ℤ` とする。
その元のcore上にgeometry・raw dataを構成し、同じ生成経路の `\bar\beta_z` が非同型であることを示す。
geometry・raw dataの選択は構成に任せる。firingとadmissibilityは既存の
`finiteAxisFold_idempotentExchange_witnessPacket` から放電し、同じ例で入力族の非空性を示す。

### D. 比較を保つ変更のsection・核・反映の分類

raw比較を可逆な `c:=\bar\alpha_z`、像の比較を
`a:=\bar\beta_z:(G_z,\bar e_z)≅(H_z,\bar d_z)` と固定する。
`Γ_c` は `vc=cu` を満たす端点自己同型対 `(u,v)` の群とする。
`Γ_a` も同様に定め、像の自己同型群は `Kar(E_geom)` で取る。

中心化群とambientな準同型を

\[
H^{\mathrm{cent}}=
\operatorname{Cent}_{\operatorname{Aut}(G_z)}(\bar e_z)\times
\operatorname{Cent}_{\operatorname{Aut}(H_z)}(\bar d_z),\qquad
\Gamma_c^{\mathrm{cent}}=H^{\mathrm{cent}}\cap\Gamma_c,
\]
\[
r:H^{\mathrm{cent}}\longrightarrow
\operatorname{Aut}(G_z,\bar e_z)\times\operatorname{Aut}(H_z,\bar d_z),
\qquad (u,v)\longmapsto(\bar e_z u\bar e_z,\bar d_z v\bar d_z)
\]

として構成する。比較の保存を証明して制限準同型 `\bar r:Γ_c^cent→Γ_a` を作り、
群準同型のsection `s:Γ_a→Γ_c^cent`、`\bar r s=id` を構成する。
反映については、ambientな逆像を使って

\[
r^{-1}(\Gamma_a)=\Gamma_c^{\mathrm{cent}}
\quad\Longleftrightarrow\quad\neg\chi_z,\qquad
r^{-1}(\Gamma_a)=H^{\mathrm{cent}}\cap\Gamma_{\bar\beta_z}
\]

を証明する。右の等式は同じ `\bar\beta_z` との両立を表し、左のraw比較 `c` の反映と区別する。

次に `P_z` がadmissibleなとき、Aのcanonical関手から全自己同型群上の準同型

\[
r_N:\operatorname{Aut}(G_z)\times\operatorname{Aut}(H_z)\longrightarrow
\operatorname{Aut}(N_{geom}G_z)\times\operatorname{Aut}(N_{geom}H_z),
\qquad (u,v)\longmapsto(N_{geom}u,N_{geom}v)
\]

を作る。比較の保存と、制限準同型 `\bar r_N:Γ_c→Γ_{N_geom(c)}` の群準同型のsectionを構成し、
`r_N⁻¹(Γ_{N_geom(c)})≠Γ_c` を証明する。結論を次の三つの場合で確定する。

| 正規化 | 比較の保存 | 比較の反映 | 比較を保つ変更の持ち上げ |
| --- | --- | --- | --- |
| G-116の選択子、`¬χ_z` | 成立 | 成立 | 群準同型のsectionを持つ |
| G-116の選択子、`χ_z` | 成立 | 不成立 | 群準同型のsectionを持つ |
| canonical `N_geom`、`P_z` admissible | 成立 | 不成立 | 群準同型のsectionを持つ |

最後の場合はcochainに依存しない。底 `πρ` への写像が恒等である自己同型の部分群でも、
その内部の中心化群と対応する像の群を使い、同じ三つの場合を証明する。
すべてのsectionは、入力の両端自己同型それぞれの底・係数写像を保持する。

各制限準同型 `\bar r`、`\bar r_N` の分裂短完全列と、各liftのfiber上での
その制限準同型の核による自由かつ推移的な作用をG-120に接続する。
反映が不成立となる各入力に対して、source端点の準同型の核に完全幾何自己同型 `τ≠1` を構成する。
底・係数写像を恒等にし、中心化群版では `τ\bar e_z=\bar e_zτ` も示す。
対 `(τ,1)` が正規化後の比較を保ち、元の `c` とは両立しないことを評価する。
このambientな核の対と、liftのfiberに作用する制限準同型の核を区別する。

## 前提・構成台帳

| 対象・対応条項 | 役割 | 必要な構成・証拠 | 出所・使用先 |
| --- | --- | --- | --- |
| 任意carrierと `A,z,ω,k,g_z`（B–D） | 入力として保持 | 共通入力の実評価と生成cochainへの適用 | 元のG-116データからcellごとのgeometryと比較へ |
| canonical admissibility（A・B・D） | 一般定理の仮定 | Aの正規化、Bの輸送保存、Dのcanonical版 | coreの対象条件から完全幾何の射・関手・群へ |
| 選択条件 `χ_z`（C・D） | 入力から定まる場合分け | Cの二つの冪等射の同定と分類、Dの反映判定 | 既存cochainとadmissibilityから同じ生成比較の像へ |
| 完全幾何の正規化・transport・単位・余単位（A・B） | 構成・放電義務 | A・Bの全field、関手則、投影等式 | 元のgeometry・raw dataから完全な射と吸収へ |
| exact-derived G-118入力とactive condition（B） | 構成・放電義務 | Bの構成表、選択点、内部入力、pullback・cleavage比較 | 元squareと `realizedReflection_ofExact` から実生成mateへ |
| 端点同型・mate一致・正規化の輸送（B） | 構成・放電義務 | Bの実経路と完全幾何の等式 | 単位・余単位とG-118の生成mateからG-116との一致、C・Dへ |
| 選択子・因子化・Karoubi同型（C） | 構成・放電義務 | Cの同じ射の像・投影・非可逆性の分類 | A・BとG-116の既存射からG-119の比較の圏へ |
| section・非自明な核・反映・fiber（D） | 構成・放電義務 | Dの全群と底を固定する群での全結論 | 完全幾何の端点自己同型からG-120の分裂・作用へ |
| 固定finite axis-fold例（C） | 構成・放電義務 | Cの元core上のgeometry、firing・admissibility、生成射の非同型性 | 既存witnessと同じcellから一般分類の実例・非空性へ |

完成済みのgeometry hom、mate一致、sectionなどの結論相当のfieldを、上の入力へ追加しない。

## 完了条件

A–Dの全称命題とCの固定例をすべてLeanで構成・証明し、同じ生成射の投影・因子化・比較群を
名前付き宣言で接続する。Cの非可逆性とDの反映不成立は、証明すべき結論の一部とする。
それ以外の固定主張への反例は共通の反証停止規則で扱う。

新規Lean成果物は `research/lean/ResearchLean/AG/` に置く。条項と宣言の対応、
G-116・G-118・G-119・G-120への使用経路、前提と構成の出所、完全幾何での投影等式、
固定例と核の元の評価、参照する既存宣言と版を
`research/reports/G-122-aat-full-geometry-normalization.md` に記録する。

[共通基準の参照適用](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)
による監査・独立最終レビューを完了判定に適用する。
承認・適用版・放電状況・検証・査読・active化の記録はtracking Issueとreportに置く。
