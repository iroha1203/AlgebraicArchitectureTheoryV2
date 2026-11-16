# G-145-aat-diagnostic-collision-geometry — 診断値の合流と構成可能関数の実現

- `id`: `G-145-aat-diagnostic-collision-geometry`
- `status`: `draft`
- `research mode`: `target-theorem`
- `tracking issue`: [#6359（設計）](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6359)。個別のResearch Loop Issueはactive化時に定める。
- 設計: [多項式特殊化ノート: 値の合流の幾何](../../docs/note/n1020_shigure_polynomial_specializations.md#collision-geometry)
- 依存: [G-144](G-144-aat-law-value-diagnostic-sheaf.md)

主経路は[n1019](../../docs/note/n1019_shigure_representability_design.md)のG-149〜G-152にある。
本カードは多項式特殊化を構成する。主経路と同じ対象・射・Law評価への比較を要し、
本カードの達成だけでSHIGURE全体の達成とはしない。

## 研究目的

Law値の合流によってK0の座標集合が変わるとき、診断のコホモロジーが保たれる条件と、
類が生じる・失われる理由をsourceの台から決定する。さらに、原始的な有限source・K1・
scalar式という制約の下で実現できるH¹の変動を分類する。

Mayer–Vietoris完全列、構成可能層の一般論、pseudo-coherent複体のfiberコホモロジーの
上半連続性は既存数学として使用する。本カードの追加義務は、実際の値の合流をこれらの
写像へ同定し、任意の基本locally closed集合と有限な非負整数値構成可能関数を、
K0/K1の原始入力から実現することである。この制約内での実現定理を標的とし、
一般の構成可能関数の実現や新規性の確定を成果の前提にしない。

## 固定target

### A. 合流によるcochain mapと特殊化

G-144の有限source S、readout L、supported nerve、診断係数Λを固定し、値の一致関係を
表すpartition πからπ′への粗化を量化する。型・source・台・incidenceは保持する。
各Law値aについて、台S_σがaを持つsourceと交わるcell全体をK_aとし、
K_aのcell選択の閉性をK1から証明する。

既存のLaw値別分解と同じ同型で、診断を⊕_a C⁎(K_a;Λ)へ分解する。
π′の一つのblockへ合流するπのblock族について、その新しい部分複体が元のK_aの合併となる
ことを証明する。同じcellの値labelへの商写像から、cochain map

```math
r_{\pi',\pi}:C^\bullet(\pi';\Lambda)
       \longrightarrow C^\bullet(\pi;\Lambda)
```

を生成する。向きは合流後から合流前への制限とする。次数別の単射性、微分との可換性、
恒等・合成を証明する。

G-144のregular readoutの族と幾何点の特殊化η̄→s̄について、ηの等値partitionがsの
等値partitionを細分することを証明する。生成されたr_{π_s,π_η}を、G-144の層の
stalk間の写像C_s→C_ηへ同定し、同じ幾何点におけるK0複体との比較を可換にする。

### B. 二値合流の完全列と必要十分条件

一つのLawで二つの値だけが合流する場合を取り、その部分複体をK_a、K_b、
合併をU、交差をIとする。Aのrと制限の差から短完全列

```math
0\longrightarrow C^\bullet(U;\Lambda)
 \xrightarrow{r}C^\bullet(K_a;\Lambda)\oplus C^\bullet(K_b;\Lambda)
 \xrightarrow{\rho}C^\bullet(I;\Lambda)\longrightarrow0
```

を原始cellから生成する。所属の包含と完全性を証明し、交差と合併を表す証明済み複体を使って
標準の長完全列を構成する。ρ_iをρのHⁱへの誘導写像としたとき、

```math
\ker H^1(r)\cong\operatorname{coker}\rho_0,
\qquad
\operatorname{coker}H^1(r)\cong\operatorname{im}\rho_1
```

を、長完全列の同じ写像に関して証明する。従ってH¹(r)が同型であることと、
ρ₀が全射かつρ₁が零であることの同値を得る。交差が空の場合も量化に含める。
Λが体の場合は核・余核の次元を同じ写像のrankで表す。

### C. 同時合流と順序の整合

任意の有限block族の同時合流について、元のK_aの全ての有限交差からMayer–Vietorisの
複体を生成し、合併のcochain複体を計算する比較を証明する。各次数の完全性は
cell所属から導き、交差のコホモロジーから合併を計算するspectral sequenceへ接続する。

同じπ→π′を二値合流の列へ分解する全ての順序について、合成されたcochain mapが
Aの同じr_{π′,π}に一致することを証明する。Bの長完全列を反復した計算と同時合流の
比較が同じ端点・同じ誘導写像を持つことを示す。途中の核・余核や直和分解そのものの
順序独立性は要求せず、全体の写像とその核・余核の同定を完了対象とする。

### D. 原始入力による構成可能関数の実現

任意の可換環k、有限表示affine scheme B=Spec A、有限個のg₁,…,g_r,h∈Aを量化する。
有限source・固定nerve・scalar readoutから、全幾何点b̄と全係数体Λについて

```math
\dim_\Lambda H^1(C_{\bar b,\Lambda})
 =\mathbf 1_{V(g_1,\ldots,g_r)\cap D(h)}(b)
```

となる入力を構成する。構成はn=max(3,r+1)頂点のcycle、各辺にだけ属するsource、
全頂点に属する一sourceから作る。cycleの辺のreadoutを0,g₁,…,g_rとし、余った辺には0を置く。
全頂点sourceのreadoutはhとする。ambient nerveはn頂点のfull 2-skeletonとし、
edge・faceの台をK1から生成する。

この入力の各Law値部分複体が、cycleの部分グラフまたはfull 2-skeletonになることを証明し、
上の等式を導く。r=0、空のlocally closed集合、h=0、単元hも同じ定理で扱う。
判定結果やH¹の次元を原始入力のfieldに含めない。

さらに、有限個のregular functionの零・非零条件による有限層別化上で一定であり、
有限な値域を持つ任意の関数β:|B|→ℕを量化する。Dの基本構成の有限直和から
dim_Λ H¹(C_{b̄,Λ})=β(b)を構成する。これを本カードでの非負整数値構成可能関数の実現とする。

Bの有限表示の生成元・関係から、rank 1・一生成元の型とunary演算、required多項式Lawを持つ
Pを生成し、M_P≅Bを構成する。g_iとhのreadoutも同じ演算の有限式から生成する。
多項式代表の変更がLawによって同じreadoutを与えることを証明し、G-144の層の構成へ接続する。

### E. H¹が下降するfamilyとpseudo-coherent実現の不存在

Wのk=ℚ、Λ=ℚについて、全点bで

```math
\dim_{\kappa(b)}H^1(E\otimes^{\mathbf L}_{\mathcal O_B}\kappa(b))
 =\dim_{\mathbb Q}H^1(C_{\bar b,\mathbb Q})
```

を満たすpseudo-coherentなO_B複体Eが存在しないことを証明する。WをV(λ)へ制限した
familyで、μ≠0からμ=0への特殊化によりH¹の次元が1から0へ下降することを用いる。
perfect複体の不存在も帰結として述べる。対象は上式で指定したderived fiberによる
全点同時実現であり、G-144の定数係数étale層の複体は同じfamilyを実現する。

### W. 同一familyでの生成・消失・合流写像

ノートのbase/delta台帳と同じB=A²_{k,(λ,μ)}を使う。3 chart、台{0,1}、{1,2}、{2,0}、
{0,1,2}の4 source、順に0、λ、0、μというreadout、full 2-skeletonを固定する。
G-144 Wと同じ入力をDへ通し、全点で

```math
\dim_\Lambda H^1(C_{\bar b,\Lambda})=1
\quad\Longleftrightarrow\quad \lambda(b)=0\ \text{かつ}\ \mu(b)\ne0
```

を証明する。それ以外の点での次元は0とする。kは任意の体、Λは独立に選ぶ任意の係数体とする。
V(μ−1)上のλ→0ではH¹が生じ、V(λ)上のμ→0ではH¹が消失することを、
Bの同じr、ρ₀、ρ₁とその核・余核で説明する。係数を変えても成立する同じincidence計算を使う。

## 前提・構成台帳

| 対象 | 役割 | 出所・構成義務 | 使用先 |
| --- | --- | --- | --- |
| 有限source・readout・supported nerve・Λ | 入力として保持 | G-144 A、A | A–C |
| partitionの粗化 | 入力として保持 | A。source・台・incidenceを保持 | A–C |
| Law値別直和分解 | 先行構成 | `ResolutionInvariance/LawValueBlockDecomposition`、`LawValueBlockCohomology` | A・D |
| 合流mapとstalk間の写像の一致 | 構成・証明義務 | A、G-144 B–D | B・C・W |
| cellのMayer–Vietoris完全列 | 既存成果と適用義務 | `AtlasGluingWidth/MayerVietoris`。対象と写像をBへ同定 | B・C |
| 合流の核・余核と必要十分条件 | 構成・証明義務 | Bの同じ長完全列 | B・W |
| Bの有限表示、g_i、h、β | Dの入力 | D。係数関数を有限式に表示 | D |
| cycle・全頂点source・K1とそのH¹ | 構成・証明義務 | Dの原始生成 | D・W |
| finite表示Bを表現するrank 1のP | 構成・証明義務 | D、G-140・G-141への同じ入力 | DからG-144への接続 |
| pseudo-coherent fiberの上半連続性 | 既存数学 | [Stacks 0BDI](https://stacks.math.columbia.edu/tag/0BDI) | E |
| H¹の下降と全点同時実現の不存在 | 構成・証明義務 | Wの同じfamilyとEの上式 | E |

## 完了条件

A–E・WをLeanで証明し、`research/reports/G-145-aat-diagnostic-collision-geometry.md`に
原始sourceからの生成、合流mapの方向、完全列の各写像、Dの一般構成、Eの不存在証明を対応づける。
証拠は`research/lean/ResearchLean/AG/`に置き、
[共通完了基準](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)を適用する。
有限個の有理数incidence計算・rank検算は、Dの任意入力についての証明を代替しない。

固定主張が偽の場合は、対象条項の入力条件を満たす具体例と破れる等式・完全性・実現条件を
原始入力から示し、不成立を証明して`target-refuted`として決着させる。
Eは指定された全点同時実現の不存在を証明する肯定形の義務である。
その義務への反証には、WでEの上式を満たすpseudo-coherent複体の具体的構成と証明を要する。
いずれも肯定形の全主定理の証明完了とは区別する。
