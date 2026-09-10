# G-120-aat-comparison-information-loss — 観測・正規化による比較情報の保存と損失

- `id`: `G-120-aat-comparison-information-loss`
- `status`: `active`
- `research mode`: `target-theorem`
- `tracking issue`: [#4443](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4443)
- `source note`: [n1010 §3–4・§9.3](../../docs/note/n1010_aat_post_annapurna_conjectures_research_plan.md)

## 研究目的

係数観測と冪等正規化が比較情報をどう変えるかを、比較を維持する変更の部分群、
その観測核、変更の持ち上げとして記述する。一般的な判定定理をG-118の生成比較と
G-119のcanonical正規化へ接続し、情報損失を具体的な元と作用で示す。
G-118の非因子化を、観測核・比較保存部分群・基点付き剰余類による表示変更に整合する
構造として説明し、生成比較で失われる相対差の全体を片側端点の係数不可視自己同型として分類する。
これにより、後続の有限表示と完全幾何のliftが保持・復元すべき比較情報を特定する。
これはn1010のS2に対応する。

## 固定target

圏の射には通常の合成記法 `gf = g ∘ f` を用いる。Leanの `f ≫ g` は `gf` に対応する。
一般の群・圏には任意のuniverseを許す。AATへの適用は既存宣言のuniverseに従い、
Atom carrierの有限性は要求しない。

### A. 観測だけで適合性を判定できる必要十分条件

任意の群 `Q,R`、群準同型 `O:Q→R`、部分群 `Γ≤Q` に対し、
`K=ker O`、`L=K∩Γ` と置く。次を証明する。

\[
\bigl(\exists h:R\to\mathrm{Prop},\ \forall q\in Q,\quad
q\in\Gamma\iff h(Oq)\bigr)
\iff K\le\Gamma,
\qquad O^{-1}(O(\Gamma))=\Gamma K.
\]

ここで像・逆像・積は元の集合として読み、右の積が部分群になることも示す。
`O`の全射性は要求しない。

任意の `γ∈Γ` に対し、`O⁻¹({Oγ})=γK` と `(γK)∩Γ=γL` を証明する。
`L`を`K`の部分群として左剰余類集合 `K/L` と基点 `L` を構成し、
`k∈K` に対して `γk∈Γ` と `kL=L` を同値にする。
この基点付き集合が一点であることと、上の判定可能性を同値にする。
`L`の正規性は要求せず、`K/L`は剰余類集合として扱う。

さらに任意の群同型 `φ:Q≃Q'`、`ψ:R≃R'` と `O':Q'→R'`、`Γ'≤Q'` が
`O'φ=ψO`、`φ(Γ)=Γ'` を満たすとき、核・交わりの群同型と
基点付き集合 `K/L≃K'/L'` を構成する。元 `kL` の像を `φ(k)L'` とし、
観測fiberとその適合部分の輸送、恒等・合成との整合を証明する。

### B. G-118の生成比較への適用と表示変更への整合

任意の `U`、`ctx : ActiveRefinementBCContext U`、`P : FiniteTransportPresentation`、
`k : CommRingCat`、`I : UpperGeometryCompatibleProblemInputData ctx P k`、`i : P.Vertex`
を量化する。`c := I.generatedCompatibleUpperGeometryMateAt i` の生成された両端を
`X,Y` とし、既存の `CompositeFiberAut`、`qualifiedComparisonSubgroup`、
`CompositeFiberAut.coefficientObservation` から

\[
Q_c=\operatorname{CompositeFiberAut}(X)\times\operatorname{CompositeFiberAut}(Y),
\quad \Gamma_c=\operatorname{qualifiedComparisonSubgroup}(c),
\quad \Gamma_c\hookrightarrow Q_c\xrightarrow{O_c}R_c
\]

を構成する。`R_c`は両端の係数環の自己同型群の直積、`O_c`は既存の係数観測の直積とする。
この図式へAを適用し、`K_c=ker O_c`、`L_c=K_c∩Γ_c` とその剰余類集合を得る。
両端の底を固定する資格は既存の合成投影によるものとし、`c`自身の底への像には
恒等性を要求しない。

各生成比較について、既存の `generatedCompatibleUpperGeometryMateAt_isIso` から
同型 `c:X≅Y` を得る。その実係数写像から係数環の同型を構成し、両端の観測を
`O_X,O_Y`、その核を `K_X^obs,K_Y^obs` とする。比較による既存の共役群同型
`T_c:CompositeFiberAut(X)≃CompositeFiberAut(Y)` と係数環の同型による共役 `S_c` が
`O_Y T_c=S_c O_X` を満たすことを実係数成分で証明し、核上の群同型
`T_c:K_X^obs≃K_Y^obs` を得る。`T_c`のunderlying射は通常の合成記法で `cbc⁻¹` とする。
このとき、同じ端点対を保つ同定として

\[
K_c=K_X^{\mathrm{obs}}\times K_Y^{\mathrm{obs}},\qquad
L_c=\{(b,T_c(b))\mid b\in K_X^{\mathrm{obs}}\}
\]

を証明する。群演算の積・逆元を用いて基点付き集合の同値

\[
\Psi_c:K_c/L_c\simeq K_Y^{\mathrm{obs}},\qquad
[(b,p)]\longmapsto p\,T_c(b)^{-1},\qquad
u\longmapsto[(1,u)]
\]

を構成する。代表元によらないこと、両逆、基点 `L_c` と恒等元 `1` の対応を証明する。
ここでも左辺は左剰余類集合として扱う。この分類とAを接続し、生成比較について
観測だけで適合性を判定できることと `K_Y^obs={1}` を同値にする。

固定例は `UpperDecisionWitness` の `fixedCoefficientObservation`、
`fixedPositiveQualifiedPair`、`fixedNegativeQualifiedPair` を用いる。
これらをそれぞれ `O_*`、`q₊`、`q₋` とし、同じ生成比較に対して

\[
q_+\in\Gamma_*,\qquad q_-\notin\Gamma_*,\qquad O_*(q_+)=O_*(q_-),
\qquad k_*:=q_+^{-1}q_-\in K_*\setminus\Gamma_*
\]

を証明する。`k_*L_*≠L_*` を示し、Aの必要十分条件から既存の
`fixedQualifiedDecision_not_factor_through_coefficientObservation` と同じ非因子化結論を導く。
さらに `Ψ_*(k_*L_*)≠1` を上の同値の評価式から証明する。
正負対と比較は上記の既存生成器で固定し、新しい例への置換はしない。

[G-118 C1s](G-118-aat-diagnostic-descent-transport.md)で固定された任意の入力表示変更に対し、
変更後の入力から再生成された比較を用いて上の図式を運ぶ群同型を構成する。
両端への射影、係数観測、`K_c,L_c`、基点付き剰余類の移送を一致させ、
恒等・逆・型の合う有限合成との整合を証明する。係数環の同一視は生成された端点同型の
係数成分から得る。輸送先の比較は既存の入力再構成と生成器から得て、その比較との
整合を証明する。

生成された端点同型による群同型を `θ_X,θ_Y`、変更後比較を `c'` とするとき、
`θ_Y T_c=T_{c'} θ_X` を証明する。上記の観測図式から得る核の同型への制限の下で、
`θ_X×θ_Y` が誘導する剰余類同値を `φ̄` とし、
`Ψ_{c'} φ̄=(θ_Y|K_Y^obs) Ψ_c` を証明する。
この同定も恒等・逆・型の合う有限合成と整合させる。

### C. 冪等像への変更の保存・反映・持ち上げ

任意の圏 `E`、対象 `X,Y`、比較 `c:X→Y`、射 `e:X→X`、`d:Y→Y` について
`e²=e`、`d²=d`、`dc=ce` を仮定し、`a=dce:(X,e)→(Y,d)` を `Kar(E)` の比較とする。
この条項では `Γ_c={(b,p)∈Aut(X)×Aut(Y) | pc=cb}` を全端点自己同型群内で定め、
`Γ_a`も `Kar(E)` の全端点自己同型群内で同様に定める。

\[
H=\operatorname{Cent}_{\operatorname{Aut}(X)}(e)
\times\operatorname{Cent}_{\operatorname{Aut}(Y)}(d),\qquad
\Gamma_0=H\cap\Gamma_c
\]

と置き、`Γ₀`を`H`の部分群として扱う。群準同型

\[
r:H\longrightarrow
\operatorname{Aut}_{\operatorname{Kar}(E)}(X,e)
\times\operatorname{Aut}_{\operatorname{Kar}(E)}(Y,d),\qquad
r(b,p)=(ebe,dpd)
\]

を構成する。各像の逆射は `eb⁻¹e`、`dp⁻¹d` とし、以下を証明する。

1. 比較の保存 `r(Γ₀)⊆Γ_a` と、制限準同型 `r̄:Γ₀→Γ_a`。
2. 反映の必要十分条件
   \[
   r^{-1}(\Gamma_a)=\Gamma_0
   \iff \bigl(\ker r\le\Gamma_0\ \land\
   r(\Gamma_0)=\Gamma_a\cap\operatorname{im}r\bigr).
   \]
3. 任意の `t∈Γ_a` について、適合するraw変更へのliftが存在することと
   `t∈r(Γ₀)` の同値。非空fiber `r̄⁻¹({t})` に、`ker r̄`の右乗法による
   自由かつ推移的な作用を構成する。`r(Γ₀)=Γ_a` の場合に
   `1→ker r̄→Γ₀→Γ_a→1` が短完全列になることを証明する。

一般反例は有限集合の圏で以下の二例に固定する。各例の冪等性、両立式、
中心化条件または像の自己同型条件を、その具体的写像から証明する。

| 固定データ | 証明する結論 |
| --- | --- |
| `X=Y={0,1,2}`、`c=id`、`e=d`は定値0、`b`は1と2の交換、`p=id` | `(b,p)∈H`、`(b,p)∉Γ₀`、`r(b,p)∈Γ_a`。元の比較式の不一致を点で評価し、反映の失敗を示す |
| `X=Y={0,1,2}`、`c=id`、`e=d`は `0↦0,1↦1,2↦1`、`a=e` | 像の2点 `0,1` の交換を両端に持つ `t∈Γ_a` を構成し、`t∉im r` を証明する。大きさ1と2のfiberを交換するraw置換が存在しないことから、すべての候補に対するlift非存在を示す |

### D. G-119のcanonical正規化への接続

G-119 Dのadmissibleなcore圏 `C`、像の圏 `N_C`、正規化関手 `N:C→N_C`、
底への投影 `πV`、`π_N` を用い、任意の `U`、`P,Q:C`、`c:P→Q` を量化する。
既存の `normalizationEndpointAutomorphismHom` を

\[
r_N:\operatorname{Aut}_C(P)\times\operatorname{Aut}_C(Q)
\to\operatorname{Aut}_{N_C}(P)\times\operatorname{Aut}_{N_C}(Q)
\]

として用いる。raw比較群を`Γ_c`、像の比較群を`Γ_{N(c)}`とし、条項Cの反映の必要十分条件を
`r_N,Γ_c,Γ_{N(c)}`について証明する。適合するliftの像、制限準同型の各非空fiberの
核による右作用、全射の場合の短完全列も同様に構成する。

比較の保存はG-119の正規化関手と誘導準同型へ接続する。対象のadmissibility以外に、
端点自己同型や`c`が正規化と可換する条件は追加しない。

底を固定する場合は、raw側では`πV`、像側では`π_N`によって両端のhomがそれぞれの
底の恒等射へ送られる全自己同型対の群を `Q_base`、`R_base` とする。
その間への制限 `r_base:Q_base→R_base` を構成する。
`Γ_base=Q_base∩Γ_c`、`Δ_base=R_base∩Γ_{N(c)}` をそれぞれの比較保存部分群とし、
`r_base`をさらに制限した `r̄_base:Γ_base→Δ_base` を構成する。
既存の `normalizationBaseQualifiedComparisonSubgroupHom` との一致は、
同じunderlying端点対を保つ部分群の同定の下で、この `r̄_base` に要求する。

反映の必要十分条件は全底資格群上で
`r_base⁻¹(Δ_base)=Γ_base` と
`ker r_base≤Γ_base ∧ r_base(Γ_base)=Δ_base∩im r_base` の同値として証明する。
適合するliftの像は `r_base(Γ_base)` とし、非空fiberの核による右作用と
全射の場合の短完全列は `r̄_base` について証明する。

この条項は判定条件とfiber構造を確定する。AATの生成された完全幾何の正規化についての
反映・lift全射性の成立判定は、n1010 S4の固定入力と持ち上げ構成において扱う。

## 前提・構成台帳

| 対象・対応条項 | 役割 | 必要な構成・証拠 | 出所・使用先 |
| --- | --- | --- | --- |
| 任意の群準同型・部分群（A） | 入力として保持 | Aの必要十分条件・fiber・剰余類 | 群の法則から観測による判定可能性へ |
| 群同型と可換図式（A） | 一般定理の仮定 | Aの輸送と整合 | 核・交わり・基点付き剰余類の移送へ |
| G-118の生成入力とC1s表示変更（B） | 既存入力として保持 | Bの実図式とその輸送は構成義務 | 既存の入力再構成・生成器・端点同型からAの適用へ |
| 生成比較の同型性・共役（B） | 既存構成として使用し、接続を放電する義務 | Bの係数観測との可換式、核のグラフ、ΨとC1s整合 | 既存の生成比較のIsIso定理と共役群同型から、失われる相対差全体の分類へ |
| G-118の固定正負対（B） | 構成・放電義務 | Bの同一観測、適合・非適合、核内の元、非基点性 | QualifiedComparisonCoefficientNonfactorizationの固定例からAの非因子化へ |
| 比較・冪等対・両立式（C） | 一般定理の仮定 | Cの準同型・保存・反映条件・lift | 中心化群とKaroubiの射から核・像・fiberへ |
| 3点集合の二例（C） | 構成・放電義務 | Cの各行の全条件と評価・非存在証拠 | 具体的写像から一般的反映・lift全射性の失敗へ |
| packageのadmissibility（D） | 入力として保持（対象条件） | G-119 Dの対象とcanonical正規化 | 任意のadmissibleな端点と任意のtotal射を扱う |
| G-119のN・投影・誘導準同型（D） | 既存構成として使用 | Dの全群版とqualified版への接続 | G-119の関手性・底への投影一致から保存と判定条件・fiber構造へ |

## 完了条件

A–DをすべてLeanで構成・証明する。Bの固定された情報損失とCの二つの有限反例は、
証明すべき結論の一部とする。それ以外の固定主張への反例は共通の反証停止規則で扱う。

新規Lean成果物は `research/lean/ResearchLean/AG/` に置く。条項と宣言の対応、
既存構成からの使用経路、固定witnessの評価、使用した既存宣言と参照版を
`research/reports/G-120-aat-comparison-information-loss.md` に記録する。

[共通基準の参照適用](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)
による監査・独立最終レビューを完了判定に適用する。
承認・適用版・放電状況・検証・査読・active化の記録はtracking Issueとreportに置く。
