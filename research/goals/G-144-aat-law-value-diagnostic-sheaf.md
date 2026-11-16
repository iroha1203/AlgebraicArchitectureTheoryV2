# G-144-aat-law-value-diagnostic-sheaf — Law値診断の層による幾何学的実現

- `id`: `G-144-aat-law-value-diagnostic-sheaf`
- `status`: `draft`
- `research mode`: `target-theorem`
- `tracking issue`: [#6359（設計）](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6359)。個別のResearch Loop Issueはactive化時に定める。
- 設計: [多項式特殊化ノート: 診断の族](../../docs/note/n1020_shigure_polynomial_specializations.md#diagnostic-family)
- 依存: [G-139 B](G-139-aat-law-coefficient-extension.md#b-同じk0k1からの整数モデル)、[G-140](G-140-aat-independent-realization-descent.md)、[G-141](G-141-aat-semantic-scheme-representability.md)

主経路は[n1019](../../docs/note/n1019_shigure_representability_design.md)のG-149〜G-152にある。
本カードは多項式特殊化を構成する。主経路と同じ対象・射・Law評価への比較を要し、
本カードの達成だけでSHIGURE全体の達成とはしない。

## 研究目的

実現のパラメータによってLaw値の一致関係が変わるK0/K1診断を、実現scheme上の層の複体として
構成する。固定labelの係数拡張に加え、値の合流を含む任意のbase changeと、幾何点で実際に
再生成した診断を同じ構成から比較する。

有限射の層の順像に関する標準定理と、既存のLaw値別の直和分解を使用する。新しい義務は、
原始的なscalar式から有限schemeとその制限を生成し、その幾何stalkを既存K0の値座標へ
同定することである。構成可能層の一般論の新規性を主張することは完了条件に含めない。

## 固定target

### A. 実現上のscalar readoutと有限scheme

量化順は、可換基礎環k、原始表示P、G-141のB=M_P、有限集合S・L、有限supported nerve、
readoutの有限式、可換な診断係数環Λとする。Sは選択した有限readingの値域とし、各chartの
台をSの部分集合として指定する。edgeとfaceの台S_σはK1の交差から生成する。
既存のfinite SourceからSへの全射readingを使う場合は、Lawのadequacyを同じ評価で照合する。

readoutとは、各(ℓ,s)∈L×Sについて、実現のscalar値を読む原始的な有限式を指定することである。
その構文は、kの定数、加法・乗法、有限tensor式で得た自己準同型のtraceから生成する。
n_v=m_vの型では、名前付き生成元が定める基底による演算成分も許す。traceの基底不変性と
成分の変換則からregular function f_{ℓ,s}∈Γ(B,O_B)を構成し、chart変更と両立することを
証明する。一般の基底chart成分を使う場合は、そのchartをBにした同じ構成を用いる。
生成元を忘れるGL作用での不変性と、marked scheme上のregularityを区別する。
required Lawの残差は実現条件によって零になる。readoutの式にはその零条件を課さず、
選択した演算・scalar式の値を読む。Λは診断の加群係数であり、kとは別に指定する。

各cell σとℓについて、同じ式から

```math
Z_{\sigma,\ell}
 =\operatorname{Spec}_B\!\left(
   \mathcal O_B[z]\Big/\Big(\prod_{s\in S_\sigma}(z-f_{\ell,s})\Big)\right),
\qquad p_{\sigma,\ell}:Z_{\sigma,\ell}\longrightarrow B
```

を構成する。空の台では空schemeとする。p_{σ,ℓ}の有限局所自由性を証明し、
S_τ⊆S_σから閉埋め込みZ_{τ,ℓ}→Z_{σ,ℓ}を生成する。制限の恒等・合成と
face incidenceの等式を証明する。これらの構成は、任意のscheme Bと有限個のregular functionに
対する一般形でも述べ、M_Pへの適用で同じfを使う。

### B. 診断複体と幾何stalkの同定

Aのscheme上の定数étale層Λから、次数0–2の複体

```math
\mathscr C^d_{B,\Lambda}
 =\bigoplus_{\dim\sigma=d,\ \ell\in L}
      (p_{\sigma,\ell})_*\underline{\Lambda}_{Z_{\sigma,\ell}}
```

を構成する。微分はAの閉埋め込みによる制限の交代和とし、d¹d⁰=0をincidenceから証明する。
任意の幾何点b̄:Spec Ω→Bについて、Z_{σ,ℓ}の幾何fiberの点を
{f_{ℓ,s}(b̄) | s∈S_σ}へ同定する。同じ値の複数の出現は一つの点に対応させる。

この対応からstalk複体と、値域Ω・係数Λで再生成したK0/K1複体の同型を構成する。
次数別加群だけでなく、両微分・Law値別直和分解を同定する。Λ=ℤではG-139 Bの整数モデル、
Λ=ℚでは既存の`lawGeneratedComplex`との同定を証明する。

stalk同定の量化対象は幾何点である。任意のk代数R上のSem_P(R)とR値のreadoutは
G-140・G-141の実現関手で保持し、このstalk同定から冪零な値の差を復元するとは述べない。

### C. 任意のbase changeと診断係数の変更

任意のscheme射g:B′→Bについて、Aの式を引き戻してZ′とC_{B′,Λ}を構成し、

```math
Z'_{\sigma,\ell}\cong Z_{\sigma,\ell}\times_B B',
\qquad
g^{-1}\mathscr C^\bullet_{B,\Lambda}
 \cong\mathscr C^\bullet_{B',\Lambda}
```

を同じ制限写像に関して証明する。恒等・合成、Bのstalk同定、原始scalar式を保つ
reading代入との可換性を含める。base changeにflatnessは要求しない。

任意の環射Λ→Λ′について、次数別の診断係数変更とK0複体の係数変更を同定し、
C_{B,Λ}の各項のΛ-flatnessから導来tensor積との同定も証明する。
コホモロジーの通常tensor積との交換はG-139 Cの仮定に従って述べる。
幾何側のbase changeと、固定labelでの診断係数の変更を別の可換図式で特定する。

### D. 等値partitionによる有限層別化

各ℓについてSのpartition π_ℓを取り、同じblock内のf_{ℓ,s}−f_{ℓ,t}を零、
異なるblock間の差を可逆にするlocally closed部分scheme B_πを生成する。
有限個のB_πがBの点集合を分割することを証明する。

B_π上では、Bの複体が、πとK1の台から生成した有限自由Λ加群の定数複体と同型になることを示す。
したがってΛが体なら各stalkコホモロジーの次元は有限層別化上で一定となる。
ここでの構成可能性は、この明示された有限層別化と有限自由定数複体によって述べる。
普遍scalar座標を持つA^{L×S}_ℤ上でもA–Dを構成し、任意のfの族がそのpullbackとなることを証明する。

### W. 同じパラメータ上での検査

ノートのbase/delta台帳と同じB=A²_{k,(λ,μ)}上で、3 chartと4 sourceを固定する。
sourceのchart台は{0,1}、{1,2}、{2,0}、{0,1,2}、readoutは順に0、λ、0、μとする。
ambient nerveは3頂点のfull 2-skeletonとし、edge・faceの台はK1から生成する。
A–Dの同じ構成で、V(λ)∩D(μ)上と原点での値座標・微分・stalk同定を証明する。
H¹の変化はG-145の同じ入力で評価する。

Λ=ℤ・ℚの両方を発火させる。さらにk=ℚ、R=k[ε]/(ε²)で、同じBのR値点
(λ,μ)=(0,0)と(0,ε)を指定し、全頂点sourceのreadoutのR値での差と
幾何点への評価後の一致を同時に証明する。

## 前提・構成台帳

| 対象 | 役割 | 出所・構成義務 | 使用先 |
| --- | --- | --- | --- |
| k、P、独立なSemとB=M_P | 入力・先行構成 | G-140・G-141の同じ実現と普遍対象 | A・W |
| S、L、chart台・face incidence | 入力として保持 | A。K1のedge・face台は交差から生成 | A・B・D |
| readout有限式 | 入力として保持 | A。required Lawの零残差と役割を分ける | A・W |
| regular function、有限scheme、閉埋め込み | 構成・証明義務 | Aの有限式と台包含 | B–D |
| 診断係数ΛとΛ→Λ′ | 入力として保持 | A・C。幾何側の基礎環射とは別に指定 | B–D |
| 有限順像のstalk公式・base change | 既存数学 | [Stacks 59.55.2–3](https://stacks.math.columbia.edu/tag/03QN)。有限性はAで証明 | B・C |
| 整数K0複体・Law値別直和分解 | 先行構成 | G-139 B、`ResolutionInvariance/LawValueBlockDecomposition` | B |
| 同じstalk・微分・係数変更の比較 | 構成・証明義務 | B・C。比較同型を入力として受け取らない | B–D |
| 有限層別化と定数複体の同定 | 構成・証明義務 | Dの等値条件とK1 | D |
| Wの同一familyと冪零値 | 構成・証明義務 | Wの原始入力 | A–Dの適用 |

## 完了条件

A–D・WをLeanで証明し、生成されたscheme、層、stalk、微分、base changeと
既存K0/K1宣言の対応を`research/reports/G-144-aat-law-value-diagnostic-sheaf.md`に記す。
証拠は`research/lean/ResearchLean/AG/`に置き、
[共通完了基準](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)を適用する。
定理名の存在に加え、Wの同じ原始入力がA–Dを通ることを完了判定に用いる。

固定主張が偽の場合は、Aの入力を満たす具体例、破れる同型・可換図式・層別化条項を示し、
その不成立を証明して`target-refuted`として決着させる。肯定形の主定理の証明完了とは区別する。
étale層や有限順像の形式化APIの不足は、固定主張の反例として扱わない。
