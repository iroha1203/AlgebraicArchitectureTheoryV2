# G-146-aat-semantic-lift-and-repair-comparison — Lawから生成する実現の持ち上げと修復の比較

- `id`: `G-146-aat-semantic-lift-and-repair-comparison`
- `status`: `draft`
- `research mode`: `target-theorem`
- `tracking issue`: [#6359（設計）](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6359)。個別のResearch Loop Issueはactive化時に定める。
- 設計: [多項式特殊化ノートの実現の持ち上げと修復](../../docs/note/n1020_shigure_polynomial_specializations.md#semantic-lift)
- 依存: [G-139](G-139-aat-law-coefficient-extension.md)、[G-140](G-140-aat-independent-realization-descent.md)、[G-141](G-141-aat-semantic-scheme-representability.md)、[G-142](G-142-aat-shigure-reading-naturality.md)

主経路は[n1019](../../docs/note/n1019_shigure_representability_design.md)のG-149〜G-152にある。
本カードは多項式特殊化を構成する。主経路と同じ対象・射・Law評価への比較を要し、
本カードの達成だけでSHIGURE全体の達成とはしない。

## 研究目的

原始Lawの式から、独立に定義した実現の変更・持ち上げ・修復を判定する複体と障害類を
構成する。局所的に許される修復、共有する宣言の整合、複数の文脈をまたぐLawの関係を
同じ入力から区別し、指定されたreadingの値を保つ変更の存在と自由度を説明する。

既存のK0/K1はLawの評価値と支持から複体を生成する。本GOALでは式の微分とsyzygyを
追加で生成し、actualな実現の持ち上げとの比較を証明する。scheme表現を固定した
G-141の量化は維持し、本GOALの有限表示・一次の定理をその系として接続する。

## 固定target

### A. 原始Lawからの微分・syzygy・複体

量化順は、可換環k、有限個の演算・Lawを持つノートの原始表示P、k代数R、
x∈Sem_P(R)、k代数の全射R′→Rとそのsquare-zero kernel Mとする。
Lawを忘れた同じ型・階数・生成元・演算の実現をambientとして独立に構成し、
G-141の基底chartから、その表現schemeがk上smoothであることを証明する。
任意のaffine test scheme上のambient liftの存在を、この構成から得る。

各基底chartでB=k[z₁,…,z_n]、原始required Lawの全成分をf₁,…,f_r、J=(f₁,…,f_r)、
A=B/Jとする。原式のsyzygy加群を

```math
S=\left\{s\in B^r\mid\sum_i s_i f_i=0\right\}
```

として構成し、N=J/J²の表示をS→B^r→Jから導く。R′→RのkernelをR加群として読み、
chartに入るxについて次の複体D_{P,x,M}を生成する。

```math
D^0=M^n\xrightarrow{d^0=\operatorname{Jac}(f)(x)}D^1=M^r
  \xrightarrow{d^1}D^2=\prod_{s\in S}M,
\qquad (d^1r)_s=\sum_i s_i(x)r_i.
```

syzygyの多項式恒等式を微分し、f_i(x)=0を用いてd¹d⁰=0を証明する。
ker d¹≃Hom_R(N⊗_A R,M)も同じ表示から構成する。
全syzygyを原式から作ってからxで評価する。有限生成族への置換では、原式に対する
その生成性と、置換前後のH⁰・H¹の比較を証明する。

### B. 独立な実現の持ち上げと低次数のcotangent比較

実現の持ち上げをLift_P(x,R′)={x′∈Sem_P(R′) | x′|_R=x}として定める。
chart上で任意のambient lift z̃を選び、r_i=f_i(z̃)∈Mを計算する。
r∈ker d¹、r(z̃+δ)=r(z̃)+d⁰δを証明し、選択に依存しない類
o_P(x,R′)∈H¹(D_{P,x,M})を構成する。次を証明する。

```math
o_P(x,R')=0\quad\Longleftrightarrow\quad
\operatorname{Lift}_P(x,R')\ne\varnothing.
```

零性から得た補正を実際の加群・演算・Lawの実現へ戻し、逆方向は実現の差から補正を
得る。非空なlift集合はH⁰(D)のtorsorになる。大域のsmooth ambientをY、M_Pのideal
sheafを𝒥とし、E_x=x*Ω_{Y/k}、N_x=x*(𝒥/𝒥²)をSpec R上の加群として読む。
二項複体D̄_{P,x,M}=[Hom_R(E_x,M)→Hom_R(N_x,M)]を構成し、chart上のDとの
H⁰・H¹の比較と障害類の一致を証明する。G-140のZariski descentとAのambientから、
単一の基底chartに入らないxにもD̄による同じ存在・torsor分類を構成する。

G-141のη_R(x):Spec R→M_Pを介し、i=0,1について

```math
H^i(\overline D_{P,x,M})\simeq
H^i\mathbf R\operatorname{Hom}_R
  (\mathbf Lx^*\mathbb L_{M_P/k},M)
```

を証明する。右辺と上の障害類の対応も対象とする。一般のNのprojectivityは仮定せず、
smooth ambientの余接加群の局所自由性とcotangent complexの次数−1・0の切断を使う。
chart上の比較は[naive cotangent complex](https://stacks.math.columbia.edu/tag/00S0)と
[square-zeroの持ち上げ](https://stacks.math.columbia.edu/tag/08S3)へ接続する。
この同定を全次数の同定へ拡張しない。

Zariski Čech totalizationで右辺の次数0・1を計算する系では、kがNoetherian、Pが有限表示で、
選んだ有限principal affine coverとその交差上の係数が準連接になることを証明する。
Nの有限表示性、Homの局所化、Čech比較の使用箇所を示す。この系の仮定を
G-141の表現可能性またはBのaffine lift存在判定へ移さない。

### C. reading相対の指定されたlift

G-142の原始代入とLaw導出u:P→P′から、ρ=u*:Sem_{P′}→Sem_Pとその微分の比較を
生成する。x∈Sem_{P′}(R)と、指定されたy′∈Lift_P(ρx,R′)について

```math
\operatorname{Lift}_u(x,y')=
\{x'\in\operatorname{Lift}_{P'}(x,R')\mid\rho(x')=y'\}
```

を独立に定める。Law導出からidealの写像、conormalの写像、微分との可換性を構成し、
F_u=Cone(D̄_{P′,x,M}→D̄_{P,ρx,M})[−1]の低次数を得る。
自由Law表示を使う比較では、syzygyの移送と導出の選択に対する独立性を証明する。

sourceのambient liftのLaw残差と、ρによる像とy′の差からo_u(x,y′)∈H¹(F_u)を作る。
o_u=0とLift_u(x,y′)の非空性の同値、および非空な集合へのH⁰(F_u)の自由推移作用を
証明する。恒等・合成、square-zero拡大の射、表示変更とこの比較が整合することも含む。
指定した観測を固定する場合は、その観測の式と指定liftを明示してこの同じ構成を使う。

### D. 合法な局所修復係数と文脈をまたぐsyzygy

有限affine Law f(z)=Lz−b、任意の基準状態p、変更可能域を指定する部分加群Hについて、
独立な修復集合{δ∈H | f(p+δ)=0}を構成する。その非空性を−f(p)∈L(H)で特徴づけ、
非空な修復集合をker(L|_H)のtorsorとして分類する。基準状態と差分を別に保持する。
一般の非線形Lawのsquare-zero修復では、線形部分Lを原始Lawから生成したJacobianに置き換える。

文脈ごとの変更可能域には、指定した変更可能な宣言の集合から生成する座標部分加群を
使う。観測を固定する系では、表示の被覆P_iと観測側の被覆O_iを持ち、原始代入
u_i:O_i→P_iが全ての交差・制限と可換で、各観測式の全参照が対応するP_iに入ることを
要求する。この条件は参照集合と代入式で記述し、出来上がったpresheafの可換性を入力にしない。
全体のuはCで扱い、局所修復へ移す際にこの被覆適合性を使う。
各文脈の合法な修復係数は、そのうち当該文脈のLawと固定する観測を保存する
部分加群として生成する。制限との可換性、局所修復集合への自由推移作用、
matching familyからのactual repairの組立てをG-140の同じ実現上で証明する。
任意の生成元への加法作用を、合法な修復作用として入力しない。

適合しない被覆では、観測方程式を全参照を含む文脈へ置いた合併被覆を構成してから
この系を適用する。k=R=ℚ、R′=ℚ[ε]/(ε²)、a=εとして、T↦X+Yを{X}/{Y}だけへ
分けた場合を反例として固定する。
合法な大域差分(a,−a)を各局所で観測固定した係数0へ制限できず、観測を局所から落とすと
(a,0)まで組み立つことを示す。観測を強めたり弱めたりして同じ修復問題と扱わない。

原始宣言の有限合併被覆について、全ての多重交差を持つČech nerveと、自由な変数変更・
自由Law残差の係数からČech total complex T_rawを生成する。
各宣言を含む文脈の添字はfull simplexを成す。各Lawの全参照が所属文脈に含まれる条件を使い、
宣言支持のincidenceからH⁰(T_raw)≃ker d⁰、H¹(T_raw)≃coker d⁰を構成する。
全大域syzygyから写像Ψを生成し、次の列の完全性とBの障害類の対応を証明する。

```math
0\longrightarrow H^1(D_{P,x,M})\longrightarrow
H^1(T_{\mathrm{raw}})\xrightarrow{\Psi}\prod_{s\in S}M.
```

Ψの全射性は要求しない。実際のambient liftから生じる残差類がker Ψに入り、
その逆像がo_Pであることを示す。複数文脈にまたがるsyzygyもSに含める。
文脈被覆の細分化と、この列およびactual repairの組立てが可換になることを証明する。

既存APIへの接続は次の対象を固定する。

- K0/K1の接続先は[LawGeneratedComplex](../lean/ResearchLean/AG/ResolutionInvariance/LawGeneratedComplex.lean)と
  [GeneratedComparisonMap](../lean/ResearchLean/AG/ResolutionInvariance/GeneratedComparisonMap.lean)のincidence生成。
  式の微分とsyzygyを持つ本複体との対応を別に構成し、値の一致からその同型を置かない。
- SAGAと診断の正の比較は、[G-148](G-148-aat-operational-descent-diagnostic-comparison.md)で
  台帳adapterから生成する同じ修復係数・被覆・実際の障害類を固定する。
  本カードの任意多項式複体とK0/K1の一般同型は要求しない。
- conormalとの接続はEの固定した係数siteと残差写像で行う。

### E. 固定ambient上のconormalと実現liftの比較

全表示Pと基底chartを固定し、B=k[z]、J=(f)をAと同じ原式から作る。
G-140 Aの普遍equation system E_Bと関手j_B:PrincipalOpen(Spec B)→S_P.categoryを使う。
各D(s)でObservable≅B_s、全required Lawが生成するideal I≅J_sを、実際の局所化から証明する。
既存[Raw.shortComplexとshortComplex_shortExact](../../Formal/AG/SemanticRepair/Conormal/LawGeneratedIdealPowerShortExact.lean)を
j_B.opでprecomposeする。これはobjectwiseに完全であり、(J²)_s=(J_s)²からprincipal-open基底上の
標準conormal列と自然同型になることを証明する。その基底から真のZariski層へ延長して
0→J̃/J̃²→O/J̃²→O/J̃→0を得る。一般openの有限生成spanとΓ(U,J̃)をsectionwiseに同一視せず、
principal-openでの同定と層化の比較を証明する。chart変更の同じtensor残差によるideal比較と可換にする。
conormalはこの普遍J/J²を先に作ってから実現xで引き戻す。LawfulなxではG-140 AのE_xの
violation idealは零になるため、そのidealからconormalを作り直して変形障害を消さない。

Spec R上の実現xとambient lift B→R′はJ²を零へ送るので、B/J²→R′を誘導する。
そのJ/J²への制限からκ:J/J²→Mを構成する。κ=0と、その**同じambient lift**が
B/J→R′へ降りることの同値を証明する。ambient liftの差はDer_k(B,M)であり、
κの差はJacobianからの写像Hom_R(E_x,M)→Hom_R(N_x,M)になることを示す。
従ってその余核中の[κ]はBのo_Pと一致し、零性を保存・反映する。
既存[InternalFirstOrderLift](../../Formal/AG/SemanticRepair/Conormal/LawGeneratedSemanticFirstOrderRepair.lean)の
section liftへSem liftを同一視するのでなく、同じconormal列からこの写像を生成する。

宣言V⊂Wの座標環の射B_V→B_Wを、このZariski制限へ逆向きに読み替えない。
V={X}、W={X,Y,XY=id}、k=ℚについて、共有xを保ち(xy−1)を0へ送る
ℚ[x,y]→ℚ[x]が存在しないことを証明し、二つのsiteを混同しない検査例にする。

### W. 同じ構成を通す指定例

ノートのbase・delta台帳と、以下の補助表示を原始入力とする。
次の計算をA–Dの複体、実現、比較写像の同じ構成から得る。

1. R=ℚとして、ノートのp=(1,1)を持つaffine例でc+d=1を扱う。基準状態c=d=0からの修復は
   Δc+Δd=1、修復の差のkernelは{(a,−a)}とする。変更可能域が全体、Δd=0、
   Δc=Δd=0の場合を比較し、修復集合がそれぞれaffine直線、単点、空になることを示す。
   同じデータで、局所Lawと指定観測を保存する部分加群への制限も計算する。
2. k=ℚ、rank 1の演算tとLaw t²=0、基準点t=0について、ℚ[ε]/(ε²)上の
   t=εはliftである。一方、その実現はℚ[ε]/(ε³)へliftできず、
   kernel (ε²)/(ε³)内の残差ε²が非零障害類になることを示す。
   比較用のLaw t=0では同じ基準点の一次自由度が零となることも示す。
3. k=ℤ、Law族(f)と(f,2f)を同じ非零多項式f=z²で比較する。
   syzygy (−2,1)とその生成性からH⁰・H¹および障害類の一致を示す。
   ℤ→F₂の特殊化後にも、冗長Lawの座標が余分な障害を作らないことを確認する。
4. k=ℚ[t]、三文脈にf₀=x₁−x₀、f₁=x₂−x₁、f₂=x₀−x₂を配置する。
   R=k/(t)、x₀=x₁=x₂=0で全大域syzygy (1,1,1)を生成し、
   H¹(T_raw)≃ℚに対しH¹(D)=0となることを示す。
   最後のLawをf₂−tへ変更すると、各文脈はR′=k/(t²)へliftできる一方、
   大域liftは存在せず、H¹(D)≃ℚの中の非零障害類を同じ残差から得る。
   両入力の基準点でLaw値と支持が一致することも示す。

## 前提・構成台帳

| 対象 | 役割 | 出所・構成義務 | 使用先 |
| --- | --- | --- | --- |
| 有限な原始表示、可換環、実現、square-zero拡大 | 入力として保持 | Aの量化。実現はG-140の独立定義 | A–C |
| smooth ambient、全syzygy、微分、残差、補正 | 構成・証明義務 | 原始宣言・式からA・Bで生成 | B–D |
| conormal表示、低次数のcotangent比較 | 構成・証明義務 | A・B。Nのprojectivityは受け取らない | B・C |
| Noetherian係数と有限principal affine cover | Čech計算の系の仮定 | Bで有限表示・準連接・比較を証明 | BのZariski計算 |
| readingの原始代入とLaw導出、指定されたtarget lift | 入力として保持 | G-142とC | Cの相対障害 |
| affine基準状態、変更可能域、固定する観測の式 | 入力として保持 | ノートのbase・delta台帳とD | 合法修復係数 |
| 観測readingと文脈被覆の適合性 | Dの局所比較の仮定 | 原始参照集合・交差・代入式から判定。X+Yの不適合例を検査 | relative repairの制限・組立て |
| repair sheaf・作用・全syzygy込み文脈比較 | 構成・証明義務 | D。完全性・同型・零性同値は入力fieldにしない | actual repairと既存APIの比較 |
| ambientのZariski site・conormal列・κ | 構成・証明義務 | E。全PのLaw idealを局所化し、ambient liftからκを生成 | Bの障害類への零性保存・反映 |
| Wの指定入力 | 構成・証明義務 | 同じLaw生成、lift、補正、reading比較 | 一般定理の検査 |

## 完了条件

A–E・WをLeanで証明し、`research/reports/G-146-aat-semantic-lift-and-repair-comparison.md`に
独立な実現、生成複体、actualな残差・補正、低次数のcotangent比較、既存APIとの対応を記す。
証拠は`research/lean/ResearchLean/AG/`に置き、
[共通完了基準](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)を適用する。

固定主張が偽の場合は、適格な原始表示・実現・拡大または修復入力から反例を構成し、
破れる比較、存在判定またはtorsor分類を示して`target-refuted`として記録する。
一般の高次cotangent比較、excisionのTor項、有限多項式計算の製品実装は後続の対象とする。
