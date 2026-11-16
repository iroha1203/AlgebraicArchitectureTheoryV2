# G-148-aat-operational-descent-diagnostic-comparison — 操作の貼り合わせ障害と同じK0診断の比較

- `id`: `G-148-aat-operational-descent-diagnostic-comparison`
- `status`: `draft`
- `research mode`: `target-theorem`
- `tracking issue`: [#6359（設計）](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6359)。個別のResearch Loop Issueはactive化時に定める。
- 設計: [多項式特殊化ノートの操作の貼り合わせ](../../docs/note/n1020_shigure_polynomial_specializations.md#operational-descent)
- 依存: [G-140](G-140-aat-independent-realization-descent.md)、[G-142](G-142-aat-shigure-reading-naturality.md)、[G-144](G-144-aat-law-value-diagnostic-sheaf.md)、[G-146](G-146-aat-semantic-lift-and-repair-comparison.md)、[G-125](G-125-aat-obstruction-diagnostic-bridge.md)、[G-104 / Atlas](G-104-aat-resolution-invariance.md)

主経路は[n1019](../../docs/note/n1019_shigure_representability_design.md)のG-149〜G-152にある。
本カードは多項式特殊化を構成する。主経路と同じ対象・射・Law評価への比較を要し、
本カードの達成だけでSHIGURE全体の達成とはしない。

## 研究目的

base・delta台帳の公開操作を保つmigration adapterから、局所的な実装の貼り合わせ障害、
修復の全解、その障害を読むK0指定類を生成する。有限graph上の加法的adapterという入力族で、
実際の操作が組み立つことと診断の指定類が零であることの同値を証明する。
readingを細かくする場合も、同じ実装・補正・指定類の比較をAtlasの生成比較へ接続する。

加法的torsorの障害、graphのコホモロジー、有限自由加群のaffine方程式は既存の数学を使う。
G-125は選択された実Čech障害とK0の比較を既に与える。本GOALの義務は、操作・adapter・
局所支持からその比較入力とgraphに対する新しい零性反映証明を生成し、既存SAGAの係数側定理を実際の操作の
貼り合わせへ適用することである。一般のK0とG-146の全syzygy複体の同型は主張しない。

## 固定target

### A. 原始操作とadapterからの局所実現

量化順は、可換環R、少なくとも一辺を持つ有限連結単純graph Γ、辺の向き、
μ∈R、各辺e:i→jのoffset b_e∈Rとする。各文脈iに同じ台帳型R²、公開状態型Rを置く。
原始加群演算と有限Lawから、次の写像と局所的な実装を構成する。

```math
p=(1,1),\qquad v=(1,-1)^{\mathsf T},\qquad
i_\lambda=(\lambda,1-\lambda)^{\mathsf T},\qquad j_\mu=\mu v,
\qquad g_b=I+bvp.
```

独立な実現はG-140のSemで与え、p i=id、p j=0をLawとする。
固定pの族はG-140 Fの一型の係数表示からmarkedな同型で構成する。
apply_u(x)=x+i(u)、compact_t(x)=x+j(t)、read=pの全有限操作語の公開意味保存を
同じLawから証明する。u,tは比較の両側で同じ外部入力とする。さらに

```math
g_b^{-1}=g_{-b},\quad p g_b=p,\quad g_bv=v,\quad
g_bi_\lambda=i_{\lambda+b},\quad g_bj_\mu=j_\mu,\quad
g_cg_b=g_{b+c}
```

を証明する。これによりg_bがapply・compact・readを運ぶ条件が
λ_j−λ_i=b_eと同値になる。各局所Lawを満たすことと、この共有部分の一致を区別する。
局所実現とadapterのパラメータには全offsetを許し、大域的一致を先に課さない。
ここで輸送する操作言語は固定引数の原子apply_u・compact_t・readである。
状態からt=Cを選ぶcompact_all、およびsnapshot phaseを加えたG-147 W7への輸送には、
引数選択・h・各phaseの比較が別途必要であり、上の式からは推論しない。W5でその相違を検査する。

Γの頂点と辺を点とし、頂点iの最小開集合をiとその接続辺からなる集合U_iとする
有限Alexandrov空間X_Γを生成する。U_iは非空連結、異なるU_i,U_jの交差は該当する
辺の一点または空、相異なる三つの交差は空であることを証明する。
同じ有限支持からAAT site、実際の開被覆、`MonomorphicOrderedCover`、K1の台を生成する。
採用したpair・tripleが全ての非空交差を表すことと、被覆がtopologyに属することを証明する。

### B. 操作の大域的組立てとSAGAの実係数定理

Aのg_bを遷移写像として、局所自由な局所定数R加群の層E_bと短完全列

```math
0\longrightarrow\underline Rv\longrightarrow E_b
 \xrightarrow{\ p\ }\underline R\longrightarrow0
```

を構成する。核の同定はp(x,y)=0から(x,y)=xvを導き、制限との可換性はg_bv=vから導く。
全site上でOb(V)=Γ(V,underline Rv)、State(V)={s∈Γ(V,E_b) | p(s)=1}を構成する。
Stateのsheaf条件はE_bとunderline Rの層条件から証明する。
大域section s∈State(X_Γ)と、局所apply・compactを運ぶ実際の大域操作iの間の
対応をi(a)=asから構成する。E_bのdescent自体と、この操作iの存在は別々に判定する。

既存SAGAへの適用先を次のように固定する。namespaceは`AAT.AG.SemanticRepair.Saga`とする。

- [EquationLift](../../Formal/AG/SemanticRepair/Saga/EquationLift.lean)の`LiftFiberData`を
  Ob、E_b、underline Rのsectionとbase=1から構成する。`exact_at_middle`、制限の自然性、
  核への埋め込みの単射性を上の式から証明し、`LiftFiberData.liftSystem`により
  `AffineCoefficientLiftSystem`を得る。局所実現から`CoefficientLiftAtlas`を構成する。
- 同ファイルの`CoefficientLiftAtlas.residualClass_isZero_iff_matching_correction`を
  同じatlasに適用する。空の交差でのStateの一元性、順序反転と対角を使って全pairの一致へ戻し、
  Stateのsheaf条件による貼り合わせから大域操作を構成する。逆方向は大域操作と局所操作の差を使う。
- [PartIVBridge](../../Formal/AG/SemanticRepair/Saga/PartIVBridge.lean)の
  `SitePresheafData.ofObstructionSheaf`と`MonomorphicOrderedCover.incToCoverRelativeH1`を
  このObへ適用する。omitted pair・tripleの係数が零であることを実交差から証明し、
  `IncH1`と同じObの`CoverRelativeHn 1`の指定類を同定する。

これらは必須の既存定理への適用であり、貼り合わせ定理への将来の接続予定ではない。
全siteの`AtomOccurrenceReading`を要求する`SemanticRepairPresentation`とは入力型を区別する。
開集合への制限で点Atomが消えるAのsiteから、そのoccurrence restrictionを仮定しない。
上の`LiftFiberData`による型の一致と、matchingから実sectionへの新しい系を証明する。

SAGAには頂点の全順序を一つ与え、増加pair i<jを用いる。指定したgraphの向きへ移す写像Tは、
次数0で恒等、次数1で同じ辺の増加pairの係数を取り、向きが一致すれば+1、逆なら−1を掛ける。
g_bv=vによりObの座標は輸送で変わらず、Tδ⁰_SAGA=d⁰_Γを証明する。三角形0→1→2→0では
T(c₀₁,c₀₂,c₁₂)=(c₀₁,c₁₂,−c₀₂)である。このTと空交差の正規化を通した後、
辺i→jの交差をj側の座標で読む。局所操作i_{λ_i}のresidualと指定障害類は

```math
r_e=\lambda_j-\lambda_i-b_e,\qquad
o_b=[r]=[-b]\in H^1(\Gamma;R)
```

となることを証明する。短完全列のconnecting class δ(1)もこの符号でo_bに同定する。
局所操作の選択に依存しないことと、次の同値を証明する。

```math
\operatorname{State}(X_\Gamma)\ne\varnothing
\quad\Longleftrightarrow\quad o_b=0
\quad\Longleftrightarrow\quad b\in\operatorname{im}(d^0:R^{V}\to R^{E}).
```

### C. 実修復の全解と変更可能域

Bで非空な大域操作の集合にOb(X_Γ)が自由推移的に作用することを、sectionの差と加法から
証明する。連結なΓではOb(X_Γ)≃Rとし、非空な解集合を一自由度のtorsorとして分類する。
固定された局所状態λに対する補正aはd⁰a=b−d⁰λである。
SAGAの補正は局所状態から引く規約なので、その変数c_SAGAとの対応はa=−c_SAGAとする。
これはG-146 Dの同じaffine Lawの修復集合に一致し、JacobianはΓのincidence行列になる。

変更可能な頂点集合から座標部分加群H_V⊆R^Vを生成した場合は、
補正の存在をb−d⁰λ∈d⁰(H_V)、全解をker(d⁰|_{H_V})のtorsorで特徴づける。
この制約付き判定は指定residualとH_Vを使い、絶対H¹の零性だけへ置き換えない。

adapter自体の変更可能な辺集合からH_E⊆R^Eを生成する場合は、
Δb∈H_Eで変更後の大域操作が存在することを[b]+[Δb]=0で特徴づける。
offset修復集合は非空ならker(H_E→H¹(Γ;R))のtorsorであり、
各修復後の操作の選択には上のH⁰の自由が残る。操作座標の補正とadapterの変更を区別する。

### D. 同じ支持・原始LawからのK0指定類

まずR=ℤとする。SourceをΓの辺で表される共有interfaceの出現とし、chart iの台を
その接続辺、edge eの台を両端chartの台の交差から生成する。補正方向vの各出現に対する
一つのscalar readoutをp(v)=0とする。この値はAの式から得て、offset残差rとは区別する。
同じchartの各interfaceで一つの操作補正を制限していることから、生成元間のrelation
[e]−[e′]を生成する。各cell上で、このrelationが実補正係数の表示の核を生成することを
証明する。Γの連結性から全Sourceのrelationによる連結性も証明する。

[GeneratorPresentation](../lean/ResearchLean/AG/ObstructionDiagnosticBridge/GeneratorPresentation.lean)の
原始表示をこのrelationから構成し、`ReflectionCondition`を上の連結性から証明する。
その整数表示加群の局所定数層をBのObへ同定する。chart・edgeの連結性と実交差を使って、
[FaceEmptyCechNormalization](../lean/ResearchLean/AG/ObstructionDiagnosticBridge/FaceEmptyCechNormalization.lean)の
`FaceEmptyAATCechCover`を構成する。全chartに全Sourceが現れるとは仮定しない。

次数0–2の整数診断複体との同型、およびℤ→ℚによる既存K0への写像を構成し、
[ActualCechH1Comparison](../lean/ResearchLean/AG/ObstructionDiagnosticBridge/ActualCechH1Comparison.lean)の
`actualCechDiagnosticH1Map`に同定する。写像は各cellでav↦a e_{(Law,0)}とし、
両微分、BのSAGA比較、実局所操作から計算したresidualと可換になることを証明する。
SAGAのrawな増加pairからの比較には、Bの符号付きTを合成する。
[SpecifiedAffineObstruction](../lean/ResearchLean/AG/ObstructionDiagnosticBridge/SpecifiedAffineObstruction.lean)の
`ActualCechAffineLocalData`にはtransition=−b、localState=λをこの実操作から生成して渡す。

指定診断類κ_bはo_bの像、すなわち同じresidualの有理数値の類とする。Γのspanning treeから
H¹(Γ;ℤ)≃ℤ^{|E|−|V|+1}を構成し、ℤ→ℚでの零性反映を証明する。
これはG-125の比較写像に対する新しい反映定理とする。既存
[diagnostic_class_eq_zero_iff_actual_class_eq_zero](../lean/ResearchLean/AG/ObstructionDiagnosticBridge/SpecifiedClassReflection.lean)は
`ReflectionCondition`に加えて、各labelを表す同一targetが全chartに現れる
`CommonLabelChartSupport`を要求する。Wのcycle支持の全交差は空であり、この定理は同じ入力へ
適用しない。各chart・edgeにlabel (Law,0)が存在することから次数別同型を作り、
spanning treeによる整数H¹の自由性で反映性を新たに証明して、次を得る。

```math
\operatorname{State}(X_\Gamma)\ne\varnothing
\quad\Longleftrightarrow\quad o_b=0
\quad\Longleftrightarrow\quad \kappa_b=0.
```

R=ℚの場合も同じ比較を証明する。一般のRについては診断係数Λ=Rで同じ複体を構成し、
ℤ→ℚの反映性を任意のR→Λへ拡張しない。
G-144の有限scheme・層の構成には、この同じ支持とregular readout p(v)=0を渡す。
診断群の次元はoffsetによらず一定でも、指定類κ_bが零であるかによって組立てが変わることを示す。
G-144・G-145のreadout (0,λ,0,μ)を持つ診断変化の族は、別に指定されたreadingとして保持する。

### E. 原始的な細分化とAtlas比較

cycleの一つのchartを二つの連続したchartへ分け、間にg_0=idを挿入する。
有限空間の射は追加辺とその両端を元の頂点へ送り、他の点を保つ縮約から生成する。
粗側E_bの逆像を細側E_bへ同定し、粗側被覆の逆像では分割された二つのchartの和を使う。
したがって実Čech比較は同じ細側空間上の二つの被覆についても構成する。
元のoffset・μ・操作を保つ代入と追加された一致Lawから、独立な局所実現と
修復集合の比較をG-142の同じ代入として生成する。新しい操作座標は一致Lawで元の座標へ戻る。
変更可能な頂点はchart mapによる逆像、変更可能な辺は元の辺の一意なliftとし、
追加辺のoffsetは0に固定する。この指定の下でCの制約付き修復も比較する。

Wで指定する支持・readingからAtlasの比較入力を生成する。C0の台の像、C1のfiberの連結性、
C2のedge lift、C3のfiber内のchain、C4のface lift、C5のedge liftの一意性、
C6のself-loop条件を証明する。C3は一辺のtreeのcycleが零であること、C4は両方のfaceが空、
C6は粗側にself-loopがないことから放電する。条件を比較写像の単射・全射という結論で代用しない。

[LawValueBlockComparisonBijectivity](../lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparisonBijectivity.lean)の
`generatedComparisonH1Map_bijective`を同じ入力へ適用する。
粗側から細側への実ObのČech比較、BのSAGA比較、DのK0比較と、このAtlas比較からなる
図式の可換性を証明する。指定類、実修復の存在、全解への作用の対応を含める。
この操作の有限反復について恒等・合成も証明する。

### W. 同じ台帳を通すcycleの指定例

Γを0→1→2→0の三角形とし、A–Eを同じ台帳・μ・支持で発火させる。
負のoriented sumによりH¹≃Rを同定すると、o_bとκ_bはb₀₁+b₁₂+b₂₀へ写る。
holonomy g_{b₀₁+b₁₂+b₂₀}がp i=1を満たす操作iを固定する条件も、この和が零であることに一致する。

1. ℤとℚについて、b=(1,2,−3)では全解λ=(t,t+1,t+3)、b=(1,0,0)では大域操作が
   存在しないことを証明する。後者でもE_b・p・j_μのdescentが成立し、局所操作は存在する。
   両者のK0のH¹は同じ一次元の有理数空間であり、指定類の零・非零が異なる。
2. R=ℚ、b=(1,0,0)のadapter修復を、全三辺、一つの指定辺、空の変更可能域で比較する。
   offset修復集合はそれぞれΔb₀₁+Δb₁₂+Δb₂₀=−1のaffine平面、単点、空となる。
   修復後の操作はそれぞれ一自由度を持つことを同じ存在定理から得る。
3. 細側のchartを0a,0b,1,2、Sourceを{s₂₀,t,s₀₁,s₁₂}とする。chart台を順に
   {s₂₀,t}、{t,s₀₁}、{s₀₁,s₁₂}、{s₁₂,s₂₀}とし、細側readingは恒等とする。
   粗側readingはt↦s₀₁、他をそのままとする非単射な商、chart mapは0a,0b↦0とする。
   粗側chart台は{s₂₀,s₀₁}、{s₀₁,s₁₂}、{s₁₂,s₂₀}である。
   新しい辺0a→0bのoffsetは0、他はbとする。同じ八点空間の細側star coverと、
   U₀=U₀a∪U₀bを持つ粗側coverから、Eの全条件・類の比較・実修復の対応を証明する。
4. R=ℚ、λ=(0,0,0)、b=(1,2,−3)で、頂点の全補正を許す場合と全頂点を固定する場合を
   比較する。κ_b=0は共通でも後者の修復集合は空となることを示し、Cの変更可能域を使う
   判定の必要性を同じ入力で確認する。
5. snapshot phaseを追加するとadapterの同じ式だけでは比較が成立しない例を構成する。
   R=ℚ、λ=μ=1はG-147 W7の意味保存条件を満たすが、g_1で移したλ′=2,μ′=1は満たさない。
   原子apply・compactの比較は成立し、移送先のsnapshot protocolではbegin; apply_1; finishの
   readが1でなく2になることを証明する。観測言語を広げる際の追加Lawと状態比較を省略しない。
   同じRとμ=1でg_1(compact_all(1,0))=(2,−1)、compact_all(g_1(1,0))=(1,0)も示し、
   固定引数compact_tの比較から状態依存の引数選択の可換性を推論できないことを検査する。

## 前提・構成台帳

| 対象 | 役割 | 出所・構成義務 | 使用先 |
| --- | --- | --- | --- |
| R、有限連結単純graph、向き、μ、offset | 入力として保持 | A。大域整合は入力に含めない | A–W |
| 独立な局所操作、有限Law、変更可能な宣言 | 入力・先行構成 | G-140・G-146の同じ台帳表示 | A–C |
| g_b、操作語の輸送、ker p≃Rv | 構成・証明義務 | Aの原始式 | B–D |
| 有限空間、site、全実交差、被覆のtopology所属 | 構成・証明義務 | Aのincidence。空のfaceを宣言するだけでは足りない | B・D・E |
| E_b、Ob、State、全siteの制限と層条件 | 構成・証明義務 | Aの実adapterとBのsection | B・C |
| LiftFiberData・局所atlas・指定residual | 構成・証明義務 | 実操作からBで生成。任意cocycleを入力にしない | B・D |
| SAGAの零類とmatching補正の同値、Part IV比較 | 既存実定理 | Bで対象と写像を固定し、同じ入力へ適用 | B・D・E |
| 原始relationの完全性、ReflectionCondition | 構成・証明義務 | Dの局所操作の制限とgraphの連結性 | D |
| ObからK0への実比較 | 既存構成への同定義務 | G-125のactualCechDiagnosticH1MapとDの生成写像 | D・E |
| ℤ→ℚでの零性反映 | 構成・証明義務 | Dのspanning tree・整数H¹。単射性を入力にしない | D・W |
| H_V、H_E | 入力から生成 | 変更可能な頂点・辺集合の座標部分加群 | C・W |
| reading・chart・edgeの細分化 | 原始的な指定変更 | E・W。追加adapterはg₀、関係式から操作の一致を導く | E |
| C0–C6と比較図式の可換性 | 構成・証明義務 | Eの同じ支持・Law値・細分化 | E・W |

## 完了条件

A–E・WをLeanで証明し、`research/reports/G-148-aat-operational-descent-diagnostic-comparison.md`に
原始操作から実修復・SAGA・G-125・Atlasまでの対象、写像、指定類と宣言の対応を記す。
証拠は`research/lean/ResearchLean/AG/`に置き、
[共通完了基準](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)を適用する。

完了には、Wの同じ実装が独立なSem、実adapter、Stateの層、既存SAGAのmatching補正定理、
actualCechDiagnosticH1Map、Atlasの生成比較を通ることが必要である。
新しいcomparison構造へ同型や零性反映を入力して得た結論だけでは完了にしない。
大域操作の不存在・一自由度の存在・変更可能域による失敗を、同じ生成経路で区別する。

固定主張が偽の場合はAの入力を満たす具体例を与え、破れる存在同値・指定類の比較・
細分化の条項を証明して`target-refuted`として決着させる。肯定形の主定理の証明完了とは区別する。
既存SAGAのoccurrence型とBの係数型の相違や、層・siteのAPI不足だけを反例とはしない。
