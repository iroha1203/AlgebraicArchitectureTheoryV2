# G-142-aat-law-value-diagnostic-sheaf — 診断の幾何と意味障害との比較

- `id`: `G-142-aat-law-value-diagnostic-sheaf`
- `status`: `draft`
- `research mode`: `target-theorem`
- 関連メモ: [#6359](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6359)。実行用tracking Issueはactive化時に定める。
- 設計: [n1020 §4・14・16](../../docs/note/n1020_shigure_polynomial_specializations.md)
- 依存: [G-139](G-139-aat-law-generated-relative-geometry.md)の実現幾何。
  E–Fの実修復との比較には[G-141](G-141-aat-coherent-repair-effectivity.md)の有限graph adapter族を使う。

## 研究目的

Law値の一致関係が変わる診断を実現の幾何上で構成し、何が保存され、どの類が生じ、
どの類が失われるかを決定する。診断次元の変動を原始入力から分類することと、
指定診断類の零性が実際の意味保存変更の存在を反映することを、同じ写像を用いて区別する。
Atlasによる観測の比較を、許す編集と目的を含む全修復の探索fiberへ接続する。
有限順像、Mayer–Vietoris、上半連続性は標準数学として使い、AATの生成規則と実修復への
比較を新たな構成・証明義務とする。

## 固定target

### A. 固定labelの整数診断と係数変更

既存の`FiniteLawFamily`、finite Source、adequate reading、`TargetSupportedNerve`の
全入力を量化する。同じ`CellCoordinate`とchart・edge・face supportから次数0–2の
整数複体C_ℤを生成し、d¹d⁰=0をface endpoint等式から証明する。
同じLaw値の複数出現は一つのlabelとし、任意可換環Λについて
Λ⊗_ℤ C_ℤ≅C_Λを両微分・生成されたreading比較射まで構成する。
Λ=ℚで`lawGeneratedComplex`、`lawGeneratedD0`、`lawGeneratedD1`、
`GeneratedComparisonMap`の同じ宣言へ同定する。

任意のflatなΛ→Λ′ではΛ′⊗_Λ Hⁱ(C_Λ)≅Hⁱ(C_Λ′)（i=0,1,2）を証明し、
faithfully flatな場合は各指定類の零性を反映すると証明する。
幾何の基礎環、Law値の値域、診断の加群係数Λを別々に保持する。
係数変更と値域変更によるlabelの再生成はW1で区別する。

### B. 任意scheme上の診断の族

任意scheme B、有限source S、有限readout添字L、有限supported nerve、
regular functions f_{ℓ,s}と診断係数環Λを量化する。chart台はSの部分集合で指定し、
edge・faceの台S_σはK1の交差から生成する。
既存のfinite SourceからSへの全射readingを使う場合は、Lawのadequacyを同じ評価で照合する。
G-139の実現scheme B=M_Pへの適用では、fを原始scalar式から生成し、評価一致を証明する。
式には係数、加法・乗法、有限tensor式の自己準同型のtraceを使い、名前付き生成元が
基底となる型では演算成分も使う。一般の基底成分はそのchart上で扱い、traceの基底不変性と
成分の変換則を証明する。required Lawの零残差と、選んだreadoutを区別する。
生成元を忘れる商stackへの降下にはGL不変性を別に証明する。

同じ支持と式から有限局所自由射p_{σ,ℓ}:Z_{σ,ℓ}→Bと層の複体を構成する。

```math
Z_{\sigma,\ell}
 =\operatorname{Spec}_B\left(\mathcal O_B[z]/\prod_{s\in S_\sigma}(z-f_{\ell,s})\right),
\qquad
\mathscr C^d_{B,\Lambda}
 =\bigoplus_{\dim\sigma=d,\ell\in L}(p_{\sigma,\ell})_*
       \underline\Lambda_{Z_{\sigma,\ell}}.
```

空支持では空schemeとする。支持包含から閉埋込み、恒等・合成に整合する層の制限、
その交代和による微分を生成し、d¹d⁰=0を証明する。
任意の幾何点b̄:Spec Ω→Bで、fiberの点を相異なる値{f_{ℓ,s}(b̄)}に対応させ、
stalk複体を同じ値域Ωで再生成したAのK0/K1複体へ、両微分・Law値別分解まで同定する。

任意のscheme射g:B′→Bについて、式の引戻しで生成したZ′とC′が
Z×_B B′、g⁻¹Cに一致することを、同じ制限写像・stalk同定で証明する。
flatnessを要求せず、恒等・合成、scalar式を保つreading代入との可換性を含める。
任意のΛ→Λ′について、次数別の診断係数変更、各項のΛ-flatness、導来tensor積との
同定を証明する。コホモロジーの通常tensor積との交換はAの条件で述べる。

各Lawの等値partition πについて、同じblock内の差を零、異なるblock間の差を可逆にする
locally closed B_πを生成する。これらの点集合による有限分割と、各B_π上での
有限自由Λ加群の定数複体への同型を証明する。
普遍座標を持つA^{L×S}_ℤ上でも構成し、任意のfの族をそのpullbackとして回収する。
全R値の実現とreadoutはG-139が保持し、幾何stalkと冪零値の相違をW2で検査する。

### C. 合流による類の生成・消失

Bのsource・台・incidenceを固定し、partition πからπ′への全粗化を量化する。
値aを持つsourceと台が交わるcellをK_aとし、その閉性、診断の⊕_a C⁎(K_a;Λ)への
分解を既存のLaw値別分解へ同定する。合流blockが元のK_aの合併になることから
次数別単射cochain map r_{π′,π}:C⁎(π′;Λ)→C⁎(π;Λ)を生成する。
合流後から合流前へ向かうこの写像の恒等・合成と、幾何点の特殊化η̄→s̄に対する
層のstalk射C_s→C_ηとの一致を証明する。

二値合流ではU=K_a∪K_b、I=K_a∩K_bとし、原始cellから

```math
0\longrightarrow C^\bullet(U;\Lambda)\xrightarrow r
C^\bullet(K_a;\Lambda)\oplus C^\bullet(K_b;\Lambda)
\xrightarrow\rho C^\bullet(I;\Lambda)\longrightarrow0
```

を生成して完全性を証明する。同じ長完全列で
ker H¹(r)≅coker H⁰(ρ)、coker H¹(r)≅im H¹(ρ)を構成し、
H¹(r)が同型であることとH⁰(ρ)が全射かつH¹(ρ)=0であることを同値にする。
空交差も含め、係数体では同じ写像のrankによる核・余核の次元を与える。
任意有限block族の全交差からMayer–Vietoris複体を生成し、cellごとの完全性、
合併を計算する比較、交差コホモロジーからのspectral sequenceを構成する。
二値合流の任意の順序による合成が同じr_{π′,π}となることを証明する。
途中の分解の一致ではなく、全体の写像・核・余核の一致を要求する。

### D. 診断次元の変動の実現と非存在定理

任意可換環k、有限表示affine scheme B=Spec A、有限個のg₁,…,g_r,h∈Aに対して、
有限source・固定nerve・scalar readoutから、全幾何点b̄と全係数体Λで

```math
\dim_\Lambda H^1(C_{\bar b,\Lambda})
 =\mathbf1_{V(g_1,\ldots,g_r)\cap D(h)}(b)
```

となる入力を構成する。n=max(3,r+1)頂点のcycleの辺sourceに0,g₁,…,g_rと残りの0、
全頂点sourceにhを割り当て、ambient nerveをfull 2-skeletonとしてK1支持を生成する。
値blockがcycleの部分グラフまたはfull 2-skeletonになることから式を証明する。
r=0、空集合、h=0、単元hも含める。有限直和により、有限個のregular functionの
零・非零条件による有限層別化上で一定な、有限値域の任意β:|B|→ℕを同じH¹として実現する。
Bの有限表示からrank 1・一生成元の型とunary演算・required Lawを持つPを生成し、
M_P≅Bおよびg_i,hの式を構成する。多項式代表の変更とreadoutの一致も証明する。

W2のk=Λ=ℚでは、全点bで

```math
\dim_{\kappa(b)}H^1(E\otimes^{\mathbf L}_{\mathcal O_B}\kappa(b))
 =\dim_{\mathbb Q}H^1(C_{\bar b,\mathbb Q})
```

を満たすpseudo-coherentなO_B複体Eが存在しないことを、μ≠0からμ=0への
H¹次元の下降とderived fiberの上半連続性から証明する。perfect複体の不存在も導く。
Bの定数係数étale層は同じfamilyを実現することと併せ、二種類の幾何を区別する。

### E. 同じ操作の障害を読む指定診断類

G-141の有限graph adapter族を使う。可換環R、少なくとも一辺を持つ有限連結単純graph Γ、
辺の向き、μ、offset bを持つ同じ台帳から、E_b、Ob=underline Rv、State、
r_e=λ_j−λ_i−b_eとo_b=[r]=[−b]を得る。まずR=ℤとする。
Sourceを共有interfaceである辺の出現、chart台を接続辺、edge台を実交差とし、
補正vのreadoutを原式からp(v)=0とする。この値とoffset残差rを区別する。
一つの操作補正のinterfaceへの制限からrelation [e]−[e′]を生成し、各cellの
補正係数表示の核を生成すること、全Sourceのrelationによる連結性を証明する。

[GeneratorPresentation](../lean/ResearchLean/AG/ObstructionDiagnosticBridge/GeneratorPresentation.lean)
の原始表示と`ReflectionCondition`を構成し、その整数表示加群の局所定数層をObへ同定する。
実交差から[FaceEmptyAATCechCover](../lean/ResearchLean/AG/ObstructionDiagnosticBridge/FaceEmptyCechNormalization.lean)
を構成し、次数0–2の整数診断複体との同型、ℤ→ℚでの既存K0への写像を作る。
各cellの写像av↦a e_{(Law,0)}を
[actualCechDiagnosticH1Map](../lean/ResearchLean/AG/ObstructionDiagnosticBridge/ActualCechH1Comparison.lean)
へ同定し、両微分、G-141のSAGA比較、実操作のresidualとの可換性を証明する。
SAGAの増加pairからgraphの向きへの符号付き写像Tを合成し、
[ActualCechAffineLocalData](../lean/ResearchLean/AG/ObstructionDiagnosticBridge/SpecifiedAffineObstruction.lean)
のtransition=−b、localState=λを同じ実操作から生成する。

指定診断類κ_bをo_bの像として構成する。spanning treeから
H¹(Γ;ℤ)≅ℤ^{|E|−|V|+1}を構成し、ℤ→ℚで零性を反映することを証明して

```math
\operatorname{State}(X_\Gamma)\ne\varnothing
\quad\Longleftrightarrow\quad o_b=0
\quad\Longleftrightarrow\quad\kappa_b=0
```

を得る。cycleでは`CommonLabelChartSupport`が偽であることも確認し、同条件を要する
[既存反映定理](../lean/ResearchLean/AG/ObstructionDiagnosticBridge/SpecifiedClassReflection.lean)
を適用せず、上の整数H¹による反映証明を構成する。
R=ℚでも比較し、一般RではΛ=Rで同じ複体を構成する。任意R→Λの零性反映は仮定しない。
同じ支持とregular readout p(v)=0をBへ通し、次元がoffsetによらず一定でも
指定類の零性で組立てが異なることをW3で証明する。

### F. 細分化とAtlasの実比較

cycleの一つのchartを二つへ分け、間にg₀=idを挿入する。追加辺と両端を元の頂点へ送る
有限空間の縮約を構成し、粗側E_bの逆像を細側へ同定する。同じ細側空間上で、
粗側被覆の逆像（分割した二chartの和）と細側被覆を比較する。
元のoffset・μ・操作を保つ代入と追加一致Lawから、実現と修復の比較を生成する。
許容頂点はchart mapの逆像、許容辺は元の辺の一意なlift、追加offsetは0とし、
G-141の制約付き修復と全解への作用も比較する。

W3の同じ支持からAtlasのC0–C6を構成・証明する。台の像、fiberの連結性、edge lift、
fiber内のchain、face lift、edge liftの一意性、self-loop条件を各々放電する。
一辺のtreeのcycleが零であること、両方のfaceが空であること、粗側にself-loopがないことを使い、
比較射の単射性・全射性を条件として入力しない。
[generatedComparisonH1Map_bijective](../lean/ResearchLean/AG/ResolutionInvariance/LawValueBlockComparisonBijectivity.lean)
を同じ入力へ適用し、実ObのČech比較、SAGA比較、EのK0比較と可換になることを証明する。
指定類・実修復の存在・全解への作用の対応、有限反復の恒等・合成を含める。

さらにG-140 Eの探索fiberを同じ粗側・細側の実修復から構成する。
目的は粗側の許容編集係数・修復後の操作のregularな式で評価し、
有限個の等式・可逆条件で定めるlocally closedな部分scheme P↪Tとして与える。
細側へは同じ式を引き戻す。
原始代入と追加一致Lawから、目的評価と修復適用の比較を構成し、
全Rで目的fiberの自然な同値、指定障害の比較との可換性を証明する。
順序付き評価を用いる場合も同じ値と順序を保持し、候補比較を運ぶ。
同値を入力fieldとして受け取らず、追加頂点の一致から候補を一意に復元する。

Law評価の十分性、C0–C6による診断の同型、目的を含む全修復fiberの同値を
別の主張として比較する。前二者だけから第三を推論できない例には、
Law評価と支持に現れない自由編集係数tを持つA¹→Spec kを用いる。
Law評価と診断は一定でも全編集のfiberは異なり、目的t=1を落とすreadingでは
目的の評価が降下しないことを示す。一般の情報を落とすreadingに同値を要求せず、
元の候補の像とfiber、目的を運べる条件を明示する。

### W. 一般定理を発火させる指定例

1. [n1020 W4](../../docs/note/n1020_shigure_polynomial_specializations.md#8-固定する具体例)の
   ×2:ℤ→ℤで非flat係数変更によるH⁰の相違と、flatなℤ→ℚによる非零H¹類の消失を示す。
   別に二source・一Law・値0,2からK0を生成し、F₂値への再生成と固定labelのtensorを区別する。
   全chart台が同じ共通Law値を持つ三辺cycle・faceなしのnerveからH¹(C_ℤ)≅ℤとℚ特殊化を証明する。
   ×2の対照例をK0の微分と同一視せず、K0でのflatnessの必要性の証明にも用いない。
2. base/delta台帳と同じB=A²_{k,(λ,μ)}、3 chart、4 sourceを固定し、sourceのchart台を順に
   {0,1}、{1,2}、{2,0}、{0,1,2}、readoutを0,λ,0,μ、ambient nerveをfull 2-skeletonとする。
   任意の体kと独立な係数体Λでdim H¹=1がλ=0かつμ≠0と同値、他では0と証明する。
   V(μ−1)上の生成とV(λ)上の消失をCの同じr、ρと核・余核で説明する。
   Λ=ℤ・ℚでstalk・微分を同定し、k=ℚ、R=k[ε]/ε²の(0,0),(0,ε)について、
   readoutのR値の相違と幾何点での一致を同時に示す。
3. G-141の三角形0→1→2→0の同じ台帳をE–Fへ通す。負のoriented sumでH¹≅Rとすると
   o_b,κ_bがb₀₁+b₁₂+b₂₀へ写ることを証明する。ℤ・ℚでb=(1,2,−3)と(1,0,0)を比較し、
   診断H¹は同じ一次元でも指定類の零性と実操作の存在が異なることを示す。
   κ_b=0でも全頂点を固定した補正が存在しないG-141の例も、同じ類へ通す。
   細側chartを0a,0b,1,2、Sourceを{s₂₀,t,s₀₁,s₁₂}、台を順に
   {s₂₀,t},{t,s₀₁},{s₀₁,s₁₂},{s₁₂,s₂₀}とする。
   細側readingは恒等、粗側はt↦s₀₁（他は恒等）、chart mapは0a,0b↦0とする。
   追加辺のoffsetを0とし、同じ八点空間の二被覆でFの全比較を証明する。

## 前提・構成台帳

| 対象 | 役割 | 構成・証拠 | 使用先 |
| --- | --- | --- | --- |
| 有限source・Law・supported nerve・Λ | 入力 | A–B。同じcellと支持から生成 | 整数診断・層・合流 |
| 実現schemeと原始scalar式 | 先行構成と入力 | G-139、Bの評価一致 | 全base change・stalk |
| 有限順像、Mayer–Vietoris、上半連続性 | 既存数学 | [03QN](https://stacks.math.columbia.edu/tag/03QN)、[0BDI](https://stacks.math.columbia.edu/tag/0BDI)、既存Law値分解 | B–D |
| Bの有限表示、g_i,h,β | 入力 | Dの原始cycle構成 | 任意構成可能関数の実現 |
| E_b,Ob,State,実residual,SAGAの比較 | 先行構成 | G-141の同じadapterと実交差 | E–F |
| relation完全性・整数H¹の自由性 | 構成・証明義務 | Eの原始支持とspanning tree | 指定類と零性反映 |
| 細分化・C0–C6・比較図式 | 構成・証明義務 | F・W3の同じ実現と支持 | Atlasと実修復の保存 |
| 許容編集・目的の評価と引戻し | 入力と構成義務 | G-140 EとFの同じ追加一致Law | 探索fiberと指定障害の可換比較 |

## 完了条件

A–F・WをLeanで証明し、同じ原始入力からの生成、既存宣言との対応、仮定と使用先を
`research/reports/G-142-aat-law-value-diagnostic-sheaf.md`に記す。
証拠は`research/lean/ResearchLean/AG/`に置き、
[共通完了基準](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)を適用する。
有限例のrank検算はDの全入力についての構成を代替せず、任意に選んだ比較同型・零性反映を
受け取る定理はE–Fの生成義務を満たさない。

固定主張が偽の場合は、対象条項の量化に属する原始入力と破れる式・写像を構成し、
不成立を証明して`target-refuted`として記録する。肯定形の全主定理の証明完了とは区別する。
Dの非存在主張への反証には、W2の全点で指定式を満たすpseudo-coherent複体の構成を要する。
形式化APIの不足は反例ではなく未証明として扱う。
