# G-137：原始入力、商nerve、因子化順序

§1–4は[GOAL T0・A](../../goals/G-137-aat-safe-coarsening-order.md)が固定する数学的定義である。
§5は既存実装へ接続するための証明方針である。

## 1. 細入力

非空有限集合S・T・V、全射 $`q:S\to T`$、有向辺関係
$`E\subseteq\{(v,w)\in V^2\mid v\ne w\}`$、各vの非空台 $`S_v\subseteq T`$ を取る。
SourceはS、fine readingはq、chartはV、edgeはEの元、faceは空型とする。
`CoverNerve` の辺の存在を表す命題はTrueとし、余分な選択データを置かない。
K1による辺台は $`S_{(v,w)}=S_v\cap S_w`$ である。空の辺台を許す。

辺の向きは入力の一部である。同じ順序対の重複を持たないため、恒等分割の商は
元のnerveと同型になる。逆向きの二辺は別のセルとして共存できる。
面が空であることは入力クラスの固定であり、入力された面を忘却する操作ではない。

これにより既存 `TargetSupportedNerve q` を作る。各Aで選択するセルは
台がAと交わる元セルであり、複体の式は

```math
C^0=\mathbb Q^{V_A},\quad C^1=\mathbb Q^{E_A},\quad C^2=0,
\qquad (d^0x)(v,w)=x(w)-x(v),\quad d^1=0.
```

K1から選択辺の両端も選択される。実H¹は既存のcocycle/coboundaryの商を用いる。

## 2. 許す粗化と商の規則

PをT上、QをV上の任意の同値関係とする。R=(P,Q)に対し、
$`\pi_P:T\to T/P`$、$`\rho_Q:V\to V/Q`$ を商写像とする。

| 成分 | 原始入力からの定義 |
| --- | --- |
| reading | $`q_R=\pi_P\circ q:S\twoheadrightarrow T/P`$ |
| chart | $`V/Q`$ |
| chart台 | $`S^R_B=\{\pi_P(t)\mid\exists v,\ \rho_Q(v)=B\ \land\ t\in S_v\}`$ |
| edge | $`E_Q=\{(B,C)\mid B\ne C\ \land\ \exists(v,w)\in E,\ \rho_Q(v)=B,\rho_Q(w)=C\}`$ |
| edge台 | $`S^R_B\cap S^R_C`$ |
| face | 空型 |

内部辺は全て縮約する。異なる細辺が同じ商の順序対へ写る場合は一つの粗辺にする。
(B,C)と(C,B)は同一視しない。商で三角形が生じても面は追加しない。
chart台の合併、像、辺台の交差はこの順序で行う。
元の辺台の像と粗辺台が一致するという仮定は置かない。

この規則を全Rに適用して $`N_R`$ を生成する。途中で安全性を検査して
生成可能な分割を減らすことはしない。
名前付きの有限全射で商を表示してもよいが、
T・Vからの商写像と可換な全単射だけを表示の違いとして同一視する。
商nerveが抽象的に同型でも、Mからの商写像が異なれば同じ粗化とは限らない。

## 3. 順序、join、比較の向き

```math
R\le R'\iff P_R\subseteq P_{R'}\ \land\ Q_R\subseteq Q_{R'},
\qquad R\vee R'=(P_R\vee P_{R'},Q_R\vee Q_{R'}).
```

各joinは関係の和の反射・対称・推移閉包である。
最小元 $`\bot`$ は二つの等号関係、最大元 $`\top`$ は二つの全関係である。
有限集合上の標準的な同値関係の束の積を使う。
安全元集合には、別途証明しない限り束構造を与えない。

$`R\le R'`$ から、targetとchartの商因子 $`\pi_{RR'},\rho_{RR'}`$ を生成する。
逆に、元のT・Vからの商写像と可換な二つの因子があれば関係包含が従う。
readingの既存記号では $`q_{R'}.\mathrm{CoarserThan}(q_R)`$ であり、
この文書の分割順序とは引数の向きが逆になる。

商の辺(B,C)は、二端点のR′像が等しければnone、異なればその順序対へsomeで送る。
face写像は空写像である。これは $`N_R\to N_{R'}`$ の原始セル比較を生成する。
chart台の包含は§2の存在証拠を移して証明し、
辺の端点、退化辺の同一fiber、空面の条件を放電する。
この比較からのcochain射は逆方向である。

```math
C^\bullet(N_{R'},A)\longrightarrow
C^\bullet(N_R,\pi_{RR'}^{-1}A)\longrightarrow
C^\bullet(N_M,\pi_{R'}^{-1}A).
```

直接商と反復商では、商集合の標準全単射、辺関係の存在条件、chart台の合併の像を
それぞれ同定する。辺のnone/someはこの同定の下で `Option.bind` の合成に一致する。
直接生成したHomと合成したHomの等式を証明して、既存H¹の合成へ降ろす。

この順序は全粗化の因子化を記述する。任意の余分なセル写像・線形写像を
因子化の証人として追加する順序ではない。
ここでの解像度は、readingとnerveの対、およびMからの二つの商写像を含む。
target分割が同じでもchart分割が異なれば、異なる粗化になり得る。

## 4. 安全性、Law、同型

$`m_R`$ は§3を $`\bot\le R`$ に適用した比較とする。
元のfine nerveと恒等商の同定を含め、各Aの既存
`aSubnerveComparisonHom` を $`u_{R,A}`$ とする。
細側は常に $`\pi_R^{-1}A`$、粗側はAである。
安全性はGOAL T0の全Aの実H¹全単射性とする。

Law条件は、**各Rについて**その粗readingにadequateな全 `FiniteLawFamily S` を量化する。
Rが変わればadequateな族の集合も変わる。細readingにadequateな全Lawを、
粗readingにも無条件に降下できるという要求にはしない。
Law値型には有限性を課さず、有限Sourceから得る発生ラベルの有限性を使う。
空Law族と空Aも含める。全A条件への逆向きは指示Lawの該当値blockを使う。

入力同型 $`\alpha:M\cong M'`$ は全単射
$`\alpha_S:S\cong S'`$、$`\alpha_T:T\cong T'`$、$`\alpha_V:V\cong V'`$ で、

```math
q'\alpha_S=\alpha_Tq,\qquad
(v,w)\in E\iff(\alpha_Vv,\alpha_Vw)\in E',\qquad
S'_{\alpha_Vv}=\alpha_T(S_v)
```

を満たすものとする。辺の全単射はこの式から誘導する。
関係を共役して $`\alpha_*R`$ を作り、商集合の全単射も誘導する。
同型の合成・恒等とこの輸送が可換になることを証明する。

全同型に対してcochainの同型 $`I_c,I_f`$ を生成し、
$`I_fu_{R,A}=u_{\alpha_*R,\alpha_*A}I_c`$ を元セルの評価式から示す。
これがH¹、実核・余核、安全性と極大性へ降りる。
S・Tの再添字づけも含めるので、chart名だけを変更する既存APIの呼出しだけでは完了しない。

## 5. 既存実装への接続方針

面が空のため原始比較は旧hereditary条件を満たす。
旧比較とG-134の `ofHereditary` の生成Hom一致を使い、G-107の全Law還元と
G-135の `allAPreservationDecision` を同じ比較へ適用する。
空Aは零複体として別途接続し、G-107の非空A量化との相違を解消する。

G-135の保存条件は $`H^1\eta`$ の全単射性と $`\tau`$ の単射性である。
本クラスでpure特殊化を使う場合、その条件は空面から放電する。
fiberの非輪状性だけを安全性の定義にせず、係数側の条件を残す。
support制限の自然性と自己同型による輸送も、別の写像として接続する。
