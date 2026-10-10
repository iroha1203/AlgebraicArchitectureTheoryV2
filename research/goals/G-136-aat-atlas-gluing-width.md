# G-136-aat-atlas-gluing-width — 診断欠損の貼り合わせと有限観測幅の限界

- `id`: `G-136-aat-atlas-gluing-width`
- `status`: `active`
- `research mode`: `target-theorem`
- `tracking issue`: [#5321](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5321)
- `source note`: [n1016 §4.4・候補13](../../docs/note/n1016_rising_sea_v2_paper_plan.md)、[n1006 R15・R3-w](../../docs/note/n1006_aat_atlas_reinforcement_plan.md)
- `design`: [構成と証明方針](../designs/G-136-aat-atlas-gluing-width/README.md)、[完全列](../designs/G-136-aat-atlas-gluing-width/exact-sequence.md)、[幅と指定例](../designs/G-136-aat-atlas-gluing-width/witnesses.md)、[再利用対応](../designs/G-136-aat-atlas-gluing-width/reuse-map.md)

## 研究目的

二領域のAtlas診断を、それらの真のセル交差上の貼り合わせデータから合併の診断へ
接続する。局所の一次診断が保存されても合併で欠損が生じる原因を、実比較の核・余核として
特定する。同時に、任意の有限観測幅で全ての一次診断が一致しながら、一様零欠損が異なる
有限原始入力対を構成する。

[G-133](G-133-aat-atlas-defect-composition.md)の標準錐と台制限、
[G-134](G-134-aat-face-relation-subdivision.md)の原始incidence比較、
[G-135](G-135-aat-atlas-coefficient-fiber.md)の固定部分集合での係数・fiber分解を用いる。
新しい対象は領域和のMayer–Vietoris列と全有限幅の分離族である。
[G-130](G-130-aat-relative-repair-composition.md)が扱う固定部分・変更範囲を持つ
実修復と、ここでの有理係数のAtlas比較は、係数・次数・射を別に特定する。

## 固定target

T0・A–Eを一つの定理群とする。各条項は証明・構成を要求する。
指定例の原始データと評価対象は[幅と指定例 §1–4](../designs/G-136-aat-atlas-gluing-width/witnesses.md)で固定する。
その他の内部APIと証明の分割は設計上の選択である。

### T0. 原始入力、量化、診断

有限 `Source`、全射reading $`q_c\preceq q_f`$、有限な両側の
`TargetSupportedNerve` $`N_c,N_f`$、G-134の
`IncidenceSupportedComparison` $`M`$ を任意に取る。係数はℚ、
$`\pi=\mathrm{comparisonFactor}`$ とする。chartの非空台、K1による辺・面台、
端点・面のincidence、chart台の包含、部分セル像の符号付き退化条件を保持する。
平行辺、loop、面での重複incidenceを含む。

この幾何の後に任意の $`A,B\subseteq q_c.\mathrm{Target}`$ を量化する。
$`X=A,B,U=A\cup B`$ について $`X_c=X`$、$`X_f=\pi^{-1}X`$ とし、
$`C_{s,X}=N_s.\mathrm{targetSubsetComplex}(X_s)`$、
$`u_X=M.\mathrm{aSubnerveComparisonHom}(X)`$、$`T_X=H^1(u_X)`$ を使う。
`oldH1Equiv` によって既存のH¹商と標準複体のH¹を対応させる。
以下の群は実線形写像の核・像の商である。

```math
\mathrm{Ph}_X=\ker T_X,\qquad
\mathrm{Hd}_X=\operatorname{coker}T_X,\qquad
J_X=\mathrm{blockDefect}(T_X)=(\dim\mathrm{Ph}_X,\dim\mathrm{Hd}_X).
```

空領域、空交差、空辺台・面台を含める。Dでは幾何の後に、粗readingにadequateな
任意の `FiniteLawFamily Source` を量化し、細adequacyを導出する。

### A. 真のセル交差と原始短完全列

各次数で台が $`X_s`$ と交わる元セルを選んだ部分nerveを $`N_{s,X}`$ とする。
$`I_s=N_{s,A}\cap N_{s,B}`$ は、同じ元セルが両方に属するセル交差である。
二つの所属証拠の台の点は一致する必要がない。
$`N_{s,U}=N_{s,A}\cup N_{s,B}`$ を証明し、$`I_s`$ のincidence閉性から
定数係数複体 $`C_{s,I}`$ を構成する。$`N_{s,A_s\cap B_s}`$ との同一視は行わない。

元のセルへの評価から制限射、差制限 $`\rho_s(x,y)=x|_{I_s}-y|_{I_s}`$ と
粗細比較 $`u_I:C_{c,I}\to C_{f,I}`$ を生成し、全三次数で

```math
0\longrightarrow C_{s,U}\xrightarrow{(\mathrm{res}_A,\mathrm{res}_B)}
C_{s,A}\oplus C_{s,B}\xrightarrow{\rho_s}C_{s,I}\longrightarrow0
```

の完全性と粗細比較による可換図式を証明する。完全性と可換性は原始入力からの出力とする。

### B. 標準錐のMayer–Vietoris列

三項複体をℤ次数へ零延長し、標準錐 $`D_X=\mathrm{Cone}(u_X)`$
($`X=A,B,U,I`$) を作る。Aの同じ図式から
$`0\to D_U\to D_A\oplus D_B\to D_I\to0`$ と全 $`m\in\mathbb Z`$ の
長完全列を構成する。連結射はcochain代表の持ち上げ・微分・貼り合わせで記述し、
mathlibの標準連結射と符号込みで同定する。

G-133の $`0\to\operatorname{coker}H^m(u_X)\to H^mD_X
\to\ker H^{m+1}(u_X)\to0`$ と接続する。
この列は隣接次数を保持する。$`J_A=J_B=0`$ から局所錐全体の消滅を結論しない。

### C. 一次欠損の正確な貼り合わせ

Aのコホモロジー列の差制限を
$`r_s^j:H^jC_{s,A}\oplus H^jC_{s,B}\to H^jC_{s,I}`$ とし、
$`Q_s=\operatorname{coker}r_s^0`$、$`P_s=\ker r_s^1`$ を構成する。
標準連結射・制限から $`0\to Q_s\to H^1C_{s,U}\to P_s\to0`$ を作り、
その粗細比較 $`q:Q_c\to Q_f`$、$`p:P_c\to P_f`$ の可換図式とsnake列

```math
0\to\ker q\to\mathrm{Ph}_U\to\ker p
\xrightarrow{\partial_{\rm sn}}\operatorname{coker}q
\to\mathrm{Hd}_U\to\operatorname{coker}p\to0
```

を、各写像の代表式を伴って証明する。
方向仮定 $`J_A=J_B=(0,0)`$ の下では
$`Z=\operatorname{im}r_c^1\cap\ker H^1(u_I)\subseteq H^1C_{c,I}`$ として

```math
\mathrm{Ph}_U\cong\ker q,\qquad
0\to\operatorname{coker}q\to\mathrm{Hd}_U\to Z\to0,
\qquad
J_U=(\dim\ker q,\dim\operatorname{coker}q+\dim Z)
```

および $`J_U=0\iff(q\text{ が同型かつ }Z=0)`$ を導く。
局所H⁰比較と交差の比較は元の写像のまま保持し、交差比較の全単射性を追加しない。

### D. 実Law診断と固定領域の係数・fiber分解への接続

各発生ラベル $`\lambda`$ の $`A_\lambda=\mathrm{labelValueFiber}`$ に対して、
A–Cを領域 $`A\cap A_\lambda,B\cap A_\lambda`$ へ適用する。
両領域が各 $`A_\lambda`$ を覆う場合、有限ラベル和をG-134の同じ
`generatedComparisonHom`・H¹商・標準錐へ同定する。
核・余核の和は `lawH1Defect_subset_sum` へ戻し、同じ台の異なるラベルの重複度を保持する。

通常の部分集合 $`X=A,B,U`$ では、同じ $`u_X,T_X,J_X`$ をG-135の
`directH1`・`coefficient_zeroDefect_iff`・`coefficientCokernel_shortExact` に接続する。
Cの領域方向の分解と、G-135の係数・fiber方向の分解が、同じ実核・余核を扱うことを
射・商の同定で示す。$`I_s`$ はAで独立に構成した対象である。

### E. 全有限幅の分離族と貼り合わせでの発火

任意の $`k\in\mathbb N`$ に対し、共通の有限概念集合 $`C_k`$、Source、reading対、
粗nerveを持つ二つの原始比較 $`M_k^+,M_k^-`$ を構成する。
観測は $`|X|\le k`$ の全 $`X\subseteq C_k`$ における
$`(H^1C_{c,X},H^1C_{f,X},T_X,J_X)`$ とする。
「一致」は各H¹の明示線形同型と比較の可換性、Jの等号を意味する。
観測値はこの同型で同一視した族とし、セル名や線形空間の表示による区別を含めない。
指定族ではこれらのH¹が全て零であることを証明する。

同時に、$`M_k^+`$ は全 $`X\subseteq C_k`$ で $`J_X=0`$、
$`M_k^-`$ は全真部分集合で $`J_X=0`$ かつ $`J_{C_k}=(0,1)`$ とする。
したがって上の幅kの観測だけを通る判定は、全ての有限原始入力での一様零欠損
$`\forall X,\ J_X=0`$ を決定できない。

Lawの観測幅は各発生値クラスの支持幅 $`|A_\lambda|`$ とする。
全発生ラベルが幅k以下である任意の同じ粗adequate Law族では、両入力の実Law H¹・比較・Jが
一致することも証明する。非一様性は同じSource上の定数Lawで検出する。
indicator Lawの補集合値クラスも、この幅条件で評価する。

指定族と $`A=\{c_0\},B=C_k\setminus A`$ にCを適用し、
$`Q_c=0,Q_f\cong\mathbb Q,Z=0`$ からhiddenの非零生成元を同じ実H¹類へ送る。
同じ例で $`I_f`$ が二点、$`N_{f,A_f\cap B_f}`$ が空であることも示す。
$`k=0`$ は指定された四角形の空領域観測として個別に確認する。

## 前提・構成台帳

| 対象・条項 | 役割 | 必要な構成・証拠 | 出所・使用先 |
| --- | --- | --- | --- |
| T0の有限性・ℚ・reading・K1・部分incidence | 一般入力。Eでは構成義務 | 既存型の全field | 元セル、実微分、Aの粗細比較 |
| A・Bおよび空領域 | 任意入力 | T0の量化 | 真のセル和・交差 |
| セル交差・SES・可換性 (A) | 構成・放電義務 | 元セルの所属、評価、延長、貼り合わせ | Bの錐SES、CのMV列 |
| 錐・連結射・Q/P・snake (B・C) | 構成・証明義務 | Aの完全性、標準API、同じ代表元 | 実phantom/hidden、次元式 |
| 局所J零 (C) | 特殊化だけの方向仮定。Eでは放電 | 同じ局所H¹射の同型 | ker p=0、coker pとZの同定 |
| Lawと粗adequacy (D・E) | 一般入力。指定Lawでは構成義務 | 細adequacy・発生ラベル・逆像 | 実Lawの比較と幅条件 |
| G-135固定X分解 (D) | 既存証明を再利用、同じ射への接続義務 | 実u・H¹・核商の同定 | 領域方向とfiber方向の結果照合 |
| 全kの有限入力対・生成元 (E) | 構成・証明義務 | 指定原始表、forest証明、閉路積分 | 全低幅一致、一様性の相違、Cの発火 |

完全列・期待rank・大域欠損を入力fieldへ移すと、A–Eの構成義務が残る。

## 完了条件

1. T0・A–Eを全量化・全方向でLeanに構成・証明する。Eは任意kの定理とし、有限個の数値検算はその代替にしない。
2. 成果を `research/lean/ResearchLean/AG/AtlasGluingWidth/`、条項と実宣言・前提の出所・使用先・指定例の対応を `research/reports/G-136-aat-atlas-gluing-width.md` に置く。
3. [共通基準の参照適用](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)に従う。
   固定主張への反例は反証として記録し、仮定・量化・指定例の変更は人間の判断に委ねる。
