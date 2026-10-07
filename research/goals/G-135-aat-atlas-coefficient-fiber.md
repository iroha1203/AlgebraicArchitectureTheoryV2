# G-135-aat-atlas-coefficient-fiber — Atlas欠損の係数・fiber分解

- `id`: `G-135-aat-atlas-coefficient-fiber`
- `status`: `active`
- `research mode`: `target-theorem`
- `tracking issue`: [#5290](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5290)
- `source note`: [n1016 §4.2・候補11](../../docs/note/n1016_rising_sea_v2_paper_plan.md)、[n1006 §1.2(e)・R8–R9](../../docs/note/n1006_aat_atlas_reinforcement_plan.md)
- `design`: [原始入力と順像](../designs/G-135-aat-atlas-coefficient-fiber/README.md)、[完全列と保存条件](../designs/G-135-aat-atlas-coefficient-fiber/exact-sequence.md)、[指定例](../designs/G-135-aat-atlas-coefficient-fiber/witnesses.md)、[再利用対応表](../designs/G-135-aat-atlas-coefficient-fiber/reuse-map.md)

## 研究目的

同じLaw・台・部分セル比較から生じるAtlas診断の核・余核を、粗側の係数と
順像係数の差、セル逆像fiberの一次コホモロジー、混在退化面による適合と
transgressionへ分解する。局所データから比較そのものを生成し、診断保存の
条件と、その条件を変える面の関係を求める。

[G-133](G-133-aat-atlas-defect-composition.md)の欠損合成・標準錐と、
[G-134](G-134-aat-face-relation-subdivision.md)の混在退化比較・実Law診断を使う。
新しい仕事は順像の構成、fiber項と完全列の同定、transgressionの消滅判定である。
Law値で定まるtarget部分集合と、セル写像で定まるchart逆像fiberを別々に保持する。

## 固定target

T0・A–E・Wを一つの構成・定理群とする。参照した設計の数学的定義・式・指定例も
固定要求に含める。新規構成の証明義務を以下に定める。

### T0. 原始入力と量化

有限Source、全射reading $`q_c\preceq q_f`$、有限な両側の
`TargetSupportedNerve`、G-134の `IncidenceSupportedComparison` $`M`$ を任意に取る。
chart写像は全域、辺・面は `Option` 値、係数はℚとする。
K1台、端点・面のincidence、chart台の包含、退化面の符号付き零和を保持する。
セル名、平行辺、loop、面での辺の重複出現を保持する。

幾何を固定した後、粗readingにadequateな任意の `FiniteLawFamily Source` と、
**すべての** $`A\subseteq q_c.\mathrm{Target}`$ を量化する。
$`\pi=\mathrm{comparisonFactor}`$、細側の選択は $`\pi^{-1}A`$ とする。
空A、空辺台・面台、空Law族を含め、Law値型全体の有限性は課さない。
細側adequacyと有限発生ラベルは既存生成経路から得る。

$`C_A,C'_A`$ は既存 `targetSubsetComplex`、$`u_A:C_A\to C'_A`$ は
Mの既存 `aSubnerveComparisonHom`、$`T_A=H^1(u_A)`$ とする。
一般構成にfiber連結性、非輪状性、辺・面の一意な持ち上げ、比較の単射・全射を加えない。

### A. 原始セルからの順像係数と実比較の因子化

[設計 §1–3](../designs/G-135-aat-atlas-coefficient-fiber/README.md)の有限incidence圏、
退化のcarrier関手、chart逆像複体 $`\Phi_c^A`$、辺の持ち上げの関係グラフ
$`\Gamma_e^A`$、面の持ち上げ集合を構成する。
順像係数 $`\mathcal P_A=\phi_{A*}\mathbb Q`$ はこの関手に沿う右Kan拡張とし、
各セルでの値を連結成分上の関数へ同定する。incidence射の作用と普遍性も証明する。
重複incidenceを持つ入力では、圏を単なるセル包含の半順序へ置き換えない。

この係数のcellular cochain複体 $`P_A`$ と、unitおよびセル評価から
$`\eta_A:C_A\to P_A`$、$`\varepsilon_A:P_A\to C'_A`$ を作る。
三次数すべてで、独立に生成済みの $`u_A=\varepsilon_A\eta_A`$ を証明する。
あわせて[設計 §4](../designs/G-135-aat-atlas-coefficient-fiber/README.md)の
退化セル生成部分複体 $`L_A\subseteq K'_A`$ を作り、
$`P_A\cong\operatorname{Hom}(K'_A/L_A,\mathbb Q)`$ と同じ写像を同定する。

### B. fiber項、完全列、transgression

[完全列 §1–3](../designs/G-135-aat-atlas-coefficient-fiber/exact-sequence.md)の
原始incidence行列から、混在面の関係による写像 $`\kappa_A`$ と

```math
R_A=\ker\left(\kappa_A^*:
  \bigoplus_c H^1(\Phi_c^A;\mathbb Q)\longrightarrow(\ker B_A)^*\right)
```

を構成する。$`B_A`$ は関係グラフのincidence行列である。
$`Q_A=\operatorname{Hom}(L_A,\mathbb Q)`$ について $`H^0Q_A=0`$、
$`H^1Q_A\cong R_A`$ を証明し、次数別短完全列
$`0\to P_A\to C'_A\to Q_A\to0`$ から全写像を持つ列

```math
0\to H^1P_A\xrightarrow{H^1\varepsilon_A}H^1C'_A
 \to R_A\xrightarrow{\tau_A}H^2P_A\to H^2C'_A
```

と各隣接三項の完全性を得る。最後の射の全射性は要求しない。
carrierの次数filtrationの $`E_2^{0,1}=R_A`$、$`E_2^{2,0}=H^2P_A`$ と
$`d_2=\tau_A`$ を、代表元・符号を含めて証明する。

一般の混在入力のfiber項は $`R_A`$ である。
関係グラフがforestなら $`R_A\cong\bigoplus_c H^1\Phi_c^A`$ を導く。
旧hereditary比較に属するpure classでは、さらに $`\tau_A=0`$ を原始セルから証明する。
一般入力の $`\tau_A=0`$ は同参照先§3の有限行列の包含条件と必要十分にし、
全Aでの消滅を有限個の入力検査へ接続する。

### C. 最終診断、保存条件、錐の対応

$`a_A=H^1\eta_A`$ として、実写像の商・部分空間の同定

```math
\ker T_A\cong\ker a_A,\qquad
0\to\operatorname{coker}a_A\to\operatorname{coker}T_A
  \to\ker\tau_A\to0
```

を構成する。[完全列 §4](../designs/G-135-aat-atlas-coefficient-fiber/exact-sequence.md)の
次元式、$`J_A=0\iff(a_A\text{ が同型かつ }\tau_A\text{ が単射})`$、
局所係数条件による十分条件、pure classでの必要条件C3′を証明する。
C3′の量化は「全Aで零欠損なら全非空A・全粗chartで $`H^1\Phi_c^A=0`$」である。
旧 `CoordinateFiberEdge` によるC3との違いを既存C3非必要性例へ実際に適用して確認する。

同じ二射と実直接比較から、標準錐
$`D_A^{\mathrm{coeff}}=\mathrm{Cone}(\eta_A)`$、
$`D_A^{\mathrm{fiber}}=\mathrm{Cone}(\varepsilon_A)`$、
$`D_A^{\mathrm{total}}=\mathrm{Cone}(u_A)`$ の合成triangleを作る。
$`D_A^{\mathrm{fiber}}\to Q_A`$ の擬同型、全次数の錐完全列、Bの連結射との対応を証明する。
G-133の相殺写像は $`\ker H^1\varepsilon_A=0`$ を始域として零になることを示し、
W3の非零 $`\tau_A`$ と区別する。

### D. Law・台制限とG-134への接続

Lawの各発生ラベル $`\lambda`$ で $`A_\lambda=\mathrm{labelValueFiber}`$ を選び、
既存の実 `lawGeneratedComplex`・混在 `generatedComparisonHom` へA–Cを接続する。
全三次数・既存H¹商・標準錐・完全列の各写像で可換図式を構成し、
Lawの欠損を同じblockの和へ戻す。同じ台のラベルの重複度を保つ。
全 $`A\subseteq A'`$ の制限に対して順像・二射・fiber適合・連結射を自然にする。

G-134の三角形追加、面に接する辺分割、reading pullback、およびそれらの
部分セル比較としての有限合成に、この分解を適用する。
同じ実比較のH¹同型と全次数の錐消滅を既存定理へ同定し、
$`a_A`$ の同型性と $`\ker\tau_A=0`$ を導く。
逆向き有限和写像はG-134の既存ホモトピーによる保存証拠に使う。
Pの構成対象はT0の部分セル比較とする。
面複製にはH¹保存と非零H²余核を同時に対応させ、H¹零欠損から錐全体の消滅を推論しない。

### E. 原始条件からの有限判定

全構成の有限性を入力から導き、連結成分、incidence行列、核・像・商の有理線形代数から、
$`a_A,R_A,\tau_A,J_A`$ と消滅条件を計算する手順を与える。
返す行列がA–Dの同じ写像の表示であることを証明し、
全Aおよび有限発生ラベルでの保存判定を既存 `blockDefect` へ接続する。

### W. 同じ原始入力からの例と反例

[指定例W1–W5](../designs/G-135-aat-atlas-coefficient-fiber/witnesses.md)のセル表、
比較、Law、台、同時成立条件を固定する。
W1は係数だけによる核・余核、W2はpureなfiber閉路、W3は非零transgression、
W4はG-134の面あり・なしと面複製、W5は混在面によるfiber適合条件の必要性を示す。
各例の原始表から実診断までをA–Eの同じ経路で評価する。

## 前提・構成台帳

| 対象・条項 | 役割 | 必要な構成・証拠 | 出所・使用先 |
| --- | --- | --- | --- |
| T0の有限入力・ℚ・K1・部分incidence | 入力として保持。Wでは構成義務 | 既存型のfield、退化パターン | Aのcarrier・支持複体 |
| Lawと粗adequacy | 一般入力。細adequacyは導出 | 発生ラベルと値の逆像 | Dの実Law比較 |
| incidence圏・順像・unit・評価・商同定 (A) | 構成・証明義務 | セルごとの極限、普遍性、全次数等式 | Bの短完全列、Cの実直接射 |
| fiber適合・完全列・filtration・transgression (B) | 構成・証明義務 | 原始行列、標準連結射、代表元 | C・E・W2–W5 |
| pure、forest、局所係数条件 (B・C) | 各特殊化だけの方向仮定。Wでは放電 | 原始退化表・連結成分・持ち上げ集合 | 消滅・保存・C3′ |
| 同型・完全性・擬同型・有限次元性 (A–E) | 出力として証明 | 商・核・像と標準APIへの接続 | `blockDefect`、錐、有限判定 |
| Law分解・制限・G-134 (D) | 既存対象・写像を再利用し、新項の自然性を証明 | 同じ比較での可換図式 | 全Lawの最終診断 |
| W1–W5 | 全入力と指定値の構成・証明義務 | 原始表→同じ二射→代表類・診断 | 非零性と各仮定の必要性 |

P、完全列、fiber同定、期待rankを入力として渡すと、A・B・Eの構成義務が残る。

## 完了条件

1. T0・A–E・Wを全量化・全方向でLeanに構成・証明し、一つのGOALとして達成する。
   一般錐triangleだけでなく、原始セルから順像・fiber項・実診断までの接続を含める。
2. Lean成果を `research/lean/ResearchLean/AG/AtlasCoefficientFiber/`、
   固定条項・宣言・前提の出所と使用先・同じ写像・全指定例の証拠対応を
   `research/reports/G-135-aat-atlas-coefficient-fiber.md` に置く。
3. [共通基準の参照適用](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)
   に従う。Bの一般混在入力をpure・forestだけへ縮小せず、W3とW5を区別して検証する。
   固定主張への反例は反証として記録し、仮定追加・量化縮小・指定例の変更は人間の判断を要する。
