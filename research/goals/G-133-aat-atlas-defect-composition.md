# G-133-aat-atlas-defect-composition — Atlasの欠損対象と解像度比較の合成

- `id`: `G-133-aat-atlas-defect-composition`
- `status`: `completed`
- `research mode`: `target-theorem`
- `tracking issue`: [#5261](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5261)
- `source note`: [n1016 §4.1・候補07](../../docs/note/n1016_rising_sea_v2_paper_plan.md)、[n1006 §1.2(a)–(d)・(f)、R14](../../docs/note/n1006_aat_atlas_reinforcement_plan.md)
- `design`: [構成・依存関係](../designs/G-133-aat-atlas-defect-composition/README.md)、[再利用対応表](../designs/G-133-aat-atlas-defect-composition/reuse-map.md)、[台署名の構成](../designs/G-133-aat-atlas-defect-composition/support-signatures.md)、[指定例](../designs/G-133-aat-atlas-defect-composition/witnesses.md)

## 研究目的

同じ有限AAT入力から生成した解像度比較について、中間解像度で生じた診断方向が
次の比較で消える仕組みを、類・写像・商を保持したまま説明する。
生成比較の合成、核・余核の相殺、写像錐、Lawごとの分解、台署名による商と普遍性、
台の包含に沿う欠損の輸送を一つの構成へ結ぶ。有限多段比較も同じ構成から得る。

[G-104](G-104-aat-resolution-invariance.md)はLaw・台・セルから比較とラベル分解を、
[G-107](G-107-aat-uniform-invariance-characterization.md)は部分集合ごとの実比較と
核・余核の次元による欠損を与えた。標準の完全列・写像錐や既存分解は再利用する基盤である。
今回明らかにするのは、それらとAATの生成経路との一致、同じ原始入力での非零相殺、
比較セルを保持する台の普遍性である。G-132の整数修復障害の零性反映とは異なるtargetであり、
再利用するグラフ座標APIは[対応表](../designs/G-133-aat-atlas-defect-composition/reuse-map.md#2-g-132からの再利用)で区別する。

## 固定target

T0、A–F、Wを一つの定理・構成群として要求する。以下は研究targetであり、
新規部分のLean証明を意味しない。固定要求の詳細を参照する場合も、参照先の該当節を含めて固定する。

### T0. 入力、比較の向き、量化

有限な `Source` を固定する。その上の三つの全射reading
$`q_0\preceq q_1\preceq q_2`$（`Reading.CoarserThan`）、各reading上の
$`N_i : \mathrm{TargetSupportedNerve}(q_i)`$、隣接する二つの
`TargetSupportedNerveMorphism` $`M_{01},M_{12}`$ を任意に取る。
chart台は非空、辺・面の台は既存K1の交差で作る。セルは有限で、面の三つの端点整合式を持つ。
比較のchart写像は全域、辺・面の写像は `Option` 値であり、退化辺の端点一致と
退化面の全三辺の退化を含む既存のincidence条件を入力幾何として保持する。

セル写像は細→粗、生成cochain写像は粗→細である。
$`\pi_{ij}:q_j.\mathrm{Target}\to q_i.\mathrm{Target}`$ は既存 `comparisonFactor` で作る。
読みの順序だけでセル比較は一意にならず、$`M_{ij}`$ 自体を量化する。
cochain写像・H¹写像・合成の一致・完全性は構成／証明する出力である。

この幾何を固定した後、$`q_0`$ にadequateな任意の `FiniteLawFamily Source` を量化する。
細かい二つのreadingでのadequacyは因子化から導く。Lawの値型全体の有限性は仮定せず、
Sourceで発生する有限な `LawValueLabel laws` を使う。
さらに **すべての** $`A\subseteq q_0.\mathrm{Target}`$（空集合を含む）について
$`A_0=A`$、$`A_i=\pi_{0i}^{-1}A`$ と置く。

- $`C_i(A_i)`$ は既存 `targetSubsetComplex`、$`u_{ij,A}`$ は既存
  `aSubnerveComparisonHom` をこれらの部分集合へ適用して生成する。
- Law全体の $`C_i(L)`$、$`u_{ij,L}`$ は既存 `lawGeneratedComplex` と
  `generatedComparisonHom` を使う。誘導H¹写像も既存の商と `h1Map` を使う。

一般条項に `ConditionC`、H¹の単射性・全射性、face型の空性を追加しない。
Fでは任意の有限列 $`q_0\preceq\cdots\preceq q_n`$ とその全隣接セル比較を量化し、
各部分集合を同じ $`q_0`$ から引き戻す。

### A. 生成比較の合成と直接比較

隣接比較のchart写像の合成と、辺・面の部分写像の `Option.bind` から
$`M_{02}`$ を構成し、T0の全incidence・台条件を証明する。恒等・結合則も示す。
$`\pi_{02}=\pi_{01}\circ\pi_{12}`$、対応するLaw降下の一致、
$`A_2=\pi_{12}^{-1}(\pi_{01}^{-1}A)`$ を証明する。

この $`M_{02}`$ に既存の生成手続きを適用した直接比較について、次数0・1・2の全成分で

```math
u_{02,A}=u_{12,A_1}\circ u_{01,A},\qquad
u_{02,L}=u_{12,L}\circ u_{01,L}
```

を示し、H¹商へ降ろした同じ等式を証明する。直接比較をcochain写像の合成として定義して
この義務を代替しない。ラベル同定と部分集合同定を伴う等式も含める。

### B. 相殺写像と欠損の合成

同じAについて $`U=H^1C_0(A)`$、$`V=H^1C_1(A_1)`$、$`W=H^1C_2(A_2)`$、
$`f=H^1u_{01,A}`$、$`g=H^1u_{12,A_1}`$ とする。
$`\chi:\ker g\to V/\operatorname{im}f`$ を $`v\mapsto[v]`$ で構成し、
次の全写像と完全性を実比較へ接続する。

```math
0\longrightarrow\ker f\longrightarrow\ker(gf)
 \xrightarrow{f}\ker g\xrightarrow{\chi}\operatorname{coker}f
 \xrightarrow{[v]\mapsto[g v]}\operatorname{coker}(gf)
 \xrightarrow{[w]\mapsto[w]}\operatorname{coker}g\longrightarrow0.
```

ここで $`gf=H^1u_{02,A}`$ はAの定理による同定である。
$`\operatorname{im}\chi\cong\ker g/(\ker g\cap\operatorname{im}f)`$
（分母は $`\ker g`$ 内の部分空間として取る）と、
既存 `blockDefect` の二成分について

```math
\begin{aligned}
\dim\ker(gf)+r&=\dim\ker f+\dim\ker g,\\
\dim\operatorname{coker}(gf)+r
 &=\dim\operatorname{coker}f+\dim\operatorname{coker}g,
\qquad r=\dim\operatorname{im}\chi
\end{aligned}
```

を証明する。これはn1016の減算式と同値な自然数の等式である。
相殺するのは「後段で消え、前段の像でもない中間の診断類」の商であり、
代表cocycleと実生成写像でその意味を示す。Law全体にもDの同定を通して同じ構成を適用する。

固定された共通A、または共通Law族に対する零欠損は恒等・合成で閉じ、
$`f,g,gf`$ のうち二つの零欠損から残る一つの零欠損が従う。
量化域はT0の共通入力であり、$`q_1`$ 上だけにadequateなLawを途中から加えない。

### C. 写像錐と各次数の寄与

既存三項複体を次数0–2以外零の $`\mathbb Z`$ 添字cochain複体へ移し、
既存H¹商・比較との自然な線形同型を構成する。
各生成写像 $`u:C\to C'`$ に対して標準の写像錐を

```math
D(u)^m=C'^m\oplus C^{m+1},\qquad
d(y,x)=(d' y+u x,-d x)
```

という符号と順序で読む。これは次数−1–2を持ち、mathlibの写像錐と同型にする。
標準長完全列から、任意の整数 $`m`$ について自然な短完全列

```math
0\to\operatorname{coker}H^m(u)\to H^mD(u)
  \to\ker H^{m+1}(u)\to0
```

を構成する。特に
$`\dim H^0D=\dim\operatorname{coker}H^0(u)+\dim\ker H^1(u)`$、
$`\dim H^1D=\dim\operatorname{coker}H^1(u)+\dim\ker H^2(u)`$、
$`H^{-1}D\cong\ker H^0(u)`$、$`H^2D\cong\operatorname{coker}H^2(u)`$ を示す。
零欠損はH¹の比較同型を意味する。錐全体の消滅には他次数の比較も必要である。

### D. Lawによる分解と同じ部分集合比較への接続

各発生ラベル $`\lambda=(\ell,v)`$ の粗側fiber $`A_\lambda`$ と、細側でのその逆像を使い、
既存の次数別block同値・H¹同値・比較自然性を一つの可換図式へ接続する。
そこから実比較の核・余核、Cの錐とその短完全列、Bの六項完全列と相殺写像を
ラベル別の有限直和へ分解する。特に

```math
D(u_L)\cong\bigoplus_\lambda D(u_{A_\lambda}),\qquad
J_L=\sum_\lambda J_{A_\lambda},\qquad r_L=\sum_\lambda r_{A_\lambda}
```

を、元と写像の同定を伴って証明する。同じ台署名を持つ複数ラベルの重複度を保持する。
非空Aは既存の指示Lawのtrue blockで実現し、空Aは零複体として処理する。
指示Law全体には補集合のblockもあるため、Aの単独blockとLaw全体を区別する。

### E. 台署名の商、普遍性、欠損の輸送

一つの実比較Mを固定する。$`\Omega_M`$ は両側の次数0・1・2のセルを
側・次数・元のセル名で区別した有限集合とする。
粗target $`t`$ が粗セルの台に属する、または細セルの台に
$`\pi^{-1}\{t\}`$ の点があるときに、そのセルを $`S_t`$ に含める。
この定義から

```math
\alpha(A)=\bigcup_{t\in A}S_t,\quad
\gamma(X)=\{t\mid S_t\subseteq X\},\quad
\mathrm{cl}=\gamma\alpha,\quad
A\sim B\ \Longleftrightarrow\ \alpha(A)=\alpha(B)
```

を構成する。$`\alpha\dashv\gamma`$、閉包の法則、join合同、
$`\Sigma_M=\mathcal P(q_0.\mathrm{Target})/{\sim}\cong\operatorname{im}\alpha
\cong\operatorname{Fix}(\mathrm{cl})`$ を証明する。空集合の署名をbottomとして含める。
同じ署名は、選択セル・incidence・退化宣言・比較写像を同定し、その上の複体・錐も同定する。

普遍性が量化する対象は、有限join半束Lとbottom・joinを保つ全射
$`p:\mathcal P(q_0.\mathrm{Target})\to L`$、同じ演算を保つ
$`d:L\to\mathcal P(\Omega_M)`$ で $`d\circ p=\alpha`$ を満たす組とする。
射 $`h:(L,p,d)\to(L',p',d')`$ はbottom・joinを保ち
$`h\circ p=p'`$、$`d'\circ h=d`$ を満たす写像である。
この圏で $`(\Sigma_M,\sigma,\iota)`$ が終対象であることを証明する。
対象の条件は全セル選択の復元を要求する。

あわせて、署名が等しいAを同一視する任意のbottom・join準同型は
$`\sigma`$ を通して一意に因子化する、という通常の商の普遍性を示す。
Law側は[台署名の構成 §4](../designs/G-133-aat-atlas-defect-composition/support-signatures.md#4-lawの再添字づけと加法的な普遍性)
の有限block族・射・加法的評価を対象とし、重複度付きの署名からDを復元する。
診断次元または零性の一致だけによる同一視との相違をW2で示す。

$`A\subseteq B`$ に沿うセル包含からcochainの制限を作り、
$`\Sigma_M^{op}`$ 上の両側の複体関手と比較自然変換、錐関手、H¹比較の
核・余核関手を構成する。三段では全段のセルを含む共通署名を使い、各対への射影の下で
Bの全写像が自然になることを示す。$`J_A`$ はこの核・余核関手の次元表である。

### F. 三段の錐の合成と有限多段比較

Aの同一視の下で、Cの実写像錐から
$`D(u_{01})\to D(u_{02})\to D(u_{12})\to D(u_{01})[1]`$
という標準のdistinguished triangleを構成し、実cochain式・符号・台制限・Law分解との対応を示す。
BはH¹写像の核・余核の完全列として、Cは錐の全次数の列として、それぞれ保持する。

任意の有限段数について、累積比較の錐と隣接比較の錐を結ぶ有限towerを構成する。
さらに累積錐にchain homotopy同値な有限複体と有限filtrationを与え、
その逐次商を対応する隣接錐へchain homotopy同値にする。
元の写像の単射性は仮定せず、必要なmapping cylinder等のモデル変更は構成する。
三段への特殊化、台制限・Law分解との整合を証明する。

### W. 同じ生成経路を通る指定例

[指定例W1–W3](../designs/G-133-aat-atlas-defect-composition/witnesses.md)の原始データと
同時成立条件を固定targetに含める。

- **W1**：一つのSource、三つの真に異なるreading、共通の非定数Law、三角形→二三角形→三角形の
  粗→細比較から、非零H¹上で前段の余核・後段の核・相殺写像が非零、直接比較の欠損が零となる例を作る。
- **W2**：異なるセル署名で同じ零欠損、真に大きくなる閉包、同署名の異なる部分集合を、
  一つの原始入力で示す。W1の二ラベルで再添字づけ後も重複度が必要なことを示す。
- **W3a・W3b**：零H¹欠損と非零 $`\operatorname{coker}H^0`$、零H¹欠損と非零
  $`\ker H^2`$ をそれぞれ実セル入力から作り、Cの追加寄与を計算する。

## 前提・構成台帳

| 対象・条項 | 役割 | 必要な構成・証拠 | 出所・使用先 |
| --- | --- | --- | --- |
| 有限Source、全射reading、K1支持セル、部分incidence比較 (T0) | 入力として保持。Wでは全条件を証明 | 既存型の全fieldと粗細の向き | Aの比較生成、Eのセル選択 |
| 有限Law、粗readingのadequacy (T0) | 一般入力。W・指示Lawでは構成義務 | 細readingのadequacy、発生ラベル、降下 | A・Dの同一ラベル比較 |
| 合成比較、因子化の一意性、生成Hom・H¹合成 (A) | 構成・証明義務 | Aの全次数と商の等式 | B・Fの直接比較 |
| 有限次元性、線形代数の完全列 (B) | 前者は既存有限複体から導出、後者は標準結果を接続 | 実H¹写像、商の射、相殺類 | Bの欠損等式、W1 |
| ℤ添字複体、H¹同型、錐・長完全列 (C) | 構成・接続義務 | 既存商・mathlib APIへの自然な同定 | D・F、W3 |
| block分解、部分集合への同定 (D) | 既存同値と自然性を再利用、錐・核・余核への接続は新規義務 | 同じLawと同じセルでの可換図式 | B・Eの集約、W1 |
| 台のGalois接続・商・普遍性 (E) | 原始台からの構成・証明義務 | 全セルを復元する対象・射、重複度付きLaw族 | 比較・欠損関手、W2 |
| $`H^0(u)`$ 全射、$`H^2(u)`$ 単射 | Cの追加項を消す場合だけの方向仮定 | 各追加項の零性との同値 | 条件付き同型。一般入力には加えない |
| 錐の合成triangle、多段filtration (F) | 標準構成を実比較へ接続する義務 | 累積比較、モデル変更と逐次商の同値 | 多段の欠損対象 |
| W1–W3 | 全入力条件と指定結論の構成・証明義務 | 原始表→実生成写像→類・相殺・追加寄与 | 一般条項への非空虚な適用 |

結論との循環を検査する箇所は、直接比較の定義、Bの完全性の入力化、Eのdecoder、
Wの比較行列の出所である。比較と診断を結論に合わせて選び直す経路は、該当条項を満たさない。

## 完了条件と弱化防止

1. A–FとWの全構成・全方向をLeanで証明し、一つのGOALとして `target-theorem-proved` を得る。
   合成等式または標準六項完全列だけの証明は到達点であり、全体の完了ではない。
2. Lean成果は `research/lean/ResearchLean/AG/AtlasDefectComposition/`、証拠対応は
   `research/reports/G-133-aat-atlas-defect-composition.md` に置く。条項、実宣言、
   premiseの出所・使用先、生成写像、指定例の評価、受理した先行成果の参照版を対応させる。
3. [共通基準の参照適用](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)
   に従う。proof artifacts・focused検証・公理監査・完了査読はそこで定める版を適用する。
4. W1の抽象行列だけの検証、Eの診断値だけを保存する商への置換、Cの次数の削除、
   2-cellを持つ一般入力のグラフへの縮小は、それぞれ対応条項の要求未達とする。
   固定主張への反例は `target-refuted`、構成未接続は未完了、仮定追加・量化縮小・
   必須例の差し替えが必要なら `goal defect` として人間へ報告する。

理論の保証はT0から生成する有理複体と実比較についての定理である。
ArchSigへの採用は、その入力表・係数・生成式・出力とこの構成との対応を別途検証して行う。
対応する実装箇所と保証範囲は[設計 §7](../designs/G-133-aat-atlas-defect-composition/README.md#7-理論とarchsigの保証範囲)に記す。
