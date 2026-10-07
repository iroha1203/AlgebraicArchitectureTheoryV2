# G-134-aat-face-relation-subdivision — 面の関係を用いた診断保存細分化

- `id`: `G-134-aat-face-relation-subdivision`
- `status`: `completed`
- `research mode`: `target-theorem`
- `tracking issue`: [#5272](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/5272)
- `source note`: [n1016 §4.5・候補08](../../docs/note/n1016_rising_sea_v2_paper_plan.md)
- `design`: [構成と依存関係](../designs/G-134-aat-face-relation-subdivision/README.md)、[基本変形](../designs/G-134-aat-face-relation-subdivision/elementary-moves.md)、[指定例](../designs/G-134-aat-face-relation-subdivision/witnesses.md)、[再利用対応表](../designs/G-134-aat-face-relation-subdivision/reuse-map.md)

## 研究目的

同じ粗辺へ写る複数の細辺を、明示的な三角面の関係で結び、辺の分割・三角形追加・
その逆縮約がLaw診断を保存する条件と構成を与える。各変形から比較、逆向きの写像、
鎖ホモトピーを生成し、有限合成を経て既存の実診断複体へ接続する。

[G-133](G-133-aat-atlas-defect-composition.md)の合成・零延長・Law分解・写像錐を基盤とする。
新たに扱うのは、三辺の像が個別には零でなくても符号付きの和が零になる退化面と、
その原始入力からの局所変形である。例3.25のC5非必要性から、変形を実行して
同じ診断類を往復させる構成へ進む。

## 固定target

T0・A–E・Wを一つの定理・構成群として要求する。以下の新規構成と接続は証明義務である。
参照する基本変形の定義と指定例の原始データ・同時成立条件も固定targetに含む。

### T0. 原始入力と量化

有限な `Source`、全射reading、有限な `TargetSupportedNerve` を入力とする。
chart台は非空、辺・面の台は既存K1の交差、三角面のincidence符号は
$`\partial_1 e=[\operatorname{right}e]-[\operatorname{left}e]`$、
$`\partial_2 f=[e_0]-[e_1]+[e_2]`$ とする。
セル名は独立な名前であり、平行辺、loop、同じ面での辺の重複出現を含む。

まずこの幾何と操作列を固定し、その後に、最初のreadingにadequateな任意の
`FiniteLawFamily Source` と、**すべての**target部分集合 $`A`$ を量化する。
係数はℚ。Law値型自体の有限性は仮定せず、Sourceで発生する `LawValueLabel laws`
を用いる。空の $`A`$、空の辺台・面台、空のLaw族も含める。

比較を作る一般部分A・Dでは、任意の $`q_c\preceq q_f`$ と両側のsupported nerveを取り、
$`\pi=\mathrm{comparisonFactor}(q_c,q_f)`$ に沿うchart台の包含を課す。
基本変形Bは同じreading上で行う。readingを細かくする段には、セル名・incidenceを保ち
chart台を $`\pi^{-1}`$ で引き戻す操作だけを許す。操作列の各段で
$`A_i=\pi_{0i}^{-1}A`$ とし、同じreading内の操作では $`A_i`$ を変えない。
細readingのadequacyは粗側から導出する。

$`K_*(N,A)`$ は台が $`A`$ と交わるセルを基底とする有限自由chain複体として構成する。
その双対と既存 `N.targetSubsetComplex A`、各Lawの実 `N.lawGeneratedComplex`
の同定はDの出力であり、入力として受け取らない。

### A. 混在退化面からの生成比較

細→粗のchart全域写像とedge・faceの `Option` 写像を取り、写る辺の端点、
写る面の三つのedge番号、退化辺の端点一致、chart台の適合を既存比較と同様に課す。
退化面については、粗辺の自由アーベル群で

```math
\overline r_1(e_0)-\overline r_1(e_1)+\overline r_1(e_2)=0,
\qquad \overline r_1(e)=
\begin{cases}[r_1(e)]&r_1(e)\ne\mathrm{none},\\0&\text{otherwise}\end{cases}
```

という原始incidence条件を課す。各辺が個別に零であることは要求しない。
このデータから各 $`A`$ のchain写像、各Lawの粗→細のcochain写像とH¹写像を生成する。
恒等と `Option.bind` による比較合成が同じ条件を満たし、直接生成と合成が
全三次数・既存H¹商で一致することを示す。

旧 `TargetSupportedNerveMorphism` からの埋め込みと、旧生成Hom・block比較・
部分集合比較・H¹写像との一致を証明する。単なる端点一致への弱化を退ける
既存 `DegenerateFaceComm1Obstruction.generated_pullback_comm1_fails` の入力で、
上の原始incidence条件が実際に破れることも示す。

### B. 基本変形と台を保つ収縮

許容する強い基本変形は[基本変形 §1–5](../designs/G-134-aat-face-relation-subdivision/elementary-moves.md)
で定義する次の操作と、そのセル名・台を保つ同型による表示変更である。

1. 元の $`e_1:v\to w`$ を残し、freshな $`v',c:v\to v',e_2:v'\to w,f`$ と
   $`\partial f=c+e_2-e_1`$ を加える。$`S(v')=S(v)`$ とする。
2. 任意の辺 $`e:v\to w`$ を $`c:v\to v',b:v'\to w`$ に分割し、元の辺を除く。
   既存の各三角面について、$`e`$ の**各出現**に別名の対角辺と三角面を設けて
   再三角形化する。対象辺が面に接する場合、loop、符号の異なる重複出現を含む。
3. 1・2で指定した局所セル・全接続・台から元の入力を復元する逆縮約。
4. T0の台の逆像によるreading変更。

freshness、台の等号、逆縮約時の局所セルへの全接続条件は同参照先で先に固定する。
各操作から、すべての $`A`$ と各Law成分で $`r:K'\to K`$、$`s:K\to K'`$、
$`h_n:K'_n\to K'_{n+1}`$ を構成し、

```math
rs=1_K,\qquad 1_{K'}-sr=\partial h+h\partial
```

を証明する。三角形追加では $`r(v')=v,r(c)=0,r(e_2)=e_1,r(f)=0`$、
旧セル上の $`r,s`$ は恒等、$`h_0(v')=c,h_1(e_2)=f`$ とする。
他の操作の式は同参照先に固定する。逆縮約では同じ二写像を逆方向に用いる。
台を保つこととchain式を原始データから証明し、双対のcochain鎖ホモトピー同値、
H⁰・H¹・H²の同型を得る。
さらに、指定した三角面で結ばれる持ち上げの選択に対して、読み戻すH¹類が一致することを示す。
比較する道と補正の式は[基本変形§7](../designs/G-134-aat-face-relation-subdivision/elementary-moves.md#7-持ち上げの選択とcochain代表)に定める。

### C. 有限合成と選択の自然性

Bの操作・逆縮約からなる任意の有限列を量化し、原始セルの像の有限和から直接比較を作る。
比較・逆・二つの鎖ホモトピーを有限帰納で構成し、直接比較のcochain化が
各段の生成写像の合成と一致することを示す。空列、恒等、括弧づけの変更も含める。
同じ始終点を持つ異なる操作列の比較の一致までは要求しない。

すべての $`A\subseteq B`$ に対する支持セルの包含、双対の制限と、比較・逆・
ホモトピーが可換であることを示す。同じ台を持つ複数Lawラベルを個別の成分として保つ。
全Lawの実H¹比較は同型、したがって `blockDefect` の核・余核の二成分はともに零となる。
G-133の合成・錐APIへこの同じ写像を渡し、強い基本変形と有限合成の錐の
全次数のcohomologyが零になることを示す。

### D. 第3章の実診断への同定

生成経路を
$`\mathrm{Source}\to\mathrm{Reading}\to\mathrm{Law}\to\text{支持セル}\to
\text{微分}\to\text{同じ比較}`$ とする。既存 `CellCoordinate`、K1台、
`lawGeneratedD0/D1` を用いてA・BのLaw比較を独立に生成し、
各ラベル $`\lambda`$ のfiber $`A_\lambda`$ のchain双対比較と全三次数で一致させる。
これを既存 `ThreeCochainComplex.Hom.h1Map`、G-133の `oldH1Equiv` と
その自然性、Law分解、標準錐へ接続する。

旧hereditary比較を引数に取る自然性・錐分解・欠損分解APIについては、新比較クラス用の
接続補題を構成する。対象複体の既存同値があることだけで、射の接続済みとはしない。
細分化の逆 $`s`$ は辺や面を有限和へ送るため、そのLaw座標での有限和の式も構成する。

### E. H¹保存と全次数保存の区別

対照操作として、既存面 $`F`$ と同じ三辺・台を持つ別名の面 $`\widehat F`$ を一枚追加し、
旧セルを恒等、$`\widehat F\mapsto F`$ とする比較を取る。
同じ実生成比較がすべての $`A`$ と各LawでH¹を保存することを示す。
$`F`$ が選択される成分では、H²比較の余核がℚ、写像錐のH²もℚとなることを構成し、
この操作がBの全次数の鎖ホモトピー同値とは異なることを証明する。

### W. 原始入力からの指定例

[指定例 W1–W3](../designs/G-134-aat-face-relation-subdivision/witnesses.md)のデータを固定する。
セル名の符号化と内部の線形代数表現は選べるが、同じ入力・比較での次の同時成立条件を保つ。

- **W1**：真のreading細分と非定数Lawを持つ三角形追加のpaired witness。
  変更部分と同じ連結成分に非零閉路を残す。面ありでは各ラベルのH¹比較が同型、
  面だけを除くとH¹が一自由度増し、同じ比較の余核がℚとなる。
  全Lawでは二ラベルの重複度を保持し、余核がℚ²となる。
- **W2a–c**：面に接する辺の実再三角形化、loopの三重出現、空辺台をそれぞれ構成し、
  Bの同じ式とDの生成経路を適用する。W2aでは台により $`c`$ だけが残る成分も扱う。
- **W3**：Eを非零H¹のある連結入力で実現し、H¹保存と非零H²余核を同時に示す。

## 前提・構成台帳

| 対象・条項 | 役割 | 必要な構成・証拠 | 出所・使用先 |
| --- | --- | --- | --- |
| 有限Source・reading・supported nerve・ℚ (T0) | 入力として保持。Wでは構成 | 既存型の有限性・全射・K1・incidence | 支持セルと微分の生成 |
| 任意Lawと粗adequacy (T0) | 一般入力。Wでは原始評価から証明 | 細adequacy・降下・有限発生ラベル | A・Dの同一ラベル輸送 |
| 原始incidence条件・chart台包含 (A) | 一般比較の仮定。B・Wでは放電義務 | 符号付きセル像の等式 | 各台のchain写像、Lawのcomm1 |
| freshness・台等号・逆縮約の全接続 (B) | 許容操作の原始入力条件 | 基本変形§2–5の構成条件 | 新セル生成、支持を保つr・s・h |
| r・s・h、chain式、全次数同型 (B・C) | 構成・証明義務 | セルごとの式と有限合成 | Dの実比較、零欠損、錐の零性 |
| 全A、空台、loop、重複出現 (T0・B) | 量化に含める入力 | 台選択と出現位置を保持 | W2、制限の自然性 |
| 旧比較の埋め込みと比較写像の接続 (A・D) | 新規接続義務 | 既存生成Homとの成分等号 | G-133の射に依存するAPI |
| H¹商・零延長・Law分解・錐 (C・D) | 既存一般APIを再利用 | 再利用対応表の型と接続補題 | 同じ診断類・写像・欠損 |
| 対照操作と指定例 (E・W) | 原始入力からの構成・証明義務 | cocycle、period、実像・余核 | 全次数保存との区別、非空虚性 |

chain写像・逆・ホモトピー・期待rank・診断同型を操作の入力fieldに移すことは、
B・D・Wで求める構成を未放電にする。

## 完了条件と弱化防止

1. A–E・Wの全義務を一つのGOALとしてLeanで証明する。基本変形の抽象的な保存補題、
   三角形追加だけ、または全台・面なしの場合だけでは全体の完了としない。
2. Lean成果を `research/lean/ResearchLean/AG/FaceRelationSubdivision/`、宣言・前提の
   出所と使用先・固定条項・指定例の証拠対応を
   `research/reports/G-134-aat-face-relation-subdivision.md` に置く。
3. [共通基準の参照適用](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)
   に従う。実診断との全次数の可換図式、旧比較への特殊化、支持制限、有限合成を含む。
4. W1の面だけを除く比較を別の写像へ替えること、非零閉路を別成分へ移すこと、
   Wの生成経路を任意行列や期待rankの仮定で代替することは要求未達とする。
   固定主張の反例は `target-refuted`、未接続は未完了、仮定追加・量化縮小・指定例変更が
   必要なら `goal defect` として扱い、目標を自動で弱めない。
