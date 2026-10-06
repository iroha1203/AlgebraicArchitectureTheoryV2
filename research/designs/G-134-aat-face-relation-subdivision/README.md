# G-134：混在退化比較と実Law診断への接続

[GOAL T0・A–E・W](../../goals/G-134-aat-face-relation-subdivision.md)の構成を、
[基本変形](elementary-moves.md)、[指定例](witnesses.md)、[再利用対応表](reuse-map.md)へ分ける。
新比較クラスと以下の接続補題は未証明の構成義務である。

## 1. 原始incidenceと生成比較

既存 `TargetSupportedNerveMorphism` は `faceMap f = none` から
`face_none_edge0/1/2` によって三辺の `edgeMap = none` を要求する。
混在退化を扱う新しい比較型は、これら三fieldをGOAL Aの自由アーベル群の等式に置き換える。
他のfieldは保つ。仮の名前を `IncidenceSupportedComparison` とする。
この型にcochain写像・H¹同型・ホモトピーをfieldとして入れない。

`Option` の基底への読み替えを $`[\mathrm{none}]=0`$、$`[\mathrm{some}(e)]=[e]`$
と書く。面 $`f=(c,e_1,e_2)`$ の縮約では
$`0-[E]+[E]=0`$ になる。端点だけの条件では、coarse loop $`E`$ に写る
同一辺が三回現れて $`[E]-[E]+[E]=[E]\ne0`$ となり得る。
後者は既存 `DegenerateFaceComm1Obstruction` の実Law反例である。

構成は次の順に接続する。

1. chart適合と写る辺の端点から、辺台の像の包含を導く。写る面には三辺の適合から
   面台の像の包含を導く。
2. 台が $`A`$ と交わるセルの自由ℚ加群を次数0–2に作り、incidenceから $`\partial`$ を定める。
   面の端点等式から $`\partial_1\partial_2=0`$ を証明する。
3. 細側の台は $`\pi^{-1}A`$ で選ぶ。写るセルの像が選択されることと、
   fine面の全出現辺が選択されることを証明し、原始の符号付き等式をこの部分複体へ移す。
4. セル基底の像から $`r_A`$ を作り、双対の写像の評価式を出す。
   Law側でも、同じcell・law・valueを持つ `CellCoordinate` を生成する。
   相殺する二辺が同じ座標を指すことには `lawDescend_comparisonFactor` と
   `CellCoordinate.ext` を使う。

原始incidenceの零性はLawに依存しない有限な組合せ条件である。
その条件から支持複体とLaw微分の可換性を証明することがAの仕事となる。

## 2. 比較の合成と旧API

新比較の恒等は全セルを同名へ送る。合成はchart写像の合成とedge・faceの
`Option.bind` で作る。後段の退化面については符号付き零和に前段の辺写像の
線形延長を作用させる。後段で写る面については前段の面条件を適用する。
これにより、合成を生成Homより先に構成できる。

旧比較から新比較への写像では三つの `face_none_edge*` を用いて原始零和を証明する。
必要な一致は、各座標輸送、`generatedPullback0/1/2`、`generatedComparisonHom`、
`generatedComparisonH1Map`、各blockと部分集合の比較までを含む。
恒等・合成とこの埋め込みも可換にする。

G-133の `cochainComp` と `cochainComp_h1Map` は任意の三項Homに適用できる。
一方、`comparisonComp` や `lawFamily_natural0/1/2` の引数は旧比較である。
新比較を旧型へ強制変換すると混在退化を失うため、新しい成分自然性から同じ
可換図式を作り、汎用APIへ接続する。必要な接続を[対応表](reuse-map.md)に列挙する。

## 3. 支持chainと実cochainの同定

各 $`A`$ に対する支持セル集合を $`V_A,E_A,F_A`$ とし、
$`K_0=\mathbb Q[V_A],K_1=\mathbb Q[E_A],K_2=\mathbb Q[F_A]`$ とする。
chainはセル上の有限形式和、cochainは同じセル上のℚ値関数で表す。
基底評価により $`\operatorname{Hom}_{\mathbb Q}(K_n,\mathbb Q)`$ を
既存 `targetSubsetComplex A` の次数 $`n`$ へ同定し、二つの微分の式を証明する。

ラベル $`\lambda=(\ell,a)`$ には既存 `labelValueFiber` を使う。
粗fiberの逆像が細fiberであることを使い、次の図式を全三次数で可換にする。

```text
実 lawGeneratedComplex（粗） ──新しい生成比較──→ 実 lawGeneratedComplex（細）
            │ Lawごとの同値                              │ Lawごとの同値
            ▼                                           ▼
 ⨁λ Hom(K(coarse,Aλ),ℚ) ───────────⨁λ rλ*─────→ ⨁λ Hom(K(fine,π⁻¹Aλ),ℚ)
```

旧対象の `lawFamilyCochainEquiv`、`lawValueBlockTargetSubsetComplexEquiv` はそのまま使う。
上の横射との自然性が新規義務である。基本変形の $`s,h`$ も有限和の評価式から双対化し、
同じ図式へ通す。$`s`$ は一セルを複数セルへ送るので、`Option` 写像に制限しない。
これは出力の線形写像であり、入力の比較型を任意行列に置き換えるものではない。

H¹は既存のcocycle／coboundaryの商を保つ。`oldH1Equiv` と `oldH1Equiv_natural`
によって零延長の標準homologyへ移し、構成した鎖ホモトピーを
mathlibの `HomotopyEquiv` へ接続する。H⁰・H²も同じ零延長から読む。
基底式は $`1-sr=\partial h+h\partial`$ の向きなので、
`HomotopyEquiv` の合成から恒等へのfieldには双対の $`-h^*`$ を使う。
原始式の自由ℤ加群はincidenceの検査に使い、診断の係数はGOALのℚに固定する。

## 4. 有限操作列

操作は幾何のconstructorから生成する。基本変形と逆縮約、セル名・台を保つ同型、
台の逆像によるreading変更からなる有限列の型を用いる。
基本変形を「鎖ホモトピー同値が供給された比較」として定義しない。

二つの収縮について $`r_{01}:K_1\to K_0`$、$`r_{12}:K_2\to K_1`$ とすると、

```math
r_{02}=r_{01}r_{12},\qquad s_{02}=s_{12}s_{01},\qquad
h_{02}=h_{12}+s_{12}h_{01}r_{12}
```

が $`1-s_{02}r_{02}=\partial h_{02}+h_{02}\partial`$ を与える。
逆縮約を含む列では、各段の両向きのホモトピーを用いて通常のhomotopy同値の合成を行う。
直接比較はセル像を有限和として代入してから生成し、cochainHom合成との一致を証明する。
すべての段が部分セル比較なら、有限和の直接比較はAの `Option.bind` 比較とも一致する。

$`A\subseteq B`$ のchain包含に対し、基底式は同じである。
基本変形の各像の台包含を証明することで、$`r,s,h`$ と支持選択の自然性を得る。
Lawの再添字づけはラベルと重複度を保持する置換に沿って行う。

## 5. 錐・欠損と適用範囲

G-133の零延長・標準錐に、Dで同定した同じHomを渡す。
錐の座標は $`D(u)^m=C_f^m\oplus C_c^{m+1}`$、
$`d(y,x)=(d_f y+u x,-d_c x)`$ を保つ。
基本変形ではhomotopy同値から全次数の比較同型を得て、`cone_short_exact` から
錐の全cohomologyの零性へ進む。有限合成は `compositionTriangle` と同じ直接射を用いる。

Law分解は新比較の成分自然性を `coneMapIso` と `FiniteConeFamily.iso` へ渡して作る。
実H¹写像の核・余核もラベル別に分解し、`blockDefect` の零性へ接続する。
この接続はn1016 §4.5が参照するR14の合成と、R8で使う実錐の局所入力を与える。
R8全体の中間複体 $`P_A`$ や最大許容クラスの分類は別のtargetに属する。

面の複製操作EではH¹の同型とH²の余核を同時に計算する。
零H¹欠損から錐全体の零性へ進む際に必要な他次数の条件は、この実例で区別する。

## 6. 証明義務の依存関係

| 構成群 | 入力と先行構成 | 出力・使用先 |
| --- | --- | --- |
| P1：原始比較 | 既存supported nerve、符号付きincidence | 新比較、旧比較の埋め込み、恒等・合成、反例の排除 |
| P2：支持chainと生成Hom | P1、K1、Law降下 | 全Aのchain写像、実Law・block・subset Hom、全次数の自然性 |
| P3：局所変形 | 基本変形の原始constructor、P2 | 三角形追加・再三角形化・逆縮約のr・s・h、支持条件 |
| P4：実診断と有限合成 | P2・P3、G-133の汎用API | 既存H¹、標準HomotopyEquiv、支持制限、Law分解、錐・欠損 |
| P5：具体的決定 | P1–P4、指定例の原始表 | W1のpaired余核、W2の全退化例、E・W3のH²余核 |

P1–P5は未証明義務の分割であり、GOALの要求はT0・A–E・Wの全体である。
`Finsupp` と有限基底のどちらを内部表現に使うか、補題の分割、module配置は選択できる。
incidence符号、台の規則、各出現の別名、逆縮約の接続条件、実比較の生成経路は固定する。
