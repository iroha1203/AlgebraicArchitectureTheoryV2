# Related Work

AAT は、Atom と Law から相対的なアーキテクチャを構成する数学理論である。
reading に相対的な対象と構造保存射を定め、幾何、輸送、比較、局所再構成を展開する。
以下では、代数的仕様、層の意味論、抽象解釈、データ移送、双方向変換を中心に、
対象・仮定・射・結論を比較し、AAT 固有の構成と帰結を位置づける。

## R.1 仕様とアーキテクチャの意味論

仕様の記述を変えたとき、その意味も対応して変わる必要がある。
Goguen と Burstall の institution は、この関係を論理に依存せずに定める。
署名、文、モデルの圏、充足関係を備え、署名の変更に沿う文の翻訳とモデルの還元が
充足関係を保つことを要求する。モデル間の射も、この枠組みの一部である
（[GB92, §2.1, 定義1](https://courses.grainger.illinois.edu/cs522/sp2016/InstitutionsAbstractModelTheory.pdf)）。
さらに、署名の余極限から理論の余極限を構成できる。
この結果によって、小さな仕様から大きな仕様を組み立てる原理を、
異なる論理に共通する基礎の上で述べられる
（[GB92, 定理11とその帰結, p. 108](https://courses.grainger.illinois.edu/cs522/sp2016/InstitutionsAbstractModelTheory.pdf)）。

部品の接続を対象とすると、振舞いの適合性が問題になる。
Allen と Garlan の Wright は、component の port と connector の role・glue を
CSP によって記述する。connector が保守的かつ deadlock-free であり、
各 role に接続する port が適合性条件を満たすなら、
それらの port で具体化した connector も deadlock-free である
（[AG97, §§8.1–8.2, 定義8.1.2・定理8.2.3](https://ix.cs.uoregon.edu/~michal/Classes/f01/fsv/papers/Allen-Garlan.pdf)）。

AAT は、Atom の reading を固定し、Law の値から相対 core を定める。
被覆・係数・評価を加えて幾何を構成し、方程式とイデアルを通じて、
Law の充足を幾何的な零点条件として表し、lawful locus を定める（定理2.9）。
この幾何が、修復の障害、reading に沿う輸送、構成経路の比較を扱う対象になる。

プロトコルでは、その対応を操作と観測の保存等式で捉えられる。
名前付き操作と経路の関係式、観測を固定すると、実現間の射は、操作と観測を保つ
頂点ごとの状態写像になる。AAT は、この独立な意味論から型付き入力を構成し、
双方の射を対応づける（命題1.38・1.43）。

## R.2 局所整合性とコホモロジー的障害

部分ごとに与えた振舞いを、一つのシステムの振舞いとして読む。
この局所から大域への記述には、Goguen の層の意味論という先例がある。
オブジェクトを層、相互作用を図式として扱い、適切な完備性の下で
システムの振舞いを図式の極限として得る
（[Goguen92, 公開稿 §§2・3.1–3.3, 命題26](https://ncatlab.org/nlab/files/Goguen-SheafSemantics.pdf)）。
設計 view を扱う Gibson のプレプリントも、パラメータごとの値の割当てを前層とし、
共通パラメータ上で一致する view を貼り合わせる。ここで働くのは、
二つずつの交わりでの一致による層条件である
（[Gibson26, 定義3.2・定理4.1, §§3–5](https://arxiv.org/html/2605.08609v1)）。

貼り合わせの前には、不一致を解消できるかという問題がある。
大域的な延長の存在を問う構図は、contextuality の研究にも現れる。
Abramsky と Brandenburger は、測定 context ごとの結果の分布を
整合する empirical model として扱い、大域的な分布への延長と
factorizable な hidden-variable model の存在を対応づけた
（[AB11, §§2.2–2.5, 定理8.1](https://arxiv.org/pdf/1102.0264v7)）。

さらに Abramsky、Mansfield、Barbosa は、support を自由可換群で線形化し、
局所 section の延長に対する Čech 障害類を構成している。
非零の障害は延長不能性を示す。一方、障害が零のときに得られるのは
線形化後の整合族であり、実際の結果の割当てへの延長には追加の条件が要る。
Hardy model は、この違いを示す例である
（[AMB12, §4, 命題4.2–4.3・§5](https://arxiv.org/pdf/1111.3620v2)）。

AAT は、可換群の係数による修復状態の torsor 構造、制限と作用の同変性、
層条件の下で、指定障害類の零性から大域的修復を構成する（定理2.22）。
torsor の切断による自明化という標準事実を、Law の評価と修復状態に結ぶ構成である
（[Stacks, Tag 03AG](https://stacks.math.columbia.edu/tag/03AG)）。

係数の選び方も、診断の意味を決める。
Young のプログラム解析の提案では、プログラムの部分構造を site とし、
意味的性質の完全束を値に持つ前層を用いる
（[Young26, §§3.1–3.4](https://arxiv.org/html/2603.27015v1)）。

AAT は、修復語の関係式と Law の方程式から独立に生成した可換群の係数を比較する。
この比較は、先行研究 SAGA で示した。
局所状態の同変な対応から関係式の健全性を導き、二つの完全性条件の下で
係数同型と cochain・残差類の対応を得る。修復状態の層条件を加えると、
大域的修復の判定につながる
（[SAGA, §§3.4–3.7・4–5, 定理5.1–5.2](https://arxiv.org/html/2608.21458v1)）。

AAT は、この SAGA の比較を基礎に（定理2.49・系2.50）、
障害と診断を reading の変更に沿って比較する。
係数の関係と共通代表に関する条件の下で、
診断の零性から元の障害類の零性を反映する（定理3.40）。
さらに、被覆の細分に沿って両者を比較し、診断不変性を障害判定へ戻す
（定理3.43・3.44）。

## R.3 抽象化と情報の保存

読取りに残すべき情報は、答えたい問いに応じて変わる。
Cousot と Cousot の抽象解釈では、具体領域と抽象領域を順序構造で結び、
局所的な意味操作の近似から、大域的な不動点計算の正しさを導く。
抽象化と具体化の関係が、実際の振舞いを含む近似を支える
（[CC77, §§5–7, pp. 240–243](https://www.di.ens.fr/~cousot/publications.www/CousotCousot-POPL-77-ACM-p238--252-1977.pdf)）。
Giacobazzi らは、さらに抽象化と意味操作が可換する completeness を調べ、
不動点の結果についての completeness と区別した
（[GRS00, §3, p. 372](https://www.sci.unich.it/~scozzari/paper/JACM00.pdf)）。
何を近似するかに加え、指定した操作について何を正確に保つかが問題となる。

AAT は、Law の値を正確に保持する最も粗い reading を
標準解像度として構成する（定理3.4）。
診断の保存には、さらに係数と被覆の比較が要る。
条件 C の下での一次コホモロジーの同型（定理3.17）と、
指定障害類の零性の反映（定理3.40）は、この情報の十分性を異なる強さで捉えている。

AAT は、変更の判定に必要な情報を、観測の核によって特徴づける。
比較 $`c`$ を保つ変更の部分群を $`\Gamma_c`$、観測の準同型を $`O`$ とする。
観測だけで $`\Gamma_c`$ への所属を判定できる必要十分条件は、
$`\ker O\subseteq\Gamma_c`$ である（定理7.9）。
観測が区別しない変更がすべて比較を保てば、同じ観測には同じ判定を下せる。

ここでの十分性は、固定した性質の判定に関するものである。
対象と全構造保存射を回復する局所再構成には、
さらに局所データの分離と組立てが必要になる（第8章）。

## R.4 輸送と基底変換

schema を変えれば、データもそれに沿って移す必要がある。
Spivak の functorial data migration は、schema を生成グラフと経路の関係式で
表示した圏、instance を集合値関手、instance 間の射を自然変換として扱う。
schema の関手に沿う制限には左右の随伴があり、三つの移送関手が得られる
（[Spivak12, §§3.2・3.4–3.5・4, 命題4.2.1・4.3.1](https://arxiv.org/pdf/1009.1166v3)）。
Schultz らの algebraic database は、型・演算・方程式をこの記述に取り込み、
entity と型側の代数を結ぶ instance、および schema mapping に沿う制限と
その左右随伴を構成する
（[SSVW17, §§6–7, 特に§6.19・命題7.3–7.4](https://arxiv.org/pdf/1602.03501v3)）。

この理論では、schema とその射、instance、query が、proarrow equipment と呼ばれる
共通の二重圏の構造に収まる。移送や query の評価も、その構造における
合成や随伴を用いて記述される
（[SSVW17, 定義8.13・命題8.14・補題8.18, §§8.25–8.26・9](https://arxiv.org/pdf/1602.03501v3)）。
対象と移送を同じ枠組みで扱うことは、AAT との体系上の接点である。

AAT は、exact な reading の変更から再添字づけを作り、
相対 core の輸送と引き戻しを構成する。
その普遍性は fibred category の標準理論に基づく
（[Stacks, Tag 02XJ](https://stacks.math.columbia.edu/tag/02XJ)）。
一般の data migration の随伴に対し、core の輸送と引き戻しが
随伴同値をなすのは、この exact な条件による（命題5.8）。

二つの移送を組み合わせると、今度は経路の比較が必要になる。
随伴の単位・余単位から mate を作り、その可逆性を Beck–Chevalley 条件として
捉える方法は、Shulman の framed bicategory と fibration の研究に明示されている
（[Shulman08, §13, 定義13.11](https://tac.mta.ca/tac/volumes/20/18/20-18.pdf)）。
AAT は有限codeから生成した reading の平方に対してこの mate を作り、
cartesian lift の選択を替えた比較との整合性を示す（定理5.11・命題5.12）。

AAT は、有限codeで実現した平方と構成5.37の共通の比較図式から
完全幾何の生成比較を作り、可逆な射と冪等射の合成に分解する。
冪等射の像に制限することで、可逆な比較が得られる（定理6.16）。

## R.5 Lens、更新と比較を保つ変更

注文の配送先を更新しても、決済情報はそのまま引き継ぎたい。
view の更新では、このように読取りに現れない情報をどう扱うかが重要になる。
Bancilhon と Spyratos は、その情報を complement として指定し、
固定した complement を保つという条件から更新の translation を定めた。
持ち上げが存在するとき、その translation は一意である。
合成で閉じ、各状態で更新を打ち消せる更新族では、すべての更新を
この条件で持ち上げられれば、合成を保つ translator が得られる
（[BS81, §§3・5・7, 定理5.6・7.1](https://www.inf.unibz.it/franconispace/lib/exe/fetch.php?media=organisation%3Asakt%3A2013%3A5.pdf)）。

Foster らの lens は、読取り get と更新 put の法則によって双方向変換を扱う。
AAT が扱う全域 lens は、原論文の very well-behaved かつ total な lens に対応する
（[FGMPS04, §3.1, 定義3.1.2–3.1.3・PutPut](https://www.cis.upenn.edu/~bcpierce/papers/newlenses-full.pdf)）。
この法則と complement の関係を圏論的に捉えたのが Johnson らである。
有限積を持つ圏で view から終対象への射が分裂するなら、
lens の圏は complement の圏と同値になる。集合の場合、view の基準点を選ぶと、
状態は view とその基準 fiber の積として表せる
（[JRW12, §3, 命題3.1–3.2](https://mta.ca/~rrosebru/articles/Lens2Cambridge.pdf)）。

AAT は、この積表示を用いて、get と put を保つ任意の射を、
基準 fiber の写像の制限・延長として記述する（命題1.33・1.34）。
この記述を、型付き射や比較へ接続する。

更新を持ち上げる普遍性について、Johnson らは categorical lens と
split opfibration を関係づけている
（[JRW12, §4, 注意4.1・系4.1・命題4.3](https://mta.ca/~rrosebru/articles/Lens2Cambridge.pdf)）。
AAT は、固定した意味論の下で比較を保つ可逆変更を分類する。
操作が隠れた状態をそのまま運ぶモデルでは、AAT はその状態の変更を
操作グラフの連結成分ごとに分類し、可視の変更との関係を分裂短完全列で表す
（定理7.24・7.25）。
同じ積lensの自己変更では、固定した可視置換の下で、隠れた置換が全viewで一致する。
内部状態を保持するプロトコルでは独立な連結成分ごとに選べる（命題7.27・7.29）。
これらのモデルでは、操作による状態の結びつきが、変更の自由度を決める。

## R.6 表示と局所再構成

対象とその変更を局所的な表示で扱うには、構造保存射も回復できる必要がある。
AAT は、各入力族で独立に定めた局所データと整合等式から対象を組み立て、
局所射と全域の構造保存射を対応づける（第8章）。

演算と方程式からモデルの圏を得る基礎には、Lawvere の関手的意味論がある。
代数的理論を有限積を持つ圏、代数を積を保つ関手、準同型を自然変換として扱う
（[Lawvere63, pp. 869–870](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/lawvere.pdf)）。
Barr と Wells の sketch は、グラフに可換にすべき図式と指定した錐を与える。
モデルは図式を可換にし、錐を極限錐へ送る解釈であり、射は自然変換となる
（[BW85, 第4章 §1.2](https://tac.mta.ca/tac/reprints/articles/12/tr12.pdf)）。

Berger らの nerve theorem は、dense generator と、それを arity として持つ
monad の条件の下で、代数の圏から前層圏への充満忠実な nerve を構成する。
その本質的像は、制限に関する条件で特徴づけられる
（[BMW12, 定理1.10](https://math.univ-cotedazur.fr/~cberger/arities.pdf)）。

ここでは、同じ意味を持つ表示をどう同一視するかも効いてくる。
『Algebraic Databases』の2025年第3版は、異なる構文上の射が同じ意味上の射を
表し得ることから、表示の圏と意味の圏の間に述べていた同値を修正している
（[SSVW17, Appendix B.1–B.3](https://arxiv.org/pdf/1602.03501v3)）。
AAT は、局所写像から全域射を作ることと、同じ読取りを持つ射が一致することを
それぞれ証明し、局所対象も同型を除いて組み立てる。
各入力族の独立な局所条件からこの三性質を導くことで、実現の圏と局所モデルの圏の同値を得る。
充満忠実性と本質的全射性から圏同値を導く判定は標準的である
（[Stacks, Tag 02C3, 補題4.2.19](https://stacks.math.columbia.edu/tag/02C3)）。

局所条件には、lens の get・put の graph と三法則、
プロトコルの生成辺・観測の graph と経路の関係式、完全幾何の係数・評価の保存条件が現れる。
lens では有限な基準 fiber を、プロトコルでは各頂点の有限な状態集合とその有限リスト被覆を用いる。

冪等射の像への拡張には、Cauchy completion の標準理論を用いる。
Kelly は集合で豊穣化された場合、小圏上の前層圏の small projective が
表現可能前層の retract であり、Cauchy completion が冪等射の分裂を加える
完備化に対応することを示している
（[Kelly82, §5.8, 定理5.36](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/kelly-book.pdf)）。
AAT は、生成比較を正規化の冪等射で因子化し、像への制限・延長を作る
（定理6.12・6.16・6.27）。lens とプロトコルの基準 fiber や生成 table による再構成も、
Karoubi 完備化と射の圏へ延長できる。

## R.7 AAT の位置づけ

AAT の寄与は、各構成を結ぶ定理と、個々の問題の意味論との対応にある。
AAT が掲げる **Rising Sea** は、こうした基礎を築くことで、
個別の問題を共通の構成の特殊な場合として捉える方針である。
