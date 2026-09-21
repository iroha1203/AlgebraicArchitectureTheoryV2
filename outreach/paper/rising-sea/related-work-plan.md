# Related Work 収録案

第1〜8章の主結果に対応する主要文献21件と、説明の必要に応じて加える補足候補4件を整理する。
章構成は [論文構成マスター](paper-structure.md)、比較する数学の範囲は
[数学内容の棚卸し](mathematics-inventory.md)に従う。第8章も、局所モデルの構成と
対象・構造保存射の再構成を比較対象に含める。

[Related Work本文](ja/12-related-work.md)と各文献の関係を、比較する問い、対象、仮定、結論によって示す。
原典の参照箇所は各項目に、書誌と引用文の対応は[文献確認記録](references.csv)に記す。

## 1. 比較の構成

Related Work は次の六つの論点を比較し、冒頭と結びで AAT の数学的な位置づけを述べる。
末節は六つの比較を踏まえた位置づけに絞り、個別の問題を共通の構成の特殊な場合として捉える
Rising Seaの方針を短く示す。
標準数学の出典 RW21 は各章の初出にも置く。
比較文では、対象、仮定、許容する射、保持する構造、結論を具体化する。
障害と診断、輸送と正規化、比較を保つ変更と局所再構成の関係を、
各構成で得た対象・写像と後続の問いとの接続によって示す。

| 論点 | 対応章 | 主要文献 | 比較で答える問い |
| --- | --- | --- | --- |
| 仕様とアーキテクチャの意味論 | 第1章 | RW01–02 | どの入力から対象・法則・構造保存射を定めるか |
| 局所整合性とコホモロジー的障害 | 第2–3章 | RW03–08 | 局所データと係数をどう作り、何が大域的整合性を特徴づけるか |
| 抽象化と情報の保存 | 第3・6–7章 | RW09–10 | 何について十分な読み取りであり、どの性質を保存・反映するか |
| 輸送と基底変換 | 第4–5章 | RW11–13 | 輸送・随伴・比較の自然変換はどの構成から得られるか |
| lens、更新と比較を保つ変更 | 第1・4・6–8章 | RW14–16 | 更新の選択、意味保存射の全体、可逆変更の分類をどう関係づけるか |
| 表示と局所再構成 | 第6・8章 | RW17–20、RW12・16・21 | 独立に定めた局所モデルから対象と全構造保存射を回復できる条件は何か |

## 2. 主要文献21件

### 仕様とアーキテクチャの意味論

**RW01 — Goguen and Burstall (1992).**
Joseph A. Goguen and Rod M. Burstall.
*Institutions: Abstract Model Theory for Specification and Programming*.
Journal of the ACM 39(1), 95–146. DOI: [10.1145/147508.147524](https://doi.org/10.1145/147508.147524).
[著者の文献案内](https://www-cse.ucsd.edu/~goguen/projs/sem.html)、
[先行技術報告 ECS-LFCS-90-106](https://publish.lfcs.inf.ed.ac.uk/reports/90/ECS-LFCS-90-106/)。

- **対応・比較:** 第1章。署名・文・モデル・充足と、その変更に対する整合性を出発点に、AAT の Atom、Law、reading、生成する幾何の関係を説明する。仕様の構成を複数の論理に共通する基礎で扱う点も比較する。institution としての定式化を主張する場合には、その構成と充足条件の証明を別途示す。
- **参照箇所:** [掲載論文](https://courses.grainger.illinois.edu/cs522/sp2016/InstitutionsAbstractModelTheory.pdf)の §2.1、定義1、pp. 101–102、および定理11、p. 108。署名・文・モデルの圏・充足条件と、署名の余極限からの理論の余極限の構成。

**RW02 — Allen and Garlan (1997).**
Robert Allen and David Garlan. *A Formal Basis for Architectural Connection*.
ACM Transactions on Software Engineering and Methodology 6(3), 213–249.
DOI: [10.1145/258077.258078](https://doi.org/10.1145/258077.258078)。
[原論文の公開コピー](https://ix.cs.uoregon.edu/~michal/Classes/f01/fsv/papers/Allen-Garlan.pdf)。

- **対応・比較:** 第1・4章のプロトコル。Wright の port・role・glue と CSP による適合性を、AAT で固定するプロトコルの意味論・観測保存射・adapter の構成と対比する。相手が指定する振舞いの下での適合性と、AAT の構造保存等式をそれぞれ述べる。
- **参照箇所:** 本文 §8.1、定義8.1.2、定理8.2.3。適合する port への置換による deadlock-freedom の保持には、connector の保守性と deadlock-freedom の仮定がある。

### 局所整合性とコホモロジー的障害

**RW03 — Goguen (1992).**
Joseph A. Goguen. *Sheaf semantics for concurrent interacting objects*.
Mathematical Structures in Computer Science 2(2), 159–191.
[出版社の書誌・要旨](https://www.cambridge.org/core/journals/mathematical-structures-in-computer-science/article/abs/sheaf-semantics-for-concurrent-interacting-objects/604DA5071EA19CDD65293205C066929B)。
DOI: [10.1017/S0960129500001420](https://doi.org/10.1017/S0960129500001420)。

- **対応・比較:** 第1–2章。object を層として扱う意味論、相互作用の図式、振舞いの極限を先行研究に位置づける。AAT については Law の方程式、lawful locus、修復 torsor と係数の構成を具体的に比較する。
- **参照箇所:** [公開稿](https://ncatlab.org/nlab/files/Goguen-SheafSemantics.pdf)の §§2・3.1–3.3、特に命題26。層としてのオブジェクト、システムの図式、完備性の下での振舞いの極限。箇所番号は公開稿による。

**RW04 — Gibson (2026).**
Josh Gibson. *Sheaves as a Means of Maintaining Consistency in Model-based Systems Engineering*.
arXiv:2605.08609v1、2026-05-09。
[書誌](https://arxiv.org/abs/2605.08609)、[本文](https://arxiv.org/html/2605.08609v1)。

- **対応・比較:** 第2・8章。複数のモデル view の整合性を層の貼り合わせで扱う研究として比較する。層条件の下での局所 section の貼り合わせと、AAT の障害類による大域的修復の判定、および対象と全構造保存射の局所再構成を、対象と仮定ごとに述べる。
- **参照箇所:** 本文 §§3–5、定理4.1と複数 view の例。定理4.1は pairwise intersections による層条件の特徴づけを用いる。書誌の題名は arXiv metadata に従う。

**RW05 — Abramsky and Brandenburger (2011).**
Samson Abramsky and Adam Brandenburger.
*The Sheaf-Theoretic Structure of Non-Locality and Contextuality*.
arXiv:1102.0264v7、2011-11-29。
[著者・書誌・要旨](https://arxiv.org/abs/1102.0264)。

- **対応・比較:** 第2章。測定 context と局所データの大域的延長という構造を説明する。AAT の局所状態・Law・修復データと、原論文の empirical model・support・global section の対応範囲を明示する。
- **参照箇所:** [第7版本文](https://arxiv.org/pdf/1102.0264v7)の §§2.2–2.4、定理8.1。結果の割当て、分布、empirical model、大域的分布と factorizable hidden-variable model の対応。

**RW06 — Abramsky, Mansfield, and Barbosa (2012).**
Samson Abramsky, Shane Mansfield, and Rui Soares Barbosa.
*The Cohomology of Non-Locality and Contextuality*.
arXiv:1111.3620v2、2012-10-02（初版2011）。
[著者・書誌・要旨](https://arxiv.org/abs/1111.3620v2)。

- **対応・比較:** 第2–3章。support から作る可換群の前層と Čech 障害類を比較し、係数の由来、特定の障害類とコホモロジー群、零性と延長可能性の関係を区別する。AAT 側の零性同値にはその成立条件を併記する。
- **参照箇所:** [第2版本文](https://arxiv.org/pdf/1111.3620v2)の §4、命題4.2–4.3、§5 の Hardy model。非零障害による延長不能性と、零性が与える線形化後の整合族。

**RW07 — Young (2026).**
Halley Young.
*Sheaf-Cohomological Program Analysis: Unifying Bug Finding, Equivalence, and Verification via Čech Cohomology*.
arXiv:2603.27015v1、2026-03-27。
[書誌](https://arxiv.org/abs/2603.27015)、[本文](https://arxiv.org/html/2603.27015v1)。

- **対応・比較:** 第2–3章。プログラムの局所解析に層・コホモロジーを用いる近接研究として、site、被覆、係数、cochain、零性判定を比較する。AAT では意味的修復と方程式から独立に生成した係数の比較写像が、どの仮定で障害類と診断を結ぶかを説明する。
- **参照箇所:** 本文 §§3.1–3.4 のプログラムsite・完全束値の前層の提案。AATの可換群係数との比較に用いる。

**RW08 — Nakahata (2026), SAGA.**
Hiroyuki Nakahata.
*SAGA: A Comparison Theorem for Local-to-Global Software Architecture - From Semantic Repair Cohomology to Algebraic-Geometric Descent*.
arXiv:2608.21458v1、2026-08-20。
[書誌](https://arxiv.org/abs/2608.21458)、[本文](https://arxiv.org/html/2608.21458v1)。

- **対応・比較:** 第2–3章および論文全体。先行する自身の研究として、意味的修復と代数幾何的 descent の比較を明示的に帰属させる。本稿で加える reading の変更、診断不変性、輸送、生成比較、正規化、変更分類、再構成をそれぞれの定理に対応づける。
- **参照箇所:** §§3.4–3.7・4–5、特に定理5.1・5.2。独立に生成する係数、その比較と残差類、大域的修復の対応。

### 抽象化と情報の保存

**RW09 — Cousot and Cousot (1977).**
Patrick Cousot and Radhia Cousot.
*Abstract interpretation: a unified lattice model for static analysis of programs by construction or approximation of fixpoints*.
POPL 1977, 238–252。
[著者の書誌・解説・原論文へのリンク](https://www.di.ens.fr/~cousot/COUSOTpapers/POPL77.shtml)。

- **対応・比較:** 第3章を中心に第6–7章。抽象領域と不動点の近似に対し、AAT が固定した Law の値を保つ商と、選んだ診断の保存・反映を何について要求するかを説明する。順序・Galois connection を使う場合は、その入力と対応を示す。
- **参照箇所:** [原論文](https://www.di.ens.fr/~cousot/publications.www/CousotCousot-POPL-77-ACM-p238--252-1977.pdf)の §§5–7、pp. 241–243。抽象領域、抽象化・具体化、局所近似と大域的な不動点の関係。

**RW10 — Giacobazzi, Ranzato, and Scozzari (2000).**
Roberto Giacobazzi, Francesco Ranzato, and Francesca Scozzari.
*Making Abstract Interpretations Complete*.
Journal of the ACM 47(2), 361–416.
DOI: [10.1145/333979.333989](https://doi.org/10.1145/333979.333989)。
[著者公開本文](https://www.sci.unich.it/~scozzari/paper/JACM00.pdf)。

- **対応・比較:** 第3・7章。演算に関する abstraction の completeness と、第3章の Law に十分な reading、第7章の観測からの比較適合性の検出を対比する。保存対象を固定し、全構造の再構成を要求する第8章との関係も説明する。
- **参照箇所:** 本文 §3、特に pp. 371–372 の completeness と fixpoint completeness の区別。

### 輸送と基底変換

**RW11 — Spivak (2012).**
David I. Spivak. *Functorial Data Migration*.
arXiv:1009.1166v3、2012-03-21。
[書誌](https://arxiv.org/abs/1009.1166)、[本文](https://arxiv.org/pdf/1009.1166v3)。

- **対応・比較:** 第1・4–5・8章。生成グラフと経路の関係式、関手としての instance、自然変換としての instance 間の射をプロトコルの意味論に対応づける。data migration の関手と、AAT の reading 変更から構成する輸送・引き戻しを比較する。
- **参照箇所:** §§3.2, 3.4–3.5、§§4.1–4.3、命題4.2.1・4.3.1。制限と左右随伴の構成には、値の圏の完備性・余完備性が関わる。本文は集合値の場合を対象とする。

**RW12 — Schultz, Spivak, Vasilakopoulou, and Wisnesky (2017).**
Patrick Schultz, David I. Spivak, Christina Vasilakopoulou, and Ryan Wisnesky.
*Algebraic Databases*.
Theory and Applications of Categories 32(16), 547–619。
[arXiv 書誌・版履歴](https://arxiv.org/abs/1602.03501)、
[第3版](https://arxiv.org/pdf/1602.03501v3)（2025-01-16、Appendix B に errata）。

- **対応・比較:** 第1・4–5・8章。型・演算・方程式を伴う schema と instance、migration の随伴、表示からのモデル構成を比較する。schema・instance・移送・query を共通の二重圏で扱う体系も比較対象とする。AAT の原始入力と全構造保存射を、schema と instance のどちらの層に対応させるかを固定する。
- **参照箇所:** 第3版の §6.19、定義7.1、命題7.3–7.4、定義8.13、命題8.14、補題8.18、§§8.25–8.26・9 と Appendix B.1–B.3。instance、制限と左右随伴、二重圏での移送・query、表示の射から意味の射への忠実性に関する訂正。

**RW13 — Shulman (2008).**
Michael Shulman. *Framed bicategories and monoidal fibrations*.
Theory and Applications of Categories 20(18), 650–738。
[出版社の書誌](https://www.tac.mta.ca/tac/volumes/20/18/20-18abs.html)、
[本文](https://www.kurims.kyoto-u.ac.jp/EMIS/journals/TAC/volumes/20/18/20-18.pdf)。

- **対応・比較:** 第4–5章。cartesian / opcartesian 輸送、mate、Beck–Chevalley の一般理論を帰属させる。AAT では reading と完全幾何から二経路を作り、実際に得た比較が可逆になる仮定を示す。
- **参照箇所:** 本文 §13、特に定義13.11の mate と Beck–Chevalley 条件、および続く例。

### lens、更新と比較を保つ変更

**RW14 — Foster et al. (2004).**
J. Nathan Foster, Michael B. Greenwald, Jonathan T. Moore, Benjamin C. Pierce, and Alan Schmitt.
*Combinators for Bi-Directional Tree Transformations: A Linguistic Approach to the View Update Problem*.
University of Pennsylvania, Technical Report MS-CIS-04-15、2004-08-07。
[著者公開本文](https://www.cis.upenn.edu/~bcpierce/papers/newlenses-full.pdf)。

- **対応・比較:** 第1・4・6–8章。get/put の法則と双方向変換の構成を帰属させる。その lens を対象として AAT が扱う意味保存射、基準 fiber からの対象・全 Hom の再構成、冪等射の分裂、比較を保つ変更の分類を接続する。
- **参照箇所:** 2004年の技術報告の §3.1、定義3.1.2–3.1.3、PutPut 法則、本文 pp. 5–6。

**RW15 — Bancilhon and Spyratos (1981).**
François Bancilhon and Nicolas Spyratos. *Update semantics of relational views*.
ACM Transactions on Database Systems 6(4), 557–575.
DOI: [10.1145/319628.319634](https://doi.org/10.1145/319628.319634)。
[原論文の公開コピー](https://www.inf.unibz.it/franconispace/lib/exe/fetch.php?media=organisation%3Asakt%3A2013%3A5.pdf)。

- **対応・比較:** 第1・7–8章。view の complement を用いる更新の選択を、lens の保持する情報と結びつける。第7章では、一つの更新方策の選択に対し、固定した比較を保つ変更全体、同じ観測を持つ複数の持ち上げ、その核と torsor を記述する点を比較する。
- **参照箇所:** §§4–5・7、定義4.1、定理5.6・7.1。固定complementを保つtranslationの一意性と、更新族の閉性などの仮定。

**RW16 — Johnson, Rosebrugh, and Wood (2012).**
Michael Johnson, Robert Rosebrugh, and R. J. Wood.
*Lenses, fibrations and universal translations*.
Mathematical Structures in Computer Science 22(1), 25–42.
DOI: [10.1017/S0960129511000442](https://doi.org/10.1017/S0960129511000442)。
[著者公開本文](https://mta.ca/~rrosebru/articles/Lens2Cambridge.pdf)。

- **対応・比較:** 第1・4・7–8章の最優先文献。sketch のモデルと view、lens と constant complement、更新の普遍的な持ち上げを、AAT の意味論・輸送・再構成の各層と比較する。積表示と補完構造を既存研究へ帰属させ、AAT の全構造保存射の再構成に必要な入力と保存等式を述べる。
- **参照箇所:** 本文 §§2–4、定義2.6・3.1、命題3.1–3.2・4.1・4.3。lensとcomplementの圏同値には有限積とviewから終対象への射の分裂を用いる。集合上のlens、categorical lens、普遍的更新をそれぞれ比較対象とする。

### 表示と局所再構成

**RW17 — Lawvere (1963).**
F. William Lawvere. *Functorial Semantics of Algebraic Theories*.
Proceedings of the National Academy of Sciences of the United States of America 50(5), 869–872。
DOI: [10.1073/pnas.50.5.869](https://doi.org/10.1073/pnas.50.5.869)。
[公式書誌](https://pmc.ncbi.nlm.nih.gov/articles/PMC221940/)、
[原論文](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/lawvere.pdf)。

- **対応・比較:** 第1・8章。演算・等式による理論と、そのモデルを関手として扱う先行研究に位置づける。AAT の共通入力宣言、構造条件、原始読み取りを、モデル圏を得るための具体的な入力として説明する。
- **参照箇所:** 学位論文の要約として発表された1963年PNAS論文の pp. 869–870。理論、積を保つ関手としての代数、自然変換としての準同型。

**RW18 — Barr and Wells (1985 / 2005).**
Michael Barr and Charles Wells. *Toposes, Triples and Theories*.
Springer、1985。Reprints in Theory and Applications of Categories 12 (2005), 1–288。
[再録本文](https://www.kurims.kyoto-u.ac.jp/EMIS/journals/TAC/reprints/articles/12/tr12.pdf)。

- **対応・比較:** 第8章。sketch、型付き図式、等式、モデルと自然変換を、局所モデルの独立な定義の最も近い標準的な構成として比較する。AAT の各入力族について、どの局所値・整合等式が対象と全構造保存射の組立てを可能にするかを示す。
- **参照箇所:** 本文第4章 §1.2 の sketch・model・model homomorphism。グラフ、可換にすべき図式、指定した錐と、それらを保つモデル。

**RW19 — Kelly (1982 / 2005).**
G. M. Kelly. *Basic Concepts of Enriched Category Theory*.
Cambridge University Press、1982。
Reprints in Theory and Applications of Categories 10 (2005), 1–136。
[再録版の書誌・本文案内](https://www.tac.mta.ca/tac/reprints/articles/10/tr10abs.html)。

- **対応・比較:** 第6・8章。Cauchy completion、representable の retract、冪等射の分裂を帰属させる。AAT では生成比較の冪等性・像の構成、lens / protocol の具体的な再構成と Karoubi への拡張を比較対象にする。
- **参照箇所:** [再録本文](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/kelly-book.pdf)の §5.8、定理5.36、pp. 100–101。集合で豊穣化された場合のsmall projective、表現可能前層のretract、冪等射の分裂。

**RW20 — Berger, Melliès, and Weber (2012).**
Clemens Berger, Paul-André Melliès, and Mark Weber.
*Monads with arities and their associated theories*.
Journal of Pure and Applied Algebra 216(8–9), 2029–2048.
DOI: [10.1016/j.jpaa.2012.02.039](https://doi.org/10.1016/j.jpaa.2012.02.039)。
[著者公開本文](https://math.univ-cotedazur.fr/~cberger/arities.pdf)。

- **対応・比較:** 第8章。nerve による充満忠実な表示と、その像に入るための独立な条件を、AAT の原始読み取り・整合する局所モデル・対象組立てと対比する。dense generator と arity の条件が、どの入力のもとで再構成を可能にするかを比較軸にする。
- **参照箇所:** 本文定理1.10の nerve theorem。dense generator と monad with arities の条件、nerveの充満忠実性と本質的像の特徴づけ。

### 各章に共通する標準数学

**RW21 — The Stacks project authors (2026).**
*The Stacks project*.
[公式本文](https://stacks.math.columbia.edu)。

- **対応・比較:** 全章。圏・site・層・アフィンスキーム・torsor・被覆の細分・fibred category の標準事実を初出で帰属させる。第8章の一般原理には、充満忠実かつ本質的全射な関手の圏同値判定を明記する。
- **参照箇所:** 各章の出典は[文献](ja/14-references.md)による。第8章の一般判定は補題4.2.19 [Tag 02C3](https://stacks.math.columbia.edu/tag/02C3)。具体的な分離・組立ての証明と、この判定の使用を対応づける。

## 3. 第8章で比較する結果と文献

第8章の比較は、一般局所再構成原理と各入力族の具体的な構成を対象とする。
局所モデルの定義、対象の組立て、全構造保存射の分離・組立てを文献と対応づける。

| 第8章の内容 | 近接する文献 | Related Work で説明する点 |
| --- | --- | --- |
| 共通入力宣言、局所対象・局所射を定める独立な等式 | RW17–18、RW12 | 署名・型・演算・等式からモデル圏を定める先行構成と、AAT の読み取り添字・局所値・整合式の対応 |
| Hom の分離・組立てと対象の同型による組立て | RW20–21 | 一般の圏同値判定への帰属と、各族でその仮定を実際に証明する内容。全域射の存在を局所整合条件へ含めない構成 |
| lens の原始 get/put データ、有限基準 fiber と全意味保存射 | RW14–16 | lens 法則・補完構造・積表示を先行研究に位置づけ、基準 fiber の任意の写像の制限・延長と両逆を比較 |
| プロトコルの頂点 carrier、生成辺・観測の graph、経路関係と全自然変換 | RW11–12、RW18 | 表示された圏のモデルと準同型を出発点に、原始局所データの整合式からの対象・射の組立てを説明 |
| 完全幾何の原始成分・関数 graph による対象と Hom の回復 | RW18・20 | 局所図式で読む構造、係数と評価の保存条件、局所モデルからの組立てを明示して比較 |
| Karoubi、retract、射の圏への再構成の拡張 | RW19・21 | 標準的な圏論的拡張と、各モデルの具体的な制限・延長との整合を分けて説明 |
| タグ族の全有限片からの回復、有限 code の表示可能性と反例 | RW20を表示の比較に使用 | 全有限片の整合族による回復、単一の有限決定集合、固定 code 間の射の表示可能性を別々に述べる。位相・逆極限の標準事実は第8章の該当箇所で出典を補う |

第2章の局所 section の貼り合わせと、第8章の対象・射の再構成を比較する際は、
添字、局所値、制限、整合条件、組立てをそれぞれ指定する。
両者を同一のコホモロジー的障害理論として結ぶ主張には、そのための追加構成と証明が要る。

## 4. 補足候補4件

主要候補との比較に必要な説明が残る場合に加える。背景の紹介だけなら導入へ置く。

| ID・文献 | 比較する問い |
| --- | --- |
| **RW22** David Garlan, Robert Allen, and John Ockerbloom. *Architectural Mismatch, or, Why it's hard to build systems out of existing parts*. ICSE, 1995。[原論文](https://www.cs.cmu.edu/afs/cs/project/able/ftp/archmismatch-icse17/archmismatch-icse17.pdf) | 導入・第1章の動機。部品の個別性質と、組合せで必要となる仮定の関係 |
| **RW23** Michael Robinson. *Sheaves are the canonical data structure for sensor integration*. Information Fusion 36, 208–224, 2017。[出版社本文・要旨](https://www.sciencedirect.com/science/article/pii/S156625351630207X)、DOI: 10.1016/j.inffus.2016.12.002 | 第2–3章の観測データの整合性とsensor fusion。consistency radiusとコホモロジーの役割 |
| **RW24** Luca de Alfaro and Thomas A. Henzinger. *Interface Automata*. FSE, 2001。[著者所属機関の文献案内](https://osq.cs.berkeley.edu/pastprojects.htm) | 第1・4章のプロトコル。環境を含む適合性・refinementと、固定した意味論の構造保存射との関係 |
| **RW25** William F. Opdyke. *Refactoring Object-Oriented Frameworks*. PhD thesis, University of Illinois at Urbana-Champaign, 1992。[大学リポジトリ](https://www.ideals.illinois.edu/items/72240) | 第7章のリファクタリング例。状態対応の下での数学的な保存結果と、ソースコード変換の正当性を結ぶ前提条件 |

## 5. 本文との対応

| 本文 | 比較する内容 |
| --- | --- |
| R.1–R.2 | 仕様と接続、層による意味論、障害類、SAGAから継承する結果 |
| R.3–R.4 | Law-value・指定診断・変更の判定に十分な情報、輸送・随伴・mateの構成 |
| R.5–R.6 | complement・lens・更新、比較を保つ変更、独立な局所モデルと対象・全構造保存射の組立て、Cauchy completion |

数学の対応は[証拠対応](claims.md)、書誌と原典の箇所は[文献](ja/14-references.md)と
[文献確認記録](references.csv)に記す。RW12は2025年第3版、RW17は1963年PNAS論文を参照する。
2026年のRW04・07・08はプレプリントとして扱う。
