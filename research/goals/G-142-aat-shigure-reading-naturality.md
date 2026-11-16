# G-142-aat-shigure-reading-naturality — SHIGUREのreading・係数自然性

- `id`: `G-142-aat-shigure-reading-naturality`
- `status`: `draft`
- `research mode`: `target-theorem`
- `tracking issue`: [#6359（設計）](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6359)。個別のResearch Loop Issueはactive化時に定める。
- 設計: [多項式特殊化ノート §6](../../docs/note/n1020_shigure_polynomial_specializations.md#6-readingの射と自然性)
- 依存: [G-140](G-140-aat-independent-realization-descent.md)、[G-141](G-141-aat-semantic-scheme-representability.md)

主経路は[n1019](../../docs/note/n1019_shigure_representability_design.md)のG-149〜G-152にある。
本カードは多項式特殊化を構成する。主経路と同じ対象・射・Law評価への比較を要し、
本カードの達成だけでSHIGURE全体の達成とはしない。

## 研究目的

独立な実現とschemeの対応が、Lawの強化、演算の解釈、表示変更、基礎環変更を通じて
同じ意味を持つことを証明する。自然性を持つscheme版SHIGUREの統合をこのカードで行う。

## 固定target

### A. readingの圏と意味の射

ノート§6の型・階数・生成元数を保つtensor式の代入とLaw導出からreadingの射を作る。
型の全単射による改名に加え、sourceの型を同じ階数・生成元数のtarget型へ単射で
対応させ、追加型・演算を忘れる射を含める。
sourceのrequired Lawの導出にはtargetのrequired Lawとノート§3.1の加群・tensor積の
標準等式だけを使う。表示ごとに追加する方程式は全てrequired Lawに含める。
derived Lawを使う場合は同じ前提からの導出を伴い、optional Lawを前提にしない。
射の等号は型の対応が同じで、全演算の代入式がこの同じ理論で等しいこととする。
導出のproof choiceを射の追加情報として残さない。この関係が合成で保たれること、
恒等・合成則を証明する。

全てのu:P→P′とk代数Rについて、代入によるu*:Sem_{P′}(R)→Sem_P(R)を生成する。
対応するRealの関手も同じ式で生成する。uの合成・恒等と任意のR→Sに関する
可換性を証明する。文脈被覆の細分化は同じ大域実現のdescent表示の変更として定め、
組立てに関する自然同値を構成する。

### B. 同じ表現同値を介した幾何の射

G-141の全てのM_PについてM(u):M_{P′}→M_Pを構成し、全Rとx∈Sem_{P′}(R)で
η_R(u*x)=M(u)∘η_R(x)を証明する。恒等・合成は同じscheme射の等式として示す。
chart上で原始式の代入が生成する環準同型との一致も含める。

型の対応も含めて互いに逆な代入とLaw導出を持つ射はscheme同型を誘導することを示す。
一般射に同型性は付けない。required Lawの追加では同じambient演算上のLaw idealの
包含から閉埋め込みを構成し、像を新しいLawの成立で特徴づける。

### C. 任意の基礎環変更

任意の環射k→k′、原始表示Pについて、P_{k′}の原始式と加群実現を先に構成する。
G-141のM_{P_{k′}}とM_P×_{Spec k}Spec k′の間の同型を作り、普遍実現のpullback、
全k′代数での表現同値、恒等、二回の係数変更の結合同型と可換になることを証明する。
同じuについてこの同型とM(u)が作る正方形の可換性も証明する。

G-139の多項式・商環の同型にchartで一致することを示す。既存の
`StandardArchitectureScheme.baseChange`へ接続する場合は、そのflatness・
HasSheafify・HasSheafComposeと対象の装飾を別に満たす入力において比較する。
C自体にはflatnessを追加しない。

### D. 階数の変わる開発変更と比較の合成

ノート[§12](../../docs/note/n1020_shigure_polynomial_specializations.md#development-change)の
before/afterの表示から、状態比較h・観測・操作語対応τを持つcomparison presentationを
原始式で構成する。両端を忘れる射と、対応するschemeのspanを構成する。
各生成操作の可換式と観測式から全有限語での観測保存を証明し、
同じbefore実現から可能な変更をspanのfiberとして同定する。

中間表示と観測が一致する二つの比較について、hの合成とτの語代入から合成比較を
作り、比較moduliのfiber productから合成比較moduliへの射を構成する。
恒等、結合、任意の係数変更との自然性を証明する。unmarked版は同型を保持した
2-fiber productをG-140の独立Realに構成する。G-143が後で同じ比較をstackへ移す。
これらの射の入力を、完成済みのSem間の写像やmoduli射で置き換えない。

G-140 Eの有限phase表示では、状態を表す0引数演算と不変量の実現fiberに同じ比較を
構成する。遷移後の不変量と観測差が元の不変量・required Lawのidealに入ることを、
原始式から証明する。その同じ式から各遷移の意味保存と全許可有限経路の保存を導く。
全ambient状態での保存と、生成された不変量上での保存を区別する。

### W. 作用・開発変更・非同型の指定例

ノートW1のf↔gとp↔qの同時改名を、R=ℚの(2,1/2)へ作用させ、作用の非恒等性と
二回作用の恒等性を証明する。W7ではLaw追加の射が同型でなく、その同じ射のℤ→F₂
base changeがB・Cの正方形に従うことを示す。W2の被覆D(2),D(3)とその交差を加えた
細分化で、同じ大域実現が復元されることを示す。

Aの射の条件も二つの反例で検査する。T=0をrequiredに持つ表示からoptionalにだけ持つ
表示への恒等代入は、T=1の実現を保たないので射にならない。演算・Lawが空で二つの型が
共にn=1,m=2の場合、型の恒等対応と交換は異なる射である。R=ℤで二型のkernelを
ℤ(0,1)、ℤ(1,0)とした実現への作用が異なることを示す。

ノート§16の台帳移行をDへ通す。比較pは非単射で、beforeとafterの状態階数が異なる。
pi=id,pj=0の係数実現をSL₂×A¹へ同定する。p=(1,1)を固定したfiberはA²_(λ,μ)であり、
全点が指定した操作語の観測意味を保つことと、途中readを加えた反例を同時に示す。
同じ台帳のsnapshot protocolでは、δ=1−λとcompact係数μに対する意味保存の像を
V(μδ)⊂A²_(δ,μ)へ同定する。Busyの全R³上へ保存を要求するとμ=0を強制することも示し、
G-140の不変量を保持した比較を同じschemeのfiberへ接続する。

## 前提・構成台帳

| 対象 | 役割 | 出所・構成義務 | 使用先 |
| --- | --- | --- | --- |
| 原始表示・代入・required Lawと標準等式による導出 | 入力として保持 | ノート§3.1・§6。意味の写像は入力にしない | A |
| Sem、Real、descent | 先行構成 | G-140 | A・C |
| M・η・普遍実現 | 先行構成 | G-141 | B・C |
| readingの圏、u*、M(u) | 構成・証明義務 | 原始代入と同じ表現同値 | A・B |
| 逆代入とLaw導出 | 同型の一般定理の仮定 | W1では具体的に構成 | B・W |
| 係数変更同型と全可換図式 | 構成・証明義務 | G-139 A、G-140、普遍実現 | C |
| W1・W2・W7 | 構成・証明義務 | ノート§8の同じデータ | W |
| before/after・h・観測・τの原始式 | 入力・生成義務 | ノート§12。両側の階数は異なってよい | D |
| 比較span・合成射・全語保存 | 構成・証明義務 | 原始式の可換性から生成 | D・W |

## 完了条件

A–D・WをLeanで証明し、`research/reports/G-142-aat-shigure-reading-naturality.md`に
G-140・G-141との同一対象上の対応を記す。証拠は`research/lean/ResearchLean/AG/`に置き、
[共通完了基準](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)を適用する。
これにより本草案が選んだreadingでのscheme版SHIGUREを完了判定できる。

否定の決着は、適格な原始表示・射・実現から固定の可換性または構成を反証し、
`target-refuted`として記録する。Atlasの診断不変性だけをBのscheme同型の証拠にせず、
一般の解像度変更への接続は、このカードの射へ変換する別の構成として扱う。
