# G-141-aat-semantic-scheme-representability — 実現関手のscheme表現

- `id`: `G-141-aat-semantic-scheme-representability`
- `status`: `draft`
- `research mode`: `target-theorem`
- `tracking issue`: [#6359（設計）](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6359)。個別のResearch Loop Issueはactive化時に定める。
- 設計: [多項式特殊化ノート §5](../../docs/note/n1020_shigure_polynomial_specializations.md#5-affine表示から大域schemeへ)
- 依存: [G-139 A](G-139-aat-law-coefficient-extension.md#a-式の係数自然性)、[G-140](G-140-aat-independent-realization-descent.md)

主経路は[n1019](../../docs/note/n1019_shigure_representability_design.md)のG-149〜G-152にある。
本カードは多項式特殊化を構成する。主経路と同じ対象・射・Law評価への比較を要し、
本カードの達成だけでSHIGURE全体の達成とはしない。

## 研究目的

独立な実現の局所基底からLawのaffine chartとその接着を生成し、SHIGUREのscheme版を
証明する。局所方程式の商環の普遍性に加え、任意の係数代数上で複数chartにまたがる
実現、普遍実現、大域での自然な対応を構成する。

## 固定target

### A. 原始データからのopen chart

任意の可換環kとノート§3.1の表示Pについて、各型vでm_v個からn_v個を選ぶ組Iを
全て取る。G-140のSem_Pの部分関手Sem_{P,I}を局所基底条件から定義する。
任意のtest scheme上でこの条件の成立部分がopenであり、その族がtest schemeを
覆うことを、生成元の全射性と局所自由性から証明する。

G-139の同じLaw式からノート§5のB_Iを構成し、
Sem_{P,I}(R)≃Hom_{k-alg}(B_I,R)を全k代数Rについて構成する。
両写像をmatrixの読み取りと加群・演算の復元で与え、元のAtom / Law評価へ戻す。
0階数、m=n、空な解集合、無限な演算・Law族も量化に含める。

### B. overlapと接着

全I,Jについて、基底変換行列から共通部分の局所化環と遷移の両逆を構成する。
tensor残差の変換式からLaw idealの対応を導く。三つの添字について、共通定義域と
cocycleを証明する。遷移同型・open性・cocycleをcallerの入力にしない。

同じU_I=Spec B_Iを貼り合わせて実際のscheme M_Pを構成する。
全chart上の商加群・演算を貼り合わせて普遍実現を作り、Lawfulnessを証明する。
`StandardArchitectureScheme`や`EquationObservableRealization`を利用する場合は
M・atlas・表現同値を構成した後に供給し、元のAAT contextとの対応がある箇所を特定する。

### C. 大域表現同値

全k代数Rについてノートの(S)を、実現の局所表示から射を貼り合わせる方向と、
普遍実現を引き戻す方向で証明する。両逆、任意のk代数射R→Sでの自然性、
任意のk-scheme Tへのdescentによる延長、普遍実現を保つ表現対象の一意同型を含める。
局所表示に用いた基底・被覆の選択に対応が依存しないことも証明する。

### W. 非退化な例と接着の検査

ノートW1–W3をA–Cの同じ構成へ通し、指定されたG_m、P¹、非被約affine schemeへの
同型を構成する。W2ではq=(2,3)がどちらの標準chartにも大域的に入らず、D(2),D(3)上の
解から復元されることと、M自体がaffineでないことを証明する。
W3ではdual numbersの二点を区別し、全体を体値点の集合やradical idealへ置き換えない。
W6の遷移表のcocycle不成立を明示し、生成された遷移との相違を示す。

## 前提・構成台帳

| 対象 | 役割 | 出所・構成義務 | 使用先 |
| --- | --- | --- | --- |
| k、原始表示P | 入力として保持 | ノート§3.1 | A–C |
| 独立Sem・descent | 先行構成 | G-140の同じ加群・演算 | A・C |
| 原始式の成分多項式 | 先行構成 | G-139 A | A・B |
| open chart、被覆、残差ideal | 構成・証明義務 | 生成元からの局所基底選択 | A |
| overlap・遷移・cocycle | 構成・証明義務 | 基底変換とtensor式の自然性 | B |
| M・普遍実現・表現同値 | 構成・証明義務 | A・B・descent | B・C |
| scheme接着の標準定理 | 既存数学 | Stacks Tag 01JJ等。適用前提はA・Bから生成 | B・C |
| W1–W3・W6 | 構成・証明義務 | ノート§8の固定入力 | W |

## 完了条件

A–C・WをLeanで証明し、`research/reports/G-141-aat-semantic-scheme-representability.md`に
原始データからの生成経路、標準接着定理への前提、表現同値の両方向を記す。
証拠は`research/lean/ResearchLean/AG/`に置き、
[共通完了基準](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)を適用する。

否定の決着には、入力条件を満たすPについて(S)を満たすschemeの不存在証明、または
A–Cの固定構成・同値が不成立になる具体的反例を要求し、`target-refuted`として区別する。
採用した接着方法の実装不足や未発見は、不存在証明とは数えない。
