# G-141 — 変更の障害・全修復・有限判定の紙上証明

[固定target](../../goals/G-141-aat-coherent-repair-effectivity.md) A–Hを、[G-139](../G-139-aat-law-generated-relative-geometry/README.md)の原始実現と、[G-140](../G-140-aat-semantic-change-category/README.md)の全変更・補完・移送fiberから構成する。原始Lawの残差と全syzygyを先に作り、その同じ修復をcotangent、Čech、逆極限、有限方程式で比較する。

## 主定理と本文

平方零liftでは、実残差の類の零性が実現liftの存在と同値であり、全lift・同型・自己同型を同じ複体の次数0・−1で分類できる。宣言supportを保つ制限から局所修復とfragmentの複体を作り、大域複体との比較条件を証明する。有限型・有効な有限還元を持つ場合には、原始候補の全解、幾何的像、共通候補の四分類を計算できる。

整数adapterの一例では、全有限段の解とZariski局所の全解が存在する一方、大域解がない。その障害は同じ指定類 `[−1/3]` としてČech、拡大類、`lim¹`、実際の平方零liftへ写る。有限graphの台帳では、実adapterからSAGAの係数・状態・残差を生成し、零性から全大域操作と許容修復を回復する。

| 本文 | 内容 | target |
| --- | --- | --- |
| [原始liftと相対障害](obstruction-complexes.md) | 全syzygy、conormal、cotangent、指定観測lift | E |
| [Fragmentと加法adapter](fragments-and-adapters.md) | 全translation、複体、導来逆極限、ML条件 | A |
| [Telescopeと拡大](telescope-and-extension.md) | 全変更scheme、有限段、cotangent、実拡大 | B |
| [同じ非零障害](local-obstruction.md) | 整数・局所・2進・微小lift、係数変更 | C |
| [局所修復と選択](descent-and-selection.md) | 宣言Čech、補完のdescent、有限étale選択 | C・E |
| [有限計算](effective-solving.md) | 有限還元、全解、像、四分類、停止不能例 | D |
| [全Artin試験](artin-detection.md) | 消去、検出次数、相対障害、係数変更 | F |
| [部分変更の相互作用](interaction-families.md) | 座標面ideal、最小不成立族、Boolean配置 | F |
| [有限graphの実修復](graph-repair.md) | 実交差・層・SAGA・全許容修復 | G |
| [指定例](witnesses.md) | H1–H9、snapshot、操作言語の反例 | H |
| [source対応](source-map.md) | 全条項と一次source、条件の使用箇所 | A–H |

## 規約

環は単位的可換環で零環を含む。集合・signature・図式は小さく、個々のtermは有限。一般の全変更はG-140のfiberであり、線形化して得た複体と同一視するのは、ここで証明するaffine問題または平方零liftである。

複体はcohomological gradingを用い、自己同型を−1、補正を0、defectを1に置く。原始Law `f=0` の残差は `f(tilde x)`、方程式 `d(c)=a` の不足量は `a−d(tilde c)` とする。両者の符号は使用する方程式から明記する。Čech差は右の局所sectionから左を引く。

これは通常の数学による紙上証明である。新しい構成と既存Lean宣言の使用箇所はsource対応で区別する。
