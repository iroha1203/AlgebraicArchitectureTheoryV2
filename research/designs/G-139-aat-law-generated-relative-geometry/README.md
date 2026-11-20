# G-139 — 量とLawから構成する相対幾何の紙上証明

[固定target](../../goals/G-139-aat-law-generated-relative-geometry.md)の N・A–D・P を、原始意味、copying 表示、量の相対表現、多項式特殊化の順に扱う。証明の入力は実際の担体・演算・関係・量・式である。表現同値、descent certificate、frame、Law ideal は入力に置かず、本文で構成する。

本稿の証明は通常の集合論・可換代数・代数幾何による紙上証明である。既存 Lean 宣言の利用箇所は [source 対応](source-map.md)に分離する。G-139 の Lean による完了条件とは別の成果物である。

## 主定理

任意の小さい原始signatureから、実際のmodelと全構造保存射の圏を構成できる。そのcartesian構造はcopying coalgebraに運ばれ、全係数環上のHomは各入力の有限直交冪等元分割で分類される。connectedな非零環、または全可換環に自然な族から元の全Homを回復できる。

構造とquantity domainを固定すると、任意個のscalar quantityと有限式による任意個のLawの独立model関手は、原始評価から生成した `Sym Q/I` のSpecで表現される。局所split構造と指定係数構造の各stack上では、この構成は相対affineな表現となる。任意native残差の全regular extensionは有限単項式supportの全chartで分類され、coherenceも普遍tupleの係数等式で課せる。

有限個のdualizable module sortと指定された生成規則からはframeとGL商を構成できる。名前付き生成元を持つ多項式特殊化では、基底openと遷移を原始実現から作ってschemeを得る。同じ構成が全指定証人を回収する。無限担体は一般構成に残り、通常の代数的空間・stackに有効化できない指定familyも含まれる。

**証明の依存順。** N1の意味とN2のcopyingからN3・N4・N5を構成する。A1の評価帰納法が相対表現の局所証明であり、B1のdescentでB2へ貼る。C2の普遍tupleがC3–C5の全拡張分類を与える。D1のdual basisからD2のframeと商を得る。P1で独立実現を定め、P1aの評価一致を用いてP2のchartを構成し、P3・P4・P6の比較を導く。各段階の証明と反例は以下の本文に置く。

## 読み順と固定targetへの対応

| 本文 | 内容 | target |
| --- | --- | --- |
| [原始意味と全Homの回復](primitive-semantics.md) | 多sortの圏、既存native族、図式・候補・評価 | N1・N4・N5 |
| [copyingとtotality](copying-and-totality.md) | coalgebra、全Hom、support表示、微小不変性、有限query反例 | N2・N3 |
| [量とregular extension](quantity-and-extension.md) | 普遍量、Law ideal、任意残差、全拡張とcoherence | A・C |
| [descentと代数性](descent-and-algebraicity.md) | copyingと係数的実現、相対Spec、有限frame、非有効化 | B・D |
| [多項式特殊化](polynomial-realizations.md) | 独立なSem・Real、chart、自然性、商stack、図式 | P1–4・P6 |
| [原始入力を通す具体例](witnesses.md) | W1–W3・W5–W8と指定反例 | P5 |
| [source対応と仮定](source-map.md) | 新規構成、既存証拠、外部標準定理の使用箇所 | 全体 |

## 共通規約

環は単位的可換環、環射は単位を保ち、零環を含む。基礎環を `k` とする。集合、signature、Law族、図式は固定した universe 内で小さい。全modelの圏は一段大きい universe で扱う。小さいことから有限性は導かない。

`C_R(X)` は basis `e_x` を持つ直和 `⊕_X R`、`ΔX` は `k` 上の scheme `⨿_X Spec k` の点関手を表す。前者の coalgebra 構造と後者の点の分類を証明してから同一視する。`R^X` は直積、`R^(X)` は有限supportの直和である。

式は有限syntax木であるが、式の集合、入力集合、変数集合は任意に小さくてよい。環の多項式は常に有限個の単項式だけを持つ。tensor式は型付きで、unit・結合・対称性・線形性の標準同型を明示した同じ式として評価する。

stack の被覆には fppf topology を使う。Zariski 被覆もこれに含まれる。scheme が代数的とは有限型であることを意味しない。無限個の変数とLawを持つ affine scheme も使用する。

各節の自然性は実際の写像の式から証明する。構造の忘却、量の引戻し、座標環の射、scheme の射はそれぞれ向きを記す。固定targetが許す十分条件と、原始入力から放電すべき条件を区別する。
