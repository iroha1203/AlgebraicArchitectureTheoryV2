# G-140 — 意味保存射と変更の全解の紙上証明

[固定target](../../goals/G-140-aat-semantic-change-category.md) A–G・P を、[G-139の紙上証明](../G-139-aat-law-generated-relative-geometry/README.md)の原始意味圏・全Hom・Law幾何から構成する。候補の状態map、操作語翻訳、固定部分、補助選択を保持してから、保存条件と評価条件を課す。

これは通常の数学による紙上証明である。既存Leanの利用箇所と新しい構成は [source対応](source-map.md)で区別する。

## 主定理

原始model間の実際のsort mapsから意味保存射の圏が構成され、生成操作の保存は全許可有限語の保存を含意する。その全HomはG-139の係数的実現に沿って表示され、非可逆な射を含む列のgroupoidはSegal同値を持つ。原始宣言から生成したcontext被覆と係数被覆について、対象・全Hom・保存式・合成はdescentを持つ。

許容規則と評価条件から全変更候補を生成すると、source固定のfiberが独立な条件付き変更を分類する。同じ構成は、固定図式の全補完、許容一段変更の列と細分化、合法状態の移送へ拡張される。readingを共有する実現に対する指定候補・各実現の候補・共通候補の三つの量化と、全係数変更で安定な全称条件を区別して構成できる。

台帳の原始操作へ適用すると、原子操作の係数空間は `SL₂×A¹`、固定した `p=(1,1)` 上では `A²`。snapshotの合法な保存族は `V(μδ)`、差し引く量を変える規則を許す族は `V(μδ(1−ρ))` となる。これらの係数点、実際の比較射、合法状態、protocolの許可経路を同じ式で比較する。

## 本文と依存順

| 本文 | 内容 | target |
| --- | --- | --- |
| [射と全操作語](semantic-morphisms.md) | 全sort map、語翻訳、観測、nerve、表示変更 | A・Bの圏と合成 |
| [射の幾何とdescent](geometry-and-descent.md) | 全Hom表示、ideal所属、witness商、二種類の被覆 | B・C |
| [条件付き変更と共通候補](conditional-changes.md) | 原始候補生成、評価fiber、三つの量化 | E |
| [図式・経路・状態移送](diagrams-paths-transfer.md) | 2-fiber、四角形・鎖・細分化、合法状態lift | F・G |
| [既存意味圏との比較](native-comparisons.md) | lens、protocol、G-124、G-126とadapter | D |
| [台帳の多項式特殊化](ledger-specialization.md) | 同じAtomと演算からPの全指定例・反例を導出 | P・Eの指定例 |
| [source対応と仮定](source-map.md) | 固定target、先行結果、必要仮定の使用箇所 | 全体 |

## 共通規約と射の向き

環は単位的可換環で零環を含む。signature、担体、規則族、図式は小さく、濃度は有限に限定しない。各termと各操作語は有限である。係数的実現 `σ` はG-139で構成した同じcopying、module、指定regular operationの解釈を用いる。係数上で保持する構文名・規則添字も [C3.1](geometry-and-descent.md#c31--構文選択自体のdescent) の局所定数dataとして解釈し、全変更のdescentに含める。

`C_R` の射は実際の状態mapの向きとする。したがって `h₀₁:X₁→X₀` は `C_R` では1から0への射である。変更前0から変更後1という時間順には `C_R^op` を使う。候補moduliの `s,t` は使用する向きを指定して選ぶ二つの端点射であり、台帳例では `s=before,t=after` とする。

本文の `×²` は、同一視を証明だけで捨てず、同型そのものを保持する2-fiber productである。集合値のmarked表示では通常のfiber productになる。groupoidの射は候補の可逆な比較であり、その対象に保持する状態mapは非可逆でもよい。一般の表示関手を無条件にschemeとは呼ばず、G-139のprofile・商・descentを含む表示として扱う。
