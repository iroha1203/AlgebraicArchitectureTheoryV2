# ArchView gluing geometry contract

この文書は`archsig-viewer-gluing-geometry-golden-ux/v0.5.0`の恒久design contractである。
ArchViewはArchSig artifactを投影し、新しいstructural verdictを生成しない。

## Golden cases

- cover nerve: 3頂点、2辺、1つのtriple-overlap faceを表示できる。H2 coherence verdictは生成しない。
- Cech H1: nonzero cocycle supportをbounded ribbonとして表示し、monodromy verdictを生成しない。
- square-free repair: forbidden cageと、そのsupportに接続されたrepair morphを表示する。automatic repairとは主張しない。
- sheaf Laplacian: curvature field、blocked region、analytic massをanalytic readingとして表示する。
- semantic anchor blocker: unsupported axisをblocked anchor glyphとして表示する。

## Required projection functions

Golden manifestはcell、strut、face、atom、seam、terrain、cage、repair morph、verdictの各projection surfaceとrepair probe更新を監査する。

## Fidelity boundary

期待値は測定artifactの投影に限る。layout、色、glyph、animationは証明、lawfulness、repair成功、未測定値のzeroを生成しない。

## Fidelity declaration surface

ArchViewは各描画要素について、視覚チャネルごとの由来区分を詳細パネルで申告する:

- `measured` … 測定量が駆動する(cell半径∝|atoms|、strut太さ∝|support|、amber = 実測mismatch/cocycle support、どの辺が存在するか)。
- `layout` … 実測adjacency/membershipの埋め込み作図。絶対座標はverdictを持たない。
- `decoration` … bloom、pulse、seamのアーチ、probe等の演出。測定値を運ばない。

「Decoration」トグルOFFは`measured`+`layout`チャネルのみで同じ測定内容を描画する
(seamは直線実線tube、bloom/pulse/probeなし)。区分はいずれのモードでも主張を変えない。

## Terminology lanes

すべてのUI文言はengineer laneとmath laneの2層を持ち、切替は文言のみを変え、
主張・境界・conclusion codeを変えない。conclusion codeは両laneで原文表示する。

## Source landing

atom / seam / strut の詳細パネルは、supplied ArchMapの`sources`宣言から解決された
`path:line`(+symbol)を表示する。解決はArchSig側(`sourceRefSamples`)で行われ、
ArchViewは位置を発明しない(未解決refはセマンティック文字列のまま表示)。
