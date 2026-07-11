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
