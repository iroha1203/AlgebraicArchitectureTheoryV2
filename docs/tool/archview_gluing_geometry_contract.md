# ArchView gluing geometry contract

この文書は`archsig-viewer-gluing-geometry-golden-ux/v0.5.3`の恒久design contractである。
ArchViewはArchSig artifactを投影し、新しいstructural verdictを生成しない。

## Golden cases

- cover nerve: 3頂点、2辺、1つのtriple-overlap faceを表示できる。H2 coherence verdictは生成しない。
- Cech H1: nonzero cocycle supportをbounded ribbonとして表示し、monodromy verdictを生成しない。
- square-free repair: observed support atomを持つ生成元だけをforbidden co-occurrenceのcageとして表示し、そのsupportに接続されたrepair morphを表示する。宣言された生成元が未生起のときはpacketの`measured_zero`と`silence_by_design`を保持し、automatic repairとは主張しない。
- sheaf Laplacian: curvature field、blocked region、analytic massをanalytic readingとして表示する。
- semantic anchor blocker: unsupported axisをblocked anchor glyphとして表示する。

## Required projection functions

Golden manifestはcell、strut、face、atom、seam、terrain、cage、repair morph、verdictの各projection surfaceとrepair probe更新を監査する。

## Fidelity boundary

期待値は測定artifactの投影に限る。layout、色、glyph、animationは証明、lawfulness、repair成功、未測定値のzeroを生成しない。

## Fidelity declaration surface

ArchViewは各描画要素について、視覚チャネルごとの由来区分を詳細パネルで申告する:

- `measured` … 測定量が駆動する(cell半径∝|atoms|、strut太さ∝|support|、amber = 実測mismatch/cocycle support、どの辺が存在するか、Y = restriction posetの深さ)。
- `derived` … 実測量からの一意導出。X,Z = 実測nerveのLaplacianスペクトル埋め込み
  (同一成分内の近さ ≈ 拡散距離。等長変換・固有値縮退を除いて一意)。
  一意性の但し書きは申告に含める。
- `layout` … 意味を持たない作図上の選択。成分間配置、絶対スケール、
  スペクトル座標が厳密一致する(nerve近傍が同型な)context同士の最小分離、レーン高さ割当。
- `decoration` … bloom、pulse、seamのアーチ、probe等の演出。測定値を運ばない。

「Decoration」トグルOFFは`measured`+`layout`チャネルのみで同じ測定内容を描画する
(seamは直線実線tube、bloom/pulse/probeなし)。区分はいずれのモードでも主張を変えない。

## Terminology lanes

すべてのUI文言はengineer laneとmath laneの2層を持ち、切替は文言のみを変え、
主張・境界・conclusion codeを変えない。conclusion codeは両laneで原文表示する。

## Derived-geometry views (measured-geometry design note)

`docs/note/archview_measured_geometry_design.md` を正本とする3つのビューの契約:

- **スペクトル座標(wave 1)** … X,Z は選択カバーnerveのスペクトル埋め込み、
  Y はposet深度。座標は`derived`/`measured`として申告し、決定論(同一packet→同一座標、
  固定sweep順Jacobi・符号正規化)を保つ。`SPECTRAL_MAX_CONTEXTS`超のsiteは
  宣言済みのlayoutリングへ段階縮退する。
- **二重被覆twist view(wave 2)** … F₂ cochain値(`nerve.edges[].value`)を
  二重被覆として描く。被覆の連結性は表示のための決定論的純関数導出であり、
  新しいstructural verdictではない。導出とpacket verdictが不一致の場合、
  twist viewは沈黙し(非描画+boundary文言)、**packetを正とする**。
  F₂・可換係数に限り、非可換torsor / stacky descent / gerbeには言及しない。
- **étale空間Sectionsビュー(wave 3)** … 宣言section値(cech sectionValue atomの
  objectRef)をレーンとして持ち上げる。レーン辺は「実測restriction辺の両端で
  宣言値が等しい」ときのみ存在する。値未宣言のcontextは空ファイバー(沈黙)であり、
  それを跨ぐレーンの連結を主張しない。「global section」表示は
  全contextが宣言済みかつ単一レーン成分が全域を貫く場合に限る
  (宣言された値の中での大域切断であり、意味宇宙全体の主張ではない)。

## Source landing

atom / seam / strut の詳細パネルは、supplied ArchMapの`sources`宣言から解決された
`path:line`(+symbol)を表示する。解決はArchSig側(`sourceRefSamples`)で行われ、
ArchViewは位置を発明しない(未解決refはセマンティック文字列のまま表示)。

## SAGA診断階段とgate入力

`sagaDescent`を持つviewer-dataは、`grounding → descent → comparison → silence`の
4段を`stageId` / `status` / `whatNext` / `leafFieldMap`の対応を保ったまま投影する。
高さはSAGAシーン内の次数の読み方であり、HUDで`H⁰ → H¹ → H²`を宣言する。
沈黙段のH²層への配置はscene-local layoutであり、個々の沈黙行の計測次数の主張ではない。
`silence_by_design`は段を消さず、沈黙表示と`whatNext`を保持する。
`sagaDescent`の段形状（order / stageId / visualRole）が契約と一致しない場合は
描画せず、statusへ拒否理由を明示する（無言の空シーンにしない）。

`archsig-gate-report/v0.5.3`は同一ディレクトリまたはtoolbarから供給する任意の第二入力である。
受理時は最終段に`decision`と`ruleOutcomes[].appliedMapping[]`の`rowRef` / `action` /
`boundaryOverrideApplied`を表示する。`action`は`pass` / `pass_with_boundary` / `block`のみを受理し、
`boundaryOverrideApplied: true`は表示上の`*`で明示する。gate reportの
`inputDigests.measurementPacket.sha256`がviewer-dataの同じdigestと一致しない場合、またはschema・語彙・行形状が不正な場合は読み込みを拒否し、statusへ理由を表示する。gate未供給時はエラーにせず、最終段を沈黙として描く。
