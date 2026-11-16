# G-149-aat-native-coalgebraic-reconstruction — 任意担体の意味と全Homの再構成

- `id`: G-149-aat-native-coalgebraic-reconstruction
- `status`: `draft`
- `research mode`: `target-theorem`
- 関連メモ: [#6359](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6359)。実行用tracking Issueはactive化時に定める。
- 設計: [n1019 §1–2](../../docs/note/n1019_shigure_representability_design.md)
- 研究目的: AATの元の状態・操作・Law・射を保持したまま、係数を持つ幾何へ進む。
  有限階数のmodelを選び直すことを本targetの代用にしない。

## 固定target

### A. 原始意味圏

任意の小さいmany-sorted signatureについて、担体、有限arityの実際のoperation、
relation、指定domain上のpartial operation、選択値から独立なmodel圏を構成する。
射は実際のsort mapsとoperation/relation保存であり、恒等と合成を証明する。
存在witnessを選んだモデルと存在だけを要求したモデルを区別する。
表示から完成済みのモデル集合やschemeへのHomを入力に取らない。

Atom configuration、opaque payload、lens、protocol、G-124のgeometryについて
原始宣言を構成し、既存の対象と全Homを回復する比較関手を与える。
generic ArchitectureObjectに未指定のHom構造を既存と称してはいけない。
その場合は実際に追加した射のデータと忘却するデータを明示する。

### B. 複製・消去を保持した係数化

全可換環Rと全集合XにC_R(X)=⊕_X R、basisの複製Δとcounitを構成する。
直積・終対象との同型を含め、Aの全termの評価、Law、恒等・合成を運ぶ。
任意のX,Yについてcoalgebra Homと
Hom_R(⊔_X Spec R,⊔_Y Spec R)の自然な全単射を構成する。
連結な非零環で全native Homを回復し、全可換環にscalar extensionで自然な射の族は
ℤ成分から元の集合写像を回復することを示す。零環での挙動も証明する。

全R上のHomを単一の集合写像と同定せず、入力ごとの有限直交冪等元分割を構成する。
任意のnilpotent thickeningでこの離散Homが一意に持ち上がることも証明する。
この零の微小変形と、G-150のquantityの非零微小変形を区別する。

### C. 無限担体のtotalityと表示

各入力ごとの有限出力supportを保持したaffine chart、その拡大、全profileの表示系を
生成し、全RでBのHomを回収する。合成のsupportを有限和の式から生成する。
次を実際に反証する。

- 全有限Boolean queryの閉条件だけからtotalityが回復する。
- 全入力に共通する有限出力集合を選べる。
- モデルごとの有限評価supportは一様な有限段階への因子分解を与える。

反例には無限出力の全false行、ℕの恒等写像、f(g(x))の評価を使う。
G-124のIsTotalとcompose_finite_supportへの同じquery単位の比較を証明する。

### D. 既存native族の回復

total lensの三等式からC≅K×Vを構成する。
同じview Vを固定してview mapを恒等とする全HomはK→K'に対応すると証明する。
viewも変える一般相対Homは、両viewに基準値がある場合、
(K→K')×(V→V')に対応させ、既存のstate/view両mapを回復する。
空viewの場合はgetのsourceも空になることから対象・Homを直接分類して残す。
有限fiberは一般targetの仮定にしない。
Set上の分解・相対射のnormal formには既存の
[GeneralRelativeLens](../lean/ResearchLean/AG/RealizationReconstruction/GeneralRelativeLens.lean)
のproductEquiv・normalForm・productMapを再利用し、新規義務を係数・descentとの比較に置く。
任意small execution category Pのprotocolは[P,E]/Oとして、
全path Lawと全自然変換を回復する。非単射射と非自明自己同型を必須例とする。

opaque payloadは任意Pと選択点のまま保持する。
任意の既存residualはその実際のgraphとして保持し、多項式性を推論しない。
量や構造の内部が未指定のfieldには、式・係数作用を捏造しない。

## 前提・構成台帳

| 対象 | 役割 | 構成・証拠 | 使用先 |
| --- | --- | --- | --- |
| signature・担体・操作・関係 | 入力 | Aの独立な意味圏 | B–Dの比較 |
| coalgebra・chart・全profile | 構成義務 | B–Cの式から生成 | 全Hom・totality・合成 |
| 連結非零環 | Bの点ごとの回復条件 | group-likeの分類 | native Hom反射 |
| lens/protocol/geometryの原始source | 比較対象 | D、既存G-124と同じ型・射 | native再構成 |

## 証明義務と完了の意味

標準coalgebra定理は再利用する。新規の義務はAAT原始宣言からの構成、
全term・全Homの比較、G-124と同じ制限・組立ての可換性である。
A–DをLeanで構成し、対応宣言・仮定・残るgeneric sourceの不足をreportに記す。
対象を有限化した定理だけで本targetを達成したことにはしない。
具体的な反証はtarget-refutedとして記録し、肯定形の再構成定理とは区別する。

G-150はこの再構成の上に量のschemeを作る。Bだけの成立を、
AAT全体の代数幾何化の達成と呼ばない。

成果物はresearch/lean/ResearchLean/AG/のLean証拠と、
research/reports/G-149-aat-native-coalgebraic-reconstruction.mdの宣言・前提対応に置く。
[共通完了基準](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)を適用する。
