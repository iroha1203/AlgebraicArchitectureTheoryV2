# G-139-aat-law-coefficient-extension — Law表示と診断の係数拡張

- `id`: `G-139-aat-law-coefficient-extension`
- `status`: `draft`
- `research mode`: `target-theorem`
- `tracking issue`: [#6359（設計）](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/6359)。個別のResearch Loop Issueはactive化時に定める。
- 設計: [多項式特殊化ノート §3–4](../../docs/note/n1020_shigure_polynomial_specializations.md#3-原始入力と独立な実現)

主経路は[n1019](../../docs/note/n1019_shigure_representability_design.md)のG-149〜G-152にある。
本カードは多項式特殊化を構成する。主経路と同じ対象・射・Law評価への比較を要し、
本カードの達成だけでSHIGURE全体の達成とはしない。

## 研究目的

Atom / Lawの式と、K0/K1から生成する診断複体について、係数を変えたときに保存される
構成を明らかにする。既存の一般可換環上のlaw algebraとℚ上の診断を接続し、
係数変更とLaw評価値の再同定を区別する。

## 固定target

### A. 式の係数自然性

任意の可換環kとノート§3.1の原始表示Pについて、各tensor式の基底上の成分を
多項式として生成する。量化はk、P、基底chart I、k代数R、演算・生成元の係数の順とする。
式の解釈と生成多項式の評価が一致し、任意のk代数射R→Sと基礎環射k→k′に関して
可換になることを証明する。恒等と合成の式も含める。

加群・tensor積の標準等式が成分多項式の恒等式になることを証明する。
個別の方程式は全てrequired Lawとして宣言し、その残差idealを生成する。
環射による係数変更後の生成idealが元のidealのextensionに一致することを示す。
商環のscalar extension同型と変数・Law別生成元の対応を構成する。
既存の`StructuralRelationFamily`を使う場合の関係族は空とする。
flatnessはこの条項の仮定にしない。

### B. 同じK0/K1からの整数モデル

既存の`FiniteLawFamily`、finite Source、adequate reading、`TargetSupportedNerve`の
全入力を量化する。既存の`CellCoordinate`、chart / edge / face supportをそのまま使い、
ノート§4のC_ℤと微分を生成する。d¹d⁰=0をface endpoint等式から証明する。

任意の可換環kでk⊗_ℤ C_ℤ≅C_kを次数0–2、微分、生成されたreading比較射について
構成する。k=ℚで`lawGeneratedComplex`、`lawGeneratedD0`、`lawGeneratedD1`と
一致する同型を与え、`GeneratedComparisonMap`の次数別射への可換図式を証明する。
座標を複製・削除せず、同じLaw値の複数の出現は一つのlabelになる。

### C. コホモロジーと情報の反映

任意のflatな環射k→k′について、Bの同じ複体から
k′⊗_k Hⁱ(C_k)≅Hⁱ(C_{k′})をi=0,1,2で構成する。
faithfully flatな射では、各コホモロジー類が移送後に零になることと、元の類が零である
ことの同値も証明する。一般の複体について、非flatな射での比較同型と、flatなだけの
射での零性反映への反例をノートW4(a)で構成する。この対照例だけからBの複体における
flatnessの必要性は結論しない。
W4(b)では、同じ二source・一Law・値0,2からK0を実際に生成し、値域をF₂へ写す
操作によるindex変化と、indexを保持するscalar extensionの相違を証明する。

### W. 元の表示への適用

ノートW1とW3のAtom / Law式からAの多項式と商環を生成し、W1の可逆性の残差と
W3の非零な冪零元を評価する。Bは零複体だけでなく、全chart台が一つの共通Law値を
含む三辺のcycle・faceなしのnerveで発火させ、H¹(C_ℤ)≅ℤとℚ特殊化を証明する。
W4(a)の×2をこのK0微分と同一視しない。

## 前提・構成台帳

| 対象 | 役割 | 出所・構成義務 | 使用先 |
| --- | --- | --- | --- |
| k、型付き有限式、係数射 | 入力として保持 | ノート§3.1。各Lawの式と出現Atomを保持 | A |
| scalar多項式環・商環の標準API | 既存定理 | `LawAlgebra/AmbientAlgebra`、`ReadingFunctoriality/Coefficient`の仮定を照合 | Aの評価・ideal比較 |
| finite Source、Law族、adequacy、chart台・face等式 | Bの入力 | `ResolutionInvariance/LawGeneratedComplex`の同じ型 | B |
| 整数微分・比較射・ℚ同定 | 構成・証明義務 | Bの同じ座標とincidenceから生成 | B・C |
| flatness | Cの一般定理の仮定 | scalar extensionの完全性に使用。A・Bでは不要 | C |
| faithful flatness | 零性反映の十分条件 | scalar extensionの忠実性とflatな比較同型を使用 | C |
| Wの全例 | 構成・証明義務 | 原始式または明示されたnerveから生成 | 非空虚性と仮定の必要性 |

## 完了条件

A–C・Wの構成、同型、可換性と指定例をLeanで証明し、宣言と前提の対応を
`research/reports/G-139-aat-law-coefficient-extension.md`に記す。
証拠は`research/lean/ResearchLean/AG/`に置く。
[共通完了基準](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)を適用する。

固定主張が偽の場合は、入力条件を満たす具体的反例、破れる写像・等式、原始データからの
構成を証明して`target-refuted`として決着させる。肯定形の証明完了とは区別する。
G-140が必要とする成果はAの式・係数部分であり、CをSemの全環射量化の条件にしない。
