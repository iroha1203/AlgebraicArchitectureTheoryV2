# G-119-aat-realization-comparison-idempotents — 実現・比較の圏と冪等正規化

- `id`: `G-119-aat-realization-comparison-idempotents`
- `status`: `draft`
- `research mode`: `target-theorem`
- `tracking issue`: 未作成。active化時に参照を確定する。
- `source note`: [n1010 §1–2・§4.3・§9.2](../../docs/note/n1010_aat_post_annapurna_conjectures_research_plan.md)

## 研究目的

実現、その間の比較、比較を維持する変更を、冪等像も含めた一つの圏で扱えるようにする。
G-116の像の同型とG-118の比較群をこの圏へ接続し、後続の観測と有限表示が読む対象を定める。
さらにcanonical正規化が比較を運ぶ関手になることと、対象ごとの射影の自然性が失敗することを、
同じ構成の中で証明する。これはn1010のS1に対応する。

## 固定target

以下は通常の合成記法 `gf = g ∘ f` を用いる。Leanの `f ≫ g` は `gf` に対応する。
一般圏の対象と射には任意のuniverseを許す。AATへの適用は既存宣言のuniverseに従い、
Atom carrierの有限性は要求しない。

### A. 比較と冪等完備化の交換

任意の圏 `E` に対し `M(E) := Arr(Kar(E))` を定め、同値

\[
T_E:\operatorname{Kar}(\operatorname{Arr}(E))
  \simeq\operatorname{Arr}(\operatorname{Kar}(E))
\]

を構成する。左辺の対象 `(c:X→Y,e,d)` は `e²=e,d²=d,dc=ce` を満たし、
その像は `((X,e),(Y,d),dce)` とする。射は端点の写像 `(u,v)` を保つ。
逆方向は `a=dae` を満たす像の比較からraw比較 `c=a` と冪等対 `(e,d)` を取る。
両方向の関手、単位・余単位の自然同型、同値の三角恒等式を証明する。
単位の両方向のunderlying正方形は `(e,d)`、余単位の両方向の端点写像も
各Karoubi対象の冪等射とする。これらはKaroubi内の恒等射であり、rawな恒等射とは区別する。

任意の関手 `F:E→E'` に対し、この同値と `Kar(Arr(F))`、`Arr(Kar(F))` の
可換な自然同型を構成する。端点・比較射の成分を特定し、恒等関手・関手の合成との整合も示す。
その端点成分は `(F(e),F(d))` とし、同じ像の比較を結ぶKaroubi内の恒等成分として固定する。
可換性を関手の等号で実現する場合も、その等号から得る自然同型を同じ条件で評価する。
可逆な表示変更の圏は `M(E)` の最大亜群とし、その対象には非可逆な比較も含める。

### B. AATの三段の投影とqualified比較群

任意の `U : AtomCarrier.{u}` と既存の幾何universe `v` に対し、
`E_geom := GeomReadCategory U`、`E_core := AATCorePackage U`、
`B := ExtractionInstance U`、`ρ := geometryProjection`、`π := packageProjection`
を用いる。Aをこの三圏と投影関手へ適用し、合成投影 `πρ` との整合を証明する。
一般の冪等対象の投影先は `Kar(B)`、比較の投影先は `M(B)` とする。

任意の `G,H : GeometryPackage.{u,v} U` と `c : GeometryTotalHom G H` に対し、
`c` を恒等冪等射によって `M(E_geom)` の対象へ埋め込む。その自己同型のうち、
両端の写像が `πρ` によってそれぞれの底の恒等射へ送られるものを部分群とする。
この群と既存の `qualifiedComparisonSubgroup c` の群同型を構成し、両端への射影と
underlyingな完全幾何写像が一致することを示す。`c` 自身の底への像には恒等性を要求しない。

同定は任意の `c` に加え、G-118の任意の
`ctx : ActiveRefinementBCContext U`、`P : FiniteTransportPresentation.{u}`、`k : CommRingCat.{v}`、
`I : UpperGeometryCompatibleProblemInputData ctx P k`、`i : P.Vertex` から生成される
`I.generatedCompatibleUpperGeometryMateAt i` へ適用する。生成された両端と比較射を保った
対象を与え、この比較群の同定がその生成比較についての既存の両端射影に一致することを示す。

### C. G-116の実際のKaroubi像の配置

任意の `U`、`[DecidableEq U.Atom]`、`input : AuthoredBCDatumSquare U`、
`cochain : DefectCochain input.toTransportData`、`cell : input.context.Category` を量化する。
既存の `authoredDiagnosticObjectCollapseKaroubiIso input cochain cell` のhomを
`M(CoreFiber input.context.square.semantic.square.northeast)` の対象として配置し、
core fiberの忘却関手に沿って `M(E_core)` へ送る。

両端は既存の `authoredDiagnosticImageSourceKaroubi` と
`authoredDiagnosticImageTargetKaroubi`、比較のunderlying射は既存の `β` と一致させる。
既存の可逆mateを `α`、cell projectorを `E` と書けば、source冪等射 `α⁻¹β`、
target冪等射 `E`、逆射 `α⁻¹E` の成分一致を証明する。
Aの左辺へ入れる対象はraw比較 `α` と冪等対 `(e:=α⁻¹Eα,E)` とする。
`Eα=αe`、`e=α⁻¹β`、`Eαe=β` を既存の `β=Eα` と冪等性から導き、
その `T` による像が上記の既存Karoubi同型のhomと一致することを示す。
両冪等射の底への像が恒等であることも証明する。
この条項の幾何段への持ち上げはn1010のS4で扱う。

### D. canonical正規化の関手と自然な包含

任意の `U` について、`C` を `CanonicalObjectNormalizationAdmissible P` を満たす
core packageの充満部分圏とする。各対象の既存の
`e_P := canonicalObjectNormalizationTotal P admissibleP` を用いる。
任意の `P,Q : C` と任意のtotal射 `f:P→Q` に対し、

\[
e_Q f e_P=f e_P
\]

をtotal射の等号として証明する。object mapの等号に加え、operation写像の依存する型を
含む全計算成分を照合する。片側吸収やoperation coherenceを追加入力にせず、
既存のadmissibilityとtotal射の法則から導く。

`N_C` は対象を `P:C`、射を `a:P→Q` かつ `a=e_Q a e_P` とする圏とし、
恒等射を `e_P`、合成を元の合成とする。これは選択した像を対象ラベル付きで扱う圏である。
`K:N_C→Kar(C)` を `P↦(P,e_P)` とする充満忠実な関手として構成する。
`N:C→N_C` を対象上で恒等、射上で `N(f)=f e_P` として構成し、その充満性を証明する。
この充満性は固定した任意の `P,Q:C` 間の全sandwich射について要求する。

包含 `V:C→E_core` に沿う `Kar(V)K:N_C→Kar(E_core)` と、そこから誘導する
`Arr(N_C)→M(E_core)` を構成し、正規化後の比較のunderlying射が `c e_P` であることを示す。
また `π(e_P)=1` を証明し、`π_N:N_C→B` を対象 `P↦packagePoint P`、射 `a↦π(a)`
で構成する。`π_N N=πV` の対象・射での一致により、正規化前後の底の比較を同一視する。

raw埋込み `J:C→Kar(C)` に対し、成分 `i_P=e_P` を持つ自然変換 `i:KN→J` を構成する。
対象別の逆向きの射 `p_P=e_P:J(P)→KN(P)` は `p_P i_P=1_{KN(P)}` を満たす。
各射 `f` での `p` の自然性が `f e_P=e_Q f` と同値であり、さらに既存の
`CanonicalNormalizationOperationCoherent` と同値であることを証明する。

G-117の固定された `taggedOperationPackage`、そのadmissibility、
`taggedEndpointFlipTotal` を同じ `C` に入れる。その射では片側吸収と `i` の自然性が成立し、
`p` の自然性は `taggedEndpointFlip_not_natural` の不等式によって失敗することを示す。
不等式は同じ例の既存Bool operationの両合成への評価に接続する。

任意の `P,Q:C` と `c:P→Q` に対して、Nから全自己同型群上の準同型

\[
r_N:\operatorname{Aut}_C(P)\times\operatorname{Aut}_C(Q)
\longrightarrow\operatorname{Aut}_{N_C}(P)\times\operatorname{Aut}_{N_C}(Q)
\]

を構成し、`pc=cb` を満たす対の像が `N(p)N(c)=N(c)N(b)` を満たすことを証明する。
従ってraw側の比較を保つ部分群から像側の比較を保つ部分群への準同型を得る。
底を固定する資格はraw側では `πV`、像側では `π_N` によって両端の自己同型のhomが
恒等射へ送られることとし、この資格を課した両部分群への準同型の制限も構成する。
この準同型の反映性・lift全射性の成立判定は後続のS2・S4で扱う。

## 前提・構成台帳

| 対象・対応条項 | 役割 | 必要な構成・証拠 | 出所・使用先 |
| --- | --- | --- | --- |
| 任意の圏・関手と冪等対（A） | 入力として保持 | Aの関係式 | 交換同値とその自然性 |
| AATの三圏・投影（B） | 既存入力として保持 | Bの投影・群同型 | 既存Categories、ObstructionGroups、QualifiedComparisonStabilizerから比較の圏へ |
| G-118の生成入力（B） | 入力として保持 | Bの実比較への適用 | 既存生成器から対象・比較を得て群同定へ |
| G-116のdatum・cochain・cell（C） | 入力として保持 | Cの成分一致と投影 | 既存Karoubi同型とcell factorizationからA・Bの圏へ |
| packageのadmissibility（D） | 入力として保持（対象条件） | 既存の5法則。Dの片側吸収は構成義務 | canonicalなtotal射を定義し、任意のtotal射との片側吸収へ |
| N、包含、投影、誘導準同型（D） | 構成・放電義務 | Dを参照 | 片側吸収・冪等性から関手性、充満性、比較の保存、M(E_core)への接続へ |
| Bool-tag例（D） | 構成・放電義務 | 既存の証明によるadmissibilityの放電と、同じ例でのDの正負の式 | 既存の具体的operation評価から射影の自然性の失敗へ |

admissibilityは一般部分圏を指定する入力条件であり、全packageについてその成立を求めない。
固定Bool-tag例では既存の証明からこの条件を放電する。

## 完了条件

A–DをすべてLeanで構成・証明し、条項と宣言の対応、入力から結論への使用経路、
固定例の評価証拠を `research/reports/G-119-aat-realization-comparison-idempotents.md` に記録する。
新規Lean成果物は `research/lean/ResearchLean/AG/` に置き、使用した既存宣言と参照版をreportへ記録する。

[共通基準の参照適用](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)
による監査・独立最終レビューを完了判定に適用する。Dの固定された自然性の失敗は証明すべき
結論の一部である。それ以外の固定主張への反例は共通の反証停止規則で扱う。
承認・適用版・放電状況・検証・査読の記録はtracking Issueとreportに置く。
