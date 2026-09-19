# Rising Sea — 数学内容の棚卸し

[論文構成マスター](paper-structure.md)に従い、数学の対象、許容射、仮定、結論、
具体例と一次資料への対応を記す。§1では、モデル同期とプロトコルの意味論、
共通の変更分類、再構成、有限決定性に関する数学を扱う。

## 1. CS との対応

### 1.1 モデル同期 — 読取りと更新を保つ変更

view の集合 `V` と基準値 `v₀` を固定し、状態集合 `C`、読取り `g:C→V`、
更新 `p:C×V→C` を持つ全域 lens を扱う。対象条件は次の三法則と、
基準 fiber `K_L={c∈C | g(c)=v₀}` の有限性とする。`V` 自体は無限でもよい。

\[
 p(c,g(c))=c,\qquad g(p(c,v))=v,\qquad p(p(c,v),w)=p(c,w).
\]

固定 view 上の一般の意味保存射は、`g'h=g`、`h(p(c,v))=p'(h(c),v)` を満たす関数 `h` とする。
三法則から `c↦(g(c),p(c,v₀))` による積表示 `C≃V×K_L` を与え、
基準 fiber への制限と、任意の写像 `t:K_L→K_L'` の延長

\[
 \operatorname{ext}(t)(c)=p'\bigl(t(p(c,v_0)),g(c)\bigr)
\]

が互いに逆になることを示す。この対応により有限集合間の table から一般射を回復する。

可視変更 `u:V≃V` に追随する可逆変更 `h:C≃C'` には、同じ `h,u` による
`g'h=ug` と `h(p(c,v))=p'(h(c),u(v))` の同時成立を要求する。
積表示での形 `h(v,k)=(u(v),φ(k))` により、変更を一つの補完の全単射 `φ` で記述する。
`u` は `v₀` を固定する必要がない。

`V=K=Bool` の積 lens で `h(v,k)=(v,k⊕v)` を取る例を導入に置く。
この変更は get を保つが put を保たず、可視変更を恒等に固定したとき、
get のみを保つ変更 4 個のうち get・put を共に保つものは 2 個になる。
この差を、第7章の変更分類と第8章の有限決定性へつなぐ。

### 1.2 プロトコル — 名前付き操作と adapter を保つ変更

有限有向多重グラフ `Q` と有限個の経路等式 `L` から実行圏 `C_Q` を定める。
観測先の関手 `O:C_Q→Set` を固定し、各制御点の状態が有限である関手 `X:C_Q→Set` と
自然変換 `o:X→O` を実現とする。一般射 `a:X→Y` は観測を保つ自然変換とし、
非可逆な adapter も含める。観測値の集合は無限でもよい。

有限表示は、制御点ごとの状態 table、名前付き生成辺の作用、各状態の観測値、
経路等式から構成する。一般射は、生成辺 `e:v→w` ごとの
`a_w X(e)=Y(e)a_v` と `o_Y(v)a_v=o_X(v)` を満たす頂点 table から回復し、
経路帰納によって全実行へ延長する。異なる操作名は、状態写像が同じ場合にも保持する。

adapter `q:X→Y` と `q':X'→Y'` に対する変更 `a:X→X'`、`b:Y→Y'` の条件を
`b∘q=q'∘a` とする。各頂点でのこの等式と操作保存から、全実行との整合を示す。
可逆変更の分類では `a,b` を同型に制限し、adapter 自体は一般射のまま扱う。
操作名を変える版では、グラフ自己同型と経路等式・観測の輸送を別の入力として定める。

### 1.3 CS 意味論から AAT の比較への対応

第1章で導入する対応では、型・役割・操作名を Atom 側に、状態 carrier と実行の値を
Source・対象・局所実現側に配置する。lens の読取り・更新とプロトコルの名前付き実行を
operation として構成し、三法則・経路等式・観測の保存を Law と射の条件に対応させる。
射の許容条件は CS 側のデータから定め、構成と読み戻しの両逆を示す。
非単射な状態写像や補完 table も、この対応の対象に含める。

lens の同時保存は、get と put をまとめた射
`c_L:C⊔(C×V)→V⊔C` と、連動する端点変更 `h⊔(h×u)`、`u⊔h` の可換図式で表す。
同じ状態 carrier が現れる各箇所に同じ `h` を作用させる条件を、許容変更の部分群として
保持する。プロトコルでは名前付き操作の可換図式と adapter の図式を保持する。
これらを第4章の合成、第7章の比較保存群、第8章の表示へ接続する。

完全幾何への対応では、context・coverage・overlap・係数・raw restriction・
Support・Axis・Observable を構成し、それぞれの保存則を示す。
比較群を運ぶ箇所では、充満忠実な関手による比較群の同型と、底を固定する条件や
CS の許容条件への制限を明記する。実生成比較と正規化に沿って、section、制限の核、
ambient な核、lift fiber のどれを回復するかを揃える。

### 1.4 二つの問題で共有する変更分類

共通定理の入力は、有向多重グラフ `Q=(V,E,s,t)`、隠れ状態の集合 `K`、
許容する可視変更群 `H≤Aut(Q)` とする。状態は `V×K`、観測は `(v,k)↦v`、
各名前付き辺 `e:v→w` の操作は `(v,k)↦(w,k)` と定める。

`u∈H` 上の観測保存変更は、頂点ごとの置換を用いて `h(v,k)=(u_V(v),φ_v(k))` と一意に書ける。
操作保存は各辺での `φ_{s(e)}=φ_{t(e)}` と同値になり、向きを忘れた連結成分 `π₀(Q)`
ごとの置換族へ降下する。操作も保つ組 `(u,h)` の群を `A_Q` とすると、

\[
 1\longrightarrow\prod_{j\in\pi_0(Q)}\operatorname{Sym}(K)
 \longrightarrow A_Q\longrightarrow H\longrightarrow1
\]

は、隠れ状態を変えない変更を section として分裂する。
各 `u` 上の変更の集合は核の torsor であり、`V,K` が有限なら個数は
`(|K|!)^{|π₀(Q)|}` になる。`H` の連結成分への作用を合成に含め、半直積として記述する。

積 lens はすべての view 間の put を辺とする連結な入力であり、核は `Sym(K)` となる。
プロトコルには、各制御点の状態を同じ `K`、各生成辺の状態作用を恒等とする
セッションモデルを代入し、連結成分ごとに独立な補完の変更を得る。
この共通分類の適用範囲は、ここに定めた辺の作用を持つ入力とする。

基準補完 `k₀` を保つ版では `Sym(K)` を `k₀` の固定部分群に置き換える。
lens 側では、`g(s(v))=v`、`p(s(v),w)=s(w)` を満たす選択 section `s:V→C` の保存に対応する。
`V=Bool`、`K={0,1,2}`、`k₀=0` の有限例では、get と選択値を保つ変更 4 個のうち
put も保つものは 2 個になる。ここでも可視変更は恒等に固定する。
プロトコルの有限例は、頂点 `{0,1,2,3}`、辺 `0→1` と `2→3`、`K=Bool` とする。
可視変更を恒等に固定すると、観測保存変更 16 個のうち操作も保つものは 4 個であり、
二つの辺を交換する可視変更の上でも追随変更は 4 個となる。

### 1.5 再構成と有限決定によって CS へ戻す帰結

第8章では、lens の有限基準 fiber とプロトコルの有限生成 table による再構成を、
整合する局所データからの再構成と対応させる。一般の意味保存射を含む圏同値を与え、
冪等射の分裂、Karoubi 再構成、retract、射の圏への拡張を同じ対応で結ぶ。
比較保存群の輸送も整合させ、表示側から元の変更の自由度を回復する。

有限読み取りには次の三性質を別々に定める。

| 性質 | 意味と、CS の帰結として示すこと |
| --- | --- |
| 区別 | 読み取りが対象とする射・変更の集合上で単射であり、同じ有限データから異なる射を取り違えない |
| 延長 | 有限片の独立な整合条件を満たす任意のデータから、全域の射・変更を構成できる |
| 実効性 | 列挙可能な有限入力と必要な等号判定を指定し、整合判定と延長を計算できる |

一般射の層では、lens は基準 fiber の任意の table が意味保存射へ延長する。
プロトコルは、全頂点・状態の table における型、生成辺、観測の整合条件から延長する。
どちらも制限・延長の両逆を示す。実効性には状態・生成辺の列挙と必要な等号判定を
入力として指定し、有限性の存在命題から計算手続きを得たことにはしない。

§1.4 の可逆変更族では、可視変更 `u` を固定し、有限頂点集合 `S⊆V` で隠れた置換を読む。
`|K|≥2` のもとで、次の同じ判定を両方の CS 問題へ適用する。

- 区別の必要十分条件は、`S` が全連結成分と交わることである。
- 延長の必要十分条件は、同じ連結成分にある `S` の任意の二頂点が、`S` 上の誘導グラフでも
  結ばれることである。局所整合条件は、両端が `S` にある辺での置換の一致とする。
- 区別と延長を満たす有限決定集合が存在する必要十分条件は、`π₀(Q)` の有限性である。
  各成分から一頂点を選べば決定集合となる。

この判定で数えるのは読み取る頂点であり、一つの読み取りの値は `K` 上の置換全体である。
有限量の table による決定には、さらに `K` の有限性を明示する。
lens では基準 fiber 上の置換 table、上記セッションモデルでは各成分の代表頂点における
置換 table が変更を決める。有限の頂点・辺・隠れ状態を明示的に列挙した入力では、
整合判定と延長の計算も示す。一般のプロトコル射には、前段の頂点・生成辺 table による
再構成を適用する。

同一定義で扱うタグ変更族では、二元巡回群 `C₂` を用いて、全有限制限の整合族との群同型

\[
 C_2^{\Omega}\cong\varprojlim_{S\subseteq_{\mathrm{fin}}\Omega}C_2^S
\]

を与える。
`Ω` が無限なら、どの有限集合の外でも変更を残せるため有限読み取りによる区別は成立しない。
全有限片からの再構成と有限決定性の違いを、lens・プロトコルの成立条件と並べて説明する。

### 1.6 一次資料との対応

定義・命題ごとの量化、仮定、結論と対応する宣言を、以下の資料から照合する。

| 対象 | 主な照合先 |
| --- | --- |
| lens・プロトコルの独立な意味論 | [LensSemantics](../../../research/lean/ResearchLean/AG/RealizationReconstruction/LensSemantics.lean)、[ProtocolSemantics](../../../research/lean/ResearchLean/AG/RealizationReconstruction/ProtocolSemantics.lean) |
| 読取り・更新の同時保存と adapter 図式 | [lens の操作図式](../../../research/lean/ResearchLean/AG/RealizationReconstruction/CSAATLensRelativeOperationSquares.lean)、[protocol の adapter 図式](../../../research/lean/ResearchLean/AG/RealizationReconstruction/CSAATProtocolAdapterSquares.lean) |
| 変更分類、分裂短完全列、有限例 | [連結成分による分類](../../../research/lean/ResearchLean/AG/RealizationReconstruction/FixedFComponentClassification.lean)、[分裂と torsor](../../../research/lean/ResearchLean/AG/RealizationReconstruction/FixedFSplitExactSequenceAndTorsor.lean)、[三つの有限例](../../../research/lean/ResearchLean/AG/RealizationReconstruction/FixedFFiniteExamples.lean) |
| Karoubi 再構成と比較群輸送 | [CS の Karoubi 再構成](../../../research/lean/ResearchLean/AG/RealizationReconstruction/CSKaroubiReconstruction.lean)、[充満忠実な関手による比較群輸送](../../../research/lean/ResearchLean/AG/RealizationReconstruction/CSAATFullyFaithfulComparisonTransport.lean) |
| 一般の意味保存射の有限決定 | [lens の一般射](../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/LensSemanticFiniteDetermination.lean)、[protocol の一般射](../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/ProtocolObservedFiniteDetermination.lean) |
| 可逆変更の有限決定と連結成分の判定 | [lens の可逆変更](../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/LensFiniteDetermination.lean)、[protocol の可逆変更](../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/ProtocolFiniteDetermination.lean)、[有限決定集合と成分の有限性](../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/FiniteDeterminingComponents.lean) |
| 有限表示と局所表示の整合 | [lens の整合](../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/LensFiberKaroubiCoherence.lean)、[protocol の整合](../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/ProtocolObservedKaroubiCoherence.lean) |
| 全有限読み取りからのタグ変更の回復 | [TagChangeFiniteReadingRecovery](../../../research/lean/ResearchLean/AG/LocalSemanticReconstruction/TagChangeFiniteReadingRecovery.lean) |

lens の三法則と定数補完、schema の関手意味論、一般的な圏同値・核・torsor の結果は
それぞれの原典に帰属させ、AAT 固有の入力構成と比較・正規化への接続を明記する。
