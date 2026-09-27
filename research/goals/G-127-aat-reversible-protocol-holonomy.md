# G-127-aat-reversible-protocol-holonomy — 可逆な操作のholonomyによる変更群と持ち上げの分類

- `id`: `G-127-aat-reversible-protocol-holonomy`
- `status`: `active`
- `research mode`: `target-theorem`
- `tracking issue`: [#4981](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4981)
- `source note`: [n1016 §2.3・候補03](../../docs/note/n1016_rising_sea_v2_paper_plan.md)
- `design`: [A–Eの実装設計](../designs/G-127-aat-reversible-protocol-holonomy/README.md)

## 研究目的

可逆な操作を持つ有限プロトコルについて、操作を保つ状態変更の全体と、可視変更を
状態変更へ持ち上げられる条件を明らかにする。閉路に沿う操作の合成からholonomyを
構成し、底を固定する変更群、持ち上がる可視変更の部分群、各持ち上げの全選択肢を求める。

[Rising Sea 定理7.24・7.25、命題7.29](../../outreach/paper/rising-sea/ja/10-comparison-and-information.md)
は、各辺が同じ隠れ状態集合を恒等に運ぶ操作系を分類する。ここでは各頂点の有限集合と
その間の全単射へ広げる。中心化群と群拡大の一般論を、名前付き操作・経路関係から
構成するプロトコル意味論へ接続する。持ち上げの存在と、合成を保つ持ち上げの選択を
区別し、それぞれが失敗する有限例まで同じ分類で説明する。

## 固定target

A–Eを一つの分類・構成定理の構成部分とする。量化順は、Aを満たす任意の入力、
その任意の可視変更 `u∈H`、それに追随するすべての持ち上げとする。
B–Dは各成分の任意の根・全域木について成立させる。有限集合には空集合も許し、
グラフの連結性やfiberの非空性は仮定しない。

### A. 原始入力と操作を保つ変更

有限有向多重グラフ `Q=(V,E,s,t)`、同じ始点・終点を持つ有向経路の等式の有限族 `Π`、
各頂点の有限集合 `F(v)`、全単射 `T_e:F(s(e))≃F(t(e))` を入力とする。
ループ辺・平行辺を許す。経路の作用は辺作用の合成とし、`T` が `Π` を満たすことを
入力条件とする。追加の観測は一元集合への定値写像とする。

`Π` が生成する経路合同関係を保つ部分群 `H≤Aut(Q)` を指定する。
`u∈H` は頂点の置換 `u_V` と名前付き辺の置換 `u_E` を持ち、始点・終点を保つ。
可視変更 `u` の持ち上げ `Lift_F(u)` は、全単射族
`φ_v:F(v)≃F(u_V(v))` で、すべての名前付き辺について

```math
\varphi_{t(e)}\circ T_e=T_{u_E(e)}\circ\varphi_{s(e)}
\tag{A1}
```

を満たすもの全体として定める。これは全状態 `S=Σ_{v∈V}F(v)` 上の全単射
`h(v,x)=(u_V(v),φ_v(x))` で、頂点の観測 `o(v,x)=v` に追随し、名前付き操作を
保つものと対応する。

底を固定する変更群を `Aut_Q(F)=Lift_F(1)` とする。対の集合
`A_F={(u,φ) | u∈H, φ∈Lift_F(u)}` に、実際の状態変更の合成

```math
(u,\varphi)(u',\psi)
=\left(uu',\left(\varphi_{u'_V(v)}\circ\psi_v\right)_{v\in V}\right)
\tag{A2}
```

と恒等・逆を構成して群にし、射影 `p:A_F→H` を群準同型にする。

### B. holonomyと底を固定する変更群

向きを忘れた連結成分の集合を `J=π₀(Q)` とする。各成分 `j` に根 `r_j` と
全域木を選び、根から頂点 `v` への木の道を `τ_v`、その輸送を `P_v` と書く。
道では辺の逆向きの通過も許し、その輸送を `T_e⁻¹` とする。
道 `γ` の輸送を `F(γ)` と書き、`K_j=F(r_j)` と置く。

各辺 `e` に対し、`τ_{s(e)}` で根から始点へ進み、`e` を通り、`τ_{t(e)}` を
逆向きにたどって根へ戻る閉路を `γ_e` とし、元の操作表から

```math
M_e=F(\gamma_e)=P_{t(e)}^{-1}\circ T_e\circ P_{s(e)},
\qquad
\mathrm{Hol}_j(F)=\langle M_e\mid e\text{ は成分 }j\text{ の辺}\rangle
\le\mathrm{Sym}(K_j)
\tag{B1}
```

を構成する。この群が、根を始点・終点とするすべての道の輸送からなる群に一致することを
示す。`C_G(L)` を群 `G` 内の部分群 `L` の中心化群として、根での評価から群同型

```math
\mathrm{Aut}_Q(F)\xrightarrow{\sim}
\prod_{j\in J}C_{\mathrm{Sym}(K_j)}(\mathrm{Hol}_j(F)),
\qquad
\alpha\longmapsto(\alpha_{r_j})_j
\tag{B2}
```

を構成する。逆写像は `α_v=P_v a_j P_v⁻¹` とし、すべての辺の条件(A1)と
群の積を保つことを証明する。

### C. 可視変更の持ち上げ条件と群拡大

`u∈H` が道の各辺名を付け替えた道を `uγ` と書く。根の全単射族
`b_j:F(r_j)≃F(u_V(r_j))` が、各成分のすべての辺について

```math
b_j\circ F(\gamma_e)=F(u\gamma_e)\circ b_j
\tag{C1}
```

を満たすことを持ち上げ条件とする。同じ `b_j` で、名前の対応する各閉路作用を
同時に結ぶ条件である。この条件を満たす根の全単射族と `Lift_F(u)` の間に全単射を
構成する。根での評価の逆は

```math
\varphi_v=F(u\tau_v)\circ b_j\circ F(\tau_v)^{-1}
\qquad(v\text{ は成分 }j\text{ の頂点})
\tag{C2}
```

とする。ここで `uτ_v` は選んだ道を `u` で移したものである。

(C1)に解がある可視変更の集合 `H_lift` を構成し、`H` の部分群であることと
`H_lift=im p` を証明する。包含 `α↦(1,α)` と可視射影による短完全列

```math
1\longrightarrow\mathrm{Aut}_Q(F)
\longrightarrow A_F\xrightarrow{p}H_{\mathrm{lift}}\longrightarrow1
\tag{C3}
```

を得る。各 `u∈H_lift` について、`Lift_F(u)` 上の右作用
`(φ·α)_v=φ_v∘α_v` が自由かつ推移的であることを証明し、持ち上げの全体を
`Aut_Q(F)` のtorsorとして分類する。

### D. 選択の変更、プロトコル意味論、恒等操作への特殊化

**根・木の変更。** 根を結ぶ道の輸送によってholonomy群を共役で対応させ、
(B2)の中心化群表示と(C1)の解の表示を移す。同じ根での木の変更も含め、これらの
表示変更が同じ頂点上の全単射族へ戻ることを示す。その対応は(A2)の合成、可視射影、
核、torsor作用を保ち、三つの選択間での逐次変更は直接変更と一致する。

**独立な意味論との対応。** Aの原始入力から、経路関係で割った実行圏上の
`ProtocolRealization` を構成する。辺作用・経路作用は元の `T` とその合成に一致させる。
`u` による実行の付け替えも経路合同関係へ降下させ、(A1)の持ち上げと、元の実現から
付け替え後の実現への自然同型を対応させる。この対応は各頂点の写像を保ち、
すべての商経路の自然性を与え、合成・射影・核・各fiberの作用と整合する。

**恒等操作系。** 任意の有限 `Q,K`、Aの条件を満たす `Π,H` に対し、
`F(v)=K`、`T_e=id` へ特殊化する。holonomyは自明、`H_lift=H` となり、
成分ごとの置換による分類、恒等な隠れ状態変更を用いるsection、分裂短完全列と
各fiberのtorsorが第7章の分類に一致することを示す。
`Π` が空の場合には、既存のFixedFプロトコル変更群との群同型を、元の辺名と状態写像、
可視射影、section、核、各fiberの作用を保って構成する。
[G-124 D・E](G-124-aat-local-semantic-reconstruction.md)の恒等操作系に対する
成分代表での読み取り・延長が、(B2)・(C2)の特殊化に一致することも示す。

### E. 有限表からの判定と構成

有限集合 `V,E,F(v),H` は列挙と等号判定を持ち、始点・終点、辺の全単射、
経路等式、`H` の元の頂点・辺への作用を有限表で与える。Aの入力条件を満たす
表に対して、根・全域木と(B1)の有限生成族を構成し、(B2)の中心化条件と
(C1)の持ち上げ条件を判定する停止手続きを与える。

任意の `u∈H` に対し、持ち上げが存在する場合は頂点ごとの全単射表を返し、
存在しない場合は不存在を返す。その判定が、Aで独立に定義した `Lift_F(u)` の
非空性と同値であり、返した表が(A1)を満たすことを証明する。
これにより `H_lift` を求め、成功時の一つの持ち上げと(B2)・Cのtorsorから
すべての持ち上げを復元できることを示す。

計算に関する完了条件は有限手続きの停止と正確性とする。
費用の扱いは[n1016 §9.1](../../docs/note/n1016_rising_sea_v2_paper_plan.md#91-一枚のカードで何を定めるか)に従う。

## 既存宣言の参照

Research pathは `research/lean/ResearchLean/AG/` からの相対とする。
宣言の参照版はactive化時にtracking Issueへ記録する。

| 用途 | path・宣言 |
| --- | --- |
| 独立なプロトコル意味論・生成辺からの延長(D) | `RealizationReconstruction/ProtocolSemantics.lean` の `ProtocolRealization`、`ProtocolReconstruction.lean` の `homEquivGeneratorMap` |
| 有限表からの実現(D・E) | `RealizationReconstruction/ProtocolFinitePresentation.lean` の `ProtocolPresentation.decoder`、`decoderObject_edgeAction` |
| 恒等操作系の成分表示・群拡大(D) | `RealizationReconstruction/FixedFComponentClassification.lean` の `equivComponentPermutationFamilies`、`FixedFSplitExactSequenceAndTorsor.lean` の `isGroupShortExact`、`canonicalSection_rightInverse` |
| 既存のプロトコル変更群(D) | `RealizationReconstruction/FixedFProtocolGroupConnection.lean` の `ProtocolChangeGroup`、`mulEquivFollowingGroup`、`projection_compatibility`、`section_compatibility`、`kernelMulEquiv`、`projectionFiberEquiv` |
| G-124の成分代表の読み取り(D) | `LocalSemanticReconstruction/CSFixedFDetermining.lean` の `protocol_representatives_determining` |

## 前提・構成台帳

| 対象・対応条項 | 役割 | 必要な構成・証拠 | 出所・使用先 |
| --- | --- | --- | --- |
| `Q,Π,F(v),T_e,H`(A) | 入力として保持 | Aの有限性・全単射性・経路等式・合同関係の保存 | 原始データからB–Eへ |
| 根・全域木・道の輸送(B) | 構成義務 | (B1)、任意の選択についての成立 | 有限グラフと辺の逆輸送からB・C・Eへ |
| holonomy・中心化群表示(B) | 構成・証明義務 | (B1)・(B2) | 元の辺作用からCの解とEの判定へ |
| `Lift_F(u),A_F,H_lift` と完全列・torsor(A・C) | 構成・証明義務 | (A1)・(A2)、(C1)–(C3)と右作用 | 原始入力と根での条件から、存在・全選択肢の分類へ |
| 表示変更・意味論との対応・既存結果への特殊化(D) | 構成・証明義務。既存宣言は再利用 | Dの三対応 | B・Cと既存decoder・FixedF宣言から同じ写像を保つ対応へ |
| 有限表の列挙・等号判定(E) | 実行可能な入力として保持 | Eの入出力、停止・正確性 | 原始入力の有限表からB・Cの判定・復元へ |
| 完了条件2・3の有限例 | 全入力条件と結論の証明義務 | 各項の固定データと評価 | 同じ例をB–Eへ適用して分類と判定を具体化 |

## 完了条件

1. A–Eを同じ原始入力・変更群についてLeanで証明する。達成として認める結果は
   `target-theorem-proved` とする。以下の不存在・非分裂は、指定した命題の証明として扱う。
2. **持ち上げが存在しない例。** 一頂点、二つの名前付きループ `a,b`、
   `F(v)={0,1}`、`T_a=id`、`T_b=τ=(01)`、`Π=∅` とする。
   `H=C₂` は頂点を固定して `a,b` を交換する。元の実現と辺名を交換した実現で
   holonomy群はともに `C₂` だが、交換 `u` には(C1)の解がなく、
   `H_lift={1}` であることを示す。Bの中心化群表示とEの不存在判定も同じ入力へ適用する。
3. **持ち上げを合成と整合して選べない例。** 二頂点 `0,1`、辺 `a:0→1` と
   `b:1→0`、各fiber `{0,1}`、`T_a=id`、`T_b=τ=(01)`、`Π=∅` とする。
   `H=C₂` は頂点と辺を同時に交換する。A–Cの実際の群・写像について
   `Aut_Q(F)≅C₂`、`A_F≅C₄`、`H_lift=H` を構成し、可視射影を `C₄→C₂` の
   剰余写像と対応させる。可視の交換の二つの持ち上げがともに位数4であり、
   射影に群準同型のsectionがないことを証明する。Eの手続きが返す持ち上げを
   この二つのいずれかとして読み戻し、Cのtorsorがその両方を与えることを示す。
4. Lean成果を `research/lean/ResearchLean/AG/` に置き、
   `research/reports/G-127-aat-reversible-protocol-holonomy.md` にA–Eと宣言、
   前提の出所・使用先、有限例、停止・正確性の証拠を対応させる。
5. [共通基準の参照適用](../../.codex/skills/target-theorem-loop/references/target-goal-contract.md#共通基準の参照適用)
   に従って完了を判定する。適用版、検証、査読、実行状態はIssue・reportへ置く。
