# 意味保存射、操作語、nerve

## 定義 A1 — 実際のmapを持つ変更

G-139 N1の原始signatureを固定する。model `A,B` の各sortについて実際の関数 `h_s:A_s→B_s` を与える。operationの可換式、relationの順方向保存、partial operationのdomain保存、指定値の保存を全て要求する。観測sort `O` と `o_A,o_B` を固定し、`o_B h=o_A` を追加する。この全mapの集合を `Chg_o(A,B)` とする。

観測が複数sortを読むなら各成分にこの式を置く。既存の状態mapを候補にしたときの検査は、まさにこれらの原始式への代入である。単射性・全射性・可逆性を追加しない。恒等は全保存式を満たし、二つの保存正方形を貼れば合成も満たす。G-139 N1の同じ圏の上に観測を加えた圏が得られる。

## 定理 A2 — 全有限語と有限termの保存

全域単項操作を `step(e):S→S` とする。語は左から実行し、

```math
\operatorname{eval}(x,[]) =x,\qquad
\operatorname{eval}(x,e::w)=\operatorname{eval}(\operatorname{step}(e)(x),w).
```

`h step_A(e)=step_B(e)h` なら、語長の帰納法で

```math
h\operatorname{eval}_A(x,w)=\operatorname{eval}_B(hx,w),\qquad
o_B\operatorname{eval}_B(hx,w)=o_A\operatorname{eval}_A(x,w).
```

空語は恒等、`e::w` では生成操作の保存式を一度使ってから帰納法を適用する。一般のfinite arityでは変数・定数・operation適用というterm帰納法に置き換える。同じ入力を複数回使うときはG-139 N2のcopyingを用いる。

partial operationとphaseについては、宣言された開始phase、各辺のdomain、直前の出力が次のdomainに入る条件を保持する。語のdomainはこれらの反復pullbackで生成する。そのdomain上で同じ帰納法を行う。元のdomainを、保存に失敗する点だけ除いて変更することはしない。

### A2.1 — Trace一致が射を与えるとは限らない

`o:S→O` に対し、同じ系の二状態がbehaviorally equivalentであるとは、全語の観測が等しいことである。これは状態間の関係であり、指定されたmapのoperation保存とは違う。

例えば `S={0,1}`、唯一の操作を交換、観測を一点への定値mapとする。全traceは同じである。しかし定数map `h(x)=0` は `h step(x)=0` と `step h(x)=1` が異なるため構造保存射ではない。全語の**状態mapの可換性**は空語・一文字を含むので生成式と同値だが、全語の**観測値だけの一致**からその可換性は導けない。

### A2.2 — 観測の強化

強い観測 `o^+:S→O^+` と `r:O^+→O` があり `o=r o^+` とする。`o^+` を保つ実際の `h` は同じmapで `o` を保つので

```math
\operatorname{Chg}_{o^+}(A,B)\hookrightarrow\operatorname{Chg}_{o}(A,B)
```

を得る。恒等と合成を保ち、係数変更とも可換である。包含は真になり得る。操作なしの二元集合で、弱い観測を定値、強い観測を恒等とすると、前者は全関数を許し、後者は恒等だけを許す。

## 定義 A3 — 操作語翻訳を持つ射

異なるsignatureでは、sort対応 `f`、各source operationをtargetの同じ入出力型の有限termへ送る代入 `τ`、実際のsort maps `h:A→f^*B` をデータとする。条件は

```math
h\omega_A=(\tau\omega)_B\prod h,
\qquad o_Bh=o_A
```

とrelation・domain・固定値の対応である。原始required Lawの解釈も保つ。Law導出を用いるなら、targetのrequired Lawと標準式からその導出を実際に与える。選択された存在witnessはデータとして運び、存在だけのLawに選択関数を付けない。

単項操作語では `τ(e)` は空語を含む有限語でよい。phaseがあれば頂点mapと各辺を送る有限pathを持ち、始点・終点・各domainを保つ。空pathへの翻訳がstutteringである。全語の翻訳は連結によって延長する。

係数familyでは、構文選択もC3.1の局所定数dataとして保持する。以下の式は各clopen片で同じ型の有限termに適用し、共通細分で合成して貼る。固定構文のfiberはこの構成にそのまま含まれる。

射 `(f,h,τ):A→B` と `(g,k,υ):B→D` の合成は、sort対応 `gf`、state map `kh`、各operationに対して `υ` を `τ` の全構文nodeへ代入したterm `υ_*τ` とする。term評価の帰納法により

```math
(kh)\omega_A=k(\tau\omega)_B\prod h
=(\upsilon_*\tau\omega)_D\prod(kh).
```

観測・domainも二つの保存式を合成して保存される。有限syntaxの代入は結合的で、恒等termへの代入は単位である。構文を標準等式で商にする場合も、導出の解釈が等しいためwell-defined。補助導出の選択を射の等号に含めない。規則が保持を指定する翻訳名・phase・補助選択は保持する。

時間順の添字では、`h₀₁:X₁→X₀`、`h₁₂:X₂→X₁` と、`τ₀₁:Words₁→Words₀`、`τ₁₂:Words₂→Words₁` に対して

```math
h_{02}=h_{01}\circ h_{12},\qquad
\tau_{02}=\tau_{01*}\circ\tau_{12}.
```

これは上の同じ合成を実際のstate mapの向きで書いたものである。

## 定理 B1 — 非可逆な変更を含むnerve

係数 `R` ごとに上の圏を `C_R` とする。`N_n(R)=Fun([n],C_R)^≃` と定義する。対象は `n` 個の実際の合成可能な射、射は各頂点の同型で全辺の正方形を可換にする族である。内部の辺は非可逆でもよい。

`N₀` は対象のcore、`N₁` は全矢印の同型比較groupoid。端点の忘却により

```math
N_n\simeq N_1\times^2_{N_0}\cdots\times^2_{N_0}N_1
```

を得る。

**証明。** 厳密に同じ中間対象を持つ列を、各つなぎの同型が恒等である右辺の対象へ送る。逆に、矢印 `A₀→A₁`、`B₁→B₂` と同型 `α:A₁≅B₁` があれば、後者を `A₁→B₂`、すなわち `gα` に置き換えて列を作る。順にこの操作を行えば全つなぎをstrictにできる。比較同型の正方形を同じ `α` で共役すればmapも運べる。二つの合成は恒等、または元のつなぎ `α` による自然同型となる。全Homについても、この正方形の式から互いに逆である。□

faceは端の忘却または隣接射の合成、degeneracyは恒等射の挿入である。simplicial identityは圏の結合・単位則から従う。2-fiber側の括弧の変更は同じ全頂点・辺・つなぎ同型のtupleへの同一視であり、pentagonもこのtupleで一致する。係数変更は実際のmapsを運ぶので全構成と可換。native比較も各辺のmapを保持するため合成と一致する。

時間順に `0→1→2` と表示しつつstate mapsを `X₂→X₁→X₀` とするなら、`C_R^op` のnerveを使う。両端へのmoduli mapの向きとstate mapの向きを混ぜない。

## 定理 B2 — 原始表示の同型と定義による補助演算

sort・operation・Lawの添字を可逆に改名し、その型付き式も同じ改名で運ぶと、modelと全Homを読む関手に逆がある。従って `C_R` と全 `N_n` が同値となる。

新しいoperation記号 `a` とrequired Law `a=τ` を加える場合、拡張は既存term `τ` の評価で一意に決まる。partial termの場合は、`a` のdomainも `τ` の構文から生成したdomainと同じに宣言する。値の等式だけを狭いdomain上で要求する拡張はここに含めない。元の全HomはA2のterm保存により `a` も保つので、忘却と拡張は対象・全Homで互いに逆である。逆にこの定義済み補助演算を消しても同じ圏を得る。全nerve・観測・後述のfiberとの比較も各dataの同じ読み戻しから得られる。存在するだけの新しい補助sortやoperationはこの一意拡張の仮定を満たさず、一般には同値にならない。
