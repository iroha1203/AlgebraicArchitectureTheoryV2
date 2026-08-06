# G-104 条件 C ハント報告

> **これは off-loop 探索 artifact であり、GOAL 完了の証拠ではない。**

## 1. 判定

- Issue: #3912
- 判定: **停止条件 B（自由係数近似における構造的否定）**
- G-104 proof state: 変更しない
- 最終候補 C: なし
- law 実現可能性: 未確認

自由な有限次元係数を無制限に許す探索モデルでは、incidence data を固定したまま
係数座標を fine 側で複製できる。非零 `H¹` を持つ正例の fine 複体を2コピーにし、
comparison map を対角写像にすると、incidence-level の任意の条件は真偽が変わらないが、
comparison map は非全射になる。したがって、自由係数モデルの全域を incidence-only
の条件 C で制御することはできない。

この結果は「law 由来係数でも不変性が偽」を意味しない。複製座標や cell support hole が
実際の law descent から生成できるかは未確認であり、Issue の指示どおり caveat として残す。

## 2. 探索対象と exact 判定

有限 nerve `N` を chart 集合 `V`、edge 集合 `E`、face 集合 `F` とし、各 edge に
left / right endpoint、各 face に boundary triple `(e₀,e₁,e₂)` を持たせる。有理数上で

```text
d₀(x)(e) = x(right(e)) - x(left(e))
d₁(y)(f) = y(e₀) - y(e₁) + y(e₂)
```

とする。`d₁ d₀ = 0` を満たさないデータは列挙時に棄却する。nerve 射は chart map、
`Option` 型の edge / face map、endpoint / boundary 可換性を持つ。`none` の edge / face
では pullback を零とし、mapped cell では対応する coarse cochain を pullback する。

reading comparison には `FaceLiftObstruction` で review 済みの proper adequate pair を固定する。
Source は `Fin 4`、fine Target は `Fin 4`、coarse Target は `Fin 3` であり、canonical factor は
`π = (0, 0, 1, 2)` で非単射である。law evaluation も `(0, 0, 1, 2)` で非定数であり、両 reading
への descent と `π` の可換性を個別に検査する。この `π` は、fine chart から coarse chart への
nerve map `φ` とは別データである。

`H¹ = ker d₁ / im d₀`、comparison rank、単射性、全射性は、浮動小数点を使わず
`fractions.Fraction` 上の Gaussian elimination で計算する。C0 は coefficient coordinate support
ではなく、reading Target 上の chart support と `π` から判定する。

cellwise 係数モデルでは、各 cell が有限 coordinate support を持ち、その要素数を
cell ごとの係数次元とする。edge support は endpoint supports の共通部分、face support は
boundary-edge supports の共通部分に含める。restriction と comparison の係数写像は、
座標により強制される零写像または恒等写像である。

## 3. Calibration gate

正本の Lean fixture と同じ nerve、nerve 射、3つの law-value coordinate を再構成した。

| fixture | coarse `dim H¹` | fine `dim H¹` | map rank | 判定 | 一致する Lean 結論 |
| --- | ---: | ---: | ---: | --- | --- |
| `FaceLiftObstruction` | 0 | 3 | 0 | 非全射 | `comparisonH1Map_not_surjective` |
| `EdgeFiberObstruction` | 0 | 3 | 0 | 非全射 | `comparisonH1Map_not_surjective` |
| `LoopLiftObstruction` | 6 | 3 | 3 | 非単射 | `comparisonH1Map_not_injective` |

3件すべて一致したため、以後の探索へ進んだ。

## 4. ラウンド記録

### Round 1: C0–C5 + self-loop endpoint reflection

暫定候補 `C*` はカードへ書ける incidence / support 条項として次を要求する。

1. C0: coarse chart support は fine chart-fiber supports の像の合併に一致する。
2. C1: 各 chart fiber graph は非空かつ連結。
3. C2: 各 coarse edge は fine lift を持つ。
4. C3: chart fiber 内の有理1-cycle は fiber 内 face boundaries で張られる。
5. C4: 各 coarse face は boundary-compatible な fine face lift を持つ。
6. C5: 各 coarse edge の nondegenerate fine lift は一意。
7. R: coarse edge が self-loop なら、その一意な fine lift も同一 fine chart を両 endpoint に持つ。

#### 全数探索 normal form と bound

- coarse chart `≤ 3`、edge `≤ 4`、face `≤ 1`
- fine chart `≤ 4`
- coarse graph は連結。parallel edge と self-loop を許す。
- edge orientation の同値な符号選択は、chart index の小さい側から大きい側への向きに正規化。
- chart fiber size の全正分割を列挙。
- fiber incidence は star tree、または star に1 edge と filling face を加えた非空虚 C3 template。
- 各 coarse edge の一意 lift について可能な endpoint assignment をすべて列挙。
- self-loop lift は R に従い同一 fine chart を endpoint とする。
- 各 coarse face には、選択された3 edge lifts を boundary とする fine face を置き、
  `d₁d₀ = 0` を満たさない assignment を棄却。
- 全 cell の自由係数 rank は1または2。座標 pullback は恒等で、基底の符号・順列変更は同型として除く。

生成した coarse nerves は1,069、refinements は112,562。`C*` を満たす3,043 refinements を
rank 1 / 2 で判定した6,086件に反例はなかった。

#### 非退化正例

filled triangle にもう1本の unfilled parallel edge を持つ coarse nerve を使い、coarse chart 0 を
fine chart 0 / 1 に分割する。両者を `edgeMap = none` の fiber edge で結び、4本の coarse edge と
1つの coarse face は一意に lift する。上記の adequate reading pair と full Target support をこの
nerve comparison に接続し、3つの係数座標は非定数 law descent の実値 `0, 1, 2` から生成する。

- canonical reading factor `π : Fin 4 → Fin 3` は `(0, 0, 1, 2)` で非単射
- nerve chart map `φ` も非単射（`π` とは別に検査）
- `π` と full Target support は両立し、C0 が成立
- coarse / fine とも `dim H¹ = 3`（law descent の3実値座標で計算）
- comparison rank 3、同型
- 2元 chart fiber あり
- coarse / fine face あり
- fine fiber edge あり

したがって、恒等比較、零 `H¹`、単一 chart、face-free、fiber-edge-free の正例ではない。

#### 定数座標層での手証明スケッチ

fine edge を coarse edge の一意 lift と fiber edge に分ける。C1 により各 vertex fiber の
`H⁰` は1次元、C3 により fiber 内の degree-one kernel は internal face boundary で消える。
C2 / C5 と R により、fiber quotient 後の nondegenerate edge と endpoint incidence は coarse edge
と一致する。C4 により coarse face relation は fine 側へ lift し、複数 face lift があっても C5 の
下では同じ edge-boundary relation を与える。よって fiber subcomplex を潰した relative complex は
coarse complex と degree 0–2 で同型になり、long exact sequence の degree 1 部分から canonical
pullback が `H¹` 同型になる、という経路である。

これは bounded 計算を説明する手証明スケッチであり、一般定理の証明ではない。特に係数が cell ごとに
変わる場合、C1 / C3 の incidence fiber と実際の coefficient-coordinate fiber が一致するとは限らない。

### Round 2: cellwise 自由係数

Round 1 の非退化 incidence を、coarse 側に2本、fine 側に少なくとも1本の非零 `H¹` が残るよう
parallel edge を1本増やして固定した。reading pair、canonical `π`、full Target support は正例・
support-hole・座標複製の3データで完全に共通である。この同じ incidence 上で、coarse 全 cell の
自由係数次元を1、fine chart 次元を1とし、fine edge / face の次元 `0/1` と、対応する零 / 恒等
restriction を全数列挙した。

- coefficient systems: 72
- 同型: 5
- 非同型: 67
- 両側 `H¹` 非零の非同型: 31

代表となる support-hole 反例では、incidence 上の fiber edge は残したまま、その edge の係数次元だけを
0にする。他の fine edge / face は次元1である。

| data | coarse `dim H¹` | fine `dim H¹` | map rank | 判定 |
| --- | ---: | ---: | ---: | --- |
| 全 cell 次元1 | 2 | 2 | 2 | 同型 |
| 同一 incidence、fiber edge 次元0 | 2 | 1 | 1 | 非単射 |
| 同一 incidence、fine 座標を2コピー | 2 | 4 | 2 | 非全射 |

3データは同じ非単射 canonical `π`、同じ Target support、同じ nerve map `φ` を持つため、C0–C5 と
R の真偽が完全に同じである。2元 chart fiber、face、fiber edge、両側非零 `H¹` も保つ。

### Round 3: (b) / (c) の incidence 改訂可能性

support-hole の機構だけなら coefficient-coordinate ごとの comma fiber connectivity を足す改訂が考えられる。
しかし、fine 側の座標コピーを増やす構成は nerve、nerve 射、endpoint / face incidence を一切変えない。
任意の incidence-only 候補がある非退化正例を受理すれば、その正例の fine coefficient complex を2コピーし、
comparison を対角写像にした非同型も受理する。comma 型 (b) や face-mediated coherence (c) をどれだけ
incidence 上で強めても、この2データを区別できない。

区別には「law descent が生成する座標を重複なく固定する」「cell support と生成座標の provenance を
反映する」等の係数生成 contract が必要である。これは incidence 条件 C の条項追加ではなく、target theorem の
ambient law-derived coefficient premise を具体化する仕事である。

同一 blocker が候補 (a)、(b)、(c) に共通するだけでなく、自由係数モデル内では任意の incidence-only 条件に
一般化できるため、停滞 C ではなく構造的否定 B と判定した。

## 5. 暫定候補 `C*` の条項独立性

停止 B のため最終候補は採用しない。ただし Round 1 の `C*` について、各条項だけを外した反例を
同じ exact engine で確認した。

| 外す条項 | 反例機構 | coarse / fine `dim H¹` | map failure |
| --- | --- | --- | --- |
| C0 | coarse Target support の元 `2` が fine supports の `π`-像から欠落 | 2 / 1 | 非単射 |
| C1 | parallel lifts が chart fiber の別成分へ着地 | 1 / 0 | 非単射 |
| C2 | coarse parallel edge の lift 欠落 | 1 / 0 | 非単射 |
| C3 | face-free fiber の2本の loop edge | 0 / 2 | 非全射 |
| C4 | `FaceLiftObstruction` | 0 / 3 | 非全射 |
| C5 | `EdgeFiberObstruction` | 0 / 3 | 非全射 |
| R | `LoopLiftObstruction` | 6 / 3 | 非単射 |

C0 の反例は full coarse Target support `{0,1,2}` に対して各 fine chart support を `{0,2}` とし、
`π({0,2}) = {0,1}` なので C0 だけが偽になることを actual Target 上で検査する。comparison failure は
coarse rank 2 / fine rank 1 の自由係数 fixture で示しており、この係数系の law 実現可能性は未確認である。
他の新規小反例も incidence / free-coordinate 証拠であり、Lean theorem や G-104 proof state を更新しない。

## 6. Coverage limit と次の判断点

- Round 1 は記載した normal form の同型類だけを覆い、任意個の face、任意の fiber 2-complex、
  arbitrary linear coefficient map は覆わない。
- Round 2 は1座標、cell dimension `0/1`、零 / 恒等 restriction の全数探索である。
- fine 座標複製は自由係数近似では正当だが、G-103 の canonical law descent から生成できることを確認していない。
- support-hole が actual G-104 coefficient generator で許されるかも未確認である。
- したがって、次に人間が G-104 を改訂する場合は、条件 C を先に増やすのではなく、law-derived coefficient
  generator が cell support と座標 multiplicity をどう固定するかを一次仕様として確定する必要がある。

本 artifact は GOAL カード、`research/reports/`、Issue #3902 の proof state、ResearchLean を変更しない。
