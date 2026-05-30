## 提案する新定理：AAT 曲率スペクトル定理

**AAT Curvature–Transfer Spectrum Theorem / ACTS**

狙いは、普通の依存グラフのスペクトルではなく、**AAT の Atom 軸ごとの obstruction が、コードベース全体でどこに局在し、どの軸へ転送され、どこで循環・増幅するか**を測ることです。

AAT では Atom が `component / relation / capability / state / effect / authority / contract / semantic / runtime_interaction` などを含む型付き事実として定義されており、各 Atom は `axis` を持ちます。つまり、最初から「静的依存だけではない多軸の構造」を扱える設計になっています。 また、AAT では static flatness から runtime flatness や semantic flatness は一般には従わないため、静的解析だけでは見えない品質劣化を測る余地があります。

---

# 1. 直感

普通の静的解析はだいたい次を見ます。

```text
module A imports B
class X depends on Y
package cycle exists
layer violation exists
```

これは AAT 的には主に `relation / dependency` 軸だけを見ています。

一方、私たちが作りたいツールは、次のような「コード全体に潜むアーキテクチャ品質」を見たい。

```text
依存グラフは acyclic だが、意味的には order-sensitive
interface に依存しているが、semantic contract が壊れている
retry / timeout はあるが、effect が冪等でない
state 更新と event emission の順序が一貫しない
authority は通っているが、trust boundary が曖昧
feature 同士は静的には独立だが、計算順序で結果が変わる
```

そこで、依存グラフの隣接行列だけでなく、AAT の law / obstruction / signature / curvature を使って、**多軸の曲率付きスペクトル**を作ります。

---

# 2. 定義：曲率付き Law Complex

コードベース全体を Atomize して、architecture object を作る。

```text
F = Atomize_V(Repo)
F => A
```

選ぶものは次です。

```text
U : law universe
X : selected axes
W : measured witness family
```

ここで `X` は例えば次。

```text
X = {
  dependency,
  projection,
  substitution,
  state,
  effect,
  authority,
  runtime,
  semantic,
  monodromy
}
```

`W` は、コード全体から構成される witness / diagram / square の集合です。

```text
σ ∈ W
```

各 witness `σ` と axis `x` について、局所曲率を置きます。

```text
κ_{σ,x}(A)
  =
distance(Obs_x(lhs(σ)), Obs_x(rhs(σ)))
```

これは既存 AAT の local curvature の考え方そのものです。AAT では diagram `D` の local curvature を `distance(Obs(lhs(D)), Obs(rhs(D)))` と読め、global curvature は重み付き和として扱えます。

---

# 3. 曲率サポート・ラプラシアン

各 witness がどの component / operation / state / effect / contract / semantic Atom に関わるかを incidence vector として表します。

```text
b_{σ,x} ∈ R^{Support(A) × X}
```

そして、次の正半定値行列を作る。

```text
L^κ_{U,X}(A)
  =
Σ_{σ ∈ W}
Σ_{x ∈ X}
  w_{σ,x} κ_{σ,x}(A) b_{σ,x} b_{σ,x}ᵀ
```

これを **AAT curvature support Laplacian** と呼びます。

このスペクトルを、

```text
Spec^κ_{U,X}(A) = spectrum(L^κ_{U,X}(A))
```

と定義します。

直感的には、これは「どこで obstruction が発生しているか」だけでなく、**その obstruction がどれだけ広い support にまたがっているか、どの軸を巻き込んでいるか、どの塊として現れているか**を測ります。

---

# 4. 新定理：AAT 曲率スペクトル定理

## 定理 1：Curvature Spectrum Zero-Reflection

有限 architecture object `A`、law universe `U`、selected axes `X`、measured witness family `W` を取る。

次を仮定する。

```text
1. finite coverage:
   W は selected law universe U の required witness を有限個として覆う

2. positive weight:
   required witness には w_{σ,x} > 0 が与えられる

3. zero-reflecting distance:
   κ_{σ,x}(A) = 0 iff selected local law が σ,x 上で満たされる

4. nonempty support:
   required witness の incidence vector b_{σ,x} は 0 ではない

5. axis exactness:
   selected signature axis が対応する law failure を exact に読む
```

このとき、

```text
Spec^κ_{U,X}(A) = {0}
```

は次と同値である。

```text
forall required σ,x,
  κ_{σ,x}(A) = 0
```

さらに `W` が witness-complete で、`X` が required signature axes を exact に読むなら、

```text
Spec^κ_{U,X}(A) = {0}
  iff RequiredSignatureAxesZero_X(A)
  iff Flat_U(A)
  iff Lawful_U(A)
```

つまり、**曲率スペクトルが完全に zero であることは、選ばれた law universe に対する architecture quality が flat であることと一致する**。

これは既存の AAT zero curvature / signature flatness と整合します。AAT では、law failure を exact に読む curvature valuation があるとき、`Lawful_U(A)`, `NoRequiredObstruction`, `RequiredSignatureAxesZero`, `ZeroCurvature_U(A)` が一致します。 また、解析表現から構造へ戻るには `ZeroReflecting / ObstructionReflecting` の仮定、coverage、witness completeness、axis exactness が必要であることも既存の整理と一致します。

---

# 5. 証明スケッチ

`L^κ` は次の和です。

```text
L^κ
  =
Σ w_{σ,x} κ_{σ,x} b_{σ,x} b_{σ,x}ᵀ
```

各項は正半定値です。

したがって、

```text
L^κ = 0
```

なら、trace も 0 です。

```text
trace(L^κ)
  =
Σ w_{σ,x} κ_{σ,x} ||b_{σ,x}||²
```

すべての項は非負で、required witness では

```text
w_{σ,x} > 0
||b_{σ,x}||² > 0
```

なので、

```text
trace(L^κ) = 0
```

から

```text
κ_{σ,x} = 0
```

が全 required witness について従います。

逆に、全 `κ_{σ,x}=0` なら明らかに `L^κ=0` で、したがってスペクトルも全て 0 です。

最後に、`κ` が law failure を exact に読み、witness family が complete なら、AAT の zero curvature theorem / signature flatness によって `Flat_U(A)` と一致します。

---

# 6. さらに重要：Transfer Spectrum

上の `L^κ` は「どこに obstruction があるか」を測ります。

ただし、アーキテクチャ品質計測ツールとして本当に欲しいのは、もう一段進んで、**obstruction がどの軸からどの軸へ転送されるか**です。

そこで、状態空間を次にします。

```text
State = Support(A) × Axis
```

例えば、

```text
(OrderService, semantic)
(PaymentService, effect)
(UserRepository, authority)
(CouponService, runtime)
```

この上に、非負行列 `T^κ` を作る。

```text
T^κ_{(s,x),(t,y)}(A)
  =
Σ measured transfer σ : (s,x) -> (t,y)
  w_σ κ_σ(A)
```

これを **AAT obstruction transfer operator** と呼ぶ。

---

# 7. 定理 2：Recurrent Obstruction Spectrum

`T^κ` を有限非負行列とする。

このとき、

```text
ρ(T^κ) > 0
```

であることと、次は同値である。

```text
Support(A) × Axis 上に、
正の defect を持つ closed walk が存在する
```

つまり、

```text
(s0,x0) -> (s1,x1) -> ... -> (sn,xn) = (s0,x0)
```

で、経路上の transfer defect が正である。

これを **recurrent architecture obstruction** と呼ぶ。

---

# 8. これが普通の静的解析と違うところ

通常の dependency spectrum は、せいぜいこれを見ます。

```text
component -> component
```

しかし `T^κ` はこれを見ます。

```text
(component, dependency)
  -> (operation, semantic)
  -> (effect, runtime)
  -> (resource, authority)
  -> (component, dependency)
```

つまり、静的依存グラフとしては循環していなくても、AAT transfer spectrum では循環することがある。

例えば、

```text
OrderService --static--> PaymentService
PaymentService --semantic--> PaymentAccepted
PaymentAccepted --effect--> CaptureMoney
CaptureMoney --runtime--> RetryPolicy
RetryPolicy --semantic--> OrderConfirmed
```

のような循環です。

これは `import cycle` ではないので普通の静的解析では出にくい。しかし、semantic / effect / runtime / authority を Atom として保持している AAT なら検出対象にできます。AAT では semantic Atom が static flatness と semantic flatness を分け、runtime interaction Atom も relation Atom や effect Atom に潰さず独立に保持されます。

---

# 9. 定理 3：Spectral Review Focus Theorem

`L^κ` の最大固有値に対応する固有ベクトルを `v_max` とする。

```text
L^κ v_max = λ_max v_max
```

`λ_max > 0` なら、`v_max` の大きな成分は、次のいずれかを含む。

```text
1. nonzero local curvature witness の support
2. 複数 witness を接続する mixed-axis support
3. obstruction transfer の強連結成分
4. coverage gap を含む boundary support
```

したがって、ツールは単に

```text
violation count = 17
```

と出すのではなく、

```text
この codebase の最大 obstruction mode は:
  CouponService / PricingPolicy / TaxCalculation / PaymentAmount
  axes:
    semantic, state, effect
  witnesses:
    discount-tax-rounding non-commutation
    PaymentAmount != FinalAmount
    ReceiptAmount != FinalAmount
```

のように出せます。

これは PR レビュー向けではなく、**コード全体の architecture health scan** に向いています。

---

# 10. AMI との関係

既存の AAT には Architecture Monodromy Index, AMI があります。

```text
AMI_X(A)
  =
Σ_{σ in measured squares}
Σ_{x in selected axes}
  w_{σ,x} * μ_x(σ)
```

AMI は単一の quality score ではなく、top contributor を選ぶための aggregate reading とされています。さらに、`μ_x(σ)>0` なら selected continuation が異なり、selected homotopy refutation や non-fillability witness につながる、という bounded soundness が整理されています。

今回の提案は、AMI をこう拡張します。

```text
AMI:
  scalar aggregate

ACTS:
  spectral aggregate
```

つまり、

```text
AMI_X(A)
  = total amount of measured monodromy

Spec^κ_{U,X}(A)
  = shape, locality, coupling, recurrence of measured monodromy
```

です。

AMI が「総量」を出すなら、ACTS は「モード」を出す。

---

# 11. ツール設計


出力は単一スコアではなく、次の report にする。

```text
ArchitectureSpectrumReport
  = selected law universe
  + selected axes
  + coverage boundary
  + Spec(L^κ)
  + ρ(T^κ)
  + top eigenmodes
  + top witness clusters
  + missing evidence
  + non-conclusions
```

AAT では aggregate は signature 全体の代替ではなく、異なる obstruction は異なる axis に残る、と整理されています。 したがって、ツールも「総合点 82 点」ではなく、次のような多軸診断にすべきです。

```text
static spectrum:
  低い。依存循環は少ない。

semantic spectrum:
  高い。価格計算・税・丸め・支払い金額に集中。

runtime/effect transfer spectrum:
  中程度。retry と external effect の周辺に recurrent mode。

authority spectrum:
  局所的に高い。管理者操作と hidden resource access に集中。

coverage:
  semantic contract evidence が 62%。
  runtime observation evidence が 41%。
  したがって zero conclusion は出さない。
```

---

# 12. 実装の最小版

最初から完全な sheaf / Hodge Laplacian にしなくても、MVP は作れます。

## Step 1: Atom extraction

```text
component
relation/import/call/read/write
state
effect
contract
semantic
runtime_interaction
authority/trust
```

AAT では実コード断片から、宣言、参照、呼び出し、状態更新、外部作用、型注釈、意味注釈を Atom family として抽出する想定がすでにあります。

## Step 2: witness generation

まずはこの witness だけでよい。

```text
dependency cycle
layer violation
state-before-effect ordering
effect idempotency missing
retry-without-idempotency
contract substitution mismatch
semantic calculation non-commutation
authority-required-but-missing
runtime call without timeout / breaker
event emitted but handler missing
```

## Step 3: local curvature

```text
κ = 0 or 1
```

から始める。

後で距離を richer にする。

```text
boolean mismatch
count
edit distance
semantic distance
policy distance
contract refinement distance
state transition distance
```

## Step 4: curvature support Laplacian

```text
L^κ
  =
Σ wκ bbᵀ
```

## Step 5: transfer operator

```text
T^κ_{(support,axis),(support,axis)}
```

## Step 6: report

```text
largest eigenmode
top contributing witness
top affected axis
coverage gap
recommended review focus
```

---

# 13. この定理で測れる「普通は見えない品質」

特に強いのは次です。

## 1. 静的には acyclic だが semantic に非可換

```text
round(tax(discount(subtotal)))
round(discount(tax(subtotal)))
```

この差は dependency graph では見えません。しかし selected semantic axis では continuation が戻らないので、curvature / monodromy として測れます。AAT の coupon / tax / rounding 例でも、final dependency graph が同じでも semantic continuation が同じ位置へ戻らないケースが説明されています。

## 2. interface 依存だが contract が弱い

DIP 的には正しく見えるが、

```text
contract(Base) not refined by contract(Impl)
```

なら substitution obstruction です。

## 3. retry はあるが effect が冪等でない

静的には resilience 実装があるように見える。しかし runtime/effect 軸では obstruction です。

## 4. state 更新と event emission の順序が破れる

```text
emit UserCreated
before persist User
```

これは call graph ではなく state/effect law の問題です。

## 5. 権限は通っているが trust boundary が曖昧

`can call` と `authorized to effect` は別 Atom なので、authority spectrum に出せます。

---

# 14. 重要な注意：スペクトルは「真理」ではなく reading

この定理は、スペクトル値だけで architecture object の全構造を復元できるとは主張しません。

AAT では解析表現は selected axes の読みであり、同じ解析値を持つ二つの architecture object が同一とは限らない、という non-reduction が明示されています。 また、projection / matrix / spectral / aggregate reading を安全に使うには、ZeroReflecting と ObstructionReflecting の仮定を明示する必要があります。

したがって、ツールは必ずこう出すべきです。

```text
This report claims:
  measured selected-axis obstruction modes

This report does not claim:
  architecture is globally correct
  unmeasured axes are flat
  missing evidence means absence of defect
```

これは AAT 的にかなり重要です。

---

# 15. まとめ

提案する新定理はこれです。

```text
AAT Curvature–Transfer Spectrum Theorem

コードベース全体から Atom family を抽出し、
selected law universe と selected axes に対する witness family を作り、
各 witness の local curvature を重み付き incidence operator に載せる。

その curvature support Laplacian の zero spectrum は、
coverage / exactness / zero-reflection の下で、
selected law universe に対する flatness と同値である。

さらに obstruction transfer operator の spectral radius が正なら、
support × axis 上に recurrent obstruction が存在する。
これは dependency graph だけでは見えない、
semantic / runtime / effect / authority をまたぐ architecture quality degradation を示す。
```

この定理を使うと、AAT ベースのツールは「PR 差分の指摘」ではなく、**コード全体の architecture quality spectrum を測る検査器**として設計できます。単一スコアではなく、`top eigenmodes + witness + axis + coverage gap` を出すのが一番 AAT らしいです。
