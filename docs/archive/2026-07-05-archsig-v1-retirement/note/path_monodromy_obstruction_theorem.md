# AAT 解析接続ホロノミー定理

## Path-Monodromy Obstruction Theorem

AAT本文では、すでに Atom から architecture object・law・obstruction・signature・operation が立ち上がること、そして operation は Atom configuration の変換として扱えることが置かれています。さらに、零曲率・zero obstruction・required signature axes zero が exactness の下で一致し、path は signature trajectory を持ち、homotopy は selected observation / trajectory を保存する、という土台もあります。

---

## 1. 新しい観測量：Architecture Monodromy Index

AATの既存の `Sig(A)` は対象 `A` の多軸状態を読む。ここでさらに、**対象そのものではなく、対象へ到達する経路の解析接続**を読む。

二つの操作 `f, g` が、粗い観測では独立に見えるとする。

```text
A --f--> A_f
|        |
g        g
v        v
A_g --f--> A_fg
```

このとき二つの path がある。

```text
p = g ∘ f : A -> A_fg
q = f ∘ g : A -> A_fg
```

既存AATでは、独立ならこの square は可換であり、二つの path は homotopic に読める。逆に signature trajectory が違えば、その selected homotopy に関しては同値ではない。

ここで各 signature axis `x` について、path に沿って signature / witness / state transition を解析接続する写像を置く。

```text
Cont_x(p)
```

そして square の **monodromy defect** を定義する。

```text
mu_x(f,g;A)
  = d_x( Cont_x(g ∘ f), Cont_x(f ∘ g) )
```

`d_x` は axis ごとの距離でよい。

```text
boolean mismatch
count
edit distance
semantic distance
state transition distance
contract mismatch count
effect replay mismatch count
authorization mismatch count
```

そして全体量を次で置く。

```text
AMI_X(A)
  = sum_{claimed independent squares sigma}
    sum_{x in X} w_{sigma,x} * mu_x(sigma)
```

これを **Architecture Monodromy Index**, 略して **AMI** と呼ぶ。

---

## 2. 定理本体

**定理：AAT 解析接続ホロノミー定理**

`A` を architecture object、`U` を selected law universe、`X` を観測する signature axes の集合とする。`Ops` を feature extension、repair、migration、substitution、split、protect などの operation family とし、それらから生成される operation path complex を `K_O(A)` とする。

次を仮定する。

```text
1. 各 axis x in X の距離 d_x は zero-reflecting である。
   d_x(u,v)=0 iff selected observation 上で u=v

2. witness family は U に関して complete である。

3. signature axes X は selected law failure を exact に読む。

4. homotopy generator は selected continuation を保存する。

5. K_O(A) の covered loop / square は、選ばれた generator で生成される。
```

このとき、次が成り立つ。

```text
AMI_X(A) = 0
```

であることは、covered operation complex 上で次と同値である。

```text
すべての claimed independent square は fillable である
すべての covered path pair は selected homotopy の下で同値である
解析接続 Cont_x は path-independent である
covered axes X 上に mixed-axis obstruction は存在しない
```

逆に、

```text
AMI_X(A) > 0
```

なら、ある operation square `sigma` と axis `x` が存在して、

```text
mu_x(sigma) > 0
```

となる。したがって、その square は selected observation に関して fill できず、対応する law failure の obstruction circuit が存在する。

つまり、

```text
nonzero monodromy
  -> non-fillability
  -> obstruction
  -> non-flatness on selected covered axes
```

である。

---

## 3. さらに強い帰結：局所零曲率でも大域 obstruction は残る

この定理の意外性はここです。

通常の静的解析やレビューは、しばしば次を見る。

```text
final dependency graph
cycle count
layering
endpoint object
local contract check
single operation diff
```

しかし AAT の path calculus では、同じ endpoint に到達する二つの path が異なる signature trajectory を持ちうる。

したがって、次が起こる。

```text
kappa_local(A_i) = 0 for every local step
static_projection(g ∘ f)(A) = static_projection(f ∘ g)(A)
but
AMI_X(A) > 0
```

この場合、局所チェックは全部通っている。最終 dependency graph も同じに見える。それでも、operation を一周させたときに runtime / semantic / state / effect axis が戻ってこない。

これを AAT では次のように読む。

```text
local zero curvature
  does not imply
global flatness

local zero curvature + zero monodromy
  implies
covered global flatness
```

これは既存の Architecture Zero Curvature Theorem の path 版です。既存定理は「対象 `A` の zero curvature」を lawfulness と結ぶ。一方この新定理は、「operation space 上の解析接続の holonomy zero」を path-independent lawfulness と結ぶ。零曲率 theorem が点の幾何なら、これは **経路空間の幾何** です。

---

## 4. 証明スケッチ

### Step 1：非ゼロ AMI は非ゼロ局所 defect を含む

`AMI_X(A)` は非負重み付き和として定義される。

```text
AMI_X(A)
  = sum w * mu
```

すべての重みが正で値域が nonnegative なら、全体が zero であることから各項の zero が従う、という形の zero-reflection はAAT本文にも置かれている。

したがって、

```text
AMI_X(A) > 0
```

なら、ある `sigma, x` について、

```text
mu_x(sigma) > 0
```

である。

### Step 2：`mu_x > 0` は path homotopy を壊す

`mu_x(sigma)` は二つの path の解析接続結果の距離である。

```text
mu_x(f,g;A)
  = d_x( Cont_x(g ∘ f), Cont_x(f ∘ g) )
```

`d_x` が zero-reflecting なので、

```text
mu_x > 0
```

なら、

```text
Cont_x(g ∘ f) != Cont_x(f ∘ g)
```

である。

AAT本文では、selected signature trajectory が homotopy generator によって保存されるなら、homotopic path は同じ trajectory を持つ。反対向きに、trajectory が違えばその selected homotopy では同値でない。

したがって、

```text
mu_x > 0
  -> not (g ∘ f ~ f ∘ g)
```

である。

### Step 3：非同値 square は filler を持たない

AAT本文では、law failure が diagram の非可換性として表されるなら、その obstruction は non-fillability witness として読める。

よって、

```text
Cont_x(g ∘ f) != Cont_x(f ∘ g)
```

は、

```text
no filler for the square
```

を与える。

### Step 4：non-fillability は obstruction である

AATの obstruction valuation / curvature / signature axes が exact であるなら、

```text
law failure
  <-> obstruction
  <-> nonzero curvature
  <-> required signature axis nonzero
```

という対応が使える。

したがって、

```text
AMI_X(A) > 0
  -> selected obstruction exists
```

である。

### Step 5：局所零曲率でも AMI は残りうる

AAT本文では、analytic representation は selected axes の読みであり、解析値だけから architecture object 全体は還元できない。また、axis を忘れる projection は coarse reading を保存できても、forgotten axes や mixed-axis support がある場合、coarse zero から structural zero は一般には反射しない。

したがって、

```text
static_projection = 0
local_static_curvature = 0
```

でも、

```text
semantic / runtime / state / effect monodromy != 0
```

はありうる。

これが、この定理が静的解析との差分を作る点です。

---

## 5. なぜこれは「普通の静的解析」では出にくいか

静的解析は主に `G(A)` や `M(A)`、つまり dependency graph、reachability、cycle、layering、matrix nilpotence などを見る。AAT本文でも graph / matrix representation は dependency や walk count を読むものとして位置づけられている。

しかし AMI が見るのは、対象 `A` ではなく、

```text
operation path pair
operation square
path-dependent signature trajectory
state transition composition
effect replay composition
semantic continuation
```

である。

つまり比較対象はこれです。

```text
static analyzer:
  inspect final A

AAT monodromy analyzer:
  compare g ∘ f with f ∘ g
  compare their continued witnesses
  measure the commutator on each axis
```

これはレビューの「この変更は大丈夫そうか」という単発判断ではなく、**変更の交換可能性そのものを測る**。レビューが見ている object-level difference ではなく、AAT は path-level noncommutativity を見る。

---

## 6. 具体例：Coupon / Tax / Rounding

AAT本文の coupon feature 例は、この定理の典型例です。coupon extension は price calculation、discount policy、rounding、tax、payment、event emission に Atom を追加し、static dependency が増えなくても rounding law や payment amount law が壊れるなら semantic obstruction が生じる、とされています。

二つの操作を置く。

```text
f = add coupon discount
g = add tax / rounding rule
```

粗い静的観測では、どちらの順に入れても最終的な component set や dependency graph は同じに見えるかもしれない。

しかし計算 path は違う。

```text
p = round(tax(discount(subtotal)))
q = round(discount(tax(subtotal)))
```

このとき、

```text
mu_amount(f,g;Checkout)
  = | p(subtotal) - q(subtotal) |
```

と置ける。

さらに payment / receipt まで含めるなら、

```text
mu_payment
  = count(PaymentAmount != FinalAmount)
    + count(ReceiptAmount != FinalAmount)
```

したがって、

```text
AMI_price > 0
```

なら、

```text
coupon-tax square is not fillable
```

であり、semantic / state / effect axis 上の obstruction がある。AAT本文でも、discount と tax が可換である law が成り立つ場合に限り二つの path は同じ calculation として読め、可換でないなら homotopy は存在しない、とされています。

---

## 7. ツールで測る方法

実装可能な測定仕様はかなり明確です。

### 7.1 入力

```text
A          : current architecture object
Ops        : candidate operations
X          : selected axes
U          : law universe
R(A)       : analytic representation
```

AAT本文では analytic representation は次の族です。

```text
R(A) = (G(A), M(A), Sig(A), kappa(A), State(A))
```

したがって AMI は、この `Sig`, `kappa`, `State` を path 上に拡張して測ります。

### 7.2 候補 square の列挙

ペア `f, g` を列挙する。

```text
same support に触る operation
同じ state を読む/書く operation
同じ effect を発生させる operation
同じ contract / semantic Atom に触る operation
同じ authority / trust boundary を横断する operation
```

feature extension では、AAT本文がすでに core embedding、feature view、lifting data、runtime / semantic coverage に相対化して split を読む構造を持っているため、split claim の検査点として AMI を差し込める。

### 7.3 二つの順序を実行またはシミュレート

```text
A_p = g(f(A))
A_q = f(g(A))
```

それぞれについて、

```text
Sig(A_p), Sig(A_q)
kappa(A_p), kappa(A_q)
StateTransition(p), StateTransition(q)
EffectTrace(p), EffectTrace(q)
SemanticWitness(p), SemanticWitness(q)
```

を取る。

### 7.4 axis ごとの defect

```text
mu_static       = distance(G(A_p), G(A_q))
mu_contract     = count(contract witness mismatch)
mu_semantic     = count(semantic witness mismatch)
mu_state        = count or metric of t_p(s) != t_q(s)
mu_effect       = replay / idempotency / compensation mismatch count
mu_authority    = permission / access path mismatch count
mu_projection   = projection soundness mismatch count
```

State / effect に関しては、AAT本文で effect または operation が state transition を誘導し、transition law は可換性・冪等性・保存性・補償性として読まれる、と定義されています。

### 7.5 出力

ツールは次を返せばよい。

```text
AMI_X(A)
top nonzero squares
offending operation pair
axis x
witness atoms
p = g ∘ f の trace
q = f ∘ g の trace
mu_x value
suggested filler / lifting / boundary evidence
```

これにより、単なる「循環があります」「依存方向が逆です」ではなく、

```text
この二つの変更は単独では安全だが、順序を交換すると semantic amount が変わる
この repair は cycle を減らすが、contract axis に monodromy を生む
この split は static には成功するが、runtime handler / effect ordering の filler がない
```

という診断ができます。

---

## 8. AAT本文に追加するなら、この形がよい

そのまま第II部の Homotopy と Diagram Filling の後、または第III部の Analytic Representation の後に入れるなら、次の節名がよいです。

```text
## Architecture Analytic Continuation and Monodromy
```

追加する定義・定理はこれです。

```text
定義: Operation Complex
定義: Analytic Continuation along Architecture Path
定義: Square Monodromy
定義: Architecture Monodromy Index
定理: Path-Monodromy Obstruction Theorem
系: Local Flatness Does Not Imply Global Path-Flatness
系: Zero Local Curvature + Zero Monodromy Implies Covered Global Flatness
系: Static-Zero / Semantic-Monodromy Separation
```

特に最後の系が、静的解析との差分になります。

```text
StaticZero(A,p,q) and AMI_semantic(p,q) > 0
------------------------------------------------
There exists a semantic obstruction invisible to static projection.
```

これはAAT本文にある「static flat でも semantic obstruction が残る」「三層 flatness は一般に相互含意しない」という既存主張を、path と解析接続の言葉で強化したものです。

---

## 9. 一文でいうと

この定理の核心は、次です。

```text
アーキテクチャの危険は、最終状態の形だけでなく、
「そこへ至る変更経路を一周させたとき、意味・状態・effect が元に戻るか」
に現れる。
```

その戻り損ねが

```text
AMI_X(A) > 0
```

であり、それは selected exactness の下で obstruction の存在を証明する。

これなら、AATの既存要素である Atom、signature、curvature、operation、path、homotopy、diagram filling、analytic representation を全部使い、しかもツールで定量測定できます。Static graph が acyclic、final object が同じ、レビュー上は自然、という状況でも、operation square の monodromy が非ゼロなら AAT は「ここに obstruction がある」と言えます。
