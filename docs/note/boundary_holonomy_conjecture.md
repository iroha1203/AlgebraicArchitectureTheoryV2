# 境界ホロノミー予想

**Boundary Holonomy Conjecture for Software Architecture Extension**

AAT では feature extension は `ext_f : A -> B` と書かれ、Atom level では既存 Atom family `F_A` に feature 側の Atom family `F_f` を加えて `F_B = F_A union F_f` と読む、という形になっています。また、split extension は「元 core を壊さず、追加 feature を独立した subconfiguration として読める」拡張であり、さらに interaction law が満たされるなら `Lawful_U(A) -> Lawful_U(B)` が成り立つ、という保存命題が置かれています。

その上で、次の予想を立てます。

---

## 予想：拡張の obstruction は境界に局在化する

`A` を既存 architecture object、`ext_f : A -> B` を feature extension とする。
`U` を selected law universe、`S` を required signature axes、`κ_U` を curvature valuation とする。

feature extension に対して、core と feature の接触部分を

```text
∂f = Boundary(A, f)
```

と書く。これは、core 側 Atom と feature 側 Atom のあいだに現れる

```text
relation
capability use
contract refinement
state read/write
effect ordering
authority / trust
runtime interaction
semantic interpretation
```

の混合 subconfiguration である。

このとき、十分な coverage、witness completeness、axis exactness、semantic/runtime observation の exactness があるなら、拡張後の新しい obstruction は次の三成分に分解できる。

```text
κ_U(B)
  =
κ_U(A)
  + κ_U(f)
  + Hol_U(∂f)
```

ここで、

```text
κ_U(A)      : 既存 core にすでにあった curvature
κ_U(f)      : feature 内部の curvature
Hol_U(∂f)   : core と feature の境界に生じる holonomy
```

である。

特に、`A` が lawful で、feature `f` も内部的に lawful である場合、

```text
Flat_U(B)
  iff
Flat_U(A)
and Flat_U(f)
and Hol_U(∂f) = 0
```

が成り立つ。

これを **境界ホロノミー予想** と呼びたいです。

---

## 直感

この予想が言っているのは、かなり現場的にはこうです。

「既存システムも綺麗、追加 feature も単体では綺麗。それでも壊れるとしたら、壊れている場所は feature の内部ではなく、core と feature の境界にある。」

つまり、拡張の危険性は feature の大きさそのものではなく、

```text
feature が core のどの contract を使うか
feature が core のどの state を読むか
feature がどの effect order を変えるか
feature が既存 semantic をどう解釈するか
feature が runtime interaction を増やすか
feature が authority / trust boundary を越えるか
```

に局在化する、という主張です。

AAT 本文にはすでに、feature extension の obstruction が

```text
inherited core obstruction
feature-local obstruction
interaction obstruction
lifting failure
filling failure
complexity transfer
residual coverage gap
```

として分類される、という Architecture Extension Formula があります。
この予想は、その分類のうち特に `interaction obstruction`、`lifting failure`、`filling failure` を **境界ホロノミー** という一つの幾何的対象にまとめられるのではないか、という強化です。

---

## Holonomy の定義案

境界ホロノミー `Hol_U(∂f)` は、core と feature をまたぐ mixed diagram の非可換性として定義します。

たとえば、ある値・状態・効果・意味が、二つの path で読めるとします。

```text
core state
  -> feature operation
  -> core effect
```

と

```text
core state
  -> declared interface
  -> core effect
```

が同じ観測に落ちるべきなら、次の diagram が可換である必要があります。

```text
Obs(path_1) = Obs(path_2)
```

ずれがあるなら、

```text
Hol_U(∂f) != 0
```

です。

AAT では law failure を curvature として読み、lawfulness、required obstruction absence、signature axes zero、zero curvature が exactness の下で一致する、という zero curvature theorem が置かれています。
境界ホロノミー予想は、その zero curvature theorem を **feature extension の相対版** にするものです。

---

## もう少し数学的な形

より美しく書くなら、extension に対する相対 signature を置きます。

```text
Sig_rel(ext_f)
  =
Sig(B) / (Sig(A) + Sig(f))
```

ただし、ここでの `/` は単純な数値除算ではなく、「core 由来の軸」と「feature-local 由来の軸」を除いたあとの residual signature です。

予想は次の形になります。

```text
Sig_rel(ext_f) ≅ Hol_U(∂f)
```

つまり、

```text
拡張によって新しく生まれた residual obstruction
=
境界を一周したときに戻ってこない量
```

です。

さらに、exact sequence 風に書くとこうです。

```text
0
-> Ob_U(A)
-> Ob_U(B)
-> Ob_U(f) ⊕ Hol_U(∂f)
-> CovGap_U(ext_f)
-> 0
```

coverage gap が 0 の場合、

```text
Ob_U(B) ≅ Ob_U(A) ⊕ Ob_U(f) ⊕ Hol_U(∂f)
```

になる。

この形はかなり AAT らしいと思います。
なぜなら、AAT は architecture quality を単一値ではなく、多軸 signature、obstruction、curvature、operation path、homotopy の構造として読む理論だからです。

---

## 非自明性

これは単なる「依存を増やさなければ安全」という話ではありません。

AAT では static / runtime / semantic flatness は一般には互いに含意しない、とされています。つまり、static dependency が綺麗でも runtime retry storm や semantic contract mismatch は残りうる。

したがって、境界ホロノミーは単一値ではなく、

```text
Hol_U(∂f)
  =
(
  Hol_static(∂f),
  Hol_runtime(∂f),
  Hol_semantic(∂f),
  Hol_effect(∂f),
  Hol_authority(∂f)
)
```

のような多軸量でなければならない。

ここが非自明です。

たとえば static には安全に見える feature extension でも、semantic boundary で壊れることがあります。AAT の coupon extension の例では、coupon feature は price calculation に Atom を追加しますが、rounding、tax、payment amount の law が壊れると semantic obstruction が生じます。

つまり、

```text
Hol_static(∂f) = 0
```

でも、

```text
Hol_semantic(∂f) != 0
```

が起こりうる。

これがこの予想の強さです。

---

## 現場的な意味

この予想が正しいなら、実務ではかなり役に立ちます。

feature を追加するとき、全システムを再解析する代わりに、次を調べればよい。

```text
1. core は既に flat か
2. feature 単体は flat か
3. core-feature boundary の Hol_U(∂f) は 0 か
```

これが成立すれば、

```text
feature extension is safe
```

と判定できる可能性があります。

逆に、障害や設計劣化が起きたときも、

```text
core が悪いのか
feature が悪いのか
境界が悪いのか
観測 coverage が足りないのか
```

を分解できます。

これは現場では、

```text
PR / CI での architecture regression check
feature flag rollout の事前検査
microservice 追加時の contract boundary 検査
DDD aggregate 追加時の semantic boundary 検査
event-driven system の handler / effect ordering 検査
permission / authority leak の検査
```

に使えるはずです。

---

## Coupon Extension での読み

AAT の coupon extension では、次の law が出ています。

```text
FinalAmount = round(tax(discount(subtotal)))
PaymentAmount = FinalAmount
ReceiptAmount = FinalAmount
```

もし feature 内部では coupon calculation が正しく、既存 checkout core も正しいのに、

```text
subtotal -> discount -> tax -> round
subtotal -> tax -> discount -> round
```

の二つが異なる値を返すなら、それは feature 内部だけの失敗でも core 内部だけの失敗でもありません。core の price semantics と coupon feature の discount semantics の境界で発生する obstruction です。AAT 本文でも、このような rounding order や discount application order の観測差は semantic obstruction として読まれています。

境界ホロノミー予想では、これは

```text
Hol_semantic(∂coupon) != 0
```

と読む。

そして repair は、

```text
discount と tax の順序を固定する
FinalAmount contract を強化する
PaymentAmount / ReceiptAmount との diagram を可換にする
rounding policy を boundary contract に昇格する
```

のいずれかになる。

---

## Homotopy 版の派生予想

この予想には、美しい派生形があります。

二つの feature extension

```text
ext_f : A -> A_f
ext_g : A -> A_g
```

があるとき、AAT では独立な feature extension は可換 square を作り、`f` の後に `g` を行う path と `g` の後に `f` を行う path は homotopic に読める、という形が示されています。

そこで次の派生予想が立てられます。

```text
ext_g . ext_f  ~  ext_f . ext_g
  iff
Hol_U(∂f, ∂g) = 0
```

つまり、

```text
二つの feature の追加順序が architecture 的に同じである
```

ことと、

```text
二つの feature の相互境界 holonomy が 0 である
```

ことが対応する。

これはとても実務的です。
ロードマップ上で feature `f` と `g` の追加順序を入れ替えてよいか、という判断が、

```text
pairwise boundary holonomy
```

の計算問題になります。

---

## CS への寄与可能性

この予想が成立すると、ソフトウェア工学に次の方向を開けます。

第一に、**modular architecture verification** です。全体を毎回検証するのではなく、拡張境界の diagram だけを見ることで安全性を判定する理論になります。

第二に、**feature interaction problem の代数化**です。feature 同士の干渉を、ad hoc な経験則ではなく、mixed boundary holonomy として扱える。

第三に、**architecture CI の理論的基礎**になります。PR が追加した Atom family `F_f` と、既存 core `F_A` の境界 `∂f` だけから、semantic regression、effect ordering regression、authority leak を検出する設計が可能になります。

第四に、**architecture synthesis / no-solution certificate** につながります。ある boundary holonomy が消せないなら、「この制約のままでは安全な extension は存在しない」という certificate になる可能性があります。AAT では no-solution soundness には制約言語、decision procedure、coverage、exactness の明示が必要とされているので、この予想はその certificate の具体的な候補にもなります。

---

## 予想の短い定式化

最後に、論文向けに短く書くならこうです。

```text
Conjecture: Boundary Holonomy of Feature Extension

Let ext_f : A -> B be a feature extension in an AAT model
with exact witness family W, required signature axes S,
and curvature valuation κ_U.

Assume:
  1. A is U-flat.
  2. f is internally U-flat.
  3. observation over A, f, and ∂f is W-complete and S-exact.
  4. residual coverage gap is zero.

Then:
  B is U-flat
  iff
  Hol_U(∂f) = 0.

More generally:
  κ_U(B)
    =
  κ_U(A) + κ_U(f) + Hol_U(∂f)
  up to the selected signature equivalence.
```

日本語では：

```text
完全観測かつ exact な AAT model において、
既存 core と追加 feature がそれぞれ flat であるなら、
拡張後 architecture の flatness を妨げる obstruction は
core-feature 境界の holonomy によって完全に測られる。
```

これが、AAT におけるソフトウェアアーキテクチャ拡張のかなり有望な中心予想だと思います。
