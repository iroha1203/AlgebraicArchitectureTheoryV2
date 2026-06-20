# AAT Quality Surface 構想の整理

## 1. 中心コンセプト

表向きには、一般エンジニアに伝わりやすい **「品質サーフェイス」** という言葉と曲面可視化を使う。

一方、数学的な本体は単なる曲面や総合品質スコアではなく、

> profile に沿って変化する複数の品質判定を、atom-supported certificate と比較写像によって統合した幾何的対象

とする。

役割分担は次のとおり。

```math
\boxed{\text{Quality Surface}=\text{プロダクト・可視化上の入口}}
```

```math
\boxed{\text{Atom-supported Quality Geometry}=\text{数学的な本体}}
```

---

## 2. 解決したい問題

従来の品質評価は、違反数や総合点のような単一スカラーに潰れやすい。

しかし AAT が扱いたい品質は、例えば次のようなもの。

* 局所的には lawful だが、大域的には貼り合わせられない
* profile を変えると、突然 obstruction が観測される
* 同じスカラー値でも、原因となる atom family が異なる
* repair direction は存在するが、特異点で lift できない
* cover や law universe の変更順序によって certificate が変わる
* 観測されていないことと、測定結果がゼロであることを区別する

したがって品質は一つの数値ではなく、

```math
\operatorname{Cert}_A(p) =
\left(
\sigma_p,
\omega_p,
S_p,
R_p,
\nu_p,
T_p
\right)
```

のような certificate として保持する。

ここで、

* (\sigma_p)：multi-axis quality signature
* (\omega_p)：obstruction class または obstruction witness
* (S_p)：supporting atom family
* (R_p)：repair directions、repair cone、repair poset など
* (\nu_p)：verdict
* (T_p)：atom から source reference への trace 情報

を表す。

---

## 3. 数学的な本体

固定した architecture (A) に対して、まず profile の集合または圏を置く。

```math
\mathsf{Prof}_A
```

profile には、例えば次のデータが含まれる。

* law universe
* coverage topology / cover
* Atom vocabulary
* coefficient sheaf
* witness family
* representation family
* measurement threshold
* certificate selector
* verdict discipline

各 profile (p) に certificate space を対応させる。

```math
\mathcal C_A(p)
```

そして profile change

```math
u:p\to q
```

に対して、certificate の比較写像を持たせる。

```math
\Phi_u:\mathcal C_A(p)\to\mathcal C_A(q)
```

したがって全体は、概念的には

```math
\mathcal C_A:
\mathsf{Prof}_A
\longrightarrow
\mathbf{Cert}_{\operatorname{At}(A)}
```

という functor または pseudofunctor になる。

その Grothendieck construction

```math
\mathfrak Q_A =
\int_{p\in\mathsf{Prof}_A}
\mathcal C_A(p)
```

を、数学的な正式対象である

> **atom-supported quality geometry**

と呼ぶ。

射影

```math
\pi:\mathfrak Q_A\to\mathsf{Prof}_A
```

の各 fiber が、その profile における品質 certificate の空間になる。

---

## 4. なぜ単なる曲面や多様体ではないのか

通常の曲面は、

```math
z=q(x,y)
```

のように、二つの入力に対して一つの高さを与える。

しかし Quality Surface が保持したいのは一つの高さではなく、obstruction、support、repair、verdict などを含む構造的 certificate である。

また profile 自体も、単なる実数座標とは限らない。cover refinement や law universe の包含関係など、有限 poset や category として表す方が自然な変更を含む。

さらに profile を変えると、次のものが跳ぶ可能性がある。

* obstruction group の次元
* certificate の個数
* minimal support family
* repair space の次元
* verdict
* comparison map の rank

したがって全体は、原則として滑らかな manifold ではなく、

> **stratified、constructible、singular な certificate geometry**

として扱う。

多様体になるのは、certificate の型や比較写像が局所的に一定な regular region に限られる。

---

## 5. 「品質サーフェイス」の正確な位置づけ

Quality Surface は、atom-supported quality geometry 全体ではなく、その二次元 slice と考える。

二次元 parameter object (B) と profile map

```math
\gamma:B\to\mathsf{Prof}_A
```

を選ぶ。

その pullback

```math
\mathfrak S_{A,\gamma} =
\gamma^*\mathfrak Q_A
\to B
```

を **quality surface** と呼ぶ。

例えば二つの profile 軸として、

* 横軸：law universe の強さ
* 縦軸：cover の細かさ

を選ぶ。

有限 regime では (B) は滑らかな平面でなくてもよく、

* grid
* finite poset
* square complex
* simplicial complex
* nerve

で構わない。

したがって数学的には、

> certificate sheaf または certificate diagram を載せた二次元セル複体

に近い。

---

## 6. 可視化としての曲面

数学的対象に reading map を加える。

```math
r:\mathfrak S_{A,\gamma}\to\mathbb R^m
```

(m=1) を選べば、通常の三次元曲面として表示できる。

ただし、その高さは「総合品質点」ではなく、選択された一つの reading にすぎない。

UI 上では、例えば次のように情報を分担できる。

| 表現         | 意味                                          |
| ---------- | ------------------------------------------- |
| 高さ         | obstruction intensity など、選択された reading      |
| 色          | quality axis、obstruction type、verdict class |
| 等高線        | repair cost や repair distance               |
| ridge      | certificate type、support、rank の変化           |
| 穴・空白       | unmeasured、coverage 不足、比較不能                 |
| 複数 sheet   | 同一 profile に複数 certificate が存在              |
| クリック       | supporting atom family                      |
| drill-down | ArchMap が提供する source reference              |

曲面はあくまで lossful projection であり、裏側の certificate を失わないことが重要になる。

---

## 7. 比較写像が幾何を作る

各 profile で品質を計算するだけでは、結果一覧や dashboard にすぎない。

幾何的な対象にするには、profile change に沿った certificate transport が必要になる。

```math
\Phi_u:\mathcal C_A(p)\to\mathcal C_A(q)
```

さらに変更の合成に対して、

```math
\Phi_{v\circ u}
\simeq
\Phi_v\circ\Phi_u
```

という coherence を要求する。

これにより、次を数学的に語れる。

* certificate が profile change に対して保存された
* obstruction が消えたのではなく、projection で見えなくなった
* cover refinement により新しい certificate が観測可能になった
* atom support が分裂または合流した
* repair direction が profile change で失われた
* 異なる変更順序が異なる結果を生んだ

---

## 8. 二次元化によって現れる profile curvature

二つの profile 変更を考える。

* (u)：cover refinement
* (v)：law universe strengthening

二つの経路

```math
p\xrightarrow{u}p_u\xrightarrow{v'}p_{uv}
```

```math
p\xrightarrow{v}p_v\xrightarrow{u'}p_{vu}
```

に沿った transport を比較する。

```math
\Phi_{v'}\circ\Phi_u
\quad\text{と}\quad
\Phi_{u'}\circ\Phi_v
```

これらが一致しなければ、

> cover を先に変える場合と law を先に変える場合で、品質 certificate が異なる

という現象になる。

これは **profile curvature** の候補になる。

加法的な setting なら形式的に

```math
\operatorname{Curv}_{u,v} =
\Phi_{v'}\Phi_u-\Phi_{u'}\Phi_v
```

と書ける。

一般には、二つの transport の間を埋める coherent 2-cell が存在するかどうかで定義する。

これは Quality Surface を単なるプロットではなく、二次元的な比較構造を持つ本当の幾何対象にする重要な論点である。

---

## 9. 三種類の特異現象を分離する

### Architecture singularity

AAT 本来の deformation obstruction。

一次の lawful deformation が高次へ lift できない。

```math
\operatorname{ob}(\eta)\neq0
```

これは architecture 内部の特異性。

### Profile ridge / discriminant

profile change によって certificate family の型が局所一定でなくなる場所。

例えば、

* obstruction rank が跳ぶ
* minimal support family が変わる
* repair space の次元が変わる
* verdict が変わる

これは観測条件や law universe の変更によって発生し得る。

### Reading fold

異なる certificate が、可視化上の同じ値に潰れる現象。

```math
c_1\neq c_2,
\qquad
r(c_1)=r(c_2)
```

これは単一スカラー化の限界を表す。

したがって、

```math
\boxed{
\text{architecture singularity}
\neq
\text{profile ridge}
\neq
\text{reading fold}
}
```

を明示的に区別する。

---

## 10. Atom support に関する重要な注意

cohomology class や obstruction class の support は、representative に依存する可能性がある。

そのため、

```math
\operatorname{ChosenSupport}(z)
```

と、

```math
\operatorname{MinSupportFamily}([z])
```

を区別する必要がある。

前者は、選択された witness representative の support。

後者は、同じ class を表すすべての representative の中で inclusion-minimal な support family の集合、または antichain。

これにより、support を単なるデバッグ情報ではなく、certificate の構造的要素として扱える。

さらに repair に対して、

> obstruction を消す repair support は、minimal certificate support family を hit しなければならない

という hitting-set 型の定理候補につながる。

---

## 11. Source reference に関する claim boundary

AAT 内部が保証するのは、certificate が supporting atom family を持つことまで。

atom と実コード上の source reference の接続は、ArchMap / observation layer が供給する。

したがって表現は、

> certificate の根拠を supporting atom に結び、利用可能な ArchMap source reference へ追跡する

とする。

AAT の内側では、次を主張しない。

* source extraction の完全性
* observation completeness
* コード全体の品質判定
* 抽出されていない構造が存在しないこと

---

## 12. 最初の有限モデル

初期研究では、滑らかな多様体を構成する必要はない。

例えば、

```math
P
=

P_{\mathrm{law}}
\times
P_{\mathrm{cover}}
```

という有限 product poset を使う。

```math
P_{\mathrm{law}}
=
{U_0\subset U_1\subset U_2}
```

```math
P_{\mathrm{cover}}
=
{\mathcal U_0\prec\mathcal U_1\prec\mathcal U_2}
```

これにより 3×3 の profile grid を得る。

各頂点で、

```math
c_{ij}
=
\left(
\sigma_{ij},
\omega_{ij},
\operatorname{MinSupp}_{ij},
R_{ij},
\nu_{ij}
\right)
```

を計算する。

各辺には comparison map を置き、各 square では transport の可換性を検査する。

この有限モデルから、次を定義できる。

* **regular cell**：certificate type が保存され、square が可換
* **ridge edge**：rank、support、verdict、repair dimension が跳ぶ
* **curvature cell**：二つの変更順序が一致しない
* **fold pair**：異なる certificate が同じ scalar reading を持つ
* **obstruction locus**：選択した obstruction certificate が非零
* **trace locus**：supporting atom が source ref まで展開可能

---

## 13. 最初に狙う研究成果

### Scalar-collapse counterexample

同じ violation count や同じ scalar reading を持ちながら、

* obstruction class
* minimal atom support family
* repair possibilities

が異なる二つの architecture を示す。

これにより Quality Surface が既存スコアの名前替えでないことを示せる。

### Atom-support repair theorem

repair support が certificate support と交わらなければ、その obstruction は残る、という局所性定理。

複数の minimal support が存在する場合、repair support はその family の hitting set になる。

### Profile ridge theorem

profile change によって obstruction map の rank が跳ぶと、

```math
\dim\ker\kappa_p
```

すなわち feasible repair space の次元も変化する、という定理候補。

### Profile curvature example

cover refinement と law strengthening の順序によって certificate transport が異なる有限例。

---

## 14. 用語の最終整理

| 用語                                | 意味                                      |
| --------------------------------- | --------------------------------------- |
| `atom-supported quality geometry` | profile-indexed certificate geometry 全体 |
| `quality surface`                 | 二次元 profile slice                       |
| `quality trajectory`              | 一次元 profile path                        |
| `quality manifold`                | certificate type が局所一定な regular stratum |
| `quality surface view`            | UI 上の可視化                                |
| `reading`                         | geometry から数値・ベクトルへの射影                  |
| `ridge`                           | certificate type が跳ぶ profile locus      |
| `fold`                            | 異なる certificate が reading 上で潰れる現象       |
| `obstruction locus`               | obstruction certificate が非零の領域          |
| `repair basin`                    | 選択した target に到達可能な repair region        |
| `profile curvature`               | profile change の順序依存性                   |

---

## 15. マーケティング上のメッセージ

中心的な訴求は、

> **コード品質を、点数ではなく地形として見る。**

より詳しくは、

> AAT Quality Surface は、アーキテクチャ品質を単一スコアに潰さず、obstruction、ridge、repair potential、multi-axis signature として可視化する。各判定は supporting atom を持ち、利用可能な source reference へ追跡できる。

ユーザー体験としては、

> 「品質が72点から65点になった」

ではなく、

> 「この変更によって ridge を越え、大域的に貼り合わせ不能な領域へ入った。obstruction certificate はこの atom family に support され、対応する source reference はここにある」

と説明できることを目指す。

---

## 16. 現時点での中心命題

研究全体を一文で表すなら、次が最も近い。

> **Atom-supported quality geometry は、intrinsic obstruction、profile-dependent observation、repair reachability、reading projection artifact を区別しながら、一つの追跡可能な品質 certificate geometry として統合できるか。**

そしてプロダクトとしては、

> **表では Quality Surface、裏では atom-supported quality geometry**

という二層構造で進める。
