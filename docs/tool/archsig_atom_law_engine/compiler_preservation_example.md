# L05: 原始変換規則からコンパイル保存を評価する例

[自己モデルの L05](engine_laws.md#l05-コンパイル保存)を、アフィン式の定数畳込みについて
具体化する。エンジン仕様の二入力は、式・型・参照・変換規則を記述する `F_eng` と、
それらの読み方と保存要求を記述する `L_eng` である。変換先の式は原始変換規則から生成し、
参照評価と比較して、成立または反例を求める。

## 1. 自己適用の対象と量化域

対象は、次の source DSL と対応する IR を扱うコンパイラの有限仕様モデルである。
`x` は変数宣言への参照、`k` は有理数リテラルを表す。

```text
SourceExpr ::= Var(x) | Lit(k) | Add(SourceExpr, SourceExpr)
SourceLaw  ::= Eq(SourceExpr, SourceExpr)
IrExpr     ::= Load(x) | Const(k) | Plus(IrExpr, IrExpr)
IrLaw      ::= Equal(IrExpr, IrExpr)
```

各構文木は有限・非循環であり、式の値型は `Q` である。式が参照する変数宣言から
有限集合 `X` を作り、代入全体 `Val(X) = (X → Q)` を量化域とする。
source Law の各代入における評価は、左右差とその零判定の組
`(residual, residual = 0)` を返す。ここでの `q` はその方程式評価である。

以下の `F_eng` は、エンジン仕様の一部である source Law と候補コンパイラ規則を
同じ原始語彙で記述する。内側の source Law と、外側の要求 `L_eng` は型で区別する。
`L_eng` の解析に、別のコンパイラプラグインや生成済み IR を渡す経路は設けない。

## 2. 入力 `F_eng`: 型・式・参照・変換の Atom

### 2.1 共通の型と評価する source Law

`sort`、`domain`、`codomain`、`input` は型と操作の宣言を表す原始事実である。
source/IR の constructor、引数位置、値型は §1 の文法に従って検査する。

```text
sort(Q)                    sort(SourceExpr)           sort(IrExpr)
sort(SourceLaw)            sort(IrLaw)                sort(Valuation)
sort(Evaluation)           sort(CompilerRules)
input(compile, 0, CompilerRules)
input(compile, 1, SourceLaw)       output(compile, IrLaw)
input(evalRef, 0, SourceLaw)       input(evalRef, 1, Valuation)
output(evalRef, Evaluation)
input(run, 0, IrLaw)               input(run, 1, Valuation)
output(run, Evaluation)

variable(x)               value_type(x, Q)
source_law(s)             body_root(s, eq0)
node(eq0, Eq)             child(eq0, left, n2)        child(eq0, right, z)
node(n2, Add)             child(n2, left, n1)         child(n2, right, k2)
node(n1, Add)             child(n1, left, vx)         child(n1, right, k1)
node(vx, Var)             refers(vx, x)
node(k1, Lit)             literal(k1, 1)
node(k2, Lit)             literal(k2, 2)
node(z, Lit)              literal(z, 0)
```

各欄は一つの Atom であり、構文木の絵を事実として追加しない。
参照をたどると、source Law は `((x + 1) + 2) = 0` と読める。
右辺の `0` は分析対象の原始方程式の定数であり、変換後の期待出力ではない。
この Law の成立を入力に含めず、各代入で成立するかは両評価経路が計算する。

### 2.2 候補コンパイラの規則

コンパイラには、一般の constructor を構造再帰で翻訳する規則と、
`Add(Add(t, Lit(u)), Lit(v))` の定数二つをまとめる規則を持たせる。
後者の原始事実を、有限パターンと有限テンプレートとして記述する。

```text
compiler(cmp)             rewrite_rule(cmp, fold)
pattern_root(fold, p0)    template_root(fold, t0)

pattern(p0, Add)          pattern_child(p0, left, p1)
pattern_child(p0, right, pv)
pattern(p1, Add)          pattern_child(p1, left, ht)
pattern_child(p1, right, pu)
pattern(pu, Lit)          pattern_value(pu, hu)
pattern(pv, Lit)          pattern_value(pv, hv)
hole(ht, SourceExpr)      hole(hu, Q)                 hole(hv, Q)

template(t0, Plus)        template_child(t0, left, tt)
template_child(t0, right, tk)
template(tt, Translate)   template_ref(tt, ht)
template(tk, Const)       template_value(tk, fv)
template(fv, ScalarBinary)
template_arg(fv, 0, hu)   template_arg(fv, 1, hv)
scalar_operator(fv, add)
```

候補を変える箇所は最後の一事実だけである。
`scalar_operator(fv, add)` を持つ family を `F_eng⁺`、同じ位置を
`scalar_operator(fv, sub)` に置き換えた family を `F_eng⁻` と書く。
これは記述の略号であり、成立・不成立を示すタグを Atom に含めるものではない。

`Translate` は束縛された source 部分木を同じ候補で翻訳するテンプレート要素であり、
`ScalarBinary` は列挙値 `add` または `sub` と二つの有理数を持つ要素である。
パターンは source の constructor を照合し、hole を束縛するだけである。
外部コードの呼出し、任意のプログラム、完成した変換先 AST の読込みを許す欄はない。
同じテンプレートを、異なる source の ID・変数名・リテラル値に適用できる。

## 3. 入力 `L_eng`: 一般規則と保存要求

ここで使う組込みの意味は、有限木の型検査、パターン照合、hole の置換、
真部分木への構造再帰、有理数の加減算、アフィン係数比較である。
その意味は [DSL の固定演算](README.md#32-law-に書く値)として定め、候補の
`scalar_operator` によって組込み加算や参照意味論を書き換えることはできない。
`F_eng` にあるのは、この固定された文法で表せる候補変換のデータである。

`L_eng` は、同じ constructor を扱うすべての提示対象に次の規則を適用する。
下記の `c`、`s`、`t`、`u`、`v`、`η` は量化変数であり、§2 の ID や定数値を含まない。

```text
derive sources = atoms(source_law)
derive compilers = atoms(compiler)
derive variables(s) = variable declarations reachable from body_root(s)
derive instances = product(compilers, sources)

operation compile(c, s):
  source Law の左右の式を translate(c, -) で翻訳し Equal を生成

operation translate(c, e):
  まず c の有限パターンを e に照合する
  一致する規則が一つなら、束縛した hole からテンプレートを生成
  一致しなければ、Var -> Load、Lit -> Const、Add -> Plus を構造再帰で生成
  Translate(t) の再帰先は、照合元 e の真部分木に限る

law L05_affine required:
  forall (c, s) in instances, η in Val(variables(s)):
    run(compile(c, s), η) = evalRef(s, η)

query evaluate(L05_affine)
```

規則の重複一致、hole の型不整合、参照欠落、循環する AST は、先に提示規則で検査する。
曖昧な規則を任意の順序で選ばない。この例の両候補には一つの規則だけがあり、
hole の型は適合し、`Translate(ht)` の再帰先は二段内側の真部分木である。
これらは原始事実から確認する条件であり、入力する保存証明ではない。

### 3.1 コンパイルと独立な参照意味論

source に対して次を定める。IR の `Load`、`Const`、`Plus` にも、別の構文上で
それぞれ変数の読出し、定数、加算という意味を定める。

```text
evalSource(Var(x), η)       = η(x)
evalSource(Lit(k), η)       = k
evalSource(Add(a,b), η)     = evalSource(a,η) + evalSource(b,η)
evalRef(Eq(a,b), η)         = (r, r = 0)
  where r = evalSource(a,η) - evalSource(b,η)

evalIR(Load(x), η)          = η(x)
evalIR(Const(k), η)         = k
evalIR(Plus(a,b), η)        = evalIR(a,η) + evalIR(b,η)
run(Equal(a,b), η)          = (r, r = 0)
  where r = evalIR(a,η) - evalIR(b,η)
```

参照評価は source AST の構造再帰だけを使う。
候補変換のテンプレートと生成した IR を参照評価の定義に使わない。
二経路が共有するのは、変数宣言・代入と、数学上の有理数演算である。

### 3.2 全代入を比較する方法

アフィン式を `(b, a) ∈ Q × Q^X` で表し、その評価を
`b + Σ_{x∈X} a_x η(x)` とする。正規化は
`Var(x) ↦ (0,e_x)`、`Lit(k) ↦ (k,0)`、`Add ↦ 成分ごとの加算` である。
IR にも constructor ごとの同じ数理的解釈を定める。

各代入での左右差を持つため、source/IR の方程式の意味もアフィン係数で保持できる。
その差 `δ_(c,s)` の全係数が零であることと、すべての代入で残差が等しいことは同値である。
実際、零代入が定数係数を、各単位代入と零代入の差が各変数係数を決める。
残差が等しければ零判定も等しいので、§3 の L05 を計算できる。

## 4. 導出した IR、残差、反例

§2 の参照をたどると、照合元 `n2` に対して
`ht ↦ vx`、`hu ↦ 1`、`hv ↦ 2` が束縛される。
テンプレートの定数は、候補に記述された演算から計算する。

| 二入力の family | 導出した定数 | 導出した IR Law | IR 側の残差 | 参照残差 | 比較残差 `δ = IR − source` |
| --- | --- | --- | --- | --- | --- |
| `F_eng⁺` | `add(1,2)=3` | `Equal(Plus(Load(x),Const(3)),Const(0))` | `x+3` | `x+3` | `0` |
| `F_eng⁻` | `sub(1,2)=−1` | `Equal(Plus(Load(x),Const(−1)),Const(0))` | `x−1` | `x+3` | `−4` |

表の IR・残差・判定は、すべて §2 と §3 からの出力である。
共通の `L_eng` に対し、`F_eng⁺` は `δ=(0,0)` となり、全 `x∈Q` について L05 が成立する。
`F_eng⁻` は `δ=(−4,0)` となり、全 `x∈Q` で残差が異なる。
さらに IR 残差 `x−1=0` を解くと `x=1` が得られる。その代入では、
参照結果は `(4,false)`、IR の結果は `(0,true)` である。
これは残差だけでなく方程式の零判定も変わる反例であり、元の二つの式へ代入して確かめられる。

固定された式についての全 `x` の判定に、数値のサンプル列挙は要らない。
また、この局所変換のリテラル値を記号 `u,v∈Q` として展開すると、
正しい候補は `(t+u)+v = t+(u+v)`、誤った候補の比較残差は `−2v` となる。
この恒等式は局所的な式変換の計算であり、任意のコンパイラ処理全体の保存証明とは別である。

## 5. AAT の自己 Law と導出根

型宣言、AST の子参照、宣言への参照、規則の hole 参照から configuration の relation を
生成し、同じ宣言への参照を identification として読む。
L05 instance の context `W_(c,s)` は source の式、候補規則、両評価経路の型宣言と、
参照先へ閉じた support を持つ。変換後のノードはその support を引き継ぐ導出対象であり、
原始 Atom family を増やさない。

[自己モデル §4](engine_laws.md#4-law-を-residual-として評価する有限モデル)に合わせ、
有限な instance 集合 `I(W)` を、提示された compiler と source Law の組から生成する。
`O(W)=Z^I(W)` の各座標には `ε_(c,s)=0` if `δ_(c,s)=0`、それ以外は `1` を置く。
したがってこの例の同じ一座標で、`F_eng⁺` は `ε=0`、`F_eng⁻` は `ε=1` となる。
`ν_(c,s)` はその座標の指示関数であり、入力に依存する `ε` と区別する。
アフィン係数の空間 `Q×Q^X` は比較のための加群であり、上の observable ring と混同しない。

| 導出対象 | 原始 Atom への根 | `L_eng`・固定演算への根 |
| --- | --- | --- |
| 変数集合と source AST | `variable`、`node`、`child`、`refers`、`literal` | 参照閉包、構文と型の検査 |
| hole の束縛と生成 IR | source AST、`pattern`、`template`、`scalar_operator` | 有限照合、置換、真部分木再帰、有理数演算 |
| 参照残差 | source AST と変数宣言 | source の構造再帰による意味論 |
| IR 残差と `δ` | 生成 IR の上記導出根 | IR の構造再帰、アフィン正規化、係数差 |
| `ε` と反例 | `δ` の導出根 | 係数の零判定、代入、元の式の再評価 |

`scalar_operator(fv, ...)` が欠けた場合も compiler と rule の存在を残し、
どの演算を使うかを不足値として返す。`add` と `sub` の補完は、それぞれ
上の成立・不成立を与えるため、この不足を零や規則なしへ置換できない。

この例は、[AAT 第I部](../../aat/algebraic_geometric_theory/part_1_atoms_objects_laws.md)
§§4–7 の configuration、architecture object、equation system を、コンパイラ仕様の
有限提示に適用したものである。確認の単位は提示された規則と source Law の組であり、
その組では全代入を記号的に比較する。任意の source 構文木への一般化には構造帰納法を、
他の最適化や式型への拡張には各演算の意味論と保存性の証明を対応させる。
設計の計算は紙上の式展開で独立に検算できる。将来の実装の自己評価が成功したことを、
その評価器自身の正しさの根拠へ循環利用しない。

## 6. 比較残差の独立検算

次は §4 の構造再帰で得た一変数アフィン式を、係数の組 `(定数, xの係数)` で検算する例である。
候補コンパイラやDSL処理系の実装ではなく、表示した式と反例の算術を独立に確認する。

```python
from fractions import Fraction as Q

def add(a, b):
    return tuple(x+y for x, y in zip(a, b))

def sub(a, b):
    return tuple(x-y for x, y in zip(a, b))

def evaluate(a, x):
    r = a[0] + a[1]*x
    return r, r == 0

x = (Q(0), Q(1))
u, v, zero = (Q(1), Q(0)), (Q(2), Q(0)), (Q(0), Q(0))
source = sub(add(add(x, u), v), zero)
target_add = sub(add(x, add(u, v)), zero)
target_sub = sub(add(x, sub(u, v)), zero)
assert sub(target_add, source) == (0, 0)
assert sub(target_sub, source) == (-4, 0)
counterexample = -target_sub[0] / target_sub[1]
assert counterexample == 1
assert evaluate(source, counterexample) == (4, False)
assert evaluate(target_sub, counterexample) == (0, True)
print("add: delta=(0,0); sub: delta=(-4,0); counterexample x=1")
```

この係数比較は固定された source Law の全有理数代入を扱う。
テンプレート生成、型検査、正規化算法そのものの一般的な正しさは、それぞれの仕様と証明で確認する。
