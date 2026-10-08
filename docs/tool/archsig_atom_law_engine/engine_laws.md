# エンジン自身の AAT モデルと要求 Law

[設計本文](README.md)のエンジンを、型付きの式・参照・操作からなる architecture object
として記述する。以下の Law は設計に課す要求である。式としての仕様と、有限例による確認と、
全入力についての証明を区別する。

## 1. エンジンを表す Atom

エンジンの仕様モデルを表す family を `F_eng` とする。
一つの Atom が一つの事実を表すよう、例えば次を宣言する。

```text
sort(AtomFamily)                 sort(LawAST)                  sort(TypedIR)
sort(DerivedModel)               sort(Result)
domain(compile, LawAST)          codomain(compile, TypedIR)
input(evaluate, 0, AtomFamily)   input(evaluate, 1, TypedIR)
output(evaluate, DerivedModel)
uses(evaluateResidual, evaluateTerm)
flows(compile_output, evaluate_law_input)
represents(ir_term, typed_expression)
bodyNode(operation, node, constructor, arguments)
refers(node, declaration)
```

sort、domain、codomain、bodyNode 等は、設計対象の型・式・参照という原始事実である。
`compile_is_sound` や `lawful` を Atom に置かない。
仕様の Atom と実装から観測する Atom は、同じ語彙を使えても由来の異なるモデルである。

composition reading は参照から relation を、同じ宣言への参照から identification を作る。

```text
C_eng = (F_eng, R_eng, I_eng)
A_eng = (C_eng, structure_maps, selected_quantities)
```

`structure_maps` は各操作の型付き入出力と式の解釈、`selected_quantities` は
入力依存・型保存・Law 保存・合成等の評価軸である。
これは [AAT 第I部](../../aat/algebraic_geometric_theory/part_1_atoms_objects_laws.md)
§§4–7・10 の configuration、architecture object、equation system に対応する。

分析対象の入力 family `F`、エンジン仕様の `F_eng`、計算結果の `DerivedModel` は別の型である。
`DerivedModel` を F の新しい観測事実へ戻す変換は持たない。
エンジンを対象として分析する場合も、`(F_eng, L_eng)` という通常の二入力を使う。

## 2. Context と操作

各 requirement の自由変数、参照式、二つの比較経路の support から context を生成する。
例えばコンパイル保存の context は、共有入力 A・L と、`compile → run` および
`evalRef` の両経路を含む。再利用の context は、根の入力、導出規則、再検査を含む。

```text
W = (Supp(W), Ax(W), Obs(W))
```

support は必要な仕様 Atom、axis は requirement の種別、observable は型付きの式と
その値である。Law の instance を支える最小 support を求め、参照先に閉じる。
その context 族と重なりを構成して、required equation と相互作用の支持を覆う。
部品名の一覧だけを cover にしない。

エンジン仕様の変更には、識別子変更、式の正規化、評価段階の分割、共通式の再利用などがある。
各変更 `f : A_eng → B_eng` を操作と呼ぶには、実際の Atom map が
family・relation・identification を保存することが要る。
計算の保存は、次節の Law によりさらに確認する。
保存される部分だけを持つ変更は `A_eng ← C → B_eng` として記述する。

## 3. 要求を方程式として定義する

以下の記号を使う。

- `A : AtomDocument`、`L : LawModule`、`q : Query(L)`。
- `E_b(A,L,q)` は予算 b での計算。`E∞` は制限を置かない数学的評価手続き。
- `⟦q⟧_L(A)` は、型付き項の解釈・方程式の充足・解集合から独立に定める参照意味論。
  最適化エンジンの返り値でこれを定義しない。
- `claims(r)` は結果が証拠とともに主張する命題の集合。
- `r ≈ r'` は同じ量化域で同じ判断・対象・解集合を表すこと。
  表示順、選んだ基底、特解の表現が異なっても、構成した対応がそれを同定すればよい。
  複数の反例や特解から選ぶ証人は個体の一致を要求せず、同じ反例関係・解集合への所属を
  それぞれ検査する。証人の選択順を、名前への自然性の要求に混ぜない。

各 Law の量化は型付けされた適用域に限る。`q` を指定しても、意味を持つ自由パラメータは
L 内で宣言・束縛する。

### L01 二入力と決定性

対応済みの決定可能な問いについて、完了した二つの計算は同じ意味を返す。

```text
complete(E_b(A,L,q)) ∧ complete(E_c(A,L,q))
  ⇒ E_b(A,L,q) ≈ E_c(A,L,q)
```

実行順、スレッド数、保存済み中間結果を変えても、採用される主張の真偽は変わらない。
不正な再利用候補の破棄や、予算中断まで同じ返り値であることは要求しない。

### L02 導出の由来と非生成

```text
family(construct(A,L)) = family(A)
leaves(d) ⊆ AtomRefs(A) ∪ RuleRefs(L) ∪ FixedBuiltinRules
```

全導出 d の根をこの三種類まで追う。組込み規則はエンジンの意味仕様の一部であり、
実行ごとの入力にはしない。証拠付きと称する外部結論を新しい根として採用しない。

### L03 識別子と provenance に対する自然性

原始値と関係を保存する参照 ID の全単射 `ρ` について、

```text
E∞(ρA, L, q) ≈ ρ(E∞(A,L,q))
```

とする。Law に入力固有 ID 定数がないため L と q は変わらない。
source ref、言語名、framework 名だけが変わる場合、計算上の値は同じで説明の参照だけが変わる。
語彙自体の翻訳は別の reading 比較として明示する。

### L04 型保存

```text
Γ ⊢ e : T ∧ evaluateTerm(A,e) = v  ⇒  v ∈ ⟦T⟧
```

等号の両辺、写像の始域・終域、合成の接続点を型検査する。
成立条件付きの型の構成には、その条件を核が検査した導出を必要とする。

### L05 コンパイル保存

参照評価とコンパイル後の評価がともに完了する対応済み部分で、

```text
run(A, compile(L), q) ≈ evalRef(A,L,q)
```

を要求する。join の最適化、式の共通化、行列の基底変更にも同じ等式を課す。
参照評価は AST の構造再帰と原始演算から定義する。

[L05の具体例](compiler_preservation_example.md)では、原始ASTと候補変換規則を
`F_eng` に、共通の参照意味論と保存要求を `L_eng` に置く。
変換先を生成してから全有理数代入で比較し、規則の一事実の差から成立と反例を導出する。

### L06 制限と評価の可換性

`j : W' → W`、`k : W'' → W'` に対し、

```text
res_id = id
res_(j ∘ k) = res_k ∘ res_j
res_j(ν_(W,i,a)) = ν_(W',i,a)
res_j(ε_(W,A,i,a)) = ε_(W',A,i,a)
```

とする。局所評価に必要な operand が残る instance に適用する。
局所に制限できない大域的な計算は、依存 support を保持する context で評価する。

### L07 操作の実体と合成

```text
a ∈ F_A       ⇒ f(a) ∈ F_B
R_A(a,b)      ⇒ R_B(f(a),f(b))
I_A(a,b)      ⇒ I_B(f(a),f(b))
underlying(id_A) = id
underlying(g ∘ f) = underlying(g) ∘ underlying(f)
```

これは `ConfigurationHom` の要求である。さらに選択された Law の保存を問うときは、
対応する residual と f の可換式を検査する。始域・終域が同じだけで操作を同一視しない。
異なる名前付き操作が同じ Atom map を持つ場合も、操作自身とその作用を区別する。

### L08 部分知識と判定の健全性

有限提示そのものを対象にする問いでは、

```text
Established(q) ∈ claims(E_b(A,L,q))  ⇒  ⟦q⟧_L(A)
Refuted(w) ∈ claims(E_b(A,L,q))      ⇒  checkCounterexample(A,L,q,w) = true
```

とする。未観測値を含む対象については、A の既知の事実と型を保つ補完の集合
`Comp(A)` を意味論として使う。L の要求 Law を最初から成立させる補完に限定しない。

```text
Established(q) ⇒ ∀ M ∈ Comp(A), ⟦q⟧_L(M)
Refuted(q)    ⇒ ∀ M ∈ Comp(A), ¬⟦q⟧_L(M)
```

補完によって答えが変わる場合は、その識別対または不足値を返す。
補完が存在することも確認する。矛盾した提示による空の補完集合から成立を作らない。
初期実装で全補完を扱う算法がなければ、対応済みの式だけを決定し、それ以外は未決とする。

### L09 対応済み算法の完全性

有限列挙または有理線形方程式の対応済み部分で、予算を制限しなければ評価は停止し、
参照意味論と一致する。特に有理線形問題では、生成した `D,b` に対して次のいずれかを返す。

```text
solution z : D z = b
または
inconsistency witness λ : λ D = 0 ∧ λ b ≠ 0
```

核は原始 Atom から D と b を構成し、生成した z または λ を再代入して検査する。
これにより、常に未決を返すだけの評価器を要件充足としない。
一般の core、任意の式、未対応の係数へこの停止要求を広げない。

### L10 局所・大域と具体的障害

係数・制限から構成した複体について `d¹d⁰=0` を要求する。
対象から導出した c が `ker d¹` に入り、`c=d⁰b` となる b を求めたときに限って零類とする。

```text
zeroClass(c) ⇔ ∃ b, d⁰ b = c       (c ∈ ker d¹)
```

局所状態を貼り合わせる構成には、同じ重なり上での一致と gluing の存在・一意性を課す。
意味的修復への出力は、構成した g が元の修復方程式を満たすことを要求する。
障害空間の次元だけから、この g の存在を結論しない。

### L11 Reading の保存と診断の保存

Law 評価保存と診断保存を、異なる方程式として検査する。

```text
ε' ∘ objectMap = coefficientMap ∘ ε
d' ∘ cochainMap = cochainMap ∘ d
diagnosticMap = H¹(cochainMap)
```

最後の写像が同型かは kernel・cokernel または構成した逆写像で検査する。
第一式だけで同型と判定しない。恒等・合成についても実際の比較写像を保持する。

### L12 再利用の健全性

```text
claims(reuse(d,A',L',q)) ⊆ trueClaims(⟦q⟧_(L')(A'))
```

d の依存先・式・条件を現在の入力へ照合し、推論を再検査する。
再利用が成功した場合、その値は通常の完全評価と同じ意味を持つ。
保存済みの判定ラベルや digest を検査の代わりにしない。

### L13 原始語彙の保守的な拡張

旧語彙 V を V' へ追加し、新しい Atom と Law が旧計算の依存に入らないとする。
忘却写像 p に対し、旧問い q は次を満たす。

```text
p(E∞(A',L',q)) ≈ E∞(pA',pL',q)
```

新しい Law が旧問いの局所性や係数を変える場合は、この前提を満たさない。
その場合は異なる reading の比較を計算する。

## 4. Law を residual として評価する有限モデル

上の要求は全量化した方程式である。有限な仕様比較や検算では、原始操作の型と式から
有限な適用 instance の集合 `Q(W)` を生成する。context はその operand を保持する。
instance の一貫した添字と、制限に沿う包含 `Q(W') ⊆ Q(W)` を構成する。

```text
O(W) = ℤ ^ Q(W)
res_j = 座標の制限

ε_i(q) = 0  if lhs_i(q) = rhs_i(q)
       = 1  if lhs_i(q) ≠ rhs_i(q)
```

ここでは型付きの等値判定が可能な instance に限る。含意の requirement は、
前提と結論を計算し、その含意の成立値を1と比較する等式として評価する。
`ν_(i,a)` は該当する Law・Atom instance の座標を選ぶ固定の指示関数とし、
object に依存する `ε` と区別する。成立の判定には `ε=0` を用いる。

未評価の operand は未定義の partial section として残す。
すべて評価済みになる前に、O(W) の零 section を得たとはしない。
この有限 reading では制限は環準同型であり、operand を保持する context 間で
residual の可換性を確かめられる。

このモデルによって、自己要件を AAT の equation system として具体的に読むことができる。
有限 instance 上の成立は、その集合についての成立である。
L01–L13 の全量化した要求を満たすには、個々の演算の意味論と保存性の証明が別途要る。
この product-ring reading に、Atlas や SAGA の適用条件を自動的に付与しない。

## 5. 自己適用と独立した確認

自己モデルは、仕様の依存関係や可換性に反例を探す対象になる。
自己評価を、評価器そのものの正しさの根拠として循環利用しない。

| 確認対象 | 独立に確かめる方法 |
| --- | --- |
| 二入力と由来 | 導出の葉を生の Atom、Law、固定規則まで再走査する |
| 型・コンパイル保存 | 独立した参照意味論との照合、演算別の保存証明 |
| 線形問題 | 原始データからの行列再構成、解・不成立証拠の再代入 |
| 局所・大域 | 制限・微分の式と、構成した gluing の一致を検査する |
| Reading 比較 | 実際の写像・逆写像・微分可換性を確認する |
| 実装との対応 | 実装を再観測して仕様モデルとの構造対応を作る |

将来の形式化では、特定の DSL 意味論や検査器の健全性を定理として切り出せる。
設計モデルの自己評価、実装のテスト、数学的な証明は、それぞれ何を確認したかを保持する。

根拠は [AAT 第I部](../../aat/algebraic_geometric_theory/part_1_atoms_objects_laws.md)
定義7.1–7.3・10.2・10.4Aと、
[第II部](../../aat/algebraic_geometric_theory/part_2_architecture_geometry_sites_sheaves.md)
定義3.1・4.3A・7.2である。これらを変更せず、tooling の有限 reading として具体化している。
