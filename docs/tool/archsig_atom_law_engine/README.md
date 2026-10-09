# Atom と Law DSL から構成する ArchSig エンジン設計

ArchSig の計算核を、型付き Atom と Law DSL から対象・操作・局所構造・診断を
構成するエンジンとして設計する。同じ構成結果を、変更の比較、修復、追加観測へ接続する。
[製品コンセプト](../archsig_v0_6_0_concept.md) §§1–4・7 を具体化した設計案であり、
DSL の記法と計算機能は、以下で定義する提案である。

利用者から見た入力、回答、根拠、再利用と受け入れ条件は
[エンジンマニュアル](../archsig_engine_manual.md)の外部仕様案で扱う。

- 本文: 入力、DSL、意味論、計算過程、具体例、AAT の成果への拡張。
- [エンジン自身のモデルと Law](engine_laws.md): Atom、configuration、操作、満たすべき方程式。
- [設計判断と未決事項](decisions.md): 選択理由、代替案、実装前に確定する事項。
- [三操作の局所・大域計算](local_global_example.md): 同じ原始入力から係数・微分・障害類・貼り合わせを構成する例。
- [L05の具体的評価](compiler_preservation_example.md): 原始変換規則からIRを生成し、保存成立と反例を導出する例。

## 1. 計算の単位

意味を持つ外部入力を二つに固定する。

```text
A : AtomDocument                 型付きの原始事実の有限提示
L : LawModule                    語彙、構成規則、方程式、読み、問い

(A, L)
  → 型検査された Atom family と Law の式
  → configuration / architecture object / operation family
  → context / equation / coverage / overlap / coefficient
  → 診断・対応・反例・修復候補・追加観測の要求
```

LawModule は LawPolicy の表現である。係数、局所化規則、比較の読みもその中に置き、
別の MeasurementProfile や RepairPlan を意味上の第三入力にしない。
呼出し時の問いは L が宣言した問いを選ぶ。対象を限定する条件も L の式に含める。
計算予算や表示順は実行上の指定であり、判定の真偽を変更しない。

計算核が知るものは、型、項、有限提示、方程式、射とその合成である。
プログラミング言語、フレームワーク、AST、型検査器、静的解析器、リポジトリ配置は
核の依存に置かない。手で記述した同じ Atom と Law でも同じ計算になる。
製品の SKILL が実装コードの使用文脈を観測し、source ref を付けて A を作る。
観測の役割は [Tooling guideline](../guideline.md) に従う。

## 2. Atom の提示

### 2.1 型と事実

[AAT 第I部](../../aat/algebraic_geometric_theory/part_1_atoms_objects_laws.md)
定義1.1の五成分を採用する。

```text
Atom = (kind, axis, subject, predicate, payload)

payload ::= exact_scalar | enum_value | subject_ref
          | finite_tuple(payload, ...) | typed_term
```

`typed_term` は、宣言済みの型・定数・演算からなる検査可能な項である。
最初の算術部分言語は有理数上のアフィン式とする。外部関数、実行コード、
自由記述の意味解釈を呼ぶ項は持たない。有限表を使う場合も、入力域・各行の原始値・
未提示値を区別し、数行の観測から全関数を補完しない。

語彙宣言は各 predicate の引数型と事実の読みを定める。例えば、対象の存在、
操作の始域・終域、操作に書かれた加算定数、合成の出現、値の参照関係を記録する。
同一 subject が複数の意味を担う場合は複数の事実を保持する。

意味ラベルは診断と独立した使用上の事実として読む。Atom の名前を変えても、
「この Law に違反する」の言い換えなら原始事実として採用しない。
数学としての Atom の広い定義のうち、このエンジンが受け取る部分言語をここで選んでいる。

### 2.2 観測の説明と計算上の値

各 Atom に付ける source ref、版、観測方法の説明は provenance とする。
核はそれらを結果へ引き継ぎ、ソースを開くための位置として扱う。
パスや拡張子、言語名から係数、所属、操作、判定を変えない。
意味に必要な事実は、provenance の文章から推測せず、型付き Atom として明示する。

入力 family は固定される。Law 評価で得た残差や証明は `Derived` な計算対象であり、
その family に「観測 Atom」として追加しない。
別の設計候補を比較するときは、観測と同じ原始語彙で記述した候補 snapshot を A 内に持ち、
観測済み／提案の由来を保持する。提案が成立済みの操作かは核が計算する。

### 2.3 入力できる事実と導出するもの

| 入力する原始事実 | Law の規則 | 核が導出するもの |
| --- | --- | --- |
| 操作の端点と式 | 合成、保存すべき方程式 | 可換性、残差、反例 |
| 参照・所属・使用の関係 | support の閉包規則 | Context、局所化、重なり |
| 対象・値・操作の有限提示 | 生成元・関係・係数の構成規則 | 係数表示、制限写像、複体 |
| 変更前後の原始事実 | 対応の生成・保存条件 | 候補写像、成立済みの射、合成 |
| 区別できる原始値 | 観測の読みと Law 評価 | 十分性、識別対、追加観測の要求 |

完成した cover、Čech 行列、障害値、rank、acyclic・adequate・repairable 等の判定、
完成した比較同型や大域修復、その成立証明を入力欄にしない。
行列や表という形式ではなく、その値が何を表すかで判断する。
例えば操作の原始係数表は認めるが、答えである障害行列を係数表と呼び替えても認めない。

型検査は導出済み型から原始事実型への流入を防ぐ。原始事実の虚偽や、巧妙な言い換えの
意味的検出は型検査だけで保証できない。語彙の選択と観測内容の確認は SKILL の責務に置き、
エンジンによる保証を「提示した A と L からの導出」に固定する。

## 3. Law DSL

### 3.1 宣言と型

DSL は読みの宣言と、そこから計算する方程式を同じ module 内で記述する。
各宣言には独立した型を与える。

| 宣言 | 内容 | 評価結果 |
| --- | --- | --- |
| `vocabulary` | 原始 predicate と値型 | Atom の型付け |
| `derive` | join、射影、有限集合、正の有限閉包 | 関係・生成元と由来 |
| `object` / `operation` | configuration と項による変換規則 | 対象・候補 configuration map |
| `context` / `coverage` | support、軸、observable と必要な支持 | context と cover の候補 |
| `coefficient` | 係数環、生成元・関係、制限の生成規則 | 有限表示された係数と写像 |
| `law` | typed equation、量化域、役割 | equation index と residual |
| `reading` | 射影・比較・診断の読み | 導出対象間の対応 |
| `query` | 方程式の充足、解、比較、観測要求 | 型付きの回答 |

型は原始データ、生成対象、写像、条件の検査結果を区別する。
`VerifiedMap`、`Cocycle`、`ExactSequence` のような成立条件付きの型は、
核の構成・検査だけが生成できる。Law の宣言も、これらの値を直接返せない。

```text
type    ::= Finite(name) | Q | Product(type, type)
          | Set(type) | Term(type, type) | PresentedModule | Map(type, type)
term    ::= variable | mathematical_constant | primitive_field(variable)
          | builtin(term, ...) | compose(term, term)
domain  ::= atoms(predicate) | derive(expression) | product(domain, domain)
equation ::= forall variables in domain : term = term
query   ::= evaluate(equation) | solve(equation_family)
          | compare(reading, reading) | distinguish(reading, equation)
```

これは抽象構文の設計であり、具体的な区切り文字などは [未決事項](decisions.md#3-未決事項)
で扱う。有限な関係の閉包と、無限に続きうる操作語の生成は別の型・評価方式にする。

### 3.2 Law に書く値

Law に書く定数は、係数環の定数、仕様上の閾値、語彙の列挙値など、事前に選択する規則の値である。
今回観測した件数、特定 subject の ID、ソースパス、対象固有の表や分割は書かない。
「subject ごと」「操作の始域と終域ごと」のような量化から、対象固有の値を A から束縛する。
規則を観測値に合わせて変えた場合は別の L の解析であり、元の解析を上書きしない。

Law は module の import とパラメータ化を認める。import を含む意味内容を L に固定する。
パラメータは型・数学定数・宣言された規則に限り、対象を見て答えを返す callback や
任意プログラム、ネットワーク取得、計算済み結果の読込みは持たない。
組込み演算の意味はエンジンの仕様版に固定し、実行ごとの拡張コードを第三入力にしない。

### 3.3 評価と不完全な情報

初期の決定可能な部分は、有限関係の計算、有限域の全列挙、有理アフィン式の正規化、
有理数行列の正確な消去である。有理数の値域は有限でなくても、有限表示の線形問題は解ける。
浮動小数点近似の零を方程式成立と同一視しない。

結果を次のように型付けする。`Established` は、必ず対象・Law・量化域とともに返す。

| 結果 | 意味 |
| --- | --- |
| `Established(value, derivation, scope)` | 方程式成立または構成結果を導出した |
| `Refuted(counterexample, derivation, scope)` | 具体的な反例または不成立証拠を導出した |
| `Undetermined(reason, missing_observations)` | 入力不足、対応する算法なし、予算中断などで問いを決定していない |
| `InvalidInput(location, reason)` | 型や参照などが入力の提示規則を満たしていない |

未観測を零・空集合・偽へ補完しない。量化域は「提示された有限モデル」と
「その外を含む観測対象」を区別する。前者を全列挙した成立はそのモデルに関する成立である。
後者の情報が欠ける問いは沈黙する。全実装を観測したという Boolean を受け取って
沈黙を成立へ変える機能は置かない。

存在が記録された対象の必須 operand が欠けている場合、その対象を join や量化域から
黙って落とさない。対象を保持したまま不足を伝播する。適用条件の判定自体に不足があれば、
条件を偽とせず、その Law instance の適用可否を未決とする。

有限モデルでの空の全称命題は論理上の成立として返し、評価件数0も返す。
Law が対象の存在を必要とする場合は別の存在条件を同時に評価する。
部分的に得た反例は有効なまま返せるが、探索中断を解なしの証拠にしない。

## 4. 共通構造を生成する順序

### 4.1 Configuration と操作

A の family と L の composition reading から
`C = (F, relation, identification)` を構成する。relation と identification の
生成元は原始事実、閉包は L の規則から得る。識別の同値閉包と、操作の合成を区別する。
生成物には、用いた Atom と規則への参照を付ける。

操作は始域・終域の名前だけではなく、実際の Atom map を持つ。
family・relation・identification の保存を計算できたものだけを
`ConfigurationHom` として扱う。Law 保存は追加の条件として別に検査する。
Atom を削除する変更は、保存される部分 C を介する `A ← C → B` または snapshot 間の比較で表す。

core は生成操作の恒等・合成に閉じた対象族を意味する。計算時は有限な項として遅延生成する。
深さ制限で列挙した部分を core 全体と同一視しない。
任意の操作語の同値判定が必要なら、対応する正規化・決定手続きの存在を確認する。

### 4.2 Context、Cover、重なり

1. L の式を A に適用し、各方程式・操作・observable の自由変数と原始 support を求める。
2. 読める部分構造を、support・axis・observable の三成分を持つ context として生成する。
   最初の有限部分では support と有限 observable 座標の制限を用いる。
3. 制限写像を生成し、恒等・合成を検査する。重なりは二つの context の同じ基底への
   写像から pullback として構成する。集合の交差を使う箇所は包含写像の有限モデルに限る。
4. 方程式、signature、相互作用が要求する support を求め、それらを読める patch または
   overlap で覆う族を生成する。必要なら support を追加して equation-closure cover を作る。
5. 生成する topology と、個々の定理が要求する adequate cover の条件を別に扱う。
   cover の候補を列挙しただけで層条件や acyclicity が成立したとはしない。

基底 context 自身を含めれば被覆できる場合でも、その自明な cover だけで局所から大域への
診断を済ませない。L が選んだ局所生成規則に従う cover と、必要な support の閉包を出力する。
分割の単位はファイルやサービスの名前に固定しない。

### 4.3 方程式、係数、診断

各 Law は equation index・役割・observable の制限・symbolic coordinate `ν`・
object-dependent residual `ε` に展開する。充足は `ε = 0` から計算する。
`ν` が生成する ideal で `ν` 自身を零にして充足とする計算は採用しない。

係数は L の規則を原始生成元と関係へ適用して構成する。例えば
`Q^(generators(W)) / span(relations(W))` と、原始写像から誘導する制限で表す。
関係が制限で保存されることを検査してから商上の写像を作る。
cochain の基底と微分は、この係数・制限・incidence から生成し、`d¹d⁰ = 0` を検査する。
この後に kernel、image、商、対象に対応する cocycle の類を計算する。

`H¹` という空間の次元と、対象の具体的な障害類の零・非零は別の出力にする。
repair を返すときは、存在判定に加えて実際の候補を作り、元の方程式へ代入して確かめる。
意味側の actual repair を名乗るには、意味状態との対応と貼り合わせの条件も必要になる。

## 5. 出力と再利用

結果は単一スコアでなく、対象・射・方程式・残差・障害類・証人を持つ型付きの構造で返す。

```text
ResultNode = (type, value, support, rule_ref, dependencies, conditions, scope)
```

`support` は Atom の集合または有限式、`dependencies` は計算の有向非巡回グラフである。
各根は A の事実、L の宣言、意味が固定された組込み演算のいずれかへ到達する。
条件ごとに「導出済み」「反証」「未決」と、その証拠を保持する。

同一評価中では、この型付きノードを直接次の算法へ渡す。別の評価から持ち込む結果は
便宜的な再利用候補であり、現在の A と L に対して根から再導出または各推論を再検査する。
digest や `verified: true` だけを信用しない。再検査できなければ通常の導出を行う。
外部の証明や解を与えることで、本来の入力から出なかった結論を得る経路は作らない。

Atom・Law・組込み意味の版が変われば、依存が変わるノードの結果を更新する。
説明文、図、ArchView 表示、FieldSig への受渡しはこの構造を読む。
LLM による説明文の再解釈を計算間の接続に使わない。

## 6. 手で確かめられる一周

三つの数量表現 `p,q,r` と、それらの間の加算操作を考える。
各操作の式は、対象の仕様または実装に記述された原始事実として A に置く。

```text
subject(p)                 subject(q)                 subject(r)
translation(a, p, q, 1)    translation(b, q, r, 1)    translation(c, p, r, 3)
```

各 `translation(e,u,v,k)` は、単一事実である `translation_operation(e)`、
`source(e,u)`、`target(e,v)`、`shift(e,k)` の四つの Atom の略記である。
存在する操作の集合は `translation_operation` から作る。
その端点と式 `x ↦ x + k` に必要な値は別々に読み、不足しても操作自身を集合から除かない。
入力に「三角形」「不整合」「障害」「局所 context」「修復可能性」はない。
L は対象名に依存しない次の宣言を持つ。

```text
vocabulary translation_operation(op)
vocabulary source(op, quantity), target(op, quantity), shift(op, value: Q)
derive translations = atoms(translation_operation)
derive composable_pairs = join translations on first.target = second.source
derive triangles = join composable_pairs with direct edge on both endpoints
context operation_support = each operation with its endpoints and expression
coefficient scalar = Q
law path_preservation required:
  forall (first, second, direct) in triangles:
    compose(term(second), term(first)) = term(direct)
query coordinate_compatibility:
  solve forall e in translations:
    coordinate(target(e)) - coordinate(source(e)) = shift(e)
reading coordinate_descent:
  coordinate_compatibility の局所解と同次係数を operation_support 上で比較
```

核は端点の join から `(a,b,c)` を求め、合成式 `x+2` と直接式 `x+3` を作る。
残差は `-1`、反例は例えば `x=0` での `2 ≠ 3` である。
各操作の support から三つの context を作り、端点上の重なりを導出する。

座標の整合問題では、核が次の行列と右辺を作る。

```text
         p   q   r
D = [  -1   1   0  ]     b = [1]
    [   0  -1   1  ]         [1]
    [  -1   0   1  ]         [3]

λ = (1, 1, -1)
λ D = 0,  λ b = -1
```

したがって `Dz=b` は解を持たない。`λ` は核が消去から求める不成立証拠である。
`c` の原始 shift を `2` に変えた候補では、核が `z=(0,1,2)` を作って代入確認できる。
`shift(c,3)` だけが欠けている入力では、c の存在と端点は残るため、
三角形と c に関する方程式を保持したまま、その値の追加観測を要求する。

この線形計算から[局所・大域計算の具体例](local_global_example.md)へ進む。
上の局所化と係数の読みを一般規則として展開し、同じ Atom から cover、係数、制限、
Čech 微分、具体的障害類を作り、元の D との比較と大域座標への貼り合わせを構成する。
SAGA の意味状態との対応は、それらに加えて別途構成する対象である。

## 7. AAT の主要成果へ接続する構造

拡張は新しい結論欄を増やす方法ではなく、原始構成・演算・比較を追加する方法で行う。
数学本文の一般定理と、計算可能な有限表示との対応を、それぞれの拡張で明示する。

| 成果・問い | 保持する構造と核の仕事 | 適用前に確認する条件 |
| --- | --- | --- |
| AAT core、操作の比較 | configuration と実際の Atom map、操作語、equation・signature reading | family・relation・identification の保存、reading 間の可換性 |
| Law algebra、lawful locus | observable ring、`ν` と `ε`、ideal・局所化の有限表示 | 制限との可換性、residual と零点条件の対応 |
| Čech 障害と局所・大域 | context category、overlap、係数、具体的 cocycle、微分 | cover adequacy、係数の層条件、対象の cocycle 条件 |
| Atlas、解像度比較 | 粗細 reading、係数写像、cochain map、核・余核 | Law の十分性、support と被覆の比較、微分との可換性、診断保存条件 |
| SAGA、意味的修復 | 意味側と方程式側の生成元・関係を独立構成、比較写像、局所解 | presentation exactness、state correspondence、torsor・層条件、大域貼り合わせ |
| 輸送・基底変換・合成 | 型付きの射、引戻し、合成と比較の可換図式 | 始域・終域、許容条件、恒等・合成・pasting の保存 |
| 正規化・再構成 | 忘却する情報、操作の表示、再構成写像 | 正規化前後の評価対応、保存・反映、再構成の一意性・普遍性 |
| protocol holonomy、非可換な lifting | 操作群・groupoid、経路語、作用、関係 | 関係の充足、lift と作用の保存。可換群の rank 計算と区別する |
| 最小観測・相対修復 | 候補族、観測写像、固定部分、修復の合成 | Law 評価の識別、全候補での十分性、固定部分と合成条件の保存 |
| Atlas 欠損の合成・係数・fiber 分解 | incidence の各出現、平行辺、loop、退化、係数写像、錐 | 鎖写像、符号、順像・fiber 構成と完全列の適用条件 |

最初の core representation は、射を端点だけへ、incidence を集合の所属だけへ潰さない。
同じ端点を持つ異なる射、同じ面に現れる辺の重複、退化の符号を保持できる型にする。
基礎実装の support poset を、一般の context category の全機能と見なさない。
非可換係数、torsor、higher structure は固有の演算を追加する。数値スコアへの変換で代用しない。

数学上の条件を実装がまだ導出できない拡張は、その条件を未決として返す。
利用者に証明済みフラグを書かせて適用可能にする設計は取らない。

## 8. 根拠資料と設計上の読み

| 根拠 | この設計で具体化する内容 |
| --- | --- |
| [製品コンセプト](../archsig_v0_6_0_concept.md) §§2–4・7 | 二入力、導出の連鎖、候補と射の区別、DSL、言語独立、数学との対応 |
| [AAT 第I部](../../aat/algebraic_geometric_theory/part_1_atoms_objects_laws.md) 定義1.1、§§4–7、定義10.2・10.4A、定理10.5、原則10.6 | Atom、configuration、equation residual、実際の configuration map、生成 core |
| [AAT 第II部](../../aat/algebraic_geometric_theory/part_2_architecture_geometry_sites_sheaves.md) §§3–7 | Context、pullback overlap、coverage requirements、generated topology と adequacy |
| [AAT 第III部](../../aat/algebraic_geometric_theory/part_3_law_algebra_obstruction_ideal_lawful_locus.md) | Law algebra、ideal、lawful locus の接続条件 |
| [AAT 第IV部](../../aat/algebraic_geometric_theory/part_4_obstruction_cohomology.md) §§2–5 | 係数、Čech complex、具体的障害類 |
| [AAT 第X部](../../aat/algebraic_geometric_theory/part_10_semantic_repair_descent_saga.md) §§3–8・10 | 原始生成元からの両側構成、SAGA 比較、actual repair、有限行列による確認 |

研究上の具体的な拡張接続点と、採否の判断は [設計判断](decisions.md) にまとめる。
