# Law DSL の具体構文と意味

## 1. Document と module

唯一の具体構文は JSON の宣言と prefix array 式である。別のテキスト DSL、例ごとの
専用 YAML、外部スクリプトを併設しない。位置はファイル名と JSON Pointer で指定する。

```text
Law = {format:"archsig.law/1", semantics:"archsig/0.6.0",
       entry:Id, modules:Module[]}
Module = {id:Id, imports:Import[], roles:Id[], declarations:Declaration[]}
Import = {module:Id, digest:Digest, as:Id}
Declaration = Sort | Data | Predicate | Def | Query
Sort = {kind:"sort", name:Id}
Data = {kind:"data", name:Id, constructors:[{name:Id, fields:PrimitiveType[]}, ...]}
Predicate = {kind:"predicate", name:Id, domain:QName, payload:PrimitiveType,
             atom_kind:Id, axis:Id, meaning:String}
Def = {kind:"pure"|"derive", name:Id, params:[{name:Id,type:Type}, ...],
       result:Type, body:Expr}
Query = {kind:"query", name:Id, result:Type, body:Expr}
```

各 module は全宣言を同時に名前解決する。sort と data は [原始型](inputs.md#3-原始型と値の唯一の-encoding)
を定める。predicate は観測される一つの使用上の事実を定め、meaning は非空の説明。
meaning の文章を評価器は解釈しない。predicate/domain/payload は kernel が検査する。
`atom_kind` と `axis` は module 内で一意に解釈する語彙名であり、完全修飾して結果へ保持する。

module digest はその module object の canonical JSON の SHA-256。
imports の参照グラフは非巡回、digest 一致を必須とする。alias は module 内だけで有効。
完全名または import alias/name を名前解決し、digest を固定した完全名へ展開する。
自己 import、同じ alias、衝突する宣言名、未収載 module は不正入力。alias と同梱module IDの衝突も禁止。参照できるのは自分と直接importしたmoduleだけ。roleもmodule/nameへ完全修飾する。
組込みは予約 module `core`。modules/roles の順は無意味。declarations は名前順に正規化する。
entry は query を公開する module。entry に query は1件以上必須。
他 module の query を公開するには entry の query body で参照する。

パラメータ化は型付き関数の params で行う。module の実行時引数や CLI の意味引数はない。
同じ規則を異なる型へ適用するには原始 data/型を共有するか、明示した型で def を定義する。
組込みの多相変数 T/K は署名中だけの記法で、利用者定義は明示的な単相型とする。

## 2. Expr の完全な文法

以下の `name`、`x`、`tag`、`qname` は JSON string、`i` は Nat。
`E*` は0個以上、`E+` は1個以上。各形式の arity は表記通り。

```text
E ::= ["lit", Type, Value]
    | ["var", x]
    | ["let", x, E, E]
    | ["if", E, E, E]
    | ["tuple", E*]
    | ["list", Type, E*] | ["set", Type, E*]
    | ["get", i, E]
    | ["ctor", QName, tag, E*]
    | ["match", E, [[tag,[x*],E], ...]]
    | ["fn", [[x,Type], ...], E]
    | ["apply", E, E*]
    | ["call", qname, E*]
    | ["snapshots", roleQName]
    | ["subjects", sortQName, E]
    | ["field", predicateQName, E]
    | ["slot", predicateQName, E]
    | ["owner", sortQName, E]
    | ["project", field, Type, E]
    | ["state_apply", Type, E, E] | ["point_value", Type, E]
    | ["residual", K, E, E]
    | ["query", qname]
    | ["fold", dataQName, Type, E, [[tag,[x*],E], ...]]
```

それ以外の array head、object を式として使う記法、裸の数字/文字列式は不正。
`lit` は原始型とRing/TermSignatureの値だけを作れる。Ref、Term、Snapshot と導出型の literal は Law では禁止。
Ref を含む複合 literal も禁止。Term は `fn` と `core/term` で生成する。
`lit` 内 data は ground value に限る。空の集合・リストには要素型を必ず記す。

fn は字句束縛・値渡し。params に重複を許さず、shadowing を拒否する。let の x は
第4要素の式だけに束縛され、右辺から自分を参照できない。
var は直近の明示的な束縛を指す。自由変数、動的スコープ、名前の文字列組立てはない。
get は Tuple の0始まり成分投影だけであり、結果 envelope の欄を読む機能ではない。

match は data の全 constructor をちょうど一回ずつ列挙し、pattern 変数は
constructor の fields を順に束縛する。枝の型は同じ。fallthrough と wildcard はない。
fold は有限 data 値の構造再帰。各 constructor の再帰出現 D は折畳み結果型 T に置き換え、
List/Option/Tuple 内も位置を保って再帰的に置き換えた引数を枝へ渡す。
第3要素で結果型 T を明示し、全枝は同じ T を返す。data の相互再帰を禁止し、自己再帰だけを許す。入力部分木を超えて再帰する関数呼出しはない。
pure/derive/query を頂点、call/query を辺とする共通依存グラフは非巡回。反復は fold と有限の `closure` だけで記述する。
未知の有限木を fold する場合は欠測を返し、想像した tree を選ばない。

`subjects(S,s)` は snapshot s に登録された sort S の subject 全部を Set(Ref(S)) として返す。
`field(P,r)` は r の snapshot 内の P を読み、欠ければ同一性を持つ Hole を作る。
`slot(P,r)` は値を読む前のFactRefを返す。owner(S,f)はFactRefの所有subjectがsort Sならsome Ref、違えばnoneを返す。
list/set形式は明示した要素型の式を格納する。projectの公開fieldは計算カタログ§12に列挙する。
projectは要求型を明示し、対象の構造fieldの実際の型を検査する。不一致はinvalid_construction。
`subjects` により操作の存在を列挙し、field のある行だけの join に置き換えない。
`query` は同梱 query の数学的な値を参照する。query を含む循環も上記共通グラフで拒否する。
query の状態・予算・基底番号・chosen witness・provenance は Law の値に含めない。
core/decide は確定した数学的真偽だけをBoolへ写し、未決や実行状態を値へ変換しない。

## 3. 型

原始型に加えて、次の型を使う。

```text
T ::= PrimitiveType | "Snapshot" | ["Fn", [T*], T]
    | ["Tuple", T*] | ["List", T] | ["Set", T] | ["Option", T]
    | "Ring" | "TermSignature" | "FactRef" | "ContextPoint" | "Evidence"
    | "AtomSet" | "Configuration" | "Architecture" | "Operation"
    | "MapCandidate" | "ConfigurationHom" | "LawHom" | "Span" | "Core"
    | "Equation" | "EquationFamily" | "LawValues" | "SolutionSet" | "Reading"
    | "Context" | "ContextMap" | "ContextFamily" | "Cover" | "Overlap"
    | ["Module",K] | ["ModuleMap",K] | ["Vector",K] | ["AffineMap",K] | ["Complex",K]
    | ["CochainMap",K] | ["Cohomology",K] | ["Class",K] | ["CoefficientSystem",K]
    | "StateMap" | "StateSystem" | ["Descent",K] | "DiagnosticComparison" | "Repair"
    | "ObservationPlan" | "Presentation" | "Proposition"
```

K は "Q" / "Z" / ["Fp",p]。計算カタログの Module等の略記は同じKを共有する型族であり、wireでは常に ["Module",K] 等と記す。
上の名前は予約語。Set は決定可能な等値を持つ原始型、Snapshot、有限 Tuple/data と
参照 identity を持つ導出型に限る。Fn/Term の外延的等値を Set の重複検査に使わない。
List は型を満たすすべての値を保持できる。

暗黙の数値変換はない。Q と Z、異なる Fp、Ref の異なる sort は異なる型。
`core/rational` が Z→Q、`core/mod` が Z→Fp の明示的変換を行う。
型付き入力に現れる数学的な整数に machine word 上限を付けない。

構造的な型検査と、構成後の添字の検査を分ける。例えば ModuleMap は source/target Module の
identity を値として持ち、合成時に中間 Module が一致する必要がある。
型が ModuleMap 同士でも形が合わない合成は `invalid_construction` という
有効 query の未決理由になる。これを偽の数学命題として返さない。
コンパイル時に確定する arity/型/参照違反は入力全体の `invalid_input`。

`ConfigurationHom`、`LawHom`、`Cover`、`CochainMap`、`Class`、`Repair` 等は
sealed な型である。ctor/lit はこれらを作れない。指定演算が構成条件を検査して作る。
検査条件が成立しない場合、条件の反証と元の候補を保持し、sealed 値を出さない。

## 4. 純粋関数と導出

pure は原始値の全域関数。params/result は原始型だけに限定し、Fn引数・Fn返り値を禁止する。純粋演算、他の pure、型に適合する fold だけを呼べる。局所fnは利用できるが、その自由変数とbodyも純粋部分の型・効果で検査する。
derive は原始値・snapshot・導出型を扱い、全カタログを使える。
pure の中から field/snapshots/subjects/query/derive を参照することは型検査違反。原始Term内も同じ効果制限。slot/owner/project/state_apply/point_value/residualもpure内で禁止する。
関数値は外部 callback でなく、この閉じた Expr 文法の lambda だけである。

call は署名の引数型と arity に一致する必要がある。組込みの型変数は引数の一致から一意に
解決する。解決できなければ型エラー。曖昧な overloading、演算子の優先順位はない。
同じ端点を持つ異なる操作を一つにする暗黙の coercion はない。

## 5. 問い、命題、方程式

query は body の型を result に明記する。Propositionの値は命題の式そのものであり、
node.state=valueだけではその命題の真を意味しない。queryまたはdecideが真偽を評価する。result が Proposition なら、成立を
`established`、偽を `refuted`、決定していない場合を `undetermined` として返す。
他の型では、その値の構成が完了すると `established`。
空の SolutionSet は正常な値であり、解の存在は `core/inhabited` で別に問う。
Bool 値 false も正常な値である。利用者に反証を返す要求には `core/proposition` で
Bool を命題へ埋め込むか、カタログの命題生成演算を使う。

Equation は型付きの二項、有限 instance index、役割を持つ。
役割は `required`（満たすべき要件）または `definition`（構成を定める方程式）。
definition を前提として required を証明する際は、解集合への制限を出力に残す。
required を入力型の不変条件にして、違反する入力を消さない。
`core/equation` と `core/equations` の意味はカタログにある。

`forall`/`exists` は提示された有限集合上の量化。
Q/Z/Fp の全代入に関する式は Term / AffineMap / EquationFamily の記号的変数で表す。
有限候補族を全探索した結果を、任意の未提示候補についての結論へ拡張しない。
不完全な無限操作語の探索から「射がない」「修復がない」を返さない。

## 6. 欠測の評価規則

意味は既知の原始事実を保つ型付き補完 `Comp(A)` における評価で定める。
量化変数、解として求める未知数、未観測 Hole は別の名前空間である。
Hole は solve の自由変数に取り込まない。補完を選んで成功することと、現在の入力からの
確定を分ける。出力には依存 Hole と、どの命題/構成がそれを必要としたかを残す。

必須の最小評価規則は次の通り。

1. 既知の純粋値を通常評価する。未評価部分を持つ tuple/list は成分ごとの導出を保持する。
2. if の条件が既知なら選ばれた枝だけを評価する。未知なら両枝の同一値が既に導出できる
   場合だけその値を返し、それ以外は条件に依存する欠測として返す。
3. filter の guard が未知なら、その要素を除去しない。結果 Set 全体は未決だが、
   既知の要素・候補要素・guard の依存を導出ノードに残す。
4. forall は有限な全 instance が成立した場合に成立、一つの確定した偽 instance が
   あれば反証。exists は双対。未知 guard の instance は未知のまま保持する。
5. Q 上の同一 Hole を含むアフィン式は係数正規化する。`h-h=0` は成立する。
   `2-h=0` は係数が非零というだけでは反証しない。すべての補完で偽と確認できる
   定数非零式だけを反証する。有限型の Hole は全補完を列挙して一致を確認してよい。
6. 上記以外の欠測を含む構成は保守的に `missing_observation` とする。
   完全入力用算法を欠測へ適用して零・空・任意の特解へ置換しない。

補完対を返すときは、型と既知値を保つ二つの完全な補完、および異なる評価結果を核が検査する。
補完の不一致は現在の入力についての `undetermined` の説明であり、観測した実装の反例ではない。
Hole の型内に Ref があるとき、その範囲は A の全snapshotに宣言済みの同sort subjects。同snapshotである要件はLawで別に検査する。
query が到達した必須 Ref の Hole の参照先 sort が空で補完がない場合、そのqueryを `undetermined/inconsistent_observation` とする。未使用predicateはこの検査に含めない。
これは空集合上の全称成立ではない。Option/List の空値は補完として使用できる。

## 7. 計算結果の接続と選択

Law の def/query 参照は同じ意味値を次の構成へ渡す。出力の文章や結果ファイルの path を
読み直す演算はない。sealed 値が未構成なら依存条件を次の query に伝播する。
独立した query は実行を継続する。

solve は解集合、kernel は部分加群、cohomology は商と写像を返す。
特解・行列基底・代表元はその表示であり、Law から「最初の基底」を読んで分岐できない。
求めたい値は解集合上の関数/全称/存在、または原始の意味ある順序を与えた有限探索で定義する。
診断用に選んだ局所解の差は、商類として選択に依存しないことを検査してから返す。
名前を並べ替えても意味値は構成した同型に沿って対応する。

## 8. エンジン自身を表す

data で `Var/Lit/Add` 等の有限構文木を宣言し、predicate に source tree、候補変換規則、
型、子参照、対応する declaration を記録する。fold によって source の参照解釈と
変換後 tree の解釈を別々に定義する。生成した affine term を全代入で比較する。
この経路には compiler 専用の入力書式・外部評価 callback を追加しない。

L01–L13 は [自己 Law](../archsig_atom_law_engine/engine_laws.md) が定める製品要求。
各有限 instance の検査は通常の query、全入力に関する評価器の健全性は
[数学への接続](math_obligations.md)で扱う。自己評価した成功ラベルを
ArchMap に戻して核の正しさを仮定する経路を設けない。

## 9. 構成した対象の identity

導出対象のidentityは、semantics、constructor名、型、引数の意味identityから構造的に定める。
Fn/Termは束縛変数を位置へ変えたα正規形とcaptureのidentityを使う。同じ構成の再呼出しは
同じidentity、異なる構成で同型な対象は別identityであり、明示的な写像で比較する。
原始Refは(snapshot,subject)、FactRefは原始位置、操作生成元の名前は原始Refを含む。
node番号、provenance、表示基底、便宜的な証人、cacheはidentityに含めない。
identityのhashは索引だけに使い、衝突時は構造を比較する。
