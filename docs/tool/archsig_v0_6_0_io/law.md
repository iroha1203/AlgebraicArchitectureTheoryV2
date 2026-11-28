# Law の宣言言語

Law ファイルは、Atom 定義への参照と読みを `reading` にまとめる。個々の `law` は、
適用先・役割・原式を持つ条件である。`view` は型付きの値を読む。
問いは [CLI](execution.md) で選ぶ。宣言から対象・写像・方程式・局所状態を生成し、
その意味・型・構造と数学の適用条件を検査する責務は ArchSig にある。

作者は定義された語彙を参照し、値の読み方、要求、公開する局所情報、許す変更を宣言する。
短い条件も構造再帰を使う意味定義も、この同じ言語の型付き宣言として扱う。
核は宣言と ArchMap から cover、行列、複体などの標準の構成を生成する。
エンジンは問いに必要な依存関係と算法から実行計画を作り、solver の適用と実行順を決める。
構成の意味は [核の構成](computations.md)、実行計画と結果の確認は
[実行仕様](execution.md)と[型付き結果](results.md)に従う。

## 1. ファイル、名前、再利用

```text
law "archsig.law/2" semantics "archsig/0.6.0";
reading Reservations {
  use vocabulary Reservations version "1" digest "sha256:8427a2712c22d6eed1cdd5f48258bea102904173558a7087bb82c7d95665c9ff";
  view holdings(s: State): (Z, Z) = (s.free, s.held);
  law required conserved(e: Reserve):
    e.to.free + e.to.held = e.from.free + e.from.held;
  law required retained(m: Migration):
    forall s in State[m.from] . holdings(m.states(s)) = holdings(s);
  local Stock(s: State) reads s.free;
  local Held(s: State) reads s.held;
  local Transfer(e: Reserve) reads holdings(e.from), holdings(e.to);
  change rebalance(s: State, d: Z) =
    s with { free = s.free - d, held = s.held + d };
}
```

ファイルは UTF-8、BOM なし。識別子は `[A-Za-z][A-Za-z0-9_]*`、case-sensitive。
空白と `//` から改行までのコメントは token 間で無視する。文字列は JSON の string 文法で、
不正 UTF-8・unpaired surrogate を拒否し、Unicode 正規化をしない。
予約語は `law semantics reading use vocabulary version digest as entity arrow correspondence align data view required
optional local reads change relation when let in if then else match forall exists not implies or
and with true false unit list set where none some fn` と組込み型名である。
予約語は宣言名・束縛名に使えない。`owner from to` は field 名として使える。

一つのファイルに一つ以上の reading を置く。Law 宣言の完全名は `Reading.Declaration`。
原始型・field・constructor の完全名は [Atom 定義](definitions.md)が所有する。
reading 内では自分の宣言を短名で参照できる。`use Other as O;` は同梱 reading の別名。
`use vocabulary N version "V" digest "D";` は登録済みの Atom 定義を参照し、
その namespace の原始宣言を短名でも使えるようにする。同じ namespace の import は reading 内で一回だけ。
未使用の import・宣言も受理する。import の版・digest と、全宣言の型・参照は検査する。
署名・式で直接名指す原始 namespace は、各使用元 reading で直接 import する。
依存のある型の署名を解決するためだけの namespace は定義の依存表から解決する。

`.` 列は、束縛変数の射影を先に読み、それ以外は reading alias、自分の宣言、import した
原始宣言、完全名の候補から最長一致で解決する。複数の解決先がある短名は reference とし、
完全名で明記する。reading と namespace は同じ名前でもよいが、全宣言の完全名は一意とする。
その衝突は duplicate_id。同じ語彙を使う reading が複数あっても原始型を複製しない。

reading 間の依存グラフは非循環。同梱 reading の参照が循環する場合、view の相互呼出し、
構造再帰でない自己呼出しは cycle。原始型の依存と data の再帰は Atom 定義の検査で扱う。
再利用する reading は依存 reading とともに Law ファイルへ同梱し、参照する定義ファイルは
CLI へ明示指定する。ファイル外の探索や download はしない。
宣言順は意味を持たず、parameter と constructor の引数順は意味を持つ。
ファイル全体の版は同一。語彙の binding と digest は [Atom 定義](definitions.md#3-依存参照digest)に従う。

ファイル全体の正規化は、空白・コメントを除いた字句列を元の順に保持する。
各 token を `{kind:"name"|"string"|"integer"|"symbol",text:String}` とする。
keyword も name、string は escape を解いた値、integer は元の10進文字列、symbol は最長一致で読む。
`{semantics:"archsig/0.6.0",tokens:[...]}` の canonical JSON の SHA-256 を model_digest(L) とする。
canonical JSON は入力仕様 §4 に従う。alias・束縛名・宣言順の書換えは行わない。

### 宣言の解決と標準の意味

`check` は、元の宣言の位置を保持して名前・型・束縛を解決する。
parameter と field の型、view の戻り型、law の role は作者が明記する。
これらや局所の読取り権限を、観測値、宣言名の意味、選択した問いから推測しない。
省略を許す位置には、次の標準の意味を適用する。

| 記述 | 解決する意味 |
| --- | --- |
| 宣言の短名・alias | §1 の scope と名前解決に従う完全名 |
| `when` の省略 | Bool の `true`。body とその出現は保つ |
| reading に `local` 宣言がない | [支持による reading](computations.md#3-読取りの圏と-cover) |

これらの規則と核の標準構成は、header の `semantics "archsig/0.6.0"` によって固定する。
宣言の解決は、原始値や実行時の構成結果を補う処理とは区別する。
`check` で確認できる解決結果と標準の選択は [型付き結果](results.md)に従い、
実際の対象・局所構造・保存条件は ArchMap と問いを与えた `run` で構成する。
簡潔な記述と標準を明示した記述の対応は [適合例](validation.md#宣言の記述と意味の確認)で示す。

## 2. 宣言の文法

以下の EBNF で `[]` は省略、`{}` は反復、引用符は literal token。
`Name` は識別子、`QName` は `Name { "." Name }`、`Expr` は §4。
`Fields` は `Name ":" Type { "," Name ":" Type }`、空も許す。
原始 entity/arrow/correspondence/data は Atom 定義で記述する。

```text
Document = "law" String "semantics" String ";" Reading { Reading } ;
Reading = "reading" Name "{" { Use | VocabularyUse | Declaration } "}" ;
Use = "use" Name "as" Name ";" ;
VocabularyUse = "use" "vocabulary" Name "version" String "digest" String ";" ;
Declaration = View | Law | Local | Change | Relation | ShigureDecl ;
View = "view" Name "(" Fields ")" ":" Type "=" Expr ";" ;
Law = "law" ( "required" | "optional" ) Name "(" Fields ")"
      [ "when" Expr ] ":" Expr ";" ;
Local = "local" Name "(" Fields ")" [ "when" Expr ] "reads" Expr { "," Expr } ";" ;
Change = "change" Name "(" Fields ")" [ "when" Expr ] "=" Expr ";" ;
Relation = "relation" Name "(" Fields ")" [ "when" Expr ] ":" Expr "=" Expr ";" ;
```

relation の body は、最上位の `=` が一つの二項式として構文解析する。その左右を上の二つの
Expr とし、左右それぞれの型を Path に限定する。通常の等号と別の優先度を与えない。

原始宣言の型・所属・対応は [Atom 定義](definitions.md#2-原始宣言の意味と型)に従う。

- `view` は型付きの純粋な読取り。整数・積・有限和・集合・有限木・項等を返せる。
  戻り値を Bool や残差に限定しない。
  対象へ適用される view は [object algebra の規則](computations.md#1-対象作用law-instance)で
  signature の軸となるため、その追加は読みの追加となり得る。
  helper への分割や `let` の展開は、原式の出現や宣言の対応を変え得る。
  値の一致だけから signature や診断全体の保存を結論しない。
- `law` の guard と body は Bool。guard=true の instance に body を要求する。
  guard=false は `not_applicable` として instance を残す。guard 不明を除外しない。
  `required` を対象の Lawful 判定へ用い、`optional` も個別に検査できる。
  導出された条件の role=`derived` は結果専用であり、作者の宣言には使わない。
- `local` は束縛参照の同一性と reads の値を公開する。field の参照値から参照先の全 field を
  読めることにはしない。view を展開した依存 slot、項の左右・出現は由来として保持するが、
  依存の記録は読取り権限ではない。合計を公開しても各加数を公開せず、Tuple の成分射影は許す。
  [同梱 SKILL の実行例](../../../tools/archsig_v0.6.0/skills/archsig-observe/SKILL.md#合計と各成分を読む)で、
  合計と Tuple、固定状態と変更候補を比較できる。
- `change` の第1引数は owned entity または根 entity、残りは参照を含まない値型。
  Path と、参照を含む data/container も残りの引数型には含めない。
  結果は第1引数と同じ entity の `with` 更新である。body の結果の位置(括弧の中、if の両枝、
  let の本体)は、第1引数への `with` 更新とする。owner・参照・Map・subject roster は変更しない。
  更新式は更新前の同一環境で同時評価する。指定根内の各対象 instance へ独立に適用する。
  guard は許す parameter/状態の条件であり、欠測値を探索変数にしない。
- `relation` の両辺は同じ始終型の Path。名前付き操作列の同効果を要求する。
  核が各 instance の始終点と実作用の一致を検査してから商の作用に用いる。
  relation を先に真として評価や構造を変更しない。

## 3. 型と有限の観測族

```text
Type = "Unit" | "Bool" | "Z" | "Q" | "Text" | "Fp" "(" DecimalPrime ")"
     | QName [ "[" Name "]" ]
     | "(" Type "," Type { "," Type } ")"
     | "List" "<" Type ">" | "Set" "<" Type ">" | "Option" "<" Type ">"
     | "Map" "<" Type "," Type ">"
     | "Term" "<" "(" [ Type { "," Type } ] ")" "->" Type ">"
     | "Path" "<" QName "," QName ">" ;
```

QName は entity/arrow/correspondence または data を指す。前3種は参照型。
`State[owner]` は同じ snapshot の owner に属する State への参照型。
`State[a]` を式の有限族として使う場合は、a と同じ snapshot の登録 subject のうち owner=a のもの。
この式の型は `Set<State>` である。
未束縛の参照型 parameter の量化域は全入力 snapshot の当該型の登録 subject。
依存型の parameter は左から束縛し、その owner の族を使う。
型名だけで未知の subject を生成しない。view/field の名から owner を推測しない。

`data` は有限値ではなく有限木の型。自己参照は直接または Tuple/List/Option を通る正の出現だけ。
相互再帰、Set/Map/Term/Path を通る再帰は禁止。少なくとも一つの有限 ground value が必要。
Map の定義域・値域は参照型に限定し、既知の値はその観測族上の全域単一値関数。
Term の引数・戻り型は参照を含まない値型、body は §4 の純粋部分言語。
Path は核が原始の arrow/correspondence から構成する型で、原始 field・data・Term 内には置かない。
Set の要素型は構造的等値を有限手順で判定できる型に限定する。Term、Path、およびそれらを
data の引数・container を通して含む型を Set の要素にしない。この適格性は型検査で決定する。
項や経路の有限族は List に保持し、外延等値を問う場合は評価・比較の問いとして扱う。
結果専用の Object、ConfigurationHom、Module、Evidence 等を原始型に使えない。

型の等値は alias 展開後の名と構造で判定する。Z/Q/Fp 間の暗黙変換はない。
同じ形の data、異なる entity、異なる owner は別の型。
Z は任意精度整数、Q は既約有理数、Fp(p) は p が素数の有限体。
有限列挙できる値域は Unit/Bool/Fp、非再帰の有限 data、それらの Tuple/Option/Set、
および明示された有限 List/Set の要素。Z/Q/Text・再帰 data・長さ無制限 List は一般に無限。

## 4. 式、束縛、純粋性

```text
Expr = Let | If | Match | Quantifier | Binary ;
Let = "let" Name "=" Expr "in" Expr ;
If = "if" Expr "then" Expr "else" Expr ;
Match = "match" Expr "{" Arm { Arm } "}" ;
Arm = Pattern "=>" Expr ";" ;
Pattern = "_" | Name | QName [ "(" Pattern { "," Pattern } ")" ] ;
Quantifier = ( "forall" | "exists" ) Name ( "in" Expr | ":" Type ) "." Expr ;
Binary = Unary { BinaryOp Unary } ;
Unary = ( "not" | "-" ) Unary | Postfix ;
Postfix = Primary { "." Name | "." Nat | "(" [ Expr { "," Expr } ] ")" }
          [ "with" "{" Name "=" Expr { "," Name "=" Expr } "}" ] ;
Primary = Name | QName | "then" | Integer | String | "true" | "false" | "unit"
        | "(" Expr ")" | "(" Expr "," Expr { "," Expr } ")"
        | "list" "<" Type ">" "[" [ Expr { "," Expr } ] "]"
        | "set" "<" Type ">" "{" [ Expr { "," Expr } ] "}"
        | ( "list" | "set" ) "{" Expr "|" Name "in" Expr [ "where" Expr ] "}"
        | "none" "<" Type ">" | "some" "(" Expr ")"
        | "fn" "(" Fields ")" "=>" Expr
        | QName "[" Expr "]" ;
```

BinaryOp は低い優先度から `implies`、`or`、`and`、`= != < <= > >= in`、`+ -`、`*`。
implies は右結合、他の算術・論理は左結合、比較の連鎖は禁止。単項は二項より強い。
Integer は `0|[1-9][0-9]*`、負号は単項演算。整数 literal は期待型 Z/Q/Fp の値、
期待型がないとき Z。Fp では 0..p−1 の範囲を検査する。Q の非整数は `rat(n,d)` で書く。
Nat は tuple の0始まり射影だけに使用する。`.` に続く数値と完全名の構文を区別する。
式に ArchMap の subject ID・snapshot ID・結果参照を書く構文はない。

文法の区切りは次のように読む。let の右辺の最上位にある `in` は二項演算でなく let の区切りとする。
change の guard と body は、宣言の最上位の `=` を後ろから順に試し、guard と body がどちらも読める
位置で区切る。
量化の `.` は、最上位の `.` のうち前を域(型)、後を本体として読め、本体が最も遠くまで読めるものから、
`in` の右辺が List/Set の型を持つ位置、または `:` の右辺が型になる位置を選ぶ。
そのような位置が複数あるときは、名前の最長一致と同じく、域(型)が最も長い位置を選ぶ。

束縛は lexical。parameter、let、pattern、量化、comprehension の同一 scope 内の名は一意。
内側の shadowing は禁止。let の右辺に自分を参照できない。match は constructor を全て一度ずつ
覆うか末尾に `_` を置き、重複・到達不能分岐を拒否する。constructor は完全名、`Data.Ctor`、
期待 data 型から一意な短名の順で解決する。変数名と衝突する短名は修飾する。
束縛変数でない一つの名前は、期待 data 型の constructor 名ならその constructor と読む。
二項演算の両辺、if の両枝、match の各枝では、文脈の型を要しない側(整数 literal や短い
constructor 名だけでない側)の型を、文脈の型を要する側の期待型とする。両方が要するときは左から読む。
pattern の名前は、照合する data 型の constructor 名ならその constructor、それ以外は新しい束縛とする。
同じ名前の束縛変数があるとき、constructor は pattern でも修飾して書く。
data 型でない値の match は `_` と束縛の分岐で受ける。
constructor が一つの data への入れ子の pattern は、その引数の pattern が全て値を残さず受けるとき、
外側の constructor の分岐を覆う。末尾の `_` を到達不能とするのは、全 constructor の分岐の引数が
`_` か束縛だけの場合とする。
全分岐を型検査し、if の両枝・match の各枝の結果型を一致させる。

`list{e | x in xs where p}` は有限 List/Set の各要素を `x` に束縛し、`p` が真なら `e` を一つ追加する。
filter の省略は全要素を採用する。filter の型は Bool。List を読むときは位置順で、同じ個体が複数の位置に
あれば各位置を数える。Set を読むときは元の要素を各一回読み、要素内の Set/Map も正規化した
値の canonical JSON を UTF-8 バイト辞書順に並べる。別個体から等しい値が得られても List の各位置に残る。
`set{...}` では結果を Set の外延等値でまとめる。
空の結果でも要素型は `e` の型。必要な filter が未知、または採用した要素の値が未知なら、結果の List/Set も
未知として元の欠測を保持する。filter が偽なら、その位置の `e` は読まない。

例えば `Cell[w]` が owner `w` の Cell の族で、`quantity:Q`、`stock:Stock` なら、
`sum(list{b.quantity | b in Cell[w] where b.stock=s})` は stock `s` に属する各 Cell の数量を足す。
数量 `rat(1,2)` の異なる2個体は合わせて `rat(1,1)` になり、該当個体が0なら型 Q の零になる。

field lookup は宣言済みの field だけ。tuple は数値射影だけ。適用は view、Map、Term、constructor、
以下の固定演算だけ。関数の名前や文字列から外部 code を実行しない。
ドット列は、先頭が束縛変数ならその field 射影として読む。それ以外は alias 展開後の
宣言完全名を最長一致で解決し、残りを射影として読む。予約語 `then` はこの合成演算の
適用位置だけで Primary となる。組込み演算名は宣言・束縛名として再定義できない。
reading・別名・constructor・field の名には組込み演算名を使える。

| 演算 | 型と意味 |
| --- | --- |
| `+ - *`、単項 `-` | 同じ Z/Q/Fp 上の正確な演算。Tuple では同じ形の数値成分へ成分ごとに適用 |
| `= !=` | 同じ型の構造的・数学的等値。Set は外延、Map は同じ域上の値、Term/Path は下記 |
| `< <= > >=` | Z/Q の順序。Fp・Text へは適用しない |
| `and or not implies` | Bool。未知への規則は §6 |
| `rat(n,d)` | 整数 literal n,d、d>0。既約化して Q |
| `count(xs)` | 有限 List/Set の長さを Z で返す |
| `sum(xs)` | 同じ数値型の有限 List/Set の和。空でも要素型を保持 |
| `x in xs` | 有限 List/Set の要素所属 |
| `path(e)`、`identity(x)`、`then(p,q)` | arrow/correspondence の1段、根/entity の空経路、順に合成。始終点を検査 |
| `source(p)`、`target(p)` | Path の端点参照 |

Map は値を記録した表、Term は閉じた有限式を適用する。
`fn` は Term を構成し、その parameter 以外の変数・field・参照族をキャプチャしない。
Term body は原始値の演算と data constructor だけを呼べる。参照・field・観測族・Path・with・
名前付き view の呼出しを含めない。観測 Term の body も同じ規則で検査する。
view は非循環な相互呼出しを許し、自己再帰は一つの data parameter の match で得た
直接の再帰 subterm に対する呼出しだけを許す。他引数で終端性を損なう再帰は導入しない。
構造再帰の引数は宣言の左端の data parameter とし、それ以外を再帰の減少尺度にしない。
有限木の評価は必須。未観測の tree 全体を有限と見なして値を推測しない。
`with` は change の body だけに置ける。対象生成・cover・係数・複体・solver の呼出しを
view へ入れる構文はない。

Term の `=` は関数外延の等値、Path の `=` は始終点と実作用の等値であり、
構文木や名前の一致だけで不等としない。有限全列挙・アフィン正規化で決められない場合は
その比較を `unsupported_algorithm` とする。経路の語そのものと、relation が生成する同値は
[compare の選択](execution.md)で別に扱う。無効な端点の then は `condition_failed`。

## 5. Law の表示と適用

未束縛の Law parameter は、その型・依存族で全称化する。scalar parameter の無限全称も
構文として保持し、[必須算法と非対応](computations.md)を区別する。
CLI による一部の parameter の束縛は、その instance を選ぶ。
`forall/exists x in xs` は xs の要素域、`x:T` は T の意味上の全域を量化する。
空の有限域では forall=true、exists=false で、件数0と域の型を結果に残す。
型検査を空域のために省略しない。

Law の識別は完全名、role、束縛、guard、原式、AST 内位置の組である。
同じ値や等価な式を持つ出現を潰さない。等号では型付きの両辺と評価値を残し、
数値等号には成分ごとの差を添える。一般の Bool 条件を一律に整数残差へ変換しない。

方程式 realization の生成規則は [核の構成](computations.md)に従う。
記号座標 ν、評価 ε、条件の真偽、witness ideal と required の obstruction ideal は
異なる値である。要求を先に満たすように対象を商にしたり、評価結果から原式を置き換えたりしない。

## 6. 未観測の意味

未観測 slot は [ArchMap](inputs.md) の identity と型を持つ。同じ slot の読取りは同じ未知変数、
別の slot は別の未知変数である。意味は既知値・subject・型・参照条件を保つ全補完にわたる。
補完には Law の成立を条件として課さない。

値が全補完で同じなら確定値、命題が全補完で真なら established、全補完で偽なら refuted。
適用状態も全補完で一致する場合に確定する。すべて適用なら `applicable`、すべて不適用なら
`not_applicable`、適用状態が混在するか未決なら `undetermined` とする。
この確認を完了できなければ依存 slot と理由を保持する。if/guard/所有者が不明なら、
複数の分岐・族を条件付きで保持し、一方を暗黙に除外しない。
Bool の false and x、true or x、同じ未知整数 h の h−h は補完によらず確定できる。
全称に既知の反例が一つあれば他 instance の欠測によらず反証できる。

原始参照・有限型の補完は有限列挙、数値アフィンの相関は記号的に保持することを必須とする。
それ以外の補完を必要とする問いは未観測箇所を明示し、対応する算法がなければその理由も付す。
未観測値の全補完が空になる提示は `inconsistent_observation` として拒否し、空虚な成立を返さない。
change の自由 parameter と未観測 slot は異なる。修復・探索で後者を決定変数にしない。

## 7. SHIGURE 宣言（原始表示・比較・変更仕様・評価条件・タスク・図式・経路・移送・複数解釈族・変形障害・診断層・Atlas・出現同定・部分提示・改訂・多源衝突）

`reading` 本体の中に、文脈キーワード `shigure` で始まる 20 種類の宣言を置ける。
`shigure` は予約語一覧へ追加しないため、既存の宣言名・view 名・変数名と衝突しない。
通常の `view` / `law` / `local` / `change` / `relation` 宣言と同一 `reading` 内で共存できる。

```text
ShigureDecl ::=
  "shigure" (ShigurePresentation | ShigureComparison | ShigureChangeSpec
           | ShigureEvalCondition | ShigureTask
           | ShigureDiagram | ShigurePath | ShigureTransfer
           | ShigureFamily | ShigureRobustness | ShigureChevalley | ShigureObservations
           | ShigureLift | ShigureArtin | ShigureDiagnostics | ShigureAtlas
           | ShigureOccurrence | ShigurePartial | ShigureRevision | ShigureMultisource)

ShigureDirection ::= "state_map" | "time_order"

ShigureScalarLit ::=
    ("-")? Integer
  | "rat" "(" ("-")? Integer "," Integer ")"
  | "fp" "(" Integer "," Integer ")"

ShigureMorphismClause ::=
    "comparison" QName ";"
  | "identity" ";"
  | ( "state_map" Name "->" Name "{" (Name "=" PolyExpr ";")* "}"
    | "translate" Name "->" ShigureWordExpr ";" )+

ShigureWordExpr ::=
  "[" (Name "(" (PolyExpr ("," PolyExpr)*)? ")"
    ("," Name "(" (PolyExpr ("," PolyExpr)*)? ")")*)? "]"

ShigureLawClause ::=
  ("semantic" | "required" | "representation") Name ":" PolyExpr "=" PolyExpr ";"

ShigurePresentation ::= "presentation" Name "{"
  "domain" ("Z" | "Q" | "Fp" "(" Integer ")") ";"
  ("sort" Name ("rank" Integer)? ";")*
  ("phase" Name "{"
    ("coord" Name ":" Name ("observed" QName)? ";")*
    ("law" ShigureLawClause)*
  "}")*
  (("op" | "operation") Name "(" (Name ":" Name ("," Name ":" Name)*)? ")" ":" Name "->" Name "{"
    ("law" ShigureLawClause)*
    (Name "=" PolyExpr ";")*
  "}")*
  (("obs" | "observation") Name "on" Name "=" "(" PolyExpr ("," PolyExpr)* ")" ";")*
"}"

ShigureComparison ::= "comparison" Name "{"
  "before" QName ";"
  "after" QName ";"
  ("state_map" Name "->" Name "{" (Name "=" PolyExpr ";")* "}")*
  ("translate" Name "->" ShigureWordExpr ";")*
"}"

ShigureChangeSpec ::= "change_spec" Name "{"
  "domain" ("Z" | "Q" | "Fp" "(" Integer ")") ";"
  ("param" Name ":" ("Z" | "Q" | "Fp" "(" Integer ")") ";")*
  ("fixed" (
      ("semantic_law" | "representation_law" | "operation" | "op" | "observation" | "obs") QName
    | ("state_comparison" | "word_translation") Name
  ) ";")*
  ("editable" (
      ("representation_law" | "operation" | "op") QName
    | "state_comparison" Name
  ) ";")*
"}"

ShigureEvalCondition ::= "eval_condition" Name "{"
  "point_domain" (
      "algebraic_closure" | "universal_ring"
    | "rational_points" | "Q_points"
    | "integer_points" | "Z_points"
    | ("finite_field_points" | "Fp_points") "(" Integer ")"
  ) ";"
  ("eval" Name "=" PolyExpr ";")*
  ("equation" Name ":" PolyExpr "=" PolyExpr ";")*
  ("invertible" Name ":" PolyExpr ";")*
"}"

ShigureTask ::= "task" Name "{"
  "comparison" QName ";"
  "change_spec" QName ";"
  ("eval_condition" QName ";")?
"}"

ShigureDiagram ::= "diagram" Name "{"
  "direction" ShigureDirection ";"
  ("vertex" ("fixed")? Name ":" QName ";")*
  ("edge" ("fixed")? Name ":" Name "->" Name "{" ShigureMorphismClause "}")*
  ("relation" Name ":" "[" (Name ("," Name)*)? "]" "=" "[" (Name ("," Name)*)? "]" ";")*
  "change_spec" QName ";"
  ("eval_condition" QName ";")?
  ("edge_eval_condition" Name ":" QName ";")*
"}"

ShigurePath ::= "path" Name "{"
  "kind" ("fixed_protocol_change_path" | "enlarged_protocol_execution_path") ";"
  "direction" ShigureDirection ";"
  ("mode" (
      "find" ";"
    | "concatenate" "{"
        "first" "[" (Name ("," Name)*)? "]" ";"
        "second" "[" (Name ("," Name)*)? "]" ";"
      "}"
    | "subdivide" "{" ShigureMorphismClause "}"
  ))?
  ("length" Integer ";")?
  ("vertex" Name ":" QName ";")*
  ("start" Name ( "{" (Name "=" ShigureScalarLit ";")* "}" | ";" ))?
  ("end" Name ( "{" (Name "=" ShigureScalarLit ";")* "}" | ";" ))?
  ("rule" Name ":" Name "->" Name "{"
    ("guard" Name ":" PolyExpr "=" PolyExpr ";")*
    ("update" Name "=" PolyExpr ";")*
    ("eval_condition" QName ";")?
    ShigureMorphismClause
  "}")*
  ("protocol" "{"
    "comparison" QName ";"
    "start_phase" Name ";"
    ("start_law" ShigureLawClause)*
    "end_phase" Name ";"
    ("end_law" ShigureLawClause)*
    "allowed_ops" "[" (Name ("," Name)*)? "]" ";"
  "}")?
  "change_spec" QName ";"
  ("eval_condition" QName ";")?
"}"

ShigureTransfer ::= "transfer" Name "{"
  ("step" Name "{"
    ("before" QName ";")?
    ("after" QName ";")?
    "source_phase" Name ";"
    "target_phase" Name ";"
    ("domain_law" ShigureLawClause)*
    "lift" "{" (Name "=" PolyExpr ";")* "}"
    ShigureMorphismClause
  "}")+
  ("word_check" Name ("(" (Name ("," Name)*)? ")")? "=" ShigureWordExpr ";")*
  ("old_word_lift" Name ("(" (Name ("," Name)*)? ")")? "{"
    "target" ShigureWordExpr ";"
    ("max_length" Integer ";")?
  "}")*
  "change_spec" QName ";"
  ("eval_condition" QName ";")?
  ("require_full_domain" ("true" | "false") ";")?
"}"

ShigurePointDomain ::=
    "algebraic_closure"
  | "universal_ring"
  | "rational_points" | "Q_points"
  | "integer_points" | "Z_points"
  | ("finite_field_points" | "Fp_points") "(" Integer ")"

ShigureOriginRef ::=
  "origin" (
      ("static_analysis" | "runtime_observation" | "llm_candidate" | "human_adopted" | "archmap") String ";"
  )

ShigureMemberValue ::=
    ShigureScalarLit
  | "observed" QName
  | "missing"

ShigureNamedPoly ::= Name ":" PolyExpr ";"
ShigureNamedEq   ::= Name ":" PolyExpr "=" PolyExpr ";"

ShigureFamily ::= "family" Name "{"
  "domain" ("Z" | "Q" | "Fp" "(" Integer ")") ";"
  "realizations" Name "{"
    "u_vars" "[" (Name ("," Name)*)? "]" ";"
    ("b_vars" "[" (Name ("," Name)*)? "]" ";")?
    ("reading_q" "[" (PolyExpr ("," PolyExpr)*)? "]" ";")?
    ( "members" "[" "]" ";"
    | ("member" Name "{"
        ShigureOriginRef
        ("is_raw_candidate" ("true" | "false") ";")?
        ("presentation" QName ";")?
        ("set" Name "=" ShigureMemberValue ";")*
      "}")+
    | "scheme" "{"
        ShigureOriginRef
        ("is_raw_candidate" ("true" | "false") ";")?
        ("equation" ShigureNamedEq)*
        ("invertible" ShigureNamedPoly)*
      "}"
    )
  "}"
  "candidates" Name "{"
    ("c_vars" "[" (Name ("," Name)*)? "]" ";")?
    ("pi" "[" (PolyExpr ("," PolyExpr)*)? "]" ";")?
    ( "members" "[" "]" ";"
    | ("member" Name "{"
        ShigureOriginRef
        ("set" Name "=" ShigureMemberValue ";")*
      "}")+
    | "scheme" "{"
        ShigureOriginRef
        ("equation" ShigureNamedEq)*
        ("invertible" ShigureNamedPoly)*
      "}"
    )
  "}"
  "goodness" (
      "direct" "{"
        ("equation" ShigureNamedEq)*
        ("invertible" ShigureNamedPoly)*
        (ShigurePreservationBlock)?
        (ShigureRawSequenceBlock)?
      "}"
    | "existential" "{"
        "witness_vars" "[" Name ("," Name)* "]" ";"
        ("equation" ShigureNamedEq)*
        ("invertible" ShigureNamedPoly)*
        (ShigurePreservationBlock)?
      "}"
  )
  ("reading_comparison" Name "{"
    "fine_b_vars" "[" (Name ("," Name)*)? "]" ";"
    "fine_q" "[" (PolyExpr ("," PolyExpr)*)? "]" ";"
    "coarsen_r" "[" (PolyExpr ("," PolyExpr)*)? "]" ";"
  "}")?
"}"

ShigurePreservationBlock ::= "preservation" "{"
  "comparison" QName ";"
  "change_spec" QName ";"
  ("bind" Name "=" PolyExpr ";")*
"}"

ShigureRawSequenceBlock ::= "raw_sequence" "{"
  "start_phase" Name ";"
  ("start_state" Name "=" ShigureScalarLit ";")*
  ("step" Name ("(" (ShigureScalarLit ("," ShigureScalarLit)*)? ")")? ";")*
  "observation" Name ";"
  ("baseline_step_index" Integer ";")?
"}"

ShigureCandidateSelector ::=
  "designated_candidate" (
      "id" Name ";"
    | "values" "{" (Name "=" ShigureScalarLit ";")* "}"
  )

ShigureRobustness ::= "robustness" Name "{"
  "family" QName ";"
  "point_domain" ShigurePointDomain ";"
  ("base_value" "[" (ShigureScalarLit ("," ShigureScalarLit)*)? "]" ";")?
  (ShigureCandidateSelector)?
  ("check_universal_ring" ("true" | "false") ";")?
  ("fine_base_value" "[" (ShigureScalarLit ("," ShigureScalarLit)*)? "]" ";")?
"}"

ShigureChevalley ::= "chevalley" Name "{"
  "family" QName ";"
  "point_domain" "algebraic_closure" ";"
  ("base_value" "[" (ShigureScalarLit ("," ShigureScalarLit)*)? "]" ";")?
  (ShigureCandidateSelector)?
  ("probe" Name "{" (Name "=" ShigureScalarLit ";")* "}")*
  ("check_global_regular_section" ("true" | "false") ";")?
  ("check_universal_ring" ("true" | "false") ";")?
"}"

ShigureObservations ::= "observations" Name "{"
  "family" QName ";"
  "point_domain" ShigurePointDomain ";"
  ("base_value" "[" (ShigureScalarLit ("," ShigureScalarLit)*)? "]" ";")?
  ("observe" Name "{"
    ShigureOriginRef
    ("cost" Integer ";")?
    ("component" ShigureNamedPoly)*
  "}")*
  ("law_readout" Name "{" ("component" ShigureNamedPoly)* "}")?
"}"

ShigureCoordVec  ::= "[" (ShigureMemberValue ("," ShigureMemberValue)*)? "]"
ShigureScalarVec ::= "[" (ShigureScalarLit ("," ShigureScalarLit)*)? "]"
ShigureSignedInt ::= ("-")? Integer
ShigurePartition ::= "[" ("[" (Name ("," Name)*)? "]"
                         ("," "[" (Name ("," Name)*)? "]")*)? "]"

ShigureSquareZeroExt ::=
    "truncated" "(" Name "," Integer ")" ";"
  | "explicit_table" "{"
      "r_prime_basis" "[" (Name ("," Name)*)? "]" ";"
      "r_prime_one" ShigureScalarVec ";"
      "r_prime_mul" "[" ("[" (ShigureScalarVec ("," ShigureScalarVec)*)? "]"
                        ("," "[" (ShigureScalarVec ("," ShigureScalarVec)*)? "]")*)? "]" ";"
      "r_base_basis" "[" (Name ("," Name)*)? "]" ";"
      "r_base_one" ShigureScalarVec ";"
      "r_base_mul" "[" ("[" (ShigureScalarVec ("," ShigureScalarVec)*)? "]"
                       ("," "[" (ShigureScalarVec ("," ShigureScalarVec)*)? "]")*)? "]" ";"
      "projection" "[" (ShigureScalarVec ("," ShigureScalarVec)*)? "]" ";"
    "}"

ShigureLift ::= "lift" Name "{"
  "domain" ("Z" | "Q" | "Fp" "(" Integer ")") ";"
  ShigureOriginRef+
  "vars" "[" (Name ("," Name)*)? "]" ";"
  ("ring_param" Name "=" ShigureCoordVec ";")*
  ("law" ShigureNamedEq)*
  "extension" ShigureSquareZeroExt
  "base_point" "{" (Name "=" ShigureCoordVec ";")* "}"
  ("ambient_lift" "{" (Name "=" ShigureCoordVec ";")* "}")?
  ("relative_reading" "{"
    "obs_vars" "[" (Name ("," Name)*)? "]" ";"
    "reading_map" "{" (Name "=" PolyExpr ";")* "}"
    ("obs_law" ShigureNamedEq)*
    "designated_obs_lift" "{" (Name "=" ShigureCoordVec ";")* "}"
    ("raw_read_diff" String ("same_sign" | "negated") ":" PolyExpr ";")?
  "}")?
  ("declaration_cover" "{"
    ("context" Name "{"
      ("vars" "[" (Name ("," Name)*)? "]" ";")?
      ("laws" "[" (Name ("," Name)*)? "]" ";")?
      ("obs" Name ":" PolyExpr ";")*
    "}")*
    ("two_context_cech" "{"
      "left" Name ";" "right" Name ";"
      "shared_vars" "[" (Name ("," Name)*)? "]" ";"
    "}")?
  "}")?
  ("affine_allowed" "{"
    "allowed_vars" "[" (Name ("," Name)*)? "]" ";"
    ("finite_displacement" ("true" | "false") ";")?
  "}")?
  ("redundant_comparison" "{" ("ref_law" ShigureNamedEq)* "}")?
  ("etale_descent" "{"
    "base_var" Name ";" "cover_var" Name ";"
    "degree" Integer ";" ("base_invertible" ("true" | "false") ";")?
  "}")?
  ("max_syzygy_pairs" Integer ";")?
"}"

ShigureArtin ::= "artin" Name "{"
  "domain" ("Z" | "Q" | "Fp" "(" Integer ")") ";"
  ShigureOriginRef+
  "obs_vars" "[" (Name ("," Name)*)? "]" ";"
  ("obs_relation" ShigureNamedEq)*
  ("aux_def" Name "=" PolyExpr ";")*
  ("extra_law" ShigureNamedEq)*
  "base_point" "{" (Name "=" ShigureMemberValue ";")* "}"
  "max_order" Integer ";"
  ("max_artin_dim" Integer ";")?
  ("composite_stage" "{"
    ("aux_def" Name "=" PolyExpr ";")*
    ("extra_law" ShigureNamedEq)*
  "}")?
  ("base_change" "{"
    "target_domain" ("Z" | "Q" | "Fp" "(" Integer ")") ";"
    ("test_order" Integer ";")?
  "}")?
  ("non_noetherian_infinite" ("true" | "false") ";")?
"}"

ShigureSupportedNerve ::= "{"
  ("chart" Name "[" (Name ("," Name)*)? "]" ";")*
  ("edge" Name "(" Name "," Name ")" ";")*
  ("face" Name "(" Name "," Name "," Name ")" ";")*
"}"

ShigureDiagnostics ::= "diagnostics" Name "{"
  "diagnostic_coeff" ("Z" | "Q" | "Fp" "(" Integer ")") ";"
  ShigureOriginRef+
  "nerve" ShigureSupportedNerve
  ( "static_readout" "{"
      "sources" "[" (Name ("," Name)*)? "]" ";"
      "targets" "[" (Name ("," Name)*)? "]" ";"
      "reading" "{" (Name "->" Name ";")* "}"
      ("law" Name "{" (Name "=" ShigureScalarLit ";")* "}")*
    "}"
  | "poly_readout" "{"
      "base_domain" ("Z" | "Q" | "Fp" "(" Integer ")") ";"
      "base_vars" "[" (Name ("," Name)*)? "]" ";"
      "sources" "[" (Name ("," Name)*)? "]" ";"
      ("base_relation" ShigureNamedEq)*
      ("law" Name "{" (Name "=" (PolyExpr | "observed" QName | "missing") ";")* "}")*
    "}" )
  ("coeff_change" "{"
    "target_domain" ("Z" | "Q" | "Fp" "(" Integer ")") ";"
    ("compare_codomain_regeneration" ("true" | "false") ";")?
    ("explicit_z_complex" "{"
      "dim0" Integer ";" "dim1" Integer ";"
      "d0" "[" ("[" (ShigureSignedInt ("," ShigureSignedInt)*)? "]"
            ("," "[" (ShigureSignedInt ("," ShigureSignedInt)*)? "]")*)? "]" ";"
      ("designated_cocycle" "[" (ShigureSignedInt ("," ShigureSignedInt)*)? "]" ";")?
    "}")?
  "}")?
  ("collision" String "on" Name "{"
    "fine" ShigurePartition ";"
    "coarse" ShigurePartition ";"
    ("alt_path" "[" (ShigurePartition ("," ShigurePartition)*)? "]" ";")*
  "}")*
  ("r_point_probe" "{"
    "ring_var" Name ";" "ring_max_deg" Integer ";"
    ("point" String "{" (Name "=" ShigureCoordVec ";")* "}")*
  "}")?
  ("dimension_realization" "{"
    "base_domain" ("Z" | "Q" | "Fp" "(" Integer ")") ";"
    "base_vars" "[" (Name ("," Name)*)? "]" ";"
    ("vanishing" ShigureNamedEq)*
    "invertible" Name ":" PolyExpr ";"
    ("probe" String "{" (Name "=" ShigureMemberValue ";")* "}")*
  "}")?
  ("max_partitions" Integer ";")?
"}"

ShigureAtlas ::= "atlas" Name "{"
  "domain" ("Z" | "Q" | "Fp" "(" Integer ")") ";"
  ShigureOriginRef+
  "vertices" "[" (Name ("," Name)*)? "]" ";"
  ("edge" Name "(" Name "->" Name ")" "offset" ShigureMemberValue ";")*
  "mu" ShigureMemberValue ";"
  "base_lambdas" "{" (Name "=" ShigureMemberValue ";")* "}"
  ("allowed_vertices" "[" (Name ("," Name)*)? "]" ";")?
  ("allowed_edges" "[" (Name ("," Name)*)? "]" ";")?
  ("compare_to_q" ("true" | "false") ";")?
  ("refinement" "{"
    "fine_vertices" "[" (Name ("," Name)*)? "]" ";"
    ("fine_edge" Name "(" Name "->" Name ")" "offset" ShigureMemberValue ";")*
    "vertex_map" "{" (Name "->" Name ";")* "}"
    "edge_map" "{" (Name "->" (Name | "none") ";")* "}"
    "common_sources" "[" (Name ("," Name)*)? "]" ";"
    "coarse_reading" "{" (Name "->" Name ";")* "}"
    "fine_reading" "{" (Name "->" Name ";")* "}"
    "coarse_nerve" ShigureSupportedNerve
    "fine_nerve" ShigureSupportedNerve
    "nerve_chart_map" "{" (Name "->" Name ";")* "}"
    "nerve_edge_map" "{" (Name "->" (Name | "none") ";")* "}"
    ("nerve_face_map" "{" (Name "->" (Name | "none") ";")* "}")?
    ("eval_condition" "{"
      ("eval" Name "=" PolyExpr ";")*
      ("equation" ShigureNamedEq)*
      ("invertible" Name ":" PolyExpr ";")*
    "}")?
    ("forgetful_reading" "{"
      "forgotten_var" Name ";"
      "eval_expr" PolyExpr ";"
      "condition_eq" ":" PolyExpr "=" PolyExpr ";"
      "sample_values" ShigureCoordVec ";"
    "}")?
  "}")?
  ("extended_language_check" "{"
    "state_vars" "[" (Name ("," Name)*)? "]" ";"
    "adapter_map" "{" (Name "=" PolyExpr ";")* "}"
    ("atomic_op" Name "(" (Name ("," Name)*)? ")" "{"
      "before" "{" (Name "=" PolyExpr ";")* "}"
      "after" "{" (Name "=" PolyExpr ";")* "}"
    "}")*
    ( "protocol_sequence" String "{"
        "extended_state_vars" "[" (Name ("," Name)*)? "]" ";"
        "initial_state" "{" (Name "=" ShigureMemberValue ";")* "}"
        ("before_step" "{" (Name "=" PolyExpr ";")* "}")*
        ("after_step" "{" (Name "=" PolyExpr ";")* "}")*
        "before_read" PolyExpr ";" "after_read" PolyExpr ";"
        ("intermediate_law" ShigureNamedEq)*
      "}"
    | "runtime_arg_op" String "{"
        "before" "{" (Name "=" PolyExpr ";")* "}"
        "after" "{" (Name "=" PolyExpr ";")* "}"
        "sample_state" "{" (Name "=" ShigureMemberValue ";")* "}"
      "}" )*
  "}")?
"}"

ShigureSym      ::= Name | Integer | String
ShigureSymValue ::= "observed" QName | "missing" | ShigureSym
ShigureSymList  ::= "[" (ShigureSym ("," ShigureSym)*)? "]"

ShigureOccurrence ::= "occurrence" Name "{"
  ShigureOriginRef+
  (("fixed_value")? "sort" Name "=" ShigureSymList ";")*
  (("operation" | "partial_operation") Name "(" "[" (Name ("," Name)*)? "]" ")" "->" Name ";")*
  ("relation" Name "(" "[" (Name ("," Name)*)? "]" ")" ";")*
  ("identify" Name ShigureSym "=" ShigureSym ";")*
  ("op_record" Name "(" ShigureSymList ")" "->" ShigureSymValue ";")*
  (("domain_record" | "rel_record") Name "(" ShigureSymList ")" "=" ("true" | "false") ";")*
  (("base_reading" | "explicit_context") Name ":" Name "{" (ShigureSym "->" (ShigureSymValue | "none") ";")* "}")*
  ("context_closed" ("true" | "false") ";")?
  ("preserve_full_domain" "[" (Name ("," Name)*)? "]" ";")*
  ("initial_readout" Name "{" (ShigureSym "->" ShigureSymValue ";")* "}")*
  ("max_congruence_steps" Integer ";")?
  ("max_partitions" Integer ";")?
"}"

PartialValue   ::= "known" ShigureSymValue | "absent" | "unobserved" Name
PartialTruth   ::= "true" | "absent" | "unobserved" Name
PartialTerm    ::= "slot" "(" Name ")" | "const" "(" ShigureSym ")" | ("-")? Integer | String
                 | Name ("(" (PartialTerm ("," PartialTerm)*)? ")")?
                 | "let" Name "=" PartialTerm "in" PartialTerm
                 | PartialTerm ("+" | "-" | "*") PartialTerm | "(" PartialTerm ")"
PartialFormula ::= "true" | "false" | "not" PartialFormula
                 | PartialFormula ("and" | "or") PartialFormula
                 | PartialTerm "=" PartialTerm
                 | "rel" "(" Name "(" (PartialTerm ("," PartialTerm)*)? ")" ")"
                 | ("exists" | "forall") Name ":" Name ("in" ShigureSymList)? "." PartialFormula
                 | "(" PartialFormula ")"

ShigurePartial ::= "partial" Name "{"
  ShigureOriginRef+
  ( "finite_table" "{"
      ("sort" Name "=" ShigureSymList ";")*
      (("operation" | "partial_operation") Name "(" "[" (Name ("," Name)*)? "]" ")" "->" Name ";")*
      ("relation" Name "(" "[" (Name ("," Name)*)? "]" ")" ";")*
      ("slot" Name ":" Name "in" ShigureSymList ";")*
      ("background" "{"
        ( "slot_eq" "(" Name "," Name ")" ";"
        | "slot_neq" "(" Name "," Name ")" ";"
        | ("injective" | "surjective") "(" Name ")" ";" )*
      "}")*
      ("record" Name ":"
        ( "op_value" Name "(" ShigureSymList ")" "=" PartialValue
        | "op_domain" Name "(" ShigureSymList ")" "=" PartialTruth
        | "op_graph" Name "(" ShigureSymList "," ShigureSym ")" "=" PartialTruth
        | "rel" Name "(" ShigureSymList ")" "=" PartialTruth
        | "slot_assign" Name "=" ShigureSym ) ";")*
      ("max_completions" Integer ";")?
    "}"
  | "affine" "{"
      "domain" ("Z" | "Q" | "Fp" "(" Integer ")") ";"
      ("coords" "[" (Name ("," Name)*)? "]" ";")?
      ("x0" "=" ShigureCoordVec ";")?
      ("direction_t" "=" "[" (ShigureCoordVec ("," ShigureCoordVec)*)? "]" ";")?
      (("background_row" | "record_row" | "eval_eq") Name ":" ShigureCoordVec "=" ShigureMemberValue ";")*
    "}"
  | "unsupported" String ";" )
  ("eval_law" Name "{"
    ("required" "=" ("true" | "false") ";")?
    ("antecedent" "=" PartialFormula ";")?
    "conclusion" "=" PartialFormula ";"
  "}")*
  ("quantifier" "{"
    ("candidates" "[" (Name ("," Name)*)? "]" ";")?
    ("completion" Name "{"
      ("slots" "{" (Name "=" ShigureSym ";")* "}")*
      ("valid" "[" (Name ("," Name)*)? "]" ";")?
      "output" "=" ShigureSym ";"
    "}")*
    ("max_steps" Integer ";")?
  "}")?
  ("open_domain" "{"
    ("substructure" | "ambient") "{"
      ("sort" Name "=" ShigureSymList ";")*
      ("op_table" Name "(" "[" (Name ("," Name)*)? "]" ")" "->" Name "{"
        (ShigureSymList "->" (ShigureSym | "none") ";")* "}")*
      ("rel_table" Name "(" "[" (Name ("," Name)*)? "]" ")" "{"
        (ShigureSymList ";")* "}")*
    "}"
    ("fiber_check" Name ":" Name "->" Name "targets" ShigureSymList ";")*
    "positive_law" Name "{"
      ("required" "=" ("true" | "false") ";")?
      ("antecedent" "=" PartialFormula ";")?
      "conclusion" "=" PartialFormula ";"
    "}"
    ("affine_restriction" "{"
      "domain" ("Z" | "Q" | "Fp" "(" Integer ")") ";"
      "num_vars" "=" Integer ";"
      "m_matrix" "=" LitMatrix ";"
      "b_rhs" "=" "[" (ShigureScalarLit ("," ShigureScalarLit)*)? "]" ";"
      "r_matrix" "=" LitMatrix ";"
    "}")?
  "}")?
"}"

ShigureRevConstraint ::= Name "support" "[" (Name ("," Name)*)? "]" ":"
  ( "eq" "(" Name "," Name ")"
  | "linear_zero" "[" ("(" ShigureScalarLit "," Name ")" ("," "(" ShigureScalarLit "," Name ")")*)? "]"
  | "allowed_tuples" "(" "[" (Name ("," Name)*)? "]" "," LitMatrix ")" ) ";"

ShigureRevision ::= "revision" Name "{"
  "kind" "=" ("extension" | "span") ";"
  "domain" ("Z" | "Q" | "Fp" "(" Integer ")") ";"
  ShigureOriginRef+
  ("coord" Name "in" "[" (ShigureScalarLit ("," ShigureScalarLit)*)? "]" ";")*
  ("shared_constraint" ShigureRevConstraint)*
  (("before" | "after") "{"
    ("assign" Name "=" ShigureMemberValue ";")*
    ("constraint" ShigureRevConstraint)*
  "}")*
  ("explicit_delta" "[" (Name ("," Name)*)? "]" ";")*
  ("probe" Name "support" "[" (Name ("," Name)*)? "]" ":"
    ("if" Name "=" ShigureScalarLit "=>")? Name "=" ShigureScalarLit ";")*
  ("snf" "{"
    "domain" ("Z" | "Q" | "Fp" "(" Integer ")") ";"
    "num_cols" "=" Integer ";"
    ( "common_operator" "=" LitMatrix ";"
    | "operator_before" "=" LitMatrix ";" "operator_after" "=" LitMatrix ";" )
    "rhs_before" "=" "[" (ShigureScalarLit ("," ShigureScalarLit)*)? "]" ";"
    "rhs_after" "=" "[" (ShigureScalarLit ("," ShigureScalarLit)*)? "]" ";"
    ("operator_unobserved" "[" (Name ("," Name)*)? "]" ";")*
    ("force_reuse" "=" ("true" | "false") ";")?
    ("origin_label_only" "=" ("true" | "false") ";")?
  "}")?
  ("max_completions" Integer ";")?
"}"

ShigureMultisource ::= "multisource" Name "{"
  "domain" ("Z" | "Q" | "Fp" "(" Integer ")") ";"
  ShigureOriginRef+
  ("coord" Name "in" "[" (ShigureScalarLit ("," ShigureScalarLit)*)? "]" ";")*
  ("background_constraint" ShigureRevConstraint)*
  ("source" Name "{"
    ShigureOriginRef
    ("assign" Name "=" ShigureMemberValue ";")*
    ("constraint" ShigureRevConstraint)*
  "}")*
  ("support_goal" "{"
    ("trusted" "{" (Name "=" ShigureScalarLit ";")* "}")*
    ("candidate" Name "{"
      ShigureOriginRef
      "coord" "=" Name ";"
      "value" "=" ShigureMemberValue ";"
      ("cost" "=" ShigureScalarLit ";")?
      ("verified_actual" "=" ShigureMemberValue ";")?
    "}")*
    "goal" "=" ("eq" "(" Name "," Name ")" | "eq_const" "(" Name "," ShigureScalarLit ")") ";"
    "expected_truth" "=" ("true" | "false") ";"
    ("check_stability" "=" ("true" | "false") ";")?
  "}")?
  ("max_steps" Integer ";")?
  ("max_results" Integer ";")?
"}"
```

`PolyExpr` は係数定数（整数、`rat(n,d)`、`fp(v,p)`）、座標・引数・探索パラメータ変数、
`+` / `-` / `*` / 単項 `-` / `pow(PolyExpr, Integer)` / 括弧からなる多項式である。`Fp(p)` の法 `p` は素数であることを検査する。
`shigure path` の `mode` 省略時は `find`、`shigure transfer` の `require_full_domain` 省略時は `false` を既定とする。
また、`shigure lift` の `etale_descent.base_invertible` 省略時は `true` を、`affine_allowed.finite_displacement`・`shigure artin` の `non_noetherian_infinite`・`shigure diagnostics` の `compare_codomain_regeneration`・`shigure atlas` の `compare_to_q`・`shigure occurrence` の `context_closed`・`shigure partial` の `eval_law.required`・`shigure revision` の `snf.force_reuse` / `snf.origin_label_only`・`shigure multisource` の `support_goal.check_stability` 省略時はそれぞれ既定値（`context_closed = true`、`eval_law.required = true`、その他 `false`）を採用する。
各 `rule`・`edge`・`subdivide`・移送 `step` における射本体 `ShigureMorphismClause` では、`comparison`・`identity`・インライン（`state_map` / `translate`）の混在を禁止する（`step` では `comparison` と `before`/`after` の混在も禁止する）。
`shigure diagram` / `shigure path` / `shigure transfer` / `shigure family` / `shigure robustness` / `shigure chevalley` / `shigure observations` / `shigure lift` / `shigure artin` / `shigure diagnostics` / `shigure atlas` / `shigure occurrence` / `shigure partial` / `shigure revision` / `shigure multisource` の各ブロックおよび `phase` ブロック内では、異なる句の配置順は上記の多重度制約のもと任意であるが、`shigure transfer` の `step`、`shigure artin`（および `composite_stage`）の `aux_def`（先行定義のみ参照する依存順）、`shigure atlas` `protocol_sequence` の `before_step` / `after_step` は記述順が意味を持つ。

静的検査と変換検査では次を強制する。

- **結論注入の拒否**: `residual_ideal`、`residuals`、`empty_witness`、`witness`、`solution`、`solutions`、
  `interaction`、`interaction_summary`、`participating_variables`、`minimal_failing_subsets`、
  `verdict`、`restored`、`reeval`、`groebner_basis` に加え、`completed_diagram`、`restored_diagram`、
  `commutativity_residuals`、`computed_path`、`restored_path`、`rejected_candidates`、`subdivision_fiber`、
  `transfer_verdict`、`restored_transfer`、`common_domain`、`composed_domain`、`word_check_results`、
  `old_word_lift_results`、`lift_found`、`domain_nonempty`、`quantifiers`、`valid_designated`、`pointwise`、
  `common_candidate`、`fiber_non_empty`、`robust_all_pass`、`all_fail`、`mixed`、`empty_realizations`、
  `effective_image_e`、`p_plus`、`p_minus`、`chevalley_partition`、`mixed_witness_pair`、`distinguishing_pairs`、
  `minimal_sufficient_sets`、`minimal_sufficient_observations`、`insufficiency_witness`、`raw_candidate_evaluations`、`reevaluation`、
  さらに変形・診断・Atlas 系の `syzygy`、`syzygies`、`syzygy_basis`、`syzygy_generators`、`syzygy_verified`、`cohomology`、
  `h0_dim`、`h1_dim`、`h2_dim`、`h0_free_rank`、`h1_free_rank`、`h2_free_rank`、`h0_torsion`、`h1_torsion`、`h2_torsion`、
  `d1_d0_zero_verified`、`obstruction`、`obstruction_class`、`obstruction_zero`、`relative_obstruction`、`designated_obstruction`、
  `o_p`、`o_u`、`kappa_u`、`o_b`、`kappa_b`、`detection_order`、`first_failure_order`、`syntax_degree_bound`、`eliminated_ideal`、
  `is_locally_isomorphic`、`universal_first_obstruction`、`ker_h1_r`、`coker_h1_r`、`ker_h1_r_dim`、`coker_h1_r_dim`、
  `coker_h0_rho_dim`、`im_h1_rho_dim`、`mayer_vietoris`、`mayer_vietoris_identity_verified`、`strata`、`upper_semicontinuity_refutation`、
  `condition_c`、`condition_c0`..`condition_c6`、`h0_isomorphism`、`h1_isomorphism`、`designated_o_preserved`、`designated_kappa_preserved`、
  `repair_fiber_isomorphism_verified`、`inverse_reconstruction_verified`、`repair_solutions`、`unconstrained_repair`、
  `vertex_constrained_repair`、`edge_constrained_repair`、`torsor_basis`、`particular_solution`、`restored_lift`、`global_lift_exists`、
  および出現同定・部分提示・改訂・多源衝突系の `minimal_functional_classes`、`context_equivalence_classes`、`separating_contexts`、
  `coarsest_sound_exists`、`coarsest_sound_classes`、`derivation_verified`、`attribute_realization`、
  `completion_consistent`、`completion_count`、`minimal_inconsistent_subsets`、`mus_verified`、`kleene_soundness_verified`、
  `quantifier_hierarchy`、`required_slot_sets`、`positive_preserved`、`affine_unique_repair_exists`、
  `monotonicity_preserved`、`invalidation_cone`、`outside_cone_coords`、`outside_projection_equal`、
  `umv_verified`、`reused_snf`、`after_solvable`、`after_particular`、`kernel_basis`、
  `pairwise_consistent`、`all_sources_consistent`、`minimal_conflict_sets`、`minimal_conflicts_verified`、`minimal_supports`、`min_cost_supports`
  などの計算結論相当の語を、`shigure <種別>` の宣言種別位置、各宣言本体・下位ブロックの句（フィールド）位置、および内部識別子・変数位置に含めた場合、構文検査で拒否する。
- **守る意味 Law と固定部分圏・初段基準・背景制約分離の保護**: `editable semantic_law` は構文・型検査で拒否する。
  `editable representation_law` で `semantic` 宣言を指す不適合な指定、`fixed` と `editable` の重複、
  `editable` による `shigure task` や `shigure family` `preservation` の `before` 表示変更・探索パラメータ混入も拒否する。
  `shigure diagram` では固定部分圏 $K$ の頂点・辺および意味 Law への編集指定と、固定辺が非固定頂点を結ぶ非閉指定を拒否する。
  `shigure transfer` では多段連鎖（`step[i].after == step[i+1].before`）を要求し、
  初段 `step[0]` の始端表示 $X_0$ をパラメータフリーかつ編集不可に制限する（2 段目以降の共有中間表示における編集・パラメータ指定は許容する）。
  `shigure partial` では `eval_law` の `finite_table` / `background` ブロック内への混入を構文上拒否し、必須 Law と背景制約による補完空間を分離する。
- **名前・参照・型・循環・無界境界の検査**: 同一 reading 内の宣言名重複、`use` alias・原始定義完全名・組込み演算名との衝突、
  `shigure` reading 間の循環参照、未宣言の phase・座標・操作・sort・slot・候補・変数、
  `state`/`arg`/`param` の名前空間衝突（`word_check`・`old_word_lift` の仮引数重複およびパラメータとの衝突、`u_vars`/`b_vars`/`c_vars` 間の名前衝突および `witness_vars`・`fine_b_vars` と `u_vars`/`b_vars`/`c_vars` の名前衝突を含む）、
  `goodness existential` の空 `witness_vars`、`raw_sequence` 指定時の必須 `presentation`・フェーズ連結・`start_state` 網羅・終端/基準フェーズ観測不整合、
  `observe.cost` および `multisource` `candidate.cost` の負数（および `observe.cost` の小数）、`realization`・`candidate`・`observe`・`lift`・`artin`・`diagnostics`・`atlas`・`occurrence`・`partial`・`revision`・`multisource` における `origin` 欠如および空 `ArchMap` origin ID 参照、
  `shigure lift` の `vars`/`base_point` 不整合・`ring_param` 長不一致・`explicit_table` 次元不整合・未宣言変数参照、
  `shigure artin` の `aux_def` の循環・逆順依存（後方参照）・`max_order == 0`・`obs_vars` と `aux_def` の名前衝突、
  `shigure diagnostics` の `static_readout` と `poly_readout` の排他違反・`nerve` の端点/面不整合・`collision` の未宣言 Law 参照、
  `shigure atlas` の単純有向グラフ端点・辺数（1 本以上必須）違反・`base_lambdas` 欠落・`refinement` の写像域外参照・`extended_language_check` の状態変数不一致、
  `shigure occurrence` の未宣言 sort/操作/関係/要素参照・記録重複、
  `shigure partial` の未宣言 sort/slot/束縛変数・`affine` 次元不一致・`eval_eq` を評価不能値へ置く背景混在、
  `shigure revision` の `snf` における列数・右辺・作用素次元不一致および `origin_label_only = true` 時の作用素/右辺差分、
  `shigure multisource` の未宣言座標・制約重複・`support_goal` 未定義目標、
  `observed Entity.field` の型と係数域の不一致、`point_domain` と `domain` の不整合
  （例: `domain Q` と `integer_points`、`domain Z` / `Q` と `finite_field_points(p)`、
  `domain Fp(p)` と `algebraic_closure` / `rational_points` / `integer_points`、
  法不一致の `Fp(p)` と `finite_field_points(q)`、`Fp(p)` での範囲外リテラル、
  `shigure robustness` / `shigure chevalley` / `shigure observations` でのトップレベル `point_domain universal_ring` 指定、
  `shigure chevalley` での非 `algebraic_closure` 指定および `domain Fp(p)` 指定）、
  および `direction` と射端点の不整合を拒否する。
  なお `domain Z` と `rational_points` は $\mathbb{Z} \hookrightarrow \mathbb{Q}$ による $\mathbb{Q}$ 点評価として受理する。
  また `shigure path` の `mode find` / `mode subdivide` における `length` 省略および `old_word_lift` の `max_length` 省略は構文上受理し、実行時に `unbounded_search_out_of_scope` の `undetermined` として扱う（`mode concatenate` は `first`・`second` の列長から経路長が定まるため `length` 省略を通常評価する）。
- **欠測と由来**: `observed Entity.field` の値が ArchMap で欠測（`Slot::Missing` または対象不在）の場合や `member` 座標に `missing` を明示した場合は、
  零へ補完せず未観測のまま保持し、計算時に `unobserved_dependency` として未決（`undetermined`）を返す。
  参照した観測座標や `origin archmap` が指す ArchMap `Origin` には `Origin.kind` の明示を要求し、未参照の `Origin` は結果由来へ混入させない。また `origin` で指定した 4 種（`static_analysis`・`runtime_observation`・`llm_candidate`・`human_adopted`）および複数 `SourceLocation` を結果まで区別保持する。
