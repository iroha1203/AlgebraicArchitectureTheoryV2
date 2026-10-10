# Law の宣言言語

Law ファイルは、観測する語彙と読みを `reading` にまとめる。個々の `law` は、
適用先・役割・原式を持つ条件である。`view` は型付きの値を読む。
問いは [CLI](execution.md) で選ぶ。宣言から対象・写像・方程式・局所状態を生成し、
その意味・型・構造と数学の適用条件を検査する責務は ArchSig にある。

作者は語彙、値の読み方、要求、公開する局所情報、許す変更を宣言する。
短い条件も構造再帰を使う意味定義も、この同じ言語の型付き宣言として扱う。
核は宣言と ArchMap から cover、行列、複体などの標準の構成を生成する。
エンジンは問いに必要な依存関係と算法から実行計画を作り、solver の適用と実行順を決める。
構成の意味は [核の構成](computations.md)、実行計画と結果の確認は
[実行仕様](execution.md)と[型付き結果](results.md)に従う。

## 1. ファイル、名前、再利用

```text
law "archsig.law/1" semantics "archsig/0.6.0";
reading Reservations {
  entity System;
  entity State(owner: System) { free: Z; held: Z; }
  arrow Reserve(owner: System, from: State[owner], to: State[owner]);
  correspondence Migration(from: System, to: System) {
    states: Map<State[from], State[to]>;
    reserves: Map<Reserve[from], Reserve[to]>;
  }
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
予約語は `law semantics reading use as entity arrow correspondence align data view required
optional local reads change relation when let in if then else match forall exists not implies or
and with true false unit list set where none some fn` と組込み型名である。
予約語は宣言名・束縛名に使えない。`owner from to` は field 名として使える。

一つのファイルに一つ以上の reading を置く。完全名は `Reading.Declaration`、field は
`Reading.Entity.field`、constructor は `Reading.Data.Constructor`。
同じ scope の名は重複不可。reading 内では自分の宣言を短名で参照できる。
`use Other as O;` は同梱 reading の別名。直接の完全名参照も許す。
参照する reading 間の有向グラフは非循環で、ファイル外の探索や download はしない。
宣言順は意味を持たず、field/constructor の引数順は意味を持つ。

reading を再利用するときは、その依存 reading とともに同梱する。
ファイル全体の版は同一。語彙の binding と digest は [入力仕様](inputs.md) に従う。

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
`Members` は `{ Name ":" Type ";" }`。

```text
Document = "law" String "semantics" String ";" Reading { Reading } ;
Reading = "reading" Name "{" { Use | Declaration } "}" ;
Use = "use" Name "as" Name ";" ;
Declaration = Entity | Arrow | Correspondence | Data | View | Law | Local | Change | Relation ;
Entity = "entity" Name [ "(" Fields ")" ] ( ";" | "{" Members "}" ) ;
Arrow = "arrow" Name "(" Fields ")" ( ";" | "{" Members "}" ) ;
Correspondence = "correspondence" Name "(" Fields ")" "{" Members { Alignment } "}" ;
Alignment = "align" QName "=" QName ";" ;
Data = "data" Name "=" Constructor { "|" Constructor } ";" ;
Constructor = Name [ "(" Type { "," Type } ")" ] ;
View = "view" Name "(" Fields ")" ":" Type "=" Expr ";" ;
Law = "law" ( "required" | "optional" ) Name "(" Fields ")"
      [ "when" Expr ] ":" Expr ";" ;
Local = "local" Name "(" Fields ")" [ "when" Expr ] "reads" Expr { "," Expr } ";" ;
Change = "change" Name "(" Fields ")" [ "when" Expr ] "=" Expr ";" ;
Relation = "relation" Name "(" Fields ")" [ "when" Expr ] ":" Expr "=" Expr ";" ;
```

relation の body は、最上位の `=` が一つの二項式として構文解析する。その左右を上の二つの
Expr とし、左右それぞれの型を Path に限定する。通常の等号と別の優先度を与えない。

`entity` / `arrow` / `correspondence` の括弧内も body も原始 field 宣言で、両者の名は一意。
括弧内は後続 field の依存型から参照できる。body field の型から別の body field を参照しない。
単なる表示位置ではなく、この依存順を語彙に保持する。

- `entity` の `owner` は省略可能な唯一の所属 field。型は owner を持たない entity とする。
  owner なし entity の各 instance が対象の根となる。所有の多段化は導入しない。
  所属以外の共有・依存は通常の参照 field で書く。
- `arrow` は `owner: R, from: E[owner], to: E[owner]` を必須とする。
  R は根 entity、E は R に属する entity。追加 field を許す。
  from→to がこの名前付き内部遷移の作用である。追加の値・式は Law で読める。
- `correspondence` は `from: R, to: S` を必須とし、R/S は根 entity。
  body の field は `Map<E[from], F[to]>`。対応する各 owned entity/arrow の組を一度ずつ宣言する。
  source/target 側の構成対象に含まれる各 owned 型を覆うことを要求する。
  同じ型間では同名 field の位置を対応させる。異なる型間では `align` で source と target の
  field の対応をすべて明記する。所属・参照は対応表に沿って、量は位置だけを対応させる。
  align は field の意味の対応であり、値が一致するという判定を入力しない。
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
- `change` の第1引数は owned entity または根 entity、残りは参照を含まない値型。
  結果は第1引数と同じ entity の `with` 更新である。owner・参照・Map・subject roster は変更しない。
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
        | "set" "{" Expr "|" Name "in" Expr [ "where" Expr ] "}"
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

束縛は lexical。parameter、let、pattern、量化、comprehension の同一 scope 内の名は一意。
内側の shadowing は禁止。let の右辺に自分を参照できない。match は constructor を全て一度ずつ
覆うか末尾に `_` を置き、重複・到達不能分岐を拒否する。constructor は完全名、`Data.Ctor`、
期待 data 型から一意な短名の順で解決する。変数名と衝突する短名は修飾する。
全分岐を型検査し、if の両枝・match の各枝の結果型を一致させる。

field lookup は宣言済みの field だけ。tuple は数値射影だけ。適用は view、Map、Term、constructor、
以下の固定演算だけ。関数の名前や文字列から外部 code を実行しない。
ドット列は、先頭が束縛変数ならその field 射影として読む。それ以外は alias 展開後の
宣言完全名を最長一致で解決し、残りを射影として読む。予約語 `then` はこの合成演算の
適用位置だけで Primary となる。組込み演算名は宣言・束縛名として再定義できない。

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
`fn` は Term を構成し、その parameter 以外の変数・field・参照族を捕獲しない。
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
この確認を完了できなければ依存 slot と理由を保持する。if/guard/所有者が不明なら、
複数の分岐・族を条件付きで保持し、一方を勝手に捨てない。
Bool の false and x、true or x、同じ未知整数 h の h−h は補完によらず確定できる。
全称に既知の反例が一つあれば他 instance の欠測によらず反証できる。

原始参照・有限型の補完は有限列挙、数値アフィンの相関は記号的に保持することを必須とする。
それ以外の補完を必要とする問いは未観測箇所を明示し、対応する算法がなければその理由も付す。
未観測値の全補完が空になる提示は `inconsistent_observation` として拒否し、空虚な成立を返さない。
change の自由 parameter と未観測 slot は異なる。修復・探索で後者を決定変数にしない。
