---
name: archsig-observe
description: Read a repository's implementation and requirement sources to create, reuse, or update ArchSig 0.6.0 Atom definitions, Law, and ArchMap with source evidence. Use for architecture questions and proposed changes requiring semantic observation.
---

# ArchSig Observe

対象リポジトリと「理解したいこと・実現したい変更」から、使用文脈を読んだ三入力を作る。
利用者が指定した出力先に、Atom 定義 JSON、Law DSL、ArchMap JSON を渡す。
観測の根拠・不足・検証結果は利用者の会話または指定された出力先へ返す。

## バンドルを使う

展開したバンドルから、利用者が指定した CLI と、本ファイルを含む SKILL ディレクトリの
本体・assets・scripts を使う。
補助には Python 3.9 以降と標準ライブラリが必要。CLI は利用環境の OS/CPU に対応した
0.6.0 の実行可能ファイルを使う。対象ソースと生成物の保存先はバンドルとは別に指定する。

本ファイルの実際の配置から skill ディレクトリを特定する。以下は CLI を `bin/archsig`、
SKILL を `skills/archsig-observe` に置いたバンドルの POSIX shell 例。`bundle` と `work` を
実際の絶対パスに置き換える。配布配置が異なる場合は `skill` と `cli` を指定された場所へ設定する。
`work` は生成物用の書込み可能なディレクトリで、対象ソースの場所とは区別する。

```sh
bundle='/path/to/extracted-bundle'
work='/path/to/observation-output'
skill="$bundle/skills/archsig-observe"
cli="$bundle/bin/archsig"
"$cli" version
```

返る `product` が `archsig`、`version` が `0.6.0`、`semantics` が
`archsig/0.6.0` を含むことを確かめる。Windows では同じ絶対パスの引数で `archsig.exe` を呼ぶ。
SKILL だけを別の場所へインストールした場合は、元バンドルの場所を利用者から受け取り、
`skill` はインストール先、`cli` はそのバンドルの実行ファイルへ明示的に設定する。
利用者が PATH 上のコマンドを指定した場合も、その解決先と版を確認して使用する。
バイナリ不在・非対応なら接続を未検証とし、ビルドや別のインストールの自動探索で補わない。
以下の相対リンクは本ファイル基準、コマンドの資産参照は `skill` 基準なので、cwd は任意。

## 問いから読解へ

問いに関係する業務範囲と revision を選ぶ。既存の Atom 定義・Law があれば意味と版を読み、
共有する語彙と変更する reading を分ける。要求の根拠、原始事実、候補設計のどれを読むかを決める。
根拠資料が見つからない要求や、実装の慣習を今後も守る要求へ採用する判断は利用者に返す。

選んだ範囲を、操作、共有する文脈、要求の関係として読む。
操作は「入力・状態の条件／作用と呼出しの順／正常・例外・何もしない出口」を一単位にする。
共有文脈は「初期値・既定値・名前の binding／公開する値と変更手段／それを使う場所」、
要求は「求める関係／適用範囲／根拠」を読む。同じ箇所の複数の役割は対応を残す。
呼出しへ渡す値・参照と戻り値の使い方を対応づけ、binding・継承先を経た作用を同じ対象についてつなぐ。
途中の失敗でどの作用まで到達するかも確かめる。
この単位は読解の整理であり、新しい schema や必須レポートではない。
条件・対象・順序が異なる意味を潰さず、同じ意味を件数のために分割しない。
実装に記述された I/O の役割・順序・状態変化も対象にする。
実際に発生した処理、性能、稼働状況は実行時の検証へ分ける。
たとえば durable commit の成否は別の検証事項として説明し、実装観測用の語彙へ
「未測定の実行結果」という field を追加しない。必要な欠測 slot は実装から読める原始情報に限る。
要求が運用上の実施・品質を求めても、その要求があることと実際に守られたことを分ける。
後者が対象ソースから読めなければ入力外の未検証事項として説明し、欠測 field や Law の評価対象を増やさない。
テストコードは実装観測へ混ぜない。
検索・位置照合・形式検査は補助に使い、AST や名前から抽出した関係を意味観測へ置き換えない。

一つの主張に適用条件と使用箇所を付ける。複数の箇所を読んで得た主張は各箇所へ結びつける。
引用を付けたら、その引用だけを読み直して主張の条件・作用・対象・順序が全て支えられるかを確かめる。
前段の guard、定数の定義、呼出し先、継承・初期化が根拠なら、その場所も locations に含める。
依存先の意味を述べるときは、呼出し箇所に加え import・alias・引数の既定値など、
その名前が何に束縛されるかを示す場所まで引用する。言語・標準ライブラリの意味仮定とは分ける。
不在や「変更しない」という主張には、除外した経路と操作の範囲を確認できる根拠を付ける。
複合主張の一部しか支えられなければ必要な根拠を追加するか、独立した主張へ分けて未確認部分を残す。
byte 範囲の妥当性やファイル全体の digest は意味支持の代わりにならない。
Atom を作る時点で、判断に使った文脈の位置を origin に残し、主箇所の狭い位置を案内として併記する。
同じ文脈を使う Atom は共通の origin を参照してよい。Law が読む field から Atom・origin へ
たどれる根拠は引用を複写せず参照で示す。source 登録だけで意味を支えたことにはしない。
未読のファイルを付け足して根拠を埋めず、引用した文脈に主張の全条件があるかを再確認する。
草稿と更新後の三入力を、同じ読解単位から二方向に照合する。
ソース側からは、選択範囲の操作・初期化・公開境界・依存する文脈・要求が
どの宣言・Atom・Law に残ったかを確認する。説明文にしか残らない条件も入力へ戻す。
出力側からは、各値と引用を開き直し、条件・作用・対象・順序が支えられるかを確認する。
総括や補助 field も詳細と照合し、型の変更可能性と操作の作用など根拠の異なる主張は分ける。
不足があればその区別に必要な文脈を読み足す。読める不足を黙って削らず、未解決なら示す。
反例で修正した後も、元の範囲の残りをこの対応から確認する。既存入力の参照による保持もよい。
保持・置換・撤回を区別し、矛盾する旧値を最終入力に残さない。範囲の変更は明示する。
判断不能な field は欠測として残し、空集合・零・false・不在で埋めない。
読めなかったファイルや不明な呼出し先も、確認できた事実と分けて報告する。

## 語彙と Law を作る

Atom 定義は語彙・型・meaning を持ち、Law と ArchMap が版と digest で参照する。
意味が異なる対象を同じ宣言に押し込めず、同じ意味の対象を名前の違いだけで分裂させない。
meaning は対象、位置、値の読みを説明し、観測値や診断結果を置かない。
宣言の対象を読んだ操作・文脈・要求に合わせる。静的な操作なら条件・作用・出口の対応を表す。
「条件を満たすとき更新する」を、全対象が現在その条件を満たすという Law に置き換えない。
条件付きの例は、例の入力条件と原典の操作を分ける。field の型と値には順序や null 可能性など、
問いが区別する意味を残す。未知の値を説明文字列で代用しない。
名前付き操作や対象間の対応に arrow や Map を使い、元コードのクラス構造をそのまま owner に写さない。

Law は要求・読取り・許可する変更を記述する。由来を次の観点で根拠へ戻して確認する。
これらは DSL の種別ではなく、同じ Law に複数の由来があってよい。

- 仕様: API 仕様や要求が定めた条件と、その適用範囲。
- 規約: 明示された設計判断が要求する依存・責務・操作の関係。
- ふるまい: 実装や仕様に記述された作用・条件・状態変化・順序・対応。

現在の操作の関係を view や optional な式で読み、将来も保つ義務への採用は別に判断する。
required にする関係は要求根拠と対応づけるか、利用者の採用判断を得る。要求が未採用でも、
原始値から具体的な関係を評価することはできる。反復パターンを無条件の義務へ昇格させない。
Law の妥当性と ArchMap の忠実性を別々に照合し、Law に合うように観測を変更しない。
Law は根拠が求める関係を、操作・文脈の原始 field から読む式にする。
要求文、適用条件、式が読む値、式の結果を対応づける。宣言数や非空の説明、由来ラベルで代用しない。
要求を満たす別の実装案でも提案 Law が成立するかを考える。要求が許す候補対で Law 値が
分かれるなら、その内部手段の区別まで要求済みとは扱わず、追加の保存仮説として分ける。

## 三入力の書き方

最小の動く形は [Atom 定義](assets/operation.atoms.json)、[Law](assets/operation.law)、
[ArchMap](assets/operation.archmap.json)。架空の仕様「入力条件が不成立なら更新に到達しない」を、
二つの静的経路で読む。提示モデルは成立側で更新して return、不成立側で更新せず throw する。
要求は満たす一方、追加仮説「拒否側も正常 return する」は反証される。実 OSS の観測や実行の実測ではない。
条件、作用、出口を別の原始値にし、要求への適合判定は Law に残す。例の二分岐で足りなければ必要な区別を追加する。
例の名前・meaning・field・origin は対象に合わせて設計し、binding の digest も更新する。

共通の semantics は `archsig/0.6.0`。JSON は UTF-8、BOM・重複 key・未知欄・null を使わない。
Id は `[A-Za-z][A-Za-z0-9_.-]*`、Law の Name は `[A-Za-z][A-Za-z0-9_]*`、
QName は Name の `.` 区切り。予約語や固定演算名を宣言・束縛名に使わない。

Atom 定義の形:

```text
{format:"archsig.atom-definition/1", semantics:"archsig/0.6.0", vocabularies:[
  {semantics:"archsig/0.6.0", namespace:Name, version:String,
   dependencies:[{namespace,version,digest}], declarations:[Declaration]}
]}
Declaration = {kind:"entity"|"arrow"|"correspondence", name:QName, meaning:String,
               parameters:[Field], fields:[Field], alignments:[{source:QName,target:QName,meaning:String}]}
            | {kind:"data", name:QName, meaning:String,
               constructors:[{name:Name,arguments:[Type],meaning:String}]}
Field = {name:Name,type:Type,meaning:String}
```

`version` と `meaning` は非空。宣言名は `N.E`、Atom の field 参照は `N.E.f`、field と constructor の name は短名。
parameters は後続 field の依存型が参照する。根 entity は owner を持たず、所属する entity の
owner は根 entity への参照。所属を多段化しない。arrow は名前付き操作を保存し、
`owner:R` を parameters の Field、`from:E[owner], to:E[owner]` を fields の Field として持つ。
JSON ではそれぞれ `["Ref","N.R"]` と `["Owned","N.E","owner"]` を使う。原始の Path 型は作らない。
correspondence は根間の `from:R,to:S` と owned 型間の全域 Map を持つ。
異なる型間の field 対応は alignments で明記する。対応候補の保存判定は計算に渡す。

型と値の代表的な対応:

| Type (JSON) | 値 |
| --- | --- |
| `"Unit"`, `"Bool"`, `"Text"` | `[]`, 真偽値, 文字列 |
| `"Z"`, `"Q"`, `["Fp","p"]` | 正規10進整数文字列、既約の `["分子","正の分母"]`、`0..p-1` の整数文字列 |
| `["Ref","N.E"]` | `["snapshot","subject"]` |
| `["Owned","N.E","owner"]` | 語彙内の依存型。値は同じ owner に属する Ref |
| `["Tuple",T,U]`, `["List",T]`, `["Set",T]` | 配列。Tuple の位置、List の順序・重複を保持。Set は重複なし |
| `["Option",T]` | `{"none":true}` または `{"some":値}` |
| `["Data","N.D"]` | `{"tag":"短いconstructor名","args":[値,...]}` |
| `["Map",E,F]` | `[[参照,参照],...]`。登録された始域族上の全域単一値対応 |
| `["Term",[T,...],U]` | `{"params":["x",...],"body":"x + 1"}` |

Term は引数以外の自由変数、field、観測族を持たない純粋な有限式。
意味を閉じた式で記述できない処理は、必要な原始事実や関係を記録して不足を説明する。
Set は Term を含めず、項の構文一致を関数の外延等値にしない。

ArchMap の形（`?` は省略可能な欄）:

```text
{format:"archsig.archmap/2", semantics:"archsig/0.6.0",
 vocabularies:[{namespace,version,digest}],
 sources:[{id,uri,revision,digest}],
 origins:[{id,mode,method,locations:[{source,path,span?:[start,end]}],note?:String}],
 snapshots:[{id,origin,subjects:[{id,type:QName,origin}],
             atoms:[{id,subject,field:QName,value,origin}]}]}
```

Source は非空 uri/revision と `sha256:` + 小文字16進64桁の内容 digest を持つ。
uri/revision が指す内容単位を決め、その bytes から digest を計算して source ID に結ぶ。
単位が一つのファイルなら全ファイル bytes を使う。意味を読む範囲と digest 対象を区別する。
Location.path は source root 相対の `/` 区切り。絶対 path、空、`.`/`..` segment を使わない。
span は UTF-8 **byte** の半開区間であり、行番号ではない。範囲を実 bytes と照合する。
observed は実装の使用箇所を1件以上指す。proposed/specification で locations が空なら非空 note が必要。
snapshot と所属 subject/atom の mode を一致させ、候補や仕様を別 snapshot に分ける。
同一 snapshot の subject/field は一度だけ記録する。宣言済み subject の未記録 field は未知、
存在しない subject を勝手に補完しない。cover、行列、判定、保存証拠は原始 Atom に入力しない。

根拠を読み返すときは、保存した Atom の既存参照を展開して内容 digest と位置を照合する。

```sh
python3 "$skill/scripts/evidence.py" "$work/observation.json" --atom snapshot/atom \
  --source "code=/path/to/target/source-file"
```

`--atom` と `--source` は繰り返せる。source の digest 単位が一つのファイルである場合に使い、
source ID と実ファイルを対応させる。値・共通 origin・実 bytes の抜粋を一緒に読み、
Law の読取りと照合する。補助は既存参照、digest、UTF-8 位置を照合するだけで、必要な依存先を
推測したり意味支持を判定したりしない。各 source へ到達する Atom を選び、未到達の登録 source は
別途実内容の hash と照合する。根拠が足りなければ該当する文脈へ読解を戻す。

Law の最小文法:

```text
law "archsig.law/2" semantics "archsig/0.6.0";
reading R {
  use vocabulary N version "1" digest "sha256:...";
  view value(x: N.E): Z = x.amount;
  law required positive(x: N.E) when x.enabled: x.amount >= 0;
  local amountOnly(x: N.E) reads x.amount;
  change adjust(x: N.E, n: Z) = x with {amount = n};
}
```

各宣言は必要なものだけ置く。`required` と `optional`、guard と Bool body を区別する。
guard=false は不適用、未知は未知として保持する。view は型付き純粋読取り、local は公開する値、
change は許可された値変更を表す。change で owner・参照・Map・subject roster を変えない。
`relation name(parameters): pathExpression = pathExpression;` は同じ始終型の名前付き操作列の同効果を要求する。
Path は `path(e)`, `identity(x)`, `then(p,q)` で構成する。
宣言の parameter 型は `N.E`, `N.E[owner]`, `List<T>`, `Set<T>`, `Option<T>`,
`Map<E,F>`, `Term<(T,...)->U>`, `Path<E,F>`、Tuple は `(T,U)` 等。
式は field 射影、型付き等値 `= / !=`、算術、`and/or/not/implies`、`if/then/else`、
`let x = e in body`、`forall x in xs . body` 等を使う。subject ID や観測値を Law の定数として貼り込まない。
文字列は JSON string、コメントは `//` から改行まで。型名と次の語は宣言・束縛名に使わない。

```text
law semantics reading use vocabulary version digest as entity arrow correspondence align data
view required optional local reads change relation when let in if then else match forall exists
not implies or and with true false unit list set where none some fn
```

`owner/from/to` は field 名に使える。`use Other as O;` は同じ Law ファイル内の reading を参照する。
再利用する reading も同梱し、直接使う原始 namespace を各 reading で import する。
短名が衝突するときは完全名を使う。束縛の shadowing、reading 間の循環を作らない。

| 式 | 型・意味 |
| --- | --- |
| `(a,b)`、`x.0` | Tuple と0始まりの成分射影 |
| `list<T>[a,b]`、`set<T>{a,b}` | 同型の有限 List / Set。空でも型を記す |
| `set { e \| x in xs where p }` | 有限族の各要素から作る集合。where は省略可 |
| `none<T>`、`some(e)` | Option の不在 / 存在 |
| `D.Ctor(a,b)`、`match e { D.Ctor(x,y) => body; _ => fallback; }` | data の構築 / 分岐。constructor 全て又は末尾 `_` で全域を覆う |
| `forall x in xs . p`、`exists x: T . p` | 有限 List/Set の要素、又は型の全域で量化。未束縛 Law 引数も型の全域で全称化 |
| `count(xs)`、`sum(xs)`、`x in xs` | 有限 List/Set の件数（Z）、数値和、所属 |
| `rat(n,d)` | 整数 literal n,d、d>0 の有理数。数値型間の暗黙変換なし |
| `m(x)`、`t(x)`、`fn(x: Z) => x + 1` | Map / Term の適用、閉じた Term の構築 |
| `source(p)`、`target(p)` | Path の端点 |

二項演算の優先度は弱い順に `implies`、`or`、`and`、`= != < <= > >= in`、`+ -`、`*`。
`implies` は右結合、比較の連鎖は禁止。順序比較は Z/Q、算術は同じ Z/Q/Fp 型で行う。
`count/sum/rat/path/identity/then/source/target` も宣言・束縛名に使わない。
if の両枝と match の各枝の結果型を揃える。view の自己再帰は左端の data 引数の match で
得た直接の再帰 subterm に限る。Term は参照・field・観測族・view を捕獲しない。
空の有限域の forall は true、exists は false。未知 slot の読取りは同じ未知を保持し、
Law が成立する値で補完しない。型や参照条件を保つ全補完で確定できる値・命題だけを確定する。
local がなければ支持による reading が構成される。原式の出現や局所の読取りを消す書換えは、
値が同じでも診断が同じとは限らない。

語彙 binding は定義確定後の vocabulary manifest の canonical JSON の SHA-256 から作り、
Law と ArchMap の vocabulary 参照に設定する。source の内容 digest とは別の内容から作る。
再検査では source ID→実内容と namespace/version→manifest をそれぞれ照合する。
declarations を完全名順、dependencies を namespace 順、alignments を (source,target) 順にし、
parameters/fields/constructors/arguments の順序を保持する。object key は Unicode scalar 順、
空白なし、非 ASCII は UTF-8、制御文字は小文字4桁の `\u00xx`、`/` は escape しない。
meaning も含める。定義を変えたら新しい version と digest を使い、依存 binding も更新する。
CLI が利用できれば、作成した定義 `definitions.json` に対して、次だけを含む
一時的な `bootstrap.law` を `work` に作る。

```text
law "archsig.law/2" semantics "archsig/0.6.0";
reading Bootstrap {}
```

```sh
"$cli" check --atom-definition "$work/definitions.json" --law "$work/bootstrap.law" --out "$work/binding-new"
```

標準出力 receipt の `result` が指す JSON の `vocabularies` 配列を読む。
各要素の `manifest.namespace`、`manifest.version`、`digest` を、そのまま本来の Law の
`use vocabulary` と ArchMap の binding に設定して三入力を再検査する。
複数の定義ファイルは依存分も `--atom-definition` を繰り返して明示指定する。
形式エラーを直した後も、修正前後の定義・Law・観測を照合し、宣言や要求が消えていないことを確認する。

## 計算へ渡し、更新する

バンドルの CLI で入力を検査する。まず同梱例を確認できる。

```sh
"$cli" check --atom-definition "$skill/assets/operation.atoms.json" --law "$skill/assets/operation.law" --archmap "$skill/assets/operation.archmap.json" --out "$work/check-new"
"$cli" run --atom-definition "$skill/assets/operation.atoms.json" --law "$skill/assets/operation.law" --archmap "$skill/assets/operation.archmap.json" \
  --ask 'v=evaluate(OperationReading.normalExit,bind.branch=@v/rejected)' \
  --ask 'c=check(OperationReading.guardedUpdate,bind.branch=@v/rejected)' --ask 'n=needed($c)' --out "$work/run-new"
```

出力先は毎回未存在のディレクトリ。実入力では3つのファイルパスも作成した絶対パスへ置き換える。同梱例では `branch` が宣言の parameter、`v` が snapshot、
`rejected` が subject の ID。実入力ではこれらをその宣言と登録 ID に合わせる。
`@snapshot/subject` の二つの ID と `bind.parameter` を使い、`on` は Architecture の環境指定として分ける。
この例は出口の値 false と要求成立を別の出力で返す。`check(OperationReading.rejectedReturnsNormally)` は追加仮説を反証する。
`build(Reading,on=@snapshot/root)` や `map(N.C,on=@snapshot/candidate,reading=Reading)` は問いに応じて選ぶ。
`needed` の不足 slot は元の subject/field/source に戻って読み、その他の未決理由と分ける。
CLI が未提供・非対応なら三入力とソース照合を進め、接続は未検証と報告する。
例示結果を実計算の証拠にしない。
標準出力は receipt JSON。`result` は呼出し cwd からのパスで、結果が作られなければ省略される。
保存結果の `answers` を問い ID で対応させ、`status`、`outputs` と依存先の `nodes`、`issues` を読む。
評価値 false と命題 refuted を区別する。`needed` は欠測 slot と他の未決理由を返す。
終了0は検査成功又は全問い確定・反証なし、1は全問い確定・反証あり、2は未決を含む。
64は使い方、65は入力、69は版非対応、70/74はinternal/io、130/143は中断。
終了コードだけで意味を判定せず、receipt と保存結果の理由・位置を確認する。
実行時間を区切るときは SIGINT/SIGTERM を送る。再利用は `--reuse OLD_DIRECTORY`。
再利用先も利用者の保存結果を明示し、旧入力を新しい観測へ読み替えない。

コード変更は該当する使用箇所と、その値を使う呼出し元・呼出し先を再読解する。
Law の変更は新たな読取りに必要な slot と十分性を確認する。語彙変更は意味・版・全参照を再照合する。
古い revision を新しい実装へ読み替えず、再確認した事実に新しい由来を付ける。
名前付き arrow、owner、対応 Map、値・項の出現、局所で読める値と要求根拠を保持し、
貼り合わせ・輸送・経路比較・変更の分類・再構成に必要な原始情報を計算へ渡す。
現行入力で表現できない関係は具体例と不足する情報を説明し、入力を捏造しない。

## 有限族上の Law 十分性を使うとき

同じ問いで比較する source または候補モデルの有限族 S、観測 q、Law 評価族 v を明示する。
ファイル一覧をそのまま S にせず、各要素が何を表すかを説明する。
各 v 列に対応する Law または view の宣言・引数・適用条件を定め、対象モデル上の式の結果を置く。
粗い q から再構成せず、対象のソース・要求から独立に読む。操作の結果値と Law の成立を分ける。
結果が false であることと「false になる」という関係の不成立は異なる。
CLI を使った場合は同じ保存入力の結果、手で評価した場合は同じ式の代入と適用条件を照合する。
view 値の十分性はその読取りについて述べ、別の Law の成立判定として扱わない。
必要な全要素を列挙でき、全 Law 値とその等号を確定できた場合に次の補助を使う。

```json
{"scope":"二つの候補モデルについて、選択した保持条件を比較する",
 "sources":["a","b"],"laws":["preserves"],
 "q":{"a":"same","b":"same"},
 "v":{"a":{"preserves":"yes"},"b":{"preserves":"no"}}}
```

`python3 "$skill/scripts/law_fibers.py" "$work/table.json"` は全 q fiber の全対を検査し、
反例対、全 Law 値による partition、十分なら q 上への descent を返す。
終了コードは十分=0、反例あり=1、不正/不完全な表=2。空族の空虚性も出力する。
q と v の値は**等号を保つと確認した非空文字列 token**。未知を `"unknown"` 等の token にせず、
未確定の評価があれば表を完成扱いしない。異なる表現の同じ意味は読解側で対応づける。
この表は補助計算の入力であり、ArchSig の三入力や計算結果の代用にはしない。

計算する条件は `q(s)=q(t) ⇒ ∀law, v(s,law)=v(t,law)`。
この有限表では同じ q 値の要素をまとめ、各 Law 値がその中で一定なら、その値を
q の像上へ一意に降ろせる。全 Law 値の tuple による partition は、指定した全 Law 値を
保つ最も粗い区別になる。これは列挙した族と確定した値の等号を前提とする。
補助は全対比較でこの条件を検査する。表に置いた値のソース忠実性は別に照合する。
反例対があれば元の使用箇所へ戻り、失われた意味を読解単位・三入力・q に反映して再検査する。
対だけのモデルを別に作る場合も元入力との保持・置換を示す。Law の追加・S や v の変更でも再検査する。
指定 v の十分性と、元の範囲の意味回収は別々に確認する。

報告はソース忠実性、経験的精度、指定表上の Law 十分性、診断保存を分ける。
診断保存には実際の被覆・係数・複体・比較写像と対象類を確認する。
有限表が返すのは指定 Law 値の保存までである。診断の比較を実計算し、対象と比較写像・
検査条件を確認できない場合、診断保存は未検証として扱う。有限表から H¹ 保存を結論しない。

## 精度を測るとき

revision、問い、業務範囲、使用モデル、試行数・読解予算を固定する。
調整用と最終評価用を業務範囲または OSS で分離し、強く結びつく呼出し先や複製を両側へ置かない。
候補出力を見る前に、独立した読解で範囲全体の意味単位と根拠を確定する。
候補が触れなかった箇所も読み、候補の和集合を参照集合にしない。
別名・分割・統合は意味で対応づけ、同じ事実の重複を回収数や precision の分子に足さない。
新しい正しい候補で参照を直す場合は、当初の評価と改訂後の評価を分ける。

precision = 支持された出力意味単位 / 判定できた出力意味単位。
反する主張・根拠のない断定を誤観測に数える。
recall = 確定参照の正しい回収数 / 確定参照数。棄権も未回収に残す。
棄権、出力未判定、参照未判定、未読範囲は別に数え、回答率の母数も明記する。
母数0の率は未定義。Law の根拠と DSL の対応は観測 precision から分け、三つの由来ごとに確認する。
判断が割れた事例は根拠とともに人間へ返す。
利用者が精度の評価を求めた場合、対象と採用水準を評価前に合意する。
改善を主張する比較は同じ範囲・予算・参照で行う。結果と代表的な誤りを利用者の指定先へ返す。
