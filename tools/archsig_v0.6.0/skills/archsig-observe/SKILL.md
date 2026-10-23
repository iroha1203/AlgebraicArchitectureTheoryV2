---
name: archsig-observe
description: Read a repository's implementation and requirement sources to create, reuse, or update ArchSig 0.6.0 Atom definitions, Law, and ArchMap with source evidence. Use for architecture questions and proposed changes requiring semantic observation.
---

# ArchSig Observe

対象リポジトリと「理解したいこと・実現したい変更」から、使用文脈を読んだ三入力を作る。
利用者が指定した出力先に、Atom 定義 JSON、Law DSL、ArchMap JSON を渡す。
研究リポジトリの checkout は不要。このファイルと同梱 assets/scripts を使う。
観測の根拠・不足・検証結果は利用者の会話または指定された Issue に説明し、
依頼されていないレポートや repo 内の実験ログを増やさない。

## 問いから読解へ

問いに関係する業務範囲と revision を選ぶ。既存の Atom 定義・Law があれば意味と版を読み、
共有する語彙と変更する reading を分ける。要求の根拠、原始事実、候補設計のどれを読むかを決める。
根拠資料が見つからない要求や、実装の慣習を今後も守る要求へ採用する判断は利用者に返す。

関係する実装を、呼出し元、引数の由来、分岐条件、返り値の使用、状態更新、呼出し先まで追う。
必要な範囲は問いに応じて選び、同名のメソッドや定数だけから役割を決めない。
たとえば、`save` の前後で保持する値、応答の status を検査する呼出し元、
別メソッドを介して同じ対象を更新する関係を読む。
選んだ範囲を入口から出口まで読み、各操作の条件、正常・例外・何もしない経路を照合する。
使われる値の初期値・既定値、公開される変更手段、継承先の実体まで、問いに必要な文脈を追う。
一度書いた主張だけを見直さず、ソース側から出力へ戻って未記述の経路や条件を探す。
似た操作の説明を流用しない。更新・通知・返却の順序はその経路の実文を読み、
途中で失敗すると既にどこまで変化しているか、不変だと述べる範囲はどこかを確かめる。
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
三入力の草稿を作った後、完成したファイルと原典を開き直し、生成時の記憶に頼らず二方向で照合する。
ソースから出力へは、選択範囲の公開境界・初期化・各分岐（非適用も含む）・依存する操作について、
読んだ意味がどの Atom に残ったかを見る。説明文にしかない条件も入力へ戻す。
出力からソースへは、各 Atom の値とその origin の引用を照合する。型の変更可能性と操作の作用など、
根拠が異なる内容を一つの説明に詰め込まず、必要なら分けてそれぞれの根拠を付ける。
支えられない値や取りこぼしを見つけたら、その区別に必要な文脈だけを読み足して草稿を直し、
直した値と引用を再照合してから渡す。読める不足を黙って削除して精度を上げず、未解決なら不足として示す。
この往復で、転記により作用を増減させたり、似た経路の更新を混ぜたりしていないことも確かめる。
分岐、所有対象、順序、量の位置が違えば別の事実として保持する。
判断不能な field は欠測として残し、空集合・零・false・不在で埋めない。
読めなかったファイルや不明な呼出し先も、確認できた事実と分けて報告する。

## 語彙と Law を作る

Atom 定義は語彙・型・meaning を持ち、Law と ArchMap が版と digest で参照する。
意味が異なる対象を同じ宣言に押し込めず、同じ意味の対象を名前の違いだけで分裂させない。
meaning は対象、位置、値の読みを説明する。観測済みの値や診断結果を置かない。

Law は要求・読取り・許可する変更を記述する。由来を次の観点で根拠へ戻して確認する。
これらは DSL の種別ではなく、同じ Law に複数の由来があってよい。

- 仕様: API 仕様や要求が定めた条件と、その適用範囲。
- 規約: 明示された設計判断が要求する依存・責務・操作の関係。
- ふるまい: 実装や仕様に記述された作用・条件・状態変化・順序・対応。

観測した反復パターンはまず事実や問いとして示す。ふるまい由来の関係を required にする際も、
要求根拠との対応、または利用者の採用判断を得る。未採用の仮説は候補として説明する。
Law の妥当性と ArchMap の忠実性を別々に照合し、Law に合うように観測を変更しない。

## 三入力の書き方

最小の動く形は [Atom 定義](assets/counter.atoms.json)、[Law](assets/counter.law)、
[ArchMap](assets/counter.archmap.json)。これは件数2の仕様モデルであり、実 OSS の観測結果ではない。
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

`version` と `meaning` は非空。宣言名は完全名、field と constructor の name は短名。
parameters は後続 field の依存型が参照する。根 entity は owner を持たず、所属する entity の
owner は根 entity への参照。所属を多段化しない。arrow は `owner:R, from:E[owner], to:E[owner]`
を持ち、名前付き操作を保存する。原始の Path 型は作らない。
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
内容が一意に分かる単位（例: 固定 revision のファイル bytes）を選び、その単位を説明する。
Location.path は source root 相対の `/` 区切り。絶対 path、空、`.`/`..` segment を使わない。
span は UTF-8 **byte** の半開区間であり、行番号ではない。範囲を実 bytes と照合する。
observed は実装の使用箇所を1件以上指す。proposed/specification で locations が空なら非空 note が必要。
snapshot と所属 subject/atom の mode を一致させ、候補や仕様を別 snapshot に分ける。
同一 snapshot の subject/field は一度だけ記録する。宣言済み subject の未記録 field は未知、
存在しない subject を勝手に補完しない。cover、行列、判定、保存証拠は原始 Atom に入力しない。

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
`Map<E,F>`, `Term<(T,...)->U>`, `Path<E,F>` 等。
式は field 射影、型付き等値、算術、`and/or/not/implies`、`if/then/else`、
`let x = e in body`、`forall x in xs . body` 等を使う。subject ID や観測値を Law の定数として貼り込まない。
local がなければ支持による reading が構成される。原式の出現や局所の読取りを消す書換えは、
値が同じでも診断が同じとは限らない。

語彙 digest は vocabulary manifest の canonical JSON の SHA-256。
declarations を完全名順、dependencies を namespace 順、alignments を (source,target) 順にし、
parameters/fields/constructors/arguments の順序を保持する。object key は Unicode scalar 順、
空白なし、非 ASCII は UTF-8、制御文字は小文字4桁の `\u00xx`、`/` は escape しない。
meaning も含める。定義を変えたら新しい version と digest を使い、依存 binding も更新する。
CLI が利用できれば、最初は import のない reading で `check` し manifest/digest を得てから
Law と ArchMap に binding を設定し、三入力を再検査する。
形式エラーを直した後も、修正前後の定義・Law・観測を照合し、宣言や要求が消えていないことを確認する。

## 計算へ渡し、更新する

利用できる対象版の `archsig version` を確かめ、入力を検査する。

```sh
archsig check --atom-definition atoms.json --law reading.law --archmap observation.json --out check-new
archsig run --atom-definition atoms.json --law reading.law --archmap observation.json \
  --ask 'c=check(R.positive)' --ask 'n=needed($c)' --out run-new
```

出力先は新しいディレクトリ。宣言名と問いは実際の入力に合わせる。
`build(R,on=@snapshot/root)`、`evaluate(R.value,x=@snapshot/entity)`、
`map(N.C,on=@snapshot/candidate,reading=R)` などを問いに応じて選ぶ。
`needed` の不足 slot は元の subject/field/source に戻って読み、その他の未決理由と分ける。
CLI が未提供・非対応なら三入力とソース照合を進め、接続は未検証と報告する。
例示結果を実計算の証拠にしない。

コード変更は該当する使用箇所と、その値を使う呼出し元・呼出し先を再読解する。
Law の変更は新たな読取りに必要な slot と十分性を確認する。語彙変更は意味・版・全参照を再照合する。
古い revision を新しい実装へ読み替えず、再確認した事実に新しい由来を付ける。
名前付き arrow、owner、対応 Map、値・項の出現、局所で読める値と要求根拠を保持し、
貼り合わせ・輸送・経路比較・変更の分類・再構成に必要な原始情報を計算へ渡す。
現行入力で表現できない関係は具体例と不足する情報を説明し、入力を捏造しない。

## 有限族上の Law 十分性を使うとき

同じ問いで比較する source または候補モデルの有限族 S、観測 q、Law 評価族 v を明示する。
ファイル一覧をそのまま S にせず、各要素が何を表すかを説明する。
各 Law 値は粗い q から再構成せず、対象のソース・要求から独立に読む。
必要な全要素を列挙でき、全 Law 値とその等号を確定できた場合に次の補助を使う。

```json
{"scope":"二つの候補モデルについて、選択した保持条件を比較する",
 "sources":["a","b"],"laws":["preserves"],
 "q":{"a":"same","b":"same"},
 "v":{"a":{"preserves":"yes"},"b":{"preserves":"no"}}}
```

`python3 scripts/law_fibers.py table.json` は全 q fiber の全対を検査し、
反例対、全 Law 値による partition、十分なら q 上への descent を返す。
終了コードは十分=0、反例あり=1、不正/不完全な表=2。空族の空虚性も出力する。
q と v の値は**等号を保つと確認した非空文字列 token**。未知を `"unknown"` 等の token にせず、
未確定の評価があれば表を完成扱いしない。異なる表現の同じ意味は読解側で対応づける。
この表は補助計算の入力であり、ArchSig の三入力や計算結果の代用にはしない。

計算する条件は `q(s)=q(t) ⇒ ∀law, v(s,law)=v(t,law)`。
q の標的を像に取れば全射であり、`FiniteLawFamily.adequate_iff_kernel` の条件に対応する。
全 Law 値の partition は `computedClass_eq_iff` / `computed_adequate` /
`computed_kernelEquivalent_jointKernel` が扱う有限計算に対応し、
`jointKernel_universal` はこれが Law 値を保つ最も粗い reading であることを述べる。
補助 Python 自体の正しさは同梱テストで検査し、Lean 検証済みプログラムとは表示しない。
反例対があれば元の使用箇所へ戻り、失われた意味を q に追加して検査し直す。
Law の追加・S の変更でも再検査する。

報告はソース忠実性、経験的精度、指定表上の Law 十分性、診断保存を分ける。
診断保存には実際の被覆・係数・複体・比較写像と対象類を確認する。
`generatedComparisonH1Map_bijective` の適用では両 reading の十分性と実 nerve 比較の条件 C を確認する。
C0–C6 の十分条件や固定比較の核・余核検査は、必要な主張に合うものを選ぶ。
有限表の十分性だけから H¹ 保存を結論しない。

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
予備評価後に許容誤観測・見逃し・回答率を一度提案し、合意した水準で最終評価する。
改善を主張する比較は同じ範囲・予算・参照で行う。結果と代表的な誤りは指定された Issue に残す。
