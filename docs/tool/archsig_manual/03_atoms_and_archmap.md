# 3. Atom と ArchMap

ArchMap は、コードから観測した Atom の記録だ。

## Atom の形

Atom は JSON の一行で書く。どの Atom も次の欄を持つ。

- `kind`:Atom の種類。
- `subject`:何についての事実か。コードの要素の名前を書く。
- `at`:観測した場所。`パス:行@<版>` の形で書く。パスはリポジトリの根からの相対パスである。版はソースの内容を指し、`blob:<hex>` か 7 文字以上の `<hex>` で書く。行は `10-14` のような範囲でもよい。
- `by`:誰が観測したか。解析器の名前と版、またはモデルの名前を書く。

種類ごとに、次の欄が加わる。

| 種類 | 加わる欄 |
| --- | --- |
| `defines` | `value`(要素の種類)、`params`(操作の引数と型)、`type`(フィールドの型)、`file`(候補の中だけ) |
| `calls`、`reads` | `object`、`when` |
| `imports` | `object` |
| `resolves` | `object` |
| `writes` | `object`、`via`、`value`、`when` |
| `passes`、`sends` | `object`、`value`、`when` |
| `receives` | `object`、`value` |
| `returns` | `value`、`when` |
| `meaning` | `meaning`、`value`、`uses` |
| `observed` | `scope` |
| `plan` | `base` |
| `corresponds` | `object` |
| `removes` | なし |

Atom の同一性は、`kind`、`subject`、`object`、`via`、`value`、`when`、`meaning`、`scope` で決まる。
`at` と `by` は同一性に入らない。行がずれても、同じ事実は同じ Atom である。
同一性は、二つの ArchMap や、候補と実装の Atom を比べるときに使う。
一つの操作の中で同じ Atom が二度出れば、二つの手順である。同じ操作を二度呼べば、`calls` が二つ並ぶ。

## 要素の名前

`subject` と `object` には、コードの要素の名前を書く。要素は、操作、型、フィールド、引数、チャネル、呼び出しの六つだ。

- 操作と型は、その言語の完全修飾名で書く。Python ならモジュールのパスと名前(`shop.shipping.service.update_shipping`)、Java ならパッケージとクラスと名前である。
- フィールドは `<型の名前>.<フィールドの名前>` と書く(`shop.order.model.Order.payment_ref`)。
- 引数は `<操作の名前>.$<引数の名前>` と書く(`shop.shipping.service.update_shipping.$new`)。
- チャネルというのは、キューのトピック、HTTP のルート、イベントのように、プロセスやサービスをまたいで操作をつなぐ名前のこと。形は次の三つに決める。
  - `channel:http:<メソッド> <パスのテンプレート>`(`channel:http:POST /orders`)
  - `channel:queue:<トピック>`
  - `channel:event:<イベントの名前>`

  チャネルで運ぶ中身の項目も要素になる。`channel:queue:order-placed:amount` のように、チャネルの名前に `:<項目>` を続ける。
  ArchSig は、`:` で四つ以上に分かれる名前の最後を項目とみなす。チャネルの名前(パスのテンプレートやトピック)の中には `:` を書かない。
- 呼び出しの一つ一つも要素になる。名前は `<呼び出し元>-><呼び出し先>` で、同じ組が一つの操作に二度あれば、行の順に `#2`、`#3` を付ける。

言語が違っても、同じチャネルは同じ名前になる。Python の `requests.post("/orders")` も、Java の `@PostMapping("/orders")` も、`channel:http:POST /orders` と書く。

解析器が名前を解決できなかった所は、書かれたとおりの字句の前に `?` を付ける(`?mail.send`)。
`?` で始まる名前が関わる計算で、ArchSig は結論を出さず、沈黙する。

## 構造 Atom

構造 Atom は、構文から決まる事実だ。エージェントが言語に合う解析器を選んで取り出す(第7章)。種類は次の十で、言語によらず同じである。

- `defines`:要素を定義する。`value` は `operation`、`type`、`field` のどれか。`value` のない `defines` を持つ要素は、種類の違う `defines` を持つ要素と同じく、種類の決まらない要素として扱う。同じ種類の `defines` を二か所以上に持つ要素も、どちらの定義かが決まらないので同じに扱う。
  操作は `params` に引数の名前と型を持つ(`{"order": "shop.order.model.Order", "new": "shop.shipping.model.Address"}`)。フィールドは `type` に型を持つ。
- `calls`:操作が別の操作を呼ぶ。
- `reads`:操作がフィールドを読む。
- `writes`:操作がフィールドに書く。`value` に書く値を持つ。
  `object` は書いたフィールドである。フィールドの値の中のフィールドに書くときは、そこまでにたどるフィールドを `via` に順に並べる。
  注文の配送先の国に書くなら、`via` は `["shop.order.model.Order.shipping_address"]`、`object` は `shop.shipping.model.Address.country` である。
  この書き込み先は、`$order.shipping_address.country` で読む値と同じ所である。`via` がなければ、引数が指す実体のフィールドに書く(`$new.country` で読む値と同じ所)。
- `passes`:呼び出しが引数に値を渡す。`subject` は呼び出しの名前、`object` は受け取る引数(`<呼び出し先>.$<引数の名前>`)である。外部でない呼び出しで、受け取る引数が呼び出し先の引数になければ、渡す値の行き先が決まらないので、その呼び出しを展開する操作は `unresolved` で沈黙し、呼び出しの場所を返す。`when` のない `passes` は、呼び出しの条件で渡す。`passes` に呼び出しと違う `when` があるか、一つの引数に値の違う `passes` が二つ以上あれば、渡す値が一つに決まらないので、その呼び出しを展開する操作は `unresolved` で沈黙する。
- `sends`:操作がチャネルの項目へ値を送る。`object` は項目、`value` は送る値である。
- `receives`:操作がチャネルの項目を受け取る。`object` は項目、`value` は受け取った値を操作の中で表す式である。
- `returns`:操作が値を返す。`value` は返す値である。`returns` の後の手順は、その `returns` を行わなかった分岐でだけ行う(`if c: return` の後の手順は、`c` が成り立たない分岐で行う)。`returns` の `when` は、`returns` の時点で一度だけ読む。`when` のない `returns` の後の手順は行わない。呼び出し先の `returns` は、呼び出し元の手順を止めない。
  観測した Atom の手順は、`at` の行の順(行の範囲は最初の行)、同じ行では Atom の順に並ぶ。戻り値の式の中の呼び出しと送信(`return g(x)`)は、その `calls`、`passes`、`sends` を `returns` より前の Atom に書き、`returns` の `at` は return 文の最後の行の一行で書く。そうしないと、呼び出しや送信が `returns` の後の手順になり、行われない。
- `imports`:モジュールが別のモジュールを取り込む。
- `resolves`:名前が、どこで定義されているか。`object` は、定義したソースのパスか、リポジトリの外なら `external:<パッケージ>` である。解析器が名前を解決できたときに書く。言語の組み込みの型(Python の `str` など)も、リポジトリの外の名前として書く。

`calls`、`reads`、`writes`、`passes`、`sends`、`returns` は `when` を持てる。`if` の中の書き込みなら、その条件を `when` に書く。

### 値と条件の書き方

`value` と `when` は、解析器が次の小さな形に直して書く。

- 定数:`None`、`0`、`"JPY"`。
- 引数と、そこからたどるフィールド:`$new`、`$order.shipping_address.country`。
- 操作の呼び出し:`shop.shipping.address.normalize_address($new)`。
- 四則演算、比較、否定:`$order.total * 100`、`$new.country != $order.shipping_address.country`、`not $order.paid`。
- それ以外:`?`。

条件は `and`、`or`、`not` と括弧でつないで書ける。値の前に `-` を付けられる。文字列は `"…"` で書く。
ArchSig は、`and` でつないだ条件を一つずつの条件に分ける。`or` でつないだ条件と、`not` の中の `and` は、ひとまとまりの一つの条件として扱う(第6章「条件どうしの関係は見ない」)。二重の `not` は外してから分ける。
`$` も `?` も付かない名前(`None`、`JP_CODE`)は定数として読む。
二つの順番の値を比べるとき(第5章 問い3)、定数は字句で比べる。字句が同じ定数は同じ値、字句が違う定数は違う値とする。ArchSig は、名前の定数の値も、数の書き方の違い(`1` と `1.0`)も知らない。そのため、同じ値の定数は同じ字句で書く。名前の定数の値が分かるなら値で書き(`JP_CODE` が `"JP"` なら `"JP"`)、分からなければ名前のまま書く。
構文として読めない `value` と `when`(`a ?? b` など)は `?` と同じに扱う。字句に分けた式の字句の数が上限を超えれば、構文として読めるかや `?` を含むかを確かめる前に、値を求めずに `limit` で沈黙する。その式の中で名指す道、名前、呼び出しは字句から拾い、型のフィールドをたどるときの名指しに数える。消える要素を使うかの判定でも、`limit` で沈黙する。読む所は付けない。

局所変数は、解析器が代入した式で置き換えて書く。置き換えられなければ `?` と書く。
`$order.total` は、引数 `order` の型と、フィールドの型をたどって、フィールド `shop.order.model.Order.total` として読む。
`$order.shipping_address.country` は、フィールド `Order.shipping_address` の値の、フィールド `Address.country` として読む。
引数は、その型のただ一つの実体を指す。`$new.country` は、型 `Address` のフィールド `Address.country` の値である。

ArchSig は、操作の呼び出しの結果を、同じ操作に同じ値を渡せば同じ結果が返るものとして扱う。
ただし、Law で `fresh` と宣言した操作は、呼ぶたびに新しい値を返すものとして扱う(第4章)。
`?` が関わる計算では沈黙する。操作を書き込みの列にする(第5章 問い3)ときは、その操作と呼び出し先の、書き込み・送信・戻り値の値と、手順(書き込み、呼び出し、送信、戻り値)の条件に `?` が一つでもあれば、列を作らずに沈黙する。

## 意味 Atom

意味 Atom は、要素が何の役割を持つかという事実だ。種類は `meaning` の一つだけである。

```json
{"kind": "meaning", "subject": "shop.order.model.Order.payment_ref", "meaning": "payment-info",
 "uses": ["shop/payment/charge.py:22@blob:8b41d07", "shop/order/confirm.py:57@blob:c52e6fa"],
 "at": "shop/order/model.py:18@blob:1d9e3b4", "by": "model:claude-sonnet-5"}
{"kind": "meaning", "subject": "shop.order.confirm.confirm->mail.send", "meaning": "role",
 "value": "order-notice", "uses": ["shop/order/confirm.py:61-64@blob:c52e6fa"],
 "at": "shop/order/confirm.py:61@blob:c52e6fa", "by": "model:claude-sonnet-5"}
```

`meaning` には、Law が定めた意味の語彙の名前を書く。語彙が `values` で値を並べていれば、その一つを `value` に書く。

意味は使われ方で決まる。`uses` には、その意味だと読んだ根拠の使用箇所を書く。
呼び出し元、前後の処理、値の渡し先、分岐である。書き方は `at` と同じだ。

### 局所ごとの意味 Atom

意味は、要素一つずつではなく、局所ごとにまとめて観測することもできる。局所というのは、読みでコードを分けた一まとまりのこと(第4章)。

```json
{"kind": "meaning", "subject": "local:service:money", "meaning": "unit", "value": "minor",
 "uses": ["shop/payment/charge.py:22@blob:8b41d07"], "at": "shop/payment",
 "by": "model:claude-sonnet-5"}
```

`subject` は `local:<読み>:<局所の名前>` と書く。
この Atom は、その局所の中で、意味の語彙が対象にする要素すべてに同じ値を与える。
ArchMap は、局所ごとの意味 Atom を局所の名前ごとに置く(`.archsig/local/<読み>/<局所>.jsonl`)。ソースのファイルとぶつからないように、`.archsig/map/` の外に置く。`at` は読んだ場所の目安で、版を補わない。
この Atom が古いかは、`uses` のソースで決まる。ソースごとの読んだ範囲には数えない。
まとめて読むと観測の手間が減る。まとめてよいかは、第5章の問い5で確かめる。

## 読んだ範囲

ArchMap は、Atom のほかに、どこを読んだかを記録する。

```json
{"kind": "observed", "subject": "shop/shipping/address.py", "scope": "structure",
 "at": "shop/shipping/address.py@blob:9f2c4e7", "by": "tool:tree-sitter-python@0.23"}
{"kind": "observed", "subject": "shop/shipping/address.py", "scope": "meaning:payment-info",
 "at": "shop/shipping/address.py@blob:9f2c4e7", "by": "model:claude-sonnet-5"}
```

`scope` は、構造を読んだのか、どの意味を読んだのかを示す。`at` の版が、読んだときのソースの内容を指す。
計算は、与えた ArchMap の読んだ範囲を、古いかによらず読んだ範囲として扱う。古さは `archsig status` が返す(下)。

読んだ範囲に Atom がなければ、その事実はない。読んでいない所の事実は、分からない。
ArchSig はこの二つを区別する。分からない所が結論に関わるとき、ArchSig は沈黙し、そこを次に読む場所として返す。

定義を読んでいない要素については、`resolves` で次に読む場所を決める。

- `resolves` がソースを指していれば、そのソースを返す。問い合わせた要素そのものの `resolves` が指すソースの構造を読んでいるのに、その要素の定義がなければ、`unresolved` で沈黙する。
- `resolves` が外部を指していれば、観測した要素へ書き込まない呼び出しとして扱い、結果の `conditions` にそう書く。`changes commute` で書いたフィールドの型をたどるとき(第5章 問い3)、外部の型は、意味を持つフィールドを持たない型として扱い、同じく `conditions` に書く。
- `resolves` がなければ、要素の名前を返す。どのソースを読むかは、観測する SKILL が決める。
- 一つの名前に、指す先の違う `resolves` が二つ以上あれば、解決が決まらないので、`unresolved` で沈黙する。指す先が同じ `resolves` が重なるのは、一つと同じに扱う。
- 外部の型のフィールドを読むか書く手順は、そのフィールドが分からないので、`unresolved` で沈黙する。外部には読むソースがないので、読む所は返さない。

ソースが今の内容と違えば、その範囲は古い。意味 Atom は使われ方で決まるので、`uses` のソースが変わったときも古い。

`archsig status` は、古い範囲を `stale` に、読んでいない範囲を `unread` に返す。
`stale` の一つ一つは、観測し直す範囲(`source` と `scope`)、観測したときの版(`observed`)、今の版(`current`)を持つ。ソースが消えていれば、`current` は `null` である。
`uses` が変わった意味 Atom では、`source` と `scope` はその意味 Atom の範囲(局所ごとの意味 Atom なら `source` はその `subject`)で、要素(`element`)と、変わった使用箇所(`use`)も持つ。`observed` と `current` は、変わった使用箇所のソースの版である。
`stale` は `source`、`scope`、`element`、`use` の順に並ぶ。
`unread` の一つ一つは、`sources` のソース(`source`)と、構造と Law が宣言した意味のうち読んでいない範囲(`scopes`)を持つ。
`status` は、Law の誤りを `law_errors` に返す(第4章「書けているかを確かめる」の `errors` と同じ形)。Law に誤りがあっても、`status` は解けた `sources` と意味の語彙で動く。解けなかった宣言の `sources` や意味は、`unread` に出ない。

## ArchMap のファイル

リポジトリの根は、`archsig` を実行するディレクトリで、そこに `.archsig/` を置く。パスはどれも、この根からの相対パスである。

ArchMap は、ソースのファイルごとに一つの JSON Lines ファイルに分けて置く。

```text
.archsig/map/shop/shipping/service.py.jsonl
.archsig/map/shop/shipping/address.py.jsonl
.archsig/map/shop/order/model.py.jsonl
```

一つのファイルには、そのソースについての `observed` と、そこで観測した Atom が入る。ソースが変わったら、そのファイルだけを観測し直す。

`archsig record` は、ソースと観測の範囲(構造か、どの意味か)ごとに、元の Atom を置き換える。
`at` と `uses` に版がなければ今のソースの版を補い、`observed` がなければ補う。一つの範囲の Atom に古い版が混ざっていれば、その範囲は古い。`observed` は `subject` のソースに置く。読んだが Atom がなかった範囲は、`observed` だけを書く。
消えたソースは、`archsig record --drop <ソース>` で ArchMap から外す。
`record` は、書いたソースと範囲ごとの Atom の数を `recorded`(`source`、`scope`、`atoms`)に、外したソースをそろえたパスで `dropped` に返す。局所ごとの意味 Atom では、`source` はその Atom の `subject`(`local:<読み>:<局所>`)である。
`uses` のパスと、外部を指さない `resolves` の `object` も、`at` と同じくリポジトリの根からの相対パスにそろえる。根の外を指すパスは書かない。

ArchMap に書くのは Atom だけである。局所の分け方や局所どうしの重なりは、ArchSig が Atom と Law の読みから導く。

## 変更の候補

変更の候補というのは、これから書くコードを、先に Atom で書いたもののこと。
ArchMap と同じ形をとり、`.archsig/plans/<候補の名前>/` に置く。コマンドや欄では `plan` と書く。
そのディレクトリの直下の `.jsonl` を、ファイル名の順に読んで一つの候補とする。

最初の行で、候補の名前と、元にするものを書く。元にするのは、コミットか、別の候補(`plan:<名前>`)である。
`plan check` と `plan split` は、元が別の候補なら、その候補を先に重ね、その上にこの候補を重ねる。元をたどってめぐれば、誤りとする。

```json
{"kind": "plan", "subject": "split-order", "base": "a1b2c3d"}
```

続けて、変更後のコードの構造 Atom を書く。`at` には `plan:<候補の名前>` と書く。
候補の中の Atom は行を持たないので、一つの操作の中の書き込みと呼び出しの順は、ファイルに書いた Atom の順とする。呼び出しの `#2`、`#3` もこの順で付ける。

- 候補の中で `subject` に構造 Atom を書いた要素は、その要素についての元の構造 Atom がすべて置き換わる。要素から出る呼び出し(`<要素>->…`)の Atom も置き換わる。
  ただし `resolves` は、名前の解決を加えるだけで、置き換えは起こさない。
  元の `defines` も置き換わるので、操作の本体だけを書き直すときも、その `defines` を候補に書く。書かなければ、変更後のその操作は定義のない要素になり、`plan check` の関わる結論は沈黙する。
- 候補に書いた意味 Atom は、変更後に加えない。
- それ以外の要素は、元のコードのまま扱う。
- 新しく定義する要素の `defines` は、`file` に、変更後にその要素を置くソースのパスを書く。局所はこのパスで決まる。

候補には、変更のための Atom が二つ加わる。

- `corresponds`:変更前の要素と変更後の要素の対応。一つの要素を二つに分けるなら、対応を二つ書く。
  変更前と変更後に同じ名前であり、`removes` していない要素は、書かなくても自分自身に対応する。
  操作の引数も、同じ名前どうしが対応する。名前が変わる引数は `corresponds` で書く。
- `removes`:変更後になくなる要素。

```json
{"kind": "corresponds", "subject": "shop.order.model.Order.payment_ref",
 "object": "shop.payment.model.OrderPayment.ref", "at": "plan:split-order"}
{"kind": "removes", "subject": "shop.order.model.Order", "at": "plan:split-order"}
```

行き先をまだ決めていない対応は、`object` に行き先を `|` で並べて書ける(`"a.X | b.Y"`)。
`|` を含めば、空の欄を捨てて行き先が一つしか残らなくても、決めていない対応として扱う。`object` のない対応と、行き先が一つも残らない対応は、対応を作らない。
`|` を含む候補は、`archsig plan choices` で決め方を数え上げる(第5章の問い6)。`plan check` は、決めていない対応があれば、`changes` の Law を `unresolved` で沈黙させる。

候補が書き直していない操作が、`removes` した要素を使っていれば、`plan check` はその操作を `missing` として挙げる。書き直す範囲はここで分かる。

実装を先にして、候補には対応だけを書いてもよい(第5章の問い3)。

変更後の要素の意味は、`corresponds` で変更前の要素の意味を移したものとして扱う。候補が定義した要素の意味は、対応の元の要素の意味を読んでいなければ決まらない。実装した後の意味は、観測し直した意味 Atom で確かめる。
