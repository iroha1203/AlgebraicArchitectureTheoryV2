# 3. Atom と ArchMap

ArchMap は、コードから観測した Atom の記録だ。

## Atom の形

Atom は JSON の一行で書く。どの Atom も次の欄を持つ。

- `kind`:Atom の種類。
- `subject`:何についての事実か。コードの要素の名前を書く。
- `at`:観測した場所。`パス:行@コミット` の形で書く。行は `10-14` のような範囲でもよい。
- `by`:誰が観測したか。解析器の名前と版、またはモデルの名前を書く。

種類ごとに、次の欄が加わる。ここに挙げていない欄を持つ Atom は受け付けない。

| 種類 | 加わる欄 |
| --- | --- |
| `defines` | `value`(要素の種類)、`params`(操作の引数と型)、`type`(フィールドの型)、`file`(候補の中だけ) |
| `calls`、`reads`、`imports` | `object`、`when` |
| `writes`、`passes`、`sends`、`receives` | `object`、`value`、`when` |
| `returns` | `value`、`when` |
| `meaning` | `meaning`、`value`、`uses` |
| `observed` | `scope`、`hash` |
| `plan` | `base` |
| `corresponds` | `object` |
| `removes` | なし |

Atom の同一性は、`kind`、`subject`、`object`、`value`、`when`、`meaning`、`scope` で決まる。
`at` と `by` は同一性に入らない。行がずれても、同じ事実は同じ Atom である。

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
- 呼び出しの一つ一つも要素になる。名前は `<呼び出し元>-><呼び出し先>` で、同じ組が一つの操作に二度あれば、行の順に `#2`、`#3` を付ける。

言語が違っても、同じチャネルは同じ名前になる。Python の `requests.post("/orders")` も、Java の `@PostMapping("/orders")` も、`channel:http:POST /orders` と書く。

解析器が名前を解決できなかった所は、書かれたとおりの字句の前に `?` を付ける(`?mail.send`)。
`?` で始まる名前が関わる計算で、ArchSig は結論を出さず、沈黙する。
フレームワークの配線(ルーティング、依存注入、デコレータ)のように解析器が解決できない所は、エージェントがコードを読んで解決してよい。解決した Atom は、意味 Atom と同じく、二つの観測者と、根拠の `uses` を持つ。

## 構造 Atom

構造 Atom は、構文から決まる事実だ。言語ごとの解析器が取り出す。種類は次の九つで、言語によらず同じである。

- `defines`:要素を定義する。`value` は `operation`、`type`、`field` のどれか。
  操作は `params` に引数の名前と型を持つ(`{"order": "shop.order.model.Order", "new": "shop.shipping.model.Address"}`)。フィールドは `type` に型を持つ。
- `calls`:操作が別の操作を呼ぶ。
- `reads`:操作がフィールドを読む。
- `writes`:操作がフィールドに書く。`value` に書く値を持つ。
- `passes`:呼び出しが引数に値を渡す。`subject` は呼び出しの名前、`object` は受け取る引数である。
- `sends`:操作がチャネルの項目へ値を送る。`object` は項目、`value` は送る値である。
- `receives`:操作がチャネルの項目を受け取る。`object` は項目、`value` は受け取った値を操作の中で表す式である。
- `returns`:操作が値を返す。`value` は返す値である。
- `imports`:モジュールが別のモジュールを取り込む。

`calls`、`reads`、`writes`、`passes`、`sends`、`returns` は `when` を持てる。`if` の中の書き込みなら、その条件を `when` に書く。

### 値と条件の書き方

`value` と `when` は、解析器が次の小さな形に直して書く。

- 定数:`None`、`0`、`"JPY"`。
- 引数と、そこからたどるフィールド:`$new`、`$order.shipping_address.country`。
- 操作の呼び出し:`shop.shipping.address.normalize_address($new)`。
- 四則演算、比較、否定:`$order.total * 100`、`$new.country != $order.shipping_address.country`、`not $order.paid`。
- それ以外:`?`。

局所変数は、解析器が代入した式で置き換えて書く。置き換えられなければ `?` と書く。
`$order.total` は、引数 `order` の型と、フィールドの型をたどって、フィールド `shop.order.model.Order.total` として読む。

ArchSig は、操作の呼び出しの結果を、同じ操作に同じ値を渡せば同じ結果が返るものとして扱う。
ただし、Law で `fresh` と宣言した操作は、呼ぶたびに新しい値を返すものとして扱う(第4章)。
`?` が関わる計算では沈黙する。

## 意味 Atom

意味 Atom は、要素が何の役割を持つかという事実だ。種類は `meaning` の一つだけである。

```json
{"kind": "meaning", "subject": "shop.order.model.Order.payment_ref", "meaning": "payment-info",
 "uses": ["shop/payment/charge.py:22@a1b2c3d", "shop/order/confirm.py:57@a1b2c3d"],
 "at": "shop/order/model.py:18@a1b2c3d", "by": ["model:claude-sonnet-5#1", "model:claude-sonnet-5#2"]}
{"kind": "meaning", "subject": "shop.order.confirm.confirm->mail.send", "meaning": "role",
 "value": "order-notice", "uses": ["shop/order/confirm.py:61-64@a1b2c3d"],
 "at": "shop/order/confirm.py:61@a1b2c3d", "by": ["model:claude-sonnet-5#1", "model:claude-sonnet-5#2"]}
```

`meaning` には、Law が定めた意味の語彙の名前を書く。語彙が `values` で値を並べていれば、その一つを `value` に書く。

意味は使われ方で決まる。`uses` には、その意味だと読んだ根拠の使用箇所を書く。
呼び出し元、前後の処理、値の渡し先、分岐である。一つ以上が必要で、書き方は `at` と同じだ。
名前、型、コメント、文書は根拠にしない。

意味 Atom は、別々の二回の観測が一致したものだけを記録する。
`by` には二つの観測者を並べる。一致は Atom の同一性で決め、`uses` は二つを合わせて記録する。
一致しなかったものを強いモデルが元のコードを読んで決めたときは、`by` の三つ目に `decided:model:<名前>` を加える。

### 局所ごとの意味 Atom

意味は、要素一つずつではなく、局所ごとにまとめて観測することもできる。局所というのは、読みでコードを分けた一まとまりのこと(第4章)。

```json
{"kind": "meaning", "subject": "local:service:shop/payment", "meaning": "unit", "value": "minor",
 "uses": ["shop/payment/charge.py:22@a1b2c3d"], "at": "shop/payment@a1b2c3d",
 "by": ["model:claude-sonnet-5#1", "model:claude-sonnet-5#2"]}
```

`subject` は `local:<読み>:<局所の名前>` と書く。
この Atom は、その局所の中で、意味の語彙が対象にする要素すべてに同じ値を与える。
まとめて読むと観測の手間が減る。まとめてよいかは、第5章の問い5で確かめる。

## 読んだ範囲

ArchMap は、Atom のほかに、どこを読んだかを記録する。

```json
{"kind": "observed", "subject": "shop/shipping/address.py", "scope": "structure",
 "hash": "sha256:9f2c…", "at": "shop/shipping/address.py@a1b2c3d", "by": "extractor:python@0.6.0"}
{"kind": "observed", "subject": "shop/shipping/address.py", "scope": "meaning:payment-info",
 "hash": "sha256:9f2c…", "at": "shop/shipping/address.py@a1b2c3d",
 "by": ["model:claude-sonnet-5#1", "model:claude-sonnet-5#2"]}
```

`scope` は、構造を読んだのか、どの意味を読んだのかを示す。`hash` は、読んだときのソースの内容の hash だ。
意味を読んだ範囲も、二つの観測者がどちらも読んだ範囲だけを記録する。

読んだ範囲に Atom がなければ、その事実はない。読んでいない所の事実は、分からない。
ArchSig はこの二つを区別する。分からない所が結論に関わるとき、ArchSig は沈黙し、そこを次に読む場所として返す。

ソースが今の内容と違えば、その範囲は古い。
意味 Atom は、`at` のソースと `uses` のソースがどれも今の内容と同じときだけ使う。
意味は使われ方で決まるので、使う側のソースが変われば読み直す。
`archsig status` は古い範囲と古い意味 Atom を返す。

## ArchMap のファイル

ArchMap は、ソースのファイルごとに一つの JSON Lines ファイルに分けて置く。

```text
.archsig/map/shop/shipping/service.py.jsonl
.archsig/map/shop/shipping/address.py.jsonl
.archsig/map/shop/order/model.py.jsonl
```

一つのファイルには、そのソースについての `observed` と、そこで観測した Atom が入る。
局所ごとの意味 Atom は、`.archsig/map/local/<読み>/<局所の名前>.jsonl` に置く。
ソースが変わったら、そのファイルだけを観測し直して置き換える。
ArchMap はリポジトリにコミットする。観測には手間がかかるので、次の担当やセッションが使い回せるようにするためだ。

ArchMap に書くのは Atom だけである。局所の分け方や局所どうしの重なりは、ArchSig が Atom と Law の読みから導く。

## 変更の候補

変更の候補というのは、これから書くコードを、先に Atom で書いたもののこと。
ArchMap と同じ形をとり、`.archsig/plans/<候補の名前>/` に置く。コマンドや欄では `plan` と書く。

最初の行で、候補の名前と、元にするものを書く。元にするのは、コミットか、別の候補(`plan:<名前>`)である。

```json
{"kind": "plan", "subject": "split-order", "base": "a1b2c3d"}
```

続けて、変更後のコードの構造 Atom を書く。`at` には `plan:<候補の名前>` と書く。

- 候補の中で `subject` に Atom を書いた要素は、その要素についての元の Atom がすべて置き換わる。要素から出る呼び出し(`<要素>->…`)の Atom も置き換わる。
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
`|` を含む候補を受け付けるのは `archsig plan choices` だけである(第5章の問い6)。

候補には意味 Atom を書かない。変更後の要素の意味は、`corresponds` で変更前の要素の意味を移したものとして扱う。
実装した後の意味は、観測し直した意味 Atom で確かめる。

## ArchSig が受け付けない ArchMap

次のものがあると、ArchSig は ArchMap や候補を入力として受け付けず、該当する行を返す。

- 知らない種類、その種類が持たない欄。
- Law の語彙にない `meaning`、語彙の `values` にない `value`。
- `uses` が空の意味 Atom。
- `by` に観測者が一人しかいない意味 Atom、意味の `observed`。
- `observed` のないソースの Atom。
- 指定したコミットでたどれない `at` と `uses`。
- `plans/` の外にある `plan`、`corresponds`、`removes`、`file`。
- 候補の中の意味 Atom。
- 候補の中で、同じ分岐の同じフィールドへ二度書く Atom。
