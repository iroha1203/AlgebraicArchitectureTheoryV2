# 3. Atom と ArchMap

ArchMap は、コードから観測した Atom の記録だ。
この章では、Atom の形、ArchMap のファイル、変更の候補の書き方を定める。

## Atom の形

Atom は JSON の一行で書く。どの Atom も次の欄を持つ。

- `kind`:Atom の種類。構造 Atom、意味 Atom、記録用の Atom に分かれる。
- `subject`:何についての事実か。コードの要素の名前を書く。
- `at`:観測した場所。`パス:行@コミット` の形で書く。行は `10-14` のような範囲でもよい。
- `by`:誰が観測したか。解析器の名前と版、またはモデルの名前を書く。

種類によって、次の欄が加わる。

- `object`:相手の要素。呼び出し先、書き込み先など。
- `value`:書き込む値、渡す値、意味の値。
- `when`:その事実が成り立つ条件。
- `uses`:意味 Atom の根拠にした使用箇所。

Atom の同一性は、`kind`、`subject`、`object`、`value`、`when` で決まる。
`at` と `by` は同一性に入らない。行がずれても、同じ事実は同じ Atom である。

## 要素の名前

`subject` と `object` には、コードの要素の名前を書く。要素は、操作、型、フィールド、チャネルの四つだ。

- 操作は、関数、メソッド、ハンドラのこと。`shipping.update_shipping` のように、モジュールから修飾した名前で書く。
- 型とフィールドは `Order`、`Order.payment_ref` のように書く。
- チャネルは、キューのトピック、HTTP のルート、イベント名のように、プロセスやサービスをまたいで操作をつなぐ名前のこと。`channel:order-placed` のように書く。

名前の付け方は解析器が決める。ArchSig は名前を文字列として扱い、一致するかどうかだけを見る。
解析器が名前を解決できなかった所は、書かれたとおりの字句の前に `?` を付ける(`?mail.send`)。
`?` で始まる名前が関わる計算で、ArchSig は結論を出さず、沈黙する。

呼び出しの一つ一つも要素になる。名前は `呼び出し元->呼び出し先` で、同じ組が二度あれば `#2` を付ける。
意味 Atom で呼び出しの役割を書くときに、この名前を使う。

## 構造 Atom

構造 Atom は、構文から決まる事実だ。言語ごとの解析器が取り出す。種類は次の八つで、言語によらず同じである。

- `defines`:要素を定義する。`value` は `operation`、`type`、`field` のどれか。
- `calls`:操作が別の操作を呼ぶ。
- `reads`:操作がフィールドを読む。
- `writes`:操作がフィールドに書く。`value` に書く値を持つ。
- `passes`:呼び出しが引数に値を渡す。`subject` は呼び出しの名前、`object` は受け取る引数。
- `sends`:操作がチャネルへ送る。
- `receives`:操作がチャネルから受け取る。
- `imports`:モジュールが別のモジュールを取り込む。

`calls`、`writes`、`passes`、`sends` は `when` を持てる。
`if` の中の書き込みなら、その条件を `when` に書く。

### 値と条件の書き方

`value` と `when` は、解析器が次の小さな形に直して書く。

- 定数:`None`、`0`、`"JPY"`。
- 引数:`$new`。フィールドをたどるときは `$order.shipping_address.country`。
- 操作の呼び出し:`normalize_address($new)`。
- 四則演算と比較:`$order.total * 100`、`$new.country != $order.shipping_address.country`。
- それ以外:`?`。

ArchSig は、呼び出しの結果を、同じ操作に同じ値を渡せば同じ結果が返るものとして扱う。中身は見ない。
条件は、成り立つ場合と成り立たない場合の二つの分岐として扱う。
`?` が関わる計算では沈黙する。

## 意味 Atom

意味 Atom は、要素が何の役割を持つかという事実だ。種類は `meaning` の一つだけである。

```json
{"kind": "meaning", "subject": "Order.payment_ref", "meaning": "payment-info",
 "uses": ["shop/payment/charge.py:22", "shop/order/confirm.py:57"],
 "at": "shop/order/model.py:18@a1b2c3d", "by": "model:claude-sonnet-5"}
{"kind": "meaning", "subject": "order.confirm->mail.send", "meaning": "role",
 "value": "order-notice", "uses": ["shop/order/confirm.py:61-64"],
 "at": "shop/order/confirm.py:61@a1b2c3d", "by": "model:claude-sonnet-5"}
```

`meaning` には、Law が定めた意味の語彙の名前を書く。語彙に値の候補があれば、その一つを `value` に書く。

意味は使われ方で決まる。`uses` には、その意味だと読んだ根拠の使用箇所を書く。
呼び出し元、前後の処理、値の渡し先、分岐である。一つ以上が必要だ。
名前、型、コメント、文書は根拠にしない。

意味 Atom は、別々の二回の観測が一致したものだけを記録する。
一致しなかったものは、強いモデルが元のコードを読んで決める。この手順は SKILL が持つ。

## 読んだ範囲

ArchMap は、Atom のほかに、どこを読んだかを記録する。

```json
{"kind": "observed", "subject": "shop/shipping/address.py", "scope": "structure",
 "hash": "sha256:9f2c…", "at": "shop/shipping/address.py@a1b2c3d", "by": "extractor:python@0.6.0"}
{"kind": "observed", "subject": "shop/shipping/address.py", "scope": "meaning:payment-info",
 "hash": "sha256:9f2c…", "at": "shop/shipping/address.py@a1b2c3d", "by": "model:claude-sonnet-5"}
```

`scope` は、構造を読んだのか、どの意味を読んだのかを示す。`hash` は、読んだときのソースの内容の hash だ。

読んだ範囲に Atom が無ければ、その事実は無い。読んでいない所の事実は、分からない。
ArchSig はこの二つを区別する。分からない所が結論に関わるとき、ArchSig は沈黙し、そこを次に読む場所として返す。

`hash` が今のソースと違えば、その範囲は古い。`archsig status` は古い範囲を返す。

## ArchMap のファイル

ArchMap は、ソースのファイルごとに一つの JSON Lines ファイルに分けて置く。

```text
.archsig/map/shop/shipping/service.py.jsonl
.archsig/map/shop/shipping/address.py.jsonl
.archsig/map/shop/order/model.py.jsonl
```

一つのファイルには、そのソースについての `observed` と、そこで観測した Atom が入る。
ソースが変わったら、そのファイルだけを観測し直して置き換える。
ArchMap はリポジトリにコミットする。観測には手間がかかるので、次の担当やセッションが使い回せるようにするためだ。

ArchMap に書くのは Atom だけである。局所の分け方や局所どうしの重なりは書かない。
それらは、ArchSig が Atom と Law の読みから導く。

## 変更の候補

変更の候補も、ArchMap と同じ形の Atom で書く。置き場所は `.archsig/plans/<候補の名前>/` だ。

最初の行で、候補の名前と、元にするコミットを書く。

```json
{"kind": "plan", "subject": "split-order", "base": "a1b2c3d"}
```

続けて、変更後のコードの Atom を書く。`at` には `plan:<候補の名前>` と書き、`uses` にも同じものを書ける。
候補の中で Atom を書いた要素は、その要素について、元のコードの Atom がすべて置き換わる。
それ以外の要素は、元のコードのまま扱う。

候補には、変更のための Atom が二つ加わる。

- `corresponds`:変更前の要素と変更後の要素の対応。一つの要素を二つに分けるなら、対応を二つ書く。
- `removes`:変更後に無くなる要素。

```json
{"kind": "corresponds", "subject": "Order.payment_ref", "object": "OrderPayment.ref", "at": "plan:split-order"}
{"kind": "removes", "subject": "Order", "at": "plan:split-order"}
```

## ArchSig が受け付けない ArchMap

次のものがあると、ArchSig は ArchMap を入力として受け付けず、該当する行を返す。

- 知らない種類、または欄。
- Law の語彙に無い `meaning`、語彙の候補に無い `value`。
- `uses` が空の意味 Atom。
- `observed` の無いソースの Atom。
- 指定したコミットで場所をたどれない `at`。
- `plans/` の外にある `plan`、`corresponds`、`removes`。
