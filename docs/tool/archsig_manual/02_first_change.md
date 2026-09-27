# 2. 一つの変更を最初から最後まで

人がエージェントに頼み、エージェントが SKILL に従って ArchSig を呼び、実装して、計画どおりかを確かめるまでを追う。

## 題材

小さな通販サービス `shop` を例にとる。コードは次のディレクトリに分かれている。

```text
shop/order/      注文
shop/shipping/   配送
shop/payment/    決済
```

注文は一つの型 `Order` にまとまっていて、配送先と決済情報を両方持つ。
配送先を変える操作は次のとおりだ。

```python
# shop/shipping/service.py
def update_shipping(order: Order, new: Address) -> None:
    if new.country != order.shipping_address.country:
        order.payment_ref = None          # 国をまたぐと与信をやり直す
    order.shipping_address = normalize_address(new)
```

リポジトリには、ArchSig のファイルを置く `.archsig/` がある。

```text
.archsig/
  law/     Law(DSL)
  map/     観測した Atom(ArchMap)
  plans/   変更の候補
  runs/    計算結果
```

## 1. 人が頼む

人はエージェントにこう頼む。

> `Order` を配送の `OrderShipping` と決済の `OrderPayment` に分けたい。決済情報の扱いは今と変えたくない。

人が伝えるのは、したいことと、変えたくないことだ。
エージェントは ArchSig の SKILL に従って作業を進める。

## 2. Law を確かめる

SKILL は、まず「変えたくないこと」に当たる Law があるかを見る。
このリポジトリには、次の Law がすでにある。

```text
# .archsig/law/shop.law

sources "shop/**"
  except "**/tests/**"

reading module = dir(depth: 2)

meaning payment-info on field
  "注文の支払いを特定する値。決済サービスの呼び出しに渡る値として使われているもの。"

law payment-follows-order
  "注文の型を変えても、決済情報は今の操作と同じように扱われる。"
  about payment-info
  changes commute with operations
```

- `sources` は、観測するソースの範囲だ。テストコードはここで外す。
- `reading` は読みだ。コードをどの単位で局所に分けて見るかを決める。
  ここでは `shop/order`、`shop/shipping`、`shop/payment` がそれぞれ一つの局所になる。
- `meaning` は、観測してほしい意味の語彙だ。
  エージェントはこの説明を手がかりに、どのフィールドが決済情報かを、使われ方から読む。
- `law` が規則だ。`changes commute with operations` は、変更と操作が可換であることを求める。
  変更前の操作をしてから新しい型へ移した結果と、先に移してから変更後の操作をした結果で、決済情報が一致しなければならない。

適切な Law がなければ、SKILL は Law を書く段に入る。Law を書くのは強いモデルの仕事で、人がその内容を承認する。

## 3. 観測をそろえる

次に SKILL は、ArchMap が今のコードに追いついているかを確かめる。

```text
archsig status
```

ArchSig は、ArchMap を観測したときのソースと今のソースを比べ、変わったソースを返す。
変わったソースだけを観測し直せばよい。観測は二段に分かれる。

- 構造 Atom は、`archsig extract` で言語ごとの解析器が取り出す。
- 意味 Atom は、軽いモデルのエージェント二つが、Law の語彙を手がかりに別々に観測する。一致したものを記録する。

ArchMap に記録される Atom は、たとえば次の形をしている。

```json
{"kind": "writes", "subject": "shop.shipping.service.update_shipping",
 "object": "shop.order.model.Order.payment_ref", "value": "None",
 "when": "$new.country != $order.shipping_address.country",
 "at": "shop/shipping/service.py:4@a1b2c3d", "by": "extractor:python@0.6.0"}
{"kind": "meaning", "subject": "shop.order.model.Order.payment_ref", "meaning": "payment-info",
 "uses": ["shop/payment/charge.py:22@a1b2c3d", "shop/order/confirm.py:57@a1b2c3d"],
 "at": "shop/order/model.py:18@a1b2c3d", "by": ["model:claude-sonnet-5#1", "model:claude-sonnet-5#2"]}
```

一行目は構造 Atom で、条件付きの書き込みを記録している。
二行目は意味 Atom だ。`uses` に、決済情報だと読んだ根拠の使用箇所が並ぶ。`by` の二つは、別々に観測した二つのエージェントである。
どちらにも「正しい」「おかしい」という判定は書かない。

## 4. 候補を書いて検査する

エージェントは、変更の候補を書く。変更の候補というのは、これから書くコードを、先に Atom で書いたもののこと。
まだないコードの構造 Atom と、変更前後の対応を書く。

```json
{"kind": "plan", "subject": "split-order", "base": "a1b2c3d"}
{"kind": "defines", "subject": "shop.shipping.model.OrderShipping", "value": "type",
 "file": "shop/shipping/model.py", "at": "plan:split-order"}
{"kind": "defines", "subject": "shop.payment.model.OrderPayment", "value": "type",
 "file": "shop/payment/model.py", "at": "plan:split-order"}
{"kind": "defines", "subject": "shop.shipping.model.OrderShipping.address", "value": "field",
 "type": "shop.shipping.model.Address", "file": "shop/shipping/model.py", "at": "plan:split-order"}
{"kind": "defines", "subject": "shop.shipping.model.OrderShipping.order_id", "value": "field",
 "type": "str", "file": "shop/shipping/model.py", "at": "plan:split-order"}
{"kind": "defines", "subject": "shop.payment.model.OrderPayment.ref", "value": "field",
 "type": "str", "file": "shop/payment/model.py", "at": "plan:split-order"}
{"kind": "corresponds", "subject": "shop.order.model.Order.shipping_address",
 "object": "shop.shipping.model.OrderShipping.address", "at": "plan:split-order"}
{"kind": "corresponds", "subject": "shop.order.model.Order.payment_ref",
 "object": "shop.payment.model.OrderPayment.ref", "at": "plan:split-order"}
{"kind": "corresponds", "subject": "shop.shipping.service.update_shipping.$order",
 "object": "shop.shipping.service.update_shipping.$shipping", "at": "plan:split-order"}
{"kind": "removes", "subject": "shop.order.model.Order", "at": "plan:split-order"}
{"kind": "defines", "subject": "shop.shipping.service.update_shipping", "value": "operation",
 "params": {"shipping": "shop.shipping.model.OrderShipping", "new": "shop.shipping.model.Address"},
 "file": "shop/shipping/service.py", "at": "plan:split-order"}
{"kind": "calls", "subject": "shop.shipping.service.update_shipping",
 "object": "shop.shipping.address.normalize_address", "at": "plan:split-order"}
{"kind": "passes", "subject": "shop.shipping.service.update_shipping->shop.shipping.address.normalize_address",
 "object": "shop.shipping.address.normalize_address.$addr", "value": "$new", "at": "plan:split-order"}
{"kind": "writes", "subject": "shop.shipping.service.update_shipping",
 "object": "shop.shipping.model.OrderShipping.address",
 "value": "shop.shipping.address.normalize_address($new)", "at": "plan:split-order"}
```

新しい型とフィールドは、置く予定のソースを `file` に書く。局所はこのパスで決まる。
`update_shipping` は名前が変わらないので、変更前の `update_shipping` に対応する。引数 `order` は `shipping` に変わるので、対応を書いた。
`update_shipping` の Atom を書いたので、その要素についての元の Atom は置き換わる。`normalize_address` の呼び出しも、候補に書き直してある。
候補には意味 Atom を書かない。`OrderPayment.ref` が決済情報であることは、`Order.payment_ref` からの対応で移る。

候補を検査する。

```text
archsig plan check split-order
```

最初の結果は沈黙だった。

```text
… 沈黙  payment-follows-order  update_shipping
  理由      unread
  次に読む  shop/shipping/address.py  構造
```

`update_shipping` は `normalize_address` を呼ぶ。ArchSig は、呼び出し先の書き込みも展開して比べる。
`normalize_address` のあるソースを読んでいないので、決済情報を書き換えるかどうかが分からない。ArchSig は結論を出さず、どこを読めば決まるかを返した。
SKILL はそこだけを観測し、ArchMap に書き足す。
読んだ範囲に書き込みの Atom がなければ、書き込みはないと分かる。読んでいない所は、分からないままだ。

もう一度検査すると、反例が返った。

```text
✘ 反例  payment-follows-order  update_shipping
  入力              注文: payment_ref = p
                    新しい配送先 new: $new.country != $shipping.address.country
  更新してから移す  OrderPayment.ref = None
  移してから更新    OrderPayment.ref = p
  食い違いの元      shop/shipping/service.py:4  order.payment_ref = None
                    候補に、これに対応する書き込みがない
```

今の `update_shipping` は、国が変わると決済情報を消す。候補の新しい `update_shipping` は配送先しか書かない。
だから、国をまたぐ配送先の変更では、移行と更新の順番で決済情報が変わる。
変更前の条件 `$order.shipping_address.country` は、対応に従って `$shipping.address.country` に読み替えてある。
反例は、入力が満たす条件、二つの順番の結果、食い違いの元になった書き込みを持つ。誰でもたどって確かめられる。

## 5. 人が判断する

ここで、エージェントは人に聞く。

> 国をまたいで配送先を変えたとき、与信をやり直す動きは、新しい型でも続けますか。

これは仕様の判断だ。人は「続ける」と答える。
エージェントは候補を直す。新しい `update_shipping` は、国が変わるときに決済側の `reset_authorization` を呼ぶ。
`reset_authorization` は `OrderPayment.ref` を `None` にする。その Atom を候補に足して、もう一度検査する。

```text
✔ 成り立つ  payment-follows-order  update_shipping
  条件の分岐 2 通り(国が変わる / 変わらない)で、二つの順番の結果が一致
```

ArchSig は、条件で分かれるすべての分岐について、二つの順番の結果を比べる。
どの分岐でも一致したので、この候補は Law を保つ。

## 6. 仕事を分ける

変更は、配送と決済の二つの局所にまたがる。SKILL は仕事を分ける。

```text
archsig plan split split-order
```

ArchSig は、局所ごとの候補を `.archsig/plans/split-order/<局所>/` に書き出し、担当が満たす条件と、局所の間でそろえる条件を返す。
人に見せる形で表示すると次のようになる。

```text
shop/shipping   候補 split-order/shop/shipping
                update_shipping は OrderShipping.address だけを書き換える
                国が変わるとき payment.service.reset_authorization を呼ぶ
shop/payment    候補 split-order/shop/payment
                reset_authorization は OrderPayment.ref を None にする
共有            update_shipping から reset_authorization への呼び出しと、渡す $shipping.order_id
                Order.shipping_address → OrderShipping.address(shop/order と shop/shipping)
                Order.payment_ref → OrderPayment.ref(shop/order と shop/payment)
```

エージェントは、局所の候補の名前をそれぞれの担当(別のエージェントでもよい)に渡す。
各担当は、自分の局所の候補と、共有の条件だけを見て実装できる。

## 7. 実装して比べる

実装が終わった局所から、SKILL は変わったソースを観測し直し、その局所の候補と比べる。

```text
archsig compare --plan split-order --only shop/payment
```

全部の局所がそろったら、全体を比べる。

```text
archsig compare --plan split-order
```

```text
✔ 候補の Atom 14 件すべてに、対応する観測がある
✔ payment-follows-order は実装後のコードで成り立つ
```

候補と違う実装があれば、ここで分かる。
たとえば決済側が `OrderPayment.ref` を `None` ではなく空文字にしていたら、ArchSig はその書き込みの場所と、候補の値との違いを返す。
新しい `OrderPayment.ref` が決済情報として使われているかも、観測し直した意味 Atom で確かめる。
ビルドとテストは、これとは別に SKILL が実行する。

## 8. 次の変更へ

計算結果は `.archsig/runs/` に残る。どの結果も、根拠にした Atom、Law、ソースの内容の hash を持つ。
次の変更では、根拠が変わっていない結果を確かめ直して使い、変わった所だけを計算し直す。
次の仕事は、この変更で更新された構造から始まる。

## エージェントが読む出力

ここまでの出力は、人に見せるための文字の表示(`--format text`)で書いた。
エージェントが読むのは JSON のサマリで、必要なときに詳細を取り出す。

```json
{
  "run": "r-0193",
  "command": "plan check split-order",
  "commit": "a1b2c3d",
  "law": "sha256:41ac…",
  "results": [
    {"id": "r-0193/1", "question": "change", "law": "payment-follows-order",
     "subject": "shop.shipping.service.update_shipping", "outcome": "fails", "kind": "counterexample",
     "at": ["shop/shipping/service.py:4"]}
  ],
  "counts": {"holds": 0, "fails": 1, "silent": 0},
  "next": []
}
```

`archsig show r-0193/1` で、その結論の詳細を取り出す。
詳細には、根拠の Atom と Law、反例の入力と二つの結果、成り立つ条件が入る。
結果の読み方は[第6章](06_results.md)で扱う。
