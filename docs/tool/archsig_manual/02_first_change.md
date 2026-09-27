# 2. 変更を一周する

この章では、一つの変更を最初から最後まで追う。
人がエージェントに頼み、エージェントが SKILL に従って ArchSig を呼び、実装して、計画どおりかを確かめるまでである。
ここに出てくるファイルの形とコマンドは、後の章で詳しく扱う。

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

reading module = dir(depth: 2)

meaning payment-info on field
  "注文の支払いを特定する値。決済サービスの呼び出しに渡る値として使われているもの。"

law payment-follows-order
  "注文の型を変えても、決済情報は今の操作と同じように扱われる。"
  about payment-info
  changes commute with operations
```

三つの部分からなる。

- `reading` は読みだ。コードをどの単位で局所に分けて見るかを決める。
  ここでは `shop/order`、`shop/shipping`、`shop/payment` がそれぞれ一つの局所になる。
- `meaning` は、観測してほしい意味の語彙だ。
  エージェントはこの説明を手がかりに、どのフィールドが決済情報かを、使われ方から読む。
- `law` が規則だ。`changes commute with operations` は、変更と操作が可換であることを求める。
  変更前の操作をしてから新しい型へ移した結果と、先に移してから変更後の操作をした結果で、決済情報が一致しなければならない。

適切な Law が無ければ、SKILL は Law を書く段に入る。Law を書くのは強いモデルの仕事で、人がその内容を承認する。

## 3. 観測をそろえる

次に SKILL は、ArchMap が今のコードに追いついているかを確かめる。

```text
archsig status
```

ArchSig は、ArchMap を観測した版と今の版を比べ、変わったソースを返す。
変わったソースだけを観測し直せばよい。観測は二段に分かれる。

- 構造 Atom は、言語ごとの解析器が取り出す。
- 意味 Atom は、軽いモデルのエージェントが Law の語彙を手がかりに観測する。

ArchMap に記録される Atom は、たとえば次の形をしている。

```json
{"kind": "writes", "subject": "shipping.update_shipping", "object": "Order.payment_ref",
 "value": "None", "when": "$new.country != $order.shipping_address.country",
 "at": "shop/shipping/service.py:4@a1b2c3d", "by": "extractor:python@0.6.0"}
{"kind": "meaning", "subject": "Order.payment_ref", "meaning": "payment-info",
 "uses": ["shop/payment/charge.py:22", "shop/order/confirm.py:57"],
 "at": "shop/order/model.py:18@a1b2c3d", "by": "model:claude-sonnet-5"}
```

一行目は構造 Atom で、条件付きの書き込みを記録している。
二行目は意味 Atom だ。`uses` に、決済情報だと読んだ根拠の使用箇所が並ぶ。
どちらにも「正しい」「おかしい」という判定は書かない。

## 4. 候補を書いて検査する

エージェントは、変更の候補を書く。候補は ArchMap と同じ形をとる。
まだ無いコードの Atom と、変更前後の対応を書き、場所には候補の名前を入れる。

```json
{"kind": "corresponds", "subject": "Order.payment_ref", "object": "OrderPayment.ref",
 "at": "plan:split-order"}
{"kind": "corresponds", "subject": "Order.shipping_address", "object": "OrderShipping.address",
 "at": "plan:split-order"}
{"kind": "writes", "subject": "shipping.update_shipping", "object": "OrderShipping.address",
 "value": "normalize_address($new)", "at": "plan:split-order"}
```

候補を検査する。

```text
archsig plan check split-order
```

最初の結果は沈黙だった。

```text
… 沈黙  payment-follows-order  update_shipping
  理由  normalize_address の書き込みを観測していない
  次に読む  shop/shipping/address.py  normalize_address
```

`update_shipping` は `normalize_address` を呼ぶ。
それが決済情報を書き換えるかどうかが分からないので、ArchSig は結論を出さず、どこを読めば決まるかを返した。
SKILL はそこだけを観測し、ArchMap に書き足す。
ArchMap は読んだ範囲も記録する。読んだ範囲に書き込みの Atom が無ければ、書き込みは無いと分かる。読んでいない所は、分からないままだ。

もう一度検査すると、反例が返った。

```text
✘ 反例  payment-follows-order  update_shipping
  入力              注文 order: payment_ref = p
                    新しい配送先 new: $new.country != $order.shipping_address.country
  更新してから移す  OrderPayment.ref = None
  移してから更新    OrderPayment.ref = p
  食い違いの元      shop/shipping/service.py:4  order.payment_ref = None
                    候補に、これに対応する書き込みが無い
```

今の `update_shipping` は、国が変わると決済情報を消す。候補の新しい `update_shipping` は配送先しか書かない。
だから、国をまたぐ配送先の変更では、移行と更新の順番で決済情報が変わる。
反例は、入力が満たす条件と、二つの順番の結果を具体的に持つ。どの書き込みを通ったかも分かるので、誰でもたどって確かめられる。

## 5. 人が判断する

ここで、エージェントは人に聞く。

> 国をまたいで配送先を変えたとき、与信をやり直す動きは、新しい型でも続けますか。

これは仕様の判断だ。人は「続ける」と答える。
エージェントは候補を直す。新しい `update_shipping` は、国が変わるときに決済側の `reset_authorization` を呼ぶ。
その書き込みを候補に足して、もう一度検査する。

```text
✔ 成り立つ  payment-follows-order  update_shipping
  条件の分岐 2 通り(国が変わる / 変わらない)で、二つの順番の結果が一致
```

ArchSig は、書き込みの条件で分かれるすべての分岐について、二つの順番の結果を比べる。
どの分岐でも一致したので、この候補は Law を保つ。

## 6. 仕事を分ける

変更は、配送と決済の二つの局所にまたがる。SKILL は仕事を分ける。

```text
archsig plan split split-order
```

ArchSig は、読みの局所ごとに、担当が満たす条件と、局所の間でそろえる対応を返す。

```text
shop/shipping   update_shipping は国が変わるとき payment.reset_authorization(order_id) を呼ぶ
                update_shipping は OrderShipping.address だけを書き換える
shop/payment    reset_authorization(order_id) は OrderPayment.ref を None にする
共有            OrderShipping と OrderPayment は order_id で Order に対応する
```

エージェントは、この条件をそれぞれの担当(別のエージェントでもよい)に渡す。
各担当は、自分の局所の条件と、共有する対応だけを見て実装できる。

## 7. 実装して比べる

実装が終わったら、SKILL は変わったソースを観測し直し、候補と比べる。

```text
archsig compare --plan split-order
```

```text
✔ 候補の Atom 9 件すべてに、対応する観測がある
✔ payment-follows-order は実装後のコードで成り立つ
```

候補と違う実装があれば、ここで分かる。
たとえば決済側が `OrderPayment.ref` を `None` ではなく空文字にしていたら、ArchSig はその書き込みの場所と、候補の値との違いを返す。
ビルドとテストは、これとは別に SKILL が実行する。

## 8. 次の変更へ

計算結果は `.archsig/runs/` に残る。どの結果も、根拠にした Atom、Law、ソースの版を持つ。
次の変更では、根拠が変わっていない結果をそのまま使い、変わった所だけを計算し直す。
次の仕事は、この変更で更新された構造から始まる。

## エージェントが読む出力

ここまでの出力は、人に見せるための文字の表示で書いた。
エージェントが読むのは JSON のサマリで、必要なときに詳細を取り出す。

```json
{
  "run": "r-0193",
  "commit": "a1b2c3d",
  "plan": "split-order",
  "results": [
    {"id": "r-0193/1", "law": "payment-follows-order", "subject": "shipping.update_shipping",
     "outcome": "counterexample", "at": ["shop/shipping/service.py:4"]}
  ],
  "silent": [],
  "next": []
}
```

`archsig show r-0193/1` で、その結論の詳細を取り出す。
詳細には、根拠の Atom と Law、反例の入力と二つの結果、成り立つ条件が入る。
