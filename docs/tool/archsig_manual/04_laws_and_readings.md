# 4. Law と読み

Law は、守りたい規則だ。専用の言語(DSL)で書き、`.archsig/law/` に `.law` ファイルとして置く。
この章では、Law ファイルに書く四つのもの、読み・意味の語彙・Law・定義を扱う。

```text
# .archsig/law/shop.law

reading module = dir(depth: 2)
reading service = dir(depth: 1)

meaning payment-info on field
  "注文の支払いを特定する値。決済サービスの呼び出しに渡る値として使われているもの。"

meaning role on call to "mail.send"
  values identity-check | order-notice | incident
  "送るメールの役割。宛先、本文の組み立て、呼び出し元の処理の流れから読む。"

law payment-follows-order
  "注文の型を変えても、決済情報は今の操作と同じように扱われる。"
  about payment-info
  changes commute with operations

law identity-mail-from-auth
  "本人確認のメールは auth から送る。"
  no call to "mail.send" that has role identity-check outside "shop/auth"
```

`#` から行末まではコメントである。字下げで、どの宣言に属するかを示す。

## 読み

読みは、コードをどの単位で局所に分けて見るかを決める。

```text
reading module = dir(depth: 2)
```

分け方は三通りある。

- `dir(depth: n)`:ソースのディレクトリを、上から `n` 段で切って局所にする。
- `file`:ソースのファイル一つを局所にする。
- `groups`:パスのパターンで局所を名指しする。

```text
reading team = groups
  shipping: "shop/shipping/**", "shop/address/**"
  payment:  "shop/payment/**"
  rest:     "**"
```

`groups` は上から順に当てはめる。どの局所にも入らないソースが残る読みは、ArchSig が受け付けない。

局所の名前は、`dir` ならディレクトリのパス(`shop/shipping`)、`groups` なら書いた名前である。

### 局所と重なり

ArchSig は、読みと Atom から局所を作る。
Atom は、その Atom が名指しする要素を定義したソースの局所すべてに属する。
`shop/order` の操作が `shop/payment` の操作を呼ぶ `calls` は、二つの局所の両方に属する。
二つの局所が共有する Atom が、その局所の重なりである。

局所の集まり、重なり、そこから作る幾何は、どれも ArchSig が導く。ArchMap にも Law にも書かない。

### 細かい読みと粗い読み

ある読みの局所がどれも、別の読みの局所のどれか一つに収まるとき、前者は後者より細かい。
上の例では `module` が `service` より細かい。ArchSig はこの関係を読みの定義から導く。
読みを変えても診断が変わらないかという問いは、この関係の上で計算する。

## 意味の語彙

意味の語彙は、観測してほしい意味を宣言する。意味 Atom の `meaning` には、ここで宣言した名前しか書けない。

```text
meaning <名前> on <要素の種類> [to <名前のパターン>]
  [values <値> | <値> | …]
  "<観測の手がかり>"
```

- 要素の種類は `operation`、`type`、`field`、`call`、`channel` のどれか。
  `call to "mail.send"` のように、呼び出し先で呼び出しを絞れる。
- `values` があれば、意味 Atom はその中の一つを `value` に持つ。無ければ、その意味を持つかどうかだけを記録する。
- 観測の手がかりには、どこを見れば読めるかを書く。答えは書かない。
  「このフィールドは決済情報だ」ではなく、「決済サービスの呼び出しに渡る値として使われているもの」と書く。

観測するエージェントは、手がかりだけを持ってコードを読む。
Law が何を求めているかは渡さない。観測が Law の結論に引っ張られないようにするためだ。

## Law

```text
law <名前>
  "<説明>"
  [on <読み>]
  [about <意味>]
  <規則>
```

- 説明は、規則を人の言葉で書いたものだ。計算には使わない。
- `on` で、どの読みの上で計算するかを選ぶ。省くと、ファイルで最初に宣言した読みになる。
- `about` で、どの意味の値を見るかを選ぶ。変更の規則と一致の規則で使う。

規則は四つの形のどれかで書く。

### 禁止:`no`

```text
no call to "mail.send" that has role identity-check outside "shop/auth"
```

当てはまる要素が一つもないことを求める。当てはまった要素が、それぞれ違反になる。

### 必須:`each`

```text
each operation that writes payment-info
  calls "audit.record"
```

一行目に当てはまる要素がどれも、二行目を満たすことを求める。満たさない要素が違反になる。

### 一致:`agrees along`

```text
meaning unit on field
  values minor | major
  "金額の単位。計算、換算、表示でどう使われているかから読む。"

law amount-units-agree
  "金額は、単位をそろえてから渡す。"
  about unit
  agrees along flows
  convert major -> minor by * 100
```

値の流れに沿って、意味の値がそろうことを求める。値の流れというのは、`writes` と `passes` で、ある要素の値が別の要素へ渡ることだ。
`convert` は、どの演算がどの値からどの値への換算に当たるかを宣言する。

この規則からは、二種類の結論が出る。
一つは、流れの一本一本で値がそろっているかだ。
もう一つは、局所ごとにはそろっているのに、局所をまたいで一周すると換算が元に戻らない所があるかだ。
後者は貼り合わせの障害で、ArchSig はその一周の流れと、換算を足し合わせた値を返す。

### 変更の保存:`changes`

```text
changes commute with operations
changes keep
```

変更の候補と、実装後のコードの比較で計算する規則だ。

- `changes commute with operations`:変更と操作が可換であることを求める。
  変更前の操作をしてから移した結果と、先に移してから変更後の操作をした結果で、`about` の意味の値が一致しなければならない。
  変更後の操作は、`corresponds` で対応させた操作である。
- `changes keep`:`about` の意味を持つ要素がどれも、変更後に対応する要素を持ち、同じ意味を保つことを求める。

### 要素と条件の書き方

規則の中では、要素を次のように選ぶ。

- 要素の種類:`operation`、`type`、`field`、`call`、`channel`。
- 名前のパターン:`"shop.payment.*"`。`*` は任意の文字列に当たる。
- 呼び出し先で絞った呼び出し:`call to "mail.send"`。
- 意味:`payment-info` のように語彙の名前を書くと、その意味を持つ要素に当たる。

条件は `that` の後に書き、`and` でつなぐ。

- `writes <要素>`、`reads <要素>`、`calls <要素>`、`sends <要素>`、`receives <要素>`。
- `has <意味> <値>`:その意味の値を持つ。
- `inside "<局所>"`、`outside "<局所>"`:その局所の中か外か。
  要素を定義したソースの局所で決める。呼び出しは、呼び出し元の局所で決める。

## 定義と取り込み

同じ要素の選び方を何度も書くときは、`def` で名前を付ける。

```text
def payment-writer = operation that writes payment-info

law payment-writes-are-audited
  "決済情報を書き換える操作は、監査記録を残す。"
  each payment-writer
    calls "audit.record"
```

`def` の中で別の `def` は使えない。定義は一段だけである。

別の Law ファイルは `include "<パス>"` で取り込む。

## Law を変えるとき

Law はプロジェクトの資産で、人が内容を承認する。
ArchSig は、どの結果にも、計算に使った Law の hash を記録する。
Law が変わると、古い Law で出した結果は使い回されない。

エージェントが Law を書き換えれば、違反を消すことも、計算を空振りさせることもできる。
だから、Law の変更は、コードの変更とは別に人がレビューする。

```text
archsig law check
archsig law diff <比べるコミット>
```

`law check` は、Law ファイルが正しく書けているかを確かめる。
`law diff` は、定義を展開した後の Law で、何が変わったかを示す。
Law を足したり変えたりしたら、`archsig next` で、新しく観測が必要な所を確かめる。
