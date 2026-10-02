# 4. Law と読み

Law は、守りたい規則だ。専用の言語(DSL)で書き、`.archsig/law/` の直下に `.law` ファイルとして置く。
Law ファイルには、観測する範囲、読み、意味の語彙、Law、定義を書く。

```text
# .archsig/law/shop.law

sources "shop/**"
  except "**/tests/**", "**/test_*.py"

reading module = dir(depth: 2)
reading service = groups
  commerce: "shop/order/**", "shop/shipping/**"
  money:    "shop/payment/**"
  rest:     "**"

fresh "shop.common.ids.new_*"

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

## 観測する範囲

`sources` は、観測するソースをパスのパターンで決める。`except` で外す。`except` は、その上の `sources` にだけ効く。
ArchSig は、リポジトリの根から作業ツリーをたどってソースを集める。`.git` と `.archsig` はたどらず、シンボリックリンクもたどらない。`.gitignore` は見ないので、外したいものは `except` に書く。パスのパターンでは、`*` は `/` をまたがず、`**` はまたぐ。
テストコードはここで外す。観測するのは実装コードだけだからだ。

## 読み

読み(reading)というのは、コードをどの単位で局所に分けて見るかの決め方のこと。
局所というのは、読みで分けたコードの一まとまりのこと。Rising Sea の局所文脈に当たる。

```text
reading module = dir(depth: 2)
```

分け方は三通りある。

- `dir(depth: n)`:ソースのディレクトリを、上から `n` 段で切って局所にする。
  `n` 段に満たない所にあるファイルは、そのファイルのディレクトリを局所にする。
- `file`:ソースのファイル一つを局所にする。
- `groups`:パスのパターンで局所を名指しする。

```text
reading team = groups
  shipping: "shop/shipping/**", "shop/address/**"
  payment:  "shop/payment/**"
  rest:     "**"
```

`groups` は上から順に当てはめる。

局所の名前は、`dir` と `file` ならパス(`shop/shipping`)、`groups` なら書いた名前である。

Law が読みを選ばないときは、最初に宣言した読みを使う。

### 局所と重なり

ArchSig は、読みと Atom から局所を作る。

- 要素は、それを定義したソースの局所に属する。候補の中で新しく定義する要素は、`defines` の `file` の局所に属する。
- チャネルとその項目は、そこへ送る操作と、そこから受け取る操作の局所すべてに属する。
- 定義を観測していない要素(外部のライブラリなど)は、どの局所にも属さない。
- Atom は、名指す要素が属する局所すべてに属する。

`shop/order` の操作が `shop/payment` の操作を呼ぶ `calls` は、二つの局所の両方に属する。
二つの局所が共有する Atom が、その局所の重なりである。
局所と重なりがつくる形を、ここでは幾何と呼ぶ。貼り合わせの障害は、この形の上で計算する。

局所、重なり、幾何は、どれも ArchSig が導く。ArchMap にも Law にも書かない。

### 細かい読みと粗い読み

ある読みの局所がどれも、別の読みの局所のどれか一つに収まるとき、前者は後者より細かい。
上の例では、`module` の局所 `shop/order` と `shop/shipping` は `service` の局所 `commerce` に、`shop/payment` は `money` に収まるので、`module` が `service` より細かい。ArchSig はこの関係を読みの定義から導く。
読みを変えても診断が変わらないかという問いは、この関係の上で計算する。

## 呼ぶたびに新しい値を返す操作

```text
fresh "shop.common.ids.new_*"
```

`fresh` は、呼ぶたびに新しい値を返す操作を名前のパターンで宣言する。ID を作る操作がこれに当たる。
ArchSig は、宣言した操作の呼び出しを、呼び出しの場所ごとに別の値として扱う。
宣言していない操作は、同じ値を渡せば同じ結果が返るものとして扱う。

## 意味の語彙

意味の語彙は、観測してほしい意味を宣言する。意味 Atom の `meaning` には、ここで宣言した名前を書く。

```text
meaning <名前> on <要素の種類>[, <要素の種類>…] [to <名前のパターン>]
  [values <値> | <値> | …]
  "<観測の手がかり>"
```

- 要素の種類は `operation`、`type`、`field`、`param`、`call`、`channel` から選ぶ。`on field, param` のように複数書ける。
  `call to "mail.send"` のように、呼び出し先で呼び出しを絞れる。
- `values` があれば、意味 Atom はその中の一つを `value` に持つ。なければ、その意味を持つかどうかだけを記録する。
- 観測の手がかりには、どこを見れば読めるかを書く。観測するエージェントは、この手がかりを持ってコードを読む。

## Law

```text
law <名前>
  "<説明>"
  [on <読み>]
  [about <意味>]
  <規則>
```

- 説明は、規則を人の言葉で書いたものだ。計算には使わない。
- `on` で、どの読みの上で計算するかを選ぶ。省くと、最初に宣言した読みになる。
- `about` で、どの意味の値を見るかを選ぶ。一致、変更の保存、往復の規則で使う。

規則は五つの形のどれかで書く。

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

値の流れに沿って、意味の値がそろうことを求める。
値の流れというのは、ある要素の値が、書き込み、引数渡し、チャネルの送受信、戻り値を通って別の要素へ渡ることだ。流れの作り方は第5章の問い2で定める。

`convert` は、どの演算がどの値からどの値への換算に当たるかを宣言する。
倍率は `* 10^k` と `/ 10^k` に当たる定数(`* 100`、`/ 1000`)に限る。

`values` のない意味に `agrees along flows` を書くと、その意味の値が、作られた所から演算を通らずに渡ることを求める。
取引 ID のように、途中で作り直されてはならない値に使う。途中で `fresh` の操作を呼んで作り直していれば、違反になる。

### 変更の保存:`changes`

```text
changes commute with operations
changes keep
```

変更の候補と、実装後のコードで計算する規則だ。

- `changes commute with operations`:変更と操作が可換であることを求める。
  変更前の操作をしてから変更後の型へ移した結果と、先に移してから変更後の操作をした結果で、`about` の意味を持つフィールドの値が一致しなければならない。
  変更後の操作は、`corresponds` で対応させた操作である。
- `changes keep`:`about` の意味を持つ要素がどれも、変更後に対応する要素を持ち、同じ意味を保つことを求める。

### 往復:`roundtrips`

```text
law order-view-sync
  "表示用の注文を編集して書き戻しても、読み取った値は崩れない。"
  about payment-info
  roundtrips read "shop.order.view.from_order" update "shop.order.view.apply"
```

読み取りと書き戻しの二つの操作が、互いに整合することを求める。確かめるのは次の二つである。

- 読み取った値をそのまま書き戻しても、`about` の意味を持つフィールドの値は変わらない。
- 書き戻した後に読み取ると、書き戻した値が返る。

表示用のデータと元のデータの同期、API の版と adapter の間の変換が、この形に当たる。

### 要素と条件の書き方

規則の中では、要素を次のように選ぶ。

- 要素の種類:`operation`、`type`、`field`、`param`、`call`、`channel`。
- 名前のパターン:`"shop.payment.*"`。`*` は任意の文字列に当たる。
- 呼び出し先で絞った呼び出し:`call to "mail.send"`。
- 意味:`payment-info` のように語彙の名前を書くと、その意味を持つ要素に当たる。

条件は `that` の後に書き、`and` でつなぐ。

- `writes <要素>`、`reads <要素>`、`calls <要素>`、`sends <要素>`、`receives <要素>`。`calls` は直接の呼び出しだけに当たる。
- `reaches <要素>`:呼び出し先をたどって、いずれその要素を呼ぶ。ヘルパーを通した呼び出しも当たる。
- `has <意味> <値>`:その意味の値を持つ。
- `inside "<局所>"`、`outside "<局所>"`:その局所の中か外か。
  要素が属する局所で決める。呼び出しは、呼び出し元の局所で決める。
  局所は、その Law の `on` の読みの局所の名前で書く。

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

## 書けているかを確かめる

`archsig law check` は、Law ファイルを読んで解いた結果を返す。

- `files`:読んだ Law ファイル。`include` で取り込んだものも入る。
- `readings`、`meanings`、`defs`、`laws`:解けた宣言。誤りがないときだけ返す。どの宣言も、名前(`name`)と場所(`at`)を持つ。
  - `readings` の分け方(`form`)は、`{"dir": {"depth": 2}}`、`"file"`、`{"groups": {"groups": [["<局所>", ["<パターン>", …]], …]}}` のどれかである。
  - `defs` は、書いたままの選び方(`selector`)を返す。
  - `laws` の規則は、`def` を展開し、`on` を省いた Law には最初の読みを補った形で返す。規則の形(`rule.form`)は `no`、`each`、`agrees along`、`changes commute`、`changes keep`、`roundtrips` のどれかで、残りの欄は文法の各部に当たる。
- `errors`:誤りの一覧。誤りがなければ空の一覧である。一つ一つが、宣言の場所(`at`、`ファイル:行`)と理由(`message`)を持つ。
  - `.archsig/law/` の直下のファイルが読めないときは、`at` はそのファイルのパスである。
  - `include` 先が読めないとき、リポジトリの外を指すときは、`at` は `include` を書いた行で、`message` が取り込もうとしたパスを持つ。
  - 並びは、まずファイルを読む中で見つけた誤り(字句や文法で解けない宣言、読めない `include`)を読んだ順に並べ、その後に解決の誤りを並べる。

Law ファイルは、`.archsig/law/` の直下の `.law` をファイル名の順に読み、`include` はその場で展開する。「最初に宣言した読み」は、この順で最初に現れる読みである。

誤りには、字句や文法で解けない宣言と、名前の解決の誤りがある。
解決の誤りは、次のどれかである。

- 宣言されていない意味や読みを使う。`on` を省いた Law で、読みが一つも宣言されていない。
- `about` の要る規則に `about` がない。
- `has` や `convert` の値が、語彙の `values` にない。
- `def` の中で `def` を使う。
- 同じ名前を二度宣言する。`def` に意味の語彙と同じ名前を付ける。
- パターンが読めない。

誤りが一つでもあれば、その Law は計算に使えない。`law check` は `files` と `errors` だけを返す。計算する問い(`plan check`、`plan split`、`compare`)は、計算も実行の記録もせずに、`{"law_errors": [<誤り>, …]}` だけを返す。`status` は動き続け、Law の誤りを `law_errors` に返す(第3章)。
