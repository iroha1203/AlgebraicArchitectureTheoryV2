# ArchSig エンジンマニュアル

注文確認画面では梱包料と送料を順に加算し、見積画面では一括で加算している。
同じ注文なら、二つの金額は一致してほしい。次のコードで、この要求が守られているかを調べる。

## 1. コードから観測する

[checkout.py](archsig_engine_manual_examples/checkout-before/checkout.py)の全体は次のとおり。

~~~python
"""注文確認画面と見積画面の金額計算。金額の単位は円。"""


def with_packaging(subtotal_yen: int) -> int:
    return subtotal_yen + 100


def with_delivery(packed_yen: int) -> int:
    return packed_yen + 200


def checkout_total(subtotal_yen: int) -> int:
    return with_delivery(with_packaging(subtotal_yen))


def quote_total(subtotal_yen: int) -> int:
    return subtotal_yen + 400


def order_totals(subtotal_yen: int) -> dict[str, int]:
    return {
        "checkout": checkout_total(subtotal_yen),
        "quote": quote_total(subtotal_yen),
    }
~~~

知りたいのは、order_totals が返す checkout と quote が、同じ商品代金に対して一致するかである。
ArchSig に渡すのは、SKILL がコードの使用文脈から観測した **ArchMap** と、
利用者が求める等式を記述した **Law** の二つである。

### 観測する Atom

SKILL は関数の本体と呼出しを読み、次の原始事実を記録する。

| コードと使用文脈 | ArchMap に記録する事実 |
| --- | --- |
| order_totals の22・23行で同じ subtotal_yen を二経路へ渡す | 入力金額の役割 subtotal |
| with_packaging の戻り値を13行で with_delivery に渡す | 梱包後金額の役割 packed、packaging の終点と delivery の始点 |
| order_totals が二つの計算結果を金額として返す | 合計金額の役割 total、delivery と quote の終点 |
| with_packaging の定義と5行の加算 | 操作 packaging、subtotal → packed、increment = 100 |
| with_delivery の定義と9行の加算 | 操作 delivery、packed → total、increment = 200 |
| quote_total の定義と17行の加算 | 操作 quote、subtotal → total、increment = 400 |

total は比較する金額の役割であり、二つの値が等しいという観測事実ではない。
関数の名前だけで役割を決めず、13行の接続と22・23行の使われ方を根拠にする。

たとえば、見積経路の加算値を表す Atom は次の形になる。

~~~json
{
  "id": "quote.increment",
  "kind": "value",
  "axis": "price",
  "subject": "quote",
  "predicate": "increment",
  "payload": {"q": "400"},
  "sourceRefs": ["quote-code"]
}
~~~

[完全な ArchMap](archsig_engine_manual_examples/checkout-before.archmap.json)には、
三つの金額の役割、三操作の存在・始点・終点・加算値と、ソースの版・行範囲が入っている。
「不一致」「正しい合計」などの判定や、完成した行列は書かない。

### 要求を Law にする

利用者が求めるのは「二段階で加算した合計と、一括で加算した合計が同じ」である。
これはコードから観測する値とは別の要求なので Law に書く。
100、200、400 は ArchMap から読み、Law には埋め込まない。

[checkout.law](archsig_engine_manual_examples/checkout.law)の全体は次のとおり。

~~~text
lawdsl 1;
module CheckoutTotals version 1;
use finite_q version 1;
use finite_graph version 1;

entity AmountRole = atom("amount_role", kind="entity", axis="price");
entity FeeStep = atom("fee_step", kind="entity", axis="price");
field source : FeeStep -> Ref<AmountRole> = atom("source", kind="relation", axis="price");
field target : FeeStep -> Ref<AmountRole> = atom("target", kind="relation", axis="price");
field increment : FeeStep -> Q = atom("increment", kind="value", axis="price");

derive steps = members(FeeStep);
derive routes = select (first, second, direct) from steps * steps * steps
  where target(first) == source(second)
    and source(first) == source(direct)
    and target(second) == target(direct);

law same_total:
  forall (first, second, direct) in routes, subtotal in Q:
    subtotal + increment(first) + increment(second) == subtotal + increment(direct);

query totals = check(same_total);
~~~

routes は始点・終点がつながる三操作を選び、same_total は各組の二経路を比較する。
この入力では packaging、delivery、quote の組が選ばれる。
端数処理のない整数の加算を有理数上の式として比較するため、有限個の金額を試すだけでなく、
全ての有理数代入について等式を判定できる。その成立は整数の金額にも適用できる。

## 2. 実行して、結果からコードへ戻る

[例のディレクトリ](archsig_engine_manual_examples/README.md)で次を実行する。

~~~sh
archsig engine run \
  --archmap checkout-before.archmap.json \
  --law checkout.law \
  --out out/checkout-before
~~~

out/checkout-before/result.json に結果が返る。
[完全な出力例](archsig_engine_manual_examples/expected/checkout-before.result.json)の totals は次を含む。

| 出力の欄 | 値 | 読み方 |
| --- | --- | --- |
| status | refuted | 要求を破る金額がある |
| data.instances[0].bindings | packaging、delivery、quote | 比較した二段階経路と直接経路 |
| left / right | subtotal + 300 / subtotal + 400 | 原始値から計算した二つの式 |
| difference.constant | "-100" | 購入時の金額が見積額より100円少ない |
| counterexample | subtotal = 2000、left = 2300、right = 2400 | 要求を破る具体的な代入 |
| evidence | Atom・Law・組込み規則への参照 | 判定を計算した根拠 |

2000円は反例の一つであり、返る反例の選択は固定されない。
全ての金額で両式の差が −100 なので、任意の整数金額でも食い違いを確認できる。

見積経路の根拠を読むには、次の順にたどる。

1. bindings の direct = quote と evidence.atomIds の quote.increment を読む。
2. ArchMap の quote.increment は値400と sourceRefs = ["quote-code"] を持つ。
3. sources の quote-code は、版 checkout-before の checkout-before/checkout.py、16〜17行を指す。
4. [17行の加算](archsig_engine_manual_examples/checkout-before/checkout.py#L17)を、
   [13行の二段階呼出し](archsig_engine_manual_examples/checkout-before/checkout.py#L13)と照らし合わせる。

CLI にソースコードは渡していない。どのコードがどの事実に対応するかは観測側で確かめ、
エンジンは ArchMap と Law から式・反例・参照を返す。

## 3. 一箇所を直して再観測する

この Law は不一致を示すが、どの料金を変更すべきかまでは決めない。
梱包料100円と送料200円を維持する方針で、quote_total の17行を次のように直す。

~~~python
    return subtotal_yen + 300
~~~

[変更後のコード全体](archsig_engine_manual_examples/checkout-after/checkout.py)を SKILL が再観測し、
[変更後の ArchMap](archsig_engine_manual_examples/checkout-after.archmap.json)を作る。
原始事実の変更は quote.increment の400から300への置換だけであり、ソースの版・参照先も更新する。

~~~sh
archsig engine run \
  --archmap checkout-after.archmap.json \
  --law checkout.law \
  --out out/checkout-after
~~~

[完全な出力例](archsig_engine_manual_examples/expected/checkout-after.result.json)では、
totals.status = established、difference.constant = "0"、counterexample = null となる。
二経路はともに subtotal + 300 で、全ての整数金額について同じ値になる。
order_totals(2000) なら、checkout と quote はどちらも2300である。

この保証は、観測した加算処理と選んだ Law に対するものになる。
値引き、税、丸め処理などを加えたら、その処理も観測して Law の適用範囲を確かめ直す。

## 4. 入力・CLI・出力を使う

入力の詳しい欄と型は [書式リファレンス](archsig_engine_reference.md)にある。
完全なファイルから始める場合は、[入出力例の一覧](archsig_engine_manual_examples/README.md)を使う。

| 入力 | 書くこと |
| --- | --- |
| ArchMap（JSON） | 操作・値・参照などの原始事実。観測ならソースの版と位置も付ける |
| Law（.law） | 語彙、構成規則、要求、量化域、query |

値が未観測なら、その field の Atom を省略し、対象・操作の存在は残す。
0や空文字で補わない。cover・行列・障害類・正解フラグは計算結果なので入力に含めない。

| CLI 引数 | 動作 |
| --- | --- |
| --archmap FILE、--law FILE | 必須の二入力 |
| --out DIRECTORY | 必須の出力先。新規または空のディレクトリを指定する |
| --query NAME | 任意、繰返し可。省略すると Law の全 query を計算する |
| --timeout-ms INTEGER | 任意、正の整数。省略すると時間上限を置かない |
| --reuse RESULT_JSON | 以前の導出を再検査して利用する候補 |

計算結果は result.json に書かれ、stdout にそのパスが一行返る。進捗・実行診断は stderr に出る。
終了コードは、全 query に回答できれば0、不正入力・使用誤りは2、情報不足などの未決は3、
読書き・内部実行の障害は4である。**反証でも計算が完了すれば0**なので、
Law の成立を要求する処理では query の status も読む。

| query の status | 意味 |
| --- | --- |
| established | 等式が成立する、解が得られる、または局所状態を統合できる |
| refuted | 反例、解なしの証拠、または統合を妨げる具体的障害がある |
| undetermined | 情報不足・非対応・適用条件未成立・中断で、問いの答えが確定していない |
| not_applicable | check の対象が空。適用件数0と理由を返す |

result.json の inputs で入力の版と hash、results で問いごとの data と evidence、
conditions で適用条件、issues で不足値などの理由を読む。null は欄と判定に合わせて読む。
成立時の counterexample = null は反例がないこと、情報不足時の difference = null は差が未確定であることを示す。

同じ Law の derive は、前の計算で得た型付きの値を次の計算へ渡せる。
保存結果を使うときも二入力を指定する。

~~~sh
archsig engine run \
  --archmap checkout-after.archmap.json --law checkout.law \
  --reuse out/checkout-before/result.json --out out/rechecked
~~~

以前の反証は、変更後の入力に照らして再検査される。再利用を指定しない計算と同じ意味の回答になる。
結果を新しい観測 Atom に転記したり、hash の一致だけで正しいと扱ったりしない。

## 5. 利用できる分析

| 分析 | 返るもの | 完全な入力・CLI・出力 |
| --- | --- | --- |
| Law の成立確認：check | 等式の正規形、成立判定、具体的な反例 | [料金計算の前後](archsig_engine_manual_examples/README.md#料金計算) |
| 同時に満たす値の計算：solve | 特解と kernel の基底、または解なしの証拠 | [三操作の座標](archsig_engine_manual_examples/README.md#三操作の座標と局所大域) |
| 局所状態の統合：descend | cover、重なり、局所解、具体的障害類、補正と大域状態 | [三操作の局所・大域](archsig_engine_manual_examples/README.md#三操作の座標と局所大域) |
| エンジン自身のコンパイル保存：check | 原始 AST と規則から生成した IR、残差の比較、反例 | [コンパイル保存](archsig_engine_manual_examples/README.md#コンパイル保存) |

三操作の例では、H¹ の次元は1のまま、特定の障害類が非零・零・未決に分かれる。
障害空間の次元だけで統合の成否を判断せず、具体的な類と補正・大域状態を読む。
コンパイル保存の成立は、提示した AST と規則についての全代入の保証である。

計算の範囲は有限関係・有理アフィン式・有理線形系である。
対応する範囲で適用条件と情報が揃い、時間上限を置かなければ、計算は完了する。
参照関係を保つ ID 変更や表示順・ソース参照だけの変更では数学的な回答は変わらず、
値・対象族・Law を変えたら再検査する。
未観測の実装や、実行時の性能・I/O の成否まで、この結果から保証することはできない。

数学的な適用条件は [局所・大域計算](archsig_atom_law_engine/local_global_example.md)、
[コンパイル保存](archsig_atom_law_engine/compiler_preservation_example.md)を参照する。
他の AAT 分析への接続は [設計判断](archsig_atom_law_engine/decisions.md#2-拡張を成立させるための判断)にある。
