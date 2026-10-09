# ArchSig エンジンマニュアル

ArchSig は、対象の原始事実を記録した **ArchMap** と、読み方・規則・問いを記述した
**Law** を受け取り、成立判定、反例、解、局所と大域の関係を、計算の根拠とともに返す。
たとえば三つの操作を入力すると、経路の食い違い、同時に満たせない座標条件、
局所解を統合できない理由を、同じ事実から計算できる。

| 知りたいこと | 使い方 |
| --- | --- |
| 何を書くか | [ArchMap の書式](#2-archmap-を書く)、[Law の構文](#3-law-を書く) |
| どう実行するか | [CLI](#4-cli) |
| どのファイルが返るか | [result.json の書式](#5-resultjson-を読む) |
| 何を分析できるか | [分析別の使い方](#6-分析別の使い方) |
| 結果をどう継ぐか | [再利用と入力変更](#7-結果を次の計算へ渡す) |

## 1. 最初の一回：三つの操作を調べる

p、q、r の三つの座標と、次の平行移動を扱う。

| 操作 | 始点 → 終点 | 加える値 |
| --- | --- | --- |
| a | p → q | 1 |
| b | q → r | 1 |
| c | p → r | 3 |

Law には「合成経路と直接経路が同じ値を返す」と「各操作の前後の座標差が加算値に等しい」を
記述する。cover、行列、期待する判定は入力に書かない。

完全な入力は [triangle-3.archmap.json](archsig_engine_manual_examples/triangle-3.archmap.json) と
[coordinates.law](archsig_engine_manual_examples/coordinates.law) の二つである。
[例のディレクトリ](archsig_engine_manual_examples/README.md)をカレントディレクトリにして実行する。
以下の CLI 表記は SKILL からの呼出しにも、そのまま使う。

~~~sh
archsig engine run \
  --archmap triangle-3.archmap.json \
  --law coordinates.law \
  --out out/triangle-3
~~~

三つの問いが計算され、out/triangle-3/result.json ができる。
[完全な期待出力](archsig_engine_manual_examples/expected/triangle-3.result.json)の要点は次のとおり。

| results の name | status | 主な data | 読み方 |
| --- | --- | --- | --- |
| paths | refuted | difference.constant = "-1"、反例 x = 0 | 合成は 2、直接は 3 になる |
| coordinates | refuted | leftNull = ["1","1","-1"]、productRhs = "-1" | 三つの座標差を同時に満たす解がない |
| descent | refuted | dimension = 1、classCoordinates = ["-1"] | 今回の局所解は大域座標へ統合できない |

CLI の終了コードは 0 である。問いへの回答が反証でも、計算は完了している。
CI で Law の成立を要求する場合は、終了コードに加え、対象 query の status を読む。

c の加算値を 2 に変えた完全な入力
[triangle-2.archmap.json](archsig_engine_manual_examples/triangle-2.archmap.json)で、
**同じ Law** を使う。

~~~sh
archsig engine run \
  --archmap triangle-2.archmap.json \
  --law coordinates.law \
  --out out/triangle-2
~~~

[出力](archsig_engine_manual_examples/expected/triangle-2.result.json)では三つとも established となり、
大域座標 p = 0、q = 1、r = 2 が返る。一方、障害を置く空間の次元 dimension は 1 のままである。
「障害空間があること」と「今回の障害類が零であること」を別の欄で読む。

expected/ の JSON は出力例であり、エンジンへ渡す入力には含めない。
表示順、基底、特解、反例の選択が異なる結果は、
[計算結果の比較](#8-計算結果を比較する)に従って同じ意味を表すか確認できる。

## 2. ArchMap を書く

### 2.1 ファイル全体

ArchMap は UTF-8 の JSON ファイルである。JSON の重複キーを認めない。
次は、対象 p の存在だけを記録する完全な最小ファイルである。
三操作の分析には、第1章でリンクした全操作・値を含むファイルを使う。

~~~json
{
  "schema": "archmap.atom/v1",
  "document": "one-quantity",
  "revision": "1",
  "origin": {"kind": "model", "description": "座標 p を持つ仕様模型。"},
  "sources": [],
  "atoms": [
    {
      "id": "p.exists",
      "kind": "entity",
      "axis": "coordinate",
      "subject": "p",
      "predicate": "quantity",
      "payload": null,
      "sourceRefs": []
    }
  ]
}
~~~

| 欄 | 必須の値と意味 |
| --- | --- |
| schema | 文字列 archmap.atom/v1。版を推測して読み替えない |
| document、revision | 空でない文字列。利用者が管理する文書名と版。内容の同一性は出力の SHA-256 でも照合する |
| origin.kind | observation：実装からの観測、model：仕様模型、proposal：変更候補 |
| origin.description | 由来を説明する文字列。計算に使う事実の代用にはしない |
| sources | ソース参照の配列。model と proposal では空でもよい |
| atoms | 原始事実の有限配列。空配列も表現できる |

archmap.atom/v1 では、上表および各オブジェクトの定義にない欄は unknown_field とする。
注記を加えるために、計算済みの cover、matrix、result、proof などの欄を増設しない。

### 2.2 Atom の五成分と ID

一つの Atom は、(kind, axis, subject, predicate, payload) という一つの原始事実を表す。
id はその事実を参照する文書内で一意な文字列、sourceRefs は由来への参照である。

| 欄 | 使い方 |
| --- | --- |
| kind | entity、relation、value、term のいずれか |
| axis | Law の語彙宣言と一致する文字列。例：coordinate、syntax |
| subject | 事実が述べる対象の ID。例：a |
| predicate | 事実の種類。例：translation、source、shift |
| payload | 下表の型付き値。存在の entity だけは null |
| sourceRefs | sources にある id の配列 |

| payload | 表す値 |
| --- | --- |
| {"ref":"p"} | 対象 p への参照 |
| {"q":"-3/2"} | 正確な有理数 |
| {"enum":"add"} | 宣言された列挙値 |
| {"term":{...}} | Law が指定する項文法の有限木。波括弧内の実例はコンパイル保存の入力にある |

有理数は、0、1、-1 のような整数、または既約分数の文字列で書く。
分母は正、分母1は整数表記、先頭の + と不要な0は使わない。小数や浮動小数点の許容誤差で
等号を判断しない。JSON の数値は、行番号や次元などの整数に用いる。

entity の subject と predicate が対象の所属を宣言する。異なる型への所属は、
Law が許すときに限る。ref と項中の参照は宣言された対象へ解決され、Law の型と照合される。
同じ端点を持つ二つの操作も、それぞれの ID と事実を持つ。端点が同じという理由で統合しない。

Law の field は単一値である。同じ subject と field に複数の Atom を与えると、
同値の重複も含め duplicate_field となる。複数の由来は一つの Atom の sourceRefs に記録する。
異なる値の併記を候補集合や矛盾からの成立として解釈しない。

### 2.3 未観測の値

操作 c が存在し、端点が分かる一方で加算値が未観測なら、c.exists、c.source、
c.target を残し、**c の shift Atom だけを記載しない**。
[triangle-missing.archmap.json](archsig_engine_manual_examples/triangle-missing.archmap.json)が完全な例である。

null、0、空文字を未知値の代わりに入力しない。存在を宣言した操作は、値が不足しても
計算対象から消えない。Law の join や適用条件の評価に必要な値が欠けた場合も、
その候補を「条件が偽だった」として除外しない。

entity の Atom 族は、この入力で提示した有限の対象族を定める。未記載の entity を勝手に生成しない。
これは実装全体の観測完了を意味しない。対象を追加観測すると量化域も変わりうる。

### 2.4 ソースへ戻れる観測を作る

origin.kind が observation の場合、各 Atom に少なくとも一つの sourceRefs を付ける。
sources の一要素は次の形である。

~~~json
{
  "id": "src-a",
  "revision": "source-revision-17",
  "path": "src/translation.txt",
  "startLine": 12,
  "endLine": 15
}
~~~

revision は観測元の版を識別する空でない文字列、path はソース内の相対パス、
行番号は1以上、両端を含む。エンジンは参照の形式と解決を検査する。
SKILL はその版の実装を読み、Atom と使用文脈の対応を確認する。
エンジンはソース本文を取りに行って Atom を補完しない。

観測するのは実装コードの操作、データ、依存、呼出しとその使用である。
テストコードは観測から除外する。実行時のレース、I/O の成否・遅延、性能は別の確認で扱う。
純粋な模型や変更案はそれぞれ model、proposal と宣言し、観測入力へ自動変換しない。
ファイル名や説明の言語・framework 名は、原始値の意味を決めない。

## 3. Law を書く

### 3.1 宣言と構文

Law は UTF-8 のテキストファイルである。完全な例は
[coordinates.law](archsig_engine_manual_examples/coordinates.law)と
[compiler.law](archsig_engine_manual_examples/compiler.law)にある。
ヘッダー、使用する演算の版、語彙、構成、要求、query の順に書く。

~~~text
lawdsl 1;
module Coordinates version 1;
use finite_q version 1;
use finite_graph version 1;
~~~

lawdsl 1 の識別子は英字または _ で始まり、英数字と _ が続く。大文字・小文字を区別する。
文字列リテラルは JSON と同じ二重引用符とエスケープ、コメントは // から行末までである。
空白と改行は区切りとして扱い、宣言は ; で終える。query の expose ブロックは } で終える。
宣言名は module 内で一意、参照先は前に宣言する。型名と組込み演算名は使用する module が定める。

| 構文 | 意味 |
| --- | --- |
| entity T = atom("predicate", kind="entity", axis="axis"); | Atom から T の対象族を読む |
| field f : T -> U = atom("predicate", kind="kind", axis="axis"); | T の各対象の原始 field を U 型で読む |
| derive name = expression; | 先行する事実・導出値から型付きの値を計算する |
| derive name(x : T) = expression; | T の各対象について導出する |
| law name: forall ...: lhs == rhs; | 宣言された域の全要素で要求する等式 |
| system name: unknown z : domain -> Q; forall ...: lhs == rhs; | 有理数の未知量について同時に解く方程式族 |
| query name = check(law); | 要求の成立・反例を返す |
| query name = solve(system); | 解集合または解なしの証拠を返す |
| query name = descend(cover, coefficient, states); | 局所状態の障害と統合結果を返す |
| query name = check(law) { expose expression as label; } | 判定に用いた導出値も data.instances[].exposed に返す |

表の T、U、name、expression と ... は構文の説明用の位置であり、そのまま入力する文字ではない。
式には、宣言参照、field の適用 f(x)、配列・写像の参照 z[x]、有理数の加減算、
等号、where 内の and、以下の組込み演算を使う。

引数と forall の束縛はコンマで複数並べられる。後の束縛域と式は、先に束縛した変数を
参照できる。select の組は forall の `(first, second, direct)` のような組で受け取る。
expose 内では、対象 Law の有限対象の束縛を instance ごとに使える。compiler.law の
c と s がこれに当たる。無限の代入域の変数 x や eta に依存する expose は対応外とする。

`Ref<T>` は対象参照、`Enum<a, b>` は列挙型、Q は有理数である。
members(T) は入力で提示された T の有限集合を返す。
select (x, y) from X * Y where ... は有限直積から条件に合う組を導出する。
forall e in edges は有限対象ごとの要求、forall x in Q は全有理数についての要求である。
Q 上の全称等号はアフィン正規化で判定する。有限サンプルで代用しない。
空の instance 族についての check は not_applicable を返し、適用件数0を明示する。

語彙に合わない Atom は入力に保持するが、その Law の計算値へ暗黙に取り込まない。
一致した field の payload が異なる型なら type_error である。
演算を使用するには、対応する use 宣言が必要である。module 名と版は参照意味を固定する。
use は下記の組込み module の指定であり、ネットワーク取得、環境変数の読出し、
任意コードの呼出しではない。

### 3.2 組込み演算

| module | 入力から構成するもの |
| --- | --- |
| finite_q/1 | 正確な有理数、アフィン式、係数比較、有限有理線形系、kernel・image・quotient、代入検査 |
| finite_graph/1 | incidence、端点を含む context、辺 support の cover、重なり、局所定数係数、座標状態、Čech 複体、貼り合わせ |
| affine_tree/1 | 下記の source/IR 項、有限木の照合・置換・構造再帰、アフィン残差 |

coordinates.law の組込み演算は次の意味を持つ。

| 呼出し | 返す型付きの値 |
| --- | --- |
| incidence(vertices, edges, source, target) | 頂点と名前付き有向辺。loop と平行辺の個体を保持する |
| edge_cover(graph) | 各辺とその端点からなる patch、および辺に属さない頂点の singleton patch |
| locally_constant(graph, Q) | context 内の各辺の両端で値が等しい、頂点上の Q 値の空間。制限は頂点値の制限 |
| affine_states(system, graph) | 各 context に含まれる辺の座標方程式を満たす状態集合。制限は座標の制限 |
| descend(cover, coefficient, states) | 重なり、局所解、その差、具体的障害類、零類の補正、統合した状態 |

edge_cover は同じ頂点集合を持つ平行辺の patch も区別する。context は、選んだ辺の
端点を必ず含む部分グラフであり、重なりは頂点と辺の共通部分である。
一枚の大域 patch や最小個数の cover を、暗黙の最適化として選ばない。
係数・状態は graph と system の対応を型検査する。descend はこの
有理アフィン座標の組に適用する。一般の層や係数環をこの呼出しへ自動で読み替えない。

### 3.3 コンパイラを入力で表す項

コンパイル保存の入力も通常の ArchMap である。`SourceLawTerm<Variable>` 型の body と
RewriteRule 型の rewrite を、原始の有限木として記録する。
[compiler-add.archmap.json](archsig_engine_manual_examples/compiler-add.archmap.json)に全体を示す。

| 項の位置 | 使用する tag と欄 |
| --- | --- |
| source の式 | var と ref、lit と有理数の value、add と二要素の args |
| source の Law | eq と二つの source 式からなる args |
| rewrite | holes、pattern、template。holes は穴の名前から SourceExpr または Q への写像 |
| pattern | add、hole と name、lit-hole と name。式と定数をそれぞれ束縛する |
| template | plus と二つの args、translate と hole、const と value |
| template の scalar | tag = scalar、operator = selected、二つの Q の hole からなる args |
| 生成される IR | load と ref、const と有理数の value、plus と二つの args、equal と二つの式の args |

scalar_operator field の `Enum<add, sub>` が、selected の演算を指定する。
入力に生成済み IR や「保存する」という判定は含めない。

compile_affine(body, rewrite, scalar_operator) は、source の式で pattern を照合する。
一致したら template を生成し、translate の穴を再帰的に変換する。
穴は元の式の真の部分木に限り、生成した IR へ規則を再適用しない。
一致しなければ var → load、lit → const、add → plus を構造再帰で変換し、
最外の eq は equal に変換する。照合失敗はこの既定変換を使う条件であり、コンパイル失敗ではない。

affine_tree/1 の RewriteRule は第6.4節の二重加算 pattern と上表の型に対応する。
型が正しくても他の書換え体系や再帰方式を要求したときは unsupported を返す。
未束縛の穴や異なる型の差し込みは不正入力である。

residual_source と residual_ir は、eq / equal の左辺から右辺を引いた有理アフィン式を返す。
valuations(body(s)) は、その source 式に現れる全変数への全有理数代入である。
両残差の一致を独立な source と IR の原始意味で検査する。
有限木は一つの term payload にまとめる。

### 3.4 二入力の境界

対象の存在、値、端点、式、使用上の役割は ArchMap に書く。Law は、その語彙と、
対象に依存しない構成・適用・評価規則を記述する。
Law の数学定数と仕様上の要求は使えるが、今回の入力固有 ID や完成した対象分割、
観測値を埋め込んで結果を決めない。

完成済み cover、微分行列、rank、障害値、正解フラグ、修復済み状態、
比較同型を入力で補わせない。エンジンは入力形式で認めない結果欄を拒否する。
ただし、原始値に見せかけた結論や、不正確な観測の意味を任意に見破れるとはしない。
語彙とソースへの対応は SKILL と利用者が確認する。

## 4. CLI

~~~text
archsig engine run --archmap FILE --law FILE --out DIRECTORY
                  [--query NAME]... [--timeout-ms INTEGER]
                  [--reuse RESULT_JSON]
~~~

| 引数 | 動作 |
| --- | --- |
| --archmap FILE | 必須。ArchMap を一つ読む |
| --law FILE | 必須。Law を一つ読む |
| --out DIRECTORY | 必須。result.json の出力先。存在しないディレクトリは作り、空でないディレクトリは上書きせず失敗する |
| --query NAME | 任意、繰返し可。Law の query 名を指定する。省略時は宣言された全 query。同名の重複指定は一回として扱う |
| --timeout-ms INTEGER | 任意、正の整数。計算時間の上限。省略時は時間上限を置かない |
| --reuse RESULT_JSON | 任意。以前の結果を再検査して利用する候補。意味上の第三入力にはしない |

引数・パスはシェルの規則に従って引用する。対象集合、係数、局所性、閾値など、
答えに影響する選択は Law に書く。環境や CLI オプションで暗黙に変えない。
未知の query 名、未知のオプション、必須引数の欠落は使用誤りである。

正常に結果ファイルを書いた場合、stdout はそのパスを一行出力する。
進捗とファイル操作などの診断は stderr に書く。機械処理では stdout の説明文を解析せず、
result.json を読む。最終ファイルは書込み完了後に一括して確定し、途中の JSON を残さない。

| 終了コード | 意味 |
| --- | --- |
| 0 | 全ての選択 query に回答した。established、refuted、not_applicable を含む |
| 2 | 使用誤り、または不正入力。使用誤りでは結果ファイルを作らない |
| 3 | 一部または全ての query が undetermined。計算済み部分を含む result.json を作る |
| 4 | 読書き、出力先、または内部実行の障害で、結果ファイルを確定できなかった |

入力を読み取れたが内容が不正な場合、出力先を確保できれば runStatus = invalid_input と
issues を持つ result.json を書き、results は空にする。
出力先に書けない場合は終了コード4となり、理由を stderr に返す。
タイムアウト時は完了した導出と各 query の到達点を残し、未決の理由を interrupted とする。

たとえば paths だけを調べるには次を使う。

~~~sh
archsig engine run \
  --archmap triangle-3.archmap.json --law coordinates.law \
  --query paths --out out/paths-only
~~~

この出力の results は、第1章の期待出力の paths 要素だけを持ち、
requestedQueries は ["paths"] となる。幾何や他の問いの判定を、未実行なのに付け加えない。

## 5. result.json を読む

### 5.1 共通の形式

完全な出力ファイルは [expected 一覧](archsig_engine_manual_examples/README.md)にある。
全出力で共通の欄は次のとおり。

| 欄 | 型・意味 |
| --- | --- |
| schema | archsig.engine.result/v1 |
| engine | interface と semantics。出力形式の版と組込みの参照意味の版 |
| inputs.archmap | file、sha256、document、revision |
| inputs.law | file、sha256、module、version |
| requestedQueries | 指定した query 名の配列。省略時は Law の宣言順 |
| runStatus | complete、partial、invalid_input |
| results | query ごとの結果の配列 |
| issues | 入力全体に関する診断の配列 |
| reuse | source は候補のパスまたは null、status は下記の再利用状態 |

file は渡された入力パス、sha256 はそのファイルのバイト列の SHA-256 である。
不正入力で文書情報を読めない場合、対応する入力レコードは file と sha256 を残し、
document / revision または module / version を null にする。
利用者は inputs の文書版と内容を照合して、どの入力の回答かを確認できる。

reuse.status は、指定なしの not_requested、依存・推論を再検査して採用した revalidated、
候補から採用せず再計算した recomputed のいずれかである。
再利用候補を読めない、形式が古い、内容が不正な場合も recomputed とし、
issues に reuse_ignored と理由を残す。入力と Law が妥当なら通常の計算を続ける。

### 5.2 query ごとの結果

| 欄 | 型・意味 |
| --- | --- |
| name | Law 内の query 名 |
| analysis | check、solve、descend |
| status | 下表の判定 |
| scope | family = input、scalarDomain = Q。入力の有限対象族と有理数の範囲 |
| data | 分析別の型付きの値。未計算の値は null と理由を組み合わせる |
| evidence | atomIds、lawDecls、builtinRules。導出の入力と規則への参照 |
| conditions | 適用条件の name と status の配列 |
| issues | この query の不足・不正でない未対応・中断などの診断 |

| status | 利用者が受け取る主張 |
| --- | --- |
| established | check：全 instance の等号が成立。solve：解集合を構成。descend：局所状態から大域状態を構成 |
| refuted | check：具体的反例がある。solve：解なしの証拠がある。descend：有理アフィン座標の状態を統合できないことを示す非零の障害類がある |
| undetermined | 情報不足、対応外の計算、適用条件未成立、または中断によって、問われた主張を確定していない |
| not_applicable | check の適用対象が空。data.instanceCount = 0 と empty_domain の理由を返す |

status は query の問いに対する判定である。conditions[].status は established、refuted、
undetermined のいずれかで、前提を個別に表す。前提の refuted を、問いそのものの refuted と
取り違えない。適用条件が満たされない計算は undetermined と condition_failed を返す。

issues の各要素は code と message を持ち、分かる場合は subject、predicate、
atomIds、location を付ける。JSON の location は pointer、Law の location は
line と column により示す。行・列は1から数える。
null は有理数の0や空集合を意味しない。空配列は、計算して要素がないと分かったときに使う。

### 5.3 計算の根拠を読む

evidence.atomIds は inputs.archmap の Atom へ、lawDecls は inputs.law の宣言へ解決する。
builtinRules は finite_q/1:gaussian_elimination のように版と規則を示す。
必要な根を全て含め、無関係な根を含まない最小集合であることまでは要求しない。

判定ラベルに加え、data に独立して照合できる構成を返す。
check は正規形と反例への代入値、solve は列・行の対象名付き行列と解または左零化ベクトル、
descend は patch、重なり、係数の制限、微分、cocycle、類への写像、補正を返す。
たとえば行 a は a.source、a.target、a.shift と Law の coordinate_system までたどれる。
出力内の配列順序は付属の基底・対象名に対応し、数値だけの行列にはしない。

sourceRefs から原始事実の観測箇所に戻れる。入力ファイルと Law、固定された演算の意味、
出力の証人を合わせて計算を検査できる。
SHA-256 の一致や evidence に名前があることだけを、推論の正しさの代わりにはしない。

### 5.4 欠落・不正・非対応の違い

| 状態 | 例 | 返すもの |
| --- | --- | --- |
| 値の情報不足 | 存在する c の shift がない | undetermined、missing_fact、必要な subject / predicate。独立に計算できる幾何は残す |
| 構文・形式の不正 | 壊れた JSON、重複キー、未定義欄 | invalid_input、syntax_error / duplicate_key / unknown_field、位置 |
| 型・参照の不正 | Q に文字列タグ、存在しない端点、同じ field の二重記録 | invalid_input、type_error / unresolved_reference / duplicate_field |
| 版が非対応 | 認識できるが非対応の schema、lawdsl、use の版 | invalid_input、unsupported_version。異なる版として推測実行しない |
| 算法が非対応 | 型の意味は分かるが非線形の全称等号などを要求 | 該当 query は undetermined、unsupported、必要な演算。独立の query は続行 |
| 適用条件が不成立 | 対象の異なる状態と係数を比較しようとするなど | 型で検出できるものは invalid_input。それ以外は undetermined、condition_failed |
| 計算を中断 | timeout に達した | undetermined、interrupted、既に構成できた部分 |

入力全体の構文・語彙による型検査は、選択 query の実行前に行う。
不正な入力から都合のよい query だけを実行しない。
一方、値の欠落は不正入力ではない。未選択の query にしか要らない値の欠落によって、
選択した query を情報不足にしない。

情報不足がある主張を成立・反証とするには、宣言された型と既存事実に適合する補完が存在し、
その全てについて同じ主張が成り立つ必要がある。
次に必要な field は issues から分かる。三操作の例では、欠けた shift を2と3で補うと
答えが変わる。不足 field の表示だけで、追加観測の個数が最小であるとは限らない。

## 6. 分析別の使い方

### 6.1 経路の Law は成り立つか

**入力。** [triangle-3.archmap.json](archsig_engine_manual_examples/triangle-3.archmap.json) と
[coordinates.law](archsig_engine_manual_examples/coordinates.law)。
paths は端点から (a,b,c) を導出し、全 x ∈ Q で (x+1)+1 = x+3 を要求する。

~~~sh
archsig engine run \
  --archmap triangle-3.archmap.json --law coordinates.law \
  --out out/path-example
~~~

**出力。** [triangle-3.result.json](archsig_engine_manual_examples/expected/triangle-3.result.json)の
results[name=paths] が該当する。data の形は次のとおり。

| 欄 | 例と意味 |
| --- | --- |
| instanceCount、instances | 1 と、その instance の配列 |
| bindings | first=a、second=b、direct=c。対象を選んだ組 |
| variables | ["x"]。全称量化する有理変数 |
| left、right | constant と coefficients からなるアフィン式。ここでは x+2 と x+3 |
| difference | 左辺−右辺の正規形。constant="-1"、x の係数は "0" |
| counterexample | valuation、left、right。x=0 を代入して 2 ≠ 3 を確認 |
| exposed | expose で指定した導出値の辞書。この例は空 |
| missingDependence | 不足値へのアフィン依存、または null |
| lawResidual | その instance の全有理数代入で等号が成立なら0、反例があれば1、未決なら null |

**解釈。** status は refuted。ID a、b、c を人が比較対象として Law に埋め込んだ結果ではない。
端点をつなぐ規則から得た組について、入力値が等号を破る。
他の言語のソースから同じ値と関係を観測しても、同じ判定になる。

### 6.2 全ての条件を満たす座標を求める

**入力。** [triangle-2.archmap.json](archsig_engine_manual_examples/triangle-2.archmap.json) と、
同じ [coordinates.law](archsig_engine_manual_examples/coordinates.law)。

~~~sh
archsig engine run \
  --archmap triangle-2.archmap.json --law coordinates.law \
  --out out/coordinate-example
~~~

**出力。** [triangle-2.result.json](archsig_engine_manual_examples/expected/triangle-2.result.json)の
results[name=coordinates]。data の matrix と rhs は、入力から次のように生成される。

~~~text
variables = [p, q, r]       equations = [a, b, c]

matrix = [ -1  1  0 ]       rhs = [ 1 ]
         [  0 -1  1 ]             [ 1 ]
         [ -1  0  1 ]             [ 2 ]

rank = 2
solution.particular = [0, 1, 2]
solution.kernelBasis = [[1, 1, 1]]
inconsistency = null
~~~

**解釈。** 全解は (h,h+1,h+2)、h ∈ Q。特解の提示だけでなく、自由度を含む解集合を返す。
特解と kernelBasis は元の matrix へ代入して確認される。
matrix の行順は equations、列順は variables に対応する。

三操作の加算値が 3 の入力では、同じ CLI の --archmap を
[triangle-3.archmap.json](archsig_engine_manual_examples/triangle-3.archmap.json)にし、
別の --out を指定する。[その完全な出力](archsig_engine_manual_examples/expected/triangle-3.result.json)は
solution = null、inconsistency.leftNull = [1,1,-1] を持つ。
このベクトルと matrix の積は零、rhs との積は -1 となるので、解がない。

### 6.3 局所解を大域状態へ統合できるか

**入力。** 第6.1節と同じ
[triangle-3.archmap.json](archsig_engine_manual_examples/triangle-3.archmap.json)、
[coordinates.law](archsig_engine_manual_examples/coordinates.law)。

~~~sh
archsig engine run \
  --archmap triangle-3.archmap.json --law coordinates.law \
  --out out/descent-example
~~~

**出力。** [triangle-3.result.json](archsig_engine_manual_examples/expected/triangle-3.result.json)の
results[name=descent]。cover は次の三つの patch になる。

| patch | 頂点・操作 | localSections の値 |
| --- | --- | --- |
| Ua | p、q、a | p=0、q=1 |
| Ub | q、r、b | q=0、r=1 |
| Uc | p、r、c | p=0、r=3 |

Ua∩Ub は q、Ua∩Uc は p、Ub∩Uc は r、三重交差は空である。
coefficient.restrictions は、これらの重なりへの定数値の恒等写像を返す。
空の三重交差の空間は0次元である。

| data の欄 | 返すもの |
| --- | --- |
| contextCount、cover、overlaps、tripleIntersections | 生成した context 数と、patch・二重・三重の重なりの対象名 |
| coefficient | ring、patchDimensions・overlapDimensions・tripleDimensions、各基底、制限行列 |
| cochain | 符号規約、c0Basis・c1Basis・c2Basis、d0・d1、rankD0 |
| cohomology | theory、degree、dimension、classMap、classCoordinates、classIsZero |
| localSections、cocycle | 局所状態と、後の patch の値から前の patch の値を引いた重なり上の差 |
| correction、globalSection | 補正と統合状態。非零類または情報不足なら null |
| comparison | 座標方程式側の行列・rhs と、Čech 側への比較写像・誘導同型の検査結果 |

この例の値は、cocycle = [-1,0,2]、classCoordinates = [-1]、classIsZero = false。
cochain.convention は increasing で、patch の順に `i<j` の差を取り、`i<j<k` に進む。
d0 は3行3列、d1 は0行3列で [] と表示する。列数は c1Basis から分かる。
cohomology.dimension = 1 だけから refuted にしているわけではない。

conditions の state_gluing は「重なりで一致する状態を一意に貼り合わせられる」という
状態族の性質である。今回の局所状態が既に一致しているという判定ではない。
local_sections は、出力に使う各局所状態を具体的に構成・検査できたかを示す。
今回の統合の成否は、query の status、具体的障害類、globalSection で読む。

coefficient の patchBases、overlapBases、tripleBases は、それぞれ cover、overlaps、
tripleIntersections と同じ順で並ぶ。各基底ベクトルは、ある連結成分の頂点集合を記し、
その成分で1、他で0となる値を表す。cochain の基底は patches と0から数える component で
この基底を参照する。restrictions の from / to は patch の組、matrix はこの基底での
制限写像である。零次元への写像も記録する。三つより多い patch でも、二重・三重の組を
同じ配列形式で返す。classMap は cocycle を H¹ の座標へ送る行列であり、
`ker d1` 上で境界を零に送り、指定した商を表すことを検査する。

加算値2の
[完全な入力](archsig_engine_manual_examples/triangle-2.archmap.json)と同じ Law では次を実行する。

~~~sh
archsig engine run \
  --archmap triangle-2.archmap.json --law coordinates.law \
  --out out/gluing-example
~~~

[出力](archsig_engine_manual_examples/expected/triangle-2.result.json)は、
cocycle = [-1,0,1]、classCoordinates = [0]、correction = [0,-1,0] を返す。
d0 × correction = cocycle を確認し、各局所状態から correction を引くと重なりで一致する。
globalSection = {p:0,q:1,r:2} を元の三方程式にも代入して established を返す。

#### 値をまだ観測していない場合

**入力。** c の shift だけを欠く
[triangle-missing.archmap.json](archsig_engine_manual_examples/triangle-missing.archmap.json) と
[coordinates.law](archsig_engine_manual_examples/coordinates.law)。

~~~sh
archsig engine run \
  --archmap triangle-missing.archmap.json --law coordinates.law \
  --out out/missing-example
~~~

**出力。** [triangle-missing.result.json](archsig_engine_manual_examples/expected/triangle-missing.result.json)。
終了コード3、runStatus = partial。三つの query は undetermined で、
issues が subject=c、predicate=shift を指す。
cover、係数、d0、rankD0=2、dimension=1 は既に計算されている。
classCoordinates、classIsZero、Uc の局所状態は null である。

**解釈。** paths の missingDependence は「2 − shift(c)」を表す。
shift=2 と shift=3 は同じ型に適合する補完で、答えが変わる。
したがって不足値を観測する必要がある。記号式が残ったことを非零の数値として反証せず、
c 自体を削除して別の問題を解くこともしない。

### 6.4 エンジン自身のコンパイル保存を調べる

**入力。** [compiler-add.archmap.json](archsig_engine_manual_examples/compiler-add.archmap.json) と
[compiler.law](archsig_engine_manual_examples/compiler.law)。
ArchMap は source の式 ((x+1)+2)=0 と、二重加算をまとめるコンパイル規則を持つ。
Law は生成した IR の残差が source の残差と、全 x ∈ Q で一致することを要求する。

~~~sh
archsig engine run \
  --archmap compiler-add.archmap.json --law compiler.law \
  --out out/compiler-add
~~~

**出力。** [compiler-add.result.json](archsig_engine_manual_examples/expected/compiler-add.result.json)。
exposed.ir はエンジンが生成した Equal(Plus(Load(x),Const(3)),Const(0)) に相当する型付き木である。
left と right はともに x+3、difference は0、status は established となる。

scalar_operator だけを sub にした
[compiler-sub.archmap.json](archsig_engine_manual_examples/compiler-sub.archmap.json)を、同じ Law へ渡す。

~~~sh
archsig engine run \
  --archmap compiler-sub.archmap.json --law compiler.law \
  --out out/compiler-sub
~~~

[出力](archsig_engine_manual_examples/expected/compiler-sub.result.json)は、定数を -1 とした IR を生成し、
left = x−1、right = x+3、difference = -4、status = refuted を返す。
counterexample の x=1 では IR の残差が0、source の残差が4である。
leftZero=true、rightZero=false により、等号の真偽も変わったことを確認できる。

演算子の field だけを欠く
[compiler-missing.archmap.json](archsig_engine_manual_examples/compiler-missing.archmap.json)も計算できる。

~~~sh
archsig engine run \
  --archmap compiler-missing.archmap.json --law compiler.law \
  --out out/compiler-missing
~~~

[出力](archsig_engine_manual_examples/expected/compiler-missing.result.json)は undetermined と
missing_fact(cmp, scalar_operator) を返す。source 残差 x+3 は残る。
IR と差は null であり、演算子を勝手に add に補わない。

この分析も check の出力形式を使う。left は IR 残差、right は source 残差である。
共通の data.instances[].lawResidual は、保存要求について全代入で成立なら0、反例があれば1、
情報不足なら null を返す。これは difference=-4 のようなアフィン差や、source の残差と別の量である。

利用者はエンジンの型・式・参照・原始操作をこのように Atom と Law で扱える。
この例の established は、提示した一つの AST と規則についての全有理数代入の保証である。
任意の AST、全コンパイラ、または実装済み処理系全体の正しさへ拡大しない。

## 7. 結果を次の計算へ渡す

### 7.1 同じ計算の中で接続する

Law の derive は型付きの導出値を次の式へ渡す。coordinates.law では、
incidence の出力が cover と coefficient の入力となり、
coordinate_system と graph から作った states が descend に渡る。
descend の中でも、局所解、cocycle、類、補正、大域状態の順に、必要な条件を確かめて進む。

利用者や LLM が中間結果を説明文から読み直し、別の Atom へ転記する必要はない。
演算の型が合わない接続は拒否し、情報不足の値を使う段階は未決として残す。

### 7.2 保存した結果から続きを計算する

先に座標系を調べ、その後で局所と大域を調べる場合は次のようにする。

~~~sh
archsig engine run \
  --archmap triangle-2.archmap.json --law coordinates.law \
  --query coordinates --out out/first

archsig engine run \
  --archmap triangle-2.archmap.json --law coordinates.law \
  --query descent --reuse out/first/result.json --out out/next
~~~

二回目も意味上の入力は ArchMap と Law である。
保存した行列・解・由来は導出候補として読み、現在の原始事実と規則から再検査する。
採用できる型付き構成は次の計算へ使い、必要なら再計算する。
二回目の descent は、再利用指定なしで同じ query を計算した結果と同じ意味を持つ。

判定ラベルだけの取り込み、署名や digest だけによる採用、
結果を「新しく観測した Atom」に変換する経路は設けない。
reuse.status により採用・再計算を区別できるが、実行時間の短縮は保証しない。

### 7.3 入力を変更する

~~~sh
archsig engine run \
  --archmap triangle-3.archmap.json --law coordinates.law \
  --reuse out/triangle-2/result.json --out out/changed
~~~

ここでは新しい shift に依存する解と判定を再検査する。
出力は triangle-3 の反証に変わり、古い established を保持しない。
変更に依存しない導出は再利用できる。どの導出を再利用しても、回答の意味は変わらない。

| 変更 | 外から見た保証 |
| --- | --- |
| 配列の並び、値と関係を保つ ID の一斉変更 | ID 対応に沿って同じ判定・対象・解集合になる。表示順、基底、特解の選択は変わりうる |
| sourceRefs、ソースパス、由来の説明だけの変更 | 数学的な値は同じ。根拠が示すソース参照と入力 hash は更新される |
| 欠けていた原始値の追加 | 既に全ての許された補完に対して確定した主張は保たれる。未決の主張は成立または反証へ進みうる |
| 既存値の置換、対象・操作の追加や削除 | 方程式、適用域、cover、判定が変わりうる。前の成立を引き継がない |
| 問いに依存しない語彙と事実の追加 | 旧計算への依存が増えなければ、旧 query の意味は保たれる |
| Law、係数、局所性、演算の版の変更 | 新しい二入力として再検査する。値が同じだけでは同じ保証と扱わない |
| timeout や再利用の指定の変更 | 完了した回答の意味は同じ。どこまで完了するかと未決理由は変わりうる |

原始値の追加の保証は、対象族・Law を固定し、矛盾しない補完をする場合に限る。
新しい entity の追加で量化域を広げる場合には適用しない。
出力の hash が変わることと、数学的な意味が変わることを別に扱う。

実装を変更したら、対応するソースを再観測して observation の ArchMap を更新する。
proposal 上の成立だけで、変更後のコードも成立したとはしない。

## 8. 計算結果を比較する

同じ二入力から得た結果でも、表示順や特解・反例・基底の選択は異なる場合がある。
文字列の一致だけで判断せず、入力への参照、query、量化域を揃えて意味を比較する。

出力例の inputs.archmap.sha256 と inputs.law.sha256 は、
対応する入力ファイルのバイト列の hash である。
空白や並び順を変えると hash も変わるため、変更した入力への参照が正しいことを確かめ、
計算結果は次の条件で照合する。

| 値 | 一致を確かめる方法 |
| --- | --- |
| 判定と範囲 | 同じ query、対象族、量化域について同じ status |
| 行列と対象 | 行・列の対象名の対応を取り、原始方程式と同じ線形写像を表す |
| 解集合 | 特解を代入し、kernelBasis が kernel 全体を張ることを確認 |
| 反例 | 指定された代入で等号が破れることを確認 |
| 障害類 | 基底・局所解の変更に伴う写像と境界の差を確認し、同じ類を表す |
| 零類と統合状態 | d0 × correction = cocycle、重なりでの一致、元の全方程式への代入を確認 |

対応する有限列挙・有理アフィン・有理線形の範囲では、適用条件と情報が揃い、時間上限を置かなければ、
参照意味に従って停止し、成立または反証を返す。空の適用域は規定どおり not_applicable とする。

## 補足：数学的な意味と拡張

### A. 三操作の保証範囲

[設計の局所・大域例](archsig_atom_law_engine/local_global_example.md)と対応する。
頂点の部分集合 V と、その端点が V に入る辺の部分集合 E からなる context は18個ある。
辺 support は coordinate_system の各方程式を覆う。
三操作の経路等号は大域の paths query で検査する。
三角形の形をしているだけで2-cell や非空の三重交差を追加しない。

係数 M(W) は W 内の辺の両端で等しい頂点値、状態 S(W) は辺の座標差を満たす頂点値である。
各非空 patch の M は Q、重なりも Q、空の三重交差では0である。
局所差を係数の切断として扱えることと、状態の制限・貼り合わせを確認して descend を適用する。

加算値を γ とすると、局所差は c = (-1,0,γ−1)。
d0 = B、類への写像 μ、方程式 D の左零化写像 λ は次のとおり。

~~~text
B = [ -1  1  0 ]     μ = [-1, 1, -1]     λ = [1, 1, -1]
    [ -1  0  1 ]
    [  0 -1  1 ]

μ B = 0       λ D = 0
μ c = λ (1,1,γ) = 2−γ
dim Čech H¹ = 3 − rank B = 1
~~~

comparison は実際の行列 T、R を返し、TD = BR と μT = λ を検査する。
それにより coker D とこの Čech H¹ の間の誘導写像が同型になる。
T 自体の同型性を主張しているわけではない。

得た H¹ は、この cover と係数の有限 Čech 計算である。
一般の sheaf cohomology への同一視には、比較や acyclic cover 等の条件が別途必要となる。
大域座標の存在も、この S(W) と元の方程式についての保証である。
未観測のコード、一般の意味的修復、運用時の成功を保証しない。

### B. 自己 Law と独立な参照意味

[コンパイル保存例](archsig_atom_law_engine/compiler_preservation_example.md)は、
[エンジン自身の Law](archsig_atom_law_engine/engine_laws.md)の L05 に対応する。
source の構造再帰による意味と IR の原始意味を、最適化エンジンの答えとは独立に定める。
入力の原始演算子の違いから IR を生成して比較し、
compile_is_sound のような成功フラグを Atom として再投入しない。

同じ方針で、二入力と決定性、導出の由来、型保存、制限との可換性、合成保存、
不足情報の健全性、局所大域、reading 比較、再利用を自己 Law として扱う。
一つの有限例の確認、対応する演算全体の証明、実装の検証は、それぞれ適用範囲を明記する。

### C. AAT の他の分析への接続

対象・名前付き操作・作用・参照・局所制限・導出は、AAT の次の分析にも必要な構造になる。
それぞれの分析に必要な構成と条件は以下のとおりである。表の分析名は query 名ではない。

| 関連する分析 | 構成する対象と、判定に必要なもの |
| --- | --- |
| 変更・輸送・合成 | 原始対応から生成した写像、操作や作用の保存、経路ごとの比較。未確認候補と成立済みの射を区別 |
| Atlas・reading 比較 | Law 値の保存と診断の保存を別に検査。実際の係数・cochain 写像、kernel・cokernel、誘導写像 |
| SAGA・意味的修復 | 意味側と方程式側を独立に構成。係数比較、局所状態の対応、層・貼り合わせ条件、元の修復方程式を満たす具体的状態 |
| 正規化・基底変換・局所再構成 | 対象だけでなく操作・作用と制限を保持。存在・一意性や普遍性を、対応する有限算法または明示した証明で確認 |
| holonomy・lifting・面の細分 | 名前付き辺、平行辺、loop、面内の重複、向き、面・高次セルと原始作用。単純グラフへ情報を落とさない |
| 追加観測・修復候補の比較 | 同じ原始操作から候補と query を生成。区別不能な対、識別する観測、最小性を述べる有限候補族 |

詳細な数学の対応と拡張条件は
[設計判断](archsig_atom_law_engine/decisions.md)、
[AAT 本文](../aat/algebraic_geometric_theory/README.md)を参照する。
比較写像や修復状態も、原始 Atom と Law から導出して検査する。
