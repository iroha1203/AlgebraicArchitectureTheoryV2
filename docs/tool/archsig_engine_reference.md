# ArchSig 入力・出力リファレンス

[操作手順](archsig_engine_manual.md) · [完全なファイル例](archsig_engine_manual_examples/README.md)

## ArchMap

UTF-8 の JSON を使う。文書内の重複キー、未定義の欄、解決できない参照は不正入力となる。

| 欄 | 値 |
| --- | --- |
| schema | archmap.atom/v1 |
| document、revision | 空でない文字列。入力文書の名前と版 |
| origin.kind | observation：実装の観測、model：仕様模型、proposal：変更候補 |
| origin.description | 由来の説明。計算する事実の代用にはしない |
| sources | id、revision、path、startLine、endLine を持つ参照の配列 |
| atoms | 原始事実の配列 |

sources の id は文書内で一意、path は相対パス、行番号は1から始まり両端を含む。
revision は観測元の版を識別する。observation の各 Atom は少なくとも一つの sourceRefs を持つ。
model と proposal の sources・sourceRefs は空でもよい。由来は自動で読み替えない。
実装の観測には、操作とデータの使用文脈を含め、テストコードと実行時の挙動を含めない。

### Atom の欄

| 欄 | 値 |
| --- | --- |
| id | 文書内で一意な原始事実の ID |
| kind | entity、relation、value、term |
| axis、subject、predicate | 読みの軸、対象 ID、事実の種類。Law の宣言と照合する |
| payload | 型付きの値。存在を表す entity だけは null |
| sourceRefs | sources の id の配列 |

payload は次のいずれか一つのタグを持つ。

| 書き方 | 意味 |
| --- | --- |
| {"ref":"subtotal"} | entity として宣言された対象への参照 |
| {"q":"-3/2"} | 正確な有理数 |
| {"enum":"add"} | 宣言された列挙値 |
| {"term":{...}} | 型付きの有限木。全体例は [compiler-add](archsig_engine_manual_examples/compiler-add.archmap.json) |

Q の値は整数または既約分数の文字列で書く。分母は正、分母1は整数表記とし、
先頭の + と不要な0、小数・近似値は使わない。JSON の数値は次元・行番号などの整数に使う。

field は単一値である。同じ subject と field の二重記録は、値が同じでも duplicate_field となる。
複数の由来は sourceRefs にまとめる。値の欠落は field の Atom を省略して表し、
その値を必要としない計算は継続する。欠落を理由に対象を除外したり、join の条件を偽と扱ったりしない。
同じ始点・終点の操作も、それぞれの ID を保持する。

## Law DSL

完全な記述は [料金計算](archsig_engine_manual_examples/checkout.law)、
[座標と局所・大域](archsig_engine_manual_examples/coordinates.law)、
[コンパイル保存](archsig_engine_manual_examples/compiler.law)を参照する。

lawdsl 1、module 名と版、use する演算の版から書き始める。
識別子は英字または _ で始まる英数字・_、文字列は JSON と同じ引用・エスケープである。
コメントは // から行末、宣言は ; で終える。expose ブロックは } で終える。
宣言名は一意にし、参照先は先に宣言する。

| 宣言・式 | 用途 |
| --- | --- |
| entity / field | Atom の kind・axis・predicate と、対象・値の型を対応づける |
| derive | 先行する値から計算する。引数付きの宣言も使える |
| members、select ... from ... where | 有限対象族、直積、条件を満たす組を作る |
| law / forall | 対象族や Q 上の全代入で要求する等式を定める |
| system / unknown | 同時に解く有理線形方程式を定める |
| query | check、solve、descend の結果を返す |
| expose | check の各有限 instance で導出値を出力する |

引数・束縛はコンマで並べ、後の式から先に束縛した値を参照できる。
型には Q、`Ref<T>`、`Enum<a,b>`、`SourceLawTerm<T>`、RewriteRule を使う。
field の適用、写像の添字参照、有理アフィン式、等号、where の and を扱う。
Q 上の全称等号はアフィン正規化で判定する。
expose は有限対象の束縛を使い、無限の代入域の変数に依存する場合は unsupported となる。

| use する module | 演算の範囲 |
| --- | --- |
| finite_q/1 | 有理アフィン式、係数比較、有理線形系、kernel・image・quotient、代入検査 |
| finite_graph/1 | incidence、端点を含む context、辺 support の cover、重なり、局所定数係数、座標状態、Čech 計算 |
| affine_tree/1 | source/IR の有限木、照合・置換・真の部分木への構造再帰、残差 |

edge_cover は各辺と端点の patch と孤立頂点の patch を作り、平行辺の個体も区別する。
locally_constant は辺の両端で等しい頂点値、affine_states は座標差の方程式を満たす値を返す。
descend はこの有理アフィン状態・係数の組に適用する。
コンパイルの二重加算規則と source/IR の意味は [コンパイル保存例](archsig_atom_law_engine/compiler_preservation_example.md)、
項の全構造は [入力 JSON](archsig_engine_manual_examples/compiler-add.archmap.json)にある。
compile_affine は規則を照合し、不一致なら var→load、lit→const、add→plus、eq→equal と構造再帰で変換する。
未束縛・型不一致の穴は不正入力、それ以外の非対応な書換え体系は unsupported となる。

use の版は組込みの意味を固定する。外部 callback、環境変数、ネットワークから値を補わない。
入力固有の対象 ID・観測値・完成した計算結果を Law の定数へ埋め込まない。
語彙に合わない Atom は入力に保持し、一致した field の型は選択 query の実行前に検査する。

## result.json

| 共通の欄 | 内容 |
| --- | --- |
| schema | archsig.engine.result/v1 |
| engine | interface と semantics：出力形式と参照意味の版 |
| inputs.archmap | file、sha256、document、revision |
| inputs.law | file、sha256、module、version |
| requestedQueries | 選択した query 名。省略時は Law の宣言順 |
| runStatus | complete、partial、invalid_input |
| results | query ごとの結果 |
| issues | 入力全体への診断 |
| reuse | source と status：not_requested、revalidated、recomputed |

sha256 は入力ファイルのバイト列の hash である。文書情報を読めない不正入力でも
file と hash を残し、読めなかった名前・版を null にする。

各 result は name、analysis、status、scope、data、evidence、conditions、issues を持つ。
scope は入力の有限対象族と Q の量化域を示す。evidence の atomIds・lawDecls・builtinRules は、
入力と版付き規則まで解決できる。conditions は前提ごとの成立・反証・未決を示す。

| analysis | data の主な内容 |
| --- | --- |
| check | instanceCount、instances。各 instance に bindings、variables、left、right、difference、counterexample、exposed、missingDependence、lawResidual |
| solve | variables、equations、matrix、rhs、rank、solution または inconsistency |
| descend | cover・重なり・係数・cochain・cohomology・局所状態・cocycle・correction・globalSection・comparison |

check の式は constant と coefficients からなる。difference は左辺−右辺。
lawResidual は instance 全体の成立なら0、反例があれば1、未決なら null で、数値の差とは別である。
solve の solution は particular と kernelBasis、inconsistency は leftNull と行列・rhs との積を返す。
行列・ベクトルの成分は Q の文字列、行・列は付属の対象名や基底順に対応する。
descend の全構造は [零類と大域状態の出力例](archsig_engine_manual_examples/expected/triangle-2.result.json)にある。
零行の行列は [] とし、列数は基底から読む。classMap は cocycle を商の座標へ送る。

null は欄と status に合わせて読む。成立時の counterexample = null は反例がないこと、
情報不足時の difference = null は差が未確定であることを示す。0や空集合の代用にはしない。
空配列は、計算して要素がないと分かったときに使う。

### 判定と診断

| 状態 | 出力 |
| --- | --- |
| 成立・反証 | query の established / refuted と証人 |
| check の適用対象が空 | not_applicable、instanceCount = 0、empty_domain |
| 値の欠落 | undetermined、missing_fact と subject / predicate、計算済み部分 |
| 非対応な算法・条件未成立 | undetermined、unsupported / condition_failed、必要な演算・条件 |
| 時間上限による中断 | undetermined、interrupted、完了した導出 |
| 不正入力 | invalid_input、空の results、syntax_error / duplicate_key / unknown_field / type_error / unresolved_reference / duplicate_field |
| 非対応の形式・演算の版 | invalid_input、unsupported_version |

issues の要素は code と message を持ち、分かる場合は subject、predicate、atomIds、location を付ける。
JSON の位置は pointer、Law の位置は1から数える line / column で示す。
入力全体の形式・型が不正なら実行せず、算法の非対応や不足値は独立した query を妨げない。
欠落値がある主張を確定するには、許された補完が存在し、その全てで同じ主張が成り立つ必要がある。

### 保存と再利用

出力は書込み完了後に確定し、途中の JSON や既存出力の上書きを残さない。
使用誤りでは結果ファイルを作らない。不正入力は出力先を確保できれば診断ファイルを作り、
読書きや内部実行の障害で確定できない場合は stderr に理由を返す。

再利用候補は現在の二入力へ照合し、推論を再検査する。採用時は revalidated、
採用しなかったときは recomputed となる。候補を読めない、古い、不正な場合も
reuse_ignored の理由を残して通常の計算を続ける。速度の向上は保証しない。

同じ意味の計算でも、表示順・基底・特解・反例の個体は異なりうる。
解は元の方程式へ代入し、kernel の基底が全体を張ることを確かめる。
反例は等号が破れること、障害類は基底の対応と境界の差、零類は補正の代入と貼り合わせで照合する。
