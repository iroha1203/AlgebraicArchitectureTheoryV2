# 必要情報から選択・再観測まで

要求を満たす変更の有無と、実際に採用する変更を決めるために必要な情報は異なる。
この二つを比較する問いでは、同じ `RepairProblem` から範囲・観測・候補を読む。
Law の作者が入力族、読んでよい原始位置、変更の意味を定める。CLI はソースの意味を抽出しない。

## 同梱例を実行する

SKILL 本体の `cli`・`skill`・`work` を実際の絶対パスに設定する。以下は架空の仕様例であり、
対象リポジトリを観測した結果ではない。`common-loop` の三入力・asks・shell だけを使い、cwd は任意。
`--out` は毎回新しい directory 名にする。

```sh
example="$skill/assets/common-loop"
sh "$example/run.sh" "$cli" "$work/finite-missing" finite missing
sh "$example/run.sh" "$cli" "$work/finite-observed" finite observed "$work/finite-missing"
sh "$example/run.sh" "$cli" "$work/finite-reobserved" finite reobserved "$work/finite-observed"

sh "$example/run.sh" "$cli" "$work/integer-missing" integer missing
sh "$example/run.sh" "$cli" "$work/integer-observed" integer observed "$work/integer-missing"
sh "$example/run.sh" "$cli" "$work/integer-reobserved" integer reobserved "$work/integer-observed"
```

`observed` の両例と `integer reobserved` は比較対象 `small` が `refuted` なので終了値1。
全体の `status=complete` と、採用した `wide`、`first`、`ap`、`ok` の成立を読む。
有限の `reobserved` は small も成立し終了値0となる。
入力を変えた `--reuse` に identity 不一致の warning が出るのは、旧結果を採用せず現在入力で計算したため。
`missing` は観測計画の成立だけを返す。観測計画が成立しても未観測の実値や採用済みの修復は得られない。

### 有限例で分かること

`finite.law` の Root.h は外部から確認する Bool。x/y/z の flag は初め false。
要求は x/y が h と等しいこと、z の flag は自由である。
`finite-observe.asks` は次を順に実行する。

1. `u` は全3部品、`n` は x だけの変更範囲を読む。
2. `p=prepare(...)` が Law、change、基準対象、入力 view を固定する。
3. `d=observe(...,output=decision)` は、全範囲なら h の両値で修復できるので追加読取りを要求しない。
4. `a=observe(...,output=assignment)` は、両方の h に共通の x/y 割当てがないので Root.h を要求する。

作業者が実際の値を確認して ArchMap に記録する段階を、同梱例では `finite-observed.archmap.json` の
h=true で表す。実務でこの値をそのまま転記しない。
`finite-choose.asks` は同じ問題から `scopes`、small/wide の `solve`、候補二つを求める。
small は y を false に固定するため反駁され、wide は x=y=true、z は false/true の二候補を持つ。
`scopes` は包含極小の範囲 {x,y} を返す。許された範囲と実際に値が変わる部品は区別する。

例は「要求に無関係な z を初期値 false に保つ」という選択理由で、`first` の index=0 を `apply` する。
`other` の index=1 も有効だが採用しない。これは利用者の選択であり、CLI の最適性・一意性の結論ではない。
`apply` は元の `Assignment` の所属と再代入を検査し、`Selection` と新しい `Architecture` を返す。
`ok` はその対象の元 Law を再検査する。後続変更ならこの object を次の prepare の on へ渡す。

h=false の再観測では、同じ問いでも small が成立し、最小範囲は空となる。
以前の x=y=true という採用理由を現在の事実へ持ち越さず、候補・範囲・Law を読み直す。

### 整数例で分かること

`integer.law` は h/k を変え、要求 h=b を満たす。未観測 b は全整数域を意味し、有限の仮値へ置換しない。
入力によらず何らかの整数修復は存在するので、定数 view の `decision` に追加読取りは不要。
共通の具体的修復には b の観測が必要で、`assignment` は State.b を要求する。
観測 b=2 後は h=2、k は全整数域のまま。候補0は k=0、候補1は k=1 で、例は初期 k=0 を保つ候補0を採る。
small は空範囲で h=0 を固定するため反駁される。wide は State 一つの変更を許し成立する。
再観測 b=4 後は h=4 へ変わり、適用後の Law も再検査する。
無限族を列挙し終える必要はなく、`SolutionSet` から必要な元割当てだけを `candidate` で復元する。

## 読む結果を絞る

通常は CLI の summary の answer id、status、必要な output を読む。
追加読取りの実位置と選択内容を説明する必要があるときだけ、保存 `result.json` で当該 answer の
`outputs.plan` / `outputs.assignment` / `outputs.selection` の node を辿る。
plan の `requirements[].field` が観測する snapshot/subject/field を、locations が Law の使用位置を示す。
`cases` や affine 表現の全件閲覧、内部消去計画の選択、証拠 node の手入力は不要。

各 status はその問いの命題について読む。`observe` の refuted は許した読取りでは目的を満たせないという意味で、
修復不能とは限らない。`solve` の refuted はその範囲に解がないこと。
`undetermined` は reasons の欠測・依存先・`unsupported_algorithm` を確認し、反駁へ読み替えない。
未対応族を通すために Law を弱めず、必要なら対象や問いを見直す判断を利用者へ返す。

保存済みの表示は現在の根拠を代替しない。観測を追加・訂正・撤回したら、現在の三入力と同じ asks を再実行する。
`--reuse` は任意であり、使わない実行と同じ意味を保つ。Law・語彙の変更時も型・所属・元 Law を再検査する。

## 担当別のモデルを全体へ構成するとき

必要なのが部品の修復ではなく担当別記述の統合なら、`assemble` を選ぶ。
担当 root と共有個体の対は Law/ArchMap の作者が意味を確認して記録し、全体対象や包含写像は CLI が構成する。
`assemble_map` には担当別の原始対応を与える。完成した全体写像や保存証拠を利用者が配線しない。

```sh
sh "$example/run.sh" "$cli" "$work/assembled" assembly observed
```

`assembly.asks` は二担当 A/B の局所対象を G へ構成し、元 Law の検査、共有個体の所属の読取り、
局所対応の全体写像への構成を行う。全 answer が established、終了値0となる。
構成後の object は check/evaluate と次の変更計算の on に使え、map は compose/compare に使う。
共有箇所の値が矛盾したらその根拠を修正し、現在入力から構成し直す。
全体にしか書けない要求を局所の検査だけで満たした扱いにしない。
