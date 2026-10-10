# 入出力例と適合条件

以下の Law、ArchMap、変種表を、[宣言](law.md)、[核の構成](computations.md)、
[実行](execution.md)に対する規範例とする。いずれも仕様の有限モデルであり、
原始値・候補と、核が導出する値・成立判定を分けて示す。

## 1. 状態の保存と移行の保存

[Reservations の Law](examples/reservations.law) は状態・予約操作・移行候補の語彙、
数量の読取り、保存要求、局所読取り、許す変更を宣言する。
[ArchMap](examples/reservations.archmap.json) の全原始値は次のとおり。

| 種別 | 原始値 |
| --- | --- |
| System | A, B |
| State | p:A=(2,0), q:A=(1,1), r:B=(4,0), s:B=(3,1)。組は(free,held) |
| Reserve | e:A, p→q ／ f:B, r→s |
| Migration | m:A→B、states={p↦r,q↦s}、reserves={e↦f} |

```sh
archsig run --law examples/reservations.law --archmap examples/reservations.archmap.json \
  --ask 'value=evaluate(Reservations.holdings,s=@v/p)' \
  --ask 'operation=check(Reservations.conserved,e=@v/e)' \
  --ask 'structure=map(Reservations.Migration,on=@v/m)' \
  --ask 'migration=check(Reservations.retained,m=@v/m)' --out result-reservations
```

`value` は型付き数量対 `(2,0)`、`operation` は残差0を伴う成立、`migration` は反証を返す。
`structure` は候補の全域性と構造保存を確認し、configuration mapを返す。
m の候補対応は端点を保存するが、pでは `(4,0)≠(2,0)`、qでは `(3,1)≠(1,1)` となる。
各 instance の残差は `(2,0)`。反例は束縛した状態、両方の値、原式、使用した Atom を持つ。
f の `conserved` も成立する。二つの操作の保存と、m による数量対の保存は別に判定する。
この呼出し全体は反証を含むため exit1 とする。

同じ Law に対し、次の変種を用いる。変更欄以外の原始値と参照は固定する。

| 変種 | 変更する原始値 | 期待結果 |
| --- | --- | --- |
| 成立 | r=(2,0), s=(1,1) | retainedは有限な二状態について成立、両残差 `(0,0)` |
| 欠測 | 成立版から `r-free` Atomだけを除く | 未決。missingは `(v,r,Reservations.State.free)` |
| 対応の未観測 | 成立版から `m-states` Atomを除く | mを保持し、同じslotの不足を返す |
| 全域性違反 | 成立版のstatesからqの行だけを除く | 提示したMapが始域全体を覆わないため不正入力 |
| 端点不保存 | states={p↦s,q↦r}、reserves={e↦f} | mapの構造保存が反証され、candidateと反例を保持。configuration map・Operationを構成しない |

欠測版の `r.free` を2で補完すれば成立し、4で補完すれば反証になる。
この補完対は追加観測が必要な理由であり、観測した対象の反例としては出力しない。
反証版から `r-free` だけを除いた場合は、qの既知反例が残るので反証を保持する。

### 宣言の記述と意味の確認

Reservations の `conserved` は、次の短い条件宣言である。

```text
law required conserved(e: Reserve):
  e.to.free + e.to.held = e.from.free + e.from.held;
```

同じ reading 内のこの宣言を次へ置き換えると、型の完全名と標準の guard を明示できる。

```text
law required conserved(e: Reservations.Reserve) when true:
  e.to.free + e.to.held = e.from.free + e.from.held;
```

二つの記述は、同じ宣言名・role・parameter と、body の各出現を対応させられる。
短名を同じ完全名へ解決し、省略 guard を `true` と読むため、同じ ArchMap と問いに対して
適用範囲、型付きの両辺の評価、成立・反証・未決は一致する。欠測に対する意味も同じである。
body の inline や出現の統合は行わず、parameter `e` とその CLI 束縛を保つ。
原始宣言は同じなので語彙 manifest と binding digest も一致する。
元の byte 列、source span、Law の token 列による model_digest は別であり、
出力 node ID の一致を要求しない。各結果はそれぞれの入力位置へ戻れることを要求する。

```sh
archsig check --law examples/reservations.law --out result-reservations-check
```

この `check` では、[宣言の解決と標準の意味](law.md#宣言の解決と標準の意味)に従って、
完全名、明記した型・role、guard の扱いと、宣言した local を使う選択を確認できる。
出力は[型付き結果](results.md)に従う。原始値を評価した残差や局所状態は `run` の結果で確認する。
元の短い宣言に対する `declarations` の確認箇所は次のとおり。

| 項目 | 要求する解決結果 |
| --- | --- |
| conserved の parameter / role | `{"name":"e","type":["Ref","Reservations.Reserve"]}` / `required` |
| conserved の resolution | `Reserve` の元位置と完全名、body の元位置と Bool 型、`guard_true` と元宣言の位置 |
| Reservations の supplied | `local_declared`。Stock・Held・Transfer の実 context はこの段階で生成しない |
| 明示形の conserved | guard は型付きの明記式 `true`。`guard_true` を重ねて補わない |

Law を上の明示形へ置き換えた場合も、§1 の同じ ArchMap・問いと変種表で評価・適用の一致を確かめる。
さらに `operation=check(Reservations.conserved,e=@v/e)` に次の原始値の変種を用い、
記述の明示化が反証や欠測の扱いも変えないことを確認する。他の原始値と参照は固定する。

| 変種 | 両方の Law 記述に要求する結果 |
| --- | --- |
| `q-free` の値を `"2"` へ変更 | 左辺3、右辺2、残差1を伴う反証 |
| 基本例から `q-free` Atom だけを除く | 未決。missing は `(v,q,Reservations.State.free)` |

## 2. 局所読取りと許す修復

Reservations の Stock と Held は同じ状態参照を共有し、それぞれ一つの値を読む。
Transfer は操作の二端点の数量対を読む。核は宣言から読取りの射影、必要な Law 座標、
局所可視性を求める。全値が観測済みでも、選択した局所読取りで読めるとは限らない。

`rebalance(s,d)` の作用は `(-d,d)`。核は宣言を代入してこの作用と合成則を生成する。
修復では元の観測を保持し、Bの各状態へ許す変更を適用した候補を求める。

| 原始値または宣言の変種 | 期待する構成・判定 |
| --- | --- |
| 基本例のr=(4,0), s=(3,1) | 必要な変更は各状態で `(-2,0)`。合計が変わるためrebalanceによる修復なし |
| r=(1,1), s=(0,2) | 各状態でd=−1を導出し、候補r=(2,0), s=(1,1)を元のretainedへ代入して成立確認 |
| Transfer宣言を除く | StockとHeldではconservedが要求する二端点の数量の可視性が不足。勝手にTransferを追加しない |
| dをZ、作用を `(−2d,2d)` とする別readingで、必要変更 `(−1,1)` を問う | 整数では修復なし。有理数のd=1/2を整数修復として返さない |

StockとHeldの個別の変更が求まっても、一つのrebalanceから来るためには
`Δfree+Δheld=0` が必要である。局所状態の貼り合わせと許す作用の条件は、
[核の構成](computations.md)に従って別々に確認する。

### 複数の修復候補からの標準選択

次の Law 片に対し、snapshot `pair` の唯一の subject `s: Pair.State` に
原始値 `x=0, y=0` を与える。State はこの例の root である。

```text
reading Pair {
  entity State { x: Z; y: Z; }
  law required total(s: State): s.x + s.y = 1;
  change setpair(s: State, a: Z, b: Z) = s with { x = a, y = b };
  view first(s: State): Z = s.x;
  law optional zero(v: Z): v = 0;
}
```

この二入力に次の問いを指定する。

```text
r=repair(Pair.total,using=Pair.setpair,on=@pair/s,s=@pair/s)
x=evaluate(Pair.first,on=$r.object,s=@pair/s)
```

解の parameter は全整数対 `(a,b)` のうち `a+b=1` を満たすもの。
[標準の候補選択](execution.md#3-固定の12の問い)に用いる key は、この一 subject では
元の change の値 parameter を宣言順 `(a,b)` で原始 Z encoding へ戻した二重 array の canonical JSON となる。
最小の UTF-8 byte 長を持つ解の key は `[["0","1"]]` と `[["1","0"]]` であり、
同じ長さでは byte 辞書順で先の `[["0","1"]]` を選ぶ。
したがって `r` は `x=0,y=1` の候補を元の Law へ再代入して確認し、後続の `x` は整数0を返す。
`r` の claim は、最小 key に属する割当ての一意性と再検査を含む修復の構成条件である。
算法が `(1,0)` を先に発見しても、あるいは異なる基底・Smith normal form の特解を得ても、
選ぶ候補と後続の評価は変わらない。前述の `rebalance` の `d=-1` は解が一意なので同じ選択となる。

最小 key の選択または再検査の途中で予算が尽きた場合は、確認済みの解存在 Proposition を保持し、
`Repair` と `object` を返さず、`r` は undetermined、run は interrupted とする。

同じ解集合を表示する特解 `(0,1)` と `(1,0)` は、計算用の証人である。
次の射影は、[意味上の射影](results.md#2-回答条件導出)の表にない `representation` の
段階で `usage`、exit 64 となり、Law の評価へ進まない。

```text
s=solve(Pair.total,using=Pair.setpair,on=@pair/s,s=@pair/s)
v=check(Pair.zero,v=$s.solutions.representation.particular.coordinates[0])
```

特解を Vector 全体として取り出す迂回も同じ理由で拒否する。結果 JSON には両方のような
正しい表示を保持できるが、その選び方で後続の命題を `0=0` または `1=0` へ変更しない。
SolutionSet 自体を `quotient` へ渡す接続と、意味上選択済みの `$r.object` を読む接続は有効である。

### 識別子によらない選択と一意性

次の Law 片で、唯一の root の `first` は owned State `a`、`second` は `b` を指し、
両方の `x=0` を観測した場合を考える。

```text
reading Rename {
  entity System { first: State; second: State; }
  entity State(owner: System) { x: Z; }
  law required total(r: System): r.first.x + r.second.x = 1;
  law optional pinned(r: System): r.first.x + r.second.x = 1 and r.first.x = 0;
  change setx(s: State, v: Z) = s with { x = v };
  view firstx(r: System): Z = r.first.x;
}
```

`repair(Rename.total,using=Rename.setx,on=@rename/root,r=@rename/root)` の最小 key は
`[["0"],["1"]]`。`a.x=0,b.x=1` と `a.x=1,b.x=0` の二つの割当てが同じ key を持つ。
核は最小性と二つの異なる割当てを確認し、一意選択を含む構成条件を反証する。
全解集合と成立済みの存在命題は保持し、Repair/object は返さない。
二つの subject ID と全参照を入れ替えても、同じ一意性の反証になる。

同じ問いの Law を `Rename.pinned` にすると、`first.x=0,second.x=1` の割当てが一意に決まる。
修復後に `firstx` を評価すると0となり、ID の改名後も0である。
この差は作者が明記した要求から生じ、ID の順序や solver の発見順から生じない。

## 3. 三辺の修復と局所・大域

次のreadingに、所属する三点p,q,rの観測座標0と、
名前付きの辺a:p→q、b:q→r、c:p→r、shift値1,1,γを与える。
座標は観測済みであり、未知の観測値を解変数に置き換えない。

```text
reading Coordinates {
  entity System;
  entity Point(owner: System) { coordinate: Z; }
  arrow Shift(owner: System, from: Point[owner], to: Point[owner]) { shift: Z; }
  law required aligned(e: Shift):
    e.to.coordinate - e.from.coordinate = e.shift;
  local Edge(e: Shift) reads e.shift, e.from.coordinate, e.to.coordinate;
  change move(p: Point, d: Z) = p with { coordinate = p.coordinate + d };
}
```

修復の問いはalignedの全instanceと、同じSystem配下の全Pointへのmoveを選ぶ。
局所診断も `localize($a.object,law=Coordinates.aligned,using=Coordinates.move)` とする。
`$a.object` は対象Systemのbuild結果。方程式側の自由座標はmoveの更新位置coordinateだけで、
shiftは固定値である。using省略時の固定観測系と、この変更族の診断を区別する。
核は各点の変更量を独立に持つ候補から `Dz=b` を生成する。
列をp,q,r、行をa,b,cとする表示では
`D=[[-1,1,0],[0,-1,1],[-1,0,1]]`、`b=(1,1,γ)` となる。
行列、局所解、係数、微分、障害類はすべて生成結果である。

| γ | 期待する修復結果 |
| --- | --- |
| 3 | λ=(1,1,−1)、λD=0、λb=−1という不成立証拠 |
| 2 | 候補座標z=(0,1,2)。Dz=bと元のalignedへ再代入して成立確認 |
| 未観測 | cの存在と端点を保持し、shiftの追加観測を要求。補完2と3で答えが異なる |

Edgeの読取りから生成した局所解の差と制限を用い、整数係数のČech H¹はZ、
対象の類は表示 `1+1−γ` となる。γ=2でもH¹そのものは零にならず、対象の類が零になる。
欠測時にはshiftに依存しない構造までを保持し、当該対象の障害値は未決とする。
局所解の貼り合わせ、係数の制限、許す変更との対応は核が確認する。

## 4. エンジンの有限仕様モデル

[Engine の Law](examples/engine.law) はExprのLit/Var/Add、IRのConst/Load/Plus/Minusを
有限木dataで定義する。`translate`、`evalSource`、`evalIR` はそれぞれ構造再帰のviewであり、
各constructorで行う計算をすべて宣言している。
[ArchMap](examples/engine.archmap.json) は原始source treeと候補演算のenumだけを持つ。

この三つの view は data と整数の parameter を取る helper であり、呼出し先の式として使う。
簡単な条件を直接書く Reservations と同じ言語で、ここでは変換と参照評価の意味を詳細に定義する。
有限木の評価、全整数代入の比較、反例の生成は核が行う。
作者が宣言する再帰式と、核が選ぶ計算手順を区別する。

sourceは `x+(1+2)`。二つのCompiler subjectは同じsourceを持ち、operatorだけが異なる。
生成IRはそれぞれ `Plus(Load,Plus(Const(1),Const(2)))` と
`Minus(Load,Minus(Const(1),Const(2)))`。次の表はそれを評価した式と保存判定を示す。

| 原始operator | 生成IRの評価（全x） | `preserves` の期待結果 |
| --- | --- | --- |
| AddOp | x+3 | 全Z代入について成立 |
| SubtractOp | x−(1−2)=x+1 | x=−1でsource=2、IR=0という反例 |
| 未観測 | 未確定 | Compilerを残しoperator不足を返す。上の二補完で答えが異なる |

```sh
archsig run --law examples/engine.law --archmap examples/engine.archmap.json \
  --ask 'add=check(Engine.preserves,c=@engine/add)' \
  --ask 'subtract=check(Engine.preserves,c=@engine/subtract)' --out result-engine
```

生成IR、正規化した係数、比較値、保存判定には、sourceとoperatorのAtom、各view、
固定演算までの導出根を付ける。参照評価はsourceの構造再帰だけで定義し、候補変換に依存しない。
生成IRは導出値として保持する。原始Atomのfamilyへ追加しない。
結果のscopeは提示されたCompilerとsourceについての仕様モデルで、内側のxは全Z代入である。
各演算の一般的な保存と、実装全体の正しさは、この有限例の成功からは導かない。

## 5. 入力・評価・空域の適合条件

| 試み | 期待する判定と保持する情報 |
| --- | --- |
| 存在するsubjectを必須field不足で除く | subjectとLaw instanceを保持し、不足を伝播する |
| 同じslot hを二度読む | h−h=0は成立可能。2−hは補完2と3で答えが異なり未決 |
| none、空List/Set、未観測を同じ値にする | 明示的不在、観測した空の族、Holeを区別する |
| 同じsubject/fieldへ二つのAtomを置く | 同じ値でも不正入力。相反する値から空の補完集合を作らない |
| 型の異なるMapの参照、重複key、未登録参照 | 提示規則で拒否し、保存Lawの反証とは分ける |
| Termを直接または複合型経由でSet要素型に置く | 型検査で拒否。項の有限族はListとして保持できる |
| viewが`Option<Path<State,State>>`を返す | `some(path(e))`をOptionの型とPathへの参照で出力し、原始Atomへ混ぜない |
| 修復結果を次のsolve/repairのonへ渡す | 前のArchitectureのoverridesを変更前状態として使い、原始観測と導出元を保持する |
| `a=needed($b)`と`b=needed($a)`を同じrunへ指定する | exit64。各問いIDを指すcycleを返し、無関係なLaw/ArchMap位置へ帰属させない。依存グラフを保持し、意味計算は開始しない |
| ObjectAlgebraの二対象が同じquery patternを持ち、適用条件や値が異なる | 固定全域延長の条件を反証し、condition_failedと構成済みの対象を保持する |
| ZとFpの方程式を一つのreadingに置く | 型別の共有環を保持し、AAT接続用Observableはその有限積。係数を暗黙に変換しない |
| 値を保って原始ID・入力順・source refを変える | 同型に沿う判断・対象・解集合。出力の由来は対応する参照へ変わる |
| 空の観測済み有限族を全称／存在量化 | 全称成立／存在反証、評価件数0、有限域scopeを保持する |
| 空の族のbodyに型不整合がある | 空虚な成立の前に型検査で拒否する |
| Compiler族が空 | preservesの全称は件数0の成立。実在する候補の保存を確認したとは出力しない |
| 結果参照や導出専用型を原始値に書く | 入力の型・参照規則で拒否する |
| 成功ラベルを普通の原始値へ偽装する | 語彙・観測の点検対象。核による意味的な偽装検出を保証しない |
| 未観測候補まで探索済みとする | 記録した有限候補と宣言した変更族のscopeを保持する |
| Law評価が等しい二つのreadingを比較する | 診断保存は実際の局所・係数・複体の比較から別に検査する |

## 6. CLI と結果の適合条件

上の例をpublic CLIで計算する実装は、[型付き結果](results.md)に従い、
原式、型、束縛、値、成立判定、証拠、scope、原始入力への参照を再読できる形で出力する。
未観測、局所可視性不足、未対応算法、予算中断を理由ごとに保持する。
空虚な成立と通常の成立を、評価件数と量化域から区別できることを確かめる。

再利用候補を改変しても、現在の二入力から得る結論は変わらない。
結果の型・参照・導出DAGを検査し、Atom、Law宣言、固定演算まで到達することを確認する。
終了コード、signal、I/O失敗、依存する問いへの未決の伝播も実行仕様に従う。
