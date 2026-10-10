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
