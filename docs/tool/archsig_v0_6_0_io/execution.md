# 実行と問い

## 1. コマンド

```text
archsig check --law L [--archmap A] --out NEW_DIRECTORY
archsig run --law L --archmap A --ask 'ID=QUESTION' [--ask 'ID=QUESTION' ...]
            --out NEW_DIRECTORY [--reuse OLD_DIRECTORY]
            [--time-ms N] [--memory-mib N]
archsig version
```

これが全コマンドと全flagである。`--ask`だけを反復でき、同じIDは拒否する。
単数flagの重複、未知flag、位置引数、必須flagの欠落は`usage`。
Nは`[1-9][0-9]*`の整数。省略した予算に論理的上限を設けない。
短縮flag、stdin、暗黙のファイル探索、環境変数による意味の変更を設けない。

`check`はLawの構文・版・参照・型・再帰と、指定されたArchMapの語彙・値・参照を検査する。
Lawの宣言一覧と原始語彙manifestを返す。問いの計算は始めない。欠測fieldは有効入力である。
`run`は同じ検査の後、問いの参照を解決し、依存順に必要な構成と計算を行う。
選択の外側を含む入力全体を静的検査する。

## 2. 問いの構文と参照

```text
Request  ::= Name "=" Question
Question ::= Kind "(" Head ("," Key "=" Argument)* ")"
Kind     ::= build | evaluate | check | map | compose | compare
           | localize | diagnose | repair | solve | quotient | needed
Head     ::= QName | Handle
Argument ::= QName | Handle | Enum | Degree
Handle   ::= "@" Id "/" Id | "$" Name ("." Name | "[" Index "]")*
Key      ::= Name | "bind." Name
Index    ::= "0" | [1-9][0-9]*
Degree   ::= Index
```

QName、Id、Nameは[入力](inputs.md)と[Law](law.md)の定義に従う。
字句の間のASCII空白を無視する。文字列literal、任意式、配列literal、入れ子の問いを受け付けない。
EnumとDegreeは次節で指定した位置だけに置ける。DegreeはJSONのNatの上限以内とする。
各引数名は一回だけ指定する。指定の順序に意味を持たせない。

`@snapshot/subject`は現在のArchMapの原始subjectを指す。
`$id.field`は同じrunの問いidの`outputs[field]`を指す。
その後の`.field`は[結果schema](results.md)に列挙したrecord欄、`[index]`はList/Tupleの
0始まりの成分を指す。Set、Map、意味上の集合表はindexで選べない。
原始dataはLawで宣言したconstructorの引数を`[index]`で選ぶ。別constructorの位置を選べない。
生のnode ID、過去の出力path、JSON PointerをHandleとして受け付けない。

`needed`だけは`$id`を受け取り、その問い全体の未決理由を読む。
その他の問いでは出力fieldまで指定する。後方参照を許し、依存循環は`cycle`。
同じ優先度の問いは`--ask`の順で評価する。出力answersは指定順にする。
存在しない問いID・schemaにないfield・宣言、静的に判明する範囲外index、引数不足、
静的な型不一致は`usage`。
schema上は有効な任意fieldが反証・未決のため生成されない場合は`dependency_blocked`と
元の理由を保持する。例えば反証されたmapの`$m.operation`を使う合成は、mapの反例を
残したまま未決となる。値を計算して初めて分かるindex・constructor・Optionの不適合は
projectionの`condition_failed`と、それに依存する問いの`dependency_blocked`を返す。

宣言のparameterを束縛する引数は`bind.parameter=Handle`。
固定引数名と衝突しないparameterは`parameter=Handle`と略記できる。
短形と`bind.`形による同じparameterの二重指定は拒否する。
Handleの型を宣言のparameter型へ照合し、依存型のownerも検査する。

問いは既存の宣言・対象・結果と固定の選択肢を指す。
原始値、式、対応表、cover、係数環、候補域、仮定をCLIから追加しない。
問いを変えるためにLawへ解析手順を追加する必要はない。
選択した問いと解決済みの束縛を結果に保存する。計算の意味は現在のArchMapとLawから決まる。

## 3. 固定の12の問い

表の`B`は宣言parameterへの上記束縛の有限族。`?`は省略可能であり実際の構文には書かない。
出力fieldの型・内容は[型付き結果](results.md)に従う。
buildの`on=@root`はownerを持たないentityの原始参照を要求する。
同じrootの型を持つ結果Handleも受け付ける。solve/repairはそのroot参照に加えてArchitectureも受け付け、
そのrootとoverridesを次の候補計算の基準とする。

| 問いの正確な形 | 選択と返すfield |
| --- | --- |
| `build(Reading,on=Handle)` | rootとreadingから対象と有限表示のobject algebraを生成する。`proposition:Proposition`、構成できた`object:Architecture`、成立時`algebra:ObjectAlgebra` |
| `evaluate(View,on=Handle?,B)` | viewの全parameterを束縛して評価する。onは結果のArchitectureを読む環境。`value:T`、`evaluation:Evaluation`。TはPathやそのcontainerを含むLawの返り型 |
| `check(Law,on=Handle?,B)` | Lawの選択instance族について、未束縛parameterと内部量化を保って成立を問う。onは結果のArchitectureを読む環境。`proposition:Proposition`、`evaluation:Evaluation` |
| `map(Correspondence,on=Handle,kind=configuration\|object_algebra?)` | onはこのcorrespondenceの原始instance。kindの既定はconfiguration。`candidate:MapCandidate`、`proposition:Proposition`、configuration保存確認時だけ`operation:Operation`、選択kindの成立時`map:ConfigurationMap\|ObjectAlgebraMap` |
| `compose(Handle,then=Handle)` | 二つの成立済みOperationまたは二つのPathを指定順に合成する。`proposition:Proposition`、端点確認後`operation:Operation\|Path`、Operationの場合は`map:ConfigurationMap` |
| `compare(Handle,to=Handle,kind=value\|word\|action\|relation\|diagnostics,along=Handle?)` | 下記の比較を行う。`comparison:Comparison`、`proposition:Proposition` |
| `localize(Handle,law=QName?,using=QName?,B)` | Architectureを局所化する。lawは選択Law、usingはchange。`system:LocalSystem`、`proposition:Proposition` |
| `diagnose(Handle,degree=Degree?,side=equation\|semantic?)` | LocalSystemのdegree（既定1）、side（既定equation）を診断する。`diagnostic:Diagnostic`。計算できた場合`space:Cohomology`、`class:Class`、`proposition:Proposition`をそれぞれ保持する |
| `solve(Law,using=Change,on=Handle,B)` | 許された変更でLawを満たす全候補を求める。`domain:CandidateSpace`、`solutions:SolutionSet`、`proposition:Proposition` |
| `repair(Law,using=Change,on=Handle,B)` | solveと同じ候補域で候補を選び元のLawへ再代入する。`domain:CandidateSpace`、`solutions:SolutionSet`、`proposition:Proposition`、成立時`repair:Repair`、`object:Architecture` |
| `quotient(View,on=Handle,law=QName?,B)` | onはCandidateSpaceまたはSolutionSet。view評価が同じ候補を同一視する。`quotient:Quotient`。law指定時`proposition:Proposition` |
| `needed($Id)` | 問いの依存先にある未観測位置と、それ以外の未決理由を返す。`plan:ObservationPlan` |

各行にない固定引数を拒否する。evaluateのBはviewの全parameterを束縛する。
LawのBは部分束縛を許し、未束縛parameterは[Lawの適用](law.md#5-law-の表示と適用)に従って全称化する。
有限entityは型・owner・固定参照に適合する有限族、scalarは宣言型の全域を使う。
evaluate/checkでonを省略した場合は現在の原始観測環境、指定した場合はArchitectureのoverridesを
重ねた環境を読む。候補のrootと無関係な原始値は固定する。onへ原始subjectは指定できない。
checkに対象選択がない場合は現在のArchMap全体、localize/solve/repairとon付きcheckでは選択rootと
固定外部参照に関係する族を使う。各entity parameterは、その型のownerがonと同じならonの族、
既に束縛した参照に依存する型ならその依存族、その他は現在のArchMapの全族とする。
無限域の全称を有限の試行例で代用せず、型付きの式と適用可能な算法を保持する。
未観測fieldの補完をBで与えることはできない。
`build/map/compose/compare/diagnose/needed`にはBを指定しない。

`build`はrootと各owned entityを対象族、保存確認済みの内部arrowを生成元とし、型の合う全有限語を
操作とするObjectAlgebraを返す。Law・方程式・circuit・不変量・signatureは標準規則で生成する。
claimはObjectAlgebraの構成条件を表す。algebraが未決・不成立でも、既に構成したobjectと
各型付き中間結果を保持し、claimが未決ならundetermined、反証されたならrefutedを返す。
`map`は全入力の存在事実と既知Atomからなる共通U上の総写像と名前を保持し、
family・関係・同一視の保存を検査する。object_algebraを選んだ場合は実際の対象族の対応、
Law・方程式・circuit・操作・不変量・signatureの対応と全域自然性も検査する。
local/change/relationは宣言の核生成式の運搬を検査し、局所診断や候補探索の実行を追加しない。
Operationは確認済みConfigurationMapを必須とする成立済み型であり、保存を反証した候補から生成しない。
kind=object_algebraの追加条件が反証されても、configuration保存を確認済みならそのOperationを保持できる。
端点の型不一致は入力/参照の提示違反、型の合う候補が保存条件を破ることは命題の反証である。
`compose(f,then=g)`はg∘f。Operationの場合は確認済み写像を合成し、中間対象のidentityとreadingの
一致を検査する。作用はU上の総写像の合成であり、合成後にfamily外の像を置き直さない。
空語の作用はU全体の恒等とする。MapCandidateをOperationとして渡すことはできない。
OperationとPathを混在させない。Pathは原始arrow/correspondenceの名前付き列を保持し、
Architecture間の構造保存済みOperationへ自動で昇格しない。
作用が同じでも生成元名・経路を消さない。

`compare`の型と意味を次に固定する。

| kind | 二つのHandle | 判定する命題 |
| --- | --- | --- |
| value | 同じ原始型Pまたは同じModule上のVector | 値の等値。商では剰余類の等値 |
| word | 二つのOperationまたは二つのPath | 恒等除去と結合の平坦化後の名前付き語の一致 |
| action | 同じ始終域を持つ同型のOperationまたはPath | OperationはU全域の総写像の等値、Pathは宣言から生成した同じ全域作用の等値 |
| relation | 同じreadingの同じ始終域を持つ同型のOperationまたはPath | Lawのrelationが生成する同効果関係に属するか |
| diagnostics | Diagnostic | alongの実Operationから生成した比較写像が同型かつ対象類を運ぶか |

`along`はdiagnosticsの場合だけ必須。他のkindでは指定できない。
diagnosticsは同じdegree・side・係数環を要求する。異なるdegree/side/係数環はusage。
同じ型でも実写像を構成する算法がなければunsupported_algorithm。
アフィンのdegree=1では診断群の同型性に加えて、双方の対象classの運搬を検査する。
その必要なclassが未生成なら未決。degree≠1のアフィン診断は群の同型性だけを問う。
有限診断はmatching familyと大域状態の実写像の全単射性と対応を検査する。
異なるkindの診断間に比較算法がなければunsupported_algorithmを返す。
比較の構成条件が未確認なら、値の見かけの一致で保存を成立させない。

`localize`でlawを指定した場合、BはそのLawのparameterを部分的に束縛できる。
省略時はBを置かず、同じreadingのrequired Lawを上記の全称規則で適用する。
局所viewはreading内で束縛可能な全instanceを使う。usingの省略は変更を使わない状態の局所化。
Lawの外側への参照は固定したまま保持する。局所可視性を増やすpatchを核が追加しない。
方程式の全fiberと許された変更による状態を別の系として生成し、diagnoseのsideで選ぶ。
方程式側の自由位置はusingで選んだchangeの`with`が更新するfieldの全成分だけとし、
それ以外の位置は観測環境に固定する。usingなしは自由位置が空の固定観測系で、意味状態も現在値の単一候補。
固定位置が未観測なら同じ未知slotとして保持する。方程式側の解を許された修復へ自動で読み替えない。
localizeは読取りの有限圏と、宣言したcoverから恒等・引戻し・合成で生成するtopologyの閉包を作る。
選択cover上と生成topology全体のsheaf検査を別の命題として返し、未検査範囲を成立に含めない。
予算内に閉包を生成できなければ部分の圏・coverを保持して未決を返す。

`solve/repair`のonは変更するrootまたは既に導出したArchitecture、BはLawの束縛と残る全称instance族を指定する。
Architectureを指定した場合はそのoverrides適用後の値を変更前状態とし、以前の導出元も保持する。
changeの第一parameterと型・ownerの合う全entityをon内で列挙し、残るparameterの型の積を
各instanceの候補parameter域とする。残るparameterはLawのchange規則に従う参照を含まない値型である。
候補は同時更新を行い、on外の値と全原始観測を固定する。同じslotへの異なる同時更新は
構成条件の不成立。未知の観測値は候補parameterへ変えない。
domainは許された全候補、solutionsはLawを満たす部分集合である。
探索を打ち切った部分列挙を全解集合・空集合・不存在証明として返さない。
repairの候補選択は有限域ではcanonical順の先頭、アフィン域では計算した特解を用いる。
選択は意味的一致の対象から除くが、元のLawと許された変更への再検査を必須とする。

`quotient`の定義域はonで指した集合そのもの。CandidateSpaceとSolutionSetを取り違えない。
Bはviewの全parameterを束縛し、各候補で更新された同じsubjectの値を読む。
law指定時はBのうちLawが宣言する同名parameterを同じ型で共有し、残るLawのparameterを
追加の`bind.`引数で束縛できる。残るLaw parameterは同じ適用規則で全称化する。
両宣言の同名parameterの型が異なる場合は`usage`。
指定Lawの型付き評価族が同じview値のfiber上で一定かを問う。
等式の評価族はinstance keyと左右の値対を保持し、成否Boolや零残差へ縮めない。
有限域の商は全fiberを返す。整数アフィン域では実際の格子像、核、射影、降下写像を返す。
それ以外の対応する算法のない無限域は式と型を保持して未決を返す。

## 4. 例

```text
archsig run --law reservations.law --archmap reservations.archmap.json \
  --ask 'a=build(Reservations,on=@v/B)' \
  --ask 'v=evaluate(Reservations.holdings,s=@v/p)' \
  --ask 'c=check(Reservations.retained,m=@v/m)' \
  --ask 's=solve(Reservations.retained,using=Reservations.rebalance,on=@v/B,m=@v/m)' \
  --ask 'r=repair(Reservations.retained,using=Reservations.rebalance,on=@v/B,m=@v/m)' \
  --ask 'n=needed($r)' --out result
```

次の問いは同じA/Lを再入力し、必要な`--ask`と依存する問いを指定して実行する。
`--reuse`を付けた場合も同じ再検査を行う。結果だけを意味入力として受け取るコマンドはない。

## 5. ファイル操作と出力

入力はローカルの通常ファイル。pathは呼出しcwd基準とする。
symlinkを読込み開始時に解決し、開始時に読み切ったbyte列だけを計算と同梱に使う。
HTTP、ZIP、source uriやLaw参照からの追加読込みを行わない。
再利用directoryは通常のdirectoryと下記固定pathの通常ファイルだけを読み、リンク先の追加探索をしない。

outは存在しないpath、親は既存directoryを要求する。
同じ親に一時directoryを作り、入力コピーと結果を書きflushした後、既存pathを置換しない
renameで最終directoryを作る。競合してoutが作られた場合も上書きしない。
捕捉した中断・不正入力・非対応版・反証も、出力を作れる場合は同じ形式で残す。
書込み失敗時は元の出力先を変更せず、一時directoryのpathをstderrに示す。
finalizeの状態確定と、その後の配送障害は次節に従う。

```text
NEW_DIRECTORY/
  inputs/law.law          開始時のLawのbyte列
  inputs/archmap.json     指定され読めた場合のArchMapのbyte列
  result.json            唯一の機械向け結果
```

読めなかった入力コピーは省略し、inputsにstate=unreadを残す。
result.jsonは[型付き結果](results.md)に従う。人向け表示はconsumerがこの結果から生成する。
stdoutは完了時に一行だけ出力する。

```text
{"format":"archsig.receipt/1","status":RunStatus,"exit_code":Nat,"result":String?}
```

resultは作成したresult.jsonの呼出しcwdからのpath。作成できなければ欄を省略する。
stderrは進捗と障害の自然文だけとし、プログラムはreceiptまたはresultのcodeで分岐する。
`version`は次の一行を出し0で終了する。

```json
{"product":"archsig","version":"0.6.0","semantics":["archsig/0.6.0"]}
```

## 6. 状態・終了コード・予算

RunStatusとexit codeは、下記のfinalize開始時の確定までに得た状態に対し、上から最初に当たる行で決まる。

| 条件 | status | exit |
| --- | --- | --- |
| 捕捉したSIGINT / SIGTERM | interrupted | 130 / 143 |
| io / internal | error | 74 / 70 |
| usage | invalid | 64 |
| 不正入力 | invalid | 65 |
| 未対応format/semantics | unsupported | 69 |
| 予算消尽 | interrupted | 75 |
| 一つ以上の問いが未決 | partial | 2 |
| 全問いが確定し一つ以上反証 | complete | 1 |
| 全問いが確定し反証なし、またはcheck成功 | complete | 0 |

io/internal併発時はio、複数signalは最初に捕捉したsignalを使う。
finalize開始時にSIGINT/SIGTERMをblockし、受信済み・pendingのsignalを一度だけ判断へ含めて
status/exit_codeを確定する。両方がpendingで受信順を取得できない場合はSIGINTを先とする。
以後は両signalをblockしたままresultを書き、公開し、receiptをwrite/flushしてプロセスを終了する。
確定後の新しいsignalはこの機械状態に反映せず、result、receipt、正常なプロセス終了codeは同じ確定値を使う。
公開前のwrite/flush/rename失敗だけは配送失敗への退避とし、最終resultを公開せず、
作成可能ならresult欄のないerror/74 receiptを出して74で終了する。
公開済みresultの後でreceiptのwrite/flushが失敗した場合は、確定済みresultと終了codeを変更せず、
stderrへ可能な範囲で通知する。receiptを再出力せず、欠落または不完全なreceiptは配送未完了として扱う。
receipt出力に伴うSIGPIPEもこのI/O失敗として捕捉し、確定済み終了codeをsignal既定動作で変更しない。
全問いが算法非対応でもpartialである。確定反例は有効な結果であり、他の問いが未決でも保持する。
不正入力・未対応版では数学計算を始めずnodes/answersを空にする。
問いの選択を解決できた場合だけrequestsを埋める。
捕捉できないSIGKILL・停電で最終directoryが存在しなければ出力未確定とする。
最終directoryと有効なresultが存在すれば計算結果は確定済みであり、receiptの欠落だけを配送未完了と読む。
この場合はプロセスの正常終了を確認したことにはせず、確定済みのstatus/exit_codeを事後に変更しない。

時間はCLI開始から評価終了までの単調時計によるwall time、memoryはprocessのpeak RSS byte。
time-msとmemory-mibは入力読込・検査・評価を含むsoft limitで、finalizeを含めない。
式評価と有限反復一回の前後で検査する。一つの原始演算中とOSの計測間隔内の超過を許す。
消尽確認後は新しい導出を始めず、検査済みの結果だけをfinalizeする。
未着手の問いにも停止理由を付け、暫定値を確定値として出さない。

## 7. 版、正規化、再利用

検査順はUTF-8・構文、format/semantics、対応版のschema、宣言・型・参照の順。
未知版の新しい欄を、先に未知欄エラーにしない。
同じsemanticsの下で判断規則を変更しない。

canonical JSONは[入力仕様](inputs.md#4-語彙-binding)に従う。
意味上の集合表は完全名/IDまたはcanonical値のUTF-8 byte辞書順へ並べる。
他のarray順、原始ID、Text、provenanceは保持する。
bytes_digestは読んだbyte列、model_digest(A)は集合表を正規化したArchMapのcanonical JSONのSHA-256。
model_digest(L)は[Lawの字句列正規化](law.md#1-ファイル名前再利用)に従う。
語彙digestとLaw全体のdigestを取り違えない。

`--reuse`は以前の出力directory一つを受け取り、現在のA/Lを常に必要とする。
候補の版・型・DAGを検査し、現在の原始根・Law式・問いの束縛へ照合して各推論を再検査する。
digest一致は候補の検索だけに用い、成立証拠の代わりにしない。
再検査を実装しない場合は全て再計算してよい。不正候補はreuse.rejectedへ記録し通常評価を続ける。
現在の入力から導けない結論を旧結果から増やさない。変わったsourceへ古い由来を貼り直さない。
同じ完全入力・解決済みの問いの数学的な値と条件は決定的とする。
時間・メモリ・node番号・表示基底・証人選択は意味的一致の対象から除く。
予算の増加は検査済みの主張の真偽を反転させず、未決の範囲と理由だけを更新する。
