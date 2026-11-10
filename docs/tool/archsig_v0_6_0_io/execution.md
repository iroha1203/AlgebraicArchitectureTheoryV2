# 実行と問い

## 1. コマンド

```text
archsig check --atom-definition D [--atom-definition D ...] --law L [--archmap A] [--out NEW_DIRECTORY]
archsig run --atom-definition D [--atom-definition D ...] --law L --archmap A --ask 'ID=QUESTION' [--ask 'ID=QUESTION' ...]
            [--out NEW_DIRECTORY] [--reuse OLD_DIRECTORY]
archsig evidence --archmap A --atom SNAPSHOT/ATOM [--atom SNAPSHOT/ATOM ...] [--source ID=FILE ...]
archsig law-fibers --table TABLE
archsig version | --version
archsig --help | -h | help
archsig help run | help check | help evidence | help law-fibers | help version
archsig run --help | check --help | evidence --help | law-fibers --help | version --help
```

これが全コマンドと全flagである。`--atom-definition`と`--ask`を反復でき、問い ID の重複を拒否する。
単数flagの重複、未知flag、位置引数、必須flagの欠落は`usage`。
`run`の`--out`は任意で、省略時は回答の状態・値・反例・未決理由を一行の
`archsig.summary/1`として標準出力へ返す。保存する場合だけ`--out`を指定する。
`check`も`--out`は任意で、省略時は検査状態を一行の`archsig.receipt/1`として返す。
helpは入力を読まず使い方と例を表示し0で終了する。各サブコマンドの`-h`も`--help`と同じ。
help以外の短縮flag、stdin、暗黙のファイル探索、環境変数による意味の変更を設けない。

`check`は Atom 定義の構文・版・名前・型・依存、Law の構文・版・参照・型・再帰と、
指定された ArchMap の binding・値・参照をこの順に検査する。
定義と Law の宣言一覧、原始語彙 manifest、元の宣言に対応する名前・型・既定規則の解決結果を返す。
`--atom-definition`は一件以上必須。ファイル間の依存は [Atom 定義](definitions.md#3-依存参照digest)に従う。
省略したguard、同名fieldの対応、local宣言の有無による構成方式を、
[型付き結果](results.md)の規則名と元のLocationから確認できる。
問いの計算は始めず、実際の対象・context・cover・候補域は生成しない。欠測fieldは有効入力である。
`run`は入力読込み前に問いの字句・区切り・Handle構文、同じ綴りの引数keyの重複と問いIDの重複を検査し、
不正なら`usage`を返す。入力I/O・schema・型の不正もある場合は、この問い構文の診断を先に返す。
その後、`check`と同じ入力検査を行い、問いの種類・宣言名・型・参照・束縛を解決し、依存順に必要な構成と計算を行う。
短形と`bind.`形の同じparameterへの二重指定は、宣言と固定引数名を使う束縛解決で検査する。
[検査の段階](definitions.md#4-検査と責務)に従い、選択の外側も構文・schema・型・明示参照を検査する。
未使用の定義・語彙・import・dependency・宣言は受理する。計算は選択した問いとその依存から進める。
全 Atom 定義と Law 全体の静的検査が完了した場合だけ、宣言と語彙の全件を出力する。
指定された全入力の検査が不正・非対応・中断で終わった場合は、§5 の標準エラー出力で理由を返す。
検査途中の宣言一覧や入力コピーだけを、失敗記録のファイルとして保存しない。

## 2. 問いの構文と参照

```text
Request  ::= Name "=" Question
Question ::= Kind "(" Head ("," Key "=" Argument)* ")"
Kind     ::= build | assemble | assemble_map | evaluate | check | map | compose | compare
           | localize | diagnose | repair | solve | quotient | needed
           | prepare | scopes | candidate | apply | observe
Head     ::= QName | Handle
Argument ::= QName | Handle | Enum | Degree | Ordinal
Handle   ::= "@" Id "/" Id | "$" Name ("." Name | "[" Index "]")*
Key      ::= Name | "bind." Name | "local." Name
Index    ::= "0" | [1-9][0-9]*
Degree   ::= Index
Ordinal  ::= Index
```

`local.` の Key は `assemble` にだけ指定できる。
QName、Id、Nameは[入力](inputs.md)と[Law](law.md)の定義に従う。
ただし固定引数名と公開された射影名の位置では、then、law、some等の当該固定語を受理する。
Lawの予約語と重なることを理由に、これらの位置の固定語を拒否しない。
字句の間のASCII空白を無視する。文字列literal、任意式、配列literal、入れ子の問いを受け付けない。
Enum・Degree・Ordinalは次節で指定した位置だけに置ける。DegreeはJSONのNatの上限以内とする。
Ordinalは candidate のindex専用の上限を持たない十進自然数であり、保存時はDecimalNat文字列とする。
各引数名は一回だけ指定する。指定の順序に意味を持たせない。

`@snapshot/subject`は現在のArchMapの原始subjectを指す。
`$id.field`は同じrunの問いidの`outputs[field]`を指す。
その後の射影は[公開する意味上の射影](results.md#公開する意味上の射影)の閉じた表と、
Lawの結果型Tの構造射影に限る。List/Tupleの`[index]`は0始まりの成分を指す。
Set、Map、意味上の集合表はindexで選べない。原始dataはAtom 定義で宣言したconstructorの引数を
`[index]`で選ぶ。別constructorの位置を選べない。
生のnode ID、過去の出力path、JSON PointerをHandleとして受け付けない。
Handleを取る位置が空、または`.` / `[`から始まる問いには、シェルが`$id`を展開した可能性と、
`--ask 'n=needed($ok)'`のように単一引用符で囲む案内をmessageへ加える。
宣言名や固定語の位置、通常の未知宣言にはこの案内を加えない。
表外の欄はresult.jsonに表示・検査用として保持し、CLIからの射影は`usage`とする。
途中の欄にも同じ規則を適用し、表示用特解をVector全体として取り出す経路も許可しない。
解集合、類、写像等は型付き結果全体として渡し、その数学的な意味とownerを保つ。

`needed`だけは`$id`を受け取り、その問い全体の未決理由を読む。
その他の問いでは出力fieldまで指定する。後方参照を許し、依存循環は`cycle`。
問いの依存循環はCLI要求の不正としてexit64を返す。循環に属する各問いについて、
Issue.requestにそのIDを入れ、Law/ArchMapのlocationを付けない。
標準エラー出力のreceipt.issuesに各問いのcycleを返し、messageに循環する問いIDと依存辺を示す。
解決した依存グラフは内部のrequestsに保持する。意味計算前に停止し、結果ファイルは生成しない。
内部のnodes/answersも空とする。
同じ優先度の問いは`--ask`の順で評価する。出力answersは指定順にする。
存在しない問いID・公開されていない射影・宣言、静的に判明する範囲外index、引数不足、
静的な型不一致は`usage`。
公開された任意fieldが反証・未決のため生成されない場合は`dependency_blocked`と
元の理由を保持する。例えば反証されたmapの`$m.operation`を使う合成は、mapの反例を
残したまま未決となる。値を計算して初めて分かるindex・constructor・Optionの不適合は
projectionの`condition_failed`と、それに依存する問いの`dependency_blocked`を返す。
公開fieldが選択したvariantや省略規則では定義されない場合もprojectionの`condition_failed`とする。
例えば観測環境のEvaluation.environmentや、Lawを指定しないQuotient.descentの省略がこれに当たる。
異種のword/generatorsから選んだ参照等の型・ownerを静的に決められない場合は、要求される型を
制約として保持し、射影後に検査する。その不適合もprojectionの`condition_failed`として扱う。

宣言のparameterを束縛する引数は`bind.parameter=Handle`。
固定引数名と衝突しないparameterは`parameter=Handle`と略記できる。
短形と`bind.`形による同じparameterの二重指定は拒否する。
Handleの型を宣言のparameter型へ照合し、依存型のownerも検査する。

問いは既存の宣言・対象・結果と固定の選択肢を指す。
原始値、式、対応表、cover、係数環、候補域、仮定をCLIから追加しない。
問いを変えるためにLawへ解析手順を追加する必要はない。
選択した問いと解決済みの束縛を結果に保存する。計算の意味は現在の Atom 定義・ArchMap・Law から決まる。
結果では明示した選択と省略時の選択を区別する。mapのkind、diagnoseのdegree/sideの既定値も
解決して保持し、環境・Law族・変更の省略規則は結果の固定規則名で示す。
未束縛parameterは宣言型の全域で量化するという意味を保持し、計画によって値を選んで埋めない。
実際のLaw instance族、候補域、自由位置と固定位置は、それぞれの生成結果へ記録する。

## 3. 問い

表の`B`は宣言parameterへの上記束縛の有限族。`?`は省略可能であり実際の構文には書かない。
出力fieldの型・内容は[型付き結果](results.md)に従う。
buildの`on=@root`はownerを持たないentityの原始参照を要求する。
同じrootの型を持つ結果Handleも受け付ける。solve/repairはそのroot参照に加えてArchitectureも受け付け、
そのrootとoverridesを次の候補計算の基準とする。

| 問いの正確な形 | 選択と返すfield |
| --- | --- |
| `build(Reading,on=Handle)` | rootとreadingから対象と有限表示のobject algebraを生成する。`proposition:Proposition`、構成できた`object:Architecture`、成立時`algebra:ObjectAlgebra` |
| `assemble(View,on=Handle,along=View,B,local.<parameter>=Handle…)` | 局所rootと共有対から対象を構成する。`proposition:Proposition`、成立時`assembly:ModelAssembly`、`object:Architecture`、`algebra:ObjectAlgebra` |
| `assemble_map(View,from=Handle,to=Handle,B)` | 始終のModelAssemblyと担当別の原始correspondenceから全体写像を構成する。`proposition:Proposition`、作用構成時`candidate:MapCandidate`、configuration保存時`configuration_map:ConfigurationMap`、全条件成立時`map:ModelMapAssembly` |
| `evaluate(View,on=Handle?,B)` | viewの全parameterを束縛して評価する。onは結果のArchitectureを読む環境。`value:T`、`evaluation:Evaluation`。TはPathやそのcontainerを含むLawの返り型 |
| `check(Law,on=Handle?,B)` | Lawの選択instance族について、未束縛parameterと内部量化を保って成立を問う。onは結果のArchitectureを読む環境。`proposition:Proposition`、`evaluation:Evaluation` |
| `map(Correspondence,on=Handle,reading=Reading,to_reading=Reading?,kind=configuration\|object_algebra?)` | onはこのcorrespondenceの原始instance。readingは始域の読み、to_readingは終域の読み（既定はreadingと同じ）。kindの既定はconfiguration。`candidate:MapCandidate`、`proposition:Proposition`、configuration保存確認時だけ`operation:Operation`、選択kindの成立時`map:ConfigurationMap\|ObjectAlgebraMap` |
| `compose(Handle,then=Handle)` | 二つの成立済みOperation、二つのPath、または二つのConfigurationMapを指定順に合成する。`proposition:Proposition`、端点確認後`operation:Operation\|Path`、Operationの場合は`map:ConfigurationMap`。ConfigurationMap同士は`map:ConfigurationMap`を返す |
| `compare(Handle,to=Handle,kind=value\|word\|action\|relation\|diagnostics,along=Handle?)` | 下記の比較を行う。`comparison:Comparison`、`proposition:Proposition` |
| `localize(Handle,law=QName?,using=QName?,B)` | Architectureを局所化する。lawは選択Law、usingはchange。`system:LocalSystem`、`proposition:Proposition` |
| `diagnose(Handle,degree=Degree?,side=equation\|semantic?)` | LocalSystemのdegree（既定1）、side（既定equation）を診断する。`diagnostic:Diagnostic`。計算できた場合`space:Cohomology`、`class:Class`、`proposition:Proposition`をそれぞれ保持する |
| `solve(Law,using=Change,on=Handle,B)` | 許された変更でLawを満たす全候補を求める。`domain:CandidateSpace`、`solutions:SolutionSet`、`proposition:Proposition` |
| `repair(Law,using=Change,on=Handle,B)` | solveと同じ全解中の元Assignmentが一意な場合だけ修復対象を構成し元のLawへ再代入する。`domain:CandidateSpace`、`solutions:SolutionSet`、存在の`existence:Proposition`、構成条件の`proposition:Proposition`、構成成立時だけ`repair:Repair`、`object:Architecture` |
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
`map` の reading/to_reading は Law ファイルの reading を完全名で選ぶ。
それぞれの読みが correspondence の始域・終域の原始型を参照できることを要求する。
宣言の namespace や同じ語彙を使う他の reading から読みを推測しない。
省略した to_reading も解決済み arguments に origin=defaulted で保持する。
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
| value | 同じ原始型P、同じModule上のVector、または同じCandidateSpace上のAssignment | 値の等値。商では剰余類、Assignmentではsubjectごとの元change parameterの等値 |
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
Assignmentの比較は表示行の順によらずsubjectを対応させ、各元parameterの宣言型の等値を検査する。
CandidateSpaceの同一性は[Assignmentの規則](results.md#5-線形表示診断修復商)に従い、node番号や
計算の共有によらず、基準Architecture・change・束縛と候補域の生成条件で検査する。
異なるCandidateSpaceのAssignmentは`usage`。同じ候補域に属しても、Term等の値の等値を決める
算法がなければ`unsupported_algorithm`とし、構文表示の違いだけで不等としない。

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
中断で閉包を生成し終えなければ部分の圏・coverを保持して未決を返す。

`solve/repair`のonは変更するrootまたは既に導出したArchitecture、BはLawの束縛と残る全称instance族を指定する。
Architectureを指定した場合はそのoverrides適用後の値を変更前状態とし、以前の導出元も保持する。
changeの第一parameterと型・ownerの合う全entityをon内で列挙し、残るparameterの型の積を
各instanceの候補parameter域とする。残るparameterはLawのchange規則に従う参照を含まない値型である。
候補は同時更新を行い、on外の値と全原始観測を固定する。同じslotへの異なる同時更新は
構成条件の不成立。未知の観測値は候補parameterへ変えない。
domainは許された全候補、solutionsはLawを満たす部分集合である。
探索を打ち切った部分列挙を全解集合・空集合・不存在証明として返さない。
repairは[修復の一意性](computations.md#修復の一意性)に従い、全解中の元Assignmentが
ちょうど一つで、その値と更新後の対象が確定した場合だけ、元のLaw・許された変更への再代入を経て
repair/objectを生成する。異なる元parameter割当てを同じ更新後状態や同型によって同一視しない。
`existence`は同じSolutionSetのinhabited命題であり、solveのpropositionと同じ意味を持つ。
異なる二つの解Assignmentがあれば、その所属と不等により一意性を反証し、
repairの構成条件をrefuted、理由を`condition_failed`とする。全解集合とestablishedのexistenceを
保持し、repair/objectは生成しない。解が空の場合はexistenceもrefutedとなる。
修復単独の確定した非一意・不存在はcomplete/exit1だが、両者はexistenceと証拠で区別する。
一つへ絞る条件は、Lawの要求またはchangeのparameter/guardに明示する。
存在を確認しても一意性・具体値・再検査が未完了なら、確認済みのexistenceを保持し、
repairの構成条件はundeterminedとする。この場合もrepair/objectを返さない。
生成されないobjectを使う後続evaluateはundetermined、`dependency_blocked`と元の理由を保持する。
非一意repairとそのevaluateを同じrunに指定した場合、runはpartial/exit2となる。

`quotient`の定義域はonで指した集合そのもの。CandidateSpaceとSolutionSetを取り違えない。
Bはviewの全parameterを束縛し、各候補で更新された同じsubjectの値を読む。
law指定時はBのうちLawが宣言する同名parameterを同じ型で共有し、残るLawのparameterを
追加の`bind.`引数で束縛できる。残るLaw parameterは同じ適用規則で全称化する。
両宣言の同名parameterの型が異なる場合は`usage`。
指定Lawの型付き評価族が同じview値のfiber上で一定かを問う。
等式の評価族はinstance keyと左右の値対を保持し、成否Boolや零残差へ縮めない。
有限候補では、括弧とlet本体を通して等式の左右値を保持する。and・or・implies・not・ifは
通常評価の子式から必要な観測を構文順のOptionのタプルにする。
ifは条件と選択分岐を観測し、非選択分岐はNoneとする。and・impliesの左辺がfalse、
orの左辺がtrueなら右辺はNoneとする。条件が未知なら分岐の観測を確定しない。
通常評価が非選択分岐も読んだ場合、その値や欠測はこの観測に含めない。
Boolの原子式、等号以外の比較、名前付きview呼出しは戻り値を観測し、呼出し内部へ展開しない。
有限量化は通常評価器の有限列挙記録と本体の評価出現を照合し、binder値と本体の観測の対の集合を保持する。Law parameterのinstance keyは宣言順とする。
必要な観測値が不明なら評価族を確定しない。適用外はNone、適用されるfalseはSome(false)として区別する。
matchは型付き判別値と構文順のarm観測を保持し、選択armだけをSome、それ以外をNoneとする。
Bool判別式は上の論理式の観測規則に従い、判別式内の等式の左右値も保持する。
選択には通常評価と同じpattern照合を使い、選択armの本体出現とpattern束縛値の一致を確認する。
判別値のconstructorとpayload、pattern内の位置は型と元式から保持し、必要な判別値・束縛・本体観測が未知なら確定しない。
選択arm内の等式は左右値を保持する。名前付きview内のmatchは呼出しの戻り値を観測する。
対応する算法のない無限量化の評価族は未実装として返す。

有限域の商は全fiberを返す。整数アフィン域では実際の格子像、核、射影、降下写像を返す。
それ以外の対応する算法のない無限域は式と型を保持して未決を返す。

### 共通の有限修復問題を使う問い

`prepare` は、同じ Law・変更・基準対象を複数の範囲で読むための `RepairProblem` を生成する。
三入力の役割は保ち、Law の作者が許す変更と局所の読取りを記述する。
核がその依存から部品の許容関係と元 parameter への復元を構成する。

| 問いの正確な形 | 選択と返すfield |
| --- | --- |
| `prepare(Law,using=Change,on=Handle,internal=Handle?,inputs=View?,B)` | `on` と B は従来の solve と同じ。`internal` は change の第1parameterと同じ entity 型の有限 Set を指す。省略時は空集合。`problem:RepairProblem`、`proposition:Proposition` |
| `solve(Handle,within=Handle,mode=existence\|solutions?)` | 第1引数は RepairProblem、within は変更を解禁する entity の有限 Set または同じ問題の ChangeRange。mode の既定は solutions。`proposition:Proposition`、solutions モードでは `solutions:SolutionSet`。双方で `range:ChangeRange` |
| `scopes(Handle)` | RepairProblem の有限な変更単位について包含極小の修復可能範囲を全て求める。`ranges:List<ChangeRange>`、完全性の `proposition:Proposition` |
| `candidate(Handle,index=Ordinal)` | 完全な有限または整数アフィン SolutionSet の要求した一候補を元座標へ復元する。`assignment:Assignment`、所属の `proposition:Proposition` |
| `apply(Handle,in=Handle)` | 第1引数は利用者が明示選択した Assignment、in は同じ候補域の SolutionSet。所属と再代入を検査する。`proposition:Proposition`、成立時だけ `selection:Selection`、`object:Architecture` |

新しい行にも、表外の固定引数を拒否する規則を適用する。RepairProblem を指す solve には
using・on・B を重ねず、prepare で固定した問題を使う。Law を指す従来の solve は従来通りである。
internal / within の Set は、既存の view を evaluate して得た型付き値などを指す。
原始値、集合literal、局所関係、係数、完成した全体解を CLI へ入力する経路を追加しない。

変更単位は、prepare が生成した change の各 entity instance とする。同じ instance の更新先は
一単位で解禁する。internal は常時変更できる instance、残りが範囲の変更単位である。
Set の要素は基準対象内の該当 instance に属さなければならず、within の Set は変更単位の部分集合とする。
within に ChangeRange を指定した場合は同じ RepairProblem の enabled を使う。別の問題の範囲は
condition_failed とする。scopes の完全な ranges は enabled のsubject参照の辞書順に並べた
型付き List で返し、利用者は `$r.ranges[0]` のように明示選択して solve へ直接渡せる。
List の順序は選択のための表示であり、ChangeRange の同一性は問題と enabled の集合で決まる。
未完了時に得た範囲は partial の表示として残し、完全な ranges の値として消費させない。
型不一致は usage、値を計算して判明する所属違反は condition_failed。
internal の観測値が未確定なら空集合と見なさず未決とする。
範囲外では、parameter を零にする代わりに更新先を基準 Architecture の値へ固定する。
同じ不変な RepairProblem を各 solve / scopes が参照する。

candidate の index は、完全な全解表示から選ぶための0始まりの明示指定である。
任意精度の Ordinal を使い、JSON Nat の上限を超える番号も指定・保存できる。
有限型では元 subject の参照順、各元 parameter の宣言順、値の標準順に従う辞書式順序を用いる。
Bool は false, true、有限和は constructor 宣言順、積は成分順、Fp は0からp−1とし、
Tuple は成分の辞書順、Option は none を先にして要素の順に従う。
Set は要素型の有限列挙順に所属を並べ、その最初の要素を最下位bitとする所属bit列の整数順とする。同じ元 Assignment の重複表示は一つとする。
整数アフィンでは、全解の表示用原点と元parameter座標の整数核の順序を使う。
核の自由係数がd個あるとき、indexのbit位置jを係数j mod dのbit位置floor(j/d)へ分配する。
各非負整数nは、偶数なら−n/2、奇数なら(n+1)/2へ戻す。この対応はZのd乗を一度ずつ覆う。
係数を元座標の全核へ作用させ原点を加え、内部の自由係数も含む元Assignmentを復元する。
d=0の非空全解にはindex=0だけが属し、空解にはどのindexも属さない。
index=0でも表示用原点を無検査で採用せず、所属・更新式・元Lawへの再代入を行う。
index は候補の恒久的な identity ではなく、この完全な解集合に対する選択要求である。
表示行や表示用特解を自動採用しない。範囲外 index は condition_failed。
一候補を取得するために全候補の Architecture や全量 JSON を作らない。
完全な整数アフィン以外の非有限全解表示と未完了の探索にこの操作を適用した場合は、前者を unsupported_algorithm、
後者を dependency_blocked とする。取得した Assignment を apply に渡すことで採用を明示する。

apply は元の解集合、候補域、選んだ元 Assignment、生成した対象を Selection で結びつける。
別の候補を選び直せるよう元の全解表示を保ち、一意性の検査を要求しない。
従来の repair は元 Assignment 全体の一意性を引き続き要求する。
apply の object は check、evaluate、localize、次の prepare / solve / repair がそのまま消費する。
構造保存の写像は、選択だけを根拠に生成せず、既存の保存条件も検査した場合に限る。

例えば、同じ root 内の Bool 値を持つ六つの entity を x,y,z,a,b,c とし、既存 view の戻り値が
`$i.value={a,b,c}`、`$xy.value={x,y}`、`$xyz.value={x,y,z}` に相当するとき、
次の参照の連鎖で同じ問題を使う。集合の記法は説明用であり CLI literal ではない。

```text
p=prepare(Example.valid,using=Example.replace,on=@v/root,internal=$i.value)
small=solve($p.problem,within=$xy.value,mode=existence)
full=solve($p.problem,within=$xyz.value)
r=scopes($p.problem)
minimal=solve($p.problem,within=$r.ranges[0])
c=candidate($minimal.solutions,index=0)
a=apply($c.assignment,in=$minimal.solutions)
ok=check(Example.valid,on=$a.object)
next=localize($a.object,law=Example.valid,using=Example.replace)
```

保存時は解決した問い、範囲、元 Assignment と生成した対象への対応を保存する。
所属・再代入の内部証拠は結果形式 §1 の保存射影に従い、再読込み時に現在入力から検査する。
再利用では現在の三入力と基準対象から導出を検査する。candidate の index だけで過去の選択を
別の Assignment に貼り替えず、保存した元 Assignment と現在の復元結果の一致も確認する。
不一致ならその保存選択を再利用せず、現在入力からの新規評価として区別する。
中断と依存先の未決は §6 の規則に従い、確認済みの先行回答を残す。

### 修復の判定と元割当てに必要な観測

有限の入力候補族を同じ修復問題へ接続する場合、prepare に `inputs=View` を指定する。
View の parameter は prepare の明示した B と同名・同型の束縛で全て与える。
この view が読む原始位置について、現在の既知値は固定し、未観測の有限型の値を合法な全補完で動かす。
型・owner・基準root・changeのinstance族は固定し、その適合を確認する。
入力viewに含まれない未観測や、有限に補完できない位置を勝手に補わない。
inputs を省略した prepare と従来の needed の意味は変えない。

| 問いの正確な形 | 選択と返すfield |
| --- | --- |
| `prepare(Law,using=Change,on=Handle,internal=Handle?,inputs=View?,B)` | inputs は原始位置の読取りを記述する view の完全名。`problem:RepairProblem`、`proposition:Proposition` |
| `observe(View,on=Handle,within=Handle,output=decision\|assignment,B)` | on は有限または適用条件を満たす整数入力族を持つ RepairProblem。View の B を完全束縛する。within は同じ問題の範囲。`plan:RepairObservation`、十分性の `proposition:Proposition`。追加読取り不要で共通の全解を確定した場合だけ `solutions:SolutionSet` |
| `observe(Handle,on=Handle,within=Handle,output=decision\|assignment)` | 第1引数は同じ問題から生成した RepairObservation。その requirements を許可する読取り集合として再評価する。B は指定しない |

observe の view は、追加で読んでよい原始位置を記述する。核は入力候補族の各点で通常のview評価が
読む原始位置を集める。比較する観測は view の集約値ではなく、その原始位置の型付き値である。
Lawの作者がviewを定め、原始値の意味の確認と実際の観測は利用者・製品SKILLが行う。
既知の値だけで区別できる候補は先に区別し、追加読取りには数えない。

output=decision は各観測群で修復の可否が一定か、output=assignment は各群が全て修復不能、
または群全体で有効な同じ元Assignmentを返せるかを調べる。二候補ずつの共通解では代用しない。
十分なら許可集合から不要な原始位置を除き、包含極小の一集合を返す。最少件数や全極小一覧は求めない。
許可集合全体でも不足する場合は proposition を refuted とし、不足する候補対または候補群を返す。
これは修復自体が不可能という結論ではない。未完了の場合は十分・不十分を確定しない。

入力viewと追加読取りview、範囲、目的を固定したまま ArchMap に観測値を追加して同じ問いを実行すると、
現在の既知値と整合する入力候補へ絞り、requirements を更新する。古い成功表示や仮の補完値を
実際の観測へ貼り替えない。保存は現在の三入力から再検査し、変更した値に対しては再導出する。
追加読取りが不要になった assignment の solutions は candidate / apply が直接消費する。
Assignment の十分性は元parameterの構成についての結果であり、適用後の全原始値が既知という意味ではない。
apply は現在入力の通常の所属・更新式・元Law検査を行い、別途未決が残れば object を生成しない。

入力候補族付き問題の solve / scopes は、現在と整合する全入力候補で共通に有効な元Assignmentを求める。
各入力ごとの修復可否の一定性は observe の output=decision で求め、この共通解の存在と区別する。
同じ原始位置は全候補・全部品で同じ座標とし、部品ごとに別の未知を作らない。
空の合法な入力候補族を空虚な十分性へ変換せず condition_failed とする。
型・束縛の不一致は usage、別問題の範囲やplanは condition_failed、非有限の補完は unsupported_algorithm、
その他の観測不足は元の missing、依存先の未完了は dependency_blocked とする。
整数changeのinputsは計算仕様の整数アフィン適用条件を使う。未観測Zを全整数域として扱い、
既知値を固定する。更新・guardとinstance族は入力未知に依存させず、Law等式と範囲の基準値に
未知を保つ。適用条件外はunsupported_algorithmであり、整数解なしへ読み替えない。

同梱 [共通構造の一周](../../../tools/archsig_v0.6.0/skills/archsig-observe/references/common-loop.md)は、
有限・整数の観測計画、範囲比較、元割当ての明示選択、適用・検査、再観測と保存の再検査を実行する。
操作・型・判定の仕様は本節に従う。

### 有限の局所モデルを組み立てる問い

`assemble(View,on=Handle,along=View,B,local.<parameter>=Handle…)` は、担当別の root の有限集合を返す View と、
共有する個体の対を返す along の View を同じ明示束縛 B で評価する。
両 View は同じ reading に属し、parameter の名前・型を共有する。全 parameter を束縛する。
第1 View の戻り型は owner を持たない同じ entity 型の `Set<Root>` とする。
along の戻り型は `List<(T,T)>`、またはそれらの有限 Tuple とし、T はその root 型の
owned entity / arrow の参照型とする。`Unit` と値 `unit` は共有個体なしを表す。
対は原始個体の明示対応であり、構成済みの全体対象や保存証拠を入力しない。

on は同じ snapshot・root 型の原始参照で、組立て後の root の identity と既知 field を与える。
担当 root は空でない有限集合とし、on と異なる。on には既存の owned 個体がないことを要求する。
初段の適用族は、同じ snapshot・定義環境・reading で、各局所 root とその所属個体、および on の field がすべて既知である族とする。
関数値 Term を含む field はこの算法の対象外とする。入力の通常の型・参照検査は先に行う。

任意の `local.<parameter>=$applyId.object` で、担当 root に対して選んだ修復済みの局所状態を使う。
parameter は第1 View の root 型引数で、束縛値と `apply` の元 root、snapshot、reading、所属域を照合する。
異なる引数で同じ担当を二重選択した場合や別担当の `apply` を選んだ場合は整合失敗になる。
同じ Key を二度書くと不正な問いになる。指定のない担当は原始状態を読む。
局所の全候補を自動選択する処理は行わず、利用者が各 `candidate` と `apply` を明示する。

返す field は `proposition:Proposition`、成立時 `assembly:ModelAssembly`、
`object:Architecture`、`algebra:ObjectAlgebra` とする。
assembly から局所ごとの包含と再制限の対応を辿れる。構成した object は evaluate / check /
localize と次の変更の on に渡せる。初段の組立ては対象と生成操作を構成し、担当別の新旧写像の
組立ては別の構成とする。局所で確認した Law の成立を全体の成立へ昇格させず、元の Law を全体で検査する。
組立てViewの元式と、対象に付随するLawの元式・parameter・束縛は分けて保持する。
Lawの追加・修正時も、その元出現の下で既存の数値族・有限読取りの算法を使う。
構成で輸送した既知の参照を族・集計のownerへ渡す場合も、元fieldの支持と輸送の由来を保つ。
有限計算の元入力への候補代入は、所属・Map全域性の検査では元の参照値を保ち、
選択対象の式・所属集合を読むときに同じ構成の参照輸送を使う。
選択対象への明示変更として渡された値は、この元入力候補の輸送と区別する。
既存算法で成立・反証を計算できる式を、組立てViewと異なる宣言であることだけで未対応化しない。

未観測 field はその原始位置を持つ `missing_observation`、適用族外は原式と束縛を持つ
`unsupported_algorithm` とする。共有対応が局所の異なる個体を潰す、型・field 値・端点が
整合しない、または生成操作の保存を満たさない場合は `condition_failed` を返す。
field 値の不一致は参照輸送後の実際の二値と元の field 位置を証拠にする。
それ以外の不整合は、評価した局所集合・明示対応と不整合な原始位置へ戻す。
失敗した組立てから完成した object / algebra を返さない。中断時は先行する確認済み回答を保持し、
未完了の組立てを成立させない。

### 局所の新旧対応から全体写像を組み立てる問い

`assemble_map(View,from=Handle,to=Handle,B)` のfrom/toは、同じsnapshot・定義環境・readingの
`ModelAssembly` を指す。Viewは原始correspondence参照の有限集合 `Set<C>` を返し、
全parameterを明示束縛Bで与える。Cの始終root型は両組立てのroot型と一致し、
owned型とfield位置の対応は同じ元宣言を結ぶものとする。
異なる型・field位置へのalignは、この初段算法の適用族外として元correspondenceを示す。Viewも同じreadingに属する。
各始域fragmentにcorrespondenceをちょうど一件対応させ、その終域は終域側のfragmentのいずれかとする。
同じ終域fragmentへ複数の担当が写ってよい。終域全体への全射は構成条件にしない。

局所対応の型・値・参照・configuration保存、重なりの像の一致、再制限の可換性、
全体生成操作の保存とLaw移送を核が検査する。Law移送はrequired status・適用とBool読取りを
元の出現と束縛で比較する。原始状態同士では、残る parameter の全域を構成できる有限 Law 族を扱う。
修復済み状態を含む場合は、束縛済みの Law を実際の更新値で読む。未束縛の族の未対応理由は
元 Law 宣言の位置と残る parameter の型を示す。
Configuration保存を確認した時点でconfiguration_mapを保持し、操作/Law保存も確認した場合だけ
ModelMapAssemblyを返す。確認済みの構造ごとにfieldを区別する。
欠測は元位置付きmissing_observation、その他の適用族外は元位置付きunsupported_algorithm、
共有像・保存・可換性の不一致は実像と元位置付きcondition_failedとする。
複数の保存条件のうち一つでも実際の反証を得た場合は、別条件が未対応・未決でも全体をrefutedとし、
その反例と失敗条件を保持する。未対応条件の理由も消さず、反証がなく確認を終えられない場合はundeterminedとする。
中断時は先行回答を保持する。
保存候補は現在の三入力と元Requestから再検査する。

`compose($f.configuration_map,then=$g.configuration_map)` はConfigurationMapの通常の総作用合成を返す。
中間のArchitectureはrootの綴りに加え、構成済みの所属域・参照輸送・値・readingが一致することを検査する。
ConfigurationMapの合成出力はmap/candidate/propositionであり、元の局所対応と始終対象を保持する。
`compare($direct.configuration_map,to=$composed.map,kind=action)` は同じ始終対象の全U作用を比較する。
不一致は最初の元位置と両像を返す。Operation同士の名前付き語の比較と、ConfigurationMapの作用比較は
それぞれの型で指定する。ConfigurationMapのkind=wordはusageとする。
ModelMapAssembly.source/targetとConfigurationMap.candidate.source/targetは構成済みArchitectureを指し、
evaluate/check/localize/後続変更のHandleとして使える。

## 4. 例

```text
archsig run --atom-definition reservations.atoms.json --law reservations.law --archmap reservations.archmap.json \
  --ask 'a=build(Reservations,on=@v/B)' \
  --ask 'v=evaluate(Reservations.holdings,s=@v/p)' \
  --ask 'c=check(Reservations.retained,m=@v/m)' \
  --ask 's=solve(Reservations.retained,using=Reservations.rebalance,on=@v/B,m=@v/m)' \
  --ask 'r=repair(Reservations.retained,using=Reservations.rebalance,on=@v/B,m=@v/m)' \
  --ask 'n=needed($r)' --out result
```

次の問いは同じ定義・A・Lを再入力し、必要な`--ask`と依存する問いを指定して実行する。
`--reuse`を付けた場合も同じ再検査を行う。結果だけを意味入力として受け取るコマンドはない。

## 5. ファイル操作と出力

入力はローカルの通常ファイル。pathは呼出しcwd基準とする。
symlinkを読込み開始時に解決し、開始時に読み切ったbyte列だけを計算と同梱に使う。
HTTP、ZIP、source uriや定義・Law参照からの追加読込みを行わない。
再利用directoryは通常のdirectoryと下記固定pathの通常ファイルだけを読み、リンク先の追加探索をしない。

`--out`を指定した場合、outは存在しないpath、親は既存directoryを要求する。満たさない場合は`usage`とし、出力を作らない。
check/runの引数では、既知flagは次の語を値として取り、未知flagは値を取らないものとして読む。
不正なコマンド引数は標準エラー出力へusageを返し、入力を読まず、directory・result.json・入力コピーを作らない。
出力先の指定を回復して失敗記録を保存する処理は行わない。
入力が読めない、または通常ファイルでない場合は`io`(operation=read)とし、検査を始めない。
入力の読込不能・構文や型の不正・非対応版、問いの不正、内部障害も標準エラー出力へ具体的なエラーを返す。
これらの失敗だけを記録するファイルは作らず、check/runで扱いを分けない。
check/runとも検査・計算中のSIGINT/SIGTERMを確認したら処理を止め、未完成の検査結果を公開しない。

明示された`--out`へ保存するcheckの検査成功結果、およびrunの値・命題・反例・診断・解集合は依頼された成果物である。
runの保存形式は[型付き結果](results.md#1-resultjson)の値の参照グラフであり、導出・証明は核の検査に保持する。
数学的な反証・未決は、この計算結果に含める。signal・内部障害で処理が止まっても、
入力検査と要求解決を終えて既に得た検査済みの計算結果は保持し、未着手の問いへ停止理由を付ける。
入力検査・要求解決中の停止や、計算結果が一つも得られていない停止はCLI通知のみとする。
評価で `unsupported_algorithm` が確定した問いは未決とし、その出力を必要とする問いに
`dependency_blocked` を付ける。独立した問いの評価は続く。全体の状態と終了コードは §6 の優先順で決まる。
生成した Answer の再検証で不整合や検証手順の未対応が検出された場合は、内部障害として停止し、
検証済みの結果を保持する。
checkが検査を完了した後に捕捉signalを反映する場合は、確認済みの検査結果を成果物として保持する。
保持する結果のための入力コピーと由来も同梱する。
同じ親に一時directoryを作り、入力コピーと結果を書きflushした後、既存pathを置換しない
renameで最終directoryを作る。競合してoutが作られた場合も上書きしない。
出力に失敗した場合は、今回の実行が作成した未完成の一時directoryを片付ける。
既存のpathや、有効な成果物のあるdirectoryは削除しない。削除できなかった一時directoryのpathと原因は、標準エラー出力のreceipt.issuesで知らせる。
finalizeの状態確定と、その後の配送障害は次節に従う。

```text
NEW_DIRECTORY/
  inputs/definitions/0.json  第1の定義ファイルの開始時byte列
  inputs/definitions/1.json  第2以降が指定された場合（同様に連番）
  inputs/law.law          開始時のLawのbyte列
  inputs/archmap.json     指定され読めた場合のArchMapのbyte列
  result.json            唯一の機械向け結果
```

保存するresult.jsonは[型付き結果](results.md)に従う。runで`--out`を省略した場合は、同じ検査済み計算から直接、短い回答を返す。
表示用の要約を後続計算の入力へ使わず、全量が必要な値は明示保存した結果から読む。
宣言の解決説明と導出は、この結果を読むための出力であり、新しいLawや実行計画の入力形式にしない。
元の宣言は同梱した Atom 定義と Law の byte 列と Location で保持し、説明用の展開によって語彙manifestを変更しない。
stdoutは計算成果を完了時に一行だけ出力する。`run`の計算成果は保存の有無によらず次の形式とする。

```text
{format:"archsig.summary/1",status:RunStatus,exit_code:Nat,answers:SummaryAnswer[],result?:String,issues?:Issue[],warnings?:Issue[]}
SummaryAnswer = {id:String,question:QuestionKind,status:Decision,outputs:Object,
                 applicability?:String,existence?:Decision,uniqueness?:Decision,reasons?:Issue[],
                 counterexamples_total?:Nat,counterexamples?:Object[]}
```

outputsは直接読める型と値を示す。構造値の選択された欄を深さ2まで表示し、集合等は件数を示す。
反例は3件、各反例の束縛と事実も各3件まで表示し、counterexamples_totalは表示前の全反例数を示す。
参照を含まないValue型の値、および反例の束縛名・事実の文字列が256 byteを超える場合はbyte数を示す。
summaryの理由と通知はIssueからdependenciesと導出参照を除いた形とする。
solveで具体的な状態値が未確定でも存在判断を完了した場合は、回答のstatusと別にexistenceを示す。要約は候補域や解集合を縮小せず、内部の全量計算と後続参照を維持する。
`run`で保存した場合はsummaryへresult pathを付加し、回答と再利用拒否のwarningsをそのまま返す。
保存に失敗した場合も、計算済みのsummaryとwarningsをstdoutへ返し、result pathを付加しない。
このsummaryのstatus/exit_codeは計算状態を保ち、保存失敗はstderrのerror/74 receiptとプロセス終了コード74で知らせる。
`--out`付きrunをパスのみのreceiptとして読む従来の呼出し側は、`archsig.summary/1`の
`result`欄を読むよう更新する。実行失敗をstdoutから読む呼出し側はstderrを読むよう更新する。
保存形式`archsig.result/4`と数学的な判断規則は同じである。
`check`の検査状態、および実行失敗の通知は次のreceiptを使う。

```text
{"format":"archsig.receipt/1","status":RunStatus,"exit_code":Nat,"result":String?,"issues":Issue[]?}
```

resultは作成したresult.jsonの呼出しcwdからのpath。作成できなければ欄を省略する。
実行失敗・中断の通知には非空のissuesを必須とする。Issueの型・並びは[型付き結果](results.md)を使う。
messageは英語で、原因と問題の引数または入力をその場で理解できる説明を入れる。入力者が指定した名前・文字列はそのまま保持する。
位置を特定できる入力エラーはlocationに元入力のIDとpointer/spanを、usageはdetails.argumentを保持する。
入力IDはlaw、archmap、指定順のdefinition0、definition1、…であり、ファイルコピーがなくてもCLIの指定と対応する。
成果物のない通知のIssueはノード参照を持たず、dependencies/missingを空とする。
成果物を伴う通知のノード参照は、そのresult.jsonを指す。正常な完了ではissuesを省略する。
実行失敗のreceiptはstderrへ出し、正常な検査状態・数学的な反証・未決の回答はstdoutへ出す。
計算中の内部障害・中断までに検査済み回答がある場合はstdoutのsummaryを保持し、停止の診断をstderrのreceiptへ出す。
進捗表示は追加しない。shell pipeline全体の終了状態はshellの`pipefail`設定等に従う。
プログラムはreceiptのstatus/exit_codeとissuesのcode、または保存されたresultのcodeで分岐する。

例えば、出力先を省略したcheckが成功するとファイルを作らず、次の一行と終了コード0を返す。

```json
{"format":"archsig.receipt/1","status":"complete","exit_code":0}
```
`version`と`--version`は次の一行を出し0で終了する。

```json
{"product":"archsig","version":"0.6.0","semantics":["archsig/0.6.0"]}
```

## 6. 状態・終了コード・中断

RunStatusとexit codeは、下記のfinalize開始時の確定までに得た状態に対し、上から最初に当たる行で決まる。

| 条件 | status | exit |
| --- | --- | --- |
| 捕捉したSIGINT / SIGTERM | interrupted | 130 / 143 |
| io / internal | error | 74 / 70 |
| usageまたは問いの依存循環 | invalid | 64 |
| 不正入力 | invalid | 65 |
| 未対応format/semantics | unsupported | 69 |
| 一つ以上の問いが未決 | partial | 2 |
| 全問いが確定し一つ以上反証 | complete | 1 |
| 全問いが確定し反証なし、またはcheck成功 | complete | 0 |

io/internal併発時はio、複数signalは最初に捕捉したsignalを使う。
finalize開始時にSIGINT/SIGTERMをblockし、受信済み・pendingのsignalを一度だけ判断へ含めて
status/exit_codeを確定する。両方がpendingで受信順を取得できない場合はSIGINTを先とする。
この状態は保存する計算結果の状態である。成果物のwrite/flush/renameの間は両signalをblockし、
原子的な公開または一時directoryの片付けを終えた後、stdout/stderrへの配送前にblockを解除する。
配送中または保存中に新しく届いてpendingになったSIGINT/SIGTERMは配送を中断し130/143で終了する。
既に中断を捕捉して計算状態を確定している場合は、その最初のsignalの終了コードを保つ。
保存済みresultのstatus/exit_codeは変更しない。配送中断時には完全なJSON通知を保証しない。
公開前のwrite/flush/rename失敗は最終resultを公開せず、result欄のないerror/74 receiptにioのissuesを入れ、
stderrへ出して74で終了する。runの計算済みsummaryはstdoutへ返し、回答の成立・反証・未決とwarningsを保持する。
入力検査や問い解決など計算前の失敗ではsummaryを生成しない。
stdoutのwrite/flush失敗は計算状態と分けて扱う。BrokenPipe（後段による早期終了を含む）は追加通知なしで141、
それ以外はerror/74の機械可読receiptをstderrへ通知し74で終了する。保存済みresultは保持し、通知にpathを付ける。
stderr自体の配送失敗も非成功終了とし、BrokenPipeは141、その他は74とする。通知の再送は行わない。
保存結果内のexit_codeは計算状態、実プロセスの終了コードは配送成否・配送中断も含む。
全問いが算法非対応でもpartialである。確定反例は有効な結果であり、他の問いが未決でも保持する。
不正入力・未対応版では数学計算を始めず、標準エラー出力のissuesで理由を伝え、結果ファイルを作らない。
保存する結果のrequestsは、問いの選択を解決できた場合だけ埋める。
捕捉できないSIGKILL・停電で最終directoryが存在しなければ出力未確定とする。
最終directoryと有効なresultが存在すれば計算結果は確定済みであり、receiptの欠落だけを配送未完了と読む。
この場合はプロセスの正常終了を確認したことにはせず、確定済みのstatus/exit_codeを事後に変更しない。

時間とメモリの上限はCLIに持たない。実行時間を区切る場合は、呼び出し側がSIGINT/SIGTERMを送る。
signalは検査・評価(計画の生成、再利用候補の検索と再検査を含む)の式評価と有限反復一回の前後で確かめる。
入力読込中に受けたsignalは、その後の最初の検査で扱う。signalを捕捉した後は新しい導出を始めず、検査済みの結果だけをfinalizeする。
未着手の問いにも停止理由を付け、暫定値を確定値として出さない。

## 7. 版、正規化、再利用

検査順はUTF-8・構文、format/semantics、対応版のschema、宣言・型・参照の順。
未知版の新しい欄を、先に未知欄エラーにしない。
Atom 定義は ArchMap と同じ JSON 検査順とする。
LawではUTF-8を確かめた後にheaderのformat/semanticsを読み、残りの字句と宣言の文法はその後に検査する。
同じsemanticsの下で判断規則を変更しない。

canonical JSONは[入力仕様](inputs.md#4-語彙-binding)に従う。
意味上の集合表は完全名/IDまたはcanonical値のUTF-8 byte辞書順へ並べる。
他のarray順、原始ID、Text、provenanceは保持する。
bytes_digestは読んだbyte列、model_digest(A)は集合表を正規化したArchMapのcanonical JSONのSHA-256。
model_digest(L)は[Lawの字句列正規化](law.md#1-ファイル名前再利用)に従う。
定義ファイルの model_digest は [Atom 定義](definitions.md#3-依存参照digest)に従う。
語彙 digest・定義ファイル digest・Law 全体の digest を区別する。
同じ意味へ解決される表記でもmodel_digest(L)は異なり得る。digestを意味同値の判定に用いない。
計画、内部表現をこれらの入力digestへ含めない。

`--reuse`は以前の出力directory一つを受け取り、現在の定義・A・Lを常に必要とする。
候補の版・型・DAGを検査し、現在の定義・原始根・Law式・問いの束縛へ照合して各推論を再検査する。
digest一致は候補の検索だけに用い、成立証拠の代わりにしない。
全て現在入力から再計算してよい。候補の値・束縛・由来を現在の計算へ取り込まず、
再計算した結果との照合で候補を検査する。不正候補はrunの`warnings`へ理由と`--reuse`を記録し、
通常評価を続ける。警告は候補を拒否した場合だけ出し、再利用件数は出力しない。
候補の拒否だけでは計算結果の状態・終了コードを変えない。再検査中の中断は通常のsignal規則に従う。
以前と同じ計算計画を使うことは要求せず、現在の式・原始根・束縛・条件に対する導出を検査する。
観測計画の各要求では、検査済みの同じ導出への重複参照を一つにまとめて照合する。
共通の計算結果を再利用・共有しても、Lawの各出現と現在のAtomの支持・由来を保持する。
Repairを再利用する場合も、現在の候補域・束縛・基準Architectureのoverridesを照合し、
全解中の元Assignmentの一意性、具体値の確定、所属と再代入を再検査する。
一解の所属だけ、更新後状態の一意性だけ、表示用特解だけではRepairを再利用しない。
一意性の反証を再利用する場合も、具体的な二解の所属・不等、または補完表・同次核による
[証拠](results.md#6-証拠と理由)を現在の全解に対して再検査し、存在判定と混同しない。
completion_fibersのrequestは現在の解決済みの問いへ対応付け、ID一致だけで採用せず、
根・Law・束縛・overridesと各補完の候補族・全解を再検査する。
現在のLawで解を絞った場合は、その条件で全解と一意性を計算し直す。
公開された射影は、その規則、現在の意味対象、型・ownerと射影値を照合し、後続の推論を再検査する。
現在の入力から導けない結論を旧結果から増やさない。変わったsourceへ古い由来を貼り直さない。
数学的な値と条件は、同じ完全入力・解決済みの問いに対して計画によらず決定的とする。
解集合・類・写像は、基底や特解等の表示を変えた場合も、元の意味対象に沿う同じ値を表す。
時間・メモリ・node番号・表示基底・同じ命題の証明証人の選択は意味的一致の対象から除く。
後続の問いが読むRepairのAssignmentとobjectは、入力と問いで定まる全解の一意性に基づく。
JSONの正規化・列挙順・表示用特解の選択を、解の選好や一意性の根拠にしない。

内部計画の自由とその検査は[意味を保つ計算計画](computations.md#10-意味を保つ計算計画)に従う。
中断までにどこまで完了するかは計画や再利用の有無で変わり得るが、確定した値と条件をそのscopeの下で保つ。

### メモリ内の再観測

Rustの `observed::reevaluate_observed(previous,prepared,control)` は、同じプロセスで生成した
検査済みの `ObservedEvaluation` と、現在の三入力・問いを通常検査した `PreparedObserved` を受け取る。
`reevaluate_observed_bytes(previous,sources,asks,control)` は現在の三入力の検査から行う。
返すのは現在入力の新しいObservedEvaluationであり、previousは変更しない。
通常のevaluateと同じ回答・条件・元Assignmentを求め、現在のsource・支持・由来を生成する。

有限修復では、不変なLaw局所関係について、生成条件・有限域・更新条件と依存位置の現在値を確認し、
前回の関係行の所有を共有して生成を省ける。変更した位置に依存する関係は生成し直す。
再利用できる部分がなければ通常生成し、現在の不正入力は前回結果の有無にかかわらず拒否する。
前回のgraphや成功表示を現在の導出として採用せず、候補所属・適用・元Lawの再代入は現在対象で検査する。

これはメモリ内のnative結果に対する計算の再利用である。CLIの `--reuse` が読む保存JSONは上記の
非信頼な再検査候補のままであり、この入口へ変換しない。再利用の件数・内部関係・計数を通常出力へ追加しない。
中断時の確定済み回答・未完成値の扱いは通常評価と同じ規則に従う。

整数アフィンのsolve/repairでは、現在入力から得た係数行列と列数が同じ場合に
整数分解と核を引き継げる。右辺だけが変わった場合も現在の整除条件・特解と
元parameterへの復元を求め、適用対象・元Lawの検査と由来は現在入力から生成する。
行列や適用条件が変わる場合は現在の生成・検査へ戻し、旧成功表示を採用しない。

### 局所組立てと追加観測の対応

Rust の `observed::assembly_reobservation::reevaluate_assembly` は前回の native 結果、
現在の検査済み三入力と要求、明示した `AssemblyAlignment` を受け取る。対応には始終 snapshot、
同じ reading、元組立ての要求 ID、主体対、前回 candidate と現在 solve の ID を指定する。
主体対は観測側で呼出し側が与える同一性の仮定であり、以下の継続判定はこの対応に従う。
同じ順序の定義と Law を使い、前後で型・既知の owner・原始参照の明示束縛を検査する。
View の実評価から担当集合と共有の同値関係を照合する。共有対は別担当の同じ型の個体を結び、
共有の同値類には各担当から高々一個体が属する。有効な共有対の順序・向きは同値関係を変えない。
対象 root・担当 root・所属個体・共有対の端点はそれぞれの評価 snapshot に属する。通常 field の外部参照は元の参照を保ち、別 snapshot を指せる。
共有対の読取りに必要な欠測、適用族外、対応そのものの不一致は区別して返す。
組立ての前回未観測 slot は、現在の同じ field と型の Atom に結ぶ。現在も未観測なら Atom の参照は空になる。

現在の要求は既存の native 再観測で実行する。有限修復の前回 Assignment は元個体を明示対応で運び、
有限 `prepare` で扱う parameter 値を現在の解集合で再検査する。保持・除外・判定不能を返す。
比較する `prepare` の引数は宣言と原始個体の直接参照に限る。
`assemble` ではこれらに加え、追跡する `local.*` の `apply.object` を受け取る。
局所 `apply` を指定する場合は一つの担当を追跡する。前回の適用要求は指定した前回候補とその候補を生成した `solve` の全解を参照する。
現在の適用と選択候補は、指定した現在 `solve` の全解を参照する。組立て成立時に実際の候補 ID を返す。
候補照合中に停止した場合も現在の確定済み回答を保持する。
現在の組立ては現在 snapshot のみで行い、以前の組立てや候補を現在の証拠へ転用しない。

## 8. 観測補助

`evidence` は観測側のArchMapと明示したローカルファイルを照合する。
`law-fibers` は観測側で読解・評価して列挙した値の等号を有限表上で比較する。
この二つの補助結果は `check` / `run` の三入力・Law評価・診断結果へ供給しない。
両コマンドはファイル保存、Python、追加設定を要求しない。入力は通常ファイルだけを読み、symlinkは解決する。

### evidence

`--archmap` は一つ、`--atom` は相異なる非空の `snapshot/atom` を一つ以上、
`--source` は相異なるsource IDと非空ファイルパスの `ID=FILE` を指定する。
パスに `=` を含む場合は最初の `=` だけを区切りとする。
対象のsource digestが一ファイルの全bytesを指す場合に使う。
JSON全体の重複key、sources/origins/snapshotsの重複ID、選択snapshot内の重複Atom IDを拒否する。
IDは非空文字列。選択したAtomから明示されたorigin・locations・sourceを辿り、必要な参照・bindingの欠落を拒否する。
使用するsourceについてファイル全体のUTF-8とSHA256を照合する。
spanは二つの非負整数による半開byte区間で、始点≦終点≦ファイル長、両端はUTF-8文字境界とする。
span省略時は全bytes。空区間を許す。値・位置・sourceメタデータを保持し、各locationへ `resolved_span` と `excerpt` を追加する。
Atomの `snapshot`、locationの `resolved_span` / `excerpt` は実際の選択・照合結果で置き換える。
Atom配列は選択順、origin/source配列は初出順で共有参照を一度だけ返す。
未選択Atomの参照・意味や全ArchMapのschemaは `check` と読解の対象であり、この補助は選択箇所を照合する。

出力は `atoms`、`origins`、`sources`、`verification` を持つJSON。
`verification` はローカルbytesと宣言digest/spanの一致を示し、revisionの真正性・観測の網羅性・意味・Law忠実性は読解側で確認する。
ローカルの `--source` パスは出力に追加しない。

### law-fibers

入力は次の五欄をちょうど持つJSON object。

```json
{"scope":"二つの候補モデルの保持条件", "sources":["a","b"], "laws":["preserves"],
 "q":{"a":"same","b":"same"}, "v":{"a":{"preserves":"yes"},"b":{"preserves":"no"}}}
```

`scope` は非空文字列、`sources` / `laws` は相異なる非空文字列の配列。
`q` / `v` のkeyはsourcesと一致し、各v行のkeyはlawsと一致する。
q/vの値は等号を保つと読解側で確認した非空文字列token。未確定値をtokenで代用しない。
余分な欄、欠落、重複key/name、非文字列値を拒否する。空のsources / lawsは許す。
完全列挙と値の忠実性は利用側の前提であり、CLIは与えられた表の全対を比較する。

出力は `scope`、`source_count`、`law_count`、`adequate_on_table`、`vacuous`、
`q_partition`、`joint_law_partition`、`counterexamples`。
同じq値の組でvのいずれかの列が異なると `left` / `right` / `laws` の反例を返す。
partitionはsourcesの初出順、反例はq群の初出順・群内のsources順、差分Lawはlaws順。
反例がなければ `descent` にq値→Law値objectを追加する。空族・空Lawは十分かつ `vacuous=true`。
これは表の等号から計算する指定Law値の保存であり、Law DSL評価や診断保存の証明へ読み替えない。

### 配送・終了コードと旧補助からの移行

結果は一行のUTF-8 JSONをstdoutへ、失敗は既存の `archsig.receipt/1` をstderrへ返す。
成功は0、有限表の反例は1。usageは64、入力不正は65、内部障害は70、I/Oは74、
SIGINT/SIGTERMは130/143、broken pipeは141。読み取り専用のため中断時の部分結果は保存しない。
`archsig help evidence` / `archsig help law-fibers` と各 `--help` / `-h` は入力を読まず0を返す。

旧Python補助の正常結果の欄と配列順を維持する。空白・object key順・Unicode escapeの綴りは固定しない。
Atom内のJSON数値は元の綴りで保持する。不正入力の旧終了2を65、引数不正を64、I/Oを74へ分ける。
非標準JSONのNaN/Infinity、空ID、型不正を入力不正として扱う。
旧補助がAtomに供給された `snapshot` で選択元を上書きしていた場合も、CLIは実際の選択元を返す。
旧実装はGit履歴で参照でき、実行用スクリプトと二重のテスト実装は同梱しない。
