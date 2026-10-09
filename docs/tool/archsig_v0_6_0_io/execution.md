# 実行、型付き結果、再利用

## 1. CLI

```text
archsig check --archmap A.json --law L.json --out NEW_DIRECTORY
archsig run --archmap A.json --law L.json --out NEW_DIRECTORY
            [--query module/name ...] [--reuse OLD_DIRECTORY]
            [--time-ms N] [--memory-mib N]
archsig version
```

これが全コマンド・全flagである。短縮flag、位置引数、暗黙の入力探索、環境変数による
意味の変更はない。各単数flagの重複・未知flag・整数の不正は usage error。
queryだけ繰返し可能で、重複query指定は拒否。Nは正の10進整数、各上限は独立。
未指定は論理的上限なし。OSの停止・資源不足を成功に変換しない。

check はJSON・版・module依存・語彙binding・値・型・自由変数・参照・循環を検査する。
欠測fieldは有効入力。queryを計算せず、query名と型と依存を出力する。
run は同じ検査をしてから選択queryとその依存を評価する。
query省略はentry moduleの全query。指定できるのはentryのqueryだけ。不存在/非公開名はusage error。
選択queryの外側も静的型検査は行う。
意味引数はflagで渡さない。Lawを変えずに量化域や比較対象をflagで変える機能はない。

stdin、HTTP、ZIPは入力として使わない。pathはローカル通常ファイルを読む。
入力が実行中に変わっても、開始時に読み切ったbyte列だけを使用し、結果に同梱する。
相対pathは呼出しcwd基準。symlinkは読込み開始時に解決し、その後解決結果のbyteを保持する。
source uriやmodule参照から追加ファイルを取得しない。

outは存在しないdirectoryを指定する。既存pathは上書きしない。親directoryが必要。
同じ親に一時directoryを作り、入力コピーと結果を書いてflush後、最終directoryへrenameする。
正常に捕捉した中断も結果をfinalizeする。write/rename失敗時は元の出力先を変更せず、
一時directoryのpathをstderrに示す。再利用候補の破損は通常評価へ戻る。

## 2. 出力ファイル

```text
NEW_DIRECTORY/
  inputs/archmap.json     開始時のAのbyte列
  inputs/law.json         開始時のLのbyte列
  result.json            唯一のmachine-readable結果
```

成功・反証・捕捉した中断・不正入力のいずれも、出力を作れる場合はこの構成で残す。
読めなかった入力のコピーは省略し、resultのinputs状態に記す。
HTMLや人向けの説明はconsumerがresultから生成する。別の判定ファイルを持たない。

stdoutは完了時に一つのJSON line：
`{"format":"archsig.receipt/1","status":RunStatus,"exit_code":Nat,"result":String}`。
resultは作成したresult.jsonの呼出しcwdからのpath、作成不能なら `result` 欄を省略。
stderrは進捗と障害の自然文だけ。機械はreceiptまたはresultを読み、自然文をparseしない。
versionは `{"product":"archsig","version":"0.6.0","semantics":["archsig/0.6.0"]}`
をstdoutに一行出し0で終了する。

## 3. result.json の全体 schema

`Ref` は常に `{node:Id}` という結果node参照。ArchMapのRef値と混同しない。
型が外側から分からない欄の `Value` は常に `TypedValue={type:Type,value:Encoding(Type)}`。
Node.valueだけはNode.typeに従うEncoding(Type)を直接置く。
各表の未知欄を拒否する。省略可能は `?`、empty arrayは許す。

```text
Result = {
 format:"archsig.result/1", semantics:"archsig/0.6.0",
 producer:{version:String, build:String}, command:"check"|"run",
 status:RunStatus, inputs:InputIdentity[], selected_queries:QName[],
 declarations:DeclarationInfo[], answers:Answer[], nodes:Node[], issues:Issue[],
 reuse:{requested:Bool, accepted_nodes:Nat, recomputed_nodes:Nat, rejected:Issue[]},
 usage:{elapsed_ms:DecimalNat, peak_bytes:DecimalNat},
 limits:{time_ms?:DecimalNat,memory_mib?:DecimalNat}
}
RunStatus = "complete"|"partial"|"invalid"|"unsupported"|"interrupted"|"error"
InputIdentity = {kind:"archmap"|"law", state:"read"|"unread",
                 bytes_digest?:Digest, model_digest?:Digest, path?:String}
DeclarationInfo = {name:QName,type:Type,location:InputLocation,dependencies:QName[]}
Answer = {query:QName,type:Type,status:"established"|"refuted"|"undetermined",
          value?:Ref, proposition?:Ref, evidence:Ref[], reasons:Issue[], scope:Scope}
Node = {id:Id,type:Type,state:"value"|"blocked",value?:Encoding(Type),partial?:PartialValue,
        rule:Rule, arguments:Ref[], support:FactPointer[],
        conditions:Condition[], scope:Scope, reasons:Issue[]}
Rule = {kind:"atom"|"subject"|"law"|"builtin", ref:String, location?:InputLocation}
Condition = {id:Id,proposition:Ref,status:"established"|"refuted"|"undetermined",
             evidence:Ref[],reasons:Issue[]}
Scope = {snapshots:Id[],modes:String[],domain:"finite_model"|"all_assignments"|"all_completions",
         quantifiers:Quantifier[],assumptions:Ref[],reading?:Ref}
Quantifier = {kind:"forall"|"exists",name:Id,type:Type,domain?:Ref}
FactPointer = {snapshot:Id,subject:Id,predicate?:QName,atom?:Id}
InputLocation = {input:"archmap"|"law",pointer:String,span?:[Nat,Nat]}
Issue = {code:IssueCode,message:String,location?:InputLocation,
         query?:QName,dependencies:Ref[],missing:FactPointer[],details:IssueDetails}
```

構文エラーでJSON Pointerを確定できない場合はpointerを空文字列にし、
spanに入力byteの半開区間を付ける。型・参照エラーでは該当値のJSON Pointerを必須とする。

Rule.ref はatomなら `snapshot/atom`、subjectなら `snapshot/subject`、lawなら完全宣言名＋
body内JSON Pointer、builtinなら `archsig/0.6.0#core/name`。
入力のbyte digestとmodel digestを分ける。model digestは正規化した内容のdigestであり、
証明の代替ではない。inputs.path は出力directoryからの固定相対path。

Scope.domain は最外の確定主張の範囲。有限snapshotだけならfinite_model、
記号的Term引数を全称評価した場合all_assignments、Hole全補完で同じ場合all_completions。
両方を含むときall_completionsとし、quantifiersにTerm引数のforallを残す。
実際に必要としたsnapshot/mode/仮定を全件保持する。empty quantifiersは量化なし。
型と既知入力以外の仮定を追加する場合は、入力Lawから生成したPropositionをassumptionsに
参照し、その成立条件を同じノードのconditionsに記す。未確認仮定に依存するsealed値は出さない。

Node.arguments が導出DAGの辺。循環は禁止、nodesは依存を先に置くtopological order。
node IDは `n`＋0始まり10進整数、同じ実行で一意。consumerはIDの番号に意味を付けない。
value内のRefも同じDAGの既出nodeのみを指す。原始参照はFactPointerまたは入力のRef encoding。
全leafはAの原始位置、Lの式、固定builtinに達する。欠測nodeはvalueを持たずblockedとなる。
PartialValueは `{kind:"tuple"|"list"|"set"|"conditional",entries:[{position:Nat,value?:Ref,guard?:Ref,missing:FactPointer[]}],observation_plan?:ObservationPlanValue}`。
部分tuple/listの全位置、filterの全候補とguard、ifの二枝を位置で保持する。
ObservationPlanValueは下表ObservationPlanと同じrecord型。neededの部分計画ではentriesは空にできる。
未知の全体値を通常のvalueとして消費させず、表示と観測要求に用いる。
node supportは原始位置の集合。欠測slotはatom欄なしで位置を保持する。

## 4. 値の encoding

原始値は [入力のencoding](inputs.md#3-原始型と値の唯一の-encoding) と同じ。
複合値中の導出型は Ref として参照する。原始値はinlineに保持する。
Fnは `{params:[{name,type}],body:Expr,environment:[{name,value:Ref}]}`、
Snapshotはsnapshot ID、FactRefはFactPointer、Ring/TermSignatureは計算カタログのliteral encoding。
ContextPointは `{context:Ref,position:Nat}`。positionはcontextのcarrier_labels中の位置で、Lawからは読めない。
Termは入力と同じparams/bodyに、`captures:[{name,value:Ref}]`を追加する。
Tuple/List/Set/Optionの構造は入力と同じ。Setのserialization順はcanonical value順。

導出型のvalueは次の必須欄だけを持つ。表内の型名は `{node:Id}` というRefを意味する。Module等は実際のnode型では係数Kを持つ。
配列等は上記一般規則に従う。`KValue`は該当係数環の原始値。

| type | value の欄と意味 |
| --- | --- |
| AtomSet | `{facts:FactPointer[]}`。原始位置の有限集合 |
| Configuration | `{family:AtomSet,requirements:FactPointer[],relation:[[FactPointer,FactPointer]],identification:[[FactPointer,FactPointer]]}`。閉包済み関係 |
| Architecture | `{configuration:Configuration,equations:EquationFamily}` |
| MapCandidate | `{source:Configuration,target:Configuration,pairs:[[FactPointer,FactPointer]]}` |
| ConfigurationHom | `{candidate:MapCandidate}`。条件の証拠はnode.conditions |
| LawHom | `{operation:Operation,underlying:ConfigurationHom,residual_map:ModuleMap}` |
| Span | `{left:ConfigurationHom,right:ConfigurationHom}` |
| Operation | `{name:OperationName,source:Architecture,target:Architecture,atom_map:MapCandidate,action:StateMap,word:Value[]}`。OperationNameは後述。wordは原始操作Refの順序列 |
| Core | `{objects:Architecture[],generators:Operation[],relations:[[Operation,Operation]],extent:"free"|"presented"}` |
| Equation | `{lhs:Term,rhs:Term,role:"required"|"definition"}` |
| EquationFamily | `{kind:"terms",signature:TermSignature,index_type:Type,instances:[{key:Value,equation:Equation}]}` または `{kind:"affine",map:AffineMap,rhs:Vector,role:"required"|"definition"}`。index_typeはequationsに渡したSet(T)のTで、空でも保持 |
| Proposition | `{predicate:String,operands:Ref[],quantifiers:Quantifier[]}`。predicateは下記の公開core命題名または固定構成条件名 |
| SolutionSet | `{state_type:Type,domain:StateDomain,definition:SetExpression,representation:SolutionRepresentation}` |
| LawValues | `{family:EquationFamily}`。key付き残差関数全体を表す |
| Presentation | `{equations:EquationFamily}`。有限式・型・生成演算は参照先から復元 |
| Reading | `{kind:"finite",domain:Ref,codomain:Ref,map:StateMap,fibers:[{image:TypedValue,preimage:TypedValue}]}` / `{kind:"state",domain:StateSystem,codomain:StateSystem,map:Ref,fibers:[]}`。finiteの両域はSet node、stateのmapはFn(Context,StateMap) |
| ContextFamily | `{configuration:Configuration,dependency:[[FactPointer,FactPointer]],equations:EquationFamily}` |
| ContextMap | `{source:Context,target:Context,images:TypedValue[]}`。sourceのcarrier_labels順のContextPoint像 |
| Context | `{base?:Context,carrier_labels:TypedValue[],projection:[{from:Value,to:FactPointer}],support:AtomSet,axes:QName[],observables:EquationFamily}` |
| Cover | `{base:Context,patches:Context[],equations:EquationFamily,kind:"inclusion"|"chart"}` |
| Overlap | `{left:Context,right:Context,pullback:Context,left_projection:ContextMap,right_projection:ContextMap}`。平行な投影も別の射 |
| Module | `{ring:Ring,generators:Value[],relations:KValue[][],free_rank:Nat,torsion:DecimalNat[],construction:{name:String,arguments:Ref[]}}` |
| Vector | `{module:Module,coordinates:KValue[]}`。指定生成元順の剰余類代表 |
| ModuleMap | `{source:Module,target:Module,columns:KValue[][]}`。source各生成元の像 |
| AffineMap | `{linear:ModuleMap,offset:Vector}` |
| Complex | `{modules:Module[],differentials:ModuleMap[],last_diagnosable_degree:Nat,construction:ComplexConstruction}` |
| CochainMap | `{source:Complex,target:Complex,components:ModuleMap[]}` |
| Cohomology | `{complex:Complex,degree:Nat,module:Module,cycles:Module,boundaries:Module}` |
| Class | `{cohomology:Cohomology,representative:Vector,coordinates:Vector}` |
| CoefficientSystem | `{contexts:ContextFamily,value_rule:Ref,restriction_rule:Ref,diagram:ContextMap[],values:[{context:Context,module:Module}],restrictions:[{arrow:ContextMap,map:ModuleMap}]}` |
| StateMap | `{kind:"term",term:Term}` / `{kind:"affine",map:AffineMap}` / `{kind:"finite",source:TypedValue,target:TypedValue,pairs:TypedValue[]}` / `{kind:"compose",first:StateMap,second:StateMap}` |
| StateSystem | `{contexts:ContextFamily,value_rule:Ref,restriction_rule:Ref,diagram:ContextMap[],values:[{context:Context,states:Ref}],restrictions:[{arrow:ContextMap,map:Ref}]}`。statesはSolutionSet、mapはStateMap |
| Descent | `{cover:Cover,coefficients:CoefficientSystem,states:StateSystem,complex:Complex,obstruction:Class,action:[{context:Context,map:ModuleMap}],local_sections:Vector[]}` |
| DiagnosticComparison | `{cochain_map:CochainMap,cohomology_map:ModuleMap,kernel:Module,cokernel:Module,source_class:Class,target_class:Class,class_matches:Proposition}` |
| Repair | `{kind:"equation"|"semantic",solutions:SolutionSet,witness:Value,descent:Descent,comparison?:Reading,recheck:Proposition}` |
| ObservationPlan | `{requirements:[{field:FactPointer,dependents:Ref[],locations:Location[]}],distinguishing_pairs:[{left:TypedValue,right:TypedValue,left_evaluation:TypedValue,right_evaluation:TypedValue,separating_candidates:Nat[]}],minimal_subsets:Nat[][],candidate_domain?:Ref,blockers:Issue[]}` |

SolutionRepresentationは次のtagged union。
`{kind:"empty",certificate:Ref}`、
`{kind:"finite",values:Value[]}`、
`{kind:"affine",particular:Vector,directions:Module,embedding:ModuleMap}`、
`{kind:"symbolic"}`。
空性未決のsymbolicとemptyは違う。
SetExpressionは `{kind:"equations",equations:EquationFamily}`、
`{kind:"image",source:SolutionSet,map:StateMap}`、
`{kind:"glue",cover:Cover,states:StateSystem}`、
`{kind:"finite",elements:TypedValue}` の閉じたunion。elementsは型Set(T)の値。

StateDomainは `{kind:"type",type:Type}` / `{kind:"module",module:Ref}` /
`{kind:"finite",elements:Ref}`。elementsはSet(T)のnode、state_typeはそれぞれType、Vector<K>、T。
solution_image/glueの定義もこのdomainと一致することを再検査する。representationがemptyでも省略しない。
StateMapの始終domainはtermのpack/返り型、affineの両Module、finiteのsource/target、
composeの両外端から一意に復元する。StateMap.kind=finiteのsource/targetはSet(T)/Set(U)のTypedValue、
pairsの各要素はTuple(T,U)のTypedValueで、各source元がちょうど一度現れ、像はtargetに属する。
検索はSetの要素同一性で行い、pairsはsource値のcanonical順に直列化する。
Vector/Classのkey照合にはlaw§9の剰余類の等値を用い、constructorや代表座標の一致で代用しない。

finite Readingのfibers.imageはU、preimageはSet(T)のTypedValue。
通常readingのUは入力Fnの返り型、sufficient_quotientのUはSet(T)である。
後者のcodomainはSet(Set(T))、pairsはTuple(T,Set(T))、各fiberのimage/preimageは同じ同値類。
LawValuesの評価nodeは導出のargumentsに残し、商の元のencodingへ流用しない。
mapと両域を先に出力し、Readingから既出nodeを参照する。空の商は型付きの空集合と空の表を保持する。

ContextFamilyの候補は `core/context_set : ContextFamily→Set(Context)` で取得し、
Set(Context)の別nodeとして出力する。順序はserializationにだけ使う。
Contextはfamily自体を参照せず、baseとsupportの情報を保持する。
同様にModuleが自分の包含/射影を参照せず、mapのnodeがModuleを参照する。
この非循環の構成順を全型に適用する。

## 5. 証拠と反例

証拠もNode。下記の予約型 `Evidence` を結果専用に追加する。
LawはEvidenceの値・literalを構成できない。
`value={kind:EvidenceKind,data:EvidenceData}`。

| kind | 必須 data |
| --- | --- |
| evaluation | `{instance:Value,lhs:Value,rhs:Value,residual?:Value}` |
| finite_exhaustion | `{domain:Ref,checked:Nat,instances:Ref[]}` |
| counterexample | `{assignment:Value,operation_paths:Ref[],lhs:Value,rhs:Value,source_facts:FactPointer[]}` |
| linear_solution | `{map:ModuleMap,rhs:Vector,solution:Vector,recheck:Ref}` |
| linear_inconsistent | `{map:ModuleMap,rhs:Vector,annihilator:Vector,pairing:Value}` |
| smith | `{map:ModuleMap,left:ModuleMap,right:ModuleMap,diagonal:Value,divisibility:Value}` |
| normalization | `{before:Ref,after:Ref,rule_steps:Ref[]}` |
| gluing | `{local:Ref[],correction:Ref,global:Ref,rechecks:Ref[]}` |
| completion_pair | `{fields:FactPointer[],first:Value[],second:Value[],first_result:Ref,second_result:Ref}` |

evidenceの算術はkernelで再検査する。row-rank等のスカラーだけを不成立証拠にしない。
LawValuesの形の不一致はevaluationでinstanceをUnit、lhs/rhsを両LawValuesのTypedValue参照とし、
参照先のsignature/key/moduleの差を再検査する。架空の状態代入やresidualは付けない。
反証のsupportには元の操作名・入力・結果・sourceへの位置を含める。
全称命題の一つの確定反例は他instanceの欠測があっても有効。
存在命題の否定は全域を尽くした証拠が必要。補完対は観測された反例と別のkindで返す。

## 6. 状態、理由、終了コード

| code | 意味 |
| --- | --- |
| missing_observation | 必要fieldが未観測。missingと依存式を必須 |
| inconsistent_observation | 到達したHoleに型を満たす補完がない |
| unsupported_algorithm | 有効な型付き命題に対応する算法がない。detailsにoperatorとoperand型 |
| theorem_obligation | 定理による昇格に必要な条件/接続証明がない。条件を名指す |
| invalid_construction | 有効入力から作ろうとした構造の条件が偽/型のidentityが不一致 |
| budget_exhausted | time/memoryの上限と停止位置 |
| cancelled | SIGINT/SIGTERMによる停止 |
| dependency_blocked | 依存先nodeの理由を推移的に参照 |
| syntax, duplicate_key, duplicate_id, duplicate_fact, type, reference, cycle, vocabulary_mismatch | 入力の提示違反。locationを必須 |
| unsupported_version | 未対応format/semantics |
| usage, io, internal | 呼出し、ファイル操作、処理系の故障 |

RunStatusとexit codeは次の優先順（上ほど優先）で一意に決める。

| 条件 | status | exit |
| --- | --- | --- |
| SIGINT/SIGTERMを捕捉 | interrupted | 130 / 143 |
| io/internal failure | error | 74 / 70 |
| usage error | invalid | 64 |
| 不正入力 | invalid | 65 |
| 未対応版 | unsupported | 69 |
| 予算消尽 | interrupted | 75 |
| 全選択queryが確定、少なくとも一つrefuted | complete | 1 |
| 全選択queryが確定、反証なし。check成功も含む | complete | 0 |
| 少なくとも一つundetermined | partial | 2 |

全queryがunsupported_algorithmでもstatusはpartial・exit2。
異なる障害種が併発した場合は上表の最初の行。io/internalはioを優先し、複数signalは最初に捕捉したsignalを用いる。
数学的な反証は有効な結果。部分結果には確定値・確定反例を残すが、exit1よりexit2/75が優先する。
途中で得たprovisional値をestablishedにしない。OSのSIGKILL/停電は捕捉できないため、
最終directoryがない場合は未完了と読む。receiptの欠落を成功と解釈しない。

## 7. 正規化、版、再利用

canonical JSONは、object keyをUnicode scalar順、空白なし、非ASCIIをUTF-8で出し、
引用符とbackslashはbackslashでescapeし、U+0000..001Fは小文字4桁の `\u00xx` に統一する。
その他の文字をescapeしない。`/`はescapeしない。数値metadataは通常の10進整数。
意味上集合の表はID/完全名またはcanonical valueのUTF-8 byte辞書順へ並べる。
集合以外のarray順、Text、原始ID、provenanceは変更しない。
正規化したmodelにはsemanticsと展開済みmodule内容を含める。

`--reuse` は以前の出力directoryを一つだけ受け取る。現在のA/Lを必須とする。
旧resultのformat/semantics/型/導出DAGを検査し、現在の原始根とLaw式へ照合して各推論を再検査する。
一致するdigestは索引の候補選択にだけ使う。再検査を実装しない初期処理系は全て再計算してよい。
不正な再利用候補はreuse.rejectedへ記録し、通常評価を続ける。

現在の入力で導出できない結論が旧resultから増えることはない。
現在のsourceが変わった場合、古い由来を新しい結果へ貼り直さない。
consumerが次の問いを計算する際は、Lawのquery依存を追加してA/Lを再入力する。
結果だけを新しい意味入力として受け取る別CLIはない。

実装は、同じ完全入力の数学的な値と条件について決定的であることを要求する。
wall time、メモリ、node番号、表示基底、証人選択は意味的一致の対象から分ける。
予算を増やしても既に検査済みの主張の真偽を反転させず、未決の理由と範囲だけを更新する。

## 8. 数値表示の寸法と順序

Module.generatorsの各値はTypedValue。relationsの各内側配列は一つの関係ベクトルであり、
長さはgeneratorsの数。意味はR^generatorsをそれらのspanで割った加群。
ModuleMap.columnsはsource生成元ごとのtarget座標ベクトル、各長さはtarget生成元数。
Vector.coordinatesもそのmoduleの生成元数と同長。部分加群・商の表示変換をconstructionに
依存nodeとして保持し、同じ座標列を異なるmoduleの値として使用しない。
free_rankは自由部のrank。Q/Fpでtorsionは空、Zでは1より大きい正の不変因子を
各要素が次を割る順に保持する。Zの有限表示はRREFだけで処理しない。
全行列の零サイズを許す。0行n列のnは始終域のgenerator数から確定する。

## 9. 外部動作の細則

- 入力検査順は通常のJSON構文、format/semantics版、対応版の欄schema、
  module/型/参照の順。未知版の新しい欄を先に不正schemaとして拒否しない。
- check成功時はselected_queries/answers/nodesが空で、declarationsはentryの全queryの
  完全名・返り型・位置・推移的query依存を持つ。checkの失敗はissuesに残す。
- runでは選択queryごとにちょうど一つAnswerを返す。非Propositionのestablishedは
  value必須、proposition無し。Propositionの確定回答はproposition必須、value無し。
  refutedはPropositionだけ。undeterminedはvalueを持たず、命題が構成できれば
  propositionを参照し、未構成ならreasonsから必要な式へ戻れる。
  中断で未着手のqueryもundeterminedと停止理由を返す。依存queryの値はnodesに保存する。
- 不正入力/未対応版では意味計算を始めずanswers/nodesは空。選択を解決できた場合だけ
  selected_queriesを埋める。usage errorでは解決前ならinputsも空にできる。
- DecimalNatは `0|[1-9][0-9]*` の文字列。時間は単調時計でCLI開始から評価終了までの
  wall time、memoryは当該processのpeak RSS byte。予算は入力読込・check・評価を含むが、
  捕捉した結果のfinalizeには適用しない。各Expr評価と各組込みの有限反復一回の前後で
  上限を確認するsoft limitとする。一つの原始演算の途中やOS計測間隔の超過を許す。
  予算消尽を確認した時点で新しい導出を開始せず、検査済みnodeだけをfinalizeする。
- model_digest(A)はAをschema上の集合表順に正規化したcanonical JSONのSHA-256。
  原始値とprovenanceの両方を含む。model_digest(L)は同梱全moduleのaliasを完全名へ展開し、
  module/import/roles/declarationsの集合表をそれぞれID/module/値/name順にしたL全体。
  Expr内arrayとListは並べ替えない。vocabulary digestはinputsで指定した宣言arrayだけ、
  import digestは同じ集合順に正規化したalias展開前のmoduleだけを対象とする。
  bytes_digestは読んだbyte列そのもの。文字列digestを他の正規化の代用にしない。
- issuesとreasonsは code, location.input, location.pointer, query の辞書順（欠ける欄は空）に
  並べ、同じ原因を重複報告する場合も依存元の位置を保持する。messageは説明であり、
  programが分岐するための値はcodeと型付きdetailsである。

## 10. 名前・計画・条件のencoding

OperationNameは `{kind:"generator",subject:TypedValue}` /
`{kind:"identity",object:Ref}` / `{kind:"word",generators:Ref[]}`。
generatorsは実際のOperation node参照の順序列。Operation.wordは生成元の原始subject RefのTypedValue列で、
恒等では空。生成元自身のOperation nodeをwordから参照しない。wordの順序をSetへ変換しない。
Readingの有限表とfiberの型は§4に従う。state readingではfibersは空、
domain/codomainはStateSystem、mapはContext→StateMapのFn nodeを指す。
ObservationPlanの候補番号はdistinguishに渡したListの0始まり位置。
minimal_subsetsは昇順index列を辞書順に並べたもの。requirements.locationsは
入力Location型のarray。反例対の値はcandidate_domainの元であり、架空のsource観測にしない。

IssueDetailsは次のcode別recordである。共通欄から復元できるものには空objectを使う。

| code | details |
| --- | --- |
| unsupported_algorithm | `{operator:QName,operand_types:Type[],required_method:String}` |
| theorem_obligation | `{obligation:String,conditions:Ref[]}` |
| invalid_construction | `{operator:QName,condition:Ref,expected?:Type,actual?:Type}` |
| budget_exhausted | `{resource:"time_ms"|"memory_mib",limit:DecimalNat,observed:DecimalNat}` |
| cancelled | `{signal:"SIGINT"|"SIGTERM"}` |
| type | `{expected:Type,actual:Type,effect?:{allowed:"pure",found:"derive"}}`。純粋性違反ではeffect必須で、値型が同じでもよい |
| unsupported_version | `{found_format:String,found_semantics?:String}` |
| io | `{operation:"read"|"create"|"write"|"flush"|"rename",path:String}` |
| internal | `{operation:String}` |
| その他 | `{}`。位置・依存・missingはIssue共通欄に保持 |

invalid_constructionのconditionは、失敗した型identity等を表す生成Proposition nodeも許す。
型を構成する前に失敗しactual/expectedを表せない場合はtype codeでなくsyntaxを使う。

Context.carrier_labelsは元の値の列。point自体をこの欄へ入れない。
projection.fromもこのlabelで、context_pointsが列の各位置からContextPointを外側で生成する。
Core.generatorsには同じ原始subject名を二度登録できない。同じ名前で異なる作用を持つ生成元は
invalid_constructionであり、同じ端点の異なる名前は保存する。

Proposition.predicateは、proposition/all/any/term_equal/holds/inhabited/solution_forall/
solution_exists/hom_condition/action_equal/word_equal/quotient_equal/map_equal/is_iso/
class_zero/sheaf_condition/preserves_diagnostics/sufficient/state_equal の
`core/`付き完全名と、結果専用 `core/constructible` に限定する。
前者のoperandsは当該署名の引数順、後者は第1operandにconstructor完全名のText、
以後にその引数を置く。意味はカタログに記したその構成の全条件の連言。
純粋Boolや内部等値検査からの命題はcore/propositionを使い、独自の判定名を増やさない。

ComplexConstructionは `{kind:"plain"}` /
`{kind:"cech",cover:Ref,coefficients:Ref,convention:"increasing"|"ordered",requested_degree:Nat}`。
ContextMapがU→Vなら、CoefficientSystemとStateSystemのrestrictionはV→Uである。
