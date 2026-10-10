# 型付き結果

## 1. result.json

出力はUTF-8のJSON。未知欄、重複key、`null`を許さない。`?`は省略可能な欄、
`T[]`は有限array、`Nat`・`Id`・`QName`・`Digest`・原始型`P`は[入力](inputs.md)に従う。
Pは同文書のTypeの別名であり、宣言metadataではOwnedを許し、具体値では束縛後のRef型へ解決する。
`DecimalNat`は`0|[1-9][0-9]*`の文字列。以下のrecordは記した欄だけを持つ。

```text
Result = {
  format:"archsig.result/1", semantics:"archsig/0.6.0",
  producer:{version:String,build:String}, command:"check"|"run",
  status:RunStatus, exit_code:Nat, inputs:InputIdentity[],
  declarations:DeclarationInfo[], vocabularies:{manifest:Vocabulary,digest:Digest}[],
  requests:Request[], answers:Answer[], nodes:Node[], issues:Issue[],
  reuse:{requested:Bool,accepted_nodes:Nat,recomputed_nodes:Nat,rejected:Issue[]},
  usage:{elapsed_ms:DecimalNat,peak_bytes:DecimalNat},
  limits:{time_ms?:DecimalNat,memory_mib?:DecimalNat}
}
RunStatus = "complete"|"partial"|"invalid"|"unsupported"|"interrupted"|"error"
InputIdentity = {kind:"archmap"|"law",state:"read"|"unread",
                 bytes_digest?:Digest,model_digest?:Digest,path?:String}
DeclarationInfo = {name:QName,kind:DeclarationKind,parameters:Parameter[],
                   fields:Parameter[],returns?:Type,role?:Role,
                   location:Location,dependencies:QName[]}
DeclarationKind = "reading"|"entity"|"arrow"|"correspondence"|"data"|
                  "view"|"law"|"local"|"change"|"relation"
Parameter = {name:String,type:Type}
Role = "required"|"optional"|"derived"
Request = {id:String,text:String,kind:QuestionKind,head:Selector,
           arguments:{name:String,value:Selector}[],dependencies:String[]}
Selector = {kind:"declaration",name:QName}
         | {kind:"subject",snapshot:Id,subject:Id}
         | {kind:"answer",id:String,path:(String|Nat)[]}
         | {kind:"enum",value:String} | {kind:"degree",value:Nat}
Answer = {id:String,status:Decision,outputs:{Field:Ref},claim?:Ref,
          evidence:Ref[],reasons:Issue[],scope:Scope}
Decision = "established"|"refuted"|"undetermined"
Ref = {node:String}
Node = {id:String,type:Type,state:"value"|"blocked",value?:Payload,
        partial?:Partial,rule:Rule,arguments:Ref[],support:FactPointer[],
        conditions:Ref[],evidence:Ref[],judgment?:Judgment,scope:Scope,reasons:Issue[]}
Judgment = {status:Decision,evidence:Ref[],reasons:Issue[]}
Rule = {kind:"subject"|"atom"|"law",location:Location}
     | {kind:"construction",name:Construction}
Partial = {entries:{path:(String|Nat)[],value?:Ref,reasons:Issue[]}[]}
Scope = {readings:QName[],snapshots:Id[],modes:("observed"|"proposed"|"specification")[],
         domain:"finite_model"|"all_assignments"|"candidate_space"|"all_completions",
         quantifiers:Quantifier[],assumptions:Ref[]}
Quantifier = {kind:"forall"|"exists",name:String,type:Type,domain?:Ref}
FactPointer = {snapshot:Id,subject:Id,field?:QName,atom?:Id}
Location = {input:"law"|"archmap",pointer?:String,span?:[Nat,Nat]}
Issue = {code:IssueCode,message:String,location?:Location,request?:String,
         dependencies:Ref[],missing:FactPointer[],details:IssueDetails}
```

Vocabularyは[入力の語彙manifest](inputs.md#4-語彙-binding)をそのまま使う。
QuestionKindとFieldは[固定12問](execution.md#3-固定の12の問い)のkindと出力fieldに限定する。
`outputs`は固定field名をkeyとするobjectであり、任意のkeyを追加しない。
Request.argumentsは`bind.`へ展開した名前順。pathのStringはrecord欄、Natは位置を表す。
CLIのEnumは問いごとの列挙に限定し、一般のString値として評価しない。
declarationsとvocabulariesは完全名順。parametersとfieldsは宣言順を保持する。
宣言metadataのTypeはPまたはLawのPath型に対応する`["Path",QName,QName]`に限る。
dataのconstructorは完全名のDeclarationInfo（kind=data、parametersに引数型）にも列挙する。
名前のないconstructor引数名は`arg0`からの位置名とする。
check成功時はrequests/answers/nodesが空。checkでAを省略した場合、inputsにAの欄を作らない。
inputs.pathは出力directoryからの固定相対pathで、読めた入力だけに付ける。

LawのLocationは元byte列の半開区間spanを必須とする。ArchMapはJSON Pointerを必須とし、
構文エラーでPointerが決まらない場合だけpointer=""とspanを使う。
FactPointerのfieldなしはsubject存在、fieldあり・atomなしは未観測slot。
由来を表すsupportから、inputsのArchMapを通してorigin/sourceへ戻れる。

## 2. 回答、条件、導出

各選択問いにちょうど一件のAnswerを返す。値を返す問いは必要な出力が構成できればestablished。
命題を問う問いはclaimをPropositionへ向け、そのjudgmentとAnswer.statusを一致させる。
evaluateがBool=falseを返す場合も値の評価はestablishedである。
map/compose/localizeのclaimは選択した構成条件、solve/repairは修復の存在、
quotientのlaw指定時は評価族の保存、compareは選択した比較の成立を表す。
diagnoseのclaimはfiniteのdegree=1では大域解の存在、affineのdegree=1では対象障害類の零性とする。
finiteのdegree=0はmatching familyと大域制限の全体を返す値の問いで、claimを持たない。
affineのdegree≠1はspaceの計算を問いとし、class/claimを作らず、spaceが得られればestablished。
degree=1でspaceだけを計算でき対象classが構成できなければundeterminedとし、classを零としない。

反証ではclaimと検査可能な反例を必須とする。不存在の反証には全候補を尽くす証拠が要る。
構成できたdomainや式、確定済みの値・反例を、別の出力が未決でもoutputs/nodesへ保持する。
反証された構成のmapやrepairは出力しない。未着手もundeterminedと停止理由を返す。
unknown、局所可視性不足、非対応の結果を通常の値として後続計算へ流さない。
`needed`は元の問いが未決でも理由を読める。元の障害を返す計画自体はestablishedになり得る。

Node.typeはP、後述の導出型名、`["Path",QName,QName]`、`["Vector",Ref]`、`["ModuleMap",Ref,Ref]`、
`["List",Type]`、`["Tuple",Type,...]`、`["Set",Type]`のいずれか。
Path/Vector/ModuleMapは必ずこのarray型を使い、型名だけのStringを使わない。
表の短い型名はこの型の略記。PathのQNameは始域・終域のentity型。
VectorのRefはModule、ModuleMapの二つのRefは始域・終域のModule。
同じ座標や同型な型でも、このidentityを黙って同一視しない。
原始型payloadは[原始encoding](inputs.md)に従う。導出型を含むcontainerの要素はRef、
原始要素だけのcontainerは原始encodingを使う。本文の表内の型名はその型のRefを意味する。
型が外側から分からない値は`TypedValue={type:Type,value:Payload}`とする。

Proposition以外のNodeにjudgmentを置かない。Propositionのvalueは命題の式、judgmentはその判断。
未知でも式を構成できるPropositionはstate=valueを持てる。
state=blockedはvalueを持たず、reasonsが一件以上。partialは位置・分岐を失わない表示専用である。
valueにはblocked nodeを含めない。ただし構成条件・式・未決理由の参照は保持できる。

全Refを導出DAGの辺とし、nodesは既出nodeだけを参照する順に並べる。
idは`n0`から連続する10進番号。同じ実行内で一意であり、番号に数学的意味を付けない。
argumentsは構成の入力、conditionsは入力から構成を許すProposition、evidenceは結果専用の証拠。
成立未確認の条件を必要とする値をstate=valueとして封じ込めない。
全leafは現在のAの原始位置、Lの式、または本仕様の固定構成規則へ達する。
CLIのselectorはこれらを選ぶためだけに使い、新しい原始leafにしない。
Scopeは実際の根・量化域・仮定を全件保持する。全補完を含む場合domain=all_completionsとし、
候補parameter等の量化もquantifiersに残す。仮定の追加はLawの式から生成したPropositionだけとし、
同じnodeのconditionsに検査結果を残す。

Constructionは次の閉じた列挙とする。各規則の意味は[核の構成](computations.md)に従う。
`binding, projection, expression, evaluation, law_instance, configuration,
architecture, map_candidate, configuration_map, object_algebra_map, operation, composition,
comparison, domain, state_space, state_map, candidate_space, solution_set, equation_space, equation_solutions, path, context, context_map,
cover, topology, local_system, equation_presentation, ring, polynomial, finite_function, ring_map, ideal, module, module_map, vector, action,
complex, cochain_map, cohomology, class, diagnostic, repair, quotient, observation_plan,
proposition, evidence`。作者が呼ぶ関数名として公開しない。

## 3. 対象・式・写像

`Binding={name:String,value:Ref}`、`Slot={subject:Ref,field:QName}`とする。
Expressionは原式または核の固定変換を表し、自由parameterとbindingsを明示する。

| Type | Payload |
| --- | --- |
| Expression | `{kind:"source",location:Location,parameters:Parameter[],bindings:Binding[]}` / `{kind:"transform",operation:"difference"\|"substitute"\|"compose"\|"project",operands:Ref[],parameters:Parameter[],bindings:Binding[],position?:Nat}` |
| Evaluation | `{expression:Expression,bindings:Binding[],environment?:Architecture,parts:{location:Location,value?:Ref,residual?:Ref,children:Ref[]}[],value?:Ref,applicability:"applicable"\|"not_applicable"\|"undetermined"}` |
| LawInstance | `{name:QName,role:Role,bindings:Binding[],guard?:Expression,body:Expression,occurrence:Location}` |
| Proposition | `{predicate:Predicate,operands:Ref[],quantifiers:Quantifier[]}` |
| Configuration | `{family:FactPointer[],requirements:FactPointer[],relations:[FactPointer,FactPointer][],identifications:[FactPointer,FactPointer][]}` |
| Architecture | `{reading:QName,root:Ref,configuration:Configuration,laws:LawInstance[],internal_arrows:Ref[],overrides:{slot:Slot,value:Ref}[]}` |
| MapCandidate | `{declaration?:QName,subject?:Ref,source:Architecture,target:Architecture,pairs:[FactPointer,FactPointer][]}` |
| ConfigurationMap | `{candidate:MapCandidate}` |
| ObjectAlgebraMap | `{configuration_map:ConfigurationMap,law_maps:[LawInstance,LawInstance][],operation_maps:[Ref,Ref][],value_maps:StateMap[],naturality:Proposition[]}` |
| Operation | `{source:Architecture,target:Architecture,candidate:MapCandidate,action:StateMap,name:OperationName,word:Ref[]}` |
| Path | `{reading:QName,source:Ref,target:Ref,generators:Ref[]}` |

OperationNameは`{kind:"generator",subject:Ref}`、`{kind:"identity",object:Ref}`、
`{kind:"word",generators:Ref[]}`。wordは原始correspondence参照の順序列。
合成はgeneratorsに元のOperationを参照し、自分自身を参照しない。
MapCandidateは原始候補を持つ場合だけdeclaration/subjectを保持する。
この二欄は両方を持つか、両方を省略する。
合成候補では両欄を省略して構成のargumentsに全生成元を残す。恒等では両欄を省略してrootへ依存する。
Architecture.overridesは候補の値であり、元のArchMapを変更しない。
Path.generatorsは原始arrowまたはcorrespondence参照の順序列。空列はsource=targetの恒等。
それぞれの始終点と作用をLawの宣言から復元する。異なる階層の生成元を一つのPathへ混在させない。
Evaluation.environment省略は原始観測、指定時はそのArchitectureのoverridesを適用した環境を指す。

Expressionのsource型は参照先の型、differenceは同じ数値型二項の差、substituteは第1項へbindingsの
型を保つ同時代入、composeは二項の順序合成、projectはpositionにおけるtuple成分である。
positionはprojectだけ必須。Evaluation.partsは元ASTの各出現を保持し、子のEvaluationを先に置く。
等号の左右の値、数値成分の残差、量化instanceの束縛を異なる参照として残す。
guard=falseのLawはapplicability=not_applicableとし、全称要求へ違反を追加しない。

Predicateは`law_holds, constructible, equal, word_equal, action_equal, relation_equal,
configuration_preserved, object_algebra_preserved, cover_adequate, restrictions_compatible,
sheaf_condition, action_laws, inhabited, class_zero, diagnostics_preserved, sufficient, divides`。
law_holdsのoperandsはLawInstance、equal系は比較順の二値、inhabitedはSolutionSet、
inhabitedはEquationSolutionSetも受け取る。class_zeroはClass、diagnostics_preservedはComparison、
sufficientはQuotient、dividesは順にZの除数と被除数。
その他は検査する構成のargumentsと同じ順のoperandsを使い、constructibleの第1operandだけは
Construction名を持つText nodeとする。これらは結果上の命題表示でありLawの呼出しAPIではない。

## 4. 候補域、局所構造、方程式

| Type | Payload |
| --- | --- |
| Domain | `{kind:"type",type:P}` / `{kind:"finite",type:P,elements:Ref[]}` / `{kind:"module",module:Ref}` / `{kind:"states",space:Ref}` / `{kind:"candidates",space:CandidateSpace}` / `{kind:"solutions",solutions:Ref}` / `{kind:"image",map:StateMap,source:Ref}` |
| StateSpace | `{base:Architecture,slots:Slot[],state_type:P}` |
| StateMap | `{source:Domain,target:Domain,kind:"expression",expression:Expression}` / `{source:Domain,target:Domain,kind:"finite",pairs:[Ref,Ref][]}` / `{source:Domain,target:Domain,kind:"affine",linear:ModuleMap,offset:Vector}` / `{source:Domain,target:Domain,kind:"compose",first:StateMap,second:StateMap}` |
| CandidateSpace | `{kind:"change"\|"identity",base:Architecture,bindings:Binding[],change?:QName,parameters:Domain,states:StateSpace,action:StateMap,instances:{subject:Ref,positions:Nat[]}[],guards:Expression[],requirements:LawInstance[]}` |
| SolutionSet | `{domain:CandidateSpace,requirements:LawInstance[],representation:SolutionRepresentation}` |
| EquationSpace | `{base:Architecture,variables:{position:Position,type:P}[],parameters:Domain,requirements:LawInstance[]}` |
| EquationSolutionSet | `{domain:EquationSpace,representation:SolutionRepresentation}` |
| Context | `{base:Architecture,locals:{declaration:QName,bindings:Binding[]}[],carrier:TypedValue[],dependencies:Slot[],readings:{expression:Expression,type:P,domain:Domain}[],law_coordinates:LawInstance[]}` |
| ContextMap | `{source:Context,target:Context,images:Nat[],restrictions:StateMap[]}` |
| Overlap | `{left:Context,right:Context,context:Context,left_projection:ContextMap,right_projection:ContextMap}` |
| Cover | `{base:Context,patches:Context[],overlaps:Overlap[],adequacy:Proposition}` |
| Topology | `{contexts:Context[],maps:ContextMap[],generators:Cover[],covering_sieves:{base:Context,arrows:ContextMap[]}[]}` |
| LocalSystem | `{base:Architecture,laws:LawInstance[],change?:QName,contexts:Context[],maps:ContextMap[],cover:Cover,topology:Topology,semantic_states:{context:Context,parameters:SolutionSet,state_image:Domain,action:StateMap}[],equation_states:{context:Context,space:EquationSpace,solutions:EquationSolutionSet}[],restrictions:{side:Side,arrow:ContextMap,map:StateMap}[],coefficients:{side:Side,context:Context,module:Ref}[],coefficient_restrictions:{side:Side,arrow:ContextMap,map:Ref}[],actions:Action[],state_comparisons:{context:Context,map:StateMap,conditions:Proposition[]}[],sheaf_checks:{scope:"cover"\|"topology",side:Side,proposition:Proposition}[],presentations:EquationPresentation[],polynomial_inclusions:{along:ContextMap,map:RingMap}[],residual_restrictions:{along:ContextMap,state_projection:StateMap,residual_projection:StateMap,commutes:Proposition}[],conditions:Proposition[]}` |
| EquationPresentation | `{instances:LawInstance[],domain:Domain,ring:Ring,coordinates:{instance:LawInstance,component:Nat[],lhs:Expression,rhs:Expression,nu:Ref,epsilon?:Ref}[],witness_ideals:Ideal[],required_ideal:Ideal,evaluation?:RingMap,context:Context}` |
| Ring | `{kind:"scalar",scalar:"Z"\|"Q"\|["Fp",String]}` / `{kind:"polynomial",base:Ring,variables:{position:Position,type:P}[]}` / `{kind:"finite_functions",domain:Domain}` |
| Polynomial | `{ring:Ring,terms:{coefficient:Ref,powers:Nat[]}[]}` |
| FiniteFunction | `{ring:Ring,values:Ref[]}` |
| RingMap | `{kind:"polynomial",source:Ring,target:Ring,images:Polynomial[]}` / `{kind:"finite_functions",source:Ring,target:Ring,basis_images:Ref[]}` / `{kind:"identity",source:Ring,target:Ring}` |
| Ideal | `{ring:Ring,generators:Ref[],kind:"witness"\|"obstruction"}` |

Domain.elements、Context.dependencies/carrier、Cover.patches/overlaps等は意味上の集合表。
有限StateMapのpairsはsourceの全元を一回ずつ含み、像はtargetに属する。
ContextMap U→Vの制限は状態・係数ともV→U。imagesはsource.carrierの各元のtarget位置。
carrierの順序はserializationだけに用い、元の同一性を位置番号に置き換えない。
ContextMap自身の写像向きと値の制限の向きを取り違えない。
Topology.covering_sievesは生成した有限圏の全covering sieve。各arrowsはbaseを終域とする射の集合で、
前合成に閉じる。恒等・引戻し・推移性と、generatorsから生成した最小性を有限閉包の過程から検査する。
sheaf_checksのcoverはLocalSystem.cover、topologyはLocalSystem.topologyの検査範囲を指す。
sheaf条件の真偽は局所状態系を構成できることとは別の命題である。
Context.readingsの各値座標は式・束縛・型・実際の像を持つ。dependenciesは式の依存位置であり、
読みの権限と同一視しない。和が読めるだけでは各項の値が公開されたことにならない。
局所のparametersは許可された全候補parameterを局所で可視なLawだけで制限したSolutionSet。
state_imageはその局所actionによる実状態の像であり、globalなLaw解集合の射影に置き換えない。
Sideは`"equation"|"semantic"`。Domain.kind=solutionsはSolutionSetまたはEquationSolutionSetを参照する。
Domain.kind=imageのsourceはCandidateSpace、SolutionSetまたはEquationSolutionSetであり、mapの定義域と一致する。
using省略時は固定対象を読むUnit parameter域のCandidateSpaceを核が生成する。
このkind=identityではchangeを省略し、actionは恒等、guardsは空、許す追加変更はない。
kind=changeではchangeを必須とする。方程式側の全fiberはEquationSpace/EquationSolutionSetで別に保持し、
その解を許された候補変更へ変換するにはstate_comparisonsの実写像と条件の確認を要求する。

SolutionRepresentationは`{kind:"empty",certificate:Ref}`、`{kind:"finite",values:Ref[]}`、
`{kind:"affine",particular:Vector,directions:Module,embedding:ModuleMap}`、
`{kind:"symbolic"}`の閉じたunion。記号表示は空集合を意味しない。
有限解の値はparameter tuple、アフィン解はparticular+embedding(directions)。
作用後の状態が同じでも異なるparameterを潰さず、実状態への商はActionで保持する。

Positionは`{kind:"observation",field:FactPointer}`または
`{kind:"parameter",subject:Ref,name:String,component:Nat[]}`。
方程式の成分位置は元ASTの等号出現とtuple位置を保持する。
同じscalar型の全required座標は同じ環と共有記号を使う。νは元の項から作った多項式差、
εは対象における評価。欠測ならepsilon/evaluationを省略し理由を残す。
各Polynomialは零係数を除き、同じpowersをまとめ、powersの辞書順に並べる。零多項式は空terms。
各powersの長さはring.variables数、coefficientはbaseのscalar型。RingMap.imagesはsourceの
各変数のtarget上の像をsourceの変数順に並べ、同じscalar baseを保つ。
scalar ring上のPolynomialはpowers=[]の定数、RingMap.images=[]である。
finite_functionsのdomainは有限の全共有代入域D、各FiniteFunction.valuesはDのcanonical順のZ値。
νは各代入でguardが成立し左右が異なることの指示値0/1、εは実対象代入のZ値。basis_imagesはDの各特性関数の像で、
環準同型の単位・積・和の保存を検査する。有限関数環の対象評価のtargetはscalar Z。
Ideal.generatorsは同じringのPolynomialまたはFiniteFunctionであり、異なる表示を混在させない。
EquationPresentationのcontextは全支持の基底で、そのAAT接続の制限は恒等だけとする。
局所の状態制限W→Vと残差射影の可換性はresidual_restrictionsに保持する。
支持型の局所多項式表示ではContextMap V→Wに対してK[X_V]→K[X_W]の環包含を
polynomial_inclusionsに保持し、逆向きの環制限を仮定しない。
一般条件に多項式realizationを作れない場合は元Expressionを保持して非対応を返す。
Idealの零性やideal membershipを、εの零性へ読み替えない。

## 5. 線形表示、診断、修復、商

| Type | Payload |
| --- | --- |
| Module | `{ring:Ring,generators:TypedValue[],relations:Ref[][],free_rank:Nat,torsion:String[],construction:{name:"free"\|"kernel"\|"image"\|"quotient",arguments:Ref[]}}` |
| Vector | `{module:Module,coordinates:Ref[]}` |
| ModuleMap | `{source:Module,target:Module,columns:Ref[][]}` |
| Action | `{side:Side,stage:"allowed"\|"lawful_fiber",parameters:Domain,states:Domain,map:StateMap,parameter_kernel?:Module,stabilizer?:Module,effective?:Module,quotient?:ModuleMap,conditions:Proposition[]}` |
| Complex | `{modules:Module[],differentials:ModuleMap[],last_diagnosable_degree:Nat,cover:Cover,convention:"increasing"\|"ordered"}` |
| CochainMap | `{source:Complex,target:Complex,components:ModuleMap[]}` |
| Cohomology | `{complex:Complex,degree:Nat,cycles:Module,boundaries:Module,module:Module,inclusion:ModuleMap,projection:ModuleMap}` |
| Class | `{cohomology:Cohomology,representative:Vector,coordinates:Vector}` |
| Diagnostic | `{kind:"finite_matching",side:Side,system:LocalSystem,degree:Nat,matching:Domain,global:Ref,restriction:StateMap,fibers:{matching:Ref,preimage:Ref}[],conditions:Proposition[]}` / `{kind:"affine_cech",side:Side,system:LocalSystem,degree:Nat,complex:Complex,space:Cohomology,class?:Class,local_sections:Vector[],conditions:Proposition[]}` |
| Repair | `{domain:CandidateSpace,solutions:SolutionSet,parameters:Ref,steps:{subject:Ref,change:QName,parameters:Ref[]}[],object:Architecture,rechecks:Proposition[],local_lift?:StateMap}` |
| Quotient | `{domain:Ref,view:QName,bindings:Binding[],classes:Domain,projection:StateMap,representation:QuotientRepresentation,law?:QName,evaluations:Evaluation[],descent?:StateMap}` |
| Comparison | `{kind:"value"\|"word"\|"action"\|"relation",left:Ref,right:Ref}` / `{kind:"diagnostics",left:Diagnostic,right:Diagnostic,along:Operation,cochain_map?:CochainMap,cohomology_map?:ModuleMap,kernel?:Module,cokernel?:Module,class_transport?:Proposition,finite_map?:StateMap,conditions:Proposition[]}` |
| ObservationPlan | `{request:String,requirements:{field:FactPointer,dependents:Ref[],locations:Location[]}[],blockers:Issue[]}` |

Moduleのringはscalarに限る。各relationとVector.coordinatesの長さはgenerator数。
ModuleMap.columnsはsource生成元ごとのtarget座標列で、その長さはtarget生成元数。
係数Refはそのringの正確な原始数値。零サイズ行列も始終Moduleで寸法を保持する。
free_rankは自由部、Q/Fpのtorsionは空、Zのtorsionは1より大きい正の整数文字列で、
各要素が次を割る順とする。部分加群・商は包含・射影の実写像を別nodeとして残す。
Cohomology.inclusionはcycles→指定次数のModule、projectionはcycles→cohomology.module。
Class.representativeは指定次数のcocycle、coordinatesはcohomology.moduleの元。
Complexは指定次数までの診断に必要な次の微分を含み、d²=0を検査する。
finite_matchingのdegreeは0または1だけに対応し、それ以外はunsupported_algorithm。
degree=0はmatching/globalの対応、degree=1は大域解の存在を返し、有限集合に加群を捏造しない。

局所解が空または未決なら対象classを生成しない。空のlocal_sectionsだけから零類を作らない。
diagnostics比較は実写像を生成した条件を保持し、群のrankの一致だけで保存としない。
finite_matchingのglobal/preimageはsideに応じたSolutionSetまたはEquationSolutionSet。
アフィン比較ではcochain_map/cohomology_map/kernel/cokernelを全て要求し、degree=1ではclass_transportも要求する。
degree≠1は対象classを持たず、診断群の実写像の同型性だけを問う。
有限比較ではfinite_mapとその全単射性・状態対応を要求する。
Actionのstage=lawful_fiberで、x=x0+AtとLaw Lx=cに対するparameter_kernelはker(LA)、
stabilizerはker A、effectiveは実状態像A(ker(LA))。quotientはker(LA)からこの実像への全射。
stage=allowedはLawを課す前の作用で、parameter_kernelを省略し、effectiveはim Aとする。
存在・群作用・自由推移性の条件を別々に確認する。
同じ値型を持つという理由だけで係数や群作用を生成しない。

QuotientRepresentationは`{kind:"finite",fibers:{image:Ref,preimage:Domain}[]}`または
`{kind:"affine",image:Module,kernel:Module,map:ModuleMap,offset:Vector}`。
有限Quotientのclassesは候補値の同値類の集合、projectionは各候補からその同値類への全域写像。
fiberのimageはその同値類、preimageは同じ候補集合。空の商も元のdomain/typeを保持する。
アフィン商は元のparameter域上の実像とoffsetを保持し、周囲の格子全体へ拡大しない。
descentは十分性成立時の商からLaw評価族への実写像。十分性のPropositionは商の後に別nodeで作る。
Lawの十分性反証には同じview値を持ち、Law評価族が異なる候補対をEvidenceに残す。
ObservationPlanは数学的な最小観測集合を主張せず、未観測と可視性不足・非対応をblockersで区別する。

## 6. 証拠と理由

Evidenceは結果専用。`{kind:EvidenceKind,data:EvidenceData}`をpayloadとする。

| kind | data |
| --- | --- |
| evaluation | `{instance:LawInstance,lhs:Ref,rhs:Ref,residual?:Ref}` |
| finite_exhaustion | `{domain:Domain,checked:Nat,instances:Ref[]}` |
| counterexample | `{bindings:Binding[],paths:Ref[],left:Ref,right:Ref,facts:FactPointer[]}` |
| linear_solution | `{map:ModuleMap,rhs:Vector,solution:Vector,recheck:Proposition}` |
| linear_inconsistent | `{map:ModuleMap,rhs:Vector,annihilator:Vector,pairing:Ref,modulus?:DecimalNat}` |
| smith | `{map:ModuleMap,left:ModuleMap,right:ModuleMap,diagonal:ModuleMap,transformed_rhs?:Vector,divisibility:Proposition[]}` |
| normalization | `{before:Ref,after:Ref,steps:Expression[]}` |
| gluing | `{local:Ref[],correction:Ref,global:Ref,rechecks:Proposition[]}` |
| completion_pair | `{fields:FactPointer[],first:Ref[],second:Ref[],first_result:Ref,second_result:Ref}` |
| separating_pair | `{domain:Ref,first:Ref,second:Ref,view_values:[Ref,Ref],law_values:[Ref,Ref]}` |

証拠の算術、全域性、再代入を核で再検査する。rank等のスカラーだけで反証を確定しない。
linear_inconsistentは自由加群間の実際の表示系Bt=dに対する証拠。
annihilatorの座標をuとし、modulus省略時はuᵀB=0かつpairing=uᵀd≠0を検査する。
modulus=m>1指定時は整数系であり、uᵀBの全成分がm倍、pairing=uᵀdがm倍でないことを検査する。
例えば2t=1はu=1,m=2で反証する。商加群の問題は関係生成元を含む自由表示系へ移した導出も残す。
smithではleft/rightがunimodularでleft∘map∘right=diagonalを検査する。
rhsを扱う場合だけtransformed_rhsを持ち、これはleftによるrhsの像。
divisibilityは各対角行の係数が対応するtransformed_rhs成分を割るPropositionを行順に持つ。
零行では0がその成分を割る条件、すなわち成分=0を使う。rhsを扱わない場合はdivisibility=[]。
completion_pairは未知slotの型を保つ補完対、separating_pairは宣言済み候補域の二候補であり、
観測された反例と区別する。反証には元の名前・入力値・結果・source位置を保持する。

| IssueCode | 必須のdetailsと意味 |
| --- | --- |
| missing_observation | `{}`。missingにslot、dependenciesに依存式を要求 |
| visibility_insufficient | `{locals:QName[],coordinates:Ref[]}`。原始値の欠測と別 |
| inconsistent_observation | `{}`。型・参照を満たす補完が存在しない提示 |
| unsupported_algorithm | `{question:QuestionKind,operand_types:Type[],method:String}`。有効な型付き問いに算法がない |
| condition_failed | `{condition:Ref,construction:Construction}`。構成条件が反証された |
| dependency_blocked | `{request:String}`。dependenciesと元理由を推移的に保持 |
| budget_exhausted | `{resource:"time_ms"\|"memory_mib",limit:DecimalNat,observed:DecimalNat}` |
| cancelled | `{signal:"SIGINT"\|"SIGTERM"}` |
| syntax, duplicate_key, duplicate_id, duplicate_fact, type, reference, cycle, vocabulary_mismatch | typeだけ`{expected:Type,actual:Type}`、他は`{}`。入力の位置を必須 |
| unsupported_version | `{found_format:String,found_semantics?:String}` |
| usage | `{argument:String}` |
| io | `{operation:"read"\|"create"\|"write"\|"flush"\|"rename",path:String}` |
| internal | `{operation:String}` |

構成条件が未決なら、その条件のmissing/visibility/unsupported/dependency理由を伝播する。
数学の適用条件を作り検査する責務を外部の追加定理要求へ置き換えない。
不正入力は意味計算前に拒否する。提示は正しいがLawが偽である場合は入力エラーにしない。
型構成前でexpected/actualを表せない不正表記はsyntaxを使う。
issues/reasonsはcode、location.input、pointerまたはspan開始、requestの辞書順に並べる。
同じ原因を再掲する場合も依存元の位置を残す。messageの自然文を機械の分岐に使わない。
