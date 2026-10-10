# 公開計算と決定範囲

## 1. カタログの読み方

Expr の call はこの表の `core/名前` と利用者定義だけを呼ぶ。
署名の `T,U,V` は任意の適合型、`K` は Q/Z/Fp、`S` は有限な添字集合、
`Fn(T,U)` は一引数関数、複数引数は `Fn([T,U],V)` と記す。
下記の `Set(T)` 等は Law の JSON 型 ` ["Set",T] ` の略記である。
Ring は `"Q"`、`"Z"`、`["Fp",p]` を値として持つ予約型。
FactRef は `(snapshot,subject,predicate?)` の原始位置を持つ予約型であり、literal はない。
原始の存在と、欠測を含む field slot を同じ support に保持する。
これら二型も [Law の型](law.md#3-型)に含む。

各構成は内容だけでなく、親構造の identity、添字、入力・規則への導出を保持する。
関数の引数が不足した場合は §10 の決定範囲と Law の欠測規則を適用する。
下の構成条件の違反は `invalid_construction`、その条件を命題として問う演算は `refuted`。
前者の場合も具体的な失敗条件と証拠を返す。

## 2. 純粋な値と有限計算

以下だけを pure と原始 Term 内で呼べる。除算は Option を返し、例外を作らない。

| 名前 | 署名 | 意味 |
| --- | --- | --- |
| add, sub, mul, neg | K×K→K、negはK→K | 正確な環演算 |
| divide | K×K→Option(K) | Q/Fp は非零除算、Z は整除するときだけ some |
| rational | Z→Q | 分母1 |
| mod | Z×Ring→K | Ring が Fp のときだけ。ほかは静的型エラー |
| equal | T×T→Bool | 原始値・Snapshot・FactRef・ContextPointの構造等値。Ref は identity、Set は外延、Term/Fn/他の導出型は不可 |
| not, and, or | Bool→Bool、Bool×Bool→Bool | and/or は左から短絡。欠測時は双方で決まる真理値を返してよい |
| less | K×K→Bool | Z/Q の順序。Fp には使えない |
| some, none | T→Option(T)、Unit→Option(T) | none の型が決まらなければ Option literal を用いる |
| is_some, unwrap | Option(T)→Bool、Option(T)×T→T | unwrap は none のとき明示した第2引数 |
| list, set | List(T)→List(T)、List(T)→Set(T) | list は恒等、set は重複除去 |
| append | List(T)×List(T)→List(T) | 連結 |
| length | List(T)→Z | 要素数 |
| at | List(T)×Z→Option(T) | 0始まり。負や範囲外はnone |
| map | Set(T)×Fn(T,U)→Set(U) | 像。UにSet適格性が必要 |
| map_list | List(T)×Fn(T,U)→List(U) | 順序保存 |
| filter | Set(T)×Fn(T,Bool)→Set(T) | 真の要素。未知guardを落とさない |
| product | Set(T)×Set(U)→Set(Tuple(T,U)) | 直積 |
| union, intersect, difference | Set(T)×Set(T)→Set(T) | 集合演算 |
| unique | Set(T)→Option(T) | 要素がちょうど一つならsome、それ以外none。表示順で選ばない |
| member | T×Set(T)→Bool | 所属 |
| forall, exists | Set(T)×Fn(T,Bool)→Bool | 有限量化。空でそれぞれtrue/false |
| sum | List(K)→K | 空は0。結合順を整数/有理数の近似へ落とさない |

Set の列挙順を List に変換する演算はない。意味ある順序が必要なら原始 List を使う。
組込みに side effect はなく、Text は equal と保持にだけ使う。
equalの適格性も複合型の成分へ再帰的に適用し、List(Term)などの比較を静的に拒否する。
Ring を指す literal は `['lit','Ring','Q']` 等（実ファイルでは二重引用符）。
mod の返り型は第2引数の Ring literal から静的に決まる。変数 Ring への mod は禁止。

`core/closure : Set(T)×Set(T)×Fn(T,Set(T))→Set(T)` はderive/query専用の構成演算。
第1引数seed、第2引数固定有限universeとし、seed⊆universe、到達した各元のsuccessor⊆universeを
検査して最小不動点を返す。違反はinvalid_construction。pure/原始Termには属さない。

## 3. 項、方程式、解

| 名前 | 署名 | 意味と条件 |
| --- | --- | --- |
| term | Fn([P…],P)→Term(P…,P) | 原始型上の純粋な式へ残余化。捕捉したfieldは値またはHoleとして明示し、導出を保持 |
| term_apply | Term(P…,P)×P…→P | 位置引数の代入。arityはTerm型に従う |
| then | Term(A,B)×Term(B,C)→Term(A,C) | `then(f,g)(x)=g(f(x))` |
| term_equal | Term(A…,B)×Term(A…,B)→Proposition | 全引数における作用の等値。有限全列挙か正規化で決定 |
| all, any | Set(T)×Fn(T,Proposition)→Proposition | 有限命題族の全称/存在。forall/existsと同じ欠測規則 |
| decide | Proposition→Bool | 確定した命題の真偽。未決なら理由を伝播しBoolを作らない |
| proposition | Bool→Proposition | 計算されたBoolの命題 |
| equation | Term(A…,K)×Term(A…,K)×Text→Equation | Text literal は `required`/`definition` の二値。両辺の型・変数位置を一致させる |
| equations | TermSignature×Set(T)×Fn(T,Equation)→EquationFamily | 明示signature上のinstance key=T。全式がsignature一致、空集合でも状態域を保持。欠測instanceもキーを保持 |
| holds | EquationFamily→Proposition | 全instanceの全Term引数で等式が成立 |
| solve | EquationFamily→SolutionSet | 全instanceの共通Term引数を同時に満たす代入集合。引数signature一致が必要 |
| inhabited | SolutionSet→Proposition | 解の存在 |
| solution_image | SolutionSet×StateMap→SolutionSet | 解集合の像。状態域が一致すること |
| solution_forall, solution_exists | SolutionSet×Fn(T,Proposition)→Proposition | Tが解集合のstate_typeと一致することを構成時に検査。不一致は空集合でもinvalid_construction。解だけを引数にして量化し、算法がなければunsupported |
| affine | Module×Module×Fn(Vector,Vector)→AffineMap | 展開した式がR線形＋定数であることを係数として検査 |
| linear_part, offset | AffineMap→ModuleMap / Vector | 線形部分と定数 |
| affine_equations | AffineMap×Vector×Text→EquationFamily | f(x)=bを一つのmodule値方程式として保持。第3引数はrequired/definition。商moduleでは座標ごとの等式に分解しない |

Term の入力順は関数の params の順。関数合成による順序は保持する。
入力の数式が多項式であっても型としては受理できる。無制限の多項式可解性を約束せず、
§10 の算法に含まれない問いは `unsupported_algorithm`。

SolutionSet は有限集合、アフィン部分空間/剰余加群の剰余類、空集合、または記号的な
方程式による集合として返す。`solve` の集合提示自体は正しく構成でき、
`inhabited` が未対応になる場合もある。Q/Fp 線形と Z 線形では空性まで必ず決定する。
特解・基底は出力表示だけ。後続の計算は解集合を消費する。

## 4. Configuration、対象、操作、core

| 名前 | 署名 | 意味と条件 |
| --- | --- | --- |
| facts | Snapshot→AtomSet | subject存在と記録済みAtomだけ |
| subject_fact | Ref(S)→FactRef | subject存在の原始位置 |
| snapshot_of | Ref(S)→Snapshot | Refに含まれるsnapshotのidentity |
| support | T→AtomSet | 式の原始依存先。全分岐の構文依存と参照閉包を保持。最小性は主張しない |
| fact_set | Set(Ref(S))→AtomSet | 各subject存在と記録されたfields、そのRef先存在の閉包 |
| config | AtomSet×Set(Tuple(FactRef,FactRef))×Set(Tuple(FactRef,FactRef))→Configuration | 第2引数を有向関係、第3引数の反射対称推移閉包をidentification。端点がfamily内 |
| fact_refs | AtomSet→Set(FactRef) | 原始位置を列挙 |
| object | Configuration×EquationFamily→Architecture | configurationとLaw instance。違反する対象も保持 |
| candidate_map | Configuration×Configuration×Set(Tuple(FactRef,FactRef))→MapCandidate | 明示した有限関係を候補として保持 |
| hom_condition | MapCandidate→Proposition | 全域一意、family・relation・identification保存を同時検査 |
| verify_hom | MapCandidate→ConfigurationHom | 上の条件の成立時だけ生成 |
| law_hom | Operation×ModuleMap→LawHom | candidateをverify_homし、値作用fと残差写像hで E_target(f(x))=h(E_source(x)) を全状態で検査 |
| operation | Ref(S)×Architecture×Architecture×MapCandidate×StateMap→Operation | 第1引数が名前。候補のsource/targetが両Architectureのconfigurationとidentity一致し、StateMapの始終carrierが各状態域と一致することを必須検査。候補保存の成否は別に保持 |
| operation_hom | Operation→ConfigurationHom | 候補Atom作用を検査。操作名を消さない |
| compose_hom | ConfigurationHom×ConfigurationHom→ConfigurationHom | g∘f。中間configuration一致 |
| identity_hom | Configuration→ConfigurationHom | 恒等写像 |
| span | ConfigurationHom×ConfigurationHom→Span | 同一始域を持つ二本。削除を含む対応の共通部分 |
| core | Set(Architecture)×Set(Operation)→Core | 指定対象・操作から自由圏の恒等と合成語を有限提示。全語の有限列挙を要求しない |
| word | Core×List(Operation)→Operation | 型の合う順序語。空語は始域不定なので `identity_operation` を用いる |
| identity_operation | Core×Architecture→Operation | 指定対象上の空語 |
| action_equal | Operation×Operation→Proposition | Atom作用とStateMap作用の等値。名前の等値と別 |
| word_equal | Operation×Operation→Proposition | 同じ名前付き語の構文等値。恒等を除く結合正規形で比較 |
| quotient_core | Core×Set(Tuple(Operation,Operation))→Core | Lawが生成した経路関係で商。両辺の端点・作用保存を別に検査 |
| quotient_equal | Core×Operation×Operation→Proposition | 有限合同閉包で尽くせる場合に決定。他は未対応 |

configuration の family は A の原始位置を持つまま固定する。関係や識別の閉包、導出対象は
原始 Atom に追加しない。operation の値作用がその Atom対応を意味として実現していることは
LawHom 等で明示的に問う。名前と端点だけを示した入力から任意の作用を補わない。

削除は、残す family が参照・選択した構造に閉じていることを config で検査し、
そこから前後への全写像を作る。部分写像を暗黙に全写像とみなさない。

## 5. 局所構造と被覆

| 名前 | 署名 | 意味と条件 |
| --- | --- | --- |
| contexts | Configuration×Set(Tuple(FactRef,FactRef))×EquationFamily→ContextFamily | 第2引数の依存へ閉じたsupport部分集合全部を生成。各方程式の自由変数・原始依存をobservableとして制限。axisは依存predicateのaxisの集合 |
| context_set | ContextFamily→Set(Context) | 全有限contextの集合。表示順を意味へ入れない |
| base_context | ContextFamily→Context | 全support |
| local_context | ContextFamily×AtomSet→Context | 指定seedの依存閉包。該当部分集合を返す |
| context_members | Context→AtomSet | support |
| cover | Context×Set(Context)×EquationFamily→Cover | 各patchがbaseへ包含し、support union=base、各要求equationの全supportが少なくとも一patchにあることを検査 |
| generated_cover | ContextFamily×Set(AtomSet)×EquationFamily→Cover | seed閉包の族に、まだ収容されない各equationのsupport閉包と未被覆singleton閉包を追加。等しいpatchのみ重複除去。大きいpatchで小さいpatchを削除しない |
| context_map | Context×Context×Fn(ContextPoint,ContextPoint)→ContextMap | carrier上の全写像、baseへの可換性、observable制限を検査 |
| overlap | Context×Context→Overlap | 共通baseへの包含のpullback。空supportを保持 |
| chart | Context×Set(T)×Fn(T,FactRef)→Context | baseへの有限chart。全像がbase内。supportは像、carrier=T、structureはbaseから引戻す |
| pullback | Context×Context→Overlap | 同じbaseへのchart mapのfiber product。carrierは同像の順序対。包含時だけ集合交差と同型 |
| cover_charts | Context×Set(Context)×EquationFamily→Cover | 有限chart族の像がbaseを覆い、各equationの全operandを保つliftが少なくとも一chartに存在するか有限列挙 |

contexts は有限だが指数的になり得る。遅延生成は許すが、途中の列挙を全体と呼ばない。
cover の対象 equation family は明示する。経路の三角形を発見したことは、三重重なりや
2-cell を生成する規則ではない。セル・面の関係は原始操作の語と Law の関係式から作る。

上記の包含context上では union cover と依存閉包が生成する topology を使う。
一般chartについては生成coverから恒等・pullback・合成に閉じる生成 topology を使う。
あるcoverが生成されたことと、係数/状態の層条件・acyclicity は別の条件である。

## 6. 加群、係数、複体

| 名前 | 署名 | 意味と条件 |
| --- | --- | --- |
| free | Ring×Set(T)→Module | 添字T上の自由加群 R^T。RingはQ/Z/Fpのliteral。返り型のKをこのliteralから静的に決める |
| vector | Module×Fn(T,K)→Vector | free module の添字ごとの値。商/部分加群には下記写像を経由 |
| basis | Module×T→Vector | free module の指定添字の単位ベクトル |
| zero | Module→Vector | 零元 |
| vector_add, vector_sub | Vector×Vector→Vector | 同一module内 |
| scale | K×Vector→Vector | 係数環一致 |
| coord | Vector×T→K | free moduleでの指定添字係数 |
| linear | Module×Module×Fn(T,Vector)→ModuleMap | 第1引数freeの各生成元の像から線形延長。外部行列入力はない |
| image, kernel, cokernel | ModuleMap→Module | 実際の部分/商加群と構造写像を保持 |
| quotient | Module×ModuleMap→Module | mapの終域が第1引数。imで割る |
| inclusion, projection | Module→ModuleMap | kernel/imageの包含、cokernel/quotientの射影。該当型以外はinvalid_construction |
| induce | Module×Module×ModuleMap→ModuleMap | 提示の生成元に対するmapから関係保存を検査し部分/商上へ誘導 |
| map_apply | ModuleMap×Vector→Vector | 域一致 |
| map_compose | ModuleMap×ModuleMap→ModuleMap | g∘f |
| map_equal, is_iso | ModuleMap×ModuleMap→Proposition、ModuleMap→Proposition | 生成元上等値、核と余核が零 |
| complex | List(Module)×List(ModuleMap)→Complex | degrees 0..n、隣接d、d²=0を検査。map数=n |
| cohomology | Complex×Z→Cohomology | degree kのker d / im d。通常の有限complexは端で零微分。k<0またはk>last_diagnosable_degreeは不正構成 |
| class | Cohomology×Vector→Class | 指定degreeのcocycle条件を検査 |
| class_zero | Class→Proposition | 境界としての補正または非零証拠を計算 |
| cochain_map | Complex×Complex×List(ModuleMap)→CochainMap | 同degreeの写像、dとの可換性を検査 |
| cohomology_map | CochainMap×Z→ModuleMap | 商上の実写像 |
| coefficients | ContextFamily×Fn(Context,Module)×Fn(ContextMap,ModuleMap)→CoefficientSystem | 制限は包含/指定chart射だけで評価。ContextMap U→Vに対し制限はM(V)→M(U)。恒等・合成を全有限contextで検査 |
| cech | Cover×CoefficientSystem×Z→Complex | degree 0..n+1まで構成しdegree≤nの診断に必要なdを持つ。n≥0 |

cech は包含の monomorphic cover に **increasing-index** 規約を用い、
`(dc)_(i0…ik+1)=Σ_j (-1)^j res(c_(i0…îj…ik+1))`。
空overlapの係数も実際に計算し、勝手に零としない。
一般chart coverには ordered tuple（重複添字あり）と反復fiber product を用いる。
結果に規約を記録する。順序は表示のためのcanonical参照順、並替え時の符号を保持する。
有限Čech群を sheaf cohomology と呼ぶには別の比較定理の条件が要る。

Z では Smith normal form を使い、自由rankだけでなくtorsion invariant factorも返す。
有限体では p を保持する。有限の式による presentation は次の演算で保持する。
`core/presentation : EquationFamily→Presentation` は、式の型・演算signature・変数・
生成元・関係式をそのまま有限提示にする。一般の非線形Q式も保持できる。自由操作語と経路関係はCoreが保持する。
これは零点や商の判定結果ではない。非対応の商・可解性計算は式を失わず未決を返す。

係数変更は比較写像と適用条件を持つ別計算として保持する。有理係数の零性を
整数係数へ戻す場合は、係数比較と零性反映の条件を確かめる。

## 7. 局所状態、貼り合わせ、修復

| 名前 | 署名 | 意味と条件 |
| --- | --- | --- |
| states | ContextFamily×Fn(Context,SolutionSet)×Fn(ContextMap,AffineMap)→StateSystem | 制限が解を解へ写すこと、恒等・合成を検査。有限解族は写像を有限表から生成する `finite_states` を使う |
| finite_states | ContextFamily×Fn(Context,Set(T))×Fn([ContextMap,T],T)→StateSystem | 有限状態の制限を全列挙で検査 |
| sheaf_condition | Cover×StateSystem→Proposition | 重なりで一致する局所族への大域制限が全単射。有限列挙またはアフィン解空間の核・余核で決定 |
| descent | Cover×CoefficientSystem×StateSystem×Fn(Context,ModuleMap)→Descent | 下の条件を検査し局所差・cocycle・商類を構成 |
| obstruction | Descent→Class | 対象の具体的な局所差の類 |
| glue | Cover×StateSystem→SolutionSet | 相性条件付き局所解集合から大域解集合を構成。制限による対応も保持 |
| repair | Descent→Repair | 障害類が零なら補正して貼り合わせ、元の全方程式へ再代入。非零なら存在命題の反証を伴うinvalid_construction |
| state_compare | StateSystem×StateSystem×Fn(Context,StateMap)→Reading | 局所の意味側と方程式側の原始生成規則から作る対応。制限と可換、全域・一意性・可逆性を個別に検査 |
| semantic_repair | Repair×Reading→Repair | Readingが独立に作られた意味状態との同型で、局所/大域対応を保存するとき実際の意味状態へ運ぶ |

v0.6.0 の descent は加法的な有限表示係数とアフィン状態のtorsorを扱う。
第4引数は係数から状態のambient moduleへのembedding。単射、像が同次解全体、
制限との自然性を検査する。各patchの局所非空性、差が係数内にあること、加法作用の自由性・推移性、
制限との可換性、当該coverの層条件を検査する。明示したembeddingと状態ambient moduleの加法から作用を作る。これらの構成が足りない場合は sealed Descent を作らない。

局所解 s_i を内部で一つ構成し、c_ij=s_j|-s_i|、d c=0、変更 s_i+t_i による差 d t を計算する。
類の選択独立性を保持し、c=d b を解けたとき s_i-b_i を貼り合わせる。
Repair は具体的状態とその全解集合、使用した作用、元の式への代入、snapshot modeを持つ。
方程式側だけで作った Repair.kind は `equation`、意味側との比較を検査したものは `semantic`。
実コードを変更したことはこの値の意味に含めない。
貼り合わせの一意性は固定した整合局所族についてのものであり、大域修復の全解集合が
一元であることとは別である。

## 8. Reading、診断保存、追加観測

| 名前 | 署名 | 意味と条件 |
| --- | --- | --- |
| reading | Set(T)×Fn(T,U)→Reading | 有限域Dと読みfから像C=f(D)、全域有限StateMap D→C、全fiberを生成 |
| sufficient | Reading×Fn(T,V)→Proposition | 同じreading値を持つ任意の二対象で、指定Law評価値Vが等しいか。Bool成否だけへの圧縮をしない |
| sufficient_quotient | Set(T)×Fn(T,V)→Reading | D上の評価同値類BをSet(T)として作り、C:Set(Set(T))と全域有限StateMap q:D→Cを生成 |
| compare_diagnostics | CochainMap×Class×Class→DiagnosticComparison | H1写像、kernel、cokernel、指定類の像の一致を別々に計算 |
| preserves_diagnostics | DiagnosticComparison→Proposition | H1写像が同型かつ指定類が対応する |
| distinguish | Reading×Fn(T,V)×List(Fn(T,U))→ObservationPlan | 下記の有限識別計算 |
| needed | T→ObservationPlan | 未決の依存Holeと、必要とするquery/式/source位置。数学的最小性は要求しない |

Reading は何の有限域かを値に保持する。T/UはSet適格型、VはSet適格型または§12のLawValuesとする。
有限表のkey・像・fiber・Vの比較にはSetの要素同一性を使い、LawValuesだけは§12の評価等値を使う。
sufficient/distinguishはkind=finiteのReadingだけを受け取り、Fnの引数型をそのdomainの要素型と照合する。
修復存在を評価値に使う場合は core/decide(inhabited(...)) を使う。Law十分性だけから係数やcoverの比較を作ったと
扱わない。compare_diagnostics は比較写像そのものを引数として導出し、単にrankが等しいことを
同型の根拠にしない。異なるcoverには実際のrefinement/chart対応と誘導cochain mapが必要。
H¹写像の同型性と、比較写像の錐全体の非輪状性は別の条件である。

distinguishの第3引数は観測関数のListである。順番は観測候補の意味ある優先順であり、全候補を保持する。
各候補の評価は原始fieldから行い、現在同じreadingを持つがLaw評価が違う対を生成する。
その各対を分離する観測候補の集合を求め、包含極小な観測候補部分集合を全列挙する。
同数の候補を一つだけ最良としない。最小性の範囲はこの有限候補Listに限る。
Holeで候補評価ができなければ未決とし、そのfieldの観測要求へ戻す。
修復存在をVに使うときは、原始操作から構成した修復の存在を評価する。

finite Readingはdomain D、codomain C=f(D)、map.source=D、map.target=Cを保持する。
fibersのpreimageはDの非空・互いに素な完全分割で、各imageはCに一度だけ現れる。
sufficient_quotientでは `B_x={y∈D | V(y)=V(x)}`、`q(x)=B_x` と一意に決める。
そのfiber行はimage=B_x、preimage=B_xであり、双方の型はSet(T)。評価値Vを商の元にしない。
空DではC:Set(Set(T))も空、mapの表とfibersも空で、評価Fnを呼ばない。
必要な評価・比較が欠測/非対応ならReadingを確定せず、その理由を返す。
商のmapは検査した有限表を持つStateMapとしてReadingより先に導出する。生成Fnや代表元選択は要らない。
projectでdomain/codomain/mapを取得し、state_applyで商の元を次の計算へ渡せる。
再利用はD、評価Fn、各比較を現在の二入力から再検査する。集合・有限表の表示順を意味に含めない。

## 9. 由来、条件、証拠

演算の正しい値を得るための条件は、
`{id, proposition, status, evidence, reasons}` として結果に持つ。
依存はPropositionのoperandsとNode.arguments、未決理由の依存はIssue.dependenciesに保持する。
条件statusは `established/refuted/undetermined`。Lawはstatusを読む演算を持たない。
条件の反証、実装していない算法、観測不足を一つのfalseへ潰さない。

出力の生成元・行列・微分・証人は、原始fieldとLaw式から再構成可能でなければならない。
Lawのliteralに観測件数・特定ID・対象固有の分割を埋めた場合は、意味上の入力規則違反である。
型検査はRef literal・sealed値・外部実行を機械的に拒否する。
巧妙な言い換えを含む意味的な不正を自動認識したとは主張しない。

## 10. v0.6.0 の決定表

| 問いの形 | 必須の決定手続き | 完了時の証拠 |
| --- | --- | --- |
| 完全な有限集合・有限型全代入・有限木fold・有限閉包 | 全列挙、構造再帰、有限不動点 | instance と値/反例 |
| Qの全代入に関するアフィン等値 | 係数正規化 | 零係数、または零/単位代入による反例 |
| Q/Fpの有限線形系 | 正確な消去 | 解集合、または左零化子λでλD=0, λb≠0 |
| Zの有限線形系・有限表示加群 | Smith normal form | unimodular変換、整除条件、解または整除違反 |
| 上記係数のkernel/image/quotient/cohomology | 同じ正確な線形計算 | 実際の写像、自由部とtorsion |
| 有限のconfiguration/cover/chart/reading | 関係と写像の有限検査 | 保存条件、fiber、反例対 |
| 有限またはアフィンの状態/作用/貼り合わせ | 全列挙または線形計算 | 制限写像、kernel/cokernel、補正と再代入 |
| 有限carrierで尽くした経路商 | 合同閉包 | 同値導出または異なる同値類 |
| 自由圏の任意語の構文等値 | 恒等除去と平坦化 | 正規形 |
| 任意の関係を持つ無限coreの商等値 | v0.6.0では未対応 | 原始presentationとrequested propositionを返す |
| 非線形Q/Z方程式の一般可解性、任意の全ASTの保存 | v0.6.0では未対応 | 式と不足するdecision methodを返す |

演算は意味を持つ入力なら記号提示を返せる。`unsupported` は型の破壊や黙った近似を意味しない。
上表の必須算法は無制限の数学的計算では停止・正確性を要求する。実行予算の消尽は
`interrupted`。巨大だが有限の計算を「決定不能」と呼ばない。
任意のprogramの意味等値や任意の無限提示に停止を保証するAPIは設けない。

入力の定理証明やcompleted certificateを受け取って上表を越える結論を許可する機能はない。
新算法や一般定理を組み込むときは、semantics版の固定規則として導出条件とともに追加する。

## 11. 形状を持つ計算の共通規則

カタログの Module/Vector/ModuleMap 等は同じ係数型Kで添字付けする。
freeのRing引数はliteralに限り、coordの返り型はVector<K>のKから決まる。
生成元の添字型は構成時に保持する。vector/basis/linear/coordの関数域・添字が
その型と一致するかは構成条件で検査する。異なる添字型の値を文字列へ変換して一致させない。

状態域は値の型とcarrierを対で保持する。terms方程式の型はTermSignatureのparametersのpack、
carrierはその型の全値。affine方程式の型はVector<K>、carrierはmap.sourceの加群の元全体である。
これは解集合へ制限する前の状態域であり、required違反の状態も含む。
term_mapの始域はparamsのpackの全値、終域は返り型の全値。affine_mapは両端Moduleの全元、
finite_mapは指定したSet(T)/Set(U)を両端carrierとする。合成は最初の始域と最後の終域を保持する。
carrier一致は同じ値型を必須とし、型全体は型の一致、Moduleは意味identity、
有限集合はSetの要素同一性による外延等値で検査する。有限集合と型全体/Moduleの比較は、
後者が有限ならその全元を列挙して照合する。無限なら不一致、必要な列挙算法が非対応なら
unsupported_algorithm、欠測ならmissing_observation。型の違いや確定した不一致はinvalid_construction。
同次元・同型というだけでは一致せず、対応を明示的なStateMapとして構成する。

operation(name,A,B,candidate,action)はcandidateの端点をA/B.configurationと、
actionの始終carrierをA/B.equationsの状態域とそれぞれ照合してからOperationを作る。
hom_conditionの成否が未確認でも端点の合う候補操作は作れるが、端点の不一致を保留したOperationは作らない。
state_thenも同じcarrier一致規則を中間に適用し、合成したOperationは合成後の両端でこの条件を満たす。

SolutionSetは空の場合もstate_typeとdomainを保持する。solveでは元の方程式の状態域、
solution_imageではStateMapの終域、glueではbaseの状態域、SetExpression.kind=finiteでは指定Setのcarrierを用いる。
solution_forall/existsのFnはちょうど一引数、引数型はstate_type、返り型はPropositionとする。
前者の型が違えばinvalid_construction、arity/返り型の静的違反は入力typeエラー。
Fnはcarrierを型引数に持たないため、domainへの所属を確かめた解だけを渡し、body内の写像・座標の
所属条件は各解への適用時に検査する。空解集合でも型・arity・返り型の照合を先に行い、
それを通ればbodyを評価せずforall=true/exists=falseを返す。

law_homは上記Operationの端点条件を保持する。ArchitectureのEquationFamilyは、各側で共通の状態signatureを持ち、残差を
instance添字の自由加群へ並べる（module値方程式ならその残差module）。operationのactionはsource状態からtarget状態へのStateMap、
hはsource残差加群からtarget残差加群へのModuleMapである。原始FactRef写像だけから
状態の作用を補わない。非アフィン作用の等値に算法がなければunsupportedを保持する。

coefficients/statesの第1引数ContextFamilyはbaseと依存閉包規則を持ち、fnは純粋な
局所構成則として任意の有限Context/ContextMapを引数に評価される。包含族については
全context・全包含・全合成を検査する。chartを用いるcechは要求次数n+2までの反復pullback、
面写像、必要な合成を有限diagramとして生成し、そこで値・制限・可換性を追加検査する。
結果に検査diagramを保持し、未生成の全site上の層条件を成立と呼ばない。
ContextMapはcarrier上の写像を持つため、同じ端点の平行射も区別する。

AtomSetは原始位置の集合であり、supportには要求された未観測slotも現れる。
configのfamilyにはこのうち実在するsubject/Atomだけを入れ、未観測slotはrequirementsに
保持する。関係の端点が未観測slotならその関係構成はmissing_observation。
不足を架空の原始Atomとして追加しない。

## 12. 状態作用と公開射影

### 12.1 StateMap と状態への適用

StateMapはterm/affine/finiteの三種類の作用と、その合成を保持する。

| 名前 | 署名 | 意味 |
| --- | --- | --- |
| term_map | Term(A…,B)→StateMap | 原始型のpack(A…)からBへの作用。0引数はUnit、1引数はA、2以上はTuple |
| affine_map | AffineMap<K>→StateMap | 指定source/target Module上のアフィン作用 |
| finite_map | Set(T)×Set(U)×Fn(T,U)→StateMap | 全域・像の所属を全列挙で検査した有限作用 |
| state_then | StateMap×StateMap→StateMap | §11の中間carrier一致を検査したg∘f。両外端の状態域を保持 |
| state_equal | StateMap×StateMap→Proposition | 全状態での作用等値。対応済み算法以外は未対応 |

状態への適用式は `["state_apply", ResultType, MapExpr, InputExpr]`。
実際の始域型・入力所属と終域型を検査してから適用する。
EquationFamilyは `{kind:"terms",instances:...}` または
`{kind:"affine",map:AffineMap,rhs:Vector,role:"required"|"definition"}`。両者とも共通状態域と残差を持つ。
solveは前者のTerm共通引数のpackまたは後者のModuleの元を未知数として解く。
通常のequationsはterms、affine_equationsはaffineを構成し、入力に依存する次元を静的な
原始Tuple型に押し込めない。

### 12.2 構造の公開field

projectできるfieldを次に限定する。各値の実際の型はresultの型付き構造に保存し、
Exprに明示した要求型と照合する。数学的な構造の射影であり、表示・statusの読出しではない。

- Architecture: configuration, equations。Configuration: family, relation, identification。
- Operation: source, target, atom_map, action。MapCandidate: source, target, pairs。
  ConfigurationHom: candidate。LawHom: operation, underlying, residual_map。Span: left, right。
- Context: carrier（Set(ContextPoint)）, support, axes（Set(Text)）, observables。axesの各値はpredicateの完全修飾axis名。ContextMap: source, target。
  Overlap: pullback（Context）, left_projection, right_projection（ContextMap）。
  Cover: base, patches（Set）, equations。
- ModuleMap: source, target。AffineMap: linear, offset。Vector: module。
  Complex: modules/differentials（degree順List）。CochainMap: source, target, components（degree順List）。
  Cohomology: module, cycles, boundaries。Class: cohomology。
- CoefficientSystem/StateSystem: contexts。Descent: cover, coefficients, states, complex, obstruction。
  DiagnosticComparison: cochain_map, cohomology_map, kernel, cokernel, class_matches。
  Repair: solutions, descent, comparison（Option Reading）。Reading: domain, codomain, map。

Readingのdomain/codomainはfiniteならSet(T)/Set(U)、stateならStateSystem。
mapはfiniteならStateMap、stateならFn(Context,StateMap)である。要求型との不一致はinvalid_construction。
semantic_repairはkind=stateのReadingを要求し、finite readingを状態比較として用いない。

Moduleの表示基底、Vectorの代表座標、Classの代表元、Repairの便宜的なwitness、
Descentのlocal_sections、Propositionの判定状態は射影できない。
ContextMapのcarrier作用は `core/context_apply : ContextMap×ContextPoint→ContextPoint`。始域への所属を検査する。
係数/状態の値を取り出す演算は
`core/coefficient_at(CoefficientSystem,Context)→Module`、
`core/restriction_at(CoefficientSystem,ContextMap)→ModuleMap`、
`core/states_at(StateSystem,Context)→SolutionSet`、
`core/state_restriction_at(StateSystem,ContextMap)→StateMap`。
有限状態もSolutionSetのfinite表示へ統一し、これらの演算は記録した構成則を指定contextで評価する。

### 12.3 加群の誘導写像と因子分解

induce(M,N,f)のfは、MとNを提示する自由加群間の写像。出力は
M→Nであり、Mの各関係の像がNの関係部分加群に属することを検査する。
部分加群からの誘導ではMの包含を先に合成し、その像がNに含まれることを検査する。
その際の必要な自由提示は `core/presenting_free : Module<K>→Module<K>`、
`core/presenting_map : Module<K>→ModuleMap<K>` で取得する。後者は自由提示からの標準全射。
表示生成元を名指す入力は許さず、原始生成元上の写像から因子分解する。
因子分解に使う `core/factor : ModuleMap×ModuleMap→ModuleMap` は、第1引数pが全射、
第2引数fが同じsourceを持ちker p⊆ker fであることを検査し、一意なhでh p=fを返す。

### 12.4 診断比較の次数

compare_diagnosticsはsource_class/target_classがdegree1で、cochain_mapの両端の
複体とそれぞれ一致し、双方のlast_diagnosable_degree≥1であることを検査する。
次数nで打ち切ったcechのn+1次を、零微分で埋めて診断することはない。

### 12.5 Context の点と制限写像

Contextの公開carrierは常にSet(ContextPoint)。
`core/context_points : Context→Set(ContextPoint)` と
`core/point_fact : ContextPoint→FactRef`（baseへの像）を持つ。
chartの元のT、包含contextのFactRef、pullbackの左右のContextPoint対はpointのlabelとして
保持し、`["point_value",Type,PointExpr]` で要求型を検査して読める。
反復pullbackでも公開point型は変わらないため、単相のFn(Context,Module<K>)で
全chartの係数を作れる。ContextMapの平行射はpoint上の作用で区別する。

`core/lift : ModuleMap<K>×ModuleMap<K>→ModuleMap<K>` は、第1引数iが単射、
第2引数fが同じtarget、im f⊆im iを検査し、一意なhでi h=fを返す。
kernel係数の制限は、ambient制限と元のkernel包含を合成してから、先のkernel包含へliftする。
表示基底の読出しをこの構成の入力に要求しない。

### 12.6 方程式の局所support

free moduleの生成元には、入力添字値の原始supportを保持する。affine_equationsの
残差moduleが自由なら、各原始生成元に対する成分式を核が構成し、局所化のequation indexにする。
各成分のsupportは、非零係数の変数座標のsupport、係数式と右辺成分の原始operand、
その参照閉包。未知の係数も候補支持として保持し、零とみなして除去しない。
全域のfree moduleを構成しただけで全座標を各成分のsupportへ加えない。
contextへの制限は、そのcontextにsupportが収まる座標・成分を保ち、値の射影を作る。
商の残差moduleでは表示行ごとに分解せず全module値方程式を一つのinstanceとして扱う。

### 12.7 Term の残余化

termによる残余化は、formal paramsに依存しないfield等を先に値/captureとして計算する。
残ったbodyは原始Termの純粋部分に属さなければinvalid_construction。
formal Ref変数に応じてfieldを読む処理を、純粋Termの中へ隠さない。
deriveでclosureを計算し終えた原始Set値はcaptureできる。formal引数に依存するclosureが
bodyに残る場合はinvalid_constructionであり、純粋Termへ昇格しない。

### 12.8 方程式のsignatureと残差

TermSignatureの唯一のliteral encodingは `{parameters:[P,...],result:K}`。
Pは原始型、KはQ/Z/Fp。Termのparams順と同じで、空のEquationFamilyにも状態域を与える。
0引数のstateはUnit、1引数はその型、2以上はTupleとする。このpack規則を
term_map、state_apply、solve、全ての方程式評価で共用する。
`["residual",K,FamilyExpr,StateExpr]` は指定stateの左辺−右辺を、
termsならinstanceを添字とする自由Module<K>、affineならmapのtarget Module<K>の
Vectorとして返す。Kとstate域を実際のfamilyと照合する。
EquationFamilyの公開fieldは `residual_space`（Module<K>）。
Symbolic座標νはinstance指示基底、residual εは上記の値とし、νを自身で割ってε=0とはしない。

### 12.9 LawValues の比較

`core/law_values : EquationFamily→LawValues` はLaw評価関数の比較に用いる値を構成する。
LawValuesは型付きの残差関数族を保持するsealed型。termsではkind、TermSignature、index_type、
instance keyの集合を、affineではkind、始域Moduleと残差Moduleの意味identityを比較の形とする。
形が違えば異なる評価値とし、形の差を証拠にする。roleや関数を構成した式のidentityは比較に含めない。
形が同じ場合に全状態での残差一致をterm_equal/線形写像等値の必須算法で検査する。
sufficient/sufficient_quotient/distinguishのVにはSet適格型に加えLawValuesを許す。
一般非線形で比較できなければunsupported_algorithm、欠測ならmissing_observation。
残差の不一致は具体的keyとstateを証拠に返す。形の不一致に架空のstate反例を要求しない。
LawValuesの比較をBool成否だけの一致へ置換しない。LawValuesはSetの要素型にはしない。

## 13. 構成則の評価と特殊な引数

通常のcallは引数を評価してから実行する。and/orは短絡、all/any/forall/existsは
有限instanceごとの確定結果を集約し、一つの確定した反例/証人で結論できる。
`support` と `needed` は値がblockedでも導出式と原始依存を受け取り、その依存を読む。
neededの完全な依存探索自体が予算で止まった場合はObservationPlanを確定値として返さず、
部分的なrequirementsをblocked nodeのpartialに保持する。
観測を増やしても解決しない理由はObservationPlan.blockersに保持する。
必要な観測が空という値と、依存探索をしていない状態を区別する。

affineのQ/Z認識は、formal Vector座標のadd/sub、既知scalarによるmul/scale、
既知ModuleMapの適用、vector/basis/zero、既知有限indexのmap/sumを展開して正規化する。
入力に依存する分岐は、両枝が同じ正規形なら消去し、そうでなければ未対応とする。
未知の観測係数を定数として確定しない。検査できた非アフィン性は構成条件の反証、
認識できない式はunsupported_algorithm。Fpの有限域では全値でアフィン条件を検査できる。
term_equalのQ上アフィン認識も同じscalar部分を用いる。等値/線形計算の完了保証は
この正規化で得る部分、有限全列挙、Zの有限線形系に対して課す。

statesのAffineMap制限はaffine_mapへ、finite_statesの全域表はfinite_mapへ変換し、
StateSystem内部と出力ではStateMapへ統一する。状態の全域carrierに合わない制限は
invalid_construction。conditionの必要な比較を決定できなければ、その理由を返す。

coreの操作はconfiguration上の射と状態上の作用を共に持つ。coreに渡す各Operationの
候補Atom作用はverify_homで成立していること、始終域が指定object集合に属すること、
§11のconfiguration・状態域の端点条件を満たすことを検査する。
未確認候補はOperationとして比較できるが、coreの生成射へ昇格させない。
自由coreのobjectは指定された対象族、morphismは型の合う全有限語であり、恒等・合成に閉じる。
新しいconfigurationや候補対象を作るLawのderiveは、同じ原始familyから作ったArchitectureを
その対象族へ加える。objectの列挙と全操作語の列挙は同じではない。
