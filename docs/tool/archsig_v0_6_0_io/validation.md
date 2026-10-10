# 構文・型・入出力の検証

以下の出力と反例表は仕様から定まる期待結果である。新しい処理系での実行による
適合確認は後続実装で行う。

## 1. 一つの Law、三つの入力

[Law](examples/law.json) は、一つのsnapshot内の名前付き有理数操作の全順序対について、
二つの合成の作用が等しいかを問う。原始語彙はOperationの存在とbodyだけである。
式の入力順は `then(f,g)=g∘f`。

| 入力 | 原始の式 | 出力の要点 |
| --- | --- | --- |
| [反証](examples/refuted.archmap.json) | f(x)=x+1、g(x)=2x | `affine/commute: refuted`。x=0でg(f(x))=2、f(g(x))=1。exit1 |
| [成立](examples/established.archmap.json) | f(x)=x+1、g(x)=x+2 | 4順序対すべての全Q代入で成立。`established`、exit0 |
| [欠測](examples/missing.archmap.json) | fの式だけ記録、gの存在は保持 | `undetermined/missing_observation`。missingは(sample,g,affine/body)。exit2 |

三入力の語彙bindingとLawは同じ。欠測例のgをx+2で補完すると成立、2xで補完すると反証になる。
補完対を観測の反例と呼ばない。端点の一致や同じsupportだけから二操作を同一視しない。

想定呼出しは次である。これは新CLIの仕様例であり、現存v0.5.x binaryのコマンドではない。

```sh
archsig run --archmap examples/refuted.archmap.json --law examples/law.json --out result-refuted
```

出力の `Answer` はquery、Proposition参照、status、証拠参照、scopeを持つ。
反証の `Evidence.kind=counterexample` には、型Qの値0の代入、二つの順序を持つ操作経路、
型Qの2と1、二つのbody Atomへの原始位置を保存する。
方程式の全Q量化はscope.domain=all_assignments、quantifiersにQ変数のforallとして残る。
欠測回答は同じ位置をmissingに持ち、provisionalな式を確定valueに置かない。

式を短く書くための独自入力フォーマットは追加していない。基本例の4ファイルはすべて通常のJSON。
入力の観測sourceは本文の二行の式を表す小さな実装例である。

## 2. 自己モデルの小さな構成

[自己Law](examples/self.law.json) と [自己Atom](examples/self.archmap.json) も同じ書式を使う。
SourceのVar/Lit/Add、IRのLoad/Const/Plus/Minusをdataで定義し、foldで変換と二つの評価を記述する。
原始入力はsource treeと候補の演算選択だけ。完成IR、行列、保存判定は入れない。

sourceはx+(1+2)。AddをPlusへ写す候補はx+3、Minusへ写す候補はx−(1−2)=x+1となる。
仕様上、同じLawが、前者の全Q代入での保存と、後者の反証（x=−1でsource=2、IR=0）を計算する。
snapshotはspecification由来であり、実装済みコンパイラの検証結果と混同しない。
この二入力は、自己モデルを型付きADT/構造再帰で表せることの短い確認である。

## 3. 短い反証的な検査

| 試み | 期待する判定と保持する情報 | 根拠 |
| --- | --- | --- |
| 欠測gをjoinで落とす | query未決、gを保持 | subjectから列挙しfield lookupを別に行う |
| 同じHole hの再読 | h−h=0は成立できる | slotのidentityを共有 |
| 2−hを非零多項式として反証 | h=2/3の補完で判断が異なるため未決 | 観測Holeと全称変数の区別 |
| none・[]・欠測の同一視 | Option不在、空の有限集合、Holeを分離 | 原始値のencodingと型 |
| 同じFactRefに二つの値 | invalid_input/duplicate_fact | 単一値predicate |
| 未約分有理数2/2 | invalid_input/type | Qの正規形 |
| 識別子を変えて違う結論を出す | 同型に沿う同じ判断 | ID文字列をLawから解析できない |
| 2z=1をQで解いてZの解とする | Qでは1/2、Zでは整除違反 | 係数環の型引数とSNF |
| 面の[e,e]をSetへ変換 | 係数2を保持 | Listの反復と符号付き和 |
| chart X={0,1}→{*} の二つの投影を潰す | p₁*≠p₂*、差は(0,1,−1,0) | ContextMapがcarrier作用を持つ |
| Lawの十分性から診断同型を付与 | 別の実cochain比較が必要 | sufficientとpreserves_diagnosticsを分離 |
| Čechを次数nで打ち切りH^(n+1)を読む | invalid_construction | last_diagnosable_degree |
| 旧resultのverifiedラベルを採用 | 現在の根から再検査/再計算 | 再利用は第三入力にならない |
| 未観測の候補を全部探索したとする | 量化域をfinite_modelに固定 | 有限候補族と任意の変更を区別 |
| 自己Lawの成功を原始Atomに戻す | sealed値・結果参照の入力を拒否 | 導出根の非循環性 |

三操作の局所例については、原始端点(p,q),(q,r),(p,r)から
`D=[[-1,1,0],[0,-1,1],[-1,0,1]]` を生成する。λ=(1,1,−1)はλD=0を満たす。
b=(1,1,3)ではλb=−1、b=(1,1,2)ではz=(0,1,2)を元の式へ代入できる。
この計算は [既存の局所・大域構成](../archsig_atom_law_engine/local_global_example.md)との
接続点の確認であり、行列を新しい入力欄に追加するものではない。

## 4. 仕様点検と実装検証の区別

仕様作成中には、JSONの一部の構文・型の点検と、固定例の算術・集合計算を行った。
自己モデルの数値確認は別のPython係数計算であり、Lawの `compile`、`source_eval`、
`ir_eval` を実行したものではない。

全DSLのparser・型検査器・solver・新CLI・出力の再読込みは未実装である。
期待結果との実行上の一致、全入力に対する型保存は後続実装の検証事項であり、
製品固有の未証明義務は [数学への接続](math_obligations.md#4-新仕様に残る証明義務)に示す。
現存ツールのcargo testやLean buildを、新I/Oの成立証拠にしない。

仕様作成中の独立点検では、入力/束縛/欠測、計算の型接続、wire/再利用を分担して確認した。
見つかったpureの間接効果、dataへの導出型混入、role衝突、query/defの循環、
係数型消去、一般chartの射、作用の欠落、出力型消去、DAG自己参照を仕様へ反映した。
これはPR公開後の正式tool-reviewに代わる合格判定ではない。

## 5. 後続実装の適合確認

実装者は上の三入力と反証表に加え、次を同じpublic CLIで確認する。

1. 入力のarray/object順だけを変更して、意味値が対応すること。
2. renameした原始IDの全単射を出力の対象・操作・反例へ運べること。
3. Z/Fpの線形問題、アフィン方程式の局所support、kernelへのlift、商からのfactorを接続できること。
4. 一般chartの二つの制限が別のcochain項になり、d²=0を検査すること。
5. 解なし、零類、修復値、意味側比較を別の型・条件として出力すること。
6. 不正入力・未対応算法・観測不足・予算中断・signal・I/O失敗の終了コードと結果を確認すること。
7. 改竄した再利用候補を破棄し、元の二入力からの結果が変わらないこと。
8. 全resultの型・参照・導出DAGを再読し、原始根と各条件へ到達できること。

これらは本仕様で決めた振る舞いの検査であり、実装時に新しいI/Oを選ぶための保留事項ではない。

## 6. 商・全域性・端点の短い適合例

次は後続実装が同じ意味を読むための反例表である。CLIで実行済みという意味ではない。

| 最小の入力/構成 | 期待結果 |
| --- | --- |
| 空のD:Set(Z)のsufficient_quotient | codomainは空のSet(Set(Z))、map/pairs/fibersも空。評価Fnを呼ばずestablished |
| D={0,1,2}、LawValuesが順にx、x+1、x | 商は{{0,2},{1}}。商元はSet(Z)、mapはStateMap、fibersのimage/preimageは同じ同値類 |
| 上の評価値を同じ式で別に構成、またはDの表示順を反転 | 同じpartitionと有限作用。式のidentityや代表元番号で商を変えない |
| LawValuesのsignature/key/残差Moduleが不一致 | 異なる評価値として別の類。形の差をevaluation証拠に保持 |
| 商に必要な一つのLawValues比較が非対応/欠測 | Readingを確定せずundetermined。unsupported_algorithm/missing_observationを保持 |
| pure(Unit)→Set(Z)のclosure({1},{},n↦{})、またはその間接呼出し/到達不能枝 | 静的typeエラー、invalid・exit65。effect={allowed:pure,found:derive} |
| queryのclosure({1},{},n↦{}) | check成功、runはundetermined/invalid_construction、partial・exit2 |
| pureのset式{x,x} / 入力Set値["1","1"] | 前者は{x}へ重複除去。後者は不正なSet encoding |
| A.configuration=Cだがcandidate.source=C'≠C。candidate自体は正しいhom | Operationを作らずinvalid_construction。作用が正しくても端点条件を省略しない |
| Aの状態域はQ全体、action.source={0,1}⊂Q | 同じ値型でもcarrier不一致でinvalid_construction |
| state_thenの中間Bool carrierが{false}と{false,true} | invalid_construction。後続のOperation/coreへ渡す値を作らない |
| 端点は一致するがcandidateの保存未確認 | Operationとして保持。law_hom/coreへの昇格時には保存成立が必要 |
| 空のQ解集合にFn(Z,Proposition)でsolution_forall | 空虚な成立の前に型照合しinvalid_construction |
| 空のQ解集合にFn(Q,Proposition)を適用 | bodyを呼ばずforall成立/exists反証。body用の架空のQ値を選ばない |
| 同じF2加群のzero(M)とvector_sub(v,v)、Z/2加群の代表0と2 | 同じ元として有限mapのkey/carrierを照合。親Moduleが異なる元は区別 |
| Context.axesをproject | Set(Text)。値は完全修飾axis名。Set(Z)要求はinvalid_construction |
| Conditionへ独自dependencies欄を追加 | 未知欄として結果schema検査で拒否。依存はNode.arguments/Proposition.operands/Issue.dependencies |

上の商の有限mapで、一行のpairのencodingは次である。これは生成結果の一部であり、第三入力ではない。

```json
{"type":["Tuple","Z",["Set","Z"]],"value":["0",["0","2"]]}
```
