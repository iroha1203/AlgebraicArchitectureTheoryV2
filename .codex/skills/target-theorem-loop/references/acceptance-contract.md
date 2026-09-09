# Target Theorem Acceptance Contract

rootの選定・実装と、標準PR review後の統合判定に適用するfail-closed契約。
適用版は[カードの読み取り手順](target-goal-contract.md#適用版の特定)で固定する。
カード固有の要求とこの検査基準を併せて判定し、旧カード固有の構成経路やwitnessを別GOALへ追加しない。

## 要求と証拠の対応

- 固定targetの全条項から、入力、量化順、対象条件、構成義務、結論、固有のwitness条件を
  抽出し、条項ごとにLean宣言・定義・証拠へ対応させる。成果物名の一覧だけでは対応としない。
- 固定targetが要求する一般定理、名前付き入力からの構成、その両者の接続をそれぞれ照合する。一般部分だけの証明や
  固定例だけの確認を、全targetの完了にしない。未対応の要求も未完了として残す。
- 全方向・全構成の完了判定と記録は[completion ledger](completion-ledger.md)に従う。
  カードを短くすることは、参照した監査・独立最終査読・同期要件の省略を意味しない。

## Statementとpremise

- 自然言語targetとLean statementの量化、対象、係数、site/cover、有限性、方向、結論強度を一致させる。
- 比較する定義とinstanceを展開し、対象のmembership、射の範囲、等号・同値関係の中に
  結論や追加制約が隠れていないかを確認する。対象だけが同じでも、射を減らした圏は同じ量化域ではない。
- total射・依存構造の等号は、指定された全計算成分とtransportを含む等号として照合する。
  忘却後のobject mapの等号やproof-field irrelevanceだけを、その代替にしない。
- material premiseを`ambient-boundary`、`direction-hypothesis`、`discharge-required`、`conclusion-equivalent-risk`へ分類する。未申告premiseは未放電とする。
- `ambient-boundary`に残せるのはGOALが入力幾何として固定したdataだけである。結論相当のfaithfulness、exactness、descent、effectivity、coherence、vanishing、adequacyを入力境界へ移さない。
- material premiseから、その役割を割り当てた構成・保存則・結論までの使用経路をproof termで
  確認する。単なる引数への出現、未使用の`have`、使わないcertificate fieldはproof-useではない。
  全前提が全最終定理で直接使われることは要求せず、役割ごとの依存経路を追う。

## 放電の資格

`discharge-required`を放電済みと呼べる証拠は次のいずれかに限る。

1. GOALの入力dataからcertificate/witnessを構成するLean theorem。
2. Leanで固定されたfinite witnessまたはconcrete construction。
3. 同じ強度を持ち、declaration hashとreview refを固定したpredecessor theoremからの導出。

explicit argument、typeclass、structure/certificate field、opaque membership、field accessorは放電ではない。certificateが結論成分を保持する場合、そのcertificate自身の生成定理とprovenanceを要求する。

一般補題で`direction-hypothesis`として保持する条件も、固定targetが具体的な入力からの導出を
求める適用箇所では`discharge-required`である。両者を別に台帳へ対応させる。
構成対象のstructureは必要な全fieldと依存するinstanceの出所を追い、別recordへ移した
未放電条件も同じ義務として扱う。先行定理は名前の一致だけでなくstatementと適用引数を読む。

## Route integrity

selected object、cover、sheaf、coefficient、complex、realization、certificate、class boundaryを使う場合、次を固定する。

- どの入力dataから構成したか。
- カードが許す入力選択、canonical/free construction、universal property、finite construction、
  review済みpredecessorのどれが選択を正当化するか。一意性はtargetが要求する場合に証明する。
- conclusion-side lawをfieldへ埋めていないこと。
- 固定targetが扱う構成・適用のnonvacuity/adequacy evidence。対象条件の展開によって、要求した
  実例や作用が空虚になっていないこと。一般定理が許す空の入力と、実例を要求する条項の空虚性を
  区別し、指定された非自明性をsingleton、自明relation、degenerate coverへの置換で消さない。
- differential、comparison、restriction、naturalityが定義展開または証明済みtheoremから出ること。

片方向theoremを同値として扱うこと、conditional package/wrapperをtarget本体として扱うこと、証明後にGOAL/reportを読み替えることは`rejected`とする。

構成経路が固定targetの一部なら、その経路から独立に生成した対象・射について指定の関係を
証明する。比較すべき出力を結論の等式から定義して構成義務を消すことや、全指定対象への
全射性を自分自身の像への全射性で置き換えることは認めない。固定していない証明方法や内部APIの
選択は許す。

## Witnessと成立判定

- 固定データと選択可能なデータを区別し、指定した同じ例で要求された条件が同時に成立するかを
  確認する。例の非空性、作用元の非恒等性、指定写像・成分への作用の非恒等性を区別する。
- 判定の対象が保存・反映・liftの全射性なら、それぞれを別に照合する。充満性から同型のliftを
  推論することや、有限例の結果を一般分類とすることは認めない。
- 証明・反証のどちらも達成とする条項では、成立・不成立それぞれについてカードが事前に指定した
  具体的証拠を、実際の判定結果に応じて要求する。
  `Classical.em`、`not_forall`、choiceによる場合分けや存在の提示だけでは、指定データでの決定・評価・
  構成を放電しない。通常の非計算的存在証明は、targetがその証拠強度を許す場合に使える。
  固定主張への反例を達成として認めることが事前に定められていなければ、ループの反証停止規則で扱う。
  達成として認める結果を後から追加しない。

## Evidenceと依存

- claim、premise、gateへ対応させる対象全宣言のownerについてfocused elaboration、
  `#print axioms`相当のkernel抽出、placeholder scanを固定する。全import closureのsource elaborationを
  要求せず、選択ownerを縮小して未確認claimを隠すことも認めない。
- main theoremだけでなく、spine、bridge、finite witness、certificate construction、instance/import chainを依存DAGとして追う。
- 人間がtracking Issueへ明示的に固定したcompletion方法に限り、lock manifestでcommitとsourceを固定した
  外部Lake packageの既存artifactをdependency trust premiseとして利用できる。このpremiseは
  sourceからartifactを再生成した証拠でも、数学premiseの放電でもない。
- 同一repoの非選択artifactはruntime dependencyに限る。material claim、premise、中心routeを支える
  repo内宣言はfocused ownerとして選択するか、exact owner・declaration digest・既受理review refを持つ
  reviewed predecessorとして対応表へ列挙する。選択宣言のvalueから到達するrepo-local terminalを
  この二経路の外で受理せず、非選択artifactだけで監査済みと扱わない。
- dependency policy、承認Issue/comment、artifact三分類、`source_build_claim: false`をpacketへ固定する。
  全Research moduleを回るfile loopやaggregate/full buildをcompletion receiptのために実行しない。
- 新規`axiom`、許可されない`sorry`/`admit`/`unsafe`、本体からResearchへのimportは受理しない。
- rootのpacket、PR本文、report、ledger、CIは監査対象であり、数学claimの一次証拠ではない。
- 中心claimの`cannot-determine`または`unchecked`はcheckpoint/blockedへ倒す。

## Regression gate

標準PR review後、rootが次の各scenarioを固定headのreview evidenceと実体へ適用する。

| Scenario | 必須判定 |
| --- | --- |
| targetより弱いstatement、対象縮小、方向欠落 | `rejected` |
| 必須条項・具体的適用・一般定理との接続に対応証拠なし | `proof-checkpoint` |
| 全成分の等号を忘却後の等号で代替 | `rejected` |
| 結論相当premiseを引数/field/membershipへ移動 | `rejected`または`proof-checkpoint` |
| certificateを受け取るだけで生成定理なし | `proof-checkpoint` |
| material premiseがproofで未使用 | `proof-checkpoint` |
| target-fitting selectionまたはvacuous witness | `rejected` |
| 一般補題の方向仮定を具体的入力でも受け取るだけ | `proof-checkpoint` |
| 指定作用の評価や成立判定を形式的な存在・場合分けだけで代替 | `proof-checkpoint` |
| 片方向theoremをequivalence/completionと表示 | `rejected` |
| support/dependency theoremが未監査 | `proof-checkpoint` |
| CI green、merge、wrapper、定理名の存在だけ | completion不可 |
| 中心claimに未確認あり | `Blocked / cannot determine`または`target-proof-checkpoint` |

観測判定と証拠を同じ固定headのPRコメントへ残し、completion candidateではfinal packetにも入れる。未実行・不一致・証拠なしは合格にしない。
