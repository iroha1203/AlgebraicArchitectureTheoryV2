# Target Theorem Acceptance Contract

rootの選定・実装と、標準PR review後の統合判定に適用するfail-closed契約。

## Statementとpremise

- 自然言語targetとLean statementの量化、対象、係数、site/cover、有限性、方向、結論強度を一致させる。
- material premiseを`ambient-boundary`、`direction-hypothesis`、`discharge-required`、`conclusion-equivalent-risk`へ分類する。未申告premiseは未放電とする。
- `ambient-boundary`に残せるのはGOALが入力幾何として固定したdataだけである。結論相当のfaithfulness、exactness、descent、effectivity、coherence、vanishing、adequacyを入力境界へ移さない。
- main theoremとsupport theoremのproof termでmaterial premiseが実質的に使われることを確認する。

## 放電の資格

`discharge-required`を放電済みと呼べる証拠は次のいずれかに限る。

1. GOALの入力dataからcertificate/witnessを構成するLean theorem。
2. Leanで固定されたfinite witnessまたはconcrete construction。
3. 同じ強度を持ち、declaration hashとreview refを固定したpredecessor theoremからの導出。

explicit argument、typeclass、structure/certificate field、opaque membership、field accessorは放電ではない。certificateが結論成分を保持する場合、そのcertificate自身の生成定理とprovenanceを要求する。

## Route integrity

selected object、cover、sheaf、coefficient、complex、realization、certificate、class boundaryを使う場合、次を固定する。

- どの入力dataから構成したか。
- canonical/free construction、universal property、finite construction、review済みpredecessorのどれが選択を一意に正当化するか。
- conclusion-side lawをfieldへ埋めていないこと。
- 空型、singleton、自明relation、degenerate coverへ退化しないnonvacuity/adequacy evidence。
- differential、comparison、restriction、naturalityが定義展開または証明済みtheoremから出ること。

片方向theoremを同値として扱うこと、conditional package/wrapperをtarget本体として扱うこと、証明後にGOAL/reportを読み替えることは`rejected`とする。

## Evidenceと依存

- 対象全宣言についてfocused elaboration、`#print axioms`、placeholder scanを固定する。
- main theoremだけでなく、spine、bridge、finite witness、certificate construction、instance/import chainを依存DAGとして追う。
- 新規`axiom`、許可されない`sorry`/`admit`/`unsafe`、本体からResearchへのimportは受理しない。
- rootのpacket、PR本文、report、ledger、CIは監査対象であり、数学claimの一次証拠ではない。
- 中心claimの`cannot-determine`または`unchecked`はcheckpoint/blockedへ倒す。

## Regression gate

標準PR review後、rootが次の各scenarioを固定headのreview evidenceと実体へ適用する。

| Scenario | 必須判定 |
| --- | --- |
| targetより弱いstatement、対象縮小、方向欠落 | `rejected` |
| 結論相当premiseを引数/field/membershipへ移動 | `rejected`または`proof-checkpoint` |
| certificateを受け取るだけで生成定理なし | `proof-checkpoint` |
| material premiseがproofで未使用 | `proof-checkpoint` |
| target-fitting selectionまたはvacuous witness | `rejected` |
| 片方向theoremをequivalence/completionと表示 | `rejected` |
| support/dependency theoremが未監査 | `proof-checkpoint` |
| CI green、merge、wrapper、定理名の存在だけ | completion不可 |
| 中心claimに未確認あり | `Blocked / cannot determine`または`target-proof-checkpoint` |

観測判定と証拠を同じ固定headのPRコメントへ残し、completion candidateではfinal packetにも入れる。未実行・不一致・証拠なしは合格にしない。
