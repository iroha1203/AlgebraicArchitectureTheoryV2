# ArchSig gate-policy authoring guide

`archsig gate` は `archsig-measurement-packet/v0.5.4` の verdict を、CI 管理者が author した
`archsig-gate-policy/v0.5.4` で制度的 action に写す。measurement verdict 自体は変更しない。

## Policy shape

`absolute` rule は次の 6 写像をすべて明示する。

- `measured_zero`
- `measured_nonzero`
- `unmeasured`
- `unknown`
- `not_computed`
- `violated_assumption_dependency`

action 語彙は `pass`, `pass_with_boundary`, `block` の 3 つだけである。
`unmeasured`, `unknown`, `not_computed` は plain `pass` にできず、`violated_assumption_dependency` は必ず `block` にする。

`introduced-by-change` rule は comparison report があるときだけ有効になる。comparison 不在時は
`not_applicable` として skip され、pass には丸めない。

structural verdict が空でも、analytic reading が `silence_by_design` boundary に明示的に束縛されている場合は、gate はその reading を `not_computed` の gate row として扱う。`boundaryKindOverrides` が適用された row は `pass_with_boundary` になり、analytic value 自体は変更しない。
`ag.saga-comparison` の `silence_by_design` は、既存の structural row またはこの analytic fallback row がある場合だけ supplemental gate row として加わる。comparison silence だけで structural verdict が空の packet は `NOT_EVALUABLE` になる。

starter template:

- `tools/archsig/tests/fixtures/ag_measurement/gate_policy_conservative.json`

ArchViewで読む場合は、同じanalyze出力ディレクトリへ`archsig-gate-report.json`を書き出す。
viewer-dataの`inputDigests.measurementPacket.sha256`とgate reportのdigestが一致するときだけ、
SAGA最終段にdecisionとper-row actionが表示される。未供給は沈黙として扱い、schema / digest /
action語彙の不一致はstatusに明示して反映しない。

## Non-claims

- gate は analytic 値の閾値判定ではない。
- gate は class transport、改善、修復、同一障害の持続を主張しない。
- `NOT_EVALUABLE` は pass でも block でもない。
