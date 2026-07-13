# ArchSig gate-policy authoring guide

`archsig gate` は `archsig-measurement-packet/v0.5.2` の verdict を、CI 管理者が author した
`archsig-gate-policy/v0.5.2` で制度的 action に写す。measurement verdict 自体は変更しない。

## Policy shape

`absolute` rule は次の 6 写像をすべて明示する。

- `measured_zero`
- `measured_nonzero`
- `unmeasured`
- `unknown`
- `not_computed`
- `violated_assumption_dependency`

action 語彙は `pass`, `pass_with_boundary`, `block` の 3 つだけである。
`unmeasured`, `unknown`, `not_computed`, `violated_assumption_dependency` は plain `pass` にできない。

`introduced-by-change` rule は comparison report があるときだけ有効になる。comparison 不在時は
`not_applicable` として skip され、pass には丸めない。

starter template:

- `tools/archsig/tests/fixtures/ag_measurement/gate_policy_conservative.json`

## Non-claims

- gate は analytic 値の閾値判定ではない。
- gate は class transport、改善、修復、同一障害の持続を主張しない。
- `NOT_EVALUABLE` は pass でも block でもない。
