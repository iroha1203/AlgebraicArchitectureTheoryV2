# Part VII 定理16.1 statement contract

Issue #3197で固定する Algebraic-Geometric AAT Synthesis のLean statement。
定理は選択済み Part I--VII tower から1個の `AATSynthesisPackage` を構成し、
同じpackage上でsite、scheme、atlas、lawful locus、obstruction cohomology、
derived geometry、stratum、analytic reading contextを接続する。

## Generic theorem

`algebraicGeometricAATSynthesis_constructedPackage I` は
`S = I.toPackage` を満たす `S` を構成し、次を同時に返す。

- `S.aatSite = S.architectureGeometry.site`
- `S.ringedAATTopos = S.architectureScheme.ringedTopos`
- `S.affineAATCharts = S.architectureScheme.chart`
- `S.lawfulLocus` は `S.obstructionIdeal` の zero locus
- cohomology、derived geometry、stratum、analytic contextは入力tower由来

`AATSynthesisConstructionInput` はschemeとlaw algebra / idealを入力とし、
ringed topos、atlas、lawful locusをconstructor側で生成する。これらの値と
coherence equalityを入力fieldとして受け取らない。依存型fieldの比較には
`HEq` を使い、追加の同一視仮定は置かない。
exact Lean signatureは `Formal/AG/StatementContracts.lean` で固定する。

## Concrete acceptance witness

`nondegenerateSynthesisPackage` は次の同一selected model上の証拠を持つ。

- `Int` 上の非零 obstruction ideal `Ideal.span {2}`
- obstruction classを `Ideal Int` そのものとし、package idealをselected witnessにするanalytic context
- decorated `AATSch` のobstruction-ideal readingをそのまま返すideal-valued representation
- analytic zeroをactual bottom-ideal equalityとして読むdetecting family
- packageのactual `dist_flat_value`におけるflat stateの measured distance `0` と
  safe stateの measured distance `1`

このwitnessは singleton / `PUnit` だけの発火や `costToDistanceValue _ := measured 0`
を完了根拠にしない。
generic / concrete package chain、ideal-valued representation output、actual distance 0/1、aggregate evidenceの
exact signatureを `Formal/AG/StatementContracts.lean` で別々に固定する。

## Non-conclusions

この定理は measurement verdict、外部artifact抽出、arbitrary representation completeness、
runtime repair synthesis、whole-codebase evaluationを主張しない。
