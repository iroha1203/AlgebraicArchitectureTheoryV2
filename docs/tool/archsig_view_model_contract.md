# archsig-measurement-view-model 契約(v0.5.4)

`archsig analyze` が出力する表示非依存の typed measurement view model
(`archsig-measurement-view-model.json`)の現行artifact契約。この文書自身をartifact契約の
source of truthとする。このartifactはArchViewの任意Analysis overlayに利用できるが、
ArchViewのArchitecture modeやproduct identityを定義しない。

## 原則

- view model は measurement packet と normalized ArchMap(観測入力)の**有界投影**であり、
  新しい invariant を計算せず、verdict を生成しない。
- **全 leaf は下の対応表に載る。** 対応表に無い leaf は存在してはならない(AC1)。
- 表示語彙(気象語ほか)は view model のフィールド名に入らない(却下条件3。
  cli テスト `cli_view_model_field_names_exclude_display_vocabulary` が執行)。
- 区画の absent(null)は「この run でその測定が記録されていない」ことを意味し、ゼロではない。
- consumer(viewer)は coverage 行の列挙を超えて観測範囲を推測してはならない。

## Leaf 対応表(AC1)

| view model leaf | 典拠(packet / normalized-archmap のパス) |
| --- | --- |
| `schema` | 定数 `archsig-measurement-view-model/v0.5.4` |
| `runId` / `toolVersion` / `inputDigests` / `componentFingerprints` | analyze run contract(他 artifact と同一機構)。`inputDigests.measurementPacket` は書き出し済み packet の canonical digest |
| `sourceArtifactRefs.*` | 同 run の出力ファイル名(固定値) |
| `conclusion` | `summary.conclusion`(archsig-analysis-summary.json) |
| `profiles[].profileRef / siteRef / coverRef / coefficient / domain` | `packet.profile` および `packet.profiles[]` の同名フィールド |
| `complex.coverRef` | cech invariant `representation.coverNerveProjection.coverRef` |
| `complex.vertices[].contextRef / atomCount` | 同 `coverNerveProjection.vertices[].contextRef` / `atomRefs` の要素数 |
| `complex.edges[].edgeRef / sourceContextRef / targetContextRef` | 同 `coverNerveProjection.edges[].edgeId / sourceContextRef / targetContextRef` |
| `complex.triples[].tripleRef / contextRefs / edgeRefs / sharedAtomRefs` | 同 `coverNerveProjection.faces[]` の `faceId / contextRefs / edgeRefs / sharedAtomRefs` |
| `complex.tripleSource` | 同 `coverNerveProjection.faceSource` |
| `observationCoverage[].contextRef` | complex の vertex(= packet が記録した選択 cover の context) |
| `observationCoverage[].profileRef` | `packet.profile.profileId` |
| `observationCoverage[].measurementAxis = "cech.sectionValue"` の行 | normalized ArchMap の `axis=cech, predicate=sectionValue` atom の当該 context への存在。`supportRefs` = その `normalizedAtomId`、`sourceRefs` = その `sourceRefs`(sort+dedup) |
| `observationCoverage[].measurementAxis = "saga-grounded.holdsCriterion"` の行 | grounding perChart 行(下記 localObservations と同典拠)。`status` = holds:true → `measured_zero` / それ以外 → `measured_nonzero`、`conclusionCode` = grounding verdict 行の `reason` |
| `observationCoverage[].boundaryKinds` | `packet.boundaryStatements[]` のうち `scopeRefs` が当該 context を含む行の `kind` |
| `localObservations.evaluator` | 固定値 `ag.saga-grounded`(行の存在は下記 premise の存在に従属) |
| `localObservations.verdict / reason` | `packet.structuralVerdict[]` の `evaluator == "ag.saga-grounded"` 行の `verdict / reason` |
| `localObservations.perChart[]` | invariant `saga-generated-end-to-end-packet` の `lawDependent.premise.perChart[]`(旧配置 `premise.perChart` を後方互換で受理)の `chart / law / holds / holdsCriterionRef / defectValueRef` |
| `edgeMismatch[].edgeRef / supportAtomRefs` | `coverNerveProjection.edges[]` の `edgeId / supportAtomRefs` |
| `edgeMismatch[].status` | 同 edges[] の `sectionObservation` と `value` の3値射影: not observed → `witness_not_supplied` / value=1 → `mismatch_observed` / value=0 → `agreement_observed` |
| `classSupport.coefficient` | cech invariant `representation.coefficient`。cech invariant が無い SAGA-only run では null。 |
| `classSupport.undirected` | cech invariant があるときは固定値 true(F₂ に向きは存在しない、という係数の事実の明示)。cech invariant が無い SAGA-only run では null。 |
| `classSupport.classNonzero` | cech invariant `representation.observedCocycle.classNonzero`。cech invariant が無い SAGA-only run では null。 |
| `classSupport.representativeEdgeRefs / supportAtomRefs` | cech invariant `representation.classSupport.edgeRefs / supportAtomRefs`。cech invariant が無い SAGA-only run では null。 |
| `classSupport.b1 / isForest` | cech invariant `representation.nerveShape.b1 / isForest`。cech invariant が無い SAGA-only run では null。 |
| `classSupport.residualClass.*` | invariant `saga-descent:residual-class` の `representation.residualClassSupport` の `nonZero / basis / representative / component.chartRefs / component.overlapRefs / cocycle.certificateKind / cocycle.tripleOverlapRefs / suppliedData.trueSheafCertificate.coverRef / suppliedData.trueSheafCertificate.memberChartRefs / suppliedData.gluingData.overlapRefs / suppliedData.gluingData.sectionRefs[].overlapRef / suppliedData.gluingData.sectionRefs[].sectionRef`。cech invariant が無い SAGA-only run でも、このSAGA residual classが記録されていれば `classSupport` をnullにせず投影する。`automatic-c2-zero` は、その residual component に triple overlap cell が無く、C²=0 により cocycle 条件が自動成立した認証を表す。suppliedData は class 認証に使った同一 component の certificate / canonical gluing 帰属を記録する。 |
| `classSupport.boundaryMembership.*` | invariant `saga-descent:boundary-membership` の `value`(無ければ representation)の `inB1 / residualSupport` |
| `harmonicFlow` | 常に null(調和代表元の per-edge 値は現行 packet に記録されない。合成しない) |
| `scalarFields[]`(harmonic 系) | invariant `harmonic-debt:*` の `representation.harmonicDebtNorm / essentialRepairLowerBound / lowerBoundStatus / invariantId` |
| `scalarFields[]`(capacity) | invariant `topological-debt-capacity:*` の `representation.capacityLowerBound / invariantId` |
| `boundaryStatements` | `packet.boundaryStatements` の逐語投影 |
| `nonClaims` | 固定文(view model の非主張) |

## 執行

- `cli_analyze_emits_measurement_view_model_typed_sections` — 区画の型・複体との整合・
  3値 witness・undirected・coverage 行の完全性・grounding 投影・boundary 逐語性・
  harmonicFlow absent・scalar provenance。
- `cli_view_model_field_names_exclude_display_vocabulary` — 表示語彙のフィールド名混入禁止。
- byte-determinism テスト(`cli_analyze_practical_service_outputs_are_byte_deterministic_with_known_digests`)の
  対象 artifact に view model を含む。

## 境界

- 区画が null の run(例: repair-plan 無しの cech-only run では residualClass が無い)は
  正常であり、エラーでも欠陥でもない。
- observationCoverage は「観測した組」の列挙であって、網羅性・完全性の主張ではない。
- per-vertex / per-edge のスカラー場・調和代表元辺値は現行 packet に存在しないため
  view model にも存在しない。将来 packet 側に測定が追加された場合のみ、この契約の
  改訂とともに投影される。
