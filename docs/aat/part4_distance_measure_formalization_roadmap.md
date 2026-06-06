# AAT Part4 Distance / Measure Lean Formalization Roadmap

この文書は、第IV部「距離・測度・アーキテクチャ幾何」を Lean で証明済み
theorem family にするためのロードマップである。

数学本文の source of truth は
`docs/aat/mathematical_theory/part_4_distance_measure_geometry.md` に置く。
この文書は本文を書き換えるものではなく、本文に対応する Lean package、
theorem suite、proof obligation、acceptance example の作業単位を切る。
実装完了後は現行入口に残さず、完了記録または archive へ移す。

## 0. 現在地

Part4 の Lean surface は未着手ではない。現在すでに次の層が存在する。

- `Formal/Arch/Signature/DistanceGeometry.lean`
  - `DistanceValue`
  - `DistanceProfile`
  - `SelectedDistanceScope`
  - `BoundedDiagnosticConclusion`
  - `SignatureDistanceBundle`
  - `AtomRootDistanceBundle`
  - `ConfigurationDistanceSchema`
  - `SignatureDistanceSchema`
  - `SelectedFiniteOptimum`
  - `SelectedDistanceToRegion`
  - `BoundedSideEffectRepair`
  - `CurvatureTransport`
  - `LipschitzRepresentation`
  - `SpectralStabilityPackage`
  - `DistanceBundle`
  - `DistanceAAT`
- `Formal/Arch/AAT/GeneratedDistance.lean`
  - `GeneratedAtomShapeCoordinate`
  - `mismatchCount`
  - generated carrier shape distance
- `Formal/Arch/Evolution/Part4DistanceMeasureGeometry.lean`
  - Part4 candidate registry
  - representative declaration list
  - claim boundary list
  - generated carrier / context / operation / repair distance bridge
  - Part4-facing theorem aliases
- `Formal/Arch/Examples/AATPart4DistanceExamples.lean`
  - selected distance profile example
  - signature distance example
  - finite route optimum example
  - Lipschitz / spectral stability example
  - generated carrier / operation / repair distance examples

現在の中心的な成果は、距離を AAT core の生成原理ではなく、
selected diagnostic overlay として扱い、`unmeasured` を `zero` に潰さない
Lean boundary を置いたことである。

## 1. あるべき姿

Part4 の最終形は、単なる距離 schema 集合ではない。

AAT complete formalization の中で、Part4 は次の役割を持つ一級 theorem family
であるべきである。

```text
Atom-generated architecture
  -> generated distance / measure geometry
  -> signature path geometry
  -> repair distance and side-effect bounds
  -> curvature mass / transport
  -> homotopy and filling cost
  -> representation metric / spectral stability
  -> bounded diagnostic conclusion
```

したがって、あるべき Lean 形式化は次を満たす。
ここでいう「満たす」は、単に構造体や schema を置くことではなく、
対応する accessor theorem、bridge theorem、example theorem が Lean で通ることを指す。

- Part4 が `AATTheoremSuite` の独立 field として読める。
- Atom の full shape / valence / slot structure から root distance geometry へ接続される。
- `DistanceValue` aggregation が `unmeasured` と `zero` を体系的に分離する。
- signature path length、endpoint distance、hidden excursion、safe margin が
  reusable theorem package として使える。
- generated operation / repair が distance-to-region、flatness、side-effect bound、
  diagnostic recommendation に接続される。
- curvature mass / transport と diagram filling / non-fillability が少なくとも
  selected generated universe 上で接続される。
- homotopy distance / filling cost / Dehn-style bound が finite witness universe に
  相対化された theorem package として読める。
- representation metric / spectral stability が generated analytic representation と
  selected obstruction valuation に接続される。
- docs ledger が `defined only`、`proved`、`future proof obligation`、
  `empirical hypothesis` を混同しない。

## 2. 現在との差分

現状の形式化は、概念名と claim boundary の配置としてはかなり進んでいる。
一方で、Part4 本文が狙う architecture geometry としてはまだ途中である。

| 領域 | 現在 | あるべき姿との差 |
| --- | --- | --- |
| Atom root geometry | `GeneratedAtomShapeCoordinate.mismatchCount` から generated carrier distance へ接続されている。 | 現在は `family` / `axis` / `subject` / `predicate` / `direction` / `arity` の最小 coordinate で、`objectSlots`、`payloadSlots`、`valence`、semantic anchor を root geometry として十分に使えていない。 |
| Distance value discipline | `zero` / `measured` / `unmeasured` 等の分離と基本 theorem はある。 | aggregation、coverage、confidence、required evidence を横断する lemma が不足している。 |
| Signature geometry | path length、endpoint distance、hidden excursion、margin stability はある。 | concat、path decomposition、measured-axis projection、safe margin reuse が薄い。 |
| Operation / repair geometry | operation cost、distance to flat region、bounded side effect、contractive repair schema はある。 | generated repair / operation と distance-to-flatness / bounded diagnostic conclusion の接続がまだ弱い。 |
| Curvature geometry | curvature reading / transport schema と accessor theorem はある。 | generated curvature、diagram filler、non-fillability、filling lower bound の bridge が薄い。 |
| Homotopy / filling cost | finite bound schema はある。 | generated path / diagram package と Part4 filling-cost package の接続が不足している。 |
| Representation metric | Lipschitz / bi-Lipschitz / spectral stability schema はある。 | generated analytic representation、selected obstruction valuation、Part4 distance の接続がまだ薄い。 |
| Complete-formalization integration | Part4 module は `Formal.lean` に import される。 | `AATTheoremSuite` の一級 field としてはまだ接続されていない。 |
| Docs ledger | theorem index / proof obligations に関連 row はある。 | Part4 専用の段階的 completion boundary が足りない。 |

距離感としては、Part4 は「bounded schema と boundary」は厚いが、
「geometry package 同士が動く定理」はまだ薄い。

## 3. Claim boundary

Part4 の形式化では、次を主張しない。

- 距離が Atom を生成する。
- 距離だけで global lawfulness や global flatness が従う。
- `unmeasured` が `zero` と同じである。
- finite candidate universe の optimum が global optimum である。
- generated shape-coordinate distance が empirical semantic distance を較正する。
- repair recommendation が repair correctness theorem である。
- curvature / filling / homotopy package が all-path completeness を持つ。
- representation metric が downstream analytic library の完全性を証明する。
- ArchSig / FieldSig の forecast correctness が Lean theorem になる。

このロードマップの目的は、上の non-claims を増やして防御的に見せることではない。
selected scope の中で肯定的に語れる theorem package を増やすことである。

## 4. Work packages

### P0. Atom root geometry completion

目的:
Atom から距離への接続を Part4 の基礎として完成させる。

Part4 は距離・測度の章であるが、その距離は AAT core の外から貼る任意 metric ではない。
Atom が `AtomShape` として持つ intrinsic coordinates、slot structure、valence、
semantic anchor から root geometry が立ち上がる必要がある。

Lean 候補:

```text
Formal/Arch/Atom/Shape.lean
Formal/Arch/Atom/Valence.lean
Formal/Arch/Atom/Composition.lean
Formal/Arch/AAT/GeneratedDistance.lean
Formal/Arch/Signature/DistanceGeometry.lean
Formal/Arch/Evolution/Part4DistanceMeasureGeometry.lean
```

追加候補:

```text
GeneratedAtomFullShapeCoordinate
GeneratedAtomShapeCoordinate.ofFullShape
GeneratedAtomShapeCoordinate.slotMismatchCount
GeneratedAtomShapeCoordinate.valenceMismatchCount
GeneratedAtomShapeCoordinate.fullMismatchCount
GeneratedAtomRootGeometryPackage
generatedCarrierFullRootDistanceBundle
generatedCarrierRootDistance_records_full_shape_boundary
```

Acceptance:

- `AtomShape` の `objectSlots`、`payloadSlots`、`valence` を距離 root に反映する。
- generated carrier distance が単なる最小 coordinate mismatch だけでなく、
  selected full-shape distance package として読める。
- `AtomRootDistanceBundle` の `fiberDistance`、`carrierDistance`、`valenceDistance`、
  `semanticAnchorDistance` が、少なくとも selected generated universe 上で意味を持つ。
- semantic anchor distance は empirical semantic calibration ではなく、
  selected semantic coordinate / boundary として扱う。
- 距離は Atom を生成せず、Atom existence / observation completeness / lawfulness を結論しない。

### P1. Complete-formalization suite 接続

目的:
Part4 を `AATTheoremSuite` の一級 field として扱う。

Lean 候補:

```text
Formal/Arch/AAT/CompleteFormalization.lean
Formal/Arch/Examples/AATCompleteFormalizationExamples.lean
Formal/Arch/Examples/AATPart4DistanceExamples.lean
```

追加候補:

```text
GeneratedDistanceMeasureGeometryFields
AATTheoremSuite.generatedDistanceMeasureGeometry
AtomGeneratedAATWorld.generated_distance_measure_geometry_fields
```

Acceptance:

- Part4 field が distance value boundary、signature distance bundle、
  generated carrier distance、generated operation / repair distance、
  bounded diagnostic conclusion を保持する。
- example suite から Part4 field を読める theorem を追加する。
- `currentImplementationFrontier` に Part4 row を追加する場合、
  `connected` として扱える entrypoint を持つ。

### P2. DistanceValue aggregation discipline

目的:
未測定軸を zero に潰さない aggregation を再利用可能な theorem package にする。

Lean 候補:

```text
Formal/Arch/Signature/DistanceGeometry.lean
Formal/Arch/Evolution/Part4DistanceMeasureGeometry.lean
```

追加候補:

```text
SignatureDistanceBundle.measuredSubtotalOf_append
SignatureDistanceBundle.measuredSubtotalOf_filterMeasured
SignatureDistanceBundle.unmeasured_axis_not_counted_as_payload
SignatureDistanceBundle.records_coverage_confidence_boundary
```

Acceptance:

- `measuredSubtotal` は measured payload subtotal であり、total distance claim ではないことを theorem として読める。
- `unmeasured`、`unavailable`、`incomparable`、`infinite` が measured payload を持たないことを bundle-level に整理する。
- selected coverage / confidence / unmeasured policy を同時に読む accessor theorem を追加する。

### P3. Signature path geometry

目的:
signature drift、path length、hidden excursion、safe margin を path calculus として厚くする。

Lean 候補:

```text
Formal/Arch/Signature/DistanceGeometry.lean
Formal/Arch/Evolution/SignatureDynamics.lean
Formal/Arch/Evolution/Part4DistanceMeasureGeometry.lean
```

追加候補:

```text
SignatureDistanceSchema.pathLength_append
SignatureDistanceSchema.endpointDistance_of_nil
SignatureDistanceSchema.hiddenExcursion_zero_of_endpoint_eq_pathLength
SignatureDistanceSchema.margin_stability_of_subpath
```

Acceptance:

- finite path decomposition に対して path length / hidden excursion が再利用できる。
- margin stability が selected safe region と measured scope に相対化される。
- 未測定軸を safe margin の証拠として使わない boundary を残す。

### P4. Generated operation / repair distance bridge

目的:
generated operation / repair を Part4 の operation geometry と bounded diagnostic conclusion に接続する。

Lean 候補:

```text
Formal/Arch/AAT/GeneratedOperation.lean
Formal/Arch/AAT/GeneratedRepair.lean
Formal/Arch/Signature/DistanceGeometry.lean
Formal/Arch/Evolution/Part4DistanceMeasureGeometry.lean
Formal/Arch/Examples/AATPart4DistanceExamples.lean
```

追加候補:

```text
GeneratedOperationDistancePackage
GeneratedRepairDistancePackage
generatedRepair_distance_to_target_region
generatedRepair_bounded_diagnostic_conclusion
```

Acceptance:

- generated operation の mapped carrier distance が operation-distance evidence として読める。
- generated repair problem operation が mapped / unmapped target primitive evidence と distance boundary を同時に保持する。
- recommended operation は repair correctness theorem ではないことを保ったまま、
  bounded diagnostic conclusion の recommendation として接続する。

### P5. Curvature / filling / non-fillability bridge

目的:
Part4 の curvature mass、filling cost、persistent non-fillability を generated diagram package に接続する。

Lean 候補:

```text
Formal/Arch/AAT/GeneratedCurvature.lean
Formal/Arch/AAT/GeneratedDiagram.lean
Formal/Arch/Evolution/Chapter8HomotopySkeleton.lean
Formal/Arch/Evolution/Part4DistanceMeasureGeometry.lean
```

追加候補:

```text
GeneratedCurvatureTransportPackage
GeneratedFillingCostPackage
generatedObservationGap_lowerBoundedBy_fillingCost
generatedNonFillability_to_persistentNonFillability
```

Acceptance:

- selected generated observation gap を filling lower bound package へ渡せる。
- generated non-fillability witness を finite candidate universe 上の persistent non-fillability として読める。
- all-path completeness や universal Dehn function は主張しない。

### P6. Homotopy distance and Dehn-style finite universe

目的:
homotopy distance / filling cost を finite generated path universe に相対化して扱う。

Lean 候補:

```text
Formal/Arch/AAT/GeneratedPath.lean
Formal/Arch/AAT/GeneratedDiagram.lean
Formal/Arch/Signature/DistanceGeometry.lean
Formal/Arch/Evolution/Part4DistanceMeasureGeometry.lean
```

追加候補:

```text
GeneratedFiniteHomotopyCost
GeneratedFiniteDehnBound
generatedHomotopyBound_observationDistance_le
```

Acceptance:

- finite generated homotopy candidate list に対して selected bound を読める。
- supplied candidate universe に閉じた theorem であることを明示する。
- generated path / diagram examples から smoke theorem を追加する。

### P7. Representation metric bridge

目的:
Part4 representation metric を generated analytic representation と selected obstruction valuation に接続する。

Lean 候補:

```text
Formal/Arch/AAT/GeneratedAnalyticRepresentation.lean
Formal/Arch/AAT/GeneratedSignature.lean
Formal/Arch/Signature/DistanceGeometry.lean
Formal/Arch/Evolution/Part4DistanceMeasureGeometry.lean
```

追加候補:

```text
GeneratedRepresentationMetricPackage
generatedAnalyticRepresentation_lipschitzPackage
generatedSpectralStabilityPackage
```

Acceptance:

- generated analytic representation が selected structural distance と analytic distance の package として読める。
- zero-preserving / zero-reflecting の既存 theorem と Part4 metric theorem の境界を分ける。
- downstream library completeness や empirical spectral calibration は主張しない。

### P8. Docs ledger and issue chain

目的:
Part4 の形式化進捗を台帳化し、Issue 化できる作業単位へ分ける。

対象:

```text
docs/aat/lean_theorem_index.md
docs/aat/proof_obligations.md
docs/aat/part4_distance_measure_formalization_roadmap.md
```

Acceptance:

- Part4 専用 row を proof obligation index に追加する。
- theorem index に suite 接続、aggregation、repair bridge、curvature / filling bridge、
  representation metric bridge の status を分けて記録する。
- `defined only` / `proved` / `future proof obligation` / `empirical hypothesis` を混同しない。
- 数学本文 `docs/aat/mathematical_theory/part_4_distance_measure_geometry.md` は、
  明示的な本文更新タスクでない限り変更しない。

## 5. 推奨順序

最初に complete-formalization suite へ接続する。
その後、Part4 の中で最も実装済み surface が厚い順に bridge を増やす。

```text
P0 Atom root geometry completion
  -> P1 suite connection
  -> P2 DistanceValue aggregation
  -> P4 generated operation / repair distance bridge
  -> P5 curvature / filling bridge
  -> P7 representation metric bridge
  -> P3 signature path geometry
  -> P6 homotopy / Dehn finite universe
  -> P8 docs ledger sync
```

P0 は Part4 全体の入口である。Atom から root distance geometry への接続が細いままだと、
後段の signature、repair、curvature、homotopy の距離が AAT 起点の幾何として読みにくい。

P3 と P6 は数学的には重要だが、既存 generated acceptance との接続がやや遠い。
P0 / P1 / P2 / P4 / P5 を先に進める方が、Part4 を実際に使える theorem family にしやすい。

## 6. 完了境界

このロードマップの完了は、次の状態を指す。

- Part4 が `AATTheoremSuite` に一級 field として接続され、その接続 theorem が証明済みである。
- Atom full shape / valence / slot structure から generated root distance geometry へ接続する theorem が証明済みである。
- `DistanceValue` aggregation discipline が theorem として再利用できる。
- generated carrier / operation / repair distance が bounded diagnostic conclusion に theorem として接続されている。
- curvature / filling / non-fillability の selected generated bridge が少なくとも一つ証明済みである。
- representation metric と generated analytic representation の selected bridge が証明済みである。
- `AATPart4DistanceExamples` と `AATCompleteFormalizationExamples` に end-to-end smoke theorem がある。
- theorem index と proof obligation index が現在の Lean 状態と同期している。

このロードマップは、未証明 schema の一覧を残すための文書ではない。
完了境界は、ここで切った Part4 の bounded architecture geometry package が、
AAT complete formalization の中で証明済み theorem family として読めることである。
数学本文の全ての将来拡張を閉じるという意味ではないが、このロードマップに載せた
P0-P8 は証明されて初めて完了とする。

## 7. 将来拡張

このロードマップ後に残る大きな課題は次である。

- real-valued / rational-valued distance への拡張。
- weighted metric algebra と finite measure algebra の本格化。
- empirical ArchSig measurement と Lean theorem package metadata の対応強化。
- FieldSig 側の evolution measurement への Part4 geometry handoff。
- architecture navigation system としての repair route search / side-effect analysis。

これらは AAT core の純粋数学と、ArchSig / FieldSig の測定・予測 layer を混同せず、
別の roadmap または tooling PRD として切る。
