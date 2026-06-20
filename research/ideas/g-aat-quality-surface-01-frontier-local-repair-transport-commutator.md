---
status: picked
goal: G-aat-quality-surface-01
candidate_type: closure
capability_category: repair-potential / certificate-transport / traceability / invariance / obstruction
expected_base_score: 65
expected_evidence_multiplier: 2.0
expected_final_score: 130
evidence_stage: proved-in-research
origin: G-aat-quality-surface-01-cycle36
tags: [quality-surface, repair, support, frontier, transport, commutator, source-ref]
created: 2026-06-20
cycle: 36
lean: Formal/AG/Research/QualitySurface/FrontierLocalRepairTransportCommutator.lean
---

# Frontier-local repair/transport commutator criterion

## 主張

Cycle 34 の lawful repair/transport commutator は、source action が table-level
`SupportLocalSourceRefRepair` を満たすとき、repair-then-transport と
transport-then-repair の両 endpoint frontier が同じ transported frontier formula を満たすことを示した。

Cycle 36 では、この仮定を Cycle 35 の missing-locus law
`FrontierLocalSourceRefRepair` へ下げる。すなわち、`τ` が lawful repair/transport square であり、
source action が packet に対して frontier-local なら、transported action も `τ.map packet` に対して
frontier-local であり、両 route endpoint は次の同じ formula を満たす。

```text
endpoint.repairFrontier atom
  ↔ (τ.map packet).repairFrontier atom ∧ ¬ transportedAction.repairSupport atom
```

さらに lawful square から source-ref exact visualization はそのまま得られる。したがって route frontier の
可換性に必要なのは table-level support-locality ではなく、missing-locus level の frontier-localityである。
Cycle 35 の token-renaming witness により、この仮定は `SupportLocalSourceRefRepair` より真に弱い。

## 候補種別

`closure`

## 依拠

- Cycle 30: `Formal/AG/Research/QualitySurface/LawfulRepairTransportCommutator.lean`
- Cycle 31: `Formal/AG/Research/QualitySurface/SupportLocalRepairFrontier.lean`
- Cycle 34: `Formal/AG/Research/QualitySurface/SupportLocalRepairTransportCommutator.lean`
- Cycle 35: `Formal/AG/Research/QualitySurface/FrontierLocalFormulaMinimality.lean`

## 非自明性

Cycle 34 は support-locality を transport して route formula を証明したが、その仮定は source-ref table identity
まで要求する。Cycle 35 は frontier formula に必要十分な law が missing-locus level まで落ちることを示した。
この候補は、transport square の中でも同じ弱化が有効であることを示し、repair/transport commutator の
frontier calculus と source-ref exact visualization を分離する。

単なる既存定理の即時系ではない理由は、`FrontierLocalSourceRefRepair` を action naturality と packet transport laws
で target 側へ運ぶ必要があるためである。support predicate、missing locus、post repair packet の table equality が
別々の経路で使われる。

## 数学的興味

repair/transport commutator は exact visualization には protected source-ref table law を使うが、
frontier calculus は missing-locus law だけで可換になる。この結果は、route exactness と frontier formula correctness
の必要構造を分離し、Quality Surface の repair-potential geometry をより細かい law 階層として読む素材になる。

## GOAL への前進

support-local repair theorem frontier を lawful transport の中で frontier-local criterion へ下げ、
repair-potential / certificate-transport / traceability / invariance の境界を鋭くする。

## SCORE 見込み

- `score_reason`: Cycle 34 の commutator theorem と Cycle 35 の frontier-local minimalityを合成し、table-level support-locality が route frontier formula には不要であることを Lean で固定する。source-ref exact visualization は lawful square 側の別成分として残るため、frontier correctness と trace exactness の law 階層が明確になる。G2 厳密性審判は、主張が Cycle 34/35 の自然な合成に近いことから base 65 へ下げたため、picked score も base 65 / final 130 とする。
- `dullness_risk`: medium。Cycle 34 の theorem を `FrontierLocalSourceRefRepair` に置換するだけに見える危険がある。strict weakening witness と route exact visualization の分離を package に含め、support-local 仮定を本当に落としたことを示す。
- `proof_or_evidence`: `transportedAction_frontierLocal_of_lawful`、left/right route frontier restriction、route frontier agreement、lawful square からの source-ref exact visualization、identity lawful square 上の Cycle 35 token-renaming witness による strict weakening package を Lean で証明した。

## CS / SWE への帰結

repair/transport dashboard が frontier formula だけを主張する場合、support 外の source-ref token identity 保存までは
必要条件ではない。一方、exact visualization は lawful square の protected table / obligation law に依存する。
これにより、UI や report が「frontier correctness」と「source-ref exact visualization」を別ラベルで表示すべき理由を
Lean-backed に説明できる。

## 証明・根拠の見込み

Lean file:

- `Formal/AG/Research/QualitySurface/FrontierLocalRepairTransportCommutator.lean`

Proved declarations:

- `transportedAction_frontierLocal_of_lawful`
- `frontierLocalRepairTransport_leftFrontierRestriction`
- `frontierLocalRepairTransport_rightFrontierRestriction`
- `frontierLocalRepairTransport_routeFrontiers_agree`
- `frontierLocalRepairTransport_sourceRefExactVisualization`
- `identitySourceRefPacketUpdate`
- `identitySourceRefPacketTransport_lawful`
- `self_repairActionTransportNaturality`
- `tokenRenaming_identity_lawfulSquare`
- `frontierLocalRepairTransport_strictlyWeakens_supportLocalHypothesis`
- `frontierLocalRepairTransportCommutator_package`

Expected claim boundary:

- finite `SourceRefPacket`
- declared `SourceRefRepairAction`
- explicit `PacketUpdate`
- `LawfulRepairTransportSquare`
- exact pre-frontier assumption for the source packet

The result does not assert canonical transport, canonical repair planning, ArchMap correctness, source extraction completeness,
or whole-codebase quality.

Local G3 checks:

- `lake env lean Formal/AG/Research/QualitySurface/FrontierLocalRepairTransportCommutator.lean`: pass
- `lake build FormalAGResearch`: pass
- `lake env lean .tmp/frontier_local_repair_transport_commutator_axioms.lean`: pass; reported declarations depend on no axioms
- `rg -n "\\b(axiom|admit|sorry|unsafe)\\b" Formal/AG/Research/QualitySurface/FrontierLocalRepairTransportCommutator.lean`: pass; no hits in the Lean evidence file

G3 audit summary:

- 公理検査: `pass`。reported declarations と主要 dependency checks は `sorryAx`、`propext`、`Classical.choice`、`Quot.sound` を含む axiom dependency を持たない。Research evidence module と `Formal/AG/Research.lean` import aggregator 以外の `Formal/AG` は編集していない。
- 形式化品質: `pass`。`LawfulRepairTransportSquare`、`FrontierLocalSourceRefRepair action packet`、`RepairFrontierExact packet` から route frontier formula、route agreement、source-ref exact visualization を導き、`SupportLocalSourceRefRepair` は主仮定に隠れていない。strict weakening は identity lawful square 上の commutator-contextual witness として実装されている。

## 審判メモ

- 厳密性: `accept`、base 65。`FrontierLocalSourceRefRepair` を lawful square の missing/support transport と action naturality で target 側へ運ぶ補題が必要なので単なる rename ではない。ただし Cycle 34/35 の自然な合成に近く、期待 80 は高い。strict weakening は identity lawful square 上の witness として実装することが要求された。
- 研究価値: `accept`、base 70。新しい不変量ではないが、frontier correctness と source-ref exact visualization の二層分離を圧縮できる。strict weakening を commutator 文脈で示すことが要求された。
- repo 全体価値: `accept`、base 70。Research / Lean / paper seed に加え、tooling/report で「frontier formula」と「exact visualization」を別ラベルで扱う根拠になる。既存 Cycle の置換補題に見えないよう、二つの結論ラベルの分離を report に明示することが要求された。

## 関連

- `research/ideas/g-aat-quality-surface-01-lawful-repair-transport-commutator.md`
- `research/ideas/g-aat-quality-surface-01-support-local-repair-transport-frontier-commutator.md`
- `research/ideas/g-aat-quality-surface-01-frontier-local-formula-minimality.md`

## 進捗ログ

- 2026-06-20: Cycle 36 G1 で作成。G1 候補生成で、Cycle 34 の support-local commutator を Cycle 35 の frontier-local law へ下げる候補として採択候補にした。
- 2026-06-20: G2 三審判すべて `accept`。A は base 65、B/C は base 70。picked は保守的に base 65 / final 130 とした。
- 2026-06-20: G3 Lean 実装を追加。対象 file 単体の `lake env lean` が pass。
- 2026-06-20: G3 公理検査と形式化品質監査がともに `pass`。G3.5 初回は report 未同期と監査要約不足で `revise`。
- 2026-06-20: report と候補カードを同期。G3.5 再審査で残った hygiene 指摘に従い、Lean evidence file に限定した no-sorry scan と resolved revise を記録。
