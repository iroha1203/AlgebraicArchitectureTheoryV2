---
status: picked
goal: G-aat-quality-surface-01
candidate_type: closure
capability_category: repair-potential / certificate-transport / traceability / invariance / obstruction
expected_base_score: 65
expected_evidence_multiplier: 2.0
expected_final_score: 130
evidence_stage: proved-in-research
origin: G-aat-quality-surface-01-cycle34
tags: [quality-surface, repair, support, transport, source-ref, frontier]
created: 2026-06-20
cycle: 34
lean: research/lean/ResearchLean/AG/QualitySurface/SupportLocalRepairTransportCommutator.lean
---

# Support-local repair/transport frontier commutator criterion

## 主張

Cycle 30 の `LawfulRepairTransportSquare` と Cycle 31 の `SupportLocalSourceRefRepair` を統合する。
`τ` が lawful packet transport で、source action が packet に対して support-local なら、transported action は
transported packet に対して support-local になる。さらに exact pre-frontier の下で、

```text
repairThenTransportPacket τ action packet
transportThenRepairPacket τ transportedAction packet
```

の両 route endpoint は、transported pre-frontier から transported support を除いた同じ frontier formula を満たす。
同時に Cycle 30 の source-ref exact visualization も得られる。

## 候補種別

`closure`

## 依拠

- Cycle 30: `research/lean/ResearchLean/AG/QualitySurface/LawfulRepairTransportCommutator.lean`
- Cycle 31: `research/lean/ResearchLean/AG/QualitySurface/SupportLocalRepairFrontier.lean`
- Cycle 32: `research/lean/ResearchLean/AG/QualitySurface/OutsideSupportMutationObstruction.lean`
- Cycle 33: `research/lean/ResearchLean/AG/QualitySurface/SupportedTokenMismatchObstruction.lean`

## 非自明性

Cycle 30 は protected commutator exactness を示したが、repair support が frontier calculus として
transport square 上でどう振る舞うかは示していない。Cycle 31 は単一 repair action の frontier restriction を
示したが、transported action や二経路 endpoint への移送は扱っていない。

この候補は、transport law と repair action naturality から support-locality 自体を移送し、両 route endpoint の
frontier restriction を同じ transported formula として固定する。

## 数学的興味

repair support は単なる metadata ではなく、lawful transport 下で functorial に移送される frontier-deleting operation として振る舞う。
Cycle 32/33 の obstruction はこの criterion の外側に位置づけられる。

## GOAL への前進

repair / transport / frontier / exact visualization を一つの sufficient criterion に統合し、
support-local repair theorem を certificate transport geometry へ接続する。

## SCORE 根拠

- `score_reason`: G6 next frontier に直接対応する closure。Cycle 30 の exact commutator と Cycle 31 の frontier calculus を、transported support-localityと両 route frontier formulaを含む theorem に圧縮する。G2 では既存 theorem 合成に近いリスクを踏まえ、期待 base を 70 から 65 に下げた。
- `dullness_risk`: medium。既存の `repairTransport_sourceRefExactVisualization_of_lawful` と `supportLocalRepair_frontier_eq_preFrontier_diff_support` を並べるだけなら低価値。transported support-locality、transported exact pre-frontier、両 route の同一 frontier formulaを結論に入れる。
- `proof_or_evidence`: transported exact pre-frontier、transported support-locality、left route frontier formula、right route frontier formula、route frontier agreement、source-ref exact visualization、package theorem を Lean で証明した。

## CS / SWE への帰結

repair action が lawful transport と support-locality の条件を満たすとき、profile / packet view を変えても
repair frontier の削れ方が一致する。これは repair dashboard が transport 後の frontier を再解釈するときの
bounded correctness criterion になる。ただし canonical repair planning、source extraction completeness、実コード全体品質は主張しない。

## 証明・根拠

Lean file:

- `research/lean/ResearchLean/AG/QualitySurface/SupportLocalRepairTransportCommutator.lean`

Proved declarations:

- `packetTransport_repairFrontierExact`
- `transportedAction_supportLocal_of_lawful`
- `supportLocalRepairTransport_leftFrontierRestriction`
- `supportLocalRepairTransport_rightFrontierRestriction`
- `supportLocalRepairTransport_routeFrontiers_agree`
- `supportLocalRepairTransport_sourceRefExactVisualization`
- `supportLocalRepairTransportCommutator_package`

Local G3 checks:

- `lake env lean research/lean/ResearchLean/AG/QualitySurface/SupportLocalRepairTransportCommutator.lean`: pass
- `lake build ResearchLean`: pass
- `lake env lean .tmp/support_local_repair_transport_axioms.lean`: pass; all reported declarations depend on no axioms
- independent axiom audit: pass; no `sorryAx`, nonstandard axioms, `propext`, `Classical.choice`, or `Quot.sound`
- independent formalization-quality audit: pass; transported exact pre-frontier, transported support-locality, left/right route frontier formula, route frontier agreement, and source-ref exact visualization are all in the theorem package

## 審判メモ

- 厳密性: `accept`、base 65。`transportedAction_supportLocal_of_lawful`、`packetTransport_repairFrontierExact`、left/right route frontier formula、route frontier agreement が実 theorem として入るなら Cycle 30/31 の単なる名前替えではない。
- 研究価値: `accept`、base 70。repair support を certificate transport 下の functorial frontier-deleting operation として読めるため、Cycle 30/31/32/33 を圧縮する。ただし existing theorem の併記なら減点。
- repo 全体価値: `accept`、base 70。AAT の certificate transport と repair basin、Tooling の view-change frontier correctness、SFT の repair operation invariance に接続できる。transported support-locality と route frontier agreement を package に含めることが採択条件。

## 関連

- `research/ideas/g-aat-quality-surface-01-support-local-repair-frontier-restriction.md`
- `research/ideas/g-aat-quality-surface-01-outside-support-mutation-obstruction.md`
- `research/ideas/g-aat-quality-surface-01-supported-token-mismatch-obstruction.md`
- `research/ideas/g-aat-quality-surface-01-lawful-repair-transport-commutator.md`

## 進捗ログ

- 2026-06-20: Cycle 34 G1 で作成。二つの G1 候補生成が第一候補として挙げた。
- 2026-06-20: G2 三審判すべて `accept`。A は既存 theorem 合成に近いリスクから base 65、B/C は base 70。picked は保守的に base 65 / final 130 とした。
- 2026-06-20: G3 Lean verification pass。対象 Lean、`ResearchLean`、axiom harness が pass。
- 2026-06-20: G3 independent axiom audit / formalization-quality audit pass。
