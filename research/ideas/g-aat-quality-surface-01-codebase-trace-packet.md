---
status: picked
goal: G-aat-quality-surface-01
candidate_type: bridge
capability_category: traceability / computability / quality-surface / repair-potential
expected_base_score: 75
expected_evidence_multiplier: 2.0
expected_final_score: 150
evidence_stage: proved-in-research
origin: cycle-9
tags: [quality-surface, traceability, codebase-trace, repair-frontier, finite-witness]
created: 2026-06-20
cycle: 9
lean: research/lean/ResearchLean/AG/QualitySurface/CodebaseTracePacket.lean
---

# Finite codebase trace packet with exact repair frontier

## 主張

ArchMap / observation layer が供給する有限 source-ref token table を opaque data として扱う。選ばれた finite atom family 上で、同じ scalar reading、同じ verdict、同じ selected support を持つ二つの codebase trace packet が、source-ref trace locus と exact repair frontier で分岐する。

この結果は source extraction completeness や実コード全体の品質判定を主張しない。主張するのは、供給済み source-ref token table に相対化された trace availability / missing locus / repair frontier の certificate geometry である。

## 候補種別

`bridge`

## 依拠

- `research/reports/G-aat-quality-surface-01.md` cycle 4, 5, 6, 8
- `research/lean/ResearchLean/AG/QualitySurface/TraceTransport.lean`
- `research/lean/ResearchLean/AG/QualitySurface/StateSeparation.lean`
- `research/lean/ResearchLean/AG/QualitySurface/TraceLocus.lean`
- `research/lean/ResearchLean/AG/QualitySurface/ReadingAdequacy.lean`
- `research/goals/G-aat-quality-surface-01.md` の `finite codebase trace example` frontier

## 非自明性

cycle 6 の trace-locus witness は toy trace token 上で、同じ surface/support の下の missing locus と repair frontier の分岐を固定した。cycle 9 では source-ref token table を明示的に packet の保護データへ持ち込み、packet から既存 `TraceLocusCertificate` への射影、source-ref missing locus の射影、repair frontier exactness の移送を有限 codebase trace packet として固定する。

単なる fixture 表ではなく、support 内 source-ref availability の partition、missing source-ref locus の exactness、repair frontier との一致、surface reading の非忠実性、packet-level exactness が trace-locus certificate に保存されることを Lean theorem として証明する。

## 数学的興味

traceability を observation completeness の主張ではなく、有限 certificate 上の partial source-ref realization として扱える。これにより、Quality Surface は source reference を「存在する / 欠ける」という外部事実の代用品ではなく、選ばれた support 上の trace locus と repair obligation の幾何として読む。

## GOAL への前進

GOAL の frontier に明示された finite codebase trace example を、source-ref token table に相対化された finite certificate geometry として前進させる。traceability、computability、quality-surface、repair-potential の能力を同時に増やす。

## SCORE 見込み

- `score_reason`: finite codebase trace example frontier に直接対応し、供給済み source-ref packet、trace-locus certificate 射影、exact repair frontier / nonfaithfulness を Lean-backed に固定するため revised base 75 を見込む。
- `dullness_risk`: source-ref token を並べるだけなら dull。`CodebaseTracePacket`、available / missing partition、repair frontier exactness、surface reading nonfaithfulness を入れて回避する。
- `proof_or_evidence_plan`: `research/lean/ResearchLean/AG/QualitySurface/CodebaseTracePacket.lean` を追加し、opaque code atom、source-ref token、partial trace table、packet support、trace-missing locus、repair frontier、`TraceLocusCertificate` への射影を定義する。主要 theorem は axiom-free で証明する。

## CS / SWE への帰結

ArchMap が supply した有限 source-ref token table の範囲で、どの support atom に trace token があり、どこが repair frontier になるかを Quality Surface の drill-down として表示できる。未供給 token は source absence ではなく trace-repair obligation として扱う。

## 証明・根拠の見込み

Lean では、codebase atom と source-ref token を opaque finite inductive type として導入する。二つの certificate は visible scalar / verdict / selected support では一致する。一方は selected support 上で full source-ref trace を持ち、もう一方は storage atom の source-ref token を欠く。partial certificate の exact repair frontier は missing source-ref locus と一致する。

予定 theorem:

- `sourceRef_locus_partition`
- `fullTrace_available_on_codebaseSupport`
- `partialTrace_missing_on_codebaseSupport`
- `partialTrace_missing_locus_exact_storage`
- `partialTrace_repair_frontier_matches_missingRefs`
- `surfaceReading_not_faithful_to_codebaseTraceFrontier`
- `exact_packet_projects_to_exact_trace_repair`
- `same_surface_support_but_codebase_trace_frontier_diff`

## ループ必須フィールド

```text
score_reason: finite codebase trace example frontier に直接対応し、source-ref token table に相対化された packet / trace-locus certificate 射影 / repair frontier を Lean-backed に固定する。
mathematical_interest: traceability を observation completeness ではなく partial source-ref realization と repair obligation の certificate geometry として扱う。
goal_advancement: traceability、computability、quality-surface、repair-potential を同時に進める。
dullness_risk: token table の列挙だけなら dull。packet boundary、projection、partition、exactness、nonfaithfulness theorem を主成果にする。
proof_or_evidence_plan: CodebaseTracePacket.lean で code atom、source-ref token、partial trace table、packet、missing locus、repair frontier、TraceLocusCertificate 射影を定義して証明する。
planned_theorem_names: sourceRef_locus_partition, fullTrace_available_on_codebaseSupport, partialTrace_missing_on_codebaseSupport, partialTrace_missing_locus_exact_storage, partialTrace_repair_frontier_matches_missingRefs, exact_packet_projects_to_exact_trace_repair, same_surface_support_but_codebase_trace_frontier_diff, surfaceReading_not_faithful_to_codebaseTraceFrontier
visible_projection: scalar / verdict / support が一致しても source-ref trace gap と exact repair frontier は分岐する。
protected_structure: supporting atom family、supplied source-ref token table、missing source-ref locus、repair frontier、TraceLocusCertificate projection。
exactness_or_minimality_claim: repair frontier は selected support 内で source-ref token が未供給の atom ちょうどである。
nonfaithfulness_or_failure_mode: scalar / verdict / support reading が source-ref trace gap を復元できると読むこと。
previous_cycle_delta: cycle 6/8 の trace-locus adequacy を supplied codebase source-ref token packet と certificate projection へ接続する。
```

## visible_projection

同じ scalar / verdict / selected support を表示していても、source-ref trace availability と repair frontier は異なる。Quality Surface の visible layer は source-ref trace packet への drill-down を必要とする。

## protected_structure

protected data は、selected support、opaque source-ref token table、source-ref available locus、source-ref missing locus、exact repair frontier、trace-repair obligation である。

## exactness_or_minimality_claim

exactness は供給済み source-ref token table に相対化する。repair frontier は selected support 内で source-ref token が未供給の atom ちょうどである。

## nonfaithfulness_or_failure_mode

visible scalar、verdict、selected support が一致していることを、source-ref trace gap や repair frontier が一致していることとして読むのが failure mode である。

## previous_cycle_delta

cycle 4 は trace transport と trace naturality を分離し、cycle 6 は toy trace-locus / repair-frontier 分岐を固定し、cycle 8 は reading adequacy chain を整理した。cycle 9 はこれらを finite codebase trace packet へ接続する。

## 審判メモ

- 厳密性: revise。cycle 6 の改名に落ちないよう、supplied source-ref packet、`TraceLocusCertificate` への射影、relative exactness を必須化した。
- 研究価値: revise。frontier 直撃だが dullness risk があるため、base 75 / final 150 に下げ、packet/refinement/compression を主張の中心にした。
- repo 全体価値: revise。Tooling bridge として読む条件は、ArchMap supplied source refs を opaque evidence として扱い、実コード品質判定や extraction completeness を主張しないこと。
- revised G2: A/B/C すべて accept。base 75。単純 rename risk は `SourceRefPacket`、`TraceLocusCertificate` への射影、exact repair-frontier preservation、packet surface nonfaithfulness により回避した。

## G3 監査

- build: `cd research/lean && lake env lean ResearchLean/AG/QualitySurface/CodebaseTracePacket.lean` pass、`cd research/lean && lake build ResearchLean` pass。
- axiom check: pass。主要 declaration はすべて `does not depend on any axioms`。
- formalization quality audit: pass。主張は supplied opaque source-ref table に相対化され、source extraction completeness、実コード全体の品質判定、現行 tooling schema impact は主張しない。
- theorem highlights: `sourceRef_missing_projects_to_trace_missing`、`exact_packet_projects_to_exact_trace_repair`、`sourceRefLocusAware_faithful_to_repairFrontier_of_exact`、`same_surface_support_but_codebase_trace_frontier_diff`。

## G4 SCORE 監査

- score_verdict: `confirm`
- base_score: 75
- evidence_multiplier: 2.0
- penalty: 0
- final_score: 150
- category: `traceability / computability / quality-surface / repair-potential`
- goal_delta: finite codebase trace example frontier を、supplied source-ref packet と exact repair frontier の Lean-proved finite witness として閉じる。
- project_value_delta: loss-aware Quality Surface の drill-down data を、Tooling が将来供給する source-ref evidence に相対化して読める形にした。
- formalization_quality: pass。packet boundary、projection、exactness preservation、reading nonfaithfulness が axiom-free / sorry-free で証明されている。

## 関連

- `research/ideas/g-aat-quality-surface-01-trace-natural-transport.md`
- `research/ideas/g-aat-quality-surface-01-finite-trace-locus-certificate.md`
- `research/ideas/g-aat-quality-surface-01-reading-adequacy-lattice.md`

## 進捗ログ

- 2026-06-20: cycle 9 候補として作成。
- 2026-06-20: G2 三審判の revise を受け、supplied source-ref packet / projection / exactness 保存へ主張を修正し、picked とした。
- 2026-06-20: `CodebaseTracePacket.lean` を追加し、G3 公理検査と Lean 形式化品質監査が pass。evidence stage を `proved-in-research` に更新。
- 2026-06-20: G4 SCORE 監査が confirm。report Cycle 9 と total SCORE 1280 を更新。
