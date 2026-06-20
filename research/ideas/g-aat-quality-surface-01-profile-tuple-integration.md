---
status: picked
goal: G-aat-quality-surface-01
candidate_type: unification
capability_category: atom-supported-quality-geometry / quality-surface / certificate-transport / traceability / repair-potential
expected_base_score: 55
expected_evidence_multiplier: 2.0
expected_final_score: 110
evidence_stage: proved-in-research
origin: G-aat-quality-surface-01-cycle-11
tags: [quality-surface, certificate-tuple, traceability, repair-frontier]
created: 2026-06-20
cycle: 11
lean: Formal/AG/Research/QualitySurface/ProfileTupleIntegration.lean
---

# Profile-typed certificate tuple integration

## 主張

有限 profile 上で `Cert_A(p) = (sigma_p, omega_p, S_p, R_p, nu_p, T_p)` 型の
profile-typed certificate tuple を固定する。tuple は visible scalar `sigma_p`、
obstruction / obligation state `omega_p`、selected atom support `S_p`、repair frontier `R_p`、
verdict `nu_p`、trace field `T_p` を同時に持つ。

主張は、同じ visible projection `(sigma_p, nu_p, S_p)` を持つ二つの endpoint tuple が、
protected tuple data `(omega_p, R_p, T_p)` で分岐しうること、tuple から trace-locus certificate への
projection が missing locus と exact repair frontier を保存すること、かつ exact trace-repair regime では
trace-missing locus を含む tuple reading が repair frontier に faithful になることである。

## 候補種別

`unification`

## 依拠

- `research/GOALS.md` の `G-aat-quality-surface-01`。
- cycle 5 の `StateSeparation.QualityCertificate`。
- cycle 6 の `TraceLocus.TraceLocusCertificate`。
- cycle 8 の `ReadingAdequacy.Reading` と exact trace-repair faithfulness。
- cycle 9 の source-ref packet projection and exact repair preservation。
- cycle 10 の typed profile grid endpoint witness。

## 非自明性

単なる tuple 定義ではなく、これまで別々に固定した state separation、trace locus、reading adequacy、
source-ref packet、profile endpoint witness を、GOAL の中心語彙である
`Cert_A(p) = (sigma_p, omega_p, S_p, R_p, nu_p, T_p)` へ戻す。Lean 側では
visible tuple projection の非忠実性、trace-locus projection の保存、exact repair frontier に対する
trace-aware tuple reading の faithful 性を同じ finite profile-typed object 上で同時に示す。

## 数学的興味

Quality Surface を「profile ごとの数値表」ではなく、profile fiber 上の certificate geometry として読むための
中心対象を固定する。visible surface と protected tuple data の分離により、同じ surface point が異なる
trace / repair geometry を持つ fold として現れることが明確になる。

## GOAL への前進

certificate tuple、traceability、repair potential、profile-typed endpoint reading を統合し、phase boundary criteria が
要求する `Cert_A(p)` の意味を Lean-backed finite witness として与える。

## SCORE 見込み

- `score_reason`: cycles 5-10 の個別成果を GOAL の中心 certificate tuple に圧縮し、visible surface 非忠実性、trace-locus projection preservation、exact repair faithful reading を一つの finite profile-typed object 上で同時に示すため。G4 SCORE 監査は、新しい現象そのものより統合・圧縮価値が中心で、projection preservation が定義的に近いとして base score を 55 に減額した。
- `dullness_risk`: tuple structure を定義するだけ、または既存 trace-locus theorem の名前替えだけなら低 SCORE であり、G2 で落とすべきである。
- `proof_or_evidence_plan`: `Formal/AG/Research/QualitySurface/ProfileTupleIntegration.lean` に `TupleCertificateAt`、`toTraceLocusCertificate`、`tuple_missing_locus_projects_to_trace_missing`、`tupleExactRepair_projects_to_trace_exactRepair`、`same_surface_but_profile_tuple_diff`、`traceAwareTupleReading_faithful_to_repair_of_exact` を証明する。

## CS / SWE への帰結

将来 tooling が表示する quality surface は、visible score、verdict、selected support だけでは repair frontier や trace gap を復元しない。
一方で trace-missing locus を certificate tuple の reading に含めると、exact repair regime では repair frontier を安定に読む条件が得られる。
この帰結は supplied trace data に相対化され、source extraction completeness や実コード全体の品質判定は主張しない。

## 証明・根拠の見込み

Research 配下に finite profile endpoint `endpointProfile` と `TupleCertificateAt p` を定義した。
full endpoint tuple と trace-missing endpoint tuple は同じ `sigma`、`nu`、`S` を持つが、`omega`、`R`、`T`
が異なる。tuple から `TraceLocus.TraceLocusCertificate` への射影を定義し、missing locus と repair frontier が
pointwise に保存されることを示した。最後に `ReadingAdequacy.FaithfulToInvariantOn` を使い、
exact trace-repair regime で trace-aware tuple reading が repair frontier に faithful であることを証明した。

Lean declarations:

- `tuple_projects_visible_surface`
- `tuple_missing_locus_projects_to_trace_missing`
- `tupleExactRepair_projects_to_trace_exactRepair`
- `endpointTuple_gridWitness_diff`
- `endpointTuple_traceField_diff`
- `endpointTuple_protectedData_diff`
- `visibleTupleSurface_not_faithful_to_traceMissingLocus`
- `visibleTupleSurface_not_faithful_to_repairFrontier`
- `traceAwareTupleReading_faithful_to_repair_of_exact`
- `same_surface_but_profile_tuple_diff`

visible_projection: `(sigma_p, nu_p, S_p)`

protected_structure: `(omega_p, R_p, T_p, profile typing)`

exactness_or_minimality_claim: `R_p` is exactly the trace-missing locus in the exact trace-repair regime.

nonfaithfulness_or_failure_mode: the visible tuple surface cannot reconstruct trace missing locus or repair frontier.

previous_cycle_delta: cycle 10 の grid witness をさらに大きくするのではなく、cycles 5-10 の protected data を `Cert_A(p)` 本体へ統合する。

## 審判メモ

- 厳密性: G2 A は `revise`。wrapper / rename risk を避けるため、profile typing、六成分 tuple、trace-locus projection、visible nonfaithfulness、exact repair faithful reading を同一 object 上で証明する必要がある。base score 期待値を 65 に下げ、主張を integration theorem に絞った。
- 研究価値: G2 B は `accept`、base 65。surprise より compression / leverage / paper spine 化の価値が中心。
- repo 全体価値: G2 C は `accept`、base 70。Research 配下の finite profile endpoint witness として扱い、canonical theory object への premature promotion を避ける。
- G3 axiom / formalization audit: pass。追加 theorem を含む 10 declaration は axiom-free、形式化品質監査も pass。
- G4 SCORE audit: `reduce`。base 55、multiplier 2.0、penalty 0、final 110。証拠不足ではなく、既存成果の統合・圧縮が中心であるため 65 から減額。

## 証拠

- Lean file: `Formal/AG/Research/QualitySurface/ProfileTupleIntegration.lean`
- Evidence stage: `proved-in-research`
- Build target: `lake env lean Formal/AG/Research/QualitySurface/ProfileTupleIntegration.lean`
- Main theorem: `ProfileTupleIntegration.same_surface_but_profile_tuple_diff`
- Axiom summary: `tuple_projects_visible_surface`、`tuple_missing_locus_projects_to_trace_missing`、`tupleExactRepair_projects_to_trace_exactRepair`、`endpointTuple_gridWitness_diff`、`endpointTuple_traceField_diff`、`endpointTuple_protectedData_diff`、`visibleTupleSurface_not_faithful_to_traceMissingLocus`、`visibleTupleSurface_not_faithful_to_repairFrontier`、`traceAwareTupleReading_faithful_to_repair_of_exact`、`same_surface_but_profile_tuple_diff` は `#print axioms` でいずれも axiom-free。
- Formalization summary: `TupleCertificateAt p` が `ProfileGridHolonomy.CertificateAt p` を保持し、endpoint tuple は law-first / cover-first grid witness を同じ endpoint profile 上で運ぶ。主 theorem は visible agreement、grid witness divergence、projection 前の `omega` / `traceField` / protected data divergence、trace-locus projection、exact repair faithful reading を同時に述べる。

## 関連

- `research/ideas/g-aat-quality-surface-01-measured-unmeasured-trace-missing.md`
- `research/ideas/g-aat-quality-surface-01-finite-trace-locus-certificate.md`
- `research/ideas/g-aat-quality-surface-01-reading-adequacy-lattice.md`
- `research/ideas/g-aat-quality-surface-01-codebase-trace-packet.md`
- `research/ideas/g-aat-quality-surface-01-profile-grid-holonomy.md`

## 進捗ログ

- 2026-06-20: Cycle 11 G1 候補として作成。
- 2026-06-20: G2 A の `revise` を受け、expected score を 65 x 2.0 = 130 に下げ、同一 finite profile-typed object 上の projection / nonfaithfulness / exact repair faithful reading を必要証拠として明確化。
- 2026-06-20: `Formal/AG/Research/QualitySurface/ProfileTupleIntegration.lean` で `TupleCertificateAt`、projection preservation、visible nonfaithfulness、exact trace-aware repair faithfulness、統合 witness theorem を追加。
- 2026-06-20: G3 形式化監査の `revise` を受け、`TupleCertificateAt p` に `ProfileGridHolonomy.CertificateAt p` を保持させ、endpoint tuple が law-first / cover-first grid witness を運ぶこと、projection 前の trace field / protected data が分岐することを主 theorem に追加。
- 2026-06-20: G3 再監査で axiom audit / formalization quality audit がいずれも pass。
- 2026-06-20: G4 SCORE 監査で base 55、evidence multiplier 2.0、final SCORE 110 に確定。
