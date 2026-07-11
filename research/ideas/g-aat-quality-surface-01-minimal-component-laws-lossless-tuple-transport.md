---
status: picked
goal: G-aat-quality-surface-01
candidate_type: orientation
capability_category: certificate-transport/obstruction/invariance/repair-potential/traceability
expected_base_score: 55
expected_evidence_multiplier: 2.0
expected_final_score: 110
evidence_stage: proved-in-research
origin: G-aat-quality-surface-01-cycle19
tags:
  - tuple-transport
  - component-laws
  - obstruction
created: 2026-06-20
cycle: 19
lean: proved
---

# Finite component-law independence witnesses for tuple transport

## 主張

Cycle 14 の `BidirectionalTupleTransport` は、tuple missing locus と exact repair frontier を
lossless に運ぶための十分条件を与えた。この候補では逆向きに、support / trace-none /
repair-frontier の保存・反映 law を component-wise に落とすと、missing locus または exact repair
frontier が壊れる finite transport witness が存在することを示す。

trace-none と repair-frontier の failure witnesses は selected support を保ち、Cycle 11 の
visible tuple surface `(sigma, nu, selectedSupport)` を保つ。support preservation / reflection の
failure witnesses は selected support 自体を変えるため、visible surface preserving とは呼ばず、
より弱い scalar / verdict visible reading の下での support-law independence として分けて扱う。

主張は supplied finite tuple transports と finite witnesses に相対化する。任意 transport に対する
完全な必要十分分類、global minimality theorem、canonical global tuple transport、任意 profile
change の exactness、source extraction completeness、ArchMap correctness、実コード全体の
traceability は結論しない。

## 候補種別

`orientation`

## 依拠

- `research/lean/ResearchLean/AG/QualitySurface/TupleTransportExactness.lean`
- `research/lean/ResearchLean/AG/QualitySurface/ProfileTupleIntegration.lean`
- `tupleTransport_preserves_traceMissingLocus`
- `tupleTransport_reflects_traceMissingLocus`
- `tupleTransport_exactRepair_iff_of_bidirectional`
- `lawFirstTupleTransport_lossless_boundary`

## 非自明性

Cycle 14 は component laws があれば exact repair frontier が不変になることを証明したが、
どの law failure がどの protected exactness failure を生むかは未整理だった。この候補は十分条件を、
有限反例群による obstruction calculus へ鋭くする。

単なる既存 theorem の対偶ではなく、trace erasure、trace creation、repair erasure、repair creation、
support loss / support expansion の具体 transport witness を分けて、各 component law の欠落が
missing locus または exact repair frontier の lossless transport を壊すことを固定する。ただし
support witness は visible tuple surface preserving claim から外す。

## 数学的興味

comparison map の exactness は「強い仮定を置けば保たれる」というだけではなく、どの component law を
落とすと何が壊れるかという obstruction profile を持つ。これは quality certificate transport の
境界を測るための最小反例 calculus になる。

## GOAL への前進

certificate-transport / obstruction / invariance / repair-potential を接続し、lossy tuple transport の
失敗様式を finite witness として分類する。

## SCORE 見込み

- `score_reason`: G2-A/C は `minimal` と visible-preserving support-law claim を強すぎるとして revise。finite independence witnesses に絞り、base 55 / final 110 に下げる。
- `dullness_risk`: medium。単なる theorem package 再掲ではなく、各 component law failure の witness と exactness failure の対応を明示する必要がある。
- `proof_or_evidence_plan`: `TupleTransportComponentLaws.lean` に lossy transport witnesses と law-failure theorem を置いた。trace/repair witnesses では visible tuple surface preservation を示し、support witnesses では scalar/verdict-only preservation に限定した。最終 package は global minimality ではなく finite independence witness package とする。

## CS / SWE への帰結

quality tuple transport の UI / report が visible tuple surface を保っていても、support、trace-none、
repair frontier の保存・反映 law を落とすと trace / repair exactness は壊れる。これは supplied finite
transport 内の数学的 obstruction であり、実コード全体や tooling completeness の claim ではない。

## 証明・根拠の見込み

Lean proof は `research/lean/ResearchLean/AG/QualitySurface/TupleTransportComponentLaws.lean` に閉じる。

主要 theorem / declaration:

- `SameTupleScalarVerdict`
- `traceErasingTransport`
- `traceCreatingTransport`
- `repairErasingTransport`
- `repairCreatingTransport`
- `supportDroppingTransport`
- `supportExpandingTransport`
- `traceErasing_preserves_visibleTupleSurface`
- `traceCreating_preserves_visibleTupleSurface`
- `repairErasing_preserves_visibleTupleSurface`
- `repairCreating_preserves_visibleTupleSurface`
- `supportDropping_preserves_scalarVerdict`
- `supportExpanding_preserves_scalarVerdict`
- `traceNonePreservation_failure_obstructs_missingLocus_preservation`
- `traceNoneReflection_failure_obstructs_missingLocus_reflection`
- `repairPreservation_failure_obstructs_exactRepair_preservation`
- `repairReflection_failure_obstructs_exactRepair_preservation`
- `supportPreservation_failure_obstructs_missingLocus_preservation`
- `supportReflection_failure_obstructs_missingLocus_reflection`
- `tupleTransport_componentLaws_independence_package`

検証:

- `lake env lean research/lean/ResearchLean/AG/QualitySurface/TupleTransportComponentLaws.lean` pass。
- `lake build ResearchLean` pass。
- `lake env lean .tmp/tuple_transport_component_laws_axioms.lean` pass。
- reported declaration はすべて `does not depend on any axioms`。
- changed-file scan で hidden / bidirectional Unicode と local path は no matches。

## 審判メモ

- 厳密性: G2-A は revise、base 55。`SameTupleVisibleSurface` は support を含むため、support-dropping / support-expanding を visible-preserving と呼ぶ claim は不整合。support cases は scalar/verdict-only reading へ分離し、global minimality は主張しないこと。
- 研究価値: G2-B は accept、base 70。Cycle 14 の十分条件を obstruction calculus へ反転する価値を認めるが、component-law independence と visible-surface preservation の明示を要求。
- repo 全体価値: G2-C は revise、base 65。repo 全体価値は高いが、`Minimal component laws` は完全最小性分類に読めるため、finite independence witness に絞ること。

## 関連

- `research/ideas/g-aat-quality-surface-01-tuple-transport-exactness.md`
- `research/ideas/g-aat-quality-surface-01-tuple-protected-data-square-criterion.md`
- `research/reports/G-aat-quality-surface-01.md`

## G2 revise log

- G2-A: 初回 revise、base 55。support-law cases を full visible tuple surface preserving と呼ぶ不整合と global minimality overclaim を指摘。修正後 accept、base 55。
- G2-B: accept、base 70。Cycle 14 の十分条件を obstruction calculus へ反転する研究価値を認めた。
- G2-C: 初回 revise、base 65。`Minimal component laws` は完全最小性分類に読めるため、finite independence witnesses に絞ることを要求。修正後 accept、base 55。

## G3 監査

- `TupleTransportComponentLaws.lean` は trace/repair witnesses の visible tuple surface preservation、support witnesses の scalar/verdict preservation、各 component-law failure と missing-locus / exact-repair failure を証明する。
- G3 axiom audit: pass。target Lean、`ResearchLean`、axiom harness は pass。reported declaration はすべて axiom-free。
- G3 formalization quality audit: pass。finite supplied witnesses、trace/repair visible-surface preservation、support scalar/verdict-only preservation、global minimality を主張しない境界が Lean statement に反映されている。

## 進捗ログ

- 2026-06-20: Cycle 19 candidate card 作成。
- 2026-06-20: G2-A/C revise を反映し、global minimality claim を外して finite independence witnesses に絞り、support-law cases を scalar/verdict-only reading へ分離した。
- 2026-06-20: `TupleTransportComponentLaws.lean` added and verified locally.
