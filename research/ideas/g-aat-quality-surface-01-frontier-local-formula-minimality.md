---
status: picked
goal: G-aat-quality-surface-01
candidate_type: closure
capability_category: repair-potential / obstruction / traceability / invariance
expected_base_score: 75
expected_evidence_multiplier: 2.0
expected_final_score: 150
evidence_stage: proved-in-research
origin: G-aat-quality-surface-01-cycle35
tags: [quality-surface, repair, support, frontier, minimality, source-ref]
created: 2026-06-20
cycle: 35
lean: research/lean/ResearchLean/AG/QualitySurface/FrontierLocalFormulaMinimality.lean
---

# Frontier-local formula minimality criterion

## 主張

Cycle 31 の `SupportLocalSourceRefRepair` は、source-ref table を support 外で保存する table-level law として
post-frontier formula を導いた。

Cycle 35 では、exact pre-frontier の下で

```text
(repairPacket action packet).repairFrontier atom
  ↔ packet.repairFrontier atom ∧ ¬ action.repairSupport atom
```

が成立するための frontier-level law を切り出す。必要な構造は次の二つである。

- support 上では post missing locus を消すこと。
- support 外では missing locus を保存・反映すること。

この `FrontierLocalSourceRefRepair` は `SupportLocalSourceRefRepair` から従うが、source-ref table の
token identity を support 外で保存することまでは要求しない。したがって table-level support-locality より弱く、
frontier formula に対して sharp な criterion である。

## 候補種別

`closure`

## 依拠

- Cycle 21: `research/lean/ResearchLean/AG/QualitySurface/CodebaseTraceRepairTrajectory.lean`
- Cycle 31: `research/lean/ResearchLean/AG/QualitySurface/SupportLocalRepairFrontier.lean`
- Cycle 32: `research/lean/ResearchLean/AG/QualitySurface/OutsideSupportMutationObstruction.lean`
- Cycle 34: `research/lean/ResearchLean/AG/QualitySurface/SupportLocalRepairTransportCommutator.lean`

## 非自明性

Cycle 31 は十分条件を与えたが、その仮定が frontier formula に対して最小かどうかは示していない。
Cycle 32 は outside-support mutation が frontier formula を壊すことを示したが、frontier formula そのものに必要十分な
law は切り出していない。

この候補は、table equality を要求する `SupportLocalSourceRefRepair` と、frontier formula に本当に必要な
missing-locus law を分離する。さらに、support 外の token identity を変えても missing locus を保存する有限 witness により、
frontier-local law が table-local law より真に弱いことを固定する。

## 数学的興味

repair frontier は source-ref table 全体ではなく、missing locus と repair support の相互作用だけを読む。
この結果は、frontier geometry の最小構造を table-level traceability law から切り離し、repair support を
frontier-deleting operation として sharp に定式化する。

## GOAL への前進

support-local repair theorem を十分条件から frontier-local な必要十分 criterion へ進め、
repair-potential / obstruction / traceability / invariance の境界を鋭くする。

## SCORE 根拠

- `score_reason`: Cycle 31 の positive theorem と Cycle 32 の obstruction を、frontier formula の sharp criterion として再定式化する。`SupportLocalSourceRefRepair -> FrontierLocalSourceRefRepair`、frontier formula との iff、table-locality より弱い有限 witness をすべて Lean で固定する。ただし `frontierLocal_iff_frontierRestriction` 自体は `RepairFrontierExact` と `repairPacket` の定義から直接的でもあるため、G2 厳密性審判に合わせて base 75 / final 150 とする。
- `dullness_risk`: medium。既存 formula の再掲に落ちる危険があるため、必要十分性、strictness witness、conjunct minimality を theorem package に入れる。
- `proof_or_evidence`: `FrontierLocalSourceRefRepair` を formula の直定義ではなく missing-locus law として定義し、support-locality からの導出、frontier formula との同値、token-renaming witness による `FrontierLocalSourceRefRepair ∧ ¬ SupportLocalSourceRefRepair`、pre-frontier conjunct / outside-support conjunct の独立 witness、package theorem を Lean で証明した。

## CS / SWE への帰結

repair dashboard が frontier だけを扱う場合、source-ref token identity の完全保存までは必要条件ではない。
一方で exact visualization や traceability surface では token identity が必要になる。frontier-local correctness と
table-local trace correctness を分けることで、repair UI / analysis packet がどの保証を表示しているかを明確にできる。

## 証明・根拠

Lean file:

- `research/lean/ResearchLean/AG/QualitySurface/FrontierLocalFormulaMinimality.lean`

Proved declarations:

- `FrontierLocalSourceRefRepair`
- `supportLocal_implies_frontierLocal`
- `frontierLocal_frontierRestriction`
- `frontierLocal_iff_frontierRestriction`
- `frontierRestriction_implies_frontierLocal`
- `tokenRenamingOutsideStorageRepairAction`
- `tokenRenamingOutsideStorageRepairPacket`
- `tokenRenaming_frontierLocal`
- `tokenRenaming_frontierRestriction`
- `tokenRenaming_not_supportLocal`
- `frontierFormula_preFrontierConjunct_is_necessary`
- `frontierFormula_outsideSupportConjunct_is_necessary`
- `frontierFormula_conjuncts_are_independent`
- `frontierLocalFormulaMinimality_package`

Local G3 checks:

- `cd research/lean && lake env lean ResearchLean/AG/QualitySurface/FrontierLocalFormulaMinimality.lean`: pass
- `cd research/lean && lake build ResearchLean`: pass
- `lake env lean .tmp/frontier_local_formula_minimality_axioms.lean`: pass; all reported declarations depend on no axioms
- `rg -n "\\b(axiom|admit|sorry|unsafe)\\b" research/lean/ResearchLean/AG/QualitySurface/FrontierLocalFormulaMinimality.lean`: pass; no hits

## 審判メモ

- 厳密性: `accept`、base 75。claim boundary は有限 `SourceRefPacket` / declared repair action / missing locus / repair frontier に収まる。`FrontierLocalSourceRefRepair` は formula の直定義ではなく、support 上 clearing と support 外 missing-locus preserve/reflect の law として定義することが採択条件。
- 研究価値: `accept`、base 80。Cycle 31/32/33/34 を frontier-local law に圧縮する価値がある。base 80 を保つには strictness witness と conjunct minimality が必要。
- repo 全体価値: `accept`、base 80。Research / Lean / paper seed として価値があり、repair UI / analysis packet で frontier-local correctness と table-local trace correctness を分ける将来 surface に接続する。

## 関連

- `research/ideas/g-aat-quality-surface-01-support-local-repair-frontier-restriction.md`
- `research/ideas/g-aat-quality-surface-01-outside-support-mutation-obstruction.md`
- `research/ideas/g-aat-quality-surface-01-supported-token-mismatch-obstruction.md`
- `research/ideas/g-aat-quality-surface-01-support-local-repair-transport-frontier-commutator.md`

## 進捗ログ

- 2026-06-20: Cycle 35 G1 で作成。二つの G1 候補生成が最上位候補として挙げ、scratch Lean feasibility check が pass。
- 2026-06-20: G2 三審判すべて `accept`。A は直接性リスクから base 75、B/C は base 80。picked は保守的に base 75 / final 150 とした。
- 2026-06-20: G3 Lean verification pass。対象 Lean、`ResearchLean`、axiom harness が pass。
