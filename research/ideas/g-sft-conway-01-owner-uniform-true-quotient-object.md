---
status: picked
goal: G-sft-conway-01
exploration_role: unifier
candidate_type: unification
capability_category: selected-finite-quotient-carrier, finite-coefficient, finite-quotient-shadow, presentation-comparison, conway-obstruction
expected_base_score: 40
expected_evidence_multiplier: 2.0
expected_final_score: 80
evidence_stage: proved-in-research
rival_advantage: CODEOWNERS, org-network analysis, Team Topologies, and AI review can identify local owner mismatch, but they do not provide one finite quotient carrier where selector, boundary-generator, local-zero, and full-family-nonzero presentations are the same obstruction class.
genius_potential: no
genius_target: not-applicable
genius_support_role: not-applicable
target_theorem: not-applicable
target_support_node: not-applicable
target_progress: not-applicable
proof_obligation_delta: not-applicable
target_completion_role: not-applicable
origin: G-sft-conway-01
cycle: 20
lean: proved-in-research
tags: [sft, conway, owner-uniform, quotient-carrier, finite-coefficient]
created: 2026-07-05
---

# Owner-uniform Conway obstruction as a selected finite quotient carrier

## 主張

`OwnerUniformFamilyDefect` と explicit owner-uniform boundary generator から、predicate ではなく
selected finite quotient carrier を定義する。`OwnerUniformConwayClass family` が zero であることは
owner-uniform span selector の存在と同値であり、restricted singleton subfamily は zero、full
restricted two-fork family は nonzero class を持つ。

この候補は selected finite quotient carrier であり、true sheaf `H^1`、arbitrary-cover naturality、
canonical selector、または任意 receiver への universal quotient theorem は主張しない。

## 候補種別

`unification`

## 依拠

- Cycle 17: `research/lean/ResearchLean/AG/SFT/ConwayOwnerUniformFamilyQuotient.lean`
- Cycle 18: `research/lean/ResearchLean/AG/SFT/ConwayOwnerUniformSpanSelector.lean`
- Cycle 19: `research/lean/ResearchLean/AG/SFT/ConwayOwnerUniformSelectorQuotientBridge.lean`
- report: `research/reports/G-sft-conway-01.md`

## 非自明性

Cycle 17 は `OwnerUniformFamilyClassVanishes` を boundary membership predicate として置き、
Cycle 19 は selector presentation と quotient-style presentation の同値を証明した。この候補では、
実際の quotient carrier、quotient class、zero/nonzero theorem を導入し、既存の同値を carrier 上の
class statement として読む。

## 数学的興味

Conway 障害を「複数 predicate の同値」から「selected finite coefficient quotient の class」へ移す。
これは true sheaf `H^1` へ飛ばずに、何が obstruction receiver で、何がまだ finite shadow なのかを
分離する。

## GOAL への前進

`true quotient object` frontier に向け、Cycle 17/19 の finite-quotient-shadow を selected finite
quotient carrier として強化する。

## ライバルに対する有効性

既存 rival は mismatch や owner conflict を列挙できるが、selector obstruction、boundary-generator
vanishing、singleton local zero、full-family nonzero を同一 quotient class として保存する構造は返さない。

## SCORE 見込み

- `score_reason`: selected finite quotient carrier と class zero/nonzero theorem を実装し、Cycle 17/19 の
  open question に限定的に答える。G2 A は既存 predicate の quotient API restatement に近いとして base 40 まで
  下げるよう求め、G2 B/C/D は base 65-75 を許容した。G4 は既存 bridge の再包装 risk を重く見て、
  G2 A の low bound を採用し、base 40 / final +80 に reduce した。
- `dullness_risk`: quotient carrier を作っても既存 `OwnerUniformFamilyClassVanishes` を包むだけなら低価値。
  quotient class の zero/nonzero statement と prior presentation comparison を reportable evidence にする必要がある。
- `proof_or_evidence_plan`: `research/lean/ResearchLean/AG/SFT/ConwayOwnerUniformTrueQuotient.lean` に selected finite quotient carrier、
  quotient class、zero iff selector、nonzero iff selector obstruction、restricted singleton zero、restricted full-family nonzero、
  selected package を置いた。

## Target Theorem 寄与

- `target_theorem`: not-applicable
- `target_support_node`: not-applicable
- `target_progress`: not-applicable
- `proof_obligation_delta`: not-applicable
- `target_completion_role`: not-applicable

## CS / SWE への帰結

owner mismatch を単一スコアや自然言語 diagnosis として扱うのではなく、局所的に消える owner-uniform class と
full family で残る nonzero class を同じ finite receiver 上で比較できる。

## 証明・根拠の見込み

`OwnerUniformFamilyBoundarySubgroup family` で `OwnerUniformFamilyZ2` を割った quotient carrier を定義し、
`OwnerUniformFamilyDefect family` の class を `OwnerUniformConwayClass family` とする。`QuotientAddGroup.eq_zero_iff`
または同等の quotient API により zero iff boundary membership を示し、Cycle 19 の selector / class equivalence に接続する。

Lean evidence:

- `OwnerUniformConwayQuotient`
- `OwnerUniformConwayClass`
- `ownerUniformConwayClass_eq_zero_iff_familyClassVanishes`
- `ownerUniformConwayClass_eq_zero_iff_spanSelector`
- `ownerUniformConwayClass_ne_zero_iff_selectorObstruction`
- `ownerUniformConwayClass_ne_zero_iff_familyNonzeroClass`
- `restrictedSingletonSubfamilies_ownerUniformConwayClass_zero`
- `restrictedTwoForkFamily_ownerUniformConwayClass_nonzero`
- `restrictedTwoForkFamily_conwayClass_nonzero_iff_selectorObstruction`
- `selectedOwnerUniformTrueQuotientPackage`

visible_projection: Cycle 17 の boundary-generator predicate と Cycle 18 の selector obstruction が、一つの quotient class の zero/nonzero presentation になる。

protected_structure: explicit owner-uniform boundary generator provenance、selected finite coefficient、communication / ownership cover の独立性。

exactness_or_minimality_claim: selected finite receiver 上では quotient class zero と owner-uniform selector existence が同値。
universal quotient property や sheaf exactness は claim しない。

nonfaithfulness_or_failure_mode: predicate-only receiver は同一 obstruction class の carrier を保存しない。local singleton zero だけを見る projection は full-family nonzero を忘れる。

previous_cycle_delta: Cycle 19 の selector / quotient bridge を、selected finite quotient carrier 上の class theorem へ蒸留する。

rival_stress_test: CODEOWNERS dashboard や AI review が同じ mismatch を指摘しても、selector presentation と quotient class presentation の同一性を保証できるかを問う。

## 審判メモ

- 厳密性: G2 A は revise / base 40。selected finite quotient carrier なら boundary は保てるが、
  `true quotient object` label と高 SCORE は強すぎると判定。
- 研究価値: G2 B は accept / base 70。same finite quotient class への圧縮には価値があるが、
  true sheaf `H^1` や arbitrary-cover naturality ではないと判定。
- repo 全体価値: G2 C は accept / base 75。SFT 第V部の paper-ready statement に近づくが、
  selected finite quotient carrier と明記する必要があると判定。
- ライバル比較: G2 D は accept / base 65。rival-facing delta はあるが、Cycle 17/19 の consolidation なので
  incremental と判定。
- G3 axiom audit: pass。`#print axioms` は reported declarations について `propext`,
  `Classical.choice`, `Quot.sound` のみ。`sorryAx`、非相談 `axiom`、`unsafe` はない。
- G3 formalization quality: pass。selected finite quotient carrier、class zero iff boundary/selector、
  singleton zero、restricted full-family nonzero は candidate と一致。arbitrary-family nonzero iff selector obstruction は
  forkwise selectability を仮定し、universal quotient / true sheaf `H^1` / arbitrary-cover naturality は主張しない。
- G3.5 sync: 初回監査は card / Lean evidence はほぼ同期済み、G3 audit 要約と report / Issue ledger が未同期として
  revise。G3 audit 要約はこの追記で解消し、report / Issue ledger は G4 SCORE 確定後に同期する。
- G4 SCORE audit: reduce。base 40、evidence multiplier 2.0、penalty 0、final +80。
  明示 quotient carrier と class API は note-level restatement より強いが、Cycle 17/19 の predicate / selector bridge の
  consolidation であり、新しい obstruction theory ではないため low-bound を採用。

## 関連

- `research/ideas/g-sft-conway-01-owner-uniform-family-quotient.md`
- `research/ideas/g-sft-conway-01-owner-uniform-span-selector.md`
- `research/ideas/g-sft-conway-01-selector-quotient-bridge.md`

## 進捗ログ

- 2026-07-05: G1 候補として作成。
- 2026-07-05: `research/lean/ResearchLean/AG/SFT/ConwayOwnerUniformTrueQuotient.lean` を追加し、
  `cd research/lean && lake env lean ResearchLean/AG/SFT/ConwayOwnerUniformTrueQuotient.lean` と
  `cd research/lean && lake build ResearchLean.AG.SFT.ConwayOwnerUniformTrueQuotient` が通過。
- 2026-07-05: G4 SCORE audit で final +80 に reduce。
