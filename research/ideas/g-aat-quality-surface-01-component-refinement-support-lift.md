---
status: picked
goal: G-aat-quality-surface-01
exploration_role: closer / obstruction / unifier / wildcard
candidate_type: closure / unification / genius-support
capability_category: certificate-transport / repair-potential / invariance / computability / obstruction / quality-surface
expected_base_score: 70
expected_evidence_multiplier: 2.0
expected_final_score: 140
evidence_stage: proved-in-research
rival_advantage: ADL / conformance / dashboard readings may preserve component refinements or visible component unions, but they do not certify the component-level support-lift condition that transports branch-family repair adequacy.
origin: cycle-76
tags: [quality-surface, component-refinement, support-lift, branch-family, adequacy, genius-support]
created: 2026-06-22
cycle: 76
lean: proved-in-research
---

# Component-level refinement support-lift theorem

## 主張

finite branch-family adequacy checker の coverage predicate を、明示的な component-level refinement lift から生成する。
各 target branch code に対して、source branch component を target branch component へ送る `componentLift` と、
source support を target support へ送る support-closure law が与えられるなら、その code は
`CodeReflectionCovered` である。したがって exact target-order enumeration 上で全 code が component-lift covered なら、
source family から target family への `BranchFamilyReflectionAdequate` が従い、source branch-transversal repair clearance は
target branch-transversal clearance へ transport される。

selected witness では、collapsed visible branch family から selected branch family への component lift を構成し、
declared repair support を trace-only から trace plus repair-frontier に拡張すると adequacy checker が `none` を返すことを証明する。
一方、trace-only support では任意の component lift が refined repair-frontier target branch を cover できないことも証明する。

この主張は finite target order、selected exchange branch family、明示的 component lift、declared support predicate に相対化する。
global atlas refinement、canonical source extraction、ArchMap correctness、runtime repair synthesis、global sheaf completeness、
whole-codebase quality は主張しない。

## 候補種別

`closure` / `unification` / `genius-support`

## 依拠

- Cycle 70: `CurvatureBasisExchange.lean` の path-indexed exchange branch family。
- Cycle 73: `BranchReflectionAdequacyKernel.lean` の branch-local `SupportLiftClosedForBranch`。
- Cycle 75: `ArbitraryBranchFamilyAdequacy.lean` の finite target-order adequacy checker。
- tracking Issue #2348 の genius target seed: semantic repair-gluing obstruction theorem。

## 非自明性

Cycle 75 の checker は `CodeReflectionCovered` を supplied predicate として受け取っていた。この候補は、その coverage を
component-level refinement lift と support-closure law から導出する。単なる `SupportLiftClosedForBranch` の言い換えにせず、
component lift が branch membership と support membership の二つを同時に運ぶことを theorem 化し、trace-only では
refined repair-frontier lift が不可能である no-go witness も固定する。

## 数学的興味

repair/refinement の local adequacy を、component 対応の存在だけではなく、branch incidence と repair support の両方を保存する
transport certificate として読む。これにより、finite checker の `none` は「component refinement がある」ではなく、
「repair support を保つ branch-level lift がある」という強い証明条件になる。

## GOAL への前進

Quality Surface の certificate-transport / repair-potential / computability 軸を進める。特に open genius target theorem の
semantic repair-gluing obstruction に必要な support node として、局所 chart adequacy を gluing 側へ運ぶための component-level
support-lift 仮定を Lean-proved artifact にする。

## ライバルに対する有効性

ADL や conformance checker は component refinement、component graph preservation、visible branch union preservation を扱える。
この候補は、それらが repair adequacy transport には不足することを、refined repair-frontier lift の trace-only no-go として固定する。
strong rival の AI-review summary でも、component lift と support-closure law を持たなければ branch-family adequacy transport は証明できない。

## SCORE 見込み

- `score_reason`: Cycle 75 checker の supplied coverage predicate を component-level refinement support lift から生成し、trace-only failure と trace-plus-repair-frontier pass を同じ finite selected witness に載せる。G2 A の strict review に合わせ、既存 adequacy machinery への adapter 性を織り込んで expected base を 70 に下げる。
- `dullness_risk`: `SupportLiftClosedForBranch` の名前替えに落ちると低価値。component lift、support closure、finite checker connection、selected pass、trace-only no-go の全てを evidence に含める。
- `proof_or_evidence_plan`: Research 側 Lean ファイルで `BranchComponentLiftClosed`、`ComponentSupportLiftClosed`、`CodeComponentLiftCovered`、listed coverage から branch-family adequacy、selected component lift pass、trace-only no-go witness、theorem package を証明する。

## CS / SWE への帰結

refinement-aware diagnostic surface が「component refinement は保たれている」と表示するだけでは repair adequacy は足りない。
repair support が refined branch obligation へ lift されるかを certificate として持つ必要がある。この theorem により、future tooling / viewer が
component refinement と repair-support adequacy を分けて表示する数学的根拠が得られる。

## 証明・根拠

Lean 証拠は `research/lean/ResearchLean/AG/QualitySurface/ComponentRefinementSupportLift.lean` に固定した。

- `BranchComponentLiftClosed`
- `ComponentSupportLiftClosed`
- `branchComponentLiftClosed_gives_supportLiftClosedForBranch`
- `CodeComponentLiftCovered`
- `codeComponentLiftCovered_gives_codeReflectionCovered`
- `listedComponentLiftCoverage_gives_branchFamilyAdequacy`
- `firstUncoveredComponentLift?_none_gives_branchFamilyAdequacy`
- `selectedCollapsedComponentLift`
- `selectedCollapsedComponentLift_covers_code`
- `traceOnly_componentLift_not_covers_refinedRepairFrontier`
- `selectedComponentLift_firstUncovered_none`
- `selectedComponentLift_gives_branchFamilyAdequacy`
- `componentLift_transports_selectedReflection`
- `componentLift_closes_selected_residual`
- `componentRefinementSupportLift_package`

G3 実績:

- `cd research/lean && lake env lean ResearchLean/AG/QualitySurface/ComponentRefinementSupportLift.lean`: pass。
- `cd research/lean && lake build ResearchLean`: pass。
- `#print axioms`: `BranchComponentLiftClosed`、`ComponentSupportLiftClosed`、`branchComponentLiftClosed_gives_supportLiftClosedForBranch`、`CodeComponentLiftCovered`、`codeComponentLiftCovered_gives_codeReflectionCovered`、`listedComponentLiftCoverage_gives_branchFamilyAdequacy`、`traceOnly_componentLift_not_covers_refinedRepairFrontier` は axiom-free。`firstUncoveredComponentLift?_none_gives_branchFamilyAdequacy`、selected pass / package theorem は標準 `propext` のみ。`sorryAx`、custom axiom、`Classical.choice`、`Quot.sound`、`unsafe` は出ていない。

## 審判メモ

- 厳密性: revise 後 accept。base 70。claim boundary は強いが、generic bridge は既存 `SupportLiftClosedForBranch` と Cycle 75 coverage machinery への adapter 性があるため、expected base を 84 から 70 に下げた。core declarations は axiom-free、selected / package theorem は標準 `propext` のみ。
- 研究価値: accept。base 84。component refinement、support closure、finite adequacy checking、selected pass、trace-only failure を一つの theorem package に圧縮し、semantic repair-gluing target の support node を作る。
- repo 全体価値: accept。base 84。Lean / future tooling / report surface に、component refinement と repair-support-preserving adequacy の区別を与える。
- ライバル比較: accept。base 84。ADL / static analyzer / conformance checker / dashboard / AI-review に対し、support-preserving branch-family transport と refined repair-frontier no-go を Lean-fixed evidence として与える。
- genius: open target の support cycle。target unlock ではなく通常 SCORE の予定。
- G3 公理検査: pass。15 declaration は axiom-free または標準 `propext` のみ。`sorryAx`、custom axiom、`Classical.choice`、`Quot.sound`、`unsafe` はない。
- G3 形式化品質: pass。`ComponentSupportLiftClosed` は branch-restricted ではなく source support 全体に対する保存 law なので必要最小よりやや強いが、候補カードの support-closure law と一致し、vacuous ではない。
- G4 SCORE 監査: confirm。base 70、evidence multiplier 2.0、penalty 0、final +140。genius unlock ではなく open target の support cycle。

## G4 SCORE 監査結果

- score_verdict: confirm。
- base_score: 70。
- evidence_multiplier: 2.0。
- penalty: 0。
- final_score: 140。
- category: genius-support / certificate-transport / repair-potential / computability。
- genius_verdict: not-applicable。これは target unlock ではなく、semantic repair-gluing obstruction theorem の component-level support-lift node を進める通常 SCORE support cycle である。
- total_delta: 10258 -> 10398。active threshold 12000 までは残り 1602。
- research_kiri_contribution: positive support-cycle contribution。phase boundary ではない。

## 追加 required fields

- `mathematical_interest`: component-level refinement を branch incidence と repair support の二重 transport certificate として読む点。
- `goal_advancement`: local adequacy checker を semantic repair-gluing target へ運ぶための support-lift node を確立する。
- `planned_theorem_names`: `branchComponentLiftClosed_gives_supportLiftClosedForBranch`, `listedComponentLiftCoverage_gives_branchFamilyAdequacy`, `selectedComponentLift_gives_branchFamilyAdequacy`, `traceOnly_componentLift_not_covers_refinedRepairFrontier`, `componentRefinementSupportLift_package`
- `visible_projection`: component refinement / visible component union。これだけでは branch-family repair adequacy transport に faithful ではない。
- `protected_structure`: branch component lift, support-closure law, target branch incidence, refined repair-frontier no-go witness。
- `exactness_or_minimality_claim`: exact target-order enumeration と component-lift coverage に相対化した adequacy transport。global canonical minimality は主張しない。
- `nonfaithfulness_or_failure_mode`: trace-only support cannot cover the refined repair-frontier target branch by any component lift.
- `previous_cycle_delta`: Cycle 75 の arbitrary checker に component-level coverage generator を与える。
- `rival_stress_test`: component graph / visible union preservation だけでは trace-only failure を検出できず、support-preserving branch lift が必要である。
- `genius_potential`: no immediate unlock
- `genius_target`: Semantic repair-gluing obstruction theorem for finite atom-supported quality atlases
- `genius_support_role`: local adequacy pass を semantic repair-gluing theorem の support map へ運ぶための component-level support-lift node。

## 関連

- `research/ideas/g-aat-quality-surface-01-branch-reflection-adequacy-kernel.md`
- `research/ideas/g-aat-quality-surface-01-arbitrary-branch-family-adequacy-checker.md`
- `research/ideas/g-aat-quality-surface-01-naive-refinement-support-counterexample.md`

## 進捗ログ

- 2026-06-22: G1 四ロール候補 pool で component-level refinement support-lift が closer / obstruction / unifier / wildcard の全てに現れた。semantic repair cocycle witness は次の高期待 genius-support 候補として残し、Cycle 76 ではその局所 adequacy transport に必要な support-lift node を picked とした。
- 2026-06-22: Lean 証拠を `ComponentRefinementSupportLift.lean` に固定し、単体 `lake env lean` が通った。
- 2026-06-22: G2 A の revise を受け、expected base を 70、expected final を 140 に下げた。既存 machinery への adapter 性を認めたうえで、component lift generator、trace-plus-repair-frontier pass、trace-only no-go を主価値として残す。
- 2026-06-22: G2 A が revise 後 accept。G2 四審判は A=70, B=84, C=84, D=84。strict base 70、expected final 140 として G3 へ進む。
- 2026-06-22: G3 公理検査と形式化品質監査が pass。core bridge / no-go は axiom-free、selected checker / package layer は標準 `propext` のみ。
- 2026-06-22: G4 SCORE 監査が confirm。base 70、multiplier 2.0、final +140。total は 10398 / threshold 12000、残り 1602。
