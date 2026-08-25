# G-110-aat-doctrine-fiber-product — doctrine fiber product と base change

- 一次仕様: [`research/goals/G-110-aat-doctrine-fiber-product.md`](../goals/G-110-aat-doctrine-fiber-product.md)
- tracking Issue: [#4034](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4034)
- target theorem: Doctrine Fiber Product and Base Change Theorem
- proof state: `active / target-proof-checkpoint`(Cycle 107 empty-wrapper audit の
  修正後 PR review 待ち。2026-08-24 改訂前カードは Cycle 75 で `target-refuted`)
- completion candidate: `no`

この report は固定 GOAL の証拠索引、proof obligation delta、material premise
監査を記録する。target statement と completion criteria の正本は GOAL カードで
あり、この report はそれらを再定義しない。target-theorem mode のため SCORE は
使わない。

## 2026-08-24 GOAL revision — unconditional diagnostic covariance

Cycle 75 は旧固定カードの (D) が要求した source-vanishing /
target-nonvanishing witness を
`no_bcDiagnosticQualifiedVanishingCounterexample` で否定し、旧カードを
`target-refuted` として停止した。この停止結果を保持した上で、人間裁定により
G-110(D) を source-fiber-qualified な実 BC 二経路上の無条件 forward
covariance へ改訂した。

- (d1)–(d3) は Cycle 74 の actual-route package を維持する。
- (d4) は canonical `mapEdgeReselection`、(d5) は `coherentAt_map`、
  (d6) は一般 fiberwise functor と direct / via-base 実経路の
  `TransportObstructionVanishes` 保存とする。
- 旧 `H_bc`・`BCConditionSyntax` checker/bridge・pointwise raw-defect
  保存・orbit map は改訂後 G-110 の completion obligation から外す。
  既存 declaration は履歴 artifact として保持する。
- 初期 raw defect と source reselection がともに非恒等で、source coherence
  と両 target coherence が同時に発火する named finite witness を K3 の残る
  nonvacuity obligation とする。
- full-domain indexed action は Gr4 gate 第一項、diagnostic conservativity /
  reflection / orbit exactness と obstruction-killing finite witness は独立した
  Gr4 gate 第五項へ移管する。
- Cycle 75 の reviewed declarations は改訂後 (d4)–(d6) の既存候補である。
  新 fixed card に対する statement match・proof-use・finite nonvacuity の監査を
  次の target-theorem cycle で行うまでは、K3 completion と数えない。

## Cycle ledger

### Cycle 107 — fixed-ledger `FiniteModelLift` empty-wrapper audit

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 107
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: afa38f884d6b09603a86e64d862d1d927f099336
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 107 selection comment 5406256194
  proof_dag_predecessors:
    - globalCartesianLift
    - cartesianLiftNonexistence_isEmpty
    - rightBranch_isEmpty
    - doctrineFiberProductAndBaseChangeTheorem
    - Cycle 106 independent completion audit
  proof_obligation: recover the omitted fixed-ledger FiniteModelLift premise, formalize why a bare no-lift implication is empty under the selected global-left theorem, and preserve the separate data-level arbitrary-target package reindexing and strong-lift reflection route as the live obligation
  selection_reason: the completion premise lane found that Cycle 106 silently dropped the unconditional FiniteModelLift ledger row; this is the only remaining mathematical completion item and must be tested against the already selected B branch
  expected_result_type: proof-checkpoint
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: fixed the universe-zero CartesianLiftNonexistence source and canonical ULift-carrier target of the no-lift corollary as named types and proved both empty from the selected global-left theorem; this excludes counting a bare implication by empty elimination but does not refute the structural arbitrary-target package reindexing and strong-lift reflection route
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteModelLiftObstruction.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - FiniteModelLiftSource
    - FiniteModelLiftTarget
    - finiteModelLiftSource_isEmpty
    - finiteModelLiftTarget_isEmpty
    - finiteModelLiftSource_not_nonempty
  claim_mapping:
    fixed_goal_clauses:
      - target theorem B lines 230-248 selects either the carrier-global left existence branch or a right branch containing a concrete finite no-lift counterexample and requires FiniteModelLift for that counterexample
      - target artifacts lines 629-634 and material premise ledger lines 799-801 list FiniteModelLift unconditionally as discharge-required
      - accepted predecessor reviews reject empty elimination and retain a data-level package reindexing and strong-lift reflection route
    selected_branch_facts:
      - globalCartesianLift supplies a strong lift for every carrier, every realized input, and every target package
      - cartesianLiftNonexistence_isEmpty therefore makes the exact source and target counterexample types empty
      - rightBranch_isEmpty excludes the only branch whose theorem output contains a concrete finite counterexample
    consequence:
      - a bare function from FiniteModelLiftSource to FiniteModelLiftTarget can be inhabited only through its empty domain and therefore does not establish the structural transport artifact
      - the existing generated-endpoint reflection demonstrates that actual high strong lifts can materially produce low strong lifts on a restricted endpoint class
      - the live route is to generalize package universe rebasing and reflection to arbitrary CartesianLiftNonexistence.targetPackage
    acceptance_point: reusable kernel-checked rejection of the empty-wrapper route only; no FiniteModelLift discharge, no no-go, and no target completion claim
audits:
  premise_delta:
    discharged:
      - exact classification of the FiniteModelLift source and lifted target under the selected global-left branch
      - proof that the bare no-lift source and target are empty under the selected branch
    remaining:
      - arbitrary-target package universe reindexing
      - reflection of every supplied lifted strong lift to the original target package with generated graph laws
      - fixed-ledger FiniteModelLift no-lift corollary derived from that structural reflection
  certificate_provenance:
    - both emptiness theorems are specializations of the already reviewed globalCartesianLift consequence
    - no no-lift witness, target package, transport graph, or contradiction is accepted from a caller
  proof_use:
    - finiteModelLiftSource_not_nonempty consumes finiteModelLiftSource_isEmpty
  route_integrity: the audit targets the no-lift corollary types named by the GOAL but explicitly does not promote them to the complete package-reindexing and reflection signature
  nonvacuity: the bare corollary cannot fire under the selected branch; the existing generated-endpoint strong-lift reflection remains the positive structural checkpoint to generalize
  static_check:
    focused_module: passed
    targeted_module_build: passed (4023 jobs; no Research aggregate or full build)
    declaration_count: 6 namespace declarations
    axiom_audit: standard axioms only
  review:
    independent_completion_audit: Cycle 106 rejected because FiniteModelLift was omitted from the final premise ledger
    initial_exact_head_pr_review: Major revisions; goal-defect/no-go claim exceeded the evidence
    repaired_exact_head_pr_review: four lanes No major findings at 889f6f04cfef0ae84780f862479b9a2f8e600019
next:
  proof_obligation: construct canonical universe rebasing for every finite-carrier target package and reflect every supplied lifted strong-cartesian lift back to that original package; retain exact component graphs and derive the named no-lift corollary only afterward
  stop_candidate: none
```

### Cycle 106 — final A–E target theorem assembly candidate

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 106
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: d8b170e1fa3d5748ac1ee1a0a64ebb6d94e9f7f2
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_dag_predecessors:
    - doctrinePullback_isPullback
    - globalDisjunctionArtifact
    - coreBeckChevalleyMate_isIso
    - finiteAxisFold_public_not_mateCoherentRel_on_orbit
    - finiteAxisFold_authoredComparison_orbit_nontrivial
    - qualifiedDiagnosticBaseChangeD1D3
    - finiteDiagnosticCovariance_nonvacuous
    - horizontalPastedBCDiagnosticCrossRouteCompatibility
    - verticalPastedBCDiagnosticCrossRouteCompatibility
  proof_obligation: state and prove one carrier-polymorphic fixed theorem whose five fields directly consume the accepted A-E producers, exactness and noncanonicity witnesses, actual-route diagnostic covariance, finite nonvacuity, and both pasted diagnostic compatibility laws
  selection_reason: Cycle 105 discharged the remaining K4 cross-route obligation; the only remaining mathematical node is final target-statement assembly over the reviewed artifact spine
  expected_result_type: completion-candidate
result:
  proposed_result_type: completion-candidate
  proof_obligation_delta: the fixed target now has one named Lean theorem assembling A fiber-product universality and proper finite firing, B the named global disjunction artifact and its produced-regime lift, C pointed pullback exact mates and the public MateCoherentRel strict/lax pair with full-orbit failure, nontrivial orbit and replacement laws, D unconditional d1-d6 covariance and named finite nonvacuity, and E finite-code pullback closure with horizontal and vertical pasted diagnostic compatibility
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/TargetTheorem.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - DoctrineFiberProductLayer
    - CartesianLiftLayer
    - BeckChevalleyLayer
    - DiagnosticBaseChangeLayer
    - PastingClosureLayer
    - DoctrineFiberProductAndBaseChangeTheorem
    - doctrineFiberProductAndBaseChangeTheorem
    - globalDisjunctionArtifact
    - cartesianRegimeOfDisjunction
    - finiteAuthoredBCDatumSquare_mateCoherentRel
    - finiteAxisFold_public_not_mateCoherentRel_on_orbit
    - finiteAxisFold_authoredComparison_orbit_nontrivial
    - mateCoherentRel_replacePresentation_iff
  claim_mapping:
    theorem_names:
      - doctrineFiberProductAndBaseChangeTheorem
    source_labels:
      - target theorem A: doctrine fiber product universality and nondegeneracy
      - target theorem B: carrier-global strong cartesian lift branch
      - target theorem C: Beck-Chevalley exactness and relative canonicity obstruction
      - target theorem D: source-fiber-qualified actual-route diagnostic covariance
      - target theorem E: pullback and diagnostic pasting closure
    undischarged_assumptions:
      - fixed-ledger arbitrary-target FiniteModelLift
      - independent completion-candidate math-lean-review
      - report correction after final review
    acceptance_point: every headline field is generated by a reviewed theorem; callers supply only the carrier and its decidable Atom equality, while theorem-internal direction hypotheses remain universally quantified inside the corresponding A-E fields
    port_status: unported (Research-proved)
audits:
  premise_delta:
    discharged:
      - final A-E theorem statement and constructor
      - proof-use of the named B branch artifact and regime producer in the final constructor
      - public C relation, strict/lax pair, full-orbit failure, orbit nontriviality and replacement invariance
      - fixed finite nondegeneracy and diagnostic nonvacuity witnesses
    remaining:
      - fixed-ledger arbitrary-target FiniteModelLift
      - completion-candidate final review after that premise is discharged
  static_check:
    focused_module: passed
    axiom_audit: standard axioms only
```

### Cycle 105 — pasted diagnostic cross-route K4 candidate

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 105
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: 82a0c747d777c6aeb96e19386ed61261c155520b
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_dag_predecessors:
    - HorizontalPastedBCDiagnosticNaturalityPredecessor
    - VerticalPastedBCDiagnosticNaturalityPredecessor
    - coreFiberCompositor_assoc_via_g106
    - verticalMateTargetAlignment_eq_selectedCompositor_inv
  proof_obligation: assemble the actual horizontal and vertical pasted diagnostic routes into four-side natural-isomorphism squares, expose their three-stage component actions and arbitrary mapped reselections, and proof-use the horizontal G-106 and vertical selected-reindex coherence in the diagnostic comparison
  selection_reason: Cycle 104 identified missing cross-route equations rather than a missing external API; the target-theorem loop therefore constructs the required transport and square APIs in one larger K4 packet
  expected_result_type: K4-completion-candidate
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: arbitrary target reselections now transport invertibly across natural isomorphisms; the horizontal and vertical outer/component mate equations generate split diagnostic squares with package, comparator, path, coherence and vanishing equivalences; the same normalized outer functors carry their d2-d6 composition packages; both literal component routes are exposed as three successive map and mapped-reselection actions; the horizontal source alignment and four-side package square consume the G-106/G-109 associativity bridge, while the vertical target diagnostic path consumes the generated selected-reindex compositor
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticNaturalIsoTransport.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticNaturalIsoSquare.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticPastedIsoSquare.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticPastedCrossRouteCompatibility.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - transportEdgeReselectionAlongNaturalIso
    - coherentAt_naturalIso_iff
    - transportObstructionVanishes_naturalIso_iff
    - FiberwiseDiagnosticNaturalIsoSquareCompatibility
    - horizontalPastedMateIsoSquare
    - verticalPastedMateIsoSquare
    - horizontalDataMateSourceAlignment_app_eq_g106Route
    - horizontalPastedPackageSquare_via_g106
    - verticalMateTargetAlignmentIso_hom_eq_selectedCompositor_inv
    - verticalPastedDiagnosticTargetPath_via_selectedCompositor
    - HorizontalPastedBCDiagnosticCrossRouteCompatibility
    - VerticalPastedBCDiagnosticCrossRouteCompatibility
  claim_mapping:
    theorem_names:
      - horizontalPastedBCDiagnosticCrossRouteCompatibility
      - verticalPastedBCDiagnosticCrossRouteCompatibility
    source_labels:
      - target theorem E: horizontal and vertical pasting compatibility for generated BC diagnostics
    conjuncts:
      - the normalized outer direct and via routes used by the split square themselves carry generated d2-d6 composition packages
      - the four separately exposed mate sides commute and generate arbitrary-reselection, comparator, complete-path, coherence and vanishing compatibility at the common endpoint
      - literal component direct and via-base diagnostics agree with their genuine three-stage successive map and mapped-reselection actions
      - the horizontal source alignment is normalized through coreFiberCompositor_assoc_via_g106 and that normal form proves the same four-side package equation containing the outer mate and target alignment
      - the vertical target alignment is generated by the inverse selectedCoreFiberReindexCompositor constructed in G-110
    undischarged_assumptions:
      - independent review of this K4 candidate
      - final A-E target theorem assembly over the accepted artifact spine
      - completion-candidate report and tracking synchronization followed by independent final math-lean review
    acceptance_point: all route functors, mate isomorphisms, mapped reselections, coherence and vanishing equivalences are generated from the fixed pasted presentations and ordinary source-fiber incidence; no target comparison or certificate is a caller input
    port_status: unported (Research-proved)
audits:
  premise_delta:
    discharged:
      - natural-isomorphism transport and inverse reflection for arbitrary target reselections
      - split component-to-outer diagnostic square in both pasting directions
      - genuine three-stage component map and mapped-reselection equations
      - horizontal transportAlong_comp_coherence proof-use through the actual source alignment and four-side package square
      - vertical generated reindex-compositor identification
    remaining:
      - independent K4 candidate review
      - final A-E theorem assembly and completion audit
  static_check:
    focused_modules: passed
    axiom_audit: standard axioms only
```

### Cycle 104 — natural-isomorphism diagnostic transport predecessor

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 104
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: 5891860b1e8d2b938cb486e31203a21c517123c7
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5404040958
  proof_dag_predecessors:
    - horizontalLiteralComponentMates_eq_outerCanonicalMate
    - verticalLiteralComponentMates_eq_outerCanonicalMate
    - horizontalPastedBCDiagnosticCompositionCompatibility
    - verticalPastedBCDiagnosticCompositionCompatibility
  proof_obligation: construct the missing natural-isomorphism action on fiberwise diagnostic data and apply it to the reviewed horizontal and vertical literal component-mate equations, while retaining actual outer-route d2-d6 factorization as the next K4 predecessor
  selection_reason: Cycle 103 isolated the outer-route factorization predecessor; the next material obligation is the component-square-to-outer diagnostic identification, and the absent API must be constructed rather than treated as a stop condition
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticBaseChangeAutomorphism.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticNaturalIsoCompatibility.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticPastedNaturalIsoCompatibility.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - replacing isomorphic mapped packages by literal equality
    - assuming exactness of pasted alignments instead of deriving it
    - recording component-to-outer mate equality without transporting comparator, reselection, path, coherence and vanishing data
    - bundling the G-106/G-109 bridge without coupling it to the actual pasted diagnostic equations
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: arbitrary naturally isomorphic core-fiber functors now generate pointwise package, edge, comparator, mapped-reselection and path naturality plus paired forward coherence and vanishing; the horizontal and vertical literal component mates are promoted to exact aligned natural isomorphisms by the reviewed outer equations; direction-specific predecessor packages retain this naturality beside both actual outer-route factorizations without claiming the missing cross-route commutative law
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticBaseChangeAutomorphism.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticNaturalIsoCompatibility.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticPastedNaturalIsoCompatibility.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - coreFiberFunctorMapAut_iso_naturality
    - coreFiberFunctorPackageAutHom_iso_naturality
    - FiberwiseDiagnosticNaturalIsoCompatibility
    - fiberwiseDiagnosticNaturalIsoCompatibility
    - horizontalAlignedLiteralComponentMateIso_eq_outer
    - verticalAlignedLiteralComponentMateIso_eq_outer
    - HorizontalPastedBCDiagnosticNaturalityPredecessor
    - horizontalPastedBCDiagnosticNaturalityPredecessor
    - VerticalPastedBCDiagnosticNaturalityPredecessor
    - verticalPastedBCDiagnosticNaturalityPredecessor
  claim_mapping:
    theorem_names:
      - horizontalPastedBCDiagnosticNaturalityPredecessor
      - verticalPastedBCDiagnosticNaturalityPredecessor
    source_labels:
      - target theorem E predecessor: aligned-mate diagnostic naturality and actual outer-route composition packages on ordinary interpretations with southwest source-fiber incidence
    conjuncts:
      - each direction retains both actual outer direct and via-base d2-d6 route-composition packages
      - the aligned literal component mate generates package, edge, comparator, mapped-reselection, reselected-edge and reselected-path compatibility
      - source coherence and source obstruction vanishing independently generate both target conclusions; this paired forward covariance is not a cross-route equality
      - the component comparison natural isomorphism equals the aligned outer canonical mate natural isomorphism
    undischarged_assumptions:
      - equations coupling successive component-square diagnostic maps to the outer direct and via-base diagnostic maps
      - comparator, mapped-reselection, path, coherence-preservation and vanishing-preservation commutation under those component-to-outer alignments
      - actual horizontal and vertical specialization and proof-use of the G-106/G-109 bridge retaining transportAlong_comp_coherence
      - final K4 assembly
      - final A-E target theorem assembly over the accepted artifact spine
      - completion-candidate report and tracking synchronization followed by independent final math-lean review
    acceptance_point: all comparison data are generated from the fixed horizontal or vertical pasted presentation and the accepted mate equations; no target comparator, mapped reselection, coherence proof, vanishing proof or comparison certificate is a caller input
    port_status: unported (Research-proved)
audits:
  premise_delta:
    discharged:
      - natural-isomorphism compatibility for endpoint group action, mapped packages, edge isomorphisms, comparators, reselections and complete reselected paths
      - paired coherence and vanishing conclusions generated from the same source witnesses
      - exact horizontal and vertical aligned literal-component comparisons derived from their equality with exact outer canonical mates
    remaining:
      - component-square sequential diagnostic action to outer diagnostic action commutative laws
      - comparison-relative coherence and vanishing compatibility, beyond paired forward covariance
      - proof-used specialization of the G-106/G-109 bridge in those commutative laws
      - final K4 assembly
      - final A-E theorem assembly and completion review
  certificate_provenance:
    discharged:
      - pointwise package comparisons are evaluations of the generated aligned natural isomorphism
      - comparator and mapped-reselection equations are consequences of naturality of the endpoint group action
      - paired target coherence and vanishing fields are independently generated by coherentAt_map and transportObstructionVanishes_map
      - horizontal and vertical exactness are derived through the Cycle 102 literal mate equalities, not supplied
  proof_use:
    discharged:
      - Cycle 102 literal component-to-outer mate equations construct the aligned comparison isomorphisms
      - Cycle 103 actual-route d2-d6 packages populate outerRouteComposition
    remaining:
      - the Cycle 82 bridge and transportAlong_comp_coherence are not proof-used by the current aligned diagnostic naturality predecessor
  structure_field_escape:
    discharged:
      - FiberwiseDiagnosticNaturalIsoCompatibility is output data whose fields are constructed by one theorem; it is not an input qualification
      - the direction-specific predecessor structures accept only ordinary interpretation and source-fiber incidence
  route_integrity:
    discharged:
      - source functors are the normalized outer direct routes selected by the generated paste presentation
      - target functors are the literal successive component via-base routes, whose aligned mate equals the outer canonical mate
      - both actual outer direct and via-base factorizations remain present in the same direction package
    remaining:
      - the retained outer-route composition and aligned-mate naturality fields are not yet coupled by a diagnostic commutative equation
  anti_weakening:
    discharged:
      - mapped packages are related by explicit natural-isomorphism components rather than identified by an invalid equality
      - no square-independent substitute functor or caller-supplied target certificate is used
    initial_review:
      - four lanes found that the first K4 claim was a product of uncoupled predecessor certificates
      - coherentAt_pair and vanishing_pair were renamed as forward pairs because they do not consume the comparison
      - the detachable generic bridge field was removed instead of being counted as proof-use
      - the direction structures and report were narrowed from K4 compatibility to naturality predecessor
validation:
  focused_lean:
    - BCDiagnosticBaseChangeAutomorphism.lean: static check passed; standard axioms only
    - BCDiagnosticNaturalIsoCompatibility.lean: static check passed; standard axioms only
    - BCDiagnosticPastedNaturalIsoCompatibility.lean: static check passed; standard axioms only
  targeted_build:
    - ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticPastedNaturalIsoCompatibility: passed; standard axioms only
  forbidden_builds:
    - ResearchLean aggregate/full build not run
next_obligation: construct horizontal and vertical commutative laws relating successive component-square diagnostic actions to the outer direct and via-base actions, and make those laws proof-use the actual G-106/G-109 bridge before K4 or final assembly is claimed
```

### Cycle 103 — outer pasted-presentation internal route factorization

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 103
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: 691c3e3a3b4d67b8ceae6f6e6f75ab5e55bceb8b
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5403833187
  proof_dag_predecessors:
    - coreFiberFunctorPackageAutHom_comp
    - mapEdgeReselection_comp
    - coherentAt_map
    - transportObstructionVanishes_map
    - bcDiagnosticDirectFunctor
    - bcDiagnosticViaBaseFunctor
    - HorizontalBCPastingData.pastePresentation
    - VerticalBCPastingData.pastePresentation
  proof_obligation: extend the accepted generic d2 and d4 composition laws through d3 transported-data generation, d5 coherence preservation and d6 vanishing preservation, then specialize this internal two-factor packet to both actual direct and via-base routes on horizontal and vertical outer pasted BC presentations
  selection_reason: Cycle 102 closed the C comparison mate-pasting packet; batching the remaining generic D composition layers with all four outer-route internal factorizations gives one reviewable predecessor packet before componentwise-to-outer K4 identification
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticPastingCoherence.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticPastedRouteCompatibility.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - proving d3 comparator composition without preserving generated edge and base-equation fields
    - accepting either target coherence or vanishing certificate from the caller
    - relabeling a generic total-category action as an actual pasted BC route
    - promoting outer-route factorization to componentwise K4 compatibility
  unchecked:
    - identification of the factorized outer diagnostic packages with successive component-square diagnostic maps through the accepted C compositors and mate equations
    - final K4 assembly and final DoctrineFiberProduct theorem assembly/completion review
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: the complete generated fiberwise datum now commutes with two-stage functor transport; coherence and vanishing are generated successively; a universal theorem bundle collects d2 through d6 and is instantiated for the internal direct and via-base factors of both horizontal and vertical outer pasted presentations from ordinary interpretations plus southwest source-fiber incidence
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticPastingCoherence.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticPastedRouteCompatibility.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - fiberwiseAdmissibleTransportData_map_comp
    - fiberwiseAdmissibleTransportData_transported_comp
    - coherentAt_map_comp
    - transportObstructionVanishes_map_comp
    - BCDiagnosticCompositionCompatibility
    - diagnosticCompositionCompatibility
    - bcDiagnosticDirectFunctor_eq_factors
    - bcDiagnosticViaBaseFunctor_eq_factors
    - bcDiagnosticDirectCompositionCompatibility
    - bcDiagnosticViaBaseCompositionCompatibility
    - horizontalPastedBCDiagnosticCompositionCompatibility
    - verticalPastedBCDiagnosticCompositionCompatibility
  claim_mapping:
    theorem_names:
      - horizontalPastedBCDiagnosticCompositionCompatibility
      - verticalPastedBCDiagnosticCompositionCompatibility
    source_labels:
      - target theorem E predecessor: internal d2-d6 factorization of each actual outer diagnostic route generated by a horizontal or vertical pasted presentation
    conjuncts:
      - the generated horizontal outer presentation selects actual direct and via-base two-factor routes, each carrying d2 through d6 composition compatibility for every source-fiber-qualified ordinary interpretation
      - the generated vertical outer presentation selects actual direct and via-base two-factor routes, each carrying d2 through d6 composition compatibility for every source-fiber-qualified ordinary interpretation
    undischarged_assumptions:
      - componentwise-to-outer identification of the diagnostic packages through the accepted pasting compositors and C mate equations
      - final K4 theorem assembly and final A-E completion review
    acceptance_point: the route factors are definitionally the factors of bcDiagnosticDirectFunctor and bcDiagnosticViaBaseFunctor on each generated pastePresentation; no square-independent substitute functor or caller-supplied target certificate occurs; component-square-to-outer compatibility is not claimed by this packet
    port_status: unported (Research-proved)
audits:
  premise_delta:
    discharged:
      - d3 equality of complete transported data under arbitrary two-stage generated fiber functors, including comparator composition through d2
      - d5 successive target coherence generated from one source coherence witness
      - d6 successive target vanishing generated from the same functorial preservation route
      - horizontal and vertical outer pastePresentation specialization for both actual direct and via-base route factors
    remaining:
      - componentwise-to-outer diagnostic comparison through accepted C compositor and mate-pasting APIs
      - final K4 and DoctrineFiberProduct theorem assembly/completion review
  certificate_provenance:
    discharged:
      - endpoint action and target comparator are generated by coreFiberFunctorPackageAutHom and its composition theorem
      - target edge isomorphisms, strong-cocartesian fields and two-cell base equations are generated by FiberwiseAdmissibleTransportData.map and transported
      - both target coherence stages and both vanishing stages are generated by coherentAt_map and transportObstructionVanishes_map
    unresolved: []
  proof_use:
    used:
      - coreFiberFunctorPackageAutHom_comp
      - mapEdgeReselection_comp
      - coherentAt_map
      - transportObstructionVanishes_map
      - bcDiagnosticDirectFunctor
      - bcDiagnosticViaBaseFunctor
      - HorizontalBCPastingData.pastePresentation
      - VerticalBCPastingData.pastePresentation
    unused: []
  structure_field_escape: none-found
  universal_law_package: BCDiagnosticCompositionCompatibility is a bundle of universally proved functorial laws, not a discriminating predicate; diagnosticCompositionCompatibility constructs it for every composable pair, so a negative instance is mathematically unavailable and is not used as nonvacuity evidence
  route_integrity: horizontal and vertical results quantify over their generated outer pastePresentation and BCDiagnosticSourceFiberIncidence; the direct and via-base factors are public definitional factorizations of the actual route functors
  target_fitting: none-found
  vacuity: conditional theorem domain is fixed and non-answer-bearing, but a joint named witness for BCDiagnosticInterpretation plus BCDiagnosticSourceFiberIncidence on each horizontal and vertical pastePresentation is not audited in this cycle; Cycle 76 separately retains revised-card K3 nonidentity firing and Cycle 77 separately retains pasted-square closure witnesses
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: initial review found the E source label too broad; the corrected mapping records only internal outer-route d2-d6 factorization, leaves successive component-square-to-outer compatibility open, and remains a target-proof-checkpoint
  validation_refs:
    - focused BCDiagnosticPastingCoherence single-file elaboration: pass
    - BCDiagnosticPastingCoherence axiom audit: 8 declarations, standard axioms only
    - focused BCDiagnosticPastedRouteCompatibility single-file elaboration: pass
    - BCDiagnosticPastedRouteCompatibility axiom audit: 21 declarations, standard axioms only
    - targeted BCDiagnosticPastingCoherence single-module build: pass
    - Research aggregate or full build: not run
  blocking_findings: []
  next_obligation: identify the factorized horizontal and vertical outer diagnostic packages with successive component-square diagnostic maps through the accepted C compositors and literal mate equations, then assemble K4 and the final theorem
```

### Cycle 102 — typed outer comparison and component-to-outer mate packet

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 102
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: f0eb4ce0c435cb5dcfa73451d2f83e9aa2f3c058
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5402766742
  proof_dag_predecessors:
    - horizontalCompositorAlignedComponentSquare_eq_componentComparison
    - verticalTypedOuterComparisonNormalForm
    - horizontalBCPastingOuterBoundaryComparison
    - verticalBCPastingOuterBoundaryComparison
    - horizontalBCPastingComparison_eq_outer
    - verticalBCPastingComparison_eq_outer
    - horizontalBCPastingOuterCanonicalMate_eq
    - verticalBCPastingOuterCanonicalMate_eq
    - horizontalBCPasting_coreBeckChevalleyMate_vcomp
    - verticalBCPasting_coreBeckChevalleyMate_hcomp
    - mateEquiv_conjugateEquiv_vcomp
    - verticalNormalizedNorthwest_mateEquiv_vcomp
  proof_obligation: prove both typed normalized outer comparisons equal the named outer boundary comparisons already identified with the independently generated semantic comparisons, then prove both literal component-mate composites equal the canonical normalized outer mate after generated source and target alignments
  selection_reason: the prior target-blocked classification incorrectly treated a missing direction-qualified transport API as a stop condition; target-theorem-loop instead requires constructing that API, and batching both directions through the final mate equations avoids repeated auxiliary-only review cycles
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingTypedOuterComparisonEquality.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingComponentToOuterMate.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - rewriting a direction-independent northwest alias through a dependent functor endpoint
    - cancelling vertical right-adjoint conjugates only after expanding them into unit/counit components
    - confusing covariant outer-square equality with the contravariant mate equation
    - promoting K2 pasting completion to the full target theorem
  unchecked:
    - actual horizontal and vertical specialization of the accepted D diagnostic composition laws
    - final K4 integration of D compatibility with the accepted square closure and G-106 / G-109 coherence bridge
    - final DoctrineFiberProduct theorem assembly and completion review
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: horizontal and vertical typed outer comparison normal forms now equal their named normalized outer boundary comparisons, whose independent semantic provenance was established by predecessor uniqueness theorems, and both literal generated component-mate composites commute with the corresponding canonical outer mate under named generated alignments
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingTypedOuterComparisonEquality.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingComponentToOuterMate.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - horizontalTypedOuterComparisonNatTrans_eq_outer
    - verticalTypedOuterComparisonNormalForm_eq_outer
    - horizontalDataNormalizedNorthwestLeftTransportSquare
    - horizontalDataTypedOuterComparisonNatTrans_eq_outer
    - horizontalComponentMate_eq_outerCanonicalMate
    - horizontalLiteralComponentMates_eq_outerCanonicalMate
    - verticalMateTargetCancellation
    - verticalDecomposedMateAlignment
    - verticalTypedOuterMate_eq_decomposed
    - verticalComponentMate_eq_outerCanonicalMate
    - verticalLiteralComponentMates_eq_outerCanonicalMate
  claim_mapping:
    theorem_names:
      - horizontalTypedOuterComparisonNatTrans_eq_outer
      - verticalTypedOuterComparisonNormalForm_eq_outer
      - horizontalComponentMate_eq_outerCanonicalMate
      - verticalComponentMate_eq_outerCanonicalMate
      - horizontalLiteralComponentMates_eq_outerCanonicalMate
      - verticalLiteralComponentMates_eq_outerCanonicalMate
    source_labels:
      - target theorem E horizontal and vertical Beck--Chevalley pasting compatibility
    conjuncts:
      - the generated horizontal component comparison equals the named normalized horizontal outer boundary comparison after northwest, top and bottom alignment; the predecessor semantic-comparison theorem supplies its independent outer-square provenance
      - the generated vertical component comparison equals the named normalized vertical outer boundary comparison after northwest, top, right and bottom alignment; the predecessor semantic-comparison theorem supplies its independent outer-square provenance
      - the literal vertical composite of the generated horizontal component mates equals the normalized outer canonical mate after named source and target alignment
      - the literal horizontal composite of the generated vertical component mates equals the normalized outer canonical mate after named source and target alignment
    undischarged_assumptions:
      - actual horizontal and vertical specialization of the accepted D diagnostic composition laws
      - final K4 integration of D compatibility with the accepted square closure and G-106 / G-109 coherence bridge
      - final DoctrineFiberProduct theorem assembly and completion review
    acceptance_point: both directions use generated finite presentations, generated transport/reindex adjunctions, mate laws, and proved alignment equalities; no caller-supplied comparison or coherence field is introduced
    port_status: unported (Research-proved)
audits:
  premise_delta:
    discharged:
      - direction-qualified horizontal northwest transport square on data.pasteNorthwestIso
      - horizontal and vertical typed-normal-form equality with named outer boundary comparisons and their predecessor semantic-provenance bridges
      - horizontal and vertical aligned component-to-outer mate equations
    remaining:
      - actual horizontal and vertical specialization of the accepted D diagnostic composition laws
      - final K4 integration of D compatibility with the accepted square closure and G-106 / G-109 coherence bridge
      - final DoctrineFiberProduct theorem assembly and completion review
  certificate_provenance:
    discharged:
      - outer comparisons are generated from normalized finite pasting provenance
      - component squares and source/target alignments are generated by presentation, compositor, equality-transport, and conjugacy APIs
      - mate equalities consume mathlib mate composition and conjugate cancellation laws
    unresolved: []
  proof_use:
    used:
      - horizontalCompositorAlignedComponentSquare_eq_componentComparison
      - horizontalReviewedOuterComparisonNormalForm_eq_outer
      - verticalReviewedOuterComparisonNatTrans_eq_outer
      - horizontalBCPastingComparison_eq_outer
      - verticalBCPastingComparison_eq_outer
      - horizontalBCPastingOuterCanonicalMate_eq
      - verticalBCPastingOuterCanonicalMate_eq
      - horizontalBCPasting_coreBeckChevalleyMate_vcomp
      - verticalBCPasting_coreBeckChevalleyMate_hcomp
      - mateEquiv_conjugateEquiv_vcomp
      - verticalNormalizedNorthwest_mateEquiv_vcomp
      - conjugateEquiv_comm
      - coreFiberCompositor
      - coreFiberTransportEqIso
    unused: []
  structure_field_escape: none-found
  route_integrity: pass; horizontal uses the data-qualified northwest source and vertical cancels generated covariant/contravariant right alignments before component expansion
  target_fitting: none-found
  vacuity: none-found; all four main equalities are parametric in arbitrary finite horizontal or vertical pasting data
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found; this closes the C comparison mate-pasting portion of E but remains a target-proof-checkpoint pending actual-route D pasting compatibility, final K4 integration and final assembly; revised-card K3 and its named finite witness were already discharged in Cycle 76
  validation_refs:
    - focused BCPastingTypedOuterComparisonEquality single-file elaboration: pass
    - focused BCPastingComponentToOuterMate single-file elaboration: pass
    - BCPastingTypedOuterComparisonEquality axiom audit: 23 declarations, standard axioms only
    - BCPastingComponentToOuterMate axiom audit: 40 declarations, standard axioms only
    - public constructor equations cover the direction-qualified horizontal and vertical acceptance-proof normal forms; direct implementation-definition unfolding was removed from the reviewed proof sites
    - direct axiom audit of both literal-component acceptance theorems and both intermediate component-to-outer theorems: standard axioms only
    - targeted BCPastingComponentToOuterMate single-module build: pass
    - Research aggregate or full build: not run
  blocking_findings: []
  next_obligation: specialize the accepted generic D composition laws to the actual horizontal and vertical pasted BC routes, assemble final K4 compatibility with the accepted closure and G-106 / G-109 bridge, then construct the final theorem assembly
```

### Cycle 101 — horizontal typed component-square alignment

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 101
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: ca645f700b68ec4b8c42625e00737b370661d488
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5397993649
  proof_dag_predecessors:
    - bcCoreTransportSquareIso
    - bcProvenanceCoreTransportSquareIso_eq_semantic
    - coreFiberCompositor
    - horizontalBCPastingComponentComparison
  proof_obligation: identify the top-and-bottom compositor alignment of the literal horizontal component-square composite with the existing generated horizontal component comparison
  selection_reason: direct reduction of the full Cycle 100 horizontal normal form timed out; the first remaining definitional mismatch is exactly the component-square composite versus composite-edge transport functors, so isolating its generated compositor alignment gives the smallest reusable proof delta
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCHorizontalTypedComponentSquareAlignment.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - reversing the top or bottom compositor orientation
    - replacing presentation-indexed component squares without consuming their semantic identification theorem
    - promoting a component-only alignment to the full outer comparison equality
  unchecked:
    - equality of horizontalTypedOuterComparisonNormalForm with horizontalBCPastingOuterBoundaryComparison.hom
    - vertical typed-normal-form equality and both final component-to-outer mate equations
    - actual D pasting, named finite nonvacuity, K4 and final assembly
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: the literal left-then-right generated component squares, aligned by generated top and bottom core-fiber compositors, are proved equal to the existing horizontal component comparison hom
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCHorizontalTypedComponentSquareAlignment.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - horizontalTypedComponentSquare
    - horizontalTypedComponentSquare_eq
    - horizontalCompositorAlignedComponentSquare
    - horizontalCompositorAlignedComponentSquare_eq
    - horizontalBCPastingComponentComparison_hom_eq
    - horizontalCompositorAlignedComponentSquare_eq_componentComparison
  claim_mapping:
    theorem_names:
      - horizontalCompositorAlignedComponentSquare_eq_componentComparison
    source_labels:
      - target theorem E horizontal typed component-to-outer predecessor
    conjuncts:
      - the presentation-indexed left and right component squares compose horizontally in the selected order
      - generated top and bottom compositors identify that square with the reviewed horizontal component comparison
    undischarged_assumptions:
      - northwest and normalized outer alignment around the horizontal component comparison
      - full horizontal and vertical typed-normal-form equalities
      - final horizontal and vertical component-to-outer mate equations
      - actual D pasting, named finite nonvacuity, K4 and final assembly
    acceptance_point: the component alignment uses only generated presentation squares, their proved semantic identities, and generated core-fiber compositors
    port_status: unported (Research-proved)
audits:
  premise_delta:
    discharged:
      - exact top and bottom compositor alignment from literal horizontal component transport composites to composite semantic-edge transport functors
      - equality of the aligned generated component square with horizontalBCPastingComponentComparison.hom
    remaining:
      - northwest and normalized outer alignment for the full horizontal normal form
      - vertical typed-normal-form equality and both final aligned mate equations
      - actual D pasting, named finite nonvacuity, K4 and final assembly
  certificate_provenance:
    discharged:
      - both component squares come from bcCoreTransportSquareIso and are identified semantically by bcProvenanceCoreTransportSquareIso_eq_semantic
      - top and bottom alignments come from coreFiberCompositor
    unresolved: []
  proof_use:
    used:
      - bcCoreTransportSquareIso
      - bcProvenanceCoreTransportSquareIso_eq_semantic
      - bcSemanticCoreTransportSquareIso
      - coreFiberCompositor
      - horizontalBCPastingComponentComparison
      - TwoSquare.hComp
      - TwoSquare.whiskerTop
      - TwoSquare.whiskerBottom
    unused: []
  structure_field_escape: none-found
  route_integrity: pass; left-then-right component squares use compositor hom on top and compositor inv on bottom
  target_fitting: none-found
  vacuity: none-found; the theorem is parametric in arbitrary finite horizontal pasting data
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found; the component-only equality is not promoted to the still-unproved full outer comparison or mate equality
  validation_refs:
    - focused BCHorizontalTypedComponentSquareAlignment single-file elaboration: pass
    - six declarations under the module namespace, standard axioms only
    - targeted predecessor module build only; Research aggregate or full build: not run
  blocking_findings: []
  next_obligation: combine the component-square alignment with the generated northwest, top and bottom alignments to prove horizontalTypedOuterComparisonNormalForm equals horizontalBCPastingOuterBoundaryComparison.hom without whole-expression reduction
```

### Cycle 100 — typed two-square normal forms

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 100
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: 4e18a519b84ef548dfc9e98f14615ff6a724cd1e
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5397305127
  proof_dag_predecessors:
    - horizontalNormalizedNorthwestLeftTransportSquare
    - verticalNormalizedNorthwestLeftTransportSquare
    - mateEquiv_vcomp
  proof_obligation: construct horizontal and vertical generated TwoSquare normal forms on the exact normalized outer functor boundaries and prove the northwest-to-component mate composition step
  selection_reason: Cycle 99 fixes the vertical target reindex orientation, while direct final-equation checking isolates nested Iso.trans expansion as the remaining obstacle; named typed normal forms expose the generated square composition and external alignments required by mate laws
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingTypedTwoSquareNormalForm.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - reversing whiskerTop, whiskerRight, or whiskerBottom orientation
    - hiding the northwest square or component square inside an opaque caller comparison
    - claiming equality with the independently named outer comparison before proving it
  unchecked:
    - equality of each typed normal form natural transformation with the corresponding outer boundary comparison hom
    - horizontal and vertical component-to-outer mate commuting equations
    - actual D pasting, named finite nonvacuity, K4 and final assembly
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: both directions now have a generated TwoSquare on the exact normalized outer functor boundaries, and the mate of each raw northwest-plus-component square is proved to be the composite of its two generated mates
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingTypedTwoSquareNormalForm.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - horizontalOuterTopToTypedComponents
    - horizontalOuterTopToTypedComponents_eq
    - horizontalTypedComponentsToOuterBottom
    - horizontalTypedComponentsToOuterBottom_eq
    - horizontalTypedRawComparisonSquare
    - horizontalTypedRawComparisonSquare_eq
    - horizontalTypedOuterComparisonNormalForm
    - horizontalTypedOuterComparisonNormalForm_eq
    - horizontalNormalizedNorthwest_mateEquiv_vcomp
    - verticalTypedRawComparisonSquare
    - verticalTypedRawComparisonSquare_eq
    - verticalTypedComponentsToOuterBottom
    - verticalTypedComponentsToOuterBottom_eq
    - verticalTypedOuterComparisonNormalForm
    - verticalTypedOuterComparisonNormalForm_eq
    - verticalTypedOuterComparisonNormalForm_eq_staged
    - verticalNormalizedNorthwest_mateEquiv_vcomp
  claim_mapping:
    theorem_names:
      - horizontalNormalizedNorthwest_mateEquiv_vcomp
      - verticalNormalizedNorthwest_mateEquiv_vcomp
    source_labels:
      - target theorem E typed component-to-outer mate-composition predecessors
    conjuncts:
      - the horizontal generated square is placed on normalized outer top and bottom boundaries and its northwest-component mate decomposes vertically
      - the vertical generated square is placed on normalized outer top, right and bottom boundaries and its northwest-component mate decomposes vertically
    undischarged_assumptions:
      - typed-normal-form equality with horizontalBCPastingOuterBoundaryComparison.hom and verticalBCPastingOuterBoundaryComparison.hom
      - horizontal and vertical component-to-outer mate commuting equations
      - actual D pasting, named finite nonvacuity, K4 and final assembly
    acceptance_point: the normal forms and mate decompositions are generated only from normalized provenance, component squares, G-109 compositors, equality transports and mathlib mate composition; equality with the independent outer comparisons remains explicit
    port_status: unported (Research-proved)
audits:
  premise_delta:
    discharged:
      - exact horizontal normalized outer functor boundaries for the generated component TwoSquare
      - exact vertical normalized outer functor boundaries for the generated component TwoSquare
      - horizontal and vertical northwest-plus-component mate decomposition
    remaining:
      - natural-transformation equality of both normal forms with the independently named outer comparisons
      - final horizontal and vertical aligned mate equations
      - actual D pasting, named finite nonvacuity, K4 and final assembly
  certificate_provenance:
    discharged:
      - northwest squares are generated by normalized realization provenance and mate alignment APIs
      - component squares are generated by bcCoreTransportSquareIso
      - external alignments are generated by top and transport compositors, equality transports and unitors
    unresolved: []
  proof_use:
    used:
      - mateEquiv_vcomp
      - horizontalNormalizedNorthwestLeftTransportSquare
      - verticalNormalizedNorthwestLeftTransportSquare
      - bcCoreTransportSquareIso
      - horizontalBCPastingNormalizedTopCompositor
      - verticalBCPastingNormalizedTopCompositor
      - verticalNormalizedRightTransportIso
      - coreFiberCompositor
      - coreFiberTransportEqIso
      - Functor.leftUnitor
    unused: []
  structure_field_escape: none-found
  route_integrity: pass; horizontal uses left-then-right component squares and vertical uses the upper-then-lower covariant square with the lower-then-upper composed right adjunction
  target_fitting: none-found
  vacuity: none-found; all declarations are parametric in arbitrary finite horizontal or vertical pasting data
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found; typed normal forms and mate decomposition are not promoted to the still-unproved outer-comparison or final mate equalities
  validation_refs:
    - focused BCPastingTypedTwoSquareNormalForm single-file elaboration: pass
    - seventeen declarations under the module namespace, standard axioms only
    - Research aggregate or full build: not run
  blocking_findings: []
  next_obligation: prove the horizontal and vertical typed normal-form natural transformations equal the corresponding outer boundary comparison homs, using staged associator and unitor normalization instead of whole-expression reduction
```

### Cycle 99 — vertical selected-reindex target alignment

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 99
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: ce3a5320aeb224b77d531ec53149f7c12b466948
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5396893973
  proof_dag_predecessors:
    - verticalNormalizedRightTransportIso
    - verticalNormalizedRightReindexAlignment
    - verticalMateTargetAlignment
    - coreTransportReindexCompositor_conjugateIsoEquiv
    - selectedCoreFiberReindexCompositor
  proof_obligation: identify the normalized vertical target reindex alignment with the inverse generated finite-composition selected-reindex compositor
  selection_reason: direct type checking of the final vertical mate equation isolates a non-definitional right-adjoint comparison; Cycle 98 proves its covariant conjugacy, and taking the inverse supplies the exact normalized-outer-to-component orientation
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingVerticalReindexCompositorAlignment.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - using the forward selected-reindex compositor instead of its inverse
    - treating normalized-provenance and literal component reindex routes as definitionally equal
    - leaving Cycle 98 conjugacy unused in the final vertical target route
  unchecked:
    - horizontal and vertical component-to-outer mate commuting equations
    - typed-boundary expression of each normalized covariant comparison as the aligned component square
    - actual D pasting, named finite nonvacuity, K4 and final assembly
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: the vertical normalized right conjugate and complete target alignment are now expressed exactly through the inverse generated selected-reindex compositor
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingVerticalReindexCompositorAlignment.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - verticalNormalizedRightTransportIso_eq_typedCompositor
    - verticalNormalizedRightReindexAlignment_eq_selectedCompositor_inv
    - verticalMateTargetAlignment_eq_selectedCompositor_inv
  claim_mapping:
    theorem_names:
      - verticalNormalizedRightTransportIso_eq_typedCompositor
      - verticalNormalizedRightReindexAlignment_eq_selectedCompositor_inv
      - verticalMateTargetAlignment_eq_selectedCompositor_inv
    source_labels:
      - target theorem E vertical pullback-side composition predecessor
    conjuncts:
      - the normalized vertical covariant right comparison is the generated typed compositor
      - its contravariant conjugate is the inverse selected-reindex compositor
      - the complete target alignment uses bottom equality transport followed by that inverse compositor
    undischarged_assumptions:
      - horizontal and vertical component-to-outer mate commuting equations
      - typed-boundary comparison of normalized covariant squares with aligned component squares
      - actual D pasting, named finite nonvacuity, K4 and final assembly
    acceptance_point: Cycle 98 conjugacy is consumed in the exact inverse orientation required by the normalized vertical target route, without caller-supplied mate or reindex comparison
    port_status: unported (Research-proved)
audits:
  premise_delta:
    discharged:
      - vertical normalized right transport comparison identification with the generated typed compositor
      - vertical normalized right reindex comparison identification with the inverse generated selected compositor
      - complete vertical target alignment rewrite
    remaining:
      - horizontal and vertical component-to-outer mate commuting equations
      - typed-boundary normalized covariant comparison decomposition
      - actual D pasting, named finite nonvacuity, K4 and final assembly
  certificate_provenance:
    discharged:
      - covariant right comparison is generated by verticalNormalizedRightTransportIso
      - contravariant comparison is generated from coreTransportReindexCompositor_conjugateIsoEquiv
      - selected compositor is generated by selectedCoreFiberReindexCompositor
    unresolved: []
  proof_use:
    used:
      - coreTransportReindexCompositor_conjugateIsoEquiv
      - congrArg Iso.inv
      - verticalNormalizedRightTransportIso
      - verticalNormalizedRightReindexAlignment
      - verticalMateTargetAlignment
    unused: []
  structure_field_escape: none-found
  route_integrity: pass; the covariant direct-to-iterated compositor is conjugated to the iterated-to-direct reindex compositor, then inverted to obtain the normalized-direct-to-component reindex alignment
  target_fitting: none-found
  vacuity: none-found; all declarations are parametric in arbitrary finite vertical pasting data
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found; the result fixes one target alignment and does not claim either final mate equation or G-110 completion
  validation_refs:
    - focused BCPastingVerticalReindexCompositorAlignment single-file elaboration: pass
    - three declarations under the module namespace, standard axioms only
    - Research aggregate or full build: not run
  blocking_findings: []
  next_obligation: express the normalized horizontal and vertical covariant comparisons as the corresponding typed aligned component squares, then apply mateEquiv composition and external-whisker coherence to close both component-to-outer mate equations
```

### Cycle 98 — generated compositor conjugacy

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 98
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: abe75f4c646a48ed3c8bcc17fb4c14a0ffecc896
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5396618808
  proof_dag_predecessors:
    - coreTransportReindexCompositorAdjunction_eq_direct
    - typedCoreFiberTransportCompositor
    - selectedCoreFiberReindexCompositor
    - conjugateIsoEquiv
    - Adjunction.ofNatIsoLeft
    - Adjunction.ofNatIsoRight
  proof_obligation: identify the right-adjoint conjugate of the typed covariant compositor with the generated selected-reindex compositor
  selection_reason: Cycle 97 fixes the normalized source and target alignments, and their final mate equations require the generated covariant compositor and generated contravariant compositor to be recognized as mates without a caller-supplied coherence equality
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CoreTransportReindexCompositorConjugacy.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - assuming the two generated compositors are definitionally equal as mates
    - introducing a caller-supplied right-adjoint comparison
    - proving only a componentwise special case instead of the natural-isomorphism equality
  unchecked:
    - horizontal and vertical component-to-outer mate equations
    - actual D pasting, named finite nonvacuity, K4 and final assembly
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: the generated selected-reindex compositor is now proved to be exactly the conjugate of the generated covariant compositor under the composite and direct generated adjunctions
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CoreTransportReindexCompositorConjugacy.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - coreTransportReindexCompositor_conjugateIsoEquiv
  claim_mapping:
    theorem_names:
      - coreTransportReindexCompositor_conjugateIsoEquiv
    source_labels:
      - target theorem E finite-composition mate-coherence predecessor
    conjuncts:
      - the mate of the generated covariant finite compositor is the generated selected-reindex compositor
    undischarged_assumptions:
      - horizontal and vertical component-to-outer mate commuting equations
      - actual D pasting, named finite nonvacuity, K4 and final assembly
    acceptance_point: the right-adjoint finite compositor is derived as the exact conjugate of the generated covariant compositor through the proved transported-adjunction equality; no mate or coherence comparison is caller-supplied
    port_status: unported (Research-proved)
audits:
  premise_delta:
    discharged:
      - generated finite-compositor conjugacy for arbitrary composable finite cartesian presentations
    remaining:
      - horizontal and vertical component-to-outer mate commuting equations
      - actual D pasting, named finite nonvacuity, K4 and final assembly
  certificate_provenance:
    discharged:
      - component and direct adjunctions are generated by coreTransportReindexAdjunction
      - covariant and contravariant compositors are generated by typedCoreFiberTransportCompositor and selectedCoreFiberReindexCompositor
      - transported-versus-direct adjunction equality is generated by coreTransportReindexCompositorAdjunction_eq_direct
    unresolved: []
  proof_use:
    used:
      - rewrite the direct generated adjunction by coreTransportReindexCompositorAdjunction_eq_direct
      - expand adjunction transport across the inverse left isomorphism and the right isomorphism
      - apply right-isomorphism naturality and the composite adjunction right triangle identity
    unused: []
  structure_field_escape: none-found
  route_integrity: pass; typedCoreFiberTransportCompositor runs from direct to iterated transport and its conjugate runs from iterated to direct selected reindex, matching the generated compositor orientations
  target_fitting: none-found
  vacuity: none-found; the theorem is parametric in arbitrary composable finite cartesian presentations and states an equality of natural isomorphisms
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found; this result is recorded only as an E predecessor and does not claim either final mate equation or G-110 completion
  validation_refs:
    - focused CoreTransportReindexCompositorConjugacy single-file elaboration: pass
    - one public declaration under the module namespace, standard axioms only
    - git diff --check and hidden or bidirectional Unicode scan: pass
    - Research aggregate or full build: not run
  blocking_findings: []
  next_obligation: combine this conjugacy theorem with the normalized mate-alignment packet and horizontal/vertical mate-composition theorems to prove the final component-to-outer mate equations
```

### Cycle 97 — normalized-provenance mate-alignment packet

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 97
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: 3cc5b8599864941ac9ed1526f04be575dc144faf
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5396224249
  proof_dag_predecessors:
    - bcPastingNormalizedProvenance
    - horizontalBCPastingNormalizedLeftCompositor
    - horizontalBCPastingNormalizedTopCompositor
    - horizontalBCPastingNormalizedBottom_eq
    - verticalBCPastingNormalizedLeftCompositor
    - verticalBCPastingNormalizedTopCompositor
    - verticalBCPastingNormalizedRight_eq
    - coreTransportReindexAdjunction
    - mateEquiv
    - conjugateEquiv
  next_stage_inputs:
    - horizontalBCPasting_mateEquiv_vcomp
    - verticalBCPasting_mateEquiv_hcomp
    - horizontalBCPastingOuterCanonicalMate_eq
    - verticalBCPastingOuterCanonicalMate_eq
    - coreTransportReindexCompositorAdjunction_eq_direct
  proof_obligation: generate the exact normalized-provenance source and target transformations required to state the horizontal and vertical component-to-outer mate commuting equations
  selection_reason: Cycle 96 aligns the paste-presentation adjunction, while Cycle 94 canonical mates inhabit reindex functors generated by the normalized realization provenance; direct type checking exposes this non-definitional mismatch and selects a normalized-provenance second mate as the smallest required predecessor
  expected_result_type: target-proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingNormalizedMateAlignment.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - treating paste-presentation and normalized-provenance reindex functors as definitionally equal
    - reversing the vertical lower/upper right-adjoint order
    - supplying source or target alignment transformations from the caller
  unchecked:
    - equality of each aligned literal component-mate composite with the normalized outer canonical mate
    - generic conjugacy of the covariant finite compositor with the selected reindex compositor
    - actual D pasting, named finite nonvacuity, K4 and final assembly
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: both directions now have a normalized-provenance northwest second mate and exact source/target alignment transformations; the vertical target route additionally generates the right-adjoint comparison as the conjugate of the inverse covariant right-edge compositor
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingNormalizedMateAlignment.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - horizontalNormalizedNorthwestLeftTransportSquare
    - horizontalNormalizedNorthwestReindexAlignment
    - horizontalMateSourceAlignment
    - horizontalMateTargetAlignment
    - verticalNormalizedBottom_eq
    - verticalNormalizedNorthwestLeftTransportSquare
    - verticalNormalizedNorthwestReindexAlignment
    - verticalMateSourceAlignment
    - verticalNormalizedRightTransportIso
    - verticalNormalizedRightReindexAlignment
    - verticalMateTargetAlignment
  claim_mapping:
    theorem_names:
      - horizontalNormalizedNorthwestReindexAlignment
      - horizontalMateSourceAlignment
      - horizontalMateTargetAlignment
      - verticalNormalizedNorthwestReindexAlignment
      - verticalNormalizedRightReindexAlignment
      - verticalMateSourceAlignment
      - verticalMateTargetAlignment
    source_labels:
      - target theorem E normalized-provenance mate-comparison predecessor
    conjuncts:
      - the normalized horizontal outer source is mapped to the literal left/right component-mate source through a generated northwest second mate and top compositors
      - the normalized horizontal outer target is mapped to the literal component-mate target through generated bottom equality transport and compositor
      - the normalized vertical outer source is mapped to the lower-then-upper reindex and upper-top component source
      - the normalized vertical outer target is mapped through bottom equality transport and a conjugate-generated lower-then-upper right reindex alignment
    undischarged_assumptions:
      - the two component-to-outer mate commuting equations
      - the generic compositor conjugacy equation needed to identify the vertical target alignment with the selected-reindex compositor route in the final commuting equation
      - actual D pasting, named finite nonvacuity, K4 and final target assembly
    acceptance_point: every alignment is generated from normalized realization provenance, canonical northwest comparison, G-109 compositors, equality transports, unitors and mate or conjugate equivalences; no route transformation is caller-supplied
    port_status: unported (Research-proved)
audits:
  premise_delta:
    discharged:
      - horizontal normalized-provenance source and target route typing
      - vertical normalized-provenance source and target route typing
      - vertical right-adjoint comparison generated by covariant conjugation
    remaining:
      - horizontal and vertical component-to-outer mate commuting equations
      - finite-compositor conjugacy with selected reindex composition
      - actual D pasting, named finite nonvacuity, K4 and final assembly
  certificate_provenance:
    discharged:
      - normalized left and right adjunctions are generated from bcPastingNormalizedProvenance
      - northwest and edge transport comparisons are generated by the pasting schema and G-109 compositors
      - right-adjoint alignment is generated by conjugateEquiv from an inverse covariant isomorphism
    unresolved: []
  proof_use:
    used:
      - mateEquiv
      - conjugateEquiv
      - coreTransportReindexAdjunction
      - coreFiberCompositor
      - coreFiberTransportEqIso
      - Functor.associator
      - Functor.leftUnitor
      - Functor.rightUnitor
      - Functor.whiskerLeft
      - Functor.whiskerRight
      - Adjunction.comp
    unused: []
  structure_field_escape: none-found
  route_integrity: normalized provenance is retained at both outer endpoints; horizontal routes use left then right component order, and vertical right adjoints occur in lower then upper order as forced by Adjunction.comp
  target_fitting: none-found
  vacuity: all route transformations are parametric in arbitrary horizontal or vertical finite pasting data
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: this packet fixes exact natural-transformation boundaries and does not claim either final commuting equation
  validation_refs:
    - focused BCPastingNormalizedMateAlignment single-file elaboration: pass
    - eleven public declarations under the module namespace, standard axioms only
  blocking_findings: []
  next_obligation: prove generic finite-compositor conjugacy on the selected reindex side, then close the horizontal and vertical component-to-outer mate commuting equations with mateEquiv composition and Cycle 94 outer comparison equality
```

### Cycle 96 — northwest second-mate alignment

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 96
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: a15391dadda6438f0a0900b29d9711e962b7c5bd
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5395926118
  proof_dag_predecessors:
    - HorizontalBCPastingData.pasteNorthwestIso_hom_left
    - VerticalBCPastingData.pasteNorthwestIso_hom_left
    - coreFiberCompositor
    - coreFiberTransportEqIso
    - coreTransportReindexAdjunction
    - mateEquiv
  next_stage_inputs:
    - coreTransportReindexCompositorAdjunction_eq_direct
    - horizontalBCPasting_mateEquiv_vcomp
    - verticalBCPasting_mateEquiv_hcomp
  proof_obligation: construct the generated contravariant second mates that align the normalized outer left reindex functor with the literal horizontal and vertical component routes across the inverse canonical northwest transport
  selection_reason: Cycle 95 discharged finite-composition adjunction coherence; the remaining functor mismatch in both mate-composition routes is exactly the canonical northwest isomorphism supplied by the pasting schema
  expected_result_type: target-proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingNorthwestSecondMate.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - reversing the canonical northwest isomorphism
    - supplying a reindex alignment instead of deriving it as a mate
    - omitting the vertical two-component left adjunction composition
  unchecked:
    - naturality squares combining these second mates with the reviewed component-mate composites and normalized outer canonical mates
    - pullback-side final composition coherence, actual D pasting, named finite nonvacuity, K4 and final assembly
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: the inverse canonical northwest isomorphism and the generated covariant compositors determine horizontal and vertical left-edge alignment squares; mateEquiv generates the corresponding contravariant reindex transformations, with normalized targets after removal of identity functors
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingNorthwestSecondMate.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - horizontalPasteNorthwest_inv_left_eq
    - horizontalPasteNorthwestLeftTransportIso
    - horizontalPasteNorthwestLeftTransportSquare
    - horizontalPasteNorthwestReindexAlignment
    - horizontalPasteNorthwestReindexAlignmentNormalized
    - verticalPasteNorthwest_inv_left_eq
    - verticalPasteNorthwestLeftTransportIso
    - verticalPasteNorthwestLeftTransportSquare
    - verticalPasteNorthwestReindexAlignment
    - verticalPasteNorthwestReindexAlignmentNormalized
  claim_mapping:
    theorem_names:
      - horizontalPasteNorthwest_inv_left_eq
      - horizontalPasteNorthwestReindexAlignmentNormalized
      - verticalPasteNorthwest_inv_left_eq
      - verticalPasteNorthwestReindexAlignmentNormalized
    source_labels:
      - target theorem E northwest second-mate predecessor
    conjuncts:
      - the inverse generated northwest isomorphism followed by the literal left route equals the generated outer left edge in each pasting direction
      - the horizontal second mate aligns outer reindexing after northwest transport with the left component reindex functor
      - the vertical second mate aligns outer reindexing after northwest transport with the lower-then-upper composite reindex functor
    undischarged_assumptions:
      - the component-to-outer mate commuting equations using these alignments
      - actual D pasting, named finite nonvacuity, K4 and final target assembly
    acceptance_point: both contravariant alignments are generated by mateEquiv from schema-produced northwest isomorphisms, semantic edge equalities and G-109 compositors; no reindex comparison is supplied by the caller
    port_status: unported (Research-proved)
audits:
  premise_delta:
    discharged:
      - horizontal outer-left reindex alignment across the canonical northwest transport
      - vertical composite outer-left reindex alignment across the canonical northwest transport
    remaining:
      - component-to-outer mate commuting equations
      - pullback-side final composition coherence, actual D pasting, named finite nonvacuity, K4 and final assembly
  certificate_provenance:
    discharged:
      - northwest isomorphisms are generated by pullback uniqueness in BCPastingSchema
      - covariant alignment is generated by coreFiberCompositor, semantic edge equality transport and unitors
      - contravariant alignment is generated by mateEquiv from the two generated adjunctions
    unresolved: []
  proof_use:
    used:
      - Iso.inv_comp_eq
      - HorizontalBCPastingData.pasteNorthwestIso_hom_left
      - VerticalBCPastingData.pasteNorthwestIso_hom_left
      - coreFiberCompositor
      - coreFiberTransportEqIso
      - Functor.isoWhiskerLeft
      - Functor.rightUnitor
      - Adjunction.comp
      - bcLeftAdjunction
      - mateEquiv
      - Functor.leftUnitor
    unused: []
  structure_field_escape: none-found
  route_integrity: both routes use pasteNorthwestIso.inv from the normalized outer northwest object to the literal pasted northwest object; vertical alignment retains the upper/lower transport composition and the reversed lower/upper reindex composition forced by adjunction composition
  target_fitting: none-found
  vacuity: all declarations are parametric in arbitrary horizontal or vertical finite pasting data
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: the generated second mates are stated as natural transformations and are not promoted to natural isomorphisms or to the final mate commuting equations
  validation_refs:
    - focused BCPastingNorthwestSecondMate single-file elaboration: pass
    - ten public declarations under the module namespace, standard axioms only
  blocking_findings: []
  next_obligation: combine the northwest second mates, Cycle 95 adjunction equality and Cycle 93 mate-composition laws to prove the horizontal and vertical component-to-outer mate commuting equations
```

### Cycle 95 — compositor-transported composite adjunction

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 95
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: aeb8bde5c7c18e3d2b7e4564a8cda3e5e5b26092
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5395127839
  proof_dag_predecessors:
    - coreTransportReindexAdjunction
    - typedCoreFiberTransportCompositor
    - selectedCoreFiberReindexCompositor
    - Adjunction.comp
    - Adjunction.ofNatIsoLeft
    - Adjunction.ofNatIsoRight
    - coreTransportToReindexHom_fac
    - selectedCoreFiberReindexCompositorApp_hom_fac
    - coreFiberLift_eqToIso_fac
    - coreFiberCompositorApp_hom_fac
  proof_obligation: construct the component-composite adjunction directly on the finite-composite presentation functors, expose its generated unit and counit routes, and prove equality with the independently generated direct adjunction
  selection_reason: Cycle 94 reduced outer-mate alignment to finite-composition adjunction coherence and northwest alignment; transporting Adjunction.comp across the two reviewed compositors is the smallest typed predecessor shared by both directions
  expected_result_type: target-proof-checkpoint
  risks:
    - treating any two adjunction structures on the same functors as definitionally equal
    - hiding a caller-supplied adjunction or coherence equality
    - omitting one component unit, counit or compositor from the transported structure
  unchecked:
    - northwest second-mate alignment and component-to-outer mate commuting equations
    - pullback-side composition coherence, actual D pasting, named finite nonvacuity, K4 and final assembly
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: coreTransportReindexCompositorAdjunction transports the component Adjunction.comp across the inverse covariant compositor and forward selected-reindex compositor; its unit and counit component theorems expose both generated component units or counits and both compositor directions in the exact order; strong-cartesian uniqueness proves that this transported structure equals the independently generated direct adjunction
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CoreTransportReindexAdjunctionComposition.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - coreTransportReindexCompositorAdjunction
    - typedCoreFiberTransportCompositor_hom_fac
    - coreTransportReindexCompositorAdjunction_unit_app
    - coreTransportReindexCompositorAdjunction_counit_app
    - coreTransportReindexCompositorAdjunction_eq_direct
  claim_mapping:
    theorem_names:
      - coreTransportReindexCompositorAdjunction_unit_app
      - coreTransportReindexCompositorAdjunction_counit_app
      - coreTransportReindexCompositorAdjunction_eq_direct
    source_labels:
      - target theorem E pullback-side finite-composition adjunction predecessor
    conjuncts:
      - the component adjunction composite is transported onto the direct composite transport and selected-reindex functors
      - the transported unit explicitly consumes both generated units, the inverse covariant compositor and the forward reindex compositor
      - the transported counit explicitly consumes the forward covariant compositor, inverse reindex compositor and both generated counits
      - the transported composite adjunction equals the independently generated direct adjunction by transpose factorization, both compositor triangles and strong-cartesian uniqueness
    undischarged_assumptions:
      - northwest semantic-isomorphism mate alignment and final component-to-outer comparison
      - actual D pasting, named finite nonvacuity, K4 and final target assembly
    acceptance_point: the exact composite-adjunction candidate, both component formulas and its equality with the direct generated adjunction are proved without caller coherence data
    port_status: unported (Research-proved)
audits:
  premise_delta:
    discharged:
      - construction of an adjunction on the direct finite-composite functor pair from component adjunctions and reviewed compositors
      - exact unit and counit expansion of that transported adjunction
      - direct-versus-transported adjunction equality by generated lift factorization and strong-cartesian uniqueness
    remaining:
      - northwest second mate and component-to-outer mate commuting equations
      - pullback-side coherence, actual D pasting, named finite nonvacuity, K4 and final assembly
  certificate_provenance:
    discharged:
      - component adjunctions are generated by coreTransportReindexAdjunction
      - covariant and contravariant route isomorphisms are generated by the finite-presentation compositors
    unresolved: []
  proof_use:
    used:
      - Adjunction.comp
      - Adjunction.ofNatIsoLeft
      - Adjunction.ofNatIsoRight
      - Adjunction.comp_unit_app
      - Adjunction.comp_counit_app
      - typedCoreFiberTransportCompositor
      - selectedCoreFiberReindexCompositor
      - coreTransportToReindexHom_fac
      - selectedCoreFiberReindexCompositorApp_hom_fac
      - coreFiberLift_eqToIso_fac
      - coreFiberCompositorApp_hom_fac
      - CategoryTheory.Functor.IsStronglyCartesian.ext
    unused: []
  structure_field_escape: none-found
  route_integrity: the direct covariant functor is aligned by typedCoreFiberTransportCompositor.symm and the iterated contravariant functor by selectedCoreFiberReindexCompositor in their required orientations
  target_fitting: none-found
  vacuity: all declarations are parametric in arbitrary two-arrow finite presentation composites
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: sharing left and right functors is not treated as definitional equality; the direct-versus-transported equality is separately proved from generated factorization laws
  validation_refs:
    - focused CoreTransportReindexAdjunctionComposition single-file elaboration: pass
    - five public declarations under the module namespace, standard axioms only
  blocking_findings: []
  next_obligation: specialize the generic adjunction equality to horizontal and vertical pasting, construct the northwest second mate, and prove the component-to-outer mate commuting equations
```

### Cycle 94 — normalized outer canonical-mate comparison alignment

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 94
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: c680ae68b49110bb7cfdcd5cfad30a2420149b5f
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5394980812
  proof_dag_predecessors:
    - bcSemanticSelectedMate_self
    - bcPastingCoreTransportSquareIso_eq_semantic
    - horizontalBCPastingComparison_eq_outer
    - verticalBCPastingComparison_eq_outer
  proof_obligation: identify the canonical mate of each independently generated normalized outer presentation with the mate of its reviewed exact-boundary covariant comparison
  selection_reason: Cycle 93 fixed the literal component-mate compositions but left their relation to the independently generated outer canonical mate open; the common outer comparison is the first well-typed alignment point before reindex and composite-adjunction transport
  expected_result_type: target-proof-checkpoint
  risks:
    - claiming equality with the literal component-mate composite
    - replacing canonical provenance with a caller-supplied comparison
    - hiding the northwest source-fiber change behind endpoint equality
  unchecked:
    - finite-presentation composition compatibility of generated transport/reindex adjunctions
    - northwest isomorphism reindex and adjunction bridge from literal component routes to normalized outer routes
    - pullback-side composition coherence, actual D pasting, named finite nonvacuity, K4 and final assembly
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: horizontalBCPastingOuterCanonicalMate_eq and verticalBCPastingOuterCanonicalMate_eq rewrite the generated provenance canonical mates through bcSemanticSelectedMate_self, the normalized semantic square comparison, and the reviewed horizontal or vertical exact-boundary comparison equality
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingOuterCanonicalMate.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - horizontalBCPastingOuterCanonicalMate_eq
    - verticalBCPastingOuterCanonicalMate_eq
  claim_mapping:
    theorem_names:
      - horizontalBCPastingOuterCanonicalMate_eq
      - verticalBCPastingOuterCanonicalMate_eq
    source_labels:
      - target theorem E normalized outer canonical-mate comparison predecessor
    conjuncts:
      - the horizontal normalized-provenance canonical mate is the mate of horizontalBCPastingOuterBoundaryComparison
      - the vertical normalized-provenance canonical mate is the mate of verticalBCPastingOuterBoundaryComparison
      - both comparison arguments are generated from finite pasting data and already identified with the canonical semantic covariant comparison
    undischarged_assumptions:
      - equality after generated route isomorphisms with the Cycle 93 literal component-mate composites
      - finite-composition adjunction compatibility and northwest semantic-isomorphism reindex compatibility
      - pullback-side composition coherence, actual D pasting, named finite nonvacuity, K4 and final target assembly
    acceptance_point: the outer canonical mates now consume the reviewed exact-boundary comparisons; no component-to-outer route alignment or final target completion is claimed
    port_status: unported (Research-proved)
audits:
  premise_delta:
    discharged:
      - horizontal exact-boundary covariant comparison to normalized outer canonical mate
      - vertical exact-boundary covariant comparison to normalized outer canonical mate
    remaining:
      - component-to-outer source and target route isomorphisms and mate naturality square
      - generated adjunction compatibility with transport/reindex compositors
      - northwest semantic-isomorphism reindex bridge
      - pullback-side composition coherence, actual D pasting, named finite nonvacuity, K4 and final assembly
  certificate_provenance:
    discharged:
      - normalized provenance is generated by pastePresentation and toSemanticBC_pastePresentation_eq
      - the mate comparison follows from generated square provenance and Cycle 91/92 comparison equalities
    unresolved: []
  proof_use:
    used:
      - bcSemanticSelectedMate_self
      - bcPastingCoreTransportSquareIso_eq_semantic
      - horizontalBCPastingComparison_eq_outer
      - verticalBCPastingComparison_eq_outer
    unused: []
  structure_field_escape: none-found
  route_integrity: each theorem stays on one normalized outer semantic input and changes only the generated covariant comparison used by mateEquiv
  target_fitting: none-found
  vacuity: both theorems quantify over arbitrary generated horizontal or vertical pasting data; named target-level nonvacuity remains open
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: the literal component mates and normalized outer mates have different route functors until explicit generated isomorphisms are constructed, so no raw NatTrans equality between them is claimed
  validation_refs:
    - focused BCPastingOuterCanonicalMate single-file elaboration: pass
    - two declarations under the module namespace, standard axioms only
  blocking_findings: []
  next_obligation: prove finite-presentation composition compatibility of coreTransportReindexAdjunction with typedCoreFiberTransportCompositor and selectedCoreFiberReindexCompositor, then construct the northwest semantic-isomorphism reindex and adjunction bridge required for the component-to-outer mate square
```

### Cycle 93 — generated canonical-mate composition algebra

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 93
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: 2ba5dab1e9d2e02c2379dd8433cf7629e6013fc1
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5394816561
  proof_dag_predecessors:
    - coreBeckChevalleyMate
    - mateEquiv_vcomp
    - mateEquiv_hcomp
  proof_obligation: specialize mates composition to the generated horizontal and vertical component squares so their canonical mate routes consume the generated adjunction units and counits before exact outer-presentation alignment
  selection_reason: Cycles 91 and 92 identified both covariant component comparisons with their normalized outer comparisons; mathlib mates composition now fixes the uniquely oriented component-mate pasting routes, while selected reindexing and composite-adjunction alignment remain separate
  expected_result_type: target-proof-checkpoint
  risks:
    - using vertical and horizontal TwoSquare composition in the wrong geometric directions
    - reversing the right-adjoint mate order in vertical pasting
    - calling a composed-adjunction mate the canonical mate of the independently generated outer presentation
  unchecked:
    - horizontal northwest/reindexing alignment with the canonical mate of the outer presentation
    - vertical composite-adjunction alignment with the canonical mate of the outer presentation
    - pullback-side composition coherence, actual D pasting, named finite nonvacuity, K4 and final assembly
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: horizontalBCPasting_mateEquiv_vcomp specializes mateEquiv_vcomp to the generated left and right squares, while verticalBCPasting_mateEquiv_hcomp specializes mateEquiv_hcomp to the generated upper and lower squares; their public corollaries identify the component routes with compositions of the corresponding coreBeckChevalleyMate declarations
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCHorizontalPastingMateComposition.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCVerticalPastingMateComposition.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - horizontalBCPasting_mateEquiv_vcomp
    - horizontalBCPasting_coreBeckChevalleyMate_vcomp
    - verticalBCPasting_mateEquiv_hcomp
    - verticalBCPasting_coreBeckChevalleyMate_hcomp
  claim_mapping:
    theorem_names:
      - horizontalBCPasting_coreBeckChevalleyMate_vcomp
      - verticalBCPasting_coreBeckChevalleyMate_hcomp
    source_labels:
      - target theorem E generated canonical-mate composition algebra predecessor
    conjuncts:
      - horizontal geometric pasting uses mateEquiv_vcomp and preserves the left-to-right component order
      - vertical geometric pasting uses mateEquiv_hcomp and the required reversed right-adjoint mate order
      - both component routes use the public generated coreBeckChevalleyMate declarations
    undischarged_assumptions:
      - exact alignment with coreBeckChevalleyMate of each independently generated outer presentation
      - selected reindexing composition and composite-adjunction coherence
      - pullback-side composition coherence, actual D pasting, named finite nonvacuity, K4 and final target assembly
    acceptance_point: unit/counit mate-composition algebra is proved for both generated component routes; outer canonical-mate alignment and final target completion are not claimed
    port_status: unported (Research-proved)
audits:
  premise_delta:
    discharged:
      - horizontal composition law for the two generated component mates
      - vertical composition law for the two generated component mates under composed adjunctions
      - public coreBeckChevalleyMate proof-use in both component routes
    remaining:
      - horizontal northwest and selected-reindexing alignment to the outer canonical mate
      - vertical covariant and contravariant compositor compatibility between composed and outer adjunctions
      - pullback-side composition coherence, actual D pasting, named finite nonvacuity, K4 and final assembly
  certificate_provenance:
    discharged:
      - component adjunctions, comparisons, units and counits are generated from the component BCPresentations
      - mate route equalities follow from mathlib mateEquiv_vcomp and mateEquiv_hcomp
    unresolved: []
  proof_use:
    used:
      - coreBeckChevalleyMate
      - bcLeftAdjunction
      - bcRightAdjunction
      - bcCoreTransportSquareIso
      - mateEquiv_vcomp
      - mateEquiv_hcomp
    unused: []
  structure_field_escape: none-found
  route_integrity: the horizontal theorem composes left then right squares across the shared adjunction; the vertical theorem composes upper then lower covariant squares and reverses mate order exactly as mateEquiv_hcomp requires
  target_fitting: none-found
  vacuity: both theorems are parametric in generated horizontal or vertical pasting data; named target-level nonvacuity remains open
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: composed component mates are not identified with the independently generated outer canonical mate until the remaining reindexing and adjunction-alignment theorems are proved
  validation_refs:
    - focused BCHorizontalPastingMateComposition single-file elaboration: pass
    - focused BCVerticalPastingMateComposition single-file elaboration: pass
    - four declarations across the two modules, standard axioms only
  blocking_findings: []
  next_obligation: construct horizontal northwest/reindexing alignment and vertical composite-adjunction alignment, then identify both composed mate routes with coreBeckChevalleyMate of the independently generated outer presentations
```

### Cycle 92 — vertical covariant-square comparison equality

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 92
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: 20449208a5c419f2d5bc597feb3dbb7310c14dcf
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5394409295
  proof_dag_predecessors:
    - verticalBCPastingComponentComparison
    - verticalBCPastingNormalizedTopCompositor
    - verticalBCPastingNormalizedLeftCompositor
    - bcSemanticCoreTransportSquareIso_hom_fac
    - coreFiberIteratedLift_isStronglyCocartesian
  proof_obligation: normalize the vertical componentwise covariant comparison onto the exact outer-square boundary and prove equality with the independently generated normalized outer semantic comparison
  selection_reason: Cycle 91 discharged the horizontal covariant-square predecessor; the generated vertical route and northwest compositors were already available, leaving right-edge realization alignment and the corresponding lift factorization
  expected_result_type: target-proof-checkpoint
  risks:
    - reversing the generated right-edge equality transport at the source
    - dropping either component comparison or the right and left compositors
    - identifying comparison isomorphisms from common endpoints without proving lift factorization
  unchecked:
    - horizontal and vertical canonical-mate pasting, including selected reindexing and unit/counit coherence
    - pullback-side composition coherence
    - actual D pasting, named finite nonvacuity, K4 and final target assembly
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: verticalBCPastingNormalizedRight_eq derives the normalized outer right edge from finite presentation composition; the normalized route consumes the right compositor, upper and lower square comparisons, northwest normalization and the left compositor; strong-cocartesian uniqueness then proves verticalBCPastingComparison_eq_outer
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCVerticalPastingComparisonNormalization.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCVerticalPastingComponentFactorization.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCVerticalPastingComparisonEqualityRoutes.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCVerticalPastingComparisonNormalizedSplit.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCVerticalPastingComparisonInnerSplit.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCVerticalPastingNormalizedFactorization.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCVerticalPastingOuterFactorization.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCVerticalPastingComparisonEquality.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - verticalBCPastingComponentComparison_hom_fac
    - verticalBCPastingNormalizedComponentComparison_hom_fac
    - verticalBCPastingOuterBoundaryComparison_hom_fac
    - verticalBCPastingComparison_eq_outer
  claim_mapping:
    theorem_names:
      - verticalBCPastingComparison_eq_outer
    source_labels:
      - target theorem E vertical covariant transport-square comparison coherence predecessor
    conjuncts:
      - the componentwise vertical comparison retains both generated square comparisons and the right and left compositors
      - the generated right-edge equality transport and northwest normalization are consumed in the lift factorization
      - the exact-boundary componentwise route equals the independently generated comparison of the normalized outer square
    undischarged_assumptions:
      - horizontal and vertical coreBeckChevalleyMate pasting, including selected reindexing and unit/counit coherence
      - pullback-side composition coherence
      - actual D pasting, named finite nonvacuity, K4 and final target assembly
    acceptance_point: both horizontal and vertical covariant transport-square comparison-Iso equalities are now proved as predecessors of E; no coreBeckChevalleyMate pasting or final target completion is claimed
    port_status: unported (Research-proved)
audits:
  premise_delta:
    discharged:
      - vertical covariant transport-square comparison-Iso equality
      - vertical normalized route lift factorization including right-edge equality transport
    remaining:
      - horizontal and vertical coreBeckChevalleyMate pasting with selected reindexing and unit/counit coherence
      - pullback-side composition coherence
      - actual D pasting, named finite nonvacuity, K4 and final assembly
  certificate_provenance:
    discharged:
      - the right-edge equality comes from toSemanticCart_compPresentation_hom applied to rightTop and rightBottom
      - both component comparisons and the outer comparison come from generated semantic square data
      - equality follows from strong-cocartesian uniqueness after both hom components factor the same normalized iterated lift
    unresolved: []
  proof_use:
    used:
      - verticalBCPastingComponentComparison
      - verticalBCPastingNormalizedTopCompositor
      - verticalBCPastingNormalizedLeftCompositor
      - verticalBCPastingNormalizedRight_eq
      - bcSemanticCoreTransportSquareIso_whisker_right_hom_fac
      - coreFiberIteratedLift_transportEqIso_fac
      - bcSemanticCoreTransportSquareIso_hom_fac
      - coreFiberIteratedLift_isStronglyCocartesian
    unused: []
  structure_field_escape: none-found
  route_integrity: the proof consumes the generated right compositor, upper and lower square comparisons, northwest and left compositors, and right-edge equality transport before uniqueness; no caller-authored comparison is substituted
  target_fitting: none-found
  vacuity: the equality is parametric in generated vertical pasting data; named target-level nonvacuity remains open
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: the result is limited to the covariant transport-square predecessor and does not discharge the canonical mate named by C and E
  validation_refs:
    - focused BCVerticalPastingComparisonEquality single-file elaboration: pass
    - one declaration under the final module namespace, standard axioms only
  blocking_findings: []
  next_obligation: prove horizontal and vertical coreBeckChevalleyMate pasting with the required selected reindexing, unit/counit and pullback-side composition coherence, retaining the Cycle 82 G-106/G-109 bridge for final integration
```

### Cycle 91 — horizontal covariant-square comparison equality

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 91
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: cf2c3e44739f2bb03ef92825b24b6e682f1585a7
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5391894801
  proof_dag_predecessors:
    - horizontalBCPastingOuterBoundaryComparison
    - bcSemanticCoreTransportSquareIso_hom_fac
    - coreFiberIteratedLift_isStronglyCocartesian
  proof_obligation: prove that the aligned horizontal componentwise comparison is the independently generated comparison of the normalized outer semantic square
  selection_reason: Cycle 90 put both comparison isomorphisms on the same exact functor boundary; strong-cocartesian uniqueness can now identify them after proving the pasted route carries the canonical top-right lift to the canonical left-bottom lift
  expected_result_type: target-proof-checkpoint
  risks:
    - treating equal source and target functors as equality of comparison isomorphisms
    - dropping the northwest, compositor, or bottom equality-transport factors during component expansion
    - relying on definitional reduction of the generated bottom presentation
  unchecked:
    - vertical normalization, boundary alignment and outer-comparison equality
    - horizontal and vertical canonical-mate pasting, including reindexing and unit/counit coherence
    - pullback-side composition coherence and actual D pasting
    - named finite nonvacuity, K4 and final target assembly
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: the horizontal route is factorized through the generated northwest compositors, both component comparisons, the normalized-left compositor, and the generated bottom equality transport; strong-cocartesian uniqueness then proves horizontalBCPastingComparison_eq_outer, the equality of the pasted comparison Iso with the independently generated normalized outer semantic comparison Iso
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingComparisonNormalization.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCHorizontalPastingNormalizedComparison.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCHorizontalPastingBottomAlignment.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCHorizontalPastingComparisonFactorization.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCHorizontalPastingComparisonEqualityRoutes.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCHorizontalPastingComparisonNormalizedSplit.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCHorizontalPastingComparisonInnerSplit.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCHorizontalPastingNormalizedFactorization.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCHorizontalPastingComparisonEquality.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - horizontalBCPastingNormalizedComponentComparison_hom_fac
    - horizontalBCPastingOuterBoundaryComparison_hom_fac
    - horizontalBCPastingComparison_eq_outer
  claim_mapping:
    theorem_names:
      - horizontalBCPastingComparison_eq_outer
    source_labels:
      - target theorem E horizontal covariant transport-square comparison coherence predecessor
    conjuncts:
      - the componentwise horizontal comparison retains both generated square comparisons and all normalization compositors
      - the generated bottom equality transport is consumed in the lift factorization
      - the aligned componentwise route equals the independently generated comparison of the normalized outer square
    undischarged_assumptions:
      - vertical comparison normalization and outer equality
      - horizontal and vertical coreBeckChevalleyMate pasting, including selected reindexing and unit/counit coherence
      - pullback-side composition coherence and actual D pasting
      - named finite nonvacuity, K4 and final target assembly
    acceptance_point: the horizontal covariant transport-square comparison-Iso equality is proved as a predecessor of E; no coreBeckChevalleyMate pasting, vertical, or final target completion is claimed
    port_status: unported (Research-proved)
audits:
  premise_delta:
    discharged:
      - horizontal covariant transport-square comparison-Iso equality
      - horizontal normalized route lift factorization including bottom equality transport
    remaining:
      - vertical normalization, alignment and comparison-Iso equality
      - horizontal and vertical coreBeckChevalleyMate pasting with selected reindexing and unit/counit coherence
      - pullback-side composition coherence
      - actual D pasting, named finite nonvacuity, K4 and final assembly
  certificate_provenance:
    discharged:
      - the bottom transport comes from horizontalBCPastingNormalizedBottom_eq
      - the outer comparison comes from normalizedNestedPasteSemanticInput and bcSemanticCoreTransportSquareIso
      - equality follows from strong-cocartesian uniqueness after both hom components are proved to factor the same iterated lift
    unresolved: []
  proof_use:
    used:
      - horizontalBCPastingComponentComparison_hom_fac
      - horizontalBCPastingNormalizedTopCompositor
      - horizontalBCPastingNormalizedLeftCompositor
      - horizontalBCPastingNormalizedBottom_eq
      - coreFiberIteratedLift_transportEqIso_fac
      - bcSemanticCoreTransportSquareIso_hom_fac
      - coreFiberIteratedLift_isStronglyCocartesian
    unused: []
  structure_field_escape: none-found
  route_integrity: the proof expands and consumes every horizontal pasted-route factor before applying uniqueness; it does not replace the route by a caller-authored comparison
  target_fitting: none-found
  vacuity: the equality is parametric in generated horizontal pasting data; named target-level nonvacuity remains open
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: the result is limited to the covariant transport-square predecessor and does not discharge the canonical mate named by C and E
  validation_refs:
    - focused BCHorizontalPastingComparisonEquality single-file elaboration: pass
    - four declarations under the final module namespace, standard axioms only
  blocking_findings: []
  next_obligation: construct the vertical covariant-square normalization, exact-boundary alignment and equality with the normalized outer semantic comparison; then prove horizontal and vertical coreBeckChevalleyMate pasting with the required reindexing, unit/counit and pullback-side composition coherence before actual diagnostic pasting
```

### Cycle 90 — horizontal outer-boundary comparison alignment

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 90
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: 093d2373bb1b22083f18894bff3992297a348bc9
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5391820004
  proof_dag_predecessors:
    - horizontalBCPastingNormalizedComponentComparison
    - toSemanticCart_compPresentation_hom
  proof_obligation: identify the normalized horizontal outer bottom edge with the composite component bottom edge and transport the normalized component comparison onto the exact outer-square functor boundary
  selection_reason: Cycle 89 left only the finite-composition realization mismatch before the horizontal component route and Cycle 85 outer semantic comparison had identical source and target functors
  expected_result_type: target-proof-checkpoint
  risks:
    - replacing the generated bottom equality by definitional equality
    - transporting the bottom functor in the wrong direction
    - claiming equality of the two comparison isomorphisms from equality of their endpoints
  unchecked:
    - equality of horizontalBCPastingOuterBoundaryComparison with the Cycle 85 outer semantic comparison
    - vertical normalization, boundary alignment and outer equality
    - pullback-side mate coherence, actual D pasting, nonvacuity, K4 and final assembly
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: horizontalBCPastingNormalizedBottom_eq derives the exact outer-bottom equality from finite presentation composition realization; horizontalBCPastingOuterBoundaryComparison then transports the Cycle 89 target functor in the reverse equality direction so the component route has the exact normalized outer-square boundary
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCHorizontalPastingBottomAlignment.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - horizontalBCPastingNormalizedBottom_eq
    - horizontalBCPastingOuterBoundaryComparison
  claim_mapping:
    theorem_names:
      - horizontalBCPastingNormalizedBottom_eq
      - horizontalBCPastingOuterBoundaryComparison
    source_labels:
      - target theorem E horizontal C comparison boundary-alignment predecessor
    conjuncts:
      - the normalized outer bottom is propositionally the composite of component bottoms
      - the normalized component comparison has exactly the outer semantic comparison source and target functors
    undischarged_assumptions:
      - equality of the aligned component comparison with the outer semantic comparison
      - all vertical normalization and equality obligations
      - pullback-side coherence, D pasting, nonvacuity, K4 and final assembly
    acceptance_point: horizontal component and outer comparisons now inhabit the same Iso type; their equality remains open
    port_status: unported (Research-proved)
audits:
  premise_delta:
    discharged:
      - generated horizontal bottom-edge realization equality
      - horizontal component comparison target-functor alignment
    remaining:
      - horizontal comparison-Iso equality
      - vertical normalization, alignment and equality
      - pullback-side coherence, D pasting, named finite nonvacuity, K4 and final assembly
  certificate_provenance:
    discharged:
      - bottom equality is generated by toSemanticCart_compPresentation_hom from the two finite arrows
      - functor alignment is the equality-induced iso, not a caller-supplied comparison
    unresolved: []
  proof_use:
    used:
      - horizontalBCPastingNormalizedComponentComparison
      - horizontalBCPastingNormalizedBottom_eq
      - toSemanticCart_compPresentation_hom
      - eqToIso
    unused: []
  structure_field_escape: none-found
  route_integrity: equality transport only replaces the component bottom composite by the exact normalized outer bottom and leaves the comparison route unchanged
  target_fitting: none-found
  vacuity: the alignment is parametric in horizontal pasting data; named target-level nonvacuity remains open
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - official focused BCHorizontalPastingBottomAlignment module check: pass
    - two declarations under the module namespace, standard axioms only
  blocking_findings: []
  next_obligation: prove horizontalBCPastingOuterBoundaryComparison equals the Cycle 85 semantic outer comparison, then build the vertical normalization and alignment chain
```

### Cycle 89 — normalized horizontal component comparison

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 89
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: 1277b575d564c8d85c0ef52b3d97b387a4092e66
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5391764147
  proof_dag_predecessors:
    - horizontalBCPastingComponentComparison
    - horizontalBCPastingNormalizedTopCompositor
    - horizontalBCPastingNormalizedLeftCompositor
  proof_obligation: transport the literal horizontal componentwise comparison route onto the canonical northwest-normalized source and left edge
  selection_reason: Cycles 86 and 87 provide exactly the conjugating compositors and the literal component route; their composition is required before comparison with the Cycle 85 outer semantic iso
  expected_result_type: target-proof-checkpoint
  risks:
    - conjugating with the northwest isomorphism in the wrong direction
    - omitting one of the normalized incident-edge compositors
    - claiming outer-comparison equality before aligning the generated bottom presentation
  unchecked:
    - equality of the generated bottom composite with the normalized outer bottom edge at the transport-functor level
    - equality of the fully aligned horizontal route with the Cycle 85 outer semantic comparison
    - vertical normalization and outer equality
    - pullback-side mate coherence, actual D pasting, nonvacuity, K4 and final assembly
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: horizontalBCPastingNormalizedComponentComparison expands the normalized top transport through the northwest inverse, applies the literal horizontal component route inside that transport context, and folds the normalized left transport back on the target side
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCHorizontalPastingNormalizedComparison.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - horizontalBCPastingNormalizedComponentComparison
  claim_mapping:
    theorem_names:
      - horizontalBCPastingNormalizedComponentComparison
    source_labels:
      - target theorem E horizontal C comparison normalization predecessor
    conjuncts:
      - source transport uses the normalized outer top edge
      - the literal component comparison is whiskered by transport across the canonical northwest inverse
      - target transport uses the normalized outer left edge
    undischarged_assumptions:
      - bottom-edge alignment and equality with the outer horizontal comparison
      - vertical normalization and comparison equality
      - pullback-side coherence, D pasting, nonvacuity, K4 and final assembly
    acceptance_point: the horizontal component route is conjugated onto the normalized northwest object; bottom alignment and outer-comparison equality remain open
    port_status: unported (Research-proved)
audits:
  premise_delta:
    discharged:
      - horizontal northwest conjugation of the component comparison route
    remaining:
      - bottom-edge functor alignment and horizontal outer-comparison equality
      - vertical normalization and equality
      - pullback-side coherence, D pasting, named finite nonvacuity, K4 and final assembly
  certificate_provenance:
    discharged:
      - conjugating comparisons are generated by the canonical northwest pullback isomorphism and G-109 compositors
      - the middle comparison is the Cycle 87 generated component route
    unresolved: []
  proof_use:
    used:
      - horizontalBCPastingNormalizedTopCompositor
      - horizontalBCPastingComponentComparison
      - horizontalBCPastingNormalizedLeftCompositor
      - bcPastingNorthwestIso
    unused: []
  structure_field_escape: none-found
  route_integrity: the same northwest inverse transport is retained on both sides of the literal horizontal comparison
  target_fitting: none-found
  vacuity: the route is parametric in horizontal pasting data; named target-level nonvacuity remains open
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - official focused BCHorizontalPastingNormalizedComparison module check: pass
    - one declaration under the module namespace, standard axioms only
  blocking_findings: []
  next_obligation: align the generated horizontal bottom composite with the normalized outer bottom edge and prove equality with the Cycle 85 semantic comparison, then perform the vertical normalization
```

### Cycle 88 — vertical componentwise comparison route

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 88
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: 95d9c3590024c43b1187a751e9c32e7b7da7e40f
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5391696103
  proof_dag_predecessors:
    - bcSemanticCoreTransportSquareIso
    - coreFiberCompositor
  proof_obligation: construct the componentwise vertical covariant comparison route from the generated comparisons of the upper and lower component squares, aligned to the literal outer rectangle by G-109 compositors
  selection_reason: Cycle 87 fixed the horizontal component route; the vertical analogue is the remaining route-construction predecessor before both directions can be normalized and compared with their outer semantic comparisons
  expected_result_type: target-proof-checkpoint
  risks:
    - reversing the upper-to-lower order of component comparisons
    - expanding the wrong composite outer edge
    - treating route construction as equality with the outer semantic comparison
  unchecked:
    - northwest conjugation of the horizontal and vertical literal routes
    - equality of both normalized component routes with their Cycle 85 outer semantic comparisons
    - pullback-side mate coherence and actual D pasting
    - named finite nonvacuity, K4 and final assembly
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: verticalBCPastingComponentComparison expands the composite right transport, applies the upper semantic square comparison whiskered by the lower right transport, applies the lower comparison inside the upper left context, and folds the two left transports to the literal outer left edge
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCVerticalPastingComparisonRoute.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - verticalBCPastingComponentComparison
  claim_mapping:
    theorem_names:
      - verticalBCPastingComponentComparison
    source_labels:
      - target theorem E vertical C comparison pasting predecessor
    conjuncts:
      - the upper component comparison is applied first with the lower right transport retained
      - the lower component comparison then carries the shared edge to the lower bottom transport
      - generated outer right and left compositors align the route with the literal rectangle
    undischarged_assumptions:
      - northwest normalization and equality with the outer comparisons in both directions
      - pullback-side mate coherence, D pasting, nonvacuity, K4 and final assembly
    acceptance_point: the actual vertical componentwise covariant comparison route exists with the required ordered factors; no outer-comparison equality is claimed
    port_status: unported (Research-proved)
audits:
  premise_delta:
    discharged:
      - vertical upper-to-lower composition of the two generated semantic square comparisons
      - covariant right and left outer-boundary alignment by G-109 compositors
    remaining:
      - northwest normalization and outer-comparison equality for both directions
      - pullback-side coherence, actual D pasting, named finite nonvacuity, K4 and final assembly
  certificate_provenance:
    discharged:
      - both component comparisons are generated directly from their semantic squares
      - all outer-boundary comparisons are generated by coreFiberCompositor from the actual arrows
    unresolved: []
  proof_use:
    used:
      - bcSemanticCoreTransportSquareIso
      - coreFiberCompositor
      - Functor.isoWhiskerLeft
      - Functor.isoWhiskerRight
    unused: []
  structure_field_escape: none-found
  route_integrity: the route follows top, upper right, applies the upper comparison, applies the lower comparison, and exits through upper left, lower left and bottom
  target_fitting: none-found
  vacuity: the route is parametric in every generated vertical pasting datum; named target-level nonvacuity remains open
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - official focused BCVerticalPastingComparisonRoute module check: pass
    - one declaration under the module namespace, standard axioms only
  blocking_findings: []
  next_obligation: conjugate both literal component routes by the Cycle 86 northwest-normalization compositors and prove their equalities with the Cycle 85 outer semantic comparisons
```

### Cycle 87 — horizontal componentwise comparison route

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 87
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: 4dcd924e18697fe4101593d980cb80fec1964e06
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5391636041
  proof_dag_predecessors:
    - bcSemanticCoreTransportSquareIso
    - coreFiberCompositor
  proof_obligation: construct the componentwise horizontal covariant comparison route from the generated comparisons of the left and right component squares, aligned to the literal outer rectangle by G-109 compositors
  selection_reason: Cycle 86 aligned the normalized outer incident edges with the literal paste; the next route-level predecessor is the actual horizontal composite of the two component comparisons before northwest conjugation and equality with the outer comparison
  expected_result_type: target-proof-checkpoint
  risks:
    - reversing the left-to-right order of component comparisons
    - omitting top or bottom outer-edge compositors
    - treating route construction as equality with the outer semantic comparison
  unchecked:
    - conjugation of this literal horizontal route by the Cycle 86 northwest-normalization compositors
    - equality of the normalized horizontal component route with the Cycle 85 outer semantic comparison
    - vertical componentwise C comparison route and its equality theorem
    - actual D pasting, named finite nonvacuity, K4 and final assembly
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: horizontalBCPastingComponentComparison composes the right semantic square comparison whiskered by the left top transport with the left semantic square comparison whiskered by the right bottom transport, and uses the top compositor and inverse bottom compositor to place both ends on the literal outer boundary
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCHorizontalPastingComparisonRoute.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - horizontalBCPastingComponentComparison
  claim_mapping:
    theorem_names:
      - horizontalBCPastingComponentComparison
    source_labels:
      - target theorem E horizontal C comparison pasting predecessor
    conjuncts:
      - the right component comparison is applied first inside the left top transport context
      - the left component comparison then carries the shared edge to the two bottom transports
      - generated outer top and bottom compositors align the component route with the literal rectangle
    undischarged_assumptions:
      - northwest-normalized horizontal route construction and equality with the outer comparison
      - vertical component comparison composition
      - pullback-side mate coherence, D pasting, nonvacuity, K4 and final assembly
    acceptance_point: the actual horizontal componentwise covariant comparison route exists with the required ordered factors; no outer-comparison equality is claimed
    port_status: unported (Research-proved)
audits:
  premise_delta:
    discharged:
      - horizontal left-to-right composition of the two generated semantic square comparisons
      - covariant top and bottom outer-boundary alignment by G-109 compositors
    remaining:
      - northwest normalization and outer-comparison equality for the horizontal route
      - the corresponding vertical route and equality theorem
      - pullback-side coherence, actual D pasting, named finite nonvacuity, K4 and final assembly
  certificate_provenance:
    discharged:
      - both component comparisons are generated directly from their semantic squares
      - all outer-boundary comparisons are generated by coreFiberCompositor from the actual arrows
    unresolved: []
  proof_use:
    used:
      - bcSemanticCoreTransportSquareIso
      - coreFiberCompositor
      - Functor.isoWhiskerLeft
      - Functor.isoWhiskerRight
    unused: []
  structure_field_escape: none-found
  route_integrity: the route follows top-left then top-right, applies the right square comparison, applies the left square comparison, and exits through bottom-left then bottom-right
  target_fitting: none-found
  vacuity: the route is parametric in every generated horizontal pasting datum; named target-level nonvacuity remains open
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - official focused BCHorizontalPastingComparisonRoute module check: pass
    - one declaration under the module namespace, standard axioms only
  blocking_findings: []
  next_obligation: conjugate the literal horizontal component route by the Cycle 86 northwest-normalization compositors and prove its equality with the Cycle 85 outer semantic comparison, then construct the vertical analogue
```

### Cycle 86 — northwest-normalization transport compositors

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 86
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: bcafa793af5a9ce9b6d6459e841a2664e9b1801d
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5391543943
  proof_dag_predecessors:
    - HorizontalBCPastingData.pasteNorthwestIso
    - VerticalBCPastingData.pasteNorthwestIso
    - normalizedNestedPasteSquare
    - coreFiberCompositor
  proof_obligation: expose the canonical northwest isomorphism uniformly and factor top- and left-edge transport of each normalized pasted square through its inverse and the corresponding literal pasted edge
  selection_reason: Cycle 85 fixed the outer comparison on the normalized square; componentwise C comparison pasting requires both incident normalized transports to be aligned with the literal component routes before their comparisons can be composed
  expected_result_type: target-proof-checkpoint
  risks:
    - identifying independently generated northwest codes by equality instead of their canonical pullback isomorphism
    - inserting caller-supplied transport comparisons
    - treating edge factorization as componentwise comparison composition
  unchecked:
    - horizontal and vertical componentwise C comparison composition using these four compositors
    - compatibility of the resulting C comparison routes with the outer semantic comparison
    - actual horizontal and vertical D route specialization
    - named finite nonvacuity, final K4 integration and final assembly
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: bcPastingNorthwestIso exposes the generated pullback isomorphism for either direction; the four horizontal and vertical top/left compositor declarations identify normalized incident-edge transport with transport first across its inverse and then along the literal pasted edge
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingComparisonNormalization.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - bcPastingNorthwestIso
    - horizontalBCPastingNormalizedTopCompositor
    - horizontalBCPastingNormalizedLeftCompositor
    - verticalBCPastingNormalizedTopCompositor
    - verticalBCPastingNormalizedLeftCompositor
  claim_mapping:
    theorem_names:
      - horizontalBCPastingNormalizedTopCompositor
      - horizontalBCPastingNormalizedLeftCompositor
      - verticalBCPastingNormalizedTopCompositor
      - verticalBCPastingNormalizedLeftCompositor
    source_labels:
      - target theorem E predecessor for C comparison compatibility with horizontal and vertical pasting
    conjuncts:
      - horizontal normalized top and left transports factor through the canonical northwest inverse
      - vertical normalized top and left transports factor through the canonical northwest inverse
    undischarged_assumptions:
      - componentwise comparison composition and equality with the outer comparison
      - pullback reindexing compatibility on the mate routes
      - actual D pasting, finite nonvacuity, final K4 integration and final assembly
    acceptance_point: the normalized and literal covariant edge functors are joined by generated G-109 compositors in both directions; no comparison-composition theorem is claimed
    port_status: unported (Research-proved)
audits:
  premise_delta:
    discharged:
      - direction-independent canonical northwest isomorphism API
      - generated covariant transport factorization for all four normalized incident edges
    remaining:
      - horizontal and vertical componentwise C comparison composition
      - equality of each composed comparison route with the outer semantic comparison
      - pullback-side route coherence, actual D pasting, named finite nonvacuity, K4 and final assembly
  certificate_provenance:
    discharged:
      - northwest comparisons are generated by the two reviewed pullback universal properties
      - transport comparisons are generated by coreFiberCompositor from the actual incident arrows
    unresolved: []
  proof_use:
    used:
      - HorizontalBCPastingData.pasteNorthwestIso
      - VerticalBCPastingData.pasteNorthwestIso
      - coreFiberCompositor
    unused: []
  structure_field_escape: none-found
  route_integrity: every factorization uses the inverse of the canonical literal-to-outer northwest isomorphism followed by the unchanged literal pasted top or left edge
  target_fitting: none-found
  vacuity: all four declarations are parametric in generated horizontal or vertical pasting data; named target-level nonvacuity remains open
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - official focused BCPastingComparisonNormalization module check: pass
    - five declarations under the module namespace, standard axioms only
  blocking_findings: []
  next_obligation: define the two componentwise horizontal and vertical C comparison routes using these normalization compositors and prove equality with the Cycle 85 outer semantic comparison
```

### Cycle 85 — pasted comparison realization bridge

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 85
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: 14c19ab73081843f0af7a6f243e628b7a7849dab
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5391366472
  proof_dag_predecessors:
    - toSemanticBC_pastePresentation_eq
    - BCRealizationProvenance
    - bcProvenanceCoreTransportSquareIso_eq_semantic
  proof_obligation: generate the exact realization provenance for the normalized pasted semantic input and identify its outer presentation comparison with the canonical semantic comparison
  selection_reason: expanding the actual D routes exposed a required northwest normalization and reindexing-compositor layer; the C-side outer comparison realization is the smallest reviewable predecessor shared by both pasting directions
  expected_result_type: target-proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingComparisonRealization.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - treating realization of the outer comparison as componentwise comparison composition
    - accepting an ungenerated realization equality from the caller
    - erasing the canonical northwest normalization required by literal pasting
  unchecked:
    - horizontal and vertical componentwise C comparison composition
    - actual horizontal and vertical D route specialization and its reindexing and transport compositors
    - final K4 integration of the Cycle 82 G-106/G-109 coherence bridge and its transportAlong_comp_coherence proof-use
    - named finite nonvacuity specialization with both actual target coherences
    - pullback-side composition coherence, K4 and final assembly
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: bcPastingNormalizedProvenance packages the reviewed finite-code paste presentation and its generated semantic realization equality; bcPastingCoreTransportSquareIso_eq_semantic then identifies the presentation-generated outer covariant comparison with the canonical semantic comparison on the northwest-normalized literal paste
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingComparisonRealization.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - bcPastingNormalizedProvenance
    - bcPastingCoreTransportSquareIso_eq_semantic
  claim_mapping:
    theorem_names:
      - bcPastingCoreTransportSquareIso_eq_semantic
    source_labels:
      - target theorem E predecessor for C comparison compatibility with horizontal and vertical pasting
    conjuncts:
      - the finite-code pasted outer presentation realizes the normalized literal pasted semantic square
      - its generated covariant comparison is the canonical semantic comparison on that normalized square
    undischarged_assumptions:
      - componentwise horizontal and vertical comparison composition
      - pullback reindexing and transport-compositor compatibility for actual routes
      - final K4 assembly consuming the Cycle 82 G-106/G-109 bridge and transportAlong_comp_coherence proof chain
      - the remaining D pasting and named finite nonvacuity obligations
    acceptance_point: outer-presentation comparison realization is discharged uniformly for either pasting direction; comparison composition and route specialization remain open
    port_status: unported (Research-proved)
audits:
  premise_delta:
    discharged:
      - exact BCRealizationProvenance for the normalized pasted semantic input
      - equality of the resulting outer presentation comparison with its canonical semantic comparison
    remaining:
      - componentwise horizontal and vertical C comparison composition
      - actual D route specialization with reindexing and transport compositors
      - final K4 integration of the already proved Cycle 82 G-106/G-109 coherence bridge
      - named finite nonvacuity, pullback-side coherence, K4 and final assembly
  certificate_provenance:
    discharged:
      - the realization equality is generated by toSemanticBC_pastePresentation_eq from the reviewed paste constructor
      - the comparison equality is generated by the generic provenance-to-semantic comparison theorem
    unresolved: []
  proof_use:
    used:
      - pastePresentation
      - normalizedNestedPasteSemanticInput
      - toSemanticBC_pastePresentation_eq
      - bcProvenanceCoreTransportSquareIso_eq_semantic
    unused: []
  prior_evidence_retained:
    - Cycle 82 proved the G-106/G-109 route bridge and consumed transportAlong_comp_coherence; Cycle 85 does not reopen that proof and leaves its final K4 integration explicit
  structure_field_escape: none-found
  route_integrity: the comparison is transported only across the reviewed outer-presentation realization equality and retains the canonical northwest-normalized pasted square
  target_fitting: none-found
  vacuity: the bridge is parametric in either finite-code pasting input; target-level named finite nonvacuity remains unverified in this cycle
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - official focused BCPastingComparisonRealization module check: pass
    - two declarations under the module namespace, standard axioms only
  blocking_findings: []
  next_obligation: prove componentwise horizontal and vertical C comparison composition through the canonical northwest normalization and pullback reindexing compositors, then specialize the D composition laws to the actual routes while retaining the Cycle 82 G-106/G-109 bridge for final K4 assembly
```

### Cycle 84 — endpoint action and reselection composition laws

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 84
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: fe80b3825376aef79f9450ee8082118a99df4f69
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5391301976
  proof_dag_predecessors:
    - coreFiberFunctorPackageAutHom
    - coreFiberFunctorPackageAutHom_hom
    - mapEdgeReselection
  proof_obligation: prove composition of the generated endpoint group homomorphisms and derive composition of the canonical mapped reselection from that d2 law
  selection_reason: Cycle 83 exposed the d4 law but its rejected ledger omitted the logically prior d2 diagnostic comparison composition; fixing both in one proof chain preserves every D pasting residual
  expected_result_type: target-proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticPastingCoherence.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - proving only pointwise reselection equality while omitting endpoint group-hom composition
    - accepting either composition compatibility from the caller
    - promoting generic functor composition to actual horizontal or vertical BC-route compatibility
  unchecked:
    - actual horizontal and vertical d2 endpoint comparison and d4 reselection route specialization
    - d3 transported diagnostic-data, d5 coherence, and d6 vanishing composition compatibility
    - named finite nonvacuity specialization with both actual target coherences
    - C comparison compatibility and pullback-side composition coherence
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: coreFiberFunctorPackageAutHom_comp identifies the generated endpoint group homomorphism for F composed with H with the composite of the two generated homomorphisms; mapEdgeReselection_comp then rewrites by that d2 theorem to derive the d4 canonical reselection composition law
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticPastingCoherence.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - coreFiberFunctorPackageAutHom_comp
    - mapEdgeReselection_comp
  claim_mapping:
    theorem_names:
      - coreFiberFunctorPackageAutHom_comp
      - mapEdgeReselection_comp
    source_labels:
      - target theorem E compatibility of D diagnostic comparison and mapped reselection with horizontal and vertical pasting
    conjuncts:
      - generated endpoint group action along a composite equals successive generated endpoint actions
      - canonical mapped reselection along a composite equals successive canonical mapping
    undischarged_assumptions:
      - identification of actual horizontal and vertical BC diagnostic routes with the relevant composite functors
      - d3 transported-data, d5 coherence, and d6 vanishing composition compatibility
      - named finite nonvacuity specialization with nonidentity initial defect and reselection
      - C comparison compatibility and pullback-side coherence
    acceptance_point: the common d2 and d4 composition laws are discharged for arbitrary composable core-fiber functors; the route-specific D pasting package remains open
    port_status: unported (Research-proved)
audits:
  premise_delta:
    discharged:
      - d2 endpoint group-hom composition for arbitrary composable core-fiber functors
      - d4 canonical reselection composition derived from the d2 theorem
    remaining:
      - actual horizontal and vertical d2 endpoint comparison and d4 reselection specialization
      - d3 transported-data, d5 coherence, and d6 vanishing composition compatibility
      - named finite nonvacuity specialization and its two actual target coherences
      - C comparison compatibility, pullback-side coherence, K4 and final assembly
  certificate_provenance:
    discharged:
      - both d2 sides are generated by packageFiberAutCoreFiberEquiv and functor mapAut from the same endpoint automorphism
      - both d4 sides are generated by mapEdgeReselection from the same source reselection and the reviewed d2 equality
    unresolved: []
  proof_use:
    used:
      - coreFiberFunctorPackageAutHom_hom
      - coreFiberFunctorPackageAutHom_comp
      - packageFiberAutCoreFiberEquiv
      - functor composition map
    unused: []
  structure_field_escape: none-found
  route_integrity: endpoint action and reselection compare the ordered first-then-second factors with their composite
  target_fitting: none-found
  vacuity: both lemmas are parametric in their endpoint or diagnostic inputs; target-level named finite nonvacuity remains unverified in this cycle
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - focused BCDiagnosticPastingCoherence file check: pass
    - two declarations under the module namespace, standard axioms only
  blocking_findings: []
  next_obligation: identify the actual horizontal and vertical diagnostic routes with the generic d2 and d4 composite laws, then construct d3, d5, and d6 composition compatibility while retaining named finite nonvacuity and the C and pullback-side obligations
```

### Cycle 82 — complete G-106/G-109 three-arrow route bridge

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 82
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: 96c4735c06a781cbaae2abb454339c9daef94262
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5390957216
  proof_dag_predecessors:
    - coreFiberCompositor_whiskered_eq_g106
    - coreFiberAssociatorCast_eq_g106
    - transportAlong_comp_coherence
  proof_obligation: identify both actual G-109 pentagon routes with the corresponding endpoint-casted G-106 paths and derive compositor equality through the named G-106 coherence theorem
  selection_reason: Cycles 80 and 81 fixed the whiskered component and associator orientation; the full route bridge is now the remaining package-to-fiber predecessor required by G-110(E)
  expected_result_type: target-proof-checkpoint
  risks:
    - using the pre-existing G-109 pentagon equality to manufacture route identification
    - invoking transportAlong_comp_coherence decoratively without proof-term dependence
    - exchanging the left and right G-106 paths
  unchecked:
    - C comparison compatibility with horizontal and vertical BC pasting
    - D diagnostic map, reselection, coherence, and vanishing compatibility with pasting
    - pullback-side composition coherence, K4 and final assembly
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: coreFiberPentagonLeftRoute_eq_components directly rewrites the actual left route by the Cycle 78 binary and Cycle 80 whiskered component bridges. coreFiberPentagonRightRoute_eq_components directly rewrites the actual right route by the Cycle 81 associator and two Cycle 78 binary component bridges. The resulting component routes are then identified with the endpoint-casted G-106 left-adjacent and inverse-associator-plus-right-adjacent paths. coreFiberG106RouteHom_eq directly rewrites by transportAlong_comp_coherence, and coreFiberCompositor_assoc_via_g106 derives the actual G-109 compositor equality through that G-106 route equality without using coreFiberCompositor_assoc.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingCoherenceRoutes.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingCoherenceRoutesWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - coreFiberG106LeftRouteHom
    - coreFiberG106RightRouteHom
    - coreFiberG106LeftComponentRoute
    - coreFiberG106RightComponentRoute
    - coreFiberPentagonLeftRoute_eq_components
    - coreFiberPentagonRightRoute_eq_components
    - coreFiberPentagonLeftRoute_hom_eq_g106
    - coreFiberPentagonRightRoute_hom_eq_g106
    - coreFiberPentagonLeftRoute_eq_g106
    - coreFiberPentagonRightRoute_eq_g106
    - coreFiberG106RouteHom_eq
    - coreFiberG106Route_eq
    - coreFiberCompositor_assoc_via_g106
    - finiteCoreFiberCompositorAssocViaG106_identity_control
  claim_mapping:
    theorem_names:
      - coreFiberPentagonLeftRoute_eq_g106
      - coreFiberPentagonRightRoute_eq_g106
      - coreFiberCompositor_assoc_via_g106
    source_labels:
      - target theorem E package-level G-106 to fiber-functor G-109 compositor bridge
    conjuncts:
      - both actual G-109 three-arrow routes equal their correctly oriented G-106 package paths
      - transportAlong_comp_coherence is consumed in the Fiber-level compositor equality proof
    undischarged_assumptions:
      - remaining C/D pasting compatibility
      - pullback-side composition coherence, K4 and final A-E assembly
    acceptance_point: the package-to-fiber compositor bridge portion of E is discharged; E as a whole remains open
    port_status: unported
audits:
  premise_delta:
    discharged:
      - route-specific three-arrow identification
      - nondecorative transportAlong_comp_coherence proof-use in the G-109 compositor equality
    remaining:
      - C/D pasting compatibility and pullback-side coherence
      - K4 and final assembly
  certificate_provenance:
    discharged:
      - each route equality is independently generated by endpoint casts, named G-106 paths, canonical factorization equations, and strong cocartesian uniqueness
      - the final path equality is generated by transportAlong_comp_coherence
    unresolved: []
  proof_use:
    used:
      - transportAlongLeftAdjacentCompHom_fac
      - transportAlongAdjacentCompHom_fac
      - transportAlong_comp_coherence
      - coreFiberCompositorApp_hom_eq_g106
      - coreFiberCompositor_whiskered_eq_g106
      - coreFiberAssociatorCast_eq_g106
      - coreFiberPentagonLeftRoute_fac
      - coreFiberPentagonRightRoute_fac
    unused:
      - coreFiberCompositor_assoc
  structure_field_escape: none-found
  route_integrity: left route maps to left-adjacent G-106 path; right route maps to inverse-associator followed by right-adjacent path
  vacuity: universal three-arrow route bridge; finite identity theorem is only an elaboration control
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - targeted BCPastingCoherenceRoutesWitnesses module build: pass
    - main module: 21 declarations, standard axioms only
    - witness module: 1 declaration, standard axioms only
  blocking_findings: []
  next_obligation: connect the C Beck--Chevalley comparison and D diagnostic covariance layers to horizontal and vertical square pasting, then construct the missing pullback-side composition coherence
```

### Cycle 81 — direct G-106/G-109 associator identification

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 81
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: 70b7758c7204f70f1a0f54e6b5bac63fb18c1302
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5390890371
  proof_dag_predecessors:
    - coreFiberLift_eqCast_fac
    - transportAlong_assocFiberIso_hom_fac
    - coreFiberWhiskeringBaseHom_eq
  proof_obligation: identify G-109 coreFiberAssociatorCast directly with the correctly oriented G-106 transportAlong_assocFiberIso comparison while retaining both direct-transport endpoint casts
  selection_reason: Cycle 80 fixed the named whiskered component; associator compatibility is the remaining component-level predecessor before either complete three-arrow route can be identified
  expected_result_type: target-proof-checkpoint
  risks:
    - using the G-106 forward leg despite the opposite G-109 associator orientation
    - erasing either direct-transport endpoint cast
    - promoting associator compatibility to the full route theorem
  unchecked:
    - both route-specific three-arrow identifications
    - nondecorative transportAlong_comp_coherence proof-use
    - C/D pasting, pullback-side coherence, K4 and final assembly
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: coreFiberTripleLeftPackageEq and coreFiberTripleRightPackageEq retain the two direct-transport endpoint casts. coreFiberAssociatorCast_hom_eq proves that the actual left-to-right G-109 associator is the left endpoint cast followed by transportAlong_assocFiberIso.iso.inv and the inverse right endpoint cast; coreFiberAssociatorCast_eq_g106 records the same equality in the actual target Fiber.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingCoherenceAssociator.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingCoherenceAssociatorWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - transportAlong_assocFiberIso_inv_fac
    - coreFiberTripleLeftBaseHom_eq
    - coreFiberTripleRightBaseHom_eq
    - coreFiberTripleLeftPackageEq
    - coreFiberTripleRightPackageEq
    - coreFiberTripleLeftLift_cast_fac
    - coreFiberTripleRightLift_cast_fac
    - coreFiberAssociatorCast_hom_eq
    - coreFiberG106AssociatorHom
    - coreFiberAssociatorCast_eq_g106
    - finiteCoreFiberAssociatorG106_identity_control
  claim_mapping:
    theorem_names:
      - coreFiberAssociatorCast_hom_eq
      - coreFiberAssociatorCast_eq_g106
    source_labels:
      - target theorem E associator predecessor of the G-106/G-109 three-arrow bridge
    conjuncts:
      - the G-109 left-to-right associator equals the endpoint-casted inverse of the named G-106 associator iso
      - the equality holds for package and actual Fiber morphisms
    undischarged_assumptions:
      - route-specific three-arrow comparison and transportAlong_comp_coherence proof-use
      - remaining C/D pasting, pullback-side coherence, K4 and final A-E assembly
    acceptance_point: associator orientation and both endpoint casts are explicit; no complete path equality is claimed
    port_status: unported
audits:
  premise_delta:
    discharged:
      - direct associator-cast compatibility between G-109 and G-106
    remaining:
      - route-specific three-arrow bridge and explicit transportAlong_comp_coherence consumption
      - C/D pasting, pullback-side coherence, K4 and final assembly
  certificate_provenance:
    discharged:
      - left and right exact doctrine morphisms are computed from the three authored pointed arrows
      - the comparison is generated from canonical lift casts, the G-106 associator factorization, inverse cancellation, and strong cocartesian uniqueness
    unresolved: []
  proof_use:
    used:
      - coreFiberLift_eqCast_fac
      - transportAlong_assocFiberIso_hom_fac
      - coreFiberWhiskeringBaseHom_eq
      - coreFiberBaseHom_comp_doctrineHom
    unused: []
  structure_field_escape: none-found
  route_integrity: associator orientation fixed as iso.inv; complete left and right routes remain unchecked
  vacuity: universal three-arrow associator equality; finite identity control is only an elaboration control
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - targeted BCPastingCoherenceAssociatorWitnesses module build: pass
    - main module: 11 declarations, standard axioms only
    - witness module: 1 declaration, standard axioms only
  blocking_findings:
    - G-110(E) remains open until both actual G-109 routes are identified with the corresponding G-106 paths and transportAlong_comp_coherence is used in the final equality
  next_obligation: identify the G-109 left route with the casted G-106 left-adjacent path and the G-109 right route with the casted inverse-associator plus right-adjacent path
```

### Cycle 80 — direct G-106/G-109 whiskered-component identification

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 80
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: 75a39c0d4e992c7dd409750b70bef58fe714b77e
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5390777501
  proof_dag_predecessors:
    - coreFiberCompositor_whiskered_g106_fac
    - transportAlong_whiskeredCompFiberIso_hom_fac
    - coreFiberDirectPackageEq
  proof_obligation: construct the dependent endpoint cast and identify the transported G-109 compositor component directly with the named G-106 transportAlong_whiskeredCompFiberIso comparison
  selection_reason: Cycle 79 exposed the binary G-106 comparison as the first whiskered factor; the next fail-closed step is to retain the third exact doctrine morphism with its package and close the component equality before introducing associator casts
  expected_result_type: target-proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingCoherenceWhiskeredIso.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingCoherenceWhiskeredIsoWitnesses.lean
  risks:
    - treating the endpoint packages as definitionally equal
    - comparing only factorizations instead of the actual package and Fiber morphisms
    - promoting one whiskered component bridge to the full three-arrow coherence theorem
  unchecked:
    - associator-cast compatibility
    - route-specific three-arrow identification and transportAlong_comp_coherence proof-use
    - C/D pasting compatibility, pullback-side coherence, K4 and final assembly
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: coreFiberWhiskeredSourcePackageEq transports the intermediate package and third exact doctrine morphism as a dependent pair. coreFiberCompositor_whiskered_hom_eq then identifies the actual G-109 transported compositor package morphism with that endpoint cast followed by the named G-106 transportAlong_whiskeredCompFiberIso hom; coreFiberCompositor_whiskered_eq_g106 records the same equality in the actual target Fiber.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingCoherenceWhiskeredIso.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingCoherenceWhiskeredIsoWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - coreFiberWhiskeringBaseHom_eq
    - coreFiberWhiskeredSourcePackageEq
    - transportAlongSigmaHom_eqToHom
    - coreFiberWhiskeredSourceLift_cast_fac
    - coreFiberCompositor_whiskered_hom_eq
    - coreFiberG106WhiskeredCompositorHom
    - coreFiberCompositor_whiskered_eq_g106
    - finiteCoreFiberWhiskeredCompositorG106_identity_control
  claim_mapping:
    theorem_names:
      - coreFiberCompositor_whiskered_hom_eq
      - coreFiberCompositor_whiskered_eq_g106
    source_labels:
      - target theorem E whiskered-component predecessor of the G-106/G-109 three-arrow bridge
    conjuncts:
      - the transported G-109 compositor component equals the endpoint-casted named G-106 whiskered comparison
      - the equality holds for both the package morphism and the actual target-fiber morphism
    undischarged_assumptions:
      - associator compatibility and route-specific three-arrow bridge
      - explicit transportAlong_comp_coherence proof-use
      - remaining C/D pasting, pullback-side coherence, K4, and final A-E assembly
    acceptance_point: the named G-106 whiskered comparison is identified componentwise with explicit dependent endpoint transport; no associator or full path equality is claimed
    port_status: unported
audits:
  premise_delta:
    discharged:
      - endpoint-cast comparison with transportAlong_whiskeredCompFiberIso
    remaining:
      - associator and three-arrow coherence bridge
      - C/D pasting compatibility, pullback-side coherence, K4 and final assembly
  certificate_provenance:
    discharged:
      - the endpoint package equality is generated by coreFiberDirectPackageEq and coreFiberWhiskeringBaseHom_eq as a dependent pair
      - the component equality is generated from Cycle 79 factorization, canonical lift transport, G-106 whiskered factorization, and strong cocartesian uniqueness
    unresolved: []
  proof_use:
    used:
      - coreFiberCompositor_whiskered_g106_fac
      - transportAlong_whiskeredCompFiberIso_hom_fac
      - coreFiberDirectPackageEq
      - coreFiberWhiskeringBaseHom_eq
    unused: []
  structure_field_escape: none-found
  route_integrity: named whiskered component fixed; associator and complete three-arrow routes remain unchecked
  vacuity: universal three-arrow component equality; finite identity control is only an elaboration control
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - targeted BCPastingCoherenceWhiskeredIsoWitnesses module build: pass
    - main module: 7 declarations, standard axioms only
    - witness module: 1 declaration, standard axioms only
  blocking_findings:
    - full route identification remains open until coreFiberAssociatorCast is compared with transportAlong_assocFiberIso
  next_obligation: prove associator-cast compatibility, then identify the two actual G-109 three-arrow routes with the corresponding G-106 paths and consume transportAlong_comp_coherence nondecoratively
```

### Cycle 79 — first whiskering factorization of the binary component bridge

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 79
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: 20f686783213407d879dd95e956457f14726808b
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5390715666
  proof_dag_predecessors:
    - coreFiberCompositorApp_hom_eq_transportAlong_compFiberIso
    - coreFiberTransportMap_fac
  proof_obligation: expose the casted G-106 binary comparison as the actual first package factor in the G-109 compositor whiskering along a third pointed arrow
  selection_reason: Cycle 78 fixed the binary component itself; the next route-specific predecessor is its image under coreFiberTransportFunctor, before endpoint casts can be compared with transportAlong_whiskeredCompFiberIso
  expected_result_type: target-proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingCoherenceWhiskering.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingCoherenceWhiskeringWitnesses.lean
  risks:
    - claiming equality with transportAlong_whiskeredCompFiberIso before endpoint casts are constructed
    - hiding the binary source cast by definitional equality
    - promoting a factorization checkpoint to the full three-arrow bridge
  unchecked:
    - endpoint-cast comparison with transportAlong_whiskeredCompFiberIso
    - associator-cast compatibility
    - route-specific three-arrow identification and transportAlong_comp_coherence proof-use
    - C/D pasting compatibility, pullback-side coherence, K4 and final assembly
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: coreFiberCompositor_whiskered_g106_fac rewrites the actual G-109 transported compositor through coreFiberTransportMap_fac and the reviewed Cycle 78 component equality. Its right side visibly starts with coreFiberDirectPackageEq followed by transportAlong_compFiberIso, then the third canonical lift. It does not yet identify the transported component with the G-106 whiskered comparison.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingCoherenceWhiskering.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingCoherenceWhiskeringWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - coreFiberCompositor_whiskered_g106_fac
    - finiteCoreFiberCompositorWhiskeredG106_identity_control
  claim_mapping:
    theorem_names:
      - coreFiberCompositor_whiskered_g106_fac
    source_labels:
      - target theorem E first whiskering predecessor of the G-106/G-109 bridge
    conjuncts:
      - the transported G-109 component factors through the same explicit casted G-106 binary comparison
    undischarged_assumptions:
      - endpoint-cast comparison with transportAlong_whiskeredCompFiberIso
      - associator compatibility and route-specific three-arrow bridge
      - explicit transportAlong_comp_coherence proof-use
      - remaining K4 and final A-E assembly
    acceptance_point: the theorem fixes the first whiskered package factor only and leaves the named G-106 whiskered comparison unclaimed
    port_status: unported
audits:
  premise_delta:
    discharged:
      - first G-109 whiskering factorization through the Cycle 78 G-106 binary component
    remaining:
      - endpoint casts and direct transportAlong_whiskeredCompFiberIso identification
      - associator and three-arrow coherence bridge
      - remaining K4 and final assembly
  certificate_provenance:
    discharged:
      - the factorization is generated from coreFiberTransportMap_fac and the Cycle 78 component equality
    unresolved: []
  proof_use:
    used:
      - coreFiberTransportMap_fac
      - coreFiberCompositorApp_hom_eq_transportAlong_compFiberIso
    unused: []
  structure_field_escape: none-found
  route_integrity: first whiskered factor fixed; full three-arrow route integrity remains unchecked
  vacuity: universal three-arrow factorization; finite identity control is not a nondegeneracy claim
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - targeted BCPastingCoherenceWhiskeringWitnesses module build: pass
    - main module: 1 declaration, standard axioms only
    - witness module: 1 declaration, standard axioms only
    - direct axiom print for both reporting declarations: propext, Classical.choice, and Quot.sound only
  blocking_findings:
    - full whiskering compatibility remains open until endpoint casts identify this factorization with transportAlong_whiskeredCompFiberIso
  next_obligation: construct endpoint casts and identify the transported component directly with transportAlong_whiskeredCompFiberIso, then prove associator-cast compatibility
```

### Cycle 78 — direct binary G-106/G-109 compositor component bridge

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 78
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: f2c615a476c947ee1eba56c177d19d1c552c32a7
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5390389022
  proof_dag_predecessors:
    - coreFiberLift_projection
    - coreFiberCompositorApp_hom_fac
    - transportAlong_compFiberIso_hom_fac
  proof_obligation: identify one G-109 binary compositor component directly with the corresponding G-106 generated binary comparison, retaining every source-object and pointed-fiber cast explicitly
  selection_reason: the first review of the earlier three-arrow candidate found that common precomposition alone did not determine which G-109 route corresponded to which G-106 path. The smallest fail-closed repair is the component-level binary bridge required before whiskering and associator compatibility can be stated without exchanging the two paths.
  expected_result_type: target-proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingCoherenceBridge.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingCoherenceBridgeWitnesses.lean
  risks:
    - identifying only the two post-composition factorizations rather than the compositor component itself
    - erasing the package/fiber casts by a false definitional equality
    - promoting the binary component bridge to the full three-arrow coherence bridge
    - mistaking the finite identity-base elaboration control for nondegeneracy
  unchecked:
    - whiskering compatibility between coreFiberTransportMap and transportAlong_whiskeredCompFiberIso
    - associator-cast compatibility between coreFiberAssociatorCast and transportAlong_assocFiberIso
    - route-specific three-arrow identification and nondecorative transportAlong_comp_coherence proof-use
    - C comparison compatibility with horizontal and vertical pasting
    - D diagnostic comparison, mapped reselection, coherence, and vanishing compatibility with pasting
    - final A-E assembly
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: coreFiberBaseHom_comp_doctrineHom computes the exact doctrine-hom equality behind pointed composition. coreFiberDirectPackageEq retains the resulting object cast. coreFiberCompositorApp_hom_eq_transportAlong_compFiberIso proves equality of the actual G-109 package component with that cast followed by the G-106 generated comparison, and coreFiberCompositorApp_hom_eq_g106 packages the same equality as a target-fiber morphism. The earlier common-factor three-arrow claims were removed; transportAlong_comp_coherence is not yet claimed as consumed.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingCoherenceBridge.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingCoherenceBridgeWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - coreFiberLift_as_transportAlongHom
    - coreFiberBaseHom_comp
    - coreFiberBaseHom_comp_doctrineHom
    - coreFiberDirectPackageEq
    - coreFiberDirectLift_cast_fac
    - coreFiberCompositorApp_binary_bridge
    - coreFiberCompositorApp_hom_eq_transportAlong_compFiberIso
    - coreFiberG106CompositorHom
    - coreFiberCompositorApp_hom_eq_g106
    - finiteCoreFiberBinaryCompositorBridge_identity_control
  claim_mapping:
    theorem_names:
      - coreFiberCompositorApp_hom_eq_transportAlong_compFiberIso
      - coreFiberCompositorApp_hom_eq_g106
    source_labels:
      - target theorem E binary predecessor for the package-level G-106 to fiber-functor G-109 bridge
    conjuncts:
      - the G-109 binary compositor component equals the casted corresponding G-106 generated comparison
      - the equality holds both for the underlying package morphism and the actual target-fiber morphism
    undischarged_assumptions:
      - whiskering and associator compatibility
      - route-specific three-arrow bridge and transportAlong_comp_coherence proof-use
      - C comparison compatibility with horizontal and vertical BC pasting
      - D diagnostic comparison, mapped reselection, coherence, and vanishing compatibility with pasting
      - pullback-side composition coherence and K4 assembly
      - final A-E assembly and completion review
    acceptance_point: the actual compositor component is identified before any three-arrow path comparison, with an explicit source cast derived from pointed-base composition; no full E discharge is claimed
    port_status: unported
audits:
  premise_delta:
    discharged:
      - binary component predecessor of the E package-level G-106 to G-109 fiber compositor compatibility
    remaining:
      - whiskering and associator compatibility
      - route-specific three-arrow bridge and explicit proof-use of transportAlong_comp_coherence
      - C and D pasting compatibility
      - pullback-side composition coherence
      - K4 and final G-110 assembly
  certificate_provenance:
    discharged:
      - pointed-base equality is derived from coreFiberLift_projection
      - binary component equality is derived from the G-109 and G-106 generated factorization equations plus strong-lift uniqueness
    unresolved: []
  proof_use:
    used:
      - coreFiberLift_projection
      - coreFiberCompositorApp_hom_fac
      - transportAlong_compFiberIso_hom_fac
      - CategoryTheory.Functor.IsStronglyCocartesian.ext
    unused: []
  structure_field_escape: none-found
  route_integrity: binary component fixed; three-arrow route integrity remains unchecked
  vacuity: universal binary theorem; finite identity control is not a nondegeneracy claim
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - focused BCPastingCoherenceBridge.lean elaboration: pass; 11 declarations, standard axioms only
    - focused BCPastingCoherenceBridgeWitnesses.lean elaboration: pass; 2 declarations, standard axioms only
    - direct axiom print for the nine reporting declarations: propext, Classical.choice, and Quot.sound only
  blocking_findings:
    - full E bridge remains open until whiskering and associator compatibility make the left/right three-arrow correspondence route-specific
  next_obligation: prove the whiskered binary comparison and associator-cast compatibility, then identify G-109 left with G-106 left-aligned and G-109 right with G-106 adjacent before consuming transportAlong_comp_coherence
```

### Cycle 77 — horizontal/vertical pullback-pasting closure package

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 77
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: 04a806303c155a2d55954948282c63b41def5fcf
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5390290062
  proof_dag_predecessors:
    - HorizontalBCPastingData.nestedSquare_isPullback
    - VerticalBCPastingData.nestedSquare_isPullback
    - nestedPasteSquare_isPullback
    - toSemanticBC_pastePresentation_eq
    - toSemanticBC_sound
  proof_obligation: package the fixed K4/E horizontal and vertical pullback-square pasting closure so that the literal nested pullback, the generated outer BCPresentation pullback, and their canonical normalized realization equality are theorem outputs of one direction-indexed input
  selection_reason: the revised-card K3 package is accepted; K4 starts with the already reviewed finite-code pasting constructor, and fixing its three closure outputs is the shortest predecessor of every later comparison, diagnostic, and coherence compatibility theorem
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingClosure.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingClosureWitnesses.lean
  risks:
    - supplying a semantic pullback certificate or normalization equality as an input field
    - proving only the generated outer square while omitting the literal nested paste
    - handling only horizontal or only vertical pasting
    - claiming comparison, diagnostic, or G-106/G-109 coherence compatibility from square closure alone
  unchecked:
    - C comparison compatibility with pasting
    - D diagnostic comparison, mapped reselection, coherence, and vanishing compatibility with pasting
    - G-106/G-109 package-to-fiber coherence bridge
    - final A-E assembly
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: BCPastingClosure packages the literal nested pullback, the generated outer BCPresentation pullback, and the canonical normalized realization equality for either horizontal or vertical BCPastingInput. finiteBCPastingClosure_nonvacuous fires both directions on named four-cell finite pastes and consumes the existing noninvertibility theorem for one authored leg in each direction.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingClosure.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingClosureWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - BCPastingClosure
    - bcPastingClosure
    - finiteHorizontalBCPastingClosure
    - finiteVerticalBCPastingClosure
    - finiteBCPastingClosure_nonvacuous
  claim_mapping:
    theorem_names:
      - bcPastingClosure
      - finiteBCPastingClosure_nonvacuous
    source_labels:
      - target theorem E horizontal and vertical pullback-square pasting closure
      - fixed finite-code pasting realization compatibility
    conjuncts:
      - the literal nested horizontal or vertical paste is a pullback
      - the generated outer BCPresentation realizes a pullback square
      - the generated outer semantic input equals the canonically northwest-normalized literal paste
      - named horizontal and vertical finite inputs have four source cells and retain a noninvertible authored leg
    undischarged_assumptions:
      - C comparison compatibility with pasting
      - D diagnostic comparison, mapped reselection, coherence, and vanishing compatibility with pasting
      - G-106/G-109 package-to-fiber coherence bridge with explicit transportAlong_comp_coherence proof-use
      - final A-E assembly and completion review
    acceptance_point: the direction-indexed constructor receives only finite-code seed data; both pullback certificates and the normalized realization equality are generated theorem outputs
    port_status: unported
audits:
  premise_delta:
    discharged:
      - E horizontal pullback-square pasting closure
      - E vertical pullback-square pasting closure
      - canonical outer-presentation realization compatibility for both directions
    remaining:
      - C and D pasting compatibility
      - G-106/G-109 coherence bridge
      - final G-110 assembly and independent completion review
  certificate_provenance:
    discharged:
      - nested pullback certificates are generated from the two component pullbacks
      - outer pullback certificate is generated by toSemanticBC_sound on pastePresentation
      - realization equality is generated by the canonical northwest pullback isomorphism
    unresolved: []
  proof_use:
    used:
      - nestedPasteSquare_isPullback
      - toSemanticBC_sound
      - toSemanticBC_pastePresentation_eq
      - finiteConstantPresentation_not_isIso
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - focused BCPastingClosure.lean elaboration: pass; 9 declarations, standard axioms only
    - focused BCPastingClosureWitnesses.lean elaboration: pass; 4 declarations, standard axioms only
    - direct axiom print for the five reporting declarations: propext, Classical.choice, and Quot.sound only
  blocking_findings: []
  next_obligation: construct the package-level G-106 to fiber-functor G-109 compositor bridge with explicit transportAlong_comp_coherence proof-term consumption before comparison and diagnostic pasting compatibility
```

### Cycle 76 — actual-route covariance acceptance and named finite nonvacuity

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 76
goal_blob_sha: 755fb872e4bd87f78441b9043e160cccfd9446d8
goal_sha256: 29eba152e354d9768ca629ef7ad3616f0f78a160ffb82a42b6d1c6c48883e65a
base_oid: 1ab9cca012a5ac069dbd645278331145888faff5
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 comment 5390134042 and the revised-card section of this report
  proof_dag_predecessors:
    - qualifiedDiagnosticBaseChangeD1D3
    - mapEdgeReselection
    - coherentAt_map
    - transportObstructionVanishes_map
    - bcDiagnosticDirectTransportObstructionVanishes
    - bcDiagnosticViaBaseTransportObstructionVanishes
    - singleDiskAbsorbingReselection
    - singleDisk_coherentAt_absorbingReselection
  proof_obligation: close K3 by fixing named direct and via-base d4/d5 specializations and one validated finite source-fiber-qualified input whose initial raw defect and coherent source reselection are both nonidentity and whose mapped target reselections are coherent on both actual routes
  selection_reason: Cycle 75 already supplies reviewed unconditional d4-d6 generic theorems and explicit d6 actual-route specializations; the shortest remaining K3 distance is to expose d4/d5 on those routes and make their nonvacuous simultaneous firing concrete
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticCovariance.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticCovarianceWitnesses.lean
  risks:
    - accepting a square-independent total-category action instead of the two actual BC functors
    - supplying target reselections or coherence certificates as input fields
    - using identity initial defect or identity source reselection
    - proving separate source and target facts on different finite fixtures
    - treating K3 closure as K4 or target-theorem completion
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: bcDiagnosticDirectMapEdgeReselection and bcDiagnosticViaBaseMapEdgeReselection specialize the reviewed canonical d4 construction to the two square-generated core-fiber functors; their path laws and bcDiagnosticDirectCoherentAt_map / bcDiagnosticViaBaseCoherentAt_map specialize d5. The validated finite single-disk input carries the reviewed adjacent swap as a nonidentity initial raw defect. Its generated absorbing right-edge reselection is nonidentity and coherent, and the two actual-route maps generate coherent target reselections and d6 vanishing on that same input.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticCovariance.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticCovarianceWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - bcDiagnosticDirectMapEdgeReselection
    - bcDiagnosticViaBaseMapEdgeReselection
    - bcDiagnosticDirectReselectedEdge_map
    - bcDiagnosticViaBaseReselectedEdge_map
    - bcDiagnosticDirectReselectedPath_map
    - bcDiagnosticViaBaseReselectedPath_map
    - bcDiagnosticDirectCoherentAt_map
    - bcDiagnosticViaBaseCoherentAt_map
    - finiteCovariance_sourceFiber_initialRawDefect_face_ne_one
    - finiteCovarianceSourceReselection_ne_one
    - finiteCovarianceSourceReselection_coherent
    - finiteCovariance_direct_target_coherent
    - finiteCovariance_viaBase_target_coherent
    - finiteCovariance_direct_target_obstruction_vanishes
    - finiteCovariance_viaBase_target_obstruction_vanishes
    - finiteDiagnosticCovariance_nonvacuous
  claim_mapping:
    theorem_names:
      - bcDiagnosticDirectMapEdgeReselection
      - bcDiagnosticViaBaseMapEdgeReselection
      - bcDiagnosticDirectCoherentAt_map
      - bcDiagnosticViaBaseCoherentAt_map
      - finiteDiagnosticCovariance_nonvacuous
    source_labels:
      - target theorem D(d4) canonical actual-route reselection maps and edge/path laws
      - target theorem D(d5) coherence preservation on both actual routes
      - target theorem D(d6) unconditional vanishing preservation on both actual routes
      - target theorem D named finite nonvacuity
    conjuncts:
      - one validated BCPresentation and ordinary BCDiagnosticInterpretation with southwest incidence
      - one named cell whose initial source-fiber raw defect is nonidentity
      - one generated source reselection that is nonidentity and coherent
      - direct and via-base mapped reselections generated by the actual BC functors
      - coherence of both mapped target reselections on the same input
      - obstruction vanishing of both actual-route target data on the same input
    undischarged_assumptions:
      - K4 pullback-square pasting closure and comparison compatibility
      - G-106 / G-109 package-to-fiber coherence bridge with explicit transportAlong_comp_coherence proof-use
      - final (A)-(E) assembly and completion review
    acceptance_point: d4-d6 now have named actual-route specializations and the finite theorem fixes all required nonidentity and coherence facts on one validated input; no target reselection or target coherence certificate is supplied
    port_status: unported
audits:
  premise_delta:
    discharged:
      - D(d4) actual-route canonical mapped reselections and path laws
      - D(d5) direct and via-base coherence preservation
      - D(d6) reviewed unconditional preservation, fired on the named finite input
      - D named finite nonvacuity with nonidentity initial defect and source reselection
    remaining:
      - K4 closure and comparison compatibility
      - final G-110 assembly and independent completion review
  certificate_provenance:
    discharged:
      - both target reselections are mapEdgeReselection outputs of the actual presentation-dependent BC functors
      - both target coherence proofs are coherentAt_map outputs consuming the same source coherent witness
      - the source reselection is singleDiskAbsorbingReselection generated from the authored source datum
    unresolved: []
  proof_use:
    used:
      - qualified source-fiber interpretation from DiagnosticSourceFiberIncidence.toFiberwise
      - mapEdgeReselection and fiberReselectedPath_map
      - coherentAt_map and both d6 actual-route specializations
      - singleDiskAbsorbingReselection and singleDisk_coherentAt_absorbingReselection
      - finiteAxisFoldSwap as the computed initial raw defect
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - focused BCDiagnosticCovariance.lean elaboration: pass; 8 declarations, standard axioms only
    - focused BCDiagnosticCovarianceWitnesses.lean elaboration: pass; 20 declarations, standard axioms only
  blocking_findings: []
  next_obligation: K4 pullback-square pasting closure and comparison compatibility, including the explicit G-106 / G-109 coherence bridge
```

### Cycle 75 — unconditional vanishing preservation and old-target refutation

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 75
goal_blob_sha: 8da7d67addc66c4c17bf74af4cb708a62ab09cfd
goal_sha256: 840b02c6dc19c435cce9aa3f8a9a62c9483f02bfcc90ab4f0b39f983dba3c31e
base_oid: 1b8fcdcfdb8e2d40cf2efb1597f9a10942c71a61
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_obligation: decide the fixed H_bc-conditional D(d4)-D(d6) route by proving how coherent reselections and obstruction vanishing behave under the actual core-fiber transports
  expected_result_type: proof-obligation-discharged or target-refuted
result:
  proposed_result_type: target-refuted
  proof_obligation_delta: transportObstructionVanishes_map proves unconditional forward preservation for every fiberwise core-fiber functor; the direct and via-base specializations cover both actual qualified BC routes; no_bcDiagnosticQualifiedVanishingCounterexample denies the mandatory old-card negative witness on a broader domain before adding H_bc or named-firing restrictions
  completion_candidate: no
  accepted_head: 44ea0e081f3e3cff445905cd04d6fe1f642ca5cf
  merge_commit: 28d7f70d86bf8db835c353a70b61bb4b64ac9c16
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticVanishingPreservation.lean
  evidence:
    - mapEdgeReselection
    - coherentAt_map
    - transportObstructionVanishes_map
    - bcDiagnosticDirectTransportObstructionVanishes
    - bcDiagnosticViaBaseTransportObstructionVanishes
    - no_bcDiagnosticQualifiedVanishingCounterexample
audits:
  route_integrity: pass; both specializations consume the actual direct and via-base core-fiber functors
  proof_use: pass; vanishing is converted to a coherent reselection, mapped by mapEdgeReselection, and closed by coherentAt_map
  axiom_audit: 18 namespace declarations, standard axioms only
  review: Math A, Math B, Lean A, and Lean B all No major findings
  ci: 7/7 pass
stop_condition: target-refuted on the old fixed card; human GOAL revision required
next_obligation: none under the old fixed card
```

### Cycle 74 — qualified actual-route diagnostic base change `(d1)`–`(d3)`

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 74
goal_blob_sha: 8da7d67addc66c4c17bf74af4cb708a62ab09cfd
goal_sha256: 840b02c6dc19c435cce9aa3f8a9a62c9483f02bfcc90ab4f0b39f983dba3c31e
base_oid: 981ddcd9a3dca380dee0a7a760748291cdc18483
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: PR 4114 revised D so that ordinary BCDiagnosticInterpretation plus southwest BCDiagnosticSourceFiberIncidence is the fixed input domain; Issue 4034 names the reviewed Cycle 68 and Cycle 71 artifacts as the first discharge candidate
  proof_dag_predecessors:
    - coreFiberFunctorPackageAutHom
    - coreFiberFunctorPackageAutHom_one
    - DiagnosticSourceFiberIncidence.toFiberwise
    - bcDiagnosticDirectTransportedInterpretationData
    - bcDiagnosticViaBaseTransportedInterpretationData
    - bcDiagnosticTransportedInterpretationComparator_naturality
    - finiteAxisFoldSourceFiberIncidence
  proof_obligation: assemble and prove the complete unconditional D(d1)-D(d3) package on the revised source-fiber-qualified input domain, using only the actual square-generated direct and via-base core-fiber routes
  selection_reason: this applies the human-approved quantifier revision to the existing reviewed DAG and closes the exact prerequisite before H_bc and conditional d4-d6 can be selected
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticQualifiedBaseChange.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticQualifiedBaseChangeWitnesses.lean
  risks:
    - repackaging arbitrary target fields instead of constructing them through the actual BC functors
    - counting source-fiber incidence as a discharged theorem rather than the revised direction-hypothesis input
    - consuming source twoCellBase in the actual-route d3 derivation
    - treating the generated d1-d3 package as H_bc, d4-d6, or K3 completion
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: QualifiedDiagnosticBaseChangeD1D3 fixes the revised universal package over every validated BCPresentation, ordinary interpretation, and southwest source-fiber incidence input. qualifiedDiagnosticBaseChangeD1D3 generates the fiberwise source representation, the direct and via-base endpoint group homomorphisms with identity preservation, both actual-route transported AdmissibleTransportData values, target comparator equations, target edgeStrong and twoCellBase proofs, and the exact-mate comparator comparison. The finite axis-fold interpretation instantiates the package while retaining two distinct authored source comparators.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticQualifiedBaseChange.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticQualifiedBaseChangeWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - QualifiedDiagnosticBaseChangeD1D3
    - qualifiedDiagnosticBaseChangeD1D3
    - finiteAxisFoldQualifiedDiagnosticBaseChangeD1D3
    - finiteAxisFoldQualifiedDiagnosticBaseChangeD1D3_comparators_ne
  claim_mapping:
    theorem_names:
      - qualifiedDiagnosticBaseChangeD1D3
      - finiteAxisFoldQualifiedDiagnosticBaseChangeD1D3
      - finiteAxisFoldQualifiedDiagnosticBaseChangeD1D3_comparators_ne
    source_labels:
      - target theorem D(d1) same-combinatorial interpretation action on source-fiber-qualified input
      - target theorem D(d2) actual direct and via-base endpoint group homomorphisms with identity preservation
      - target theorem D(d3) actual-route generated transported admissible data
    conjuncts:
      - ordinary interpretation plus southwest incidence -> unchanged source packages, edge lifts, and comparators in the actual source core fiber
      - actual direct and via-base core-fiber functors -> endpoint PackageFiberAut group homomorphisms preserving identity
      - actual direct and via-base routes -> generated target AdmissibleTransportData with derived edgeStrong and twoCellBase
      - generated target comparators -> fixed endpoint-action equations
      - exact canonical mate -> pointwise comparison of the two generated comparator tables
      - nonvacuity -> reviewed finite axis-fold input with distinct authored source comparators
    undischarged_assumptions:
      - H_bc definition, qualification theorems, checker, and non-definitional bridge
      - conditional d4 raw-defect preservation, d5 reselection equivariance, and d6 orbit map
      - named source-firing positive-negative vanishing pair
      - K3 completion, K4, and final G-110 assembly
    acceptance_point: the revised qualified domain is universal in presentation, ordinary interpretation, and incidence, and every target field is generated by the actual square-dependent BC routes; d1-d3 are discharged while H_bc and every conditional downstream layer remain open
    port_status: unported
audits:
  premise_delta:
    discharged:
      - D(d1) same-combinatorial source interpretation conversion on the revised incidence-qualified input domain
      - D(d2) endpoint group homomorphisms and identity-cochain preservation for both actual BC routes
      - D(d3) generated direct and via-base transported data, comparator equations, edgeStrong, and twoCellBase
    remaining:
      - H_bc definition and all fixed qualification/checker obligations
      - H_bc-conditional d4-d6 and vanishing preservation proof DAG
      - source-firing positive-negative pair
      - K3 completion, K4, and final assembly
  certificate_provenance:
    discharged:
      - source incidence is exactly the revised direction-hypothesis and supplies only source vertex-base and edge-verticality facts
      - endpoint actions come from coreFiberFunctorPackageAutHom applied to the actual direct and via-base functors
      - target data come from the existing actual-route constructors, and the comparison consumes the exact canonical mate
    unresolved:
      - H_bc condition provenance and checker bridge
      - d4-d6 and vanishing artifacts
  proof_use:
    used:
      - BCDiagnosticSourceFiberIncidence
      - DiagnosticSourceFiberIncidence.toFiberwise and its package/edge/comparator preservation theorems
      - coreFiberFunctorPackageAutHom_one
      - both actual transported-data constructors and all generated comparator/edgeStrong/twoCellBase theorems
      - bcDiagnosticTransportedInterpretationComparator_naturality
      - finiteAxisFoldSourceFiberIncidence and finiteAxisFoldSourceFiberBridge_comparators_ne
    unused:
      - source AdmissibleTransportData.twoCellBase in the actual-route d3 derivation; target twoCellBase is re-derived from incidence and the common target core fiber
      - H_bc and all conditional d4-d6 material, which are outside this unconditional package
  structure_field_escape: none-found; the public producer constructs every conclusion field from reviewed predecessor theorems, while no target package, edge qualification, two-cell equation, comparator, or comparison is an input
  route_integrity: pass; both actions and transported data name bcDiagnosticDirectFunctor and bcDiagnosticViaBaseFunctor, and the comparison names the exact canonical mate route
  target_fitting: none-found; the universal package is assembled from pre-existing reviewed definitions and the finite firing witness predates this cycle
  vacuity: none-found; finiteAxisFoldQualifiedDiagnosticBaseChangeD1D3 inhabits the package and its two source comparators are proved distinct
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found; the package matches the revised card exactly and does not claim full-domain action, H_bc, d4-d6, or K3 completion
  validation_refs:
    - focused BCDiagnosticQualifiedBaseChange.lean: pass; 18 namespace declarations, standard axioms only
    - targeted BCDiagnosticQualifiedBaseChangeWitnesses module: pass; 4062 jobs; core 18 and witness 3 namespace declarations, standard axioms only
  blocking_findings: []
  next_obligation: define H_bc in the fixed BCConditionSyntax vocabulary and prove its qualification/checker bridge before selecting conditional d4
review:
  status: pending standard fixed-head review
stop_condition_candidate: none
next_obligation: after merge, select H_bc definition and qualification/checker bridge as the next K3 prerequisite
```

### Cycle 72 — realized-schema no-go for universal source-fiber incidence

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 72
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: b349b6ed52abc1a2f1cf1f928e18bc06db5e1d77
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Cycle 71 proved that source-fiber incidence is sufficient for the actual direct/via-base route but left its arbitrary-input provenance open
  proof_dag_predecessors:
    - BCPresentation
    - BCDiagnosticInterpretation
    - finiteTransportTriangleData
    - finiteTransportTriangle_not_sourceFiberIncident
  proof_obligation: decide whether the fixed realized BC schema itself generates DiagnosticSourceFiberIncidence for every ordinary BCDiagnosticInterpretation
  selection_reason: this is the first branch of Cycle 71's exact next obligation; a finite realized-schema counterexample decides it before any different total-category extension is attempted
  expected_result_type: blocker-fixed
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticSourceFiberNoGoWitnesses.lean
  risks:
    - proving only a generic G-106 counterexample rather than one inside a validated BCPresentation
    - overstating failure of universal incidence as failure of every conceivable full-domain total action
    - treating the blocker checkpoint as G-110 refutation or completion
  unchecked: []
result:
  proposed_result_type: blocker-fixed
  proof_obligation_delta: finiteTransportTriangleDiagnosticPresentation enumerates the existing nonidentity transport triangle as valid diagnostic code. finiteTransportTriangleBCPresentation combines it with the reviewed constant cospan and compatible-point table, and finiteTransportTriangleBCInterpretation supplies the existing admissible triangle datum on the decoded geometry. finiteTransportTriangleBC_not_sourceFiberIncident proves that this realized ordinary interpretation cannot enter the actual southwest core-fiber route. no_universalBCDiagnosticSourceFiberIncidence therefore refutes a universal incidence generator for the current ordinary interpretation schema. This does not refute a genuinely different square-generated total-category action.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticSourceFiberNoGoWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - finiteTransportTriangleDiagnosticPresentation
    - finiteTransportTriangleBCRawCode_wellFormed
    - finiteTransportTriangleBCPresentation
    - finiteTransportTriangleBCInterpretation
    - finiteTransportTriangleBC_not_sourceFiberIncident
    - no_universalBCDiagnosticSourceFiberIncidence
  claim_mapping:
    theorem_names:
      - finiteTransportTriangleBC_not_sourceFiberIncident
      - no_universalBCDiagnosticSourceFiberIncidence
    source_labels:
      - target theorem D(d1)-D(d3) current ordinary-interpretation incidence-generation branch
    conjuncts:
      - realized finite BC input -> validated BCPresentation
      - ordinary package interpretation -> BCDiagnosticInterpretation
      - actual-route domain mismatch -> no southwest DiagnosticSourceFiberIncidence
      - universal generation no-go -> no incidence output for every current-schema interpretation
    undischarged_assumptions:
      - existence or impossibility of a different square-generated full-domain DiagnosticPackageTotalAction
      - full d1-d3
      - H_bc and conditional d4-d6
      - named actual-firing positive-negative vanishing pair and checker bridge
    acceptance_point: the incidence-generation branch is formally blocked on a validated realized input; no claim is made that every total-category extension is impossible, and D(d1)-D(d3), K3, and G-110 remain incomplete
    port_status: unported
audits:
  premise_delta:
    discharged:
      - the Cycle 71 generic negative datum is embedded in a validated realized BC presentation
      - universal source-fiber incidence generation from the current BCDiagnosticInterpretation schema is refuted
    remaining:
      - construct an actual square-generated full-domain action not mediated by source-fiber incidence, or fix a formal no-go for that route
      - define qualified H_bc and consume it only after d1-d3
      - construct the source-firing positive-negative vanishing pair
  certificate_provenance:
    discharged:
      - cospan and compatible-point validation reuse the reviewed finite constant presentation
      - diagnostic nonincidence is derived from the existing nonidentity Atom transport theorem
    unresolved:
      - full-domain square action provenance
  proof_use:
    used:
      - finiteConstantCompatiblePointCode_wellFormed
      - finiteTransportTriangleData
      - finiteTransportTriangle_not_sourceFiberIncident
      - BCDiagnosticSourceFiberIncidence
    unused: []
  structure_field_escape: none-found; the raw BC input contains only the existing cospan, compatible point table, and finite diagnostic code, while nonincidence is a theorem
  route_integrity: the negative theorem targets the exact actual southwest source-fiber abbreviation and does not relabel the Cycle 70 identity action as square-generated
  target_fitting: none-found; the nonidentity transport triangle predates this cycle and is inserted unchanged into the validated BC schema
  vacuity: the realized presentation, ordinary interpretation, three edge generators, and nonidentity edge transport are concrete and inhabited
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found; the result blocks only universal incidence generation and leaves the distinct total-action branch open
  validation_refs:
    - focused BCDiagnosticSourceFiberNoGoWitnesses.lean: pass; 8 namespace declarations, standard axioms only
    - targeted module build: pass; 4061 jobs
    - common diff, placeholder, hidden/BiDi Unicode, privacy, import-direction, and umbrella-wiring scans: pass
  blocking_findings: []
  next_obligation: after merge, construct an actual square-generated full-domain total action not mediated by universal source-fiber incidence, or prove an exact no-go for that distinct route
review:
  status: pending standard fixed-head review
stop_condition_candidate: none; this is the first formally blocked branch and a distinct implementation route remains
next_obligation: after merge, attempt the distinct square-generated total-category action route for full-domain d1-d3
```

### Cycle 71 — ordinary G-106 source-fiber incidence bridge to the actual BC routes

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 71
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: b5af8340bb37914331ceccdc33a877ff2de7612c
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Cycle 69 constructed the actual direct and via-base target data from a parallel fiberwise source representation, while Cycle 70 accepted an arbitrary global total-category action rather than generating the actual square action
  proof_dag_predecessors:
    - BCDiagnosticInterpretation
    - AdmissibleTransportData
    - FiberwiseAdmissibleTransportData
    - bcDiagnosticDirectFunctor
    - bcDiagnosticViaBaseFunctor
    - bcDiagnosticTransportedComparator_naturality
  proof_obligation: connect an ordinary accepted G-106 interpretation to the actual BC direct and via-base routes by deriving the fiberwise source representation from source incidence, without accepting any target package, edge qualification, two-cell equation, or comparator
  selection_reason: the actual BC functors are defined on the southwest core fiber, so source incidence is the smallest input-side qualification that makes the existing ordinary interpretation their mathematical domain; strongly cocartesian source edges over identity then become fiber isomorphisms by theorem
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticSourceFiberBridge.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticSourceFiberBridgeWitnesses.lean
  risks:
    - treating source incidence as a target certificate or an H_bc conclusion
    - supplying edge invertibility instead of deriving it from source edgeStrong and verticality
    - replacing the ordinary G-106 source packages, edge lifts, or comparators during conversion
    - claiming the source-fiber qualified construction covers arbitrary-base diagnostic edges
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: Conditional on DiagnosticSourceFiberIncidence, which is not generated from an arbitrary BCDiagnosticInterpretation, fiberEdgeIso derives total and fiber invertibility from source edgeStrong plus identity-base verticality. toFiberwise preserves each source package, edge lift, and comparator pointwise. The two actual BC functors then generate direct and via-base target AdmissibleTransportData, with named theorems deriving target edgeStrong and twoCellBase and fixing both comparator generation equations. The exact BC mate identifies the two generated target comparator tables pointwise. The finite ordinary double-diamond interpretation supplies a positive qualified instance with genuinely distinct authored comparators, while the finite nonidentity transport triangle proves that the qualification does not hold for all ordinary G-106 data.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticSourceFiberBridge.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticSourceFiberBridgeWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - DiagnosticSourceFiberIncidence.fiberEdgeIso
    - DiagnosticSourceFiberIncidence.toFiberwise
    - DiagnosticSourceFiberIncidence.toFiberwise_package
    - DiagnosticSourceFiberIncidence.toFiberwise_edgeLift
    - DiagnosticSourceFiberIncidence.toFiberwise_comparator
    - bcDiagnosticDirectTransportedInterpretationData
    - bcDiagnosticViaBaseTransportedInterpretationData
    - bcDiagnosticDirectTransportedInterpretationData_comparator
    - bcDiagnosticViaBaseTransportedInterpretationData_comparator
    - bcDiagnosticDirectTransportedInterpretationData_edgeStrong
    - bcDiagnosticViaBaseTransportedInterpretationData_edgeStrong
    - bcDiagnosticDirectTransportedInterpretationData_twoCellBase
    - bcDiagnosticViaBaseTransportedInterpretationData_twoCellBase
    - bcDiagnosticTransportedInterpretationComparator_naturality
    - finiteAxisFoldSourceFiberIncidence
    - finiteAxisFoldSourceFiberBridge_comparators_ne
    - finiteAxisFoldBridgeTransportedComparator_naturality
    - finiteTransportTriangle_not_sourceFiberIncident
  claim_mapping:
    theorem_names:
      - bcDiagnosticDirectTransportedInterpretationData_comparator
      - bcDiagnosticViaBaseTransportedInterpretationData_comparator
      - bcDiagnosticDirectTransportedInterpretationData_edgeStrong
      - bcDiagnosticViaBaseTransportedInterpretationData_edgeStrong
      - bcDiagnosticDirectTransportedInterpretationData_twoCellBase
      - bcDiagnosticViaBaseTransportedInterpretationData_twoCellBase
      - bcDiagnosticTransportedInterpretationComparator_naturality
    source_labels:
      - target theorem D(d1) same-combinatorial interpretation action on the source-fiber qualified ordinary G-106 domain
      - target theorem D(d2) actual direct and via-base endpoint group homomorphisms from Cycle 68
      - target theorem D(d3) actual-route generated transported admissible data on that domain
    conjuncts:
      - ordinary G-106 source interpretation -> source-incidence-generated fiberwise representation
      - unchanged combinatorial layer -> both target constructors retain the decoded diagnostic presentation
      - derived source edge invertibility -> source edgeStrong plus source identity-base verticality
      - derived target edgeStrong -> mapped fiber isomorphism
      - derived target twoCellBase -> common target core fiber
      - generated target comparators -> actual direct and via-base endpoint group homomorphisms
      - actual route comparison -> exact canonical BC mate naturality
      - nonvacuity -> pre-existing ordinary double-diamond interpretation with distinct authored comparators
    undischarged_assumptions:
      - DiagnosticSourceFiberIncidence is caller-supplied and is not generated from an arbitrary ordinary BCDiagnosticInterpretation
      - full-domain d1 and d3 remain open outside the selected southwest identity-base source fiber
      - arbitrary-base source diagnostic edges are handled only by the generic Cycle 70 engine, not by the actual square core-fiber routes
      - H_bc and conditional d4-d6
      - named actual-firing positive-negative vanishing pair and checker bridge
    acceptance_point: this is a conditional support theorem: ordinary accepted G-106 data equipped with actual southwest source-fiber incidence feeds the actual direct and via-base BC routes without target-field supply; generation of that incidence, full-domain d1 and d3, H_bc, d4-d6, K3 completion, and G-110 completion are not claimed
    port_status: unported
audits:
  premise_delta:
    discharged:
      - given source incidence, the Cycle 69 parallel fiberwise representation is generated internally from the ordinary BCDiagnosticInterpretation
      - source fiber-edge invertibility is derived rather than supplied
      - actual direct and via-base target edgeStrong, twoCellBase, and comparator generation are exposed as named theorems
      - the actual mate comparison is stated directly for ordinary interpretation input
    remaining:
      - generate or otherwise discharge DiagnosticSourceFiberIncidence from the fixed semantic schema, or construct a full-domain actual-route action
      - determine the required treatment of arbitrary-base source diagnostic edges from the fixed semantic schema
      - define qualified H_bc and consume it only in d4-d6
      - construct the source-firing positive-negative vanishing pair
  certificate_provenance:
    discharged:
      - vertex and edge incidence refer only to already selected source packages and edge lifts
      - fiberEdgeIso consumes source edgeStrong and IsHomLift over identity
      - target fields are generated exclusively through the actual core-fiber functors
      - comparator comparison consumes the exact canonical BC mate
    unresolved:
      - DiagnosticSourceFiberIncidence provenance for arbitrary ordinary BCDiagnosticInterpretation inputs
  proof_use:
    used:
      - BCDiagnosticInterpretation.data
      - source AdmissibleTransportData.edgeStrong
      - source incidence edgeVertical
      - Functor.IsStronglyCocartesian.isIso_of_base_isIso
      - bcDiagnosticDirectFunctor and bcDiagnosticViaBaseFunctor
      - bcDiagnosticTransportedComparator_naturality
      - finiteAxisFold_comparators_ne
    unused:
      - source AdmissibleTransportData.twoCellBase in this qualified conversion route; the target twoCellBase equations are re-derived from the common target fiber, while the Cycle 70 generic engine consumes the source field
  structure_field_escape: none-found for target data; DiagnosticSourceFiberIncidence contains only source vertex-base and source edge-verticality facts, while edge invertibility and every target G-106 field are theorems or generated definitions
  route_integrity: the target constructors use the existing actual direct and via-base core-fiber functors and exact canonical mate; no generic action is relabeled as square-generated
  target_fitting: none-found; the finiteAxisFold interpretation and distinct-comparator theorem predate this cycle
  vacuity: finiteAxisFoldSourceFiberIncidence is a positive instance with two genuinely distinct authored source comparators; finiteTransportTriangle_not_sourceFiberIncident is a named negative instance showing that the qualification excludes ordinary data with nonidentity base transport
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found; the qualified southwest-source-fiber domain is named explicitly and arbitrary-base coverage remains open
  validation_refs:
    - focused BCDiagnosticSourceFiberBridge.lean: pass; 23 namespace declarations, standard axioms only
    - focused BCDiagnosticSourceFiberBridgeWitnesses.lean: pass; 10 namespace declarations, standard axioms only
    - targeted bridge and witness module build: pass; 4060 jobs
    - common diff, placeholder, hidden/BiDi Unicode, privacy, import-direction, and umbrella-wiring scans: pass
  blocking_findings: []
  next_obligation: after merge, construct the full-domain actual diagnostic action or generate and discharge DiagnosticSourceFiberIncidence from the fixed semantic schema before selecting d4
review:
  status: pending standard fixed-head review
stop_condition_candidate: none
next_obligation: after merge, return to full-domain d1 and d3 by constructing the actual diagnostic action or generating source-fiber incidence from the fixed semantic BC schema
```

### Cycle 70 — arbitrary-source total diagnostic transport engine

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 70
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: f64c490f527c7566e637a2a566c596ff7e0da763
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Cycle 69 generated target data only for identity-base fiberwise source edges
  proof_dag_predecessors:
    - AdmissibleTransportData
    - PackageTotalHom.packageTotalCategory
    - DiagnosticPackageTotalAction
    - DiagnosticPackageTotalAction.mapPackageFiberAut
  proof_obligation: remove the fiberwise source restriction by constructing the generic arbitrary-source d1/d3 engine from a total-category action, deriving all target G-106 fields and fixing comparator generation; leave construction of the square-generated action itself explicit
  selection_reason: arbitrary nonidentity source edges require an action on the package total category rather than only a functor between two core fibers
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticTotalTransport.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticTotalTransportWitnesses.lean
  risks:
    - accepting target edge qualifications or two-cell equations as action fields
    - allowing the mapped comparator to leave the target fiber
    - confusing the generic total-action engine with construction of the actual BC action
    - witnessing only identity-base edges
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: DiagnosticPackageTotalAction packages a functor on the package total category with two structural laws, preservation of strongly cocartesian morphisms and congruence of image base morphisms under source-base equality. For every arbitrary AdmissibleTransportData input, transportedData maps packages and edge lifts functorially, derives target edgeStrong from the first law, derives target twoCellBase from source path equality and the second law, and generates each target comparator by mapping its source automorphism and proving the image remains vertical. The finite transport triangle shows the engine consumes genuine nonidentity source transports and preserves their nontrivial Atom equivalence under the inhabited identity action.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticTotalTransport.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticTotalTransportWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - DiagnosticPackageTotalAction.mapPackageFiberAut
    - DiagnosticPackageTotalAction.mapPackageFiberAut_one
    - DiagnosticPackageTotalAction.mapPackageFiberAut_mul
    - DiagnosticPackageTotalAction.transportedEdgeLift_isStronglyCocartesian
    - DiagnosticPackageTotalAction.transportedPathLift_eq_map
    - DiagnosticPackageTotalAction.transportedTwoCellBase
    - DiagnosticPackageTotalAction.transportedData
    - DiagnosticPackageTotalAction.transportedData_comparator
    - finiteTransportTriangleIdentityTransported_edge_atomEquiv_ne_refl
  claim_mapping:
    theorem_names:
      - DiagnosticPackageTotalAction.transportedData_comparator
      - DiagnosticPackageTotalAction.transportedData_edgeStrong
      - DiagnosticPackageTotalAction.transportedData_twoCellBase
      - finiteTransportTriangleIdentityTransported_edge_atomEquiv_ne_refl
    source_labels:
      - target theorem D(d1) same-combinatorial interpretation action, generic total-action engine
      - target theorem D(d3) generated transported datum, generic total-action engine
    conjuncts:
      - arbitrary source packages and edges -> transportedPackage and transportedEdgeLift
      - unchanged combinatorial layer -> transportedLiftData and transportedData retain G
      - derived target edgeStrong -> transportedData_edgeStrong
      - derived target twoCellBase -> transportedData_twoCellBase
      - generated vertical comparator -> mapPackageFiberAut and transportedData_comparator
      - identity and multiplication preservation -> mapPackageFiberAut_one and mapPackageFiberAut_mul
      - nonidentity-edge nonvacuity -> finiteTransportTriangleIdentityTransported_edge_atomEquiv_ne_refl
    undischarged_assumptions:
      - construct DiagnosticPackageTotalAction from the accepted semantic BC square and A-C rather than supplying an arbitrary action
      - identify its core-fiber restrictions with the Cycle 68 direct/via endpoint group homomorphisms
      - H_bc and conditional d4-d6
      - named actual-firing positive-negative vanishing pair and checker bridge
    acceptance_point: the arbitrary-source target-data engine exists and accepts no target diagnostic fields; the actual square-generated total action, full d1/d3 discharge, H_bc, d4-d6, K3 completion, and G-110 completion are not claimed
    port_status: unported
audits:
  premise_delta:
    discharged:
      - arbitrary source edge lifts no longer need identity base morphisms
      - target edgeStrong is derived uniformly from the structural action law
      - target twoCellBase is derived uniformly from source equality and base congruence
      - mapped comparator verticality is derived from source verticality and identity functoriality
      - the engine handles a concrete nonidentity Atom transport
    remaining:
      - generate the actual total action from the semantic BC square and prove its two structural laws
      - connect the actual total action to the canonical mate comparison
      - define qualified H_bc and consume it only in d4-d6
      - construct the source-firing positive-negative vanishing pair
  certificate_provenance:
    discharged:
      - action maps source total morphisms functorially
      - target edge qualification consumes source edgeStrong through map_stronglyCocartesian
      - target base equality consumes source twoCellBase through map_base_eq_of_base_eq
      - comparator fiber membership is proved by comparing the source automorphism base with identity and using Functor.map_id
    unresolved: []
  proof_use:
    used:
      - source AdmissibleTransportData.edgeStrong
      - source AdmissibleTransportData.twoCellBase
      - source PackageFiberAut.hom_base_eq
      - Functor.map_id and Functor.map_comp
      - finiteTransportTriangle_edge_atomEquiv_ne_refl
    unused: []
  structure_field_escape: none-found for target data; the action stores only global functorial preservation laws and no target diagnostic package, lift, field, comparison, or vanishing certificate
  route_integrity: the generic engine is not labeled as the actual BC route; construction and identification of the square-generated action remain explicit obligations
  target_fitting: none-found; finiteTransportTriangleData and its nonidentity-edge theorem predate this cycle
  vacuity: the witness contains genuine nonidentity base transport and three nontrivial authored comparator coordinates
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found; the action-construction gap is not counted as d1/d3 discharge
  validation_refs:
    - focused BCDiagnosticTotalTransport.lean: pass; 29 namespace declarations, standard axioms only
    - focused BCDiagnosticTotalTransportWitnesses.lean: pass; 5 namespace declarations, standard axioms only
    - targeted total transport module build: pass; 4044 jobs
    - targeted total transport witness module build: pass; 4050 jobs
    - common scans: pass
  blocking_findings: []
  next_obligation: after merge, generate the actual DiagnosticPackageTotalAction from the accepted semantic BC square and prove its structural laws from A-C rather than accepting them
review:
  status: pending standard fixed-head review
stop_condition_candidate: none
next_obligation: after merge, construct and identify the square-generated total action with the existing direct/via core-fiber routes
```

### Cycle 69 — fiberwise same-combinatorial transported datum engine

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 69
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: ee33b5403207c47015ae3d9fea8b66970dd1db38
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Cycle 68 generated the d2 endpoint group homomorphism and canonical direct-via comparison but left d1 and d3 open
  proof_dag_predecessors:
    - FiberwiseAdmissibleTransportData
    - coreFiberFunctorPackageAutHom
    - bcDiagnosticDirectFunctor
    - bcDiagnosticViaBaseFunctor
    - bcDiagnosticEndpointComparison_naturality
  proof_obligation: construct a same-combinatorial transported-datum engine on the fiberwise identity-base subdomain, deriving target edgeStrong and twoCellBase and fixing the target comparator by the d2 generation equation; then specialize it to the actual direct and via-base BC routes
  selection_reason: the repository had no target-data constructor beneath d3; the fiberwise subdomain is the smallest nonempty layer where every post-base-change G-106 field can be generated without accepting target certificates
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticFiberwiseTransport.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticFiberwiseTransportWitnesses.lean
  risks:
    - treating source fiber isomorphisms as a discharge of arbitrary G-106 edge transport
    - supplying target edgeStrong or twoCellBase rather than deriving them
    - copying the source comparator instead of applying the generated endpoint homomorphism
    - promoting pointwise direct-via comparator naturality to raw-defect or orbit preservation
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: FiberwiseAdmissibleTransportData represents a diagnostic interpretation internal to one core fiber by vertex objects, edge isomorphisms, and the source authored comparator only. Its conversion to AdmissibleTransportData derives strong cocartesianness from mapped isomorphisms and derives every parallel-path base equation from the common fiber. Mapping through any core-fiber functor leaves the combinatorial presentation fixed and generates the target comparator by coreFiberFunctorPackageAutHom. The actual direct and via-base BC functors now generate transported G-106 data, and the canonical mate-generated endpoint comparison identifies their comparator tables pointwise. The finite double-diamond fixture instantiates both actual routes with distinct identity/swap source comparators.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticFiberwiseTransport.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticFiberwiseTransportWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - FiberwiseAdmissibleTransportData.edgeLift_isStronglyCocartesian
    - FiberwiseAdmissibleTransportData.pathLift_eq_pathIso_hom
    - FiberwiseAdmissibleTransportData.twoCellBase
    - FiberwiseAdmissibleTransportData.transported
    - FiberwiseAdmissibleTransportData.transported_comparator
    - FiberwiseAdmissibleTransportData.transported_edgeStrong
    - FiberwiseAdmissibleTransportData.transported_twoCellBase
    - bcDiagnosticDirectTransportedData
    - bcDiagnosticViaBaseTransportedData
    - bcDiagnosticTransportedComparator_naturality
    - finiteAxisFoldTransportedComparator_naturality
  claim_mapping:
    theorem_names:
      - FiberwiseAdmissibleTransportData.transported_comparator
      - FiberwiseAdmissibleTransportData.transported_edgeStrong
      - FiberwiseAdmissibleTransportData.transported_twoCellBase
      - bcDiagnosticTransportedComparator_naturality
    source_labels:
      - target theorem D(d1) same-combinatorial interpretation action, fiberwise subdomain only
      - target theorem D(d3) generated transported datum, fiberwise subdomain only
      - target theorem D diagnostic comparison generated from A-C
    conjuncts:
      - unchanged vertex/edge/two-cell types -> FiberwiseAdmissibleTransportData.map
      - generated target packages and edge lifts -> FiberwiseAdmissibleTransportData.map and toLiftData
      - derived edgeStrong -> transported_edgeStrong
      - derived twoCellBase -> transported_twoCellBase
      - generated comparator equation -> transported_comparator
      - actual direct/via route constructors -> bcDiagnosticDirectTransportedData and bcDiagnosticViaBaseTransportedData
      - canonical comparison of target tables -> bcDiagnosticTransportedComparator_naturality
      - nonempty finite source and actual-route target data -> finiteAxisFoldFiberwiseTransportData and finiteAxisFoldDirectTransportedData
    undischarged_assumptions:
      - bridge from the full accepted G-106 AdmissibleTransportData input domain to the fiberwise representation or a more general total interpretation action
      - full d1 and d3 outside identity-base fiberwise edges
      - H_bc and conditional d4-d6
      - named actual-firing positive-negative vanishing pair and checker bridge
    acceptance_point: the missing target-data constructor exists and consumes no post-base-change fields on a nonempty fiberwise subdomain; full d1/d3, raw-defect preservation, orbit mapping, vanishing preservation, H_bc, K3 completion, and G-110 completion are not claimed
    port_status: unported
audits:
  premise_delta:
    discharged:
      - target edgeStrong is derived from the mapped edge isomorphism
      - target twoCellBase is derived from composed fiber isomorphisms over one fixed base
      - target comparator is generated pointwise by the d2 endpoint homomorphism
      - direct and via-base transported comparator tables are related by the canonical mate
    remaining:
      - generate the full-domain interpretation action from the accepted square and source G-106 data
      - define qualified H_bc and consume it only in d4-d6
      - derive raw-defect, reselection-equivariance, orbit, and vanishing preservation through the mandated proof DAG
      - construct the source-firing positive-negative pair and checker bridge
  certificate_provenance:
    discharged:
      - source edge isomorphisms generate target edge lifts through Functor.mapIso
      - strong cocartesianness follows from total IsIso and the canonical IsHomLift instance
      - base equations follow from the fiber morphism lift equations and path composition
      - comparator generation uses coreFiberFunctorPackageAutHom rather than a target table input
    unresolved: []
  proof_use:
    used:
      - fiberInclusion preservation of edge isomorphisms
      - IsStronglyCocartesian.of_isIso
      - Functor.mapIso and path composition
      - Cycle 68 endpoint group homomorphism
      - Cycle 68 canonical mate naturality
      - finiteAxisFold_comparators_ne
    unused: []
  structure_field_escape: none-found for the target datum; FiberwiseAdmissibleTransportData contains only source packages, source edge isomorphisms, and the source authored comparator
  route_integrity: actual target data uses bcDiagnosticDirectFunctor and bcDiagnosticViaBaseFunctor, and comparison uses bcDiagnosticEndpointComparison rather than a supplied isomorphism
  target_fitting: none-found; the finite double-diamond fixture and identity/swap table predate this cycle
  vacuity: the finite source has nonempty vertices, edges, and two-cells, and its two comparator values are distinct
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found; the fiberwise restriction is recorded as an explicit remaining full-domain obligation
  validation_refs:
    - focused BCDiagnosticFiberwiseTransport.lean: pass; 34 namespace declarations, standard axioms only
    - focused BCDiagnosticFiberwiseTransportWitnesses.lean: pass; 11 namespace declarations, standard axioms only
    - targeted fiberwise transport module build: pass; 4043 jobs
    - targeted fiberwise transport witness module build: pass; 4059 jobs
    - common scans: pass
  blocking_findings: []
  next_obligation: after merge, construct the full-domain bridge from accepted G-106 data and the semantic BC square to a same-combinatorial action, without accepting target lifts or qualifications
review:
  status: pending standard fixed-head review
stop_condition_candidate: none
next_obligation: after merge, remove the fiberwise restriction by generating the total interpretation action needed for arbitrary admissible source edges
```

### Cycle 68 — generated endpoint automorphism action for diagnostic base change

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 68
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: c2cae2d735acdbc3be479bd4cc9561e1c61458c8
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Cycle 67 discharged the selected K2 public comparison and left every K3 diagnostic base-change layer open
  proof_dag_predecessors:
    - PackageFiberAut
    - coreFiberTransportFunctor
    - selectedCoreFiberReindexFunctor
    - coreBeckChevalleyMate
    - coreBeckChevalleyMate_isIso
  proof_obligation: construct the unconditional d2 endpoint PackageFiberAut group homomorphism, its pointwise cochain action and identity preservation, and the generated direct-versus-via-base endpoint comparison without accepting a diagnostic comparison map
  selection_reason: d2 is the smallest independently checkable K3 layer; it is generated functorially from G-101 core fibers and the accepted exact BC mate and does not require premature H_bc assumptions
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticBaseChangeAutomorphism.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticBaseChangeAutomorphismWitnesses.lean
  risks:
    - storing an endpoint comparison rather than generating it from the canonical mate
    - forgetting the identity cochain law
    - treating this endpoint/cochain action as transported admissible data or raw-defect preservation
    - using a constant finite action as nonvacuity evidence
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: packageFiberAutCoreFiberEquiv identifies each G-106 PackageFiberAut with the categorical automorphism group of its core-fiber object. Every generated core-fiber functor therefore induces coreFiberFunctorPackageAutHom, a group homomorphism preserving identity and multiplication. Applied vertexwise, it generates the endpoint package family and pointwise defect-cochain map on the unchanged finite combinatorial presentation, with identity-cochain and multiplication laws. The two exact BC routes are generated from the finite presentation; coreBeckChevalleyMate_isIso supplies their endpoint package isomorphism, and mate naturality proves that conjugating the direct image through this generated comparison equals the via-base image. On the finite lax support, the identity core-fiber action sends the adjacent swap to itself and differs from its identity image.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticBaseChangeAutomorphism.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticBaseChangeAutomorphismWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - packageFiberAutCoreFiberEquiv
    - coreFiberFunctorPackageAutHom
    - coreFiberFunctorPackageAutHom_one
    - coreFiberFunctorPackageAutHom_mul
    - bcDiagnosticDirectFunctor
    - bcDiagnosticViaBaseFunctor
    - bcDiagnosticComparisonIso
    - bcDiagnosticEndpointComparison
    - bcDiagnosticEndpointComparison_naturality
    - coreFiberFunctorDefectCochainMap
    - coreFiberFunctorDefectCochainMap_identity
    - coreFiberFunctorDefectCochainMap_mul
    - finiteAxisFold_identityEndpointAction_nonconstant
  claim_mapping:
    theorem_names:
      - coreFiberFunctorDefectCochainMap_identity
      - bcDiagnosticEndpointComparison_naturality
      - finiteAxisFold_identityEndpointAction_nonconstant
    source_labels:
      - target theorem D(d2) endpoint PackageFiberAut group homomorphism
      - target theorem D diagnostic comparison map generated from A-C
    conjuncts:
      - endpoint group hom -> coreFiberFunctorPackageAutHom
      - identity preservation -> coreFiberFunctorPackageAutHom_one and coreFiberFunctorDefectCochainMap_identity
      - cochain map on fixed combinatorial cells -> coreFiberFunctorDefectCochainMap
      - generated direct-via comparison -> bcDiagnosticComparisonIso and bcDiagnosticEndpointComparison
      - comparison naturality -> bcDiagnosticEndpointComparison_naturality
      - nonconstant finite action -> finiteAxisFold_identityEndpointAction_nonconstant
    undischarged_assumptions:
      - d1 same-combinatorial-layer interpretation pullback
      - d3 transported AdmissibleTransportData with generated comparator and derived edgeStrong/twoCellBase
      - H_bc and conditional d4-d6
      - named actual-firing positive-negative vanishing pair and checker bridge
    acceptance_point: the endpoint group-hom/cochain-map layer and the canonical direct-via endpoint comparison are generated and proved functorial; no transported datum, raw-defect preservation, orbit mapping, vanishing preservation, H_bc, or K3 completion is claimed
    port_status: unported
audits:
  premise_delta:
    discharged:
      - endpoint automorphism maps are generated by core-fiber functors
      - direct-via endpoint comparison is generated by the exact canonical mate
      - identity cochain and pointwise multiplication are preserved
      - the concrete finite identity action is nonconstant
    remaining:
      - construct d1 and d3 without supplied post-base-change certificates
      - define qualified H_bc and consume it only in d4-d6
      - derive vanishing preservation through the complete mandated proof DAG
      - construct the source-firing positive-negative pair and checker bridge
  certificate_provenance:
    discharged:
      - PackageFiberAut-to-fiber-Aut conversion uses the existing fiber membership equation
      - endpoint maps are Functor.mapAut transported back through a proved group equivalence
      - the comparison is asIso of the producer-generated canonical mate using its proved IsIso theorem
    unresolved: []
  proof_use:
    used:
      - PackageFiberAut hom/inv and identity-base equations
      - functor mapAut multiplication and identity laws
      - coreBeckChevalleyMate_isIso
      - coreBeckChevalleyMate naturality on every source automorphism
      - finiteAxisFoldSwap_ne_one
    unused: []
  structure_field_escape: none-found; no new input structure or certificate is introduced
  route_integrity: direct and via-base functors are the exact routes appearing in coreBeckChevalleyMate, and endpoint comparison is generated by that mate rather than supplied
  target_fitting: none-found
  vacuity: the generic maps quantify over every endpoint automorphism; the finite adjacent swap is mapped to itself and remains distinct from the identity image
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - focused BCDiagnosticBaseChangeAutomorphism.lean: pass; 16 namespace declarations, standard axioms only
    - focused BCDiagnosticBaseChangeAutomorphismWitnesses.lean: pass; 4 namespace declarations, standard axioms only
    - targeted base-change automorphism module build: pass; 4042 jobs
    - targeted base-change automorphism witness module build: pass; 4060 jobs
    - common scans: pass
  blocking_findings: []
  next_obligation: after merge, construct d1 and d3 together so target packages, edge lifts, edgeStrong, twoCellBase, and comparator generation arise from the same fixed-combinatorial interpretation pullback
review:
  status: pending standard fixed-head review
stop_condition_candidate: none
next_obligation: after merge, build the same-combinatorial-layer transported admissible datum and expose its generated comparator equation before introducing H_bc
```

### Cycle 67 — generated non-twist comparison on the genuine reselection orbit

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 67
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 797617bc7531fc78e7c8aa24adc7e81f7a6cf867
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Cycle 66 accepted the package-selected canonical normalization and left the diagnostic selector, public producer/relation, genuine orbit bridge, and replacement compatibility open
  proof_dag_predecessors:
    - canonicalObjectNormalizationTotal
    - canonicalTwoCellComparator
    - rawDefectCochain
    - reselectLiftData
    - authoredSupportCanonicalMate
  proof_obligation: generate the two-route authored comparison from the G-106 raw diagnostic without a supplied collapse morphism, define one all-input public relation, prove its strict positive and lax full-orbit negative instances, and preserve it under presentation replacement
  selection_reason: the missing route is now constructible from the accepted package normalization and the existing G-106 edge-reselection action; no API absence is a stop condition
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredDiagnosticObjectCollapseProducer.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredDiagnosticObjectCollapseProducerWitnesses.lean
  risks:
    - choosing an arbitrary noninvertible endomorphism instead of the package-selected map
    - replacing the real edge-reselection action by an invented authored-table action
    - proving a cochain-indexed auxiliary predicate but not the fixed public MateCoherentRel
    - claiming general admissibility where the selector has an explicit fallback branch
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: authoredDiagnosticObjectCollapseComponentAtCochain selects identity on a vanishing component, the package-selected canonical normalization when the component fires and its reading laws are admissible, and identity otherwise. Transport through the exact via-base route produces an all-input AuthoredComparisonProducerSignature and the fixed public MateCoherentRel. The strict fixture satisfies that relation. For the lax fixture every support discharges admissibility, every firing selected factor is the reviewed finite noninvertible normalization, and every genuine G-106 edge reselection yields a reselected datum whose initial raw defect is the corresponding orbit cochain and which fails the same fixed public relation. Presentation replacement preserves the producer equation and public relation.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredDiagnosticObjectCollapseProducer.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredDiagnosticObjectCollapseProducerWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - authoredDiagnosticObjectCollapseComponentAtCochain
    - authoredDiagnosticObjectCollapseComponentAtCochain_eq_canonical
    - generatedAuthoredDiagnosticObjectCollapseComparison
    - MateCoherentRel
    - generatedAuthoredDiagnosticObjectCollapseComparison_replacement
    - mateCoherentRel_replacePresentation_iff
    - AuthoredBCDatumSquare.reselectEdges
    - AuthoredBCDatumSquare.initialRawDefectCochain_reselectEdges
    - finiteAxisFold_reselectEdges_not_mateCoherentRel
    - finiteAxisFold_public_not_mateCoherentRel_on_orbit
    - finiteAuthoredBCDatumSquare_mateCoherentRel
    - finiteAxisFold_input_reselectionOrbit_nontrivial
  claim_mapping:
    theorem_names:
      - finiteAxisFold_public_not_mateCoherentRel_on_orbit
      - finiteAuthoredBCDatumSquare_mateCoherentRel
      - mateCoherentRel_replacePresentation_iff
    source_labels:
      - target proof artifacts K2 authored support induced comparison
      - target proof artifacts fixed MateCoherentRel positive-negative pair and full reselection orbit
      - target proof artifacts presentation replacement invariance
    conjuncts:
      - diagnostic-generated non-twist factor -> authoredDiagnosticObjectCollapseComponentAtCochain
      - all-input comparison producer -> generatedAuthoredDiagnosticObjectCollapseComparison
      - fixed public equation -> MateCoherentRel
      - strict positive fixture -> finiteAuthoredBCDatumSquare_mateCoherentRel
      - lax negative fixture on every actual orbit representative -> finiteAxisFold_public_not_mateCoherentRel_on_orbit
      - nontrivial orbit -> finiteAxisFold_input_reselectionOrbit_nontrivial
      - presentation replacement -> mateCoherentRel_replacePresentation_iff
    undischarged_assumptions: []
    acceptance_point: the authored-support K2 comparison is generated for every input from the raw diagnostic and package-selected normalization branch, the fixed public relation has the required strict-positive and genuine full-orbit lax-negative witnesses, and replacement invariance is proved; this does not discharge K3, K4, final assembly, or G-110 completion
    port_status: unported
audits:
  premise_delta:
    discharged:
      - no collapse morphism or comparison is supplied by the caller
      - diagnostic firing is read from rawDefectCochain
      - finite support admissibility and noninvertibility are concretely proved
      - every actual G-106 reselection orbit cochain is represented by the initial diagnostic of a reselected authored datum
      - the same public relation is used for strict positive, lax negative, orbit, and replacement statements
    remaining:
      - K3 diagnostic base-change action, admissibility condition, checker bridge, and positive-negative pair
      - K4 pasting closure, comparison compatibility, pullback-side composition coherence, and G-106/G-109 bridge
      - final target assembly and completion review
  certificate_provenance:
    discharged:
      - the selected normalization object map comes from AATCorePackage.reading.objectReading
      - admissibility proves reading-law compatibility and cannot change the fixed constructor by proof irrelevance
      - edge orbit representatives are generated by reselectLiftData and reselectedTwoCellBase
      - the authored comparator table remains fixed under reselectEdges
    unresolved: []
  proof_use:
    used:
      - raw diagnostic identity versus firing branch
      - canonical normalization admissibility and finite noninvertibility
      - exact via-base transport and canonical mate epimorphism cancellation
      - reselectedPathLift_mul and canonicalTwoCellComparator_fac
      - finiteAxisFold_not_coherentizable on every reselection
      - provenance route comparisons for presentation replacement
    unused: []
  structure_field_escape: none-found; AuthoredBCDatumSquare retains only context, base equality, and authored comparator input fields, while the selected factor and comparison are generated
  route_integrity: the comparison is canonical mate followed by the package-selected factor on the actual authored support route; the orbit bridge changes edge lifts through the reviewed G-106 action and leaves the authored table fixed
  target_fitting: none-found
  vacuity: strict positive and lax negative fixtures are both inhabited; the lax orbit is nontrivial and every orbit coordinate fires somewhere
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - focused BCAuthoredDiagnosticObjectCollapseProducer.lean: pass; 24 namespace declarations, standard axioms only
    - focused BCAuthoredDiagnosticObjectCollapseProducerWitnesses.lean: pass; 16 namespace declarations, standard axioms only
    - targeted producer module build: pass; 4066 jobs
    - targeted producer-witness module build: pass; 4071 jobs
    - common scans: pass
  blocking_findings: []
  next_obligation: after merge, select the smallest K3 diagnostic base-change action obligation and retain the existing H_bc qualification and checker contract
review:
  status: pending standard fixed-head review
stop_condition_candidate: none
next_obligation: after merge, begin K3 with the generated diagnostic base-change action and its named actual-firing condition
```

### Cycle 66 — package-selected canonical object normalization

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 66
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: a5b94e57d6f169dee88cbb663b8f15d2079f9361
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Cycle 65 review rejected arbitrary Classical.choose of an unrelated noninvertible support endomorphism
  proof_dag_predecessors:
    - finiteAxisFoldEraseTotal
    - finiteAxisFoldEraseTotal_not_isIso
    - AATCorePackage.reading.objectReading
  proof_obligation: replace arbitrary endomorphism selection by the package-selected normalization to its selected object on each existing configuration, expose exactness as explicit reading laws, and recover the reviewed finite noninvertible erasure
  selection_reason: the object reading is already part of every support package and uniquely fixes the normalization object map; no authored comparison, collapse morphism, or existential endomorphism is selected
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredCanonicalObjectNormalization.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredCanonicalObjectNormalizationWitnesses.lean
  risks:
    - hiding arbitrary morphism data inside an admissibility certificate
    - assuming auxiliary readings are configuration-insensitive without proof
    - promoting this normalization checkpoint to the public K2 producer
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: canonicalObjectNormalization sends every architecture object to the object selected by the package's existing objectReading on the same configuration. It retains configuration, fixes selected objects, and is idempotent. CanonicalObjectNormalizationAdmissible records the conditional equation, operation, invariant, and signature compatibility laws needed by the exact constructor; proof irrelevance proves only that different proofs of these laws cannot change that constructor's morphism. On finiteAxisFoldSupportPackage the normalization object map is exactly finiteAxisFoldEraseObject, the reviewed reading laws discharge admissibility, and noninjectivity makes the resulting total normalization non-IsIso.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredCanonicalObjectNormalization.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredCanonicalObjectNormalizationWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - canonicalObjectNormalization
    - canonicalObjectNormalization_idempotent
    - CanonicalObjectNormalizationAdmissible
    - CanonicalObjectNormalizationAdmissible.equationResidual_configurationInvariant
    - canonicalObjectNormalizationTotal
    - canonicalObjectNormalizationTotal_proof_irrel
    - finiteCanonicalObjectNormalization_admissible
    - auxiliarySensitiveCorePackage_not_admissible
    - finiteCanonicalObjectNormalizationTotal_not_isIso
  claim_mapping:
    theorem_names:
      - finiteCanonicalObjectNormalizationTotal_not_isIso
    source_labels:
      - target proof strategy K2 non-twist factor route
      - Cycle 65 fixed-head forcing-theorem finding
    conjuncts:
      - package-selected normalization object map -> canonicalObjectNormalization
      - conditional exactness surface -> CanonicalObjectNormalizationAdmissible
      - proof-independent output of the fixed constructor -> canonicalObjectNormalizationTotal_proof_irrel
      - fixed finite non-twist witness -> finiteCanonicalObjectNormalizationTotal_not_isIso
    undischarged_assumptions:
      - diagnostic firing selector for this canonical normalization
      - general-package discharge of CanonicalObjectNormalizationAdmissible or a conditional all-input selector
      - all-input AuthoredComparisonProducerSignature
      - fixed public MateCoherentRel and full-orbit bridge
      - presentation-replacement compatibility of the resulting comparison
    acceptance_point: the previously arbitrary object-collapse choice is replaced by a package-selected idempotent object map, with a conditional exact constructor and a concretely discharged finite noninvertible instance; no public K2 claim is made
    port_status: unported
audits:
  premise_delta:
    discharged:
      - normalization object map is fixed by the existing package objectReading
      - proof irrelevance prevents admissibility proofs from changing the output of the fixed constructor
      - the fixed finite support discharges every reading compatibility law
      - an auxiliary-sensitive package refutes canonical-normalization admissibility
      - the fixed normalization is noninvertible
    remaining:
      - discharge CanonicalObjectNormalizationAdmissible on each support where the selector fires, or retain that branch condition explicitly
      - generate the comparison from the raw authored diagnostic using this fixed normalization
      - define the all-input AuthoredComparisonProducerSignature
      - bridge the public initial relation to genuine reselection-orbit representatives
      - prove presentation-replacement compatibility for the resulting comparison
  certificate_provenance:
    discharged:
      - no arbitrary endomorphism, K2 comparison, or K2 target equality is selected or supplied; exactness laws remain explicit admissibility fields
      - the selected object per configuration comes from AATCorePackage.reading.objectReading
      - finite admissibility reuses reviewed equation/operation/invariant/signature laws
    unresolved:
      - general-package admissibility is discharge-required and currently conditional
      - authored diagnostic proof-use for the later comparison selector
  proof_use:
    used:
      - ObjectReading.object and configuration_eq
      - equation residual normalization invariance
      - operation endpoint transport and naturality
      - invariant and signature coordinate transport
      - finiteAxisFoldEraseObject noninjectivity
    unused: []
  structure_field_escape: the object map is package-selected and contains no supplied morphism; exactness remains conditional on the discharge-required CanonicalObjectNormalizationAdmissible laws, concretely discharged only for the finite support
  route_integrity: pass for the package-selected object-map and finite-instance checkpoint; an exact total factor is not characterized as unique among all package endomorphisms, and the public producer remains unclaimed
  target_fitting: none-found
  vacuity: the finite support inhabits admissibility and has a concretely noninvertible normalization; auxiliarySensitiveCorePackage_not_admissible supplies the package-level negative instance
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - focused BCAuthoredCanonicalObjectNormalization.lean: pass; 23 namespace declarations, standard axioms only
    - focused BCAuthoredCanonicalObjectNormalizationWitnesses.lean: pass; 8 namespace declarations, standard axioms only
    - targeted normalization and witness module build: pass; 4062 jobs
    - common scans: pass
  blocking_findings: []
  next_obligation: after merge, make the raw diagnostic select the package normalization only on supports where admissibility is discharged, define the all-input producer, prove presentation-replacement compatibility, and construct a public-relation orbit bridge without an authored-table action invention
review:
  status: pending standard fixed-head review
stop_condition_candidate: none
next_obligation: after merge, connect the raw diagnostic to conditionally admissible canonical object normalization, complete the all-input and presentation-replacement surfaces, and connect the public relation to genuine orbit representatives
```

### Cycle 65 — rejected arbitrary all-input selector

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 65
base_oid: a5b94e57d6f169dee88cbb663b8f15d2079f9361
tracking_issue: 4034
pull_request: 4106
reviewed_head: 756d889805be97f6eed684c1c6cc87aeae1161cd
result:
  proposed_result_type: rejected
  completion_candidate: no
  proof_obligation_delta: none accepted; nonidentity raw data only triggered Classical.choose of an arbitrary existing noninvertible support endomorphism, and the all-orbit theorem used a separate cochain-indexed predicate rather than the fixed public relation
audits:
  route_integrity: fail
  target_fitting: found
  blocking_findings:
    - selected factor was not forced by the authored comparator or a universal construction
    - no bridge connected every orbit representative to the fixed public MateCoherentRel
review:
  status: rejected; PR 4106 closed without merge
next_obligation: construct a package-forced normalization factor and a genuine public-relation orbit bridge
```

### Cycle 64 — diagnostic-generated object-collapse comparison

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 64
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 4daa69a7e5ec277709468c79aeaa9d62ab8402b8
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Cycle 63 constructs the genuine non-twist exact object erasure but does not generate it from the authored diagnostic or place it on the public routes
  proof_dag_predecessors:
    - finiteAxisFoldEraseTotal
    - finiteAxisFoldEraseTotal_not_isIso
    - initialRawDefectCochain
    - authoredSupportCanonicalMate
  proof_obligation: make the reviewed object erasure an output of the fixed G-106 raw diagnostic and bridge that selected factor into the public direct/via-base authored-support routes
  selection_reason: this is the shortest construction from the reviewed non-twist factor to the fixed K2 route while consuming the actual authored raw cochain rather than accepting a firing certificate
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredDiagnosticObjectCollapse.lean
    - finiteDiagnosticObjectCollapse_not_mateCoherent_on_orbit
  risks:
    - replacing diagnostic generation by a caller-supplied branch certificate
    - losing the factor under bottom transport and right reindexing
    - promoting a fixed-support comparison to the public all-input K2 producer
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: raw diagnostic equality with identity now selects identity, while raw nonidentity selects the reviewed exact object erasure. The initial lax second face computes to the erasure and is noninvertible. The selected southwest factor is transported along the actual bottom and right functors to an endomorphism of the public via-base route; the two identity unitors reflect IsIso, so every firing via-base factor remains noninvertible. That factor is composed with the public canonical mate to form a component-generated authored-support comparison. Every genuine reselection cochain has a nonidentity component because the fixed datum is not coherentizable; the generated non-twist comparison therefore differs from the canonical mate throughout the full G-106 reselection orbit.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredDiagnosticObjectCollapse.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - finiteDiagnosticObjectCollapseTotalAtCochain
    - finiteDiagnosticObjectCollapseTotalAtCochain_not_isIso
    - finiteInitialDiagnosticObjectCollapse_second_eq_erase
    - finiteViaBaseDiagnosticObjectCollapseComponentAtCochain
    - finiteViaBaseDiagnosticObjectCollapseComponentAtCochain_ne_id
    - finiteViaBaseDiagnosticObjectCollapseComponentAtCochain_not_isIso
    - finiteDiagnosticObjectCollapseComparisonAtCochain
    - finiteDiagnosticObjectCollapseComparisonAtCochain_identity_eq_canonical
    - finiteDiagnosticObjectCollapse_not_mateCoherent_on_orbit
    - finiteGeneratedDiagnosticObjectCollapseComparison_second_ne_canonical
  claim_mapping:
    theorem_names:
      - finiteDiagnosticObjectCollapse_not_mateCoherent_on_orbit
    source_labels:
      - target proof strategy K2 non-twist factor route
      - target route integrity and all-orbit gates
    conjuncts:
      - authored diagnostic generation -> finiteDiagnosticObjectCollapseTotalAtCochain
      - non-twist noninvertibility -> finiteInitialDiagnosticObjectCollapse_second_not_isIso
      - public route bridge -> finiteDiagnosticObjectCollapseComparisonAtCochain
      - full orbit persistence -> finiteDiagnosticObjectCollapse_not_mateCoherent_on_orbit
    undischarged_assumptions:
      - extension from the fixed finite datum to the all-input AuthoredComparisonProducerSignature
      - presentation-replacement compatibility of the object-collapse comparison
      - identification with the fixed public MateCoherentRel
    acceptance_point: the fixed authored diagnostic now generates the reviewed non-twist factor and a public-route comparison with full-orbit mismatch; it is not yet the all-input K2 producer
    port_status: unported
audits:
  premise_delta:
    discharged:
      - branch selection is computed from the actual raw cochain component
      - nonidentity selects the internally constructed exact erasure without a collapse or firing certificate
      - bottom transport and right reindexing place the factor on the public via-base route
      - identity unitors reflect IsIso and prove that a firing transported factor remains noninvertible
      - noncoherentizability supplies a firing component for every genuine reselection cochain
    remaining:
      - define the all-input public producer or an input-derived package-generic non-twist construction
      - prove finite presentation replacement for the selected object-collapse comparison
      - connect the reviewed comparison to the fixed public MateCoherentRel
  certificate_provenance:
    discharged:
      - selector consumes cochain cell equality against the independent identity cochain
      - the selected nonidentity branch is the reviewed Cycle 63 construction
    unresolved:
      - all-input producer provenance
  proof_use:
    used:
      - initialRawDefectCochain and the fixed authored comparator computation
      - finiteAxisFoldEraseTotal and its concrete object-map noninjectivity
      - bottom transport, right reindexing, and their identity unitors
      - finiteAxisFold_not_coherentizable and the raw-cochain coherence equivalence
    unused: []
  structure_field_escape: none-found
  route_integrity: pass for the fixed finite diagnostic and public-route bridge; all-input producer remains unconstructed
  target_fitting: none-found
  vacuity: none-found; identity cochain gives the positive predicate instance and every orbit cochain gives a negative instance
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - focused BCAuthoredDiagnosticObjectCollapse.lean: pass; 24 namespace declarations, standard axioms only
    - shared identity-unitor reflection API migration: six focused files pass; standard axioms only
    - targeted changed-module set build including BCAuthoredDiagnosticObjectCollapse and migrated witnesses: pass; 4067 jobs
  blocking_findings: []
  next_obligation: generalize the diagnostic-selected non-twist comparison across presentation replacement and connect it to the all-input public K2 producer/relation without a supplied collapse
review:
  status: pending standard fixed-head review
stop_condition_candidate: none
next_obligation: after merge, construct presentation-replacement compatibility and the all-input public K2 producer bridge
```

### Cycle 63 — exact object-collapse endomorphism

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 63
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: ec52417b2e9297c03b8e194e68b36848e3e9d372
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Cycle 62 leaves objectMap and operationMap as the remaining exact-endomorphism fields that may support a non-axis collapse
  proof_dag_predecessors:
    - finiteAxisFoldSupportPackage
    - finiteAxisFoldSupportPackage_coordinateEquiv_injective
    - finiteAxisFoldSupportPackage_equationMap_injective
  proof_obligation: decide whether same-configuration object collapse survives the exact-hom laws on the fixed authored support and, if so, construct the complete exact package endomorphism
  selection_reason: a surviving object collapse gives a concrete non-twist noninvertible factor inside the fixed BC target and directly removes the missing-exact-hom API gap
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredObjectCollapse.lean
    - finiteAxisFoldEraseTotal_not_isIso
  risks:
    - equation residual compatibility after transported equation-reading reindexing
    - operationMap endpoint casts and naturality
    - confusing an unconditional object erasure with a diagnostic-generated K2 comparison
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: the finite authored-support reading admits a configuration-preserving erasure of auxiliary object readings. Configuration-only residual dependence is proved for the finite equation system and preserved through Atom transport and equation-reading base reindexing. The erasure therefore extends to a complete SignedExactCoreReadingHom and PackageTotalHom; its operation map is constructed by endpoint casts and satisfies configuration naturality. Two explicit same-configuration objects with PUnit and Bool structure-map readings are distinct but have equal erasure, so the total endomorphism is not an isomorphism.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredObjectCollapse.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - finiteAxisFoldEraseObject_not_injective
    - auxiliarySensitiveEquationSystem_not_configurationInvariant
    - finiteEquationResidual_configurationInvariant
    - transportEquationResidual_configurationInvariant
    - castEquationResidual_configurationInvariant
    - finiteAxisFoldEraseEquationTransport
    - finiteAxisFoldEraseUpper
    - finiteAxisFoldEraseTotal
    - packageTotalHom_objectMap_injective_of_isIso
    - finiteAxisFoldEraseTotal_not_isIso
  claim_mapping:
    theorem_names:
      - finiteAxisFoldEraseTotal_not_isIso
    source_labels:
      - target proof strategy K2 non-twist factor route
      - target route integrity gate
    conjuncts:
      - fixed-support non-axis exact factor -> finiteAxisFoldEraseTotal
      - noninvertibility -> finiteAxisFoldEraseTotal_not_isIso
      - residual and operation compatibility -> finiteAxisFoldEraseEquationTransport / finiteAxisFoldEraseUpper
    undischarged_assumptions:
      - generation of this erasure from the authored diagnostic input
      - insertion into the two canonical authored-support comparison paths
      - MateCoherentRel and all-orbit negative theorem
    acceptance_point: the selected object/operation exact-lifting obligation is closed by a concrete construction; it is not yet the public K2 producer
    port_status: unported
audits:
  premise_delta:
    discharged:
      - same-configuration object collapse survives every SignedExactCoreReadingHom field required on the fixed authored support
      - operationMap and operation_naturality for that collapse are internally constructed
      - noninvertibility is derived from explicit object-map noninjectivity
    remaining:
      - generate or select the object erasure from authored diagnostic data without a conclusion certificate
      - compose it into the public authored comparison and prove presentation replacement plus all-orbit noncoherence
  certificate_provenance:
    discharged:
      - erasure is defined from the fixed finite reading, Atom equivalence, and input object configuration
      - noninjectivity uses explicit PUnit/Bool same-configuration objects
    unresolved:
      - diagnostic-to-erasure selection theorem
  proof_use:
    used:
      - finite NoCycle residual definition
      - canonical Atom transport and equation-reading cast
      - finite operation reading and endpoint casts
    unused: []
  structure_field_escape: none-found
  route_integrity: pass for the exact endomorphism; public diagnostic generation remains unconstructed
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - focused BCAuthoredObjectCollapse.lean: pass; 21 namespace declarations, standard axioms only
    - exact target module build ResearchLean.AG.DoctrineFiberProduct.BCAuthoredObjectCollapse: pass; 4060 jobs
  blocking_findings: []
  next_obligation: construct an input-generated selector that uses authored diagnostic data to choose the exact object erasure, then insert that generated non-twist factor into the two K2 comparison paths
review:
  status: pending standard fixed-head review
stop_condition_candidate: none
next_obligation: after merge, construct the diagnostic-generated object-collapse factor and public authored comparison bridge
```

### Cycle 62 — non-axis collapse field audit

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 62
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 1703f5e38e2f69a02e170a36b5bcfc1522891000
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Cycle 61 excludes comparator-induced noninjective axis collapse but leaves other exact-endomorphism fields unclassified
  proof_obligation: determine whether invariant, equation, Atom, or dependent coordinate transport in the fixed authored support package can supply a noninjective alternative to the rejected axis fold
  selection_reason: these are the remaining index/coordinate maps visible in SignedExactCoreReadingHom before auditing object and operation maps
  expected_result_type: proof-checkpoint
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: every exact endomorphism of finiteAxisFoldSupportPackage has the identity map on its singleton invariant index. Its equation map is the function of the stored equation equivalence, its Atom map is the stored Atom equivalence, and each dependent coordinate map is a stored equivalence. All four maps are therefore injective and cannot supply the noninjective collapse sought as a non-axis alternative.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredNonAxisCollapseAudit.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - finiteAxisFoldSupportPackage_invariantMap_eq_id
    - finiteAxisFoldSupportPackage_invariantMap_injective
    - finiteAxisFoldSupportPackage_equationMap_injective
    - finiteAxisFoldSupportPackage_atomMap_injective
    - finiteAxisFoldSupportPackage_coordinateEquiv_injective
audits:
  premise_delta:
    discharged:
      - invariant-index collapse
      - equation-index collapse
      - primitive Atom collapse
      - pointwise dependent-coordinate collapse
    remaining:
      - audit objectMap and operationMap, then either construct a surviving non-axis K2 factor or prove the relevant fixed-fixture structural reduction
  certificate_provenance:
    discharged:
      - injectivity follows from the exact-hom schema and the concrete singleton invariant index, not caller certificates
  proof_use:
    used:
      - concrete finiteAxisFoldSupportPackage
      - stored Atom, equation, and coordinate equivalences
  structure_field_escape: none-found
  route_integrity: no public producer or comparison is defined
  target_fitting: none; the theorems quantify every exact endomorphism of the fixed support package
  vacuity: none-found
  validation_refs:
    - focused BCAuthoredNonAxisCollapseAudit.lean: pass; 5 namespace declarations, standard axioms only
    - exact target module build: pass; 4059 jobs
review:
  status: pending standard fixed-head review
stop_condition_candidate: none
next_obligation: after merge, audit objectMap and operationMap for the fixed support package and complete or refute the fixed-fixture reduction
```

### Cycle 61 — comparator-induction obstruction for the fixed swap

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 61
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 08b4ef716c3135f07346d3e8734b3cb298e893a0
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Cycle 60 PR 4101 was rejected because it definitionally promoted the Cycle 46 choice-based auxiliary fold without an authored-table or universal forcing theorem
  proof_obligation: formalize the finite induction laws for an axis operation generated only by the fixed authored adjacent transposition and decide whether any non-twist diagnostic axis collapse can satisfy them
  selection_reason: the rejected producer becomes noninvertible by orienting one endpoint of a symmetric two-cycle. Comparator equivariance and locality to supplied comparator orbits make the missing induction requirement explicit without accepting a fold or orientation certificate from the caller.
  expected_result_type: blocker-fixed
result:
  proposed_result_type: blocker-fixed
  proof_obligation_delta: FiniteAxisFoldComparatorInduced packages equivariance under the actual authored swap and the no-new-axis orbit-locality law. Every such operation is injective. FiniteAxisFoldCollapse records the noninjective axis action used to make the diagnostic factor non-IsIso, and finiteAxisFold_not_comparatorInduced_and_collapse proves the two requirements incompatible. The exact choice-based generated axis map has a collapse and therefore fails comparator induction. FiniteAxisFoldInducedFold packages an oriented AxisFoldWitness with the induction laws, and its type is empty. Thus the Cycle 46/60 axis-fold producer cannot be promoted by supplying the missing comparator-induction law.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredComparatorInductionObstruction.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - FiniteAxisFoldComparatorInduced
    - FiniteAxisFoldCollapse
    - finiteAxisFold_comparatorInduced_injective
    - finiteAxisFold_not_comparatorInduced_and_collapse
    - finiteAxisFoldGeneratedAxisMap_collapse
    - finiteAxisFoldGeneratedAxisMap_not_comparatorInduced
    - FiniteAxisFoldInducedFold
    - finiteAxisFoldInducedFold_isEmpty
    - finiteAxisFold_no_comparatorInduced_fold
audits:
  premise_delta:
    discharged:
      - whether the existing choice-based axis fold can satisfy the explicit comparator-induction laws -> no
    remaining:
      - construct a K2 producer from additional structure already present in the fixed authored datum but outside comparator-orbit axis collapse, or determine that the fixed schema lacks the structure required by every admissible non-twist route
  certificate_provenance:
    discharged:
      - the obstruction consumes the actual finite authored swap and universally quantifies the candidate axis operation or fold witness
  proof_use:
    used:
      - actual authored adjacent-transposition axis action
      - equivariance, comparator-orbit locality, and the noninjective collapse used by the attempted route
  structure_field_escape: none-found
  route_integrity: no public comparison is defined; the failed Cycle 60 promotion remains rejected
  target_fitting: the theorem eliminates every axis operation satisfying the stated induction laws, including the exact prior generator
  vacuity: none-found; the actual generated axis map supplies the collapse and concretely fails induction
  validation_refs:
    - focused BCAuthoredComparatorInductionObstruction.lean: pass; 22 namespace declarations visible to the namespace audit, standard axioms only
    - exact target module build: pass; 4058 jobs
review:
  status: pending standard fixed-head review
stop_condition_candidate: theorem-backed fixed-route obstruction; not yet a global K2 impossibility because constructions using additional fixed input structure remain unclassified
next_obligation: after merge, either construct a non-axis-collapse K2 producer from existing fixed datum structure or prove the broader reduction from every GOAL-admissible comparator-only non-twist route to the obstructed induction laws
```

### Cycle 60 — rejected public promotion attempt

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 60
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 08b4ef716c3135f07346d3e8734b3cb298e893a0
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_obligation: expose the Cycle 46 cochain-indexed diagnostic under a public producer contract together with strict/lax, orbit, and presentation-replacement laws
  expected_result_type: proof-obligation-discharged
result:
  proposed_result_type: rejected
  completion_candidate: no
  rejected_head: a15c8edab62da90f7b5b403d8ae77342aa03d4d1
  rejected_pr: 4101
  proof_obligation_delta: none accepted. The proposed authoredBCComparisonAtCochain was definitionally authoredDiagnosticComparisonAtCochain, and its public producer was only the initial-cochain specialization. The strict/lax, orbit, and presentation laws were valid for that auxiliary construction but did not force its choice-based postfold from the authored table or a universal property. mateCoherentRel_iff_initial restated only the initial coordinate and did not bridge arbitrary orbit coordinates to the same public relation.
audits:
  blocking_findings:
    - all four fixed-head lanes found the same forbidden auxiliary promotion and missing postfold provenance
    - math review additionally found that the claimed exact initial-to-full-orbit bridge consisted of separate initial and orbit statements rather than an orbit-quantified bridge to one public relation
  route_integrity: fail; Cycle 46's rejected auxiliary was promoted by a definitional alias without a new forcing theorem
review:
  status: rejected; PR 4101 closed without merge
stop_condition_candidate: none
next_obligation: formalize and test the missing comparator-induction law instead of renaming the auxiliary construction
```

### Cycle 59 — nonvacuous authored diagnostic replacement witness

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 59
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 5af7f7eb88b50d80828ad9c6e7eddd353d1449f4
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Cycle 58 proved the universal generated authored diagnostic presentation-replacement equality and left its nonempty raw-distinct specialization open
  proof_obligation: place nonempty authored support, raw-distinct equal-decoding BC presentations, and the generated initial-cochain comparison replacement square on one finite fixture
  selection_reason: the existing authored-support endpoint is definitionally the endpoint already carrying a padded identity presentation, so the missing specialization can be constructed without adding a caller-supplied comparison or compatibility certificate
  expected_result_type: proof-checkpoint
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: the first identity leg of finiteAuthoredSupportCospan is replaced by the existing singleton-support padded identity code. The canonical and padded full BC presentations are proved raw-distinct and equal after complete semantic decoding. Their shared semantic input gives finitePaddedAuthoredSupportBCProvenance, and the Cycle 58 generated comparison theorem is specialized on finiteAuthoredBCDatumSquare. A single conjunction records nonempty authored support, raw distinction, and the replacement square together.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredDiagnosticPresentationReplacementWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - finiteAuthoredSupportBCPresentation_ne_padded
    - finiteAuthoredSupportBCPresentations_semantic_eq
    - finitePaddedAuthoredSupportBCProvenance
    - finiteAuthored_generatedDiagnosticComparison_replacement
    - finiteAuthored_generatedDiagnosticReplacement_nonvacuous
audits:
  premise_delta:
    discharged:
      - nonempty authored raw-distinct equal-decoding specialization of the generated diagnostic replacement square
    remaining:
      - construct the fixed public MateCoherentRel/full-orbit bridge without promoting the unforced auxiliary fold as K2's induced comparison
  certificate_provenance:
    discharged:
      - semantic equality is derived from the padded identity decoder and heterogeneous extensionality for the full BC input
  proof_use:
    used:
      - existing nonempty finiteAuthoredBCDatumSquare and its complete authored comparator table
      - existing raw-distinct singleton-support identity Atom code
      - Cycle 58 generatedAuthoredDiagnosticComparison_replacement
  route_integrity: no comparison, natural family, expected equality, or compatibility certificate is added to the authored datum or replacement provenance
  vacuity: none-found; finiteAuthored_generatedDiagnosticReplacement_nonvacuous packages inhabited authored support, raw presentation inequality, and the specialized replacement equality on the same fixture
  validation_refs:
    - focused BCAuthoredDiagnosticPresentationReplacementWitnesses.lean: pass; 10 namespace declarations, standard axioms only
    - exact target module build: pass; 4078 jobs
review:
  status: pending standard fixed-head review
stop_condition_candidate: none
next_obligation: after merge, construct the fixed public MateCoherentRel/full-orbit bridge or a theorem-backed fixed-target obstruction; do not promote the auxiliary producer by renaming alone
```

### Cycle 58 — diagnostic comparison presentation replacement

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 58
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 4d9388201ce78d0bbe382c16881eb61ebd50b7f0
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Cycles 52--57 completed the actual canonical-mate finite-presentation replacement bridge
  proof_obligation: prove that the diagnostic-generated authored comparison commutes with the same generated direct-route and via-base-route isomorphisms while the semantic input, G-106 transport datum, and complete authored table remain fixed
  selection_reason: Cycle 46 left actual presentation replacement open; Cycle 57 now supplies the canonical square needed to assemble the full diagnostic comparison square
  expected_result_type: proof-checkpoint
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: bcProvenanceCanonicalMate_replacement turns the Cycle 57 rebased equality into the canonical provenance square. The authored canonical mate, transported raw defect, and transported unified fold are each normalized onto provenance-indexed routes. The latter two commute with replacement by naturality of the generated via-base route isomorphism. A four-factor categorical lemma composes those three squares into authoredDiagnosticComparisonAtCochain_replacement, and generatedAuthoredDiagnosticComparison_replacement specializes it to the named initial-cochain producer.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredDiagnosticPresentationReplacement.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - bcProvenanceCanonicalMate_replacement
    - authoredSupportCanonicalMate_replacement
    - authoredViaBaseRawDefectComponentAtCochain_replacement
    - authoredViaBaseUnifiedAxisFoldComponentAtCochain_replacement
    - authoredDiagnosticComparisonAtCochain_replacement
    - generatedAuthoredDiagnosticComparison_replacement
audits:
  premise_delta:
    discharged:
      - universal finite-presentation replacement equality for the arbitrary-cochain diagnostic comparison
      - universal finite-presentation replacement equality for the named generated auxiliary producer
    remaining:
      - specialize the replacement equality on one nonempty authored datum with raw-distinct equal-decoding presentations
      - construct the fixed public MateCoherentRel/full-orbit bridge without promoting the unforced auxiliary fold as K2's induced comparison
  certificate_provenance:
    discharged:
      - route isomorphisms come from realization provenance; raw and fold squares are instances of their naturality
  proof_use:
    used:
      - Cycle 57 canonical mate replacement square
      - G-106 raw defect component at the supplied cochain
      - internally generated unified diagnostic fold at the same cochain
      - literal preservation of toTransportData and the authored comparator under replacePresentation
  route_integrity: no mate, route comparison, fold, expected equality, or compatibility certificate is supplied by the caller
  vacuity: the universal equality is usable for every supplied replacement provenance, but this cycle does not yet exhibit a nonempty authored raw-distinct equal-decoding specialization
  validation_refs:
    - focused BCAuthoredDiagnosticPresentationReplacement.lean: pass; 9 namespace declarations, standard axioms only
    - exact target module build: pass; 4050 jobs
review:
  status: pending standard fixed-head review
stop_condition_candidate: none
next_obligation: after merge, first build a nonempty authored raw-distinct equal-decoding specialization, then construct the public relation/orbit bridge or a theorem-backed fixed-target obstruction; do not promote the auxiliary producer by renaming alone
```

### Cycle 57 — semantic mate replacement square and canonical identification

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 57
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: b8e20e761d2bd022d370890f30ee6bb5c83c6859
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Cycle 56 separated square provenance from selected-route provenance and proved generated unit/counit compatibility
  proof_obligation: assemble the semantic selected mate comparison square and identify the reference-fixed rebased mate with the replacement canonical mate
  selection_reason: this is the remaining non-self naturality law isolated by Cycle 56 and directly composes the already generated square, unit, counit, and route comparisons
  expected_result_type: proof-checkpoint
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: coreTransportReindexHomEquiv_provenanceCompatibility transports the generated right adjunction hom-set equivalence across provenance. bcSemanticSelectedMate_replacement combines it with the covariant-square naturality and generated left counit compatibility to prove the public replacement square. Cancelling the direct-route isomorphism against the existing cleavage-rebased square proves that the rebased mate is the semantic mate and hence the replacement provenance's canonical mate. The same equality is restricted to fixed authored support in normalized provenance-route form.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCPresentationReplacement.lean
  evidence:
    - coreTransportReindexHomEquiv_provenanceCompatibility
    - bcSemanticSelectedMate_homEquiv
    - bcSemanticSelectedMate_replacement
    - bcSelectedRebasedReplacementMate_eq_semanticSelectedMate
    - bcSelectedRebasedReplacementMate_eq_canonical
    - authoredSupportSelectedRebasedReplacementMate_eq_canonical
audits:
  premise_delta:
    discharged:
      - semantic selected mate public comparison square under non-self provenance replacement
      - equality of the reference-fixed rebased mate and replacement canonical mate
      - authored-support normalization of that canonical equality
    remaining:
      - re-audit the fixed GOAL acceptance table after merge and select the next undischarged target obligation
  certificate_provenance:
    discharged:
      - every square, route comparison, unit, counit, and hom-set equivalence is generated from the fixed semantic input and finite realization provenance
  proof_use:
    used:
      - Cycle 55 presentation-independent covariant square comparison
      - Cycle 56 generated unit and counit provenance compatibility
      - Cycle 53 cleavage-rebased public mate comparison square
  route_integrity: the comparison square is derived inside mateEquiv from naturality and generated adjunction data; no caller-supplied mate or comparison certificate is introduced
  vacuity: none-found; the theorem is quantified over arbitrary reference and replacement provenances, and Cycle 54 supplies a raw-distinct equal-decoding witness
  validation_refs:
    - focused BCPresentationReplacement.lean: pass; 70 namespace declarations, standard axioms only
review:
  status: pending standard fixed-head review
stop_condition_candidate: none
next_obligation: after merge, re-audit the fixed GOAL acceptance table and continue with the highest-priority undischarged obligation
```

### Cycle 56 — square/route provenance separation for the canonical mate

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 56
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: cd1954e60543121354b8ee65f4332eaea235ea4b
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Cycle 55 presentation-independent covariant square comparison and merged PR 4096
  proof_obligation: separate square provenance from selected-route provenance in the generated mate and identify the exact remaining compatibility needed for full presentation replacement
  selection_reason: Cycle 55 proves that square provenance is irrelevant; exposing both provenance roles in one mate distinguishes that discharged layer from adjunction unit/counit provenance
  expected_result_type: proof-checkpoint
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: bcSemanticSelectedMate accepts independently generated square and route provenances over one literal semantic input. Its value is independent of square provenance and reduces to bcProvenanceCanonicalMate when both roles use one provenance. The existing selected rebased mate also reduces to the canonical mate on self-replacement. coreTransportReindexUnit_provenanceCompatibility and coreTransportReindexCounit_provenanceCompatibility construct the two generated adjunction laws under cartRealizationProvenanceComparison by cartesian and cocartesian uniqueness. Thus the remaining non-self comparison is the mate naturality square assembled from proved compatibility laws, not a missing premise.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCPresentationReplacement.lean
  evidence:
    - bcSemanticSelectedMate
    - bcSemanticSelectedMate_reference_independent
    - bcSemanticSelectedMate_self
    - coreTransportReindexUnit_provenanceCompatibility
    - coreTransportReindexCounit_provenanceCompatibility
    - bcSelectedRebasedReplacementMate_self
audits:
  premise_delta:
    discharged:
      - square provenance independence at the mateEquiv input
      - normalization of both semantic and rebased mates on self-replacement
      - generated unit compatibility under cartRealizationProvenanceComparison
      - generated counit compatibility under cartRealizationProvenanceComparison
    remaining:
      - assemble the semantic selected mate's public comparison square from the generated unit and counit compatibility laws
      - use those laws to prove bcSelectedRebasedReplacementMate reference replacement = bcProvenanceCanonicalMate replacement
  certificate_provenance:
    discharged:
      - both adjunctions are generated from the route provenance
      - the square comparison is generated from the square provenance
  proof_use:
    used:
      - Cycle 55 square comparison provenance equality
      - reflexivity of generated cartesian provenance comparisons
      - the Cycle 53 public mate comparison square
  route_integrity: the separation is inside mateEquiv itself; it introduces no caller-supplied mate, unit, counit, or comparison certificate
  vacuity: none-found; the self theorem is general and Cycle 54 provides a raw-distinct pair for the remaining non-self law
  validation_refs:
    - focused BCPresentationReplacement.lean: pass; 64 namespace declarations, standard axioms only
review:
  status: pending standard fixed-head review
stop_condition_candidate: none
next_obligation: assemble the semantic selected mate public comparison square, cancel the direct-route comparison against the existing rebased square, and propagate the resulting canonical mate equality to authored support
```

### Cycle 55 — presentation-independent covariant BC square comparison

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 55
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 8b0fc26b977d4d0dcdfdb68e3caad9c684c53a4f
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Cycle 54 remaining square-isomorphism compatibility obligation and merged PR 4095
  proof_dag_predecessors:
    - Cycle 37 canonical Beck--Chevalley mate
    - Cycle 52 semantic BC realization provenance
    - Cycle 54 raw-distinct equal-decoding BC replacement witness
  proof_obligation: prove that the covariant square isomorphism assembled from a finite BCPresentation is exactly the isomorphism assembled from the fixed semantic BC square, and hence is independent of realization provenance
  selection_reason: the reference-fixed rebased mate and the replacement canonical mate differ only at the covariant square comparison after the cleavage and route bridges already proved in Cycles 52--54
  expected_result_type: proof-checkpoint
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: typedCoreFiberTransportPresentationComparison_eqToIso identifies the generated exact-endpoint presentation comparison with equality transport by strong-cocartesian uniqueness. The typed compositor now exposes its semantic-composition equality isomorphism explicitly. These normal forms prove bcProvenanceCoreTransportSquareIso_eq_semantic and the two-provenance independence theorem bcProvenanceCoreTransportSquareIso_eq.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CoreBeckChevalleyMate.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCPresentationReplacement.lean
  evidence:
    - coreFiberLift_eqToIso_fac
    - typedCoreFiberTransportPresentationComparison_eqToIso
    - typedCoreFiberTransportCompositor_eq
    - bcProvenanceCoreTransportSquareIso_eq_semantic
    - bcProvenanceCoreTransportSquareIso_eq
  claim_mapping:
    comparison_normalization: the generated comparison is the equality-induced semantic transport isomorphism
    compositor_normalization: presentation composition contributes only its decoded semantic equality followed by the G-109 compositor
    provenance_independence: both presentation-built square comparisons equal the one square comparison generated from the fixed literal semantic input
audits:
  premise_delta:
    discharged:
      - compatibility of the presentation-built covariant square isomorphism with the fixed semantic square isomorphism
      - independence of the covariant square comparison from finite BC realization provenance
    remaining:
      - identify bcSelectedRebasedReplacementMate reference replacement with bcProvenanceCanonicalMate replacement using the proved square comparison equality
  certificate_provenance:
    discharged:
      - all equality isomorphisms are generated from decoder and square commutativity theorems
      - the transport comparison is characterized by the generated strong-cocartesian lift
  proof_use:
    used:
      - typed presentation-composition decoder equality on both routes
      - equality of the two decoded composite presentations
      - fixed semantic square commutativity
      - G-109 core transport compositors
  route_integrity: the theorem compares the actual BC square isomorphisms consumed by mateEquiv; it does not factor through a twist, accept a comparison certificate, or replace the mate by an equality cast
  vacuity: none-found; Cycle 54 supplies unequal presentations with equal complete semantic BC input on which this theorem fires
  validation_refs:
    - focused CoreBeckChevalleyMate module build: pass; 4038 jobs, standard axioms only
    - focused BCPresentationReplacement.lean: pass; 58 namespace declarations, standard axioms only
review:
  status: pending standard fixed-head review
stop_condition_candidate: none
next_obligation: identify the reference-fixed rebased replacement mate with bcProvenanceCanonicalMate replacement, then propagate that equality to the authored-support theorem
```

### Cycle 54 — raw-distinct finite BC replacement firing witness

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 54
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: ebfdccf8e8b11796b403023394a2cf69e653fdbc
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Cycle 53 remaining nonvacuity obligation and PR 4094 fixed-head review
  proof_dag_predecessors:
    - Cycle 33 raw-distinct cartesian presentation replacement witness
    - Cycle 52 BC realization provenance
    - Cycle 53 public route/mate comparison square
  proof_obligation: construct two unequal finite BCPresentation values with equal complete toSemanticBC output and instantiate the public route/mate replacement theorem
  selection_reason: arbitrary same-input provenance quantification did not by itself prove that a nontrivial raw replacement exists. Replacing one cospan leg's empty identity Atom support by a singleton-supported identity code changes the authored presentation while preserving its semantic arrow.
  expected_result_type: proof-checkpoint
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: finiteConstantPresentation and finitePaddedConstantPresentation have the same noninvertible source map and semantic identity Atom equivalence but unequal authored Atom supports. Their generated BC cospans share all endpoint codes, the second leg, selected points, and diagnostic geometry. Extensionality of pointed doctrine morphisms and generated pullback squares proves equality of the complete toSemanticBC decoders. finiteReplacementBCPresentation_mate_square then instantiates the Cycle 53 public comparison square on this raw-distinct pair.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCPresentationReplacementWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - finitePaddedConstantPresentation
    - finiteConstantPresentation_ne_padded
    - finiteCanonicalReplacementBCPresentation
    - finitePaddedReplacementBCPresentation
    - finiteReplacementBCPresentations_ne
    - finiteConstantPresentation_semantic_eq
    - finiteConstantPullbackSnd_semantic_eq
    - finiteReplacementBCPresentations_semantic_eq
    - finiteCanonicalReplacementBCProvenance
    - finitePaddedReplacementBCProvenance
    - finiteReplacementBCPresentation_mate_square
  claim_mapping:
    raw_difference: the first cospan leg has empty versus singleton authored Atom support
    semantic_equality: both complete BC decoders are propositionally equal, including generated square, compatible points, and diagnostic geometry
    theorem_firing: the public direct/via-base route comparisons and reference-fixed mate square are instantiated on the unequal pair
audits:
  premise_delta:
    discharged:
      - existence of a raw-distinct equal-decoding finite BCPresentation pair
      - nonvacuous firing of the public presentation replacement theorem
    remaining:
      - identify the reference-fixed rebased replacement mate with the replacement presentation's canonical mate
  certificate_provenance:
    discharged:
      - presentation inequality is witnessed by authored support membership
      - semantic equality is proved by extensionality from computational source maps and decoded Atom equivalences
  proof_use:
    used:
      - the first cospan leg's raw Atom support difference
      - the padded identity decoder equality
      - generated pullback top arrow and fixed bottom arrow semantic equalities
      - complete BCSemanticInput extensionality
  route_integrity: the witness changes an actual noninvertible cospan leg and fires the generated public route comparisons; it is not a proof-field-only or diagnostic-order-only replacement
  vacuity: none-found; the finite presentations are theorem-proved unequal and their complete semantic decoders theorem-proved equal
  validation_refs:
    - focused BCPresentationReplacementWitnesses.lean: pass; 13 namespace declarations, standard axioms only
review:
  status: pending standard fixed-head review
stop_condition_candidate: none
next_obligation: prove compatibility of the presentation-built covariant square isomorphism with the semantic square isomorphism, then identify the rebased replacement mate with bcProvenanceCanonicalMate replacement
```

### Cycle 53 — public route/mate bridge on fixed authored support

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 53
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: aeb9a2036ae009397c6f182ddd88fb6a6da6825e
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: PR 4093 merged checkpoint and its fixed-head mathematical/Lean review findings
  proof_dag_predecessors:
    - Cycle 33 canonical cartesian presentation comparison
    - Cycles 37--38 canonical BC mate and cleavage-independence square
    - Cycle 52 BC realization provenance and rebased replacement mate
  proof_obligation: identify the public direct/via-base route isomorphisms with the cleavage comparisons used by the rebased mate theorem, prove the resulting public mate square, and restrict it while keeping the complete authored G-106 datum fixed
  selection_reason: Cycle 52 constructed both ingredients but did not prove that they were the same generated comparison. The authored comparator is not a field of BCSemanticInput, so an explicit AuthoredBCDatumSquare replacement operation is also required.
  expected_result_type: proof-checkpoint
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: bcReplacementLeftSelectedComparison and bcReplacementRightSelectedComparison factor the public provenance comparisons through the replacement-generated rebased cleavages; their equality theorems are proved by strong-cartesian uniqueness. bcSelectedRebasedReplacementMate normalizes the rebased mate onto the public replacement routes. bcProvenanceCanonicalMate_rebasedReplacement proves the public route/mate square with the reference covariant square isomorphism fixed. AuthoredSupportContext.replacePresentation and AuthoredBCDatumSquare.replacePresentation preserve the semantic square, lift, endpoint incidence, two-cell base equations, diagnostic interpretation, and authored comparator table definitionally. authoredSupportCanonicalMate_rebasedReplacement restricts the public square to that fixed authored support.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCPresentationReplacement.lean
  evidence:
    - AuthoredSupportContext.replacePresentation
    - AuthoredSupportContext.realizationProvenance
    - AuthoredBCDatumSquare.replacePresentation
    - AuthoredBCDatumSquare.replacePresentation_toTransportData
    - AuthoredBCDatumSquare.replacePresentation_authored
    - bcReplacementLeftSelectedComparison
    - bcReplacementRightSelectedComparison
    - bcReplacementLeftSelectedComparison_eq
    - bcReplacementRightSelectedComparison_eq
    - bcSelectedRebasedReplacementMate
    - coreBeckChevalleyMate_rebasedReplacement_inv
    - bcProvenanceCanonicalMate_rebasedReplacement
    - authoredSupportDirectRouteReplacementComparison
    - authoredSupportViaBaseRouteReplacementComparison
    - authoredSupportSelectedRebasedReplacementMate
    - authoredSupportCanonicalMate_rebasedReplacement
  claim_mapping:
    public_route_bridge: the route isomorphisms and the mate square are generated by the same strong-cartesian uniqueness comparisons
    authored_support: presentation provenance changes while semantic diagnostic data, lift, endpoint data, and authored table remain fixed
    mate_scope: the replacement mate uses the reference presentation's covariant square isomorphism and is not yet identified with bcProvenanceCanonicalMate replacement
audits:
  premise_delta:
    discharged:
      - public direct/via-base comparisons are connected to the cleavage-independent mate theorem
      - authored G-106 data and comparator table are explicitly fixed under presentation replacement
    remaining:
      - identify the reference-fixed rebased mate with the replacement presentation's canonical mate by proving covariant square-isomorphism compatibility
      - construct a raw-distinct finite BCPresentation pair with equal toSemanticBC and fire the public theorem on it
  certificate_provenance:
    discharged:
      - every route comparison is generated from strong-cartesian lift uniqueness
      - no mate, route, comparator, or compatibility certificate is accepted as input
  proof_use:
    used:
      - complete BCSemanticInput equality through BCRealizationProvenance
      - left and right selected cartesian lifts
      - reference canonical mate and cleavage-independence theorem
      - fixed authored support functor
    preserved_but_not_consumed_by_structural_mate:
      - two-cell base equations and authored comparator table, via the datum-level replacement equalities
  route_integrity: no equality-cast route, twist factorization, caller-supplied mate, or comparator certificate is used
  vacuity: concern-open; arbitrary provenance pairs are quantified, but a raw-distinct finite BC pair has not yet been instantiated
  validation_refs:
    - focused BCPresentationReplacement.lean: pass; 53 namespace declarations, standard axioms only
review:
  status: pending standard fixed-head review
stop_condition_candidate: none
next_obligation: construct and fire a raw-distinct equal-decoding finite BC presentation witness, then identify the reference-fixed rebased mate with the replacement canonical mate
```

### Cycle 52 — semantic BC presentation replacement bridge

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 52
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 2c97a6ca13dfdf94c53c0148117615cd8d704f0b
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 51 merge synchronization comment 5385315900 and Cycle 52 fixed selection comment 5385324279
  proof_dag_predecessors:
    - Cycle 33 cartesian presentation replacement comparison over one literal semantic arrow
    - Cycle 35 transport--reindex adjunction and unit/counit presentation compatibility
    - Cycles 37--38 canonical BC mate and cleavage-independence comparison
    - Cycle 51 explicit separation of swap equivariance from actual presentation replacement
  proof_obligation: for two authored BC presentations with one literal decoded BCSemanticInput, generate the four edge provenances, compare the direct and via-base routes, and prove the canonical mate comparison or isolate its exact remaining compatibility law
  selection_reason: actual presentation replacement is the closest open bridge between the fixed authored diagnostic data and a public K2 comparison. It also tests a condition previously left as an explicit hypothesis without introducing a fold, quotient, twist, or equality-cast answer.
  expected_result_type: proof-checkpoint
  risks:
    - silently strengthening semantic equality to literal equality of finite endpoint codes
    - transporting a complete reindexing functor instead of generating its comparison by cartesian uniqueness
    - treating route comparison alone as compatibility of the canonical mate
    - hiding the covariant square-isomorphism compatibility inside a supplied certificate
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: BCRealizationProvenance places arbitrary finite BC presentations over one literal decoded semantic input even when their finite endpoint codes differ. The four edge provenance constructors consume only the decoder equality. bcProvenanceDirectRouteComparison and bcProvenanceViaBaseRouteComparison generate the route NatIsos from cartesian-lift uniqueness. bcReplacementLeftCleavage and bcReplacementRightCleavage rebase the replacement-generated selected cleavages onto the reference semantic square. coreBeckChevalleyMate_rebasedReplacement then applies the reviewed cleavage-independence theorem and proves that all adjunction, unit, and counit changes commute with the canonical mate while the reference covariant square isomorphism is fixed. bcSemanticCoreTransportSquareIso constructs a presentation-free square isomorphism directly from the literal semantic square, its commutativity law, and the G-109 compositors. The remaining unproved bridge is equality of each presentation-built bcCoreTransportSquareIso with this semantic square isomorphism across heterogeneous finite endpoint codes.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCPresentationReplacement.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - BCRealizationProvenance
    - BCRealizationProvenance.leftProvenance
    - BCRealizationProvenance.topProvenance
    - BCRealizationProvenance.bottomProvenance
    - BCRealizationProvenance.rightProvenance
    - bcProvenanceDirectRoute
    - bcProvenanceViaBaseRoute
    - bcProvenanceCanonicalMate
    - bcProvenanceCoreTransportSquareIso
    - bcSemanticCoreTransportSquareIso
    - bcProvenanceDirectRouteComparison
    - bcProvenanceViaBaseRouteComparison
    - bcReplacementLeftCleavage
    - bcReplacementRightCleavage
    - bcRebasedReplacementMate
    - coreBeckChevalleyMate_rebasedReplacement
  claim_mapping:
    semantic_replacement_domain: two finite presentations over one literal complete BCSemanticInput
    edge_provenance: all four semantic Cart inputs and their finite realizations are generated from the BC decoder equality
    route_comparison: selected reindexing changes by the canonical cartesian-lift comparison; covariant legs are the fixed semantic arrows
    adjunction_compatibility: the reviewed arbitrary-cleavage mate theorem supplies the full unit/counit comparison with the reference square isomorphism fixed
    remaining_bridge: presentation-built covariant square isomorphisms must be identified with bcSemanticCoreTransportSquareIso
    port_status: unported
audits:
  premise_delta:
    discharged:
      - exact finite-code endpoint equality is not required for direct/via-base route comparison
      - selected reindexing comparison is generated by cartesian uniqueness from realization provenance
      - unit/counit and adjunction change commute with the mate for the replacement-generated cleavages
    remaining:
      - prove bcCoreTransportSquareIso presentation = bcSemanticCoreTransportSquareIso (toSemanticBC presentation) without dependent elimination of heterogeneous finite endpoint codes
  certificate_provenance:
    discharged:
      - all four edge provenances are generated from BCRealizationProvenance.realization_eq
      - route comparisons are generated by cartRealizationProvenanceComparison
    unresolved:
      - no certificate is accepted for the remaining square-isomorphism equality; it requires a theorem from compositor factorization and transport comparison uniqueness
  proof_use:
    used:
      - complete semantic BC decoder equality
      - all four semantic square arrows
      - presentation-generated selected cleavages
      - cartesian uniqueness and reviewed cleavage-independence mate comparison
    unused:
      - diagnostic geometry is held fixed by equality of the complete BCSemanticInput; the authored comparator is outside BCSemanticInput and was not fixed in Cycle 52
  structure_field_escape: none-found
  route_integrity: direct and via-base comparisons are generated from finite realization provenance and universal cartesian comparison; no comparison or mate field is accepted
  target_fitting: none-found
  vacuity: concern-open; Cycle 52 quantified conditional provenance pairs but did not instantiate a raw-distinct equal-decoding finite BC pair
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none
  validation_refs:
    - focused BCPresentationReplacement.lean: pass; 33 namespace declarations, standard axioms only
review:
  status: pending standard fixed-head review
stop_condition_candidate: none
next_obligation: prove the presentation-built covariant square isomorphism equals the presentation-free semantic square isomorphism, then close the full canonical-mate replacement square
```

### Cycle 51 — swap-symmetric orbit-local fold no-go

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 51
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 525c98d55a959a5db80bea40c26682ad8048c97a
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 50 merge synchronization comment 5385213996 and Cycle 51 fixed selection comment 5385228778
  proof_dag_predecessors:
    - Cycles 44--46 diagnostic-generated noninvertible one-axis fold
    - Cycle 46 formal-review rejection of its arbitrary orientation as the public authored comparison
    - Cycle 50 natural insertion normalization to a forbidden post-isomorphism twist
  proof_obligation: test the conditional repair class in which an axis operation on the fixed lax Fin 3 witness is equivariant under the authored adjacent transposition and local to its supplied orbits; determine whether the existing noninvertible fold lies in that class
  selection_reason: the prior fold becomes noninvertible by choosing one endpoint of its symmetric two-cycle. Commutation with the swap and locality to its orbits are explicit algebraic conditions under which that orientation would be removed. This cycle does not derive either condition from actual presentation replacement or comparator-only provenance.
  expected_result_type: blocker-fixed
  risks:
    - treating axis injectivity as categorical invertibility
    - presenting the scoped fixed-witness theorem as a global classification of K2 producers
    - accepting an orientation, order, fold, comparison, or noninvertibility certificate from the caller
result:
  proposed_result_type: blocker-fixed
  proof_obligation_delta: FiniteAxisFoldSwapEquivariant states commutation with the actual authored adjacent transposition and FiniteAxisFoldSwapOrbitLocal states locality to its supplied orbits. finiteAxisFold_swapEquivariant_orbitLocal_injective proves every operation satisfying both conditions is injective. finiteAxisFoldWitness_orbitLocal and finiteAxisFoldWitness_not_equivariant prove that every AxisFoldWitness for the fixed swap is orbit-local and breaks swap equivariance. finiteAxisFoldGeneratedAxisMap_eq_chosen opens the actual generatedAxisFoldTotal availability branch and transports those results to its Classical.choice-selected witness, so the exact Cycle 44 generator fails the symmetric repair condition independently of which orientation is selected. The named source-zero witness supplies computational values and separate predicate controls. The cycle does not prove that GOAL presentation replacement implies equivariance or that comparator-only generation implies orbit locality.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCAxisFoldSwapSymmetryNoGo.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - finiteAxisFold_swapEquivariant_orbitLocal_injective
    - finiteAxisFold_not_swapEquivariant_and_orbitLocal_of_not_injective
    - finiteAxisFoldWitness_orbitLocal
    - finiteAxisFoldWitness_not_equivariant
    - finiteAxisFoldGeneratedAxisMap_eq_chosen
    - finiteAxisFoldGeneratedAxisMap_orbitLocal
    - finiteAxisFoldGeneratedAxisMap_not_equivariant
    - finiteAxisFoldSwapWitness_axisMap_zero
    - finiteAxisFoldSwapWitness_axisMap_one
    - finiteAxisFoldSwapWitness_axisMap_two
    - finiteAxisFoldSwapWitness_orbitLocal
    - finiteAxisFoldSwapWitness_not_equivariant
    - finiteAxisFoldSwapEquivariant_id
    - finiteAxisFoldSwapOrbitLocal_not_constZero
    - finiteAxisFoldSwapWitness_invariance_noGo
  claim_mapping:
    swap_symmetry: equivariance under the concrete authored swap is an explicit hypothesis
    orbit_local_scope: each axis image remains in its supplied swap orbit is an explicit hypothesis
    no_go: both properties force injectivity, whereas the earlier fold obtains noninvertibility from a noninjective oriented collapse
    concrete_firing: the actual choice-based generator is orbit-local and non-equivariant for every possible selected witness; the named source-zero fold computes the failure at axis zero
    global_boundary: no categorical IsIso conclusion and no quantification over unrelated K2 producers
audits:
  premise_delta:
    discharged:
      - whether the existing one-axis fold satisfies the swap-equivariant orbit-local repair conditions -> no
    remaining:
      - construct additional structure from the fixed authored table without an orientation choice, or prove a broader exhaustion/GOAL-defect theorem
  certificate_provenance:
    discharged:
      - the concrete firing opens the exact generatedAxisFoldTotal branch and covers its arbitrary Classical.choice witness
    unresolved:
      - any producer using structure beyond comparator-orbit transport
  proof_use:
    used:
      - actual authored swap action
      - every possible prior fold witness and the actual choice-based generated axis map
      - equivariance and orbit-locality as explicit conditional repair hypotheses
    unused: []
  structure_field_escape: none-found; the central theorem is conditional and does not claim that its hypotheses are generated from the authored schema
  route_integrity: the earlier fold remains auxiliary; no public MateCoherentRel or presentation-replacement bridge is defined
  target_fitting: the theorem explains rather than hides the selected orientation
  vacuity: the concrete fold fires orbit locality, noninjectivity, and failure of equivariance
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none; this is a scoped conditional fold-symmetry blocker, not an actual presentation-replacement obstruction
  validation_refs:
    - focused BCAxisFoldSwapSymmetryNoGo.lean: pass after claim-scope and generated-choice bridge fix; 21 namespace declarations, standard axioms only
    - targeted build for exactly BCAxisFoldSwapSymmetryNoGo: pass; 4057 jobs; no Research aggregate or full build
review:
  status: initial Math A/B rejected actual-presentation-replacement and comparator-only provenance overclaims, Lean A requested two-sided predicate controls, and Lean B found the missing bridge to generatedAxisFoldTotal; the batch fix scopes the claim to explicit swap symmetry/orbit locality, adds both controls, and proves the result for every possible choice-selected fold witness; one full post-core-fix rerun required
stop_condition_candidate: none
next_obligation: complete standard review; then construct the missing bridge from actual presentation replacement/comparator-only generation to concrete algebraic constraints, or select a different non-twist producer
```

### Cycle 50 — natural unit-interior insertion normalization

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 50
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: f8f3ccbd4f1dbba61204293790dae1a394dfd8f6
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 49 merge synchronization comment 5385085907 and Cycle 50 fixed selection comment 5385111160
  proof_dag_predecessors:
    - Cycle 37 generated canonical mate and explicit unit--square--counit component
    - Cycle 40 canonical mate IsIso
    - Cycle 43 exact canonical-comp-raw normalization
    - Cycle 47 canonical post-IsIso twist classification
    - Cycles 48--49 fixed-target quotient/Cofork direction and nonexistence barriers
  proof_obligation: insert the actual G-106 residual before the generated Beck--Chevalley unit--square--counit mate, with no fold or quotient; either fire a genuinely non-IsIso interior factor or prove that every such natural source-derived insertion normalizes to the forbidden canonical-post-IsIso route
  selection_reason: the canonical mate is assembled from a right unit, generated square map, and mapped left counit. Inserting the authored residual at the entrance tests whether these individually generated universal maps can turn the diagnostic automorphism into a genuine non-twist factor without inventing a fold, quotient, intermediate endomorphism, or return map.
  expected_result_type: proof-obligation-discharged-or-blocker-fixed
  risks:
    - presenting an ordinary naturality rewrite as a new K2 producer
    - accepting an intermediate endomorphism not generated from the source residual
    - claiming the scoped natural-insertion normalization covers every conceivable non-Cofork construction
    - promoting a concrete mismatch whose residual is still invertible
  unchecked:
    - standard four-lane formal review
result:
  proposed_result_type: blocker-fixed
  proof_obligation_delta: coreBeckChevalleyPreMateInsertion, coreBeckChevalleyPostUnitInsertion, and coreBeckChevalleyPostSquareInsertion place an arbitrary source-fiber diagnostic before the unit, after the unit, and after the square; the fourth placement is postcomposition after the counit. The three boundary theorems separately consume unit naturality, generated-square naturality, and counit naturality, and coreBeckChevalleyNaturalInsertionBoundary_normalization identifies all four placements with the canonical mate followed by the via-base functor image of the same diagnostic. coreBeckChevalleyPreMateInsertion_isIso proves that an invertible diagnostic therefore remains invertible. authoredPreMateDiagnosticComponent specializes the construction to the actual initial G-106 residual without accepting a caller endomorphism, and its exact normalization identifies the postfactor with authoredViaBaseRawDefectComponent. The fixed lax second face proves the component genuinely differs from the canonical mate and that the residual is nonidentity, so every natural boundary placement fires concretely but is exactly a forbidden canonical post-automorphism twist rather than a non-twist K2 comparison.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredPreMateInsertionNoGo.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - coreBeckChevalleyPreMateInsertion
    - coreBeckChevalleyPostUnitInsertion
    - coreBeckChevalleyPostSquareInsertion
    - coreBeckChevalleyPreMateInsertion_eq_post
    - coreBeckChevalleyPreMateInsertion_eq_postUnit
    - coreBeckChevalleyPostUnitInsertion_eq_postSquare
    - coreBeckChevalleyPostSquareInsertion_eq_post
    - coreBeckChevalleyNaturalInsertionBoundary_normalization
    - coreBeckChevalleyPreMateInsertion_isIso
    - authoredPreMateDiagnosticComponent
    - authoredPreMateDiagnosticComponent_eq_canonical_comp_viaRawDefect
    - authoredPreMateDiagnosticComponent_isIso
    - authoredPreMateDiagnosticComponent_isCanonicalPostIsoTwist
    - finiteAxisFold_preMateDiagnostic_second_ne_canonical
    - finiteAxisFold_preMateDiagnostic_has_nontrivial_postIsoResidual
  claim_mapping:
    generic_route: source diagnostic at each of the four natural boundaries of the generated unit--square--counit mate
    normalization: unit, square, and counit naturality separately identify all boundary placements with the via-base postfactor
    authored_provenance: the diagnostic is the actual initialRawDefectCochain component and its postfactor is the existing via-base image
    finite_firing: the fixed adjacent-swap residual gives a noncanonical component with a concrete nonidentity residual
    route_no_go: because the residual is an isomorphism, the fired mismatch is precisely a forbidden canonical post-isomorphism twist
    global_boundary: the theorem covers natural source-derived insertion into the mate; it does not quantify arbitrary intermediate endomorphisms unrelated to functorial transport
    port_status: unported
audits:
  premise_delta:
    discharged:
      - whether moving the G-106 residual among the natural boundaries of the unit--square--counit path can evade the Cycle 43 twist normalization -> refuted by the three constituent naturality laws
    remaining:
      - construct a separately generated noninvertible intermediate operation with provenance from the fixed authored data and no fold/quotient/return input, or determine that all GOAL-admissible K2 routes are exhausted
  certificate_provenance:
    discharged:
      - source residual and via-base residual are existing generated images of initialRawDefectCochain
    unresolved:
      - provenance of any non-natural noninvertible intermediate operation
  proof_use:
    used:
      - actual source residual
      - unit, square-comparison, and counit naturality
      - canonical mate IsIso
      - transported residual IsIso
      - concrete finite residual nonidentity
    unused: []
  structure_field_escape: none-found; the generic route-class lemma quantifies its source diagnostic, while the authored producer fixes it to initialRawDefectCochain and accepts no comparison, intermediate map, quotient, return, fold, equality, or noninvertibility certificate
  route_integrity: the attempted interior route is rejected by exact normalization; no public K2 relation is defined
  target_fitting: none
  vacuity: the finite lax second face proves a genuine mismatch and nonidentity residual
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none; this is a scoped blocker, not a global K2 refutation
  validation_refs:
    - focused BCAuthoredPreMateInsertionNoGo.lean: pass after the review fix; 16 namespace declarations, standard axioms only
    - targeted build for exactly BCAuthoredPreMateInsertionNoGo: pass; 4062 jobs; no Research aggregate or full build
review:
  status: initial Math B central finding fixed by adding all internal boundary placements and separate unit, square, and counit naturality proofs; one full post-core-fix rerun required
stop_condition_candidate: none
next_obligation: complete standard review of this blocker-fixed route; if accepted, audit whether any GOAL-admissible non-Cofork producer remains beyond functorial source insertion, the rejected diagnostic folds, and the impossible fixed-target Cofork route
```

### Cycle 49 — finite standard Cofork nonexistence

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 49
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 8faa8044805e5cac29e20f23bb30646dfb049df2
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 48 merge synchronization comment 5384910468 and Cycle 49 fixed selection comment 5384925074
  proof_dag_predecessors:
    - G-106 initial raw-defect cochain on the fixed lax double diamond
    - diagnostic axis-fold construction generated from a moved object-fixing axis
    - Cycle 43 transport of the raw residual to the fixed authored via-base route
    - Cycle 48 standard Cofork direction and return-map barrier
  proof_obligation: prove that the concrete transported G-106 adjacent-swap residual is absorbed by its generated transported axis fold; use that equation to construct a Cofork on the existing via-base target and use identity as its canonical return, with no cofork, return map, comparison, or expected equality supplied by the caller
  selection_reason: for the fixed lax datum the residual is the adjacent transposition and the generated fold identifies exactly its two-element orbit, so raw followed by fold should equal fold. This directly constructs the Cofork and return data left unresolved by Cycle 48 instead of treating their absence as a stop condition.
  expected_result_type: proof-obligation-discharged
  risks:
    - proving absorption only for a hand-authored map unrelated to the diagnostic generator
    - hiding the Cofork equation or return map as an input
    - claiming the finite construction is already natural for every authored square
    - replacing the fixed via-base target by an unrelated quotient object
  unchecked:
    - Lean construction and exact focused validation
    - standard four-lane formal review
result:
  proposed_result_type: blocker-fixed
  proof_obligation_delta: the attempted absorption equation is impossible for the reviewed finite residual. finiteAxisFold_initialRawDefect_no_coequalizing_arrow proves that no exact-core arrow out of the support object coequalizes the actual G-106 residual with identity: the residual fixes axis 2 while its coordinate equivalence acts by the nontrivial adjacent swap, and the target coordinate equivalence of every exact-core arrow cancels to a contradiction. finiteAxisFold_viaBaseRawDefect_no_cofork transports this no-arrow result through the identity-like core transport and selected reindex functors and proves that the standard Cofork type is empty on the fixed authored via-base route. Thus Cycle 48's conditional theorem is concretely vacuous for this datum, and the proposed generated Cofork with identity return cannot be created inside the current exact fiber category.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredFixedTargetCoforkNoGoWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - finiteAxisFold_initialRawDefect_no_coequalizing_arrow
    - finiteAxisFold_viaBaseRawDefect_no_cofork
  claim_mapping:
    fixed_coordinate_obstruction: the concrete residual fixes signature axis 2 but acts there by a nonidentity coordinate equivalence
    support_no_go: no exact-core arrow from the fixed support object coequalizes that residual with identity
    via_base_no_go: no standard Cofork exists after the actual identity-like transport and reindex route
    global_boundary: the theorem does not show that every K2 producer factors through a Cofork; non-Cofork constructions on the same exact category, quotient categories with weaker coordinate morphisms, and different diagnostic factors remain unrefuted
    port_status: unported
audits:
  premise_delta:
    discharged:
      - existence of a standard Cofork on the fixed finite via-base datum -> refuted by a generated finite no-go theorem
    remaining:
      - construct a non-Cofork K2 factor that does not require raw absorption, or generate a different non-twist factor that stays inside the fixed BC target
      - treat any proposal to change the target category or its morphism notion as a separate GOAL-defect decision rather than a current K2 discharge
  certificate_provenance:
    discharged:
      - the residual, fixed axis, coordinate action, and contradiction are all computed from the existing finite G-106 datum
    unresolved:
      - a GOAL-admissible non-Cofork construction or alternative diagnostic-generated factor
  proof_use:
    used:
      - exact initial raw residual value
      - fixed axis 2
      - nonidentity adjacent-swap coordinate action
      - invertibility of every exact-core coordinate map
      - natural isomorphisms from both identity-like route functors to identity
    unused: []
  structure_field_escape: none-found; the arbitrary outgoing arrow is universally eliminated rather than promoted to a producer input
  route_integrity: the failed Cofork route is rejected by theorem; no caller Cofork, return, comparison, or equality is accepted
  target_fitting: none
  vacuity: converted into the theorem that the relevant Cofork type is empty for the fixed lax datum
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none; this is a scoped blocker for the current exact fiber category, not a global K2 refutation
  validation_refs:
    - focused BCAuthoredFixedTargetCoforkNoGoWitnesses.lean: pass; 3 namespace declarations, standard axioms only
    - targeted build for exactly BCAuthoredFixedTargetCoforkNoGoWitnesses: pass; 4063 jobs; no Research aggregate or full build
    - repository diff, placeholder, hidden/BiDi Unicode, privacy, and import-direction scans: pass
  blocking_findings:
    - initial Math B review found that the aggregate/report presented changing the morphism surface or diagnostic factor as an exhaustive K2 dichotomy without a reduction theorem; the wording now limits the theorem to the standard Cofork route and retains non-Cofork constructions
    - initial Math A found that an external weak quotient followed by an exact coequalizing return cannot evade the support no-arrow theorem; category change is now separated as a GOAL-defect decision rather than a fixed-GOAL obligation
    - initial Lean A/B found the missing Cycle 49 selection reference, and Lean B found the result-opposite heading; both ledger defects are corrected
review:
  status: initial four-lane review findings fixed; one full post-core-fix rerun required
stop_condition_candidate: none
next_obligation: validate the review fix and run the one allowed full rerun; if accepted, select a non-Cofork construction that does not require raw absorption or a different diagnostic-generated non-twist factor inside the fixed BC target
```

### Cycle 48 — fixed-target quotient and return-map barrier

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 48
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 92aeb899e88c59f583ca3e2049dee342bc7a1970
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 47 rejection and Cycle 48 fixed selection comment 5384775710
  proof_dag_predecessors:
    - Cycle 43 exact normalization to canonical mate followed by transported raw defect
    - rejected Cycle 47 residual classification and finite lax mismatch, reselected as proof content rather than merged evidence
    - Cycles 44-46 generated non-IsIso folds and their unresolved universal provenance
    - G-106 raw cochain and reselection orbit
  proof_obligation: use the standard mathlib Cofork API to formalize that a coequalizing arrow generated by a nonidentity diagnostic action has codomain a separate object and requires an additional return map to become an endomorphism of the fixed viaBase target; prove every such conditional returned endomorphism noninvertible after specializing the action to the fixed lax residual
  selection_reason: two independent route searches found no CoreFiber coequalizer, image, idempotent-splitting, reflector, quotient-package, or canonical return-map API. They agreed that quotient existence alone gives Y to Q, whereas K2 requires the fixed Y to Y target. The direction barrier can be stated without revising F0 or accepting a caller return as the public producer.
  expected_result_type: blocker-fixed
  risks:
    - mistaking quotient existence for a generated return map
    - promoting the explicit theorem argument returnMap to K2 data
    - calling a conditional Cofork theorem a constructed quotient or public K2 firing
    - treating absence of current colimit APIs as global mathematical impossibility
  unchecked:
    - standard four-lane formal review
result:
  proposed_result_type: blocker-fixed
  proof_obligation_delta: coforkReturn_not_isIso_of_ne uses mathlib Cofork directly and proves that for a nonidentity action, every cofork arrow followed by every explicit return map is noninvertible, by canceling the hypothetical invertible composite. identityEndomorphismCofork records the standard identity positive control. finiteAxisFold_viaBase_identity_not_coequalizing supplies a concrete negative control for the fixed adjacent-swap residual. finiteAxisFold_viaBase_coforkReturn_not_isIso specializes the action to that actual transported residual while leaving both the cofork and return map explicit and conditional. The rejected optional idempotent fixed-target specialization was removed because its idempotence and nonidentity hypotheses were not generated from the fixed input. The result exposes, rather than discharges, the missing input-generated cofork and return-map provenance.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredComparisonNoGo.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredComparisonNoGoWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredFixedTargetQuotientNoGo.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - coforkReturn_not_isIso_of_ne
    - identityEndomorphismCofork
    - finiteAxisFold_viaBase_identity_not_coequalizing
    - finiteAxisFold_viaBase_coforkReturn_not_isIso
  claim_mapping:
    quotient_direction: a mathlib Cofork arrow may land in its cocone point rather than the fixed viaBase object
    return_boundary: Q to Y is an explicit additional argument and is not generated by the theorem
    noninvertibility: any returned endomorphism coequalizing the fixed nonidentity lax residual is noninvertible
    conditional_boundary: existence and input provenance of a cofork for the fixed lax action remain unresolved
    global_boundary: authored constructions and cofork objects equipped with independently generated return structure remain unrefuted
    port_status: unported
audits:
  premise_delta:
    discharged:
      - action nonidentity -> concrete finite lax viaBase residual theorem
      - hypothetical composite invertibility -> eliminated by categorical cancellation
      - standard Cofork API connection -> direct use, with identity positive and fixed-action identity-negative controls
    remaining:
      - construct an input-generated quotient object and return structure natural in authored support, or prove a stronger current-data no-go without accepting that structure from the caller
  certificate_provenance:
    discharged:
      - no quotient, return map, collapse, noninvertibility certificate, or comparison is selected by the theorem
    unresolved:
      - public K2 requires a producer-generated return to the fixed viaBase route
  proof_use:
    used:
      - coequalizing equation
      - explicit nonidentity action
      - concrete transported raw residual from the fixed lax authored datum
    unused: []
  structure_field_escape: none-found; all externally quantified maps occur only in a negative theorem
  route_integrity: blocker theorem only; no explicit return map is promoted to AuthoredComparisonProducerSignature
  target_fitting: no target comparison or expected equality is an input
  vacuity: action nonidentity and failure of the identity coequalizing arrow fire concretely; existence of a nontrivial cofork for this action is unresolved, so the returned-endomorphism theorem is recorded as conditional rather than a public K2 firing
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none; blocker-fixed is a proof checkpoint and no stop condition is proposed
  validation_refs:
    - focused BCAuthoredComparisonNoGo.lean: pass after predicate removal; 9 namespace declarations, standard axioms only
    - focused BCAuthoredComparisonNoGoWitnesses.lean: pass after existential restatement; 4 namespace declarations, standard axioms only
    - official focused BCAuthoredFixedTargetQuotientNoGo.lean check: pass; 5 namespace declarations, standard axioms only
    - targeted build for exactly BCAuthoredFixedTargetQuotientNoGo after the central review fix: pass; no Research aggregate or full build
    - repository scans after the central review fix: pass
    - one allowed post-core-fix four-lane rerun at 9d1efb8c: Math A, Math B, and Lean A returned No major findings; Lean B returned one noncentral aggregate-summary finding only
    - direct response at e31b16eb: the Lean B aggregate-summary finding is resolved; the exact docstring diff records the Cofork direction barrier, additional return map, unresolved provenance, and next K2 obligations
    - PR 4089 CI at e31b16eb: 7 of 7 checks passed
  blocking_findings:
    - initial Math B and Lean A/B review rejected counting supplied idempotence/nonidentity as generated evidence; optional idempotent results were removed
    - initial Math B rejected finite firing language because the cofork remained external; the ledger now marks the theorem conditional and records cofork provenance as unresolved
    - initial Lean B required the standard mathlib Cofork API and Lean A/B required positive/negative controls for new Prop predicates; the custom predicates were removed, Cofork is used directly, and residual classifications were restated as existential theorems
  next_obligation: merge this accepted blocker-fixed checkpoint and continue with input-generated cofork-object and return-map provenance, including naturality and presentation-replacement compatibility
review:
  status: accepted after the one allowed full four-lane rerun; no central finding remained, and the sole noncentral aggregate-summary finding was resolved by direct response at e31b16eb
stop_condition_candidate: none
next_obligation: merge PR 4089, synchronize Issue 4034, and open the next cycle on input-generated cofork and return provenance
```

### Cycle 47 — residual-isomorphism classification and concrete lax firing

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 47
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 92aeb899e88c59f583ca3e2049dee342bc7a1970
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 46 merge synchronization comment 5384653309 and Cycle 47 fixed selection comment 5384671988
  proof_dag_predecessors:
    - F0b2b bare AuthoredComparisonProducerSignature and fixed MateCoherentRelSignature
    - Cycle 40 invertible authored-support canonical mate
    - Cycle 43 exact universal-factorization normalization to canonical mate followed by transported raw defect
    - Cycles 44-46 generated non-IsIso diagnostic folds and review rejection of their promotion to K2
  proof_obligation: classify the exact invertible universal/raw-factor route as a canonical post-isomorphism twist; fire that classification on the fixed lax witness without assuming the mismatch; distinguish this scoped route obstruction from the still-open universal quotient/reflection route
  expected_result_type: proof-checkpoint
  risks:
    - overstating a route-class obstruction as target-refuted
    - treating every IsIso comparison as forbidden without requiring an actual mismatch/nonidentity residual
    - inventing a new admissibility predicate and thereby revising the fixed schema
    - using the GOAL's prose gate as though it were a Lean-quantified construction language
  unchecked:
    - whether a universal quotient/reflection can be internally generated from the raw orbit and inserted into the existing cocartesian assembly
result:
  proposed_result_type: rejected
  proof_obligation_delta: isCanonicalPostIsoTwist_of_isIso gives the residual existential directly, canonicalPostIsoResidual_unique proves cancellation recovers it uniquely, and hasNontrivialCanonicalPostIsoResidual_of_ne gives a residual with nonidentity hom for a genuine mismatch. The Cycle 43 initial raw component is proved IsIso in the southwest fiber and remains IsIso after bottom transport and right reindexing. Its complete universal-factorization component is therefore IsIso, and authoredFactorizationComparisonComponent_has_raw_residual identifies the exact residual as the transported initial raw defect. The finite lax double diamond discharges the mismatch by reflecting identity equality through the two identity-equivalent functors and reading the adjacent axis swap. This excludes the exact Cycle 43 invertible route on the fixed lax witness but not a non-IsIso universal construction.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredComparisonNoGo.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredComparisonNoGoWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
    - research-modules.txt
  evidence:
    - isCanonicalPostIsoTwist_of_isIso
    - hasNontrivialCanonicalPostIsoResidual_of_ne
    - canonicalPostIsoResidual_unique
    - authoredInitialRawDefectComponent_isIso
    - authoredViaBaseRawDefectComponent_isIso
    - authoredFactorizationComparisonComponent_isIso
    - authoredFactorizationComparisonComponent_has_raw_residual
    - authoredFactorizationComparisonComponent_isCanonicalPostIsoTwist
    - authoredFactorizationComparisonComponent_has_nontrivial_residual_of_ne
    - finiteAxisFold_viaBaseRawDefect_second_ne_id
    - finiteAxisFold_factorizationComparison_second_ne_canonical
    - finiteAxisFold_factorizationComparison_second_has_nontrivial_residual
  claim_mapping:
    generic_classification: invertible parallel components differ by a target automorphism residual
    nontriviality: component inequality makes the residual nonidentity, and the fixed lax witness supplies that inequality concretely
    exact_route: the Cycle 43 universal-factorization residual is exactly the transported initial raw defect
    route_no_go: a lax mismatch from the exact Cycle 43 route is a forbidden nontrivial canonical post-twist
    global_boundary: no theorem quantifies all AuthoredComparisonProducerSignature inhabitants or refutes K2 globally
    remaining_route: a schema-preserving non-IsIso universal quotient/reflection remains neither constructed nor refuted
    acceptance_point: the fixed GOAL prose already supplies the route-integrity and anti-target-fitting acceptance contract; no GOAL change is proposed
    port_status: unported
audits:
  premise_delta:
    discharged:
      - canonical IsIso -> Cycle 40 authored-support canonical-mate instance
      - raw residual IsIso -> PackageFiberAut inverse, fiber IsIso construction, and functorial IsIso preservation
      - Cycle 43 exact residual -> reviewed canonical-comp-viaRawDefect normalization
      - concrete lax mismatch -> adjacent finite-axis swap reflected through transport and reindex functors naturally isomorphic to identity
    remaining:
      - construct a universal quotient/reflection from the raw orbit, or prove its absence for the current data
  certificate_provenance:
    discharged:
      - residual is constructed as canonical inverse followed by authored comparison, not caller-supplied
      - Cycle 43 residual is identified with the actual initial raw defect
    unresolved:
      - a universally forced non-IsIso collapse or quotient landing back in the fixed viaBase object
  proof_use:
    used:
      - IsIso instances of canonical and authored components
      - concrete finite-axis component inequality for nonidentity residual
      - initialRawDefectCochain and PackageFiberAut inverse data
      - Cycle 43 normalization theorem
    unused: []
  structure_field_escape: none-found for the scoped classification
  route_integrity: pass for the exact route-class no-go; no global K2 refutation claimed
  target_fitting: no new producer or collapse is constructed
  vacuity: generic theorem is fired on the exact Cycle 43 component and the fixed lax witness discharges its mismatch hypothesis
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none; initial review rejected the proposed goal-defect inference and the ledger was corrected to proof-checkpoint
  validation_refs:
    - focused BCAuthoredComparisonNoGo.lean: pass; 11 namespace declarations, standard axioms only
    - focused BCAuthoredComparisonNoGoWitnesses.lean: pass; 4 namespace declarations, standard axioms only
    - targeted build for exactly BCAuthoredComparisonNoGoWitnesses (including its direct dependency BCAuthoredComparisonNoGo): pass; no Research aggregate or full build
    - repository scans: pass after the central review fix
  blocking_findings:
    - initial Math A, Math B, and Lean B review rejected the goal-defect stop inference because the theorem excludes only the invertible Cycle 43 route and the fixed GOAL prose already defines admissibility gates
  next_obligation: do not merge this cycle; reselect the useful residual and finite-witness proof DAG into Cycle 48 together with a schema-preserving fixed-target universal-quotient no-go obligation
review:
  status: rejected; the one allowed full rerun found stale GOAL-defect scope text in the aggregate module, so target-theorem-loop forbids merging this cycle even though the text was subsequently corrected
stop_condition_candidate: none
next_obligation: close PR 4088 without merge, synchronize the rejection, and open Cycle 48 from main with the corrected residual checkpoint plus fixed-target universal quotient/reflection no-go
```

### Cycle 46 — generated authored diagnostic on the supplied cochain

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 46
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: a181351b0ec433c6558b7092b62032e4f03b3171
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 45 merge synchronization comment 5384472040 and Cycle 46 fixed selection comment 5384504157
  proof_dag_predecessors:
    - G-106 arbitrary-coordinate rawDefectCochain and InReselectionOrbit
    - Cycle 40 exact authored-support routes and canonical mate
    - Cycle 43 canonical-comp-raw factorization
    - Cycle 44 direct diagnostic fold and Cycle 45 same-boundary pairwise fallback
  proof_obligation: test whether retaining the actual supplied raw defect at every cochain coordinate and appending an internally selected direct-first/pairwise-fallback fold at that same coordinate can realize the fixed public authored-support comparison; prove the resulting diagnostic's lax negative over the full nontrivial orbit and strict positive without accepting caller comparison, fold, equality, or noninvertibility data
  selection_reason: the Cycle 45 quotient alone is an auxiliary diagnostic, while freezing the Cycle 43 raw factor at the initial coordinate would break the required orbit theorem. Keeping the actual raw factor at every coordinate and appending the generated unified fold preserves authored-comparator provenance and carries the non-twist obstruction through the full orbit.
  expected_result_type: proof-checkpoint
  risks:
    - dropping or freezing the supplied raw cochain factor
    - exposing an auxiliary generated diagnostic under the fixed public name
    - accepting caller comparison or noninvertibility data
    - proving only the initial representative or using a singleton orbit
    - treating group-factor invariance as actual presentation replacement
  unchecked:
    - whether the generated fold is uniquely forced as the authored-table induced comparison required by K2
    - public MateCoherentRel and its full-orbit bridge
    - actual replacement of the square presentation for both K2 producers
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: authoredRawDefectTotalAtCochain and its decoded/via-base images retain the supplied G-106 component at every coordinate. Cocartesian universality generates the raw left factor and its comparison normalizes to canonical mate followed by the transported raw component. generatedUnifiedAxisFoldTotalAt selects a direct diagnostic fold when available, otherwise the typed same-boundary pairwise fold, otherwise identity. authoredDiagnosticComparisonComponentAtCochain composes canonical mate, supplied raw factor, and generated fold in that order. The named auxiliary generatedAuthoredDiagnosticComparison is literally the initialRawDefectCochain specialization, and authoredInitialRawDefectTotal_uses_authoredComparator exposes proof-use of input.authored.comparator. On the fixed lax double diamond the selected fold is non-IsIso at every reselection; canonical and raw prefixes are isomorphisms, so the cochain-indexed diagnostic differs from canonical throughout the nontrivial InReselectionOrbit. Its initial-coordinate auxiliary relation fails, while the strict datum fires the same auxiliary relation. Formal review refuted promoting this construction to K2: the noninvertible postfactor is not uniquely forced by the authored table or a universal property, and the full-orbit theorem concerns the cochain-indexed extension rather than the fixed initial relation. The public MateCoherentRel name and all K2 discharge claims are therefore withheld.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredDiagnosticComparison.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredDiagnosticComparisonWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - PackageFiberAut.generatedUnifiedAxisFoldTotalAt_not_isIso
    - authoredRawDefectTotalAtCochain
    - authoredRawFactorizationComparisonComponentAtCochain_eq_canonical_comp_raw
    - authoredDiagnosticComparisonComponentAtCochain_eq_canonical_comp_raw_comp_fold
    - generatedAuthoredDiagnosticComparison
    - GeneratedAuthoredDiagnosticMateCoherentRel
    - authoredInitialRawDefectTotal_uses_authoredComparator
    - finiteAxisFold_generatedUnified_not_isIso
    - finiteAxisFold_not_mateCoherent_on_orbit
    - finiteAxisFoldBCDatumSquare_not_generatedAuthoredDiagnosticMateCoherent
    - finiteAuthoredBCDatumSquare_generatedAuthoredDiagnosticMateCoherent
    - finiteAxisFold_authoredComparison_orbit_nontrivial
  claim_mapping:
    auxiliary_producer: generatedAuthoredDiagnosticComparison is the initial-cochain specialization of the arbitrary-cochain canonical-then-raw-then-unified-fold diagnostic
    auxiliary_relation: GeneratedAuthoredDiagnosticMateCoherentRel compares that diagnostic with authoredSupportCanonicalMate and is explicitly not K2's fixed public relation
    raw_provenance: authoredInitialRawDefectTotal_uses_authoredComparator exposes the actual input.authored.comparator in G-106 raw-defect order
    strict_control: finiteAuthoredBCDatumSquare_generatedAuthoredDiagnosticMateCoherent
    lax_initial_control: finiteAxisFoldBCDatumSquare_not_generatedAuthoredDiagnosticMateCoherent
    full_orbit_auxiliary_equation: finiteAxisFold_not_mateCoherent_on_orbit
    orbit_nontriviality: finiteAxisFold_authoredComparison_orbit_nontrivial
    undischarged_assumptions:
      - K2 authored-table induced comparison and fixed public MateCoherentRel
      - exact bridge from every orbit coordinate to the same public relation
      - actual presentation replacement for both K2 producers
      - fixed-ledger arbitrary-target FiniteModelLift
      - K3 diagnostic base-change action, qualified H_bc package, and positive/negative vanishing pair
      - K4 pullback-square pasting and G-106/G-109 coherence bridge
      - cumulative final assembly and completion review
    acceptance_point: the arbitrary-cochain generated diagnostic and its strict/lax controls are a non-twist predecessor only; K2 is not discharged
    port_status: unported
audits:
  premise_delta:
    discharged:
      - arbitrary cochain raw factor
      - internally generated non-twist fold
      - auxiliary strict/lax diagnostic pair and full nontrivial orbit equation
    remaining:
      - K2 public producer/relation/orbit bridge, actual presentation replacement, FiniteModelLift, K3, K4, and final assembly
  certificate_provenance:
    discharged:
      - beyond the fixed authored comparator table, no additional comparison, diagnostic/fold endomorphism, fold, equality, or noninvertibility certificate is accepted from the caller
      - raw factor comes from the supplied DefectCochain and unified fold from direct or same-boundary pairwise availability
    unresolved:
      - universal provenance forcing the K2 authored comparison
      - public-relation orbit bridge and presentation replacement
  proof_use:
    used:
      - input.authored.comparator through initialRawDefectCochain and explicit proof-use theorem
      - supplied raw component at each orbit coordinate
      - direct-first and same-boundary pairwise fold availability
      - cocartesian universal factor, BC unit, square isomorphism, transport, and selected reindexing
      - identity-route unitors, canonical/raw IsIso instances, and actual EdgeReselection witnesses
    unused: []
  structure_field_escape: none-found
  route_integrity: pass only as an auxiliary diagnostic; rejected as the fixed K2 authored producer
  target_fitting: initial formal review found that the extra non-IsIso postfactor can manufacture mismatch without proving mismatch of the universally induced authored comparison; resolved by removing the public name and K2 discharge claim
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - focused BCAuthoredDiagnosticComparison.lean: pass; 40 namespace declarations, standard axioms only
    - focused BCAuthoredDiagnosticComparisonWitnesses.lean: pass; 9 namespace declarations, standard axioms only
    - targeted builds for exactly the two new modules: pass; no Research aggregate or full build
    - git diff --check and required repository scans: pass before PR
  blocking_findings:
    - Math B Critical: generated non-IsIso postfactor is not uniquely forced by the authored table or universal factorization; resolved by limiting the artifact to an auxiliary diagnostic and withholding K2
    - Math B Major: full-orbit theorem is the cochain-indexed extension rather than the initial auxiliary relation; resolved by correcting claims and retaining the public orbit bridge as open
  next_obligation: construct the authored-table induced comparison through a universal route and an exact public-relation orbit bridge; presentation replacement remains subsequent
review:
  initial_reviewed_head: f08cc2e518c69df35c67475d5fdf607f5f57eadf
  initial_round:
    math_a: no central findings; two report precision issues
    math_b: Critical target-fitting postfactor and Major public-relation orbit gap
    lean_a: no findings
    lean_b: no central findings; same report precision issues
  core_fix:
    - renamed the named producer and relation as generated auxiliary diagnostics and explicitly stated that they are not K2's fixed public MateCoherentRel
    - removed all K2 discharge claims and distinguished initial auxiliary relation failure from full-orbit cochain-indexed equation failure
  post_core_fix_reviewed_head: 70b50c51ac72e85b1353623311343bab0ef99f23
  post_core_fix_round:
    math_a: no findings
    math_b: no central findings; one caller-endomorphism wording issue fixed in the report-only tail
    lean_a: no findings
    lean_b: no findings
  integrated_verdict: pass for the auxiliary generated-diagnostic proof-checkpoint only; K2 public producer/relation/orbit bridge, presentation replacement, FiniteModelLift, K3, K4, final assembly, and G-110 completion are not accepted
  ci: post-core-fix head passed 7 of 7 PR checks
  report_tail_audit:
    reviewed_tail: 04c577d482bed95443344d83c6ac8c9f94ad47af
    protection_scope: no findings; theorem statements and bodies unchanged
    completion_claim_discipline: no findings; auxiliary checkpoint only and K2 remains open
    consistency_traceability: no findings; heads, four-lane summaries, wording fix, CI, and next obligation agree
    public_quality_privacy: no findings
  status: pass
stop_condition: none
next_obligation: merge the auxiliary checkpoint, then construct the universal K2 authored comparison route
```

### Cycle 45 — pairwise diagnostic quotient on the full reselection orbit

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 45
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: f5634c405ce7244af80d1234cbc8edd17d72cd2c
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 44 merge synchronization comment 5384235674 and Cycle 45 fixed selection comment 5384246482
  proof_dag_predecessors:
    - G-106 rawDefectCochain and InReselectionOrbit on the fixed double diamond
    - Cycle 39 packageProjection Beck--Chevalley exactness
    - Cycle 40 exact authored-support routes and canonical mate restriction
    - Cycle 44 diagnostic-generated noninvertible axis fold and exact canonical-comp-fold normalization
  proof_obligation: on the fixed lax double diamond, compare the two facewise raw defects over their common endpoint and identical boundary paths so that the common generated canonical comparator cancels; use the resulting cochain-indexed quotient to generate the named authored-support relation as an initial-cochain specialization, prove its lax failure and strict control together with failure of the cochain-indexed equation over the full InReselectionOrbit, and construct a concrete nontrivial orbit; actual presentation-replacement invariance remains a separate theorem
  selection_reason: Cycle 44 proves a genuine noninvertible diagnostic fold only at the initial representative because a single raw component can lose the object-fixing moved axis. The double-diamond faces have identical boundary paths, so their ordered quotient cancels the common canonical comparator at every coordinate while retaining the authored relative swap. This is the shortest route to the fixed all-orbit K2 negative without introducing a new gauge, arbitrary comparison, fold, or noninvertibility certificate.
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticPairwiseAxisFold.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticPairwiseAxisFoldWitnesses.lean
  risks:
    - defining a new predicate instead of the fixed public MateCoherentRel equation
    - authored twist or an arbitrary noninvertible endomorphism masquerading as the relative obstruction
    - comparing face values that do not share a generated canonical factor
    - proving only the initial coordinate instead of every InReselectionOrbit representative
    - a singleton orbit making the all-orbit theorem vacuous
    - claiming presentation replacement from a group-level common-factor identity
  unchecked:
    - public authored-table MateCoherentRel fidelity outside the fixed double-diamond diagnostic
    - actual presentation replacement for the canonical and authored comparison producers
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: PackageFiberAut.pairwiseRawDefect forms the ordered quotient of two actual DefectCochain components after retagging only along equality of their target packages. PairwiseAxisFoldWitnessAt now additionally requires literal equality of both boundary paths, so arbitrary same-endpoint cells cannot witness common-factor cancellation. commonCanonicalPairwiseQuotient_eq proves that an already identified common right factor cancels, and commonCanonicalPairwiseQuotient_factor_invariant proves only the corresponding group-level factor invariance. generatedPairwiseAxisFoldTotalAt derives the endomorphism and is non-IsIso whenever the typed witness is available. The exact diagnostic comparison is rebuilt at an arbitrary cochain by the selected reindexing functor, cocartesian universal factor, BC unit, square isomorphism, transport, and right reindexing, and normalizes to the reviewed canonical mate followed by the transported generated fold. In the fixed double diamond, both faces have identical boundary paths and the same canonical comparator at every reselection; their quotient is always the adjacent swap. The swap supplies the same concrete moved-axis fold at every coordinate, its via-base image remains non-IsIso, and therefore the auxiliary comparison differs from the canonical mate at every coordinate. finiteAxisFold_pairwise_not_mateCoherent_on_orbit quantifies over every actual InReselectionOrbit representative. A right-edge swap supplies a second raw cochain distinct from the initial cochain, proving orbit nontriviality. The singleton datum is retained only as a diagnostic control. This checkpoint does not claim that DiagnosticPairwiseAxisFoldMateCoherentRel is the fixed public authored-table relation and does not claim actual presentation-replacement invariance.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticPairwiseAxisFold.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticPairwiseAxisFoldWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - PackageFiberAut.pairwiseRawDefect
    - PackageFiberAut.commonCanonicalPairwiseQuotient_eq
    - PackageFiberAut.commonCanonicalPairwiseQuotient_factor_invariant
    - PackageFiberAut.generatedPairwiseAxisFoldTotalAt_not_isIso
    - authoredPairwiseAxisFoldLeftFactor_fac
    - authoredPairwiseAxisFoldLeftFactor_eq_counit_comp_fold
    - authoredPairwiseAxisFoldComparisonComponentAtCochain_eq_canonical_comp_fold
    - DiagnosticPairwiseAxisFoldMateCoherentRel
    - finiteAxisFold_canonicalComparator_faces_eq
    - finiteAxisFold_pairwiseRawDefect_eq_swap
    - finiteAxisFold_pairwiseRawDefect_reselection_invariant
    - finiteAxisFold_pairwise_commonFactor_invariant
    - finiteAxisFold_pairwise_not_mateCoherent_on_orbit
    - finiteAxisFoldBCDatumSquare_not_pairwiseMateCoherent
    - finiteAuthoredBCDatumSquare_pairwiseMateCoherent
    - finiteAxisFold_input_reselectionOrbit_nontrivial
  claim_mapping:
    theorem_names:
      - DiagnosticPairwiseAxisFoldMateCoherentRel
      - finiteAxisFoldBCDatumSquare_not_pairwiseMateCoherent
      - finiteAuthoredBCDatumSquare_pairwiseMateCoherent
      - finiteAxisFold_pairwise_not_mateCoherent_on_orbit
      - finiteAxisFold_input_reselectionOrbit_nontrivial
      - finiteAxisFold_pairwise_commonFactor_invariant
    source_labels:
      - target theorem C diagnostic predecessor on the fixed double diamond
      - target proof artifact full InReselectionOrbit nonvanishing predecessor
    conjuncts:
      - auxiliary initial relation -> DiagnosticPairwiseAxisFoldMateCoherentRel specializes the cochain-indexed diagnostic comparison and reviewed canonical mate to initialRawDefectCochain
      - singleton diagnostic control -> finiteAuthoredBCDatumSquare_pairwiseMateCoherent
      - fixed lax diagnostic -> finiteAxisFoldBCDatumSquare_not_pairwiseMateCoherent
      - full actual orbit -> finiteAxisFold_pairwise_not_mateCoherent_on_orbit
      - orbit nontriviality -> finiteAxisFold_input_reselectionOrbit_nontrivial
      - common-factor algebra -> commonCanonicalPairwiseQuotient_factor_invariant and finiteAxisFold_pairwise_commonFactor_invariant
    undischarged_assumptions:
      - fixed-ledger arbitrary-target FiniteModelLift
      - K3 diagnostic base-change action, qualified H_bc package, and positive/negative vanishing pair
      - K4 pullback-square pasting and G-106/G-109 coherence bridge
      - cumulative final assembly and completion review
      - public authored-table MateCoherentRel with nonvacuous strict/lax fidelity
      - actual presentation-replacement invariance for both named producers
    acceptance_point: the Cycle 45 fixed-double-diamond diagnostic is generated from the actual G-106 raw cochain, remains a non-IsIso fold after transport over every actual reselection, and has a concrete non-singleton orbit; it is a predecessor checkpoint only
    port_status: unported
audits:
  premise_delta:
    discharged:
      - common target package -> finite double-diamond endpoint equality and finiteAxisFold_canonicalComparator_faces_eq
      - all InReselectionOrbit coordinates -> finiteAxisFold_pairwise_not_mateCoherent_on_orbit
      - orbit nontriviality -> finiteAxisFold_input_reselectionOrbit_nontrivial
      - common right-factor cancellation -> commonCanonicalPairwiseQuotient_factor_invariant
    remaining:
      - public authored-table MateCoherentRel and actual presentation replacement
      - FiniteModelLift, K3, K4, and final assembly as listed in claim_mapping
  certificate_provenance:
    discharged:
      - pairwise quotient is computed from the supplied G-106 cochain and endpoint equality
      - finite fold witness is generated from the quotient theorem equating it to the concrete adjacent swap
      - authored comparison and its factor are generated by existing reindexing, transport, adjunction, and cocartesian universal APIs
    unresolved:
      - provenance bridge from actual presentation replacement to the common canonical factor
  proof_use:
    used:
      - both raw cochain face components and their common canonical comparator
      - endpoint equality in castTarget
      - moved-axis swap witness in generated non-IsIso fold
      - both identity-route unitors in transport reflection
      - canonical-mate IsIso in component cancellation
      - InReselectionOrbit witness by elimination to an actual EdgeReselection
    unused: []
  structure_field_escape: none-found
  route_integrity: pass for the fixed diagnostic route; public producer and presentation replacement remain unchecked
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - post-core-fix focused BCDiagnosticPairwiseAxisFold.lean: pass; 48 namespace declarations, standard axioms only
    - post-core-fix focused BCDiagnosticPairwiseAxisFoldWitnesses.lean: pass; 25 namespace declarations, standard axioms only
    - targeted builds for exactly the two changed modules: pass; no Research aggregate or full build
    - git diff --check, focused module manifest, placeholder, hidden/BiDi, and Research import-direction scans: pass
  blocking_findings:
    - initial Math B review refuted the public-relation fidelity claim; resolved by removing the public name and limiting this cycle to the typed fixed-double-diamond diagnostic checkpoint
    - initial Math A/B and Lean A/B reviews found no actual presentation-replacement theorem; resolved for this PR by renaming the group lemma, removing the discharge claim, and returning that bridge to the remaining ledger
    - Lean A requested no-unfold APIs and premise-provenance docstrings; pairwiseRawDefect_eq and strengthened declaration documentation added
  next_obligation: after this checkpoint merges, construct the actual authored-table producer and presentation-replacement bridge required by the public MateCoherentRel
review:
  reviewed_head: ae98249585bb2be843712635542fa1c087eea9b1
  initial_round:
    - Math A, Lean A, and Lean B found the claimed presentation replacement was only a group identity
    - Math B additionally refuted the generic public-relation fidelity by a singleton-support counterexample and missing same-boundary constraint
  core_fix:
    - removed the public MateCoherentRel name and limited the result to DiagnosticPairwiseAxisFoldMateCoherentRel
    - required both boundary paths by HEq in PairwiseAxisFoldWitnessAt
    - renamed replacement claims to group-level factor invariance and returned actual presentation replacement to remaining obligations
    - added pairwiseRawDefect_eq, castTarget_heq, premise-provenance docs, and downstream no-unfold use
    - downgraded the cycle result to proof-checkpoint
  post_core_fix_round:
    math_a: no central findings; one report metadata issue fixed in the report-only tail, and stale PR-body drift was fixed at unchanged reviewed head during review
    math_b: no central findings; one report enum issue fixed in the report-only tail
    lean_a: no central or noncentral findings
    lean_b: no Lean-claim finding; stale PR-body drift was fixed at unchanged reviewed head, and selection-history plus result-enum metadata were fixed in the report-only tail
  integrated_verdict: pass for the fixed-double-diamond full-orbit diagnostic proof-checkpoint only; public authored-table MateCoherentRel, actual presentation replacement, FiniteModelLift, K3, K4, final assembly, and G-110 completion are not accepted
  ci: reviewed head passed 7 of 7 PR checks
  report_tail_audit:
    reviewed_tail: a2fc7e5a208b28e54f177ef75ce97a5394490480
    protection_scope: no findings
    completion_claim_discipline: no findings
    consistency_traceability: initial noncentral lane-summary omission fixed at reviewed_tail; direct reaudit pass
    public_quality_privacy: no findings
  status: pass
stop_condition: none
next_obligation: audit the report-only review tail and merge the Cycle 45 checkpoint; then construct the public authored-table MateCoherentRel and actual presentation-replacement bridge
```

### Cycle 44 — diagnostic axis fold at the initial representative

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 44
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 5893cca6da0ab6771c609e1b73a92faf325de753
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 43 merge synchronization comment 5383944560
  proof_dag_predecessors:
    - F0b2b raw AuthoredBCDatumSquare and exact producer signatures
    - G-106 initialRawDefectCochain as a PackageFiberAut-valued diagnostic action
    - Cycle 40 exact authored-support routes and canonical mate
    - Cycle 43 theorem-level rejection of all universal-factor routes that preserve the raw automorphism
  proof_obligation: construct from a diagnostic PackageFiberAut value a genuinely noninvertible endomorphism by folding one moved signature axis onto its image when the automorphism fixes architecture objects; prove the fold laws, identity specialization, and noninvertibility from its generated axis graph; transport that fold into a cross-route authored comparison without accepting an arbitrary endomorphism or comparison certificate
  selection_reason: Cycle 43 proves that functorially transporting the raw automorphism preserves the forbidden twist class. The shortest route out of that class is to generate a noninvertible map before BC transport. SignedExactCoreReadingHom permits a noninjective axisMap when coordinate and selected-status laws are generated from the same object-fixing automorphism.
  expected_result_type: proof-checkpoint
  risks:
    - arbitrary choice of a noninvertible endomorphism unrelated to the diagnostic action
    - failure of the dependent coordinate law after folding a moved axis
    - fold existence encoded as a caller certificate rather than derived from a concrete lax fixture
    - transport functors failing to reflect the fold's noninvertibility
    - another theorem-level normalization to an automorphism twist
    - target-fitting branch on a fixture identity
  unchecked:
    - whether every reselection in a fixed lax orbit retains an object-fixing moved-axis witness
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: AxisFoldWitness now generates a noninjective signature-axis map, its dependent coordinate equivalence and coordinate law, the complete SignedExactCoreReadingHom, and a PackageTotalHom directly from one object-fixing moved-axis diagnostic automorphism. packageTotalHom_axisMap_injective_of_isIso and total_not_isIso prove that a fold generated under AxisFoldAvailable cannot be an automorphism. generatedAxisFoldTotal selects such an intrinsic witness when it exists and otherwise returns identity; generatedAxisFoldTotal_one proves strict specialization without a caller endomorphism. authoredDiagnosticAxisFoldComponent sends this generated fold into the southwest fiber, authoredDiagnosticAxisFoldLeftFactor generates the left factor by cocartesian universality, and authoredDiagnosticAxisFoldComparison assembles the exact authored-support family. Generically, its normalization is the canonical mate followed by the transported generated fold. For the finite double-diamond fixture specifically, identity edge lifts and identity/swap authored faces live on one decoded three-axis package; its second raw defect is the adjacent swap, AxisFoldAvailable is discharged concretely, the generated via-base fold remains noninvertible through both identity-route unitors, the authored component differs from the canonical mate, and the lax datum refutes DiagnosticAxisFoldMateCoherentRel. Thus this concrete firing is not an automorphism twist. The existing strict authored square fires the same relation. G-106 double-diamond uniqueness also proves no edge reselection can make both faces coherent. The remaining all-orbit gap is exact: a single-cell AxisFoldWitness requires objectMap=id, which arbitrary reselection need not preserve; Cycle 45 must form a pairwise raw-defect quotient that cancels the common reselection action before folding.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticAxisFold.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticAxisFoldWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticAxisFoldComparison.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCDiagnosticAxisFoldComparisonWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - PackageFiberAut.AxisFoldWitness
    - PackageFiberAut.AxisFoldWitness.total_not_isIso
    - PackageFiberAut.generatedAxisFoldTotal_not_isIso
    - PackageFiberAut.generatedAxisFoldTotal_one
    - authoredDiagnosticAxisFoldLeftFactor_fac
    - authoredDiagnosticAxisFoldLeftFactor_eq_counit_comp_fold
    - authoredDiagnosticAxisFoldComparisonComponent_eq_canonical_comp_fold
    - finiteAxisFoldSwap_generated_not_isIso
    - finiteAxisFold_not_coherentizable
    - finiteAxisFold_initialRawDefect_second
    - finiteAxisFold_viaBaseFold_second_not_isIso
    - finiteAxisFoldBCDatumSquare_not_mateCoherent
    - finiteAuthoredBCDatumSquare_diagnosticAxisFoldMateCoherent
  claim_mapping:
    generated_axis_fold: AxisFoldWitness produces the axis map, dependent coordinate data, complete SignedExactCoreReadingHom, and PackageTotalHom; not_injective_axisMap plus packageTotalHom_axisMap_injective_of_isIso proves total_not_isIso when AxisFoldAvailable is discharged
    generic_comparison: initialRawDefectCochain is converted to generatedAxisFoldTotal, reindexed, factored by cocartesian universality, and assembled by authoredDiagnosticAxisFoldComparison; the generic normalization claims only canonical mate followed by the transported generated fold
    lax_negative: finiteAxisFoldSwapWitness discharges AxisFoldAvailable for the second face; the two identity-route unitors reflect IsIso back to the source fold, yielding a non-IsIso transported fold, component inequality, and failure of DiagnosticAxisFoldMateCoherentRel
    strict_positive: the existing finite CoherentAt proof yields identity initial raw defect, hence identity fold and the same DiagnosticAxisFoldMateCoherentRel
    orbit_boundary: finiteAxisFold_not_coherentizable rules out simultaneous face coherence under edge reselection, but does not prove comparison failure for every InReselectionOrbit representative
  premise_audit:
    ambient_boundary:
      - AtomCarrier and DecidableEq on atoms
      - reviewed G-106 raw-defect and double-diamond APIs
      - existing reindex, core-transport, cocartesian-factor, and canonical-mate APIs
    direction_hypothesis:
      - AuthoredBCDatumSquare realization_eq, edgeStrong, endpoint_eq, twoCellBase, and base-change-preceding authored comparator
      - strict specialization hdefect, discharged in the finite control from CoherentAt through the reviewed raw-defect equivalence
    discharge_required:
      - AxisFoldWitness source, moved, objectMap_eq, and axisDecidableEq are used to generate the fold and prove source/image collision
      - AxisFoldAvailable is required only for generic non-IsIso conclusions and is concretely discharged by finiteAxisFoldSwapWitness in the lax firing
      - two identity-route unitors reflect non-IsIso only in the finite fixture; no generic transport-reflection claim is made
    conclusion_equivalent_risk:
      - authored.comparator remains a raw semantic input and does not store a fold, BC comparison, expected equality, or noninvertibility certificate
      - AxisFoldWitness stores a moved source and object-map equality, not the generated endomorphism or its non-IsIso conclusion
      - authored comparator supply alone does not discharge all-orbit comparison failure
  structure_field_escape:
    status: none found
    justification: every material input is consumed along the raw-defect-to-fold-to-factor-to-comparison dependency chain; the strict identity and finite lax non-IsIso conclusions are derived rather than stored as fields
  proof_use:
    - moved proves the generated axisMap is noninjective
    - objectMap_eq turns the diagnostic coordinate law into the dependent coordinate law at a fixed architecture object
    - axisDecidableEq controls the fold branch, while coordinateEquiv and axis_selected_iff generate its coordinate and selected-status fields
    - authored.comparator enters toTransportData, initialRawDefectCochain, generatedAxisFoldTotal, the cocartesian left factor, and the assembled comparison
    - the finite non-IsIso proof consumes both identity-route unitors and the source fold non-IsIso theorem; canonical-mate IsIso supplies cancellation for component inequality
  route_integrity:
    status: checkpoint-only
    anti_twist: the generic theorem makes no noninvertibility claim; the concrete lax firing proves its transported generated fold is non-IsIso
    anti_wrapper: no arbitrary fold, endomorphism, comparison, expected equality, or factorization certificate is accepted from a caller
    unresolved: all InReselectionOrbit representatives, orbit nontriviality, and presentation-replacement invariance remain undischarged
  audits:
    remaining:
      - pairwise raw-defect quotient cancelling the common reselection action
      - nonidentity generated fold and relation failure for every representative in the fixed lax orbit
      - nontrivial orbit witness and presentation-replacement invariance required by K2
      - FiniteModelLift, K3-K4, and final target assembly
  validation:
    - focused BCDiagnosticAxisFold.lean: pass; 35 namespace declarations, standard axioms only
    - focused BCDiagnosticAxisFoldWitnesses.lean: pass; 3 namespace declarations, standard axioms only
    - focused BCDiagnosticAxisFoldComparison.lean: pass; 18 namespace declarations, standard axioms only
    - focused BCDiagnosticAxisFoldComparisonWitnesses.lean: pass; 32 public namespace declarations, standard axioms only
    - targeted lake builds only; no Research aggregate or full build was run
    - git diff --check: pass
  review:
    reviewed_head: 12db0b00c1ce29f7aa2865fb2415bf394ee06e2f
    initial_round: one central report-strength finding and noncentral ledger, docstring, no-unfold, and helper-visibility findings; all were batched into commit 12db0b00c1ce29f7aa2865fb2415bf394ee06e2f
    post_core_fix_round:
      math_a: no major findings
      math_b: no major findings
      lean_a: no major findings
      lean_b: no major findings
    integrated_verdict: pass for the Cycle 44 target-proof-checkpoint only; not K2 or G-110 completion
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4085#issuecomment-5384205384
    ci: 7 of 7 checks successful at reviewed_head, including 5 of 5 branch-required checks
  stop_condition: none
  next_obligation: merge the Cycle 44 proof-checkpoint after standard review, then construct the double-diamond pairwise raw-defect quotient that cancels the common reselection component and prove the generated mismatch on every InReselectionOrbit representative
```

### Cycle 43 — universal-factorization anti-wrapper refutation

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 43
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: dda3848d62ee1816e197e2388c8f825a8b26c1ce
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 43 resumption correction comment 5383772467
  correction: the prior review-stagnation stop was invalid because Cycle 42 had not received its within-cycle central fix and permitted full rerun; the loop therefore resumes from accepted Cycle 40 rather than treating absence of a ready-made API as a stop
  proof_dag_predecessors:
    - F0b2b comparator-free AuthoredSupportContext, raw AuthoredBCDatumSquare, exact producer signatures, and MateCoherentRel equation
    - G-106 initialRawDefectCochain and canonical path comparison generated by strong cocartesian uniqueness
    - Cycle 35 transport/reindex hom equivalence and its IsStronglyCocartesian.map inverse transpose
    - Cycle 37 canonical mate constituents and Cycle 40 exact authored-support routes
  proof_obligation: test whether the most direct missing-structure route is genuine: realize the G-106 initial raw defect in the southwest fiber, reindex it to the northwest fiber, generate a left-leg factor from the cocartesian universal property and its total-morphism equation, assemble the authored BC component from the mate constituents, and perform an explicit anti-wrapper normalization against the completed canonical mate
  selection_reason: target-theorem-loop owns construction of missing intermediate lemmas and factors. Cycle 42 was rejected because its definition was literally a route endomorphism composed with authoredSupportCanonicalMate; Cycle 43 moves raw proof-use inside a universal factor before the BC comparison is assembled.
  expected_result_type: blocker-fixed
  risks:
    - the universal factor being merely a cosmetic wrapper for the rejected direct-route twist
    - accepting a comparison, mate, expected equality, raw defect, or factorization certificate from the caller
    - hiding the raw authored field or canonical G-106 comparator behind an unused projection
    - treating the strict firing as the required lax all-orbit negative
    - promoting this checkpoint to K3-K4, FiniteModelLift, or theorem completion
  unchecked: []
result:
  proposed_result_type: blocker-fixed
  proof_obligation_delta: authoredInitialRawDefectComponent realizes the existing G-106 initial cochain on the exact southwest support. authoredLeftFactor reindexes that component and invokes reindexToCoreTransportHom, whose implementation is IsStronglyCocartesian.map, to generate a vertical factor; authoredLeftFactor_fac records its defining total-morphism equation. The decisive anti-wrapper theorem authoredLeftFactor_eq_counit_comp_rawDefect proves that cocartesian uniqueness forces this allegedly new factor to equal the canonical counit followed by the raw-defect component. After assembly from the unit, square isomorphism, bottom transport, and right reindexing, authoredFactorizationComparisonComponent_eq_canonical_comp_viaRawDefect proves that the entire candidate is exactly the canonical mate followed by the via-base image of the same raw defect. Thus moving the raw automorphism inside a universal factor does not create a genuine non-twist comparison. The strict identity specialization remains valid but cannot discharge the fixed lax-negative obligation. Cycle 43 fixes this route blocker as a reusable Lean normalization theorem and rejects the candidate as the K2 authored producer.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredFactorizationComparison.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredFactorizationComparisonWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - authoredInitialRawDefectTotal
    - authoredInitialRawDefectComponent
    - authoredInitialRawDefectDecodedComponent
    - authoredLeftFactor
    - authoredLeftFactor_fac
    - authoredLeftFactor_eq_counit_comp_rawDefect
    - authoredFactorizationComparisonComponent
    - authoredViaBaseRawDefectComponent
    - authoredFactorizationComparisonComponent_eq_canonical_comp_viaRawDefect
    - authoredFactorizationComparison
    - AttemptedFactorizationMateCoherentRel
    - authoredLeftFactor_eq_counit
    - authoredFactorizationComparison_eq_canonical
    - attemptedFactorizationMateCoherentRel_of_initialRawDefect_eq_identity
    - finiteAuthoredFactorization_coherentAt_identity
    - finiteAuthoredBCDatumSquare_attemptedFactorizationMateCoherentRel
    - finiteAuthoredFactorization_nonempty_support
  claim_mapping:
    source_facts:
      - input.authored.comparator is retained by toTransportData and consumed by initialRawDefectCochain relative to canonicalTwoCellComparator
      - selectedCoreFiberReindexFunctor maps that generated vertical defect into the northwest fiber
      - reindexToCoreTransportHom generates the left factor by the package-specific cocartesian universal property
      - the BC square comparison, unit, and canonical comparison remain independently producer-generated
    consequences:
      - syntactic absence of the completed canonical mate from the component definition is insufficient for route integrity
      - the raw defect participates in the defining factorization equation, but universal uniqueness normalizes that equation to a canonical-mate twist
      - identity raw defect recovers the canonical counit and canonical mate by uniqueness
      - the concrete strict support is inhabited and exercises the complete producer
  premise_audit:
    ambient_boundary:
      - carrier U and DecidableEq U.Atom
      - reviewed G-106 raw-defect API
      - Cycle 35 transport/reindex universal maps and Cycle 40 route definitions
    direction_hypotheses:
      - RealizableSquare and realization_eq
      - AdmissibleLiftData and edgeStrong
      - endpoint_eq and twoCellBase
    conclusion_equivalent_risk:
      - AuthoredBC2CellPresentation.authored.comparator is consumed through initialRawDefectCochain, but the generated factor is not independent: the normalization theorem identifies it with canonical counit composed with the raw automorphism
    theorem_local_conditional_premise:
      - hdefect is used only by the generic identity specialization; the finite strict firing derives it from CoherentAt through coherentAt_iff_rawDefectCochain_eq_identity
    structure_field_escape: none; the failure is route collapse rather than a supplied conclusion field
    proof_use: authored comparator -> toTransportData -> initialRawDefectCochain -> southwest vertical component -> selected reindex map -> IsStronglyCocartesian.map factor -> canonical counit followed by raw defect -> canonical mate followed by via-base raw defect
  route_integrity:
    selected_route: G-106 relative path defect passed through a left-leg universal factor and direct assembly from the mate constituents
    nonvacuity: the factor and full component both have explicit normalization theorems; the strict fixture remains inhabited
    forbidden_route_detected:
      - authoredSupportCanonicalMate is syntactically absent from the component definition but appears after theorem-level normalization
      - the full component is exactly canonical mate composed with a via-route image of the raw PackageFiberAut value
      - the fixed anti-twist and anti-wrapper clauses therefore reject the candidate
  audits:
    discharged:
      - reusable anti-wrapper normalization of the universal-factor route
      - exact identification of the generated left factor and complete comparison with their forbidden canonical-twist normal forms
    remaining:
      - construct a genuinely noninvertible diagnostic-induced comparison rather than another functorial image of PackageFiberAut
      - concrete lax negative with all-reselection nonvanishing and nontrivial orbit witness
      - presentation replacement invariance and final anti-wrapper proof-use audit
      - arbitrary-target FiniteModelLift, K3-K4, and final assembly
  validation_refs:
    - official focused check BCAuthoredFactorizationComparison.lean: pass after normalization audit, 18 declarations and standard axioms only
    - official focused check BCAuthoredFactorizationComparisonWitnesses.lean: pass, 6 declarations and standard axioms only
    - targeted module check BCAuthoredFactorizationComparison: pass; no Research aggregate or full build
  review_refs:
    status: pending independent four-lane review of the blocker-fixed anti-wrapper result
  stop_condition: none
  next_obligation: construct from the diagnostic automorphism action a genuinely noninvertible orbit-fold/collapse morphism on authored support, prove it is not an automorphism twist on a fixed lax fixture, then use it to build the K2 producer and all-orbit negative
```

### Cycle 40 — canonical Beck--Chevalley mate on authored support

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 40
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: b44196671a6708e586ed993151a6996ef527f4c0
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 39 merge synchronization comment 5383099155 and Cycle 40 fail-closed selection comment 5383125159
  scope_correction: the prior report phrase arbitrary endpoint-isomorphism rebasing was not an independently fixed GOAL artifact and was ambiguous among northwest-only apex replacement, four-corner square conjugation, and same-fiber component conjugation; arbitrary semantic replacement also loses the RealizableHom provenance required by the selected reindexing APIs, so no new endpoint-isomorphism schema or semantic-arrow layer was invented
  proof_dag_predecessors:
    - F0b2b AuthoredSupportContext and exact direct/via-base/canonical producer signatures
    - Cycle 37 exact canonical Beck--Chevalley mate over every BCPresentation
    - Cycle 39 canonical mate exactness and four-noninvertible-leg control
    - existing nonempty finite authored-support context and raw-table boundary witness
  proof_obligation: for every comparator-free AuthoredSupportContext, generate the exact direct route by restricting the Cycle 37 source functor along supportFunctor; generate the exact via-base route similarly; inhabit CanonicalMateRestrictionSignature by restricting the exact canonical mate without inspecting the authored comparator; expose each component through a named decoded support object and direct use of RealizableSquare.realization_eq; inherit Cycle 39 IsIso; fire a component on the existing nonempty authored support while retaining the four-noninvertible-leg exactness fixture as a separate control
  selection_reason: the fixed GOAL and BCRelativeSchema already determine the authored-support route and canonical restriction types, making them the shortest well-typed predecessor of the authored induced comparison and MateCoherentRel; endpoint rebasing had no single fixed quantification and was not required because every AuthoredSupportContext already contains exact RealizableSquare provenance
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredSupportCanonicalMate.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredSupportCanonicalMateWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - accepting either route, a natural transformation, mate, comparison, unit, counit, endpoint isomorphism, or exactness certificate from a caller
    - inspecting input.authored or an authored comparator on the canonical side
    - hiding RealizableSquare endpoint alignment behind a whole-functor equality cast
    - inventing a new endpoint-isomorphism schema outside the fixed GOAL
    - claiming the identity authored-support fixture itself has four noninvertible legs
    - promoting this restriction checkpoint to the authored induced comparison, MateCoherentRel, orbit invariance, K3-K4, FiniteModelLift, or G-110 completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  content_head: d448f19daddefe2f0e83f4d0be4c99e1b27ca4df
  review_target_head: 1fd5eb6201cf55462d431a765856d7c9bbec653a
  proof_obligation_delta: For every comparator-free AuthoredSupportContext, Cycle 40 destructs only its RealizableSquare provenance and consumes realization_eq to identify the semantic square with the exact decoded BCPresentation. The direct route is supportFunctor followed by the selected left-projection reindexing and top transport; the via-base route is supportFunctor followed by bottom transport and selected right-leg reindexing. These definitions inhabit the two fixed AuthoredSupportRouteFamily signatures. Whiskering the Cycle 37 canonical mate with the discrete support functor produces the fixed CanonicalMateRestrictionSignature and depends on no authored values. Because the semantic and decoded southwest fibers are propositionally rather than definitionally equal, authoredSupportDecodedObject names the exact decoded object and the application theorem records the component correspondence by HEq after direct realization_eq elimination instead of a whole-functor cast. Componentwise Cycle 39 exactness makes the restricted natural transformation IsIso. The existing finite authored fixture supplies one actual support cell whose restricted component is IsIso. A separate theorem re-exports the symmetric Cycle 39 producer pullback, all four non-IsIso legs, and canonical exactness without conflating the two fixtures. No authored induced comparison or MateCoherentRel is claimed.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredSupportCanonicalMate.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCAuthoredSupportCanonicalMateWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - authoredSupportDirectRoute
    - authoredSupportViaBaseRoute
    - authoredSupportDirectRouteFamily
    - authoredSupportViaBaseRouteFamily
    - authoredSupportCanonicalMate
    - authoredSupportCanonicalMateFamily
    - authoredSupportDecodedObject
    - authoredSupportCanonicalMate_app_heq
    - authoredSupportCanonicalMate_isIso
    - finiteAuthoredSupportDirectRoute
    - finiteAuthoredSupportViaBaseRoute
    - finiteAuthoredSupportCanonicalMate
    - finiteAuthoredSupportCanonicalMate_component_heq
    - finiteAuthoredSupportCanonicalMate_component_isIso
    - finiteAuthoredSupport_separate_four_leg_exactness_control
  claim_mapping:
    theorem_names:
      - authoredSupportCanonicalMate_app_heq
      - authoredSupportCanonicalMate_isIso
      - finiteAuthoredSupportCanonicalMate_component_heq
      - finiteAuthoredSupportCanonicalMate_component_isIso
      - finiteAuthoredSupport_separate_four_leg_exactness_control
    source_labels:
      - target theorem (C) authored-support induced comparison and MateCoherentRel predecessor
      - F0b2b exact producer signatures
      - Cycle 37 canonical mate predecessor
      - Cycle 39 exactness predecessor
    conjuncts:
      - exact direct and via-base route families are generated for every comparator-free authored support
      - the canonical mate restricts to the same support without reading the raw authored table
      - every restricted component is the exact decoded producer component and is invertible
      - one nonempty authored cell fires the component while a separate fixture retains four noninvertible square legs
    undischarged_assumptions:
      - authored pointwise-table induced comparison with direct raw-field proof-use
      - public MateCoherentRel over the two named producers
      - strict positive and lax negative pair, presentation replacement invariance, full reselection-orbit nonvanishing, and nontrivial orbit witness
      - fixed-ledger arbitrary-target FiniteModelLift
      - K3 diagnostic base-change action, H_bc condition package, and positive/negative vanishing pair
      - K4 pullback-square pasting and G-106/G-109 coherence bridge
      - final (A)-(E) assembly, cumulative premise audit, and completion four-lane review
  dependency_dag:
    - comparator-free AuthoredSupportContext plus realization_eq -> exact decoded BCPresentation and supportFunctor
    - supportFunctor plus left selected reindexing plus top transport -> authored direct route
    - supportFunctor plus bottom transport plus right selected reindexing -> authored via-base route
    - supportFunctor whiskered with Cycle 37 canonical mate -> canonical authored-support comparison
    - Cycle 39 component IsIso -> restricted component IsIso -> restricted NatTrans IsIso
    - nonempty finite authored cell -> actual restricted component firing
    - separate symmetric Cycle 39 fixture -> producer pullback plus four noninvertible legs plus exact mate
  premise_audit:
    direction_hypotheses:
      - comparator-free AuthoredSupportContext, whose fixed fields are a RealizableSquare, G-106 lift geometry, and endpoint incidence equalities
    discharge_required_consumed:
      - RealizableSquare.realization_eq
      - typed left/right RealizableHom values from the exact BCPresentation
      - Cycle 37 canonical mate
      - Cycle 39 canonical mate component exactness
    conclusion_equivalent_inputs: none
    structure_field_escape: none; AuthoredSupportContext contains no route, natural transformation, mate, comparison, exactness, or endpoint-isomorphism field, and the canonical producer does not accept AuthoredBCDatumSquare or inspect input.authored
    proof_use: both route definitions destruct the exact realization_eq; the canonical restriction directly whiskers coreBeckChevalleyMate; the HEq component theorem again eliminates realization_eq; the IsIso instance directly consumes coreBeckChevalleyMate_app_isIso
  route_integrity:
    selected_route: exact BCPresentation stored by RealizableSquare, fixed selected left/right reindexing functors, G-109 top/bottom transports, and Cycle 37 canonical mate
    provenance: comparator-free authored support plus exact realization provenance; no endpoint-isomorphism or semantic replacement schema is introduced
    nonvacuity: the finite authored category contains the named diagnostic cell and its actual canonical component is IsIso; four noninvertible square legs remain verified on the distinct symmetric Cycle 39 control
    forbidden_routes_absent:
      - no caller route, natural transformation, mate, comparison, unit/counit, endpoint iso, or exactness certificate
      - no raw authored comparator access on the canonical side
      - no whole-functor equality cast
      - no invented endpoint-rebase schema
      - no combined-fixture overclaim
      - no authored comparison, MateCoherentRel, orbit, K3-K4, FiniteModelLift, or completion claim
  regression_scenarios:
    canonical_reads_authored: rejected; the producer quantifies only over AuthoredSupportContext and cannot access AuthoredBCDatumSquare.authored
    supplied_routes: rejected; both fixed route families are named definitions generated from the exact four legs
    hidden_endpoint_cast: rejected; a named decoded object and HEq theorem expose the sole realization_eq transport
    empty_support: rejected; the concrete Category is inhabited by FiniteBCDiagnosticCell.cell and the exact component IsIso is instantiated there
    combined_fixture_overclaim: rejected; the witness module explicitly keeps nonempty authored support and four-noninvertible-leg exactness as separate controls
    scope_invention: rejected; endpoint-isomorphism rebasing is recorded as an unfixed ambiguous report phrase and no new schema is introduced
  verification:
    - focused direct check BCAuthoredSupportCanonicalMate.lean: pass; 9 namespace declarations, standard axioms only
    - targeted module BCAuthoredSupportCanonicalMate: pass
    - focused direct check BCAuthoredSupportCanonicalMateWitnesses.lean: pass; 8 namespace declarations, standard axioms only
    - targeted module BCAuthoredSupportCanonicalMateWitnesses: pass
    - exact G-110 umbrella module ResearchLean.AG.DoctrineFiberProduct: pass
    - placeholder/unsafe/new-axiom scan on both exact files: clean
    - hidden/BiDi and private-path scan on both exact files: clean
    - Formal to ResearchLean import-direction scan: no new reverse import
    - Research aggregate/full build: not run, per hard rule
  review:
    exact_head: 1fd5eb6201cf55462d431a765856d7c9bbec653a
    four_lane_result: Math A, Math B, Lean A, and Lean B independently passed with no central or noncentral findings
    refutation_attempts: route orientation, unused realization provenance, authored-comparator dependence, caller route or mate certificate, hidden whole-functor cast, HEq weakening, IsIso transport circularity, empty support, combined-fixture overclaim, invented endpoint-rebase schema, axiom and dependency hygiene, and scope/ledger completeness were checked and rejected
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4081#issuecomment-5383159859
    ci: 7 of 7 checks passed, including lake build, research integrity gates, tooling checks, and Workers build
    status: accepted canonical authored-support restriction proof-checkpoint; G-110 completion remains no
next:
  proof_obligation: generate the authored comparison from the raw pointwise table on the fixed support with direct authored-field proof-use, then define MateCoherentRel from the authored and canonical named producers; strict/lax and orbit obligations remain later nodes
```

### Cycle 39 — package-projection Beck--Chevalley exactness

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 39
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: a0b17d373715ccb6b0a2528f26ef6dc8022a3948
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 38 merge synchronization comment 5382985835 and Cycle 39 selection comment 5383012575
  proof_dag_predecessors:
    - G-110 arbitrary-target inverseCorePackageHom with its generated upper two-sided inverse and cancellation laws
    - Cycle 35 generated package transport/reindexing adjunction, unit, counit, and universal properties
    - Cycle 37 unit-square-counit canonical mate expansion
    - Cycle 38 arbitrary-cleavage mate comparison and selected normalization
  proof_obligation: derive packageProjection-specific invertibility of the generated unit and counit components from explicit upper inverses and the cartesian/cocartesian universal properties; prove the Cycle 37 canonical mate IsIso for every BCPresentation by consuming its unit-square-counit expansion; transport exactness to every arbitrary-cleavage mate through the Cycle 38 comparison; fire both conclusions on one producer-derived finite pullback whose four legs are all noninvertible
  selection_reason: Cycle 38 left packageProjection-specific exactness as the immediate open K2 subnode, while the realized total-hom inverse data, generated adjunction, explicit mate expansion, and arbitrary-cleavage comparison already supplied the required proof route without an exactness certificate
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/PackageProjectionBeckChevalleyExactness.lean
    - ResearchLean/AG/DoctrineFiberProduct/PackageProjectionBeckChevalleyExactnessWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - inferring mate invertibility from pullbackness or pseudofunctor coherence alone
    - leaving IsIso, adjunction equivalence, inverse, exactness, or mate certificates as caller premises of the public unit/counit or mate exactness route
    - proving only the selected-cleavage mate rather than every arbitrary-cleavage mate
    - leaving one or more finite control legs invertible
    - promoting package-specific exactness to arbitrary endpoint rebasing, MateCoherentRel, K3-K4, FiniteModelLift, or G-110 completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  content_head: 85aecf5287b1f22e14bc60fe0eb4365c459e9710
  review_target_head: f3954e288b4631ffced09ce1b329d7268866c095
  proof_obligation_delta: Cycle 39 first proves a generic criterion saying that a package total hom supplied with a two-sided inverse of its complete upper map is strongly cocartesian. It then discharges that criterion specifically for the G-110 arbitrary-target strongCartesianLiftOfTarget construction by using inverseCorePackageBackwardUpper and its two generated cancellation theorems; SignedExactCoreReadingHom itself carries no inverse field. The generated selected cartesian lift is compared to that explicit cocartesian lift through cartesian uniqueness, so it is also strongly cocartesian. Conversely, the support lift used by the counit is proved strongly cartesian. Over identity base maps, these two universal-property packages produce total isomorphisms, and the total-to-fiber reflection theorem yields IsIso for every component of the generated unit and counit. The Cycle 37 component formula then expresses the canonical mate as generated unit, mapped square isomorphism, and generated counit, so every component and hence the natural transformation are IsIso. Cycle 38 selected comparison transports this result to every arbitrary-cleavage mate. A symmetric three-to-two cospan generates an actual pullback whose bottom, right, left, and top legs are all proved noninvertible; both canonical and arbitrary-cleavage exactness fire on this single control. No caller exactness or invertibility certificate is consumed.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/PackageProjectionBeckChevalleyExactness.lean
    - ResearchLean/AG/DoctrineFiberProduct/PackageProjectionBeckChevalleyExactnessWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - packageTotalHom_isStronglyCocartesian_of_upper_inverse
    - packageTotalHom_isStronglyCocartesian_of_upper_inverse_lift
    - strongCartesianLiftOfTarget_isStronglyCocartesian
    - selectedCoreFiberCartesianLift_isStronglyCocartesian
    - coreFiberHom_isIso_of_total_isIso
    - coreFiberLift_isStronglyCartesian_support
    - coreTransportReindexUnit_app_isIso
    - coreTransportReindexCounit_app_isIso
    - coreTransportReindexUnit_isIso
    - coreTransportReindexCounit_isIso
    - coreBeckChevalleyMate_app_isIso
    - coreBeckChevalleyMate_isIso
    - coreBeckChevalleyCleavageMate_isIso
    - finiteBCExactness_isPullback
    - finiteBCExactness_bottom_not_isIso
    - finiteBCExactness_right_not_isIso
    - finiteBCExactness_left_not_isIso
    - finiteBCExactness_top_not_isIso
    - finiteBCExactnessMate_isIso
    - finiteBCExactnessCleavageMate_isIso
  claim_mapping:
    theorem_names:
      - selectedCoreFiberCartesianLift_isStronglyCocartesian
      - coreTransportReindexUnit_app_isIso
      - coreTransportReindexCounit_app_isIso
      - coreBeckChevalleyMate_isIso
      - coreBeckChevalleyCleavageMate_isIso
      - finiteBCExactnessMate_isIso
      - finiteBCExactnessCleavageMate_isIso
    source_labels:
      - target theorem (C) Beck--Chevalley mate exactness
      - G-110 arbitrary-target inverseCorePackageHom and cancellation-law predecessor
      - Cycle 35 generated adjunction predecessor
      - Cycle 37 canonical mate component predecessor
      - Cycle 38 arbitrary-cleavage comparison predecessor
    conjuncts:
      - generated package transport/reindexing unit and counit are componentwise invertible
      - canonical Beck--Chevalley mate is invertible for every validated BCPresentation
      - the corresponding mate is invertible for every pair of arbitrary cartesian cleavages
      - one producer-derived finite pullback has all four legs noninvertible and fires both results
    undischarged_assumptions:
      - arbitrary endpoint-isomorphism rebasing beyond the exact producer endpoint bridge
      - authored-support induced comparison, MateCoherentRel positive/negative pair, full-orbit invariance, and nontrivial orbit witness
      - fixed-ledger arbitrary-target FiniteModelLift
      - K3 diagnostic base-change action, H_bc condition package, and positive/negative vanishing pair
      - K4 pullback-square pasting and G-106/G-109 coherence bridge
      - final (A)-(E) assembly, cumulative premise audit, and completion four-lane review
  dependency_dag:
    - generated inverseCorePackage upper inverse -> explicit strongly cocartesian arbitrary-target lift -> selected lift comparison -> selected lift strongly cocartesian
    - selected lift over the realized base is strongly cartesian and strongly cocartesian -> generated unit component is strongly cartesian over identity -> total IsIso -> fiber IsIso
    - support lift over the realized base is strongly cocartesian and strongly cartesian -> generated counit component is strongly cocartesian over identity -> total IsIso -> fiber IsIso
    - unit IsIso plus mapped square IsIso plus counit IsIso -> canonical mate component IsIso -> canonical mate IsIso
    - Cycle 38 arbitrary-to-selected comparison plus selected mate IsIso -> arbitrary-cleavage mate IsIso
    - symmetric finite cospan producer plus projection bridges -> four noninvertible legs and exactness firing
  premise_audit:
    direction_hypotheses:
      - validated BCPresentation; arbitrary-cleavage theorem additionally quantifies over the two cleavage values
    discharge_required_consumed:
      - the generated inverseCorePackageBackwardUpper and its two cancellation theorems for each arbitrary-target lift
      - generated cartesian and cocartesian universal properties
      - Cycle 35 unit and counit components
      - Cycle 37 unit-square-counit mate expansion
      - Cycle 38 arbitrary-to-selected mate comparison
    conclusion_equivalent_inputs: none
    structure_field_escape: none on the public exactness route; the generic cocartesian criterion explicitly takes an upper inverse and two equations, and its sole concrete arbitrary-target use discharges all three from inverseCorePackageHom before the certificate-free unit/counit and mate theorems
    proof_use: upper inverse equations prove factor and uniqueness for cocartesianness; cartesian uniqueness transports that structure to the selected lift; identity-base universal properties construct the unit and counit inverses; the mate proof rewrites by the explicit component formula; arbitrary-cleavage exactness cancels the generated Cycle 38 comparison
  route_integrity:
    selected_route: exact decoded BCPresentation, realized packageProjection total morphisms, generated Cycle 35 adjunction, Cycle 37 mate, and Cycle 38 comparison
    provenance: G-110 inverseCorePackageHom, its generated backward upper hom and cancellation laws, and reviewed generated universal properties; the finite witness is produced from the symmetric finite cospan and the existing pointed-pullback bridge
    nonvacuity: the symmetric three-to-two control is an actual producer-derived pullback and each of its four structural legs is noninvertible
    forbidden_routes_absent:
      - no exactness, IsIso, inverse, adjunction-equivalence, mate, or comparison certificate input to the public unit/counit and Beck--Chevalley exactness theorems
      - no derivation from pullbackness or coherence alone
      - no selected-cleavage-only conclusion
      - no invertible-leg control
      - no endpoint rebasing, MateCoherentRel, K3-K4, FiniteModelLift, or completion claim
  regression_scenarios:
    pullback_implies_exactness: rejected; the proof uses package upper inverses and both universal-property directions before invoking the mate formula
    supplied_inverse: rejected; every inverse is generated from the existing package total hom or universal property
    selected_only: rejected; coreBeckChevalleyCleavageMate_isIso quantifies over arbitrary left and right cleavages
    degenerate_control: rejected; four separate non-IsIso theorems cover bottom, right, left, and top
    completion_overclaim: rejected; completion_candidate remains no and all later obligations remain explicit
  verification:
    - focused direct check PackageProjectionBeckChevalleyExactness.lean: pass; 14 namespace declarations, standard axioms only
    - targeted module PackageProjectionBeckChevalleyExactness: pass
    - focused direct check PackageProjectionBeckChevalleyExactnessWitnesses.lean: pass; 11 namespace declarations, standard axioms only
    - targeted module PackageProjectionBeckChevalleyExactnessWitnesses: pass
    - exact G-110 umbrella module ResearchLean.AG.DoctrineFiberProduct: pass
    - placeholder/unsafe/new-axiom scan on both exact files: clean
    - hidden/BiDi and private-path scan on both exact files: clean
    - Formal to ResearchLean import-direction scan: no new reverse import
    - Research aggregate/full build: not run, per hard rule
  review:
    exact_head: f3954e288b4631ffced09ce1b329d7268866c095
    four_lane_result: Math A, Math B, Lean A, and Lean B independently passed after the sole initial inverse-provenance documentation finding was integrated and all four lanes re-reviewed the corrected exact head
    refutation_attempts: generic mates preserving IsIso, pullbackness or coherence alone implying exactness, upper-inverse field or caller-certificate escape, circular unit/counit IsIso, mate orientation, selected-only weakening, arbitrary-cleavage cancellation direction, invertible or split finite controls, axiom and dependency hygiene, and scope/ledger completeness were checked and rejected
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4080#issuecomment-5383082087
    ci: 7 of 7 checks passed, including lake build, research integrity gates, tooling checks, and Workers build
    status: accepted package-projection Beck--Chevalley exactness proof-checkpoint; G-110 completion remains no
next:
  proof_obligation: construct arbitrary endpoint-isomorphism rebasing for the package Beck--Chevalley mate without changing the fixed exact producer endpoint; authored-support MateCoherentRel and later K3-K4 obligations remain separate
```

### Cycle 38 — canonical mate independence under arbitrary cleavages

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 38
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: f05a69bc9300f2cb6e1ea91787c898e8b7f39b62
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 37 merge synchronization comment 5382888528 and Cycle 38 selection comment 5382907491
  proof_dag_predecessors:
    - Cycle 33 canonical comparison between arbitrary cartesian cleavages
    - Cycle 36 arbitrary-cleavage adjunction, unit, counit, and hom-equivalence compatibility
    - Cycle 37 selected-cleavage canonical Beck--Chevalley mate and asymmetric finite square
  proof_obligation: for every BCPresentation and arbitrary cleavages on pi1 and sigma2, generate the mate from the Cycle 36 adjunctions and the Cycle 37 square; expose its unit-square-counit component and naturality; prove pairwise mate comparison by consuming the Cycle 36 counit and hom-equivalence comparison laws; normalize every arbitrary mate to the Cycle 37 selected mate; separately fire visible cleavage choice and noninvertible-leg controls without claiming that one fixture has both properties
  selection_reason: Cycle 37 left mate-level cleavage independence as the immediate open K2 subnode, while Cycles 33 and 36 already supplied the exact generated comparison laws needed to discharge it without caller certificates
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CoreBeckChevalleyMateCleavageIndependence.lean
    - ResearchLean/AG/DoctrineFiberProduct/CoreBeckChevalleyMateCleavageIndependenceWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - accepting a square, adjunction, mate, or cleavage-comparison certificate from a caller
    - proving only selected-cleavage specialization rather than arbitrary-cleavage pairwise comparison
    - ignoring either the left counit comparison or right hom-equivalence comparison
    - overclaiming a single finite fixture with both visible cleavage difference and noninvertible reindexing legs
    - inferring mate IsIso or packageProjection exactness from pullbackness and coherence
    - promoting this checkpoint to endpoint rebasing, MateCoherentRel, K3-K4, FiniteModelLift, or G-110 completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  content_head: 7b0e17664821e3da8201c78df490894387ca5ebc
  review_target_head: 9e04152c20ac308ea20708f0f5571363da3e9e68
  proof_obligation_delta: For every validated BCPresentation and every pair of cartesian cleavages on the exact pi1 and sigma2 semantic legs, Cycle 36 generates both adjunctions and Cycle 37 supplies the covariant square, so mateEquiv constructs the fixed-orientation mate without caller categorical certificates. Named theorems expose the unit-square-counit component, naturality, and right-adjunction transpose. For any two pairs of cleavages, square naturality and the Cycle 36 left-counit and right-hom-equivalence comparison theorems prove the canonical mate comparison. Generated arbitrary-to-selected bridges then normalize every such mate to the Cycle 37 mate. One finite identity-square control uses the reviewed literal and twisted right cleavages, exposes their visibly nonidentity comparison, and fires naturality on a nonidentity axis swap. A separate asymmetric control specializes normalization while retaining noninvertible pi1 and sigma2. The controls are deliberately not conflated. No mate invertibility or exactness conclusion is claimed.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CoreBeckChevalleyMateCleavageIndependence.lean
    - ResearchLean/AG/DoctrineFiberProduct/CoreBeckChevalleyMateCleavageIndependenceWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - bcLeftInput
    - bcRightInput
    - coreBeckChevalleyCleavageMate
    - coreBeckChevalleyCleavageMate_app
    - coreBeckChevalleyCleavageMate_naturality
    - coreBeckChevalleyCleavageMate_homEquiv
    - coreBeckChevalleyCleavageMate_comparison
    - coreBeckChevalleyMate_homEquiv
    - bcRightAdjunction_homEquiv_apply
    - coreBeckChevalleyCleavageMate_selectedComparison
    - finiteIdentityCoreBeckChevalleyMate_comparison
    - finiteIdentityMateRightComparison_axis_zero
    - finiteIdentityLiteralCoreBeckChevalleyMate_axisSwap_naturality
    - finiteIdentityMate_axisSwap_ne_id
    - finiteCanonicalSelectedCleavageMate_comparison
    - finiteCanonicalSelectedCleavageMate_left_not_isIso
    - finiteCanonicalSelectedCleavageMate_right_not_isIso
  claim_mapping:
    theorem_names:
      - coreBeckChevalleyCleavageMate_comparison
      - coreBeckChevalleyCleavageMate_selectedComparison
      - finiteIdentityMateRightComparison_axis_zero
      - finiteIdentityMate_axisSwap_ne_id
      - finiteCanonicalSelectedCleavageMate_left_not_isIso
      - finiteCanonicalSelectedCleavageMate_right_not_isIso
    source_labels:
      - target theorem (C) cleavage-independent canonical-mate artifact
      - Cycle 33 cleavage-comparison predecessor
      - Cycle 36 arbitrary-adjunction compatibility predecessor
      - Cycle 37 selected canonical-mate predecessor
    conjuncts:
      - every pair of arbitrary cleavages on the two reindexing legs generates a fixed-orientation mate
      - every two such pairs are related by the canonical left and right cleavage comparisons
      - every arbitrary mate normalizes to the selected Cycle 37 mate
      - finite controls separately witness genuine choice difference and noninvertible reindexing legs
    undischarged_assumptions:
      - packageProjection-specific Beck--Chevalley exactness support and a positive IsIso theorem
      - arbitrary endpoint-isomorphism rebasing beyond the exact producer endpoint bridge
      - authored-support induced comparison, MateCoherentRel positive/negative pair, full-orbit invariance, and nontrivial orbit witness
      - fixed-ledger arbitrary-target FiniteModelLift
      - K3 diagnostic base-change action, H_bc condition package, and positive/negative vanishing pair
      - K4 pullback-square pasting and G-106/G-109 coherence bridge
      - final (A)-(E) assembly, cumulative premise audit, and completion four-lane review
  dependency_dag:
    - BCPresentation plus arbitrary pi1/sigma2 cleavages -> Cycle 36 adjunctions plus Cycle 37 square -> mateEquiv -> arbitrary-cleavage mate
    - left Cycle 33 comparison plus Cycle 36 counit compatibility plus square naturality -> left side of pairwise mate comparison
    - right Cycle 36 hom-equivalence compatibility -> right side of pairwise mate comparison
    - arbitrary-to-selected bridges plus selected transpose formula -> normalization to Cycle 37 mate
  premise_audit:
    direction_hypotheses:
      - validated BCPresentation and two arbitrary CoreFiberCartesianCleavage values on each exact reindexing leg
    discharge_required_consumed:
      - Cycle 33 canonical cleavage comparisons
      - Cycle 36 generated arbitrary adjunctions, counit comparison, and hom-equivalence comparison
      - Cycle 37 generated covariant square and selected mate
    conclusion_equivalent_inputs: none
    structure_field_escape: none; no square comparison, adjunction, unit, counit, mate, or mate-comparison certificate is an input field
    proof_use: mateEquiv consumes the generated arbitrary adjunctions and square; pairwise comparison rewrites through the generated left counit comparison and right transpose comparison; selected normalization consumes both generated arbitrary-to-selected bridges
  route_integrity:
    selected_route: exact decoded BCPresentation legs, generated arbitrary-cleavage adjunctions, and the exact Cycle 37 square comparison
    provenance: reviewed Cycles 33, 36, and 37 declarations; the finite witnesses reuse reviewed raw fixtures and add no categorical certificate fields
    nonvacuity: the identity control has a right comparison that moves axis zero to axis one and a nonidentity vertical map; the separate asymmetric control has both reindexing legs noninvertible
    forbidden_routes_absent:
      - no caller square, adjunction, mate, or comparison certificate
      - no functor equality cast replacing generated natural isomorphisms
      - no combined-fixture claim
      - no mate IsIso, exactness, rebasing, MateCoherentRel, K3-K4, or completion claim
  regression_scenarios:
    selected_only: rejected; the public mate and pairwise theorem quantify over arbitrary left and right cleavages
    unused_predecessor: rejected; the proof explicitly consumes Cycle 36 counit and hom-equivalence comparison theorems
    hand_authored_comparison: rejected; both sides use generated CoreFiberCartesianCleavage.comparison or arbitrary-to-selected bridges
    combined_fixture_overclaim: rejected; visible choice difference and noninvertible legs remain in distinct controls
    exactness_from_coherence: rejected; completion_candidate remains no and packageProjection exactness stays explicit
  verification:
    - focused direct check CoreBeckChevalleyMateCleavageIndependence.lean: pass; 10 namespace declarations, standard axioms only
    - targeted module CoreBeckChevalleyMateCleavageIndependence: pass
    - focused direct check CoreBeckChevalleyMateCleavageIndependenceWitnesses.lean: pass; 14 namespace declarations, standard axioms only
    - targeted module CoreBeckChevalleyMateCleavageIndependenceWitnesses: pass
    - exact G-110 umbrella module ResearchLean.AG.DoctrineFiberProduct: pass
    - placeholder/unsafe/new-axiom scan on both exact files: clean
    - hidden/BiDi and private-path scan on both exact files: clean
    - Formal to ResearchLean import-direction scan: no new reverse import
    - Research aggregate/full build: not run, per hard rule
  review:
    exact_head: 9e04152c20ac308ea20708f0f5571363da3e9e68
    four_lane_result: Math A, Math B, Lean A, and Lean B independently passed with no central or noncentral findings
    refutation_attempts: mate and whisker orientation, selected-only weakening, unused Cycle 36 predecessor, caller certificate escape, arbitrary-to-selected bridge direction, combined-fixture overclaim, exactness or IsIso promotion, axiom and dependency hygiene, and ledger completeness were all checked and rejected
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4079#issuecomment-5382972825
    ci: 7 of 7 checks passed, including lake build and research integrity gates
    status: accepted arbitrary-cleavage canonical-mate proof-checkpoint; G-110 completion remains no
next:
  proof_obligation: prove packageProjection-specific Beck--Chevalley exactness support and a positive IsIso theorem without deriving either from pullbackness or pseudofunctor coherence alone; arbitrary endpoint-isomorphism rebasing remains a separate open obligation
```

### Cycle 37 — producer-anchored canonical core Beck--Chevalley mate

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 37
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 7bb3d26c475254a1b1b612b3e4e8a341ebb7e016
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 36 merge synchronization comment 5382741864, Cycle 37 selection comment 5382772472, and witness refinement comment 5382800375
  proof_dag_predecessors:
    - Cycle 30 generic pointedPullback and pointedPullback_isPullback producer
    - G-109 reviewed covariant core transport functor and compositor
    - Cycle 35 producer-derived core transport/reindexing adjunction, unit, counit, and triangles
  proof_obligation: for every validated BCPresentation, generate the exact pointed finite-code pullback bridge and transport the Cycle 30 pullback theorem to the decoded four-leg square; construct the covariant square isomorphism from the two G-109 compositors and decoded commutativity; apply Mathlib mateEquiv to the two Cycle 35 selected adjunctions to generate the fixed-orientation selected-cleavage canonical mate; expose its unit/compositor-square/counit component and naturality; fire the surface on a finite square with noninvertible relevant reindexing legs and a genuine nonidentity vertical map
  selection_reason: the producer-derived selected reindexing, coherence, and adjunction predecessors were accepted, making construction of the selected-cleavage canonical mate the shortest open K2 subnode; Cycle 36 supplies the separate adjunction-level comparison predecessor that a later mate-level cleavage-independence theorem must still consume
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CoreBeckChevalleyMate.lean
    - ResearchLean/AG/DoctrineFiberProduct/CoreBeckChevalleyMateWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - accepting an endpoint isomorphism, pullback certificate, square comparison, adjunction, unit, counit, or mate component from a caller
    - replacing the producer-anchored finite-code bridge by arbitrary endpoint rebasing or a whole-functor equality cast
    - reversing the fixed mate orientation or hiding the unit/counit provenance behind a hand-authored natural transformation
    - inferring IsIso or packageProjection exactness from pullbackness and bifibration coherence alone
    - firing only on invertible legs or identity vertical maps
    - promoting this mate-construction checkpoint to MateCoherentRel, K3-K4, FiniteModelLift, or G-110 completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  content_head: 8ef650ccaf284154587fc1873dcb2bb55e6f79f1
  review_target_head: 390f9abf17b207ecdb4e4e788c041c98f3ce8fb6
  proof_obligation_delta: The decoded finite-code pullback is connected to the Cycle 30 generic pointed pullback by the producer-generated doctrine isomorphism plus an internally proved selected-point equation. Both projection graphs transport pointedPullback_isPullback to the exact four decoded legs of every BCPresentation. The top/right and left/bottom typed composite presentations decode to the same semantic arrow by generated square commutativity; the G-109 compositors and typed presentation comparison therefore form the covariant square isomorphism. Mathlib mateEquiv consumes this isomorphism and the Cycle 35 selected adjunctions on pi1 and sigma2 to construct the fixed mate `(pi2)_! (pi1)^* -> (sigma2)^* (sigma1)_!`. A named component theorem exposes the right-leg unit, mapped square comparison, and mapped left-leg counit, and a separate theorem exposes naturality on every vertical source-fiber map. The asymmetric finite witness uses identity/support versus selective-two/support; both the generated pi1 and sigma2 are proved noninvertible, while naturality fires on the reviewed nonidentity four-axis swap. This checkpoint does not yet compare mates generated from arbitrary cleavages and claims no mate invertibility or exactness conclusion.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CoreBeckChevalleyMate.lean
    - ResearchLean/AG/DoctrineFiberProduct/CoreBeckChevalleyMateWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - finiteCodePointedPullbackIso
    - finiteCodePointedPullbackIso_hom_fst
    - finiteCodePointedPullbackIso_hom_snd
    - finiteCodePointedPullback_isPullback_from_producer
    - bcPresentation_isPullback_from_producer
    - bcPresentation_commutes
    - typedCoreFiberTransportCompositor
    - bcCompositePresentations_semantic_eq
    - bcCoreTransportSquareIso
    - bcLeftAdjunction
    - bcRightAdjunction
    - coreBeckChevalleyMate
    - coreBeckChevalleyMate_app
    - coreBeckChevalleyMate_naturality
    - finiteCanonicalMate_isPullback
    - finiteCanonicalMate_right_not_isIso
    - finiteCanonicalMate_left_not_isIso
    - finiteCanonicalCoreBeckChevalleyMate_app
    - finiteCanonicalCoreBeckChevalleyMate_axisSwap_naturality
    - finiteCanonicalMate_axisSwap_ne_id
  claim_mapping:
    theorem_names:
      - finiteCodePointedPullback_isPullback_from_producer
      - bcCoreTransportSquareIso
      - coreBeckChevalleyMate
      - coreBeckChevalleyMate_app
      - coreBeckChevalleyMate_naturality
      - finiteCanonicalMate_left_not_isIso
      - finiteCanonicalMate_right_not_isIso
      - finiteCanonicalCoreBeckChevalleyMate_axisSwap_naturality
      - finiteCanonicalMate_axisSwap_ne_id
    source_labels:
      - target theorem (C) compatible-point pullback and canonical-mate construction artifact
      - Cycle 30 pointed pullback producer
      - G-109 covariant compositor and Cycle 35 adjunction predecessors
    conjuncts:
      - every validated finite BC presentation yields the exact ExtInst_U pullback square from producer data
      - its two covariant routes are compared through the typed G-109 compositors and generated semantic commutativity
      - mateEquiv generates the fixed-orientation canonical mate from the Cycle 35 unit and counit
      - the mate component formula and naturality are exported without caller-supplied comparison data
      - a finite example fires naturality with both relevant reindexing legs noninvertible and the vertical map nonidentity
    undischarged_assumptions:
      - mate-level cleavage independence: construct the arbitrary-cleavage mate and prove its comparison with the selected mate by consuming Cycle 36 adjunction, unit, and counit compatibility
      - packageProjection-specific Beck--Chevalley exactness support and positive IsIso theorem
      - arbitrary endpoint-isomorphism rebasing beyond the exact producer endpoint bridge
      - authored-support induced comparison, MateCoherentRel positive/negative pair, full-orbit invariance, and nontrivial orbit witness
      - fixed-ledger arbitrary-target FiniteModelLift
      - K3 diagnostic base-change action, H_bc condition package, and positive/negative vanishing pair
      - K4 pullback-square pasting and G-106/G-109 coherence bridge
      - final (A)-(E) assembly, cumulative premise audit, and completion four-lane review
  dependency_dag:
    - finite cospan plus compatible selected points -> producer finite-code/generic pointed-pullback isomorphism and projection graphs -> exact decoded ExtInst_U IsPullback
    - decoded square commutativity plus two G-109 compositors -> covariant square NatIso
    - covariant square NatIso plus Cycle 35 adjunctions on pi1 and sigma2 -> mateEquiv -> canonical mate component and naturality
    - asymmetric finite cospan plus two distinct compatible pullback sources -> noninvertible pi1 and sigma2 -> naturality firing on nonidentity axis swap
  premise_audit:
    direction_hypotheses:
      - validated BCPresentation carrying only finite cospan code, compatible selected-point table, and unrelated diagnostic presentation
    discharge_required_consumed:
      - Cycle 30 pointedPullback_isPullback and finite-code producer isomorphism
      - selected-point equations of both cospan legs
      - generated decoded square commutativity
      - G-109 covariant compositors and typed presentation comparison
      - Cycle 35 generated adjunctions, unit, and counit
    conclusion_equivalent_inputs: none
    structure_field_escape: none; no endpoint isomorphism, IsPullback, square NatIso, adjunction, mate, component, naturality, or invertibility certificate is an input field
    proof_use: the pointed bridge proves the selected source equation componentwise and both projection graph equations; IsPullback.of_iso consumes those graphs; the square comparison consumes both compositors and semantic commutativity; mateEquiv consumes both adjunctions and the square comparison; the component expansion exposes the generated unit and counit; the witness proves noninvertibility by explicit source-map noninjectivity and fires naturality on the named nonidentity map
  route_integrity:
    selected_route: exact decoded finite-code pullback, exact G-109 core transport functors, and exact Cycle 35 selected reindexing adjunctions
    provenance: reviewed Cycle 30, G-109, and Cycle 35 declarations; Cycle 36 remains an unconsumed predecessor for the next mate-level cleavage-independence theorem; the finite witness supplies only raw finite cospan/point data
    nonvacuity: generated pi1 and authored sigma2 are both noninvertible, and the vertical axis-swap map is provably nonidentity
    forbidden_routes_absent:
      - no caller endpoint isomorphism or pullback certificate
      - no caller square comparison, adjunction, unit, counit, or mate component
      - no arbitrary whole-functor equality cast
      - no IsIso, exactness, MateCoherentRel, K3-K4, or completion claim
  regression_scenarios:
    weakened_or_reversed_mate: rejected; the displayed functor type is the fixed `(pi2)_! (pi1)^* -> (sigma2)^* (sigma1)_!` orientation
    conclusion_as_field: rejected; the public constructor accepts only BCPresentation and derives every categorical artifact
    pullback_certificate_escape: rejected; the exact IsPullback is transported from pointedPullback_isPullback through producer-generated projection graphs
    hand_authored_component: rejected; mateEquiv_apply exposes the unit-square-counit expansion
    vacuous_witness: rejected; both relevant reindexing legs are noninvertible and the naturality map is nonidentity
    exactness_from_general_coherence: rejected; completion_candidate remains no and packageProjection exactness remains explicit
  verification:
    - focused direct check CoreBeckChevalleyMate.lean: pass; 21 namespace declarations, standard axioms only
    - targeted module CoreBeckChevalleyMate: pass
    - focused direct check CoreBeckChevalleyMateWitnesses.lean: pass; 18 namespace declarations, standard axioms only
    - targeted module CoreBeckChevalleyMateWitnesses: pass
    - exact G-110 umbrella module ResearchLean.AG.DoctrineFiberProduct: pass
    - placeholder/unsafe/new-axiom scan on both exact files: clean
    - hidden/BiDi and private-path scan on both exact files: clean
    - Formal to ResearchLean import-direction scan: no new reverse import
    - Research aggregate/full build: not run, per hard rule
  review:
    initial_exact_head: 45aeb86e43bb1e81222b1122027c0352a1922b36
    initial_four_lane_result: Lean construction claims passed all four lanes; one central ledger finding and one repeated noncentral docstring finding required repair
    central_finding: Cycle 36 proves adjunction-level cleavage independence, but this cycle neither constructs arbitrary-cleavage mates nor proves comparison with the selected mate; the first ledger incorrectly omitted mate-level cleavage independence from remaining obligations
    noncentral_finding: the module docstring reversed the left Lean-composition display while the declaration itself had the correct fixed orientation
    initial_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4078#issuecomment-5382853151
    repair: restrict the accepted delta to the selected-cleavage mate, restore mate-level cleavage independence as the next discharge obligation, remove Cycle 36 from consumed provenance, and correct the docstring display; no declaration, proof, or import changed
    fresh_full_rerun: all four lanes passed the central mathematical and Lean claims at 390f9abf17b207ecdb4e4e788c041c98f3ce8fb6; one noncentral implementation-note finding remained
    noncentral_repair_head: c1aba8db3ee9f5ef457fc10610e16c25f77c7fa5
    noncentral_repair: corrected the prose compositor directions to inverse top/right, decoded comparison, and forward left/bottom; declaration, proof, and import surfaces were unchanged
    direct_response: fresh finding-limited audit of 390f9abf..c1aba8db passed with no findings and confirmed the repair was comment-only
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4078#issuecomment-5382875861
    status: accepted selected-cleavage canonical-mate proof-checkpoint; G-110 completion remains no
next:
  proof_obligation: consume Cycle 36 arbitrary-cleavage adjunction, unit, and counit comparison theorems to construct mates for arbitrary left/right cleavages and prove their generated comparison with the selected mate; only after that prove packageProjection-specific exactness and positive IsIso without deriving either from pullbackness or pseudofunctor coherence alone
```

### Cycle 36 — cleavage-independent core transport/reindexing adjunction

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 36
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: c79487fbfd44bf87f46a5fd8c91ee28facdfcd9f
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 35 merge synchronization comment 5382565767 and Cycle 36 selection comment 5382579240
  proof_dag_predecessors:
    - Cycle 33 arbitrary-cleavage comparison, both lift triangles, naturality, and coherence
    - Cycle 35 producer-derived selected core transport/reindexing adjunction, its hom equivalence, unit, counit, and triangles
    - Cycle 33 finite literal and twisted cleavages with their visibly nonidentity four-axis comparison
  proof_obligation: for every RealizableHom and arbitrary CoreFiberCartesianCleavage, generate the comparison to the exact selected reindexing functor from cartesian-lift universality; transport the Cycle 35 adjunction along that generated natural isomorphism and expose both transpose directions, unit, counit, and both triangles; prove that the Cycle 33 canonical comparison between any two cleavages intertwines the forward and inverse hom equivalences, unit, and counit; fire the surface on the finite literal and twisted cleavages with a visibly nonidentity comparison
  selection_reason: Cycle 35 constructed the exact selected-cleavage adjunction but left the GOAL-required cleavage independence open; Cycle 33 already supplies the canonical cleavage comparison and its lift triangles, so connecting those two reviewed predecessors is the shortest remaining K2 discharge after the reviewed Cycle 30 pointed-pullback bridge and before the canonical Beck--Chevalley mate
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CoreTransportReindexCleavageIndependence.lean
    - ResearchLean/AG/DoctrineFiberProduct/CoreTransportReindexCleavageIndependenceWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - accepting an adjunction, hom equivalence, unit, counit, triangle, or compatibility certificate from a caller
    - replacing arbitrary-cleavage quantification by the fixed selected cleavage
    - constructing unrelated adjunctions for two cleavages without proving that the Cycle 33 canonical comparison intertwines their transpose maps, unit, and counit
    - hiding the comparison behind functor equality or a whole-adjunction cast rather than consuming the generated cartesian-lift comparison
    - calling a proof-field-only difference or an identity comparison nontrivial
    - promoting cleavage independence to a canonical Beck--Chevalley mate, packageProjection exactness, K3-K4, or G-110 completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  content_head: 748281246e041b5bbd0a74342ed18eda66c9a1f4
  review_target_head: 7c0f77f851b4231fca80aeb7797720a14ca2d090
  proof_obligation_delta: For every arbitrary CoreFiberCartesianCleavage, strong-cartesian lift uniqueness generates a component isomorphism from its reindexing object to the Cycle 31 selected object. Both component factor triangles and naturality on every vertical target-fiber map package these components as a natural isomorphism to the exact selected reindexing functor. Cycle 35's exact core-transport/selected-reindexing adjunction is transported only along that generated right-functor isomorphism. Named formulas identify the resulting forward transpose as the selected transpose followed by the inverse bridge and the inverse transpose as the forward bridge followed by the selected inverse transpose; the generated unit and counit components and both triangle identities are exposed. For any two arbitrary cleavages, the Cycle 33 canonical comparison and both selected-bridge factor triangles prove compatibility of the forward transpose, inverse transpose, unit, and counit. The finite literal and twisted identity cleavages fire all four comparison laws and opposite triangle identities; their component comparison sends axis zero to axis one and is therefore genuinely nonidentity. This Cycle 36 fixture uses an identity base arrow and claims nontriviality only for cleavage choice; the Cycle 35 finite fixture separately retains the adjunction's noninvertible-base firing.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CoreTransportReindexCleavageIndependence.lean
    - ResearchLean/AG/DoctrineFiberProduct/CoreTransportReindexCleavageIndependenceWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - coreFiberCleavageSelectedComparisonApp
    - coreFiberCleavageSelectedComparisonApp_hom_fac
    - coreFiberCleavageSelectedComparisonApp_inv_fac
    - coreFiberCleavageSelectedComparison_naturality
    - coreFiberCleavageSelectedComparison
    - coreFiberCleavageComparison_selected_hom
    - coreFiberCleavageComparison_selected_inv
    - coreTransportCleavageAdjunction
    - coreTransportCleavageAdjunction_homEquiv_apply
    - coreTransportCleavageAdjunction_homEquiv_symm_apply
    - coreTransportCleavageUnit
    - coreTransportCleavageCounit
    - coreTransportCleavageUnit_app
    - coreTransportCleavageCounit_app
    - coreTransportCleavage_left_triangle
    - coreTransportCleavage_right_triangle
    - coreTransportCleavageHomEquiv_comparison
    - coreTransportCleavageHomEquiv_symm_comparison
    - coreTransportCleavageUnit_comparison
    - coreTransportCleavageCounit_comparison
    - finiteCoreLiteralCleavageAdjunction
    - finiteCoreTwistedCleavageAdjunction
    - finiteCoreCleavageHomEquiv_comparison
    - finiteCoreCleavageHomEquiv_symm_comparison
    - finiteCoreCleavageUnit_comparison
    - finiteCoreCleavageCounit_comparison
    - finiteCoreLiteralCleavage_left_triangle
    - finiteCoreTwistedCleavage_right_triangle
    - finiteCoreCleavageComparison_axis_zero
    - finiteCoreCleavageAxisSwap_ne_id
  claim_mapping:
    theorem_names:
      - coreFiberCleavageSelectedComparison
      - coreTransportCleavageAdjunction
      - coreTransportCleavageHomEquiv_comparison
      - coreTransportCleavageHomEquiv_symm_comparison
      - coreTransportCleavageUnit_comparison
      - coreTransportCleavageCounit_comparison
      - finiteCoreCleavageComparison_axis_zero
      - finiteCoreCleavageAxisSwap_ne_id
    source_labels:
      - target theorem (C) cleavage-independence discharge artifact
      - Cycle 33 canonical arbitrary-cleavage comparison predecessor
      - Cycle 35 producer-derived selected adjunction predecessor
    conjuncts:
      - every arbitrary cleavage over every realized finite-code base arrow receives an adjunction generated from the exact selected adjunction and the canonical cartesian comparison
      - both transpose directions, unit, counit, and both triangles are exposed for that generated adjunction
      - the Cycle 33 comparison between every two cleavages intertwines both transpose directions, unit, and counit
      - a finite literal/twisted pair fires the comparison laws with a provably nonidentity four-axis component
    undischarged_assumptions:
      - arbitrary endpoint-isomorphism rebasing beyond exact-endpoint presentation replacement
      - canonical Beck--Chevalley mate and packageProjection-specific exactness/positive IsIso
      - authored-support MateCoherentRel positive/negative pair and nontrivial full-orbit invariance
      - fixed-ledger arbitrary-target FiniteModelLift, which remains open
      - K3 diagnostic base-change action, H_bc condition package, positive/negative vanishing pair
      - K4 pullback-square pasting and push/pull coherence bridge
      - final (A)-(E) assembly, cumulative premise audit, and completion four-lane review
  dependency_dag:
    - arbitrary CoreFiberCartesianCleavage + selectedCoreFiberCartesianLift -> generated component domainIso and both factor triangles -> natural isomorphism to selectedCoreFiberReindexFunctor
    - Cycle 35 selected adjunction + generated right-functor natural isomorphism -> arbitrary-cleavage adjunction -> hom equivalence, unit, counit, and triangles
    - Cycle 33 comparisonApp factor triangles + each cleavage's selected bridge -> forward/inverse hom-equivalence compatibility and unit/counit squares
    - finite literal/twisted cleavages + four-axis comparison computation -> nonidentity cleavage-choice firing
  premise_audit:
    direction_hypotheses:
      - RealizableHom presentation witness supplied by the existing finite-code schema
      - arbitrary CoreFiberCartesianCleavage universally quantified as a lift family over that semantic arrow
    discharge_required_consumed:
      - arbitrary cleavage's internally supplied strong-cartesian lifts and their factor laws
      - selectedCoreFiberCartesianLift and its strong-cartesian universality
      - Cycle 33 canonical comparison and its hom factor triangle
      - Cycle 35 exact selected adjunction and its generated transpose maps
    conclusion_equivalent_inputs: none
    structure_field_escape: none; the public construction accepts only RealizableHom, arbitrary cleavage lift families, and fiber objects/morphisms, while the selected bridge, adjunction, hom compatibility, unit/counit compatibility, and triangles are generated conclusions
    proof_use: component bridges and naturality consume strong-cartesian uniqueness and both lift factor graphs; Adjunction.ofNatIsoRight consumes the generated bridge rather than a caller certificate; the explicit transpose formulas expose the transport direction; comparison compatibility consumes the Cycle 33 comparison factor triangle together with both cleavages' selected-bridge triangles; finite theorems compute the comparison on an axis and prove it differs from identity
  route_integrity:
    selected_route: exact G-109 coreFiberTransportFunctor against each cleavage's exact reindexFunctor, connected through the exact Cycle 35 selectedCoreFiberReindexFunctor
    provenance: reviewed Cycle 33 and Cycle 35 declarations plus arbitrary strong-cartesian lift families
    nonvacuity: finite literal/twisted cleavage comparison is visibly nonidentity; noninvertible-base adjunction nonvacuity remains supplied separately by Cycle 35
    forbidden_routes_absent:
      - no caller adjunction, hom equivalence, unit, counit, triangle, or compatibility certificate
      - no whole-functor equality cast and no whole-adjunction cast
      - no proof-field-only nonidentity claim
  regression_scenarios:
    selected_only_statement: rejected; the construction universally quantifies arbitrary CoreFiberCartesianCleavage values
    conclusion_as_field: rejected; the adjunction and all compatibility laws are generated after accepting only lift families
    comparison_not_consumed: rejected; forward/inverse transpose and unit/counit theorems explicitly use the Cycle 33 comparison
    vacuous_witness: rejected; the comparison is computed on axis zero and shown unequal to identity
    completion_from_checkpoint: rejected; completion_candidate remains no
  verification:
    - focused direct check CoreTransportReindexCleavageIndependence.lean: pass; 20 namespace declarations, standard axioms only
    - targeted module CoreTransportReindexCleavageIndependence: pass
    - focused direct check CoreTransportReindexCleavageIndependenceWitnesses.lean: pass; 12 namespace declarations, standard axioms only
    - targeted module CoreTransportReindexCleavageIndependenceWitnesses: pass
    - exact G-110 umbrella module ResearchLean.AG.DoctrineFiberProduct: pass
    - placeholder/unsafe/new-axiom scan on both exact files: clean
    - hidden/BiDi and private-path scan on both exact files: clean
    - Formal to ResearchLean import-direction scan: no new reverse import
    - Research aggregate/full build: not run, per hard rule
  review:
    initial_exact_head: 7c0f77f851b4231fca80aeb7797720a14ca2d090
    initial_four_lane_result: all four lanes passed the central mathematical and Lean claims; three noncentral ledger/documentation findings required direct response
    noncentral_findings:
      - Cycle 30 pointedPullback_isPullback had been incorrectly returned to the undischarged list and next obligation
      - fixed-ledger arbitrary-target FiniteModelLift was described conditionally instead of as definitely open
      - the nontrivial domainIso/ofNatIsoRight route lacked Implementation notes and an affirmative umbrella summary
    repaired_head: 2951b837be8a38ee1cf220c3eea8c2831abc13e7
    repair: synchronized the cumulative proof DAG and FiniteModelLift state, documented the generated comparison and rejected routes, and added the positive umbrella summary; no Lean declaration, proof, or import changed
    direct_response: fresh finding-limited audit of 7c0f77f8..2951b837 passed with no findings and confirmed that all Lean changes were comment-only
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4077#issuecomment-5382705629
    status: accepted arbitrary-cleavage adjunction-independence proof-checkpoint; G-110 completion remains no
next:
  proof_obligation: consume the reviewed Cycle 30 pointedPullback_isPullback together with the accepted push/pull compositors and generated adjunction units/counits to construct the canonical Beck--Chevalley mate; keep packageProjection-specific exactness and authored-support relative obstruction as separate downstream subnodes
```

### Cycle 35 — producer-derived core transport/reindexing adjunction

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 35
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 8bd3c0562af4063594235b1e237b02b5b508081b
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 34 merge synchronization comment 5381864085 and Cycle 35 selection comment 5382357145
  proof_dag_predecessors:
    - G-109 reviewed coreFiberTransportFunctor, coreFiberLift, and strong-cocartesian factor/uniqueness API
    - Cycle 31 producer-derived selectedCoreFiberReindexFunctor and selectedCoreFiberCartesianLift
    - Cycle 32 selected typed compositor/unitor and coherence
    - Cycle 33 cleavage-choice independence
    - Cycle 34 exact-endpoint presentation replacement and finite-code quotient pseudoaction
  proof_obligation: construct the natural hom-set equivalence between canonical G-109 cocartesian core transport and G-110 selected cartesian reindexing over every RealizableHom; package it as an adjunction with generated unit, counit, naturality, and both triangles; prove exact-endpoint presentation-replacement compatibility without casting a whole functor or adjunction; fire the surface on the finite noninvertible selective leg and nonidentity axis swap
  selection_reason: the fixed (C) target requires the adjunction f_! left-adjoint f^* before the canonical Beck--Chevalley mate can be generated from units and counits; Cycle 34 already closed the reindexing functor, coherence, choice independence, and presentation descent needed to make this the shortest remaining K2 predecessor
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CoreTransportReindexAdjunction.lean
    - ResearchLean/AG/DoctrineFiberProduct/CoreTransportReindexAdjunctionWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - accepting a hom equivalence, adjunction, unit, counit, lift, comparison, factorization, naturality, or triangle certificate from a caller
    - deriving an adjunction from existence of lifts without constructing both transpose maps and proving both inverse and naturality laws
    - replacing the G-109 canonical cocartesian functor or G-110 selected cartesian functor by a target-fitted wrapper
    - transporting a complete functor or adjunction across presentation equality rather than using the reviewed generated comparison and lift factor graphs
    - firing only an identity or invertible base leg, or omitting a genuine nonidentity vertical map
    - promoting the adjunction checkpoint to the canonical Beck--Chevalley mate, exactness, K3-K4, or G-110 completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  content_head: 92afa071f31d7ea654a4876cd82ac1f5ea444069
  review_target_head: pending repaired-head report commit
  proof_obligation_delta: A vertical map from canonical cocartesian pushforward to a target package is transposed by factoring the canonical G-109 lift followed by that map through the selected G-110 cartesian lift. The inverse transpose factors a source vertical map followed by the selected cartesian lift through the G-109 cocartesian lift. The two defining factor graphs and the corresponding strong-cartesian/strong-cocartesian uniqueness principles prove both inverse laws. Separate universal-property arguments prove naturality in the source and target fiber variables, yielding Adjunction.CoreHomEquiv and Mathlib Adjunction.mkOfHomEquiv. Unit and counit are generated by that constructor, their components are identified with the two transpose maps on identities, and their factor graphs, naturality, and both triangle identities are exposed as named theorems. For exact-endpoint raw-distinct but semantically equal presentations, a new G-109-side natural isomorphism is generated componentwise by strong-cocartesian lift uniqueness after retagging only the second lift's strong-cocartesianness proposition; Cycle 34 supplies the G-110 selected-reindexing natural isomorphism. These two comparisons directly intertwine both transpose maps and the pointwise hom-set equivalences, and the generated unit and counit satisfy actual comparison squares. No complete functor or adjunction is cast by equality. The finite witness instantiates the adjunction over the reviewed noninvertible selective-two-to-support leg, proves both inverse laws and both lift factor graphs, fires right naturality with the genuine four-axis swap, records that the swap is nonidentity, fires both triangles, and fires both directions of padded-presentation correspondence compatibility, the unit/counit squares, and forward compatibility after the nonidentity axis swap.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CoreTransportReindexAdjunction.lean
    - ResearchLean/AG/DoctrineFiberProduct/CoreTransportReindexAdjunctionWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - coreTransportToReindexHom
    - coreTransportToReindexHom_fac
    - reindexToCoreTransportHom
    - reindexToCoreTransportHom_fac
    - reindexToCoreTransportHom_toReindex
    - coreTransportToReindexHom_toCoreTransport
    - coreTransportReindexHomEquiv
    - reindexToCoreTransportHom_comp_left
    - coreTransportToReindexHom_comp_right
    - coreTransportReindexCoreHomEquiv
    - coreTransportReindexAdjunction
    - coreTransportReindexUnit
    - coreTransportReindexCounit
    - coreTransportReindexUnit_app
    - coreTransportReindexCounit_app
    - coreTransportReindexUnit_app_fac
    - coreTransportReindexCounit_app_fac
    - coreTransportReindexUnit_naturality
    - coreTransportReindexCounit_naturality
    - coreTransportReindex_left_triangle
    - coreTransportReindex_right_triangle
    - typedCoreFiberTransportPresentationComparisonApp
    - typedCoreFiberTransportPresentationComparisonApp_hom_fac
    - typedCoreFiberTransportPresentationComparisonApp_inv_fac
    - typedCoreFiberTransportPresentationComparison_naturality
    - typedCoreFiberTransportPresentationComparison
    - coreTransportToReindexHom_typedPresentationCompatibility
    - reindexToCoreTransportHom_typedPresentationCompatibility
    - coreTransportReindexHomEquiv_typedPresentationCompatibility
    - coreTransportReindexUnit_typedPresentationCompatibility
    - coreTransportReindexCounit_typedPresentationCompatibility
    - finiteCoreTransportReindexAdjunction
    - finiteCoreTransportReindexAdjunction_base_not_isIso
    - finiteCoreTransportReindexCounit_forward_eq_id
    - finiteCoreTransportReindexUnit_backward_eq_id
    - finiteCoreTransportReindexUnit_fac
    - finiteCoreTransportReindexCounit_fac
    - finiteCoreTransportReindex_axisSwap_naturality
    - finiteCoreTransportReindex_axisSwap_ne_id
    - finiteCoreTransportReindex_left_triangle
    - finiteCoreTransportReindex_right_triangle
    - finiteCoreTransportReindexHomEquiv_paddedPresentationCompatibility
    - finiteCoreTransportReindexInverse_paddedPresentationCompatibility
    - finiteCoreTransportReindexUnit_paddedPresentationCompatibility
    - finiteCoreTransportReindexCounit_paddedPresentationCompatibility
    - finiteCoreTransportReindexAxisSwap_paddedPresentationCompatibility
  claim_mapping:
    theorem_names:
      - coreTransportReindexAdjunction
      - coreTransportReindexUnit_app_fac
      - coreTransportReindexCounit_app_fac
      - coreTransportReindex_left_triangle
      - coreTransportReindex_right_triangle
      - coreTransportToReindexHom_typedPresentationCompatibility
      - reindexToCoreTransportHom_typedPresentationCompatibility
      - coreTransportReindexHomEquiv_typedPresentationCompatibility
      - finiteCoreTransportReindexAdjunction_base_not_isIso
      - finiteCoreTransportReindex_axisSwap_naturality
      - finiteCoreTransportReindexHomEquiv_paddedPresentationCompatibility
      - finiteCoreTransportReindexInverse_paddedPresentationCompatibility
      - finiteCoreTransportReindexAxisSwap_paddedPresentationCompatibility
    source_labels:
      - target theorem (C) producer-derived reindexing adjunction discharge artifact
      - Cycle 34 presentation-replacement and selected-comparison predecessor
      - G-109 reviewed covariant core pseudofunctor predecessor
    conjuncts:
      - every realized finite-code base arrow has the exact G-109 core transport functor left adjoint to the exact G-110 selected reindexing functor
      - both transpose directions, both inverse laws, and both-variable naturality are generated from strong lift universality
      - unit and counit are generated from the hom equivalence and satisfy named factor graphs, naturality, and both triangle identities
      - semantic-equal presentation replacement gives generated natural isomorphisms on both transport and reindexing sides that intertwine both transpose directions, the hom equivalence, unit, and counit without a whole-functor cast
      - the complete surface fires on a noninvertible base leg and a genuine nonidentity vertical map
    undischarged_assumptions:
      - pointed pullback square assembly and pointedPullback_isPullback
      - connect the Cycle 33 arbitrary-cleavage comparison to the Cycle 35 adjunction hom equivalence, unit, and counit; Cycle 35 constructs only the fixed selected-cleavage adjunction
      - canonical Beck--Chevalley mate and packageProjection-specific exactness/positive IsIso
      - authored-support MateCoherentRel positive/negative pair and nontrivial full-orbit invariance
      - arbitrary-target FiniteModelLift if not already closed by a later accepted predecessor
      - K3 diagnostic base-change action, H_bc condition package, positive/negative vanishing pair
      - K4 pullback-square pasting and push/pull coherence bridge
      - final (A)-(E) assembly, cumulative premise audit, and completion four-lane review
  dependency_dag:
    - coreFiberLift/coreFiberTransportFunctor -> reindexToCoreTransportHom -> inverse/naturality -> CoreHomEquiv -> Adjunction -> unit/counit/triangles
    - selectedCoreFiberCartesianLift/selectedCoreFiberReindexFunctor -> coreTransportToReindexHom -> inverse/naturality -> CoreHomEquiv
    - strongLiftComparisonIso + semantic-equality proposition retag -> typedCoreFiberTransportPresentationComparison -> forward/inverse hom-correspondence compatibility
    - selectedTypedCoreFiberPresentationComparisonApp_hom_fac + typedCoreFiberTransportPresentationComparison factor graphs -> hom-equivalence/unit/counit presentation squares
    - finiteSelectiveTwoToSupportInput + finiteReindexAxisSwapHom -> noninvertible/nonidentity finite firing, including presentation compatibility after the axis swap
  premise_audit:
    direction_hypotheses:
      - RealizableHom presentation witness supplied by the existing finite-code schema
      - semantic_eq decoded-arrow equality for GOAL-authorized exact-endpoint presentation replacement
    discharge_required_consumed:
      - selectedCartesianRegime and its internally generated strong cartesian lift
      - G-109 canonical core transport and internally generated strong cocartesian lift
      - Cycle 34 selected presentation comparison and its lift triangle
      - G-109 strong-lift comparison construction and both component factor triangles
    conclusion_equivalent_inputs: none
    structure_field_escape: none; public constructors accept only input presentations, fiber objects, and fiber morphisms, while hom equivalence, adjunction, unit, counit, factors, naturality, and triangles are generated conclusions
    proof_use: forward factorization consumes the selected strong-cartesian API; inverse factorization consumes the G-109 strong-cocartesian API; inverse and naturality laws consume both factor graphs and their uniqueness; presentation compatibility generates and consumes the G-109 comparison hom/inv factor triangles together with the Cycle 34 reindexing comparison triangle, then proves both transpose equations and unit/counit squares by the corresponding universal uniqueness; finite naturality and padded compatibility consume the named nonidentity axis map
  route_integrity:
    selected_route: exact G-109 coreFiberTransportFunctor and exact G-110 selectedCoreFiberReindexFunctor
    provenance: reviewed predecessor declarations plus the fixed selectedCartesianRegime producer
    nonvacuity: finite selective base is noninvertible and the target axis swap is provably nonidentity
    forbidden_routes_absent:
      - no caller adjunction or unit/counit/triangle certificate
      - no whole-functor or whole-adjunction equality cast
      - no identity-only base witness
  regression_scenarios:
    weaker_statement_or_direction_missing: rejected; both transpose directions, inverse laws, both-variable naturality, and both triangles are present
    conclusion_as_field: rejected; generated Adjunction.mkOfHomEquiv consumes the internally proved CoreHomEquiv
    certificate_without_producer: rejected; no adjunction certificate is an argument
    material_premise_unused: rejected; both strong lift APIs and both generated presentation-comparison triangles occur in the proof DAG
    vacuous_witness: rejected; named noninvertible base and nonidentity vertical swap are proved
    completion_from_wrapper_or_ci: rejected; completion_candidate remains no
  verification:
    - focused direct check CoreTransportReindexAdjunction.lean: pass; 33 namespace declarations, standard axioms only
    - focused direct check CoreTransportReindexAdjunctionWitnesses.lean: pass; 19 namespace declarations, standard axioms only
    - targeted module CoreTransportReindexAdjunction: pass
    - targeted module CoreTransportReindexAdjunctionWitnesses: pass
    - exact G-110 umbrella module ResearchLean.AG.DoctrineFiberProduct: pass
    - placeholder/unsafe/new-axiom scan on both exact files: clean
    - hidden/BiDi and private-path scan on both exact files: clean
    - Formal to ResearchLean import-direction scan: no new reverse import
    - Research aggregate/full build: not run, per hard rule
  review:
    initial_exact_head: dbb7c7d2ffbfe844993f3f859e8f32c92f208c9a
    initial_status: Major revisions by all four independent lanes
    initial_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4076#issuecomment-5382474389
    central_finding: the first head preserved only the first presentation's factor graph; the second presentation's transpose/hom equivalence/unit/counit did not occur in the claimed compatibility theorems
    repaired_content_head: 92afa071f31d7ea654a4876cd82ac1f5ea444069
    repair: added a componentwise G-109 transport NatIso, both transpose commuting equations, explicit hom-equivalence compatibility, actual unit/counit squares, and nondegenerate padded finite firing; restored adjunction-specific arbitrary-cleavage compatibility to the undischarged ledger
    formal_rerun_exact_head: c56d19e964616bb432eae6d5c362cb7f48632e1d
    formal_rerun: central claims passed all four fresh lanes; two noncentral ledger/documentation drifts were returned for direct response
    direct_response: umbrella status now distinguishes the constructed selected adjunction from open arbitrary-cleavage compatibility, and semantic_eq is classified as a direction hypothesis; finding-limited audit passed with no Lean declaration/proof/import change
    status: accepted selected-cleavage adjunction proof-checkpoint; G-110 completion remains no
next:
  proof_obligation: first connect the Cycle 33 arbitrary-cleavage comparison to the Cycle 35 selected adjunction hom equivalence/unit/counit, then construct the pointed pullback square from the existing compatible-point producer and generate the canonical Beck--Chevalley mate from the Cycle 35 units/counits and accepted push/pull compositors; keep packageProjection-specific exactness and authored-support relative obstruction as separate downstream subnodes if the typed mate surface closes first
```

### Cycle 34 — presentation replacement and finite-code quotient pseudoaction

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 34
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 32712146a11a252e3476250e03a1f8b18b386dd1
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 33 merge synchronization comment 5380624006 and Cycle 34 selection comment 5380666516
  proof_dag_predecessors:
    - Cycle 31 producer-derived selected core-fiber reindexing functor and its exact factor and uniqueness laws
    - Cycle 32 exact-endpoint typed contravariant compositor and unitor with constructor-relative coherence
    - Cycle 33 arbitrary-cleavage comparison, both lift triangles, naturality, refl/symm/cocycle, and replacement-compatible compositor/unitor
    - CartPresentation, CartPresentationBetween, CartSemanticInput, RealizableHom, cartPresentationSetoid, and the finite-code realization calculus
  proof_obligation: index presentation provenance over one literal CartSemanticInput; derive the selected reindexing comparison for every two provenance values with both component triangles, naturality, refl/symm/cocycle; specialize it to exact-endpoint semantically equal CartPresentationBetween values; derive relative compositor and unitor for arbitrary semantically matching direct and identity presentations; prove simultaneous presentation-replacement compatibility; expose the selected FiniteCodeCartHom quotient pseudoaction up to generated NatIso with arbitrary-representative comparison, quotient compositor/unitor, replacement compatibility, pentagon, both unit laws, and a Mathlib Pseudofunctor package without Quotient.lift into Functor; and fire the complete surface on raw-distinct but semantically equal finite presentations with noninvertible legs and a nonidentity vertical map
  selection_reason: A RealizableHom reindexing functor is indexed by its semantic source and target, so equality of semantic arrows alone cannot compare unre-based functors with different dependent endpoint types. Full CartSemanticInput equality may generate a common literal index, after which Cycle 33 cartesian uniqueness supplies the comparison. This cycle records that provenance-preserving descent, forbids whole-functor casts and strict Quotient.lift into Functor, and—once the typed API closes—packages the selected quotient action only up to generated natural isomorphism.
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingPresentationReplacement.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingPresentationCoherence.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingFiniteCodePseudoaction.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingFiniteCodePseudoactionWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingPresentationWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - accepting a lift, cleavage, endpoint iso, comparison, NatIso, triangle, naturality, compositor, unitor, or coherence certificate from a caller
    - using semantic equality to cast a complete RealizableHom or reindexing functor into the result instead of rebasing provenance into one literal semantic input
    - stating a direct NatIso between functors whose source or target CoreFiber categories are differently indexed
    - claiming a strict quotient functor even though presentation replacement supplies natural isomorphism rather than functor equality
    - treating Quotient.out as a mathematical normal form, or replacing generated representative comparisons and coherence by equality casts
    - omitting the selected quotient pseudoaction after the typed replacement and compatibility surfaces have closed
    - proving only same-code endpoint replacement while calling it arbitrary RealizableHom presentation descent
    - firing only proof-field-distinct presentations, invertible legs, identity vertical maps, or claiming opaque selected comparison nonidentity merely from raw presentation inequality
    - promoting presentation replacement to an adjunction, canonical Beck--Chevalley mate, K3-K4, or G-110 completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  content_head: dfa1b06f990f8172fd169eeb4759d258420fabb7
  review_target_head: dfa1b06f990f8172fd169eeb4759d258420fabb7
  reviewed_content_head: dfa1b06f990f8172fd169eeb4759d258420fabb7
  proof_obligation_delta: CartRealizationProvenance indexes finite presentation provenance over one literal CartSemanticInput and stores no lift, cleavage, comparison, or coherence certificate. Every two provenance values generate selected reindexing functors whose components are compared by the StrongCartesianLift domain isomorphism; both lift triangles, naturality on every vertical map, and whole-natural-isomorphism reflexivity, symmetry, and cocycle follow from cartesian uniqueness. For exact-endpoint CartPresentationBetween values, equality of decoded homs generates equality of their full typed semantic inputs and retags only the selected lift's strong-cartesianness proposition. This yields the typed selected comparison without transporting a complete functor. An arbitrary direct presentation satisfying the decoded composition equation receives a relative contravariant compositor, and an arbitrary identity-decoding presentation receives a relative unitor. Simultaneous replacement of both composable legs and the direct presentation, and replacement of two identity presentations, preserve those structures by direct use of the Cycle 33 cleavage compatibility laws. At the finite-code quotient, the action evaluates the distinguished Quotient.out representative but compares every supplied representative to that action by the generated typed NatIso. Quotient compositors and unitors are constructed from the actual selected lifts, their replacement laws consume the typed compatibility surface, and cartesian uniqueness proves the pentagon and both unit laws before LocallyDiscrete.mkPseudofunctor packages the contravariant action on the opposite category. No Quotient.lift targets Functor. Named object, map, mapId, and mapComp theorems expose that package without unfolding it; the quotient-level map factor theorem is the stable characterization used by downstream associativity and unit proofs; and three inverse-normalization theorems isolate route unfolding from the final package coherence proof. The finite fixture replaces the empty-support identity Atom code by a singleton-support code decoding the same identity permutation; it proves typed and raw presentation inequality, equality of decoded homs and full semantic inputs, fires both representative comparison triangles, naturality, refl/symm/cocycle, quotient compositor/unitor and replacement laws, pentagon and both units, reads all four packaged fields on the same quotient chain, and retains two noninvertible quotient legs plus a nonidentity vertical axis map. The infinite-source semantic identity supplies an independent typed negative CartRealizationProvenance example. The fixture deliberately makes no claim that opaque selected comparison components are nonidentity merely because authored codes differ.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingPresentationReplacement.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingPresentationCoherence.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingFiniteCodePseudoaction.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingFiniteCodePseudoactionWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingPresentationWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - CartRealizationProvenance
    - CartRealizationProvenance.toRealizableHom
    - RealizableHom.provenance
    - selectedCoreFiberCleavageBridge
    - cartRealizationProvenanceComparisonApp_hom_fac
    - cartRealizationProvenanceComparisonApp_inv_fac
    - cartRealizationProvenanceComparison_naturality
    - cartRealizationProvenanceComparison
    - cartRealizationProvenanceComparison_refl
    - cartRealizationProvenanceComparison_symm
    - cartRealizationProvenanceComparison_cocycle
    - typedCartSemanticInput_eq_of_hom_eq
    - selectedTypedCoreFiberPresentationComparisonApp_hom_fac
    - selectedTypedCoreFiberPresentationComparisonApp_inv_fac
    - selectedTypedCoreFiberPresentationComparison_naturality
    - selectedTypedCoreFiberPresentationComparison
    - selectedTypedCoreFiberPresentationComparison_refl
    - selectedTypedCoreFiberPresentationComparison_symm
    - selectedTypedCoreFiberPresentationComparison_cocycle
    - selectedTypedCoreFiberPresentationCompositor
    - selectedTypedCoreFiberPresentationCompositor_compatibility
    - selectedTypedCoreFiberPresentationUnitor
    - selectedTypedCoreFiberPresentationUnitor_compatibility
    - FiniteCodeCartHom.representative
    - FiniteCodeCartHom.presentations_semantic_eq
    - finiteCodeSelectedCoreFiberRepresentativeComparison
    - finiteCodeSelectedCoreFiberRepresentativeComparison_cocycle
    - finiteCodeSelectedCoreFiberRepresentativeCompositor_compatibility
    - finiteCodeSelectedCoreFiberRepresentativeUnitor_compatibility
    - finiteCodeSelectedCoreFiberCompositor
    - finiteCodeSelectedCoreFiberUnitor
    - finiteCodeSelectedCoreFiberCompositor_assoc
    - finiteCodeSelectedCoreFiberCompositor_left_unit
    - finiteCodeSelectedCoreFiberCompositor_right_unit
    - finiteCodeSelectedCoreFiberReindexPseudoaction
    - finiteCodeSelectedCoreFiberReindexPseudoaction_obj
    - finiteCodeSelectedCoreFiberReindexPseudoaction_map
    - finiteCodeSelectedCoreFiberReindexPseudoaction_mapId
    - finiteCodeSelectedCoreFiberReindexPseudoaction_mapComp
    - finiteCodeSelectedCoreFiberReindexFunctor_map_fac
    - finiteCodeSelectedCoreFiberAssocRightRoute_inverse_normalization
    - finiteCodeSelectedCoreFiberRightUnitRoute_inverse_normalization
    - finiteCodeSelectedCoreFiberLeftUnitRoute_inverse_normalization
    - finiteSelectiveTwoToSupportPresentation_ne_padded
    - finiteSelectiveTwoToSupportRawPresentation_ne_padded
    - finiteSelectiveTwoToSupportPresentation_semanticInput_eq
    - finiteSelectiveTypedPresentationComparison_naturality
    - finiteSelectivePresentationCompositor_compatibility
    - finiteSupportPresentationUnitor_compatibility
    - finitePresentationDescentCompositorFirstLeg_not_isIso
    - finitePresentationDescentAxisSwap_ne_id
    - finiteCodeRawDistinctSelectivePresentationPair
    - finiteCodeSelectivePaddedCanonicalComparisonApp_hom_fac
    - finiteCodeSelectivePaddedCanonicalComparison_naturality
    - finiteCodeSelectiveRepresentativeComparison_cocycle
    - finiteCodePaddedSelectiveRepresentativeCompositor_compatibility
    - finiteCodePaddedSupportRepresentativeUnitor_compatibility
    - finiteCodeSelectiveQuotientCompositor_assoc
    - finiteCodeSelectiveQuotientCompositor_left_unit
    - finiteCodeSelectiveQuotientCompositor_right_unit
    - finiteCodeSelectiveTwoToOneHom_not_isIso
    - finiteCodePseudoactionWitnessAxisSwap_ne_id
    - finiteCodeSupportPseudoaction_obj
    - finiteCodeSelectivePseudoaction_map
    - finiteCodeSupportPseudoaction_mapId
    - finiteCodeSelectivePseudoaction_mapComp
    - infiniteIdentityInput_has_no_cartRealizationProvenance
  claim_mapping:
    theorem_names:
      - cartRealizationProvenanceComparison
      - cartRealizationProvenanceComparison_refl
      - cartRealizationProvenanceComparison_symm
      - cartRealizationProvenanceComparison_cocycle
      - selectedTypedCoreFiberPresentationComparison
      - selectedTypedCoreFiberPresentationCompositor_compatibility
      - selectedTypedCoreFiberPresentationUnitor_compatibility
      - finiteCodeSelectedCoreFiberRepresentativeComparison
      - finiteCodeSelectedCoreFiberRepresentativeCompositor_compatibility
      - finiteCodeSelectedCoreFiberRepresentativeUnitor_compatibility
      - finiteCodeSelectedCoreFiberCompositor_assoc
      - finiteCodeSelectedCoreFiberCompositor_left_unit
      - finiteCodeSelectedCoreFiberCompositor_right_unit
      - finiteCodeSelectedCoreFiberReindexPseudoaction
      - finiteCodeSelectedCoreFiberReindexPseudoaction_map
      - finiteCodeSelectedCoreFiberReindexPseudoaction_mapComp
      - finiteSelectiveTwoToSupportPresentation_ne_padded
      - finiteSelectiveTwoToSupportPresentation_semanticInput_eq
      - infiniteIdentityInput_has_no_cartRealizationProvenance
      - finitePresentationDescentCompositorFirstLeg_not_isIso
      - finiteCodeRawDistinctSelectivePresentationPair
      - finiteCodeSelectivePseudoaction_map
      - finiteCodeSelectivePseudoaction_mapComp
      - finiteCodeSelectiveQuotientCompositor_assoc
      - finiteCodeSelectiveTwoToOneHom_not_isIso
    source_labels:
      - target theorem (C) contravariant reindexing coherence subnode
      - K2 common-semantic presentation-replacement checkpoint
      - Cycle 34 conditional quotient-level selected finite-code pseudoaction obligation
      - Cycle 33 cartesian-cleavage choice-independence and replacement coherence
    conjuncts:
      - every two finite provenance values over one literal CartSemanticInput have a producer-derived selected reindexing natural isomorphism with both lift triangles and naturality
      - common-semantic comparisons satisfy whole-natural-isomorphism reflexivity, symmetry, and three-provenance cocycle
      - exact-endpoint typed presentations with equal decoded arrows admit the same selected comparison after retagging only strong-cartesianness, never the whole functor
      - arbitrary semantically matching direct and identity presentations generate relative contravariant compositors and unitors
      - simultaneous replacement of both legs and the direct presentation preserves the compositor, and replacement of identity presentations preserves the unitor
      - every FiniteCodeCartHom receives a selected contravariant action through a distinguished representative, while every other representative is related by a generated natural isomorphism with triangles, naturality, refl/symm/cocycle, and composition/unit replacement laws
      - quotient compositors and unitors satisfy the cartesian-uniqueness pentagon and both unit laws and assemble a Pseudofunctor on the opposite locally discrete finite-code category without Quotient.lift into Functor
      - raw-distinct identity-decoding finite presentations fire the full surface with a noninvertible leg and nonidentity vertical map
    undischarged_assumptions:
      - fixed-ledger FiniteModelLift for arbitrary CartesianLiftNonexistence targets
      - arbitrary endpoint-isomorphism rebasing and any strict quotient functor or strictification beyond the selected NatIso-level finite-code pseudoaction
      - adjunction with the G-109 covariant core pseudofunctor, the canonical natural Beck--Chevalley mate, packageProjection-specific exactness support, and the positive IsIso theorem
      - AuthoredBC2CellPresentation, the authored-support induced comparison, and the strict/lax MateCoherentRel positive/negative pair; the relative negative is a canonicity obstruction independent of positive IsIso
      - canonical-comparison replacement and proof-use invariance, InReselectionOrbit all-orbit nonvanishing, and a concrete nontrivial-orbit witness
      - K3-K4 and final Doctrine Fiber Product and Base Change theorem assembly and completion review
    acceptance_point: common-literal-semantic presentation replacement, exact-endpoint relative compositor/unitor descent, and selected finite-code quotient pseudoaction up to generated NatIso; no strict Quotient.lift into Functor, arbitrary endpoint rebase, adjunction, mate, or G-110 completion is claimed
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary:
      - arbitrary AtomCarrier U, arbitrary literal CartSemanticInput, and arbitrary finite realization provenance over that input
      - exact-endpoint FiniteInstanceCode and CartPresentationBetween values only for the typed comparison and relative compositor/unitor calculus
      - arbitrary FiniteCodeCartHom values and the opposite locally discrete finite-code category for the selected quotient pseudoaction
      - packageProjection core fibers, selected strong-cartesian lifts, and Cycle 33 cartesian uniqueness/coherence APIs
    input_geometry:
      - arbitrary pairs and triples of finite provenance values over one common semantic input
      - arbitrary target-fiber objects and arbitrary vertical target-fiber maps
      - arbitrary exact-endpoint typed direct, first-leg, second-leg, and identity presentations satisfying internally consumed decoded-arrow equalities
      - arbitrary quotient morphisms and arbitrary typed representatives proved to belong to those quotient classes
    direction_hypothesis:
      - realization_eq and decoded-arrow equalities identify authored finite provenance with one literal semantic input and are consumed to retag only strong-cartesianness propositions
      - selected lifts, comparisons, triangles, naturality, compositors, unitors, and compatibility data are internally generated and are never caller premises
    discharge_required:
      - both comparison lift triangles and naturality for every vertical map
      - whole comparison reflexivity, symmetry, and cocycle
      - relative compositor and unitor component triangles and naturality
      - simultaneous compositor replacement and two-identity unitor replacement compatibility
      - quotient-level representative independence, compositor/unitor, arbitrary-representative replacement compatibility, pentagon, both unit laws, and the final Pseudofunctor package
      - raw-code inequality, decoded semantic equality, and noninvertible/nonidentity finite firing
    conclusion_equivalent_risk:
      - no caller lift, cleavage, endpoint iso, comparison, NatIso, triangle, naturality, compositor, unitor, or coherence packet appears in a selected public producer
      - semantic equality is not used to cast a complete RealizableHom or reindexing functor
      - quotient membership proofs derive semantic equalities but do not supply the comparison, compositor, unitor, pentagon, or unit laws
    unused_or_ambient_only:
      - no Quotient.lift into Functor, arbitrary endpoint equivalence, adjunction, mate, exactness, positive IsIso, K3-K4, or final assembly API is used or claimed
  certificate_provenance:
    - CartRealizationProvenance contains only an authored presentation and its equality to the fixed semantic input
    - comparison components use StrongCartesianLift.domainIso on the two internally selected lifts; their factor graphs and all whole-coherence laws are derived by the cartesian universal property
    - typed semantic equality reuses the second selected lift's domain and hom while rewriting only its IsStronglyCartesian proposition before applying the same generated comparison
    - relative compositor and unitor compose accepted Cycle 32 components with the producer-generated typed presentation comparison; their replacement equations explicitly consume Cycle 33 cleavage compatibility
    - the quotient action makes only the distinguished Quotient.out representative choice; arbitrary-representative comparisons, compositor/unitor replacement, and all pseudoaction coherence are generated from the already accepted typed APIs and cartesian uniqueness
  proof_use:
    - common-provenance naturality and refl/symm/cocycle postcompose with actual selected lifts before applying strong-cartesian uniqueness
    - selectedTypedCoreFiberPresentationComparisonApp compares the actual first selected lift with the actual second lift retagged along the internally derived full semantic-input equality
    - compositor compatibility normalizes first, second, and direct selected lifts to one literal semantic input and uses each generated comparison triangle plus coreFiberCleavageReindexCompositor_compatibility
    - unitor compatibility uses the canonical and replacement identity selected lifts and coreFiberCleavageReindexUnitor_compatibility
    - quotient representative comparisons consume the quotient-derived decoder equalities and the actual typed selected lifts; the quotient pentagon and units compare explicit iterated lift triangles by IsStronglyCartesian uniqueness
    - the Mathlib Pseudofunctor coherence fields cancel the inverse quotient compositor/unitor components against these generated forward pentagon/unit routes; equality casts appear only at the terminal bicategory typing boundary
  anti_weakening:
    verdict: pass
    notes:
      - the common-provenance comparison quantifies all representatives, objects, and vertical maps; the typed surface quantifies all semantically equal exact-endpoint presentations
      - the quotient pseudoaction quantifies all finite-code quotient morphisms and all their supplied typed representatives; its final laws are whole Pseudofunctor coherence fields rather than fixture-only component markers
      - the finite witness proves raw presentation inequality separately from semantic equality and does not infer an opaque selected comparison's nonidentity from that inequality
      - descent is stated up to generated natural isomorphism; Quotient.out selects an evaluation representative but is not claimed to be a mathematical normal form, and no strict Quotient.lift into Functor is used
  witness_nondegeneracy:
    - finitePresentationPaddedIdentityAtomCode has singleton support but decodes to Equiv.refl, while the canonical composite and identity codes have empty support
    - typed and raw presentation inequalities and full CartSemanticInput equalities are independently proved
    - both provenance and typed selected comparison triangles, naturality, refl/symm/cocycle are instantiated
    - relative compositor compatibility uses the genuine selective two-to-one-to-support chain and proves its first leg noninvertible
    - relative unitor compatibility uses canonical and padded identity presentations
    - naturality fires on finiteReindexAxisSwapHom, which is independently nonidentity
    - the same authored quotient chain fires representative hom/inverse triangles, naturality, refl/symm/cocycle, quotient compositor/unitor, arbitrary-representative compatibility, pentagon, and both unit laws
    - the final packaged pseudofunctor is read directly through named object, map, mapId, and mapComp projections on the same finite quotient chain
    - the infinite-source semantic identity supplies a typed negative example for CartRealizationProvenance, independently of the finite positive examples
    - finiteCodeSelectiveTwoToOneHom and finiteCodeSelectiveTwoToSupportHom have non-IsIso semantic realizations, independently of the nonidentity axis-swap vertical map
  structure_field_escape: none-found
  empty_elimination: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - focused CartesianRegimeReindexingPresentationReplacement.lean: pass; namespace audit 39 declarations and standard axioms only
    - focused CartesianRegimeReindexingPresentationCoherence.lean: pass; namespace audit 20 declarations and standard axioms only
    - focused CartesianRegimeReindexingPresentationWitnesses.lean: pass; namespace audit 57 declarations and standard axioms only
    - focused CartesianRegimeReindexingFiniteCodePseudoaction.lean: pass with no warnings; namespace audit 89 declarations and standard axioms only
    - focused CartesianRegimeReindexingFiniteCodePseudoactionWitnesses.lean: pass; namespace audit 41 declarations and standard axioms only
    - targeted modules CartesianRegimeReindexingPresentationReplacement, CartesianRegimeReindexingPresentationCoherence, CartesianRegimeReindexingPresentationWitnesses, CartesianRegimeReindexingFiniteCodePseudoaction, and CartesianRegimeReindexingFiniteCodePseudoactionWitnesses: pass; no Research aggregate or full build
    - exact umbrella target ResearchLean.AG.DoctrineFiberProduct: pass
    - git diff --check, untracked-file whitespace, placeholder, hidden/BiDi Unicode, private-path, import-direction, manifest, and umbrella scans: pass
  initial_review_findings:
    - Math A Major: the conditional quotient-level pseudoaction obligation fired once the typed replacement API closed, but no FiniteCodeCartHom pseudoaction was present and the report had moved it to future scope
    - Lean B Major: the same missing quotient-level selected pseudoaction made Cycle 34 incomplete despite the valid representative-level API
    - Lean A Minor: unstable Lane A wording and the missing Implementation notes section weakened public API documentation without changing the mathematics
    - Math B: no content finding at the initial head
  repaired_head_review_findings:
    - Math A and Math B: no content finding at fixed head 8a7dbf38a27909b1dd52f6ab4a8d91e47681c4a5
    - Lean A Minor: the final Pseudofunctor package lacked named projection APIs and direct fixture firing; reviewed_content_head also overstated a pending review
    - Lean B Minor: the same package API/fixture gap, a missing typed negative CartRealizationProvenance example, two downstream definition unfolds despite existing hom APIs, and four undocumented private normalization lemmas
  second_repair_review_findings:
    - Math A, Math B, and Lean B: no content finding at fixed report head 58a275b735ac223a866a22ed0568fdd67d1d7e7c and Lean content head eae1591cfb6f53384935fb63ef665a55501f8883
    - Lean A Minor: the quotient-level selected functor and lift lacked a stable map factor theorem, so associativity and right-unit proofs unfolded both definitions downstream
  third_repair_review_findings:
    - Math B: no content finding at fixed report head b14728b1e39804aa87f7d710a70c013dd6148e3d and Lean content head c75827e6d93b0b5e6418db59b5fddd4e11e3313b
    - Lean A Minor: the final package coherence still unfolded the public associativity and unit route definitions in three places instead of consuming named inverse-normalization laws
    - Math A and Lean B were stopped without integrated verdicts after the actionable finding invalidated the review target
  fresh_review_verdicts:
    fixed_head: 1fee0300f81a2e52325c8f6a9042e04190e0d724
    reviewed_content_head: dfa1b06f990f8172fd169eeb4759d258420fabb7
    math_a: no major findings
    math_b: no major findings
    lean_a: no major findings
    lean_b: no major findings
    integrated_verdict: pass for Cycle 34 only; no G-110 completion claim
  review_refs:
    initial_fixed_head: d80a9d13867d49193eebe93a4905b533e99df2a7
    initial_report_head: 2a3b50c06d0d48c59e3a1084bc524e0d05e5c32b
    first_repair_head: 7d8227d3c1e8301aa9f13af20b5ce2453ea4ca7c
    first_repair_report_head: 8a7dbf38a27909b1dd52f6ab4a8d91e47681c4a5
    initial_direct_response: not used; the repair added two public modules, a Pseudofunctor declaration, representative/coherence laws, finite witnesses, imports, manifest entries, and stable documentation, so a fresh four-lane review was required
    second_repair_head: eae1591cfb6f53384935fb63ef665a55501f8883
    second_direct_response: not used; the repair adds public projection and witness declarations, so the repaired packet requires another fresh four-lane review
    third_repair_head: c75827e6d93b0b5e6418db59b5fddd4e11e3313b
    third_direct_response: not used; the repair adds the public finiteCodeSelectedCoreFiberReindexFunctor_map_fac theorem, so the repaired packet requires another fresh four-lane review
    fourth_repair_head: dfa1b06f990f8172fd169eeb4759d258420fabb7
    fourth_direct_response: not used; the repair adds three public inverse-normalization theorems, so the repaired packet requires another fresh four-lane review
    fresh_review_fixed_head: 1fee0300f81a2e52325c8f6a9042e04190e0d724
    fresh_review: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4071#issuecomment-5381803316
    report_only_audit: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4071#issuecomment-5381843966
    report_only_direct_response: the live PR body was re-fetched after its body-only synchronization; the fourth-repair review and final-head CI/mergeability entries are complete, the Research-only skipped lake build remains unchecked and excluded from theorem evidence, and no actionable finding remains
  blocking_findings: []
  next_obligation: merge Cycle 34 and synchronize Issue 4034, then stop as directed; adjunction remains the next future proof node but is not selected
```

### Cycle 33 — cartesian-cleavage choice independence

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 33
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: ac10a421155562c406fa3098bfe99aac3270d2d0
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 32 merge synchronization comment 5380000610 and Cycle 33 selection comment 5380220475
  proof_dag_predecessors:
    - Cycle 31 producer-derived cartesian reindexing functor and its exact factor and uniqueness laws
    - Cycle 32 selected typed compositor, unitor, associativity, unit laws, and exact-endpoint presentation discipline
    - Mathlib strong-cartesian comparison, factorization, uniqueness, composition, fiber extensionality, and whiskering APIs
  proof_obligation: isolate a minimal cartesian cleavage over one literal CartSemanticInput; derive its complete reindexing functor; construct the canonical natural isomorphism between every two choices with forward and inverse lift triangles, naturality, reflexivity, symmetry, and cocycle; derive choice-relative compositors and unitors and prove simultaneous replacement compatibility; bridge the selected specialization directly to Cycle 32; and fire the comparison on an actually different finite lift family with a computationally nonidentity component and a noninvertible compositor leg
  selection_reason: Cycle 32 proves coherence only for the fixed selected lift constructor. Cartesian uniqueness should make the reindexing independent of any alternative lift family over the same literal semantic input, but this is distinct from replacing one RealizableHom presentation by another. This cycle therefore quantifies arbitrary lift families as comparison subjects while keeping all comparison and coherence data producer-derived. Presentation replacement remains the next dependent descent obligation.
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingCleavage.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingCleavageCoherence.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingCleavageWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - adding comparison components, natural isomorphisms, factor triangles, naturality, refl, cocycle, compositor compatibility, or unitor compatibility as fields of the cleavage or as caller premises
    - calling arbitrary cleavages an escape merely because they are quantified comparison subjects, or conversely using them to discharge the selected regime's existence obligation
    - casting or identifying differently presented RealizableHom values using only equality of their semantic arrows
    - proving only objectwise comparison without the derived vertical-map action, both lift triangles, or naturality on every vertical map
    - proving compositor or unitor compatibility only for the selected cleavage instead of arbitrary simultaneous replacements
    - firing only propositionally equal lift records, identity vertical maps, invertible base legs, or a computationally constant comparison component
    - promoting same-input choice independence to arbitrary presentation descent, an adjunction, a Beck--Chevalley mate, K3-K4, or final G-110 completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  content_head: 1d42f25398122f910e1ea22f6ff90c7bad8304e9
  reviewed_content_head: 1d42f25398122f910e1ea22f6ff90c7bad8304e9
  proof_obligation_delta: CoreFiberCartesianCleavage has exactly one field, a strong-cartesian lift at each target-fiber object. Its reindexing object, every vertical map, factor graph, uniqueness, identity law, composition law, and functor are generated from that field by the universal property. For any two choices over the same literal CartSemanticInput, StrongCartesianLift.domainIso supplies both directions of the comparison; their lift triangles prove inverse laws and naturality, and the same uniqueness proves whole-natural-isomorphism reflexivity, symmetry, and three-choice cocycle. Arbitrary choice-relative two-step lifts and literal identity lifts generate the contravariant compositor and unitor. Simultaneous comparison of the first, second, and composite choices proves compositor compatibility, while identity-choice comparison proves unitor compatibility. The selected specialization is connected by an explicit natural bridge to the accepted Cycle 32 functor, compositor, and unitor. A finite identity input uses a visible four-axis swap at one named target and literal lifts elsewhere; reflecting its dependent Axis carrier shows that the canonical comparison sends axis zero to axis one. The same fixture fires both lift triangles, naturality, refl/cocycle, unitor compatibility, a noninvertible-leg compositor compatibility, and both selected bridges.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingCleavage.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingCleavageCoherence.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingCleavageWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - CoreFiberCartesianCleavage
    - CoreFiberCartesianCleavage.reindexMap_fac
    - CoreFiberCartesianCleavage.reindexMap_unique
    - CoreFiberCartesianCleavage.reindexFunctor
    - CoreFiberCartesianCleavage.comparisonApp
    - CoreFiberCartesianCleavage.comparisonApp_hom_fac
    - CoreFiberCartesianCleavage.comparisonApp_inv_fac
    - CoreFiberCartesianCleavage.comparison_naturality
    - CoreFiberCartesianCleavage.comparison
    - CoreFiberCartesianCleavage.comparison_refl
    - CoreFiberCartesianCleavage.comparison_symm
    - CoreFiberCartesianCleavage.comparison_cocycle
    - coreFiberCleavageReindexCompositor
    - coreFiberCleavageReindexUnitor
    - coreFiberCleavageReindexCompositor_compatibility
    - coreFiberCleavageReindexUnitor_compatibility
    - selectedTypedCoreFiberCartesianCleavage
    - selectedTypedCoreFiberCleavageBridge
    - selectedTypedCoreFiberCleavageCompositor_bridge
    - selectedTypedCoreFiberCleavageUnitor_bridge
    - finiteCleavageAxisSwapHom_ne_id
    - finiteCleavageComparisonApp_axis_zero
    - finiteCleavageComparisonApp_hom_fac
    - finiteCleavageComparisonApp_inv_fac
    - finiteCleavageComparison_naturality
    - finiteCleavageComparison_cocycle
    - finiteCleavageUnitor_compatibility
    - finiteCleavageSelectiveLeg_not_isIso
    - finiteCleavageCompositor_compatibility
    - finiteCleavageSelectedCompositor_bridge
    - finiteCleavageSelectedUnitor_bridge
  claim_mapping:
    theorem_names:
      - CoreFiberCartesianCleavage.comparison
      - CoreFiberCartesianCleavage.comparison_refl
      - CoreFiberCartesianCleavage.comparison_symm
      - CoreFiberCartesianCleavage.comparison_cocycle
      - coreFiberCleavageReindexCompositor_compatibility
      - coreFiberCleavageReindexUnitor_compatibility
      - selectedTypedCoreFiberCleavageCompositor_bridge
      - selectedTypedCoreFiberCleavageUnitor_bridge
      - finiteCleavageComparisonApp_axis_zero
    source_labels:
      - target theorem (C) contravariant reindexing coherence subnode
      - K2 cartesian-cleavage choice-independence checkpoint
      - Cycle 32 selected constructor-relative functor and coherence surface
    conjuncts:
      - every cleavage over one literal CartSemanticInput derives its full reindexing functor and universal factor laws from its lift family alone
      - every two such cleavages have a producer-derived natural isomorphism with both lift triangles and naturality on all vertical maps
      - the comparisons satisfy whole-natural-isomorphism reflexivity, symmetry, and three-choice cocycle
      - arbitrary first, second, and composite cleavage replacements preserve the choice-relative contravariant compositor, and arbitrary identity-choice replacement preserves the unitor
      - the selected specialization agrees with the accepted Cycle 32 functor, compositor, and unitor through explicit natural bridges
      - a finite alternate lift family has a computationally nonidentity comparison component and fires all compatibility laws with a noninvertible base leg
    undischarged_assumptions:
      - fixed-ledger FiniteModelLift for arbitrary CartesianLiftNonexistence targets
      - arbitrary RealizableHom presentation replacement, endpoint rebasing, and descent of the reindexing functor and coherence across that replacement
      - adjunction with the G-109 covariant core pseudofunctor, the canonical natural Beck--Chevalley mate, packageProjection-specific exactness support, and the positive IsIso theorem
      - AuthoredBC2CellPresentation, the authored-support induced comparison, and the strict/lax MateCoherentRel positive/negative pair; the relative negative is a canonicity obstruction independent of positive IsIso
      - canonical-comparison replacement and proof-use invariance, InReselectionOrbit all-orbit nonvanishing, and a concrete nontrivial-orbit witness
      - K3-K4 and final Doctrine Fiber Product and Base Change theorem assembly and completion review
    acceptance_point: same-literal-input cartesian-cleavage choice-independence checkpoint only; arbitrary presentation descent remains open and G-110 remains target-proof-checkpoint
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary:
      - arbitrary AtomCarrier U and arbitrary CartSemanticInput for the generic cleavage comparison
      - exact-endpoint finite CartPresentationBetween values and DecidableEq U.Atom only for choice-relative compositor, unitor, and selected specialization
      - packageProjection core fibers and Mathlib strong-cartesian universal-property API
    input_geometry:
      - arbitrary target-fiber objects and arbitrary vertical target-fiber morphisms
      - arbitrary first, second, and third cleavage choices over one literal semantic input
      - arbitrary first-leg, second-leg, and composite choices for every exact-endpoint typed composable pair
    direction_hypothesis:
      - arbitrary cleavage lift families are the universally quantified objects being compared, not certificates for the comparison conclusion and not a discharge of the selected regime's lift existence
      - the selected specialization remains internally generated from selectedTypedCoreFiberCartesianLift
    discharge_required:
      - all derived map factor and uniqueness laws
      - both directions of the canonical component and their lift triangles
      - naturality, reflexivity, symmetry, and cocycle of the whole comparison
      - arbitrary simultaneous compositor replacement and arbitrary unitor replacement compatibility
      - exact agreement with Cycle 32 selected surfaces
      - nonidentity and noninvertible finite firing
    conclusion_equivalent_risk:
      - no comparison component, natural isomorphism, factor triangle, map law, naturality law, refl/symmetry/cocycle law, or compositor/unitor compatibility law is an input field or public producer argument
    unused_or_ambient_only:
      - no alternate cleavage is used by selectedCoreFiberCartesianCleavage or to prove selected lift existence
      - semantic composition equality is used only to type the explicit two-step strong-cartesian lift
      - arbitrary presentation equivalences, quotient/setoid descent, adjunction, mate, and K3-K4 APIs are not used or claimed
  certificate_provenance:
    - CoreFiberCartesianCleavage stores only the family being compared; its maps and all laws are generated by strong-cartesian factorization and uniqueness
    - comparisonApp uses StrongCartesianLift.domainIso in both directions and proves its inverse laws from the generated vertical domain isomorphism
    - compositor and unitor components compare explicit two-step or literal identity lifts to the chosen direct lift; caller comparison or coherence certificates do not appear
    - selectedTypedCoreFiberCleavageBridge is an internally typed identity-total-hom bridge between two presentations of the same selected lift, with its triangle and naturality proved before the compositor/unitor bridge
  proof_use:
    - comparison_naturality postcomposes both routes with the second target lift and uses both reindexing factor graphs plus comparison triangles
    - comparison_refl, comparison_symm, and comparison_cocycle postcompose with the appropriate actual chosen lift before applying strong-cartesian uniqueness
    - compositor compatibility reduces both sides to the same second-choice target lift after consuming the first-, second-, and composite-choice comparison triangles
    - unitor compatibility reduces both identity-choice routes to the literal total identity
    - selected compositor and unitor bridges compare the generic selected triangles directly with the Cycle 32 selected triangles
  anti_weakening:
    verdict: pass
    notes:
      - generic comparisons quantify all choices, target objects, and vertical maps over one literal input; compatibility quantifies all simultaneous typed-constructor choices
      - the theorem surface does not identify differently presented RealizableHom inputs and explicitly leaves that dependent descent open
      - no adjunction, Beck--Chevalley mate, K3-K4, or completion claim is included
  witness_nondegeneracy:
    - finiteCleavageTwistedIdentityChoice differs from the literal choice by an actual four-axis swap lift at one named target
    - finiteCleavageAxisSwapHom is provably nonidentity
    - finiteCleavageComparisonApp_axis_zero reflects the dependent target Axis and proves that the canonical comparison sends zero to one
    - both comparison triangles and comparison naturality fire on the same alternate choice and nonidentity vertical swap
    - the three-choice cocycle includes the literal, twisted, and producer-derived selected choices
    - compositor compatibility uses finiteSelectiveTwoToSupportPresentation, whose semantic leg is independently noninvertible
    - the selected compositor and unitor bridges are instantiated on the existing selective chain and support endpoint
  structure_field_escape: none-found
  empty_elimination: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - focused CartesianRegimeReindexingCleavage.lean: pass; namespace audit 36 declarations and standard axioms only
    - focused CartesianRegimeReindexingCleavageCoherence.lean: pass; namespace audit 28 declarations and standard axioms only
    - focused CartesianRegimeReindexingCleavageWitnesses.lean: pass; namespace audit 28 declarations and standard axioms only
    - targeted modules CartesianRegimeReindexingCleavage, CartesianRegimeReindexingCleavageCoherence, and CartesianRegimeReindexingCleavageWitnesses: pass
    - exact umbrella target ResearchLean.AG.DoctrineFiberProduct: pass
    - git diff --check, untracked-file whitespace, placeholder, hidden/BiDi Unicode, private-path, import-direction, manifest, and umbrella scans: pass
    - fixed reviewed head 043a4863b335bebcfcace5d76f617b7a846f651e: 7 of 7 PR checks successful and mergeable/CLEAN; the Research-only lake build job skipped Lean setup, build, kernel axiom audit, and premise report, so it is not counted as theorem evidence
    - report-sync head 2ff10ace2fbd50a01bcbeed5e8909a6f6159ebd9: 7 of 7 PR checks successful and mergeable/CLEAN; independent report-only audit passed after closing one PR title/body language and template finding without changing the Git head
  review_refs:
    fixed_head: 043a4863b335bebcfcace5d76f617b7a846f651e
    standard_review: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4070#issuecomment-5380539824
    final_report_sync_head: 2ff10ace2fbd50a01bcbeed5e8909a6f6159ebd9
    report_only_audit: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4070#issuecomment-5380605339
    report_only_direct_response:
      - initial finding: the live PR title/body were English and did not follow the repository PR template
      - repair: the title and complete template packet were rewritten in Japanese, retaining the checkpoint scope, validation qualification, and the explicit continuing-tracker reason for Refs #4034
      - closure: public-quality reinspection confirmed the finding closed with no Git-head, claim, source-of-truth, or responsibility-surface change
    fresh_review_verdicts:
      - Math A: No major findings; checked statement scope, material-premise classification, producer provenance, proof-use, every coherence law, finite nondegeneracy, and remaining obligations
      - Math B: No major findings; independently attacked field escape, objectwise-only weakening, selected-choice leakage, semantic-equality casting, finite degeneration, and presentation-descent overclaim
      - Lean A: No major findings; traced the six-file fixed diff, comparison and coherence proof terms, selected bridges, imports, manifest, report scope, and the finite witness
      - Lean B: No major findings; independently checked signatures, dependent casts, producer provenance, arbitrary-choice quantification, proof-use, module DAG, and source/report alignment
  blocking_findings: []
  next_obligation: merge Cycle 33 and synchronize Issue 4034; then construct arbitrary RealizableHom presentation replacement and cleavage/coherence descent without weakening the fixed K2 scope
```

### Cycle 32 — constructor-relative cartesian reindexing coherence

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 32
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: a56d9519dfe37979874b92418e5960583e8041b2
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 31 merge synchronization comment 5379610614 and Cycle 32 selection comment 5379703627
  proof_dag_predecessors:
    - Cycle 31 selectedCoreFiberReindexFunctor and its producer-derived map laws, PR 4068 merge a56d9519
    - typed finite presentation identity and composition constructors with their semantic hom equalities
    - Mathlib strong-cartesian composition, factorization, uniqueness, and fiber extensionality APIs
  proof_obligation: expose exact-endpoint typed reindexing functors; construct the actual two-step selected lift; derive the contravariant compositor and unitor, their component triangles, and naturality; prove constructor-relative associativity against one fixed left-associated direct presentation and both unit laws; and fire all results on a finite chain with noninvertible legs and a genuine nonidentity vertical map
  selection_reason: Cycle 31 supplied the fixed-arrow functor but no comparison between reindexing along typed identity or composition constructors. RealizableHom carries presentation provenance, so semantic associativity and unit equalities cannot identify differently presented inputs. This cycle therefore compares only explicit selected lifts over fixed typed constructors and transports equality solely in the strong-cartesianness proposition. Arbitrary presentation replacement and cleavage-choice independence remain separate obligations.
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingCoherence.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingCoherenceWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - accepting a lift, comparison component, natural isomorphism, factorization, naturality, associativity, or unit certificate from the caller
    - casting one RealizableHom or selected functor to a differently presented input using only semantic equality
    - reusing the covariant G-109 compositor or unitor despite the opposite direction and universal property
    - proving only component existence without the actual lift triangle or naturality on every vertical map
    - calling objectwise associativity presentation independence or full cleavage coherence
    - firing only identity arrows, invertible base arrows, or constant vertical maps in the finite witness
    - promoting this checkpoint to the adjunction, Beck--Chevalley mate, K3-K4, or final G-110 theorem
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  content_head: d71d3d5d1af005a9dd6ada9cd9948df75b4d7e1f
  reviewed_content_head: d71d3d5d1af005a9dd6ada9cd9948df75b4d7e1f
  proof_obligation_delta: typedCartSemanticInput and typedRealizableHom retain literal finite-code endpoints. selectedCoreFiberIteratedCartesianLift composes the two actual selected lifts and transports only its strong-cartesianness across the internally proved semantic composition equality. The unique comparison between this iterated lift and the directly selected composite lift yields a contravariant natural compositor with its factor triangle. Comparing the literal identity lift with the selected identity lift yields the natural unitor and triangle. Relative comparison helpers keep one direct typed presentation fixed while using semantic associativity or unit equality only to type an explicit composed lift. Both associativity routes factor the same three-step lift, and both unit routes factor the original selected lift, so cartesian uniqueness proves the pointwise coherence laws. A three-to-two-to-one-to-support selective chain supplies two independently verified noninvertible legs; the genuine four-axis swap fires compositor and unitor naturality.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingCoherence.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingCoherenceWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - typedCartSemanticInput
    - typedRealizableHom
    - typedRealizableHom_id_hom
    - typedRealizableHom_comp_hom
    - selectedTypedCoreFiberReindexFunctor
    - selectedTypedCoreFiberCartesianLift
    - selectedCoreFiberIteratedCartesianLift
    - selectedCoreFiberReindexCompositorApp
    - selectedCoreFiberReindexCompositorApp_hom_fac
    - selectedCoreFiberReindexCompositor_naturality
    - selectedCoreFiberReindexCompositor
    - selectedCoreFiberIdentityCartesianLift
    - selectedCoreFiberReindexUnitorApp
    - selectedCoreFiberReindexUnitorApp_hom_fac
    - selectedCoreFiberReindexUnitor_naturality
    - selectedCoreFiberReindexUnitor
    - selectedCoreFiberReindexAssocLeftRoute_fac
    - selectedCoreFiberReindexAssocRightRoute_fac
    - selectedCoreFiberReindexCompositor_assoc
    - selectedCoreFiberReindexLeftUnitRoute_fac
    - selectedCoreFiberReindexRightUnitRoute_fac
    - selectedCoreFiberReindexCompositor_left_unit
    - selectedCoreFiberReindexCompositor_right_unit
    - finiteSelectiveThreeToTwoCoherenceInput_not_isIso
    - finiteSelectiveCoherenceMiddle_not_isIso
    - finiteSelectiveReindexCompositor_naturality
    - finiteSupportReindexUnitor_naturality
    - finiteSelectiveReindexCompositor_assoc
    - finiteSelectiveReindexCompositor_left_unit
    - finiteSelectiveReindexCompositor_right_unit
    - finiteSelectiveReindexCoherence_axisSwap_ne_id
  claim_mapping:
    theorem_names:
      - selectedCoreFiberReindexCompositor
      - selectedCoreFiberReindexUnitor
      - selectedCoreFiberReindexCompositor_assoc
      - selectedCoreFiberReindexCompositor_left_unit
      - selectedCoreFiberReindexCompositor_right_unit
      - finiteSelectiveReindexCompositor_assoc
      - finiteSelectiveReindexCoherence_axisSwap_ne_id
    source_labels:
      - target theorem (C) contravariant reindexing coherence subnode
      - K2 typed-constructor unitor/compositor and coherence checkpoint
      - selected cartesian regime as the internally generated cleavage source
    conjuncts:
      - every pair of composable typed presentations has a producer-derived contravariant compositor natural isomorphism
      - every typed finite instance has a producer-derived identity unitor natural isomorphism
      - every compositor and unitor component exposes its actual selected-lift factor triangle and is natural on all vertical maps
      - both three-step compositor routes to one fixed left-associated direct presentation are equal on every target package
      - both unit routes relative to the original typed presentation equal identity on every target package
      - a finite noninvertible selective chain and nonidentity vertical map fire all selected laws without caller certificates
    undischarged_assumptions:
      - fixed-ledger FiniteModelLift for arbitrary CartesianLiftNonexistence targets
      - comparison under arbitrary RealizableHom presentation replacement and independence of arbitrary generated cartesian-lift choices, including reflexivity, cocycle, and compatibility with this compositor and unitor
      - adjunction with the G-109 covariant core pseudofunctor, the canonical natural Beck--Chevalley mate, packageProjection-specific exactness support, and the positive IsIso theorem
      - AuthoredBC2CellPresentation, the authored-support induced comparison, and the strict/lax MateCoherentRel positive/negative pair; the relative negative is a canonicity obstruction independent of positive IsIso
      - canonical-comparison replacement and proof-use invariance, InReselectionOrbit all-orbit nonvanishing, and a concrete nontrivial-orbit witness
      - K3-K4 and final Doctrine Fiber Product and Base Change theorem assembly and completion review
    acceptance_point: constructor-relative selected-reindexing coherence checkpoint only; no arbitrary presentation or cleavage-choice independence, and G-110 remains target-proof-checkpoint
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary:
      - arbitrary AtomCarrier U with the existing DecidableEq U.Atom boundary of typed finite presentations and CartesianRegime
      - packageProjection core fibers and Mathlib strong-cartesian universal-property API
    input_geometry:
      - arbitrary composable CartPresentationBetween values with literal finite-code endpoints
      - arbitrary target-fiber objects and arbitrary vertical target-fiber morphisms
    direction_hypothesis:
      - no caller direction certificate; reindexing lifts are selected through the Cycle 31 producer, the identity reference lift is constructed internally from the identity isomorphism, and iterated lifts are internal composites of selected lifts
    discharge_required:
      - strong cartesianness of the explicit two-step and identity lifts
      - invertible comparison components and their factor triangles
      - naturality on every vertical map
      - constructor-relative associativity and both unit laws on every target object
      - noninvertible/nonidentity finite firing
    conclusion_equivalent_risk:
      - no lift, cleavage, comparison, natural isomorphism, factorization law, naturality law, associativity law, or unit law is an argument to a public producer
    unused_or_ambient_only:
      - semantic composition and unit equalities transport only the strong-cartesianness proposition of explicit hom composites
      - arbitrary RealizableHom presentation equivalences, cleavage comparisons, G-109 covariant coherence, adjunction, and mate APIs are not used or claimed
  certificate_provenance:
    - selectedTypedCoreFiberCartesianLift is the exact-endpoint specialization of the Cycle 31 selected-regime producer
    - the module-private strong-cartesian comparison helper is assembled from the two directions of the universal factor and proves both inverse laws by the same universal uniqueness; no caller-supplied lift comparison is exported
    - compositor and unitor components compare actual selected lifts; relative helpers receive only an internally proved base-hom equality, not a comparison or factor certificate
  proof_use:
    - selectedCoreFiberReindexCompositorApp_hom_fac consumes the direct and iterated selected lift comparison
    - compositor and unitor naturality compare both routes after postcomposition with the selected target lift and use the actual map factor graph
    - left and right associativity routes each reduce to the same literal three-lift composite before cartesian uniqueness
    - left and right unit routes each reduce to the original selected lift before cartesian uniqueness
  anti_weakening:
    verdict: pass
    notes:
      - generic declarations quantify every typed composable pair or triple and every target package; naturality quantifies every vertical map
      - no theorem identifies differently presented RealizableHom values, and the module explicitly excludes arbitrary presentation or cleavage-choice independence
      - no adjunction, Beck--Chevalley mate, K3-K4, or completion claim is included
  witness_nondegeneracy:
    - finiteSelectiveThreeToTwoCoherenceSourceMap collapses distinct selected and third source cells, proving its typed semantic hom noninvertible
    - finiteSelectiveTwoToOnePresentation supplies a second reviewed noninvertible leg
    - associativity fires on the genuine three-to-two-to-one-to-support chain without identity padding
    - finiteReindexAxisSwapHom is provably nonidentity and fires compositor and unitor naturality
    - compositor and both unit laws are instantiated on the selected finite chain
  structure_field_escape: none-found
  empty_elimination: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - focused CartesianRegimeReindexingCoherence.lean after the public-firewall repair: pass; namespace audit 36 declarations and standard axioms only
    - focused CartesianRegimeReindexingCoherenceWitnesses.lean: pass; namespace audit 20 declarations and standard axioms only
    - targeted modules CartesianRegimeReindexingCoherence and CartesianRegimeReindexingCoherenceWitnesses: pass
    - git diff --check, untracked-file whitespace, placeholder, hidden/BiDi Unicode, import-direction, manifest, and umbrella scans: pass
    - repaired fixed head 37f96ee8bcac677fa6d8a01d597b2b1c842088d0: 7 of 7 PR checks successful and mergeable/CLEAN; the Research-only lake build job skipped Lean setup, build, kernel axiom audit, and premise report, so it is not counted as theorem evidence
    - report-sync head 981594de5888e72bfacbd18430cc6bf76fbbb032: 7 of 7 PR checks successful; independent report-only audit passed with no actionable finding
  review_refs:
    initial_fixed_head: b66a55dc50930be266f3468a6be3f695cb70b76c
    initial_standard_review:
      - Lean A found that three generic comparison helpers accepted caller-supplied StrongCartesianLift values on the public namespace surface
      - Math A, Math B, and Lean B found no other Cycle 32 content issue
    repair_head: d71d3d5d1af005a9dd6ada9cd9948df75b4d7e1f
    direct_response: not used; making three declarations module-private changes the public declaration surface, so a fresh four-lane review is required
    fixed_head: 37f96ee8bcac677fa6d8a01d597b2b1c842088d0
    standard_review: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4069#issuecomment-5379945963
    final_report_sync_head: 981594de5888e72bfacbd18430cc6bf76fbbb032
    report_only_audit: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4069#issuecomment-5379985719
    fresh_review_verdicts:
      - Math A: No major findings; checked orientation, premise classification, selected-lift provenance, proof-use, and finite nondegeneracy
      - Math B: No major findings; checked all public signatures, private helper boundaries, factor graphs, witness connection, and remaining-scope accuracy
      - Lean A: No major findings; independently confirmed the prior three-declaration public-firewall finding is closed, the helpers have no external references, and no alternate caller-certificate path remains
      - Lean B: No major findings; independently checked endpoint typing, dependency/provenance, both comparison directions, all coherence proof terms, and static wiring
  blocking_findings: []
  next_obligation: merge Cycle 32 and synchronize Issue 4034; then construct arbitrary-presentation and cleavage-choice comparison coherence before the adjunction and Beck--Chevalley mate
```

### Cycle 31 — producer-derived cartesian reindexing functor

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 31
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 66fbe2d5866f790b1f94fd9afc7f4270f9591061
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 30 merge synchronization comment 5379311529 and Cycle 31 selection comment 5379364390
  proof_dag_predecessors:
    - selectedCartesianRegime and selectedCartesianRegime_HCart from the fixed cartesian branch artifact
    - Mathlib packageProjection strong-cartesian map, factorization, uniqueness, and extensionality APIs
    - Cycle 30 generic pointed pullback bridge, PR 4067 merge 66fbe2d5
  proof_obligation: construct the selected pullback reindexing functor on core fibers for every RealizableHom by generating each cartesian lift internally from the selected regime; define every vertical map as the universal factor through the codomain lift; export its factor graph, uniqueness, identity law, and composition law; and fire those results on a noninvertible selective-two base with a nonidentity four-axis vertical map plus an identity-base sensitivity control
  selection_reason: Cycle 30 supplies the generic pointed pullback bridge required before the fixed K2 fiber construction. The next independent node is the contravariant object-and-map action of f^*. It must be generated from the selected cartesian regime rather than accept a lift, cleavage, factor, map, or law packet. Base-arrow unitor/compositor data, cleavage independence, the adjunction with the G-109 covariant core transport, and the Beck--Chevalley mate are separate later nodes.
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexing.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - accepting a strong cartesian lift, cleavage, object action, map, factorization equality, uniqueness proof, or functor-law packet from the caller
    - defining only object pullback and silently obtaining the map action or functor laws from an unrelated preassembled functor
    - using choice over a supplied low preimage rather than the selected regime's internally generated existence theorem
    - weakening factor uniqueness or the identity/composition laws to a selected object, map, or finite fixture
    - calling a nonidentity target map or a noninvertible base sufficient without firing the actual factor graph and a nonconstant-map control
    - promoting fixed-arrow functoriality to base-arrow unitor/compositor, cleavage independence, adjunction, mate invertibility, K3-K4, or final G-110 completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  content_head: db1a511950b0499b358bc5ef048cfe69238d8d71
  reviewed_content_head: 14471cd33278b42ccf73fd4c6b55b79561f9f47d
  proof_obligation_delta: cartesianRegimeChosenLift obtains a strong cartesian lift solely from CartesianRegime.hasStrongCartesianLift at the admitted realized arrow and target package. Its domain defines the reindexed object. For every vertical target-fiber morphism, cartesianRegimeReindexMap applies Mathlib IsStronglyCartesian.map to the codomain lift and the composite of the domain lift with that morphism. The defining factor graph, its uniqueness among all vertical candidates, and identity and composition laws are proved from the same strong-cartesian universal property, then assembled into cartesianRegimeReindexFunctor. The selected public producer has only the realized arrow as data input and specializes this generic construction to selectedCartesianRegime. The finite firing uses a noninvertible selective-two realized base and an actual nonidentity four-axis swap, while a separate identity-base control uses cartesian-lift invertibility and cancellation to prove that the generated map action cannot be constant.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexing.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeReindexingWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - cartesianRegimeChosenLift
    - cartesianRegimeReindexObject
    - cartesianRegimeReindexMap
    - cartesianRegimeReindexMap_fac
    - cartesianRegimeReindexMap_unique
    - cartesianRegimeReindexMap_id
    - cartesianRegimeReindexMap_comp
    - cartesianRegimeReindexFunctor
    - selectedCoreFiberCartesianLift
    - selectedCoreFiberReindexFunctor
    - selectedCoreFiberReindexFunctor_obj
    - selectedCoreFiberReindexFunctor_map
    - selectedCoreFiberReindexFunctor_map_fac
    - selectedCoreFiberReindexFunctor_map_unique
    - selectedCoreFiberReindexFunctor_map_id
    - selectedCoreFiberReindexFunctor_map_comp
    - finiteReindexAxisSwapHom_ne_id
    - finiteSelectiveTwoReindexInput_not_isIso
    - finiteSelectiveTwoReindexedAxisSwap_fac
    - finiteSelectiveTwoReindex_map_id
    - finiteSelectiveTwoReindex_map_comp
    - finiteReindexIdentityAxisSwapHom_ne_id
    - finiteReindexIdentityAxisSwap_map_ne_id
  claim_mapping:
    theorem_names:
      - selectedCoreFiberReindexFunctor
      - selectedCoreFiberReindexFunctor_map_fac
      - selectedCoreFiberReindexFunctor_map_unique
      - selectedCoreFiberReindexFunctor_map_id
      - selectedCoreFiberReindexFunctor_map_comp
      - finiteSelectiveTwoReindexedAxisSwap_fac
      - finiteReindexIdentityAxisSwap_map_ne_id
    source_labels:
      - target theorem (C) producer-derived pullback reindexing object and map
      - K2 reindexing functor identity and composition subnode
      - selected cartesian regime as the internally generated cleavage source
    conjuncts:
      - every selected-regime realized arrow and every target-fiber object receives an internally generated strong cartesian lift
      - every vertical target morphism is sent to the unique vertical factor through the codomain lift
      - the generated map action satisfies the complete factor graph and universal uniqueness statement
      - object and map actions form a functor with all-object identity and all-composable-map composition laws
      - the finite firing combines a noninvertible base, nonidentity target map, actual factor graph, functor laws, and a nonconstant-map sensitivity control
    undischarged_assumptions:
      - fixed-ledger FiniteModelLift for arbitrary CartesianLiftNonexistence targets
      - base-arrow reindexing unitor and compositor, their coherence, and independence of the internally selected cleavage
      - adjunction with the G-109 covariant core pseudofunctor, the canonical natural Beck--Chevalley mate, packageProjection-specific exactness support, and the positive IsIso theorem
      - AuthoredBC2CellPresentation, the authored-support induced comparison, and the strict/lax MateCoherentRel positive/negative pair; the relative negative is a canonicity obstruction independent of positive IsIso
      - canonical-comparison replacement and proof-use invariance, InReselectionOrbit all-orbit nonvanishing, and a concrete nontrivial-orbit witness
      - K3-K4 and final Doctrine Fiber Product and Base Change theorem assembly and completion review
    acceptance_point: producer-derived fixed-arrow core-fiber reindexing functor checkpoint only; G-110 remains target-proof-checkpoint
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary:
      - arbitrary AtomCarrier U with the existing DecidableEq U.Atom boundary of CartesianRegime
      - packageProjection core fibers and Mathlib strong-cartesian universal-property API
    input_geometry:
      - generic helper receives a CartesianRegime, an arbitrary RealizableHom, and proof that the regime admits that arrow
      - selected public producer receives only an arbitrary RealizableHom; its regime and membership are named branch outputs
      - arbitrary target-fiber objects and arbitrary vertical target-fiber morphisms
    direction_hypothesis:
      - regime.HCart membership is the generic eliminator input; selectedCartesianRegime_HCart generates it for the fixed public producer
    discharge_required:
      - strong cartesian lift at every target object
      - vertical map factor, factorization equality, and uniqueness
      - all-object identity and all-composable-map composition laws
      - noninvertible/nonidentity finite firing and nonconstant-map control
    conclusion_equivalent_risk:
      - no lift, cleavage, object action, map, factor, graph, uniqueness proof, or functor law is a selected-producer argument
    unused_or_ambient_only:
      - Classical.choice appears only inside cartesianRegimeChosenLift and chooses from regime.hasStrongCartesianLift; it does not recover a caller-supplied preimage
      - finite presentations and the four-axis permutation occur only in the witness
      - G-109 covariant pushforward, adjunction, compositor/unitor, and mate APIs are not claimed by this checkpoint
  certificate_provenance:
    - cartesianRegimeChosenLift consumes regime.hasStrongCartesianLift for the actual input, membership, and target package
    - cartesianRegimeReindexMap consumes the domain and codomain generated lifts and Mathlib IsStronglyCartesian.map
    - selectedCoreFiberReindexFunctor specializes only the named selectedCartesianRegime and selectedCartesianRegime_HCart outputs
  proof_use:
    - cartesianRegimeReindexMap_fac is the direct IsStronglyCartesian.fac equation for the generated codomain lift
    - cartesianRegimeReindexMap_unique consumes the candidate factor graph in IsStronglyCartesian.map_uniq
    - cartesianRegimeReindexMap_id and cartesianRegimeReindexMap_comp compare candidates by strong-cartesian extensionality and the actual factor graph
    - finiteReindexIdentityAxisSwap_map_ne_id combines the generated factor graph with IsStronglyCartesian.isIso_of_base_isIso and categorical cancellation
  anti_weakening:
    verdict: pass
    notes:
      - generic statements quantify every admitted realized arrow, every target object, every vertical map, and every composable pair
      - selected producer accepts neither a regime nor its membership, and no witness-specific object occurs in its type
      - this checkpoint does not count base-arrow pseudofunctor coherence, cleavage independence, adjunction, mate, or completion
  witness_nondegeneracy:
    - finiteSelectiveTwoToSupportInput supplies a reviewed non-IsIso semantic base arrow
    - finiteReindexAxisSwapHom exchanges distinct axes zero and one and is therefore a genuine nonidentity vertical target map
    - the selected factor graph and both functor laws fire on that base and map
    - the identity-base control proves the same nonidentity map is not collapsed to identity by the selected map action
  structure_field_escape: none-found
  empty_elimination: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - focused CartesianRegimeReindexing.lean: pass; namespace audit 16 declarations and standard axioms only
    - focused CartesianRegimeReindexingWitnesses.lean before and after the doc-only repair: pass; namespace audit 24 declarations and standard axioms only
    - targeted modules CartesianRegimeReindexing and CartesianRegimeReindexingWitnesses: pass
    - git diff --check, untracked-file whitespace, placeholder, hidden/BiDi Unicode, privacy, import-direction, manifest, and umbrella scans: pass
    - PR checks at repaired reviewed head 14471cd3: 7/7 success; the Research-only lake build job is not counted as theorem elaboration evidence because Lean setup, build, kernel-audit, and premise-report steps were skipped
    - PR checks at initial report-sync head 0a70d2a6: 7/7 success with the same Research-only lake build step exclusions
    - PR checks at repaired report-sync head 3e033d2f: 7/7 success with the same Research-only lake build step exclusions
  review_refs:
    fixed_head: 873283b0d0651c0c47c44446fba59f11cb0e796b
    standard_review: four-lane math-lean-review completed; one documentation-only Minor was repaired and directly rechecked by its reporting reviewer
    independent_final_reviews:
      - Math A: No major findings at fixed head 873283b0
      - Math B: No major findings at fixed head 873283b0
      - Lean A: No major findings at fixed head 873283b0
      - Lean B: Minor for a missing named-local-instance docstring at fixed head 873283b0; Pass after qualified direct response at repaired head 14471cd3
    qualified_direct_response: 873283b0..14471cd3 adds exactly one docstring line, changes no declaration, type, proof, import, report, umbrella, or manifest, and was accepted by Lean B without a fresh four-lane review
    initial_integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4068#issuecomment-5379504079
    qualified_audit_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4068#issuecomment-5379577393
    public_audit_correction: the qualified audit comment supplies each lane's findings, refutation attempts, checked evidence, coverage limits, Issue acceptance mapping, validation commands, direct-response qualification, and the complete fixed-GOAL remaining K2 scope omitted by the initial abbreviated comment
    initial_report_sync_head: 0a70d2a61be637fe1c51f4a17feb27613524c36d
    final_report_sync_head: 3e033d2f418493d2258081440b10b6a292de17f9
    report_only_audit: PASS; the qualified direct-response audit confirmed that the public-review-traceability Major and remaining-K2-scope Minor are both substantively repaired, the exact repair range changes only this report, the fixed GOAL and Lean artifacts are unchanged, and the repaired report-sync head has 7/7 successful checks
  blocking_findings: []
  next_obligation: merge Cycle 31; then construct base-arrow unitor/compositor and cleavage-independence data before the adjunction and Beck--Chevalley mate
```

### Cycle 30 — generic pointed pullback bridge

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 30
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: b943b582dd00a0487b05dceaa63c5278b5b3bc47
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 29 merge synchronization comment 5379013074 and Cycle 30 selection comment 5379029132
  proof_dag_predecessors:
    - G-101 pointed extraction-doctrine category ExtInst_U and source-preserving morphisms
    - Cycle 29 arbitrary Doct_U pullback producer and proper finite witness, PR 4066 merge b943b582
  proof_obligation: discharge the explicit K2 bridge by generating the selected point, projections, arbitrary-cone factor, factorization, uniqueness, and pointedPullback_isPullback in ExtInst_U from every pointed exact-doctrine cospan. The selected sources and the two ExtInstHom.source_eq fields are the compatible point cone; no separate compatibility, lift, factorization, or pullback certificate is accepted. Fire the result on the proper three-by-three over two cospan while retaining both noninvertible projections and a nonidentity-Atom universal factor.
  selection_reason: the fixed ledger requires the pointed ExtInst_U pullback to be generated from the concrete K0 Source pullback and source_eq proof-use. The existing pullbackPresentation_isPullback theorem remains correct for finite-code cospans but does not discharge this generic K0-to-pointed bridge. Producer-derived reindexing is the following K2 node and is deliberately not combined with this bridge.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/PointedDoctrinePullback.lean
    - ResearchLean/AG/DoctrineFiberProduct/PointedDoctrinePullbackWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - accepting the northwest point, compatibility equality, universal factor, factorization laws, uniqueness, or IsPullback from the caller
    - hiding the arbitrary pointed-cone factor behind choice from an already assembled pullback theorem rather than consuming doctrinePullbackLift
    - restricting the generic bridge to finite presentation inputs, identity Atom equivalences, or the old all-compatible fixture
    - counting the finite Schema pullback as the generic K0-to-ExtInst bridge
    - promoting the bridge to the reindexing functor, adjunction, Beck-Chevalley mate, K3-K4, or final theorem completion
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  content_head: fac123dd5327e64332a691d5497bcf6d25e18347
  reviewed_content_head: fac123dd5327e64332a691d5497bcf6d25e18347
  proof_obligation_delta: constructed pointedPullbackSource directly from the two selected input sources and sigmaOne.source_eq.trans sigmaTwo.source_eq.symm, equipped the Cycle 29 doctrine pullback with that internally generated point, and lifted both doctrine projections to ExtInst_U. Every pointed pullback cone is converted only to its underlying doctrine cone; doctrinePullbackLift supplies the computational factor and the two pointed cone-leg source_eq proofs generate its source equation. The factor preserves the first leg's actual Atom equivalence, satisfies both projection laws, is unique, and yields pointedPullback_isPullback with no finite, DecidableEq, compatibility-certificate, or caller-pullback premise. The symmetric three-by-three over two witness identifies the generated point with the named compatible pair, retains source nonemptiness and both projection non-IsIso facts, and fires a nonidentity finite Atom swap through the generated pointed factor.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/PointedDoctrinePullback.lean
    - ResearchLean/AG/DoctrineFiberProduct/PointedDoctrinePullbackWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - pointedPullbackSource
    - pointedPullback
    - pointedPullbackFst
    - pointedPullbackFst_doctrineHom
    - pointedPullbackSnd
    - pointedPullbackSnd_doctrineHom
    - pointedPullback_commutes
    - pointedPullbackLift
    - pointedPullbackLift_atomEquiv
    - pointedPullbackLift_fst
    - pointedPullbackLift_snd
    - pointedPullbackLift_unique
    - pointedPullback_isPullback
    - finiteProperPointedLeg_doctrineHom
    - finiteProperPointedPullback_source_eq_compatible00
    - finiteProperPointedPullback_source_compatible
    - finiteProperPointedPullback_source_nonempty
    - finiteProperPointedPullback_fst_not_isIso
    - finiteProperPointedPullback_snd_not_isIso
    - finiteProperPointedPullback_isPullback
    - finiteProperPointedSwapLift_componentC
  claim_mapping:
    theorem_names:
      - pointedPullback_isPullback
      - pointedPullbackLift_atomEquiv
      - pointedPullbackLift_unique
      - finiteProperPointedPullback_isPullback
      - finiteProperPointedPullback_fst_not_isIso
      - finiteProperPointedPullback_snd_not_isIso
      - finiteProperPointedSwapLift_componentC
    source_labels:
      - target theorem (C) compatible point cone and ExtInst_U pullback bridge
      - material-premise ledger pointed ExtInst pullback bridge
      - Cycle 29 proper K0 witness reused as a nondegenerate pointed firing
    conjuncts:
      - every pointed exact-doctrine cospan obtains an internally selected K0 pullback point from its two source_eq fields
      - universality ranges over every pointed semantic cone and its generated factor preserves the first leg's arbitrary Atom equivalence
      - both pointed factorization laws and uniqueness descend to the reviewed K0 doctrine pullback theorems
      - the resulting square is a categorical pullback in ExtInst_U without a caller IsPullback certificate
      - the proper finite firing remains inhabited with two noninvertible pointed projections and a nonidentity-Atom factor
    undischarged_assumptions:
      - fixed-ledger FiniteModelLift for arbitrary CartesianLiftNonexistence targets
      - producer-derived reindexing functor, id and composition laws, adjunction, compositor and unitor, cleavage independence, and the packageProjection Beck-Chevalley mate and IsIso theorem
      - K3-K4 and final Doctrine Fiber Product and Base Change theorem assembly and completion review
    acceptance_point: candidate discharge of the pointedPullback_isPullback ledger item only; G-110 remains target-proof-checkpoint
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary:
      - arbitrary fixed AtomCarrier U and the reviewed G-101 Doct_U and ExtInst_U category APIs
      - Cycle 29 doctrinePullback construction and universality
    input_geometry:
      - arbitrary pointed instances DOne, DTwo, Base and pointed exact morphisms sigmaOne, sigmaTwo
      - arbitrary PullbackCone sigmaOne sigmaTwo in the universal property
    direction_hypothesis:
      - the selected sources and the two pointed cospan source_eq laws constitute the fixed compatible point cone
    discharge_required:
      - compatible selected source of the K0 pullback
      - pointed projections and their square commutativity
      - arbitrary pointed-cone factor source_eq, both factorization laws, uniqueness, and IsPullback
      - nonempty, two-noninvertible, nonidentity-Atom finite firing
    conclusion_equivalent_risk:
      - northwest point, compatibility equality, factor, factorization laws, uniqueness, and IsPullback are never producer inputs
    unused_or_ambient_only:
      - finite presentation and DecidableEq occur only in the witness
      - reindexing, cartesian lifts, adjunctions, and mate APIs are absent from the producer
  certificate_provenance:
    - pointedPullbackSource is the pair of the two input selected sources and its compatibility proof is exactly sigmaOne.source_eq followed by sigmaTwo.source_eq.symm
    - the universal doctrine factor is doctrinePullbackLift applied to the doctrine projection of the arbitrary pointed cone
    - the factor source_eq is generated componentwise from cone.fst.source_eq and cone.snd.source_eq
    - factorization and uniqueness are proved after ExtInstHom.ext by the corresponding Cycle 29 doctrine theorems
  proof_use:
    - pointedPullbackLift.doctrineHom is the explicit K0 doctrine factor and its Atom equivalence is definitionally cone.fst.doctrineHom.atomEquiv
    - pointedPullbackLift.source_eq consumes both pointed cone-leg source_eq proofs
    - pointedPullbackLift_unique sends both pointed factorization equalities to doctrinePullbackLift_unique
    - the concrete non-IsIso proofs consume the two independent Cycle 29 source collisions through ExtInstHom source-map injectivity
  anti_weakening:
    verdict: pass
    notes:
      - generic construction has no DecidableEq, finiteness, presentation, compatibility packet, factor, or pullback premise
      - ordinary pointed cone input appears only as the universally quantified cone receiving its factor
      - finite Schema pullback, reindexing, adjunction, and mate statements are not counted in this checkpoint
  witness_nondegeneracy:
    - the generated selected source equals finiteProperFiberCompatible00 and directly supplies Nonempty
    - finiteProperFiberCompatible00/01 and 00/10 independently refute invertibility of the two pointed projections
    - finiteProperPointedSwapCone and finiteProperPointedSwapLift_componentC fire componentC-to-dependsAB through the actual universal factor
  structure_field_escape: none-found
  empty_elimination: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - focused PointedDoctrinePullback.lean: pass; namespace audit 13 declarations and standard axioms only
    - targeted module PointedDoctrinePullback: pass
    - focused PointedDoctrinePullbackWitnesses.lean: pass; namespace audit 13 declarations and standard axioms only
    - targeted module PointedDoctrinePullbackWitnesses: pass
    - git diff --check, placeholder, hidden/BiDi Unicode, privacy, import-direction, manifest, and umbrella scans: pass
    - PR checks at reviewed head 10a7fa36: 7/7 success; the Research-only lake build job is not counted as theorem elaboration evidence because Lean setup, build, kernel-audit, and premise-report steps were skipped
    - PR checks at report synchronization head d10ea254: 7/7 success with the same Research-only lake build step exclusions
  review_refs:
    fixed_head: 10a7fa3631435cd48c6cb2552f68f1807610d5fb
    initial_integrated_rejection: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4067#issuecomment-5379133281
    direct_response: not used; the no-unfold repair added three public computation declarations, so a fresh four-lane review is required
    standard_review: repaired fixed-head four-lane math-lean-review completed with no blocking, major, or minor findings
    independent_final_reviews:
      - Math A: No major findings at repaired Lean content head fac123dd
      - Math B: No major findings at repaired Lean content head fac123dd
      - Lean A: No major findings at repaired Lean content head fac123dd
      - Lean B: No major findings at repaired Lean content head fac123dd
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4067#issuecomment-5379250808
    final_report_sync_head: d10ea2546a76a0222c60acd21c71a2e3ad216d49
    report_only_audit: no findings; 10a7fa36..d10ea254 changes only this report, all Lean, GOAL, umbrella, and manifest blobs are unchanged, the four verdicts and integrated comment are synchronized, and both reviewed and report-sync heads have 7/7 successful checks
  blocking_findings: []
  next_obligation: merge Cycle 30, then construct the producer-derived reindexing functor and its functor laws while retaining arbitrary-target FiniteModelLift as open
```

### Cycle 29 — arbitrary `Doct_U` pullbacks and a proper finite fiber

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 29
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 8c93c256d2763a2125600857af2da514dddd89ac
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 28 merge synchronization comment 5378335661 and Cycle 29 selection comment 5378412642
  proof_dag_predecessors:
    - G-101 exact extraction-doctrine category Doct_U and exact doctrine morphisms
    - Cycle 2 finite-code pullback presentation and ExtInst_U realization closure
    - Cycle 28 normalized generated-endpoint checkpoint, PR 4065 merge 8c93c256
  proof_obligation: discharge target conjunct (A) and ledger K0 by constructing the pullback of every exact-doctrine cospan in Doct_U without decidable-Atom, finiteness, point, or caller pullback premises; preserve every semantic cone's actual Atom equivalence; connect the existing finite-code pullback representation by an internally generated doctrine isomorphism; and fire a representation-invariant proper-fiber witness satisfying nonemptiness, canonical-pair non-surjectivity, two noninvertible projections, compatible and common-base-incompatible pairs
  selection_reason: the existing pullbackPresentation_isPullback theorem quantifies arbitrary pointed ExtInst_U cones only after fixing a finite-code cospan and therefore does not prove the unpointed arbitrary-Doct_U statement in (A). The old two-source constant cospan has every component pair compatible, so its canonical pair map is surjective and it cannot satisfy the K0 witness. A symmetric three-to-two cospan with table [0, 0, 1] supplies independent collisions in both projections and an incompatible product pair while keeping the pullback inhabited.
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/DoctrinePullback.lean
    - ResearchLean/AG/DoctrineFiberProduct/DoctrinePullbackFiniteCode.lean
    - ResearchLean/AG/DoctrineFiberProduct/DoctrinePullbackWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - weakening arbitrary Doct_U cospans to finite presentations, pointed instances, identity Atom maps, or cones carrying a supplied factor or pullback certificate
    - reusing pullbackPresentation_isPullback while silently dropping unpointed semantic cones
    - calling the old all-compatible two-to-one self-cospan a proper fiber
    - expressing the witness by raw equality or a cross-type intersection rather than typed common-base compatibility and an isomorphism-invariant property
    - proving projection noninvertibility only for an enumeration without connecting the finite-code and semantic pullback representations
    - promoting K0 to FiniteModelLift, K2-K4, or final theorem completion
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  content_head: 812c34c5943fb03c064ea6b1b01f82301d3109e0
  reviewed_content_head: 812c34c5943fb03c064ea6b1b01f82301d3109e0
  proof_obligation_delta: constructed DoctrinePullbackSource as the subtype of source pairs with equal common-base image and assembled doctrinePullback for every exact-doctrine cospan. The two generated projections commute; every semantic doctrine cone receives a unique factor whose Atom equivalence is exactly the cone first leg's actual equivalence, yielding doctrinePullback_isPullback with no DecidableEq, finite presentation, selected point, or caller certificate. ProperDoctrineFiber packages only the resulting nonempty-source, pair-map non-surjectivity, and two projection non-IsIso propositions; properDoctrineFiber_id_id_false supplies its general negative instance, while properDoctrineFiber_iff_of_iso proves invariance under internally commuting doctrine isomorphisms. The finite-code bridge builds an isomorphism from the decoded compatible-source rank/unrank representation to the arbitrary semantic producer, proves both projection graphs, and transports the pullback theorem to the decoded finite presentation in Doct_U. The symmetric three-by-three over two witness exhibits compatible pairs (0,0), (0,1), and (1,0), the common-base-incompatible component pair (0,2), non-surjectivity, independent collisions proving both projections noninvertible, transport of properness to the finite-code representation, and a nonidentity finite Atom swap cone whose universal factor retains that Atom map.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/DoctrinePullback.lean
    - ResearchLean/AG/DoctrineFiberProduct/DoctrinePullbackFiniteCode.lean
    - ResearchLean/AG/DoctrineFiberProduct/DoctrinePullbackWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - DoctrinePullbackSource
    - doctrinePullback
    - doctrinePullbackFst
    - doctrinePullbackSnd
    - doctrinePullback_commutes
    - doctrinePullbackLift
    - doctrinePullbackLift_atomEquiv
    - doctrinePullbackLift_fst
    - doctrinePullbackLift_snd
    - doctrinePullbackLift_unique
    - doctrinePullback_isPullback
    - ProperDoctrineFiber
    - properDoctrineFiber_id_id_false
    - properDoctrineFiber_iff_of_iso
    - doctrinePullbackFiniteCodeIso
    - doctrinePullbackFiniteCodeIso_hom_fst
    - doctrinePullbackFiniteCodeIso_hom_snd
    - pullbackPresentation_doctrine_isPullback
    - finiteProperFiberCompatible00
    - finiteProperFiberCompatible01
    - finiteProperFiberCompatible10
    - finiteProperFiberIncompatible02_commonBase_ne
    - finiteProperFiberIncompatible02_not_in_range
    - finiteProperDoctrinePullback_pairMap_not_surjective
    - finiteProperDoctrinePullback_fst_not_isIso
    - finiteProperDoctrinePullback_snd_not_isIso
    - finiteProperDoctrineFiber
    - finiteProperFiberFiniteCode_proper
    - finiteProperFiberFiniteCode_isPullback
    - finiteProperFiberSwapLift_componentC
  claim_mapping:
    theorem_names:
      - doctrinePullback_isPullback
      - properDoctrineFiber_iff_of_iso
      - pullbackPresentation_doctrine_isPullback
      - finiteProperDoctrineFiber
      - finiteProperFiberFiniteCode_proper
      - finiteProperFiberSwapLift_componentC
    source_labels:
      - target theorem (A) fiber product construction and universality in Doct_U
      - target theorem (A) finite realization-image proper-fiber witness
      - material-premise ledger K0
      - dullness filter excluding identity-Atom-only cone universality and empty pullbacks
    conjuncts:
      - every exact-doctrine cospan on every fixed carrier has an internally constructed pullback in Doct_U
      - universality ranges over every semantic doctrine cone and copies the first leg's arbitrary Atom equivalence into the generated factor
      - the proper finite fiber is inhabited, its canonical source-to-component-pair map is not surjective, and neither projection is an isomorphism
      - compatible pairs and an incompatible component pair are both typed over the same common-base maps
      - proper-fiber conclusions are invariant under commuting doctrine isomorphisms and transport to the existing finite-code pullback representation
      - a nonidentity Atom cone concretely fires the generic universal factor
    undischarged_assumptions:
      - fixed-ledger FiniteModelLift for arbitrary CartesianLiftNonexistence targets
      - K2-K4
      - final Doctrine Fiber Product and Base Change theorem assembly and completion review
    acceptance_point: candidate discharge of target conjunct (A) and K0 only; G-110 remains target-proof-checkpoint
    port_status: not-applicable
audits:
  premise_delta:
    ambient_boundary:
      - arbitrary fixed AtomCarrier U and the G-101 Doct_U category API
      - finite realization-image code calculus only for the required K0 witness and representation bridge
    input_geometry:
      - arbitrary DOne, DTwo, Base and exact morphisms sigmaOne, sigmaTwo
      - arbitrary PullbackCone sigmaOne sigmaTwo in the universal property
    discharge_required:
      - compatible-pair source subtype and componentwise normalization
      - both projection exactness laws and square commutativity
      - arbitrary-cone factorization and uniqueness including the Atom component
      - internally generated finite-code doctrine isomorphism and projection graphs
      - nonempty, non-surjective, two-noninvertible proper witness and its representation transport
    conclusion_equivalent_risk:
      - IsPullback, factor, factorization equations, properness, source equivalence, and projection invertibility are never producer inputs
    unused_or_ambient_only:
      - the selected point of FiniteInstanceCode is absent from the generic Doct_U producer
      - Cycle 28 strong-lift artifacts are predecessor context only and are unused by K0 proofs
  certificate_provenance:
    - compatibility of normalized pairs is generated from sigmaOne.normalize_eq, sigmaTwo.normalize_eq, and the input pair equality
    - the universal source pair is generated by evaluating the cone condition on every source
    - the second projection and second factorization Atom laws are derived from the cospan and cone equations
    - the finite-code source equivalence is compatibleSourceEquiv generated from the complete duplicate-free enumeration
    - ProperDoctrineFiber contains propositions only; its positive instance is proved from explicit pairs, range exclusion, and IsIso source-map injectivity, while the identity-projection pair gives an internally proved negative instance
  proof_use:
    - doctrinePullbackLift.atomEquiv is definitionally cone.fst.atomEquiv and doctrinePullbackLift_snd consumes cone.condition on atomEquiv
    - doctrinePullbackLift_unique consumes both factorization equations to identify both source components and the first equation to identify the Atom equivalence
    - doctrinePullbackFiniteCodeIso uses compatibleSourceEquiv in both hom directions and its projection graphs drive IsPullback.of_iso'
    - properDoctrineFiber_iff_of_iso transports nonemptiness and pair-map surjectivity through all three source equivalences and transports IsIso through the commuting projection graphs
  anti_weakening:
    verdict: pass
    notes:
      - generic construction has no DecidableEq, finiteness, point, presentation, factor, or pullback hypothesis
      - witness uses the selected symmetric three-to-two cospan rather than the all-compatible old fixture
      - no claim is made about intersections of differently typed Source values
  witness_nondegeneracy:
    - finiteProperFiberCompatible00 inhabits the pullback source
    - finiteProperFiberIncompatible02_commonBase_ne gives a typed unequal pair of common-base images
    - finiteProperFiberIncompatible02_not_in_range refutes surjectivity of the canonical component-pair map
    - independent pairs 00/01 and 00/10 collide under the first and second projections respectively
    - finiteProperFiberSwapCone_fst_componentC and finiteProperFiberSwapLift_componentC fire a nonidentity Atom equivalence
  structure_field_escape: none-found
  empty_elimination: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - focused DoctrinePullback.lean: pass; namespace audit 13 declarations and standard axioms only
    - targeted module DoctrinePullback: pass
    - focused DoctrinePullbackFiniteCode.lean after the instance-pair repair: pass; namespace audit 11 declarations and standard axioms only
    - targeted module DoctrinePullbackFiniteCode: pass
    - focused DoctrinePullbackWitnesses.lean: pass; namespace audit 42 declarations and standard axioms only
    - targeted module DoctrinePullbackWitnesses: pass
    - git diff --check, placeholder, hidden/BiDi Unicode, privacy, import-direction, manifest, and umbrella scans: pass
    - PR checks at report synchronization head f02bf3f8: 7/7 success; the Research-only lake build job is not counted as theorem elaboration evidence because its Lean build and kernel-audit steps were skipped
  review_refs:
    fixed_head: 7a5b66af9f468fa1a60b9ced1cc39ac55945fe98
    initial_integrated_rejection: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4066#issuecomment-5378950198
    direct_response: not used; the qualified instance-pair repair added a theorem declaration, so a fresh four-lane review was completed
    independent_final_reviews:
      - Math A: No major findings at repaired Lean content head 812c34c5
      - Math B: No major findings at repaired Lean content head 812c34c5
      - Lean A: No major findings at repaired Lean content head 812c34c5
      - Lean B: No major findings at repaired Lean content head 812c34c5
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4066#issuecomment-5378975237
    final_report_sync_head: f02bf3f8cbb1a4b718ce7c03cc09bf4dd20db09a
    report_only_audit: Math A no finding; Lean blobs unchanged and all review, scope, validation, and open-obligation references synchronized
  blocking_findings: []
  next_obligation: merge Cycle 29, then continue K2 while retaining arbitrary-target FiniteModelLift as open
```

### Cycle 28 — semantic-input lift transport and the remaining `FiniteModelLift` gap

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 28
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 2c34fb0c21a83dd4ed9b0701f849ee1e62564b22
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 27 merge synchronization comment 5377884640 and Cycle 28 selection comment 5378017080
  proof_dag_predecessors:
    - Cycle 26 reflected ambient universal property and strong lift, PR 4062
    - Cycle 27 realization-compatible finite-presentation ULift bridge, PR 4063 merge 2c34fb0c
  proof_obligation: transport every supplied strong-cartesian lift on the genuine rebased high realization and its internally transported selected target back to the direct high semantic lift; test whether completion through the selected core package, Cycle 26 reflection, and low-tail cancellation supplies the fixed-ledger universe-polymorphic FiniteModelLift without empty or pre-existing-global-lift escape
  selection_reason: Cycle 27 supplies source and target isomorphisms between the direct semantic lift and the rebased realization, but the Cycle 26 reflector consumes a completed generated arrow to the selected finite core package. The supplied prefix lift must therefore be conjugated across both endpoint isomorphisms, composed with the generated high completion tail, reflected as a full lift, and then structurally factored through the low completion tail. Returning only the reflected full composite would have the wrong target and would not transport the original prefix lift.
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteModelStrongLiftIsoTransport.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteModelLift.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteModelRealizationULiftWitnesses.lean
  risks:
    - accepting a source or target package isomorphism, transported package, lift, factor, or factorization certificate from the caller
    - replacing the genuine rebased realization by the direct semantic lift through an unsupported definitional equality
    - returning only the reflected completed lift instead of cancelling the low tail to recover the original realized prefix
    - reusing globalCartesianLift, the existing low generated cartesianness certificate, CartesianLiftNonexistence emptiness, or strongCartesianLiftOfTarget in the generic producer
    - presenting a one-way conditional no-lift transport as an equivalence of lift types or as an inhabited right-branch counterexample
    - promoting the selected generated-endpoint construction to arbitrary package transport, K0, K2-K4, or theorem completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  reviewed_content_head: faf83312acfbeb7b6b1d935bc5b38f044638b1f3
  proof_obligation_delta: constructed a total-package isomorphism for canonical CoreFiber transport over every base isomorphism and proved that its forward and inverse maps lie over the corresponding base maps. For every CartSemanticInputIso, target package, and supplied strong-cartesian lift on the second input at the internally transported target, pullStrongCartesianLift conjugates the supplied hom by the inverse source and target total isomorphisms, composes the three strong-cartesian legs, and uses the semantic-input commuting square to recover the first input exactly; its public triangle recovers the supplied hom. The completion experiment then transports a supplied finite-model prefix lift, composes the selected high tail, invokes the Cycle 26 reflector, and cancels the selected low tail by Mathlib IsStronglyCartesian.of_comp. A selective-two noninvertible input fires this data path and both triangles. Fixed-head review rejected counting the resulting conditional no-lift wrapper as FiniteModelLift: the source no-lift premise is impossible under strongCartesianLiftOfTarget and cartesianLiftNonexistence_isEmpty, the reflected domain and hom remain the pre-existing canonical generated low data, and the construction covers only inverse-package endpoints generated from a completion tail rather than an arbitrary CartesianLiftNonexistence.targetPackage. The conditional finiteModelLift_no_lift and named FiniteModelLift declarations were therefore removed. The surviving artifact is a normalized generated-endpoint proof checkpoint, and the fixed-ledger FiniteModelLift remains open.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteModelStrongLiftIsoTransport.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteModelLift.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteModelRealizationULiftWitnesses.lean
  evidence:
    - coreFiberLiftIsoOfIso
    - coreFiberLiftIsoOfIso_hom_isHomLift
    - coreFiberLiftIsoOfIso_inv_isHomLift
    - CartSemanticInputIso.pullStrongCartesianLift
    - CartSemanticInputIso.pullStrongCartesianLift_conjugation_triangle
    - finiteModelCompletedRebasedHighTarget
    - finiteModelCompletedPulledHighPrefixLift
    - finiteModelCompletedHighTransport_triangle
    - finiteModelCompletedHighLift
    - finiteModelReflectedCompletedLift
    - finiteModelReflectedCompletedLift_components
    - finiteModelCompletedLowFactor
    - finiteModelCompletedLowFactor_isHomLift
    - finiteModelCompletedLowFactor_triangle
    - finiteModelReflectCompletedStrongCartesianLift
    - finiteModelReflectCompletedStrongCartesianLift_triangle
    - finiteSelectiveTwoCompletedRebasedHighLift
    - finiteSelectiveTwoFiniteModelStrongLift
    - finiteSelectiveTwoFiniteModelHighTransport_triangle
    - finiteSelectiveTwoFiniteModelReflected_components
    - finiteSelectiveTwoFiniteModelStrongLift_triangle
    - finiteSelectiveTwoFiniteModelStrongLift_noninvertible
  claim_mapping:
    theorem_names:
      - CartSemanticInputIso.pullStrongCartesianLift
      - finiteModelReflectCompletedStrongCartesianLift
    source_labels:
      - target theorem B universe-polymorphic FiniteModelLift clause, as the still-open obligation tested by this checkpoint
      - target artifact list and material-premise ledger FiniteModelLift entries
      - Cycle 12 nonvacuous structural-route guard
    conjuncts:
      - every supplied lift on the internally transported target of an isomorphic semantic input pulls back to a lift on the original input
      - every realized finite-model prefix completed by a tail to the selected core reflects from a supplied rebased high lift to a strong-cartesian lift of that original prefix
      - the selective-two noninvertible fixture exercises the data producer on an actual high lift independently of any no-lift premise
    undischarged_assumptions:
      - arbitrary-target package transport for CartesianLiftNonexistence.targetPackage
      - a fixed-ledger nonexistence transport whose source is not the empty low no-lift premise
      - a route which does not retain the pre-existing generated low domain and hom from strongCartesianLiftOfTarget
      - K0 and K2-K4
      - final Doctrine Fiber Product and Base Change theorem assembly
    acceptance_point: useful semantic-input transport and normalized completion checkpoint only; fixed-ledger FiniteModelLift is not discharged
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - total-package isomorphism over every base isomorphism generated by canonical CoreFiber transport
      - supplied strong-cartesian lift transport along every CartSemanticInputIso at the internally transported target
      - completion of every realized finite-model prefix to the selected core package in low and high carriers
      - reflection of the completed high lift and structural cancellation of the low completion tail
      - actual selective-two firing over non-IsIso low and high bases
    remaining:
      - fixed-ledger FiniteModelLift for an actual arbitrary-target universe-zero counterexample, without empty/global-lift escape
      - K0
      - K2-K4
      - final target theorem assembly and independent completion review
  certificate_provenance:
    discharged:
      - coreFiberLiftIsoOfIso accepts only a base isomorphism and source package and computes the total isomorphism from coreFiberLift
      - pullStrongCartesianLift accepts only a semantic-input isomorphism, first-input target package, and supplied second-input lift; both total bridges and all strong-cartesian certificates are generated internally
      - finiteModelReflectCompletedStrongCartesianLift accepts only a realized input, authored completion tail, and supplied rebased high lift; the completion targets, tails, factors, and factorization laws are generated internally, while the normalized low/high anchors are inherited from Cycle 26
    unresolved:
      - Cycle 26 reflection returns the canonical generated low domain and hom and compares with the generated high lift; both anchors are defined through strongCartesianLiftOfTarget
      - no theorem covers an arbitrary CartesianLiftNonexistence.targetPackage
  proof_use:
    used:
      - supplied lift hom and isStronglyCartesian in the three-leg semantic-input conjugation
      - CartSemanticInputIso.hom_comm and both endpoint isomorphisms in the base equality and conjugation triangle
      - pulled high prefix lift and high inverse-package tail in the completed high lift
      - reflectNormalizedStrongCartesianLift and reflectNormalizedHighHom_components on that actual completed high lift
      - the Cycle 26 canonical low domain and hom and generated-high comparison anchor, both ultimately produced by strongCartesianLiftOfTarget
      - low inverse-package tail IsStronglyCartesian.map and fac to generate the original-prefix factor and its triangle
      - low tail strong cartesianness, reflected composite strong cartesianness, factor IsHomLift, and Mathlib IsStronglyCartesian.of_comp in the returned prefix lift
    unused:
      - globalCartesianLift
      - cartesianLiftNonexistence_isEmpty or any empty elimination
      - input.lowGeneratedLift.isStronglyCartesian or another pre-existing low generated certificate in the new generic producer
      - any caller-supplied package transport, endpoint equality, factor, universal-property packet, or low lift
  structure_field_escape: the support theorem accepts no conclusion certificate, but its Cycle 26 leg retains the existing generated low domain and hom; this prevents the support artifact from discharging the fixed-ledger transport
  route_integrity: pass for semantic-input conjugation and selected-tail cancellation; fail for the original claim that this is arbitrary-target FiniteModelLift
  target_fitting: none in the quantified support theorem or selective-two firing; coverage remains restricted to an authored tail into FiniteModel.corePackage
  vacuity: found in the removed no-lift wrapper because strongCartesianLiftOfTarget supplies the negated source lift and cartesianLiftNonexistence_isEmpty rules out every source counterexample
  one_way_as_equivalence: none found; no lift-type equivalence is claimed
  goal_or_report_reinterpretation: found in the initial 1ab7d108 report, which counted a nonempty data producer plus an empty conditional corollary as literal FiniteModelLift discharge; corrected by deleting the two declarations, documenting both generated anchors, and restoring the ledger item to open at faf83312
  validation_refs:
    - exact focused check FiniteModelStrongLiftIsoTransport.lean: pass, 9 namespace declarations and standard axioms only
    - exact focused repair check FiniteModelLift.lean: pass, 29 namespace declarations and standard axioms only
    - exact focused compatibility recheck FiniteModelRealizationULiftWitnesses.lean: pass, 16 namespace declarations and standard axioms only
    - targeted module builds for FiniteModelStrongLiftIsoTransport, FiniteModelRealizationULiftWitnesses, and FiniteModelLift: pass; no Research aggregate or full build
    - manifest and umbrella wiring, diff, placeholder, prohibited-dependency, hidden and bidirectional Unicode, privacy, and import-direction scans: pass locally
    - fixed GOAL blob and SHA256 lock: pass
  review_refs:
    independent_final_reviews:
      - Math A: No major findings at repaired Lean content head faf83312
      - Math B: No major findings at repaired Lean content head faf83312
      - Lean A: No major findings at repaired Lean content head faf83312
      - Lean B: No major findings at repaired Lean content head faf83312
    initial_integrated_rejection: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4065#issuecomment-5378233691
    direct_response: not used; the qualified rejection changed declarations and ledger status, so a fresh four-lane review was completed
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4065#issuecomment-5378318720
  blocking_findings: []
  next_obligation: construct K0 fiber product universality and its nondegenerate realization-image witness while keeping the arbitrary-target FiniteModelLift ledger item open; arbitrary-package transport requires a separately selected obligation unless a fixed-GOAL defect is established
```

### Cycle 27 — realization-compatible finite-presentation ULift bridge

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 27
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: f2f505b21d9e58d2bf4f740cb8a4a145bc246d4a
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 26 merge synchronization comment 5377705516 and Cycle 27 selection comment 5377743041
  proof_dag_predecessors:
    - Cycle 7 finite-code rebase and decoder component graphs, PR 4043
    - Cycle 13 through Cycle 26 selected generated-package lift reflection, ending at PR 4062 merge f2f505b2
  proof_obligation: bridge the exact realization boundary between the direct semantic ULift used by the reviewed generated-lift reflection and the genuine high-universe RealizableHom produced by rebasing a finite presentation; generate decoder-doctrine, pointed-instance, and arrow-category isomorphisms without caller certificates; instantiate the bridge on the noninvertible selective-two support-prefix presentation
  selection_reason: a rebased finite presentation has first-order source type FiniteSource at the target universe, while direct semantic lifting nests ULift over the low finite source; these endpoints are canonically isomorphic but not definitionally equal, so package and strong-lift transport must be built over an explicit generated semantic-input isomorphism
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteModelRealizationULift.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteModelRealizationULiftWitnesses.lean
  risks:
    - accepting an exact-doctrine, pointed-instance, or semantic-input isomorphism or equality certificate from the caller
    - replacing the rebased decoder input by the directly lifted semantic input through an unsupported definitional equality
    - claiming equivalence of all extraction instances or all packages across universes
    - using CartesianLiftNonexistence emptiness, globalCartesianLift, a package, or a strong lift to construct the realization bridge
    - promoting this decoder-level checkpoint to package transport, strong-lift reflection, FiniteModelLift, K0, or theorem completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  reviewed_content_head: aaed441477de5bec3b0e7dfe087adf2764813686
  proof_obligation_delta: defined direct semantic lifting for every finite-model CartSemanticInput; constructed mutually inverse exact doctrine morphisms between the directly lifted decoder doctrine and the decoder of the rebased finite code, with finite-source and Atom graphs; lifted them to pointed extraction-instance isomorphisms; assembled, for every finite presentation, a CartSemanticInputIso whose generated source and target isomorphisms make the lower arrow square commute; generated a genuine high-universe RealizableHom solely from the rebased presentation and exposed the corresponding semantic-input isomorphism for every low RealizableHom. The selective-two-to-support composite is now a named realized prefix of the reviewed generated arrow to FiniteModel.corePackage; both its low realization and every high-universe rebase identify two explicitly distinct source cells and are non-IsIso.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteModelRealizationULift.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteModelRealizationULiftWitnesses.lean
  evidence:
    - finiteModelLiftSemanticInput
    - finiteModelLiftDecodedDoctrineHom
    - finiteModelLiftDecodedDoctrineInv
    - finiteModelLiftDecodedDoctrineIso
    - finiteModelLiftDecodedDoctrineIso_hom_sourceMap
    - finiteModelLiftDecodedDoctrineIso_inv_sourceMap
    - finiteModelLiftDecodedInstanceIso
    - finiteModelLiftPresentationSemanticIso
    - finiteModelLiftPresentationSemanticIso_hom_comm
    - finiteModelLiftRealizableHom
    - finiteModelLiftRealizableHomSemanticIso
    - finiteSelectiveTwoToSupportPresentation
    - finiteSelectiveTwoToSupportInput
    - finiteSelectiveTwoToSupportInput_comp_core
    - finiteSelectiveTwoToSupportInput_not_isIso
    - finiteSelectiveTwoToSupportSemanticIso
    - finiteSelectiveTwoToSupportSemanticIso_hom_comm
    - finiteSelectiveTwoToSupportLiftedInput_not_isIso
  claim_mapping:
    theorem_names:
      - finiteModelLiftPresentationSemanticIso
      - finiteModelLiftRealizableHom
      - finiteModelLiftRealizableHomSemanticIso
    source_labels:
      - target theorem B FiniteModelLift universe transport clause
      - GOAL realization-image quantification and FiniteModelLift material-premise ledger
      - Cycle 12 graph-bearing nonvacuity guard
    conjuncts:
      - every low finite presentation generates a genuine rebased high RealizableHom
      - direct semantic lifting and rebased decoding are related by internally generated source and target isomorphisms
      - the lower-arrow square commutes as an actual CartSemanticInputIso field
      - the concrete noninvertible realized prefix remains noninvertible at every lifted universe
    undischarged_assumptions:
      - selected package transport along the generated target isomorphism
      - conversion of every supplied strong lift on the rebased realized input to the canonical-image high lift consumed by reflectNormalizedStrongCartesianLift
      - graph-bearing FiniteModelLift nonexistence corollary
      - K0 and K2-K4
    acceptance_point: realization-compatible finite-presentation ULift is proposed as a proof checkpoint only; the fixed FiniteModelLift ledger item remains open
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - direct semantic ULift for arbitrary finite-model semantic inputs
      - decoder-doctrine and pointed-instance finite-image isomorphisms
      - arrow-category semantic-input isomorphism for every finite presentation
      - genuine rebased RealizableHom producer
      - noninvertible selective-two realized firing in every universe
    remaining:
      - package and supplied-strong-lift transport along the generated endpoint isomorphisms
      - FiniteModelLift and graph-bearing nonexistence transfer
      - K0 and K2-K4
  certificate_provenance:
    discharged:
      - every generic producer accepts only a finite code, presentation, semantic input, or RealizableHom
      - all doctrine, instance, and semantic-input isomorphisms are computed internally from finiteSourceRebaseEquiv and finiteModelLiftCarrierEquiv
      - the concrete high realized arrow is generated from the rebased selective-two presentation
    unresolved: []
  proof_use:
    used:
      - finiteSourceRebaseEquiv in both directions of every decoder source isomorphism
      - FiniteDoctrineCode.toDoctrine_extracts_rebase_iff in both exactness proofs
      - toSemanticCart_rebase_atomEquiv and finiteModelLiftExtInstHom_atomEquiv in the lower-square proof
      - the realization_eq field only to align an arbitrary RealizableHom with its own authored presentation
    unused:
      - CartesianLiftNonexistence and cartesianLiftNonexistence_isEmpty
      - globalCartesianLift
      - any package, PackageTotalHom, StrongCartesianLift, or cartesianness certificate
      - reflectNormalizedStrongCartesianLift
  structure_field_escape: none found; no endpoint isomorphism, commuting-square proof, high semantic input, or realization equality is accepted as a replaceable caller certificate
  route_integrity: pass; finite presentation rebase generates the high RealizableHom, while the direct semantic lift is retained as a distinct endpoint connected only by the explicit generated arrow-category isomorphism
  target_fitting: none found; the generic bridge quantifies over every finite code, presentation, and realized arrow, and the selective-two fixture only fires that surface
  vacuity: none found; the generic isomorphism types are inhabited independently of no-lift premises, and the fixture proves concrete low and high non-IsIso arrows by two distinct source cells with equal images
  one_way_as_equivalence: none found; equivalence is claimed only between two canonical finite-image decoder objects, not arbitrary extraction instances or packages
  goal_or_report_reinterpretation: none found; package transport, supplied strong-lift conversion, FiniteModelLift, K0, K2-K4, and theorem completion remain open
  validation_refs:
    - exact focused check FiniteModelRealizationULift.lean: pass, 18 namespace declarations and standard axioms only
    - exact focused check FiniteModelRealizationULiftWitnesses.lean: pass, 16 namespace declarations and standard axioms only
    - targeted module builds for both new modules: pass; no Research aggregate or full build
    - manifest and umbrella wiring, diff, placeholder, prohibited-dependency, privacy, and import-direction scans: pass locally
    - fixed GOAL blob and SHA256 lock: pass
    - PR 4063 reviewed content head aaed441477de5bec3b0e7dfe087adf2764813686: 7/7 CI green and MERGEABLE/CLEAN
  review_refs:
    independent_final_reviews:
      - Math A — Pass / no findings for the Cycle 27 checkpoint
      - Math B — Pass / no findings for the Cycle 27 checkpoint
      - Lean A — Pass / no findings for the Cycle 27 checkpoint
      - Lean B — central Lean content pass; Minor report provenance finding: Cycle 7 predecessor was PR 4043, not PR 4037
    direct_response: repair aaed441477de5bec3b0e7dfe087adf2764813686..f479333f changes only the Cycle 7 predecessor reference from PR 4037 to PR 4043; the finding author independently confirmed the correction, unchanged Lean/GOAL/manifest blobs and claims, clean static scans, and no new finding
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4063#issuecomment-5377872815
  blocking_findings: []
  next_obligation: transport the selected lifted package and every supplied high strong lift along the generated endpoint isomorphisms, then feed the resulting canonical-image high lift to reflectNormalizedStrongCartesianLift and derive the graph-bearing FiniteModelLift nonexistence corollary without empty elimination
```

### Cycle 26 — reflected ambient universal property and strong lift

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 26
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 7672f958b7f9842dac7dc246a52914319c9ab3e0
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 25 merge synchronization comment 5377501393 and Cycle 26 selection comment 5377524422
  proof_dag_predecessors:
    - Cycle 16 exact ReflectedGeneratedComponentGraph and ReflectedGeneratedUniversalProperty output types, PR 4052
    - Cycle 17 explicit inverseCorePackageFactor uniqueness by upper inverse cancellation, PR 4053
    - Cycle 24 complete actual-high-derived generated SignedExactCoreReadingHom, PR 4060
    - Cycle 25 actual-high-derived PackageTotalHom, whole triangle, and arbitrary ambient factor with IsHomLift/fac, PR 4061 merge 7672f958
  proof_obligation: prove uniqueness for every ambient package/base/hom/candidate quantified by ReflectedGeneratedUniversalProperty; assemble the exact Cycle 16 reflected hom, component graph, universal-property, retraction, IsStronglyCartesian, and StrongCartesianLift declarations; and fire them on the noninvertible selective-two ambient problem without reusing the existing low cartesianness certificate
  selection_reason: Cycle 25 made factor existence and factorization materially dependent on the supplied high lift, leaving only arbitrary-candidate uniqueness and the fixed reflection packet/strong-lift assembly
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedReflectedUniversalProperty.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedReflectedUniversalPropertyWitnesses.lean
  risks:
    - using input.lowGeneratedLift.isStronglyCartesian, globalCartesianLift, a known low cartesianness certificate, or the existing low Mathlib map/uniq
    - returning an independently generated low factor instead of finiteGeneratedReflectedAmbientFactor while the supplied high lift is decorative
    - accepting a factor, universal-property packet, candidate preimage, uniqueness proof, or component graph from the caller
    - weakening the arbitrary ambient package/base/hom/candidate quantifiers to the selective-two fixture or an image-only category
    - claiming reflection of arbitrary high uniqueness when the accepted proof is high-driven factor/fac plus intrinsic inverse-package cancellation
    - promoting this exact reflection checkpoint to FiniteModelLift, K0, or theorem completion
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  reviewed_content_head: bc2cb28ac50c4de11859e9a04966fb4e9727568c
  proof_obligation_delta: proved that every arbitrary candidate for the Cycle 25 ambient factorization equals the actual-high-derived factor by applying inverseCorePackageFactor_unique to the candidate and to the generated factor and comparing their identical explicit normal forms. The generated factor comparison consumes its new IsHomLift and supplied-high-derived fac; no low strong-cartesian proof is used. Defined the exact Cycle 16 reflectNormalizedHighHom at the fixed generated low endpoint, generated its component graph internally, assembled ReflectedGeneratedUniversalProperty with the Cycle 25 factor and all four laws, proved the required one-direction retraction, and derived Mathlib IsStronglyCartesian solely from that packet. Packaged the result as a fresh StrongCartesianLift record with the exact generated domain and reflected hom. The selective-two witness instantiates the component packet, the full universal property, factor/lift/fac, arbitrary-candidate uniqueness, strong cartesianness, and the reflected strong lift on the existing noninvertible prefix and noninvertible composite competitor.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedReflectedUniversalProperty.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedReflectedUniversalPropertyWitnesses.lean
  evidence:
    - finiteGeneratedReflectedAmbientFactor_unique
    - reflectNormalizedHighHom
    - reflectNormalizedHighHom_base
    - reflectNormalizedHighHom_components
    - reflectNormalizedUniversalProperty
    - reflectNormalizedUniversalProperty_factor
    - reflectNormalizedHighHom_retraction
    - reflectNormalizedHighHom_isStronglyCartesian
    - reflectNormalizedStrongCartesianLift
    - reflectNormalizedStrongCartesianLift_domain
    - reflectNormalizedStrongCartesianLift_hom
    - finiteSelectiveTwoReflectNormalizedUniversalProperty_factor
    - finiteSelectiveTwoReflectNormalizedUniversalProperty_factor_isHomLift
    - finiteSelectiveTwoReflectNormalizedUniversalProperty_factor_fac
    - finiteSelectiveTwoReflectNormalizedUniversalProperty_factor_unique
    - finiteSelectiveTwoReflectNormalizedUniversalProperty_base_not_isIso
    - finiteSelectiveTwoReflectNormalizedUniversalProperty_competitor_base_not_isIso
    - finiteSelectiveTwoReflectNormalizedHighHom_isStronglyCartesian
    - finiteSelectiveTwoReflectNormalizedStrongCartesianLift
  claim_mapping:
    theorem_names:
      - reflectNormalizedHighHom
      - reflectNormalizedUniversalProperty
      - reflectNormalizedHighHom_isStronglyCartesian
      - reflectNormalizedStrongCartesianLift
    source_labels:
      - Cycle 16 exact_downstream_reflection_signature
      - GOAL material ledger FiniteModelLift remains discharge-required before K0
    conjuncts:
      - the exact reflected hom, base, components, universal-property, retraction, strong-cartesian theorem, strong lift, domain, and hom signatures are present without weakening
      - every ambient factor is finiteGeneratedReflectedAmbientFactor and retains the arbitrary package/base/hom quantifiers
      - every arbitrary candidate is compared by structural inverse-package cancellation after the generated factor's high-derived fac is established
      - Mathlib IsStronglyCartesian is constructed from the new packet and not from the existing low certificate
    undischarged_assumptions:
      - FiniteModelLift and graph-bearing generated nonexistence transfer
      - K0 and K2-K4 after the F0 ledger is resolved
    acceptance_point: exact Cycle 16 ambient reflection obligation is proposed as discharged; the unchanged theorem remains a target-proof-checkpoint because FiniteModelLift and later obligations are open
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - arbitrary ambient factor uniqueness at the exact ReflectedGeneratedUniversalProperty quantifiers
      - caller-free ReflectedGeneratedUniversalProperty producer
      - Mathlib strong cartesianness derived from the new packet
      - exact reflected StrongCartesianLift producer and domain/hom projections
      - noninvertible selective-two firing with arbitrary candidate quantification
    remaining:
      - FiniteModelLift and its generated nonexistence corollary without empty elimination
      - K0 and K2-K4 after the F0 ledger is resolved
  certificate_provenance:
    discharged:
      - the universal-property producer accepts only the finite input and supplied high lift
      - factor, IsHomLift, fac, uniqueness, component graph, and strong-cartesian proof are internally generated
      - the concrete factor and competitor IsHomLift premise are inherited from the reviewed Cycle 25 fixture
    unresolved: []
  proof_use:
    used:
      - finiteGeneratedReflectedAmbientFactor as the computational factor output for every ambient problem
      - finiteGeneratedReflectedAmbientFactor_isHomLift and finiteGeneratedReflectedAmbientFactor_fac in both uniqueness and packet assembly
      - inverseCorePackageFactor_unique only as structural cancellation for the arbitrary candidate and generated factor
      - canonicalLowGeneratedComponentComparison as the reviewed internally generated component packet
      - all four ReflectedGeneratedUniversalProperty fields in the Mathlib IsStronglyCartesian constructor
    unused:
      - input.lowGeneratedLift.isStronglyCartesian
      - globalCartesianLift
      - finiteGeneratedLowFactor and finiteGeneratedLowFactorUpper
      - arbitrary high package/hom rebase or reflected high uniqueness
  structure_field_escape: none found; no factor, universal property, component packet, candidate preimage, or uniqueness certificate is a producer argument
  route_integrity: proposed pass; factor value and fac are supplied-high-derived, while uniqueness is explicitly classified as intrinsic low inverse-package cancellation rather than arbitrary high uniqueness reflection
  target_fitting: none found; the generic theorem retains every ambient package/base/hom/candidate and the fixture only fires it
  vacuity: none found; the witness uses a non-IsIso prefix, a competitor over a non-IsIso composite, an inhabited generated factor, and an arbitrary-candidate uniqueness theorem
  one_way_as_equivalence: none found; no arbitrary cross-carrier package equivalence or high-package descent is claimed
  goal_or_report_reinterpretation: none found; FiniteModelLift, K0, K2-K4, and theorem completion remain open
  validation_refs:
    - official focused wrapper FiniteGeneratedLiftNaturality.lean after the review repair: pass, 235 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedReflectedUniversalProperty.lean: pass, 11 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedReflectedUniversalPropertyWitnesses.lean: pass, 16 namespace declarations and standard axioms only
    - targeted module build FiniteGeneratedReflectedUniversalProperty: pass; no Research aggregate or full build
    - manifest and umbrella wiring, diff, placeholder, prohibited-dependency, hidden/BiDi Unicode, privacy, and import-direction scans: pass locally
    - fixed GOAL blob and SHA256 lock: pass
    - PR 4062 reviewed content head bc2cb28ac50c4de11859e9a04966fb4e9727568c: 7/7 CI green and MERGEABLE/CLEAN
  review_refs:
    independent_final_reviews:
      - Math A — Major: component low_domain_point transitively reused input.lowGeneratedLift.isStronglyCartesian
      - Math B — same Major provenance finding
      - Lean A — Pass / no major findings at the initial content head
      - Lean B — same Major provenance finding
    direct_response: repair df7453e5923e86971af735659d5de5acb15a9294..bc2cb28ac50c4de11859e9a04966fb4e9727568c changed only the existing lowGeneratedLift_domain_point theorem proof body, replacing the low strong-cartesian certificate and IsHomLift.domain_eq route with direct inverse-package endpoint reduction; one independent read-only verifier confirmed the prohibited transitive dependency closed, all declaration signatures, definitions, instances, declaration counts, imports, witnesses, manifest, GOAL, and status unchanged, and no new finding in the repair range; a second four-lane review was therefore unnecessary under the shared review protocol
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4062#issuecomment-5377681573
  blocking_findings: []
  next_obligation: construct FiniteModelLift and its graph-bearing generated nonexistence transfer from the reflected strong lift, then proceed to K0 or fail closed with a formal obstruction
```

### Cycle 25 — generated total hom, whole triangle, and ambient factor

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 25
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 5b4d944cf7520396ae65e4ffdb389c8db0f24871
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 24 merge synchronization / Cycle 25 selection comment 5376955988
  proof_dag_predecessors:
    - Cycle 17 supplied-high generated prefix factor and exact high factorization triangle, PR 4053
    - Cycle 18 through Cycle 23 generated-image descent for every computational upper field
    - Cycle 24 complete actual-high-derived SignedExactCoreReadingHom, PR 4060 merge 5b4d944c
  proof_obligation: pair the actual-high-derived lower and complete upper components into the exact generated low PackageTotalHom; descend the supplied high factorization through all seven computational SignedExactCoreReadingHom fields to prove the whole generated prefix triangle; use that triangle to construct, for every ambient low competitor, a factor with IsHomLift and factorization laws; and fire the same construction on a noninvertible selective-two fixture without claiming ambient uniqueness or strong cartesianness
  selection_reason: Cycle 24 completed the generated low upper, but the lower-upper compatibility, whole composition triangle, and arbitrary ambient factor remained absent
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedPackageTotalHomAssembly.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedUpperCompositionEquationDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationTransportCompositionDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedContextEquivalenceCompositionDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedObservableCompositionDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationTransportWholeCompositionDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedUpperCompositionOperationSignatureDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedPackageTotalHomTriangle.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedPackageTotalHomTriangleWitnesses.lean
  risks:
    - returning the existing low inverse-package factor or rewriting the actual normalized high factor wholesale to its canonical factor
    - proving only the Atom or object component of the upper triangle while leaving a dependent equation, operation, invariant, axis, or coordinate field unreflected
    - using thin context categories or the rigidity of Int observables to invent object or observable equalities without the actual high factorization
    - accepting a low total hom, upper, factor, image, preimage, equality, or composition certificate from the caller
    - constructing an ambient factor from the existing low cartesianness proof while the supplied high lift is decorative
    - promoting factor existence and factorization to uniqueness, reflected strong cartesianness, FiniteModelLift, K0, or theorem completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  reviewed_content_head: 4de0c83d784a2bb13899e5304156dfda1273e965
  proof_obligation_delta: paired the actual-high-derived reflected base and Cycle 24 complete upper into the exact PackageTotalHom between the outer and inner generated low domains, with lower-upper Atom compatibility, projection equality, IsHomLift, and high-image graphs. Projecting finiteGeneratedNormalizedHighFactor_fac to the supplied high upper gives the sole whole-factorization source. Its objectMap projection is evaluated on every lifted low object, aligned with the complete reflected-object high image and both generated upper object graphs, and reflected only on the shared opaque carrier shape. Its operationMap projection is evaluated on every generated high operation, transported through the reflected-operation image, and reflected through both generated operation images; endpoint and Atom-map equality are taken only after this actual high value equality. The same high upper equality is descended to the remaining exact low Atom, context, equation-index, all-context observable-family, invariant, axis, and dependent coordinate composition equalities. These pieces assemble the complete equation-transport HEq and all seven computational SignedExactCoreReadingHom fields. SignedExactCoreReadingHom.ext then proves the upper composition equality, and PackageTotalHom.ext proves the exact whole generated prefix triangle. For every ambient package, base, competitor hom, and IsHomLift premise, the new ambient factor is the existing vertical-to-outer decomposition followed by this supplied-high-derived total hom; its IsHomLift and factorization laws use both legs and the whole triangle. No uniqueness theorem is asserted. A selective-two fixture constructs one total hom over a non-IsIso base, routes all eighteen Cycle 24 upper observations through it, fires the whole triangle, and constructs a concrete ambient factor for a generated competitor whose composite base is also non-IsIso.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedPackageTotalHomAssembly.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedUpperCompositionEquationDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationTransportCompositionDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedContextEquivalenceCompositionDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedObservableCompositionDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationTransportWholeCompositionDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedUpperCompositionOperationSignatureDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedPackageTotalHomTriangle.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedPackageTotalHomTriangleWitnesses.lean
  evidence:
    - FiniteGeneratedReflectedPackageTotalHomOutput
    - finiteGeneratedReflectedPackageTotalHom
    - finiteGeneratedReflectedPackageTotalHom_base_eq
    - finiteGeneratedReflectedPackageTotalHom_upper
    - finiteGeneratedReflectedPackageTotalHom_projection_eq
    - finiteGeneratedReflectedPackageTotalHom_isHomLift
    - finiteGeneratedReflectedPackageTotalHom_base_high_image
    - finiteGeneratedReflectedPackageTotalHom_atom_high_image
    - finiteGeneratedNormalizedHighFactor_upper_fac
    - finiteGeneratedReflectedUpper_comp_atomEquiv
    - finiteGeneratedReflectedUpper_comp_objectMap
    - finiteGeneratedReflectedUpper_comp_contextEquivalence
    - finiteGeneratedReflectedUpper_comp_equationEquiv
    - finiteGeneratedReflectedUpper_comp_observable_high_image
    - finiteGeneratedReflectedUpper_comp_observableEquiv
    - finiteGeneratedReflectedUpper_comp_equationTransport
    - finiteGeneratedReflectedUpper_comp_operationMap
    - finiteGeneratedReflectedUpper_comp_invariantMap
    - finiteGeneratedReflectedUpper_comp_axisMap
    - finiteGeneratedReflectedUpper_comp_coordinateEquiv
    - finiteGeneratedReflectedUpper_comp
    - finiteGeneratedReflectedPackageTotalHom_fac
    - finiteGeneratedReflectedAmbientFactor
    - finiteGeneratedReflectedAmbientFactor_isHomLift
    - finiteGeneratedReflectedAmbientFactor_fac
    - finiteSelectiveTwoReflectedPackageTotalHom
    - finiteSelectiveTwoReflectedPackageTotalHom_base_not_isIso
    - finiteSelectiveTwoReflectedPackageTotalHom_upper_eq
    - finiteSelectiveTwoReflectedPackageTotalHom_fac
    - finiteSelectiveTwoGeneratedAmbientCompetitor_base_not_isIso
    - finiteSelectiveTwoReflectedAmbientFactor
    - finiteSelectiveTwoReflectedAmbientFactor_isHomLift
    - finiteSelectiveTwoReflectedAmbientFactor_fac
  claim_mapping:
    fixed_goal_clauses:
      - target theorem B and the material ledger retain FiniteModelLift as discharge-required before K0
      - the premise policy forbids caller-supplied transported packages, low preimages, image membership, hom graphs, and conclusion-equivalent certificates
      - F0 proof checkpoints may be split, but each artifact must remain connected to the unchanged final output
    runtime_route_constraints:
      - the supplied high lift and its actual normalized factorization must drive the generated total hom triangle and ambient factorization
      - all seven computational SignedExactCoreReadingHom fields must be descended before a whole upper or total-hom equality is claimed
      - context and observable descent must retain full object and all-value quantification; thinness and rigid selected semantics cannot supply missing data
      - ambient uniqueness and strong cartesianness may not be inferred from factor existence and factorization alone
    source_facts:
      - finiteGeneratedReflectedPackageTotalHom is a literal base-plus-upper assembly and its upper is the Cycle 24 actual-high-derived SignedExactCoreReadingHom
      - finiteGeneratedNormalizedHighFactor_upper_fac is obtained by projecting the supplied high factorization, not by replacing it with the canonical low factor
      - the object composition theorem projects objectMap from that high equality on every lifted object before complete reflected-object and generated-upper image alignment
      - the operation composition theorem projects operationMap from that high equality on every generated high operation before reflecting its configuration Atom map
      - finiteGeneratedReflectedUpper_comp applies SignedExactCoreReadingHom.ext to Atom, object, equation transport, operation, invariant, axis, and coordinate descents
      - finiteGeneratedReflectedPackageTotalHom_fac applies PackageTotalHom.ext to the descended base and complete upper equations
      - finiteGeneratedReflectedAmbientFactor contains the supplied-high-derived total hom as its second computational leg for every ambient competitor
      - the fixture reads all eighteen upper observations and the triangle from one assembled total hom and separately fires the arbitrary ambient-factor API
    consequence:
      - an exact generated low PackageTotalHom and its whole composition triangle are now available
      - every ambient low competitor has a generated factor with the required IsHomLift and factorization laws
      - ambient uniqueness, the reflected universal-property packet, reflected strong cartesianness, and FiniteModelLift remain open
audits:
  premise_delta:
    discharged:
      - exact lower-upper assembly into the generated low PackageTotalHom
      - all seven computational-field descents for the whole generated prefix triangle
      - arbitrary ambient low factor existence, IsHomLift, and factorization
      - one noninvertible selective-two fixture firing the total hom, triangle, and ambient factor
    remaining:
      - ambient factor uniqueness with an accepted provenance route
      - ReflectedGeneratedUniversalProperty and reflected generated strong cartesianness
      - FiniteModelLift and generated nonexistence transfer
      - K0 and K2-K4 after the F0 ledger is resolved
  certificate_provenance:
    discharged:
      - the total-hom and ambient-factor producers accept only input, supplied high lift, ambient package/base/hom, and the ordinary IsHomLift premise
      - all endpoint, image, context, equation, observable, operation, invariant, axis, coordinate, composition, and factorization equalities are internally generated
      - the fixture derives its total hom, competitor, IsHomLift instance, and ambient factor from named selective-two data
    prohibited_and_absent:
      - finiteGeneratedLowFactor, finiteGeneratedLowFactorUpper, caller low preimages or image certificates, globalCartesianLift, input.lowGeneratedLift.isStronglyCartesian, and Classical.choose of a low preimage
      - direct or wholesale use of finiteGeneratedNormalizedHighFactor_eq_canonical as the low triangle proof source; the predecessor complete-object image theorem may use canonical comparison only to establish its internally generated endpoint and opaque-carrier alignment, while the Cycle 25 object and operation equalities are driven by the corresponding projections of the actual high factorization
  proof_use:
    used:
      - the actual supplied-high factorization in finiteGeneratedNormalizedHighFactor_upper_fac and every downstream whole-composition descent
      - the Cycle 24 actual-high-derived lower and complete upper in the total-hom assembly
      - the objectMap projection of the actual high equality, complete reflected-object high image, and both generated upper object images for every low architecture object
      - the operationMap projection of the actual high equality, reflected-operation high image, and both generated operation images for every low generated operation
      - actual high context objects, maps, unit/counit, index values, and observable values in the dependent equation-transport descent
      - all seven computational upper fields in SignedExactCoreReadingHom.ext
      - both legs of the ambient factor in its IsHomLift and factorization proofs
    not_yet_available:
      - a high-driven proof of uniqueness for every arbitrary low candidate
      - the completed reflected ambient universal property and strongly cartesian lift
  structure_field_escape: none; no target-facing producer accepts a total hom, upper, factor, image, preimage, graph, equality, or uniqueness certificate
  route_integrity: pass for generated total-hom assembly, whole triangle, and ambient factor existence/factorization only; uniqueness and strong cartesianness remain open
  target_fitting: none found in the generic implementation; the ambient factor theorem retains arbitrary package, base, competitor hom, and IsHomLift quantification
  vacuity: none found at this checkpoint; the fixture uses a non-IsIso base, all eighteen upper observations, an exact whole triangle, and a concrete generated competitor with non-IsIso composite base
  proof_irrelevance_scope: proof fields inside equation transport and the complete upper are eliminated only after every computational field has been matched; no computational equality is obtained from proof irrelevance
  goal_or_report_reinterpretation: none; ambient uniqueness, ReflectedGeneratedUniversalProperty, reflected strong cartesianness, FiniteModelLift, K0, and theorem completion remain open
  validation_refs:
    - official focused wrapper FiniteGeneratedPackageTotalHomAssembly.lean: pass, 11 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedUpperCompositionEquationDescent.lean: pass, 5 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedEquationTransportCompositionDescent.lean: pass, 4 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedContextEquivalenceCompositionDescent.lean: pass, 6 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedObservableCompositionDescent.lean: pass, 2 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedEquationTransportWholeCompositionDescent.lean: pass, 1 namespace declaration and standard axioms only
    - official focused wrapper FiniteGeneratedUpperCompositionOperationSignatureDescent.lean: pass, 4 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedPackageTotalHomTriangle.lean: pass, 6 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedPackageTotalHomTriangleWitnesses.lean: pass, 34 namespace declarations and standard axioms only
    - targeted module builds for all nine Cycle 25 modules: pass; used only to materialize oleans for dependent focused imports
    - no Research aggregate or full build
    - manifest and umbrella wiring, diff, placeholder, hidden/BiDi Unicode, privacy, and import-direction scans: pass locally
    - fixed GOAL blob and SHA256 lock: pass
    - PR 4061 reviewed content head 4de0c83d784a2bb13899e5304156dfda1273e965: 7/7 CI green and MERGEABLE/CLEAN
  review_refs:
    independent_final_reviews:
      - Math A — Pass / no major findings at the initial content head
      - Math B — Pass / no major findings at the initial content head
      - Lean A — Pass / no major findings at the initial content head
      - Lean B — objectMap and operationMap proof-use Major plus private-docstring Minor; all repaired in the eligible direct-response range
    direct_response: repair 2b04755c0c43b47931bd57abc274ee1a6be63812..4de0c83d784a2bb13899e5304156dfda1273e965 changed only the two theorem proof bodies, private docstrings, and finding-specific report provenance prose; one independent read-only verifier confirmed both Major findings and the Minor closed, theorem and def statements, def and instance bodies, declaration set and counts, imports, and report status unchanged, all required scans clean, and no new finding in the repair range; a second four-lane review was therefore unnecessary under the shared review protocol
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4061#issuecomment-5377480849
  stop_condition: none; continue before K0
  blocking_findings: []
  next_obligation: determine and implement an accepted provenance route for arbitrary ambient factor uniqueness, then assemble the exact reflected universal-property packet and strongly cartesian generated lift without reusing the existing low cartesianness proof
```

### Cycle 24 — complete actual-high-derived generated upper

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 24
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 86467f9221f03f920f79b4dca0ebc4060411817e
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 23 merge synchronization / Cycle 24 selection comment 5376513253
  proof_dag_predecessors:
    - Cycle 19 complete actual-high architecture-object image descent, PR 4055
    - Cycle 22 complete actual-high-derived EquationSystemExactTransport, PR 4058
    - Cycle 23 actual-high-derived operation, invariant, axis, and coordinate computational fields, PR 4059 merge 86467f92
  proof_obligation: reflect the nine remaining SignedExactCoreReadingHom proof fields directly from the corresponding fields of the actual normalized high factor; assemble the exact existing eighteen-field generated low SignedExactCoreReadingHom without a custom packet or additional premise; export every field projection; and fire the complete assembly on the selective-two noninvertible fixture with the available nonconstant controls
  selection_reason: Cycle 23 supplied all remaining computational fields and genuine generated-image equivalences, leaving exactly the structural, detector, operation-naturality, invariant, and signature proof fields plus direct upper assembly
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedUpperStructuralLawDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedDetectorLawDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedOperationNaturalityDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedInvariantSignatureLawDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedUpperAssembly.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedUpperAssemblyWitnesses.lean
    - finiteGeneratedReflectedSignedExactCoreReadingHom
  risks:
    - returning or record-updating finiteGeneratedLowFactorUpper while the supplied high lift is ignored
    - rewriting the actual normalized high factor wholesale to its canonical factor before a reflected law is produced
    - using a known low law as the proof while the corresponding actual high law occurs only in a sibling proposition or no-op rewrite
    - accepting a low upper, law packet, image or preimage, equivalence, landing graph, or round-trip certificate from the caller
    - replacing complete object formation by configuration-only descent or assuming a generic inverse for opaque ArchitectureObject fields
    - simplifying the rigid PUnit, True, or constant-coordinate fields before consuming their actual high laws
    - presenting the completed generated upper as a whole PackageTotalHom, ambient strong-lift reflection, FiniteModelLift, K0, or theorem completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  reviewed_content_head: 3c345062932f71288f5f701df312247cc082e1b5
  proof_obligation_delta: directly reflected configuration_eq, extraction_eq, composition_eq, object_formation_eq, detectorCode_eq, operation_naturality, invariant_transport, axis_selected_iff, and coordinate_eq from the corresponding nine fields of the actual normalized high upper. Each proof first consumes its actual field and then descends through the internally generated Atom, family, configuration, complete architecture-object, equation-index, detector, operation, invariant, axis, or dependent-coordinate images. The object-formation proof remains specialized to the generated finite object reading and does not assert a generic inverse for arbitrary opaque high objects. The accepted Cycle 18 through Cycle 23 data producers, complete equation transport, and these nine laws are assembled literally into the existing SignedExactCoreReadingHom type between the outer and inner generated low domains. The producer accepts only the finite generated input, supplied high strong-cartesian lift, and ambient base arrow, and exports eighteen auditable field projections. A single selective-two producer fires all eighteen projections: distinct all and empty families, cyclic and acyclic object inputs, accepted and rejected detector data on both the generated source and assembled target codes, a nonidentity collapse operation and its naturality square, the complete seven-field equation transport, and coordinate value 3 with an inverse round trip. Singleton invariant and axis laws and the constant coordinate-read law are fired without a false sensitivity claim. Whole PackageTotalHom descent, ambient factor reflection, FiniteModelLift, K0, and theorem completion remain unclaimed.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedUpperStructuralLawDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedDetectorLawDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedOperationNaturalityDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedInvariantSignatureLawDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedUpperAssembly.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedUpperAssemblyWitnesses.lean
  evidence:
    - finiteGeneratedReflectedConfiguration_eq
    - finiteGeneratedReflectedExtraction_eq
    - finiteGeneratedReflectedComposition_eq
    - finiteGeneratedReflectedObjectFormation_eq
    - finiteGeneratedActualHighDetectorCode_eq
    - finiteGeneratedReflectedDetectorCode_eq
    - finiteGeneratedReflectedDetectorCode_eval_high_image
    - finiteGeneratedReflectedOperationMap_naturality
    - finiteGeneratedReflectedInvariant_transport
    - finiteGeneratedReflectedAxis_selected_iff
    - finiteGeneratedReflectedCoordinate_eq
    - FiniteGeneratedReflectedSignedExactCoreReadingHomOutput
    - finiteGeneratedReflectedSignedExactCoreReadingHom
    - finiteGeneratedReflectedSignedExactCoreReadingHom_atomEquiv
    - finiteGeneratedReflectedSignedExactCoreReadingHom_extraction_eq
    - finiteGeneratedReflectedSignedExactCoreReadingHom_composition_eq
    - finiteGeneratedReflectedSignedExactCoreReadingHom_objectMap
    - finiteGeneratedReflectedSignedExactCoreReadingHom_object_formation_eq
    - finiteGeneratedReflectedSignedExactCoreReadingHom_configurationMap
    - finiteGeneratedReflectedSignedExactCoreReadingHom_configurationMap_atomMap
    - finiteGeneratedReflectedSignedExactCoreReadingHom_configuration_eq
    - finiteGeneratedReflectedSignedExactCoreReadingHom_equationTransport
    - finiteGeneratedReflectedSignedExactCoreReadingHom_detectorCode_eq
    - finiteGeneratedReflectedSignedExactCoreReadingHom_operationMap
    - finiteGeneratedReflectedSignedExactCoreReadingHom_operation_naturality
    - finiteGeneratedReflectedSignedExactCoreReadingHom_invariantMap
    - finiteGeneratedReflectedSignedExactCoreReadingHom_invariant_transport
    - finiteGeneratedReflectedSignedExactCoreReadingHom_axisMap
    - finiteGeneratedReflectedSignedExactCoreReadingHom_coordinateEquiv
    - finiteGeneratedReflectedSignedExactCoreReadingHom_axis_selected_iff
    - finiteGeneratedReflectedSignedExactCoreReadingHom_coordinate_eq
    - finiteSelectiveTwoReflectedSignedExactCoreReadingHom
    - finiteSelectiveTwoReflectedSignedExactCoreReadingHom_atomEquiv_nonconstant
    - finiteSelectiveTwoReflectedSignedExactCoreReadingHom_composition_eq
    - finiteSelectiveTwoReflectedSignedExactCoreReadingHom_object_formation_eq
    - finiteSelectiveTwoDetectorSourceIndex
    - finiteSelectiveTwoOuterCycleQueryDatum
    - finiteSelectiveTwoOuterEmptyQueryDatum
    - finiteSelectiveTwoReflectedSignedExactCoreReadingHom_detectorCode_eq
    - finiteSelectiveTwoReflectedSignedExactCoreReadingHom_operationMap
    - finiteSelectiveTwoReflectedSignedExactCoreReadingHom_operation_naturality
    - finiteSelectiveTwoReflectedSignedExactCoreReadingHom_equationTransport
    - finiteSelectiveTwoReflectedSignedExactCoreReadingHom_coordinateEquiv_value_three
    - finiteSelectiveTwoReflectedSignedExactCoreReadingHom_coordinate_eq_constant_law
  claim_mapping:
    fixed_goal_clauses:
      - target theorem B and the material ledger retain FiniteModelLift as discharge-required before K0
      - the premise policy forbids caller-supplied transported packages, hom graphs, low preimages, image membership, and conclusion-equivalent certificates
      - F0 proof checkpoints may be split, but each artifact must remain connected to the unchanged final output
    runtime_route_constraints:
      - Issue 4034 requires all nine law proofs to consume the corresponding actual normalized high fields directly
      - generated endpoint equalities may align dependent types but may not replace an actual high field by a known low or canonical upper
      - complete object data, not only configurations, must be used for object formation and dependent laws
      - rigid selected semantics require direct proof-term dependency and honest witness language rather than invented sensitivity
      - this upper checkpoint may not be promoted to whole total-hom descent or ambient cartesianness reflection
    source_facts:
      - the four structural proofs use actual upper configuration_eq, extraction_eq, composition_eq, and object_formation_eq before generated-image descent
      - the detector, operation, invariant, selected-axis, and coordinate proofs directly use the matching five actual high fields
      - finiteGeneratedReflectedSignedExactCoreReadingHom is a literal eighteen-field record assembled from accepted named producers and the nine new named laws
      - the output alias depends only on the two low endpoints, while the producer takes and uses the supplied high lift
      - every fixture theorem reads a field of the single assembled selective-two hom rather than reconstructing a known low upper
    consequence:
      - the exact generated low SignedExactCoreReadingHom between the outer and inner inverse-package domains is now available
      - all eighteen upper fields have public projection theorems and a concrete noninvertible fixture firing
      - the next obligation is whole PackageTotalHom descent and the equality or composition reflection needed for ambient factors
audits:
  premise_delta:
    discharged:
      - all nine remaining actual-high-derived SignedExactCoreReadingHom proof fields
      - exact eighteen-field generated low upper assembly
      - one assembled noninvertible fixture firing all eighteen projections with all available nonconstant controls
    remaining:
      - exact lower and upper pairing into a whole PackageTotalHom descended from the actual normalized high factor
      - whole-hom image, composition, and equality-reflection laws sufficient to reflect high-generated factors
      - high-driven ambient low factorization and uniqueness
      - FiniteModelLift and generated nonexistence transfer
      - K0 and K2-K4 after the F0 ledger is resolved
  certificate_provenance:
    discharged:
      - every top-level law and assembly producer accepts only input, supplied high lift, base, and the mathematically quantified family, configuration, object, index, operation, or axis arguments
      - family, configuration, complete object, detector, operation, invariant, axis, coordinate, and equation images are internally generated
      - the fixture derives its data and base from existing named selective-two constructions and applies the assembled producer once
    prohibited_and_absent:
      - finiteGeneratedLowFactorUpper, finiteGeneratedNormalizedHighFactor_eq_canonical, a caller low upper or law packet, globalCartesianLift, Classical.choose of a low preimage, and empty elimination
  proof_use:
    used:
      - all four actual structural laws in FiniteGeneratedUpperStructuralLawDescent
      - the actual detectorCode_eq in FiniteGeneratedDetectorLawDescent
      - the actual operation_naturality in FiniteGeneratedOperationNaturalityDescent
      - the actual invariant_transport, axis_selected_iff, and coordinate_eq in FiniteGeneratedInvariantSignatureLawDescent
      - all accepted actual-derived data producers and the complete actual-derived equation transport in the final assembly
      - all eighteen assembled projections in the single selective-two fixture
    not_yet_available:
      - a complete actual-high-derived PackageTotalHom
      - composition and equality reflection for arbitrary generated-image factor homs
      - an ambient low universal-property producer driven by the supplied high lift
  structure_field_escape: none; neither a target-facing law nor the assembly accepts a law, image, inverse, upper, or completion certificate, and the fixture constructs no replacement record
  route_integrity: pass for the complete generated upper only; whole total-hom descent and ambient reflection remain open
  target_fitting: none found in the generic implementation; all structure fields retain their full quantification and the fixture only instantiates them
  vacuity: none found at the assembly level; the fixture uses distinct family and object inputs, positive and negative detector controls, a nonidentity operation, and coordinate values 3 and 0, while rigid fields are classified explicitly
  proof_irrelevance_scope: invariant and signature indices are PUnit, their selected predicates are True, and the coordinate reading is constant 0; these proof fields are audited by direct dependency rather than a false nontriviality claim
  goal_or_report_reinterpretation: none; whole PackageTotalHom descent, ambient reflection, FiniteModelLift, K0, and theorem completion remain open
  validation_refs:
    - official focused wrapper FiniteGeneratedUpperStructuralLawDescent.lean: pass, 10 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedDetectorLawDescent.lean: pass, 5 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedOperationNaturalityDescent.lean: pass, 5 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedInvariantSignatureLawDescent.lean: pass, 3 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedUpperAssembly.lean: pass, 20 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedUpperAssemblyWitnesses.lean: pass after detector-control repair, 22 namespace declarations and standard axioms only
    - targeted module checks for the four law modules, the assembly module, and required predecessor witness modules: pass; used only to materialize oleans for dependent focused imports
    - no Research aggregate or full build
    - manifest and umbrella wiring, diff, placeholder, hidden/BiDi Unicode, privacy, and import-direction scans: pass locally
    - fixed GOAL blob and SHA256 lock: pass
    - PR 4060 reviewed content head 3c345062932f71288f5f701df312247cc082e1b5: 7/7 CI green and MERGEABLE/CLEAN
    - metadata and docstring synchronization 266d21d0a351c2445ab8c1adcc6fbec84d6a831f: all four direct-response reviews passed, 7/7 CI green, and MERGEABLE/CLEAN
  review_refs:
    independent_final_reviews:
      - Math A — one Minor report and PR synchronization finding; repaired and direct-response closure passed
      - Math B — one overlapping Minor report and PR synchronization finding; repaired and direct-response closure passed
      - Lean A — report and PR synchronization plus one docstring precision Minor; repaired and direct-response closure passed
      - Lean B — one overlapping Minor report and PR synchronization finding; repaired and direct-response closure passed
    direct_response: detector-control repair d2e03ee7b76498640be3abff09148bf0056cbc30..3c345062932f71288f5f701df312247cc082e1b5 received a new four-lane fresh review; metadata and docstring range 3c345062932f71288f5f701df312247cc082e1b5..266d21d0a351c2445ab8c1adcc6fbec84d6a831f then changed only reviewed-head and declaration-count evidence, source/target detector wording, and fixture-only backward-upper provenance; Math A/B and Lean A/B all returned Pass
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4060#issuecomment-5376884165
  stop_condition: none; continue before K0
  blocking_findings: []
  next_obligation: assemble an actual-high-derived whole PackageTotalHom from the reflected lower and complete upper components, prove its generated-image and projection laws, and add the composition or equality reflection needed before retrying ambient strong-lift reflection
```

### Cycle 23 — actual generated upper computational maps

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 23
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 2ba9d35edb66f536300903ccc14b4a068b757e14
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 22 merge synchronization / Cycle 23 selection comment 5376198751
  proof_dag_predecessors:
    - Cycle 19 complete actual-high architecture-object image descent, PR 4055
    - Cycle 20 actual generated context-equivalence reflection, PR 4056
    - Cycle 22 complete actual-high-derived EquationSystemExactTransport, PR 4058 merge 2ba9d35e
  proof_obligation: construct genuine two-sided generated-domain images for operations, invariant indices, signature axes, and dependent coordinates; define the reflected operationMap, invariantMap, axisMap, and coordinateEquiv by reading the corresponding computational fields of the actual normalized high factor; prove all-input forward and inverse image graphs and round trips; and fire the exact proof-used constructions on the noninvertible selective-two fixture without claiming the remaining SignedExactCoreReadingHom laws
  selection_reason: Cycle 22 discharged the complete equationTransport field, while the four remaining computational upper fields still lacked actual-high-derived low producers and two-sided generated-image APIs
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedOperationMapDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedInvariantSignatureMapDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedUpperComputationalWitnesses.lean
    - finiteGeneratedReflectedOperationMap
    - finiteGeneratedReflectedInvariantMap
    - finiteGeneratedReflectedAxisMap
    - finiteGeneratedReflectedCoordinateEquiv
  risks:
    - returning finiteGeneratedLowFactorUpper or updating a known low upper while the supplied high fields occur only in sibling propositions
    - rewriting the actual normalized high factor to its canonical factor before its operationMap, invariantMap, axisMap, or coordinateEquiv supplies the reflected computational value
    - accepting a low map, image equivalence, inverse, endpoint graph, or round-trip certificate from the caller
    - treating one-way operation lifting as a genuine image equivalence without arbitrary-high inverse coverage
    - casting an actual operation through complete object-image endpoints in the wrong direction
    - treating the selected PUnit invariant/axis directions or the True predicate as sensitivity evidence
    - presenting the four computational fields as the remaining structural and proof laws, a complete SignedExactCoreReadingHom, whole PackageTotalHom descent, ambient reflection, or FiniteModelLift
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  reviewed_content_head: 1a8e9312b12e2f62d5484c5e046a4c1588456d09
  proof_obligation_delta: completed the generated-domain operation lift and reflection to a two-sided equivalence with operation datum, configuration-map, and Atom-map graphs; defined the reflected operationMap by applying the actual normalized high operationMap to the generated high image and reflecting its result through the complete architecture-object endpoint equalities; completed the generated-domain invariant-index and signature-axis maps to two-sided equivalences; completed the dependent coordinate images at every axis to two-sided equivalences with landing alignment; and defined the reflected invariantMap, axisMap, and coordinateEquiv by conjugating the corresponding actual normalized high fields through those internally generated images. The public theorems cover every low source input and every high source input in the inverse direction where appropriate, and provide both coordinate round trips. The selective-two noninvertible fixture fires a genuinely nonidentity collapse operation and its Atom action, both directions of the rigid singleton invariant and axis maps, and coordinate value 3 with its inverse image and round trip. Separate Boolean instances fire the exact proof-used ordinary and dependent conjugation primitives, without claiming sensitivity of the selected PUnit or True components. The existing complete object transport gives the future configuration_eq field after projection, but its explicit field theorem and the remaining structural, detector, naturality, invariant, and signature laws are not assembled here. Complete SignedExactCoreReadingHom, PackageTotalHom descent, ambient factor reflection, FiniteModelLift, K0, and theorem completion remain unclaimed.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedOperationMapDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedInvariantSignatureMapDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedUpperComputationalWitnesses.lean
  evidence:
    - finiteGeneratedDomainOperationLift
    - finiteGeneratedDomainOperationReflect
    - finiteGeneratedDomainOperationEquiv
    - finiteGeneratedDomainOperation_reflect_lift
    - finiteGeneratedDomainOperation_lift_reflect
    - finiteGeneratedDomainOperation_configurationMap_graph
    - finiteGeneratedDomainOperation_inverse_configurationMap_graph
    - finiteGeneratedReflectedOperationMap
    - finiteGeneratedReflectedOperationMap_forward_image
    - finiteGeneratedReflectedOperationMap_inverse_image
    - finiteGeneratedReflectedOperationMap_atom_graph
    - generatedIndexMapConjugation
    - generatedIndexMapConjugation_actual_injective
    - generatedDependentEquivConjugation
    - generatedDependentEquivConjugation_apply_high_image
    - generatedDependentEquivConjugation_symm_apply_high_image
    - finiteGeneratedInvariantIndexEquiv
    - finiteGeneratedInvariantIndexInverseEquiv
    - finiteGeneratedSignatureAxisEquiv
    - finiteGeneratedSignatureAxisInverseEquiv
    - finiteGeneratedSignatureCoordinateEquiv
    - finiteGeneratedSignatureCoordinateInverseEquiv
    - finiteGeneratedReflectedInvariantMap
    - finiteGeneratedReflectedInvariantMap_high_image
    - finiteGeneratedReflectedInvariantMap_inverse_source_high_image
    - finiteGeneratedReflectedAxisMap
    - finiteGeneratedReflectedAxisMap_high_image
    - finiteGeneratedReflectedAxisMap_inverse_source_high_image
    - finiteGeneratedReflectedCoordinateLandingEquiv
    - finiteGeneratedReflectedCoordinateEquiv
    - finiteGeneratedReflectedCoordinateEquiv_apply_high_image
    - finiteGeneratedReflectedCoordinateEquiv_symm_apply_high_image
    - finiteGeneratedReflectedCoordinateEquiv_symm_apply_apply
    - finiteGeneratedReflectedCoordinateEquiv_apply_symm_apply
    - finiteSelectiveTwoUpperComputationalBase_not_isIso
    - finiteSelectiveTwoOuterCollapseOperation_atom_graph
    - finiteSelectiveTwoOuterCollapseOperation_nonidentity
    - finiteSelectiveTwoActualReflectedCollapseOperation_forward_image
    - finiteSelectiveTwoActualReflectedCollapseOperation_inverse_image
    - finiteSelectiveTwoActualReflectedCollapseOperation_atom_graph
    - finiteSelectiveTwoActualReflectedInvariantIndex_high_image
    - finiteSelectiveTwoActualReflectedInvariantIndex_inverse_source_high_image
    - finiteSelectiveTwoActualReflectedSignatureAxis_high_image
    - finiteSelectiveTwoActualReflectedSignatureAxis_inverse_source_high_image
    - finiteSelectiveTwoUpperSignatureCoordinateThree_ne_zero
    - finiteSelectiveTwoActualReflectedSignatureCoordinateThree_forward_high_image
    - finiteSelectiveTwoActualReflectedSignatureCoordinateThree_inverse_high_image
    - finiteSelectiveTwoActualReflectedSignatureCoordinateThree_roundtrip
    - primitiveGeneratedIndexMapConjugation_middle_sensitive
    - primitiveGeneratedDependentEquivConjugation_middle_sensitive
  claim_mapping:
    fixed_goal_clauses:
      - target theorem B and the material ledger retain FiniteModelLift as discharge-required before K0
      - premise policy forbids caller-supplied transported packages, hom graphs, low preimages, image membership, and conclusion-equivalent certificates
    runtime_route_constraints:
      - Issue 4034 requires the four reflected computational values to be read from the actual normalized high factor
      - generated endpoint equalities may align dependent types but may not replace an actual high field with a known low or canonical upper
      - operation reflection must use complete architecture-object endpoint images, not configuration-only descent
      - rigid selected indices require all-input theorems and honest scope language rather than a false nontriviality claim
      - this checkpoint may not be promoted to a complete upper or total hom before every remaining law is directly reflected and assembled
    source_facts:
      - finiteGeneratedDomainOperationEquiv is a genuine equivalence between the low and high generated-domain operation types, with both round trips and arbitrary-high inverse coverage
      - finiteGeneratedReflectedOperationMap applies the actual normalized high upper operationMap before reflecting the resulting operation
      - finiteGeneratedReflectedInvariantMap and finiteGeneratedReflectedAxisMap use generatedIndexMapConjugation with the actual normalized high invariantMap and axisMap as the middle functions
      - finiteGeneratedReflectedCoordinateEquiv uses generatedDependentEquivConjugation with the actual normalized high coordinateEquiv as the middle equivalence and an internally generated dependent target landing
      - the witness instantiates the public reflected producers and their all-input image theorems rather than reconstructing known low maps
    consequence:
      - the four remaining computational map fields for a future generated low SignedExactCoreReadingHom now have actual-high-derived producers
      - operation, invariant, axis, and dependent coordinate generated images now have the two-sided APIs needed to state and prove their remaining laws
      - the remaining structural and proof fields, whole upper assembly, total-hom descent, and ambient strong-lift reflection remain open
audits:
  premise_delta:
    discharged:
      - two-sided generated operation image with configuration and Atom graphs
      - actual-high-derived operationMap for every generated low operation and arbitrary-high inverse image
      - two-sided generated invariant-index and signature-axis images
      - actual-high-derived invariantMap and axisMap with forward and arbitrary-high inverse-source graphs
      - dependent coordinate image equivalences and actual-high-derived coordinateEquiv with both image directions and round trips
      - noninvertible fixture firing a nonidentity operation and nonzero coordinate value, plus exact-primitive Boolean sensitivity
    remaining:
      - direct reflection of extraction_eq, composition_eq, object_formation_eq, detectorCode_eq, operation_naturality, invariant_transport, axis_selected_iff, and coordinate_eq from the corresponding actual high fields
      - explicit configuration_eq field theorem and exact assembly of all 18 SignedExactCoreReadingHom fields; the underlying complete object transport theorem is already available
      - whole PackageTotalHom descent, composition and equality reflection, and high-driven ambient factorization and uniqueness
      - FiniteModelLift and generated nonexistence transfer
      - K0 and K2-K4 after the F0 ledger is resolved
  certificate_provenance:
    discharged:
      - each top-level reflected computational producer accepts only input, supplied high lift, base, and its mathematical operation, index, axis, or coordinate argument
      - operation, invariant, axis, and coordinate image equivalences, inverses, endpoint alignments, and round trips are internally generated
      - the operation inverse theorem quantifies every high source operation; the invariant and axis inverse-source theorems quantify every high source index or axis; the coordinate inverse theorem quantifies every low target coordinate, equivalently every canonical high target image through the target equivalence, and the two coordinate round trips cover both low coordinate carriers
      - the witness derives its operation, indices, axes, coordinates, and base noninvertibility from named finite constructions
    prohibited_and_absent:
      - finiteGeneratedLowFactorUpper, finiteGeneratedNormalizedHighFactor_eq_canonical, inverseCorePackageFactor as a returned low answer, globalCartesianLift, caller map/equivalence/image/round-trip certificates, Classical.choose of a low preimage, and empty elimination
  proof_use:
    used:
      - the actual normalized high operationMap in the transparent finiteGeneratedReflectedOperationMap body
      - the actual normalized high invariantMap and axisMap as the middle functions of the two transparent reflected map bodies
      - the actual normalized high coordinateEquiv as the middle equivalence of the transparent dependent reflected coordinate body
      - complete Cycle 19 object-image equalities only for dependent operation endpoints
      - all four actual-derived computational producers in the concrete noninvertible fixture
    not_yet_available:
      - direct actual-high proofs of the remaining eight structural and law fields
      - exact 18-field SignedExactCoreReadingHom and PackageTotalHom assembly
      - high-driven ambient low factor, factorization, and uniqueness
  structure_field_escape: none in the four target-facing reflected producers; the generic conjugation helpers explicitly accept source, actual-middle, target, and dependent-landing data, but each target-facing instantiation generates those inputs internally and fixes its middle data to the corresponding actual normalized high field; no target-facing producer accepts a free map, equivalence, image, inverse, round-trip, or law certificate
  route_integrity: pass for the four actual-high-derived computational upper fields only; remaining SignedExactCoreReadingHom laws and whole hom descent remain open
  target_fitting: none found in implementation; core theorems quantify all low and high generated inputs and the fixture only instantiates them
  vacuity: none found; the fixture uses a noninvertible base, a nonidentity collapse operation with moved Atom, and coordinate values 3 and 0; singleton invariant and axis directions are explicitly classified as rigid
  proof_irrelevance_scope: selected invariant and axis indices are PUnit and the invariant predicate is True, so nontriviality is not claimed there; the exact proof-used ordinary and dependent conjugation primitives are separately shown sensitive to Boolean middle maps
  goal_or_report_reinterpretation: none; FiniteModelLift and the fixed ambient reflection output remain open
  validation_refs:
    - official focused wrapper FiniteGeneratedOperationMapDescent.lean: pass, 17 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedInvariantSignatureMapDescent.lean: pass, 37 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedUpperComputationalWitnesses.lean: pass, 29 namespace declarations and standard axioms only
    - targeted module check FiniteGeneratedOperationMapDescent: pass; used only to materialize its olean for the dependent witness import
    - targeted module check FiniteGeneratedInvariantSignatureMapDescent: pass; used only to materialize its olean for the dependent witness import
    - no Research aggregate or full build
    - manifest and umbrella wiring, diff, placeholder, hidden/BiDi Unicode, privacy, and import-direction scans: pass locally
    - fixed GOAL blob and SHA256 lock: pass
    - PR 4059 reviewed content head 1a8e9312b12e2f62d5484c5e046a4c1588456d09: 7/7 CI green and MERGEABLE/CLEAN
    - report-only precision repair ede76f22afd15d28791d3310715b1a45c9b5aa48: all four direct-response reviews passed, 7/7 CI green, and MERGEABLE/CLEAN
  review_refs:
    independent_final_reviews:
      - Math A — two Minor report-precision findings; repaired report-only and direct-response closure passed
      - Math B — No major findings
      - Lean A — No major findings
      - Lean B — one Minor report-precision finding overlapping Math A; repaired report-only and direct-response closure passed
    direct_response: report-only range 1a8e9312b12e2f62d5484c5e046a4c1588456d09..ede76f22afd15d28791d3310715b1a45c9b5aa48 changed only the coordinate inverse quantification and generic-helper versus target-facing producer scope; Math A/B and Lean A/B all returned Pass
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4059#issuecomment-5376484172
  stop_condition: none; continue before K0
  blocking_findings: []
  next_obligation: reflect the remaining structural, detector, operation-naturality, invariant, and signature laws directly from their corresponding actual normalized high fields; expose configuration_eq from the existing complete object transport; assemble the exact 18-field SignedExactCoreReadingHom; then descend the whole PackageTotalHom before retrying ambient strong-lift reflection
```

### Cycle 22 — complete actual-high-derived equation-system transport

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 22
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 8673b3a161482c18605313b144f56870543685b2
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 21 merge synchronization / Cycle 22 selection comment 5375675447
  proof_dag_predecessors:
    - Cycle 19 complete object-image value descent and canonical context primitives, PR 4055
    - Cycle 20 actual generated context-equivalence reflection, PR 4056
    - Cycle 21 actual generated equation-index and observable-equivalence reflection, PR 4057 merge 8673b3a1
  proof_obligation: reflect the actual normalized high equation transport's role, observable-naturality, violation-coordinate, and equation-residual laws through the generated images; assemble the exact seven-field low generated EquationSystemExactTransport without caller laws or returning a pre-existing low whole-factor transport; and fire all seven fields on the noninvertible finite fixture
  selection_reason: Cycles 20 and 21 supplied the actual-high-derived contextEquivalence, equationEquiv, and observableEquiv computational fields, while the four remaining laws and the complete record assembly were still open
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationRoleDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedObservableNaturalityDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationGeneratorDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationTransportDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationTransportWitnesses.lean
    - finiteGeneratedReflectedEquationSystemExactTransport
  risks:
    - copying a known low EquationSystemExactTransport or using EquationSystemExactTransport.refl while the supplied high laws occur only in sibling propositions
    - rewriting the actual normalized high factor to the canonical factor before consuming its four law fields
    - accepting role, naturality, generator, context, index, object, or endpoint graph certificates from the caller
    - using context thinness to invent a restriction arrow before the actual high map is reflected
    - proving residual preservation from configuration-only descent instead of the complete Cycle 19 architecture-object image equality
    - firing only constant selected values and presenting that as sensitivity of proof-valued law fields
    - presenting the complete equation transport as a complete SignedExactCoreReadingHom, whole PackageTotalHom descent, ambient reflection, or FiniteModelLift
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  reviewed_content_head: 4ad0c648b0394dff972860822da99d9d214729d6
  proof_obligation_delta: proved selected-target and canonical generated-domain role, observable-restriction, violation-coordinate, and residual image graphs; projected and directly consumed the corresponding four laws of the actual normalized high equation transport; reflected each law through the internally generated context, index, observable, Atom, and complete architecture-object images; and assembled the exact low generated EquationSystemExactTransport with all seven fields. The canonical endpoint image proofs legitimately use the predecessor inverse-package forward equation transports only to align low and high source/target generator data; the assembled outer-to-inner transport is not copied from either endpoint transport. The top-level producer accepts only the finite generated input, supplied high strong-cartesian lift, and ambient base arrow. Its context, index, observable, role, naturality, violation, and residual fields are named prior or current generated outputs rather than caller laws. The selective-two noninvertible fixture instantiates all seven public projections on distinct contexts and a genuine restriction, a nonzero observable value and violation coordinate, and both cyclic and acyclic residual values. Complete SignedExactCoreReadingHom and PackageTotalHom descent, ambient factor reflection, FiniteModelLift, K0, and theorem completion remain unclaimed.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationRoleDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedObservableNaturalityDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationGeneratorDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationTransportDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationTransportWitnesses.lean
  evidence:
    - finiteModelTargetEquationRole_lift
    - finiteGeneratedDomainEquationRole_image
    - finiteGeneratedActualHighEquationRole_eq
    - finiteGeneratedReflectedEquationRole_eq
    - finiteModelTargetEquationObservableEquiv_restrict
    - finiteGeneratedEquationObservableEquiv_restrict
    - finiteGeneratedReflectedEquationObservableEquiv_naturality
    - finiteModelTargetEquationViolationCoordinate_image
    - finiteModelTargetEquationResidual_image
    - finiteGeneratedEquationViolationCoordinate_image
    - finiteGeneratedEquationResidual_image
    - finiteGeneratedReflectedEquationObservableTargetCast_violation
    - finiteGeneratedReflectedEquationObservableTargetCast_residual
    - finiteGeneratedReflectedViolationCoordinate_eq
    - finiteGeneratedReflectedEquationResidual_eq
    - FiniteGeneratedReflectedEquationSystemExactTransportOutput
    - finiteGeneratedReflectedEquationSystemExactTransport
    - finiteGeneratedReflectedEquationSystemExactTransport_contextEquivalence
    - finiteGeneratedReflectedEquationSystemExactTransport_equationEquiv
    - finiteGeneratedReflectedEquationSystemExactTransport_observableEquiv
    - finiteGeneratedReflectedEquationSystemExactTransport_role_eq
    - finiteGeneratedReflectedEquationSystemExactTransport_observable_naturality
    - finiteGeneratedReflectedEquationSystemExactTransport_violationCoordinate_eq
    - finiteGeneratedReflectedEquationSystemExactTransport_equationResidual_eq
    - finiteSelectiveTwoReflectedEquationSystemExactTransport
    - finiteSelectiveTwoEquationTransport_base_not_isIso
    - finiteSelectiveTwoEquationTransport_contextEquivalence
    - finiteSelectiveTwoEquationTransport_equationEquiv
    - finiteSelectiveTwoEquationTransport_observableEquiv
    - finiteSelectiveTwoEquationTransport_role_eq
    - finiteSelectiveTwoEquationObservableThreeAtV
    - finiteSelectiveTwoEquationObservableThreeAtV_ne_zero
    - finiteSelectiveTwoEquationTransport_observable_naturality
    - finiteSelectiveTwoEquationTransport_violationCoordinate_eq
    - finiteSelectiveTwoEquationTransport_cyclic_equationResidual_eq
    - finiteSelectiveTwoEquationTransport_acyclic_equationResidual_eq
    - finiteSelectiveTwoTargetViolationCoordinate_ne_zero
    - finiteSelectiveTwoCyclic_noCycleResidual_eq_one
    - finiteSelectiveTwoAcyclic_noCycleResidual_eq_zero
    - finiteSelectiveTwo_noCycleResidual_object_sensitive
  claim_mapping:
    fixed_goal_clauses:
      - target theorem B and the material ledger retain FiniteModelLift as discharge-required before K0
      - premise policy forbids caller-supplied transported packages, hom graphs, low preimages, image membership, and conclusion-equivalent certificates
    runtime_route_constraints:
      - Issue 4034 requires all four remaining law fields to be read from the actual normalized high equation transport
      - prior generated images may align dependent endpoints but may not replace an actual high law with a known low or canonical transport
      - residual reflection must consume the complete generated architecture-object image equality
      - the seven-field result is an equation-system checkpoint and may not be promoted to a whole upper or total hom
    source_facts:
      - finiteGeneratedActualHighEquationRole_eq is the actual normalized high role_eq projection at every generated high index
      - finiteGeneratedReflectedEquationObservableEquiv_naturality applies the actual high observable_naturality to every reflected context arrow and observable value
      - finiteGeneratedReflectedViolationCoordinate_eq applies the actual high violationCoordinate_eq after internally generated context, index, Atom, and observable alignment
      - finiteGeneratedReflectedEquationResidual_eq applies the actual high equationResidual_eq and aligns its object endpoint through finiteGeneratedReflectedArchitectureObject_high_image
      - finiteGeneratedReflectedEquationSystemExactTransport fills all seven EquationSystemExactTransport fields from the Cycle 20, Cycle 21, and Cycle 22 reflected producers and laws
      - the witness instantiates the assembled public projections rather than separately restating the component lemmas
    consequence:
      - the complete generated low EquationSystemExactTransport is now constructed from the actual supplied-high transport on canonical generated images
      - the equationTransport field needed by a future reflected SignedExactCoreReadingHom is discharged
      - remaining upper computational fields and laws, whole total-hom descent, and ambient strong-lift reflection remain open
audits:
  premise_delta:
    discharged:
      - actual high role equality reflected for every generated low equation index
      - actual high observable naturality reflected for every generated low context arrow and observable value
      - actual high violation-coordinate law reflected for every context, index, and Atom
      - actual high residual law reflected for every context, complete low architecture object, index, and Atom
      - exact seven-field generated low EquationSystemExactTransport assembly
      - concrete noninvertible fixture firing every assembled field, including cyclic and acyclic residual controls
    remaining:
      - remaining operation, invariant, signature, composition, and proof fields needed for a complete reflected SignedExactCoreReadingHom
      - whole PackageTotalHom descent, composition/equality reflection, and high-driven ambient factorization/uniqueness
      - FiniteModelLift and generated nonexistence transfer
      - K0 and K2-K4 after the F0 ledger is resolved
  certificate_provenance:
    discharged:
      - the top-level transport producer accepts only input, supplied high lift, and base; all seven fields and dependent endpoint alignments are internally generated
      - every reflected law quantifies its mathematical index, context, arrow, value, Atom, or architecture object rather than accepting a proof packet
      - the witness derives its generated index, observable value, restriction, objects, and base noninvertibility from prior named fixtures
    prohibited_and_absent:
      - returning a known low outer-to-inner or reflected final equation transport, finiteGeneratedLowFactor, inverseCorePackageFactor, EquationSystemExactTransport.refl, finiteGeneratedNormalizedHighFactor_eq_canonical, globalCartesianLift, caller law/image/graph certificates, Classical.choose of a low preimage, and empty elimination
  proof_use:
    used:
      - the actual normalized high role_eq in finiteGeneratedActualHighEquationRole_eq and the final reflected role proof
      - the actual normalized high observable_naturality before restriction endpoint descent
      - the actual normalized high violationCoordinate_eq before the target observable cast and canonical image reflection
      - the actual normalized high equationResidual_eq together with the complete reflected architecture-object high-image equality
      - predecessor low/high generated endpoint equation transports only in the canonical role, restriction, violation, and residual image graphs
      - all seven named component producers in the final EquationSystemExactTransport structure literal
    not_yet_available:
      - complete actual-high-derived SignedExactCoreReadingHom and PackageTotalHom
      - high-driven ambient low factor, factorization, and uniqueness
  structure_field_escape: none; standalone definitions accept no free law, transport, image, or comparison fields
  route_integrity: pass for the complete generated-image EquationSystemExactTransport; whole upper and total hom descent remain open
  target_fitting: none found in implementation; core laws quantify all generated inputs and the fixture only instantiates them
  vacuity: none found; the fixture uses a noninvertible base, distinct contexts with a restriction, a nonzero observable value and violation coordinate, and residual values that distinguish cyclic from acyclic objects
  proof_irrelevance_scope: the four new law fields are propositions, so sensitivity of proof terms is neither claimed nor used; material use is audited from the direct actual-high field dependencies and all-value theorem statements
  goal_or_report_reinterpretation: none; FiniteModelLift and the fixed ambient reflection output remain open
  validation_refs:
    - official focused wrapper FiniteGeneratedEquationRoleDescent.lean: pass, 4 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedObservableNaturalityDescent.lean: pass, 3 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedEquationGeneratorDescent.lean: pass, 8 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedEquationTransportDescent.lean: pass, 9 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedEquationTransportWitnesses.lean: pass, 16 namespace declarations and standard axioms only
    - manifest and umbrella wiring, diff, placeholder, hidden/BiDi Unicode, privacy, and import-direction scans: pass locally
    - fixed GOAL blob and SHA256 lock: pass
    - PR 4058 reviewed content head 4ad0c648b0394dff972860822da99d9d214729d6: 7/7 CI green and MERGEABLE/CLEAN
    - report-only provenance/evidence repair 674041461dec8d19495722ac3be7ae6d131d8d0c: all four direct-response reviews passed with no remaining finding
    - no Research aggregate or full build
  review_refs:
    independent_final_reviews:
      - Math A — two Minor report-precision findings; repaired report-only and direct-response closure passed
      - Math B — No major findings
      - Lean A — No major findings
      - Lean B — No major findings
    direct_response: report-only range 4ad0c648b0394dff972860822da99d9d214729d6..674041461dec8d19495722ac3be7ae6d131d8d0c changed only provenance wording and two witness evidence rows; Math A/B and Lean A/B all returned Pass
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4058#issuecomment-5376094093
  stop_condition: none; continue before K0
  blocking_findings: []
  next_obligation: reflect and assemble the remaining actual-high operation, invariant, signature, composition, and proof fields needed for a complete SignedExactCoreReadingHom; then descend the whole total hom before retrying ambient strong-lift reflection
```

### Cycle 21 — actual generated equation-index and observable-equivalence reflection

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 21
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: ec48fc0adea8bf4dc877bd98dad1f58ca92a2bdc
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 20 merge synchronization / Cycle 21 selection comment 5375309572
  proof_dag_predecessors:
    - Cycle 17 actual supplied-high generated prefix factor and canonical normalization, PR 4053
    - Cycle 19 complete object-image value descent and canonical context primitives, PR 4055
    - Cycle 20 actual generated context-equivalence reflection, PR 4056 merge ec48fc0a
  proof_obligation: complete the generated-domain equation-index image maps to two-sided equivalences; reflect the actual normalized high equationEquiv and context-indexed observableEquiv through internally generated images; prove all-value forward/inverse image graphs; and fire both fields plus their proof-used conjugation primitives nonvacuously
  selection_reason: Cycle 20 reflected only contextEquivalence, while the existing generated-domain index map was one-way and the equation-system observable rings required a separate Int-to-ULift-Int construction rather than the ArchitectureContext Observable carrier graph
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationIndexDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedObservableEquivalenceDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationEquivalenceWitnesses.lean
    - finiteGeneratedReflectedEquationIndexEquiv
    - finiteGeneratedReflectedEquationObservableEquiv
  risks:
    - treating the existing one-way generatedDomainEquationIndexLift as an equivalence without an inverse and both round trips
    - confusing the ArchitectureContext Observable carrier with the equation-system observable coefficient ring
    - returning a known low equation transport while the actual high fields occur only in sibling equalities
    - allowing an index map, ring equivalence, context equality, inverse, or graph certificate from the caller
    - using the selected PUnit index or rigid Int coefficient ring alone as evidence that conjugation is sensitive to its actual middle leg
    - presenting equationEquiv and observableEquiv as the complete EquationSystemExactTransport, whole hom descent, or FiniteModelLift
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  reviewed_content_head: cd8a450e163028db1070a0dd0925ebf54a522a58
  proof_obligation_delta: introduced transparent equation-index and equation-observable conjugation primitives and proved that each is injective in its actual middle equivalence for fixed generated images; completed the selected and generated-domain equation-index maps to named equivalences with inverse accessors and two-sided round trips; projected the actual normalized high equationEquiv and reflected it through the outer and inner generated-domain images; constructed the equation-system observable image equivalence by composing the low inverse-package upper, the selected Int-to-ULift-Int target equivalence, and the inverse high upper; projected the actual high observableEquiv at every canonical-image context; aligned only its dependent target context with the Cycle 20 landing theorem; and reflected it through the two generated observable images. Both reflected producers use the proof-used conjugation primitives computationally and accept no equivalence or graph from the caller. All-index and all-context/all-value forward and inverse image graphs are proved. The existing selective-two noninvertible fixture fires both actual reflected fields and both round trips at a generated index and observable value 3. Separate Boolean and product-ring swaps fire the same proof-used primitives, without claiming nontriviality of the selected PUnit index. Role preservation, observable naturality, violation/residual generators, the complete EquationSystemExactTransport, remaining upper fields, whole factor descent, ambient reflection, FiniteModelLift, K0, and theorem completion remain unclaimed.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationIndexDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedObservableEquivalenceDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedEquationEquivalenceWitnesses.lean
  evidence:
    - generatedEquationIndexEquivConjugation
    - generatedEquationIndexEquivConjugation_actual_injective
    - finiteModelTargetEquationIndexEquiv
    - finiteGeneratedDomainEquationIndexEquiv
    - finiteGeneratedDomainEquationIndexReflect
    - finiteGeneratedDomainEquationIndex_reflect_lift
    - finiteGeneratedDomainEquationIndex_lift_reflect
    - finiteGeneratedActualHighEquationIndexEquiv
    - finiteGeneratedReflectedEquationIndexEquiv
    - finiteGeneratedReflectedEquationIndex_forward_image
    - finiteGeneratedReflectedEquationIndex_inverse_image
    - generatedEquationObservableRingEquivConjugation
    - generatedEquationObservableRingEquivConjugation_actual_injective
    - finiteModelTargetEquationObservableEquiv
    - finiteGeneratedEquationObservableEquiv
    - finiteGeneratedEquationObservableEquiv_forward_image
    - finiteGeneratedEquationObservableEquiv_inverse_image
    - finiteGeneratedActualHighEquationObservableEquiv
    - finiteGeneratedReflectedEquationObservableTargetCast
    - finiteGeneratedReflectedEquationObservableEquiv
    - finiteGeneratedReflectedEquationObservableEquiv_apply_high_image
    - finiteGeneratedReflectedEquationObservableEquiv_symm_apply_high_image
    - finiteSelectiveTwoReflectedEquationIndex_forward_high_image
    - finiteSelectiveTwoReflectedEquationIndex_inverse_high_image
    - finiteSelectiveTwoReflectedEquationIndex_roundtrip
    - finiteSelectiveTwoReflectedEquationObservableThree_forward_high_image
    - finiteSelectiveTwoReflectedEquationObservableThree_inverse_high_image
    - finiteSelectiveTwoReflectedEquationObservableThree_roundtrip
    - finiteSelectiveTwoEquationEquivalenceWitness_base_not_isIso
    - primitiveEquationIndexConjugation_middle_sensitive
    - primitiveEquationObservableConjugation_middle_sensitive
  claim_mapping:
    fixed_goal_clauses:
      - target theorem B and the material ledger retain FiniteModelLift as discharge-required before K0
      - premise policy forbids caller-supplied transported packages, hom graphs, low preimages, image membership, and conclusion-equivalent certificates
    runtime_route_constraints:
      - Issue 4034 requires the equation-index and equation-observable equivalences to be read from the actual normalized high transport rather than copied from the known low factor
      - the Cycle 20 reflected context landing may align dependent observable targets but may not replace the actual high observable map
      - selected PUnit and Int endpoints require a separate finite sensitivity check of the exact proof-used conjugation operations
    source_facts:
      - finiteGeneratedDomainEquationIndexEquiv extends the existing generatedDomainEquationIndexLift and supplies a named inverse plus both round trips
      - finiteGeneratedActualHighEquationIndexEquiv is definitionally the actual normalized factor's equationEquiv projection
      - finiteGeneratedReflectedEquationIndexEquiv invokes generatedEquationIndexEquivConjugation with internally generated outer image, actual high field, and inner image
      - finiteGeneratedEquationObservableEquiv maps through the low target observable equivalence, the selected Int-to-ULift-Int equivalence, and the inverse high target observable equivalence
      - finiteGeneratedActualHighEquationObservableEquiv is definitionally the actual normalized factor's observableEquiv projection at the generated high context
      - finiteGeneratedReflectedEquationObservableTargetCast is generated solely from the Cycle 20 canonical-image-equals-actual-image theorem
      - finiteGeneratedReflectedEquationObservableEquiv invokes generatedEquationObservableRingEquivConjugation with internally generated source, actual, and target legs
      - both conjugation operations are injective in the actual middle equivalence and are fired on concrete nonidentity finite swaps
      - the finite witness internally reuses the supplied high lift, noninvertible prefix, generated index, context, and observable value
    consequence:
      - the equationEquiv and observableEquiv computational fields now have actual-high-derived low outputs with complete forward/inverse image graphs
      - only those two fields, in addition to Cycle 20 contextEquivalence, are discharged toward the eventual complete EquationSystemExactTransport
      - role, naturality, generator laws, whole upper/total descent, and ambient strong-lift reflection remain open
audits:
  premise_delta:
    discharged:
      - two-sided selected and generated-domain equation-index equivalences
      - named generated-domain index reflection and both round trips
      - actual high equationEquiv projection and reflected low equivalence for every index
      - canonical generated-domain equation-observable RingEquiv for every low context and every ring value
      - actual high observableEquiv projection, dependent target cast, and reflected low RingEquiv
      - forward and inverse actual-high image graphs for all indices, contexts, and observable values
      - actual-middle injectivity for both proof-used conjugation primitives
      - concrete noninvertible fixture firing plus Boolean and product-ring sensitivity
    remaining:
      - actual high role_eq reflection
      - observable restriction naturality on every reflected context arrow
      - violationCoordinate and equationResidual generator graphs
      - assembly of the complete actual-high-derived EquationSystemExactTransport
      - remaining operation, invariant, signature, and proof fields needed for SignedExactCoreReadingHom
      - whole PackageTotalHom descent, composition/equality reflection, and high-driven ambient factorization/uniqueness
      - FiniteModelLift and generated nonexistence transfer
      - K0 and K2-K4 after the F0 ledger is resolved
  certificate_provenance:
    discharged:
      - both top-level reflected producers accept only input, supplied high lift, base, and their quantified index/context/value; all equivalence and cast legs are internally generated
      - the target observable cast is generated from the prior context landing theorem and carries no observable value or inverse certificate
      - the finite witness generates its source index and observable value through the canonical low upper and supplies no producer field
    qualified_primitive:
      - the generic index and ring conjugation operations are transparent low-level functions used by the actual producers; their separate finite instantiations test the actual-leg dependency but are not caller inputs to the generated producers
    prohibited_and_absent:
      - known low equation transport, finiteGeneratedLowFactor, inverseCorePackageFactor, EquationSystemExactTransport.refl, canonical whole-factor rewriting, globalCartesianLift, caller image/equivalence/graph certificates, and Classical.choose of a low preimage
  proof_use:
    used:
      - the actual normalized high equationEquiv in the computational body of finiteGeneratedReflectedEquationIndexEquiv
      - the actual normalized high observableEquiv in the computational body of finiteGeneratedReflectedEquationObservableEquiv
      - the Cycle 20 actual context landing only to construct the dependent RingEquiv.cast target alignment
      - both proof-used conjugation primitives and their generated source and target image legs
    not_yet_available:
      - actual high role_eq, observable_naturality, violationCoordinate_eq, and equationResidual_eq reflection
      - complete actual-high-derived EquationSystemExactTransport, SignedExactCoreReadingHom, and PackageTotalHom
  structure_field_escape: none; standalone definitions accept no free proof or comparison fields
  route_integrity: pass for equationEquiv and observableEquiv on the complete canonical generated images; complete equation transport and whole factor remain open
  target_fitting: none found in implementation; core theorems quantify every generated index, context, and observable value, while the concrete fixture only fires them
  vacuity: none found; the fixture uses a genuinely noninvertible prefix and both directions of each actual field, and the exact proof-used conjugation primitives distinguish identity from finite swaps
  one_way_as_equivalence: none; the prior one-way equation-index lift is now the forward map of an explicit Equiv with named inverse and both round trips
  goal_or_report_reinterpretation: none; FiniteModelLift and the fixed ambient reflection output remain open
  validation_refs:
    - official focused wrapper FiniteGeneratedEquationIndexDescent.lean: pass, 19 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedObservableEquivalenceDescent.lean: pass, 15 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedEquationEquivalenceWitnesses.lean: pass, 13 namespace declarations and standard axioms only
    - manifest and umbrella wiring, diff, placeholder, hidden/BiDi Unicode, privacy, and import-direction scans: pass locally
    - fixed GOAL blob and SHA256 lock: pass
    - PR 4057 reviewed content head cd8a450e163028db1070a0dd0925ebf54a522a58: 7/7 CI green and MERGEABLE/CLEAN
    - no Research aggregate or full build
  review_refs:
    independent_final_reviews:
      - Math A — No major findings
      - Math B — No major findings
      - Lean A — No major findings
      - Lean B — No major findings
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4057#issuecomment-5375633359
  stop_condition: none; continue before K0
  blocking_findings: []
  next_obligation: reflect actual role equality, observable restriction naturality, and violation/residual generator laws through the same generated images; then assemble the complete actual-high-derived EquationSystemExactTransport before descending the remaining upper and total hom fields
```

### Cycle 20 — actual generated context-equivalence reflection

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 20
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: faa1129e1eecd5377b87394680a8da66a253b15f
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 19 merge synchronization / Cycle 20 selection comment 5374189023
  proof_dag_predecessors:
    - Cycle 17 actual supplied-high generated prefix factor and canonical normalization, PR 4053
    - Cycle 18 actual-high base, Atom, object-configuration, and configuration-map descent, PR 4054
    - Cycle 19 complete object-image value descent and canonical context object/map primitives, PR 4055 merge faa1129e
  proof_obligation: derive the actual normalized high factor's forward and inverse context images internally; reflect its functor, inverse, unit, and counit on every canonical generated-image object and map; and construct the fixed FiniteGeneratedReflectedContextEquivalenceOutput
  selection_reason: Cycle 19 fixed the exact output type and supplied all-value context and raw-morphism image primitives, but deliberately stopped before consuming the actual equationTransport.contextEquivalence
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianTarget.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedContextImageFunctor.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedReflectedContextEquivalence.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedReflectedContextEquivalenceWitnesses.lean
    - finiteGeneratedContextImageFunctor
    - finiteGeneratedActualHighContextEquivalence
    - finiteGeneratedReflectedContextEquivalence
  risks:
    - returning a known low context equivalence while the actual high equivalence appears only in a sibling equality proof
    - accepting carrier shapes, object preimages, functors, an equivalence, unit, counit, or comparison graphs from the caller
    - using thin-category proof irrelevance to invent a morphism before reflecting the actual high map
    - claiming an equivalence with the full high context category or arbitrary Type-u descent
    - presenting the contextEquivalence projection as a complete EquationSystemExactTransport, whole hom descent, or FiniteModelLift
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  reviewed_content_head: 3f3396edec61232ddbc5398628ded9ea13377087
  proof_obligation_delta: extended the canonical inverse-package upper API across its internal equation casts with complete context-functor and context-inverse object graphs; constructed generated-domain context image functors and proved them Full and Faithful; projected the actual normalized supplied-high equation context equivalence; internally derived all forward and inverse carrier shapes; reflected every actual forward and inverse object and map; reflected both hom and inverse components of the actual unit and counit; and assembled the exact low FiniteGeneratedReflectedContextEquivalenceOutput. The computational object, map, unit, and counit definitions read the corresponding actual high projections, while the canonical whole-factor equality is used only in the carrier-shape proofs. A concrete finite fixture supplies distinct four-carrier contexts, a categorical restriction generated from a raw restriction whose support, axis, and observable maps all fire, and public forward/inverse object, map, unit, and counit image instances. No equivalence with the full high context category is claimed. The equation-index and observable-ring equivalences, observable naturality, violation/residual graphs, remaining upper fields, whole factor descent, ambient reflection, FiniteModelLift, K0, and theorem completion remain unclaimed.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianTarget.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedContextImageFunctor.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedReflectedContextEquivalence.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedReflectedContextEquivalenceWitnesses.lean
  evidence:
    - inverseCorePackageForwardUpper_contextFunctor_obj_eq
    - inverseCorePackageForwardUpper_contextInverse_obj_eq
    - finiteGeneratedHighDomain_object_lift
    - finiteGeneratedContextImageFunctor
    - finiteGeneratedContextImageFunctor_full
    - finiteGeneratedContextImageFunctor_faithful
    - finiteGeneratedContextImageFunctor_carrierShape
    - finiteGeneratedContextImageFunctor_obj_ctx_eq_lift
    - finiteGeneratedActualHighContextEquivalence
    - finiteGeneratedReflectedForwardActualContext
    - finiteGeneratedReflectedForwardCarrierShape
    - finiteGeneratedReflectedForwardObject
    - finiteGeneratedReflectedInverseActualContext
    - finiteGeneratedReflectedInverseCarrierShape
    - finiteGeneratedReflectedInverseObject
    - finiteGeneratedReflectedForwardObject_image_eq
    - finiteGeneratedReflectedInverseObject_image_eq
    - finiteGeneratedReflectedForwardHighMap
    - finiteGeneratedReflectedForwardMap
    - finiteGeneratedReflectedInverseHighMap
    - finiteGeneratedReflectedInverseMap
    - finiteGeneratedReflectedUnitHighHom
    - finiteGeneratedReflectedUnitHighInv
    - finiteGeneratedReflectedCounitHighHom
    - finiteGeneratedReflectedCounitHighInv
    - finiteGeneratedReflectedContextEquivalence
    - finiteGeneratedReflectedForwardMap_image
    - finiteGeneratedReflectedInverseMap_image
    - finiteGeneratedReflectedUnitIsoApp_hom_image
    - finiteGeneratedReflectedUnitIsoApp_inv_image
    - finiteGeneratedReflectedCounitIsoApp_hom_image
    - finiteGeneratedReflectedCounitIsoApp_inv_image
    - finiteSelectiveTwoContextEquivalenceW_ne_V
    - finiteSelectiveTwoContextEquivalenceRawRestriction_support_graph
    - finiteSelectiveTwoContextEquivalenceRawRestriction_axis_graph
    - finiteSelectiveTwoContextEquivalenceRawRestriction_observable_graph
    - finiteSelectiveTwoContextEquivalence_forward_object_landing
    - finiteSelectiveTwoContextEquivalence_inverse_object_landing
    - finiteSelectiveTwoContextEquivalence_forward_map_image
    - finiteSelectiveTwoContextEquivalence_inverse_map_image
    - finiteSelectiveTwoContextEquivalence_unit_hom_image
    - finiteSelectiveTwoContextEquivalence_unit_inv_image
    - finiteSelectiveTwoContextEquivalence_counit_hom_image
    - finiteSelectiveTwoContextEquivalence_counit_inv_image
  claim_mapping:
    fixed_goal_clauses:
      - target theorem B and the material ledger retain FiniteModelLift as discharge-required before K0
      - premise policy forbids caller-supplied transported packages, hom graphs, low preimages, image membership, and conclusion-equivalent certificates
    runtime_route_constraints:
      - Issue 4034 requires actual high functor, inverse, unit, and counit consumption rather than a known low-equivalence alias
      - canonical whole-hom equality may derive carrier alignment but may not supply the reflected predicates, maps, or equivalence computationally
      - thinness may close equality and naturality only after the relevant actual high morphism has been reflected through Fullness
    source_facts:
      - finiteGeneratedActualHighContextEquivalence is definitionally the contextEquivalence projection of finiteGeneratedNormalizedHighFactor
      - forward and inverse reflected objects read the actual high context predicates and extension through finiteModelReflectArchitectureContextAt
      - forward and inverse reflected maps are preimages of the corresponding actual high maps under internally generated Full image functors
      - all four unit/counit hom and inverse components are preimages of actual high unit/counit routes
      - finiteGeneratedNormalizedHighFactor_eq_canonical occurs in carrier-shape theorem proofs and not in the computational definitions of reflected objects, maps, unit, or counit
      - both generated-domain image functors are Full and Faithful, but no essential-surjectivity or equivalence with all high contexts is claimed
      - the categorical witness arrow is generated from a raw restriction with explicit support, axis, and observable value graphs; thin categorical homs are not claimed to expose those raw maps directly
    consequence:
      - the actual normalized high context equivalence now has a generated low equivalence on the full canonical image, including forward/inverse objects and maps plus unit/counit
      - only the contextEquivalence field of the eventual EquationSystemExactTransport has been reflected
      - complete equation transport, whole upper/total descent, and ambient strong-lift reflection remain open
audits:
  premise_delta:
    discharged:
      - complete context action of the canonical inverse-package forward upper across internal source-equation casts
      - Full/Faithful generated-domain context image functors on both endpoints
      - internally generated forward and inverse carrier shapes for every low context
      - actual high forward and inverse object reflection with complete image landing equalities
      - actual high forward and inverse map reflection on every categorical arrow
      - actual high unit hom, unit inverse, counit hom, and counit inverse reflection
      - construction of the fixed FiniteGeneratedReflectedContextEquivalenceOutput
      - distinct nontrivial contexts, a generated categorical restriction, and all object/map/unit/counit image witnesses
    remaining:
      - equation-index equivalence and its generated-image graphs
      - observable-ring equivalence, restriction naturality, and violation/residual generator graphs
      - remaining operation, invariant, signature, and proof fields needed for SignedExactCoreReadingHom
      - whole PackageTotalHom descent, composition/equality reflection, and high-driven ambient factorization/uniqueness
      - FiniteModelLift and generated nonexistence transfer
      - K0 and K2-K4 after the F0 ledger is resolved
  certificate_provenance:
    discharged:
      - the top-level producer accepts only input, the supplied high lift, and base; no shape, image/preimage, functor, equivalence, unit/counit, or graph certificate is a caller input
      - forward and inverse shapes are named internal constructions from the actual high equivalence
      - map, unit, and counit preimages are chosen only by the internally proved Full instances after constructing their actual high arrows
      - the finite witness generates its input, high lift, base, contexts, restriction, and all output projections internally
    prohibited_and_absent:
      - arbitrary high-context descent, full-high essential-surjectivity, known low equivalence return, globalCartesianLift, caller image/preimage certificates, and Classical.choose of a low context
  proof_use:
    used:
      - the actual high equivalence's functor and inverse object projections in reflected object definitions
      - the actual high functor and inverse maps before Full preimage extraction
      - the actual high unit and counit hom/inverse components before Full preimage extraction
      - complete canonical context-action graphs and canonical whole-factor equality only for internal image/carrier alignment
    not_yet_available:
      - actual high equation-index and observable-ring transport, observable naturality, and violation/residual descent
      - whole actual-high-derived SignedExactCoreReadingHom and PackageTotalHom
  structure_field_escape: none in the generated producer; no generated output data is accepted from its caller
  route_integrity: pass for the actual contextEquivalence projection on canonical generated images; complete EquationSystemExactTransport and whole factor remain open
  target_fitting: none found in implementation; all low contexts and categorical arrows are quantified, while the concrete fixture only fires the generic producer
  vacuity: none found; the witness uses distinct contexts with nontrivial Support, Axis, Observable, and Extension carriers, a raw restriction with all three map graphs, and all eight forward/inverse object-map-unit-counit observations
  one_way_as_equivalence: none; the image functors are Full/Faithful and the reflected equivalence is only between the two low generated context categories
  goal_or_report_reinterpretation: none; only contextEquivalence is discharged and FiniteModelLift remains open
  validation_refs:
    - official focused wrapper CartesianTarget.lean: pass, 43 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedContextImageFunctor.lean: pass, 16 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedReflectedContextEquivalence.lean: pass, 38 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedReflectedContextEquivalenceWitnesses.lean: pass, 31 namespace declarations and standard axioms only
    - manifest and umbrella wiring, diff, placeholder, hidden/BiDi Unicode, privacy, and import-direction scans: pass locally
    - fixed GOAL blob and SHA256 lock: pass
    - PR 4056 reviewed content head 3f3396edec61232ddbc5398628ded9ea13377087: 7/7 CI green and MERGEABLE/CLEAN
    - report-only unchecked-state repair 09f37ac62d75: Lean A direct response confirmed the Minor closed with no new finding
    - no Research aggregate or full build
  review_refs:
    independent_final_reviews:
      - Math A — No major findings
      - Math B — No major findings
      - Lean A — No major findings after direct-response closure of the report-only unchecked-state Minor
      - Lean B — No major findings
    direct_response: report-gate repair head 09f37ac62d75 records pending review/comment/sync gates; Lean A confirmed the Minor closed with no new finding
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4056#issuecomment-5375272145
  stop_condition: none; continue before K0
  blocking_findings: []
  next_obligation: reflect the actual equation-index and observable-ring equivalences, observable naturality, and violation/residual generators without caller certificates; then assemble the remaining actual-high-derived EquationSystemExactTransport fields before whole upper and total factor descent
```

### Cycle 19 — generated-image object and context primitive retraction

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 19
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 12b89bd60b5de8f595b7009d541e6d55f9edee7d
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 18 merge synchronization / Cycle 19 selection comment 5373494897
  proof_dag_predecessors:
    - Cycle 13-14 canonical finite package, configuration-hom, and equation ULift data, PR 4049/4050
    - Cycle 17 actual supplied-high generated factor and normalization equality, PR 4053
    - Cycle 18 actual-high base, Atom, object-configuration, and configuration-map descent, PR 4054 merge 12b89bd6
  proof_obligation: descend the two opaque fields of the actual normalized high object image without copying the source values, and construct the all-context/all-raw-morphism canonical image primitives needed before reflecting the actual equation-context equivalence
  selection_reason: Cycle 18 stopped at configuration-only object descent, while arbitrary high Type-u data cannot be lowered; the next legal route is a shape-indexed canonical-image retraction whose generated object producer derives shape internally and reads actual high values
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedObjectImageDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedContextImageDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedObjectContextImageWitnesses.lean
    - finiteGeneratedReflectedArchitectureObject
    - finiteModelLiftArchitectureContext
    - finiteModelReflectArchitectureContextAt
    - finiteModelLiftContextMorphism
    - finiteModelReflectContextMorphismAt
    - FiniteGeneratedReflectedContextEquivalenceOutput
  risks:
    - returning source structureMaps or selectedQuantities while using the high graph only as a sibling proof
    - treating a caller-supplied context carrier shape as the generated context-equivalence producer
    - claiming arbitrary high-context lowering or an equivalence with the full high context category
    - replacing actual context-equivalence descent by a singleton probe or by thin-hom proof irrelevance
    - presenting primitive lift-reflect APIs as complete EquationSystemExactTransport or whole-factor descent
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  reviewed_content_head: f0e8ecc565574bd512d1ac924d78839d86cdc0d9
  proof_obligation_delta: constructed an all-value ULift shape retraction; proved that the actual normalized supplied-high objectMap on every lifted finite-model object is a canonical lifted image; derived both opaque carrier shapes internally; defined the reflected complete object by reading its actual high configuration, structureMaps, and selectedQuantities fields; and proved its full high-image equality. Separately constructed generic four-carrier ArchitectureContext lift and carrier-shape reflection, raw ContextMorphism lift/reflection for all three maps, two-sided canonical-endpoint round trips, IsRestriction preservation/reflection, and a Full/Faithful canonical context-category lift. A single internally generated noninvertible fixture fires the full object descent with Bool and Fin 2 values, all four nontrivial context carriers with positive and negative readings, a nonidentity restriction plus both raw-map round trips, and a mismatched empty-support high context proving that the public carrier-shape certificate is not automatic. The actual normalized high equation context equivalence is not yet descended; its exact low output type is fixed by FiniteGeneratedReflectedContextEquivalenceOutput. Complete EquationSystemExactTransport, whole hom descent, ambient reflection, FiniteModelLift, K0, and theorem completion remain unclaimed.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedObjectImageDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedContextImageDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedObjectContextImageWitnesses.lean
  evidence:
    - finiteGeneratedULiftValueDown
    - finiteGeneratedULiftValueDown_up
    - finiteGeneratedULiftValueUp_down
    - finiteGeneratedNormalizedHighFactor_objectMap_lift_graph
    - finiteGeneratedReflectedArchitectureObject
    - finiteGeneratedReflectedArchitectureObject_structureMaps_high_graph
    - finiteGeneratedReflectedArchitectureObject_selectedQuantities_high_graph
    - finiteGeneratedReflectedArchitectureObject_high_image
    - finiteModelLiftArchitectureContext
    - FiniteModelContextCarrierShape
    - finiteModelReflectArchitectureContextAt
    - finiteModelReflectArchitectureContextAt_lift
    - finiteModelLiftArchitectureContext_reflectAt
    - finiteModelLiftContextMorphism
    - finiteModelReflectContextMorphismAt
    - finiteModelReflectLiftedContextMorphism_lift
    - finiteModelLiftContextMorphism_reflectLifted
    - finiteModelLiftContextFunctor
    - finiteModelLiftContextFunctor_full
    - finiteModelLiftContextFunctor_faithful
    - FiniteGeneratedReflectedContextEquivalenceOutput
    - finiteSelectiveTwoActualReflectedNontrivialObject_high_image
    - finiteSelectiveTwoActualHighObject_structureMaps_heq
    - finiteSelectiveTwoActualHighObject_selectedQuantities_heq
    - finiteSelectiveTwoObjectContextWitnessBase_not_isIso
    - finiteSelectiveTwoReflectedLiftedNontrivialContext_eq
    - finiteSelectiveTwoLiftedReflectedNontrivialContext_eq
    - finiteSelectiveTwoSupportShapeMismatchContext_no_shape
    - finiteSelectiveTwoNonidentityRestriction_ne_identity
    - finiteSelectiveTwoReflectedLiftedNonidentityRestriction_eq
  claim_mapping:
    fixed_goal_clauses:
      - target theorem B and the material ledger retain FiniteModelLift as discharge-required before K0 in the current runtime route
      - premise policy forbids caller-supplied transported packages, hom graphs, low preimages, image membership, and conclusion-equivalent certificates
    runtime_route_constraints:
      - Issue 4034 requires generated-image object data before context/equation transport and whole-factor reflection
      - Cycle 19 selection permits carrier-shape equalities only in low-level generic helpers; the actual object producer must derive them internally and read the actual high values
    source_facts:
      - finiteGeneratedReflectedArchitectureObject uses finiteGeneratedULiftValueDown on the actual normalized high object projections and never reads the source object's two opaque inhabitants
      - finiteGeneratedNormalizedHighFactor_eq_canonical occurs only in the object image-alignment theorem, not in the reflected object's computational body
      - finiteModelReflectArchitectureContextAt takes only four carrier equalities and reads all predicates plus the extension value from the actual high context
      - finiteModelReflectContextMorphismAt reads all three actual high maps through carrier casts
      - the context-category lift is Full and Faithful only on canonical lifted endpoints; no essential-surjectivity or full-high equivalence is claimed
      - the witness context has nontrivial Support, Axis, Observable, and Extension carriers, both accepted and rejected readings, and a nonidentity restriction
    consequence:
      - complete ArchitectureObject generated-image descent is now typed and fired on an actual supplied-high factor
      - canonical context object/map image retraction is available for every low context and raw restriction
      - the exact eventual low context-equivalence output type is fixed, but the actual high equation-context functor/inverse and unit/counit have not yet been reflected
audits:
  premise_delta:
    discharged:
      - actual normalized high object generated-image alignment for every low object
      - both opaque carrier shapes generated internally from the actual factor
      - actual high structureMaps and selectedQuantities value descent with all-value round-trip laws
      - full object high-image equality including opaque fields
      - canonical four-carrier context lift and shape reflection with both complete context round trips
      - raw context-morphism lift/reflection, all three map graphs, and restriction preservation/reflection
      - Full/Faithful canonical context-category lift on image endpoints
      - concrete nonexistence of a carrier shape for an inhabited Boolean template versus an empty-support high context
      - nontrivial object, context, and nonidentity restriction witnesses
    remaining:
      - internally generated forward/inverse carrier shapes for the actual high equation context equivalence
      - actual high context functor/inverse object and map descent, comparison graphs, unit, and counit
      - equation-index and observable-ring equivalences, observable naturality, violation and residual generators
      - remaining operation, invariant, signature, and proof fields needed for SignedExactCoreReadingHom
      - whole PackageTotalHom descent, composition/equality reflection, and high-driven ambient factorization/uniqueness
      - FiniteModelLift and generated nonexistence transfer
      - K0 and K2-K4 after the F0 ledger is resolved
  certificate_provenance:
    discharged:
      - the top-level actual object producer accepts no shape, preimage, image, graph, or low-value certificate
      - both opaque values are transparent functions of actual high projections and internally generated carrier equalities
      - the finite witness generates its input, supplied high lift, package, base, object, context, and restriction internally
    qualified_primitive:
      - FiniteModelContextCarrierShape is a low-level four-type alignment used to define a generic on-image context reflector; it stores no predicate, map, preimage, functor, or equivalence
      - it is not counted as the missing generated actual-context-equivalence producer, whose shapes remain internally discharge-required
    prohibited_and_absent:
      - finiteGeneratedLowFactor, inverseCorePackageFactor, low cartesianness, globalCartesianLift, Classical.choose of a low preimage, and source opaque inhabitants in the reflected object body
  proof_use:
    used:
      - actual normalized high objectMap configuration and both opaque values in finiteGeneratedReflectedArchitectureObject
      - actual high predicates and extension in finiteModelReflectArchitectureContextAt
      - actual high supportMap, axisMap, and observableRestrict in finiteModelReflectContextMorphismAt
      - canonical equality only to derive generated-image object shapes and full image alignment
    not_yet_available:
      - actual normalized high equation context-equivalence descent and complete equation transport
  structure_field_escape: none in the generated object producer; the generic carrier-shape helper is explicitly outside the missing generated equivalence claim
  route_integrity: pass for complete object image descent and canonical context primitives; actual equation-context equivalence and whole factor remain open
  target_fitting: none found in implementation; object/context primitives quantify all low objects, contexts, and raw morphisms, while the concrete fixture only fires them
  vacuity: none found; opaque carriers and values are nontrivial, each context predicate has positive and negative cases, the restriction is not identity, and the public carrier-shape certificate has both a canonical positive instance and a concrete empty-support negative instance
  one_way_as_equivalence: none; the low-to-high context functor is only Full/Faithful, not an equivalence with all high contexts
  goal_or_report_reinterpretation: none; FiniteModelLift and the fixed ambient reflection output remain open
  validation_refs:
    - targeted FiniteGeneratedObjectImageDescent check: pass, 16 namespace declarations and standard axioms only
    - targeted FiniteGeneratedContextImageDescent check: pass, 49 namespace declarations and standard axioms only
    - official focused wrapper FiniteGeneratedObjectContextImageWitnesses.lean: pass, 69 namespace declarations and standard axioms only
    - manifest and umbrella wiring, diff, placeholder, hidden/BiDi Unicode, privacy, and import-direction scans: pass locally
    - fixed GOAL blob and SHA256 lock: pass
    - PR 4055 reviewed content head f0e8ecc565574bd512d1ac924d78839d86cdc0d9: 7/7 CI green and MERGEABLE/CLEAN
    - PR body synchronized to the repaired 69-declaration witness count and concrete carrier-shape negative instance
    - no Research aggregate or full build
  review_refs:
    independent_final_reviews:
      - Math A — No major findings
      - Math B — No major findings
      - Lean A — No major findings
      - Lean B — No major findings
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4055#issuecomment-5374145556
  stop_condition: none; continue before K0
  blocking_findings: []
  next_obligation: derive the forward and inverse canonical-image carrier shapes of the actual normalized high equation context equivalence internally; reflect its actual functor and inverse on every object and map; construct the exact FiniteGeneratedReflectedContextEquivalenceOutput with comparison graphs, unit, and counit; then descend the remaining EquationSystemExactTransport fields before assembling the whole actual-high-derived upper and total hom
```

### Cycle 18 — actual normalized high-factor computational field descent

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 18
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 1abce5fc8b047728045af097c80263e1726f6a8a
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 17 merge synchronization / Cycle 18 selection comment 5373045110
  proof_dag_predecessors:
    - Cycle 13-14 canonical finite package, configuration-hom, and equation ULift data, PR 4049/4050 merges c135ea34 / 2a0d76c
    - Cycle 16 generated low/high package-hom observations and exact reflection output types, PR 4052 merge 6477eff0
    - Cycle 17 actual supplied-high generated factor, canonical normalization, and low-independence theorem, PR 4053 merge 1abce5fc
  proof_obligation: construct the first computational fields of a low factor by reading finiteGeneratedNormalizedHighFactor itself, without selecting the known low inverse-upper factor or transporting the whole high hom along its equality with the canonical high factor
  selection_reason: Cycle 17 proved that pairing an independently generated low factor with a high equality is insufficient, while the existing finite-model ULift API already supports direct reflection of the actual high base, Atom equivalence, object configuration, and configuration map
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedFactorFieldDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedFactorFieldDescentWitnesses.lean
    - finiteGeneratedReflectedBase
    - finiteGeneratedReflectedUpperAtomEquiv
    - finiteGeneratedReflectedObjectConfiguration
    - finiteGeneratedReflectedConfigurationMap
  risks:
    - returning finiteGeneratedLowFactor or inverseCorePackageFactor through equality transport, Classical.choose, or a wrapper
    - using finiteGeneratedNormalizedHighFactor_eq_canonical to fill computational data rather than only to prove an image or alignment law
    - presenting configuration-only reflection as complete ArchitectureObject descent
    - presenting selected field observations as SignedExactCoreReadingHom, PackageTotalHom, or cartesianness reflection
    - hiding a caller-supplied image, endpoint, low factor, graph, or descent certificate in a structure field
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  reviewed_content_head: 4c690172be456bb24e4aa8ce05baf518978712a0
  proof_obligation_delta: constructed reflection of arbitrary ExactDoctrineHom and ExtInstHom values between canonical finite-model universe lifts, including two-sided round trips; defined the reflected base of the actual normalized supplied-high factor by applying that operation directly to its base projection; reflected the actual upper Atom equivalence by conjugation; reflected the configuration of the actual high object image and its actual configuration map; proved high-image graphs, prefix equality for the base and upper Atom map, and an Atom-level prefix graph for the configuration map; instantiated every field on the existing two-source chain, whose reflected base is proved noninvertible. Beyond the required supplied high lift, no known low factor, low cartesianness, additional low/image/descent certificate, or arbitrary high semantic descent is used by the computational definitions. Full ArchitectureObject data, context/equation transport, whole SignedExactCoreReadingHom and PackageTotalHom descent, ambient reflection, FiniteModelLift, K0, and theorem completion remain unclaimed.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedFactorFieldDescent.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedFactorFieldDescentWitnesses.lean
  evidence:
    - finiteModelReflectExactDoctrineHom
    - finiteModelReflectExactDoctrineHom_lift
    - finiteModelLiftExactDoctrineHom_reflect
    - finiteModelReflectExtInstHom
    - finiteModelReflectExtInstHom_lift
    - finiteModelLiftExtInstHom_reflect
    - finiteGeneratedReflectedBase
    - finiteGeneratedReflectedBase_high_graph
    - finiteGeneratedReflectedBase_eq
    - finiteModelReflectAtomEquiv
    - finiteGeneratedReflectedUpperAtomEquiv
    - finiteGeneratedReflectedUpperAtomEquiv_high_graph
    - finiteGeneratedReflectedUpperAtomEquiv_eq
    - finiteGeneratedReflectedObjectConfiguration
    - finiteGeneratedReflectedObjectConfiguration_high_graph
    - finiteGeneratedReflectedConfigurationMap
    - finiteGeneratedReflectedConfigurationMap_atom_graph
    - finiteGeneratedReflectedConfigurationMap_atom_eq
    - finiteSelectiveTwoActualReflectedBase_not_isIso
    - finiteSelectiveTwoActualHighFactor_upper_atom_graph
    - finiteSelectiveTwoReflectedCoreObjectConfiguration_high_graph
    - finiteSelectiveTwoReflectedCoreObjectConfigurationMap_atom_graph
  claim_mapping:
    fixed_goal_clauses:
      - target theorem B and the material ledger retain FiniteModelLift as discharge-required
      - premise policy forbids caller-supplied transported packages, hom graphs, conclusion-equivalent certificates, and decorative premises
    runtime_route_constraints:
      - Issue 4034 keeps the unresolved FiniteModelLift ledger item in the current F0 continuation before starting K0
      - Cycle 16-17 proof-use gate requires the low computational factor to be read from the actual supplied-high factor rather than independently generated first
    source_facts:
      - finiteModelReflectExactDoctrineHom reads the high sourceMap and atomEquiv projections and has both lift-reflect round trips on canonical lifted doctrines
      - finiteGeneratedReflectedBase reads finiteGeneratedNormalizedHighFactor.base directly
      - finiteGeneratedReflectedUpperAtomEquiv reads finiteGeneratedNormalizedHighFactor.upper.atomEquiv directly
      - finiteGeneratedReflectedObjectConfiguration reads the configuration of finiteGeneratedNormalizedHighFactor.upper.objectMap applied to a canonically lifted low object
      - finiteGeneratedReflectedConfigurationMap reads finiteGeneratedNormalizedHighFactor.upper.configurationMap and reflects the actual high ConfigurationHom
      - finiteGeneratedNormalizedHighFactor_eq_canonical appears only in proof-side graph/equality theorems and not in any reflected computational definition
      - the witness supplies its high lift, package, prefix, object, and configuration map by named internal constructions and proves the reflected prefix noninvertible
    consequence:
      - four computational layers of an actual-high generated-prefix descent are now typed, generated, and fired nonvacuously
      - opaque ArchitectureObject fields and EquationSystemExactTransport remain outside the claim
      - no whole hom or ambient universal property follows from this field checkpoint alone
audits:
  premise_delta:
    discharged:
      - exact-doctrine and pointed-hom reflection on canonical finite-model ULift endpoints
      - two-sided round-trip laws for those reflected lower homs
      - actual normalized high base descent and high graph
      - actual normalized high upper Atom descent and high graph
      - actual normalized high object-configuration and configuration-map descent
      - the same concrete firing data instantiate every exported field layer, and their reflected base is noninvertible
    remaining:
      - generated-image ArchitectureObject descent retaining StructureMaps and SelectedQuantities rather than discarding them
      - architecture-context lift and on-image functor/inverse laws for Support, Axis, Observable, and Extension
      - complete EquationSystemExactTransport descent, including contextEquivalence and observable naturality
      - remaining operation, invariant, signature, and proof fields needed for SignedExactCoreReadingHom
      - whole PackageTotalHom descent, composition/equality reflection, and high-driven ambient factorization/uniqueness
      - FiniteModelLift and generated nonexistence transfer
      - K0 and K2-K4 after the F0 ledger is resolved
  certificate_provenance:
    discharged:
      - every reflected computational value is a transparent named function of an actual high projection and canonical ULift equivalences
      - the finite witness generates its supplied high lift and all endpoints internally
    prohibited_and_absent:
      - caller-supplied low factor, image membership, component graph, descent, or conclusion-equivalent low cartesianness certificate beyond the required supplied high lift
      - Classical.choose of a low preimage
      - finiteGeneratedLowFactor, inverseCorePackageFactor, generated low cartesianness, or globalCartesianLift in reflected definitions
  proof_use:
    used:
      - actual high base sourceMap and atomEquiv in finiteModelReflectExactDoctrineHom
      - actual normalized high base in finiteGeneratedReflectedBase
      - actual normalized high upper atomEquiv in finiteGeneratedReflectedUpperAtomEquiv
      - actual normalized high objectMap configuration in finiteGeneratedReflectedObjectConfiguration
      - actual normalized high configurationMap in finiteGeneratedReflectedConfigurationMap
      - canonical factor equality only to prove external high-image and prefix-equality theorems
    not_yet_available:
      - actual-high computational descent for opaque object data and equation context equivalence
  structure_field_escape: none found; there is no packet accepting proof or comparison fields
  route_integrity: pass for the narrowed computational field-descent checkpoint; whole-factor and cartesianness reflection remain explicitly open
  target_fitting: none found; the generic reflection operations quantify arbitrary homs between canonical lifted finite-model endpoints, and the concrete fixture only fires the API
  vacuity: none found; the reflected concrete base is propositionally equal to a reviewed non-IsIso arrow
  one_way_as_equivalence: none found; two-sided equivalence is claimed only for exact/pointed homs between canonical lifted doctrines, while object and context descent remain unclaimed
  goal_or_report_reinterpretation: none; FiniteModelLift and the fixed ambient reflection output remain open
  validation_refs:
    - targeted ResearchLean.AG.DoctrineFiberProduct.FiniteGeneratedFactorFieldDescent module check: pass, 25 namespace declarations and standard axioms only
    - official focused wrapper ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedFactorFieldDescentWitnesses.lean: pass, 17 namespace declarations and standard axioms only
    - manifest and umbrella wiring, diff, placeholder, hidden/BiDi Unicode, privacy, and import-direction scans: pass at reviewed content head
    - fixed GOAL blob and SHA256 lock: pass
    - PR 4054 reviewed content head 4c690172be456bb24e4aa8ce05baf518978712a0: 7/7 CI green, mergeable/CLEAN
    - no Research aggregate or full build
  review_refs:
    independent_final_reviews:
      - Math A: No major findings for the narrowed Cycle 18 proof-checkpoint only
      - Math B: one Minor PR-body choice-provenance wording finding, closed by direct response; final No major findings
      - Lean A: two Minor report premise/runtime-classification findings, closed by report-only direct response; final No major findings
      - Lean B: provisional selection.unchecked finding withdrawn after cycle-ledger schema re-audit; final No major findings
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4054#issuecomment-5373297986
  stop_condition: none; continue before K0
  blocking_findings: []
  next_obligation: construct generated-image ArchitectureObject shape descent from actual high objectMap fields, then add architecture-context lift and on-image functor/inverse graphs sufficient to descend EquationSystemExactTransport.contextEquivalence and observable data; assemble the remaining upper computational fields into an actual-high-derived SignedExactCoreReadingHom and PackageTotalHom; only then use that descended factor to derive every ambient factor, factorization, and uniqueness field from the supplied high universal property
```

### Cycle 17 — supplied-high generated-factor comparison and proof-use checkpoint

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 17
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 6477eff07bf25c536f988135c4076bdcee9e7f3a
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 16 merge synchronization / Cycle 16 exact downstream reflection signature
  proof_dag_predecessors:
    - Cycle 8 inverse-package forward/backward upper round trips, PR 4044 merge 9f144dfd
    - Cycle 15 same-carrier canonical-domain inverse triangle, PR 4051 merge ab63c6f3
    - Cycle 16 generated package-hom ULift naturality and selected two-arrow coherence, PR 4052 merge 6477eff0
  proof_obligation: apply the supplied high strong-cartesian universal property to every generated prefix, normalize the resulting high factor, and determine whether the resulting comparison materially constructs the ambient low factors required by the fixed reflection signature
  selection_reason: Cycle 16 supplied complete endpoint and upper-component observations but had not yet connected the supplied high universal property to the arbitrary low factor problems quantified by ReflectedGeneratedUniversalProperty
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedFactorComparison.lean
    - finiteGeneratedNormalizedHighFactor_eq_canonical
    - GeneratedPrefixFactorComparison
    - generatedPrefixFactorComparison_lowFactor_independent
  risks:
    - pairing an independently generated low inverse-upper factor with a high equality and calling the pair reflection
    - reusing the generated low strong-cartesian proof or its local upper-inverse proof while the supplied high premise is decorative
    - treating an Atom-only graph as a whole SignedExactCoreReadingHom reflection
    - using a caller-supplied image, factor, component graph, or descent certificate
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  reviewed_content_head: cf544391248fd7e126b576e1ffe0b0a5e8ebe329
  proof_obligation_delta: constructed the explicit inverse-package factor, its IsHomLift/factorization/uniqueness laws, and the generated outer-input decomposition; applied Mathlib IsStronglyCartesian.map to the actual supplied high lift for every finite-model prefix, normalized the resulting factor by canonicalDomainIso.hom, and proved whole-PackageTotalHom equality with the named high inverse-package factor; independently constructed the corresponding low whole-upper factor and full total hom; generated the complete Cycle 16 component comparison for the canonical low hom and instantiated the packet on the noninvertible two-source chain. An initial ambient-reflection prototype was rejected by four independent pre-PR lanes because its low factor, factorization, uniqueness, and final strong-cartesian proof were definitionally independent of the supplied high lift. Those declarations were removed. The surviving theorem generatedPrefixFactorComparison_lowFactor_independent records that exact proof-use limitation in Lean. FiniteModelLift, the Cycle 16 reflected hom/universal-property signature, K0, and theorem completion remain unclaimed.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedFactorComparison.lean
  evidence:
    - inverseCorePackageFactor
    - inverseCorePackageFactor_isHomLift
    - inverseCorePackageFactor_fac
    - inverseCorePackageFactor_unique
    - finiteGeneratedHighFactor
    - finiteGeneratedHighFactor_fac
    - finiteGeneratedNormalizedHighFactor
    - finiteGeneratedNormalizedHighFactor_fac
    - finiteGeneratedCanonicalHighFactor
    - finiteGeneratedNormalizedHighFactor_eq_canonical
    - finiteGeneratedLowFactorUpper
    - finiteGeneratedLowFactor
    - GeneratedPrefixFactorComparison
    - generatedPrefixFactorComparison
    - generatedPrefixFactorComparison_lowFactor_independent
    - finiteGeneratedAmbientToOuter
    - finiteGeneratedAmbientToOuter_fac
    - canonicalLowGeneratedComponentComparison
    - finiteSelectiveTwoGeneratedPrefixFactorComparison
  claim_mapping:
    theorem_names:
      - finiteGeneratedNormalizedHighFactor_eq_canonical
      - generatedPrefixFactorComparison_lowFactor_independent
      - canonicalLowGeneratedComponentComparison
    source_labels:
      - target theorem B FiniteModelLift universe transport clause
      - material-premise ledger FiniteModelLift discharge-required line
      - Cycle 16 exact downstream reflection signature and material proof-use gate
    conjuncts:
      - supplied high universal property generates and normalizes the complete high prefix factor
      - canonical low/high factors and full selected component comparison are available without caller certificates
      - the naive paired low factor is formally independent of the supplied high lift and therefore cannot discharge reflection
    undischarged_assumptions:
      - structural whole-factor descent from the actual normalized high factor
      - ambient low factorization and uniqueness driven by supplied high cartesianness
      - graph-bearing FiniteModelLift and no-lift corollary without empty elimination
    acceptance_point: useful proof-use checkpoint and rejected-route witness only; not reflection discharge
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - actual supplied-high generated prefix factor and canonical normalization
      - explicit inverse-package factor laws in either carrier
      - arbitrary ambient low competitor decomposition into an outer generated inverse package
      - complete selected component comparison for the already generated canonical low hom
      - formal identification of the low-first pairing route as supplied-lift independent
    remaining:
      - generated low hom whose computational data are structurally descended from the actual normalized high factor
      - high-driven ambient factorization, factorization law, and uniqueness
      - exact Cycle 16 reflectNormalizedHighHom and ReflectedGeneratedUniversalProperty producers
      - FiniteModelLift and generated nonexistence transfer
      - K0 and K2-K4 after the F0 ledger is resolved
  certificate_provenance:
    discharged:
      - high factor is generated by Mathlib IsStronglyCartesian.map from input, prefix, and the supplied high lift
      - canonical comparison, low inverse factor, component packet, and finite witness are named internal constructions
    unresolved:
      - a caller-free whole SignedExactCoreReadingHom descent operation on the actual normalized high factor
  proof_use:
    used:
      - lift.hom and lift.isStronglyCartesian in finiteGeneratedHighFactor and its factorization law
      - canonicalDomainIso_hom_fac in high-factor normalization
      - inverseCorePackageFactor_unique in normalized-high whole-hom equality
      - inverseCorePackage backward/forward round trips in the independent low factor scaffold
      - generatedPackageHomULiftNaturality and every selected component graph in canonicalLowGeneratedComponentComparison
    unused:
      - supplied high lift in the low factor value and low factor laws, now exposed by generatedPrefixFactorComparison_lowFactor_independent
  structure_field_escape: concern found and removed from the proposed ambient reflection; the surviving comparison structure makes no reflection or cartesianness claim
  route_integrity: pass for the narrowed comparison checkpoint; fail for the removed low-first ambient reflection prototype
  target_fitting: none found in the surviving universal high-factor construction; the concrete fixture is only a noninvertible firing witness
  vacuity: none found; the supplied high type is inhabited, Mathlib map is invoked, and the concrete prefix is noninvertible
  one_way_as_equivalence: none found; no full package functor or arbitrary high descent is claimed
  goal_or_report_reinterpretation: none; the fixed Cycle 16 reflection signature and FiniteModelLift remain open
  validation_refs:
    - official focused wrapper ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedFactorComparison.lean: pass after review repair, 52 namespace declarations and standard axioms only
    - manifest and umbrella wiring, diff, placeholder, hidden/BiDi Unicode, privacy, and import-direction scans: pass
    - fixed GOAL blob and SHA256 lock: pass
    - PR 4053 repaired content head cf544391248fd7e126b576e1ffe0b0a5e8ebe329: 7/7 CI green, mergeable/CLEAN
    - no Research aggregate or full build
  review_refs:
    independent_final_reviews:
      - Math A: No major findings for the narrowed Cycle 17 proof-checkpoint only
      - Math B: No major findings for the narrowed Cycle 17 proof-checkpoint only
      - Lean A: one Minor docstring-direction finding, closed by direct-response review at repaired content head; final No major findings
      - Lean B: No major findings for the narrowed Cycle 17 proof-checkpoint only
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4053#issuecomment-5372734342
  stop_condition: none; continue before K0
  blocking_findings:
    - the low-first paired route cannot satisfy the Cycle 16 material proof-use gate because its low projection is independent of the supplied high lift
  next_obligation: define a specialized generated-prefix whole-factor descent whose base and SignedExactCoreReadingHom computational fields are constructed from finiteGeneratedNormalizedHighFactor itself, prove its composition and equality-reflection laws without first selecting finiteGeneratedLowFactor, use that output in every ambient factor/fac/unique field, and only then retry the exact Cycle 16 reflection signature
```

### Cycle 16 — generated finite package-hom ULift naturality and coherence

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 16
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: ab63c6f3e75ce794c896e4d04f9e701a9353b7de
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 15 merged / Cycle 16 selection comment 5370429848
  proof_dag_predecessors:
    - Cycle 8 inverse-package strong-cartesian constructor, PR 4044 merge 9f144dfd
    - Cycle 13-14 canonical finite package and equation ULift data, PR 4049/4050 merges c135ea34 / 2a0d76c
    - Cycle 15 inverse triangle for arbitrary high strong lifts, PR 4051 merge ab63c6f3
  proof_obligation: consume domainIso_inv_fac before cross-carrier work and construct a typed generated-package/hom naturality theorem; if reflection does not safely fit one review unit, fix its exact downstream signature without claiming a full package functor
  selection_reason: arbitrary high domains no longer need direct descent after same-carrier normalization, but the generated low/high package homs still lacked a proof-used cross-carrier relation across their upper computational and semantic components
  expected_result_type: proof-checkpoint at the Issue-authorized typed naturality split gate
  risks:
    - caller-supplied package, image, endpoint, index, operation, descent, or graph certificates
    - calling a selected finite observation a functor or equality of cross-carrier PackageTotalHom values
    - equation-index equivalence cancellation without detector or EquationHolds semantics
    - returning the already generated low lift while the arbitrary high lift and its cartesianness are decorative
    - weakening ambient Mathlib strong cartesianness to an image-only universal property
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  reviewed_content_head: 6a3b067276dd4fa7d9fd13c70dd184d01e17299a
  proof_obligation_delta: constructed canonical lifting for arbitrary finite-model ExtractionInstance, ExactDoctrineHom, and ExtInstHom with source, Atom, identity, and composition laws; generated named high inverse package and PackageTotalHom data directly from the lifted low arrow; proved endpoint, projection, base, Atom, object, configuration, equation-map, detector, EquationHolds, operation, invariant, axis, and coordinate observations against the generated low inverse package; normalized every supplied ambient high strong lift by canonicalDomainIso.inv followed by its actual hom and used domainIso_inv_fac to identify that composite with the named high hom; bundled all observations in GeneratedPackageHomULiftNaturality indexed only by the original finite input and generated it without caller proof fields; for every two-arrow chain ending at the selected target, constructed direct and staged generated PackageTotalHom lifts in both carriers, used actual PackageTotalHom composition and Mathlib strong-cartesian composition, and proved unit/compositor coherence up to the canonical vertical domain iso; instantiated naturality and coherence on a concrete noninvertible two-source portfolio chain; fixed ReflectedGeneratedComponentGraph and ReflectedGeneratedUniversalProperty as elaborated theorem-output types for the next reflection step. This is not a complete cross-carrier package functor, arbitrary-hom reflection, FiniteModelLift, K0, or theorem completion.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedLiftNaturality.lean
  evidence:
    - finiteModelLiftExactDoctrineHom_id
    - finiteModelLiftExactDoctrineHom_comp
    - finiteModelLiftExtInstHom_id
    - finiteModelLiftExtInstHom_comp
    - FiniteGeneratedLiftInput.highPackageFromLowData
    - FiniteGeneratedLiftInput.highPackageHomFromLowData
    - FiniteGeneratedLiftInput.inverseGeneratedDomain_detectorCode_graph
    - FiniteGeneratedLiftInput.inverseGeneratedDomain_equationHolds_iff
    - FiniteGeneratedLiftInput.generatedUpper_operation_configurationMap_graph
    - FiniteGeneratedLiftInput.generatedUpper_invariantMap_graph
    - FiniteGeneratedLiftInput.generatedUpper_axisMap_graph
    - FiniteGeneratedLiftInput.generatedUpper_coordinateEquiv_graph
    - FiniteGeneratedLiftInput.normalizedHighHom
    - FiniteGeneratedLiftInput.normalizedHighHom_eq_highPackageHomFromLowData
    - GeneratedPackageHomULiftNaturality
    - generatedPackageHomULiftNaturality
    - GeneratedLiftChain
    - GeneratedLiftChain.unitIso_fac
    - GeneratedLiftChain.compIso_fac
    - GeneratedPackageHomULiftCoherence
    - generatedPackageHomULiftCoherence
    - finiteIdentityGeneratedInput_high_base
    - FiniteSelectedGeneratedChain.lift_composite_base
    - ReflectedGeneratedComponentGraph
    - ReflectedGeneratedUniversalProperty
    - finiteSelectiveTwoGeneratedChain_composition_coherence
    - finiteSelectiveTwoGeneratedPackageHomULiftNaturality
  claim_mapping:
    fixed_goal_clauses:
      - target theorem B describes FiniteModelLift on the right-branch finite counterexample, while the literal material ledger retains the artifact as an unconditional pre-K0 discharge item
      - premise policy forbids supplying transported packages, hom graphs, or conclusion-equivalent certificates
      - Issue 4034 comment 5370429848 permits a split only at a typed generated-package/hom naturality theorem with the exact downstream reflection signature fixed in this report
    source_facts:
      - PackageTotalHom is same-carrier, so the cross-carrier statement is a generated observational relation rather than an ill-typed equality
      - the named high package and hom close only over input.hom, the canonical carrier equivalence, the selected lifted target package, and inverseCorePackage/inverseCorePackageHom
      - the equation relation contains both detector syntax and EquationHolds preservation/reflection; it is not only apply_symm_apply for an equation-index equivalence
      - operation endpoint casts are generated from the proved object-map equality
      - invariant and signature observations use the selected singleton/constant readings and actual inverse-upper maps
      - normalizedHighHom contains canonicalDomainIso(lift).inv followed by lift.hom, and its equality uses domainIso_inv_fac
      - generated PackageTotalHom identity and composition are compared honestly up to canonical vertical domain isomorphism because direct and staged generated domains need not be definitionally equal; explicit high-base laws consume finiteModelLiftExtInstHom_id/comp
    consequence:
      - generated low/high endpoint and upper-component observations are now available as one theorem output
      - generated identity and arbitrary selected-target two-arrow composition are coherent in both carriers, and composite/tail naturality packets are produced uniformly
      - arbitrary high package descent, a full cross-carrier package-category functor, and reflection of arbitrary package homs remain unclaimed
      - the next cycle must reflect cartesianness from the normalized high hom through the generated observations, not reuse the existing low cartesianness proof
audits:
  premise_delta:
    discharged:
      - canonical low ExtInstHom lift with identity and composition laws
      - selected-target generated PackageTotalHom unit and arbitrary two-arrow composition coherence in both carriers, up to canonical vertical domain isomorphism, with explicit lifted identity/composite base alignment
      - independent named high inverse package and total hom from the low input
      - endpoint, base, projection, and selected upper-component cross-carrier graphs
      - detector syntax and EquationHolds semantics on generated low/high inverse domains
      - arbitrary-high inverse-triangle normalization before cross-carrier reflection
      - a caller-certificate-free proof-only naturality producer
      - noninvertible concrete firing input and noninvertible two-arrow coherence chain
    remaining:
      - generated reflection of the normalized high hom to a low PackageTotalHom
      - ambient strong-cartesian reflection using the supplied high IsStronglyCartesian universal property
      - producer of the fixed ReflectedGeneratedComponentGraph and ReflectedGeneratedUniversalProperty output types, plus the one-direction retraction theorem
      - FiniteModelLift and its generated nonexistence corollary without empty elimination
      - K0 and K2-K4 after the F0 ledger is resolved
  certificate_provenance:
    discharged:
      - GeneratedPackageHomULiftNaturality is indexed only by FiniteGeneratedLiftInput and all proof fields are filled by the named producer
      - GeneratedPackageHomULiftCoherence quantifies every selected-target two-arrow chain and generates its packages, strong lifts, unit/compositor isomorphisms, and naturality packets internally
      - index, operation, endpoint, package, and hom values are definitions, not caller arguments
      - the concrete witness uses the reviewed finite portfolio and proves its lower arrow noninvertible
    prohibited:
      - taking GeneratedPackageHomULiftNaturality as a premise in the downstream producer instead of invoking generatedPackageHomULiftNaturality
      - taking GeneratedPackageHomULiftCoherence, ReflectedGeneratedComponentGraph, or ReflectedGeneratedUniversalProperty as a caller premise instead of invoking their named producers
      - caller-supplied image membership, descent, component graph, reflected hom, or cartesianness proof
      - using globalCartesianLift or input.lowGeneratedLift.isStronglyCartesian as the downstream reflected cartesianness proof
  proof_use:
    used:
      - inverseCorePackage and inverseCorePackageHom for both generated domains and homs
      - finiteModelLiftExtInstHom_id/comp in the high unit and direct-composite base-alignment fields
      - finite carrier, family, configuration, object, circuit, equation, invariant, signature, and operation lift laws in the selected observations
      - SignedExactCoreReadingHom equation_holds_iff on both same-carrier sides
      - StrongCartesianLift.canonicalDomainIso and domainIso_inv_fac on every supplied high lift
      - Mathlib IsStronglyCartesian.comp and PackageTotalHom composition in every staged two-arrow lift, followed by domainIso_hom_fac for both unit and compositor laws
      - the finite portfolio noninjective source map in the non-IsIso witness
    next_use:
      - the downstream producer must internally invoke generatedPackageHomULiftNaturality input
      - lift.hom and lift.isStronglyCartesian must drive the reflected ambient universal-property proof
      - every arbitrary low competitor in IsStronglyCartesian must be handled by newly generated operations, not a caller certificate or an image-only replacement category
  structure_field_escape: avoided in the current artifact. The naturality and coherence packets contain proofs about named generated data and no replaceable package, hom, index map, operation map, or semantic conclusion field. ReflectedGeneratedUniversalProperty is deliberately only the exact next theorem-output type; its future producer may not accept any instance of it from the caller.
  route_integrity: the arbitrary high lift is first normalized in the ambient package category and only the resulting theorem-generated endpoint/hom is compared cross-carrier. The selected observations do not claim a whole-structure equality that the type system cannot state.
  target_fitting: the naturality packet is uniform in every source pointed instance and exact arrow into the selected FiniteModel package; unit/compositor coherence quantifies every two-arrow chain ending there. The concrete two-source chain is only a nondegenerate firing witness.
  vacuity: both packets are universally produced, normalization quantifies an inhabited StrongCartesianLift type, detector and EquationHolds layers have semantic content, staged composition uses two actual generated package homs, and both the concrete first arrow and direct composite are noninvertible.
  one_way_as_equivalence: avoided. Only one-way canonical lifts plus explicitly listed preservation/reflection propositions are claimed; no arbitrary high object/package is lowered.
  validation_refs:
    - official focused wrapper ResearchLean/AG/DoctrineFiberProduct/FiniteGeneratedLiftNaturality.lean: pass after review repair, 234 namespace declarations and standard axioms only
    - manifest and umbrella wiring: pass
    - fixed GOAL blob and SHA256 lock: pass
    - diff, placeholder, hidden/BiDi Unicode, privacy, and import-direction scans: pass
    - PR 4052 repaired content head 6a3b067276dd4fa7d9fd13c70dd184d01e17299a: 7/7 CI green, mergeable/CLEAN
    - no local Research aggregate/full build
  review_refs:
    preliminary_design_review:
      - Math: initial observational layer passed, then fixed-head review required package-level unit/composition coherence and an elaborated downstream reflection contract
      - Lean: initial source layer passed, then fixed-head review required the downstream dependent relation to exist as a Lean type
    standard_review_pr: Mergeable at repaired content head; the sole stale-PR-body count finding was already closed by synchronizing the live body to 234 declarations and the repaired scope
    independent_final_reviews:
      - Math A: No major findings for Cycle 16 only
      - Math B: No major findings for Cycle 16 only
      - Lean A: No major findings for Cycle 16 only; official focused wrapper passed with 234 declarations and standard axioms only
      - Lean B: No major findings for Cycle 16 only; official focused wrapper passed with 234 declarations and standard axioms only
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4052#issuecomment-5371912551
  stop_condition: none; continue before K0
  exact_downstream_reflection_signature: |
    -- ReflectedGeneratedComponentGraph and
    -- ReflectedGeneratedUniversalProperty are actual elaborated structures in
    -- FiniteGeneratedLiftNaturality.lean, not report-only aliases.

    noncomputable def reflectNormalizedHighHom.{u}
        (input : FiniteGeneratedLiftInput)
        (lift : StrongCartesianLift input.highInput input.highTarget) :
        input.lowGeneratedLift.domain ⟶ FiniteModel.corePackage

    theorem reflectNormalizedHighHom_base.{u} (input) (lift) :
      (reflectNormalizedHighHom input lift).base = input.hom

    theorem reflectNormalizedHighHom_components.{u} (input) (lift) :
      ReflectedGeneratedComponentGraph input lift
        (reflectNormalizedHighHom input lift)

    noncomputable def reflectNormalizedUniversalProperty.{u} (input) (lift) :
      ReflectedGeneratedUniversalProperty input lift
        (reflectNormalizedHighHom input lift)

    theorem reflectNormalizedHighHom_retraction.{u} (input) (lift) :
      reflectNormalizedHighHom input lift = input.lowGeneratedLift.hom

    theorem reflectNormalizedHighHom_isStronglyCartesian.{u} (input) (lift) :
      (packageProjection FiniteModel.carrier).IsStronglyCartesian
        input.lowInput.hom (reflectNormalizedHighHom input lift)

    noncomputable def reflectNormalizedStrongCartesianLift.{u}
        (input : FiniteGeneratedLiftInput)
        (lift : StrongCartesianLift input.highInput input.highTarget) :
        StrongCartesianLift input.lowInput input.lowTarget

    theorem reflectNormalizedStrongCartesianLift_domain.{u} (input) (lift) :
      (reflectNormalizedStrongCartesianLift input lift).domain =
        input.lowGeneratedLift.domain

    theorem reflectNormalizedStrongCartesianLift_hom.{u} (input) (lift) :
      (reflectNormalizedStrongCartesianLift input lift).hom =
        reflectNormalizedHighHom input lift

    ReflectedGeneratedComponentGraph fixes Atom, object/configuration,
    equation/detector, operation, invariant, signature, normalized-high-hom,
    domain, and projection graphs. ReflectedGeneratedUniversalProperty fixes an
    output factor for every ambient low package/base/hom problem together with
    IsHomLift, factorization, and uniqueness. Neither structure may be a caller
    argument. The producer must internally invoke
    generatedPackageHomULiftNaturality input and use lift.hom plus
    lift.isStronglyCartesian to construct those ambient factors. Because proof
    irrelevance cannot encode proof-term provenance in the result type, fresh
    review must directly verify that proof-use. It may not use
    globalCartesianLift, reuse input.lowGeneratedLift.isStronglyCartesian, or
    replace ambient IsStronglyCartesian by an image-only property.
  next_obligation: construct the exact reflected hom/component relation and prove ambient strong-cartesian reflection from the supplied normalized high lift; then package FiniteModelLift and its graph-bearing nonexistence transfer or fail closed with a formal obstruction to this exact signature
```

### Cycle 15 — same-carrier strong-lift comparison and reflection checkpoint

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 15
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 2a0d76c22a1e21b352007c10592c3143f0a94291
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 14 merged / Cycle 15 selection comment 5369971369
  proof_dag_predecessors:
    - Cycle 9 arbitrary-target strong cartesian lifts and GlobalCartesianLift, PR 4045 merge 75627b6825fb0b715e4fab29fe3a7f3e0f159b79
    - Cycle 12 emptiness of every CartesianLiftNonexistence under the generated global branch, PR 4048 merge 037f343c2972ca342c3b360de12960f7367289f9
    - Cycles 13-14 one-way finite package, equation, circuit, and AATCorePackage ULift construction, PR 4049/4050 merges c135ea34373f9d7b98117a7f8c92987f0338d79c / 2a0d76c22a1e21b352007c10592c3143f0a94291
  proof_obligation: construct the exact package-total hom and arbitrary-strong-lift reflection required to make the fixed-ledger FiniteModelLift structural rather than an empty implication, while preserving ambient strong cartesianness; if direct descent fails, isolate and consume any same-carrier normalization before classifying the route
  selection_reason: object-level finite package ULift is complete, so the only pre-K0 residual is whether an arbitrary high-universe strong lift can be descended to a base lift with generated endpoint and hom graph laws rather than empty elimination
  expected_result_type: proof-checkpoint toward a generated reflection, unless a formal no-go covers normalization through the canonical high lift
  risks:
    - using the already generated base global lift while the supplied high lift is decorative
    - treating a same-carrier cartesian-domain isomorphism as a cross-carrier package descent
    - accepting image membership, a descended package, total hom, or graph equality as a caller certificate
    - replacing Mathlib ambient strong cartesianness by an image-restricted universal property
    - claiming that Atom/configuration reflection lowers arbitrary Type-u package reading data
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: proved that any two strong lifts of the same semantic arrow to the same target package have a canonical domain isomorphism, both triangle equations, and verticality over the source identity; specialized the comparison to the generated lift and to the concrete lifted finite core package. Directly lowering an arbitrary lifted domain package and all of its SignedExactCoreReadingHom data remains unavailable, but independent review showed that this does not establish a no-go: the inverse triangle first normalizes an arbitrary lifted hom to the generated high domain, after which the live route can focus on theorem-generated low-to-high naturality and reflection between canonical image endpoints. The proposed terminal goal-defect is therefore withdrawn. A bare FiniteModelLift implication remains inadmissibly empty under GlobalCartesianLift, so the fixed-ledger item stays open until a generated data-level reflection is constructed or its branch-conditioned status is resolved without weakening the fixed contract.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteModelLiftComparison.lean
  evidence:
    - StrongCartesianLift.domainIso
    - StrongCartesianLift.domainIso_hom_fac
    - StrongCartesianLift.domainIso_inv_fac
    - StrongCartesianLift.domainIso_hom_isHomLift
    - StrongCartesianLift.domainIso_inv_isHomLift
    - StrongCartesianLift.canonicalDomainIso
    - StrongCartesianLift.canonicalDomainIso_hom_fac
    - finiteModelLiftIdentityDomainIso
    - finiteModelLiftIdentityDomainIso_hom_fac
    - cartesianLiftNonexistence_isEmpty
    - rightBranch_isEmpty
    - globalCartesianLift
  claim_mapping:
    fixed_goal_clauses:
      - target theorem B lines 196-220 permits either one carrier-global left branch or one qualified right branch and describes FiniteModelLift as transport of the right-branch finite counterexample
      - target artifacts lines 594-600 and material-premise ledger lines 738-740 nevertheless list FiniteModelLift as discharge-required; this cycle retains that literal item rather than discharging it by the already selected left branch
      - premise and anti-weakening policy lines 665-671 and 795-807 reject conclusion-equivalent supplied data and require generated proof use
      - failure policy lines 830-833 permits goal-defect only after the acceptance contract is shown insufficient; this cycle does not reach that threshold
    source_facts:
      - globalCartesianLift constructs a StrongCartesianLift for every carrier, realized input, and target-fiber package, so CartesianLiftNonexistence is empty at every universe
      - StrongCartesianLift.domain is an arbitrary AATCorePackage at the ambient carrier and its hom is a full PackageTotalHom, not an image-tagged finite package
      - PackageTotalHom and SignedExactCoreReadingHom are same-carrier types; the latter contains maps over all ArchitectureObject values plus dependent equation, operation, invariant, and signature data
      - arbitrary lifted ArchitectureObject and reading fields contain genuine Type-u carriers; finiteModelSemanticDescent reflects only configuration and intentionally discards opaque StructureMaps and SelectedQuantities, so direct arbitrary-package descent is unavailable
      - Mathlib cartesian uniqueness produces a vertical isomorphism between domains of two already-cartesian arrows in the same total/base categories; the new Lean comparison theorem records exactly this result
      - domainIso_inv_fac rewrites the supplied arbitrary lifted hom as a composite from the generated high domain, so a reflection route can avoid lowering the arbitrary domain itself
    consequence:
      - same-carrier normalization of an arbitrary high lift to the generated high lift is available and proof-used
      - no cross-carrier package object or total-hom reflection is yet produced by that normalization
      - the live route is to construct generated low-to-high package/hom naturality and reflect only the normalized hom between canonical image endpoints, without caller certificates or an image-only replacement universal property
      - FiniteModelLift remains uncounted until that route yields a graph-bearing reflection and a named no-lift corollary; branch-conditioned applicability is not used here to erase the literal ledger item
audits:
  premise_delta:
    discharged:
      - same-carrier domain comparison for arbitrary pairs of strong cartesian lifts
      - forward and inverse triangle laws and vertical source-identity laws
      - comparison with the generated strong lift at arbitrary endpoints
      - concrete elaborated comparison at the lifted finite core package
    remaining:
      - canonical low-to-high package and PackageTotalHom rebase for the generated finite endpoints
      - projection, endpoint, identity, composition, and upper-component graph laws for that rebase
      - naturality identifying the generated high lift with the rebase of the generated low lift
      - reflection of the normalized hom between canonical image endpoints, with round-trip and strong-cartesianness laws
      - FiniteModelLift as a generated nonexistence transfer rather than empty elimination, if retained as a literal branch-independent ledger artifact
      - K0 and K2-K4 after the F0 ledger is resolved
  certificate_provenance:
    discharged:
      - domainIso closes only over the two supplied strong lifts and their actual IsStronglyCartesian proofs
      - both comparison maps and factorization laws come from Mathlib cartesian uniqueness
      - the concrete comparison witness uses generated lifted package and strong-lift constructors
    prohibited:
      - supplying a low package, low total hom, image-membership proof, domain iso, or hom graph as reflection input
      - using globalCartesianLift or strongCartesianLiftOfTarget to manufacture the low output while ignoring the high lift
      - a counterexample-specific equivalence between empty lift types
  proof_use:
    used:
      - both IsStronglyCartesian witnesses in Mathlib domain uniqueness
      - both total lift morphisms in the forward and inverse triangle equations
      - packageProjection and the exact semantic bottom arrow in the vertical IsHomLift laws
      - the generated lifted finite CorePackage in the concrete comparison
    next_use:
      - domainIso_inv_fac must normalize an arbitrary supplied high lift before the cross-carrier reflection step
      - generated package/hom naturality and image-endpoint factor reflection must be newly constructed and consumed
      - there is no inhabitant of CartesianLiftNonexistence FiniteModel.carrier on which a bare no-lift implication can fire
  structure_field_escape: avoided in the Lean artifact; no reflection context structure or caller certificate is introduced. Adding the missing domain/package/hom graph as fields would merely assume the undischarged conclusion.
  route_integrity: the formal theorem stops exactly at the same-carrier vertical iso delivered by cartesian uniqueness. Review rejected the initial route restriction to direct arbitrary-domain descent; the next route keeps the ambient Mathlib universal property and uses the inverse triangle before reflecting a normalized canonical-image hom.
  target_fitting: none; domainIso is uniform over every carrier, semantic input, target package, and pair of strong lifts. The concrete finite-package specialization is only an elaboration witness.
  vacuity: same-carrier normalization is inhabited and consumes actual lifts. The bare finite nonexistence implication has an empty source by cartesianLiftNonexistence_isEmpty and therefore is not counted; the planned data-level reflection can instead be exercised on actual lifted StrongCartesianLift values.
  one_way_as_equivalence: avoided; Cycles 13-14 remain one-way at ArchitectureObject/AATCorePackage level, and this cycle adds only a same-carrier iso between strong-lift domains.
  goal_or_report_reinterpretation: the initial terminal goal-defect inference is withdrawn. FiniteModelLift is semantically attached to the right-branch counterexample, but because the material ledger lists it discharge-required this report retains a generated structural artifact as the fail-closed residual rather than declaring it automatically inapplicable.
  validation_refs:
    - official focused wrapper ResearchLean/AG/DoctrineFiberProduct/FiniteModelLiftComparison.lean: pass, namespace audit 9 declarations and standard axioms only
    - manifest and umbrella wiring: pass
    - fixed GOAL blob and SHA256 lock: pass
    - diff, placeholder, hidden/BiDi Unicode, privacy, and import-direction scans: pass
    - repaired content head CI: 7/7 success, mergeable/CLEAN
    - no local Research aggregate/full build
  review_refs:
    initial_fixed_head: 4a996eb7ceeb8fbbdf3345869a5958f35af2f2de
    repaired_head: 6d63e24b8f347ce207c7afb099225a465c0c3e7b
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4051#issuecomment-5370360922
    initial_verdicts:
      - Math A Major: global-left does not by itself require a nonempty right-branch counterexample, and generated-image normalization remains a legal route
      - Math B Major: arbitrary ambient package descent and global fullness were overrequired; retain package/hom naturality and image-endpoint reflection as obligations
      - Lean A Major: normalization route remains and the initial public status terminology violates the AAT documentation hard rule
      - Lean B Major: domainIso_inv_fac eliminates the arbitrary-domain obstacle before cross-carrier reflection
      - standard review-pr content gate: Pass for the nine same-carrier declarations and provisional packet
    repaired_verdicts:
      - Math A: Pass, no major findings for the Cycle 15 proof-checkpoint only
      - Math B: Pass, no major findings for the Cycle 15 proof-checkpoint only
      - Lean A: Pass, no major findings for the Cycle 15 proof-checkpoint only
      - Lean B: Pass, no major findings for the Cycle 15 proof-checkpoint only
  review_repairs:
    - withdrew blocker-fixed, goal-defect, and next-obligation-none claims
    - renamed the public module and descriptions to state the proved same-carrier comparison directly
    - retained the literal FiniteModelLift ledger item while separating it from a nonempty right-branch application
    - fixed the next route at generated-lift naturality plus normalized image-endpoint reflection
  stop_condition: none; continue before K0 without empty elimination or arbitrary-domain descent
  next_obligation: construct and review canonical generated-lift ULift naturality and reflection of the normalized high hom between image endpoints, then derive a graph-bearing data-level reflection and decide the fixed FiniteModelLift artifact without weakening ambient strong cartesianness
```

### Cycle 14 — lifted finite equation, circuit, and core package

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 14
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: c135ea34373f9d7b98117a7f8c92987f0338d79c
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 13 merged / Cycle 14 selection comment 5369565454
  proof_dag_predecessors:
    - Cycle 7 finite presentation and checker ULift rebase, PR 4043 merge 9400096d8a55f12ea6e18ee5f64bf7d73c650bf2
    - Cycle 12 FiniteModelLift nonvacuity guard, PR 4048 merge 037f343c2972ca342c3b360de12960f7367289f9
    - Cycle 13 canonical finite-package ULift foundation, PR 4049 merge c135ea34373f9d7b98117a7f8c92987f0338d79c
  proof_obligation: rebase the finite circuit syntax, construct a direct lifted FiniteModel NoCycle equation and sound detector on every lifted object, assemble the complete lifted CoreReading and AATCorePackage, and exhibit nondegenerate cyclic and acyclic witnesses without introducing a generic EquationReading transport or any reflection certificate
  selection_reason: Cycle 13 deliberately stopped before equations and package assembly; these generated data and soundness laws are the last object-level prerequisites before package-total hom rebasing and structural strong-lift reflection can be stated exactly
  expected_result_type: proof-checkpoint
  risks:
    - pretending to transport a generic EquationReading across carriers whose contexts quantify arbitrary high-universe objects
    - lowering arbitrary lifted ArchitectureObject fields rather than reading only their actual configuration
    - accepting a matching, soundness, equation, package, or reflection certificate from the caller
    - using an empty/default circuit or vacuous context to discharge soundness
    - counting package assembly as FiniteModelLift, K0, or theorem completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: constructed lift/reflect operations for CircuitQuery, FiniteCircuitDatum, and CircuitDetectorCode with two-sided round trips, injectivity, matching, Holds, and evaluation graph laws, including arbitrary lifted target data through semantic configuration descent; directly reconstructed the lifted FiniteModel NoCycle equation system on every lifted ArchitectureObject and proved its EquationHolds equivalences; constructed the exact lifted cycle detector and proved Sound without caller evidence; assembled the complete lifted CoreReading and generated AATCorePackage with component and endpoint graph theorems; and exhibited cyclic/acyclic, accepted/rejected, matching/nonmatching, equation-failing/equation-holding witnesses. The generated package itself has a concrete accepted base circuit whose own circuit_sound theorem refutes its selected equation. Package-total hom rebasing, ambient strong-cartesian reflection, and the FiniteModelLift no-lift corollary remain intentionally unclaimed.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteEquationULift.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteCorePackageULift.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteEquationULiftWitnesses.lean
  evidence:
    - finiteModelLiftCircuitQuery
    - finiteModelReflectCircuitQuery_lift
    - finiteModelLiftCircuitQuery_holds_iff
    - finiteModelLiftFiniteCircuitDatum
    - finiteModelLiftFiniteCircuitDatum_matches_iff
    - finiteModelLiftCircuitDetectorCode_eval
    - finiteModelReflectCircuitDetectorCode_eval
    - finiteModelLiftEquationSystem
    - finiteModelLiftEquationHolds_iff_source
    - finiteModelLiftEquationCircuitReading
    - finiteModelLiftEquationCircuitReading_sound
    - finiteModelLiftCoreReading
    - finiteModelLiftCorePackage
    - finiteModelLiftCorePackage_object
    - finiteModelLiftCorePackage_base_circuit_nonempty
    - finiteModelLiftCorePackage_base_equationHolds_fails
    - finiteModelLiftAcyclicObject_equationHolds
    - finiteModelLiftEmptyQueryDatum_eval_false
  claim_mapping:
    fixed_goal_clauses:
      - target theorem B lines 216-220 requires the finite counterexample carrier to move through canonical ULift rather than an implicit universe-zero specialization
      - target artifacts lines 594-600 and material-premise ledger lines 738-740 retain FiniteModelLift before K0
      - completion criteria lines 638-653 require generated provenance, proof use, nonvacuity, and standard-axiom audit
    source_facts:
      - finite circuit queries, data, and recursive detector code use the fixed Atom equivalence and preserve Holds, Matches, and Bool evaluation in both generated directions
      - every lifted target object is read only through finiteModelSemanticDescent of its actual configuration; no opaque Type-u StructureMaps or SelectedQuantities are lowered
      - the lifted equation residual is the ULift of FiniteModel.noCycleResidual on that descent and therefore quantifies all lifted objects
      - detector soundness extracts all three concrete dependency edges from an accepted matching datum and contradicts the same descended NoCycle equation
      - CoreReading and AATCorePackage are generated from the Cycle 13 components plus the new equation reading, not supplied as fields or theorem inputs
      - the package base circuit is built from the canonical cycle datum and passed through ObjectAlgebra.circuit_sound
    consequence:
      - the canonical finite-model package now exists at every target universe with an exact, sound, nonvacuous equation/circuit layer
      - the cyclic source behavior and an acyclic negative control both survive the same uniform construction
      - no package-total morphism transport or strong-cartesian preservation/reflection follows merely from this object-level assembly
audits:
  premise_delta:
    discharged:
      - cross-carrier circuit query, finite datum, and detector-code rebase/reflection laws
      - direct lifted NoCycle equation semantics on every lifted ArchitectureObject
      - exact detector evaluation and soundness against the same lifted equation
      - complete lifted FiniteModel CoreReading and generated AATCorePackage
      - cyclic/acyclic, accepted/rejected, matching/nonmatching, equation-failure/equation-holding witnesses
      - generated-package base circuit nonemptiness and package-level circuit soundness use
    remaining:
      - package-total hom rebasing between canonical image packages with endpoint and composition graph laws
      - the exact generated data-level reflection surface needed by ambient strong-cartesian universality
      - FiniteModelLift as a structurally generated nonexistence corollary
      - all K0 and K2-K4 obligations
  certificate_provenance:
    discharged:
      - all rebase and reflection functions close over the fixed carrier equivalence and source syntax
      - the equation system, circuit reading, CoreReading, package, and witnesses are named generated definitions
      - matching, evaluation, soundness, equation truth, and circuit inhabitants are proved rather than accepted
    prohibited:
      - a generic cross-carrier EquationReading equivalence over all contexts
      - lowering arbitrary lifted object fields or choosing default/preimage objects
      - caller-supplied Matches, Sound, EquationHolds, package image, lift, or reflection certificates
  proof_use:
    used:
      - query round trips in datum cancellation, datum reflection on arbitrary lifted inputs, and datum injectivity in exact-detector evaluation
      - recursive detector structure and exact-pattern equality
      - every relation edge of the concrete three-edge cycle
      - semantic descent and the FiniteModel NoCycle residual/equation facts
      - every generated CoreReading field in package assembly and the package object projection in the concrete base witness
      - the generated package's actual Circuit value and ObjectAlgebra.circuit_sound
    standalone_outputs:
      - query and detector-code injectivity and the remaining CoreReading/AATCorePackage projection graph theorems are exported APIs rather than downstream-consumed premises in this cycle
    unavailable:
      - package-total hom and ambient strong-cartesian reflection data are not yet constructed
  structure_field_escape: none; no new structure accepts a circuit result, soundness proof, equation truth value, package morphism, cartesian lift, reflection, or conclusion certificate
  route_integrity: partial and exact; the cycle extends the canonical carrier/data route through a complete package while preserving the boundary between configuration-observable finite semantics and arbitrary high-universe object fields
  target_fitting: none introduced; the reviewed FiniteModel cycle and acyclic control are mapped into the same lifted carrier and tested by the same syntax/equation construction, while the generated package base is the cyclic object and the acyclic object remains an object-level negative control; the detector evaluator also retains a distinct false case
  vacuity: the lifted cycle datum matches and evaluates true, yields an actual Circuit and equation failure; the lifted acyclic object satisfies the same equation, rejects the cycle match, differs from the cyclic object, and the empty datum evaluates false
  one_way_as_equivalence: avoided; query/data/code syntax has explicit lift/reflect cancellation, while architecture objects and complete packages remain one-way generated constructions with no essential-surjectivity claim
  goal_or_report_reinterpretation: none; FiniteModelLift remains an unconditional fixed-ledger residual and this cycle supplies its complete object-level package endpoint only
  validation_refs:
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/FiniteEquationULift.lean: pass, namespace audit 35 declarations and standard axioms only
    - targeted single-module build ResearchLean.AG.DoctrineFiberProduct.FiniteCorePackageULift: pass, namespace audit 16 declarations and standard axioms only; no Research aggregate build
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/FiniteEquationULiftWitnesses.lean: pass, namespace audit 17 declarations and standard axioms only
    - research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/FiniteEquationULiftWitnesses.lean: pass, namespace audit 17 declarations and standard axioms only
    - manifest, umbrella, placeholder, hidden/BiDi Unicode, privacy, import-direction, wiring, and git diff scans: pass
    - fixed content head PR CI: 7/7 success
    - repaired report-only head PR CI: 7/7 success
  review_refs:
    fixed_head: 9be31e20e9ff7cb9fb77295ce2519d5afad76296
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4050#issuecomment-5369927331
    verdicts:
      - Math A: No major findings after report-only repair
      - Math B: No major findings after report-only repair
      - Lean A: No major findings
      - Lean B: No major findings
  initial_review_findings:
    - Math A Minor: selection.unchecked was empty while fixed-head review and integration references were still pending; retain final synchronization explicitly until it is complete
    - Math B Minor: separated terminal projection/injectivity APIs from proof-used dependencies and clarified that the generated package base is cyclic while the acyclic witness is an object-level control under the same equation
  blocking_findings: []
  stop_condition: none; continue before K0 without weakening the fixed FiniteModelLift obligation
  next_obligation: construct canonical package-total hom rebasing and the generated reflection operation on strong-cartesian lifts, with endpoint, graph, identity, and composition laws sufficient to derive FiniteModelLift without empty elimination
```

### Cycle 13 — canonical finite-package ULift foundation

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 13
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 037f343c2972ca342c3b360de12960f7367289f9
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 12 merged / Cycle 13 selection comment 5369081592
  proof_dag_predecessors:
    - Cycle 7 finite presentation and checker ULift rebase, PR 4043 merge 9400096d8a55f12ea6e18ee5f64bf7d73c650bf2
    - Cycle 9 arbitrary-target strong cartesian lifts and GlobalCartesianLift, PR 4045 merge 75627b6825fb0b715e4fab29fe3a7f3e0f159b79
    - Cycle 12 FiniteModelLift nonvacuity guard, PR 4048 merge 037f343c2972ca342c3b360de12960f7367289f9
  proof_obligation: construct the first canonical, executable-on-data layer of the finite package universe lift without assuming arbitrary lifted objects, package morphisms, cartesian lifts, reflection certificates, or a no-lift conclusion
  selection_reason: finite-code rebasing alone does not transport package semantics; the exact family, configuration, hom, doctrine, reading-component, and graph laws must be fixed before equation/CoreReading/package assembly or strong-lift reflection can be audited
  expected_result_type: proof-checkpoint
  risks:
    - claiming a full equivalence of architecture objects or core packages from an Atom-carrier equivalence
    - lowering arbitrary Type-u object fields to universe zero
    - using a caller-supplied image/descent certificate
    - treating finite-model-specific constant/configuration-only readings as generic reading transport
    - counting this foundation as FiniteModelLift, K0, or theorem completion
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: constructed canonical family and configuration lift/reflect operations with two-sided round trips, list-finiteness and family-support preservation; constructed configuration-hom lift/reflect by Atom-map conjugation with endpoint-normalized two-sided round trips and identity/composition laws; lifted arbitrary universe-zero architecture objects in one direction; rebased extraction doctrines and Atom axioms with extraction/atomization graphs; generated lifted composition and object readings with graph laws; directly reconstructed the FiniteModel-specific invariant, signature, and all-configuration-hom operation readings; added configuration-based semantic descent for every lifted architecture object; and exhibited positive, negative, nontrivial-identification, and nonidentity-hom finite witnesses. The construction intentionally stops before EquationReading, CoreReading, AATCorePackage, package homs, ambient cartesianness reflection, and FiniteModelLift.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FinitePackageULift.lean
    - ResearchLean/AG/DoctrineFiberProduct/FinitePackageULiftWitnesses.lean
  evidence:
    - finiteModelLiftAtomFamily
    - finiteModelReflectAtomFamily_lift
    - finiteModelLiftAtomConfiguration_reflect
    - finiteModelLiftConfigurationHom
    - finiteModelReflectConfigurationHom_lift
    - finiteModelLiftConfigurationHom_comp
    - finiteModelLiftExtractionDoctrine_extracts_iff
    - finiteModelLiftExtractionDoctrine_atomize
    - finiteModelLiftAtomAxiomSystem
    - finiteModelLiftCompositionReading_compose
    - finiteModelLiftObjectReading_object
    - finiteModelLiftInvariantFamily
    - finiteModelLiftArchitectureSignature
    - finiteModelLiftOperationReading
    - finiteModelSemanticDescent
    - finiteModelLiftCorePackage_componentA_mem
    - finiteModelLiftCorePackage_componentC_not_mem
    - finiteModelLiftCorePackage_componentA_identified_componentB
    - finiteModelLiftCollapseConfigurationHom_roundtrip
  claim_mapping:
    fixed_goal_clauses:
      - target theorem B lines 216-220 requires the finite counterexample carrier to move through canonical ULift rather than an implicit universe-zero specialization
      - target artifacts lines 594-600 and material-premise ledger lines 738-740 retain FiniteModelLift before K0
      - completion criteria lines 638-653 require generated provenance, proof use, nonvacuity, and standard-axiom audit
    source_facts:
      - finiteModelLiftCarrierEquiv supplies the fixed five-coordinate and Atom equivalences already used by finite presentation rebasing
      - every Atom-dependent family/configuration field is transported by that equivalence and reflected by its inverse
      - configuration homs are conjugated rather than copied or accepted as fields, and the conjugation is proved functorial
      - extraction doctrine carriers are raised through ULift and all four extraction conjuncts are preserved on corresponding cells
      - the FiniteModel invariant/signature/operation readings are reconstructed only from their reviewed singleton, constant, and all-configuration-hom definitions
      - semantic descent reads every lifted object's actual reflected configuration and does not pretend to lower its opaque Type-u fields
    consequence:
      - finite package transport now has a checked carrier/data foundation and concrete nondegenerate witnesses
      - no equivalence of all lifted architecture objects, core packages, or package homs follows
      - no strong-cartesian reflection or no-lift transport is claimed at this checkpoint
audits:
  premise_delta:
    discharged:
      - Atom-family and Atom-configuration universe rebase and reflection
      - configuration-hom rebase/reflection graph, round-trip, identity, and composition laws
      - extraction doctrine, atomization, Atom-axiom, composition-reading, and object-reading foundation
      - FiniteModel-specific invariant, signature, operation, and semantic-configuration readings
      - positive/negative family content, nontrivial identification, and nonidentity hom witnesses
    remaining:
      - cross-carrier circuit syntax and a sound lifted FiniteModel EquationReading on every lifted object
      - complete lifted FiniteModel CoreReading and AATCorePackage with projection/endpoint graph laws
      - package-total hom rebasing and the exact reflection surface needed by ambient strong-cartesian universality
      - FiniteModelLift as a structurally generated nonexistence corollary
      - all K0 and K2-K4 obligations
  certificate_provenance:
    discharged:
      - every constructor closes over source family/configuration/doctrine/reading data and finiteModelLiftCarrierEquiv
      - configuration-hom round trips normalize only generated endpoint equalities through castConfigurationHom
      - no image membership, descent datum, package morphism, lift, condition result, or no-lift proof is accepted
    prohibited:
      - an arbitrary lifted ArchitectureObject inverse or all-package equivalence
      - default/PEmpty extension presented as ambient strong-cartesian reflection
      - a caller-supplied package image or high-hom restriction certificate
  proof_use:
    used:
      - both directions and cancellation laws of the fixed Atom equivalence
      - every family/configuration relation and identification field
      - every configuration-hom map and preservation law
      - all four extraction predicates, normalization, source values, and the source AtomAxiomSystem
      - the source composition and object constructors and their laws
      - concrete FiniteModel family membership, nonmembership, identification, and collapse-hom data
    unavailable:
      - EquationReading and package-total universal-property data do not yet exist at the lifted carrier
  structure_field_escape: none; this cycle introduces named functions and theorems, not a structure carrying a package, hom, lift, reflection, or conclusion certificate
  route_integrity: partial and exact; the construction uses the existing canonical carrier equivalence and finite model definitions, while explicitly stopping before the ambient package category where arbitrary high-universe objects and homs must be handled
  target_fitting: none introduced; the only fixture is the pre-existing reviewed FiniteModel required by the fixed GOAL, and positive/negative facts survive one uniform construction
  vacuity: concrete lifted membership and nonmembership coexist, a nontrivial identification survives, and the lifted collapse hom has a visible constant Atom map whose reflection returns the original hom
  one_way_as_equivalence: avoided; architecture-object lifting and semantic descent are stated separately, and no inverse or essential-surjectivity theorem is claimed for arbitrary lifted object fields
  goal_or_report_reinterpretation: none; FiniteModelLift remains an unconditional fixed-ledger residual and this cycle is only its first structural prerequisite
  validation_refs:
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/FinitePackageULift.lean: pass, namespace audit 45 declarations and standard axioms only
    - targeted single-module build ResearchLean.AG.DoctrineFiberProduct.FinitePackageULiftWitnesses: pass; no Research aggregate build
    - research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/FinitePackageULiftWitnesses.lean: pass, namespace audit 7 declarations and standard axioms only
    - module manifest and DoctrineFiberProduct umbrella imports updated
    - report diff, placeholder, hidden/BiDi Unicode, privacy, import-direction, and wiring scans: pass
    - fixed-head PR CI: 7/7 success
  review_refs:
    fixed_head: 9349fe0dad632f500a429071035aedd2f5006d0c
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4049#issuecomment-5369521004
    verdicts:
      - Math A: No major findings
      - Math B: No major findings
      - Lean A: No major findings
      - Lean B: No major findings
  initial_review_findings:
    - all four lanes Minor: corrected the finite witness ledger from relation to the distinct identification field and added the exact theorem to evidence
    - Math A Minor: narrowed the ArchitectureObject docstring to disclaim only a full-field inverse or equivalence, preserving the configuration-only semantic descent claim
    - Math A final-sync Minor: closed the previously pending scan, review, integrated-comment, and CI references before leaving selection.unchecked empty
  blocking_findings: []
  stop_condition: none; continue before K0 without weakening the fixed FiniteModelLift obligation
  next_obligation: construct the direct lifted FiniteModel equation/circuit reading and complete CoreReading/package assembly with endpoint graph laws; then reassess the exact ambient package-hom reflection boundary
```

### Cycle 12 — `FiniteModelLift` nonvacuity guard and structural-route checkpoint

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 12
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: a02e0a57ab73aafc412fdd81fb1ad95e5c002e60
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 11 merged / Cycle 12 fixed-contract audit comment 5368825849
  proof_dag_predecessors:
    - Cycle 7 finite presentation and checker ULift rebase, PR 4043 merge 9400096d8a55f12ea6e18ee5f64bf7d73c650bf2
    - Cycle 9 arbitrary-target strong cartesian lifts and GlobalCartesianLift, PR 4045 merge 75627b6825fb0b715e4fab29fe3a7f3e0f159b79
    - Cycle 11 carrier-global branch artifact and selected regime producer, PR 4047 merge a02e0a57ab73aafc412fdd81fb1ad95e5c002e60
  proof_obligation: construct and review canonical finite-package ULift reindexing and strong-lift reflection sufficient for the fixed FiniteModelLift obligation before K0; reject a direct empty-elimination implementation and distinguish a genuine data-level transport route from a fixed-contract defect
  selection_reason: FiniteModelLift is the last fixed-ledger F0 residual after the actual global left branch was selected, so its direct no-lift function type is empty-domain and requires an explicit nonvacuous structural surface before it can count
  expected_result_type: proof-checkpoint
  risks:
    - inhabiting FiniteModelLift by eliminating the now-empty finite no-lift domain
    - counting finite presentation rebasing as package-level strong-lift reflection
    - accepting caller-supplied descent data or a counterexample-specific equivalence as provenance
    - declaring a terminal goal defect before excluding a richer canonical image-relative rebase and reflection theorem
    - continuing to K0 with an undisposed F0 residual
  unchecked: []
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: proved cartesianLiftNonexistence_isEmpty from the generated GlobalCartesianLift for every carrier, realized bottom arrow, and endpoint package; rightBranch_isEmpty already instantiates the same contradiction at FiniteModel.carrier. This proves that a direct FiniteModelLift function can be inhabited by empty elimination and therefore cannot count without separately generated package reindexing, data-level strong-lift reflection, and checkable graph laws. It does not rule out constructing those richer operations on canonical image packages and exercising the reflection on actual lifted strong lifts, whose type is inhabited under the global branch. The terminal goal-defect inference proposed at the initial head was therefore rejected; the structural transport route remains the next fixed-ledger obligation.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianBranch.lean
  existing_evidence:
    - GlobalCartesianLift
    - globalCartesianLift
    - CartesianLiftNonexistence
    - cartesianLiftNonexistence_isEmpty
    - RightBranch
    - rightBranch_isEmpty
    - DisjunctionArtifact
    - globalDisjunctionArtifact
  claim_mapping:
    fixed_goal_clauses:
      - target theorem (B) lines 196-220 chooses one carrier-global left-or-right branch and introduces FiniteModelLift as transport of the right branch finite counterexample
      - target artifacts lines 594-600 and material-premise ledger lines 738-740 require FiniteModelLift before K0
      - completion criteria lines 638-653 require every discharge-required ledger item together with provenance and proof-use review
    source_facts:
      - globalCartesianLift realizes the global left branch at every carrier, realized input, and target-fiber package
      - CartesianLiftNonexistence stores exactly an input, target package, and denial of that same lift existence
      - cartesianLiftNonexistence_isEmpty proves in Lean that these two facts make the no-lift witness type empty at every carrier and universe
      - rightBranch_isEmpty applies the generated global lift to a hypothetical finite counterexample and closes the contradiction
      - FiniteCodeULift explicitly stops before package-level reindexing and nonexistence transfer
    consequence:
      - no finite no-lift witness remains on which a bare no-lift corollary can fire
      - empty elimination can inhabit the nominal function type but cannot establish the fixed ULift provenance or proof-use requirements
      - a richer branch-independent image-package rebase and data-level reflection may still be nonvacuous on actual lifted strong lifts and has not been refuted
audits:
  premise_delta:
    discharged:
      - source-level incompatibility between the selected global branch and an inhabited CartesianLiftNonexistence
      - direct empty-elimination FiniteModelLift is exposed as an inadmissible vacuous route
    remaining:
      - canonical rebase of the concrete finite input and selected target package into the lifted carrier
      - data-level reflection from every strong lift over those generated endpoints to a base strong lift, with generated graph and endpoint laws
      - FiniteModelLift as the no-lift corollary of those named structural operations
      - all K0 and K2-K4 obligations, which cannot begin before this F0 residual is disposed
  certificate_provenance:
    discharged:
      - the emptiness argument uses the named generated globalCartesianLift and the exact input/package stored by CartesianLiftNonexistence
      - no hypothetical package rebase, descent datum, or reflection certificate is accepted
    prohibited:
      - False.elim or IsEmpty elimination presented as finite counterexample universe transport
      - a caller-supplied image/descent witness for an arbitrary lifted package
      - a counterexample-specific equivalence between already-empty strong-lift types
  proof_use:
    used:
      - the full carrier/input/package quantifiers of globalCartesianLift
      - CartesianLiftNonexistence.input, targetPackage, and no_lift
      - the fixed target-artifact, completion, ledger, and failure-policy clauses
    unavailable:
      - there is no inhabitant of CartesianLiftNonexistence FiniteModel.carrier after globalCartesianLift, so the final no-lift corollary cannot itself demonstrate nonvacuity
  structure_field_escape: an ex-falso FiniteModelLift would pass type checking while using none of the required universe-rebase structure, so it is explicitly rejected rather than added
  route_integrity: pending; presentation-only ULift rebase does not imply package transport, while a canonical image-relative package rebase and reflection with graph laws remains an admissible route to test
  target_fitting: none introduced; no new condition, fixture, package, or certificate was selected
  vacuity: the nominal base counterexample domain is empty; a bare FiniteModelLift value is vacuous, but a richer reflection theorem can be tested on actual lifted strong lifts and is not excluded by this theorem
  one_way_as_equivalence: avoided; no full cross-universe package equivalence is claimed
  goal_or_report_reinterpretation: initial terminal goal-defect inference rejected by Math B review; the report retains FiniteModelLift as an unconditional residual and resumes the structural route
  validation_refs:
    - existing focused and CI evidence for globalCartesianLift and rightBranch_isEmpty remains accepted from Cycles 9 and 11
    - research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/CartesianBranch.lean: pass, namespace audit 47 declarations and standard axioms only
    - Cycle 12 changes no GOAL, umbrella, or manifest
    - report diff, placeholder, hidden/BiDi Unicode, privacy, import-direction, and wiring scans: pass
    - fixed-head PR CI: 7/7 success
  review_refs:
    fixed_head: 0ab1bb9611b9bc1f53887be47b446bd2702dfb3c
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4048#issuecomment-5369044812
    verdicts:
      - Math A: No major findings
      - Math B: No major findings
      - Lean A: No major findings
      - Lean B: No major findings
  initial_review_findings:
    - Math B Major: cartesianLiftNonexistence_isEmpty does not exclude a richer canonical image-package rebase and data-level reflection whose proof-use is testable on inhabited lifted strong lifts; terminal goal-defect withdrawn
    - Math A Minor: narrowed the report from impossibility of every structured implication to nonvacuity failure of the bare no-lift corollary
    - Lean B Minor: corrected the Cycle 7 predecessor merge SHA
  blocking_findings: []
  stop_condition: none; continue before K0 without weakening the fixed FiniteModelLift obligation
  next_obligation: construct the exact canonical image-relative finite package rebase and data-level strong-lift reflection with endpoint and graph laws, then derive and audit the FiniteModelLift corollary
```

### Cycle 11 — carrier-global branch artifact and regime producer

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 11
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: f23698403c32d7c4b1832e4597fb33742a76f6b4
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 10 merged / Cycle 11 selection comment 5368610427
  proof_dag_predecessors:
    - Cycle 6 qualified right-regime and per-carrier CartesianRegime signatures, PR 4042 merge 487bee332fbd426cb70ffe926b4c0201ab569a60
    - Cycle 9 universe-polymorphic GlobalCartesianLift, PR 4045 merge 75627b6825fb0b715e4fab29fe3a7f3e0f159b79
    - Cycle 10 branch-independent nondegenerate lift portfolio, PR 4046 merge f23698403c32d7c4b1832e4597fb33742a76f6b4
  proof_obligation: fix a carrier-uniform RightBranch theorem-output type, one universe-polymorphic DisjunctionArtifact with branch selection outside the carrier quantifier, the required cartesianRegimeOfDisjunction producer, and the actual selected regime generated from globalCartesianLift
  selection_reason: the left theorem and independent lift portfolio are now constructed, so later K0-K4 must receive one named regime from a single global artifact rather than an arbitrary caller-supplied CartesianRegime; the unselected right surface must still prevent carrier-by-carrier condition fitting without accepting finite-universe transport as a certificate field
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianBranch.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - replacing one global branch artifact by a per-carrier disjunction
    - letting each carrier choose an unrelated condition or semantic predicate
    - accepting an arbitrary CartesianRegime as the source of later lift data
    - storing a counterexample-specific package rebase, lift reflection, or FiniteModelLift certificate in RightBranch
    - using the contradiction from globalCartesianLift to claim the required canonical ULift transport
    - counting the artifact/producer as K0 or G-110 completion
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: fixed RightBranch with one universe-zero structural syntax template, exact equality to the base qualified condition term, canonical rebase equality for every carrier-level qualified condition, a nondegenerate same-condition positive family, and a finite condition-failing no-lift witness; proved the selected global theorem makes that conditional theorem-output type empty; defined the Type-valued carrier-global DisjunctionArtifact; defined cartesianRegimeOfDisjunction with artifact selection preceding the carrier quantifier; constructed globalDisjunctionArtifact from globalCartesianLift; generated selectedCartesianRegime only through that producer; and connected its membership and lift supply to the existing CartesianRegime eliminator
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianBranch.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - RightBranch
    - rightBranch_isEmpty
    - DisjunctionArtifact
    - cartesianRegimeOfDisjunction
    - globalDisjunctionArtifact
    - selectedCartesianRegime
    - selectedCartesianRegime_eq_global
    - selectedCartesianRegime_HCart
    - selectedCartesianRegime_hasStrongCartesianLift
  claim_mapping:
    theorem_names:
      - cartesianRegimeOfDisjunction
      - globalDisjunctionArtifact
      - selectedCartesianRegime
      - selectedCartesianRegime_hasStrongCartesianLift
    source_labels:
      - target theorem (B) carrier-global disjunction selection
      - target material premise CartesianRegime producer
      - target proof strategy F0c2b branch-output typing and K1 left-branch selection
    conjuncts:
      - the disjunction is one Type-valued artifact whose constructors carry complete carrier-global branch payloads
      - the producer receives that artifact before quantifying every carrier and decidable Atom equality instance
      - the selected artifact is generated from globalCartesianLift rather than supplied by a caller or finite counterexample
      - the selected per-carrier regime is generated only by cartesianRegimeOfDisjunction and supplies actual lifts through the reviewed regime eliminator
      - a hypothetical right branch uses one authored structural condition template, its exact base term, and canonical rebasing at every carrier; checker bridges determine the semantic predicate on all realized inputs
      - the right theorem-output type carries its own same-condition positive family and finite failing no-lift witness rather than an arbitrary condition alone
    undischarged_assumptions:
      - the fixed ledger's canonical package-level ULift reindexing, strong-lift reflection, and FiniteModelLift remain unresolved and are not replaced by ex-falso
      - K0 and K2-K4 remain unresolved
    acceptance_point: the single global artifact and named per-carrier regime producer are constructed from the proved left branch; canonical finite counterexample universe transport and all later layers remain uncounted
    port_status: unported
audits:
  premise_delta:
    discharged:
      - carrier-uniform conditional theorem-output signature
      - one carrier-global Type-valued disjunction artifact
      - cartesianRegimeOfDisjunction
      - selected global artifact and generated per-carrier regime
      - actual lift supply through the selected producer output
    remaining:
      - canonical package ULift reindexing and strong-lift reflection
      - FiniteModelLift
      - K0 and K2-K4
  certificate_provenance:
    discharged:
      - globalDisjunctionArtifact directly stores the named globalCartesianLift theorem
      - selectedCartesianRegime is definitionally cartesianRegimeOfDisjunction applied to that named artifact
      - selectedCartesianRegime_hasStrongCartesianLift consumes the selected regime through CartesianRegime.hasStrongCartesianLift
      - right-branch condition uniformity is constrained by term equality and rebaseCartCondition rather than a carrier-indexed choice of syntax
    unresolved:
      - no package-level universe rebase or lift-reflection result is accepted as a RightBranch field; those must be named constructions before FiniteModelLift can count
  proof_use:
    used:
      - RightBranch.finiteCounterexample.nonexistence and globalCartesianLift at the base carrier in rightBranch_isEmpty
      - each DisjunctionArtifact constructor payload in the two producer branches
      - globalCartesianLift in globalDisjunctionArtifact
      - globalDisjunctionArtifact in selectedCartesianRegime
      - selected producer membership in the ordinary regime lift eliminator
    unused:
      - RightBranch template and uniformity fields cannot have a runtime consumer because the proved global branch makes RightBranch empty; their statement-level role is to close the fixed conditional signature without creating a value or transporting a no-lift certificate
  structure_field_escape: none-found for the selected result; RightBranch packages the theorem outputs required only if the conditional branch were selected, while presentation fields remain unchanged and FiniteModelLift is deliberately not a field
  route_integrity: pass for the artifact/producer; branch selection occurs once before carrier quantification, the selected value comes from globalCartesianLift, and no contradiction is repackaged as ULift provenance
  target_fitting: rebaseCartCondition fixes every right-regime syntax from one base template and each QualifiedCartCondition bridge fixes its semantic extension on the realization image; the actual selected branch has no condition choice
  vacuity: the actual global artifact supplies lifts for all realized inputs; rightBranch_isEmpty explicitly records why no positive RightBranch instance can coexist with the proved global theorem rather than supplying a fake right value
  one_way_as_equivalence: none-found; no package or source-map equivalence is introduced in this layer
  goal_or_report_reinterpretation: none for F0c2b1; FiniteModelLift remains a separate literal fixed-ledger residual and is not made branch-conditional by this report
  validation_refs:
    - research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/CartesianBranch.lean: pass, namespace audit 46 declarations and standard axioms only
    - lake build ResearchLean.AG.DoctrineFiberProduct.CartesianBranch: pass targeted module check
    - lake env lean ResearchLean/AG/DoctrineFiberProduct.lean: pass
    - git diff, placeholder, hidden/BiDi Unicode, privacy, import-direction, manifest, and wiring scans: pass
    - fixed-head PR CI: 7/7 success
  review_refs:
    fixed_head: f64cc3630107891ae79804ca8813eeec912f9abd
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4047#issuecomment-5368786784
    verdicts:
      - Math A: No major findings
      - Math B: No major findings
      - Lean A: No major findings
      - Lean B: No major findings
  initial_review_findings: []
  blocking_findings: []
  next_obligation: construct and review canonical finite-package ULift reindexing and strong-lift reflection sufficient for the fixed FiniteModelLift obligation before selecting K0
```

### Cycle 11 acceptance spine

Cycle 11 の直接 axiom audit は上記 `evidence` 9 declaration と current module
全 46 declaration に固定する。`globalDisjunctionArtifact` と
`cartesianRegimeOfDisjunction` は固定 GOAL の branch artifact / producer を
inhabit するが、`FiniteModelLift`、K0、K2–K4、G-110 completion を達成したとは
数えない。

### Cycle 10 — nondegenerate parametric cartesian lift portfolio

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 10
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 75627b6825fb0b715e4fab29fe3a7f3e0f159b79
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 10 selection comment 5368313496
  proof_dag_predecessors:
    - Cycle 2 finite cartesian presentations and realization provenance, PR 4038 merge 5dd7bbb297c50498e6cff706258a5237381df9d4
    - Cycle 6 branch-independent nondegenerate lift-family signature, PR 4042 merge 487bee332fbd426cb70ffe926b4c0201ab569a60
    - Cycle 9 arbitrary-target strong cartesian lifts and GlobalCartesianLift, PR 4045 merge 75627b6825fb0b715e4fab29fe3a7f3e0f159b79
  proof_obligation: construct one branch-independent ParametricCartLiftFamily with at least two pairwise nonisomorphic realized semantic arrows, nonisomorphic endpoints, noninvertible bottom morphisms, concrete target-fiber packages, and actual strong cartesian lifts for those same members
  selection_reason: the left branch is now proved uniformly, but the fixed portfolio constraint separately requires a finite nondegenerate family; constant maps from two- and three-cell selective doctrines to one shared one-cell target expose source-cardinality obstructions while Cycle 9 generates their lifts to one concrete package
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianTargetWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - using identity arrows or two isomorphic copies of one semantic arrow
    - proving only inequality of presentations rather than nonexistence of CartSemanticInputIso
    - selecting an empty target fiber or an unrelated family of lift witnesses
    - supplying a package, lift, or cartesianness certificate as a theorem premise or finite-presentation field
    - counting the portfolio as the still-missing carrier-global disjunction artifact or regime producer
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: constructed identity-normalized selective finite doctrines with one, two, and three source cells; validated constant two-to-one and three-to-one exact presentations; generated a concrete package in the shared one-cell target fiber through reviewed package transport and the Cycle 9 arbitrary-target producer; constructed actual strong cartesian lifts of both family members to that package; proved both source tables noninjective, both semantic arrows noninvertible, each source endpoint nonisomorphic to the common target, and the two semantic arrows pairwise nonisomorphic in both orientations; and assembled the Bool-indexed ParametricCartLiftFamily
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianTargetWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - finiteSelectiveDoctrineCode
    - finiteSelectiveTwoToOnePresentation
    - finiteSelectiveThreeToOnePresentation
    - finiteSelectiveTwoInput
    - finiteSelectiveThreeInput
    - finitePortfolioSupportPackage
    - finitePortfolioSupportPackage_point
    - finiteSelectiveOneToSupportPresentation
    - finiteSelectiveOneSupportLift
    - finiteSelectiveOneTargetPackage
    - finiteSelectiveTwoSourceMap_not_injective
    - finiteSelectiveThreeSourceMap_not_injective
    - finiteSelectiveTwoInput_not_isIso
    - finiteSelectiveThreeInput_not_isIso
    - extractionInstanceSourceEquiv
    - finiteSelectiveTwoEndpoints_not_isomorphic
    - finiteSelectiveThreeEndpoints_not_isomorphic
    - finiteSelectiveTwoThreeInputs_not_isomorphic
    - finiteSelectiveThreeTwoInputs_not_isomorphic
    - finiteSelectiveTwoLift
    - finiteSelectiveThreeLift
    - finiteParametricCartLiftFamily
  claim_mapping:
    theorem_names:
      - finiteSelectiveTwoInput_not_isIso
      - finiteSelectiveThreeInput_not_isIso
      - finiteSelectiveTwoThreeInputs_not_isomorphic
      - finiteSelectiveTwoLift
      - finiteSelectiveThreeLift
      - finiteParametricCartLiftFamily
    source_labels:
      - target theorem (B) branch-independent lift-construction positive family
      - target portfolio constraint
      - target proof strategy K1 finite nondegeneracy witness
    conjuncts:
      - Bool supplies two distinguished unequal parameters
      - the members are realized finite presentations rather than arbitrary semantic arrows
      - source-cardinality two versus three rules out semantic arrow isomorphism
      - source-cardinality two or three versus one rules out endpoint isomorphism
      - each constant source table identifies two explicit distinct cells, hence its decoded bottom morphism cannot be an isomorphism
      - each exact same member has a concrete target-fiber package and an actual StrongCartesianLift generated by strongCartesianLiftOfTarget
    undischarged_assumptions:
      - the single DisjunctionArtifact and cartesianRegimeOfDisjunction remain unresolved
      - K0 and K2-K4 remain unresolved
    acceptance_point: the fixed branch-independent portfolio obligation is inhabited nonvacuously; no final branch artifact, generated regime, or G-110 completion is counted
    port_status: unported
audits:
  premise_delta:
    discharged:
      - concrete nonempty common target fiber
      - two pairwise nonisomorphic noninvertible realized arrows with nonisomorphic endpoints
      - actual strong cartesian lifts for the same two portfolio members
    remaining:
      - single carrier-global disjunction artifact and named regime producer
      - K0 and K2-K4
  certificate_provenance:
    discharged:
      - the support package is computed by transportAlong from FiniteModel.corePackage and finiteModelDoctrineFromFixture
      - the package in the one-cell target fiber is the generated domainObject of strongCartesianLiftOfTarget on an explicit realized bridge
      - both portfolio lifts are direct applications of strongCartesianLiftOfTarget to the two named semantic inputs and that generated target package
      - no lift, package recovery equality, isomorphism certificate, or cartesianness proof occurs in either finite presentation or as a theorem premise
    unresolved:
      - named source of the eventual carrier-global disjunction and regime
  proof_use:
    used:
      - finiteModelDoctrineFromFixture and the selected finite-code point in concrete package construction
      - finitePortfolioSupportPackage_point in the bridge target CoreFiber
      - StrongCartesianLift.domainObject in construction of the shared one-cell target package
      - explicit unequal source cells and extInstHom_sourceMap_injective_of_isIso in both noninvertibility proofs
      - source equivalences induced by actual ExtInst isomorphisms and Fintype.card_congr in all endpoint and arrow-isomorphism contradictions
      - all nondegeneracy and lift declarations in the final ParametricCartLiftFamily fields
    unused: []
  structure_field_escape: none-found; the finite presentations retain the reviewed four authored fields, while packages and lifts are downstream named constructions
  route_integrity: pass; the fixture cardinalities and common target route were fixed in the Issue selection before implementation, and every lift is generated through the reviewed arbitrary-target theorem
  target_fitting: the family is a fixed Bool-indexed finite witness with source cardinalities two and three over one named selective target; it does not inspect a checker result or select representatives after proving a conclusion
  vacuity: pass; the target CoreFiber is explicitly inhabited, both arrows are noninvertible, endpoints are nonisomorphic, and the two members are not isomorphic as semantic arrows
  one_way_as_equivalence: none-found; no lower source-map inverse is constructed, and the only equivalences used are consequences of hypothetical categorical isomorphisms inside contradiction proofs
  goal_or_report_reinterpretation: none; this cycle discharges only the branch-independent portfolio and explicitly retains the artifact, regime producer, K0, and K2-K4
  validation_refs:
    - research/lean/check_research_modules.sh --focused ResearchLean/AG/DoctrineFiberProduct/CartesianTargetWitnesses.lean: pass, namespace audit 34 declarations and standard axioms only
    - lake build ResearchLean.AG.DoctrineFiberProduct.CartesianTargetWitnesses: pass targeted module check
    - lake env lean ResearchLean/AG/DoctrineFiberProduct.lean: pass
    - git diff, placeholder, hidden/BiDi Unicode, privacy, import-direction, and wiring scans: pass
    - fixed-head PR CI: 7 of 7 checks green
  review_refs:
    fixed_head: 6395554af125edae2b8a9e802c1412c7d5518f49
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4046#issuecomment-5368573694
    verdicts:
      - Math A: no major findings for the Cycle 10 portfolio obligation only
      - Math B: no major findings for the Cycle 10 portfolio obligation only
      - Lean A: no major findings for the Cycle 10 portfolio obligation only
      - Lean B: no major findings for the Cycle 10 portfolio obligation only
  initial_review_findings:
    - all four initial lanes found the center portfolio claim intact but identified that CartesianTargetWitnesses was absent from research-modules.txt, so the official focused wrapper rejected the file and the initial wiring-pass claim was false; the module is now registered and the official single-file focused check passes
  blocking_findings: []
  next_obligation: fix the single carrier-global DisjunctionArtifact and cartesianRegimeOfDisjunction from globalCartesianLift before selecting K0
```

### Cycle 10 acceptance spine

Cycle 10 の直接 axiom audit は、上記 `evidence` 22 declaration と witness module
全 34 declaration に固定する。`finiteParametricCartLiftFamily` は固定 GOAL の
枝非依存 portfolio を inhabit するが、単一 `DisjunctionArtifact`、
`cartesianRegimeOfDisjunction`、K0、K2–K4 を達成したとは数えない。

### Cycle 9 — arbitrary-target strong cartesian lifts and the global left branch

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 9
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 9f144dfd3e4a04f2af76b3cb086aa0aa078f3b49
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 9 selection comment 5367593191
  proof_dag_predecessors:
    - Cycle 6 F0c1 strong-lift and regime signatures, PR 4042 merge 487bee332fbd426cb70ffe926b4c0201ab569a60
    - Cycle 7 canonical finite-code universe reindexing, PR 4043 merge 9400096d8a55f12ea6e18ee5f64bf7d73c650bf2
    - Cycle 8 canonical package transport strong-cartesianness, PR 4044 merge 9f144dfd3e4a04f2af76b3cb086aa0aa078f3b49
  proof_obligation: inverse-reindex every primitive field of an arbitrary target package along the input pointed exact morphism, generate mutually inverse upper morphisms, and construct a strong cartesian lift ending at that exact target package for every carrier and realization input
  selection_reason: the pointed input already supplies the selected-source equation while exactness supplies an Atom equivalence, so the target reading can be inverse-conjugated without assuming an inverse lower source map; Cycle 8 supplied the reviewed universal-property pattern, while this cycle independently generalizes that argument rather than proof-term-calling the canonical transport theorem
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianTarget.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - replacing the pointed ExtInstHom by a bare doctrine morphism without a selected-source preimage
    - assuming the lower source map or the semantic bottom arrow is invertible
    - accepting a preimage package, upper inverse, cancellation law, or strong-cartesian certificate from the caller
    - proving only a canonical transport codomain theorem rather than ending at every target-fiber package
    - hiding dependent equation or operation round trips behind an equality field
    - counting the global existence theorem alone as the required nondegenerate parametric portfolio or final disjunction artifact
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: proved inverse/forward round trips for composition, object, invariant, signature, and operation readings; generated a list-finite inverse selected family and inverse base object; constructed the complete inverse CoreReading and package; generated backward and forward SignedExactCoreReadingHom values including dependent equation and operation transports; proved both hom-level cancellation laws; proved a generic upper-inverse strong-cartesian criterion; aligned an arbitrary target-fiber endpoint by IsHomLift rather than definitional equality; constructed the requested StrongCartesianLift; and inhabited the universe-polymorphic GlobalCartesianLift left branch
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianTarget.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - transportCompositionReading_symm_roundtrip
    - transportObjectReading_symm_roundtrip
    - transportInvariant_symm_roundtrip
    - transportInvariantFamily_symm_roundtrip
    - transportArchitectureSignature_symm_roundtrip
    - transportOperationReading_symm_roundtrip
    - inverseFamilyListFinite
    - inverseBaseObject
    - inverseBaseObject_eq
    - inverseCoreReading
    - inverseCorePackage
    - inverseCorePackage_point
    - inverseCorePackageBackwardUpper
    - inverseCoreEquationForward
    - inverseCoreEquationForward_equationMap_heq
    - inverseCoreEquationForward_detectorCode
    - inverseCorePackageForwardUpper
    - inverseCorePackageBackward_comp_forward
    - inverseCorePackageForward_comp_backward
    - inverseCorePackageHom
    - packageTotalHom_isStronglyCartesian_of_upper_inverse
    - packageTotalHom_isStronglyCartesian_of_upper_inverse_lift
    - inverseCorePackageHom_isStronglyCartesian
    - strongCartesianLiftOfTarget
    - globalCartesianLift
  claim_mapping:
    theorem_names:
      - inverseCorePackageBackward_comp_forward
      - inverseCorePackageForward_comp_backward
      - inverseCorePackageHom_isStronglyCartesian
      - strongCartesianLiftOfTarget
      - globalCartesianLift
    source_labels:
      - target theorem (B) global-left branch
      - target material premise CartesianRegime producer precursor
      - target proof strategy K1 cartesian-lift branch construction
    conjuncts:
      - every realization input and every package in its semantic target fiber receives an actual StrongCartesianLift
      - the inverse package is generated from the input source endpoint, target package, pointed source equality, and Atom equivalence
      - dependent equation and operation transports are constructed and cancelled rather than supplied as comparisons
      - both upper inverse laws are proved and consumed in factorization and uniqueness
      - the carrier quantifier is outside branch selection through one GlobalCartesianLift inhabitant
    undischarged_assumptions:
      - the branch-independent ParametricCartLiftFamily on pairwise nonisomorphic noninvertible realized arrows remains unresolved
      - RightBranch, the single DisjunctionArtifact, and cartesianRegimeOfDisjunction remain unresolved even though the global constructor is now available
      - K0 and K2-K4 remain unresolved
    acceptance_point: the fixed global-left existence branch is proved for every realization input and arbitrary target-fiber package; the portfolio and exported branch artifact/regime are not counted
    port_status: unported
audits:
  premise_delta:
    discharged:
      - arbitrary target-package inverse reindexing
      - generated forward and backward upper maps with two-sided cancellation
      - endpoint-aligned arbitrary-target strong cartesian lift
      - GlobalCartesianLift
    remaining:
      - nondegenerate parametric lift family
      - single disjunction artifact and named regime producer
      - K0 and K2-K4
  certificate_provenance:
    discharged:
      - every inverse reading and package field is computed from the target package and pointed bottom morphism
      - both upper maps and cancellation laws are named generated declarations
      - the generic upper-inverse criteria accept an inverse and two laws conditionally, while inverseCorePackageHom_isStronglyCartesian and strongCartesianLiftOfTarget instantiate those premises with the named generated maps and cancellation theorems
      - the IsHomLift endpoint alignment is derived from targetPackage.2 and inverseCorePackage_point
      - the global theorem calls strongCartesianLiftOfTarget rather than accepting a lift or certificate
    unresolved:
      - branch artifact and regime producer
      - explicit branch-independent nondegenerate family
  proof_use:
    used:
      - source_eq and atomize_naturality to recover the selected finite source family
      - the public composition and object roundtrip theorems in the generated upper cancellation proofs
      - dependent equation-index, detector, context, observable-ring, and operation endpoint equalities in the upper maps and cancellations
      - both upper inverse laws in the strong-cartesian factorization and uniqueness proof
      - targetPackage.2 in the exact endpoint IsHomLift instance
    unused:
      - transportInvariantFamily_symm_roundtrip, transportArchitectureSignature_symm_roundtrip, and transportOperationReading_symm_roundtrip are standalone coverage API rather than named dependencies of the final global proof; operation cancellation instead uses the private endpoint-level HEq theorem, while invariant and signature components close by extensionality
      - inverseCoreEquationForward_equationMap_heq and inverseCorePackageHom_isStronglyCartesian are standalone consequences not called by strongCartesianLiftOfTarget
      - Cycle 8 transportAlongHom_isStronglyCartesian is a reviewed conceptual predecessor, not a direct proof-term dependency of the independently generalized upper-inverse criterion
  structure_field_escape: none-found; the generic criterion explicitly takes upper inverse data as theorem premises, but the final arbitrary-target and global constructors discharge them with named generated declarations rather than presentation fields or caller inputs
  route_integrity: pass; the route uses pointed source_eq and the upper Atom equivalence only, never an inverse lower source map, supplied vertical iso, or supplied target recovery equality; Cycle 8 is a conceptual predecessor rather than a direct theorem call
  target_fitting: the central construction quantifies every AtomCarrier, CartSemanticInput, and target CoreFiber package; the public left branch then restricts to the fixed RealizableHom domain
  vacuity: the theorem is universal rather than fixture-selected and assumes neither IsIso nor injectivity of the lower source map; the separate nonisomorphic noninvertible family required by the portfolio constraint remains explicitly undischarged
  one_way_as_equivalence: none-found; only the upper SignedExactCoreReadingHom is inverted, with two proved cancellation laws, while the lower source map remains directional
  goal_or_report_reinterpretation: none; this cycle proves the fixed left branch but does not count it as the parametric portfolio, final disjunction artifact, or G-110 completion
  validation_refs:
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/CartesianTarget.lean: pass, namespace audit 25 declarations and standard axioms only
    - lake build ResearchLean.AG.DoctrineFiberProduct.CartesianTarget: pass targeted module check
    - lake env lean ResearchLean/AG/DoctrineFiberProduct.lean: pass
    - direct acceptance-spine #print axioms audit: all 25 evidence declarations use only standard axioms
    - fixed-head PR CI: 7 of 7 checks green
  review_refs:
    fixed_head: cd7b6974f8e62eaccb691e780e5a46f096b0c881
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4045#issuecomment-5368253799
    verdicts:
      - Math A: no major findings for the Cycle 9 global-left obligation only
      - Math B: no major findings for the Cycle 9 global-left obligation only
      - Lean A: no major findings for the Cycle 9 global-left obligation only
      - Lean B: no major findings for the Cycle 9 global-left obligation only
  initial_review_findings:
    - all four initial lanes found no Major issue in the global-left theorem but required report precision about conditional generic-helper premises, standalone roundtrip API, and the absence of a direct Cycle 8 theorem dependency
    - Lean B and Math A required unchecked to retain repaired-head review/CI until the final sync
    - Math B found two unused private helper declarations; both were removed before rereview
  blocking_findings: []
  next_obligation: construct a pairwise nonisomorphic noninvertible ParametricCartLiftFamily, then fix the single carrier-global DisjunctionArtifact and cartesianRegimeOfDisjunction from the proved global branch before K0-K4
```

### Cycle 9 acceptance spine

Cycle 9 の直接 axiom audit は上記 `evidence` 25 declaration に固定する。
`globalCartesianLift` は固定 GOAL の左枝を inhabit するが、非退化
`ParametricCartLiftFamily`、単一 `DisjunctionArtifact`、
`cartesianRegimeOfDisjunction`、K0、K2–K4 を達成したとは数えない。

### Cycle 8 — canonical package transport is strongly cartesian

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 8
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 9400096d8a55f12ea6e18ee5f64bf7d73c650bf2
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 8 selection comment 5367241492
  proof_dag_predecessors:
    - G-101 canonical package transport and strong cocartesian theorem, merge dd5e02b5 and reviewed head db47ee9e
    - Cycle 6 F0c1 strong-lift and regime signatures, PR 4042 merge 487bee332fbd426cb70ffe926b4c0201ab569a60
    - Cycle 7 canonical finite-code universe reindexing, PR 4043 merge 9400096d8a55f12ea6e18ee5f64bf7d73c650bf2
  proof_obligation: construct the unique suffix factor of every total hom whose base factors through canonical package transport, and derive Mathlib Functor.IsStronglyCartesian for the canonical transport arrow without inverting the lower source map
  selection_reason: independent orientation audits showed that the existing upper deconjugation already generates a two-sided inverse to canonical upper transport, so the universal-property half of the global-left branch can be discharged before the separate arbitrary-target package preimage construction
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianTransport.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - renaming the existing strongly cocartesian prefix factorization as cartesian without reversing the factorization direction
    - assuming an inverse ExactDoctrineHom or invertible sourceMap
    - accepting the upper inverse, total factor, or strong-cartesian certificate as an input
    - restricting the competitor base prefix or total hom instead of proving the strong universal property
    - counting a canonical codomain transport theorem as a lift ending at every arbitrary target-fiber package
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: specialized canonical upper deconjugation to the identity upper hom; proved both upper inverse laws; constructed the total suffix factor from an arbitrary competitor and its derived base factorization; proved base, factorization, and uniqueness laws; packaged the explicit exists-unique property; and instantiated Mathlib Functor.IsStronglyCartesian for transportAlongHom over packageProjection
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianTransport.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - transportAlongUpperInverse
    - transportAlongUpperInverse_atomEquiv
    - transportAlongUpper_comp_inverse
    - transportAlongUpperInverse_comp
    - packageCartesianFactor
    - packageCartesianFactor_base
    - packageCartesianFactor_fac
    - packageCartesianFactor_unique
    - transportAlongHom_cartesianFactor_existsUnique
    - transportAlongHom_isStronglyCartesian
  claim_mapping:
    theorem_names:
      - transportAlongUpper_comp_inverse
      - transportAlongUpperInverse_comp
      - transportAlongHom_cartesianFactor_existsUnique
      - transportAlongHom_isStronglyCartesian
    source_labels:
      - target theorem (B) strong cartesian lift universal-property layer
      - target proof strategy F0c2 branch-exact package construction precursor
    conjuncts:
      - the upper inverse is generated from the reviewed G-101 deconjugation theorem and the identity upper hom
      - the total factor lies over an arbitrary prefix base map and composes on the left of canonical transport to recover the arbitrary competitor
      - uniqueness uses both the competitor factorization and the canonical upper inverse law
      - strong cartesianness quantifies every prefix base morphism and every total hom over its composite with the canonical base arrow
    undischarged_assumptions:
      - an arbitrary targetPackage in CoreFiber input.target has not yet been inverse-reindexed to a source package whose canonical transport reaches that target
      - GlobalCartesianLift, the exact RightBranch and FiniteModelLift type surfaces, DisjunctionArtifact, and cartesianRegimeOfDisjunction remain unresolved
      - the branch-independent nonisomorphic noninvertible parametric lift family remains unresolved
      - K0 and K2-K4 remain unresolved
    acceptance_point: the universal-property half of arbitrary-target cartesian lifting is closed for canonical transport codomains; no arbitrary-target or carrier-global conclusion is counted
    port_status: unported
audits:
  premise_delta:
    discharged:
      - generated two-sided inverse of canonical upper transport
      - arbitrary total suffix factor and uniqueness
      - canonical transport Functor.IsStronglyCartesian
    remaining:
      - inverse-Atom reindexing of an arbitrary target package and endpoint casts
      - global branch artifact and generated regime
      - branch-independent nondegenerate lift family
      - K0 and K2-K4
  certificate_provenance:
    discharged:
      - transportAlongUpperInverse is computed by canonicalDeconjugateTransportUpper on SignedExactCoreReadingHom.refl
      - packageCartesianFactor is computed from the supplied competitor, its base prefix, and the generated upper inverse
      - IsStronglyCartesian is built from the explicit exists-unique factor theorem
    unresolved:
      - arbitrary target-package preimage and the named source of the eventual global disjunction
  proof_use:
    used:
      - canonicalTailAtomEquiv_factor and transportAlongUpper_comp_deconjugate for the first inverse law
      - transportAlongUpper_comp_injective plus upper associativity and unit laws for the second inverse law
      - both inverse laws in total factorization and uniqueness
      - IsHomLift.eq_of_isHomLift to derive competitor base equalities in the Mathlib universal property
    unused: []
  structure_field_escape: none-found; no structure or certificate field is introduced, and the factor and universal-property witness are named constructions
  route_integrity: pass for canonical codomains; the report explicitly retains arbitrary-target object construction before GlobalCartesianLift
  target_fitting: the theorem is generic over every carrier, source package, exact doctrine morphism, prefix base map, and competing total hom
  vacuity: the theorem assumes no IsIso instance for the lower morphism and proves the strong universal property for arbitrary competitors; the required explicit noninvertible parametric family remains separately undischarged
  one_way_as_equivalence: none-found; both upper inverse laws are proved, while no inverse lower source map is defined or assumed
  goal_or_report_reinterpretation: none; canonical strong cartesianness is recorded only as one construction lemma toward the fixed arbitrary-target left branch
  validation_refs:
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/CartesianTransport.lean: pass, namespace audit 10 declarations and standard axioms only
    - lake build ResearchLean.AG.DoctrineFiberProduct.CartesianTransport: pass targeted module check
    - lake env lean ResearchLean/AG/DoctrineFiberProduct.lean: pass
    - fixed-head direct acceptance-spine #print axioms audit: all 10 evidence declarations use only standard axioms
    - fixed-head PR CI: 7 of 7 checks green
  review_refs:
    fixed_head: 77539722f50cdee3c89055a3ac226b384d233260
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4044#issuecomment-5367470736
    verdicts:
      - Math A: no major findings for the Cycle 8 canonical-codomain obligation only
      - Math B: no major findings for the Cycle 8 canonical-codomain obligation only
      - Lean A: no major findings for the Cycle 8 canonical-codomain obligation only
      - Lean B: no major findings for the Cycle 8 canonical-codomain obligation only
  initial_review_findings: []
  blocking_findings: []
  next_obligation: construct the arbitrary target-package inverse reindexing and derive GlobalCartesianLift before fixing the final carrier-global artifact and regime producer
```

### Cycle 8 acceptance spine

Cycle 8 の直接 axiom audit は上記 `evidence` 10 declaration に固定する。
canonical target `transportAlong P f` 以外の package、`GlobalCartesianLift`、
right-branch data、または分岐 artifact の inhabitant を達成したとは数えない。

### Cycle 7 — F0c2a1 canonical finite-code universe reindexing

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 7
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 487bee332fbd426cb70ffe926b4c0201ab569a60
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 7 selection comment 5366211911 and route-clarification comment 5366392928
  proof_dag_predecessors:
    - Cycle 2 F0a finite-code cartesian schema, PR 4038 merge 5dd7bbb297c50498e6cff706258a5237381df9d4
    - Cycle 3 F0b1 basic BC presentation and condition schema, PR 4039 merge 1f096739106d22c21ffa49fc6c2bd0c0e6fb940b
    - Cycle 4 F0b2a finite-code pasting and authored raw schema, PR 4040 merge 76ffc581f7075163579ad4d1a246f295c0903f07
    - Cycle 5 F0b2b authored-support and relative-predicate signatures, PR 4041 merge b67c112b7dfc4aba260901c16568d94bf4f7c08d
    - Cycle 6 F0c1 strong-lift and qualified-regime signatures, PR 4042 merge 487bee332fbd426cb70ffe926b4c0201ab569a60
  proof_obligation: construct the canonical cross-universe reindexing of every finite cartesian code component, derive validated presentations and decoder-component compatibility, and prove preservation of the complete finite Bool condition evaluator
  selection_reason: full equivalences of all ExtractionInstance and AATCorePackage values were rejected as an over-strong auxiliary route because arbitrary Type u doctrine/reading components need not descend to universe zero; the fixed GOAL instead permits this exact finite-code boundary to be discharged before the selected package and strong-cartesian branch construction
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteCodeULift.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteCodeULiftWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - claiming a whole semantic category equivalence from the finite-code image
    - storing well-formedness, condition bits, semantic arrows, packages, or no-lift conclusions as new raw-code fields
    - dropping or replacing the noninvertible source table or nonidentity Atom permutation during rebasing
    - proving only selected evaluator branches instead of all projections, constants, derived sets, universal equalities, and syntax constructors
    - counting finite-code transport as packageProjection or StrongCartesianLift existence/nonexistence transport
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: defined a six-sort AtomCarrierEquiv with all five projection-commutation laws; canonical first-order source reindexing; predicate support mapping and evaluation naturality; finite permutation support mapping and conjugation; doctrine, pointed-instance, four-field raw-code, typed-presentation, and validated-presentation reindexing; derived WellFormed preservation; source-map, Atom-map, selected-point, extraction, and decoder-component compatibility; equivalences for every condition value sort; naturality of all 13 projections, 3 named constants, 5 derived finite sets, and 7 finite-universal equality atoms; complete reindexing invariance of all 4 CartConditionSyntax constructors; the canonical FiniteModel carrier/presentation specialization; and positive/nonidentity/malformed finite witnesses
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/FiniteCodeULift.lean
    - ResearchLean/AG/DoctrineFiberProduct/FiniteCodeULiftWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - AtomCarrierEquiv
    - finiteSourceRebaseEquiv
    - AtomPredicateCode.rebase
    - AtomPredicateCode.eval_rebase
    - AtomPermutationCode.rebase
    - AtomPermutationCode.toEquiv_rebase
    - FiniteDoctrineCode.rebase
    - FiniteDoctrineCode.toDoctrine_extracts_rebase_iff
    - FiniteInstanceCode.rebase
    - CartRawCode.rebase
    - CartRawCode.WellFormed.rebase
    - CartRawCode.rebase_sourceMap
    - CartRawCode.rebase_atomEquiv_apply
    - rebaseCartPresentation
    - CartPresentationBetween.rebase
    - toSemanticCart_rebase_sourceMap
    - toSemanticCart_rebase_atomEquiv
    - toSemanticCart_rebase_sourcePoint
    - toSemanticCart_rebase_targetPoint
    - readCartProjection_rebase
    - readCartNamedConstant_rebase
    - evalCartFieldTerm_rebase
    - evalCartDerivedSet_rebase
    - evalCartUniversalEquality_rebase
    - evalCartCondition_rebase
    - finiteModelLiftCarrierEquiv
    - finiteModelLiftCartPresentation
    - evalCartCondition_finiteModelLift
    - finiteModelLiftConstantSourceMap_not_injective
    - finiteModelLiftSwapPresentation_moves_componentC
    - finiteModelLiftBadPointRawCode_check_false
  claim_mapping:
    theorem_names:
      - CartRawCode.WellFormed.rebase
      - toSemanticCart_rebase_sourceMap
      - toSemanticCart_rebase_atomEquiv
      - evalCartCondition_rebase
      - evalCartCondition_finiteModelLift
    source_labels:
      - target theorem (B) fixed finite-presentation and universe-polymorphic boundary
      - target material premise FiniteModelLift precursor
      - target proof strategy F0 split signature typing
    conjuncts:
      - every carrier coordinate and Atom projection has a canonical typed equivalence rather than an Atom-only cast
      - predicate exceptions and permutation support/graph are mapped injectively, with permutations conjugated rather than erased
      - doctrine normalization and source maps are conjugated through the canonical FiniteSource equivalence while source cardinalities and first-order indices are preserved
      - raw WellFormed at the target is derived from the source proof and predicate-transport naturality; no validation field is authored
      - decoded source maps, Atom permutations, selected points, and extraction predicates commute on corresponding cells
      - evaluator preservation covers field equality by value-sort equivalence injectivity, membership by unchanged first-order indices, all seven universal atoms, and conjunction recursively
      - the lifted constant source map remains noninjective, the moved Atom remains moved, positive and negative identity-Atom checks retain their values, and the malformed selected-point code remains rejected
    undischarged_assumptions:
      - F0c2a2/b must still fix the carrier-global disjunction artifact and named regime producer; this finite-code result neither constructs nor transports an endpoint AATCorePackage or StrongCartesianLift
      - if K1 closes the right branch, it must construct the actual FiniteModel no-lift witness and its arbitrary-universe nonexistence preservation without a counterexample-specific lift-type equivalence or caller-provided result field
      - if K1 closes the left branch, it must construct GlobalCartesianLift directly; no H_cart checker or finite no-lift transport is then counted from this cycle
      - K0-K4 remain entirely unresolved
    acceptance_point: F0c2a1 closes the computable finite-code and checker portion of canonical universe reindexing while keeping semantic package and branch conclusions outside the code layer
    port_status: unported
audits:
  premise_delta:
    discharged:
      - canonical carrier, finite-source, predicate, permutation, doctrine, instance, raw code, and validated presentation reindexing
      - derived WellFormed and decoder-component compatibility
      - complete finite condition evaluator preservation
      - positive, negative, and malformed finite reindexing witnesses
    remaining:
      - F0c2a2/b carrier-global branch/artifact/producer signatures and any selected package-level transport actually needed by that branch
      - K0 nondegenerate proper-fiber witness
      - K1 branch construction
      - K2-K4 BC, diagnostic, and closure obligations
  certificate_provenance:
    discharged:
      - finiteModelLiftCarrierEquiv is generated only from ULift up/down and projection laws are rfl
      - every rebased code field is computed from the corresponding source field
      - target WellFormed is proved from source WellFormed; evaluator equality is proved by reader and universal-atom naturality
    unresolved:
      - any packageProjection-level or strong-cartesian construction
      - named source of the eventual carrier-global disjunction
  proof_use:
    used:
      - source normalization, extraction exactness, and selected-point laws in CartRawCode.WellFormed.rebase
      - both source and rebased validation proofs in the universal normalization/default/exception evaluator branches
      - value-sort equivalence injectivity in fieldEq preservation
      - canonical source/Atom equivalences in the noninjective, nonidentity, and malformed witnesses
    unused:
      - the five non-Atom coordinate equivalences and five projection-commutation laws of AtomCarrierEquiv are constructed canonically but are not consumed by the finite-code layer, which reads only U.Atom; their proof-use is deferred to the still-undischarged package-level construction and is not counted in F0c2a1
  structure_field_escape: none-found; the only new structure is an input carrier equivalence whose fields are coordinate equivalences and projection-commutation laws, while raw presentation fields remain exactly the reviewed four
  route_integrity: pass for the finite-code boundary; no image-category or full semantic-category equivalence is claimed
  target_fitting: the implementation is generic over every AtomCarrierEquiv and every CartPresentation/CartConditionSyntax; concrete witnesses only test the generic route
  vacuity: positive accepted, negative evaluator, noninjective source-map, moved-Atom, and malformed-rejected witnesses all survive the canonical lift
  one_way_as_equivalence: none-found; only genuine value equivalences are named equivalences, while validation and decoder laws remain directional/naturality theorems
  goal_or_report_reinterpretation: none; the rejected whole-category equivalence was an auxiliary Issue route stronger than the fixed GOAL, and Cycle 7 records its replacement without weakening any GOAL conjunct
  validation_refs:
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/FiniteCodeULift.lean: pass, namespace audit 89 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/FiniteCodeULiftWitnesses.lean: pass, namespace audit 11 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct.lean: pass
    - lake build ResearchLean.AG.DoctrineFiberProduct.FiniteCodeULift: pass targeted module check
    - lake build ResearchLean.AG.DoctrineFiberProduct.FiniteCodeULiftWitnesses: pass targeted module check
    - repaired-head direct acceptance-spine #print axioms audit: 31 evidence declarations plus 11 witness declarations, each uses only standard axioms or no axioms
    - fixed-head PR CI: 7 of 7 checks green
  review_refs:
    fixed_head: adcd90280325c80a506093a388091f13f6dc40b6
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4043#issuecomment-5367057730
    verdicts:
      - Math A: no major findings for F0c2a1 only
      - Math B: no major findings for F0c2a1 only
      - Lean A: no major findings for F0c2a1 only
      - Lean B: no major findings for F0c2a1 only
  initial_review_findings:
    - initial head 7348d910 omitted docstrings on three public helper theorems; repaired without changing statements or proof bodies
    - initial head 7348d910 recorded no unused fields even though the five non-Atom coordinate equivalences and five projection laws are deferred to the package layer; repaired by explicit proof-use classification
  blocking_findings: []
  next_obligation: superseded by Cycle 8, which proves canonical package transport strongly cartesian while retaining arbitrary-target package reindexing and the carrier-global artifact/producer as unresolved
```

### Cycle 7 / F0c2a1 acceptance spine

Cycle 7 の直接 axiom audit は、上記 `evidence` 31 declaration と witness module の
11 declaration に固定する。ここでは `FiniteModelLift`、`RightBranch`、
`DisjunctionArtifact`、`cartesianRegimeOfDisjunction`、package reindexing、
strong-cartesian existence/nonexistence を達成したとは数えない。

### Cycle 6 — F0c1 strong-lift, qualification, and per-carrier regime signatures

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 6
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: b67c112b7dfc4aba260901c16568d94bf4f7c08d
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 6 selection comment 5365512778, final fixed-head ledger comment 5366159629, integrated review comment 5366158627, and revised GOAL strategy F0
  proof_dag_predecessors:
    - Cycle 2 F0a finite-code cartesian schema, PR 4038 merge 5dd7bbb297c50498e6cff706258a5237381df9d4
    - Cycle 3 F0b1 basic BC presentation and condition schema, PR 4039 merge 1f096739106d22c21ffa49fc6c2bd0c0e6fb940b
    - Cycle 4 F0b2a finite-code pasting and authored raw schema, PR 4040 merge 76ffc581f7075163579ad4d1a246f295c0903f07
    - Cycle 5 F0b2b authored-support and relative-predicate signatures, PR 4041 merge b67c112b7dfc4aba260901c16568d94bf4f7c08d
    - G-101 packageProjection and G-109 CoreFiber API
  proof_obligation: fix the exact strong-cartesian-lift, carrier-global left proposition, qualified per-carrier right-regime, pairwise arrow-nonisomorphic positive-family, branch-independent lift-family, finite counterexample endpoint, and per-carrier CartesianRegime signatures on RealizableHom
  selection_reason: the initial full-F0c head was rejected because its positive-family type admitted isomorphic duplicates and its counterexample-specific StrongCartesianLift equivalence did not encode canonical ULift provenance; F0 may be split, so this repaired checkpoint retains only the exact surfaces independent of cross-carrier package-projection reindexing
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeSchema.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeSchemaWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - quantifying over arbitrary semantic arrows instead of the RealizableHom image
    - weakening one carrier-global branch to a per-carrier disjunction
    - letting the selected syntax or semantic condition vary with a fixture or carrier
    - defining H_cart from lift existence, a checker bit, or one fixture equality
    - omitting presentation replacement, semantic isomorphism, identity, composition, or either pullback-stability direction
    - treating unequal but isomorphic semantic arrows as a nondegenerate family
    - using a counterexample-specific equivalence of empty lift types as universe transport
    - carrying an unrelated caller-supplied CartesianRegime into K1-K4 before the F0c2 producer exists
    - counting an identity lift or tautological schema witness as selection of the global theorem branch
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: defined the actual mathlib strong-cartesian lift bundle over a named CartSemanticInput and endpoint CoreFiber package; restricted carrier lift existence to RealizableHom; placed the carrier quantifier inside GlobalCartesianLift; fixed semantic arrow isomorphisms and a QualifiedCartCondition whose checker is derived from frozen syntax and whose bridge type, presentation replacement invariance, semantic isomorphism invariance, and constructor-relative wide pullback-stable closure are explicit; rebased the structural syntax uniformly across carriers; fixed a right-positive-family interface whose distinct parameters are pairwise nonisomorphic semantic arrows and whose same H_cart-positive members carry endpoint packages and actual strong lifts; fixed a branch-independent family of actual strong lifts over pairwise nonisomorphic noninvertible arrows; fixed finite no-lift/counterexample endpoint types; and fixed CartesianRegime with branch-independent lift and closure eliminators
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeSchema.lean
    - ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeSchemaWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - StrongCartesianLift
    - StrongCartesianLift.domainObject
    - HasStrongCartesianLift
    - CarrierCartesianLift
    - GlobalCartesianLift
    - CartSemanticInputIso
    - rebaseCartCondition
    - QualifiedCartCondition
    - QualifiedCartCondition.checkCart_input_eq_true_iff
    - ParametricCartPositiveFamily
    - ParametricCartLiftFamily
    - RightCartesianRegime
    - finiteModelLiftCarrier
    - CartesianLiftNonexistence
    - CartesianLiftCounterexample
    - CartesianRegime
    - CartesianRegime.hasStrongCartesianLift
    - CartesianRegime.identity_mem
    - CartesianRegime.comp_mem
    - CartesianRegime.pullback_fst_mem
    - CartesianRegime.pullback_snd_mem
    - packageIdentityStrongCartesianLift
    - tautologicalQualifiedCartCondition
    - finiteModelLiftAtoms_ne
  claim_mapping:
    theorem_names:
      - GlobalCartesianLift
      - QualifiedCartCondition
      - ParametricCartPositiveFamily
      - ParametricCartLiftFamily
      - CartesianRegime
    source_labels:
      - target theorem (B) lift and qualified-right-branch domains
      - target proof artifact CartesianRegime
      - target proof strategy F0 split signature typing
    conjuncts:
      - StrongCartesianLift stores a generated domain package and total morphism together with mathlib IsStronglyCartesian over the actual semantic bottom arrow
      - CarrierCartesianLift quantifies all RealizableHom values and all packages in the semantic target CoreFiber
      - GlobalCartesianLift quantifies all carriers before any branch constructor is selected
      - QualifiedCartCondition selects one frozen CartConditionSyntax term and derives checkCart directly from evalCartCondition
      - checkCart_input_eq_true_iff extends the canonical-presentation bridge to every RealizableHom by consuming realization_eq
      - the same qualified condition requires presentation replacement invariance, arrow-isomorphism invariance, identity and composition closure, and both generated pullback projection directions
      - rebaseCartCondition is structural because the frozen language contains no authored Atom, external set, fixture literal, result bit, or lift vocabulary
      - distinct parameters in ParametricCartPositiveFamily admit no CartSemanticInputIso, and every same member has nonisomorphic endpoints, a noninvertible arrow, H_cart membership, an endpoint package, and an actual StrongCartesianLift
      - ParametricCartLiftFamily requires actual StrongCartesianLift values over a pairwise arrow-nonisomorphic noninvertible family independently of the eventual branch
      - finiteModelLiftCarrier is only the explicit ULift carrier; no package/input transport or no-lift preservation is claimed in F0c1
      - CartesianLiftNonexistence and CartesianLiftCounterexample fix the exact per-carrier negative endpoint types without transporting them
      - CartesianRegime exports HCart, lift sufficiency, identity, composition, and both pullback-stability directions uniformly across branches
      - the concrete identity lift and tautological qualified condition exercise only the F0 type surface and are explicitly not a K1 branch artifact
    undischarged_assumptions:
      - F0c2 must construct the canonical finite-code carrier/presentation reindexing, then fix only the selected package/strong-cartesian construction required by the eventual global branch before defining RightBranch, DisjunctionArtifact, and cartesianRegimeOfDisjunction; a full equivalence of all higher-universe semantic objects is neither required nor claimed
      - if the right branch is selected, F0c2/K1 must derive the lifted input/package and strong-cartesian nonexistence preservation from a uniform construction; a package-valued result field or counterexample-specific lift-type equivalence is not accepted
      - K1 must construct a named GlobalCartesianLift or the final named RightBranch and thereby the actual DisjunctionArtifact
      - in the right branch K1 must define semantic H_cart without referring to lift existence or checker output, prove all qualification fields, construct endpoint packages and actual lifts for the same pairwise arrow-nonisomorphic noninvertible H_cart-positive family, and prove uniform sufficiency
      - if K1 selects the global branch it must separately construct a pairwise arrow-nonisomorphic parametric family of noninvertible RealizableHom inputs and instantiate GlobalCartesianLift on every member and endpoint package
      - K1 must construct the exact FiniteModel no-lift counterexample and the F0c2 canonical transport value
      - K1-K4 must use the future cartesianRegimeOfDisjunction applied to the named artifact; an arbitrary CartesianRegime argument is conclusion-equivalent and does not discharge provenance
    acceptance_point: F0c1 fixes the local lift, qualification, nondegenerate family, negative endpoint, and per-carrier regime types while refusing to fake the unresolved cross-universe package transport
    port_status: unported
audits:
  premise_delta:
    discharged:
      - exact strong-cartesian-lift and endpoint-package dependent indices
      - carrier-global left-branch rather than per-carrier left-branch quantifier order
      - exact fixed-syntax/semantic-predicate/checker bridge and invariance signature
      - constructor-relative identity, composition, and two-direction pullback-stability signature
      - carrier-independent syntax rebasing and explicit finite-model lifted carrier
      - pairwise arrow-nonisomorphic positive and actual-lift family interfaces
      - exact per-carrier regime and eliminator types
    remaining:
      - F0c2 canonical finite-code reindexing, branch-exact package/strong-cartesian construction, and carrier-global producer signatures
      - K0 nondegenerate proper-fiber witness
      - K1 mathematical branch determination and all branch values
      - K2 route functors, adjunctions, canonical mate, authored comparison, strict/lax pair, and orbit theorems
      - K3-K4 diagnostic base change, conditions, closure, and coherence
  certificate_provenance:
    discharged:
      - strong lift endpoints are indexed by CartSemanticInput and CoreFiber rather than equality fields in finite code
      - the checker is computed only by evalCartCondition on the selected frozen term
      - every RealizableHom bridge consumes its own presentation and realization_eq
      - uniform syntax is generated by structural constructor rebasing
    unresolved:
      - F0c2 branch-exact package/strong-cartesian construction beyond the finite decoder components
      - F0c2 RightBranch, DisjunctionArtifact, and named regime producer
      - named K1 source of the selected branch and every theorem field in it
  proof_use:
    used:
      - IsStronglyCartesian in StrongCartesianLift.domainObject through IsHomLift.domain_eq
      - RealizableHom.realization_eq in checkCart_input_eq_true_iff
      - right condition sufficiency in CartesianRegime.hasStrongCartesianLift
      - right qualification fields in all four closure eliminators
    unused: []
    deferred_field_proof_use:
      - replacement_invariant, isomorphic_invariant, both family values including the right-positive family's same-member lifts, and counterexample values are target outputs; F0c1 fixes their types while K1 must construct and audit their proof terms
  structure_field_escape: none-found in the retained F0c1 surface; the rejected counterexample-specific strongLiftEquiv, liftedInput, liftedTargetPackage, and condition_preserved fields were removed
  route_integrity: pass for F0c1 typing; global producer provenance remains explicitly unresolved until F0c2
  target_fitting: pairwise_nonisomorphic prevents duplicated representatives of one semantic-arrow isomorphism class, while targetPackage and lift on ParametricCartPositiveFamily prevent an H-positive empty-fiber or unrelated-family witness; no fixture-specific condition or counterexample transport remains
  vacuity: an actual identity strong lift, qualified fixed-syntax condition, both per-carrier regime eliminator paths under honest premises, and two distinct lifted Atoms elaborate; actual nondegenerate family and counterexample values remain unresolved and are not claimed
  one_way_as_equivalence: none-found in the retained surface; sufficiency remains one-way H_cart to lift existence, and the rejected counterexample-specific equivalence was deleted
  goal_or_report_reinterpretation: initial full-F0c claim was narrowed after review under the GOAL's explicit permission to split F0; F0c2 remains discharge-required before K0
  validation_refs:
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeSchema.lean: pass, namespace audit 180 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/CartesianRegimeSchemaWitnesses.lean: pass, namespace audit 15 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct.lean: pass
    - lake build ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeSchema: pass targeted module check
    - lake build ResearchLean.AG.DoctrineFiberProduct.CartesianRegimeSchemaWitnesses: pass targeted module check
    - repaired-head direct acceptance-spine #print axioms audit: 42 declarations, each uses only propext/Classical.choice/Quot.sound or no axioms
    - fixed-head PR CI: 7 of 7 checks green
  review_refs:
    fixed_head: d6d178452759a22bf6cbfc67680e09da474f048f
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4042#issuecomment-5366158627
    verdicts:
      - Math A: no major findings for F0c1 only
      - Math B: no major findings for F0c1 only
      - Lean A: no major findings for F0c1 only
      - Lean B: no content findings for F0c1; tracker fixed-head synchronization closed by Issue comment 5366159629
  initial_review_findings:
    - initial head fd9ff6c6 admitted isomorphic duplicates in ParametricCartPositiveFamily; repaired by pairwise_nonisomorphic
    - initial head fd9ff6c6 used a counterexample-specific StrongCartesianLift equivalence without canonical ULift provenance; repaired by deleting that surface and splitting canonical finite-code reindexing plus branch-exact package construction into F0c2
    - repaired head 11d297d6 left the H_cart-positive and actual-lift families unrelated; repaired by requiring an endpoint package and actual lift on every same ParametricCartPositiveFamily member
  blocking_findings: []
  next_obligation: superseded by Cycle 7, which discharges canonical finite-code reindexing and retains branch-exact package construction plus global RightBranch/DisjunctionArtifact/cartesianRegimeOfDisjunction signatures before K0
```

### Cycle 6 / F0c1 acceptance spine

Cycle 6 / F0c1 の直接 axiom audit は次の42 declaration に固定する。
`RightBranch` / `DisjunctionArtifact` / global producer はまだ定義せず、
tautological witness はK1右枝候補として数えない。

- lift domain: `StrongCartesianLift`, `StrongCartesianLift.domainObject`,
  `HasStrongCartesianLift`, `CarrierCartesianLift`, `GlobalCartesianLift`
- semantic invariance and syntax uniformity: `CartSemanticInputIso`,
  `CartSemanticInputIso.refl`, `rebaseCartProjection`,
  `rebaseCartNamedConstant`, `rebaseCartFieldTerm`, `rebaseCartCondition`
- qualified condition: `QualifiedCartCondition`,
  `QualifiedCartCondition.checkCart`,
  `QualifiedCartCondition.checkCart_eq_true_iff`,
  `QualifiedCartCondition.checkCart_input_eq_true_iff`,
  `ParametricCartPositiveFamily`, `ParametricCartLiftFamily`,
  `RightCartesianRegime`
- finite-universe endpoint types: `finiteModelLiftCarrier`,
  `CartesianLiftNonexistence`, `CartesianLiftCounterexample`
- per-carrier regime: `CartesianRegime`,
  `CartesianRegime.HCart`, `CartesianRegime.hasStrongCartesianLift`,
  `CartesianRegime.identity_mem`, `CartesianRegime.comp_mem`,
  `CartesianRegime.pullback_fst_mem`, `CartesianRegime.pullback_snd_mem`
- F0 witnesses: `packageIdentitySemanticInput`, `packageIdentityTarget`,
  `packageIdentityStrongCartesianLift`, `packageIdentity_hasStrongCartesianLift`,
  `packageIdentity_domainObject_val`, `tautologicalCartConditionTerm`,
  `tautologicalQualifiedCartCondition`,
  `tautologicalQualifiedCartCondition_check_true`,
  `tautologicalRightCartesianRegime`, `globalRegime_hasStrongCartesianLift`,
  `conditionalRegime_hasStrongCartesianLift`, `finiteModelLiftAtomA`,
  `finiteModelLiftAtomB`, `finiteModelLiftAtoms_ne`

### Cycle 5 — F0b2b authored-support and relative-predicate signatures

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 5
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 76ffc581f7075163579ad4d1a246f295c0903f07
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 4 merge update comment 5365010745 and revised GOAL strategy F0
  proof_dag_predecessors:
    - Cycle 2 F0a finite-code cartesian schema, PR 4038 merge 5dd7bbb297c50498e6cff706258a5237381df9d4
    - Cycle 3 F0b1 basic BC presentation and condition schema, PR 4039 merge 1f096739106d22c21ffa49fc6c2bd0c0e6fb940b
    - Cycle 4 F0b2a finite-code pasting and one-field authored raw table, PR 4040 merge 76ffc581f7075163579ad4d1a246f295c0903f07
    - G-106 AdmissibleLiftData and AdmissibleTransportData
    - G-109 CoreFiber API
  proof_obligation: fix the exact authored-datum-square domain, tagged finite authored support, pointwise-component-to-NatTrans interface, K2 authored-comparison and canonical-mate producer types, and the MateCoherentRel equality/signature shape without supplying comparison values, naturality certificates, a canonical mate, or expected equality in an input field
  selection_reason: the fixed strategy requires presentation, condition, relative-predicate, and regime signatures to elaborate before K0; Cycle 4 fixed the raw table but deliberately left its support domain and dependent comparison types to this immediately following F0b2b obligation
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCRelativeSchema.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCRelativeSchemaWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - an endpoint-deduplicated full support could falsely force unrelated authored comparator values to agree
    - a comparator-dependent commutant category could make naturality true by target fitting
    - discrete support could be selected only after seeing a fixture instead of uniformly from the finite authored index
    - southwest endpoint incidence could hide a comparison or coherence conclusion
    - the canonical mate signature could inspect the raw authored comparator
    - arbitrary NatTrans values or expected equality could be accepted as public relation inputs
    - generic F0 equation scaffolding could be overclaimed as the actual K2 comparison construction
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: separated a comparator-free support context from the authored datum; fixed the support uniformly as Discrete G.TwoCell with a realization functor into the southwest CoreFiber; reconstructed reviewed G-106 semantic data from the separated lift, twoCellBase, and one-field raw table; converted every PackageFiberAut value to a southwest-fiber component and a discrete natural endotransformation; fixed the dependent northeast route-family, component-family, authored-comparison producer, comparator-independent canonical-mate restriction, and final relation signatures; and elaborated the equality equation that K2 must specialize to named producers
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCRelativeSchema.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCRelativeSchemaWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - AuthoredSupportContext
    - AuthoredSupportContext.Category
    - AuthoredSupportContext.supportFunctor
    - AuthoredBCDatumSquare
    - AuthoredBCDatumSquare.toTransportData
    - AuthoredBCDatumSquare.ofInterpretation
    - AuthoredBCDatumSquare.endpointComponentTotal_isHomLift
    - AuthoredBCDatumSquare.endpointAutomorphism
    - AuthoredBCDatumSquare.endpointAutomorphism_app_val
    - AuthoredSupportRouteFamily
    - AuthoredComparisonComponents
    - authoredComparisonOfComponents
    - AuthoredComparisonProducerSignature
    - CanonicalMateRestrictionSignature
    - AuthoredSupportComparison.Agrees
    - MateCoherentRelSignature
    - mateCoherentRelEquation
    - finiteAuthoredBCDatumSquare
    - finiteAuthoredSupport_nonempty
    - finiteAuthoredEndpointAutomorphism_component
    - finiteAuthoredEndpointAutomorphism_eq_identity
    - finiteAgreement_positive
    - finiteAgreement_negative
  claim_mapping:
    theorem_names:
      - AuthoredSupportContext
      - AuthoredBCDatumSquare
      - AuthoredBCDatumSquare.endpointAutomorphism
      - authoredComparisonOfComponents
      - AuthoredComparisonProducerSignature
      - CanonicalMateRestrictionSignature
      - MateCoherentRelSignature
      - mateCoherentRelEquation
    source_labels:
      - target theorem (C) authored support and generated 2-cell family
      - target proof artifacts AuthoredBC2CellPresentation / authored support / MateCoherentRel
      - target proof strategy F0 relative-predicate exact signature
    conjuncts:
      - every authored occurrence is indexed by the complete finite G-106 TwoCell type
      - the support category is the same Discrete TwoCell construction for every input and does not inspect comparator values or fixture values
      - distinct authored cell tags remain distinct even when their endpoint packages coincide
      - the support functor lands in the square southwest CoreFiber through an explicit endpoint-incidence direction hypothesis
      - AuthoredBCDatumSquare contains only a realizable square, G-106 lift/base data, endpoint incidence, and the one-field AuthoredBC2CellPresentation
      - toTransportData reconstructs exactly the reviewed G-106 semantic shape and copies the authored comparator definitionally
      - every raw PackageFiberAut is used as the underlying total morphism of its support component
      - Discrete.natTrans generates naturality from the complete component family without a naturality input field
      - authored comparison producers see the authored datum while canonical mate restrictions see only the comparator-free support context
      - both producer signatures land in the same dependent NatTrans type on authored support
      - mateCoherentRelEquation is equality of those two results and the public relation domain is exactly AuthoredBCDatumSquare U
      - the generic equation scaffold is not the K2 public relation and does not count as construction of either producer
      - a concrete finite-code square has nonempty authored support and a package genuinely placed over its southwest vertex
      - positive and negative agreement instances prevent the equality predicate from being definitionally constant
    undischarged_assumptions:
      - K2 must generate AuthoredSupportContext.endpoint_eq from its actual pointed input or discharge it on each quantified input; an arbitrary context argument does not prove the final theorem
      - F0c/K1 must generate the route families and cartesian regime used by K2
      - K2 must construct the authored comparison from raw data, construct the canonical mate from units/counits, prove comparator proof-use and cleavage independence, and expose a closed MateCoherentRel with strict/lax instances
    acceptance_point: F0b2b fixes an elaborated and nonempty type surface while preserving the F0/K2 boundary; discrete tagged support is selected uniformly because the fixed GOAL explicitly disclaims canonical full-fiber extension, and no comparison value or equality certificate is smuggled into input data
    port_status: unported
audits:
  premise_delta:
    discharged:
      - exact authored-support domain and southwest realization-functor signature
      - separation of comparator-free canonical context from the one-field authored raw table
      - pointwise component quantification and authored-support naturality constructor
      - exact dependent types of K2 route, authored comparison, canonical restriction, and relative predicate
      - finite nonempty endpoint-incidence witness and agreement predicate instance pair
    remaining:
      - F0c CartesianRegime and DisjunctionArtifact producer signature
      - K0 nondegenerate proper-fiber witness
      - K1 cartesian disjunction and generated regime
      - K2 route functors, pullback adjunctions, canonical mate, authored induced comparison, strict/lax MateCoherentRel pair, and orbit theorems
      - K3-K4 diagnostic base change, conditions, closure, and coherence
  certificate_provenance:
    discharged:
      - support tags come only from the input diagnostic TwoCell type
      - support packages come only from the input G-106 lift and twoTarget
      - endpoint fiber objects consume the explicit incidence equality
      - raw endpoint components consume AuthoredBC2CellPresentation.comparator directly
      - naturality is generated by the fixed discrete-category API rather than supplied as a field
      - the concrete support package is generated by G-101 transportAlong from the reviewed FiniteModel core package
      - the concrete square is generated by bcPresentationOfCospan and realizableSquareOf
    unresolved:
      - final K2 endpoint-incidence producer and both comparison producers
  proof_use:
    used:
      - square realization in all support source/target fiber indices
      - G-106 package and twoTarget in supportPackage
      - endpoint_eq in supportObject and endpoint-component IsHomLift
      - twoCellBase and authored comparator in toTransportData
      - every authored comparator in endpointComponentTotal and endpointAutomorphism
      - all pointwise components in authoredComparisonOfComponents
      - raw authored input only on AuthoredComparisonProducerSignature, not CanonicalMateRestrictionSignature
      - both producer results in mateCoherentRelEquation
    unused: []
  structure_field_escape: none-found for the F0 signature claim; no comparison, natural family, canonical mate, expected equality, or result bit is a field
  route_integrity: pass for F0 typing; K2 provenance remains explicitly unresolved
  target_fitting: none-found; support is a uniform type-level construction independent of comparator and fixture values
  vacuity: none-found; the concrete support has one authored 2-cell and the agreement predicate has true and false instances
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found; F0 claims signature typing only and leaves all K2 values and the public relation definition unproved
  validation_refs:
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/BCRelativeSchema.lean: pass, namespace audit 59 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/BCRelativeSchemaWitnesses.lean: pass, namespace audit 21 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct.lean: pass
    - lake build ResearchLean.AG.DoctrineFiberProduct.BCRelativeSchema: pass targeted module check
    - lake build ResearchLean.AG.DoctrineFiberProduct.BCRelativeSchemaWitnesses: pass targeted module check
    - direct acceptance-spine #print axioms audit: 30 declarations, each uses only propext/Classical.choice/Quot.sound
    - fixed repaired head 361bcb7d65688282177db48cef9305b3897418be: CI 7/7 pass
  review_refs:
    initial_fixed_head: 895f5c265954e1db7136c4cdf93d580dc104bfc8
    fixed_head: 361bcb7d65688282177db48cef9305b3897418be
    initial_integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4041#issuecomment-5365378113
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4041#issuecomment-5365424673
    verdicts:
      - Math A: No major findings
      - Math B: No major findings
      - Lean A: No major findings
      - Lean B: two minor documentation/reproducibility findings, both repaired and direct-response PASS
  blocking_findings: []
  next_obligation: F0c CartesianRegime and DisjunctionArtifact producer signature before K0-K4
```

### Cycle 5 acceptance spine

Cycle 5 の直接 axiom audit 対象は次の30 declaration に固定する。generic
equation scaffold は actual K2 producer または public `MateCoherentRel` として
数えず、endpoint incidence の一般放電も K2 residual に保つ。

- support context: `AuthoredSupportContext`,
  `AuthoredSupportContext.supportPackage`,
  `AuthoredSupportContext.supportObject`,
  `AuthoredSupportContext.Category`,
  `AuthoredSupportContext.supportFunctor`
- authored datum and G-106 bridge: `AuthoredBCDatumSquare`,
  `AuthoredBCDatumSquare.toTransportData`,
  `AuthoredBCDatumSquare.toDiagnosticInterpretation`,
  `AuthoredBCDatumSquare.ofInterpretation`
- raw endpoint family: `AuthoredBCDatumSquare.endpointComponentTotal`,
  `AuthoredBCDatumSquare.endpointComponentTotal_isHomLift`,
  `AuthoredBCDatumSquare.endpointComponent`,
  `AuthoredBCDatumSquare.endpointAutomorphism`,
  `AuthoredBCDatumSquare.endpointAutomorphism_app_val`
- K2 type surface: `AuthoredSupportRoute`, `AuthoredSupportRouteFamily`,
  `AuthoredComparisonComponents`, `authoredComparisonOfComponents`,
  `AuthoredComparisonProducerSignature`,
  `CanonicalMateRestrictionSignature`,
  `AuthoredSupportComparison.Agrees`,
  `AuthoredSupportComparison.not_agrees_of_app_ne`,
  `MateCoherentRelSignature`, `mateCoherentRelEquation`
- finite and predicate witnesses: `finiteAuthoredBCDatumSquare`,
  `finiteAuthoredSupport_nonempty`,
  `finiteAuthoredEndpointAutomorphism_component`,
  `finiteAuthoredEndpointAutomorphism_eq_identity`,
  `finiteAgreement_positive`, `finiteAgreement_negative`

### Cycle 5 fixed-head acceptance

初回 implementation head `895f5c265954e1db7136c4cdf93d580dc104bfc8` の4 lane
査読は、数学A/B・Lean Aが `No major findings`、Lean Bが新規API補題9件の
docstring欠落と、直接axiom audit 30宣言の完全な対象manifest欠落を Minor と判定した。
初回統合結果は
[#4041 review comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4041#issuecomment-5365378113)
に固定した。

修復 head `361bcb7d65688282177db48cef9305b3897418be` は、対象9宣言へ
docstringを追加し、上記acceptance spine 30宣言をreportへ明記した。差分はこの二つの
findingへの直接対応だけで、宣言の追加削除、statement、proof/definition body、値、
import、statusを変更していない。有資格なMath/Lean直接対応確認で両findingの解消と
対象外変更なしを確認し、修復headのCIは7/7 passとなった。最終統合判定は
[#4041 acceptance comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4041#issuecomment-5365424673)
に固定した。

この受理はF0b2bのsignature typingだけを `proof-obligation-discharged` とする。
`endpoint_eq` の一般生成、named route、pullback reindexing、adjunction、raw comparatorを
実消費するauthored comparison、canonical mate、cleavage independence、closed
`MateCoherentRel`、strict/lax正負対、orbit theoremはK1/K2に未放電である。F0c、
K0--K4、Formal port、G-110全体も未完了であり、次cycleはF0cとする。

### Cycle 4 — F0b2a finite-code square pasting and authored 2-cell raw schema

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 4
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 1f096739106d22c21ffa49fc6c2bd0c0e6fb940b
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 3 merge update and revised GOAL strategy F0
  proof_dag_predecessors:
    - Cycle 2 F0a finite-code cartesian schema, PR 4038 merge 5dd7bbb297c50498e6cff706258a5237381df9d4
    - Cycle 3 F0b1 BC presentation and condition schema, PR 4039 merge 1f096739106d22c21ffa49fc6c2bd0c0e6fb940b
    - G-106 AdmissibleTransportData authored comparator table
  proof_obligation: generate strictly composable horizontal and vertical pairs of finite-code pullback squares, an outer BCPresentation, semantic pasting pullback theorems, and realization compatibility without identifying independently enumerated northwest pullback codes; fix the one-field AuthoredBC2CellPresentation raw table without supplying a natural family, canonical mate, or expected equality
  selection_reason: pasting closure is the remaining finite-code constructor required before the other F0 signatures; the authored raw table can be fixed independently, while the authored-support and MateCoherentRel signatures remain the immediately following F0b2b obligation and must be fixed before K0 without supplying direct or canonical comparisons as abstract fields or arguments
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingSchema.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingSchemaWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - arbitrary semantic squares or IsPullback certificates could be accepted as pasting input
    - horizontal or vertical adjacency could be asserted by caller-supplied semantic equality rather than generated at typed code endpoints
    - the iterated and outer canonical pullback codes could be falsely identified by definitional equality
    - a comparison isomorphism could become an authored input field
    - the authored 2-cell schema could store a natural family, canonical mate, expected equality, or result bit
    - canonical three-arrow seeds could silently narrow the previously accepted BCPresentation class through their generated compatible-point tables
  unchecked: []
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: added direction-indexed horizontal and vertical three-arrow seeds; generated both adjacent component presentations, their shared edge, outer cospan, and outer BCPresentation; proved literal semantic pasting is a pullback in both directions; generated the unique northwest isomorphism to the independently re-enumerated outer pullback, explicitly reindexed the literal paste, and proved equality of the complete named semantic inputs; defined strict composability on existing presentation pairs and proved seed coverage in both directions; proved every existing BCPresentation normalizes to the canonical compatible-point producer; and fixed AuthoredBC2CellPresentation with exactly one G-106-shaped PackageFiberAut assignment table
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingSchema.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCPastingSchemaWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - compatiblePointCodeOfCospan_wellFormed
    - bcPresentationOfCospan_normalizes
    - HorizontalBCPastingData.leftPresentation
    - HorizontalBCPastingData.rightPresentation
    - HorizontalBCPastingData.nestedSquare_isPullback
    - HorizontalBCPastingData.pasteNorthwestIso_hom_left
    - HorizontalBCPastingData.pasteNorthwestIso_hom_top
    - HorizontalBCPastingData.realization_eq_reindexNested
    - VerticalBCPastingData.upperPresentation
    - VerticalBCPastingData.lowerPresentation
    - VerticalBCPastingData.nestedSquare_isPullback
    - VerticalBCPastingData.pasteNorthwestIso_hom_left
    - VerticalBCPastingData.pasteNorthwestIso_hom_top
    - VerticalBCPastingData.realization_eq_reindexNested
    - strictHorizontalComposable_coverage
    - strictVerticalComposable_coverage
    - toSemanticBC_pastePresentation_eq
    - AuthoredBC2CellPresentation.ofTransportData
    - finiteHorizontalBCPasting_sourceCard
    - finiteVerticalBCPasting_sourceCard
    - finiteAuthoredBC2CellPresentation_comparator
  claim_mapping:
    theorem_names:
      - BCPastingInput
      - pastePresentation
      - nestedPasteSquare
      - nestedPasteSquare_isPullback
      - StrictHorizontalComposable
      - StrictVerticalComposable
      - normalizedNestedPasteSemanticInput
      - toSemanticBC_pastePresentation_eq
      - HorizontalBCPastingData.pasteNorthwestIso
      - VerticalBCPastingData.pasteNorthwestIso
      - AuthoredBC2CellPresentation
    source_labels:
      - target theorem schema invariant (s5) pasting closure
      - target proof strategy F0 schema typing
      - target theorem (C) authored comparator raw-schema boundary
    conjuncts:
      - a horizontal input has exactly three typed finite-code arrows and one shared pre-base-change diagnostic presentation
      - the right pullback is generated first and its first projection is definitionally the shared vertical edge used by the generated left pullback
      - a vertical input has exactly three typed finite-code arrows and one shared pre-base-change diagnostic presentation
      - the lower pullback is generated first and its second projection is definitionally the shared horizontal edge used by the generated upper pullback
      - pastePresentation generates the outer finite cospan by Cart presentation composition and then applies the existing BCPresentation producer
      - the compatible-point table is generated and validated; bcPresentationOfCospan_normalizes proves this canonical table does not remove existing validated presentations
      - pair-level strict composability names exactly the two shared code objects, shared typed edge, and shared pre-BC diagnostic; every such existing pair is covered by a three-arrow seed
      - horizontal and vertical literal semantic pastes are pullbacks by IsPullback.paste_horiz and IsPullback.paste_vert
      - the nested and outer pullbacks share the exact outer cospan but may have different finite northwest enumerations
      - the northwest comparison is generated by IsPullback.isoIsPullback, and its hom commutes with both projections
      - reindexNorthwest transports only the two northwest incident arrows, and toSemanticBC_pastePresentation_eq identifies the complete outer semantic input with the normalized literal paste by equality
      - finite noninvertible examples exercise horizontal and vertical pasting and compute a four-cell outer source
      - AuthoredBC2CellPresentation has exactly one comparator field indexed by finite G-106 2-cells and support packages
      - ofTransportData reuses the reviewed G-106 comparator table definitionally
      - no natural family, canonical/direct comparison, expected equality, mate relation, regime, or result bit is stored
    undischarged_assumptions: []
    acceptance_point: finite-code pasting is generated from typed arrows and tested by categorical universality, not certified by inputs; the pair-level predicates and coverage theorems prevent narrowing to chosen seeds; the canonical northwest isomorphism forced by independent finite re-enumeration is consumed by an explicit reindexing operation and an equality-level named-semantic-input theorem; canonical compatible points preserve the full existing BCPresentation class; and the authored 2-cell raw boundary is fixed without inventing comparison fields
    port_status: unported
audits:
  premise_delta:
    discharged:
      - finite-code horizontal and vertical pastePresentation constructors
      - equality-level realization compatibility after explicit canonical northwest reindexing
      - canonical compatible-point generation, single-presentation normalization, and pair-level strict-composability coverage
      - one-field AuthoredBC2CellPresentation raw schema
    remaining:
      - F0b2b authored-support domain, generated-family interface, and MateCoherentRel signature fixed before K0 without caller-supplied comparison fields
      - F0c CartesianRegime and DisjunctionArtifact producer signature
      - K0 nondegenerate proper-fiber witness
      - K1-K4 theorem obligations, including H_bc pasting closure and mate/diagnostic-comparison pasting coherence
  certificate_provenance:
    discharged:
      - each component PullbackPresentation is generated from a typed finite cospan
      - nestedSquare_isPullback invokes the two component realization theorems and Mathlib pasting
      - pasteNorthwestIso is generated from the nested and outer IsPullback proofs
      - toSemanticBC_pastePresentation_eq consumes that generated isomorphism and does not accept a comparison or equality argument
      - neither BCPastingInput variant has a square, IsPullback proof, comparison isomorphism, or equality field
      - AuthoredBC2CellPresentation.ofTransportData copies only data.comparator
    unresolved: []
  proof_use:
    used:
      - all three horizontal arrows in the two component pullbacks, bottom composition, outer cospan, and pasted universality proof
      - all three vertical arrows in the two component pullbacks, right composition, outer cospan, and pasted universality proof
      - both generated component pullback proofs in each Mathlib pasting theorem
      - nested and outer IsPullback proofs in the unique northwest comparison and its two projection equations
      - both projection equations in the reindexed square equality and the complete BCSemanticInput equality
      - shared-object, shared-edge, and diagnostic equalities in both existing-pair seed coverage theorems
      - all seven compatible-point equations in the canonical well-formedness proof, and the five field-determining equations in the normalization theorem
      - G-106 comparator values in AuthoredBC2CellPresentation.ofTransportData and its concrete witness
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/BCPastingSchema.lean: pass, namespace audit 137 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/BCPastingSchemaWitnesses.lean: pass, namespace audit 17 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct.lean: pass
    - lake build ResearchLean.AG.DoctrineFiberProduct.BCPastingSchema: pass targeted module check
    - lake build ResearchLean.AG.DoctrineFiberProduct.BCPastingSchemaWitnesses: pass targeted module check
    - direct #print axioms on all 66 Cycle 4 acceptance-spine declarations: only propext, Classical.choice, and Quot.sound
    - fixed implementation head 41961b616a76c34b01402fb533a9bbcabc004a3c: CI 7/7 pass
  review_refs:
    fixed_head: 41961b616a76c34b01402fb533a9bbcabc004a3c
    integrated_comment: https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4040#issuecomment-5364983129
    verdicts:
      - Math A: No major findings
      - Math B: No major findings
      - Lean A: No major findings
      - Lean B: No major findings
  blocking_findings: []
  next_obligation: F0b2b authored-support/MateCoherentRel signature typing before F0c and K0-K4
```

### Cycle 3 — F0b1 basic BC presentation and condition schema typing

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 3
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: 5dd7bbb297c50498e6cff706258a5237381df9d4
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 Cycle 2 merge update comment 5363876694 and revised GOAL strategy F0
  proof_dag_predecessors:
    - Cycle 2 F0a finite-code cartesian schema, PR 4038 merge 5dd7bbb297c50498e6cff706258a5237381df9d4
    - G-106 FiniteTransportPresentation and AdmissibleTransportData
  proof_obligation: fix an elaborating basic BCPresentation whose authored groups are a typed finite-code cospan, a finite compatible-point table, and a pre-base-change G-106 diagnostic presentation; generate the semantic pullback square and selected-point equations; and enumerate the complete four-constructor BC condition vocabulary over all finite cartesian, compatible-point, and diagnostic fields
  selection_reason: the fixed GOAL explicitly permits F0 to be split; the basic BC input boundary and evaluator can be checked independently before adding pasting, authored 2-cell, and regime-producer signatures
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/BCSchema.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCSchemaWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - the pullback square or IsPullback proof could become a caller-authored field
    - the compatible-point table could be retained but not consumed by validation or realization soundness
    - semantic G-106 package values could leak into the finite condition projection language
    - a target-result bit, regime, mate, or transported diagnostic could be smuggled into raw code
    - empty diagnostic geometry could make every structural diagnostic check vacuous
    - every semantic square could be silently accepted as realizable
  unchecked:
    - fixed-head four-lane math-lean-review after the computability and operand-sort repair
    - whether the F0b2 pasting and authored-2-cell layer requires an auxiliary typed square category
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: fixed the basic BC raw/validated boundary, generated semantic pullback realization and provenance, an executable compatible-source rank/unrank producer, exhaustive first-order serialization of the pre-BC G-106 finite geometry, the fixed four-constructor BC condition language with a shared natural operand sort, and concrete positive, negative, nonempty-diagnostic, and non-realizable semantic-square witnesses
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/BCSchema.lean
    - ResearchLean/AG/DoctrineFiberProduct/BCSchemaWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - BCRawCode.checkWellFormed_eq_true_iff
    - toSemanticBC_authored_point_table_sound
    - toSemanticBC_sound
    - finiteConstantBCDiagnosticInterpretation
    - finiteConstantBC_generated_leg_source_cards
    - finiteConstantBC_generated_top_source_point_mem
    - finiteConstantBC_bottom_point_eq_compatible_first
    - evalBCCondition_firstAtomMapIdentity_bridge
    - evalBCCondition_firstAtomMapIdentity_replacement_invariant
    - finiteBCDiagnostic_vertices_nonempty
    - finiteBCDiagnostic_twoCells_nonempty
    - finiteBCDiagnostic_threeFaces_nonempty
    - finiteBadBCRawCode_check_false
    - finiteNonPullbackSquare_not_isPullback
    - finiteNonPullbackBCInput_has_no_realizableSquare
  claim_mapping:
    theorem_names:
      - FiniteDiagnosticPresentation
      - CartCospanPresentation
      - BCPresentation
      - BCSemanticInput
      - BCDiagnosticInterpretation
      - decodeBCSquare
      - toSemanticBC
      - toSemanticBC_sound
      - RealizableSquare
      - BCProjection
      - BCConditionSyntax
      - evalBCCondition
    source_labels:
      - target theorem (B), schema invariants (s1)-(s6)
      - target proof strategy F0 schema typing
      - G-106 pre-base-change diagnostic presentation
    conjuncts:
      - BCRawCode has exactly the typed cospan, compatible-point table, and finite pre-BC diagnostic-presentation groups
      - BCPresentation is the validated layer and its Boolean checker is exact
      - the pullback object, projections, square commutativity, and IsPullback proof are generated from the cospan
      - the authored compatible-point table is consumed by validation and agrees componentwise with decoded selected sources and images
      - BCSemanticInput has only the square, compatible points, and underlying pre-BC diagnostic geometry, with no authored enumeration, package interpretation, regime, condition result, mate, or transported diagnostic
      - BCDiagnosticInterpretation places G-106 AdmissibleTransportData in a separate dependent semantic-input layer
      - every finite cartesian field of all four square legs and every compatible-point and G-106 combinatorial component is represented in BCProjection
      - all cartesian derived sets and finite universals are available for all four generated legs
      - cartesian natural fields share the BC natural operand sort, so generated-leg membership and cross-group equality are well typed
      - the compatible-pair source is explicitly enumerated and the complete four-leg evaluator is executable rather than a noncomputable Bool specification
      - semantic G-106 interpretation data is absent from presentation fields and projection evaluation
      - BCNamedConstant contains no natural/source-index value constant
      - BCConditionSyntax has exactly field equality, membership, finite universal equality, and conjunction constructors
      - the selected finite universal has a semantic bridge and semantic-replacement invariance theorem
      - nonempty 0/1/2/3-cell diagnostic data and oriented pasting faces exercise the structural serialization
      - malformed point tables are rejected and identity/nonidentity Atom conditions both fire
      - a concrete commutative non-pullback semantic input has neither presentation provenance nor a RealizableSquare certificate
    undischarged_assumptions: []
    acceptance_point: the finite-only basic BC presentation generates rather than stores its pullback conclusion; package interpretation is a separate dependent semantic input; the compatible table is tied to decoded semantics; explicit compatible-pair enumeration makes the four-leg evaluator executable; the shared natural operand sort lets membership and equality consume generated Cart fields; the evaluator sees the complete authored finite combinatorics but has neither semantic package values nor a fixture source-value constant; positive and negative validators and realization boundaries close the nonvacuity audit; and no F0b2 pasting, authored-2-cell, or regime claim is included
    port_status: unported
audits:
  premise_delta:
    discharged:
      - basic finite-code BCPresentation and named BCSemanticInput boundary
      - separate dependent BCDiagnosticInterpretation package layer
      - generated categorical pullback square and selected-point soundness
      - complete four-leg basic BC condition field vocabulary and evaluator
      - executable compatible-source enumeration and shared natural relation operands
      - finite diagnostic presentation capabilities and nonempty structural witness
      - basic realization provenance and a semantic non-realizability boundary witness
    remaining:
      - F0b2 pastePresentation and admissible-square pasting closure
      - F0b2 AuthoredBC2CellPresentation and MateCoherentRel typing
      - F0c CartesianRegime and DisjunctionArtifact producer signature
      - K0 nondegenerate proper-fiber witness
      - K1-K4 theorem obligations
  certificate_provenance:
    discharged:
      - BCRawCode validation consumes the authored compatible-point table against the cospan
      - BCRawCode and BCSemanticInput contain no AdmissibleTransportData field; finiteConstantBCDiagnosticInterpretation inhabits the separate dependent package layer
      - decodeBCSquare invokes the F0a pullback producer; BCRawCode stores no pullback object or proof
      - toSemanticBC_sound obtains IsPullback from pullbackPresentation_isPullback
      - realizableSquareOf is generated from a validated presentation
      - finiteNonPullbackBCInput_has_no_realizableSquare rules out a generic certificate wrapper for an invalid square
    unresolved: []
  proof_use:
    used:
      - all seven compatible-point equalities in validation; the first five are consumed directly by the authored-table soundness theorem, while the final two redundant image/base equalities remain checked by the validator
      - both typed cospan legs in generated pullback object, projections, and IsPullback proof
      - all four square legs in BCProjection, BCDerivedSet, and BCUniversalEquality; generated top/left source-card projections fire, generated top source membership executes to true, and a Cart/compatible-point natural equality executes to true
      - every finite diagnostic field family in a listed projection or structural universal
      - finite support/table data in the Atom-identity semantic bridge
      - collapse and constant source maps in the non-pullback contradiction
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/Schema.lean: pass, namespace audit 498 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/SchemaWitnesses.lean: pass, namespace audit 46 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/BCSchema.lean: pass, namespace audit 506 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/BCSchemaWitnesses.lean: pass, namespace audit 61 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct.lean: pass
    - executable #eval of generated-top source membership and Cart/compatible-point equality: true, true
    - lake build ResearchLean.AG.DoctrineFiberProduct.BCSchema: pass targeted module check
    - lake build ResearchLean.AG.DoctrineFiberProduct.BCSchemaWitnesses: pass targeted module check
    - lake build ResearchLean.AG.DoctrineFiberProduct: pass targeted umbrella module check
    - direct #print axioms on all 92 F0b1 acceptance-spine declarations plus 14 directly changed F0a producer declarations: only standard axioms
    - placeholder, hidden/BiDi Unicode, privacy, import-direction, wiring, and git diff checks: pass
  blocking_findings: []
  next_obligation: F0b2 pasting, authored 2-cell, mate-relation, and regime-producer signature typing
```

### Cycle 3 initial fixed-head review and response

初回 fixed head `4c942ab188072de3e227568bf559df9e1b33e178` の標準
review-pr / math-lean-review 監査は
[#4039 comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4039#issuecomment-5364183765)
に固定した。4 lane の統合判定は `Needs changes` で、次の3点を検出した。

1. `AdmissibleTransportData` を `BCRawCode` / `BCPresentation` に格納し、
   finite presentation と package semantic interpretation の二層を混同した。
2. `BCNamedConstant.zero` が authored source index との fixture-dependent
   等式原子を許した。
3. `BCSquareLeg` が authored cospan の2脚しか列挙せず、生成された pullback
   脚 `top / left` を condition projection から落とした。

修正では `BCRawCode.diagnostic` を `FiniteDiagnosticPresentation` のみにし、
`BCSemanticInput.diagnostic` は underlying `FiniteTransportPresentation`、
G-106 package 値は別 dependent structure `BCDiagnosticInterpretation` に分離した。
natural/source-index 定数は全廃し、`BCSquareLeg` は `top / left / right /
bottom` の4脚を列挙する。さらに全 `CartDerivedSet` /
`CartUniversalEquality` を各脚へ埋め込み、生成 `top / left` の source-card
projection が具体的4元 pullback codeを読む witness を追加した。signature と
declaration を変更したため、修正 head は直接対応ではなく4 lane 正式再査読を要する。

### Cycle 3 second fixed-head review and response

第2 fixed head `b9f278dd292e2a4a03a60628cf8bfe509aadfb37` の4 lane 再査読は
[#4039 rereview comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4039#issuecomment-5364364812)
に固定した。旧3 finding の解消を確認した一方、統合判定は再び
`Needs changes` となり、次の2点を検出した。

1. Cart の自然数 projection が `BCFieldKind.cart .natural`、membership と
   compatible/diagnostic projection が `BCFieldKind.natural` に分かれ、生成
   `top / left` の `sourcePoint ∈ sourceCells` と cross-group equality が
   型付け不能だった。
2. `compatibleSourceEquiv` が `Fintype.equivFin` / classical choice を使ったため、
   `bcCartPresentation` から `evalBCCondition` までの complete evaluator chain が
   `noncomputable` となり、有限 checker の操作化を満たさなかった。

第2修正は `BCFieldKind.ofCart` で Cart natural を共通 BC natural sort に写し、
`cartFieldValueToBC` で値を型付き移送する。さらに左右 source の canonical list
product を compatibility equality で `filterMap` し、nodup / complete 証明から
list rank/unrank equivalence `compatibleSourceEquiv` を計算可能に再構成した。
pullback code と全四脚 evaluator から `noncomputable` を除去し、生成 top の
source membership と Cart/compatible-point equality がどちらも実際の `#eval` で
`true` を返すことを確認した。この signature repair も4 lane 正式再査読を要する。

### Cycle 3 final fixed-head acceptance

最終 fixed head `73ff2dfefb24b182cb8b940ab2abd260989f9615` は、4 lane の
fresh fixed-head 査読ですべて `No major findings`、CI 7/7 pass となった。
統合判定は
[#4039 acceptance comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4039#issuecomment-5364567800)
に固定した。PR #4039 は merge commit
`1f096739106d22c21ffa49fc6c2bd0c0e6fb940b` として main に統合済みである。
この受理は F0b1 のみを `proof-obligation-discharged` とし、F0b2 / F0c /
K0–K4 または G-110 全体の完了を主張しない。

### Cycle 4 acceptance spine

Cycle 4 の直接 axiom audit 対象は次の66 declaration に固定する。生成された
northwest isomorphism は semantic output であり、pasting input または authored
raw field ではない。

- semantic reindexing: `ExtInstSquare.ext_heterogeneous`,
  `ExtInstSquare.reindexNorthwest`,
  `compatiblePointSemanticInputOfSquare_heq`,
  `BCSemanticInput.ext_heterogeneous`
- canonical BC point producer: `compatiblePointCodeOfCospan`,
  `compatiblePointCodeOfCospan_wellFormed`, `bcPresentationOfCospan`,
  `bcPresentationOfCospan_normalizes`
- input types: `HorizontalBCPastingData`, `VerticalBCPastingData`,
  `BCPastingInput`, `StrictHorizontalComposable`, `StrictVerticalComposable`,
  `AuthoredBC2CellPresentation`
- horizontal producer: `HorizontalBCPastingData.rightPullback`,
  `HorizontalBCPastingData.leftPullback`,
  `HorizontalBCPastingData.leftPresentation`,
  `HorizontalBCPastingData.rightPresentation`,
  `HorizontalBCPastingData.outerCospan`,
  `HorizontalBCPastingData.pastePresentation`,
  `HorizontalBCPastingData.nestedSquare`,
  `HorizontalBCPastingData.nestedSquare_isPullback`
- vertical producer: `VerticalBCPastingData.lowerPullback`,
  `VerticalBCPastingData.upperPullback`,
  `VerticalBCPastingData.upperPresentation`,
  `VerticalBCPastingData.lowerPresentation`,
  `VerticalBCPastingData.outerCospan`,
  `VerticalBCPastingData.pastePresentation`,
  `VerticalBCPastingData.nestedSquare`,
  `VerticalBCPastingData.nestedSquare_isPullback`
- direction-indexed calculus: `pastePresentation`, `nestedPasteSquare`,
  `nestedPasteSquare_isPullback`,
  `HorizontalBCPastingData.strictComposable`,
  `VerticalBCPastingData.strictComposable`,
  `strictHorizontalComposable_coverage`,
  `strictVerticalComposable_coverage`
- realization comparison: `HorizontalBCPastingData.pasteNorthwestIso`,
  `HorizontalBCPastingData.pasteNorthwestIso_hom_left`,
  `HorizontalBCPastingData.pasteNorthwestIso_hom_top`,
  `HorizontalBCPastingData.realization_eq_reindexNested`,
  `VerticalBCPastingData.pasteNorthwestIso`,
  `VerticalBCPastingData.pasteNorthwestIso_hom_left`,
  `VerticalBCPastingData.pasteNorthwestIso_hom_top`,
  `VerticalBCPastingData.realization_eq_reindexNested`,
  `normalizedNestedPasteSquare`, `normalizedNestedPasteSemanticInput`,
  `toSemanticBC_pastePresentation_eq`
- authored raw table: `AuthoredBC2CellPresentation.ofTransportData`,
  `AuthoredBC2CellPresentation.ofTransportData_comparator`
- finite witnesses: `finiteHorizontalBCPastingData`,
  `finiteHorizontalBCPasting_diagnostic_shared`,
  `finiteHorizontalBCPasting_sourceCard`,
  `finiteHorizontalBCPasting_isPullback`,
  `finiteHorizontalBCPasting_strictComposable`,
  `finiteHorizontalBCPasting_realization_eq`,
  `finiteVerticalBCPastingData`,
  `finiteVerticalBCPasting_diagnostic_shared`,
  `finiteVerticalBCPasting_sourceCard`,
  `finiteVerticalBCPasting_isPullback`,
  `finiteVerticalBCPasting_strictComposable`,
  `finiteVerticalBCPasting_realization_eq`,
  `finiteConstantBC_not_strictHorizontal_self`,
  `finiteConstantBC_not_strictVertical_self`,
  `finiteAuthoredBC2CellPresentation`,
  `finiteAuthoredBC2CellPresentation_comparator`

### Cycle 4 initial fixed-head review and response

初回 fixed head `dd020ae424b39eb19babc7b7641eb075d39e2e45` の4 lane 査読は
[#4040 review comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4040#issuecomment-5364845275)
に固定した。pasting の向き、Mathlib の普遍性証明、northwest isomorphism の
provenance、一フィールド authored schema、有限 witness は通過したが、固定 GOAL
に対する次の anti-weakening gap を検出した。

1. 初回実装は outer と nested paste の northwest object を canonical isomorphism と
   二つの射影式で比較するだけで、s5 が要求する realization compatibility の equality
   を与えていなかった。
2. 三射 seed が生成する隣接 presentation のみを扱い、すでに受理済みの任意の
   strict-composable BCPresentation pair を seed が被覆する定理を持たなかった。
3. F0b2b の authored-support / MateCoherentRel signature を K2 producer 実装後まで
   待つ記述は、K0--K4 前に relative predicate の型を固定する GOAL の順序を満たさない。

修正では canonical northwest isomorphism の inverse で literal nested square の
二本の northwest incident arrow だけを明示的に reindex し、outer
`BCSemanticInput` と、square・compatible points・diagnostic のすべてを含む
equality `toSemanticBC_pastePresentation_eq` を証明した。また existing-pair の
`StrictHorizontalComposable` / `StrictVerticalComposable` を定義し、共有 object、
共有 typed edge、共有 diagnostic だけから三射 seed を復元して両 component が元の
presentation に等しい coverage theorem を証明した。F0b2b は K0 より前の次 cycle
として明記し、比較射や期待等式を field / argument として先取りしない。

### Cycle 4 final fixed-head acceptance

修正 implementation head `41961b616a76c34b01402fb533a9bbcabc004a3c` は、旧判定を
流用しない4 lane の fresh fixed-head 査読ですべて `No major findings`、CI
7/7 pass となった。統合判定は
[#4040 acceptance comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4040#issuecomment-5364983129)
に固定した。査読は reindex 後の equality が nested paste と二つの pullback
普遍性を実消費し、outer decoder の別名化ではないこと、pair-level predicate が
任意の code-level strict pair を被覆すること、typed-edge `HEq` が semantic
certificate を運ばないこと、正負 witness がともに発火することを独立に確認した。

この受理は F0b2a のみを `proof-obligation-discharged` とする。F0b2b の
authored-support domain・generated-family interface・`MateCoherentRel` signature、
F0c、K0--K4、Formal port、G-110 全体は未完了であり、F0b2b を次 cycle とする。

### Cycle 2 — F0a finite-code cartesian schema typing

```yaml
ledger_type: target_cycle_result
goal: G-110-aat-doctrine-fiber-product
cycle: 2
goal_blob_sha: 4b497352e586ed85c36fbcf4ea80730415f70040
goal_sha256: e6891d264ae8446341ee5b4fa4e73542b341c6551de70cb65cfda995a7b72e34
base_oid: ea6eb80d3f9388f0eeeb550370664ae1a6b3e0b0
tracking_issue: 4034
report_path: research/reports/G-110-aat-doctrine-fiber-product.md
selection:
  proof_state_ref: Issue 4034 fixed-head update comment 5363348621 and revised GOAL strategy F0
  proof_dag_predecessors:
    - G-101 AtomFoundation exact doctrine and pointed morphism API
    - PR 4037 finite-code schema invariants s1-s6
  proof_obligation: fix an elaborating finite-code bottom schema whose Source varies by presentation, together with raw/validated CartPresentation, named CartSemanticInput realization and soundness, RealizableHom provenance, the complete CartConditionSyntax, and id/comp/pullback closure signatures with realization compatibility
  selection_reason: every F0b and K0-K4 node consumes this bottom realization image; fixing the pullback-closed cartesian spine directly removes the former fixed-two-source blocker without bundling the independent BC diagnostic and regime layer
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/Schema.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  risks:
    - semantic payload or conclusion certificates could escape into the four authored raw fields
    - a fixed fixture Source could reintroduce the Cycle 1 pullback-closure defect
    - sourceMap could be silently restricted to equivalences and lose mandatory noninvertible inputs
    - finite-support Atom permutations could be asserted rather than decoded with inverse data
    - pullback closure could be equality-shaped data instead of an IsPullback theorem
    - condition syntax could add a target-result predicate or fixture constant
  unchecked:
    - exact signature supported by the current AtomFoundation category API
    - whether id/comp/pullback realization compatibility can all be proved in this cycle without changing s1-s6
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: fixed an elaborating four-field finite-code realization spine with presentation-varying first-order Source, a quotient category of typed code presentations and its ExtInst realization functor, decoded finite/cofinite Atom predicates and finite-support permutations, arbitrary source maps, raw/validated separation, semantic soundness and provenance, id/comp/pullback constructors, and a pullback realization theorem against every semantic ExtInst cone
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/Schema.lean
    - ResearchLean/AG/DoctrineFiberProduct/SchemaWitnesses.lean
    - ResearchLean/AG/DoctrineFiberProduct.lean
  evidence:
    - pullbackPresentation_isPullback
    - finiteCodeCartRealization_pullback_isPullback
    - finiteModelDoctrineRealizationIso
    - toSemanticCart_sound
    - toSemanticCart_idPresentation_hom
    - toSemanticCart_compPresentation_hom
    - finiteConstantPresentation_not_isIso
    - finiteBadPointRawCode_check_false
    - infiniteIdentityInput_has_no_realizableHom
    - finiteConstantPullback_sourceCard
    - finiteConstantPullback_isPullback
    - evalCartCondition_atomMapIdentity_bridge
    - evalCartCondition_atomMapIdentity_replacement_invariant
  claim_mapping:
    theorem_names:
      - FiniteDoctrineCode.toDoctrine
      - decodeCartDoctrineHom
      - toSemanticCart_sound
      - finiteCodeCartRealization
      - finiteCodeCartRealization_pullback_isPullback
      - pullbackPresentation_isPullback
      - CartConditionSyntax
      - evalCartCondition
      - finiteConstantPresentation_not_isIso
      - finiteModelDoctrineRealizationIso
    source_labels:
      - target theorem (B), schema invariants (s1)-(s6)
      - target proof strategy F0 schema typing
      - presentation closure constructors id / comp / pullback
    conjuncts:
      - presentation-owned finite Source and finite doctrine/instance codes
      - four authored raw fields with decidable well-formedness and validated decoder
      - named semantic input and realization provenance with semantic-law soundness
      - finite-support Atom permutation identity, inverse, and composition closure
      - arbitrary noninvertible source maps remain in the realization image
      - identity and composition realization compatibility
      - typed code presentations modulo decoded equality form a category and realization is a functor to ExtInst_U
      - pullback source re-enumeration and projection presentations remain finite-code
      - generated semantic projection square is an ExtInst categorical pullback for arbitrary semantic cones
      - the reviewed FiniteModel extraction doctrine lies in the object realization image up to Doct_U isomorphism
      - Holds, WellFormed/checker, and RealizableHom provenance have explicit positive and negative finite/infinite instances
      - fixed four-constructor Cart condition syntax over the completely enumerated cartesian projections, constants, relations, and derived finite sets
    undischarged_assumptions: []
    acceptance_point: every selected F0a artifact is generated from the four raw fields; typed composability is explicit in FiniteCodeCartCategory and finiteCodeCartRealization rather than inferred from independently chosen semantic endpoint presentations; neither semantic morphisms nor pullback proofs nor condition bits are caller-authored; positive/negative validator and realization instances close the vacuity audit; and the finite constant witness proves that sourceMap was not narrowed to equivalences
    port_status: unported
audits:
  premise_delta:
    discharged:
      - finite-code Cart presentation and semantic realization bridge
      - realization soundness for normalize_eq, extraction_iff, and source_eq
      - id / comp closure of the typed finite-code quotient category and functorial semantic realization
      - pullbackPresentation output remains in the code family and realizes to an ExtInst pullback against arbitrary semantic cones
      - fixed CartConditionSyntax signature
    remaining:
      - F0b BC presentation, BC condition language, authored 2-cell, and regime signatures
      - K0 nondegenerate proper-fiber witness
      - K1-K4 theorem obligations
  certificate_provenance:
    discharged:
      - validated well-formedness is finite-table data consumed by decodeCartDoctrineHom
      - pullback object and projections are generated by pullbackPresentation from the cospan
      - IsPullback is proved by pullbackSemanticLift and uniqueness, not stored in PullbackPresentation
      - finiteConstantPresentation_check_true and finiteBadPointRawCode_check_false form the validator instance pair
      - finiteConstantRealizableHom and infiniteIdentityInput_has_no_realizableHom form the realization-certificate boundary pair
      - finiteModelDoctrineRealizationIso derives both exact comparison arrows from the finite source equivalence
    unresolved: []
  proof_use:
    used:
      - both cospan source-map equations in CompatibleSource and semantic cone lift construction
      - both cospan atomEquiv components in the second projection and cone factorization
      - normalize_eq, extraction_eq, and source_eq in decoder soundness and pullback realization
      - finite-support support/table data in permutation decoding and condition evaluation
      - quotient-category composition laws consume the id/comp semantic compatibility theorems
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/Schema.lean: pass, namespace audit 492 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct/SchemaWitnesses.lean: pass, namespace audit 46 declarations and standard axioms only
    - lake env lean ResearchLean/AG/DoctrineFiberProduct.lean: pass
    - lake build ResearchLean.AG.DoctrineFiberProduct: pass targeted module check
    - direct #print axioms on all 87 acceptance-spine declarations: only propext, Classical.choice, and Quot.sound
    - placeholder, hidden/BiDi Unicode, privacy, import-direction, and git diff checks: pass
  blocking_findings: []
  next_obligation: F0b BC presentation, authored 2-cell, condition-language, and CartesianRegime typing
```

Cycle 1 の旧 fixed-card head に対する `goal defect` と PR #4035 の rejected
artifact は tracking Issue #4034 を正本とする。PR #4037 でカードが改訂されたため、
旧 fixed-two-source schema は本 cycle の受理証拠として再利用しない。

### Initial fixed-head review and response

初回 fixed head `3a3e60a8` の標準 review-pr / math-lean-review 監査は
[#4038 comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4038#issuecomment-5363718027)
に固定した。4 lane の統合判定は `Needs changes` で、(i) code endpoint を
定義的に共有する constructor の閉性を semantic realization image 全体の閉性と
過大表示しないこと、(ii) `Holds` / `WellFormed` / `RealizableHom` の正負
instance を固定すること、の2点を是正対象とした。

修正後は `FiniteCodeCartCategory` と `finiteCodeCartRealization` により typed
code calculus と semantic interpretation を型で分離した。pullback の普遍性は
`finiteCodeCartRealization_pullback_isPullback` として任意 semantic cone 上に
維持する。あわせて predicate、validator、realization certificate の正負対と、
既存 `FiniteModel.extractionDoctrine` の `Doct_U` 同型
`finiteModelDoctrineRealizationIso` を追加した。修正 fixed head
`a486f2f105ac097c287abf1fcac18c267fde1bea` は4 lane の独立再査読で全 lane
`No major findings`、CI 7/7 pass となり、統合監査を
[#4038 acceptance comment](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4038#issuecomment-5363868928)
に固定した。PR #4038 は merge commit
`5dd7bbb297c50498e6cff706258a5237381df9d4` として main に統合済みである。

## F0b1 acceptance spine

F0b1 の直接 axiom audit 対象は次の92 declaration に固定する。semantic package
layerの `BCDiagnosticInterpretation.data` は presentation / decoded square と
別の dependent input であり、condition projection/evaluator の対象には含めない。

- raw/validated and semantic boundary: `FiniteDiagnosticPresentation`,
  `BCDiagnosticInterpretation`, `CartCospanPresentation`, `CompatiblePointCode`,
  `CompatiblePointCode.WellFormed`, `CompatiblePointCode.checkWellFormed`,
  `CompatiblePointCode.checkWellFormed_eq_true_iff`, `BCRawCode`,
  `BCRawCode.WellFormed`, `BCRawCode.checkWellFormed`,
  `BCRawCode.checkWellFormed_eq_true_iff`, `ValidatedBCCode`,
  `BCPresentation`, `ExtInstSquare`, `CompatiblePointSemanticInput`,
  `compatiblePointSemanticInputOfSquare`, `BCSemanticInput`, `decodeBCSquare`,
  `toSemanticBC`, `toSemanticBC_authored_point_table_sound`,
  `toSemanticBC_sound`, `RealizableSquare`, `realizableSquareOf`
- diagnostic serialization: `DiagnosticEdgeValue`,
  `DiagnosticWhiskeredFaceValue`, `finiteListIndex`, `diagnosticPathValue`,
  `diagnosticWhiskeredFaceValue`, `diagnosticPastingValue`,
  `diagnosticEdgeCardTable`, `diagnosticTwoSources`, `diagnosticTwoTargets`,
  `diagnosticTwoLeftPaths`, `diagnosticTwoRightPaths`,
  `diagnosticThreeSources`, `diagnosticThreeTargets`,
  `diagnosticThreeStartPaths`, `diagnosticThreeFinishPaths`,
  `diagnosticThreeLeftPastings`, `diagnosticThreeRightPastings`
- fixed BC vocabulary: `BCFieldKind`, `BCFieldKind.ofCart`, `BCFieldValue`,
  `cartFieldValueToBC`, `BCSquareLeg`,
  `BCProjection`, `BCNamedConstant`, `BCFieldTerm`, `bcCartPresentation`,
  `readBCProjection`, `readBCNamedConstant`, `evalBCFieldTerm`,
  `BCDerivedSet`, `evalBCDerivedSet`, `BCUniversalEquality`,
  `diagnosticFaces`, `evalBCUniversalEquality`, `BCConditionSyntax`,
  `evalBCCondition`, `evalBCCondition_firstAtomMapIdentity_eq_true_iff`,
  `FirstLegIdentityAtomComponent`,
  `evalBCCondition_firstAtomMapIdentity_bridge`,
  `evalBCCondition_firstAtomMapIdentity_replacement_invariant`
- finite checks: `FiniteBCDiagnosticCell`,
  `finiteBCDiagnosticTwoPresentation`, `finiteBCDiagnosticGeometry`,
  `finiteBCDiagnosticPresentation`, `finiteBCDiagnosticTransportData`,
  `finiteConstantBCDiagnosticInterpretation`,
  `finiteBCDiagnostic_vertices_nonempty`,
  `finiteBCDiagnostic_twoCells_nonempty`,
  `finiteBCDiagnostic_threeFaces_nonempty`, `finiteConstantBCCospan`,
  `finiteConstantCompatiblePointCode_wellFormed`,
  `finiteConstantBCRawCode_wellFormed`,
  `finiteConstantBCRawCode_check_true`,
  `finiteConstantBC_generated_leg_source_cards`,
  `finiteConstantBC_generated_top_source_point_mem`,
  `finiteConstantBC_bottom_point_eq_compatible_first`,
  `finiteBadBCRawCode_not_wellFormed`, `finiteBadBCRawCode_check_false`,
  `finiteConstantBC_firstAtom_check`,
  `finiteConstantBC_diagnostic_structure_check`,
  `finiteSwapBC_firstAtom_check_false`, `finiteConstantRealizableSquare`,
  `finiteConstantRealizableSquare_firstLegIdentity`,
  `finiteSwapRealizableSquare_not_firstLegIdentity`,
  `finiteTwoCollapseSemantic_ne_id`,
  `finiteTwoCollapse_comp_finiteConstant`,
  `finiteNonPullbackSquare_not_isPullback`,
  `finiteNonPullbackBCInput_not_presented`,
  `finiteNonPullbackBCInput_has_no_realizableSquare`

## F0a acceptance spine

F0a の報告対象 declaration は次に固定する。補助 lemma と生成された
recursor を completion claim の代用品にはしない。

- predicate/permutation code: `AtomPredicateCode.eval_transport`,
  `AtomPredicateCode.transport_refl`, `AtomPredicateCode.transport_trans`,
  `AtomPredicateCode.transport_symm_cancel`,
  `AtomPermutationCode.toEquiv_ofPerm`, `AtomPermutationCode.toEquiv_refl`,
  `AtomPermutationCode.toEquiv_symm`, `AtomPermutationCode.toEquiv_trans`
- decoder/provenance: `FiniteDoctrineCode.toDoctrine`,
  `FiniteDoctrineCode.toDoctrine_extracts_iff`, `CartRawCode.WellFormed`,
  `CartRawCode.checkWellFormed_eq_true_iff`, `decodeCartDoctrineHom`,
  `toSemanticCart`, `toSemanticCart_sound`, `RealizableHom`,
  `realizableHomOf`
- closure: `idPresentation`, `toSemanticCart_idPresentation_hom`,
  `compPresentation`, `toSemanticCart_compPresentation_hom`,
  `cartPresentationSetoid`, `FiniteCodeCartHom`,
  `FiniteCodeCartHom.ofPresentation`, `typedPresentationToSemantic`,
  `FiniteCodeCartHom.toSemantic`, `FiniteCodeCartHom.comp`,
  `FiniteCodeCartCategory`, `finiteCodeCartCategory`,
  `finiteCodeCartRealization`,
  `finiteSourceCells`, `finiteSourceCells_nodup`,
  `finiteSourceCells_complete`, `CompatibleSource`,
  `compatibleSourceValues`, `compatibleSourceValues_nodup`,
  `compatibleSourceValues_complete`, `compatibleSourceEquiv`,
  `compatibleSourceValues_length_eq_card`, `pullbackDoctrineCode`,
  `pullbackInstanceCode`,
  `pullbackFstPresentation`, `pullbackSndPresentation`,
  `PullbackPresentation`, `pullbackPresentation`,
  `pullbackPresentation_commutes`, `pullbackSemanticLift`,
  `pullbackSemanticLift_fst`, `pullbackSemanticLift_snd`,
  `pullbackSemanticLift_unique`, `pullbackPresentation_isPullback`,
  `finiteCodeCartRealization_pullback_isPullback`
- fixed cartesian vocabulary: `CartProjection`, `CartNamedConstant`,
  `CartDerivedSet`, `CartUniversalEquality`, `CartConditionSyntax`,
  `evalCartCondition`, `evalCartCondition_atomMapIdentity_eq_true_iff`,
  `IdentityAtomComponent`, `evalCartCondition_atomMapIdentity_bridge`,
  `evalCartCondition_atomMapIdentity_replacement_invariant`
- finite checks: `finiteConstantSourceMap_not_injective`,
  `finiteWithoutComponentCAtomPredicate`,
  `finiteWithoutComponentC_holds_componentA`,
  `finiteWithoutComponentC_not_holds_componentC`,
  `finiteModelCodeSourceToFixture`, `finiteModelFixtureSourceToCode`,
  `finiteModelSourceEquiv`, `finiteModelSourceEquiv_zero`,
  `finiteModelSourceEquiv_one`, `finiteModelSourceEquiv_symm_all`,
  `finiteModelSourceEquiv_symm_withoutComponentC`,
  `finiteModelDoctrineCode`, `finiteModelDoctrineToFixture`,
  `finiteModelDoctrineFromFixture`, `finiteModelDoctrineRealizationIso`,
  `finiteConstantPresentation_check_true`, `finiteBadPointRawCode`,
  `finiteBadPointRawCode_not_wellFormed`,
  `finiteBadPointRawCode_check_false`,
  `extInstHom_sourceMap_injective_of_isIso`,
  `finiteConstantPresentation_not_isIso`,
  `finiteConstantRealizableHom`, `infiniteAllDoctrine`,
  `infiniteAllInstance`, `infiniteIdentityInput`,
  `infiniteIdentityInput_not_presented`,
  `infiniteIdentityInput_has_no_realizableHom`,
  `finiteConstantCompatibleSource_card`,
  `finiteConstantPullback_sourceCard`, `finiteConstantPullback_isPullback`,
  `finiteSwapPermutationCode_componentC`,
  `finiteConstant_identityAtom_check`,
  `finiteSwap_identityAtom_check_false`

この cycle は K0 の真部分 fiber witness を主張しない。constant cospan は
非可逆入力と Source 成長を検査する F0 witness であり、成分直積への
canonical map の非全射性を必要とする K0 witness は次段以降で別途構成する。
