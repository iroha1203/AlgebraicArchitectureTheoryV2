# G-117 — 冪等 modification と lax 診断選択子

この report は固定 GOAL
`research/goals/G-117-aat-lax-diagnostic-projector.md` の証拠索引と
proof obligation delta を記録する。GOAL の statement は変更しない。

## Fixed target

- target: **Natural Idempotent Modification and Lax Diagnostic Projector Theorem**
- tracking Issue: #4359
- fixed GOAL blob: `107263cd9185412b72453a6ebfe0c3e7cf979740`
- base commit: `8b669569525c0125e809d2d8b56d885edd8a3724`
- current status: `active / target-proof-checkpoint`

## Proof obligation state

- 完了(Cycle 1): K5-h2 core propagation。任意長のtyped pastingに対する
  非可換cons再帰、fixed fixtureの左右endpoint gauge、raw cochain変換、固定
  reselectionの非恒等性、二面pastingとclosed obstructionのbaseline/shifted決定を
  一つの宣言群へ接続した。
- 完了(Cycle 2): F0の(a)(b)型表現とK1。任意のcanonical `transportAlong` に対する
  admissibility保存を全fieldについて証明し、`AdmCoreFiber X` と制限transport functorを
  構成した。
- 未完: F0のmodification packaging、(e)(f)(i)の型表現。K2(c)(d)、K3(e)、
  K4(f)(g)、K5(h1)(i)。
- h1が成り立つ枝の場合に必要な二witnessへの固定increment作用は、h1の分類後に
  h2へ追加する。

## Cycle 1 — K5-h2 core propagation

### Mathematical result

任意の `RewritePasting` について、nilのraw defectは `1` であり、consではtailの
raw defectに、tailのcanonical comparatorで共役した新しいoriented face defectを
右から掛ける。これによりlocal defectの単純積へ可換化しない順序を固定した。

fixed `finiteAxisFoldBCDatumSquare.toTransportData` は
`finiteAxisFoldTransportData` と定義的に一致する。このdatumで
`finiteAxisFoldSecondFaceReselection` は恒等reseletionではなく、左endpoint gaugeは
`1`、右endpoint gaugeは `finiteAxisFoldSwap` となる。したがってfiring cellのraw値は
baselineの `finiteAxisFoldSwap` から `1` へ変わる。

一方、`.first` forwardと `.second` backwardをこの順に合成したlength-2 pastingの
raw defect、および `DoubleDiamondThreeCell.comparison` のclosed obstructionは、
baselineとshiftedの双方で `finiteAxisFoldSwap` である。したがってこの固定作用は
cell値を変えるが、二面pastingとclosed comparisonの値を保存する。

### Declaration map

| GOAL clause | Lean declaration |
| --- | --- |
| (h2)(1), nil | `pastingRawDefect_nil` |
| (h2)(1), noncommutative cons | `pastingRawDefect_cons` |
| (h2)(2), arbitrary single-edge gauge | `pathReselectionTransition_singleEdge_at` |
| (h2)(2), left/right endpoint | `finiteAxisFold_leftTransition_atFiringCell`, `finiteAxisFold_rightTransition_atFiringCell` |
| (h2)(2), substituted raw action | `finiteAxisFold_rawDefect_transition` |
| (h2)(3), nonidentity and fixed gauges | `finiteAxisFoldSecondFaceReselection_ne_one`, `finiteAxisFold_fixed_leftTransition`, `finiteAxisFold_fixed_rightTransition` |
| (h2)(3), firing-cell change | `finiteAxisFold_fixed_rawDefect_transition`, predecessor `finiteAxisFold_shiftedCochain_ne_initial` |
| (h2)(3), length-2 geometry | `doubleDiamondBackwardFace`, `doubleDiamondBackwardStep`, `finiteAxisFoldTwoFacePasting` |
| (h2)(3), length-2 no-unfold API | `doubleDiamondBackwardFace_cell`, `_incoming`, `_outgoing`, `_orientation`, `doubleDiamondBackwardStep_face`, `finiteAxisFoldTwoFacePasting_spec` |
| (h2)(3), length-2 decision | `finiteAxisFold_twoFacePasting_baseline`, `finiteAxisFold_twoFacePasting_shifted` |
| (h2)(3), closed comparison decision | `finiteAxisFold_closedObstruction_baseline`, `finiteAxisFold_closedObstruction_shifted` |
| connected fixed-fixture result | `finiteAxisFold_propagation_decision` |

### Premise and proof-use audit

- `pastingRawDefect_cons` unfolds the authored and canonical pasting products separately and
  retains the canonical tail conjugation.
- `finiteAxisFold_rawDefect_transition` uses `rawTwoCellDefect_transition` together with both
  newly proved endpoint calculations.
- `finiteAxisFold_twoFacePasting_baseline` and `_shifted` invoke
  `pastingRawDefect_cons` twice, including the nontrivial outer cons case.
- The backward face, backward step, and ordered two-face pasting expose
  constructor/destructor equations, so the two evaluation proofs use the public
  specification rather than unfolding the new geometry definitions.
- `finiteAxisFold_propagation_decision` uses the input equality
  `finiteAxisFold_toTransportData`, G-110's actual cochain-change theorem, and every new fixed
  evaluation theorem.
- no theorem receives the desired propagation equality, nonidentity result, or evaluation as
  an argument, structure field, typeclass, or certificate.
- route integrity: pass for K5-h2 core。fixture、firing cell、increment、two-face orderは
  fixed GOALの指定から変更していない。
- vacuity: none found。incrementは非恒等であり、raw cochainの変化を伴う。

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-117-aat-lax-diagnostic-projector
cycle: 1
goal_blob_sha: 107263cd9185412b72453a6ebfe0c3e7cf979740
base_oid: 8b669569525c0125e809d2d8b56d885edd8a3724
tracking_issue: 4359
report_path: research/reports/G-117-aat-lax-diagnostic-projector.md
selection:
  proof_state_ref: "Issue #4359 goal-defect record plus merged GOAL revision PR #4361"
  proof_dag_predecessors: ["G-106 propagation API", "G-110 finite axis-fold orbit", "G-117 revised h2"]
  proof_obligation: "K5-h2 core propagation on the fixed finite axis-fold datum"
  selection_reason: "The revised clause was the former typing blocker; closing its full nonconditional core gives the most direct reusable proof delta."
  expected_result_type: proof-obligation-discharged
  lean_targets: ["ResearchLean.AG.DoctrineFiberProduct.LaxDiagnosticProjectorPropagation"]
  risks: ["noncommutative factor order", "identity-increment vacuity", "one-face repackage", "fixture drift", "missing raw-transition proof-use"]
  unchecked: ["h1 branch and its conditional two-witness action", "all non-h2 target clauses"]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "h2 core changed from a typed GOAL obligation to a checked theorem family with concrete baseline/shifted decisions"
  completion_candidate: no
  lean_artifacts: ["ResearchLean/AG/DoctrineFiberProduct/LaxDiagnosticProjectorPropagation.lean"]
  evidence: ["pastingRawDefect_cons", "finiteAxisFold_rawDefect_transition", "finiteAxisFold_propagation_decision"]
  claim_mapping:
    theorem_names: ["pastingRawDefect_nil", "pastingRawDefect_cons", "finiteAxisFold_propagation_decision"]
    source_labels: ["G-117(h2)(1)", "G-117(h2)(2)", "G-117(h2)(3)"]
    conjuncts: ["arbitrary typed-pasting recursion", "two endpoint gauges plus raw action", "fixed nonidentity length-2 and closed decisions"]
    undischarged_assumptions: []
    acceptance_point: "Every unconditional h2 component is proved from reviewed predecessor declarations and fixed input data."
    port_status: not-applicable
audits:
  premise_delta:
    discharged: ["K5-h2 unconditional core"]
    remaining: ["h1-dependent transformed witness product", "clauses (a)-(g), (h1), (i)"]
  certificate_provenance:
    discharged: ["fixed datum and named reselection from G-110", "generated endpoint gauges from G-106 uniqueness"]
    unresolved: []
  proof_use:
    used: ["rawTwoCellDefect_transition", "pastingRawDefect definitions", "finiteAxisFold_shiftedCochain_ne_initial", "finiteAxisFold_toTransportData"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/LaxDiagnosticProjectorPropagation.lean: exit 0; standard-axiom audit 38 declarations", "cd research/lean && lake build ResearchLean.AG.DoctrineFiberProduct.LaxDiagnosticProjectorPropagation: exit 0; 4062 targeted dependency jobs", "all 37 reported declarations #print axioms: propext, Classical.choice, Quot.sound only"]
  blocking_findings: []
  next_obligation: "complete the remaining F0 type map, then K1 admissibility transport and AdmCoreFiber"
```

## Cycle 2 — K1 admissibility transport and admissible fiber

### Mathematical result

任意のpackage `P`、そのcanonical object normalizationのadmissibility証明、任意の
exact doctrine morphism `f` に対して、`transportAlong P f` もadmissibleである。
これにより各 `CoreFiber X` のadmissible packageはfull subcategory
`AdmCoreFiber X` をなし、任意のbase arrow `sigma : X ⟶ Y` に沿う既存の
`coreFiberTransportFunctor sigma` は
`AdmCoreFiber X ⥤ AdmCoreFiber Y` へ制限される。

### F0 field transport map

| admissibility field | transport route and dependent equality handling |
| --- | --- |
| equation residual | `castEquationResidual_configurationInvariant` after `transportEquationResidual_configurationInvariant`; normalizationのconfiguration equalityで評価対象を同定 |
| operation type | inverse Atom transport後のobject normalizationを `transportArchitectureObject_symm_canonicalObjectNormalization` で同定し、sourceの `operation_type_eq` を使用 |
| operation naturality | sourceの `operation_naturality` をatom mapへ射影し、endpoint equalityと二つの `cast_heq` を `operationConfigurationMap_atomMap_eq_of_heq` で接続 |
| invariant | function/predicate両分岐を `transportedInvariant_self_naturality` で共役し、同じobject-transport同定を使用 |
| coordinate | inverse Atom transport後のobject normalization同定からsourceの `coordinate_eq` を使用 |

### Declaration map

| GOAL clause | Lean declaration |
| --- | --- |
| (a), object transport | `transportArchitectureObject_symm_canonicalObjectNormalization` |
| (a), equation residual | `equationResidualConfigurationInvariant_transportAlong` |
| (a), invariant | `transportedInvariant_self_naturality` |
| (a), dependent operation cast | `operationConfigurationMap_atomMap_eq_of_heq` |
| (a), all fields | `canonicalObjectNormalizationAdmissible_transportAlong` |
| (b), object property | `admissibleCoreFiberObjectProperty` |
| (b), full subcategory | `AdmCoreFiber` |
| (b), restricted functor | `admissibleCoreFiberTransportFunctor` |
| (b), no-unfold object/map API | `admissibleCoreFiberTransportFunctor_obj_obj`, `admissibleCoreFiberTransportFunctor_map_hom` |

### Premise and proof-use audit

- `canonicalObjectNormalizationAdmissible_transportAlong` quantifies over every source package,
  supplied admissibility proof, target doctrine, and exact doctrine morphism accepted by
  `transportAlong`; it does not generalize to arbitrary `PackageTotalHom`.
- equation residual preservation derives target configuration invariance from the source
  admissibility field; no target residual certificate is supplied.
- operation naturality uses source naturality as proof input and discharges the dependent cast
  through endpoint equalities plus `HEq`; it does not assume the target naturality conclusion.
- invariant transport handles both constructors of `Invariant` and preserves the supplied value
  equivalence in the function-valued branch.
- `AdmCoreFiber` is the standard `ObjectProperty.FullSubcategory`, and the restricted functor is
  `ObjectProperty.lift` of the existing core-fiber transport; morphisms are therefore the full
  subcategory morphisms rather than a newly weakened morphism type.
- route integrity: pass for K1. The implementation uses exactly canonical `transportAlong` and
  the reviewed `coreFiberTransportFunctor` fixed by the GOAL.
- vacuity: none found. The preservation theorem consumes every field of source admissibility,
  and the target property is constructed rather than received as a certificate.

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-117-aat-lax-diagnostic-projector
cycle: 2
goal_blob_sha: 107263cd9185412b72453a6ebfe0c3e7cf979740
base_oid: 4334ef5500ac62ccd2a72d534a8a7a4c0fd5f4cc
tracking_issue: 4359
report_path: research/reports/G-117-aat-lax-diagnostic-projector.md
selection:
  proof_state_ref: "Issue #4359 after merged Cycle 1 PR #4362"
  proof_dag_predecessors: ["G-116 canonical normalization admissibility", "G-109 coreFiberTransportFunctor"]
  proof_obligation: "K1(a)(b): admissibility transport and the admissible core-fiber restriction"
  selection_reason: "This closes the first structural prerequisite for the modification components and their base-arrow compatibility."
  expected_result_type: proof-obligation-discharged
  lean_targets: ["ResearchLean.AG.DoctrineFiberProduct.LaxDiagnosticProjectorAdmissibleFiber"]
  risks: ["dependent operation cast mismatch", "equation-reading base cast", "function/predicate invariant mismatch", "morphism weakening"]
  unchecked: ["modification packaging", "clauses (c)-(g), (h1), (i)"]
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "K1(a)(b) changed from unimplemented fixed clauses to a checked all-field preservation theorem and restricted full-subcategory functor"
  completion_candidate: no
  lean_artifacts: ["ResearchLean/AG/DoctrineFiberProduct/LaxDiagnosticProjectorAdmissibleFiber.lean"]
  evidence: ["canonicalObjectNormalizationAdmissible_transportAlong", "AdmCoreFiber", "admissibleCoreFiberTransportFunctor"]
  claim_mapping:
    theorem_names: ["canonicalObjectNormalizationAdmissible_transportAlong", "admissibleCoreFiberTransportFunctor"]
    source_labels: ["G-117(a)", "G-117(b)"]
    conjuncts: ["all-field canonical transport preservation", "full admissible subcategory", "restricted core-fiber transport"]
    direction_hypotheses: ["source CanonicalObjectNormalizationAdmissible"]
    undischarged_assumptions: []
    acceptance_point: "Every K1 construction is generated from source admissibility and the fixed canonical transport route."
    port_status: not-applicable
audits:
  premise_delta:
    discharged: ["K1(a) all five admissibility fields", "K1(b) full subcategory and restricted functor"]
    remaining: ["clauses (c)-(g), (h1), (i)"]
  certificate_provenance:
    direction_hypotheses: ["source CanonicalObjectNormalizationAdmissible"]
    discharged: ["target admissibility generated field-by-field", "ExactDoctrineHom-generated transportAlong", "reviewed coreFiberTransportFunctor"]
    unresolved: []
  proof_use:
    used: ["source equationResidual_configurationInvariant", "source operation_type_eq", "source operation_naturality", "source invariant_transport", "source coordinate_eq"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs: ["cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/LaxDiagnosticProjectorAdmissibleFiber.lean: exit 0; namespace axiom assertion: 10 declarations, standard axioms only", "cd research/lean && lake build ResearchLean.AG.DoctrineFiberProduct.LaxDiagnosticProjectorAdmissibleFiber: exit 0; 4062 targeted dependency jobs", "all 10 reported declarations #print axioms: propext, Classical.choice, Quot.sound only; one declaration uses no axioms"]
  blocking_findings: []
  next_obligation: "complete the F0 modification packaging, then K2(c)(d)"
```

## Current judgment

- latest cycle result proposal: `proof-obligation-discharged` for K1(a)(b)。
- completion candidate: no。
- target result: `target-proof-checkpoint`。
- next obligation: complete the F0 modification packaging, then K2(c)(d)。
