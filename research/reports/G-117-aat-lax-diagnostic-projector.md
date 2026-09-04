# G-117 — 冪等 modification と lax 診断選択子

この report は固定 GOAL
`research/goals/G-117-aat-lax-diagnostic-projector.md` の証拠索引と
proof obligation delta を記録する。GOAL の statement は変更しない。

## Fixed target

- target: **Natural Idempotent Modification and Lax Diagnostic Projector Theorem**
- tracking Issue: #4359
- fixed GOAL blob: `107263cd9185412b72453a6ebfe0c3e7cf979740`
- base commit: `8b669569525c0125e809d2d8b56d885edd8a3724`
- current status: `target-refuted pending fixed-head review`

## Proof obligation state

- 完了(Cycle 1): K5-h2 core propagation。任意長のtyped pastingに対する
  非可換cons再帰、fixed fixtureの左右endpoint gauge、raw cochain変換、固定
  reselectionの非恒等性、二面pastingとclosed obstructionのbaseline/shifted決定を
  一つの宣言群へ接続した。
- 完了(Cycle 2): F0の(a)(b)型表現とK1。任意のcanonical `transportAlong` に対する
  admissibility保存を全fieldについて証明し、`AdmCoreFiber X` と制限transport functorを
  構成した。
- 反例(Cycle 4): full `AdmCoreFiber` の実際の対象・射において prescribed component の
  自然性が破れるため、fixed universal clause (c) は偽。
- 未完: F0のmodification packaging、(e)(f)(i)の型表現、K2(d)、K3(e)、K4(f)(g)、
  K5(h1)(i)。targetがconjunctionとして反証されたため、これらは現カードでは追行しない。

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

## Cycle 3 — K2(c) operation-map naturality blocker

### Mathematical result

各 `P : AdmCoreFiber X` には、G-116 の total normalization を underlying hom とする
`admissibleCanonicalNormalizationComponent P : P ⟶ P` があり、その成分は
`canonicalObjectNormalizationTotal_comp` により冪等である。

一方、これらの成分を full subcategory 上の `NatTrans` に束ねる自然性は、任意の
`PackageTotalHom hom : P ⟶ Q` について、source の operation を normalization の
dependent cast で移してから `hom.upper.operationMap` を適用する経路と、先に operation
を移して target の dependent cast を適用する経路の `HEq` を要求する。object map、exact
equation transport、invariant、axis、coordinate の各 field は既存 API で閉じるが、この
operation-map coherence は `CanonicalObjectNormalizationAdmissible` にも
`SignedExactCoreReadingHom` にも含まれない。後者の `operation_naturality` は両経路が
与える `ConfigurationHom` の合成則であり、operation 値そのものの一致ではない。

`CanonicalNormalizationOperationCoherent` は残った field をそのまま命名し、
`canonicalObjectNormalizationTotal_natural_of_operationCoherent` は、それを置いた場合に
他の全 field が閉じることを Lean で示す。
`canonicalObjectNormalizationTotal_natural_iff_operationCoherent` は total naturality が
この残存 field と同値であることを固定し、`canonicalNormalizationOperationCoherent_id`
は identity total morphism での成立例を与える。この仮定相対 theorem 群は K2(c) の
放電には数えず、一般の不成立例は本 cycle では主張しない。

### Declaration map

| role | Lean declaration |
| --- | --- |
| exact residual field | `CanonicalNormalizationOperationCoherent` |
| all remaining fields close from the residual | `canonicalObjectNormalizationTotal_natural_of_operationCoherent` |
| exact characterization | `canonicalObjectNormalizationTotal_natural_iff_operationCoherent` |
| positive identity instance | `canonicalNormalizationOperationCoherent_id` |
| proposed component family | `admissibleCanonicalNormalizationComponent` |
| component projection API | `admissibleCanonicalNormalizationComponent_hom_hom` |
| component idempotence | `admissibleCanonicalNormalizationComponent_comp` |

### Premise and proof-use audit

- `canonicalObjectNormalizationTotal_natural_of_operationCoherent` uses
  `canonicalObjectNormalization_natural` for the object map and
  `equationSystemExactTransport_hext` for equation transport; all other non-operation fields
  close by reflexivity.
- the residual premise is conclusion-bearing for the missing operation field and therefore is
  recorded only as a blocker witness; it is not accepted as a material premise of the target.
- `admissibleCanonicalNormalizationComponent_comp` instantiates
  `canonicalObjectNormalizationTotal_comp`; it does not reprove G-116 idempotence.
- no `NatTrans` or modification package is claimed in this cycle.

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-117-aat-lax-diagnostic-projector
cycle: 3
goal_blob_sha: 107263cd9185412b72453a6ebfe0c3e7cf979740
base_oid: cdbfa1539b76d7f0da06f7af7d482249e91fbbe6
tracking_issue: 4359
report_path: research/reports/G-117-aat-lax-diagnostic-projector.md
selection:
  proof_state_ref: "K1 accepted by merged PR #4363; F0 modification packaging and K2(c)(d) selected"
  proof_dag_predecessors: ["G-116 canonical normalization idempotence", "G-116 object-map naturality", "G-117 AdmCoreFiber"]
  proof_obligation: "K2(c): assemble the canonical normalization components into a natural idempotent endotransformation"
  selection_reason: "This is the immediate prerequisite for base-arrow, unitor, and compositor compatibility."
  expected_result_type: proof-obligation-discharged
  lean_targets: ["ResearchLean.AG.DoctrineFiberProduct.LaxDiagnosticProjectorModificationBlocker"]
  risks: ["dependent operation cast", "configuration-map equality mistaken for operation equality", "conclusion-bearing coherence premise"]
  unchecked: ["whether a stronger reviewed morphism API discharges the residual", "fixed-target counterexample", "clauses (d)-(g), (h1), (i)"]
result:
  proposed_result_type: blocker-fixed
  proof_obligation_delta: "the component family and its idempotence are checked; the exact operation-map coherence preventing NatTrans assembly is isolated"
  completion_candidate: no
  lean_artifacts: ["ResearchLean/AG/DoctrineFiberProduct/LaxDiagnosticProjectorModificationBlocker.lean"]
  evidence: ["CanonicalNormalizationOperationCoherent", "canonicalObjectNormalizationTotal_natural_iff_operationCoherent", "canonicalNormalizationOperationCoherent_id", "admissibleCanonicalNormalizationComponent_comp"]
  claim_mapping:
    theorem_names: ["admissibleCanonicalNormalizationComponent_comp"]
    source_labels: ["G-117(c), idempotence subclause"]
    conjuncts: ["pointwise component construction", "pointwise idempotence"]
    undischarged_assumptions: ["operation-map coherence required for naturality on the full subcategory"]
    acceptance_point: "Accept only as a reusable blocker-fixed checkpoint, not as K2(c) discharge."
    port_status: not-applicable
audits:
  premise_delta:
    discharged: ["K2(c) component construction", "K2(c) component idempotence"]
    remaining: ["K2(c) naturality", "K2(d)", "clauses (e)-(g), (h1), (i)"]
  certificate_provenance:
    discharged: ["component generated from G-116 normalization"]
    unresolved: ["no reviewed source theorem has been identified that generates operation-map coherence for arbitrary full-subcategory morphisms", "negative instance not yet constructed"]
  proof_use:
    used: ["canonicalObjectNormalization_natural", "equationSystemExactTransport_hext", "canonicalObjectNormalizationTotal_comp"]
    unused: []
  structure_field_escape: "residual premise exposed but rejected as target evidence"
  route_integrity: pass-for-blocker-artifact
  target_fitting: "K2(c) remains unmet"
  vacuity: "positive identity instance proved; negative instance unresolved"
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none
  validation_refs: ["cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/LaxDiagnosticProjectorModificationBlocker.lean: exit 0; namespace axiom assertion: 7 declarations, standard axioms only", "cd research/lean && lake build ResearchLean.AG.DoctrineFiberProduct.LaxDiagnosticProjectorModificationBlocker: exit 0; 4066 targeted dependency jobs before review-finding documentation and characterization additions", "all 7 reported declarations #print axioms: propext, Classical.choice, Quot.sound only"]
  blocking_findings: ["arbitrary SignedExactCoreReadingHom supplies configuration naturality but no equality between operationMap values at normalization-related endpoint indices"]
  next_obligation: "search for a stronger existing morphism API or construct a fixed-target counterexample; a repeated unresolved blocker triggers target-blocked"
```

## Cycle 4 — K2(c) full-subcategory naturality counterexample

### Mathematical result

review済み finite package の operation 型へ、configuration realizationから見えない
`Bool` tagを積として加えた `taggedOperationPackage` を構成した。equation、invariant、
signature、object readingは変えず、operationのconfiguration mapは第一成分だけを読む。
したがって `taggedOperationPackage_admissible` は五つのadmissibility fieldをすべて
既存finite theoremから構成する。

`taggedEndpointFlipTotal` はsource architecture objectが
`finiteAxisFoldBoolObject`であるときだけtagを反転するactual
`PackageTotalHom`である。configuration mapはtagを読まないため、このendomorphismは
`SignedExactCoreReadingHom.operation_naturality`を満たす。一方canonical normalizationは
同じconfigurationを持つ`finiteAxisFoldBoolObject`をdistinctな
`finiteAxisFoldUnitObject`へ送る。

初期tag `false`の`taggedBoolOperation`を評価すると、normalization後にflipする合成のtagは
`false`、flip後にnormalizationする合成のtagは`true`になる。これによりCycle 3の
operation coherenceを否定し、total naturalityを否定する。さらにpackageとendomorphismを
実際のfull admissible fiberへ持ち上げ、prescribed componentとendomorphismが可換でないこと、
および全componentがprescribed canonical normalizationであるidentity endofunctor上の
`NatTrans`が存在しないことを証明した。

最後の定理は、任意のadmissible package上でその`NatTrans`を要求するfixed clause (c)の
一つの具体的反例である。GOAL failure policyによりtarget全体は`target-refuted`となる。

### Declaration map

| role | Lean declaration |
| --- | --- |
| configuration-invisible operation extension | `taggedOperationPackage` |
| all-field admissibility | `taggedOperationPackage_admissible` |
| endpoint-dependent exact endomorphism | `taggedEndpointFlipUpper`, `taggedEndpointFlipTotal` |
| fixed operation input | `taggedBoolOperation` |
| no-unfold operation APIs | `taggedEndpointFlipTotal_operationMap`, `taggedBoolOperation_snd`, `taggedLeftComposite_operationMap`, `taggedRightComposite_operationMap` |
| normalization moves the endpoint | `taggedBoolNormalization_eq_unit` |
| left/right tag evaluations | `taggedLeftComposite_snd`, `taggedRightComposite_snd` |
| residual coherence failure | `taggedEndpointFlip_not_coherent` |
| total naturality failure | `taggedEndpointFlip_not_natural` |
| actual full-fiber object/morphism | `taggedAdmCoreFiberObject`, `taggedAdmCoreFiberEndomorphism` |
| component naturality failure | `taggedAdmCoreFiberComponent_not_natural` |
| fixed clause counterexample | `no_taggedAdmissibleCanonicalNormalizationNatTrans` |

### Premise and proof-use audit

- `taggedOperationPackage_admissible` constructs every target field; no target admissibility
  certificate is accepted.
- `taggedEndpointFlipUpper.operation_naturality` proves equality of configuration maps directly;
  the nontrivial tag action is retained in `operationMap`.
- `taggedLeftComposite_snd` uses the reviewed object distinction
  `finiteAxisFoldUnitObject_ne_boolObject`; the two evaluated tags are definitionally distinct.
- `taggedEndpointFlip_not_natural` uses Cycle 3's exact iff characterization rather than treating
  an unconnected operation discrepancy as total-morphism inequality.
- the full-fiber endomorphism is constructed over identity via `IsHomLift.of_commsq`; the morphism
  type is not narrowed.
- `no_taggedAdmissibleCanonicalNormalizationNatTrans` consumes `NatTrans.naturality` at the actual
  endomorphism and contradicts the proved component inequality. It does not accept a nonnaturality
  certificate.

### Target cycle ledger

```yaml
ledger_type: target_cycle_result
goal: G-117-aat-lax-diagnostic-projector
cycle: 4
goal_blob_sha: 107263cd9185412b72453a6ebfe0c3e7cf979740
base_oid: 7cb967ddbe8b2ab9e16328e36ef60bbb71cdac29
tracking_issue: 4359
report_path: research/reports/G-117-aat-lax-diagnostic-projector.md
selection:
  proof_state_ref: "Cycle 3 blocker accepted by merged PR #4364"
  proof_dag_predecessors: ["Cycle 3 exact operation-coherence characterization", "G-116 finite normalization witness", "G-117 AdmCoreFiber"]
  proof_obligation: "decide K2(c) by discharging residual coherence or constructing a fixed universal-clause counterexample"
  selection_reason: "A configuration-invisible operation tag directly tests the missing faithfulness of the full-subcategory morphism interface."
  expected_result_type: proof-obligation-discharged-or-target-refuted
  lean_targets: ["ResearchLean.AG.DoctrineFiberProduct.LaxDiagnosticProjectorModificationCounterexample"]
  risks: ["tagged package not admissible", "flip not an exact total morphism", "operation discrepancy not lifted to the actual full fiber", "counterexample outside universal quantification"]
  unchecked: ["fixed-head independent review", "CI"]
result:
  proposed_result_type: target-refuted
  proof_obligation_delta: "the Cycle 3 residual is realized by a concrete noncoherent full-fiber endomorphism, refuting the prescribed NatTrans on one admissible fiber"
  completion_candidate: yes-terminal-refutation
  lean_artifacts: ["ResearchLean/AG/DoctrineFiberProduct/LaxDiagnosticProjectorModificationCounterexample.lean"]
  evidence: ["taggedOperationPackage_admissible", "taggedEndpointFlip_not_natural", "taggedAdmCoreFiberComponent_not_natural", "no_taggedAdmissibleCanonicalNormalizationNatTrans"]
  claim_mapping:
    theorem_names: ["no_taggedAdmissibleCanonicalNormalizationNatTrans"]
    source_labels: ["G-117(c)"]
    conjuncts: ["existence of the prescribed natural endotransformation on every admissible core fiber"]
    undischarged_assumptions: []
    acceptance_point: "The theorem negates the prescribed NatTrans on one explicitly constructed admissible full fiber, which refutes the universally quantified conjunct."
    port_status: not-applicable
audits:
  premise_delta:
    discharged: ["counterexample package admissibility", "counterexample total-hom laws", "full-fiber object and morphism", "left/right unequal evaluations"]
    remaining: []
  certificate_provenance:
    discharged: ["package generated from reviewed finite data", "tag flip generated by endpoint equality decision", "failure derived from false/true evaluation"]
    unresolved: []
  proof_use:
    used: ["finiteCanonicalObjectNormalization_admissible", "finiteAxisFoldUnitObject_ne_boolObject", "canonicalObjectNormalizationTotal_natural_iff_operationCoherent", "NatTrans.naturality"]
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none
  validation_refs: ["cd research/lean && lake env lean ResearchLean/AG/DoctrineFiberProduct/LaxDiagnosticProjectorModificationCounterexample.lean: exit 0; namespace axiom assertion: 26 declarations, standard axioms only", "cd research/lean && lake build ResearchLean.AG.DoctrineFiberProduct.LaxDiagnosticProjectorModificationCounterexample: exit 0; 4068 targeted dependency jobs", "all 25 public reported declarations #print axioms: standard axioms only; two generic cast lemmas use no axioms"]
  blocking_findings: []
  stopping_reason: "target-refuted: no_taggedAdmissibleCanonicalNormalizationNatTrans contradicts fixed clause (c)"
  next_obligation: "fixed-head standard review, CI, merge, and target-refuted Issue synchronization"
```

## Current judgment

- latest cycle result proposal: `target-refuted` by fixed clause (c)。
- terminal refutation candidate: yes。
- target result: `target-refuted pending fixed-head review`。
- next obligation: fixed-head standard review, CI, merge, and Issue synchronization。
