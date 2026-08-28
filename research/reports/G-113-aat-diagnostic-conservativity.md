# G-113-aat-diagnostic-conservativity — 診断保守性・反射・orbit exactness の分類

- 一次仕様: [`research/goals/G-113-aat-diagnostic-conservativity.md`](../goals/G-113-aat-diagnostic-conservativity.md)
- tracking Issue: [#4198](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4198)
- target theorem: Diagnostic Conservativity Classification Theorem
- proof state: `active / F0 type surface checkpoint`
- completion candidate: `no`

この report は固定 GOAL の証拠索引と proof obligation delta を記録する。
target statement と completion criteria は GOAL カードを正本とし、SCORE は
使わない。

## Fixed heads

- reviewed fixed statement blob SHA (tracking Issue link insertion前):
  `fd6956ae3f29c64fc9102dd6dff37a590908c179`
- current GOAL blob SHA (数学statement同一、tracking Issue link同期後):
  `89d47851711f9335bf42d312c8522db01c7718ba`
- fixed GOAL SHA-256:
  `c4ff9c3ffbb0a12e4ddc412895cdd343422b679331b2d3cd5d0a4835e6f6aa61`
- base OID: `0a31b61f3b161ce857524716e57d4fef6cca8275`
- language head: `DiagnosticClassTerm` / `DiagnosticClassTerm.eval`
- class-term candidate sequence: `diagnosticClassTermCandidates`。順序は
  `vertexwiseSourceMapInjective`、その `edgewiseSquarePullback` との conjunction、
  `edgewiseSquarePullback` の3項で固定する。
- O20-term head: `pointwiseReflectionTerm` =
  `vertexwiseSourceMapInjective`。候補遷移を持たない。
- (i) candidate head: `VertexwiseSourceMapBijective` の1項。
  `FullFaithfulCandidate` / `fullFaithfulCandidateRegistry` が独立 singleton
  registry として機械登録し、2項目が無いことまで API 化する。
- conservativity head: `DiagnosticConservative`。source interpretation を
  含意の外側で全量化する per-interpretation 形。
- iso witness head: `IndexedBaseDiagramIso` /
  `IndexedBaseDiagramHomIsoWitness`。前者は既存の diagram category 上の
  `CategoryTheory.Iso` の abbrev であり、後者は比較対象 hom に対する正逆の
  可換 square を持つ。
- universe contract: shape、carrier、diagram、hom、interpretation を同一の
  任意 universe `u` で量化する。条件 syntax 自体は carrier / shape /
  diagram parameter を保持しない。(f)(g) の finite raw witness は後続 cycle
  で per-universe に構成する。

## Qualification correspondence

| G-113 の資格 / 構文規則 | G-110 `H_cart` 資格 | 対応と現在状態 |
| --- | --- | --- |
| (i) 探索前固定 + (ii) 結論非参照 | (i) 固定条件言語 + 結論非参照 | `DiagnosticClassTerm`、3項候補列、evaluator 依存監査を F0 で固定 |
| (iii) diagram 同型不変性 | (ii) 入力同型不変性 | `CategoryTheory.Iso` 上の witness 型を固定、保存 theorem は K0 未証明 |
| (iv) hom / square 閉性 | (iii) id / comp / pullback 安定性 | G-113 は hom の id / vertical comp と path-square 水平安定性を要求、K4 未証明 |
| syntax の fixture / 値 / carrier parameter 排除 | (iv) fixture tag・命名・特定 carrier 非依存 | parameter-free inductive と下記依存監査で固定 |
| (v) 非空発火 | (v) 非恒等・非可逆・非同型の正例族 | G-113 はさらに非恒等 defect / reselection を要求、K3 未構成 |

## F0 transitive dependency audit

条件 evaluator の全枝を宣言本体と依存先まで実読した結果を固定する。

| evaluator branch | 直接依存 | 依存先の実体 | diagnostic 結論への経路 |
| --- | --- | --- | --- |
| `vertexwiseSourceMapInjective` | `hom.app vertex` → `doctrineHom.sourceMap` | G-111 diagram hom の vertex 成分と G-101 exact-doctrine arrow の underlying function | なし |
| `edgewiseSquarePullback` | `hom.edgeSquare edge` → `IsPullback left top bottom right` | `edgeSquare` は source / target edge、vertex `app`、`naturality` だけから生成 | なし |
| `conjunction` | 左右 term の `eval` | inductive recursion のみ | なし |

`DiagnosticClassTerm` は上記2原子と conjunction 以外の constructor / operandを
持たない。`eval` の型・本体には `IndexedDiagnosticInterpretation`、defect、
reselection、coherence、vanishing、`DiagnosticConservative`、fixture、callback、
certificate、external set / constant が現れない。module が vanishing layerを import
する理由は別宣言 `DiagnosticConservative` の signature であり、evaluator の
declaration dependency には入らない。したがって F0 の結論非参照と route は pass。
K0 に残す language obligation は Mono 排除と ACI normalization completeness である。

## Prop instance-pair status

`DiagnosticConservativitySchemaWitnesses.lean` は、既存 G-111 の2頂点・2平行辺・
非自明 carrier を持つ named shape 上で次を固定する。

- identity hom: injectivity / pullback / conjunction / generated class /
  `VertexwiseSourceMapBijective` / 登録済み (i) candidate の正例。
- finite constant hom: injectivity / conjunction / generated class /
  `VertexwiseSourceMapBijective` / 登録済み (i) candidate の負例。
- `finiteNonPullbackSquare`: pullback atom / generated pullback class の負例。
- `indexedCovarianceSource`: `DiagnosticConservative` の source interpretation
  量化域が非空である具体的 inhabitant。fixture field に vanishing や
  conservativity は無い。

`DiagnosticConservative` 自体の正負 pair は未放電である。非退化な正例は K1 の
identity / sufficiency theoremを必要とし、負例は固定 target (f) O16 の
「generated target obstruction vanishing かつ source nonvanishing」そのもので
K3 の建設義務である。空 interpretation、単一objectへの縮退、結論供給 fieldで
先行 pairを作ることは GOAL の dullness filter / anti-weakening に反する。
したがって §1.4 の「片方が作れない理由」を K1/K3 の exact obligationへ接続して
記録し、この cycle は引き続き `proof-checkpoint` とする。

## Cycle ledger

### Cycle 1 — F0 type surface

```yaml
ledger_type: target_cycle_result
goal: G-113-aat-diagnostic-conservativity
cycle: 1
goal_blob_sha: fd6956ae3f29c64fc9102dd6dff37a590908c179
base_oid: 0a31b61f3b161ce857524716e57d4fef6cca8275
tracking_issue: 4198
report_path: research/reports/G-113-aat-diagnostic-conservativity.md
selection:
  proof_state_ref: "Issue #4198: active / F0 proof-checkpoint review / next K0"
  proof_dag_predecessors:
    - "G-111 PR #4181 / merge 8850a5b4"
    - IndexedBaseDiagramHom
    - IndexedDiagnosticInterpretation
    - IndexedBaseDiagramHom.transportedInterpretation
    - IndexedBaseDiagramHom.indexedTransportObstructionVanishes_transport
  proof_obligation: >-
    Fix the F0 closed language and evaluator, the ordered class-term head,
    the by-value O20 term, the fixed bijectivity candidate, the diagram-iso
    witness, the per-interpretation DiagnosticConservative signature, and the
    common universe contract without proving conservativity or qualification.
  selection_reason: >-
    F0 is the unique next obligation in Issue #4198 and fixes every head used by
    K0--K4 before any proof result can influence candidate selection.
  expected_result_type: proof-checkpoint
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/DiagnosticConservativitySchema.lean
    - ResearchLean/AG/DoctrineFiberProduct/DiagnosticConservativitySchemaWitnesses.lean
  risks:
    - DiagnosticConservative could accidentally use an aggregate antecedent
    - the closed language could acquire diagnostic data or an arbitrary callback
    - componentwise isomorphisms could omit diagram naturality
    - O20 or the Full+Faithful candidate could drift with the class-term state
    - later finite witnesses could be weakened to one fixed universe
  unchecked:
    - focused Lean elaboration
    - target declaration axiom audit
    - fixed-head standard PR review
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: >-
    DiagnosticClassTerm has exactly the two fixed atomic constructors and
    conjunction; its evaluator reads only vertex sourceMap injectivity and
    IsPullback for generated G-111 edge squares.  The ordered three-term
    sequence, independent by-value O20 term, sole bijectivity candidate,
    diagram-isomorphism witness, GeneratedDiagnosticClass, and the
    per-interpretation DiagnosticConservative predicate are now fixed at every
    universe u without any theorem-result input.  Structural positive/negative
    controls for eval, generated membership, and the fixed (i) predicate fire
    on named nonempty fixtures.  DiagnosticConservative itself remains without
    a positive/negative pair because those are K1 and K3/O16 results, so this is
    a proof checkpoint rather than target-proof completion.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/DiagnosticConservativitySchema.lean
    - ResearchLean/AG/DoctrineFiberProduct/DiagnosticConservativitySchemaWitnesses.lean
  evidence:
    - DiagnosticClassTerm
    - DiagnosticClassTerm.eval
    - diagnosticClassTermCandidates_head
    - mem_diagnosticClassTermCandidates_iff
    - pointwiseReflectionTerm
    - VertexwiseSourceMapBijective
    - fullFaithfulCandidateRegistry_head
    - fullFaithfulCandidateRegistry_second
    - diagnosticSchemaIdentity_eval_conjunction
    - diagnosticSchemaCollapse_not_eval_injective
    - diagnosticSchemaNonPullback_not_eval_pullback
    - diagnosticSchemaInterpretation_nonempty
    - IndexedBaseDiagramIso
    - IndexedBaseDiagramHomIsoWitness
    - diagnosticConservative_iff
  claim_mapping:
    theorem_names:
      - DiagnosticClassTerm.eval_vertexwiseSourceMapInjective_iff
      - DiagnosticClassTerm.eval_edgewiseSquarePullback_iff
      - DiagnosticClassTerm.eval_conjunction_iff
      - diagnosticClassTermCandidates_head
      - diagnosticConservative_iff
    source_labels:
      - "target theorem (a) DiagnosticConservative signature"
      - "target theorem (b) closed language and fixed class-term head"
      - "target theorem (e) by-value O20 term"
      - "target theorem (i) fixed bijectivity candidate"
    conjuncts:
      - "F0 typing -> DiagnosticConservativitySchema"
    undischarged_assumptions:
      - closed-language normalization completeness and Mono exclusion
      - class qualification and conservativity sufficiency
      - reflection, orbit detection, and O20 classification
      - outside-class and inside-class finite witnesses
      - closure and Full+Faithful decision
    acceptance_point: >-
      This cycle is not an acceptance point.  It fixes the pre-proof type
      surface named by F0 and structural controls for its condition predicates.
      DiagnosticConservative's pair and every conservativity, reflection,
      detection, target witness, closure, or Full+Faithful result remain
      unaccepted.
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "F0 closed language and evaluator typing / DiagnosticClassTerm.eval"
      - "F0 transitive dependency audit / no diagnostic conclusion dependency"
      - "F0 class, O20, and bijectivity statement heads / three independent declarations"
      - "F0 category-iso witness typing / IndexedBaseDiagramHomIsoWitness"
      - "F0 per-interpretation conservativity statement / DiagnosticConservative"
    remaining:
      - "all discharge-required rows / F0 fixes signatures only"
      - "DiagnosticConservative positive/negative pair / K1 and K3 O16"
  certificate_provenance:
    discharged:
      - "fixed heads are literal GOAL-card translations and consume no certificate"
    unresolved:
      - "all later theorem and witness producers"
  proof_use:
    used:
      - "G-111 diagram/hom and generated diagnostic transport API / F0 signatures"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: >-
    structural predicates have positive/negative controls; DiagnosticConservative
    has a nonempty interpretation domain but its truth-value pair remains K1/K3
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - >-
      cd research/lean && lake env lean
      ResearchLean/AG/DoctrineFiberProduct/DiagnosticConservativitySchema.lean
      / exit 0 / axiom audit: 83 declarations, standard axioms only
    - >-
      cd research/lean && lake env lean
      ResearchLean/AG/DoctrineFiberProduct/DiagnosticConservativitySchemaWitnesses.lean
      / exit 0 / axiom audit: 26 declarations, standard axioms only
    - >-
      cd research/lean && lake build
      ResearchLean.AG.DoctrineFiberProduct.DiagnosticConservativitySchema
      / exit 0 / targeted module only
    - >-
      target #print axioms audit / all 26 reported declarations use only
      propext, Classical.choice, Quot.sound or no axioms
    - >-
      schema SHA-256
      238eab17378a62cb75dbfe5f53a3522484704a0dc91c5d785b5e11c16995ccd3
    - >-
      witness SHA-256
      96dca57c4279f5311a57fa29429ec93382b210c33e4644ee58114116eec7a090
  blocking_findings:
    - "DiagnosticConservative pair is intentionally not an F0 result; exact producers are K1 and K3 O16"
  next_obligation: K0 normalization, Mono exclusion, and qualification
```
