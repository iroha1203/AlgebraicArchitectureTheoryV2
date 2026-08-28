# G-113-aat-diagnostic-conservativity — 診断保守性・反射・orbit exactness の分類

- 一次仕様: [`research/goals/G-113-aat-diagnostic-conservativity.md`](../goals/G-113-aat-diagnostic-conservativity.md)
- tracking Issue: [#4198](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4198)
- target theorem: Diagnostic Conservativity Classification Theorem
- proof state: `active / F0 typing`
- completion candidate: `no`

この report は固定 GOAL の証拠索引と proof obligation delta を記録する。
target statement と completion criteria は GOAL カードを正本とし、SCORE は
使わない。

## Fixed heads

- fixed GOAL blob SHA: `fd6956ae3f29c64fc9102dd6dff37a590908c179`
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
- conservativity head: `DiagnosticConservative`。source interpretation を
  含意の外側で全量化する per-interpretation 形。
- iso witness head: `IndexedBaseDiagramIso` /
  `IndexedBaseDiagramHomIsoWitness`。diagram hom の正逆と、比較対象 hom に
  対する正逆の可換 square を持つ。
- universe contract: shape、carrier、diagram、hom、interpretation を同一の
  任意 universe `u` で量化する。条件 syntax 自体は carrier / shape /
  diagram parameter を保持しない。(f)(g) の finite raw witness は後続 cycle
  で per-universe に構成する。

## Qualification correspondence

| G-113(b) 資格 | F0 surface | 現在状態 |
| --- | --- | --- |
| (i) 探索前固定 | `diagnosticClassTermCandidates` / `diagnosticClassTermCandidates_head` | 型固定、review pending |
| (ii) 結論非参照 | `DiagnosticClassTerm` の3 constructor と evaluator unfolding theorem 群 | 型固定、transitive dependency audit は K0 |
| (iii) diagram 同型不変性 | `IndexedBaseDiagramIso` / `IndexedBaseDiagramHomIsoWitness` | witness 型固定、保存 theorem は K0 |
| (iv) 閉性 | identity / vertical composition と path-square 水平安定性を既存 G-111 API 上で量化 | K4 未証明 |
| (v) 非空発火 | raw finite geometry から class membership と実発火を生成 | K3 未構成 |

G-110 `H_cart` (i)–(v) との対応は、探索前固定、結論非参照、同型不変性、
閉性、非空発火の同じ五つの役割を共有する。ただし G-113 の (iii) は
vertex naturality を含む diagram 圏の同型であり、(iv) は hom の恒等・垂直合成
と生成 path square の水平安定性、(v) は非恒等 defect・reselection・非可逆
vertex 成分を同時に要求する。

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
  proof_state_ref: "Issue #4198: active / execution gate discharged / F0 typing pending"
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
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - ResearchLean/AG/DoctrineFiberProduct/DiagnosticConservativitySchema.lean
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
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: >-
    DiagnosticClassTerm has exactly the two fixed atomic constructors and
    conjunction; its evaluator reads only vertex sourceMap injectivity and
    IsPullback for generated G-111 edge squares.  The ordered three-term
    sequence, independent by-value O20 term, sole bijectivity candidate,
    diagram-isomorphism witness, GeneratedDiagnosticClass, and the
    per-interpretation DiagnosticConservative predicate are now fixed at every
    universe u without any theorem-result input.
  completion_candidate: no
  lean_artifacts:
    - ResearchLean/AG/DoctrineFiberProduct/DiagnosticConservativitySchema.lean
  evidence:
    - DiagnosticClassTerm
    - DiagnosticClassTerm.eval
    - diagnosticClassTermCandidates_head
    - pointwiseReflectionTerm
    - VertexwiseSourceMapBijective
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
      This cycle fixes only the pre-proof type surface named by F0; no
      conservativity, reflection, detection, witness, closure, or Full+Faithful
      result is claimed.
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "F0 closed language and evaluator signature / DiagnosticClassTerm.eval"
      - "F0 class, O20, and bijectivity heads / three independent declarations"
      - "F0 diagram-isomorphism witness / IndexedBaseDiagramHomIsoWitness"
      - "F0 per-interpretation conservativity signature / DiagnosticConservative"
    remaining:
      - "all discharge-required rows / F0 fixes signatures only"
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
  vacuity: cannot-determine
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - >-
      cd research/lean && lake env lean
      ResearchLean/AG/DoctrineFiberProduct/DiagnosticConservativitySchema.lean
      / exit 0 / axiom audit: 70 declarations, standard axioms only
    - >-
      cd research/lean && lake build
      ResearchLean.AG.DoctrineFiberProduct.DiagnosticConservativitySchema
      / exit 0 / targeted module only
    - >-
      target #print axioms audit / all 14 reported declarations use only
      propext, Classical.choice, Quot.sound or no axioms
    - >-
      source SHA-256
      c9fafca71e89e1730b9d9159e09fa76e89e4acabfca412f6ba7760ab4985158f
  blocking_findings: []
  next_obligation: K0 closed-language normalization, Mono exclusion, and qualification
```
