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

Lean 品質基準 §1.4 の正負 instance-pair は未構成なので、この cycle は
受理点ではなく `proof-checkpoint` とする。`DiagnosticConservative` の負例は
固定 target (f) O16 の class 外消失 witnessそのものであり、生成 class 上の
非空な正例は K1 の十分性と K3 (g) の実発火を合成して得る。空 interpretation、
singleton、結論供給 fieldによる先行 pairは GOAL の dullness filter / anti-weakening
に反するため採らない。`DiagnosticClassTerm.eval`、
`GeneratedDiagnosticClass`、`VertexwiseSourceMapBijective` の構造的な正負例も、
同じ instance-pair obligationとして次 cycle以後に固定する。

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
  expected_result_type: proof-checkpoint
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
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: >-
    DiagnosticClassTerm has exactly the two fixed atomic constructors and
    conjunction; its evaluator reads only vertex sourceMap injectivity and
    IsPullback for generated G-111 edge squares.  The ordered three-term
    sequence, independent by-value O20 term, sole bijectivity candidate,
    diagram-isomorphism witness, GeneratedDiagnosticClass, and the
    per-interpretation DiagnosticConservative predicate are now fixed at every
    universe u without any theorem-result input.  The required positive and
    negative instances are not yet constructed, so this is a statement-only
    checkpoint rather than an accepted proof-obligation discharge.
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
      This cycle is not an acceptance point.  It fixes the pre-proof type
      surface named by F0, while positive/negative instances and every
      conservativity, reflection, detection, witness, closure, or Full+Faithful
      result remain unaccepted.
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
      - "positive and negative instance pairs / Lean quality standard section 1.4"
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
      / exit 0 / axiom audit: 60 declarations, standard axioms only
    - >-
      cd research/lean && lake build
      ResearchLean.AG.DoctrineFiberProduct.DiagnosticConservativitySchema
      / exit 0 / targeted module only
    - >-
      target #print axioms audit / all 19 reported declarations use only
      propext, Classical.choice, Quot.sound or no axioms
    - >-
      source SHA-256
      696f4bdb32115526e37edc18008f056f63a72ee8bf3c33129289428a838384c5
  blocking_findings:
    - "F0 predicates are statement-only until positive/negative instance pairs are fixed"
  next_obligation: F0 instance pairs, then K0 normalization, Mono exclusion, and qualification
```
