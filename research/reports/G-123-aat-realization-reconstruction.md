# G-123 — Independent realization and reconstruction from finite presentations

一次仕様は
[`research/goals/G-123-aat-realization-reconstruction.md`](../goals/G-123-aat-realization-reconstruction.md)
である。本reportは固定target A--Fの要求、Lean宣言、入力前提、入力から構成する証拠、
その証拠の使用先、未完了項目をcycleごとに追跡する。

## Proof state

- fixed activation head: `e4d5a0a3b668d2298c727d6145803336e931dee2`
- fixed GOAL blob: `4e5af099ab9b5612db12867ba1546f74bfed9f97`
- common criteria base: `e4d5a0a3b668d2298c727d6145803336e931dee2`
- acceptance contract blob: `eb8e1b230e1106cc3d2c826a037578d8dfea7a1f`
- target-theorem-loop blob: `941ee0b9bf6692f3812204ab74383361eff5b048`
- tracking Issue: [#4520](https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/issues/4520)
- current proof obligation: Cycle 1 lens realization and finite-presentation reconstruction
- current target state: `target-proof-checkpoint`
- completion candidate: no
- next proof obligation: protocol realization and finite-presentation reconstruction

## Requirement ledger

| 条項 | 要求 | 対応する定義・Lean宣言 | 入力前提 | 構成する証拠 | 使用先 | 未完了部分 |
| --- | --- | --- | --- | --- | --- | --- |
| A | 一つの宣言の下で意味圏と有限構文を独立に構成する | `LensData`, `IsTotalLens`, `LensRealization`, `LensPresentation`, `lensDecoder` | `V`, `v₀`, 三つのlens法則、有限な基準fiber | product decoderと有限table構文 | Bのlens具体適用、Eのモデル同期 | AAT共通宣言、完全幾何、必須三入力族の同一宣言への収録 |
| B0 | 生成部の写像と全域射の`res/ext`往復、構文評価`J` | `res`, `ext`, `homEquivFiberMap`, `displayedRes`, `displayedExt`, `displayedHomEquivGeneratorMap`, `evaluationEquiv`, `lensDecoder_map_eq_displayedExt_evaluation` | 完成射は`get`と`put`を保存。生成写像は有限fiber間の関数のみ | `res_ext`, `ext_res`, `displayedRes_displayedExt`, `displayedExt_displayedRes`, `F_Θ(f)=ext(J(f))` | decoderの充満性・忠実性 | protocolとAAT完全幾何の対応する構成 |
| B1 | 充満性、忠実性、冪等完備性、retract生成を個別に放電する | `lensDecoder_full`, `lensDecoder_faithful`, `lensRealization_isIdempotentComplete`, `exists_decoder_retract` | lens入力条件のみ | finite table、固定点lens、fiber列挙によるnormal form | `lensPresentationEquivalence` | 共通Karoubi延長、arrow再構成、分裂選択の自然同型、AAT完全幾何への適用 |
| C | 一様operation flipと同じ射の二つのreading | — | G-117の固定入力 | — | operation保持の必要性 | 全項目未完了 |
| D | G-122の全比較群・底固定群・二種類の核・fiberを表示へ回復する | — | G-122の固定版 | — | n1012第7章から第8章 | 全項目未完了 |
| E lens | CSで独立に定めた全域get/put lensと全ての保存射を有限補完tableから再構成する | `LensData`, `IsTotalLens`, `Hom`, `canonicalNormalFormEquiv`, `canonicalNormalFormIso`, `lensPresentationEquivalence` | 任意の`V`, `v₀`; 非可逆な一般の`Hom`を含む | 正確な`c ↦ (get c, put c v₀)`と逆写像`(v,k) ↦ put k v`; finite列挙との合成; 射の往復 | AATへのlens翻訳、Fの積lens適用 | AATのAtom・Law・operation・完全幾何への往復翻訳、可視変更版、section保存版 |
| E protocol | 有限schemaの関手意味論と生成辺tableの再構成 | — | `Q,L,O` | — | AAT翻訳、Fのprotocol適用 | 全項目未完了 |
| F | 操作連結性による分裂短完全列・核・torsor、二つのCS適用、三有限例 | — | `Q,K,H` | — | D・Eとの共通分類 | 全項目未完了 |

## Cycle 1 — Lens semantics and finite-presentation reconstruction

```yaml
ledger_type: target_cycle_result
goal: G-123-aat-realization-reconstruction
cycle: 1
goal_blob_sha: 4e5af099ab9b5612db12867ba1546f74bfed9f97
base_oid: 2fc3de3f612a8df26d32181694ecf8930d094106
tracking_issue: 4520
report_path: research/reports/G-123-aat-realization-reconstruction.md
selection:
  proof_state_ref: "Issue #4520 initial state: A--F future proof obligations"
  proof_dag_predecessors:
    - "n1015 (L1)--(L4): independent total-lens semantics and finite complement normal form"
    - "Mathlib.CategoryTheory.Equivalence: full-faithful-essentially-surjective criterion"
    - "Mathlib.CategoryTheory.Idempotents.Basic: IsIdempotentComplete"
  proof_obligation: "A/B/E-lens: construct the independent total-lens category with all get/put-preserving maps, finite table syntax and decoder, res/ext/J, fullness, faithfulness, idempotent splitting, retract generation, and the resulting category equivalence"
  selection_reason: "This constructs an independent semantic category and simultaneously discharges one complete CS instance of A/B; its res/ext pattern is a direct predecessor for the protocol and AAT complete-geometry constructions."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/RealizationReconstruction/LensSemantics.lean
    - research/lean/ResearchLean/AG/RealizationReconstruction/LensFinitePresentation.lean
  risks:
    - "defining semantic objects or morphisms by decoder image"
    - "storing extension existence or uniqueness in generator data"
    - "restricting morphisms to equivalences and losing noninvertible finite tables"
    - "deriving idempotent completeness or retract generation only from res/ext without separate constructions"
    - "calling the lens equivalence the completed AAT realization reconstruction"
  unchecked:
    - "AAT common declaration and complete-geometry res/ext/J"
    - "protocol reconstruction"
    - "C uniform flip"
    - "D G-122 comparison-group recovery"
    - "E AAT translations in both directions"
    - "F classification and fixed finite examples"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed the independent semantic category before the decoder; proved restriction and extension inverse on complete lens maps; constructed finite table syntax and evaluation; proved decoder fullness and faithfulness; enumerated the finite reference fiber to construct every object's normal form and explicit retract; split every idempotent through its fixed-point lens; and obtained the lens presentation equivalence."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/RealizationReconstruction/LensSemantics.lean
    - research/lean/ResearchLean/AG/RealizationReconstruction/LensFinitePresentation.lean
  evidence:
    - AAT.AG.RealizationReconstruction.LensRealization.homEquivFiberMap
    - AAT.AG.RealizationReconstruction.LensRealization.displayedHomEquivGeneratorMap
    - AAT.AG.RealizationReconstruction.LensRealization.lensDecoder_map_eq_displayedExt_evaluation
    - AAT.AG.RealizationReconstruction.LensRealization.canonicalNormalFormEquiv
    - AAT.AG.RealizationReconstruction.LensRealization.canonicalNormalFormIso
    - AAT.AG.RealizationReconstruction.LensRealization.canonicalNormalFormIso_hom_apply
    - AAT.AG.RealizationReconstruction.LensRealization.canonicalNormalFormIso_inv_apply
    - AAT.AG.RealizationReconstruction.LensRealization.lensDecoder_full
    - AAT.AG.RealizationReconstruction.LensRealization.lensDecoder_faithful
    - AAT.AG.RealizationReconstruction.LensRealization.normalFormIso
    - AAT.AG.RealizationReconstruction.LensRealization.exists_decoder_retract
    - AAT.AG.RealizationReconstruction.LensRealization.fixedPoint_split_id
    - AAT.AG.RealizationReconstruction.LensRealization.fixedPoint_split_e
    - AAT.AG.RealizationReconstruction.LensRealization.lensRealization_isIdempotentComplete
    - AAT.AG.RealizationReconstruction.LensRealization.lensPresentationEquivalence
  claim_mapping:
    theorem_names:
      - homEquivFiberMap
      - displayedHomEquivGeneratorMap
      - lensDecoder_map_eq_displayedExt_evaluation
      - canonicalNormalFormEquiv
      - canonicalNormalFormIso
      - canonicalNormalFormIso_hom_apply
      - canonicalNormalFormIso_inv_apply
      - lensDecoder_full
      - lensDecoder_faithful
      - exists_decoder_retract
      - lensRealization_isIdempotentComplete
      - lensPresentationEquivalence
    source_labels:
      - "GOAL A: lens mandatory input family"
      - "GOAL B0: res/ext/J"
      - "GOAL B(1)--(4): four reconstruction properties"
      - "GOAL E: model synchronization"
      - "n1015 (L1)--(L4)"
    conjuncts:
      - "independent semantic objects and all get/put-preserving morphisms -> LensRealization and Hom"
      - "finite generator data without completed maps -> Fiber maps and LensPresentation.GeneratorMap"
      - "restriction/extension inverse -> res_ext and ext_res"
      - "finite syntax evaluation bijection -> evaluationEquiv and displayedHomEquivGeneratorMap"
      - "decoder equation -> lensDecoder_map_eq_displayedExt_evaluation proves F_Theta(f)=ext(J(f))"
      - "exact canonical L4 normal form -> canonicalNormalFormEquiv and canonicalNormalFormIso"
      - "fullness/faithfulness -> lensDecoder_full and lensDecoder_faithful"
      - "idempotent splitting -> fixedPointLens and split equations"
      - "finite enumeration connection and retract generation -> normalFormIso and exists_decoder_retract"
      - "category equivalence -> lensPresentationEquivalence"
    undischarged_assumptions: []
    acceptance_point: "The lens-family obligation is derived from the fixed CS inputs; none of fullness, faithfulness, splitting, retract generation, or completed morphism data is a theorem input or object-membership condition."
    port_status: not-applicable
audits:
  premise_delta:
    discharged:
      - "extension existence and uniqueness from the three lens laws via res_ext/ext_res"
      - "exact canonical L4 normal form from the lens laws via canonicalNormalFormEquiv/canonicalNormalFormIso"
      - "finite presentation existence from finite reference fiber by transporting the complement into the exact canonical normal form"
      - "idempotent splitting from the fixed-point carrier and the actual idempotent map"
      - "retract generation from the explicitly constructed normal-form isomorphism"
    remaining:
      - "all AAT-wide, protocol, comparison, translation, and common-classification obligations listed above"
  certificate_provenance:
    discharged:
      - "IsTotalLens laws are the fixed n1015 semantic inputs, not reconstruction conclusions"
      - "canonicalNormalFormIso is constructed directly from get/put and the lens laws"
      - "normalFormIso composes finite Fiber enumeration with canonicalNormalFormIso.symm"
      - "fixedPointCondition is constructed from the original lens laws and idempotent"
    unresolved: []
  proof_use:
    used:
      - "put_get/get_put/put_put in ext inverse laws and normal form"
      - "finite_fiber in presentationOf and normalFormIso"
      - "get_naturality/put_naturality in res and ext uniqueness"
      - "idempotence equation in fixedPointRetraction"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused LensSemantics.lean: standard axioms only"
    - "focused LensFinitePresentation.lean: standard axioms only"
  blocking_findings: []
  next_obligation: "Construct protocol semantics, finite generator tables, res/ext/J, and the four reconstruction properties without restricting the independently defined natural transformations."
```
