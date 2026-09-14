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
- current proof obligation: Cycle 4 AAT common realization and operation-aware complete geometry
- current target state: `target-proof-checkpoint`
- completion candidate: no
- next proof obligation: AAT common realization declaration and operation-aware complete geometry

## Requirement ledger

| 条項 | 要求 | 対応する定義・Lean宣言 | 入力前提 | 構成する証拠 | 使用先 | 未完了部分 |
| --- | --- | --- | --- | --- | --- | --- |
| A | 一つの宣言の下で意味圏と有限構文を独立に構成する | lens宣言群; `ProtocolSchema`, `ProtocolRealization`, `ProtocolPresentation`, `ProtocolPresentation.decoder`; 予備的な`AATReferenceShape`, `FiniteReferenceSkeleton` | lens入力; protocolの有限`Q,L`と任意の観測functor `O`; 任意の依存reference carrier shape | product lens decoder; path/quotient protocol decoder; 有限参照tableの型付けscaffold | Bの二具体適用、Eのモデル同期; 後続のclosed AAT宣言候補の型設計 | primitive由来を固定して完成射の再入力を排除する閉じた`Σ`、AAT parameter interpretation、`D_Θ,R_Θ,P_Θ,F_Θ`、完全幾何、必須三入力族の同一宣言への収録 |
| B0 | 生成部の写像と全域射の`res/ext`往復、構文評価`J` | lens B0宣言群; `ProtocolRealization.GeneratorMap`, `generatorPathNatTrans`, `res`, `ext`, `homEquivGeneratorMap`; `ProtocolPresentation.evaluationEquiv`, `displayedHomEquivGeneratorMap`, `decoder_map_eq_displayedExt_evaluation` | lens保存則; protocolの生成辺可換式と観測保存だけ | lens全域map; path帰納と商帰納による全execution自然変換 | 各decoderの充満性・忠実性 | AAT完全幾何の対応する構成 |
| B 充満性 | 各decoderの充満性を個別に放電する | `lensDecoder_full`, `ProtocolPresentation.decoder_full` | 各具体入力条件のみ | 任意の完成射を制限して有限tableを構成 | 各direct equivalence | AAT完全幾何への適用 |
| B 忠実性 | 各decoderの忠実性を個別に放電する | `lensDecoder_faithful`, `ProtocolPresentation.decoder_faithful` | 各具体入力条件のみ | `res`で各table entryを回復 | 各direct equivalence | AAT完全幾何への適用 |
| B 冪等完備性 | 各意味圏の冪等射を個別に分裂する | `lensRealization_isIdempotentComplete`, `protocolRealization_isIdempotentComplete`; `karoubiReconstructionEquivalence` | 各具体入力条件と任意の冪等射 | lens固定点; objectwise protocol固定点functor | lens/protocolのKaroubi延長とarrow再構成 | AAT意味圏での分裂構成と共通再構成への適用 |
| B retract生成 | 全意味対象をdecoder像のretractとして個別に構成する | lens/protocol各`exists_decoder_retract`; `karoubiObjectOfRetract`, `karoubiMapEssSurj` | 各具体入力条件のみ | fiber列挙; vertexwise列挙; retractからpresentation側冪等元を逆像構成 | `karoubiCompletionEquivalence`, lens/protocolのKaroubi再構成 | AAT完全幾何への適用 |
| B1 | `Kar(P) ≃ R`、decoderの延長、一意性、arrow圏での再構成を同じ四証拠から得る | `karoubiReconstructionEquivalence`, `karoubiReconstructionRestrictionIso`, `karoubiExtensionComparison`, `karoubiExtensionComparison_unique`, `karoubiExtensionComparison_self`, `karoubiExtensionComparison_trans`, `karoubiArrowReconstructionEquivalence`; lens/protocol各適用 | full、faithful、意味圏の冪等完備性、decoder像によるretract生成 | `functorExtension₂`のfull/faithful/essentially-surjective証明、`toKaroubiEquivalence`による延長、fully faithfulな制限から比較同型を逆像構成 | lens/protocol双方のobject・任意arrow再構成 | AAT共通decoderへの同じ適用、分裂選択を明示する具体比較、完全幾何への適用 |
| C | 一様operation flipと同じ射の二つのreading | — | G-117の固定入力 | — | operation保持の必要性 | 全項目未完了 |
| D | G-122の全比較群・底固定群・二種類の核・fiberを表示へ回復する | — | G-122の固定版 | — | n1012第7章から第8章 | 全項目未完了 |
| E lens | CSで独立に定めた全域get/put lensと全ての保存射を有限補完tableから再構成する | `LensData`, `IsTotalLens`, `Hom`, `canonicalNormalFormEquiv`, `canonicalNormalFormIso`, `lensPresentationEquivalence` | 任意の`V`, `v₀`; 非可逆な一般の`Hom`を含む | 正確な`c ↦ (get c, put c v₀)`と逆写像`(v,k) ↦ put k v`; finite列挙との合成; 射の往復 | AATへのlens翻訳、Fの積lens適用 | AATのAtom・Law・operation・完全幾何への往復翻訳、可視変更版、section保存版 |
| E protocol | 有限schemaの関手意味論と生成辺tableの再構成 | `ProtocolSchema.ExecutionCategory`, `ProtocolRealization`, `ProtocolPresentation`, `ProtocolPresentation.presentationEquivalence` | 有限vertex・typed edge・有限parallel path relations `Q,L`; 任意の`O:C_Q⥤Type`; vertexwise有限carrier | 自由path評価、relation quotient、全path `ext`、vertexwise列挙normal form | AAT翻訳、Fのprotocol適用 | operation名変更版、adapter square (P1)、AATとの双方向翻訳、Fへの適用 |
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
      - "GOAL B: four separately required reconstruction properties"
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
review:
  fixed_head: 7846ca4578992b078f117108d76fb3ca178250ad
  audit_comment: "https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4523#issuecomment-5666372803"
  independent_lanes:
    math_a: pass
    math_b: pass-after-noncentral-fix
    lean_a: pass-after-noncentral-fix
    lean_b: pass-after-noncentral-fix
  resolved_findings:
    - "constructed the exact canonical n1015 (L4) equivalence and lens isomorphism with no-unfold component API"
    - "added declaration-level source, position, and premise provenance to new Lean declarations"
    - "recorded the B0 decoder equation F_Theta(f)=ext(J(f)) in every evidence mapping"
    - "separated the four G-123(B) properties from the distinct equation label (B1) and corrected proof-use"
    - "added displayedRes_lensDecoder_map and used it in faithfulness without unfolding decoder internals"
  direct_response:
    reviewed_delta: "173b0a2b99eb75503b7ff084a81c127fb7078afb..7846ca4578992b078f117108d76fb3ca178250ad"
    verdict: pass
    new_findings: []
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

## Cycle 2 — Protocol semantics and finite-presentation reconstruction

```yaml
ledger_type: target_cycle_result
goal: G-123-aat-realization-reconstruction
cycle: 2
goal_blob_sha: 4e5af099ab9b5612db12867ba1546f74bfed9f97
base_oid: 53b68dcd3d44f45f1a3727d12a39f7c62a1d40f7
tracking_issue: 4520
report_path: research/reports/G-123-aat-realization-reconstruction.md
selection:
  proof_state_ref: "Cycle 1 merged at 53b68dcd3; protocol reconstruction remained unchecked"
  proof_dag_predecessors:
    - "n1015 §3.1: finite typed schema, quotient path category, finite-carrier functors over O"
    - "Mathlib.CategoryTheory.Paths: free paths, lift, and generator naturality induction"
    - "Mathlib.CategoryTheory.Quotient: quotient category, soundness, lift, and induction"
    - "Cycle 1 res/ext and fixed-point construction pattern"
  proof_obligation: "A/B/E-protocol: construct the independent protocol category for fixed finite Q,L and arbitrary O, finite generator-table syntax and quotient-path decoder, res/ext/J, fullness, faithfulness, objectwise idempotent splitting, retract generation, and direct category equivalence"
  selection_reason: "This is the second mandatory CS model and preserves named operations, every finite execution, arbitrary observations, and noninvertible adapters before any AAT translation is introduced."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/RealizationReconstruction/ProtocolSchema.lean
    - research/lean/ResearchLean/AG/RealizationReconstruction/ProtocolSemantics.lean
    - research/lean/ResearchLean/AG/RealizationReconstruction/ProtocolReconstruction.lean
    - research/lean/ResearchLean/AG/RealizationReconstruction/ProtocolFinitePresentation.lean
    - research/lean/ResearchLean/AG/RealizationReconstruction/ProtocolIdempotents.lean
  risks:
    - "identifying named edges merely because a realization gives equal functions"
    - "storing a completed path functor or natural transformation in finite syntax"
    - "proving naturality only for named edges and reporting all-execution reconstruction"
    - "requiring the arbitrary observation values O(v) to be finite"
    - "restricting semantic morphisms to isomorphisms or already displayed maps"
    - "deriving idempotent completeness or retract generation only from the direct equivalence"
  unchecked:
    - "AAT common declaration and complete-geometry res/ext/J"
    - "C uniform flip"
    - "D G-122 comparison-group recovery"
    - "E AAT translations in both directions, lens L5/section variant, and protocol adapter square"
    - "F common classification and fixed finite examples"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed a finite named schema and Mathlib quotient path category; defined independent finite-carrier functor semantics over arbitrary O with all observation-preserving natural transformations; extended vertex/edge generator maps to all paths and quotient executions; decoded finite state/edge/observation tables; proved res/ext/J, fullness, faithfulness, finite normal form, explicit retract, objectwise fixed-point splitting, and the protocol presentation equivalence."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/RealizationReconstruction/ProtocolSchema.lean
    - research/lean/ResearchLean/AG/RealizationReconstruction/ProtocolSemantics.lean
    - research/lean/ResearchLean/AG/RealizationReconstruction/ProtocolReconstruction.lean
    - research/lean/ResearchLean/AG/RealizationReconstruction/ProtocolFinitePresentation.lean
    - research/lean/ResearchLean/AG/RealizationReconstruction/ProtocolIdempotents.lean
  evidence:
    - AAT.AG.RealizationReconstruction.ProtocolSchema.relation_sound
    - AAT.AG.RealizationReconstruction.ProtocolSchema.namedEdgeFintype
    - AAT.AG.RealizationReconstruction.ProtocolSchema.relationFintype
    - AAT.AG.RealizationReconstruction.ProtocolRealization.generatorPathNatTrans
    - AAT.AG.RealizationReconstruction.ProtocolRealization.generator_path_naturality
    - AAT.AG.RealizationReconstruction.ProtocolRealization.homEquivGeneratorMap
    - AAT.AG.RealizationReconstruction.ProtocolPresentation.pathFunctor_relation
    - AAT.AG.RealizationReconstruction.ProtocolPresentation.decoder_map_eq_displayedExt_evaluation
    - AAT.AG.RealizationReconstruction.ProtocolPresentation.decoder_full
    - AAT.AG.RealizationReconstruction.ProtocolPresentation.decoder_faithful
    - AAT.AG.RealizationReconstruction.ProtocolPresentation.normalFormIso
    - AAT.AG.RealizationReconstruction.ProtocolPresentation.normalFormIso_hom_app_vertex
    - AAT.AG.RealizationReconstruction.ProtocolPresentation.normalFormIso_inv_app_vertex
    - AAT.AG.RealizationReconstruction.ProtocolPresentation.exists_decoder_retract
    - AAT.AG.RealizationReconstruction.ProtocolPresentation.presentationEquivalence
    - AAT.AG.RealizationReconstruction.ProtocolRealization.fixedPoint_split_id
    - AAT.AG.RealizationReconstruction.ProtocolRealization.fixedPoint_split_e
    - AAT.AG.RealizationReconstruction.ProtocolRealization.protocolRealization_isIdempotentComplete
  claim_mapping:
    source_labels:
      - "GOAL A: protocol mandatory input family"
      - "GOAL B0: res/ext/J and F_Theta(f)=ext(J(f))"
      - "GOAL B: four separately required reconstruction properties"
      - "GOAL E: protocol reconstruction and model synchronization"
      - "n1015 §3.1"
    conjuncts:
      - "finite Q,L with preserved operation names -> ProtocolSchema and ExecutionCategory"
      - "finite reference families -> vertexFintype, namedEdgeFintype, and relationFintype"
      - "independent finite-carrier functors and all observation-preserving natural transformations -> ProtocolRealization and Hom"
      - "vertex maps plus named-edge/observation equations only -> ProtocolRealization.GeneratorMap"
      - "all-path and quotient extension -> generatorPathNatTrans and ProtocolRealization.ext"
      - "finite syntax without completed executions -> ProtocolPresentation"
      - "syntax evaluation and decoder equation -> evaluationEquiv and decoder_map_eq_displayedExt_evaluation"
      - "fullness and faithfulness -> decoder_full and decoder_faithful"
      - "finite presentation and retract -> presentationOf, normalFormIso, exists_decoder_retract"
      - "objectwise idempotent splitting -> fixedPoint, both split equations, protocolRealization_isIdempotentComplete"
      - "direct protocol equivalence -> presentationEquivalence"
    undischarged_assumptions: []
    acceptance_point: "The protocol-family obligation is derived from the fixed Q,L,O inputs. O(v) is not finite; completed path maps, natural transformations, representation, splitting, and retract data are constructed rather than accepted as fields."
    port_status: not-applicable
review:
  initial_head: 8197f349c98def47b5c0646f1be45a483856d9c2
  fixed_head: 3918f3063dbeec697b99cac1f49315f94c5b996e
  audit_comment: "https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4524#issuecomment-5667034655"
  independent_lanes:
    math_a: pass
    math_b: pass
    lean_a: pass-after-central-fix
    lean_b: pass-after-noncentral-fix
  resolved_findings:
    - "connected vertex_finite, edge_finite, and relation_finite to Finite instances and explicit finite reference enumerations"
    - "constructed finite endpoint-labelled NamedEdge without asserting finiteness of observations, all paths, or the quotient category"
    - "added presentationEdgeTable_apply and exact normalFormIso hom/inv vertex-component APIs, removing downstream unfolding"
  validation:
    focused_checks: "5/5 pass"
    namespace_axiom_audits: "43 / 41 / 26 / 81 / 8 declarations, standard axioms only"
    pr_ci: "7/7 pass at fixed_head"
    research_full_build: not-run
  verdict: "Cycle 2 A/B/E-protocol proof obligation discharged; G-123 remains target-proof-checkpoint"
audits:
  premise_delta:
    discharged:
      - "all-path naturality from named-edge squares via Paths.liftNatTrans"
      - "quotient-execution naturality from path naturality via Quotient.induction"
      - "relation descent from the finite generating equations via Quotient.lift"
      - "finite presentation existence from vertexwise finite carriers and transported edge/observation data"
      - "idempotent splitting from the objectwise fixed-point functor and actual idempotence equation"
      - "retract generation from the explicitly constructed finite normal-form isomorphism"
    remaining:
      - "all AAT-wide, comparison, translation, adapter, and common-classification obligations listed above"
  certificate_provenance:
    discharged:
      - "ProtocolSchema relation equations are fixed input L, not completed execution data"
      - "ProtocolPresentation relation and observation proofs are constructed for presentationOf from quotient soundness and semantic naturality"
      - "normalFormIso is constructed from vertexwise finite enumerations and generator extension"
      - "fixedPoint is constructed from the original functor, observation, morphism naturality, and idempotence"
    unresolved: []
  proof_use:
    used:
      - "fixed path relations in quotient soundness, decoder descent, and presentationOf relation compatibility"
      - "edge squares in path-inductive naturality and decoderMap"
      - "observation equations in decodedObservation and all semantic Hom constructions"
      - "vertexwise finiteness in presentationCard/stateEquivFin and normalFormIso"
      - "schema vertex/edge/relation finiteness in the explicit finite reference APIs vertexFintype, namedEdgeFintype, and relationFintype"
      - "idempotence equation in fixedPointRetraction"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: none-found
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused ProtocolSchema.lean: standard axioms only"
    - "focused ProtocolSemantics.lean: standard axioms only"
    - "focused ProtocolReconstruction.lean: standard axioms only"
    - "focused ProtocolFinitePresentation.lean: standard axioms only"
    - "focused ProtocolIdempotents.lean: standard axioms only"
  blocking_findings: []
  next_obligation: "Construct the common AAT realization declaration and operation-aware complete-geometry res/ext/J while preserving the lens and protocol translations as actual two-way applications."
```

## Cycle 3 — Common Karoubi and arrow reconstruction

```yaml
ledger_type: target_cycle_result
goal: G-123-aat-realization-reconstruction
cycle: 3
goal_blob_sha: 4e5af099ab9b5612db12867ba1546f74bfed9f97
base_oid: 9155fc9a2396d53469e3db0f6827fedd29a0440c
tracking_issue: 4520
report_path: research/reports/G-123-aat-realization-reconstruction.md
selection:
  proof_state_ref: "Cycle 2 merged at 9155fc9a2; B1 common extension, uniqueness, coherence, and arrow reconstruction remained unchecked"
  proof_dag_predecessors:
    - "Cycles 1 and 2: separately constructed full, faithful, idempotent-complete, and retract-generation evidence"
    - "Mathlib functorExtension₂ and toKaroubiEquivalence"
    - "G-119 karoubiArrowEquivalence and Mathlib mapArrowEquivalence"
  proof_obligation: "B1: from the four separate reconstruction properties construct Kar(P) ≃ R, identify its restriction with the original decoder, prove coherent uniqueness of extensions, and reconstruct arbitrary arrows; apply the same theorem to both CS models without using their direct equivalences as a shortcut"
  selection_reason: "This discharges the shared categorical engine before the AAT-wide presentation is built and makes proof-use of idempotent completeness and retract generation explicit for both existing CS models."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/RealizationReconstruction/KaroubiReconstruction.lean
    - research/lean/ResearchLean/AG/RealizationReconstruction/KaroubiArrowReconstruction.lean
    - research/lean/ResearchLean/AG/RealizationReconstruction/CSKaroubiReconstruction.lean
  risks:
    - "redefining R as a decoder image or as Kar(P)"
    - "accepting fullness, faithfulness, splitting, or retract data inside syntax or semantic objects"
    - "using the direct lens/protocol equivalence and leaving the required four proofs unused"
    - "proving object equivalence while dropping noninvertible arrows"
    - "asserting uniqueness without a restriction equation or coherence laws"
  unchecked:
    - "AAT common declaration and complete-geometry res/ext/J"
    - "application of B1 to the future AAT decoder and explicit comparison of concrete splitting choices"
    - "C uniform flip"
    - "D G-122 comparison-group recovery"
    - "E AAT translations in both directions, lens L5/section variant, and protocol adapter square"
    - "F common classification and fixed finite examples"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Constructed the induced functor Kar(P) ⟶ Kar(R); proved its faithfulness, fullness, and essential surjectivity from the corresponding decoder proofs and explicit retract generation; removed Kar(R) using separately supplied idempotent completeness; identified restriction with F; constructed the unique comparison of any two extensions with restriction, identity, and transitivity coherence; transported G-119 through the resulting equivalence to reconstruct arbitrary arrows; instantiated all results for the independent lens and protocol models from their named evidence."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/RealizationReconstruction/KaroubiReconstruction.lean
    - research/lean/ResearchLean/AG/RealizationReconstruction/KaroubiArrowReconstruction.lean
    - research/lean/ResearchLean/AG/RealizationReconstruction/CSKaroubiReconstruction.lean
  evidence:
    - AAT.AG.RealizationReconstruction.RetractGeneratedBy
    - AAT.AG.RealizationReconstruction.not_retractGeneratedBy_emptyPresentationDecoder
    - AAT.AG.RealizationReconstruction.karoubiMapFull
    - AAT.AG.RealizationReconstruction.karoubiMapFaithful
    - AAT.AG.RealizationReconstruction.karoubiObjectOfRetract
    - AAT.AG.RealizationReconstruction.karoubiObjectOfRetractIso
    - AAT.AG.RealizationReconstruction.karoubiMapEssSurj
    - AAT.AG.RealizationReconstruction.karoubiReconstructionEquivalence
    - AAT.AG.RealizationReconstruction.karoubiReconstructionRestrictionIso
    - AAT.AG.RealizationReconstruction.karoubiExtensionComparison
    - AAT.AG.RealizationReconstruction.karoubiExtensionComparison_restrict_hom
    - AAT.AG.RealizationReconstruction.karoubiExtensionComparison_unique
    - AAT.AG.RealizationReconstruction.karoubiExtensionComparison_self
    - AAT.AG.RealizationReconstruction.karoubiExtensionComparison_trans
    - AAT.AG.RealizationReconstruction.karoubiArrowReconstructionEquivalence
    - AAT.AG.RealizationReconstruction.LensRealization.lensKaroubiReconstructionEquivalence
    - AAT.AG.RealizationReconstruction.LensRealization.lensKaroubiArrowReconstructionEquivalence
    - AAT.AG.RealizationReconstruction.ProtocolPresentation.protocolKaroubiReconstructionEquivalence
    - AAT.AG.RealizationReconstruction.ProtocolPresentation.protocolKaroubiArrowReconstructionEquivalence
  claim_mapping:
    source_labels:
      - "GOAL B1: Kar(P) ≃ R and arrow reconstruction"
      - "GOAL B: four separately required reconstruction properties"
      - "GOAL E: both CS models and noninvertible changes"
      - "G-119(A1): Kar(Arrow E) ≃ Arrow(Kar E)"
    conjuncts:
      - "full plus faithful -> every Karoubi morphism is lifted by F.preimage and its corner equation is reflected"
      - "retract generation -> every Kar(R) object is represented by the preimage of r ≫ p ≫ i"
      - "idempotent completeness of the independently defined R -> Kar(R) ≃ R"
      - "extension equation -> restriction of the reconstruction functor is naturally isomorphic to F"
      - "extension uniqueness -> fully faithful restriction constructs the comparison and proves self/trans coherence"
      - "arrow reconstruction -> G-119 karoubiArrowEquivalence followed by mapArrowEquivalence"
      - "lens application -> four named lens constructions, not lensPresentationEquivalence"
      - "protocol application -> four named protocol constructions, not presentationEquivalence"
    undischarged_assumptions: []
    acceptance_point: "The common theorem is assumption-relative as permitted by B1, while each CS application discharges all four assumptions from the fixed model input. No semantic category, morphism class, or presentation membership condition is changed."
    port_status: not-applicable
review:
  initial_head: 69aea2d83697add6a728e662d32b4db44ad8a1d9
  fixed_head: 239f1b8d05c77f33451d8a9b170106e1f8290fab
  audit_comment: "https://github.com/iroha1203/AlgebraicArchitectureTheoryV2/pull/4525#issuecomment-5667679327"
  independent_lanes:
    math_a: pass
    math_b: pass-after-noncentral-fix
    lean_a: pass-after-noncentral-fix
    lean_b: pass-after-noncentral-fix
  resolved_findings:
    - "added an actual negative RetractGeneratedBy witness from an empty presentation category to a nonempty semantic category, paired with the lens/protocol positive witnesses"
    - "corrected invented B2/B3/B4 labels to the fixed GOAL B property 1/2/4 wording"
  validation:
    focused_checks: "3/3 pass at fixed_head"
    namespace_axiom_audits: "20 / 1 / 8 declarations, standard axioms only"
    pr_ci: "7/7 pass at fixed_head"
    research_full_build: not-run
  verdict: "Cycle 3 B1 common and two-CS application proof obligation discharged; G-123 remains target-proof-checkpoint"
audits:
  premise_delta:
    discharged:
      - "fullness and faithfulness of Karoubi extension from the corresponding decoder properties"
      - "essential surjectivity of Kar(P) ⟶ Kar(R) from explicit semantic retract generation"
      - "removal of Kar(R) from the separately constructed IsIdempotentComplete proof"
      - "two-CS application assumptions from the exact Cycle 1 and Cycle 2 declarations"
    remaining:
      - "all AAT-wide, comparison, translation, adapter, and common-classification obligations listed above"
  certificate_provenance:
    discharged:
      - "the generic theorem accepts exactly the four B1 properties and does not add them to P or R"
      - "lens/protocol application modules pass named, already constructed proofs from fixed input data"
      - "Karoubi object idempotents are constructed by preimage from the actual retract and Karoubi projector"
    unresolved: []
  proof_use:
    used:
      - "F.Full in morphism and idempotent preimages"
      - "F.Faithful in corner equations and lifted-idempotent proof"
      - "RetractGeneratedBy in essential surjectivity"
      - "IsIdempotentComplete R in toKaroubiEquivalence and the extension restriction isomorphism"
      - "G-119 arrow/Karoubi equivalence in the arrow-level result"
    unused: []
  structure_field_escape: none-found
  route_integrity: pass
  target_fitting: none-found
  vacuity: "positive lens/protocol instances and the empty-presentation/nonempty-semantics negative witness are proved"
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused KaroubiReconstruction.lean: standard axioms only"
    - "focused KaroubiArrowReconstruction.lean: standard axioms only"
    - "focused CSKaroubiReconstruction.lean: standard axioms only"
  blocking_findings: []
  next_obligation: "Construct the common AAT realization declaration and operation-aware complete-geometry res/ext/J, then apply the same B1 theorem from AAT-specific discharged evidence."
```


## Cycle 4 — Parameter-relative AAT primitive references

```yaml
ledger_type: target_cycle_result
goal: G-123-aat-realization-reconstruction
cycle: 4
goal_blob_sha: 4e5af099ab9b5612db12867ba1546f74bfed9f97
base_oid: 77213e96e0f90216355640ca842fefc32f794e7b
tracking_issue: 4520
report_path: research/reports/G-123-aat-realization-reconstruction.md
selection:
  proof_state_ref: "Cycle 3 merge 77213e96e0f90216355640ca842fefc32f794e7b; common AAT declaration and complete-geometry res/ext/J unconstructed"
  proof_dag_predecessors:
    - "n1014 sections 6.2--6.4: all-object, all-endpoint, and all-context generation obligations"
    - "G-122 fixed finite-axis-fold two-cell family"
    - "existing GeometryTotalHom component extensionality, usable only after the component maps are constructed"
  proof_obligation: "A checkpoint: define an unrestricted dependent reference-shape scaffold retaining typed operation endpoints and context owners, keep finiteness at the table level, and connect the fixed G-122 context-object carrier directly; construction of the closed source-provenanced Sigma remains a later obligation"
  selection_reason: "The dependency shape and the fixed input type must be exposed before the closed source-derived declaration, evaluator, or extension can be defined. Existing extensionality lemmas compare already completed maps and therefore cannot supply the missing generators."
  expected_result_type: proof-obligation-checkpoint
  lean_targets:
    - research/lean/ResearchLean/AG/RealizationReconstruction/AATFiniteReferenceSyntax.lean
  risks:
    - "storing a PackageTotalHom, SignedExactCoreReadingHom, GeomReadHom, or GeometryTotalHom under a renamed field"
    - "making the whole parameter, context, coefficient, or local carrier finite"
    - "dropping dependent operation endpoints or the context owner of local data"
    - "treating reference-table completeness as complete-morphism extension"
    - "calling a two-cell reference witness the inclusion of the full G-122 geometry"
  unchecked:
    - "interpretation of primitive references into AAT objects and intrinsic D_Theta"
    - "independent R_Theta and all of P_Theta, F_Theta, G_Theta, C_Theta"
    - "all-object, all-endpoint, and all-context term recursors and evaluation"
    - "AAT complete-geometry res/ext/J and four reconstruction properties"
    - "C uniform flip, D full comparison recovery, E AAT translations, and F classification/examples"
result:
  proposed_result_type: proof-obligation-checkpoint
  proof_obligation_delta: "Defined an unrestricted dependent reference-shape scaffold and finite occurrence tables for source, configuration, object formation, typed operations, laws, invariants, signature axes, contexts, coverage, overlap, Support, Axis, Observable, coefficients, raw coordinates, relations, and restrictions. Finiteness is confined to each table. The generic scaffold does not certify primitive provenance. Added a positive complete table whose carrier is the actual fixed finiteAxisFoldBCDatumSquare context category and a negative first-only table."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/RealizationReconstruction/AATFiniteReferenceSyntax.lean
  evidence:
    - AAT.AG.RealizationReconstruction.AATReferenceShape
    - AAT.AG.RealizationReconstruction.AATReferenceShape.NamedObjectFormation
    - AAT.AG.RealizationReconstruction.AATReferenceShape.NamedOperation
    - AAT.AG.RealizationReconstruction.AATReferenceShape.NamedContext
    - AAT.AG.RealizationReconstruction.AATReferenceShape.NamedRestriction
    - AAT.AG.RealizationReconstruction.FiniteReferenceTable
    - AAT.AG.RealizationReconstruction.FiniteReferenceTable.Complete
    - AAT.AG.RealizationReconstruction.FiniteReferenceSkeleton
    - AAT.AG.RealizationReconstruction.finiteAxisFoldContextReferences_complete
    - AAT.AG.RealizationReconstruction.firstOnlyFiniteAxisFoldContextReferences_not_complete
  claim_mapping:
    source_labels:
      - "GOAL A: finite generator references and typed operation/context dependency requirements"
      - "n1014 section 6.2: recovery targets remain future construction obligations"
      - "n1014 section 6.3: fixed finite-axis-fold context-object carrier"
    input_premises:
      - "an arbitrary AATReferenceShape and parameter theta; no primitive provenance is inferred"
      - "the actual finiteAxisFoldBCDatumSquare.context.Category from the fixed input"
    constructed_evidence:
      - "dependent occurrence types retaining owners and endpoints"
      - "finite tables into possibly infinite carriers"
      - "separately proved positive and negative completeness propositions"
    proof_use:
      - "the occurrence types expose the endpoint/context dependencies which the future closed syntax and evaluator must retain"
      - "the positive table supplies both actual fixed context objects; the negative witness prevents a hidden-completeness reading"
    unfinished:
      - "no semantic realization, decoder, completed morphism, res, ext, or J is constructed in this cycle"
      - "the generic shape does not prove primitive provenance or exclude answer-encoding through arbitrary carrier choices; the closed Sigma must do so"
      - "the full finite-axis-fold core/geometry and its comparisons have not yet been included"
  validation:
    focused_checks: "1/1 pass"
    namespace_axiom_audit: "standard axioms only"
    prerequisite_target_build: "ResearchLean.AG.DoctrineFiberProduct.BCDiagnosticAxisFoldComparisonWitnesses passed as a bounded named target"
    named_target_build: "ResearchLean.AG.RealizationReconstruction.AATFiniteReferenceSyntax passed"
    research_full_build: not-run
  initial_review:
    head: c3e644829a5303fae36c49abb4b5f4f27d46f273
    verdict: "major revisions / reject"
    resolved_findings:
      - "removed the unsupported claim that an unrestricted carrier shape itself proves primitive provenance or excludes type-parameter answer encoding; the closed source-derived Sigma remains explicitly unconstructed"
      - "expanded the shape to distinguish source, configuration, object formation, invariant, signature-axis, coverage, and overlap reference sorts"
      - "retyped the positive and negative tables over the actual finiteAxisFoldBCDatumSquare.context.Category"
      - "added the missing theorem docstring"
      - "restored chronological Cycle 1--4 report order"
  verdict: "Cycle 4 establishes a dependency-shape scaffold and direct fixed-context reference only; primitive provenance and the closed Sigma remain unconstructed, and G-123 remains target-proof-checkpoint"
audits:
  premise_delta:
    discharged:
      - "finite reference tables do not require finite parameter carriers"
      - "operation occurrences retain both typed endpoints"
      - "local occurrences retain their owning object and context"
      - "the fixed reference table is typed by finiteAxisFoldBCDatumSquare.context.Category rather than an unattached two-constructor carrier"
    remaining:
      - "source-derived primitive provenance and exclusion of completed-map answer encoding in the closed Sigma"
      - "all interpretation, generation, semantic-category, reconstruction, comparison, translation, and classification obligations listed above"
  certificate_provenance:
    discharged:
      - "FiniteReferenceSkeleton stores data only; completeness is an external Prop proved for the selected table"
    unresolved:
      - "construct completeness and adequacy from each fixed input, rather than accepting either in a presentation record"
  proof_use:
    used:
      - "the fixed two-cell constructors in the positive and negative table theorems"
    unused: []
  structure_field_escape: "the generic scaffold has unrestricted carriers and therefore is not itself an anti-answer-encoding certificate; this remains explicit and unresolved"
  route_integrity: "checkpoint-only; closed source-derived Sigma not yet constructed"
  target_fitting: "partial reference-shape scaffold; no discharge of GOAL A"
  vacuity: "positive two-entry completeness and negative one-entry incompleteness are both proved"
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused AATFiniteReferenceSyntax.lean: standard axioms only"
  blocking_findings: []
  next_obligation: "Construct the closed source-provenanced Sigma that rules out completed-map answer encoding, then its primitive interpretation and intrinsic D_Theta before the all-object, all-endpoint, and all-context syntax recursors and AAT res/ext/J."
```
