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
- current proof obligation: Cycle 10 finite operation-reference obstruction and admissible-range decision
- current target state: `target-proof-checkpoint`
- completion candidate: no
- next proof obligation: construct an intrinsic non-circular `D_Theta` whose required input families have finite recursive presentations, or prove that a mandatory input family contains the Cycle 10 obstruction without re-inputting a completed operationMap

## Requirement ledger

| 条項 | 要求 | 対応する定義・Lean宣言 | 入力前提 | 構成する証拠 | 使用先 | 未完了部分 |
| --- | --- | --- | --- | --- | --- | --- |
| A | 一つの宣言の下で意味圏と有限構文を独立に構成する | lens宣言群; `ProtocolSchema`, `ProtocolRealization`, `ProtocolPresentation`, `ProtocolPresentation.decoder`; 予備的な`AATReferenceShape`, `FiniteReferenceSkeleton`; `G122FamilyInput`, `G122CellInput`; `ClosedFamilyParameter.g122`, `FamilyRealization.g122`, 対象依存の`PrimitiveAtom`/`PrimitiveSource`/`PrimitiveObject`/`PrimitiveContext`とG-122のsignature/equation/invariant/raw各role; `PrimitiveOperation.g122Ref`, `g122Value`, `g122ConfigurationMap`; `OperationTag`, `sequenceTaggedOperationPackage`, `no_surjectiveEndomorphismDecoder_of_listGeneratedCode` | lensの`V,v₀`; protocolの有限`Q,L`と任意の観測functor `O`; G-117のnullary tag; G-122の任意の`A,z,omega,k,g_z`; Cycle 10の候補失敗ではopaqueな`Nat → Bool` operation tag | product lens decoder; path/quotient protocol decoder; 閉じた4枝dispatch; G-122原入力から`fixedGeometry`, `sourceTransport`, `compatibleProblemData`, `barBeta`を出力として組み立て、同じ一般branchへ入れる依存分解; 原supportの各operation identityとconfiguration作用の端点付き評価; 全tag変換を実際のpackage endomorphismへ埋め込み、有限tag参照listからの全射decoderを対角化で否定 | Bの二具体適用、Eのモデル同期; 後続の非循環な`D_Theta`とG-122有限operation生成規則、branch別interpretation、closed presentation設計; Dの量化保持 | Cycle 10 obstructionを避ける内在的生成条件と必須入力からの放電、G-122 operation族の有限生成・全域operationMap回復、branch別primitive interpretation、G-122原入力の有限構文化とinterpretation、有限`Σ`、`D_Θ,R_Θ,P_Θ,F_Θ`、完全幾何 |
| B0 | 生成部の写像と全域射の`res/ext`往復、構文評価`J` | lens B0宣言群; `ProtocolRealization.GeneratorMap`, `generatorPathNatTrans`, `res`, `ext`, `homEquivGeneratorMap`; `ProtocolPresentation.evaluationEquiv`, `displayedHomEquivGeneratorMap`, `decoder_map_eq_displayedExt_evaluation` | lens保存則; protocolの生成辺可換式と観測保存だけ | lens全域map; path帰納と商帰納による全execution自然変換 | 各decoderの充満性・忠実性 | AAT完全幾何の対応する構成 |
| B 充満性 | 各decoderの充満性を個別に放電する | `lensDecoder_full`, `ProtocolPresentation.decoder_full` | 各具体入力条件のみ | 任意の完成射を制限して有限tableを構成 | 各direct equivalence | AAT完全幾何への適用 |
| B 忠実性 | 各decoderの忠実性を個別に放電する | `lensDecoder_faithful`, `ProtocolPresentation.decoder_faithful` | 各具体入力条件のみ | `res`で各table entryを回復 | 各direct equivalence | AAT完全幾何への適用 |
| B 冪等完備性 | 各意味圏の冪等射を個別に分裂する | `lensRealization_isIdempotentComplete`, `protocolRealization_isIdempotentComplete`; `karoubiReconstructionEquivalence` | 各具体入力条件と任意の冪等射 | lens固定点; objectwise protocol固定点functor | lens/protocolのKaroubi延長とarrow再構成 | AAT意味圏での分裂構成と共通再構成への適用 |
| B retract生成 | 全意味対象をdecoder像のretractとして個別に構成する | lens/protocol各`exists_decoder_retract`; `karoubiObjectOfRetract`, `karoubiMapEssSurj` | 各具体入力条件のみ | fiber列挙; vertexwise列挙; retractからpresentation側冪等元を逆像構成 | `karoubiCompletionEquivalence`, lens/protocolのKaroubi再構成 | AAT完全幾何への適用 |
| B1 | `Kar(P) ≃ R`、decoderの延長、一意性、arrow圏での再構成を同じ四証拠から得る | `karoubiReconstructionEquivalence`, `karoubiReconstructionRestrictionIso`, `karoubiExtensionComparison`, `karoubiExtensionComparison_unique`, `karoubiExtensionComparison_self`, `karoubiExtensionComparison_trans`, `karoubiArrowReconstructionEquivalence`; lens/protocol各適用 | full、faithful、意味圏の冪等完備性、decoder像によるretract生成 | `functorExtension₂`のfull/faithful/essentially-surjective証明、`toKaroubiEquivalence`による延長、fully faithfulな制限から比較同型を逆像構成 | lens/protocol双方のobject・任意arrow再構成 | AAT共通decoderへの同じ適用、分裂選択を明示する具体比較、完全幾何への適用 |
| C | 一様operation flipと同じ射の二つのreading | `taggedUniformFlipTotal_square`, `taggedUniformFlipTotal_commutes_normalization`, `taggedNormalizationThenUniformFlip_ne_normalization`, `taggedNormalizationThenUniformFlipKaroubiAut`, `fixedArchitectureObjectFunctor`, `fixedArchitectureObjectFunctor_identifies_uniform_flip`, `fixedArchitectureObjectFunctor_not_injective_at_tagged`, `taggedUniformFlipTotal_ne_endpointFlipTotal` | G-117の固定`taggedOperationPackage`とadmissibility | 全端点・全operationの一様Bool tag反転、package射の`t²=1`、`et=te`、指定operation評価による`et≠e`、Karoubi自己同型、固定点関手と非忠実性witness | 固定点関手は同じKaroubi二射`et,e`の像を同一視する | Aで構成するoperation保持実現へ同じ二射を送り、像が異なることの接続 |
| D | G-122の全比較群・底固定群・二種類の核・fiberを表示へ回復する | `G122FamilyInput`, `G122CellInput`, `ClosedFamilyParameter.g122`, `FamilyRealization.g122`, `PrimitiveOperation.g122Ref`, `G122CellInput.fixedGeometry`, `G122CellInput.sourceTransport`, `G122CellInput.compatibleProblemData`, `G122CellInput.barBeta`, `finiteAxisFoldParameter`, `finiteAxisFoldRealization`, `finiteAxisFoldOperationReference` | G-122の固定版にある任意の`A,z,omega,k,g_z`; 固定有限axis-fold例 | 原入力と生成出力を分離し、任意のcell inputを共通familyの意味対象にし、元の有限例を同じ一般branchへ入れ、supportの全端点の各operation identityを参照し、同じ実際の`barBeta`を生成する証拠 | 将来のG-122 branch interpretationと表示回復 | operation族の有限生成・全域写像回復とprimitive interpretation、比較群・section・底/係数成分・二種類の核・各lift fiberの全元の表示回復と三場合分類は未完了 |
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

## Cycle 5 — Closed family dispatch and object-dependent primitive sorts

```yaml
ledger_type: target_cycle_result
goal: G-123-aat-realization-reconstruction
cycle: 5
goal_blob_sha: 4e5af099ab9b5612db12867ba1546f74bfed9f97
base_oid: 6ac24eeb055bee6287911c2ff1c3bc1556d34e87
tracking_issue: 4520
report_path: research/reports/G-123-aat-realization-reconstruction.md
selection:
  proof_state_ref: "Cycle 4 merged at 6ac24eeb0; its unrestricted carrier shape was explicitly not the final source-provenanced Sigma"
  proof_dag_predecessors:
    - "Cycle 1 independent lens semantics over fixed V,v0"
    - "Cycle 2 independent protocol semantics over fixed Q,L,O"
    - "G-117 fixed tagged-operation package and operation family"
    - "G-122 fixed finite-axis-fold primitive source indices"
  proof_obligation: "A/C: replace arbitrary carrier dispatch by one closed four-branch family parameter, preserve the order theta then arbitrary semantic X in the CS branches, generate endpoint/object-dependent primitive names without a constructor for completed AAT maps, and construct the fixed G-117 uniform operation action"
  selection_reason: "The closed dispatch is required before a source-derived presentation can be stated without letting a caller choose arbitrary carrier roles that quote the desired answer."
  expected_result_type: target-proof-checkpoint
  lean_targets:
    - research/lean/ResearchLean/AG/RealizationReconstruction/AATClosedFamilySignature.lean
  risks:
    - "calling the closed family tag alone the final finite Sigma"
    - "placing a completed lens, protocol realization, AAT package, geometry map, or comparison element in theta"
    - "making source sorts depend only on theta although CS values depend on X"
    - "losing typed protocol endpoints or reducing the G-117 flip to selected endpoints"
    - "using the fixed G-122 witness tag as the general G-122 input family"
  unchecked:
    - "branch-specific primitive interpretation and generated equations"
    - "general G-122 primitive input decomposition without sourceTransport or completed geometry"
    - "closed finite presentation Sigma and intrinsic D_Theta"
    - "AAT complete-geometry res/ext/J and four reconstruction properties"
    - "C package-morphism equality t^2=1 and comparison with normalization, including commutation and inequality"
    - "D comparison-group recovery"
    - "E bidirectional AAT translations"
    - "F classification and fixed finite examples"
result:
  proposed_result_type: target-proof-checkpoint
  proof_obligation_delta: "Constructed one closed tagged union containing G-117, fixed G-122, lens, and protocol branches. Lens theta contains only V,v0; protocol theta contains only Q,L,O, after which their arbitrary independent semantic X is quantified. Defined role-specific Atom, Source, Object, endpoint-indexed Operation, and object-indexed Context constructors. The fixed G-117 branch now uses its actual ArchitectureObject endpoints and existing tagged operations; its uniform Boolean flip is separately constructed as one actual package endomorphism. Lens Read and Write=CxV endpoints are distinct, protocol edges retain typed endpoints, and every listed fixed G-122 source role is branch-indexed."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/RealizationReconstruction/AATClosedFamilySignature.lean
  evidence:
    - AAT.AG.RealizationReconstruction.LensFamilyInput
    - AAT.AG.RealizationReconstruction.ProtocolFamilyInput
    - AAT.AG.RealizationReconstruction.ClosedFamilyParameter
    - AAT.AG.RealizationReconstruction.FamilyRealization
    - AAT.AG.RealizationReconstruction.PrimitiveAtom
    - AAT.AG.RealizationReconstruction.PrimitiveSource
    - AAT.AG.RealizationReconstruction.protocolObservationValue
    - AAT.AG.RealizationReconstruction.LensPrimitiveObject.Carrier
    - AAT.AG.RealizationReconstruction.PrimitiveObject
    - AAT.AG.RealizationReconstruction.PrimitiveOperation
    - AAT.AG.RealizationReconstruction.PrimitiveContext
    - AAT.AG.RealizationReconstruction.PrimitiveDiagnosticCell
    - AAT.AG.RealizationReconstruction.taggedOperation
    - AAT.AG.RealizationReconstruction.taggedUniformFlipAction
    - AAT.AG.RealizationReconstruction.taggedUniformFlipAction_involutive
    - AAT.AG.RealizationReconstruction.taggedUniformFlipTotal
    - AAT.AG.RealizationReconstruction.taggedUniformFlipTotal_operationMap
    - AAT.AG.RealizationReconstruction.taggedUniformFlipSquare_operationMap
    - AAT.AG.RealizationReconstruction.protocolEdge
    - AAT.AG.RealizationReconstruction.FiniteAxisFoldSignatureAxis
    - AAT.AG.RealizationReconstruction.PrimitiveSignatureAxis
    - AAT.AG.RealizationReconstruction.PrimitiveSignatureCoordinate
    - AAT.AG.RealizationReconstruction.PrimitiveEquationIndex
    - AAT.AG.RealizationReconstruction.PrimitiveInvariantIndex
    - AAT.AG.RealizationReconstruction.PrimitiveCoordinateIndex
    - AAT.AG.RealizationReconstruction.PrimitiveRelationIndex
  claim_mapping:
    source_labels:
      - "GOAL A: one common declaration and mandatory input families"
      - "GOAL C: one uniform package self-map acting at every endpoint pair"
      - "GOAL E: independent lens and protocol inputs and arbitrary semantic objects"
      - "n1015 L1-L2 and protocol section 3.1"
      - "fixed G-122 finite-axis-fold primitive indices"
    input_premises:
      - "lens View type and reference value only"
      - "finite protocol schema and arbitrary observation functor only"
      - "no payload for the two fixed AAT branch tags"
    constructed_evidence:
      - "closed parameter dispatch"
      - "semantic object family depending on theta"
      - "source sorts depending on both theta and X"
      - "endpoint-indexed operation names and object-indexed contexts"
      - "one actual G-117 package self-map whose operation action is involutive at every endpoint"
    proof_use:
      - "LensRealization and ProtocolRealization occur as independently quantified FamilyRealization branches"
      - "protocolEdge retains source, target, and the original edge value"
      - "taggedOperation takes the actual fixed package operation at its actual ArchitectureObject endpoints"
      - "taggedUniformFlipTotal applies taggedUniformFlipAction to every such operation and its action is involutive"
      - "lensGet has Read-to-View endpoints and lensPut has Write=CxV-to-State endpoints"
      - "LensPrimitiveObject.Carrier makes Read and State the same X.Carrier and Write definitionally X.Carrier x View"
      - "protocol observations are derived by protocolObservationValue from a generating state and are not an independent Source summand"
      - "the G-122 branch separately indexes FiniteModel.FiniteAtom, FiniteModel.ExtractionSource, signature Axis and Coordinate as Fin 3, equation/invariant as PUnit, raw coordinate/relation as Unit, every source ArchCtx, and the outer DoubleDiamondTwoCell PUnit diagnostic role"
    unfinished:
      - "this closed family signature is not yet the finite presentation Sigma"
      - "no branch interpretation, decoder, D_Theta, res, ext, J, or reconstruction proof is asserted"
      - "the general G-122 source input is not represented; the nullary branch records only the required fixed example"
  validation:
    focused_checks: "1/1 pass"
    namespace_axiom_audit: "371 declarations, standard axioms only"
    declaration_scan: "no data constructor accepts a completed AAT/core/geometry map, decoder, extension, comparison element, splitting, or retract; the constructed taggedUniformFlipTotal occurs only as a derived def result"
    research_full_build: not-run
  verdict: "Cycle 5 fixes the common family quantification and role-dependent primitive-name layer only; GOAL A and G-123 remain incomplete"
audits:
  premise_delta:
    discharged:
      - "the common parameter family is a closed four-constructor union rather than an arbitrary carrier shape"
      - "lens and protocol semantic objects occur after theta and are not stored in theta"
      - "primitive CS values depend on X where their source types require it"
      - "the G-117 branch is fixed to the actual source-derived object and operation families, closing the former arbitrary-Type quote escape"
      - "one uniform G-117 action and package self-map are constructed for every actual endpoint and operation"
      - "lens Read and Write endpoint roles retain get:C->V and put:CxV->C arities"
      - "protocol operation names retain their typed endpoints"
    remaining:
      - "construct every primitive interpretation and prove that role-specific arbitrary values cannot be consumed as completed AAT maps"
      - "derive the general G-122 input from raw finite data without accepting sourceTransport or completed comparison data"
      - "all presentation, geometry, reconstruction, comparison, translation, and classification obligations"
  certificate_provenance:
    discharged:
      - "theta stores only the independent CS inputs admitted by n1015 and nullary tags for the fixed AAT examples"
    unresolved:
      - "future presentation adequacy and interpretation must be constructed rather than stored"
  proof_use:
    used:
      - "lens V,v0 in the LensRealization branch and lens primitive roles"
      - "protocol Q,L,O in ProtocolRealization and typed primitive roles"
      - "fixed G-122 Atom, extraction source, signature axis/coordinate, equation/invariant, raw coordinate/relation, and diagnostic-cell source types"
      - "all fixed G-122 ArchCtx values are context names, while outer diagnostic cells remain a distinct role"
    unused: []
  structure_field_escape: "no completed AAT/core/geometry map, decoder, extension, comparison element, splitting, or retract field; the G-117 arbitrary-Type escape was removed; authorized arbitrary CS values have only role-specific constructors"
  route_integrity: "checkpoint-only; the closed presentation and interpretations remain future obligations"
  target_fitting: "partial GOAL A source-signature construction; no final Sigma or reconstruction claim"
  vacuity: "mandatory branches and typed constructors are inhabited directly"
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused AATClosedFamilySignature.lean: standard axioms only"
  blocking_findings: []
  next_obligation: "Construct branch-specific primitive interpretations and the general G-122 raw primitive input before defining the finite presentation Sigma or intrinsic D_Theta."
initial_review:
  head: df5a75ecd0e7351b4c46de1e8cec477f7525a46e
  verdict: major-revisions
  central_findings:
    - "the G-117 branch accepted arbitrary ObjectName types and values, permitting renamed completed-map quotation"
    - "uniformFlip was incorrectly represented as an operation token rather than one action on every actual tagged operation"
    - "lens put had State-to-State endpoints rather than Write=CxV-to-State"
    - "G-122 Fin 3 and singleton roles were global aliases rather than branch-indexed primitive roles"
  direct_response:
    - "fixed the G-117 branch to the source ArchitectureObject and taggedOperationPackage operation families"
    - "constructed taggedUniformFlipAction, its involutivity theorem, and taggedUniformFlipTotal as an actual package endomorphism"
    - "added distinct lensRead and lensWrite object roles and corrected get/put endpoints"
    - "added the missing branch-indexed G-122 signature-coordinate role"
  rerun_required: true
review_round_2:
  head: d86c710e633888b3e16ae08877d03ec85fb5f161
  verdict: major-revisions
  central_findings:
    - "the fixed G-122 signature Coordinate role was missing and raw Unit roles were conflated with PUnit equation/invariant roles"
    - "outer diagnostic cells were incorrectly used as complete-geometry contexts instead of being separated from all source ArchCtx values"
  noncentral_findings:
    - "the report key for the rejected first-round snapshot was named fixed_head"
  direct_response:
    - "added branch-indexed signature Coordinate and distinct PUnit/Unit roles"
    - "made PrimitiveContext range over every source ArchCtx and moved DoubleDiamondTwoCell to PrimitiveDiagnosticCell"
    - "listed package-level t^2=1 explicitly among the unfinished C obligations"
    - "renamed the rejected-snapshot report key to head"
  rerun_required: true
review_round_3:
  head: 76a27c0daf4aa22e1d06e4665f6f80c2b40f0ed3
  verdict: major-revisions
  central_findings:
    - "lens Read/Write were distinct names but their C and CxV carrier interpretation was not yet fixed"
    - "signature Coordinate did not retain its parent Axis dependency"
    - "protocol Source incorrectly included arbitrary unattached O(v) values beyond the fixed n1015 source sum"
  noncentral_findings:
    - "the top-level C ledger had not recorded the partial uniform-flip construction"
  direct_response:
    - "introduced LensPrimitiveObject.Carrier with Read=State=X.Carrier and Write=X.Carrier x View definitionally"
    - "indexed PrimitiveSignatureCoordinate by its PrimitiveSignatureAxis parent"
    - "removed protocolObservation from PrimitiveSource and derived protocolObservationValue from a generating state"
    - "synchronized the top-level C ledger while retaining package-level square and comparison obligations as unfinished"
  rerun_required: true
```

## Cycle 6 — Uniform package flip and the fixed Karoubi witness

```yaml
ledger_type: target_cycle_result
goal: G-123-aat-realization-reconstruction
cycle: 6
goal_blob_sha: 4e5af099ab9b5612db12867ba1546f74bfed9f97
base_oid: f6c26ae4b7820e04d0d02a57c602603bb94366b3
tracking_issue: 4520
report_path: research/reports/G-123-aat-realization-reconstruction.md
selection:
  proof_state_ref: "Cycle 5 merged at f6c26ae4b; it constructed the uniform action and package self-map but left every package-level C equation open"
  proof_dag_predecessors:
    - "G-117 fixed taggedOperationPackage, canonical normalization, admissibility, and taggedBoolOperation"
    - "Cycle 5 taggedUniformFlipAction and taggedUniformFlipTotal at all actual endpoints"
    - "G-119 canonicalPackageNormalization and normalizedPackageKaroubiObject"
  proof_obligation: "C: prove the uniform flip is a package involution, commutes with the fixed canonical normalization, gives et distinct from e at the mandated false-tag operation, forms a nonidentity Karoubi automorphism, and is identified only by the object-only reader"
  selection_reason: "These are the remaining fixed equations for C and use the already constructed all-endpoint action without shrinking the object or morphism family."
  expected_result_type: proof-obligation-discharged
  lean_targets:
    - research/lean/ResearchLean/AG/RealizationReconstruction/AATUniformFlipKaroubi.lean
  risks:
    - "proving involutivity only at one operation rather than as PackageTotalHom equality"
    - "using absorption in place of the required two-sided commutation"
    - "changing the endpoint or operation used for et != e"
    - "calling an arbitrary raw endomorphism a Karoubi automorphism without constructing its sandwich law and inverse"
    - "conflating the new uniform flip with the old endpoint-dependent G-117 counterexample"
  unchecked:
    - "general G-122 raw primitive input and branch interpretations"
    - "closed finite presentation Sigma and intrinsic D_Theta"
    - "AAT complete-geometry res/ext/J and four reconstruction properties"
    - "D comparison-group recovery"
    - "E bidirectional AAT translations"
    - "F classification and fixed finite examples"
result:
  proposed_result_type: proof-obligation-discharged
  proof_obligation_delta: "Lifted the pointwise uniform action to a complete package equality t^2=1; proved et=te by commuting the dependent tagged-operation cast with Boolean negation; evaluated et and e on the original taggedBoolOperation to prove et!=e; constructed et with its sandwich law and itself as inverse in the actual normalized Karoubi object; constructed the fixed-architecture-object functor on the Karoubi category and its explicit nonfaithfulness witness at et/e; and separately proved the uniform flip is not the old endpoint-dependent flip. The direct operation evaluation is not claimed to be A's unfinished operation-preserving realization."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/RealizationReconstruction/AATUniformFlipKaroubi.lean
  evidence:
    - AAT.AG.RealizationReconstruction.taggedOperationCast_uniformFlip
    - AAT.AG.RealizationReconstruction.taggedUniformFlipTotal_square
    - AAT.AG.RealizationReconstruction.taggedUniformFlipTotal_commutes_normalization
    - AAT.AG.RealizationReconstruction.taggedNormalizationThenUniformFlip_snd
    - AAT.AG.RealizationReconstruction.taggedNormalization_snd
    - AAT.AG.RealizationReconstruction.taggedNormalizationThenUniformFlip_ne_normalization
    - AAT.AG.RealizationReconstruction.taggedUniformFlipTotal_ne_endpointFlipTotal
    - AAT.AG.RealizationReconstruction.taggedNormalizationThenUniformFlipKaroubiHom
    - AAT.AG.RealizationReconstruction.taggedNormalizationThenUniformFlipKaroubiHom_ne_id
    - AAT.AG.RealizationReconstruction.taggedUniformFlipMorphism_square
    - AAT.AG.RealizationReconstruction.taggedUniformFlipMorphism_commutes_normalization
    - AAT.AG.RealizationReconstruction.taggedNormalizationThenUniformFlipKaroubiAut
    - AAT.AG.RealizationReconstruction.FixedArchitectureObject
    - AAT.AG.RealizationReconstruction.fixedArchitectureObjectFunctor
    - AAT.AG.RealizationReconstruction.fixedArchitectureObjectFunctor_identifies_uniform_flip
    - AAT.AG.RealizationReconstruction.fixedArchitectureObjectFunctor_not_injective_at_tagged
    - AAT.AG.RealizationReconstruction.taggedOperationReader_distinguishes_uniform_flip
  claim_mapping:
    source_labels:
      - "GOAL C: uniform flip on the fixed G-117 tagged package"
      - "GOAL C: t^2=1, et=te, and et!=e at taggedBoolOperation with initial false"
      - "GOAL C: et is an automorphism of (P,e)"
      - "GOAL C: object-only fixed-point reading versus operation-preserving reading"
      - "n1014 section 3"
    input_premises:
      - "the fixed taggedOperationPackage and its already proved canonical-normalization admissibility"
      - "no new theorem argument, typeclass, certificate, selected subgroup, or selected endpoint family"
    constructed_evidence:
      - "full PackageTotalHom equalities for involution and commutation"
      - "a direct false-to-true evaluation on taggedBoolOperation"
      - "the Karoubi sandwich morphism and both inverse laws"
      - "an actual fixed-point functor on the Karoubi category and an explicit noninjective Hom-map witness"
      - "a direct operation evaluation separating the underlying package maps, retained only as input for the future A-realization bridge"
    proof_use:
      - "pointwise involutivity is consumed by SignedExactCoreReadingHom extensionality to prove package involutivity"
      - "the tagged cast commutation is consumed by operation-map extensionality to prove et=te"
      - "normalization idempotence, t commutation, and t involutivity are all consumed by the Karoubi inverse proof"
      - "the original false-tag evaluation proves et!=e and the raw operation-map separation needed by the future A-realization bridge"
      - "taggedUnitOperation only separates the uniform action from the old endpoint-dependent action and does not replace the mandated taggedBoolOperation inequality"
    unfinished:
      - "send the same Karoubi morphisms et and e through G-123(A)'s still-unconstructed operation-preserving realization and prove their images differ"
  validation:
    focused_checks: "1/1 pass"
    namespace_axiom_audit: "23 declarations, standard axioms only"
    prerequisite_target_build: "ResearchLean.AG.RealizationComparisonIdempotents.NormalizationCategory passed as a bounded named target"
    research_full_build: not-run
  verdict: "Cycle 6 discharges C1, the Karoubi automorphism, and the fixed-point functor nonfaithfulness witness on the original data. The required image inequality under A's operation-preserving realization remains open, so C and G-123 remain target-proof-checkpoint."
audits:
  premise_delta:
    discharged:
      - "package-level t^2=1 for the one uniform all-endpoint self-map"
      - "two-sided commutation et=te, not merely one-sided normalization absorption"
      - "et!=e on the original taggedBoolOperation with initial false"
      - "nonidentity automorphism of the actual Karoubi object (P,e)"
      - "same-pair identification by the actual fixed-architecture-object functor and its nonfaithfulness witness"
      - "formal distinction from the earlier endpoint-dependent flip"
    remaining:
      - "the same-pair image inequality under A's operation-preserving realization"
      - "all non-C obligations listed above"
  certificate_provenance:
    discharged:
      - "all C evidence is constructed from the fixed package and prior admissibility theorem; no conclusion is stored as input"
    unresolved: []
  proof_use:
    used:
      - "G-117 admissibility operation_type_eq in cast/flip commutation"
      - "G-119 canonical normalization idempotence and absorption in the Karoubi construction"
      - "Cycle 5 uniform action involutivity in package extensionality"
    unused: []
  structure_field_escape: none-found
  route_integrity: "C1 and the fixed-point functor pass; the A-realization bridge remains explicitly unfinished"
  target_fitting: "exact fixed package, all endpoints and operations, exact taggedBoolOperation evaluation"
  vacuity: "et!=e and nonidentity Karoubi hom are explicit"
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: "the initial Cycle 6 snapshot overclaimed the raw Bool evaluator as A's realization; independent review caught it and this report now keeps that bridge unfinished"
  validation_refs:
    - "focused AATUniformFlipKaroubi.lean: standard axioms only"
  blocking_findings: []
  next_obligation: "Construct the general G-122 raw primitive input decomposition and branch-specific primitive interpretations before the closed finite presentation and AAT reconstruction."
initial_review:
  head: 3fc3b8f99f23847b36f80d74a299b563246e9b4a
  verdict: major-revisions
  central_findings:
    - "the raw objectMap projection was not the required fixed-point functor on the Karoubi category"
    - "the raw Bool evaluator was incorrectly reported as A's operation-preserving realization"
  noncentral_findings:
    - "the n1014 source label pointed to nonexistent section 5.3 instead of section 3"
  direct_response:
    - "constructed FixedArchitectureObject and fixedArchitectureObjectFunctor on every admissible-package Karoubi object and morphism"
    - "proved equality of the et/e functor images and a concrete Hom-map noninjectivity witness"
    - "retained direct Bool evaluation only as package-level separation and restored the A-realization image inequality to unfinished status"
    - "corrected the n1014 source label"
  rerun_required: true
review_round_2:
  head: 23c421b11fb882cb973e7c89e5c1bae01c6937ab
  verdict: pass-with-noncentral-report-fix
  central_findings: []
  noncentral_findings:
    - "a broad replacement changed Cycle 1 expected_result_type and left Cycle 6 expected/proposed result types inconsistent"
    - "target-proof-checkpoint is the overall GOAL state, not the selected cycle-result type"
  direct_response:
    - "restored the historical Cycle 1 expected result"
    - "recorded Cycle 6's selected C1, Karoubi, and fixed-point-reader obligation as proof-obligation-discharged while retaining the overall target state and A-realization bridge as unfinished"
  rerun_required: false
```

## Cycle 7 — Preservation of the original G-122 input range

```yaml
ledger_type: target_cycle_result
goal: G-123-aat-realization-reconstruction
cycle: 7
goal_blob_sha: 4e5af099ab9b5612db12867ba1546f74bfed9f97
base_oid: 396410397efd6c175c0fb48718e4d3190aba8215
tracking_issue: 4520
report_path: research/reports/G-123-aat-realization-reconstruction.md
selection:
  proof_state_ref: "Cycle 6 merged at 396410397; the closed signature still had only a nullary fixed G-122 tag and did not represent the original arbitrary A,z,omega,k,g_z input range"
  proof_dag_predecessors:
    - "G-122 fixed theorem input: arbitrary AuthoredBCDatumSquare A, cell z, DefectCochain omega, coefficient ring k, and FixedCoefficientGeometryAt g_z"
    - "G-122 authoredExactSourceTransportAt and authoredExactCompatibleProblemDataAt constructions"
    - "G-122(C) finiteAxisFoldBCDatumSquare, second cell, initial cochain, and fixed integral geometry family"
  proof_obligation: "Construct a standalone, dependency-equivalent representation of the exact original G-122 input range while keeping source transport, compatible problem data, comparisons, normalization, groups, sections, kernels, and fibers on the constructed-output side; common-family integration remains a later obligation"
  selection_reason: "Any later finite syntax and decoder must range over the original G-122 family, not only the fixed finite witness or the subset already known to display. Fixing this dependency split first makes input shrinkage and conclusion-as-input errors visible."
  expected_result_type: proof-checkpoint
  lean_targets:
    - research/lean/ResearchLean/AG/RealizationReconstruction/G122OriginalInput.lean
  risks:
    - "replacing arbitrary authored squares or fixed geometries by only the fixed finite witness"
    - "storing authoredExactSourceTransportAt or compatible problem data as an input field"
    - "calling the semantic input bundle itself a finite syntax or a reconstruction"
    - "using the fixed example to define the general branch"
    - "conflating selected geometry/raw source fields with the generated complete comparison data"
  unchecked:
    - "primitive finite syntax and interpretation for the preserved G-122 semantic inputs"
    - "integration of the standalone G-122 bundles into ClosedFamilyParameter and FamilyRealization"
    - "closed finite presentation Sigma and intrinsic D_Theta"
    - "AAT complete-geometry res/ext/J and four reconstruction properties"
    - "D comparison-group, section, kernel, and lift-fiber recovery and three-case classification"
    - "E bidirectional AAT translations"
    - "F classification and fixed finite examples"
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: "Constructed a standalone two-level dependent input family with a dependency-equivalent quantifier range for arbitrary Atom carrier, decidable equality, authored square, coefficient carrier/ring, cell, cochain, selected geometry, and raw restrictions. Reassembled FixedCoefficientGeometryAt and generated source transport, compatible problem data, and the actual barBeta only after receiving those original fields. Instantiated the same general decomposition with G-122(C)'s original finite axis-fold square, required second cell, generated cochain, and integral geometry/raw data. The existing closed-family G-122 branch remains nullary and is not yet connected to these bundles; no finite-syntax reconstruction claim is made."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/RealizationReconstruction/G122OriginalInput.lean
  evidence:
    - AAT.AG.RealizationReconstruction.G122FamilyInput
    - AAT.AG.RealizationReconstruction.G122CellInput
    - AAT.AG.RealizationReconstruction.G122CellInput.fixedGeometry
    - AAT.AG.RealizationReconstruction.G122CellInput.geometryPackage
    - AAT.AG.RealizationReconstruction.G122CellInput.sourceTransport
    - AAT.AG.RealizationReconstruction.G122CellInput.compatibleProblemData
    - AAT.AG.RealizationReconstruction.G122CellInput.barBeta
    - AAT.AG.RealizationReconstruction.G122CellInput.initialCochain
    - AAT.AG.RealizationReconstruction.finiteAxisFoldG122FamilyInput
    - AAT.AG.RealizationReconstruction.finiteAxisFoldG122CellInput
    - AAT.AG.RealizationReconstruction.finiteAxisFoldG122CellInput_fixedGeometry
    - AAT.AG.RealizationReconstruction.finiteAxisFoldG122CellInput_barBeta
  claim_mapping:
    source_labels:
      - "GOAL A and D: mandatory general G-122 input family and fixed finite axis-fold example"
      - "user instruction: anti-weakening clauses 1--3 and 5"
      - "n1014 sections 6.3 and 6.5"
    input_premises:
      - "arbitrary AtomCarrier U and the exact DecidableEq U.Atom input"
      - "arbitrary AuthoredBCDatumSquare A"
      - "arbitrary coefficient type k and CommRing k"
      - "arbitrary cell z and DefectCochain omega"
      - "the two original source components of g_z: selected geometry and raw restriction data"
    constructed_evidence:
      - "the exact FixedCoefficientGeometryAt value assembled from selectedGeometry and raw"
      - "the resulting GeometryPackage"
      - "authoredExactSourceTransportAt from A,z,k,g_z"
      - "authoredExactCompatibleProblemDataAt from the same inputs"
      - "authoredExactBarBetaAt from A,z,omega,k,g_z"
      - "the original fixed finite G-122(C) input as an inhabitant of the general decomposition"
    proof_use:
      - "selectedGeometry and raw are consumed by fixedGeometry"
      - "authored, cell, coefficient ring, and fixedGeometry are consumed by sourceTransport and compatibleProblemData"
      - "cochain and every other input are consumed by barBeta"
      - "the fixed example theorem proves reassembly is exactly finiteAxisFoldFixedCoefficientGeometryFamily at the mandated second cell"
      - "the finite barBeta theorem identifies the generated output with the same authoredExactBarBetaAt used by G-122(C)"
    unfinished:
      - "G122FamilyInput and G122CellInput are semantic input bundles, not finite primitive syntax"
      - "no claim that arbitrary authored squares or geometry/raw data have already been finitely presented"
      - "no Sigma, D_Theta, interpretation, decoder, res, ext, J, comparison recovery, or classification theorem is asserted"
      - "the standalone bundles are not yet constructors or branches of ClosedFamilyParameter and FamilyRealization"
  validation:
    focused_checks: "1/1 pass"
    namespace_axiom_audit: "44 declarations, standard axioms only"
    prerequisite_target_builds:
      - "ResearchLean.AG.FullGeometryNormalization.ExactDerivedRefinementBC passed as a bounded named target"
      - "ResearchLean.AG.FullGeometryNormalization.ExactBarBetaFiniteWitness passed as a bounded named target"
    research_full_build: not-run
  verdict: "Cycle 7 is a proof checkpoint: it constructs the exact standalone G-122 semantic-input range and dependency split needed before common-family integration and primitive interpretation. It does not discharge the one-declaration requirement, finite presentation, reconstruction, display recovery, or any remaining A--F conclusion."
audits:
  premise_delta:
    discharged:
      - "a standalone semantic bundle now represents arbitrary A,z,omega,k,g_z without narrowing their dependency range"
      - "the fixed finite branch inhabits the general range without defining it"
      - "source transport and compatible problem data are constructed outputs, not input fields"
      - "the actual barBeta comparison is a constructed output using the arbitrary cochain"
    remaining:
      - "connect the standalone bundle to the still-nullary G-122 branch of ClosedFamilyParameter and FamilyRealization"
      - "construct primitive syntax and interpretation without embedding arbitrary completed AAT/core/geometry maps"
      - "all presentation, geometry, reconstruction, comparison, translation, and classification obligations listed above"
  certificate_provenance:
    discharged:
      - "FixedCoefficientGeometryAt is assembled from the two original G-122 geometry inputs"
      - "sourceTransport, compatibleProblemData, and barBeta call the existing G-122 constructions from the preserved inputs"
    unresolved:
      - "finite representability and interpretation adequacy of the semantic inputs"
  proof_use:
    used:
      - "every field of G122FamilyInput and G122CellInput in a downstream constructed output"
      - "the same fixed geometry family and mandated second cell in the finite witness specialization"
    unused: []
  structure_field_escape: "no source transport, compatible problem data, generated mate, barAlpha, barBeta, normalization, comparison element, section, kernel, or lift fiber is an input field"
  route_integrity: "checkpoint-only; the standalone semantic input is preserved but has not yet been connected to the common family declaration or reached from primitive finite syntax"
  target_fitting: "exact original G-122 quantifier range and exact G-122(C) finite input; no subgroup or displayed-subset restriction"
  vacuity: "the fixed finite witness inhabits the same general dependent structures and reassembles the exact fixed geometry"
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused G122OriginalInput.lean: standard axioms only"
  blocking_findings: []
  next_obligation: "Integrate the preserved G-122 bundles into ClosedFamilyParameter and FamilyRealization, then construct branch-specific primitive interpretations without accepting completed transports or comparisons; define the closed finite presentation only after those interpretations are fixed."
initial_review:
  head: fcacee5e99470cd66537c5aece05c517431e4b31
  verdict: major-revisions
  central_findings:
    - "the standalone G122FamilyInput and G122CellInput were not connected to the still-nullary ClosedFamilyParameter.finiteAxisFold branch, so the report could not call the one-declaration A/D obligation discharged"
  noncentral_findings:
    - "the report said same quantifier order although the dependency-equivalent bundle moves independent k before z and omega"
    - "the n1014 source label pointed to section 4 instead of the direct sections 6.3 and 6.5"
  direct_response:
    - "reclassified Cycle 7 from proof-obligation-discharged to proof-checkpoint"
    - "described the new structures consistently as standalone semantic bundles and kept common-family integration explicit and unfinished"
    - "replaced same-order wording with dependency-equivalent quantifier range"
    - "corrected the n1014 provenance and distinguished the user-supplied anti-weakening clauses"
  rerun_required: true
review_round_2:
  head: 1283e9cb511b4cd870bea783d8682d6611465f15
  verdict: pass-after-noncentral-fix
  independent_lanes:
    math_a: pass
    math_b: pass
    lean_a: pass
    lean_b: pass-after-noncentral-fix
  noncentral_findings:
    - "the Lean docstring still described the dependency-equivalent rearrangement as the literal fixed G-122 quantifier order"
  direct_response:
    reviewed_delta: "1283e9cb511b4cd870bea783d8682d6611465f15..ef4da6d9938598979645784c21b2398553a98d95"
    verdict: pass
    new_findings: []
```

## Cycle 8 — Common-family integration of the original G-122 range

```yaml
ledger_type: target_cycle_result
goal: G-123-aat-realization-reconstruction
cycle: 8
goal_blob_sha: 4e5af099ab9b5612db12867ba1546f74bfed9f97
base_oid: f2b175cdb2fe03a02675b6c7eff8db79a35cd9bd
tracking_issue: 4520
report_path: research/reports/G-123-aat-realization-reconstruction.md
selection:
  proof_state_ref: "Cycle 7 merged at f2b175cdb; the exact G-122 input range existed only as a standalone bundle and the common declaration still had a nullary fixed-example branch"
  proof_dag_predecessors:
    - "Cycle 7 G122FamilyInput/G122CellInput dependency split and fixed finite specialization"
    - "Cycle 4 ClosedFamilyParameter and role-indexed primitive source scaffold"
    - "G-122 support-package, signature, equation, invariant, selected-geometry, and raw-restriction source fields"
  proof_obligation: "Replace the nullary fixed G-122 family tag by the arbitrary original G122FamilyInput, place every G122CellInput under that same branch, and expose only source-derived primitive roles without accepting completed transports, comparisons, or display maps"
  selection_reason: "This closes the Cycle 7/common-declaration disconnect while preserving the quantifier order parameter first and arbitrary semantic object second. It deliberately stops before inventing an operation syntax that would merely re-input completed operation maps."
  expected_result_type: proof-checkpoint
  lean_targets:
    - research/lean/ResearchLean/AG/RealizationReconstruction/G122OriginalInput.lean
    - research/lean/ResearchLean/AG/RealizationReconstruction/AATClosedFamilySignature.lean
    - research/lean/ResearchLean/AG/RealizationReconstruction/AATUniformFlipKaroubi.lean
  risks:
    - "retaining only the fixed finite G-122 example under the common declaration"
    - "collapsing the independent carrier and coefficient universes"
    - "using a universe wrapper that changes or restricts the underlying semantic object"
    - "adding a G-122 operation constructor whose payload is already a completed global operation map"
    - "calling source-role availability a finite presentation or interpretation"
    - "calling common-family integration an A or D discharge"
  unchecked:
    - "a source-generated G-122 primitive operation role and its endpoint discipline"
    - "branch-specific primitive interpretations and congruence"
    - "closed finite presentation Sigma and intrinsic D_Theta"
    - "AAT complete-geometry res/ext/J and four reconstruction properties"
    - "D display recovery, both kernels, every lift fiber, and the three-case classification"
    - "E bidirectional AAT translations"
    - "F classification and fixed finite examples"
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: "Reversed the dependency between the standalone input module and the common signature; replaced the nullary G-122 tag by a payload carrying an arbitrary G122FamilyInput at independent carrier and coefficient universes; introduced a property-free indexed FamilyRealization constructor carrying every arbitrary G122CellInput unchanged; and specialized the mandated finite axis-fold input through that same general branch. Added source-derived G-122 Atom, source, object, context, diagnostic-cell, signature-axis/coordinate, equation, invariant, raw-coordinate, and raw-relation roles. No G-122 operation constructor or interpreter was added, because a constructor accepting a completed global operation map would move a target conclusion into syntax."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/RealizationReconstruction/G122OriginalInput.lean
    - research/lean/ResearchLean/AG/RealizationReconstruction/AATClosedFamilySignature.lean
  evidence:
    - AAT.AG.RealizationReconstruction.ClosedFamilyParameter.g122
    - AAT.AG.RealizationReconstruction.FamilyRealization.g122
    - AAT.AG.RealizationReconstruction.PrimitiveAtom.g122
    - AAT.AG.RealizationReconstruction.PrimitiveSource.g122
    - AAT.AG.RealizationReconstruction.PrimitiveObject.g122
    - AAT.AG.RealizationReconstruction.PrimitiveContext.g122
    - AAT.AG.RealizationReconstruction.PrimitiveDiagnosticCell.g122
    - AAT.AG.RealizationReconstruction.PrimitiveSignatureAxis.g122
    - AAT.AG.RealizationReconstruction.PrimitiveSignatureCoordinate.g122
    - AAT.AG.RealizationReconstruction.PrimitiveEquationIndex.g122
    - AAT.AG.RealizationReconstruction.PrimitiveInvariantIndex.g122
    - AAT.AG.RealizationReconstruction.PrimitiveCoordinateIndex.g122
    - AAT.AG.RealizationReconstruction.PrimitiveRelationIndex.g122
    - AAT.AG.RealizationReconstruction.finiteAxisFoldParameter
    - AAT.AG.RealizationReconstruction.finiteAxisFoldRealization
    - AAT.AG.RealizationReconstruction.finiteAxisFoldAtom
  claim_mapping:
    source_labels:
      - "GOAL A: one declaration, fixed mandatory input family, and quantification over every semantic object after the parameter"
      - "GOAL D: the original G-122 input range and mandated finite axis-fold specialization"
      - "user instruction: anti-weakening clauses 1--3 and 5"
      - "n1014 sections 6.3 and 6.5"
    input_premises:
      - "one arbitrary G122FamilyInput containing the original carrier, authored square, coefficient carrier/ring, and decidable equality"
      - "one arbitrary G122CellInput below that fixed family parameter, containing z, omega, selected geometry, and raw restrictions"
      - "no source transport, compatible problem data, comparison, normalization, section, kernel, fiber, decoder, or display map"
    constructed_evidence:
      - "ClosedFamilyParameter.g122 carries the family input without narrowing it"
      - "FamilyRealization.g122 injects each original cell input under the already fixed parameter without adding a premise"
      - "the fixed finite-axis-fold parameter and realization inhabit the same general constructors"
      - "each added primitive role is read from the original carrier or authored/support/geometry/raw structures"
    proof_use:
      - "the G-122 parameter payload determines the carrier, coefficient universe, authored square, and all dependent primitive role types"
      - "the semantic-object constructor carries the cell, cochain, selected geometry, and raw inputs unchanged; the cell, selected geometry, and raw inputs determine the corresponding added role types, while the cochain remains available to the already constructed barBeta output"
      - "the fixed finite Atom specialization passes through the general g122 parameter and realization constructors"
    unfinished:
      - "FamilyRealization is only a property-free common index; it is not the realization category, a decoder image, or a reconstruction theorem"
      - "the primitive role types are semantic-source references and are not yet a finite syntax Sigma"
      - "PrimitiveOperation has no G-122 constructor; operation generation and interpretation remain open"
      - "no D recovery or AAT complete-geometry reconstruction conclusion is asserted"
  validation:
    focused_checks: "2/2 pass"
    namespace_axiom_audits:
      - "G122OriginalInput: 44 declarations, standard axioms only"
      - "AATClosedFamilySignature: 397 declarations, standard axioms only"
    bounded_target_builds:
      - "ResearchLean.AG.RealizationReconstruction.AATClosedFamilySignature passed"
      - "ResearchLean.AG.RealizationReconstruction.AATUniformFlipKaroubi passed"
    research_full_build: not-run
  verdict: "Cycle 8 is a proof checkpoint: the exact arbitrary G-122 input range is now inside the same closed family declaration and the mandated finite example uses that branch. Operation generation, interpretation, finite presentation, reconstruction, and display recovery remain unproved, so neither A nor D nor G-123 is discharged."
audits:
  premise_delta:
    discharged:
      - "the common family no longer represents G-122 by a nullary fixed-example tag"
      - "arbitrary G122CellInput values remain quantified after one fixed G122FamilyInput parameter"
      - "the carrier and coefficient universes remain independent"
      - "the fixed finite example is a specialization of the arbitrary branch"
    remaining:
      - "construct the missing operation role from generated source data rather than completed maps"
      - "construct branch-specific interpretations and the closed finite presentation"
      - "all reconstruction, display recovery, translation, and classification obligations listed above"
  certificate_provenance:
    discharged:
      - "the common constructors carry only the Cycle 7 original inputs"
      - "source-derived role payloads are selected from the carrier, authored square, its support package, selected geometry, or raw restrictions"
    unresolved:
      - "finite generation and interpretation adequacy of all G-122 roles"
  proof_use:
    used:
      - "G122FamilyInput in ClosedFamilyParameter.g122 and every dependent G-122 role"
      - "G122CellInput in FamilyRealization.g122 and every object-dependent G-122 role"
      - "the same general constructors in the fixed finite specialization"
    unused: []
  structure_field_escape: "FamilyRealization.g122 adds no field beyond the original cell input; no generated transport, comparison, normalization, group element, section, kernel, lift fiber, decoder, or completed map is accepted"
  route_integrity: "checkpoint-only; the preserved source roles have no interpreter or decoder yet"
  target_fitting: "the general branch retains arbitrary authored squares, cells, cochains, coefficient rings, selected geometries, and raw restrictions; the finite example does not define or restrict it"
  vacuity: "the branch has arbitrary payloads and the fixed witness is proved by direct specialization, not by replacing the general family"
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused G122OriginalInput.lean: pass, standard axioms only"
    - "focused AATClosedFamilySignature.lean: pass, standard axioms only"
    - "bounded AATClosedFamilySignature and AATUniformFlipKaroubi targets: pass"
  blocking_findings: []
  next_obligation: "Construct a source-generated G-122 PrimitiveOperation with exact endpoints, then define branch-specific primitive interpretations and congruence without accepting completed maps."
initial_review:
  head: bf0829140e691d3e1979f899d483e0064f4897f6
  verdict: pass-after-noncentral-fix
  central_findings: []
  noncentral_findings:
    - "the diagnostic-cell docstring still described the former fixed finite family"
    - "two disconnected FiniteAxisFold signature aliases could be mistaken for the new general source roles"
    - "the report omitted carrier-derived roles and overstated the cochain's direct role-type dependency"
  direct_response:
    - "generalized the diagnostic-cell wording and removed the disconnected aliases"
    - "added carrier provenance and separated cochain preservation/barBeta use from primitive role-type dependencies"
  rerun_required: true
review_round_2:
  head: a95ac65ace99682e8eee934fb87ae856c3a14c7c
  verdict: pass-after-noncentral-fix
  independent_lanes:
    math_a: pass
    math_b: pass-after-noncentral-fix
    lean_a: pass-after-external-metadata-fix
    lean_b: pass
  noncentral_findings:
    - "the module introduction called the general G-122 branch an example rather than a branch"
    - "the PR body retained the pre-fix 399-declaration audit count"
  direct_response:
    reviewed_delta: "a95ac65ace99682e8eee934fb87ae856c3a14c7c..03f079c5c"
    code: "changed examples to branches in the module introduction"
    pr_metadata: "updated the PR validation count from 399 to 397 without changing the reviewed source head"
  rerun_required: true
```

## Cycle 9 — Endpoint-indexed G-122 operation references

```yaml
ledger_type: target_cycle_result
goal: G-123-aat-realization-reconstruction
cycle: 9
goal_blob_sha: 4e5af099ab9b5612db12867ba1546f74bfed9f97
base_oid: 2eaa58fae1e0ac915a61995cd2d683832519ead6
tracking_issue: 4520
report_path: research/reports/G-123-aat-realization-reconstruction.md
selection:
  proof_state_ref: "Cycle 8 merged at 2eaa58fae; the common G-122 branch retained objects and non-operation source roles but PrimitiveOperation had no G-122 constructor"
  proof_dag_predecessors:
    - "Cycle 8 arbitrary G122FamilyInput/G122CellInput common-family branch"
    - "OperationReading.Op: endpoint-indexed selected operation identity with configurationMap evaluation"
    - "G-123(A) and n1014 section 2: retain both endpoints, operation identity, and configuration action"
  proof_obligation: "Represent each original G-122 support operation at its exact endpoints and evaluate both its identity and configuration action, without accepting a completed operationMap family or claiming a finite generating grammar"
  selection_reason: "An individual source Op value is original primitive data, while a family assigning a target Op to every source Op would already be the completed morphism component forbidden by the fixed target. This cycle makes that distinction explicit in the common declaration."
  expected_result_type: proof-checkpoint
  lean_targets:
    - research/lean/ResearchLean/AG/RealizationReconstruction/AATClosedFamilySignature.lean
  risks:
    - "calling an arbitrary source-operation reference a finite generator"
    - "forgetting operation identity by interpreting only its ConfigurationHom"
    - "accepting a forall-source-target operation family and thereby repackaging a completed operationMap"
    - "restricting endpoints to the fixed finite example or a selected object subset"
    - "deriving full operation-map reconstruction from the reference evaluator"
  unchecked:
    - "finite operation grammar and sufficient generating relations for arbitrary opaque Op families"
    - "construction of every admissible full operationMap from finite coherent data"
    - "branch-specific full primitive interpretations and congruence"
    - "closed Sigma, D_Theta, R_Theta, P_Theta, and F_Theta"
    - "AAT res/ext/J and four reconstruction properties"
    - "D display recovery and classification; E translations; F"
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: "Added PrimitiveOperation.g122Ref for one operation of the original authored support package at arbitrary source and target ArchitectureObject values. Added g122Value to recover the identical Op value and g122ConfigurationMap to evaluate its original configuration action without assuming configurationMap injective. Specialized every operation of the mandated finite-axis-fold support package through the same general constructor and proved literal identity readback. No operation-map family, target-operation choice, finiteness premise, interpreter completeness, or reconstruction conclusion was added."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/RealizationReconstruction/AATClosedFamilySignature.lean
  evidence:
    - AAT.AG.RealizationReconstruction.PrimitiveOperation.g122Ref
    - AAT.AG.RealizationReconstruction.PrimitiveOperation.g122Value
    - AAT.AG.RealizationReconstruction.PrimitiveOperation.g122ConfigurationMap
    - AAT.AG.RealizationReconstruction.PrimitiveOperation.g122Value_ref
    - AAT.AG.RealizationReconstruction.PrimitiveOperation.g122ConfigurationMap_ref
    - AAT.AG.RealizationReconstruction.finiteAxisFoldOperationReference
    - AAT.AG.RealizationReconstruction.finiteAxisFoldOperationReference_value
  claim_mapping:
    source_labels:
      - "GOAL A operation row: endpoints, operation identity, and configuration action"
      - "GOAL C: configuration-invisible operation distinctions must remain visible"
      - "user anti-weakening clauses 1--3 and 5"
      - "n1014 sections 2, 6.3, and 6.4"
    input_premises:
      - "the already fixed arbitrary G122FamilyInput and G122CellInput"
      - "one operation value from the original authored support package at arbitrary original endpoints"
      - "no target operation, completed operation-map family, extension witness, finiteness, or injectivity premise"
    constructed_evidence:
      - "an endpoint-indexed PrimitiveOperation value under the same common parameter and semantic object"
      - "literal readback of the same source operation identity"
      - "configuration action evaluated by the source OperationReading.configurationMap"
      - "the full fixed finite-axis-fold Op family specializes through the general branch"
    proof_use:
      - "the dependent Op type fixes both source and target indices of g122Ref"
      - "g122Value keeps operation identity available independently of configuration action"
      - "g122ConfigurationMap consumes g122Value and the original operation reading"
      - "the fixed specialization theorem verifies identity readback rather than only equality after configuration forgetting"
    unfinished:
      - "g122Ref is a parameter-relative source reference, not a proof that the Op family has finite generators"
      - "no map between two arbitrary G-122 operation families is constructed"
      - "no res/ext/J, fullness, faithfulness, finite syntax, or D recovery claim is asserted"
  candidate_failure_record:
    candidate: "recover a full target operationMap from object/configuration data alone"
    obstacle: "OperationReading.Op is an opaque endpoint-indexed type and configurationMap need not be injective or surjective; it supplies no constructors, composition, normal form, or reification from ConfigurationHom"
    forbidden_shortcut: "supplying a target operation reference for every source operation is definitionally the missing completed operationMap family under another name"
    status: "candidate obstruction only; not yet a refutation of the fixed target, and alternative finite grammars remain to be investigated"
    paper_conclusion_at_risk: "without operation-identity recovery, the uniform flip separation and the claimed recovery of comparison-preserving changes would be lost"
  validation:
    focused_checks: "1/1 pass"
    namespace_axiom_audit: "409 declarations, standard axioms only"
    research_full_build: not-run
  verdict: "Cycle 9 is a proof checkpoint: it preserves and evaluates every individual source operation at exact endpoints, including the original finite specialization, but it does not construct finite operation generation or recover a full operationMap. A, D, and G-123 remain unproved."
audits:
  premise_delta:
    discharged:
      - "the common G-122 PrimitiveOperation role is no longer absent"
      - "operation identity and configuration action are kept as distinct outputs"
      - "arbitrary source/target endpoints and the full original Op family are retained"
      - "the fixed finite example uses the general operation-reference constructor"
    remaining:
      - "find finite generating syntax sufficient for every admissible operationMap without accepting that map as data"
      - "construct full branch interpretation, congruence, and reconstruction"
      - "all remaining A--F obligations"
  certificate_provenance:
    discharged:
      - "the operation payload comes only from the original authored support package"
      - "configuration evaluation uses the same support package's OperationReading.configurationMap"
    unresolved:
      - "finite generation and full-map recovery for arbitrary opaque Op families"
  proof_use:
    used:
      - "operation identity in g122Value and the fixed identity theorem"
      - "configurationMap in g122ConfigurationMap and its constructor equation"
      - "both endpoint indices in the PrimitiveOperation result type"
    unused: []
  structure_field_escape: "no forall-endpoint operation-map family, target-operation selector, extension witness, or completed core/geometry morphism is stored"
  route_integrity: "identity-preserving source evaluation only; no finite-generation or extension route is claimed"
  target_fitting: "all endpoints and all original support Op values remain referenceable; no fixed subgroup, selected endpoint subset, or configuration-map quotient is used"
  vacuity: "g122Value_ref is literal identity, and the fixed theorem ranges over every operation of the mandated support package"
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused AATClosedFamilySignature.lean: pass, 409 declarations, standard axioms only"
  blocking_findings: []
  next_obligation: "Investigate a genuine parameter-relative finite grammar for arbitrary G-122 Op families and admissible maps; distinguish a failed grammar from a target-level cardinality or opacity obstruction."
initial_review:
  head: 3a714f99ae1a1e0774b7c77918004daa9382589d
  verdict: pass-after-noncentral-fix
  independent_lanes:
    math_a: pass
    math_b: pass-after-noncentral-fix
    lean_a: pass
    lean_b: pass-after-noncentral-fix
  central_findings: []
  noncentral_findings:
    - "g122Value was described as preventing future identity erasure, although the current accessor only keeps identity independently available"
  direct_response:
    reviewed_delta: "3a714f99ae1a1e0774b7c77918004daa9382589d..98b36ac19"
    report: "replaced prevents replacement with keeps identity available independently of configuration action"
  rerun_required: true
```

## Cycle 10 — Finite operation-reference obstruction

```yaml
ledger_type: target_cycle_result
goal: G-123-aat-realization-reconstruction
cycle: 10
goal_blob_sha: 4e5af099ab9b5612db12867ba1546f74bfed9f97
base_oid: 47beb94b1bcf69e5a259c9dc5829eb4e1d3a0ad9
tracking_issue: 4520
report_path: research/reports/G-123-aat-realization-reconstruction.md
selection:
  proof_state_ref: "Cycle 9 retained every individual source operation but left open whether finite source references can recover every admissible operationMap"
  proof_dag_predecessors:
    - "Cycle 9 endpoint-indexed PrimitiveOperation.g122Ref and literal source readback"
    - "the fixed target requires a finite presentation and decoder fullness for all admissible maps"
    - "the fixed target forbids carrying a completed full operationMap or arbitrary comparison element as one primitive constant"
  proof_obligation: "Test the finite-reference strategy against an actual AATCorePackage whose configuration-invisible operation tags admit every endotransformation, and separate failure of that strategy from refutation of the fixed target"
  selection_reason: "The operation component is opaque in the current authored reading. Before designing D_Theta around references, the loop must establish whether finite parameter references can possibly make its decoder full."
  expected_result_type: proof-checkpoint
  lean_targets:
    - research/lean/ResearchLean/AG/RealizationReconstruction/OperationFiniteReferenceObstruction.lean
  risks:
    - "calling a failed list grammar a refutation of G-123 without proving membership in mandatory D_Theta"
    - "escaping the diagonal by storing an arbitrary OperationTag-to-OperationTag function as one code leaf"
    - "restricting semantic morphisms to syntax-generated maps and thereby defining fullness into the input class"
    - "forgetting that the semantic endomorphisms must be actual PackageTotalHom values"
    - "silently replacing the paper claim by a finite or selected subgroup"
  unchecked:
    - "an intrinsic non-circular D_Theta and construction of its evidence from every mandatory input family"
    - "whether the Cycle 10 package or an equivalent opaque family is mandatory in D_Theta"
    - "a finite recursive presentation of every D_Theta-admissible operationMap"
    - "closed Sigma, R_Theta, P_Theta, F_Theta, AAT res/ext/J, and all four B properties"
    - "D display recovery and classification; E translations; F"
result:
  proposed_result_type: proof-checkpoint
  proof_obligation_delta: "Constructed a sequence-tagged AATCorePackage in which operation configuration actions ignore an opaque OperationTag = Nat -> Bool component. Every arbitrary transformation of OperationTag induces an actual PackageTotalHom, and readSequenceTransform is a left inverse, hence this family embeds into package endomorphisms. Cantor diagonalization, together with an embedding of finite OperationTag lists into OperationTag, proves that no decoder from List OperationTag is surjective. The generic bridge extends this failure to every code type surjectively generated by such finite lists."
  completion_candidate: no
  lean_artifacts:
    - research/lean/ResearchLean/AG/RealizationReconstruction/OperationFiniteReferenceObstruction.lean
  evidence:
    - AAT.AG.RealizationReconstruction.operationTags_not_surjective_transformations
    - AAT.AG.RealizationReconstruction.listOperationTags_not_surjective_transformations
    - AAT.AG.RealizationReconstruction.sequenceTaggedOperationPackage
    - AAT.AG.RealizationReconstruction.sequenceTransformTotal
    - AAT.AG.RealizationReconstruction.readSequenceTransform_sequenceTransformTotal
    - AAT.AG.RealizationReconstruction.sequenceTransformTotal_injective
    - AAT.AG.RealizationReconstruction.sequencePackageEndomorphisms_not_listTagEnumerable
    - AAT.AG.RealizationReconstruction.no_surjectiveEndomorphismDecoder_of_listGeneratedCode
  claim_mapping:
    source_labels:
      - "GOAL A finite presentation, independent semantic category, and all admissible maps"
      - "GOAL B decoder fullness and faithfulness"
      - "GOAL C operation information invisible to configuration-only reading"
      - "user anti-weakening clauses 1--4"
      - "n1014 sections 2, 6.3, and 6.4"
    input_premises:
      - "the existing taggedOperationPackage semantic reading"
      - "an opaque authored OperationTag = Nat -> Bool attached to every operation"
      - "finite list codes contain only finitely many OperationTag references"
      - "no completed operationMap, decoder fullness witness, or D_Theta membership certificate"
    constructed_evidence:
      - "a genuine AATCorePackage retaining exact endpoint-indexed operations"
      - "one actual PackageTotalHom for every arbitrary OperationTag endotransformation"
      - "a readback left inverse and injectivity of the transformation embedding"
      - "a diagonal non-surjectivity theorem for list-reference decoders and list-generated code types"
    proof_use:
      - "operation_naturality uses the unchanged first component and the source configurationMap"
      - "readSequenceTransform evaluates the operationMap on the fixed tagged Bool operation at every tag"
      - "decoder surjectivity would cover every sequenceTransformTotal and therefore surject onto all tag transformations"
      - "operationTagNot supplies the diagonal value that differs at its own index"
    unfinished:
      - "the sequence-tagged package is not proved to satisfy the still-unconstructed D_Theta"
      - "the theorem blocks list/tree grammars generated by finitely many tag references, not every possible finite parameter-relative grammar"
      - "no target-level impossibility is claimed"
      - "no positive common grammar, interpretation, res/ext/J, or display recovery is constructed"
  candidate_failure_record:
    candidate: "generate every operationMap from a finite list or finite tree whose leaves are only source-provenanced opaque operation tags"
    obstacle: "the semantic package has one distinct actual endomorphism for every OperationTag endotransformation, but a finite tag-reference list has cardinality at most OperationTag and cannot enumerate that function space"
    tried_construction: "Cycle 9 endpoint-indexed source references followed by a proposed finite list/tree closure; Cycle 10 internalizes the resulting cardinality test in Lean"
    forbidden_shortcuts:
      - "put the arbitrary tag transformation or completed operationMap into a primitive leaf"
      - "define admissible morphisms as exactly those already decoded by the syntax"
      - "replace all semantic endomorphisms by a selected finite-support subgroup"
    status: "candidate grammar refuted; fixed target not refuted because mandatory D_Theta membership has not been established"
    paper_conclusion_at_risk: "excluding opaque comparison-preserving changes or storing each completed change as input would remove the claimed finite recovery of information loss and its transfer to the two CS models"
  validation:
    focused_checks: "1/1 pass"
    named_target_build: "ResearchLean.AG.RealizationReconstruction.OperationFiniteReferenceObstruction passed"
    namespace_axiom_audit: "19 declarations, standard axioms only"
    research_full_build: not-run
  verdict: "Cycle 10 is a proof checkpoint: it rigorously rules out finite tag-reference list/tree codes for an actual operation-rich AAT package, while preserving the distinction between candidate failure and target refutation. Until a mandatory D_Theta input is shown to contain this obstruction, or an intrinsic non-circular D_Theta is constructed and discharged from all required inputs, A, B, D, and G-123 remain unproved."
audits:
  premise_delta:
    discharged:
      - "the finite-reference candidate is tested against actual PackageTotalHom values rather than an external function toy model"
      - "the impossibility covers arbitrary finite lists of parameter tags and every code type surjectively generated by them"
      - "candidate failure and fixed-target refutation are explicitly separated"
    remaining:
      - "define D_Theta without decoder-image, extension, idempotent-splitting, or retract-generation fields"
      - "derive the intrinsic finite-recursion evidence from the fixed examples, C operation family, and both E families"
      - "decide whether arbitrary G-122 inputs required by the GOAL necessarily admit the opaque operation family used here"
      - "all remaining A--F obligations"
  certificate_provenance:
    discharged:
      - "semantic endomorphisms are constructed from the authored operation reading and explicit tag transformations"
      - "non-surjectivity is proved by diagonalization and cardinal arithmetic, not accepted as a record field"
    unresolved:
      - "positive finite presentation evidence for the mandatory common family"
  proof_use:
    used:
      - "all arbitrary tag transformations in sequenceTransformTotal"
      - "the operationMap component in readSequenceTransform"
      - "finite-list generation in operationTagListEnumeration_surjective and the composed decoder contradiction"
    unused: []
  structure_field_escape: "no decoder, full-map family, extension witness, fullness certificate, or D_Theta membership is stored in the package"
  route_integrity: "the result narrows candidate syntax design only; it is not used to assert target-refuted or to discharge A/B"
  target_fitting: "the actual package keeps all endpoints and all operation tags, and its semantic morphism range contains every tag transformation"
  vacuity: "the contradiction quantifies over every proposed decoder and exhibits a concrete diagonal transformation outside its range"
  one_way_as_equivalence: none-found
  goal_or_report_reinterpretation: none-found
  validation_refs:
    - "focused OperationFiniteReferenceObstruction.lean: pass, 19 declarations, standard axioms only"
    - "named target ResearchLean.AG.RealizationReconstruction.OperationFiniteReferenceObstruction: pass"
  blocking_findings: []
  next_obligation: "Formulate the strongest intrinsic, syntax-independent finite-generation condition that does not contain the requested reconstruction conclusion, then prove or disprove it for each mandatory D_Theta input from its primitive data."
```
