---
status: picked
goal: G-aat-quality-surface-04
candidate_type: target-support
capability_category: finite-query-representation / explicit-current-shadow-coordinate-certificate / current-shadow-adequacy-boundary / anti-weakening
expected_base_score: 38
expected_evidence_multiplier: 2.0
expected_final_score: 76
evidence_stage: proved-in-research
rival_advantage: support membership and query-reading recovery are separated from explicit per-coordinate current-shadow factor certificates.
genius_potential: false
genius_target: none
genius_support_role: not-applicable
target_theorem: Universal Semantic Repair Obstruction Tower Theorem
target_support_node: explicit per-coordinate current-shadow factor certificates for finite query coordinates
target_progress: support-node
proof_obligation_delta: Names the exact per-coordinate factor certificates equivalent to query-coordinate current-shadow extensionality and records a Bool support-factor/no-current-factor boundary.
target_completion_role: support / obstruction theorem package only; not target theorem completion
origin: T1-cycle44
tags: [target-theorem-loop, G-04, finite-query-representation, anti-weakening]
created: 2026-06-25
cycle: 44
lean: Formal/AG/Research/QualitySurface/SemanticRepairFiniteQueryExplicitCurrentShadowCertificates.lean
---

# Explicit Current-Shadow Coordinate Certificates

## 主張

`SourceTraceCoordinateCurrentShadowFactor atom` を、source-trace coordinate observation が current canonical shadow 上の factor で計算できることとして定義する。この factor certificate は `SourceTraceCoordinateCurrentShadowExtensional atom` と同値であり、finite query 上の certificate family は `QueryTraceCoordinatesCurrentShadowExtensional query` と同値である。

この certificate から query-level determinacy、raw query readings の current-shadow factorization、finite query-generated observation の factorization、represented finite-query observation の factorization が導かれる。Bool `true` coordinate は complete support shadow には factor するが current shadow には factor しないため、support membership / complete support / recovery と current-shadow adequacy は別である。

## 候補種別

`target-support`

## 依拠

- `SemanticRepairCurrentShadowCoordinateObligations.lean`: source coordinate current-shadow extensionality と support determinacy
- `SemanticRepairFiniteQueryCurrentShadowCoordinates.lean`: query-coordinate current-shadow obligation
- `SemanticRepairFiniteQuerySupportedCurrentShadowFactorization.lean`: support determinacy から supported query factorization
- `SemanticRepairFiniteSupportCompleteness.lean`: complete Bool support factorization witness

## 非自明性

既存の extensionality premise を、current-shadow factor certificate と Bool no-factor witness を持つ finite certificate surface として再表示する。単なる support membership や recovery ではなく、current shadow 上の factor が必要であることを theorem-level に分離する。

## 数学的興味

finite computable shadow adequacy の未放電箇所を、support 全体の抽象 premise から per-coordinate factor certificate へ細分化する。これにより、future proof search は「どの source-trace coordinate が current shadow に落ちるか」を監査単位にできる。

## GOAL への前進

G-04 の representation adequacy / finite shadow adequacy 側の未完 premise を、明示的な per-coordinate current-shadow factor certificate として名前付けする。

## ライバルに対する有効性

ADL、静的解析、metric dashboard、AI reviewer は support membership や recovered readings を示せても、それが current-shadow factorization のための per-coordinate certificate かどうかを区別しにくい。この候補は、その不足分を Lean theorem と Bool no-factor witness で固定する。

## SCORE 見込み

- `score_reason`: Cycle 25/26/43 の近傍整理だが、factor certificate と Bool no-current-factor witness まで明示するため proof-DAG 上の監査単位が具体化する。
- `dullness_risk`: 既存 extensionality premise の再包装に見える危険がある。report では target completion ではなく explicit certificate boundary として書く。
- `proof_or_evidence_plan`: 新規 Lean file、reported declarations の `#print axioms`、`FormalAGResearch` build、placeholder / hidden Unicode / local path scan。

## Target Theorem 寄与

- `target_theorem`: Universal Semantic Repair Obstruction Tower Theorem
- `target_support_node`: explicit finite/per-coordinate current-shadow factor certificate boundary
- `target_progress`: support-node
- `proof_obligation_delta`: `SourceTraceCoordinateCurrentShadowFactor`、query certificate surface、certificate-driven factorization theorems、Bool support-factor/no-current-factor witness を追加する。
- `target_completion_role`: support / obstruction theorem package only. semantic soundness、representation adequacy、finite shadow adequacy、global repair coherence、obstruction vanish、target completion は not discharged。

## CS / SWE への帰結

finite support list や recovered query readings は、current-shadow adequacy の必要証拠にはなり得るが、それ自体では factorization を保証しない。current-shadow factorization には、source-trace coordinate ごとの explicit factor certificate が必要である。

## 証明・根拠の見込み

`ShadowExtensionalTowerObservation` と `canonicalShadowFactor` から coordinate factor と coordinate extensionality の同値を証明する。query certificate は pointwise factor certificate family として定義し、既存の query-coordinate theorem へ変換する。Bool witness は existing complete-support factorization と existing non-extensional Bool true coordinate obstruction を合成する。

Proved declarations:

- `SourceTraceCoordinateCurrentShadowFactor`
- `sourceTraceCoordinateCurrentShadowFactor_of_currentShadowExtensional`
- `sourceTraceCoordinateCurrentShadowExtensional_of_currentShadowFactor`
- `sourceTraceCoordinateCurrentShadowFactor_iff_currentShadowExtensional`
- `QueryCurrentShadowCoordinateCertificate`
- `SupportedFiniteQueryCurrentShadowCertificate`
- `queryCoordinateCurrentShadowExtensional_of_certificate`
- `certificate_of_queryCoordinateCurrentShadowExtensional`
- `queryCoordinateCurrentShadowExtensional_iff_certificate`
- `supportedFiniteQueryCurrentShadowCertificate_of_currentShadowDeterminesSupportTraceShadow`
- `currentShadowDeterminesTraceQuery_of_queryCurrentShadowCoordinateCertificate`
- `queryTraceReadings_currentShadowFactor_of_queryCurrentShadowCoordinateCertificate`
- `supportedQueryGeneratedObservation_currentShadowFactor_of_supportedCurrentShadowCertificate`
- `representedFiniteTraceQueryObservation_currentShadowFactor_of_queryCurrentShadowCoordinateCertificate`
- `currentShadowDeterminesSupportTraceShadow_iff_supportCoordinateCurrentShadowFactors`
- `sourceTraceCoordinateCurrentShadowFactor_of_singletonQueryReadings_currentShadowFactor`
- `currentShadowDeterminesSupportTraceShadow_of_singletonQueryReadings_currentShadowFactors`
- `boolTrueSourceTraceCoordinate_supportFactor_but_no_currentShadowFactor`

## Target Loop Audit Fields

- `material_premises`: per-coordinate current-shadow factor certificate is visible theorem data. It is not semantic soundness, representation adequacy, finite shadow adequacy, global coherence, or obstruction vanish.
- `premise_discharge_plan`: future work must derive these coordinate factor certificates from semantic soundness / representation adequacy / finite certificates without circularity.
- `anti_weakening_verdict`: pass as target-support / target-obstruction; reject as target-proof or target theorem completion.
- `claim_boundary`: finite source-trace coordinate observations, finite queries, and represented finite-query observations only.
- `statement_strength_audit`: certificate existence is an explicit premise or theorem conclusion, not hidden in representation packages.
- `dependency_plan`: import `SemanticRepairFiniteQuerySupportedCurrentShadowFactorization`.
- `math_lean_review_scope`: if used in a target proof, reviewers must check each coordinate certificate is constructed and not moved into a hidden field.

## 審判メモ

- 厳密性: T2 A accepted as target-support / target-obstruction, rejected as target-proof; base 38 if factor-certificate and Bool witness are included.
- 研究価値: T2 B accepted with base 48, but completion remains open.
- repo 全体価値: T2 D accepted; explicit certificate surface has positive rival delta.
- anti-weakening: T2 C accepted with constraints; certificate fields are visible proof obligations.

## 関連

- `research/ideas/g-aat-quality-surface-04-supported-current-shadow-factorization-boundary.md`
- `research/ideas/g-aat-quality-surface-04-recovered-current-shadow-factorization-criterion.md`

## 進捗ログ

- 2026-06-25: Cycle 44 で picked。Lean file、candidate card、report を同期し、T3 build / axiom audit と T4 SCORE 監査で pass / confirmed。
