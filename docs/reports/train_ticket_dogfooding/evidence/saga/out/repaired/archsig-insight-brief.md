# ArchSig Insight Brief

## Read this first
Conclusion: REPAIR_GLUES_WITHIN_SELECTED_COMPLEX

What it means:
ag.saga-grounded did not compute because grounded_skeleton_not_aligned.

Where to look first:

Next action:
Inspect blocking reason

Boundary:
Profile-relative. 10 assumptions declared. 0 supports unmeasured. 0 unknown. 1 not_computed.

## Top insights
- Measurement blocked by reason code: ag.saga-grounded did not compute because grounded_skeleton_not_aligned.
  Why this matters: The blocked reason belongs in the Decision Bar so reviewers do not mistake an empty scene for absence of conflict.
- No measured H^1 glue mismatch under profile: No selected-cover H^1 glue mismatch was measured under this profile.
  Why this matters: This lets reviewers distinguish a profile-relative zero result from unmeasured or unknown regions.
- Measurement boundary recorded: Checked, assumed, unmeasured, unknown, and not_computed states are preserved for review.
  Why this matters: This tells reviewers exactly where the conclusion is profile-relative and where it is blocked or unmeasured.

## Where to look
- src:ts-admin-basic-info-service/src/main/java/adminbasic/AdminBasicInfoApplication.java
- src:ts-admin-basic-info-service/src/main/java/adminbasic/config/SecurityConfig.java
- src:ts-admin-basic-info-service/src/main/java/adminbasic/controller/AdminBasicInfoController.java
- src:ts-admin-basic-info-service/src/main/java/adminbasic/entity/PriceInfo.java
- src:ts-admin-basic-info-service/src/main/java/adminbasic/service/AdminBasicInfoService.java
- src:ts-admin-basic-info-service/src/main/java/adminbasic/service/AdminBasicInfoServiceImpl.java
- src:ts-admin-basic-info-service/src/main/resources/application.yml
- src:ts-admin-order-service/src/main/java/adminorder/AdminOrderApplication.java
- src:ts-admin-order-service/src/main/java/adminorder/config/SecurityConfig.java
- src:ts-admin-order-service/src/main/java/adminorder/controller/AdminOrderController.java

## Suggested next inspections
- Inspect blocking reason: ag.saga-grounded did not compute because grounded_skeleton_not_aligned.
- Inspect measurement boundary: No selected-cover H^1 glue mismatch was measured under this profile.
- Inspect measurement boundary: Checked, assumed, unmeasured, unknown, and not_computed states are preserved for review.

## Repair candidates
- No measured repair candidate was promoted by this packet.

## Measurement boundary
Profile-relative. 10 assumptions declared. 0 supports unmeasured. 0 unknown. 1 not_computed.
- checked: 4
- assumed: 10
- blocking: 1
- omitted detail counts:
  - omittedAtoms: 0
  - omittedEdges: 0
  - omittedContextMemberships: 0
  - omittedCoverOverlaps: 0
  - omittedSceneLayerObjects: 0
  - omittedLabels: 0
  - omittedSourceRefs: 0

## Artifact links
- summaryRef: archsig-analysis-summary.json
- briefRef: archsig-insight-brief.md
- viewerDataRef: archsig-atom-viewer-data.json

## Raw technical details
- source packet: archsig-measurement-packet.json
- theorem-candidate readings are analytic-only and are not structural conclusions.
- holonomy-like visual modes are exploratory cover / restriction path views, not monodromy verdicts.

## LLM handoff
Use the following ArchSig result as bounded evidence.
Do not infer beyond the listed claims and boundaries.

Conclusion:
REPAIR_GLUES_WITHIN_SELECTED_COMPLEX

Top insights:
- ag.saga-grounded did not compute because grounded_skeleton_not_aligned.
- No selected-cover H^1 glue mismatch was measured under this profile.
- Checked, assumed, unmeasured, unknown, and not_computed states are preserved for review.

Boundary:
Profile-relative. 10 assumptions declared. 0 supports unmeasured. 0 unknown. 1 not_computed.

Source refs:
- src:ts-admin-basic-info-service/src/main/java/adminbasic/AdminBasicInfoApplication.java
- src:ts-admin-basic-info-service/src/main/java/adminbasic/config/SecurityConfig.java
- src:ts-admin-basic-info-service/src/main/java/adminbasic/controller/AdminBasicInfoController.java
- src:ts-admin-basic-info-service/src/main/java/adminbasic/entity/PriceInfo.java
- src:ts-admin-basic-info-service/src/main/java/adminbasic/service/AdminBasicInfoService.java
- src:ts-admin-basic-info-service/src/main/java/adminbasic/service/AdminBasicInfoServiceImpl.java
- src:ts-admin-basic-info-service/src/main/resources/application.yml
- src:ts-admin-order-service/src/main/java/adminorder/AdminOrderApplication.java
- src:ts-admin-order-service/src/main/java/adminorder/config/SecurityConfig.java
- src:ts-admin-order-service/src/main/java/adminorder/controller/AdminOrderController.java
