# ArchSig Insight Brief

## Read this first
Conclusion: MEASURED_NONGLUING_RESIDUAL_CLASS

What it means:
Local checks do not explain the whole selected cover; ArchSig measured a cross-context H^1 mismatch.

Where to look first:
- src:ts-cancel-service/src/main/java/cancel/config/SecurityConfig.java
- src:ts-cancel-service/src/main/java/cancel/controller/CancelController.java
- src:ts-consign-price-service/src/main/java/consignprice/config/SecurityConfig.java
- src:ts-order-service/src/main/java/order/config/SecurityConfig.java
- src:ts-preserve-service/src/main/java/preserve/config/SecurityConfig.java

Next action:
Inspect mismatch support

Boundary:
Profile-relative. 11 assumptions declared. 0 supports unmeasured. 0 unknown. 0 not_computed.

## Top insights
- Global glue mismatch measured: Local checks do not explain the whole selected cover; ArchSig measured a cross-context H^1 mismatch.
  Why this matters: This highlights architecture drift that can be invisible as a local law violation and gives reviewers a first seam to inspect.
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
- Inspect mismatch support: Local checks do not explain the whole selected cover; ArchSig measured a cross-context H^1 mismatch.
- Inspect measurement boundary: Checked, assumed, unmeasured, unknown, and not_computed states are preserved for review.

## Repair candidates
- No measured repair candidate was promoted by this packet.

## Measurement boundary
Profile-relative. 11 assumptions declared. 0 supports unmeasured. 0 unknown. 0 not_computed.
- checked: 5
- assumed: 11
- blocking: 0
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
MEASURED_NONGLUING_RESIDUAL_CLASS

Top insights:
- Local checks do not explain the whole selected cover; ArchSig measured a cross-context H^1 mismatch.
- Checked, assumed, unmeasured, unknown, and not_computed states are preserved for review.

Boundary:
Profile-relative. 11 assumptions declared. 0 supports unmeasured. 0 unknown. 0 not_computed.

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
