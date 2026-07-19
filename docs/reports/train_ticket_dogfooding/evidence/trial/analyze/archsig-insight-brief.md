# ArchSig Insight Brief

## Read this first
Conclusion: NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE

What it means:
No selected-cover H^1 glue mismatch was measured under this profile.

Where to look first:
- src:ts-cancel-service/src/main/java/cancel/config/SecurityConfig.java
- src:ts-inside-payment-service/src/main/java/inside_payment/config/SecurityConfig.java
- src:ts-notification-service/src/main/java/notification/config/SecurityConfig.java
- src:ts-order-other-service/src/main/java/other/config/SecurityConfig.java
- src:ts-order-service/src/main/java/order/config/SecurityConfig.java

Next action:
Inspect measurement boundary

Boundary:
Profile-relative. 7 assumptions declared. 0 supports unmeasured. 0 unknown. 0 not_computed.

## Top insights
- No measured H^1 glue mismatch under profile: No selected-cover H^1 glue mismatch was measured under this profile.
  Why this matters: This lets reviewers distinguish a profile-relative zero result from unmeasured or unknown regions.
- Measurement boundary recorded: Checked, assumed, unmeasured, unknown, and not_computed states are preserved for review.
  Why this matters: This tells reviewers exactly where the conclusion is profile-relative and where it is blocked or unmeasured.

## Where to look
- src:ts-cancel-service/src/main/java/cancel/CancelApplication.java
- src:ts-cancel-service/src/main/java/cancel/config/SecurityConfig.java
- src:ts-cancel-service/src/main/java/cancel/controller/CancelController.java
- src:ts-cancel-service/src/main/java/cancel/entity/GetAccountByIdInfo.java
- src:ts-cancel-service/src/main/java/cancel/entity/GetAccountByIdResult.java
- src:ts-cancel-service/src/main/java/cancel/entity/GetOrderByIdInfo.java
- src:ts-cancel-service/src/main/java/cancel/service/CancelService.java
- src:ts-cancel-service/src/main/java/cancel/service/CancelServiceImpl.java
- src:ts-cancel-service/src/main/resources/application.yml
- src:ts-inside-payment-service/src/main/java/inside_payment/InsidePaymentApplication.java

## Suggested next inspections
- Inspect measurement boundary: No selected-cover H^1 glue mismatch was measured under this profile.
- Inspect measurement boundary: Checked, assumed, unmeasured, unknown, and not_computed states are preserved for review.

## Repair candidates
- No measured repair candidate was promoted by this packet.

## Measurement boundary
Profile-relative. 7 assumptions declared. 0 supports unmeasured. 0 unknown. 0 not_computed.
- checked: 4
- assumed: 7
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
NO_MEASURED_H1_OBSTRUCTION_UNDER_PROFILE

Top insights:
- No selected-cover H^1 glue mismatch was measured under this profile.
- Checked, assumed, unmeasured, unknown, and not_computed states are preserved for review.

Boundary:
Profile-relative. 7 assumptions declared. 0 supports unmeasured. 0 unknown. 0 not_computed.

Source refs:
- src:ts-cancel-service/src/main/java/cancel/CancelApplication.java
- src:ts-cancel-service/src/main/java/cancel/config/SecurityConfig.java
- src:ts-cancel-service/src/main/java/cancel/controller/CancelController.java
- src:ts-cancel-service/src/main/java/cancel/entity/GetAccountByIdInfo.java
- src:ts-cancel-service/src/main/java/cancel/entity/GetAccountByIdResult.java
- src:ts-cancel-service/src/main/java/cancel/entity/GetOrderByIdInfo.java
- src:ts-cancel-service/src/main/java/cancel/service/CancelService.java
- src:ts-cancel-service/src/main/java/cancel/service/CancelServiceImpl.java
- src:ts-cancel-service/src/main/resources/application.yml
- src:ts-inside-payment-service/src/main/java/inside_payment/InsidePaymentApplication.java
