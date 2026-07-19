#!/usr/bin/env python3
"""train-ticket money settlement loop: full-SAGA artifact builder.

Real finding (train-ticket 313886e9, verified against source):
  cancel  : Double.parseDouble(order.getPrice()) * 0.8 -> DecimalFormat("0.00")
            (CancelServiceImpl.calculateRefund)
  inside-payment: new BigDecimal(order.getPrice()) exact arithmetic
            (InsidePaymentServiceImpl)
  order   : Order.price is `private String price` (string passthrough)
Real call triangle cancel--inside-payment--order with three pairwise distinct
conventions => odd parity on a closed loop => nonzero F2 class.
Zero primitive: consign--consign-price (both double-primitive-fields, real edge).
"""
import copy
import hashlib
import json
import os

FB = "<SCRATCHPAD>/fullbuild"
OUT = os.path.dirname(os.path.abspath(__file__))

SURFACE_ID = "law-surface:train-ticket-money-saga-v053"
PROFILE_ID = "profile:train-ticket-money-saga@1"
COVER_ID = "cover:money-settlement-loop"
DRIFT = "drift:refund-rounding"
WITNESS_ATOM = "atom:refund-drift-witness"

CHARTS = [
    "ctx:cancel-surface",
    "ctx:inside-payment-surface",
    "ctx:order-surface",
    "ctx:consign-surface",
    "ctx:consign-price-surface",
    "ctx:preserve-surface",
]
TRIANGLE = [
    ("overlap:cancel-insidepay", "ctx:cancel-surface", "ctx:inside-payment-surface"),
    ("overlap:insidepay-order", "ctx:inside-payment-surface", "ctx:order-surface"),
    ("overlap:cancel-order", "ctx:cancel-surface", "ctx:order-surface"),
]
# Consign-fee region: preserve books a consignment, consign prices it via
# consign-price and returns the fee; the same fee value is shared by all three
# charts, with no refund-rounding residue on any of these overlaps.
CONSIGN_FEE = [
    ("overlap:consign-consignprice", "ctx:consign-surface", "ctx:consign-price-surface"),
    ("overlap:preserve-consign", "ctx:preserve-surface", "ctx:consign-surface"),
    ("overlap:preserve-consignprice", "ctx:preserve-surface", "ctx:consign-price-surface"),
]
OVERLAPS = TRIANGLE + CONSIGN_FEE
TRIPLES = [
    ("triple:consign-fee-region", [oid for oid, _, _ in CONSIGN_FEE]),
]
EDGE_VARS = [
    ("e_cancel_insidepay", "ctx:cancel-surface", "ctx:inside-payment-surface"),
    ("e_insidepay_order", "ctx:inside-payment-surface", "ctx:order-surface"),
    ("e_cancel_order", "ctx:cancel-surface", "ctx:order-surface"),
    ("e_consign_consignprice", "ctx:consign-surface", "ctx:consign-price-surface"),
]
REPAIRED_SECTION = "section=money-amount:bigdecimal-scale2-half-even-shared"
REPAIRED_LABELS = {
    "ctx:cancel-surface": "Refund path computes 80% in BigDecimal at scale 2 HALF_EVEN and books the remainder explicitly",
    "ctx:inside-payment-surface": "Inside-payment ledgers the shared scale-2 BigDecimal amount unchanged",
    "ctx:order-surface": "Order keeps the price string but the shared reading is exact scale-2 BigDecimal",
}


def complex_dict():
    return {
        "charts": list(CHARTS),
        "overlaps": [{"id": i, "left": l, "right": r} for i, l, r in OVERLAPS],
        "tripleOverlaps": [
            {"id": tid, "overlapRefs": list(refs)} for tid, refs in TRIPLES
        ],
        "enumerationComplete": True,
    }


def fingerprint(cx):
    return hashlib.sha256(json.dumps(cx, separators=(",", ":")).encode()).hexdigest()


def write(name, obj):
    with open(os.path.join(OUT, name), "w") as f:
        json.dump(obj, f, indent=1, ensure_ascii=False)
        f.write("\n")
    print("wrote", name)


# ---- archmap variants -------------------------------------------------------
base = json.load(open(os.path.join(FB, "archmap-money-variant.json")))

head = copy.deepcopy(base)
head["id"] = "train-ticket-money-saga-head/v0.5.3"
head["covers"].append({
    "id": COVER_ID,
    "contexts": list(CHARTS),
    "refs": [
        "src:ts-cancel-service/src/main/java/cancel/service/CancelServiceImpl.java",
        "src:ts-inside-payment-service/src/main/java/inside_payment/service/InsidePaymentServiceImpl.java",
    ],
    "label": "Refund settlement loop cancel/inside-payment/order plus the preserve/consign/consign-price fee region as glued reference",
})
head["atoms"].append({
    "id": WITNESS_ATOM,
    "kind": "semantic",
    "subject": DRIFT,
    "object": "cancel books an 80% refund rounded by DecimalFormat(\"0.00\") while inside-payment ledgers the exact BigDecimal amount against order's unrounded price string; the rounding remainder is recorded nowhere",
    "axis": "semantic",
    "predicate": "reconciliationResidue",
    "refs": [
        "src:ts-cancel-service/src/main/java/cancel/service/CancelServiceImpl.java",
    ],
    "label": "CancelServiceImpl.calculateRefund rounds 0.8*price to two decimals; no chart books the sub-cent remainder",
})
write("archmap-saga-head.json", head)

repaired = copy.deepcopy(head)
repaired["id"] = "train-ticket-money-saga-repaired/v0.5.3"
repaired["atoms"] = [a for a in repaired["atoms"] if a["id"] != WITNESS_ATOM]
for a in repaired["atoms"]:
    if a.get("axis") == "cech" and a.get("predicate") == "sectionValue" and a["subject"] in REPAIRED_LABELS:
        a["object"] = REPAIRED_SECTION
        a["label"] = REPAIRED_LABELS[a["subject"]]
write("archmap-saga-repaired.json", repaired)

# ---- law surface ------------------------------------------------------------
def edge_witnesses():
    return [
        {"variable": v, "binding": {"edge": [l, r], "axis": "cech", "predicate": "sectionValue"}}
        for v, l, r in EDGE_VARS
    ]

surface = {
    "schema": "law-equation-surface/v0.5.3",
    "id": SURFACE_ID,
    "laws": [
        {
            "lawId": "surface:cech-surface-v052",
            "conditionType": "closed-equational",
            "witnessVariables": edge_witnesses(),
            "forbiddenSupportGenerators": [{"support": [v]} for v, _, _ in EDGE_VARS],
        },
        {
            "lawId": "law:money-settlement-convention",
            "conditionType": "closed-equational",
            "witnessVariables": edge_witnesses(),
            "forbiddenSupportGenerators": [{"support": [v for v, _, _ in EDGE_VARS]}],
        },
        {
            "lawId": "law:money-repair-descent",
            "conditionType": "descent",
            "evaluatorRef": "ag.saga-descent",
        },
    ],
    "skeleton": [
        {
            "simplex": f"vertex:money-{c.removeprefix('ctx:').removesuffix('-surface')}",
            "supportAtomRef": f"atom:semantic:{c.removeprefix('ctx:')}:cech-section-money-amount",
            "requiredLawId": "law:money-settlement-convention",
        }
        for c in CHARTS
    ],
    "defectSources": [
        {
            "lawId": "law:money-settlement-convention",
            "coverRef": COVER_ID,
            "chartDefects": [
                {"chart": c, "defectObservable": {"axis": "square-free", "predicate": "support"}}
                for c in CHARTS
            ],
            "holdsCriterion": {"kind": "defect-raw-value-zero", "zeroSense": "empty-witness-set"},
        }
    ],
    "quotientSheafCondition": {"mode": "assumed"},
}
write("law-surface-saga.json", surface)

# ---- law policy / profile / gate -------------------------------------------
policy = {
    "schema": "law-policy/v0.5.3",
    "id": "train-ticket-money-saga-policy",
    "lawSurfaceRef": SURFACE_ID,
    "measurementProfileRef": PROFILE_ID,
    "policies": [
        {
            "law": law,
            "evaluator": ev,
            "basis": ["policy-basis:shared-convention-consistency"],
            "scope": [
                "ts-cancel-service/",
                "ts-inside-payment-service/",
                "ts-order-service/",
                "ts-consign-service/",
                "ts-consign-price-service/",
            ],
            "severity": "high",
        }
        for law, ev in [
            ("surface:cech-surface-v052", "ag.cech-obstruction"),
            ("law:money-settlement-convention", "ag.saga-grounded"),
            ("law:money-repair-descent", "ag.saga-descent"),
        ]
    ],
    "basisLedger": [
        {
            "basisId": "policy-basis:shared-convention-consistency",
            "kind": "repo-document",
            "path": "docs/aat/algebraic_geometric_theory/README.md",
            "revision": "aat-ag-current",
        }
    ],
}
write("law-policy-saga.json", policy)

profile = {
    "schema": "measurement-profile/v0.5.3",
    "profileId": PROFILE_ID,
    "siteRef": "archmap:/contexts",
    "coverRef": COVER_ID,
    "coefficient": "F2",
    "effCoeff": "finite-linear-algebra@1",
    "resolutionSelector": "taylor@1",
    "domain": "finite-poset-site",
    "zeroPredicate": "rank-zero@1",
    "nonZeroPredicate": "rank-positive@1",
    "certSelector": "finite-certificate@1",
    "verdictDiscipline": "five-valued-structural-verdict@1",
    "finiteBounds": {
        "maxSquareFreeWitnessVariables": 12,
        "maxCoherenceContexts": 12,
        "maxTorWitnessVariables": 12,
        "maxBoundaryResidueVariables": 16,
        "maxLaplacianCells": 16,
        "maxPeriodCycles": 16,
        "maxTransferTargets": 16,
    },
}
write("measurement-profile-saga.json", profile)

gate = {
    "schema": "archsig-gate-policy/v0.5.3",
    "policyId": "gate-policy:train-ticket-money-saga@1",
    "rules": [
        {
            "ruleId": "absolute-verdict-discipline",
            "scope": "absolute",
            "verdictMapping": {
                "measured_zero": "pass",
                "measured_nonzero": "block",
                "unmeasured": "pass_with_boundary",
                "unknown": "pass_with_boundary",
                "not_computed": "pass_with_boundary",
                "violated_assumption_dependency": "block",
            },
            "boundaryKindOverrides": {"silence_by_design": "pass_with_boundary"},
        },
        {
            "ruleId": "introduced-by-change-discipline",
            "scope": "introduced-by-change",
            "introducedByChangeMapping": {
                "new": "block",
                "cleared": "pass",
                "preexisting": "pass_with_boundary",
                "removed": "pass_with_boundary",
                "other": "pass_with_boundary",
            },
        },
    ],
}
write("gate-policy-saga.json", gate)

# ---- repair plans -----------------------------------------------------------
def repair_plan(drifted):
    cx = complex_dict()
    fp = fingerprint(cx)
    var = [DRIFT] if drifted else []
    vmap = [{"source": DRIFT, "target": DRIFT}] if drifted else []
    triangle_ids = {i for i, _, _ in TRIANGLE}
    plan = {
        "schema": "archsig-repair-plan/v0.5.3",
        "id": "repair-plan:train-ticket-money-" + ("head" if drifted else "repaired"),
        "residual": {"kind": "supplied"},
        "complex": cx,
        "primitives": [
            {
                "id": "primitive:" + oid.removeprefix("overlap:"),
                "overlapRef": oid,
                "resL": list(var) if oid in triangle_ids else [],
                "resR": [],
                "support": {
                    "kind": "supplied",
                    "variables": list(var) if oid in triangle_ids else [],
                },
            }
            for oid, _, _ in OVERLAPS
        ],
        "semanticProjection": {
            "lambda": [WITNESS_ATOM] if drifted else [],
            "k": list(var),
            "pi": [{"atomRef": WITNESS_ATOM, "subject": DRIFT}] if drifted else [],
        },
        "faithfulness": {
            "mode": "supplied",
            "supplied": {
                "zeroPrimitiveRef": "primitive:consign-consignprice",
                "residualSupportPredicate": {
                    "kind": "finite-support",
                    "supportVariables": list(var),
                    "zeroOnZeroPrimitive": True,
                },
                "faithfulnessLaw": "the refund rounding witness projects one-to-one onto the cancel-service reconciliation observation",
            },
        },
        "coefficient": "f2-additive",
        "trueSheafCertificate": {
            "kind": "true-sheaf-certificate",
            "coverRef": COVER_ID,
            "memberCharts": list(CHARTS),
            "globalCondition": "assumed",
        },
        "gluingData": {
            "kind": "gluing-data",
            "overlapRefs": [oid for oid, _, _ in OVERLAPS],
            "sectionRefs": [
                {"overlapRef": oid, "sectionRef": "section:money-" + oid.removeprefix("overlap:")}
                for oid, _, _ in OVERLAPS
            ],
        },
        "grounding": {
            "kind": "saga-grounding",
            "surfaceRef": SURFACE_ID,
            "profileRef": PROFILE_ID,
        },
        "comparison": {
            "kind": "saga-comparison",
            "incidenceBridge": {
                "kind": "explicit",
                "sourceComplexRef": "complex:repair",
                "targetComplexRef": "complex:cech",
                "targetComplex": complex_dict(),
            },
            "h1ComparisonData": {
                "schema": "h1-comparison-data/v0.5.3",
                "kind": "explicit",
                "cochainMapRef": "comparison:cochain-map",
                "sourceComplexFingerprint": fp,
                "targetComplexFingerprint": fp,
                "targetCochainSupport": [
                    {
                        "overlapRef": oid,
                        "support": list(var) if oid in triangle_ids else [],
                    }
                    for oid, _, _ in OVERLAPS
                ],
                "cochainMap": {
                    "degreeZero": [
                        {"sourceChartRef": c, "targetChartRef": c, "variableMap": list(vmap)}
                        for c in CHARTS
                    ],
                    "degreeOne": [
                        {"sourceOverlapRef": oid, "targetOverlapRef": oid, "variableMap": list(vmap)}
                        for oid, _, _ in OVERLAPS
                    ],
                    "degreeTwo": {
                        "basisMap": [
                            {"sourceTripleRef": tid, "targetTripleRef": tid}
                            for tid, _ in TRIPLES
                        ],
                        "zeroImage": [],
                    },
                },
            },
        },
    }
    return plan

write("repair-plan-head.json", repair_plan(True))
write("repair-plan-repaired.json", repair_plan(False))
print("complex fingerprint:", fingerprint(complex_dict()))
