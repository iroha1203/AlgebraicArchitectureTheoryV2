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

OUT = os.path.dirname(os.path.abspath(__file__))
REPO_ROOT = os.path.normpath(os.path.join(OUT, "..", "..", "..", "..", ".."))
FB = os.path.join(REPO_ROOT, "docs", "reports", "train_ticket_dogfooding", "evidence", "fullbuild")

SURFACE_ID = "law-surface:train-ticket-money-saga-v054"
PROFILE_ID = "profile:train-ticket-money-saga@2"
COVER_ID = "cover:money-settlement-complex"
LAW_COVER_ID = "cover:money-settlement-loop"
DIAGNOSTIC_COVER_ID = "cover:money-settlement-diagnostic"
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
REPAIR_CHARTS = ["ctx:repair-" + chart.removeprefix("ctx:") for chart in CHARTS]
REPAIR_CHART_CONTEXTS = dict(zip(CHARTS, REPAIR_CHARTS))
DIAGNOSTIC_CHARTS = [
    REPAIR_CHART_CONTEXTS[chart]
    for chart in ["ctx:cancel-surface", "ctx:inside-payment-surface", "ctx:order-surface"]
]
DIAGNOSTIC_OVERLAPS = [overlap for overlap in OVERLAPS if overlap in TRIANGLE]
OVERLAP_CONTEXTS = {
    overlap_id: "ctx:intersection:" + overlap_id.removeprefix("overlap:")
    for overlap_id, _, _ in OVERLAPS
}
TRIPLE_CONTEXTS = {
    triple_id: "ctx:intersection:" + triple_id.removeprefix("triple:")
    for triple_id, _ in TRIPLES
}
EDGE_VARS = [
    ("e_cancel_insidepay", "ctx:cancel-surface", "ctx:inside-payment-surface"),
    ("e_insidepay_order", "ctx:inside-payment-surface", "ctx:order-surface"),
    ("e_cancel_order", "ctx:cancel-surface", "ctx:order-surface"),
    ("e_consign_consignprice", "ctx:consign-surface", "ctx:consign-price-surface"),
    ("e_preserve_consign", "ctx:preserve-surface", "ctx:consign-surface"),
    ("e_preserve_order", "ctx:preserve-surface", "ctx:order-surface"),
]
# v0.5.7: the plan declares only the observed 1-skeleton of the selected loop cover.
# The residual is derived by analyze from the observed sections under the witness
# bindings above; nothing about the residual is authored here any more.
PLAN_OVERLAPS = TRIANGLE + [
    ("overlap:consign-consignprice", "ctx:consign-surface", "ctx:consign-price-surface"),
    ("overlap:preserve-consign", "ctx:preserve-surface", "ctx:consign-surface"),
    ("overlap:preserve-order", "ctx:preserve-surface", "ctx:order-surface"),
]
# 各 overlap / chart / triple の equation generator は、法曲面が実際に宣言している
# witness variable と skeleton simplex そのものである。合成した名前は使わない。
EDGE_VAR_BY_OVERLAP = {
    oid: next((v for v, l, r in EDGE_VARS if {l, r} == {left, right}), None)
    for oid, left, right in OVERLAPS
}
# cech law の witness edge に入らない overlap は、同じ法曲面の skeleton simplex へ束縛する。
# cech law の witness edge に入らない overlap と triple には、この法曲面が宣言する
# 対応物が無い。束縛を騙らず、供給側で採番したことが分かる名前にする。
UNBOUND_CELL = {
    oid: "unbound-equation:" + oid
    for oid, var in EDGE_VAR_BY_OVERLAP.items()
    if var is None
}
UNBOUND_CELL["triple:consign-fee-region"] = "unbound-equation:triple:consign-fee-region"
CHART_SIMPLEX = {
    c: f"vertex:money-{c.removeprefix('ctx:').removesuffix('-surface')}" for c in CHARTS
}
# 0.8 x price は 4p/5 なので、丸め剰余は 1/5 セント単位に住む。全セントしか記帳できない
# チャートはこれを表現できない。したがって semantic 側の局所関係は 5 sigma = 0、
# equation 側の obstruction ideal は (5) であり、Q_E(V) = Z/(5) となる。
SUBCENT_UNITS_PER_CENT = 5
REPAIRED_SECTION = "section=money-amount:bigdecimal-scale2-half-even-shared"
REPAIRED_LABELS = {
    "ctx:cancel-surface": "Refund path computes 80% in BigDecimal at scale 2 HALF_EVEN and books the remainder explicitly",
    "ctx:inside-payment-surface": "Inside-payment ledgers the shared scale-2 BigDecimal amount unchanged",
    "ctx:order-surface": "Order keeps the price string but the shared reading is exact scale-2 BigDecimal",
}


def complex_dict():
    return {
        "charts": list(REPAIR_CHARTS),
        "archmapCoverRef": COVER_ID,
        "overlaps": [
            {
                "id": overlap_id,
                "left": REPAIR_CHART_CONTEXTS[left],
                "right": REPAIR_CHART_CONTEXTS[right],
                "archmapContextRef": OVERLAP_CONTEXTS[overlap_id],
            }
            for overlap_id, left, right in OVERLAPS
        ],
        "tripleOverlaps": [
            {
                "id": triple_id,
                "overlapRefs": list(overlap_refs),
                "archmapContextRef": TRIPLE_CONTEXTS[triple_id],
            }
            for triple_id, overlap_refs in TRIPLES
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


def unique(items):
    return list(dict.fromkeys(items))


def source_refs_for(contexts, context_ids):
    refs = []
    for context_id in context_ids:
        context = contexts[context_id]
        if not context["refs"]:
            raise ValueError(f"{context_id} has no source refs")
        refs.append(context["refs"][0])
    return unique(refs)


def intersection_atom_id(context_id):
    return "atom:contract:" + context_id.removeprefix("ctx:").replace(":", "-")


def add_intersection_atom(archmap, context_id, refs):
    atom_id = intersection_atom_id(context_id)
    archmap["atoms"].append({
        "id": atom_id,
        "kind": "contract",
        "subject": context_id,
        "object": "source-grounded finite intersection selected for the settlement presentation",
        "axis": "static",
        "predicate": "component",
        "refs": refs,
    })
    return atom_id


def add_presentation_complex(archmap):
    contexts = {context["id"]: context for context in archmap["contexts"]}
    for chart in CHARTS:
        if chart not in contexts:
            raise ValueError(f"missing chart context: {chart}")

    repair_contexts = {}
    for chart in CHARTS:
        context_id = REPAIR_CHART_CONTEXTS[chart]
        refs = source_refs_for(contexts, [chart])
        context = {
            "id": context_id,
            "atoms": [add_intersection_atom(archmap, context_id, refs)],
            "refs": refs,
            "restrictsTo": [],
        }
        archmap["contexts"].append(context)
        contexts[context_id] = context
        repair_contexts[chart] = context

    overlap_contexts = {}
    for overlap_id, left, right in OVERLAPS:
        context_id = OVERLAP_CONTEXTS[overlap_id]
        if context_id in contexts:
            raise ValueError(f"duplicate intersection context: {context_id}")
        repair_contexts[left]["restrictsTo"].append(context_id)
        repair_contexts[right]["restrictsTo"].append(context_id)
        refs = source_refs_for(contexts, [left, right])
        context = {
            "id": context_id,
            "atoms": [add_intersection_atom(archmap, context_id, refs)],
            "refs": refs,
            "restrictsTo": [],
        }
        archmap["contexts"].append(context)
        contexts[context_id] = context
        overlap_contexts[overlap_id] = context

    triple_context_ids = []
    for triple_id, overlap_refs in TRIPLES:
        context_id = TRIPLE_CONTEXTS[triple_id]
        if context_id in contexts:
            raise ValueError(f"duplicate triple intersection context: {context_id}")
        for overlap_id in overlap_refs:
            overlap_contexts[overlap_id]["restrictsTo"].append(context_id)
        refs = unique(
            ref
            for overlap_id in overlap_refs
            for ref in overlap_contexts[overlap_id]["refs"]
        )
        context = {
            "id": context_id,
            "atoms": [add_intersection_atom(archmap, context_id, refs)],
            "refs": refs,
        }
        archmap["contexts"].append(context)
        contexts[context_id] = context
        triple_context_ids.append(context_id)

    complex_contexts = list(REPAIR_CHARTS) + list(OVERLAP_CONTEXTS.values()) + triple_context_ids
    archmap["covers"].append({
        "id": COVER_ID,
        "contexts": complex_contexts,
        "refs": source_refs_for(contexts, CHARTS),
        "label": "Source-grounded finite settlement complex with explicit pair and triple intersections",
    })
    archmap["covers"].append({
        "id": DIAGNOSTIC_COVER_ID,
        "contexts": list(DIAGNOSTIC_CHARTS),
        "refs": source_refs_for(contexts, ["ctx:cancel-surface", "ctx:inside-payment-surface", "ctx:order-surface"]),
        "label": "Refund settlement diagnostic component",
    })
    archmap["covers"].append({
        "id": LAW_COVER_ID,
        "contexts": list(CHARTS),
        "refs": source_refs_for(contexts, CHARTS),
        "label": "Observed settlement surface for law evaluation",
    })


# ---- archmap variants -------------------------------------------------------
base = json.load(open(os.path.join(FB, "archmap-money-variant.json")))

head = copy.deepcopy(base)
head["schema"] = "archmap/v0.5.4"
head["id"] = "train-ticket-money-saga-head/v0.5.4"
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
add_presentation_complex(head)
write("archmap-saga-head.json", head)

repaired = copy.deepcopy(head)
repaired["id"] = "train-ticket-money-saga-repaired/v0.5.4"
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
    "schema": "law-equation-surface/v0.5.4",
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
            "coverRef": LAW_COVER_ID,
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
    "schema": "law-policy/v0.5.4",
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
            "path": "docs/reports/train_ticket_dogfooding/evidence/saga/build_saga_artifacts.py",
            "revision": "train-ticket-313886e9",
        }
    ],
}
write("law-policy-saga.json", policy)

profile = {
    "schema": "measurement-profile/v0.5.4",
    "profileId": PROFILE_ID,
    "siteRef": "archmap:/contexts",
    "coverRef": LAW_COVER_ID,
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
    "schema": "archsig-gate-policy/v0.5.4",
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
    return {
        "schema": "archsig-repair-plan/v0.5.7",
        "id": "repair-plan:train-ticket-money-" + ("head" if drifted else "repaired"),
        "complex": {
            "charts": list(CHARTS),
            "overlaps": [
                {"id": oid, "left": left, "right": right}
                for oid, left, right in PLAN_OVERLAPS
            ],
            "tripleOverlaps": [],
            "enumerationComplete": True,
        },
    }


write("repair-plan-head.json", repair_plan(True))
write("repair-plan-repaired.json", repair_plan(False))
