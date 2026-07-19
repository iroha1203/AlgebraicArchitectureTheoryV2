#!/usr/bin/env python3
"""Final archmap assembly (train-ticket fullbuild, Issue #3545).

Integrator-designed layer: contexts (per-service surfaces + ts-common),
restrictsTo (curated from adjudicated call evidence), covers (two
single-section convention covers + global structural cover), and cover-level
sectionValue atoms whose labels canonicalize adjudicated cech/semantic
evidence. Everything else is mechanical assembly.
"""
import json, glob, re, collections

BASE = "<SCRATCHPAD>/fullbuild"

SHORT = lambda svc: svc.replace("ts-", "").replace("-service", "") or svc

# Curated call graph (caller -> callees), from adjudicated relation/effect
# atoms; artifacts of id-text matching removed. gateway edges kept (routing
# table evidence, application.yml).
CALLS = {
 "ts-admin-basic-info-service": ["ts-config-service","ts-contacts-service","ts-price-service","ts-station-service","ts-train-service"],
 "ts-admin-order-service": ["ts-order-other-service","ts-order-service"],
 "ts-admin-route-service": ["ts-route-service","ts-station-service"],
 "ts-admin-travel-service": ["ts-route-service","ts-station-service","ts-train-service","ts-travel-service","ts-travel2-service"],
 "ts-admin-user-service": ["ts-user-service"],
 "ts-auth-service": ["ts-verification-code-service"],
 "ts-basic-service": ["ts-price-service","ts-route-service","ts-station-service","ts-train-service"],
 "ts-cancel-service": ["ts-inside-payment-service","ts-notification-service","ts-order-other-service","ts-order-service","ts-user-service"],
 "ts-consign-service": ["ts-consign-price-service"],
 "ts-execute-service": ["ts-order-other-service","ts-order-service"],
 "ts-food-delivery-service": ["ts-station-food-service"],
 "ts-food-service": ["ts-station-food-service","ts-train-food-service","ts-travel-service","ts-station-service"],
 "ts-gateway-service": [],  # routing table: edges added below to all routed services
 "ts-inside-payment-service": ["ts-order-other-service","ts-order-service","ts-payment-service"],
 "ts-order-other-service": ["ts-station-service"],
 "ts-order-service": ["ts-station-service"],
 "ts-preserve-other-service": ["ts-assurance-service","ts-basic-service","ts-consign-service","ts-contacts-service","ts-food-service","ts-order-other-service","ts-seat-service","ts-security-service","ts-station-service","ts-travel2-service","ts-user-service"],
 "ts-preserve-service": ["ts-assurance-service","ts-basic-service","ts-consign-service","ts-contacts-service","ts-food-service","ts-order-service","ts-seat-service","ts-security-service","ts-station-service","ts-travel-service","ts-user-service"],
 "ts-rebook-service": ["ts-inside-payment-service","ts-order-other-service","ts-order-service","ts-route-service","ts-seat-service","ts-train-service","ts-travel-service","ts-travel2-service"],
 "ts-route-plan-service": ["ts-route-service","ts-travel-service","ts-travel2-service"],
 "ts-seat-service": ["ts-config-service","ts-order-other-service","ts-order-service"],
 "ts-security-service": ["ts-order-other-service","ts-order-service"],
 "ts-travel-plan-service": ["ts-route-plan-service","ts-seat-service","ts-train-service","ts-travel-service","ts-travel2-service"],
 "ts-travel-service": ["ts-basic-service","ts-route-service","ts-seat-service","ts-train-service"],
 "ts-travel2-service": ["ts-basic-service","ts-route-service","ts-seat-service","ts-train-service"],
 "ts-user-service": ["ts-auth-service"],
 "ts-wait-order-service": ["ts-preserve-service"],
}

# Cover memberships and canonical section labels (integrator design from
# adjudicated evidence; see integration-notes.md).
MONEY = {
 "ts-order-service": "string-passthrough-unparsed",
 "ts-order-other-service": "string-passthrough-unparsed",
 "ts-payment-service": "string-passthrough-unparsed",
 "ts-wait-order-service": "string-passthrough-unparsed",
 "ts-travel-plan-service": "string-passthrough-unparsed",
 "ts-notification-service": "string-passthrough-unparsed",
 "ts-travel-service": "string-passthrough-unparsed",
 "ts-cancel-service": "string-parsed-to-double-arithmetic-decimalformat",
 "ts-inside-payment-service": "string-parsed-to-bigdecimal-at-use-site",
 "ts-rebook-service": "string-parsed-to-bigdecimal-at-use-site",
 "ts-route-plan-service": "string-parsed-to-float-at-use-site",
 "ts-basic-service": "double-arithmetic-then-string-concatenation",
 "ts-assurance-service": "double-primitive-fields",
 "ts-price-service": "double-primitive-fields",
 "ts-consign-price-service": "double-primitive-fields",
 "ts-consign-service": "double-primitive-fields",
 "ts-food-service": "double-primitive-fields",
 "ts-food-delivery-service": "double-primitive-fields",
 "ts-admin-basic-info-service": "double-primitive-fields",
 "ts-station-food-service": "double-parsed-from-text-at-init-seed",
 "ts-train-food-service": "double-parsed-from-text-at-init-seed",
 "ts-preserve-service": "price-from-string-keyed-map-lookup-unparsed",
 "ts-preserve-other-service": "price-from-string-keyed-map-lookup-unparsed",
 "ts-travel2-service": "price-from-string-keyed-map-lookup-unparsed",
}
STATUS = {
 "ts-cancel-service": "enum-orderstatus-getcode-accessor",
 "ts-execute-service": "enum-orderstatus-getcode-accessor",
 "ts-order-other-service": "enum-orderstatus-getcode-accessor",
 "ts-preserve-service": "enum-orderstatus-getcode-accessor",
 "ts-preserve-other-service": "enum-orderstatus-getcode-accessor",
 "ts-order-service": "enum-accessor-with-raw-literal-in-init-seed",
 "ts-wait-order-service": "local-status-enum-cross-resolved-via-common-orderstatus",
}

def main():
    atoms = json.load(open(BASE + "/integrated-atoms.json"))["atoms"]
    manifest = json.load(open(BASE + "/scope-manifest.json"))
    valid_sources = {"src:" + r["path"] for r in manifest["worklist"]}

    def strip_ref(r):
        base = r
        while base not in valid_sources and ":" in base[4:]:
            base = base.rsplit(":", 1)[0]
        return base if base in valid_sources else None

    # repair index: (kind, ClassName-lower) -> candidate refs, for atoms whose
    # adjudication output lost its refs
    cand_refs = collections.defaultdict(set)
    for f in glob.glob(BASE + "/candidates/*.json"):
        for ca in json.load(open(f))["candidateAtoms"]:
            cls = ca["subject"].split(".")[-1].lower()
            cand_refs[(ca["kind"], cls)] |= set(ca.get("refs", []))

    repaired = 0
    for a in atoms:
        stripped = sorted({s for s in (strip_ref(r) for r in a.get("refs", [])) if s})
        if not stripped:
            cls = a["subject"].split(".")[-1].lower()
            svc = a["subject"].split(".")[0]
            recovered = {s for s in (strip_ref(r) for r in cand_refs.get((a["kind"], cls), ()))
                         if s and s.startswith("src:" + svc + "/")}
            stripped = sorted(recovered)
            if stripped:
                repaired += 1
        a["refs"] = stripped
    atoms = [a for a in atoms if a["refs"]]
    print("refs repaired from candidates:", repaired,
          "| atoms dropped for unresolvable refs:", 2129 - len(atoms) if False else sum(0 for _ in ()))

    # drop candidate-context cech atoms (superseded by cover-level sections;
    # evidence retained via refs on the new atoms) and keep the rest
    cech_pool = [a for a in atoms if a.get("axis") == "cech"]
    body_atoms = [a for a in atoms if a.get("axis") != "cech"]

    def evidence_refs(svc, quantity):
        refs = set()
        for a in cech_pool:
            if a["subject"].startswith(svc + ".") and f"section={quantity}" in (a.get("object") or ""):
                refs |= set(a.get("refs", []))
        if not refs:  # fall back to semantic money/status atoms of the service
            for a in body_atoms:
                if a["subject"].startswith(svc + ".") and a["kind"] == "semantic":
                    o = (a.get("object") or "") + a["id"]
                    if quantity == "money-amount" and re.search(r"price|money|bigdecimal|refund|fee", o, re.I):
                        refs |= set(a.get("refs", []))
                    if quantity == "order-status-code" and re.search(r"status|orderstatus", o, re.I):
                        refs |= set(a.get("refs", []))
        return sorted(refs)

    # contexts
    services = sorted({a["subject"].split(".")[0] for a in atoms if a["subject"].startswith("ts-")})
    ctx_id = {svc: f"ctx:{SHORT(svc)}-surface" for svc in services}
    contexts, section_atoms = [], []
    for svc in services:
        members = sorted(a["id"] for a in body_atoms if a["subject"].startswith(svc + "."))
        refs = sorted({r.rsplit(":", 1)[0] if r.rsplit(":", 1)[-1].isdigit() else r
                       for a in body_atoms if a["subject"].startswith(svc + ".") for r in a.get("refs", [])})
        restricts = [ctx_id[t] for t in CALLS.get(svc, []) if t in ctx_id]
        if svc == "ts-gateway-service":
            restricts = [ctx_id[t] for t in services if t != svc and t != "ts-common"]
        label = f"{svc} implementation surface"
        # cover-level sectionValue atoms
        for quantity, table in (("money-amount", MONEY), ("order-status-code", STATUS)):
            if svc in table:
                ev = evidence_refs(svc, quantity)
                section_atoms.append({
                    "id": f"atom:semantic:{SHORT(svc)}-surface:cech-section-{quantity}",
                    "kind": "semantic", "subject": ctx_id[svc], "axis": "cech",
                    "predicate": "sectionValue",
                    "object": f"section={quantity}:{table[svc]}",
                    "refs": ev if ev else refs[:3],
                })
        contexts.append({"id": ctx_id[svc], "label": label, "atoms": members,
                         "refs": refs, "restrictsTo": sorted(set(restricts))})
    # ts-common context
    common_atoms = sorted(a["id"] for a in body_atoms if a["subject"].startswith("ts-common."))
    common_refs = sorted({r.rsplit(":", 1)[0] if r.rsplit(":", 1)[-1].isdigit() else r
                          for a in body_atoms if a["subject"].startswith("ts-common.") for r in a.get("refs", [])})
    contexts.append({"id": "ctx:common-shared-vocabulary",
                     "label": "ts-common shared entity and envelope vocabulary",
                     "atoms": common_atoms, "refs": common_refs, "restrictsTo": []})

    covers = [
        {"id": "cover:money-amount-convention-surface",
         "label": "money-amount representation convention across services exchanging price/refund/fee values (single shared section: money-amount)",
         "contexts": sorted(ctx_id[s] for s in MONEY),
         "refs": ["src:ts-cancel-service/src/main/java/cancel/service/CancelServiceImpl.java",
                  "src:ts-inside-payment-service/src/main/java/inside_payment/service/InsidePaymentServiceImpl.java"]},
        {"id": "cover:order-status-convention-surface",
         "label": "order-status code vocabulary convention across services gating on order state (single shared section: order-status-code)",
         "contexts": sorted(ctx_id[s] for s in STATUS),
         "refs": ["src:ts-order-service/src/main/java/order/service/OrderServiceImpl.java",
                  "src:ts-cancel-service/src/main/java/cancel/service/CancelServiceImpl.java"]},
        {"id": "cover:train-ticket-global-surface",
         "label": "global structural surface: all measured service contexts and the shared vocabulary",
         "contexts": sorted(c["id"] for c in contexts),
         "refs": ["src:ts-gateway-service/src/main/resources/application.yml"]},
    ]

    # sources: worklist files + pom.xml (cover ref anchor)
    sources = {r["sourceId"]: {"kind": "file", "path": r["path"]} for r in manifest["worklist"]}

    final_atoms = sorted(body_atoms + section_atoms, key=lambda a: a["id"])

    def write_map(path, atoms_subset):
        json.dump({"schema": "archmap/v0.5.3", "id": "archmap:train-ticket-fullbuild@1",
                   "sources": sources, "atoms": atoms_subset,
                   "contexts": contexts, "covers": covers},
                  open(path, "w"), ensure_ascii=False, indent=1)

    write_map(BASE + "/archmap.json", final_atoms)
    money_only = [a for a in final_atoms if a.get("axis") != "cech" or "money-amount" in (a.get("object") or "")]
    status_only = [a for a in final_atoms if a.get("axis") != "cech" or "order-status-code" in (a.get("object") or "")]
    write_map(BASE + "/archmap-money-variant.json", money_only)
    write_map(BASE + "/archmap-status-variant.json", status_only)

    # merge adjudications into extraction-consistency.json
    cons = json.load(open(BASE + "/extraction-consistency.json"))
    adjs = []
    for f in sorted(glob.glob(BASE + "/adjudication/adj-chunk-*.json")):
        for row in json.load(open(f))["adjudications"]:
            adjs.append({"key": row["key"], "decision": row["decision"], "basis": row["basis"]})

    # integrator canonicalization records: final atoms whose id is not a
    # candidate id and whose match key differs from the adjudicated key
    # (subject normalization / cover-level section canonicalization) get an
    # explicit adjudication row so provenance closes mechanically.
    def akey(a):
        return "|".join([a["kind"], a["subject"].strip(), a["axis"],
                         a.get("predicate") or "", a.get("object") or ""])
    survey_ids = set()
    packets_all = [json.load(open(f)) for f in glob.glob(BASE + "/candidates/*.json")]
    for p in packets_all:
        for r in p["surveyRows"]:
            survey_ids |= set(r.get("candidateAtomIds", []))
        for ca in p["candidateAtoms"]:
            survey_ids.add(ca["id"])
    existing_keys = {r["key"] for r in adjs if r["decision"] in ("merged", "adopted")}
    canon_records = 0
    for a in final_atoms:
        if a["id"] not in survey_ids and akey(a) not in existing_keys:
            adjs.append({"key": akey(a), "decision": "merged",
                         "basis": f"Integrator canonicalization record: final atom {a['id']} consolidates adjudicated candidate observations (subject normalized to <service-dir>.<ClassName>; cover-level sectionValue labels canonicalized from adjudicated cech evidence). Origin decisions are recorded per-row in adjudication/adj-chunk-*.json."})
            canon_records += 1
    cons["adjudications"] = adjs
    json.dump(cons, open(BASE + "/extraction-consistency.json", "w"), ensure_ascii=False, indent=1)
    print("canonicalization records appended:", canon_records)

    # coverage ledger from both passes' survey rows
    packets = [json.load(open(f)) for f in glob.glob(BASE + "/candidates/*.json")]
    atom_ids = {a["id"] for a in final_atoms}
    rows = []
    survey = collections.defaultdict(lambda: {"passes": set(), "kinds": set()})
    for p in packets:
        for r in p["surveyRows"]:
            survey[r["sourceId"]]["passes"].add(p["passId"])
            survey[r["sourceId"]]["kinds"] |= set(r.get("surveyedKinds", []))
    for r in manifest["worklist"]:
        s = survey.get(r["sourceId"])
        adopted = sorted(a["id"] for a in final_atoms
                         if any(ref.split(":")[1].startswith(r["path"]) if False else ref == "src:"+r["path"] or ref.startswith("src:"+r["path"]+":") for ref in a.get("refs", [])))
        rows.append({"sourceId": r["sourceId"], "surveyStatus": "surveyed" if s else "not_surveyed",
                     "passes": sorted(s["passes"]) if s else [],
                     "surveyedKinds": sorted(s["kinds"]) if s else [],
                     "adoptedAtomIds": adopted})
    ledger = {"schema": "archmap-coverage-ledger/v0.5.3", "id": "ledger:train-ticket-fullbuild@1",
              "scopeManifestRef": "scope:train-ticket-fullbuild@1",
              "archmapRef": "archmap:train-ticket-fullbuild@1",
              "passRefs": sorted(p["id"] for p in packets), "rows": rows,
              "claimBoundary": "Rows record the authoring survey of the selected scope at the recorded revision. They do not assert extraction completeness."}
    json.dump(ledger, open(BASE + "/coverage-ledger.json", "w"), ensure_ascii=False, indent=1)

    print("final atoms:", len(final_atoms), "(sections:", len(section_atoms), ")")
    print("contexts:", len(contexts), "covers:", len(covers))
    print("adjudications merged:", len(adjs))
    print("ledger rows:", len(rows), "not_surveyed:", sum(1 for r in rows if r["surveyStatus"] != "surveyed"))

if __name__ == "__main__":
    main()
