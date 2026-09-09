#!/usr/bin/env python3
"""Explicit small leaf checks. Run from the repository root after commit."""
import argparse
import copy
import json
import os
from pathlib import Path
import completion_packet as cp


def expected_reference_fixture():
    # Literal AST-derived expectations: no extractor output is copied here.
    edge = lambda name, site, position: {"name": name, "site": site, "position": position}
    return {
        "const": [edge("C", "term", "")],
        "app": [edge("F", "term", "/function"), edge("A", "term", "/argument")],
        "lambda": [edge("T", "type", "/binder"), edge("B", "term", "/body")],
        "forall": [edge("T", "type", "/binder"), edge("B", "term", "/body")],
        "let": [edge("T", "type", "/binder"), edge("Unused", "term", "/value"), edge("B", "term", "/body")],
        "projection": [edge("Record", "projection", "/2"), edge("R", "term", "/structure")],
        "metadata": [edge("M", "term", "")],
        "bvar": [], "fvar": [], "mvar": [], "sort": [], "literal": [],
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", default=".tmp/completion/integration")
    args = parser.parse_args()
    repo = cp.root()
    here = Path(__file__).resolve().parent
    out = repo / cp.relative(repo, args.out)
    raw = cp.run(["lean", "--run", "research/lean/ResearchLean/Tools/CompletionAudit.lean", "--reference-fixture"], repo)
    cp.need(json.loads(raw) == expected_reference_fixture(), "AST reference fixture mismatch")
    receipt = cp.check(repo, cp.relative(repo, here / "fixtures/CompletionFixture.lean"),
                       "CompletionFixture", out / "cache")
    receipt_path = out / "receipt.json"
    cp.write(receipt_path, receipt)
    forged = copy.deepcopy(receipt)
    forged["command"][0] = "true"
    try:
        cp.validate_receipt(repo, forged)
    except cp.Invalid:
        pass
    else:
        raise cp.Invalid("forged focused command accepted")
    forged = copy.deepcopy(receipt)
    forged["dependency_context"]["source_build_claim"] = True
    try:
        cp.validate_receipt(repo, forged)
    except cp.Invalid:
        pass
    else:
        raise cp.Invalid("runtime dependency promoted to source-build evidence")
    # Independent caches sharing a namespace: the earlier cache contains stale B.
    shadow_a = cp.check(repo, cp.relative(repo, here / "fixtures/ShadowA.lean"),
                        "CompletionShadow.A", out / "cache-a")
    shadow_b = cp.check(repo, cp.relative(repo, here / "fixtures/ShadowB.lean"),
                        "CompletionShadow.B", out / "cache-b")
    cp.write(out / "receipt-a.json", shadow_a)
    cp.write(out / "receipt-b.json", shadow_b)
    external = cp.check(repo, cp.relative(repo, here / "fixtures/CompletionExternalFixture.lean"),
                        "CompletionExternalFixture", out / "cache-external")
    cp.need(external["dependency_context"]["policy"] == "manifest-pinned-runtime-trust",
            "external dependency policy missing")
    cp.need(external["dependency_context"]["source_build_claim"] is False,
            "runtime dependencies mislabeled as source-built")
    with cp.extraction_environment(repo, [external]) as env:
        external_rows = json.loads(cp.run(
            ["lean", "--run", "research/lean/ResearchLean/Tools/CompletionAudit.lean",
             "CompletionExternalFixture"], repo, env))
    cp.need(any(row["name"] == "CompletionExternalFixture.manifestPinnedRuntimeCanary"
                for row in external_rows["declarations"]),
            "external-package focused overlay failed")
    (out / "cache-a/CompletionShadow/B.olean").write_bytes(b"stale unrecorded artifact")
    previous_path = os.environ.get("LEAN_PATH")
    os.environ["LEAN_PATH"] = str(out / "cache-a")
    try:
        bundle = cp.collect(repo, cp.relative(repo, here / "fixtures/mapping.json"),
                            [receipt_path, out / "receipt-a.json", out / "receipt-b.json"], out / "bundle.json")
        cp.validate_bundle(repo, bundle)
    finally:
        if previous_path is None:
            os.environ.pop("LEAN_PATH", None)
        else:
            os.environ["LEAN_PATH"] = previous_path
    rows = {row["name"]: row for row in bundle["extraction"]["declarations"]}
    cp.need(rows["CompletionShadow.a"]["owner"] == "CompletionShadow.A" and
            rows["CompletionShadow.b"]["owner"] == "CompletionShadow.B", "multiple cache module resolution failed")
    cp.need(rows["CompletionFixture.positive"]["kind"] == "definition" and
            rows["CompletionFixture.inputCharacterization"]["kind"] == "theorem", "declaration kind mismatch")
    cp.need(rows["CompletionFixture.universeIdentity"]["universe_parameters"] == ["u"], "universe parameters lost")
    cp.need(rows["CompletionFixture.positive"]["type_display"] == "Nat → Prop", "readable type mismatch")
    for row in rows.values():
        cp.need("source_range" in row, "source availability missing")
    terms = lambda name: {r["name"] for r in rows[name]["references"] if r["site"] == "term"}
    # Independent source-derived expectations, not a copy of the extractor traversal.
    cp.need({"CompletionFixture.differenceCriterion", "CompletionFixture.kernelInputCriterion"}
            <= terms("CompletionFixture.inputCharacterization"), "missing acceptance predecessor")
    cp.need(any("helper" in n for n in terms("CompletionFixture.throughHelper")), "private helper lost")
    cp.need(cp.path_between(rows, "CompletionFixture.throughHelper", "CompletionFixture.differenceCriterion") is not None,
            "indirect path lost")
    cp.need("CompletionFixture.positive" not in terms("CompletionFixture.typedOnly"), "type confused with term")
    cp.need("CompletionFixture.differenceCriterion" in terms("CompletionFixture.bySimp"), "simp dependency lost")
    packet = cp.render(bundle, {"notes": "", "refs": []})
    cp.write(out / "packet.json", packet)
    cp.validate_packet(bundle, packet)
    # Removing every type reference passed the old partial checks. It must fail now.
    missing_types = copy.deepcopy(bundle["extraction"])
    for row in missing_types["declarations"]:
        row["references"] = [r for r in row["references"] if r["site"] != "type"]
    try:
        cp.material(bundle["mapping"], missing_types, (repo / bundle["source"]["goal"]["path"]).read_text())
    except cp.Invalid:
        pass
    else:
        raise cp.Invalid("missing type category accepted")
    cp.need(cp.canonical(cp.render(bundle, {"notes": "", "refs": []})) == cp.canonical(packet), "nondeterministic render")
    forged = copy.deepcopy(packet)
    forged["core"]["direction_coverage"].pop()
    try:
        cp.validate_packet(bundle, forged)
    except cp.Invalid:
        pass
    else:
        raise cp.Invalid("manual packet edit accepted")
    cp.write(out / "result.json", {"head": receipt["head"], "declarations": len(rows),
             "packet_digest": cp.digest(packet), "checks": ["focused", "AST-exact-coverage", "upstream-constant-set-coverage", "missing-type-category-rejected", "direct", "private-via", "type-only", "simp",
             "axioms", "fixed-source", "declaration-metadata", "forged-command-rejected", "source-build-overclaim-rejected", "multiple-cache-same-namespace", "focused-owner-overlay", "manifest-pinned-runtime-canary", "re-extraction", "regeneration", "manual-edit-rejected"], "result": "pass"})
    print(json.dumps({"result": "pass", "declarations": len(rows), "output": cp.relative(repo, out)}, ensure_ascii=False))


if __name__ == "__main__":
    main()
