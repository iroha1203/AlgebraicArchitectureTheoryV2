#!/usr/bin/env python3
"""Explicit small leaf checks. Run from the repository root after commit."""
import argparse
import copy
import json
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
    parser.add_argument("--case", required=True,
                        choices=("reference", "fixture", "external", "shadow-a", "shadow-b", "repo-predecessor"))
    args = parser.parse_args()
    repo = cp.root()
    here = Path(__file__).resolve().parent
    out = repo / cp.relative(repo, args.out)
    if args.case == "reference":
        raw = cp.run(["lean", "--run", "research/lean/ResearchLean/Tools/CompletionAudit.lean",
                      "--reference-fixture"], repo)
        cp.need(json.loads(raw) == expected_reference_fixture(), "AST reference fixture mismatch")
        print(json.dumps({"result": "pass", "case": args.case}))
        return
    if args.case in ("shadow-a", "shadow-b"):
        suffix = "A" if args.case == "shadow-a" else "B"
        receipt = cp.check(repo, cp.relative(repo, here / f"fixtures/Shadow{suffix}.lean"),
                           f"CompletionShadow.{suffix}", out / "cache")
        cp.write(out / "receipt.json", receipt)
        print(json.dumps({"result": "pass", "case": args.case}))
        return
    if args.case == "repo-predecessor":
        receipt = cp.check(repo, "Formal/Util/AssertStandardAxioms.lean",
                           "Formal.Util.AssertStandardAxioms", out / "cache")
        cp.write(out / "receipt.json", receipt)
        print(json.dumps({"result": "pass", "case": args.case}))
        return
    if args.case == "external":
        receipt = cp.check(repo, cp.relative(repo, here / "fixtures/CompletionExternalFixture.lean"),
                           "CompletionExternalFixture", out / "cache")
        cp.write(out / "receipt.json", receipt)
        cp.need(receipt["dependency_context"]["policy"] == "lake-resolved-runtime-trust",
                "external dependency policy missing")
        cp.need(receipt["dependency_context"]["source_build_claim"] is False,
                "runtime dependencies mislabeled as source-built")
        with cp.extraction_environment(repo, [receipt]) as env:
            extracted = json.loads(cp.run(
                ["lean", "--run", "research/lean/ResearchLean/Tools/CompletionAudit.lean",
                 "CompletionExternalFixture"], repo, env))
        terminals = {row["name"] for row in extracted["terminals"]}
        cp.need("AAT.Util.standardAxioms" in terminals, "repo-local terminal missing")
        cp.need("CategoryTheory.Idempotents.Karoubi.idem" in terminals, "external terminal missing")
        cp.need(cp.repo_module_sources(repo, "Formal.Util.AssertStandardAxioms"),
                "repo-local owner classification failed")
        cp.need(not cp.repo_module_sources(repo, "Mathlib.CategoryTheory.Idempotents.Karoubi"),
                "external owner classification failed")
        print(json.dumps({"result": "pass", "case": args.case}))
        return
    cp.need(args.case == "fixture", "unknown integration case")
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
    bundle = cp.collect(repo, cp.relative(repo, here / "fixtures/mapping.json"),
                        [receipt_path], out / "bundle.json")
    cp.validate_bundle(repo, bundle)
    rows = {row["name"]: row for row in bundle["extraction"]["declarations"]}
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
             "axioms", "fixed-source", "declaration-metadata", "forged-command-rejected", "source-build-overclaim-rejected", "focused-owner-overlay", "re-extraction", "regeneration", "manual-edit-rejected"], "result": "pass"})
    print(json.dumps({"result": "pass", "declarations": len(rows), "output": cp.relative(repo, out)}, ensure_ascii=False))


if __name__ == "__main__":
    main()
