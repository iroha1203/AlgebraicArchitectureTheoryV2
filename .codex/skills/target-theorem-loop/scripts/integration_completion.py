#!/usr/bin/env python3
"""Explicit single-leaf integration check. Run from the repository root after commit."""
import argparse
import copy
import json
from pathlib import Path
import completion_packet as cp


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", default=".tmp/completion/integration")
    args = parser.parse_args()
    repo = cp.root()
    here = Path(__file__).resolve().parent
    out = repo / cp.relative(repo, args.out)
    receipt = cp.check(repo, cp.relative(repo, here / "fixtures/CompletionFixture.lean"),
                       "CompletionFixture", out / "cache", [])
    receipt_path = out / "receipt.json"
    cp.write(receipt_path, receipt)
    bundle = cp.collect(repo, cp.relative(repo, here / "fixtures/mapping.json"), [receipt_path], out / "bundle.json")
    rows = {row["name"]: row for row in bundle["extraction"]["declarations"]}
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
    cp.validate_bundle(repo, bundle)
    cp.validate_packet(bundle, packet)
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
             "packet_digest": cp.digest(packet), "checks": ["focused", "direct", "private-via", "type-only", "simp",
             "axioms", "fixed-source", "re-extraction", "regeneration", "manual-edit-rejected"], "result": "pass"})
    print(json.dumps({"result": "pass", "declarations": len(rows), "output": cp.relative(repo, out)}, ensure_ascii=False))


if __name__ == "__main__":
    main()
