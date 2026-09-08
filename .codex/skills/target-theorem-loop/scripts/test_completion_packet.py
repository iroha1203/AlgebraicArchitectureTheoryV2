"""Small deterministic regressions; semantic fixture judgments are reviewed separately."""
import copy
import importlib.util
import json
import hashlib
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("completion_packet", HERE / "completion_packet.py")
cp = importlib.util.module_from_spec(spec)
spec.loader.exec_module(cp)


def mapping():
    n = lambda s: "CompletionFixture." + s
    return {"schema_version": 2, "goal": "completion-fixture", "goal_path": str(HERE / "fixtures/goal.md"),
            "report_path": str(HERE / "fixtures/goal.md"), "criteria": ["classification", "decisions"],
            "claims": [
                {"id": "input", "criterion": "classification", "goal_quote": "入力条件の必要十分性", "direction": "iff",
                 "declarations": [n("inputCharacterization")],
                 "central": [n("inputCharacterization"), n("differenceCriterion"), n("kernelInputCriterion")],
                 "routes": [{"from": n("inputCharacterization"), "to": n(x), "distance": "direct"}
                            for x in ("differenceCriterion", "kernelInputCriterion")]},
                {"id": "decisions", "criterion": "decisions", "goal_quote": "成立例と不成立例", "direction": "decision",
                 "declarations": [n("identityMember"), n("negativeMember")],
                 "central": [n("identityMember"), n("negativeMember")], "routes": []}],
            "premises": [], "evidence": {g: [n("inputCharacterization")] for g in cp.GATES}}


def extraction():
    """Hand-inspected minimal graph; integration uses the actual Lean output."""
    n = lambda s: "CompletionFixture." + s
    rows = []
    for name, deps in [("inputCharacterization", ["differenceCriterion", "kernelInputCriterion"]),
                       ("differenceCriterion", []), ("kernelInputCriterion", []),
                       ("identityMember", []), ("negativeMember", [])]:
        rows.append({"name": n(name), "owner": "CompletionFixture", "type": "type:" + name,
                     "value": "value:" + name, "axioms": [],
                     "constant_names": {"type": [], "value": sorted(n(d) for d in deps)},
                     "references": [{"name": n(d), "site": "term", "position": "/body", "origin": "value"} for d in deps]})
    return {"schema_version": 2, "modules": ["CompletionFixture"], "declarations": rows, "terminals": []}


class PacketTests(unittest.TestCase):
    def setUp(self):
        self.m = mapping()
        self.x = extraction()
        self.goal = "入力条件の必要十分性。成立例と不成立例。"

    def core(self):
        return cp.material(self.m, self.x, self.goal)

    def test_grouped_exact_directions(self):
        core = self.core()
        self.assertEqual(len(core["direction_coverage"][1]["declarations"]), 2)
        self.assertEqual(len(core["dependency_dag"]["edges"]), 2)

    def test_array_containers(self):
        for invalid in ({}, "", None, 0):
            for field in ("claims", "premises"):
                with self.subTest(field=field, invalid=invalid):
                    bad = mapping()
                    bad[field] = invalid
                    with self.assertRaises(cp.Invalid):
                        cp.validate_map(bad)
            bad = mapping()
            bad["claims"][1]["routes"] = invalid
            with self.assertRaises(cp.Invalid):
                cp.validate_map(bad)
            for role in ("ambient-boundary", "direction-hypothesis", "discharge-required", "conclusion-equivalent-risk"):
                bad = mapping()
                bad["premises"] = [{"id": "p", "goal_quote": "入力条件", "role": role,
                                    "declarations": ["CompletionFixture.positive"], "consumed_by": invalid}]
                with self.assertRaises(cp.Invalid):
                    cp.validate_map(bad)
            for field in ("declarations", "terminals"):
                bad = extraction()
                bad[field] = invalid
                with self.assertRaises(cp.Invalid):
                    cp.material(mapping(), bad, self.goal)

    def test_import_tree_recursive_and_conflict(self):
        # Test staging independently of git/Lean qualification, covered by integration.
        with tempfile.TemporaryDirectory() as d:
            repo = Path(d)
            (repo / "a.olean").write_bytes(b"a")
            (repo / "b.olean").write_bytes(b"b")
            a = {"module": "P.A", "olean": "a.olean", "olean_sha256": cp.file_hash(repo / "a.olean"), "dependencies": []}
            b = {"module": "P.B", "olean": "b.olean", "olean_sha256": cp.file_hash(repo / "b.olean"), "dependencies": [a]}
            with patch.object(cp, "validate_receipt"), patch.object(cp, "run", return_value=d):
                with cp.extraction_environment(repo, [b]) as env:
                    tree = Path(env["LEAN_PATH"])
                    self.assertEqual((tree / "P/A.olean").read_bytes(), b"a")
                    self.assertEqual((tree / "P/B.olean").read_bytes(), b"b")
                conflict = {**a, "olean": "b.olean", "olean_sha256": b["olean_sha256"]}
                with self.assertRaisesRegex(cp.Invalid, "conflicting module"):
                    with cp.extraction_environment(repo, [a, conflict]):
                        pass
                (repo / "lib/lean/P").mkdir(parents=True)
                with self.assertRaisesRegex(cp.Invalid, "toolchain namespace"):
                    with cp.extraction_environment(repo, [a]):
                        pass

    def test_false_central_edge(self):
        self.m["claims"][0]["routes"][0]["to"] = "CompletionFixture.identityMember"
        self.m["claims"][0]["central"].append("CompletionFixture.identityMember")
        with self.assertRaisesRegex(cp.Invalid, "false central"):
            self.core()

    def test_missing_central_predecessor(self):
        self.m["claims"][0]["central"].pop()
        with self.assertRaisesRegex(cp.Invalid, "missing central"):
            self.core()

    def test_type_reference_is_not_proof_use(self):
        self.x["declarations"][0]["references"][0]["site"] = "type"
        with self.assertRaisesRegex(cp.Invalid, "false central"):
            self.core()

    def test_missing_direction_criterion(self):
        self.m["claims"].pop()
        with self.assertRaisesRegex(cp.Invalid, "criterion coverage"):
            self.core()

    def test_missing_ref(self):
        self.m["claims"][1]["declarations"] = ["CompletionFixture.absent"]
        self.m["claims"][1]["central"].append("CompletionFixture.absent")
        with self.assertRaisesRegex(cp.Invalid, "missing declaration"):
            self.core()

    def test_enum_type(self):
        self.m["claims"][0]["direction"] = {"iff": True}
        with self.assertRaises(cp.Invalid):
            self.core()

    def test_gate_omission(self):
        del self.m["evidence"]["structure_field_escape"]
        with self.assertRaises(cp.Invalid):
            self.core()

    def test_unavailable_value(self):
        self.x["declarations"][0]["value"] = None
        with self.assertRaisesRegex(cp.Invalid, "unavailable"):
            self.core()

    def test_omitted_reference_rejected_by_independent_set(self):
        self.x["declarations"][0]["references"].pop()
        with self.assertRaisesRegex(cp.Invalid, "constant coverage"):
            self.core()

    def test_extra_reference_rejected_by_independent_set(self):
        self.x["declarations"][0]["references"].append({"name": "invented", "site": "term", "position": "/extra", "origin": "value"})
        with self.assertRaisesRegex(cp.Invalid, "constant coverage"):
            self.core()

    def test_axiom_rejection(self):
        self.x["declarations"][0]["axioms"] = ["unknownAxiom"]
        with self.assertRaisesRegex(cp.Invalid, "axiom"):
            self.core()

    def test_duplicate_json_key(self):
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "input.json"
            p.write_text('{"x":1,"x":2}')
            with self.assertRaisesRegex(cp.Invalid, "duplicate key"):
                cp.read(p)

    def test_g118_source_manifest(self):
        sample = cp.read(HERE / "fixtures/g118-sample.json")
        source = sample["sources"][0]
        self.assertEqual(hashlib.sha256(source["body"].encode()).hexdigest(), source["body_sha256"])
        self.assertIn("generatedQualifiedComparisonRelation_iff_difference_mem", source["body"])
        self.assertIn("mem_generatedPulledComparisonKernel_iff_inputConditions", source["body"])
        self.assertEqual(sample["routing_comparison"][0]["new_additional_full_batches"], 1)
        self.assertEqual(sample["routing_comparison"][1]["new_additional_full_batches"], 0)

    def bundle(self):
        return {"source": {"snapshot": {"head": "a"}, "base_oid": "base"}, "mapping": self.m,
                "extraction": self.x, "core": self.core(), "receipts": []}

    def packet(self):
        return cp.render(self.bundle(), {"notes": "", "refs": []})

    def review(self, old, cls="packet-only", gate="packet-integrity"):
        return {"packet_digest": cp.digest(old), "implementer": "author", "lanes": {l: "packet-only" for l in cp.LANES},
                "lane_evidence": {l: {"reviewer": l, "ref": {"path": "fixture-" + l, "sha256": "0" * 64},
                                      "checked_gates": cp.GATES, "unchecked_central_claim": []} for l in cp.LANES},
                "findings": [{"id": "F1", "class": cls, "gate": gate,
                              "reason": "missing auxiliary reference", "evidence": "fixture comparison"}]}

    def test_determinism_and_manual_edit(self):
        b = self.bundle()
        p = self.packet()
        self.assertEqual(cp.canonical(p), cp.canonical(self.packet()))
        p["core"]["direction_coverage"].pop()
        with self.assertRaises(cp.Invalid):
            cp.validate_packet(b, p)

    def test_packet_only_does_not_restart(self):
        old = self.packet()
        new = copy.deepcopy(old)
        new["auxiliary"]["refs"] = ["fixture evidence"]
        self.assertEqual(cp.route_findings(old, new, self.review(old)), "independent-direct-recheck-required")

    def test_direction_overclaim_review_veto(self):
        self.m = cp.read(HERE / "fixtures/overclaim.json")
        # identityMember only proves positive 0, not the requested universal iff.
        self.core()
        p = self.packet()
        # Semantic finding is an explicit independent reviewer input, not a lint result.
        self.assertEqual(cp.route_findings(p, p, self.review(p, "central", "direction_coverage")), "fresh-four-lane-review")

    def test_changed_core_cannot_copy_digests(self):
        p = self.packet()
        q = copy.deepcopy(p)
        q["core"]["direction_coverage"].pop()
        self.assertEqual(cp.route_findings(p, q, self.review(p)), "fresh-four-lane-review")

    def test_missing_independent_coverage(self):
        p = self.packet()
        r = self.review(p)
        r["lane_evidence"]["lean_a"]["checked_gates"] = ["axiom_audit"]
        with self.assertRaisesRegex(cp.Invalid, "coverage"):
            cp.route_findings(p, p, r)

    def test_reused_reviewer(self):
        p = self.packet()
        r = self.review(p)
        r["lane_evidence"]["lean_a"]["reviewer"] = "math_a"
        with self.assertRaisesRegex(cp.Invalid, "duplicate"):
            cp.route_findings(p, p, r)

    def test_routing_batch_comparison(self):
        p = self.packet()
        q = copy.deepcopy(p)
        q["auxiliary"]["notes"] = "display correction"
        for cls, gate, expected_new in [("central", "dependency_dag", 1),
                                        ("central", "direction_coverage", 1),
                                        ("packet-only", "packet-integrity", 0),
                                        ("packet-only", "all_discharge_required", 1)]:
            route = cp.route_findings(p, q, self.review(p, cls, gate))
            self.assertEqual(int(route == "fresh-four-lane-review"), expected_new)

    def test_cannot_downgrade_central_gate(self):
        p = self.packet()
        self.assertEqual(cp.route_findings(p, p, self.review(p, "packet-only", "proof_use")), "fresh-four-lane-review")

    def test_changed_head_invalidates(self):
        p = self.packet()
        q = copy.deepcopy(p)
        q["head_oid"] = "b"
        self.assertEqual(cp.route_findings(p, q, self.review(p)), "fresh-four-lane-review")

    def test_missing_lane(self):
        p = self.packet()
        r = self.review(p)
        del r["lanes"]["lean_b"]
        with self.assertRaises(cp.Invalid):
            cp.route_findings(p, p, r)

    def test_ledger_requires_independent_recheck(self):
        p = self.packet()
        q = copy.deepcopy(p)
        q["auxiliary"]["notes"] = "corrected"
        r = self.review(p)
        gates = {g: "pass" for g in cp.GATES + ["root_recheck", "acceptance_check"]}
        gates["standard_pr_review"] = "Mergeable"
        gates["completed_criteria"] = self.m["criteria"]
        gates["premise_status"] = {}
        gates["stage_evidence"] = {s: {"head": p["head_oid"], "ref": {"path": "fixture-" + s, "sha256": "0" * 64}}
                                   for s in ("standard_pr_review", "acceptance_check", "root_recheck")}
        with self.assertRaisesRegex(cp.Invalid, "recheck missing"):
            cp.ledger(q, r, gates, old=p)
        check = {"old_packet_digest": cp.digest(p), "new_packet_digest": cp.digest(q), "review_digest": cp.digest(r),
                 "reviewer": "independent-reviewer", "implementer": "author", "qualified": True,
                 "resolved": ["F1"], "evidence": {"path": "fixture-recheck", "sha256": "0" * 64}, "new_findings": []}
        self.assertEqual(cp.ledger(q, r, gates, check, p)["verdict"], "target-theorem-proved")
        for reviewer in cp.LANES:
            check["reviewer"] = reviewer
            with self.assertRaisesRegex(cp.Invalid, "must be new"):
                cp.ledger(q, r, gates, check, p)
        check["reviewer"] = "author"
        with self.assertRaises(cp.Invalid):
            cp.ledger(q, r, gates, check, p)


if __name__ == "__main__":
    unittest.main()
