#!/usr/bin/env python3
"""Deterministic completion evidence. Python stdlib only; JSON is the input format.

No network writes and no implicit builds. Semantic findings are reviewer inputs,
never inferred from a dependency edge or a successful command.
"""
from __future__ import annotations

import argparse
from collections import deque
from contextlib import contextmanager
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

VERSION = 3
GATES = (
    "goal_claim_and_artifacts statement_strength all_discharge_required "
    "certificate_provenance proof_use structure_field_escape route_integrity "
    "nonvacuity direction_coverage definition_unfolding dependency_dag "
    "axiom_audit placeholder_scan artifact_sync regression_gate"
).split()
LANES = ["math_a", "math_b", "lean_a", "lean_b"]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PLACEHOLDER = re.compile(r"\b(sorry|admit|unsafe|native_decide)\b|^\s*axiom\b", re.M)


class Invalid(ValueError):
    pass


def need(ok, message):
    if not ok:
        raise Invalid(message)


def fields(value, required, optional=()):
    need(isinstance(value, dict), "expected object")
    need(set(required) <= value.keys() <= set(required) | set(optional),
         f"fields: required={required}; actual={list(value)}")


def canonical(value):
    return json.dumps(value, ensure_ascii=False, sort_keys=True, separators=(",", ":"), allow_nan=False).encode()


def digest(value):
    return hashlib.sha256(canonical(value)).hexdigest()


def file_hash(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def unique_pairs(pairs):
    result = {}
    for k, v in pairs:
        need(k not in result, f"duplicate key: {k}")
        result[k] = v
    return result


def read(path):
    return json.loads(Path(path).read_text(), object_pairs_hook=unique_pairs)


def write(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".new")
    temporary.write_bytes(canonical(value) + b"\n")
    temporary.replace(path)


def run(args, cwd=None, env=None):
    p = subprocess.run(args, cwd=cwd, env=env, capture_output=True)
    need(p.returncode == 0, f"command failed: {args[0]}: {p.stderr.decode(errors='replace')}")
    return p.stdout.decode().strip()


def root():
    return Path(run(["git", "rev-parse", "--show-toplevel"])).resolve()


def relative(repo, path):
    p = Path(path)
    p = (repo / p).resolve() if not p.is_absolute() else p.resolve()
    need(p.is_relative_to(repo), "path must be repository relative")
    return p.relative_to(repo).as_posix()


def blob(repo, head, path):
    path = relative(repo, path)
    expected = run(["git", "rev-parse", f"{head}:{path}"], repo)
    need(run(["git", "hash-object", path], repo) == expected, f"dirty/stale source: {path}")
    return {"path": path, "blob": expected}


def snapshot(repo):
    head = run(["git", "rev-parse", "HEAD"], repo)
    # This inventories source bytes, never elaborates a module list.
    files = run(["git", "ls-tree", "-r", head], repo).splitlines()
    entries = []
    for line in files:
        meta, path = line.split("\t", 1)
        if path.endswith(".lean") or Path(path).name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
            entries.append({"path": path, "blob": meta.split()[2]})
    changed = set(run(["git", "diff", "--name-only", head], repo).splitlines())
    need(not (changed & {e["path"] for e in entries}), "dirty source snapshot")
    return {"head": head, "sources": entries,
            "lean_version": run(["lean", "--version"], repo)}


def dependency_context(repo, source):
    """Bind a focused check to its Lake manifest without certifying runtime imports."""
    source_path = (repo / relative(repo, source)).resolve()
    directory = source_path.parent
    manifest = None
    while directory.is_relative_to(repo):
        candidate = directory / "lake-manifest.json"
        if candidate.is_file():
            manifest = blob(repo, run(["git", "rev-parse", "HEAD"], repo), candidate)
            break
        if directory == repo:
            break
        directory = directory.parent
    need(manifest is not None, "Lake manifest not found for focused source")
    return {"policy": "manifest-pinned-runtime-trust",
            "manifest": manifest,
            "source_build_claim": False}


def validate_receipt(repo, receipt):
    fields(receipt, ["head", "source", "module", "olean", "olean_sha256", "dependency_context", "command", "stdout", "stderr", "exit_code", "lean_version"])
    distinct(receipt["command"], "command arguments", unique=False)
    need(isinstance(receipt["module"], str) and re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*", receipt["module"]), "invalid receipt module")
    need(Path(receipt["source"]["path"]).stem == receipt["module"].rsplit(".", 1)[-1], "module/source mismatch")
    need(receipt["olean"].endswith(receipt["module"].replace(".", "/") + ".olean"), "module/olean mismatch")
    need(receipt["head"] == run(["git", "rev-parse", "HEAD"], repo), "receipt head mismatch")
    need(receipt["lean_version"] == run(["lean", "--version"], repo), "receipt toolchain mismatch")
    need(blob(repo, receipt["head"], receipt["source"]["path"]) == receipt["source"], "receipt source mismatch")
    need(receipt["dependency_context"] == dependency_context(repo, receipt["source"]["path"]), "dependency context mismatch")
    need(file_hash(repo / relative(repo, receipt["olean"])) == receipt["olean_sha256"], "stale olean")
    need(receipt["command"] == ["lean", "-o", receipt["olean"], receipt["source"]["path"]], "focused command mismatch")
    need(receipt["exit_code"] == 0, "failed focused check")
    for stream in ("stdout", "stderr"):
        fields(receipt[stream], ["path", "sha256"])
        need(file_hash(repo / relative(repo, receipt[stream]["path"])) == receipt[stream]["sha256"], "missing/changed command output")


def check(repo, source, module, out):
    """Compile one explicit selected owner against its manifest-pinned Lake environment."""
    need(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*", module), "invalid module")
    source = relative(repo, source)
    need(Path(source).name not in ("ResearchLean.lean", "Formal.lean", "AG.lean"), "aggregate forbidden")
    head = run(["git", "rev-parse", "HEAD"], repo)
    source_ref = blob(repo, head, source)
    out = repo / relative(repo, out)
    out.mkdir(parents=True, exist_ok=True)
    olean = out / (module.replace(".", "/") + ".olean")
    olean.parent.mkdir(parents=True, exist_ok=True)
    command = ["lean", "-o", relative(repo, olean), source]
    result = subprocess.run(command, cwd=repo, capture_output=True)
    streams = {}
    for name, data in (("stdout", result.stdout), ("stderr", result.stderr)):
        path = out / (module + "." + name)
        path.write_bytes(data)
        streams[name] = {"path": relative(repo, path), "sha256": file_hash(path)}
    need(result.returncode == 0, f"focused check failed: {streams}")
    return {"head": head, "source": source_ref, "module": module,
            "olean": relative(repo, olean), "olean_sha256": file_hash(olean),
            "dependency_context": dependency_context(repo, source),
            "command": command, "exit_code": result.returncode,
            "lean_version": run(["lean", "--version"], repo), **streams}


def string(value):
    need(isinstance(value, str) and bool(value.strip()), "empty/non-string value")


def array(values):
    need(isinstance(values, list), "expected array")


def distinct(values, what, allow_empty=False, unique=True):
    array(values)
    need(allow_empty or values, f"empty {what}")
    for value in values:
        string(value)
    need(not unique or len(values) == len(set(values)), f"duplicate {what}")


def validate_map(mapping):
    fields(mapping, ["schema_version", "goal", "goal_path", "report_path", "criteria", "claims", "premises", "evidence"])
    need(mapping["schema_version"] == VERSION, "unsupported schema version")
    for name in ["goal", "goal_path", "report_path"]:
        string(mapping[name])
    distinct(mapping["criteria"], "criteria")
    array(mapping["claims"])
    array(mapping["premises"])
    claim_ids = []
    covered = set()
    for claim in mapping["claims"]:
        fields(claim, ["id", "criterion", "goal_quote", "direction", "declarations", "central", "routes"])
        string(claim["id"])
        claim_ids.append(claim["id"])
        string(claim["goal_quote"])
        need(claim["criterion"] in mapping["criteria"], "unknown criterion")
        covered.add(claim["criterion"])
        need(claim["direction"] in ["forward", "reverse", "iff", "construction", "decision"], "direction enum")
        distinct(claim["declarations"], "exact declaration refs")
        distinct(claim["central"], "central declarations")
        need(set(claim["declarations"]) <= set(claim["central"]), "acceptance must be central")
        seen = set()
        array(claim["routes"])
        for route in claim["routes"]:
            fields(route, ["from", "to", "distance"])
            need(route["distance"] in ("direct", "via", "either"), "distance enum")
            need(route["from"] in claim["central"] and route["to"] in claim["central"], "missing central predecessor")
            pair = (route["from"], route["to"])
            need(pair not in seen, "duplicate route")
            seen.add(pair)
    distinct(claim_ids, "claim IDs")
    need(covered == set(mapping["criteria"]), "missing criterion coverage")
    premises = []
    for p in mapping["premises"]:
        fields(p, ["id", "goal_quote", "role", "declarations", "consumed_by"])
        premises.append(p["id"])
        string(p["goal_quote"])
        need(p["role"] in ("ambient-boundary", "direction-hypothesis", "discharge-required", "conclusion-equivalent-risk"), "premise role")
        distinct(p["declarations"], "premise evidence")
        distinct(p["consumed_by"], "premise consumers", allow_empty=p["role"] != "discharge-required")
        if p["role"] == "discharge-required":
            distinct(p["consumed_by"], "premise consumers")
    if premises:
        distinct(premises, "premise IDs")
    fields(mapping["evidence"], GATES)
    for refs in mapping["evidence"].values():
        distinct(refs, "gate evidence")


def path_between(rows, start, end, direct=False):
    queue = deque([(start, [start])])
    visited = {start}
    while queue:
        node, path = queue.popleft()
        if direct and len(path) > 1:
            continue
        for name in sorted({e["name"] for e in rows.get(node, {}).get("references", []) if e["site"] == "term"}):
            if name == end:
                return path + [name]
            if name not in visited:
                visited.add(name)
                queue.append((name, path + [name]))
    return None


def material(mapping, extraction, goal_text):
    validate_map(mapping)
    fields(extraction, ["schema_version", "modules", "declarations", "terminals"])
    need(extraction["schema_version"] == VERSION, "extractor schema")
    distinct(extraction["modules"], "owner modules")
    array(extraction["declarations"])
    array(extraction["terminals"])
    rows = {}
    for row in extraction["declarations"]:
        fields(row, ["name", "owner", "kind", "universe_parameters", "type_display", "source_range", "type", "value", "axioms", "constant_names", "references"])
        need(row["kind"] in ("definition", "theorem", "axiom", "opaque", "quotient", "inductive", "constructor", "recursor"), "declaration kind")
        distinct(row["universe_parameters"], "universe parameters", allow_empty=True)
        string(row["type_display"])
        if row["source_range"] is not None:
            fields(row["source_range"], ["start_line", "start_column", "end_line", "end_column"])
            need(all(type(v) is int and v >= (1 if k.endswith("line") else 0) for k, v in row["source_range"].items()), "source position")
        need(row["name"] not in rows, "duplicate extracted declaration")
        need(row["owner"] in extraction["modules"], "owner mismatch")
        distinct(row["axioms"], "axioms", allow_empty=True)
        array(row["references"])
        need(set(row["axioms"]) <= ALLOWED_AXIOMS, "axiom audit failed")
        for ref in row["references"]:
            fields(ref, ["name", "site", "position", "origin"])
            need(ref["site"] in ("term", "type", "projection"), "reference site")
            need(ref["origin"] in ("type", "value"), "reference origin")
        fields(row["constant_names"], ["type", "value"])
        for origin in ("type", "value"):
            distinct(row["constant_names"][origin], "constant names", allow_empty=True)
            names = sorted({e["name"] for e in row["references"] if e["origin"] == origin and e["site"] != "projection"})
            need(names == row["constant_names"][origin], "independent constant coverage mismatch")
        rows[row["name"]] = row
    terminals = {r["name"] for r in extraction["terminals"]}
    for row in rows.values():
        need(all(e["name"] in rows or e["name"] in terminals for e in row["references"]), "unresolved extracted reference")
    central = set()
    routes = []
    directions = []

    def declaration(name):
        need(name in rows, f"missing declaration: {name}")
        need(rows[name]["value"] is not None, f"unavailable value: {name}")
        return {"name": name, "owner": rows[name]["owner"], "type": rows[name]["type"],
                "kind": rows[name]["kind"], "universe_parameters": rows[name]["universe_parameters"],
                "type_display": rows[name]["type_display"], "source_range": rows[name]["source_range"],
                "type_digest": digest(rows[name]["type"]), "value_digest": digest(rows[name]["value"])}

    def route(a, b, distance):
        path = path_between(rows, a, b, distance == "direct")
        need(path is not None, f"false central edge / missing route: {a} -> {b}")
        need(distance != "via" or len(path) > 2, "via was direct")
        routes.append({"from": a, "to": b, "distance": "direct" if len(path) == 2 else "via", "path": path})

    for claim in mapping["claims"]:
        need(claim["goal_quote"] in goal_text, "claim GOAL ref does not resolve")
        central.update(claim["central"])
        directions.append({"claim": claim["id"], "direction": claim["direction"],
                           "declarations": [declaration(n) for n in claim["declarations"]]})
        for edge in claim["routes"]:
            route(edge["from"], edge["to"], edge["distance"])
    for p in mapping["premises"]:
        need(p["goal_quote"] in goal_text, "premise GOAL ref does not resolve")
        central.update(p["declarations"])
        central.update(p["consumed_by"])
        if p["role"] == "discharge-required":
            for dep in p["declarations"]:
                for consumer in p["consumed_by"]:
                    need(path_between(rows, consumer, dep), "premise has no value-use route for registered consumer")
                    route(consumer, dep, "either")
    for names in mapping["evidence"].values():
        central.update(names)
    # Every selected node is present; cycles are explicit, not silently discarded.
    for n in central:
        declaration(n)
    adjacency = {n: set() for n in central}
    for a in sorted(central):
        for b in sorted(central - {a}):
            path = path_between(rows, a, b)
            if path and not any(n in central for n in path[1:-1]):
                adjacency[a].add(b)
                edge = {"from": a, "to": b, "distance": "direct" if len(path) == 2 else "via", "path": path}
                if edge not in routes:
                    routes.append(edge)
    def visit(n, active, done):
        need(n not in active, "central cycle requires explicit SCC support; cannot determine")
        if n in done:
            return
        for next_node in adjacency[n]:
            visit(next_node, active | {n}, done)
        done.add(n)
    done = set()
    for n in adjacency:
        visit(n, set(), done)
    return {"criteria": mapping["criteria"], "direction_coverage": directions,
            "dependency_dag": {"semantics": "target-acceptance-spine", "nodes": [declaration(n) for n in sorted(central)],
                               "edges": sorted(routes, key=lambda e: canonical(e))},
            "material_premises": mapping["premises"], "gate_evidence": mapping["evidence"],
            "review_required": GATES}


@contextmanager
def extraction_environment(repo, receipts):
    """Put focused owner artifacts first; runtime imports remain Lake environment inputs."""
    array(receipts)
    need(receipts, "no focused receipts")
    artifacts = {}

    def include(receipt):
        validate_receipt(repo, receipt)
        module = receipt["module"]
        previous = artifacts.get(module)
        need(previous is None or previous[1] == receipt["olean_sha256"], "conflicting module receipts")
        artifacts[module] = (repo / receipt["olean"], receipt["olean_sha256"])

    for receipt in receipts:
        include(receipt)
    with tempfile.TemporaryDirectory(prefix="completion-import-") as directory:
        for module, (source, expected) in artifacts.items():
            destination = Path(directory) / (module.replace(".", "/") + ".olean")
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, destination)
            need(file_hash(destination) == expected, "artifact changed while staging")
        env = dict(os.environ)
        ambient = env.get("LEAN_PATH", "")
        env["LEAN_PATH"] = directory + (os.pathsep + ambient if ambient else "")
        yield env


def collect(repo, mapping_path, receipt_paths, output, base="origin/main"):
    mapping = read(mapping_path)
    validate_map(mapping)
    snap = snapshot(repo)
    head = snap["head"]
    mapping_ref = blob(repo, head, mapping_path)
    goal = blob(repo, head, mapping["goal_path"])
    report = blob(repo, head, mapping["report_path"])
    receipts = [read(p) for p in receipt_paths]
    need(receipts, "no focused receipts")
    for r in receipts:
        validate_receipt(repo, r)
    modules = sorted(r["module"] for r in receipts)
    distinct(modules, "receipt modules")
    for r in receipts:
        need(not PLACEHOLDER.search((repo / r["source"]["path"]).read_text()), "placeholder scan failed")
    extractor = "research/lean/ResearchLean/Tools/CompletionAudit.lean"
    extractor_ref = blob(repo, head, extractor)
    with extraction_environment(repo, receipts) as env:
        result = run(["lean", "--run", extractor, *modules], repo, env)
    extraction = json.loads(result, object_pairs_hook=unique_pairs)
    core = material(mapping, extraction, (repo / goal["path"]).read_text())
    source = {"snapshot": snap, "base_oid": run(["git", "rev-parse", base + "^{commit}"], repo),
              "goal": goal, "report": report, "mapping": mapping_ref,
              "extractor": extractor_ref, "generator_sha256": file_hash(__file__)}
    bundle = {"schema_version": VERSION, "source": source, "mapping": mapping,
              "extraction": extraction, "receipts": receipts, "core": core}
    write(output, bundle)
    return bundle


def validate_bundle(repo, b):
    fields(b, ["schema_version", "source", "mapping", "extraction", "receipts", "core"])
    need(b["schema_version"] == VERSION, "bundle schema")
    fields(b["source"], ["snapshot", "base_oid", "goal", "report", "mapping", "extractor", "generator_sha256"])
    need(run(["git", "rev-parse", b["source"]["base_oid"] + "^{commit}"], repo) == b["source"]["base_oid"], "base ref mismatch")
    need(b["source"]["snapshot"] == snapshot(repo), "source snapshot mismatch")
    need(b["source"]["generator_sha256"] == file_hash(__file__), "generator changed; recollect")
    head = b["source"]["snapshot"]["head"]
    for key in ("goal", "report", "mapping", "extractor"):
        ref = b["source"][key]
        need(blob(repo, head, ref["path"]) == ref, f"{key} ref mismatch")
    need(read(repo / b["source"]["mapping"]["path"]) == b["mapping"], "mapping differs from fixed source")
    for r in b["receipts"]:
        validate_receipt(repo, r)
    need(sorted(r["module"] for r in b["receipts"]) == b["extraction"]["modules"], "extract scope mismatch")
    # Re-extract from the checked artifacts; a consistent edit of bundle/core is not evidence.
    with extraction_environment(repo, b["receipts"]) as env:
        actual = json.loads(run(["lean", "--run", b["source"]["extractor"]["path"], *b["extraction"]["modules"]], repo, env))
    need(actual == b["extraction"], "extraction differs from Lean artifacts")
    core = material(b["mapping"], b["extraction"], (repo / b["source"]["goal"]["path"]).read_text())
    need(core == b["core"], "core was edited")


def render(bundle, auxiliary):
    fields(auxiliary, ["notes", "refs"])
    need(isinstance(auxiliary["notes"], str), "notes type")
    need(isinstance(auxiliary["refs"], list), "aux refs type")
    for ref in auxiliary["refs"]:
        string(ref)
    packet = {"packet_type": "target_theorem_final_review", "schema_version": VERSION,
              "head_oid": bundle["source"]["snapshot"]["head"], "base_oid": bundle["source"]["base_oid"],
              "goal": bundle["mapping"]["goal"],
              "source_digest": digest(bundle["source"]), "claim_map_digest": digest(bundle["mapping"]),
              "core_evidence_digest": digest({"extraction": bundle["extraction"], "core": bundle["core"], "receipts": bundle["receipts"]}),
              "bundle_digest": digest(bundle), "core": bundle["core"], "auxiliary": auxiliary}
    return packet


def validate_packet(bundle, packet):
    need(packet == render(bundle, packet.get("auxiliary", {})), "packet differs from generated result")


def evidence_ref(ref):
    fields(ref, ["path", "sha256"])
    string(ref["path"])
    need(isinstance(ref["sha256"], str) and re.fullmatch(r"[0-9a-f]{64}", ref["sha256"]), "evidence digest")


def resolve_evidence(repo, ref):
    evidence_ref(ref)
    need(file_hash(repo / relative(repo, ref["path"])) == ref["sha256"], "review evidence missing/changed")


def route_findings(old, new, review):
    """Return routing only. An independent recheck is still needed for noncentral findings."""
    fields(review, ["packet_digest", "implementer", "lanes", "lane_evidence", "findings"])
    string(review["implementer"])
    need(review["packet_digest"] == digest(old), "review packet mismatch")
    fields(review["lanes"], LANES)
    fields(review["lane_evidence"], LANES)
    reviewers = []
    array(review["findings"])
    for lane in LANES:
        evidence = review["lane_evidence"][lane]
        fields(evidence, ["reviewer", "ref", "checked_gates", "unchecked_central_claim"])
        string(evidence["reviewer"])
        evidence_ref(evidence["ref"])
        reviewers.append(evidence["reviewer"])
        distinct(evidence["checked_gates"], "checked gates")
        need(set(evidence["checked_gates"]) == set(GATES), "incomplete lane coverage")
        need(evidence["unchecked_central_claim"] == [], "unchecked central claim")
    distinct(reviewers, "independent lane reviewers")
    need(review["implementer"] not in reviewers, "implementer cannot review their own work")
    for lane in review["lanes"].values():
        need(lane in ("pass", "packet-only", "veto", "unchecked-central-claim"), "lane enum")
    ids = []
    central = False
    for f in review["findings"]:
        fields(f, ["id", "class", "gate", "reason", "evidence"])
        string(f["reason"])
        string(f["evidence"])
        ids.append(f["id"])
        need(f["class"] in ("central", "packet-only"), "finding class")
        need(f["gate"] in GATES or f["gate"] == "packet-integrity", "finding gate")
        central |= f["class"] == "central" or f["gate"] != "packet-integrity"
    if ids:
        distinct(ids, "finding IDs")
    same = all(old.get(k) == new.get(k) for k in ("head_oid", "source_digest", "claim_map_digest", "core_evidence_digest"))
    same &= {k: v for k, v in old.items() if k != "auxiliary"} == {k: v for k, v in new.items() if k != "auxiliary"}
    if central or not same or any(v in ("veto", "unchecked-central-claim") for v in review["lanes"].values()):
        return "fresh-four-lane-review"
    if not ids and all(v == "pass" for v in review["lanes"].values()) and old == new:
        return "unchanged-review"
    need(ids, "packet-only verdict/change without a finding")
    return "independent-direct-recheck-required"


def ledger(packet, review, gates, recheck=None, old=None):
    fields(gates, GATES + ["root_recheck", "standard_pr_review", "acceptance_check", "premise_status", "completed_criteria", "stage_evidence"])
    need(all(gates[g] == "pass" for g in GATES + ["root_recheck", "acceptance_check"]), "gate not pass")
    need(gates["standard_pr_review"] == "Mergeable", "standard PR gate")
    distinct(gates["completed_criteria"], "completed criteria")
    need(sorted(gates["completed_criteria"]) == sorted(packet["core"]["criteria"]), "incomplete criteria")
    premises = packet["core"]["material_premises"]
    fields(gates["premise_status"], [p["id"] for p in premises])
    for premise in premises:
        status = gates["premise_status"][premise["id"]]
        need(status == "discharged" if premise["role"] == "discharge-required" else status in ("discharged", "justified-boundary"), "undischarged premise")
    fields(gates["stage_evidence"], ["standard_pr_review", "acceptance_check", "root_recheck"])
    for evidence in gates["stage_evidence"].values():
        fields(evidence, ["head", "ref"])
        need(evidence["head"] == packet["head_oid"], "stage evidence head mismatch")
        evidence_ref(evidence["ref"])
    route = route_findings(old or packet, packet, review)
    need(route != "fresh-four-lane-review", "fresh review required")
    if route == "independent-direct-recheck-required":
        need(recheck is not None and old is not None, "direct recheck missing")
        fields(recheck, ["old_packet_digest", "new_packet_digest", "review_digest", "reviewer", "implementer", "qualified", "resolved", "evidence", "new_findings"])
        need(recheck["old_packet_digest"] == digest(old) and recheck["new_packet_digest"] == digest(packet), "recheck packet mismatch")
        need(recheck["review_digest"] == digest(review), "recheck review mismatch")
        string(recheck["reviewer"])
        string(recheck["implementer"])
        need(recheck["reviewer"] != recheck["implementer"] and recheck["qualified"] is True, "independent qualification missing")
        need(recheck["implementer"] == review["implementer"], "implementer identity changed")
        need(recheck["reviewer"] not in {e["reviewer"] for e in review["lane_evidence"].values()}, "recheck reviewer must be new")
        evidence_ref(recheck["evidence"])
        distinct(recheck["resolved"], "resolved findings")
        need(sorted(recheck["resolved"]) == sorted(f["id"] for f in review["findings"]), "unresolved finding")
        need(recheck["new_findings"] == [], "new finding needs review/recheck")
    else:
        need(review["findings"] == [], "unresolved finding")
    return {"ledger_type": "target_theorem_completion", "schema_version": VERSION,
            "head_oid": packet["head_oid"], "goal": packet["goal"], "packet_digest": digest(packet),
            "review_digest": digest(review), "recheck_digest": digest(recheck) if recheck else None,
            "gates": gates, "review_lanes": {lane: "pass" for lane in LANES},
            "verdict": "target-theorem-proved", "math_lean_review_verdict": "No major findings",
            "completed_proof_obligations": gates["completed_criteria"], "material_premises": gates["premise_status"],
            "remaining_proof_obligations": [], "unchecked_central_claim": [], "blockers": []}


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="command", required=True)
    c = sub.add_parser("check")
    c.add_argument("--source", required=True)
    c.add_argument("--module", required=True)
    c.add_argument("--out", required=True)
    c = sub.add_parser("collect")
    c.add_argument("--mapping", required=True)
    c.add_argument("--receipt", action="append", required=True)
    c.add_argument("--out", required=True)
    c.add_argument("--base", default="origin/main")
    for command in ("render", "validate", "ledger"):
        c = sub.add_parser(command)
        c.add_argument("--bundle", required=True)
        c.add_argument("--packet", required=True)
        if command == "render":
            c.add_argument("--auxiliary")
        if command == "ledger":
            c.add_argument("--review", required=True)
            c.add_argument("--gates", required=True)
            c.add_argument("--old-packet")
            c.add_argument("--recheck")
            c.add_argument("--out", required=True)
    c = sub.add_parser("route")
    for key in ("old", "new", "review"):
        c.add_argument("--" + key, required=True)
    a = p.parse_args()
    repo = root()
    if a.command == "check":
        r = check(repo, a.source, a.module, a.out)
        write(Path(a.out) / (a.module + ".receipt.json"), r)
    elif a.command == "collect":
        collect(repo, a.mapping, a.receipt, a.out, a.base)
    elif a.command == "route":
        print(route_findings(read(a.old), read(a.new), read(a.review)))
    else:
        b = read(a.bundle)
        validate_bundle(repo, b)
        if a.command == "render":
            packet = render(b, read(a.auxiliary) if a.auxiliary else {"notes": "", "refs": []})
            write(a.packet, packet)
            Path(a.packet + ".md").write_text("```json\n" + json.dumps(packet, ensure_ascii=False, indent=2) + "\n```\n")
        else:
            packet = read(a.packet)
            validate_packet(b, packet)
            if a.command == "ledger":
                review, gates = read(a.review), read(a.gates)
                for row in review["lane_evidence"].values():
                    resolve_evidence(repo, row["ref"])
                for row in gates["stage_evidence"].values():
                    resolve_evidence(repo, row["ref"])
                if a.recheck:
                    resolve_evidence(repo, read(a.recheck)["evidence"])
                write(a.out, ledger(packet, review, gates, read(a.recheck) if a.recheck else None,
                                    read(a.old_packet) if a.old_packet else None))
    print("ok")


if __name__ == "__main__":
    try:
        main()
    except (Invalid, OSError, ValueError, KeyError, TypeError) as error:
        print(f"completion audit failed: {error}", file=sys.stderr)
        sys.exit(1)
