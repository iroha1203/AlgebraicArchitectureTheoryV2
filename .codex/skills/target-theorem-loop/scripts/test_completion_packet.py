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
            "fixed_goal": {"commit": "8" * 40, "path": str(HERE / "fixtures/goal.md"), "blob": "4" * 40},
            "report_path": str(HERE / "fixtures/goal.md"),
            "dependency_policy": {
                "schema_version": 1, "method": "focused-owner-plus-pinned-dependency-trust",
                "authorization": {"goal": "completion-fixture",
                                  "decision_ref": "https://github.com/example/project/issues/1#issuecomment-10",
                                  "conflict_issue_ref": "https://github.com/example/project/issues/1",
                                  "tracking_issue_ref": "https://github.com/example/project/issues/2"},
                "selected_owner": "focused-source-receipt-required",
                "repository_local": "runtime-only-material-selected-or-reviewed",
                "external_lake": "manifest-pinned-artifact-trust", "source_build_claim": False},
            "reviewed_predecessors": [], "criteria": ["classification", "decisions"],
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
                     "kind": "theorem", "universe_parameters": [], "type_display": "type:" + name, "source_range": None,
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

    def test_any_reference_path_preserves_every_hop_kind(self):
        rows = {
            "A": {"references": [{"name": "B", "site": "type", "position": "/binder", "origin": "type"}]},
            "B": {"references": [{"name": "C", "site": "projection", "position": "/0", "origin": "value"}]},
            "C": {"references": []},
        }
        found = cp.path_between_any_reference(rows, "A", "C")
        self.assertEqual(found["path"], ["A", "B", "C"])
        self.assertEqual(found["references"], [
            {"from": "A", "to": "B", "site": "type", "position": "/binder", "origin": "type"},
            {"from": "B", "to": "C", "site": "projection", "position": "/0", "origin": "value"},
        ])

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
            repo = Path(d).resolve()
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

    def registry_row(self, module, olean_hash, dependencies=None, url="https://example.test/repo"):
        dependency_set = cp.digest({"artifact_ids": sorted(dependencies or [])})
        return {"artifact_type": "lean-olean", "schema_version": cp.REGISTRY_VERSION, "module": module,
                "repository": {"kind": "baseline", "url": url, "commit": "c" * 40,
                               "manifest": {"path": "lake-manifest.json", "blob": "b" * 40},
                               "manifest_entry": {"type": "path", "name": "fixture", "dir": "."}},
                "source": {"path": module.replace(".", "/") + ".lean", "blob": "a" * 40},
                "olean_sha256": olean_hash, "olean_files": {"olean": olean_hash},
                "lean_version": "Lean fixture", "dependency_set": dependency_set}

    def test_registry_companion_staging_and_tamper(self):
        with tempfile.TemporaryDirectory() as d:
            registry = Path(d)
            objects = registry / "objects"
            objects.mkdir()
            main = hashlib.sha256(b"main").hexdigest()
            private = hashlib.sha256(b"private").hexdigest()
            (objects / main).write_bytes(b"main")
            (objects / private).write_bytes(b"private")
            row = self.registry_row("Pkg.A", main)
            row["olean_files"]["olean.private"] = private
            artifact_id = cp.digest(row)
            index = {"artifacts": {artifact_id: row}}
            with patch.object(cp, "validate_registry", return_value=index), \
                 patch.dict(cp.os.environ, {"LEAN_PATH": "/ambient/must-not-survive"}):
                with cp.registry_environment(Path(d), registry, [artifact_id]) as env:
                    tree = Path(env["LEAN_PATH"])
                    self.assertNotIn("ambient", env["LEAN_PATH"])
                    self.assertEqual((tree / "Pkg/A.olean").read_bytes(), b"main")
                    self.assertEqual((tree / "Pkg/A.olean.private").read_bytes(), b"private")
                (objects / private).write_bytes(b"tampered")
                with self.assertRaisesRegex(cp.Invalid, "changed while staging"):
                    with cp.registry_environment(Path(d), registry, [artifact_id]):
                        pass

    def test_content_addressed_diamond_is_unique(self):
        h = hashlib.sha256(b"artifact").hexdigest()
        leaf = self.registry_row("Pkg.Leaf", h)
        leaf_id = cp.digest(leaf)
        left = self.registry_row("Pkg.Left", h, [leaf_id])
        right = self.registry_row("Pkg.Right", h, [leaf_id])
        left_id, right_id = cp.digest(left), cp.digest(right)
        root = self.registry_row("Pkg.Root", h, [leaf_id, left_id, right_id])
        index = {"artifacts": {leaf_id: leaf, left_id: left, right_id: right, cp.digest(root): root}}
        self.assertEqual(len(index["artifacts"]), 4)
        self.assertEqual(root["dependency_set"], cp.digest({"artifact_ids": sorted({leaf_id, left_id, right_id})}))
        for artifact_id, row in index["artifacts"].items():
            self.assertEqual(cp.digest(row), artifact_id)

    def test_focused_receipt_chain_replaces_baseline(self):
        h = hashlib.sha256(b"artifact").hexdigest()
        rows = {}
        def add(module, tag, deps=()):
            row = self.registry_row(module, hashlib.sha256(tag.encode()).hexdigest(), list(deps))
            artifact_id = cp.digest(row)
            rows[artifact_id] = row
            return artifact_id
        base_a = add("Pkg.A", "base-a")
        focused_a = add("Pkg.A", "focused-a")
        base_b = add("Pkg.B", "base-b", [base_a])
        focused_b = add("Pkg.B", "focused-b", [focused_a])
        empty = {"artifact_ids": []}
        focused_a_set = {"artifact_ids": [focused_a]}
        receipt_a = {"artifact_id": focused_a, "dependency_set": cp.digest(empty)}
        receipt_b = {"artifact_id": focused_b, "dependency_set": cp.digest(focused_a_set)}
        index = {"artifacts": rows, "dependency_sets": {cp.digest(empty): empty,
                                                         cp.digest(focused_a_set): focused_a_set}}
        selected = cp.overlay_artifact_ids(index, [base_a, base_b], [receipt_a, receipt_b])
        self.assertEqual(set(selected), {focused_a, focused_b})

    def test_registry_rejects_root_namespace_collision(self):
        with tempfile.TemporaryDirectory() as d:
            repo, registry = Path(d), Path(d) / "registry"
            objects = registry / "objects"
            objects.mkdir(parents=True)
            h = hashlib.sha256(b"same").hexdigest()
            (objects / h).write_bytes(b"same")
            a = self.registry_row("Pkg.A", h, url="https://example.test/a")
            b = self.registry_row("Pkg.B", h, url="https://example.test/b")
            aid, bid = cp.digest(a), cp.digest(b)
            empty = {"artifact_ids": []}
            cp.write(registry / "index.json", {"registry_type": "completion-artifact-registry", "schema_version": cp.REGISTRY_VERSION,
                     "lean_version": "Lean fixture", "manifest": a["repository"]["manifest"],
                     "indexer": {"path": "CompletionRegistry.lean", "blob": "d" * 40},
                     "artifacts": {aid: a, bid: b}, "dependency_sets": {cp.digest(empty): empty}, "roots": {}})
            def fake_run(args, cwd=None, env=None):
                if args[:2] == ["lean", "--version"]: return "Lean fixture"
                if args[:2] == ["lean", "--print-prefix"]: return str(repo / "sysroot")
                if args[:3] == ["git", "rev-parse", "HEAD"]: return "c" * 40
                raise AssertionError(args)
            def fake_blob(owner, head, path):
                if path == "lake-manifest.json": return a["repository"]["manifest"]
                if path == "CompletionRegistry.lean": return {"path": path, "blob": "d" * 40}
                return {"path": path, "blob": "a" * 40}
            with patch.object(cp, "run", side_effect=fake_run), \
                 patch.object(cp, "blob", side_effect=fake_blob), \
                 patch.object(cp, "validate_repository", return_value=(repo, repo)), \
                 patch.object(cp, "source_for_module", side_effect=lambda owner, package, module, commit:
                              a["source"] if module == "Pkg.A" else b["source"]):
                with self.assertRaisesRegex(cp.Invalid, "root namespace collision"):
                    cp.validate_registry(repo, registry, [aid, bid])

    def test_registry_rejects_search_order_collision(self):
        with tempfile.TemporaryDirectory() as d:
            a, b = Path(d) / "a.olean", Path(d) / "b.olean"
            a.write_bytes(b"a")
            b.write_bytes(b"b")
            with self.assertRaisesRegex(cp.Invalid, "search order"):
                cp.select_artifact([(Path(d), a), (Path(d), b)], "Pkg.A")
            b.write_bytes(b"a")
            with self.assertRaisesRegex(cp.Invalid, "multiple artifact candidates"):
                cp.select_artifact([(Path(d), a), (Path(d), b)], "Pkg.A")

    def test_registry_rejects_manifest_commit_mismatch(self):
        entry = {"type": "git", "name": "pkg", "rev": "a" * 40, "url": "https://example.test/pkg"}
        with patch.object(cp, "run", return_value="b" * 40):
            with self.assertRaisesRegex(cp.Invalid, "manifest commit mismatch"):
                cp.repo_identity(Path("/tmp/pkg"), Path("/tmp/repo"),
                                 {"path": "lake-manifest.json", "blob": "c" * 40}, entry)

    def test_registry_rejects_missing_object(self):
        with tempfile.TemporaryDirectory() as d:
            registry = Path(d)
            h = hashlib.sha256(b"missing").hexdigest()
            row = self.registry_row("Pkg.A", h)
            artifact_id = cp.digest(row)
            with patch.object(cp, "validate_registry", return_value={"artifacts": {artifact_id: row}}):
                with self.assertRaises(OSError):
                    with cp.registry_environment(Path(d), registry, [artifact_id]):
                        pass

    def test_manifest_resolves_external_sibling_package(self):
        with tempfile.TemporaryDirectory() as d:
            base = Path(d)
            repo, project = base / "repo", base / "repo/project"
            package = base / "packages/pkg"
            project.mkdir(parents=True)
            package.mkdir(parents=True)
            manifest = project / "lake-manifest.json"
            entry = {"type": "git", "name": "pkg", "rev": "a" * 40,
                     "url": "https://example.test/pkg"}
            data = {"version": "1", "packagesDir": "../../packages", "packages": [entry],
                    "name": "project", "lakeDir": ".lake"}
            resolved_package = package.resolve()
            def fake_run(args, cwd=None, env=None):
                if args[:3] == ["git", "rev-parse", "--show-toplevel"]:
                    return str(resolved_package if Path(cwd).resolve().is_relative_to(resolved_package) else repo.resolve())
                raise AssertionError(args)
            with patch.object(cp, "run", side_effect=fake_run):
                owners = cp.package_owners(repo, manifest, data)
            self.assertTrue(any(owner == resolved_package and row == entry for owner, _, row in owners))

    def test_manifest_adds_explicit_root_baseline_identity(self):
        with tempfile.TemporaryDirectory() as d:
            repo = Path(d).resolve()
            manifest = repo / "lake-manifest.json"
            manifest.write_text("{}")
            data = {"version": "1", "packagesDir": ".lake/packages", "packages": [],
                    "name": "root-fixture", "lakeDir": ".lake"}
            with patch.object(cp, "run", return_value=str(repo)):
                owners = cp.package_owners(repo, manifest, data)
            self.assertEqual(owners, [(repo, repo, {"type": "root", "name": "root-fixture", "dir": "."})])
            row = self.registry_row("Pkg.A", "f" * 64)
            row["repository"]["manifest_entry"] = owners[0][2]
            cp.validate_artifact_metadata(row)

    def test_nested_manifest_root_is_distinct_from_same_repository_path_dependency(self):
        with tempfile.TemporaryDirectory() as d:
            repo = Path(d).resolve()
            project = repo / "research/lean"
            project.mkdir(parents=True)
            manifest = project / "lake-manifest.json"
            path_entry = {"type": "path", "name": "baseline", "dir": "../.."}
            data = {"version": "1", "packagesDir": "../../.lake/packages",
                    "packages": [path_entry], "name": "researchLean", "lakeDir": ".lake"}
            with patch.object(cp, "run", return_value=str(repo)):
                owners = cp.package_owners(repo, manifest, data)
            self.assertIn((repo, repo, path_entry), owners)
            self.assertIn((repo, project, {"type": "root", "name": "researchLean", "dir": "."}), owners)

    def test_registry_rejects_repository_url_mismatch(self):
        entry = {"type": "git", "name": "pkg", "rev": "a" * 40,
                 "url": "https://example.test/pkg"}
        def fake_run(args, cwd=None, env=None):
            if args[:3] == ["git", "rev-parse", "HEAD"]: return "a" * 40
            if args[:3] == ["git", "remote", "get-url"]: return "https://attacker.test/pkg"
            raise AssertionError(args)
        with patch.object(cp, "run", side_effect=fake_run):
            with self.assertRaisesRegex(cp.Invalid, "repository identity mismatch"):
                cp.repo_identity(Path("/tmp/pkg"), Path("/tmp/repo"),
                                 {"path": "lake-manifest.json", "blob": "c" * 40}, entry)

    def test_validator_rejects_external_path_package_as_baseline(self):
        repo = Path("/tmp/baseline").resolve()
        external = Path("/tmp/external-path-package").resolve()
        entry = {"type": "path", "name": "external", "dir": "../external-path-package"}
        identity = {"kind": "baseline", "url": "https://github.com/example/project",
                    "commit": "a" * 40,
                    "manifest": {"path": "lake-manifest.json", "blob": "b" * 40},
                    "manifest_entry": entry}
        manifest = {"name": "baseline", "packages": [entry]}
        with patch.object(cp, "blob", return_value=identity["manifest"]), \
             patch.object(cp, "read", return_value=manifest), \
             patch.object(cp, "package_owners", return_value=[(external, external, entry)]), \
             patch.object(cp, "run", return_value="a" * 40):
            with self.assertRaisesRegex(cp.Invalid, "must belong to baseline"):
                cp.validate_repository(repo, identity)

    def test_repository_url_must_be_public_and_credential_free(self):
        for value in (
            "https://token@github.com/example/repo",
            "file:///example/repo",
            "/example/repo",
            "../private/repo",
            "https://github.com/example/repo?token=secret",
            "https://localhost/example/repo",
            "https://127.0.0.1/example/repo",
            "https://127.1/example/repo",
            "https://10.1/example/repo",
            "https://0x7f.0.0.1/example/repo",
            "https://224.0.0.1/example/repo",
            "https://239.255.255.255/example/repo",
            "https://internal/example/repo",
            "ssh://git@buildhost/example/repo",
            "https://cache.corp/example/repo",
        ):
            with self.subTest(value=value), self.assertRaisesRegex(cp.Invalid, "public"):
                cp.public_repository_url(value)
        for value in (
            "https://github.com/example/repo.git",
            "git://github.com/example/repo",
            "git@github.com:example/repo.git",
            "ssh://git@github.com/example/repo.git",
        ):
            self.assertEqual(cp.public_repository_url(value), value)

    def test_registry_rejects_lean_version_mismatch(self):
        with tempfile.TemporaryDirectory() as d:
            registry = Path(d)
            cp.write(registry / "index.json", {"registry_type": "completion-artifact-registry", "schema_version": cp.REGISTRY_VERSION,
                     "lean_version": "Lean old", "manifest": {"path": "lake-manifest.json", "blob": "b" * 40},
                     "indexer": {"path": "CompletionRegistry.lean", "blob": "d" * 40},
                     "artifacts": {}, "dependency_sets": {}, "roots": {}})
            with patch.object(cp, "run", return_value="Lean current"):
                with self.assertRaisesRegex(cp.Invalid, "Lean version mismatch"):
                    cp.validate_registry(Path(d), registry, [])

    def test_registry_rejects_per_artifact_lean_version_mismatch(self):
        with tempfile.TemporaryDirectory() as d:
            repo, registry = Path(d), Path(d) / "registry"
            objects = registry / "objects"
            objects.mkdir(parents=True)
            h = hashlib.sha256(b"main").hexdigest()
            (objects / h).write_bytes(b"main")
            row = self.registry_row("Pkg.A", h)
            row["lean_version"] = "Lean forged-old"
            artifact_id = cp.digest(row)
            empty = {"artifact_ids": []}
            cp.write(registry / "index.json", {
                "registry_type": "completion-artifact-registry",
                "schema_version": cp.REGISTRY_VERSION,
                "lean_version": "Lean current",
                "manifest": row["repository"]["manifest"],
                "indexer": {"path": "CompletionRegistry.lean", "blob": "d" * 40},
                "artifacts": {artifact_id: row},
                "dependency_sets": {cp.digest(empty): empty},
                "roots": {},
            })
            def fake_run(args, cwd=None, env=None):
                if args[:2] == ["lean", "--version"]: return "Lean current"
                if args[:2] == ["lean", "--print-prefix"]: return str(repo / "sysroot")
                if args[:3] == ["git", "rev-parse", "HEAD"]: return "c" * 40
                raise AssertionError(args)
            def fake_blob(owner, head, path):
                if path == "CompletionRegistry.lean": return {"path": path, "blob": "d" * 40}
                return row["repository"]["manifest"]
            with patch.object(cp, "run", side_effect=fake_run), \
                 patch.object(cp, "blob", side_effect=fake_blob):
                with self.assertRaisesRegex(cp.Invalid, "artifact Lean version mismatch"):
                    cp.validate_registry(repo, registry, [artifact_id])

    def test_source_module_is_derived_from_lake_package_path(self):
        with tempfile.TemporaryDirectory() as d:
            repo = Path(d).resolve()
            source = repo / "project/Pkg/Owner.lean"
            source.parent.mkdir(parents=True)
            source.write_text("def x := 1\n")
            (repo / "project/lake-manifest.json").write_text(json.dumps({
                "version": "1", "packagesDir": ".lake/packages", "packages": [],
                "name": "fixture", "lakeDir": ".lake",
            }))
            self.assertEqual(cp.source_module_name(repo, source), "Pkg.Owner")

    def test_registry_root_is_content_addressed(self):
        with tempfile.TemporaryDirectory() as d:
            repo, registry = Path(d), Path(d) / "registry"
            registry.mkdir()
            empty = {"artifact_ids": []}
            manifest = {"path": "lake-manifest.json", "blob": "b" * 40}
            root = {"root_id": "0" * 64, "module": "Pkg.Owner",
                    "source": {"path": "Pkg/Owner.lean", "blob": "a" * 40},
                    "direct_modules": [], "dependency_set": cp.digest(empty)}
            cp.write(registry / "index.json", {
                "registry_type": "completion-artifact-registry",
                "schema_version": cp.REGISTRY_VERSION,
                "lean_version": "Lean fixture", "manifest": manifest,
                "indexer": {"path": "CompletionRegistry.lean", "blob": "d" * 40},
                "artifacts": {}, "dependency_sets": {cp.digest(empty): empty},
                "roots": {"Pkg.Owner": root},
            })
            def fake_run(args, cwd=None, env=None):
                if args[:2] == ["lean", "--version"]: return "Lean fixture"
                if args[:3] == ["git", "rev-parse", "HEAD"]: return "c" * 40
                raise AssertionError(args)
            def fake_blob(owner, head, path):
                if path == "CompletionRegistry.lean": return {"path": path, "blob": "d" * 40}
                return manifest
            with patch.object(cp, "run", side_effect=fake_run), \
                 patch.object(cp, "blob", side_effect=fake_blob), \
                 patch.object(cp, "source_module_name", return_value="Pkg.Owner"):
                with self.assertRaisesRegex(cp.Invalid, "content-addressed registry root mismatch"):
                    cp.validate_registry(repo, registry, [])

    def test_focused_command_binds_source_module_and_output(self):
        with tempfile.TemporaryDirectory() as d:
            repo = Path(d)
            output = repo / "cache/Pkg/Owner.olean"
            output.parent.mkdir(parents=True)
            output.write_bytes(b"focused")
            h = cp.file_hash(output)
            metadata = self.registry_row("Pkg.Owner", h)
            receipt = {"module": "Pkg.Owner",
                       "command": ["lean", "-o", "cache/Pkg/Owner.olean", "Pkg/Owner.lean"]}
            cp.validate_focused_command(repo, receipt, metadata)
            bad = copy.deepcopy(receipt)
            bad["command"] = ["definitely-not-lean"]
            with self.assertRaisesRegex(cp.Invalid, "command shape"):
                cp.validate_focused_command(repo, bad, metadata)
            bad = copy.deepcopy(receipt)
            bad["command"][3] = "Pkg/Other.lean"
            with self.assertRaisesRegex(cp.Invalid, "source mismatch"):
                cp.validate_focused_command(repo, bad, metadata)
            output.write_bytes(b"tampered")
            with self.assertRaisesRegex(cp.Invalid, "output missing/changed"):
                cp.validate_focused_command(repo, receipt, metadata)

    def test_registry_rejects_source_blob_and_path_escape(self):
        with tempfile.TemporaryDirectory() as d:
            repo, registry = Path(d), Path(d) / "registry"
            objects = registry / "objects"
            objects.mkdir(parents=True)
            h = hashlib.sha256(b"main").hexdigest()
            (objects / h).write_bytes(b"main")
            row = self.registry_row("Pkg.A", h)
            artifact_id = cp.digest(row)
            empty = {"artifact_ids": []}
            cp.write(registry / "index.json", {"registry_type": "completion-artifact-registry", "schema_version": cp.REGISTRY_VERSION,
                     "lean_version": "Lean fixture", "manifest": row["repository"]["manifest"],
                     "indexer": {"path": "CompletionRegistry.lean", "blob": "d" * 40},
                     "artifacts": {artifact_id: row}, "dependency_sets": {cp.digest(empty): empty}, "roots": {}})
            def fake_run(args, cwd=None, env=None):
                if args[:2] == ["lean", "--version"]: return "Lean fixture"
                if args[:2] == ["lean", "--print-prefix"]: return str(repo / "sysroot")
                if args[:3] == ["git", "rev-parse", "HEAD"]: return "c" * 40
                raise AssertionError(args)
            def fake_blob(owner, head, path):
                if path == "lake-manifest.json": return row["repository"]["manifest"]
                if path == "CompletionRegistry.lean": return {"path": path, "blob": "d" * 40}
                return {"path": path, "blob": "f" * 40}
            with patch.object(cp, "run", side_effect=fake_run), patch.object(cp, "blob", side_effect=fake_blob), \
                 patch.object(cp, "validate_repository", return_value=(repo, repo)), \
                 patch.object(cp, "source_for_module", return_value={"path": row["source"]["path"], "blob": "f" * 40}):
                with self.assertRaisesRegex(cp.Invalid, "module/source mismatch"):
                    cp.validate_registry(repo, registry, [artifact_id])
            with self.assertRaisesRegex(cp.Invalid, "repository relative"):
                cp.relative(repo, "../escape")

    def test_registry_evidence_is_self_describing_and_deduplicated(self):
        h = hashlib.sha256(b"main").hexdigest()
        empty = {"artifact_ids": []}
        direct = self.registry_row("Pkg.Direct", h)
        direct["repository"]["kind"] = "lake-git"
        direct["repository"]["manifest_entry"] = {
            "type": "git", "name": "external", "rev": "c" * 40,
            "url": "https://example.test/repo"}
        direct_id = cp.digest(direct)
        runtime = self.registry_row("Pkg.Runtime", h)
        runtime_id = cp.digest(runtime)
        deps = {"artifact_ids": sorted([direct_id, runtime_id])}
        owner = self.registry_row("Pkg.Owner", h, deps["artifact_ids"])
        owner_id = cp.digest(owner)
        root = {"module": "Pkg.Owner", "source": owner["source"],
                "direct_modules": ["Pkg.Direct", "Pkg.Runtime"], "dependency_set": cp.digest(deps)}
        root["root_id"] = cp.digest(root)
        index = {"lean_version": "Lean fixture", "manifest": owner["repository"]["manifest"],
                 "indexer": {"path": "CompletionRegistry.lean", "blob": "d" * 40},
                 "artifacts": {direct_id: direct, runtime_id: runtime, owner_id: owner},
                 "dependency_sets": {cp.digest(empty): empty, cp.digest(deps): deps},
                 "roots": {"Pkg.Owner": root}}
        receipt = {"module": "Pkg.Owner", "root_id": root["root_id"],
                   "artifact_id": owner_id, "dependency_set": cp.digest(deps)}
        evidence = cp.registry_evidence(index, [direct_id, runtime_id, owner_id], [receipt], mapping()["dependency_policy"])
        self.assertEqual(evidence["artifact_count"], 3)
        self.assertEqual(len(evidence["repositories"]), 2)
        self.assertEqual(evidence["selected_owner_artifacts"][0]["metadata"]["source"], owner["source"])
        self.assertEqual(evidence["direct_dependency_artifacts"][0]["metadata"]["olean_files"], direct["olean_files"])
        self.assertEqual(evidence["artifact_classes"]["focused_owner"]["artifact_count"], 1)
        self.assertEqual(evidence["artifact_classes"]["repository_runtime"]["artifact_count"], 1)
        self.assertEqual(evidence["artifact_classes"]["manifest_pinned_external"]["artifact_count"], 1)
        self.assertEqual(sum(row["artifact_count"] for row in evidence["artifact_classes"].values()), 3)
        self.assertFalse(evidence["dependency_policy"]["source_build_claim"])

    def test_dependency_policy_is_closed_and_fail_closed(self):
        bad = mapping()
        bad["dependency_policy"]["source_build_claim"] = True
        with self.assertRaisesRegex(cp.Invalid, "must not claim source build"):
            cp.validate_map(bad)
        bad = mapping()
        bad["dependency_policy"]["authorization"]["decision_ref"] = "local decision"
        with self.assertRaisesRegex(cp.Invalid, "authorization ref"):
            cp.validate_map(bad)
        bad = mapping()
        bad["dependency_policy"]["repository_local"] = "trusted"
        with self.assertRaisesRegex(cp.Invalid, "repository-local policy"):
            cp.validate_map(bad)
        bad = mapping()
        bad["dependency_policy"]["authorization"]["decision_ref"] = \
            "https://github.com/example/project/issues/2#issuecomment-10"
        with self.assertRaisesRegex(cp.Invalid, "decision must be recorded"):
            cp.validate_map(bad)
        bad = mapping()
        bad["dependency_policy"]["authorization"]["goal"] = "another-goal"
        with self.assertRaisesRegex(cp.Invalid, "GOAL linkage"):
            cp.validate_map(bad)

    def test_repository_kind_must_match_manifest_entry(self):
        row = self.registry_row("Pkg.A", "f" * 64)
        row["repository"]["kind"] = "lake-git"
        with self.assertRaisesRegex(cp.Invalid, "kind/manifest entry mismatch"):
            cp.validate_artifact_metadata(row)

    def test_authorization_must_match_baseline_repository(self):
        with patch.object(cp, "run", return_value="git@github.com:iroha1203/AlgebraicArchitectureTheoryV2.git"):
            with self.assertRaisesRegex(cp.Invalid, "differs from baseline"):
                cp.validate_mapping_repository(Path("."), mapping())
        local = mapping()
        for key in ("decision_ref", "conflict_issue_ref", "tracking_issue_ref"):
            local["dependency_policy"]["authorization"][key] = \
                local["dependency_policy"]["authorization"][key].replace("example/project", "iroha1203/AlgebraicArchitectureTheoryV2")
        with patch.object(cp, "run", return_value="git@github.com:iroha1203/AlgebraicArchitectureTheoryV2.git"):
            cp.validate_mapping_repository(Path("."), local)

    def test_mapping_binds_fixed_goal_id_and_tracking_issue(self):
        with tempfile.TemporaryDirectory() as d:
            repo = Path(d).resolve()
            goal = repo / "goal.md"
            goal.write_text("# fixture\n\n- `id`: `completion-fixture`\n- `tracking issue`: [#2](https://github.com/example/project/issues/2)\n")
            m = mapping()
            m["goal_path"] = "goal.md"
            m["fixed_goal"] = {"commit": "8" * 40, "path": "goal.md", "blob": "4" * 40}
            def fixed_goal_git(args, cwd=None, env=None):
                if args[:2] == ["git", "rev-parse"] and args[2].endswith("^{commit}"):
                    return "8" * 40
                if args[:2] == ["git", "rev-parse"]:
                    return "4" * 40
                if args[:2] == ["git", "hash-object"]:
                    return "4" * 40
                raise AssertionError(args)
            with patch.object(cp, "run", side_effect=fixed_goal_git):
                cp.validate_goal_binding(repo, m)
            m["goal"] = "other"
            m["dependency_policy"]["authorization"]["goal"] = "other"
            with patch.object(cp, "run", side_effect=fixed_goal_git), \
                 self.assertRaisesRegex(cp.Invalid, "fixed GOAL card"):
                cp.validate_goal_binding(repo, m)

    def test_repository_local_value_terminal_requires_reviewed_predecessor(self):
        x = extraction()
        terminal = copy.deepcopy(x["declarations"][0])
        terminal.update({"name": "RepoLocal.UnreviewedLemma", "owner": "RepoLocal.Unreviewed",
                         "type": "Prop", "type_display": "Prop", "value": "proof-value",
                         "axioms": []})
        x["terminals"].append(terminal)
        row = next(row for row in x["declarations"] if row["name"] == "CompletionFixture.negativeMember")
        row["references"].append({"name": terminal["name"], "site": "term", "position": "/body",
                                  "origin": "value"})
        row["constant_names"]["value"].append(terminal["name"])
        row["constant_names"]["value"].sort()
        context = {terminal["owner"]: {"artifact_id": "f" * 64,
                                        "source": {"path": "RepoLocal/Unreviewed.lean", "blob": "e" * 40},
                                        "repository_commit": "c" * 40}}
        with self.assertRaisesRegex(cp.Invalid, "terminal predecessor coverage"):
            cp.material(mapping(), x, self.goal, context)
        m = mapping()
        m["reviewed_predecessors"] = [{"declaration": terminal["name"], "owner": terminal["owner"],
                                        "declaration_digest": cp.digest(terminal),
                                        "reviewed_head": "d" * 40, "source_blob": "e" * 40,
                                        "artifact_id": "f" * 64,
                                        "review_ref": "https://github.com/example/project/pull/3#issuecomment-30"}]
        same_reviewed_source = lambda head, path: {"path": path, "blob": "e" * 40}
        core = cp.material(m, x, self.goal, context, same_reviewed_source)
        predecessor = core["reviewed_predecessors"][0]
        self.assertEqual(predecessor["artifact_id"], "f" * 64)
        self.assertEqual(predecessor["reviewed_head"], "d" * 40)
        self.assertEqual(predecessor["artifact_repository_commit"], "c" * 40)
        edge = next(edge for edge in core["dependency_dag"]["edges"] if edge["to"] == terminal["name"])
        self.assertEqual(edge["dependency_kind"], "typed-reference-path")
        self.assertEqual(edge["reference_path"][-1]["site"], "term")
        self.assertEqual(edge["reference_path"][-1]["origin"], "value")
        changed = copy.deepcopy(x)
        changed["terminals"][0]["value"] = "changed-proof-value"
        with self.assertRaisesRegex(cp.Invalid, "predecessor declaration mismatch"):
            cp.material(m, changed, self.goal, context, same_reviewed_source)
        with self.assertRaisesRegex(cp.Invalid, "reviewed source mismatch"):
            cp.material(m, x, self.goal, context,
                        lambda head, path: {"path": path, "blob": "0" * 40})

    def test_repository_local_predecessor_closure_is_transitive(self):
        x = extraction()
        first = copy.deepcopy(x["declarations"][0])
        second = copy.deepcopy(x["declarations"][0])
        first.update({"name": "RepoLocal.First", "owner": "RepoLocal.A", "value": "first"})
        second.update({"name": "RepoLocal.Second", "owner": "RepoLocal.B", "value": "second",
                       "references": [], "constant_names": {"type": [], "value": []}})
        first["references"] = [{"name": second["name"], "site": "term", "position": "/body",
                               "origin": "value"}]
        first["constant_names"] = {"type": [], "value": [second["name"]]}
        x["terminals"].extend([first, second])
        x["declarations"][0]["references"].append(
            {"name": first["name"], "site": "term", "position": "/body", "origin": "value"})
        x["declarations"][0]["constant_names"]["value"].append(first["name"])
        x["declarations"][0]["constant_names"]["value"].sort()
        context = {
            first["owner"]: {"artifact_id": "a" * 64,
                              "source": {"path": "RepoLocal/A.lean", "blob": "1" * 40},
                              "repository_commit": "3" * 40},
            second["owner"]: {"artifact_id": "b" * 64,
                               "source": {"path": "RepoLocal/B.lean", "blob": "2" * 40},
                               "repository_commit": "4" * 40}}
        m = mapping()
        m["reviewed_predecessors"] = [{"declaration": first["name"], "owner": first["owner"],
                                        "declaration_digest": cp.digest(first),
                                        "reviewed_head": "5" * 40, "source_blob": "1" * 40,
                                        "artifact_id": "a" * 64,
                                        "review_ref": "https://github.com/example/project/pull/3#issuecomment-30"}]
        with self.assertRaisesRegex(cp.Invalid, "terminal predecessor coverage"):
            cp.material(m, x, self.goal, context,
                        lambda head, path: {"path": path, "blob": "1" * 40})

    def test_repository_local_projection_terminal_cannot_escape_review(self):
        x = extraction()
        terminal = copy.deepcopy(x["declarations"][0])
        terminal.update({"name": "RepoLocal.Projected", "owner": "RepoLocal.Projection",
                         "type": "Sort 1", "type_display": "Type", "value": None, "axioms": []})
        x["terminals"].append(terminal)
        x["declarations"][0]["references"].append(
            {"name": terminal["name"], "site": "projection", "position": "/0", "origin": "value"})
        context = {terminal["owner"]: {"artifact_id": "a" * 64,
                                        "source": {"path": "RepoLocal/Projection.lean", "blob": "b" * 40},
                                        "repository_commit": "c" * 40}}
        with self.assertRaisesRegex(cp.Invalid, "terminal predecessor coverage"):
            cp.material(mapping(), x, self.goal, context)

    def test_repository_local_type_terminal_cannot_escape_review(self):
        x = extraction()
        terminal = copy.deepcopy(x["declarations"][0])
        terminal.update({"name": "RepoLocal.UnreviewedPredicate", "owner": "RepoLocal.Interface",
                         "type": "Sort 1", "type_display": "Type", "value": None, "axioms": []})
        x["terminals"].append(terminal)
        row = x["declarations"][0]
        row["references"].append({"name": terminal["name"], "site": "type", "position": "/binder",
                                  "origin": "type"})
        row["constant_names"]["type"].append(terminal["name"])
        row["constant_names"]["type"].sort()
        context = {terminal["owner"]: {"artifact_id": "a" * 64,
                                        "source": {"path": "RepoLocal/Interface.lean", "blob": "b" * 40},
                                        "repository_commit": "c" * 40}}
        with self.assertRaisesRegex(cp.Invalid, "terminal predecessor coverage"):
            cp.material(mapping(), x, self.goal, context)

    def test_metadata_rejection(self):
        for key, value in (("kind", "unknown"), ("universe_parameters", {}), ("type_display", ""),
                           ("source_range", {}), ("source_range", {"start_line": 0, "end_line": 1, "start_column": 0, "end_column": 1})):
            bad = extraction()
            bad["declarations"][0][key] = value
            with self.subTest(key=key, value=value), self.assertRaises(cp.Invalid):
                cp.material(mapping(), bad, self.goal)

    def test_every_registered_premise_consumer(self):
        self.m["premises"] = [{"id": "p", "goal_quote": "入力条件", "role": "discharge-required",
                               "declarations": ["CompletionFixture.differenceCriterion"],
                               "consumed_by": ["CompletionFixture.inputCharacterization", "CompletionFixture.identityMember"]}]
        with self.assertRaisesRegex(cp.Invalid, "registered consumer"):
            self.core()
        self.m["premises"][0]["consumed_by"].pop()
        self.core()

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
                "extraction": self.x, "core": self.core(), "receipts": [],
                "registry": {"fixture": "required"}}

    def packet(self):
        return cp._render_validated(self.bundle(), {"notes": "", "refs": []})

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
            cp._validate_packet_generated(b, p)

    def test_policy_packet_rejects_missing_registry(self):
        b = self.bundle()
        del b["registry"]
        with self.assertRaisesRegex(cp.Invalid, "registry is required"):
            cp._render_validated(b, {"notes": "", "refs": []})
        with tempfile.TemporaryDirectory() as d:
            with self.assertRaisesRegex(cp.Invalid, "registry is required"):
                cp.collect(Path(d), "mapping.json", [], "bundle.json", registry=None)

    def test_public_packet_apis_cannot_skip_live_validation(self):
        b = self.bundle()
        p = self.packet()
        with patch.object(cp, "validate_bundle", side_effect=cp.Invalid("live bundle rejected")):
            with self.assertRaisesRegex(cp.Invalid, "live bundle rejected"):
                cp.render(Path("."), b, {"notes": "", "refs": []})
            with self.assertRaisesRegex(cp.Invalid, "live bundle rejected"):
                cp.validate_packet(Path("."), b, p)
        review = self.review(p)
        gates = {"stage_evidence": {"standard_pr_review": {"ref": {"path": "missing", "sha256": "0" * 64}}}}
        with patch.object(cp, "validate_packet"), \
             patch.object(cp, "resolve_evidence", side_effect=cp.Invalid("evidence missing")):
            with self.assertRaisesRegex(cp.Invalid, "evidence missing"):
                cp.ledger(Path("."), b, p, review, gates)

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
            cp._ledger_validated(q, r, gates, old=p)
        check = {"old_packet_digest": cp.digest(p), "new_packet_digest": cp.digest(q), "review_digest": cp.digest(r),
                 "reviewer": "independent-reviewer", "implementer": "author", "qualified": True,
                 "resolved": ["F1"], "evidence": {"path": "fixture-recheck", "sha256": "0" * 64}, "new_findings": []}
        self.assertEqual(cp._ledger_validated(q, r, gates, check, p)["verdict"], "target-theorem-proved")
        for reviewer in cp.LANES:
            check["reviewer"] = reviewer
            with self.assertRaisesRegex(cp.Invalid, "must be new"):
                cp._ledger_validated(q, r, gates, check, p)
        check["reviewer"] = "author"
        with self.assertRaises(cp.Invalid):
            cp._ledger_validated(q, r, gates, check, p)


if __name__ == "__main__":
    unittest.main()
