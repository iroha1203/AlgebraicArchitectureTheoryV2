#!/usr/bin/env python3
"""Exercise registry evidence with a tiny sibling Git package and no network access."""
import json
import os
from pathlib import Path
import shutil
import tempfile

import completion_packet as cp


def git(repo, *args):
    return cp.run(["git", *args], repo)


def init_repository(repo, remote):
    repo.mkdir(parents=True)
    git(repo, "init")
    git(repo, "config", "user.email", "fixture@example.test")
    git(repo, "config", "user.name", "Completion Fixture")
    git(repo, "remote", "add", "origin", remote)


def commit_all(repo, message):
    git(repo, "add", ".")
    git(repo, "commit", "-m", message)
    return git(repo, "rev-parse", "HEAD")


def main():
    with tempfile.TemporaryDirectory(prefix="completion-external-") as directory:
        base = Path(directory).resolve()
        repo = base / "project"
        package = base / "packages/external"
        init_repository(package, "https://github.com/example/completion-external.git")
        source = package / "External/Dependency.lean"
        source.parent.mkdir(parents=True)
        source.write_text("namespace External\n/-- External fixture value. -/\ndef dependency : Nat := 1\nend External\n")
        external_commit = commit_all(package, "fixture external source")
        external_root = package / ".lake/build/lib/lean"
        external_olean = external_root / "External/Dependency.olean"
        external_olean.parent.mkdir(parents=True)
        cp.run(["lean", "-o", str(external_olean), "External/Dependency.lean"], package)

        init_repository(repo, "https://github.com/example/completion-project.git")
        (repo / "Owner.lean").write_text(
            "import External.Dependency\nnamespace Owner\n/-- Use the external fixture. -/\n"
            "def value : Nat := External.dependency\nend Owner\n")
        shutil.copyfile(Path(__file__).with_name("CompletionRegistry.lean"), repo / "CompletionRegistry.lean")
        cp.write(repo / "lake-manifest.json", {
            "version": "1", "packagesDir": "../packages", "packages": [
                {"type": "path", "name": "completion-project", "dir": "."},
                {"type": "git", "name": "external", "rev": external_commit,
                 "url": "https://github.com/example/completion-external.git"}],
            "name": "completion-project", "lakeDir": ".lake"})
        commit_all(repo, "fixture project source")

        registry = repo / "registry"
        output = repo / "output"
        previous = os.environ.get("LEAN_PATH")
        os.environ["LEAN_PATH"] = str(external_root)
        try:
            cp.index_dependencies(repo, repo / "Owner.lean", "Owner", registry,
                                  helper_path=repo / "CompletionRegistry.lean")
        finally:
            if previous is None:
                os.environ.pop("LEAN_PATH", None)
            else:
                os.environ["LEAN_PATH"] = previous
        receipt = cp.check_registry(repo, repo / "Owner.lean", "Owner", output, registry, [])
        receipt_path = output / "Owner.receipt.json"
        cp.write(receipt_path, receipt)
        owner = cp.validate_registry_receipt(repo, registry, receipt)
        index = cp.read(registry / "index.json")
        external_ids = [artifact_id for artifact_id, row in index["artifacts"].items()
                        if row["repository"]["kind"] == "lake-git"]
        cp.need(len(external_ids) == 1, "external artifact classification mismatch")
        external_row = index["artifacts"][external_ids[0]]
        object_path = registry / "objects" / external_row["olean_sha256"]
        original = object_path.read_bytes()
        object_path.write_bytes(b"tampered")
        try:
            cp.validate_registry(repo, registry, [external_ids[0]])
        except cp.Invalid:
            pass
        else:
            raise cp.Invalid("external artifact tamper accepted")
        object_path.write_bytes(original)
        cp.validate_registry_receipt(repo, registry, receipt)
        print(json.dumps({"result": "pass", "owner": owner["module"],
                          "external_artifacts": len(external_ids),
                          "receipt_sha256": cp.file_hash(receipt_path)}, sort_keys=True))


if __name__ == "__main__":
    main()
