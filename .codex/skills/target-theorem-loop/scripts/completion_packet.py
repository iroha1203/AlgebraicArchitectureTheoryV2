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
import ipaddress
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

VERSION = 2
REGISTRY_VERSION = 2
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


def normalize_url(url):
    """Normalize the harmless spelling differences used by Git and Lake."""
    return re.sub(r"\.git$", "", url.strip().rstrip("/"))


def public_repository_url(url):
    """Reject credentials and machine-local repository identities before serialization."""
    string(url)
    value = url.strip()
    need(value == url and not re.search(r"[\x00-\x20]", value), "unsafe repository URL")
    scp = re.fullmatch(r"git@([A-Za-z0-9.-]+):([A-Za-z0-9._~/-]+)", value)
    ordinary = re.fullmatch(
        r"(?:https|git)://([A-Za-z0-9.-]+)(?::[0-9]+)?/([A-Za-z0-9._~/-]+)", value)
    ssh = re.fullmatch(
        r"ssh://git@([A-Za-z0-9.-]+)(?::[0-9]+)?/([A-Za-z0-9._~/-]+)", value)
    need(scp is not None or ordinary is not None or ssh is not None,
         "repository URL must be public and credential-free")
    match = scp or ordinary or ssh
    host = match.group(1).lower()
    need("." in host and host != "localhost" and
         not host.endswith((".local", ".localhost", ".internal", ".lan", ".home", ".corp")),
         "repository URL must be public")
    try:
        address = ipaddress.ip_address(host)
    except ValueError:
        pass
    else:
        need(address.is_global, "repository URL must be public")
    return value


def github_repository(url):
    """Return the canonical GitHub owner/repository pair for a public Git remote."""
    value = normalize_url(public_repository_url(url))
    patterns = (
        r"https://github\.com/([^/]+)/([^/]+)",
        r"git://github\.com/([^/]+)/([^/]+)",
        r"git@github\.com:([^/]+)/([^/]+)",
        r"ssh://git@github\.com/([^/]+)/([^/]+)",
    )
    match = next((re.fullmatch(pattern, value) for pattern in patterns
                  if re.fullmatch(pattern, value) is not None), None)
    need(match is not None, "completion authorization requires a GitHub repository")
    return match.group(1), match.group(2)


def github_ref_repository(ref):
    match = re.fullmatch(r"https://github\.com/([^/]+)/([^/]+)/(?:issues|pull)/[1-9][0-9]*(?:#issuecomment-[1-9][0-9]*)?", ref)
    need(match is not None, "invalid GitHub evidence ref")
    return match.group(1), match.group(2)


def validate_mapping_repository(repo, mapping):
    """Reject authorization or predecessor reviews from a repository other than this checkout."""
    expected = github_repository(run(["git", "remote", "get-url", "origin"], repo))
    authorization = mapping["dependency_policy"]["authorization"]
    refs = [authorization["decision_ref"], authorization["conflict_issue_ref"],
            authorization["tracking_issue_ref"]]
    refs.extend(predecessor["review_ref"] for predecessor in mapping["reviewed_predecessors"])
    need(all(github_ref_repository(ref) == expected for ref in refs),
         "evidence ref repository differs from baseline repository")


def manifest_for(repo, source):
    source_path = repo / relative(repo, source)
    candidates = [p / "lake-manifest.json" for p in source_path.parents if p.is_relative_to(repo)]
    manifests = [p for p in candidates if p.is_file()]
    need(manifests, "lake-manifest.json not found for source")
    manifest = manifests[0]
    data = read(manifest)
    fields(data, ["version", "packagesDir", "packages", "name", "lakeDir"])
    array(data["packages"])
    return manifest, data


def source_module_name(repo, source):
    """Derive the selected Lean module from its package-relative source path."""
    source = repo / relative(repo, source)
    manifest, _ = manifest_for(repo, source)
    need(source.is_relative_to(manifest.parent), "source is outside its Lake package")
    rel = source.relative_to(manifest.parent)
    need(rel.suffix == ".lean", "selected source must be a Lean file")
    module = rel.with_suffix("").as_posix().replace("/", ".")
    need(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*", module),
         "invalid source module path")
    return module


def package_owners(repo, manifest, data):
    """Resolve manifest packages without recording machine-specific absolute paths."""
    result = []
    packages_dir = (manifest.parent / data["packagesDir"]).resolve()
    for entry in data["packages"]:
        need(isinstance(entry, dict), "invalid manifest package entry")
        string(entry.get("name"))
        if entry.get("type") == "git":
            string(entry.get("rev"))
            string(entry.get("url"))
            directory = (packages_dir / entry["name"]).resolve()
        elif entry.get("type") == "path":
            string(entry.get("dir"))
            directory = (manifest.parent / entry["dir"]).resolve()
        else:
            raise Invalid("unregistered/unsupported manifest package")
        need(directory.is_dir(), f"manifest package missing: {entry['name']}")
        owner = Path(run(["git", "rev-parse", "--show-toplevel"], directory)).resolve()
        need(directory.is_relative_to(owner), "package directory is not in its Git repository")
        result.append((owner, directory, entry))
    # The parent repository is always a valid baseline owner, even if a Lake
    # manifest omits its conventional path entry.
    if not any(owner == repo for owner, _, _ in result):
        result.append((repo, manifest.parent, {"type": "root", "name": data["name"], "dir": "."}))
    return result


def repo_identity(owner, repo, manifest_ref, entry):
    commit = run(["git", "rev-parse", "HEAD"], owner)
    if entry["type"] == "git":
        need(commit == entry["rev"], f"manifest commit mismatch: {entry['name']}")
        remote = run(["git", "remote", "get-url", "origin"], owner)
        public_repository_url(entry["url"])
        public_repository_url(remote)
        need(normalize_url(remote) == normalize_url(entry["url"]), f"repository identity mismatch: {entry['name']}")
        identity = {"kind": "lake-git", "url": entry["url"], "commit": commit,
                    "manifest": manifest_ref, "manifest_entry": entry}
    elif entry["type"] in ("path", "root"):
        need(owner == repo, "path package outside baseline repository")
        remote = run(["git", "remote", "get-url", "origin"], owner)
        public_repository_url(remote)
        identity = {"kind": "baseline", "url": remote, "commit": commit,
                    "manifest": manifest_ref, "manifest_entry": entry}
    return identity


def registry_paths(registry):
    registry = Path(registry).resolve()
    return registry, registry / "index.json", registry / "objects"


def empty_registry(lean_version, manifest_ref):
    return {"registry_type": "completion-artifact-registry", "schema_version": REGISTRY_VERSION,
            "lean_version": lean_version, "manifest": manifest_ref, "artifacts": {},
            "dependency_sets": {}, "roots": {}}


def store_dependency_set(index, artifact_ids):
    members = sorted(set(artifact_ids))
    value = {"artifact_ids": members}
    set_id = digest(value)
    index["dependency_sets"][set_id] = value
    return set_id


def dependency_members(index, set_id):
    need(set_id in index["dependency_sets"], "missing dependency-set ID")
    value = index["dependency_sets"][set_id]
    fields(value, ["artifact_ids"])
    distinct(value["artifact_ids"], "dependency-set artifact IDs", allow_empty=True)
    need(value["artifact_ids"] == sorted(value["artifact_ids"]), "dependency-set must be sorted")
    need(digest(value) == set_id, "content-addressed dependency-set ID mismatch")
    return value["artifact_ids"]


def validate_artifact_metadata(metadata):
    fields(metadata, ["artifact_type", "schema_version", "module", "repository", "source",
                      "olean_sha256", "olean_files", "lean_version", "dependency_set"])
    need(metadata["artifact_type"] == "lean-olean", "artifact type")
    need(metadata["schema_version"] == REGISTRY_VERSION, "artifact schema")
    need(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*", metadata["module"]), "invalid artifact module")
    fields(metadata["source"], ["path", "blob"])
    need(re.fullmatch(r"[0-9a-f]{64}", metadata["olean_sha256"]) is not None, "artifact hash")
    fields(metadata["olean_files"], ["olean"], ["olean.private", "olean.server", "ir"])
    need(metadata["olean_files"]["olean"] == metadata["olean_sha256"], "main olean hash mismatch")
    for value in metadata["olean_files"].values():
        need(isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value), "olean companion hash")
    string(metadata["dependency_set"])
    need(re.fullmatch(r"[0-9a-f]{64}", metadata["dependency_set"]) is not None, "dependency-set ID")
    fields(metadata["repository"], ["kind", "url", "commit", "manifest", "manifest_entry"])
    need(metadata["repository"]["kind"] in ("baseline", "lake-git"), "repository kind")
    entry_type = metadata["repository"]["manifest_entry"].get("type")
    need((metadata["repository"]["kind"], entry_type) in
         (("baseline", "path"), ("baseline", "root"), ("lake-git", "git")),
         "repository kind/manifest entry mismatch")
    public_repository_url(metadata["repository"]["url"])


def validate_repository(repo, identity):
    entry = identity["manifest_entry"]
    need((identity["kind"], entry.get("type")) in
         (("baseline", "path"), ("baseline", "root"), ("lake-git", "git")),
         "repository kind/manifest entry mismatch")
    manifest_ref = identity["manifest"]
    need(blob(repo, run(["git", "rev-parse", "HEAD"], repo), manifest_ref["path"]) == manifest_ref,
         "registry manifest mismatch")
    manifest = read(repo / manifest_ref["path"])
    if entry["type"] == "root":
        need(entry == {"type": "root", "name": manifest["name"], "dir": "."},
             "baseline root identity mismatch")
    else:
        need(entry in manifest["packages"], "manifest entry no longer pinned")
    owners = package_owners(repo, repo / manifest_ref["path"], manifest)
    matches = [(owner, package_dir, row) for owner, package_dir, row in owners if row == entry]
    need(len(matches) == 1, "manifest owner resolution mismatch")
    owner, _, _ = matches[0]
    need(run(["git", "rev-parse", "HEAD"], owner) == identity["commit"], "artifact repository commit mismatch")
    remote = run(["git", "remote", "get-url", "origin"], owner)
    need(normalize_url(remote) == normalize_url(identity["url"]), "artifact repository URL mismatch")
    return owner


def validate_registry(repo, registry, artifact_ids=None):
    registry, index_path, objects = registry_paths(registry)
    index = read(index_path)
    fields(index, ["registry_type", "schema_version", "lean_version", "manifest", "artifacts", "dependency_sets", "roots"])
    need(index["registry_type"] == "completion-artifact-registry" and index["schema_version"] == REGISTRY_VERSION,
         "registry schema")
    need(index["lean_version"] == run(["lean", "--version"], repo), "registry Lean version mismatch")
    need(blob(repo, run(["git", "rev-parse", "HEAD"], repo), index["manifest"]["path"]) == index["manifest"],
         "registry manifest changed")
    ids = sorted(index["artifacts"]) if artifact_ids is None else sorted(set(artifact_ids))
    for set_id in index["dependency_sets"]:
        need(set(dependency_members(index, set_id)) <= set(index["artifacts"]),
             "dependency-set contains missing artifact ID")
    for root_module, root_entry in index["roots"].items():
        fields(root_entry, ["root_id", "module", "source", "direct_modules", "dependency_set"])
        need(root_entry["module"] == root_module, "registry root module mismatch")
        need(root_entry["root_id"] == digest({k: v for k, v in root_entry.items() if k != "root_id"}),
             "content-addressed registry root mismatch")
        fields(root_entry["source"], ["path", "blob"])
        distinct(root_entry["direct_modules"], "root direct modules", allow_empty=True)
        dependency_members(index, root_entry["dependency_set"])
    owners = {}
    top_owners = {}
    sysroot = Path(run(["lean", "--print-prefix"], repo)).resolve() / "lib/lean"
    for artifact_id in ids:
        need(artifact_id in index["artifacts"], f"missing registry artifact: {artifact_id}")
        metadata = index["artifacts"][artifact_id]
        validate_artifact_metadata(metadata)
        need(metadata["lean_version"] == index["lean_version"], "artifact Lean version mismatch")
        need(digest(metadata) == artifact_id, "content-addressed artifact ID mismatch")
        for component_hash in metadata["olean_files"].values():
            obj = objects / component_hash
            need(obj.is_file() and file_hash(obj) == component_hash, "missing/changed registry object")
        key = canonical(metadata["repository"])
        owner = owners.get(key)
        if owner is None:
            owner = validate_repository(repo, metadata["repository"])
            owners[key] = owner
        need(blob(owner, metadata["repository"]["commit"], metadata["source"]["path"]) == metadata["source"],
             "artifact source blob mismatch")
        top = metadata["module"].split(".")[0]
        need(not (sysroot / top).exists() and not (sysroot / (top + ".olean")).exists(), "registry overlaps toolchain namespace")
        prior = top_owners.setdefault(top, key)
        need(prior == key, "root namespace collision between repositories")
    module_rows = {}
    selected_ids = set(ids)
    for artifact_id in ids:
        row = index["artifacts"][artifact_id]
        prior = module_rows.get(row["module"])
        need(prior is None or prior == artifact_id, "same module has conflicting artifact digest")
        module_rows[row["module"]] = artifact_id
        need(set(dependency_members(index, row["dependency_set"])) <= selected_ids,
             "missing dependency artifact ID from selected set")
    return index


def store_object(source, objects, expected):
    objects.mkdir(parents=True, exist_ok=True)
    destination = objects / expected
    if not destination.exists():
        try:
            os.link(source, destination)
        except OSError:
            shutil.copyfile(source, destination)
    need(file_hash(destination) == expected, "artifact changed while storing")


def source_for_module(owner, package_dir, module, commit):
    suffix = module.replace(".", "/") + ".lean"
    candidates = [package_dir / suffix, owner / suffix]
    for candidate in candidates:
        if candidate.is_file() and candidate.is_relative_to(owner):
            rel = candidate.relative_to(owner).as_posix()
            try:
                return blob(owner, commit, rel)
            except Invalid:
                pass
    matches = [p for p in run(["git", "ls-tree", "-r", "--name-only", commit], owner).splitlines()
               if p == suffix or p.endswith("/" + suffix)]
    need(len(matches) == 1, f"cannot resolve unique source for module: {module}")
    return blob(owner, commit, matches[0])


def module_from_artifact(path, roots):
    matches = [(root, path.relative_to(root).with_suffix("").as_posix().replace("/", "."))
               for root in roots if path.is_relative_to(root)]
    need(len(matches) == 1, f"artifact search root mismatch: {path.name}")
    return matches[0][1]


def select_artifact(candidates, module):
    need(candidates, f"missing imported artifact: {module}")
    need(len(candidates) == 1, f"search order has multiple artifact candidates: {module}")
    return candidates[0][1], file_hash(candidates[0][1])


def index_dependencies(repo, source, module, registry, helper_path=None):
    """Inventory the already-built transitive imports; never elaborate a dependency file."""
    source = relative(repo, source)
    need(Path(source).name not in ("ResearchLean.lean", "Formal.lean", "AG.lean"), "aggregate forbidden")
    need(module == source_module_name(repo, source), "source/module identity mismatch")
    manifest, manifest_data = manifest_for(repo, source)
    head = run(["git", "rev-parse", "HEAD"], repo)
    manifest_ref = blob(repo, head, manifest)
    lean_version = run(["lean", "--version"], repo)
    registry, index_path, objects = registry_paths(registry)
    if index_path.exists():
        index = read(index_path)
        need(index["lean_version"] == lean_version and index["manifest"] == manifest_ref, "registry context mismatch")
    else:
        index = empty_registry(lean_version, manifest_ref)
    empty_set = store_dependency_set(index, [])
    sysroot = Path(run(["lean", "--print-prefix"], repo)).resolve() / "lib/lean"
    roots = list(dict.fromkeys(Path(p).resolve() for p in os.environ.get("LEAN_PATH", "").split(os.pathsep)
                              if p and Path(p).resolve() != sysroot))
    direct_paths = [Path(p).resolve() for p in run(["lean", "--deps", source], repo).splitlines()]
    direct_modules = [module_from_artifact(p, roots) for p in direct_paths if not p.is_relative_to(sysroot)]
    helper = relative(repo, helper_path or Path(__file__).with_name("CompletionRegistry.lean"))
    imported = (json.loads(run(["lean", "--run", helper, *direct_modules], repo), object_pairs_hook=unique_pairs)
                if direct_modules else [])
    distinct(imported, "imported modules", allow_empty=True)
    owners = package_owners(repo, manifest, manifest_data)
    artifact_ids = []
    top_owners = {}
    for imported_module in imported:
        rel_olean = imported_module.replace(".", "/") + ".olean"
        candidates = [(root, root / rel_olean) for root in roots if (root / rel_olean).is_file()]
        if (sysroot / rel_olean).is_file():
            need(not candidates, f"package artifact overlaps toolchain module: {imported_module}")
            continue
        artifact_path, main_hash = select_artifact(candidates, imported_module)
        owner_matches = [(owner, package_dir, entry) for owner, package_dir, entry in owners
                         if artifact_path.is_relative_to(owner)]
        need(len(owner_matches) == 1, f"unregistered package artifact: {imported_module}")
        owner, package_dir, entry = owner_matches[0]
        identity = repo_identity(owner, repo, manifest_ref, entry)
        source_ref = source_for_module(owner, package_dir, imported_module, identity["commit"])
        candidates = {suffix: Path(str(artifact_path.with_suffix("")) + "." + suffix)
                      for suffix in ("olean", "olean.private", "olean.server", "ir")}
        components = {suffix: path for suffix, path in candidates.items() if path.is_file()}
        need("olean" in components, f"missing olean data file: {imported_module}")
        olean_files = {suffix: file_hash(path) for suffix, path in components.items()}
        metadata = {"artifact_type": "lean-olean", "schema_version": REGISTRY_VERSION,
                    "module": imported_module, "repository": identity, "source": source_ref,
                    "olean_sha256": main_hash, "olean_files": olean_files,
                    "lean_version": lean_version, "dependency_set": empty_set}
        artifact_id = digest(metadata)
        top = imported_module.split(".")[0]
        owner_key = digest(identity)
        need(top_owners.setdefault(top, owner_key) == owner_key, "root namespace collision between repositories")
        index["artifacts"][artifact_id] = metadata
        for suffix, path in components.items():
            store_object(path, objects, olean_files[suffix])
        artifact_ids.append(artifact_id)
    dependency_set = store_dependency_set(index, artifact_ids)
    root_entry = {"module": module, "source": blob(repo, head, source),
                  "direct_modules": sorted(direct_modules), "dependency_set": dependency_set}
    root_entry["root_id"] = digest(root_entry)
    index["roots"][module] = root_entry
    write(index_path, index)
    validate_registry(repo, registry, artifact_ids)
    return index["roots"][module]


def validate_receipt(repo, receipt):
    fields(receipt, ["head", "source", "module", "olean", "olean_sha256", "dependencies", "command", "stdout", "stderr", "exit_code", "lean_version"])
    array(receipt["dependencies"])
    distinct(receipt["command"], "command arguments", unique=False)
    need(isinstance(receipt["module"], str) and re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*", receipt["module"]), "invalid receipt module")
    need(receipt["olean"].endswith(receipt["module"].replace(".", "/") + ".olean"), "module/olean mismatch")
    need(receipt["head"] == run(["git", "rev-parse", "HEAD"], repo), "receipt head mismatch")
    need(receipt["lean_version"] == run(["lean", "--version"], repo), "receipt toolchain mismatch")
    need(blob(repo, receipt["head"], receipt["source"]["path"]) == receipt["source"], "receipt source mismatch")
    need(file_hash(repo / relative(repo, receipt["olean"])) == receipt["olean_sha256"], "stale olean")
    need(receipt["exit_code"] == 0, "failed focused check")
    for stream in ("stdout", "stderr"):
        fields(receipt[stream], ["path", "sha256"])
        need(file_hash(repo / relative(repo, receipt[stream]["path"])) == receipt[stream]["sha256"], "missing/changed command output")
    sysroot = Path(run(["lean", "--print-prefix"], repo)).resolve()
    for dep in receipt["dependencies"]:
        if "system" in dep:
            fields(dep, ["system", "sha256"])
            path = (sysroot / dep["system"]).resolve()
            need(path.is_relative_to(sysroot), "system path escape")
            need(file_hash(path) == dep["sha256"], "system dependency mismatch")
        elif "repository" in dep:
            fields(dep, ["repository", "receipt"])
            external_repo = repo / relative(repo, dep["repository"])
            need(Path(run(["git", "rev-parse", "--show-toplevel"], external_repo)).resolve() == external_repo.resolve(), "dependency repository mismatch")
            validate_receipt(external_repo, dep["receipt"])
        else:
            validate_receipt(repo, dep)


def artifact_set_digest(index, artifact_ids):
    return digest({artifact_id: index["artifacts"][artifact_id] for artifact_id in sorted(set(artifact_ids))})


def validate_focused_command(repo, receipt, metadata):
    """Bind a focused receipt to its exact source and surviving output artifacts."""
    repo = Path(repo).resolve()
    command = receipt["command"]
    distinct(command, "command arguments", unique=False)
    need(len(command) == 4 and command[0:2] == ["lean", "-o"],
         "focused receipt command shape")
    need(command[3] == metadata["source"]["path"], "focused receipt source mismatch")
    output = repo / relative(repo, command[2])
    need(command[2].endswith(receipt["module"].replace(".", "/") + ".olean"),
         "focused receipt module/output mismatch")
    for suffix, expected in metadata["olean_files"].items():
        component = Path(str(output.with_suffix("")) + "." + suffix)
        need(component.is_file() and file_hash(component) == expected,
             "focused receipt output missing/changed")


def validate_registry_receipt(repo, registry, receipt):
    fields(receipt, ["receipt_type", "schema_version", "registry_schema_version", "module", "root_id",
                     "artifact_id", "dependency_set",
                     "artifact_set_digest", "command", "stdout", "stderr", "exit_code", "lean_version"])
    need(receipt["receipt_type"] == "registry-focused-check" and receipt["schema_version"] == VERSION,
         "registry receipt schema")
    need(receipt["registry_schema_version"] == REGISTRY_VERSION, "registry receipt version")
    _, index_path, _ = registry_paths(registry)
    index = read(index_path)
    dependency_ids = dependency_members(index, receipt["dependency_set"])
    ids = [receipt["artifact_id"], *dependency_ids]
    index = validate_registry(repo, registry, ids)
    metadata = index["artifacts"][receipt["artifact_id"]]
    need(metadata["module"] == receipt["module"], "receipt module mismatch")
    need(metadata["dependency_set"] == receipt["dependency_set"], "receipt dependency set mismatch")
    need(receipt["artifact_set_digest"] == artifact_set_digest(index, ids), "receipt artifact set mismatch")
    need(receipt["lean_version"] == index["lean_version"], "receipt Lean version mismatch")
    need(receipt["module"] in index["roots"], "missing registry root for receipt")
    root_entry = index["roots"][receipt["module"]]
    need(receipt["root_id"] == root_entry["root_id"], "receipt registry root mismatch")
    need(root_entry["source"] == metadata["source"], "receipt root/source mismatch")
    dependency_modules = {index["artifacts"][artifact_id]["module"] for artifact_id in dependency_ids}
    need(set(root_entry["direct_modules"]) <= dependency_modules,
         "receipt omits a direct dependency")
    validate_focused_command(repo, receipt, metadata)
    with registry_environment(repo, registry, dependency_ids) as env:
        sysroot = Path(run(["lean", "--print-prefix"], repo, env)).resolve() / "lib/lean"
        roots = [Path(p).resolve() for p in env["LEAN_PATH"].split(os.pathsep) if p]
        direct_paths = [Path(p).resolve() for p in
                        run(["lean", "--deps", metadata["source"]["path"]], repo, env).splitlines()]
        actual_direct = sorted(module_from_artifact(path, roots)
                               for path in direct_paths if not path.is_relative_to(sysroot))
    need(actual_direct == root_entry["direct_modules"], "registry root direct imports changed")
    need(receipt["exit_code"] == 0, "failed focused check")
    for stream in ("stdout", "stderr"):
        fields(receipt[stream], ["path", "sha256"])
        need(file_hash(repo / relative(repo, receipt[stream]["path"])) == receipt[stream]["sha256"],
             "missing/changed command output")
    return metadata


@contextmanager
def registry_environment(repo, registry, artifact_ids):
    """Stage exactly the requested content-addressed artifacts, never ambient roots."""
    index = validate_registry(repo, registry, artifact_ids)
    _, _, objects = registry_paths(registry)
    modules = {}
    with tempfile.TemporaryDirectory(prefix="completion-registry-") as directory:
        for artifact_id in sorted(set(artifact_ids)):
            metadata = index["artifacts"][artifact_id]
            previous = modules.get(metadata["module"])
            need(previous is None or previous == artifact_id, "same module has conflicting artifact digest")
            modules[metadata["module"]] = artifact_id
            base = Path(directory) / metadata["module"].replace(".", "/")
            base.parent.mkdir(parents=True, exist_ok=True)
            for suffix, component_hash in metadata["olean_files"].items():
                source = objects / component_hash
                destination = Path(str(base) + "." + suffix)
                try:
                    os.link(source, destination)
                except OSError:
                    shutil.copyfile(source, destination)
                need(file_hash(destination) == component_hash, "artifact changed while staging")
        env = dict(os.environ)
        env["LEAN_PATH"] = directory
        yield env


def overlay_artifact_ids(index, baseline_ids, receipts):
    """Resolve a focused-receipt chain by module, with explicit owners winning baseline artifacts."""
    selected = {index["artifacts"][artifact_id]["module"]: artifact_id for artifact_id in baseline_ids}
    focused = {}
    inherited = {}
    for receipt in receipts:
        owner = index["artifacts"][receipt["artifact_id"]]
        previous = focused.get(owner["module"])
        need(previous is None or previous == receipt["artifact_id"], "conflicting focused dependency receipts")
        focused[owner["module"]] = receipt["artifact_id"]
        for artifact_id in dependency_members(index, receipt["dependency_set"]):
            row = index["artifacts"][artifact_id]
            previous = inherited.get(row["module"])
            need(previous is None or previous == artifact_id or row["module"] in focused,
                 "conflicting transitive focused dependency artifacts")
            inherited[row["module"]] = artifact_id
    selected.update(inherited)
    selected.update(focused)
    return sorted(selected.values())


def check_registry(repo, source, module, out, registry, dependency_receipts=()):
    """Compile one leaf against only its indexed dependencies and register the result."""
    need(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*", module), "invalid module")
    source = relative(repo, source)
    need(Path(source).name not in ("ResearchLean.lean", "Formal.lean", "AG.lean"), "aggregate forbidden")
    need(module == source_module_name(repo, source), "source/module identity mismatch")
    registry, index_path, objects = registry_paths(registry)
    index = read(index_path)
    need(module in index["roots"], "owner leaf has not been indexed")
    root_entry = index["roots"][module]
    fields(root_entry, ["root_id", "module", "source", "direct_modules", "dependency_set"])
    head = run(["git", "rev-parse", "HEAD"], repo)
    source_ref = blob(repo, head, source)
    need(root_entry["source"] == source_ref, "indexed owner source mismatch")
    dependency_ids = dependency_members(index, root_entry["dependency_set"])
    index = validate_registry(repo, registry, dependency_ids)
    receipt_rows = []
    for receipt_path in dependency_receipts:
        receipt = read(receipt_path)
        validate_registry_receipt(repo, registry, receipt)
        receipt_rows.append(receipt)
    dependency_ids = overlay_artifact_ids(index, dependency_ids, receipt_rows)
    out = repo / relative(repo, out)
    out.mkdir(parents=True, exist_ok=True)
    olean = out / (module.replace(".", "/") + ".olean")
    olean.parent.mkdir(parents=True, exist_ok=True)
    command = ["lean", "-o", relative(repo, olean), source]
    for suffix in ("olean", "olean.private", "olean.server", "ir"):
        stale = Path(str(olean.with_suffix("")) + "." + suffix)
        if stale.exists():
            stale.unlink()
    with registry_environment(repo, registry, dependency_ids) as env:
        result = subprocess.run(command, cwd=repo, env=env, capture_output=True)
    streams = {}
    for name, data in (("stdout", result.stdout), ("stderr", result.stderr)):
        path = out / (module + "." + name)
        path.write_bytes(data)
        streams[name] = {"path": relative(repo, path), "sha256": file_hash(path)}
    need(result.returncode == 0, f"focused registry check failed: {streams}")
    manifest = index["manifest"]
    manifest_data = read(repo / manifest["path"])
    matches = [(owner, package_dir, entry) for owner, package_dir, entry in
               package_owners(repo, repo / manifest["path"], manifest_data) if owner == repo]
    need(matches, "baseline repository is not registered in manifest")
    owner, _, entry = matches[0]
    identity = repo_identity(owner, repo, manifest, entry)
    candidates = {suffix: Path(str(olean.with_suffix("")) + "." + suffix)
                  for suffix in ("olean", "olean.private", "olean.server", "ir")}
    companions = {suffix: path for suffix, path in candidates.items() if path.is_file()}
    need("olean" in companions, "focused check did not produce an olean")
    olean_files = {suffix: file_hash(path) for suffix, path in companions.items()}
    dependency_set = store_dependency_set(index, dependency_ids)
    metadata = {"artifact_type": "lean-olean", "schema_version": REGISTRY_VERSION, "module": module,
                "repository": identity, "source": source_ref, "olean_sha256": olean_files["olean"],
                "olean_files": olean_files,
                "lean_version": index["lean_version"], "dependency_set": dependency_set}
    artifact_id = digest(metadata)
    index["artifacts"][artifact_id] = metadata
    for suffix, path in companions.items():
        store_object(path, objects, olean_files[suffix])
    write(index_path, index)
    ids = [artifact_id, *dependency_ids]
    validate_registry(repo, registry, ids)
    return {"receipt_type": "registry-focused-check", "schema_version": VERSION,
            "registry_schema_version": REGISTRY_VERSION, "module": module,
            "root_id": root_entry["root_id"], "artifact_id": artifact_id, "dependency_set": dependency_set,
            "artifact_set_digest": artifact_set_digest(index, ids), "command": command,
            "exit_code": result.returncode, "lean_version": index["lean_version"], **streams}


def check(repo, source, module, out, dependency_receipts):
    """Compile one explicit leaf; require receipts for every non-toolchain import."""
    need(re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*(\.[A-Za-z_][A-Za-z_0-9]*)*", module), "invalid module")
    source = relative(repo, source)
    need(Path(source).name not in ("ResearchLean.lean", "Formal.lean", "AG.lean"), "aggregate forbidden")
    head = run(["git", "rev-parse", "HEAD"], repo)
    source_ref = blob(repo, head, source)
    out = repo / relative(repo, out)
    out.mkdir(parents=True, exist_ok=True)
    deps = []
    available = []
    for receipt_path in dependency_receipts:
        receipt_path = Path(receipt_path).resolve()
        owner_repo = Path(run(["git", "rev-parse", "--show-toplevel"], receipt_path.parent)).resolve()
        r = read(receipt_path)
        available.append((owner_repo, r))
    sysroot = Path(run(["lean", "--print-prefix"], repo)).resolve()
    for depname in run(["lean", "--deps", source], repo).splitlines():
        dep = Path(depname).resolve()
        if dep.is_relative_to(sysroot):
            deps.append({"system": dep.relative_to(sysroot).as_posix(), "sha256": file_hash(dep)})
        else:
            found = [(owner_repo, r) for owner_repo, r in available if (owner_repo / r["olean"]).resolve() == dep]
            need(len(found) == 1, f"dependency needs focused receipt: {dep.name}")
            owner_repo, r = found[0]
            validate_receipt(owner_repo, r)
            deps.append(r if owner_repo == repo else {"repository": relative(repo, owner_repo), "receipt": r})
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
            "dependencies": deps, "command": command, "exit_code": result.returncode,
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
    fields(mapping, ["schema_version", "goal", "goal_path", "report_path", "dependency_policy",
                     "reviewed_predecessors", "criteria", "claims", "premises", "evidence"])
    need(mapping["schema_version"] == VERSION, "unsupported schema version")
    for name in ["goal", "goal_path", "report_path"]:
        string(mapping[name])
    policy = mapping["dependency_policy"]
    fields(policy, ["schema_version", "method", "authorization", "selected_owner", "repository_local",
                    "external_lake", "source_build_claim"])
    need(policy["schema_version"] == 1, "dependency policy version")
    need(policy["method"] == "focused-owner-plus-pinned-dependency-trust", "dependency policy method")
    authorization = policy["authorization"]
    fields(authorization, ["goal", "decision_ref", "conflict_issue_ref", "tracking_issue_ref"])
    need(authorization["goal"] == mapping["goal"], "dependency policy GOAL linkage")
    issue_pattern = re.compile(r"https://github\.com/([^/]+)/([^/]+)/issues/([1-9][0-9]*)")
    comment_pattern = re.compile(r"https://github\.com/([^/]+)/([^/]+)/issues/([1-9][0-9]*)#issuecomment-([1-9][0-9]*)")
    conflict = issue_pattern.fullmatch(authorization["conflict_issue_ref"])
    tracking = issue_pattern.fullmatch(authorization["tracking_issue_ref"])
    decision = comment_pattern.fullmatch(authorization["decision_ref"])
    need(conflict is not None and tracking is not None and decision is not None,
         "dependency policy authorization ref")
    need(conflict.groups()[:2] == tracking.groups()[:2] == decision.groups()[:2],
         "dependency policy authorization repository")
    need(conflict.group(3) == decision.group(3), "decision must be recorded on conflict issue")
    need(authorization["conflict_issue_ref"] != authorization["tracking_issue_ref"],
         "conflict and tracking issues must differ")
    need(policy["selected_owner"] == "focused-source-receipt-required", "selected owner policy")
    need(policy["repository_local"] == "runtime-only-material-selected-or-reviewed", "repository-local policy")
    need(policy["external_lake"] == "manifest-pinned-artifact-trust", "external Lake policy")
    need(policy["source_build_claim"] is False, "dependency policy must not claim source build")
    array(mapping["reviewed_predecessors"])
    predecessor_names = []
    for predecessor in mapping["reviewed_predecessors"]:
        fields(predecessor, ["declaration", "owner", "declaration_digest", "reviewed_head",
                             "source_blob", "artifact_id", "review_ref"])
        string(predecessor["declaration"])
        string(predecessor["owner"])
        need(re.fullmatch(r"[0-9a-f]{64}", predecessor["declaration_digest"]) is not None,
             "predecessor declaration digest")
        need(re.fullmatch(r"[0-9a-f]{40}", predecessor["reviewed_head"]) is not None,
             "predecessor reviewed head")
        need(re.fullmatch(r"[0-9a-f]{40}", predecessor["source_blob"]) is not None,
             "predecessor source blob")
        need(re.fullmatch(r"[0-9a-f]{64}", predecessor["artifact_id"]) is not None,
             "predecessor artifact ID")
        need(re.fullmatch(r"https://github\.com/[^/]+/[^/]+/(?:issues|pull)/[1-9][0-9]*#issuecomment-[1-9][0-9]*",
                          predecessor["review_ref"]) is not None, "predecessor review ref")
        predecessor_names.append(predecessor["declaration"])
    distinct(predecessor_names, "reviewed predecessor declarations", allow_empty=True)
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


def path_between_any_reference(rows, start, end):
    """Find a dependency path including statement, value, and projection references."""
    queue = deque([(start, [start])])
    visited = {start}
    while queue:
        node, path = queue.popleft()
        for name in sorted({edge["name"] for edge in rows.get(node, {}).get("references", [])}):
            if name == end:
                return path + [name]
            if name in rows and name not in visited:
                visited.add(name)
                queue.append((name, path + [name]))
    return None


def material(mapping, extraction, goal_text, repository_artifacts=None):
    validate_map(mapping)
    repository_artifacts = {} if repository_artifacts is None else repository_artifacts
    need(isinstance(repository_artifacts, dict), "repository artifact context")
    for module, artifact in repository_artifacts.items():
        string(module)
        fields(artifact, ["artifact_id", "source", "repository_commit"])
        need(re.fullmatch(r"[0-9a-f]{64}", artifact["artifact_id"]) is not None, "repository artifact ID")
        fields(artifact["source"], ["path", "blob"])
        need(re.fullmatch(r"[0-9a-f]{40}", artifact["source"]["blob"]) is not None,
             "repository source blob")
        need(re.fullmatch(r"[0-9a-f]{40}", artifact["repository_commit"]) is not None,
             "repository commit")
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
    terminal_rows = {}
    for terminal in extraction["terminals"]:
        fields(terminal, ["name", "owner", "kind", "universe_parameters", "type_display", "source_range",
                          "type", "value", "axioms", "constant_names", "references"])
        for field in ("name", "owner", "type", "kind", "type_display"):
            string(terminal[field])
        if terminal["value"] is not None:
            string(terminal["value"])
        distinct(terminal["axioms"], "terminal axioms", allow_empty=True)
        need(set(terminal["axioms"]) <= ALLOWED_AXIOMS, "terminal axiom audit failed")
        need(terminal["name"] not in terminal_rows, "duplicate extracted terminal")
        terminal_rows[terminal["name"]] = terminal
    terminals = set(terminal_rows)
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
    reachable_rows = set()
    reachable_terminals = set()
    queue = deque(central)
    while queue:
        name = queue.popleft()
        if name in reachable_rows:
            continue
        reachable_rows.add(name)
        for edge in rows[name]["references"]:
            dependency = edge["name"]
            if dependency in rows and dependency not in reachable_rows:
                queue.append(dependency)
            elif dependency in terminal_rows:
                reachable_terminals.add(dependency)
    required_predecessors = {name for name in reachable_terminals
                             if terminal_rows[name]["owner"] in repository_artifacts}
    declared_predecessors = {p["declaration"] for p in mapping["reviewed_predecessors"]}
    need(declared_predecessors == required_predecessors,
         "repository-local terminal predecessor coverage mismatch")
    predecessor_nodes = []
    for predecessor in mapping["reviewed_predecessors"]:
        terminal = terminal_rows[predecessor["declaration"]]
        need(predecessor["owner"] == terminal["owner"], "predecessor owner mismatch")
        need(predecessor["declaration_digest"] == digest(terminal), "predecessor declaration mismatch")
        artifact = repository_artifacts[terminal["owner"]]
        need(predecessor["artifact_id"] == artifact["artifact_id"], "predecessor artifact mismatch")
        need(predecessor["source_blob"] == artifact["source"]["blob"], "predecessor source mismatch")
        need(predecessor["reviewed_head"] == artifact["repository_commit"], "predecessor reviewed head mismatch")
        predecessor_nodes.append({"name": terminal["name"], "owner": terminal["owner"],
                                  "type": terminal["type"], "kind": "reviewed-predecessor",
                                  "declaration_digest": digest(terminal),
                                  "type_digest": digest(terminal["type"]),
                                  "value_digest": digest(terminal["value"]),
                                  "axioms": terminal["axioms"],
                                  "artifact_id": artifact["artifact_id"],
                                  "source": artifact["source"],
                                  "reviewed_head": artifact["repository_commit"],
                                  "review_ref": predecessor["review_ref"]})
        for start in sorted(central):
            path = path_between_any_reference(rows, start, terminal["name"])
            if path is not None:
                edge = {"from": start, "to": terminal["name"],
                        "distance": "direct" if len(path) == 2 else "via", "path": path,
                        "dependency_kind": "statement-value-or-projection"}
                if edge not in routes:
                    routes.append(edge)
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
    return {"criteria": mapping["criteria"], "dependency_policy": mapping["dependency_policy"],
            "direction_coverage": directions,
            "dependency_dag": {"semantics": "target-acceptance-spine",
                               "nodes": [declaration(n) for n in sorted(central)] + predecessor_nodes,
                               "edges": sorted(routes, key=lambda e: canonical(e))},
            "reviewed_predecessors": predecessor_nodes,
            "material_premises": mapping["premises"], "gate_evidence": mapping["evidence"],
            "review_required": GATES}


@contextmanager
def extraction_environment(repo, receipts):
    """One clean namespace tree, containing only recursively validated receipts.

    Lean selects the first root namespace directory, not the first exact module.
    Never append ambient/cache roots: they can supply an unrecorded stale module.
    Toolchain namespaces cannot be overlaid by user receipts in this version.
    """
    array(receipts)
    need(receipts, "no focused receipts")
    system = Path(run(["lean", "--print-prefix"], repo)).resolve() / "lib/lean"
    artifacts = {}

    def include(owner, receipt):
        validate_receipt(owner, receipt)
        module = receipt["module"]
        top = system / module.split(".")[0]
        need(not top.exists() and not top.with_suffix(".olean").exists(), "receipt overlaps toolchain namespace")
        previous = artifacts.get(module)
        need(previous is None or previous[1] == receipt["olean_sha256"], "conflicting module receipts")
        artifacts[module] = (owner / receipt["olean"], receipt["olean_sha256"])
        for dep in receipt["dependencies"]:
            if "repository" in dep:
                include(owner / relative(owner, dep["repository"]), dep["receipt"])
            elif "system" not in dep:
                include(owner, dep)

    for receipt in receipts:
        include(repo, receipt)
    with tempfile.TemporaryDirectory(prefix="completion-import-") as directory:
        for module, (source, expected) in artifacts.items():
            destination = Path(directory) / (module.replace(".", "/") + ".olean")
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, destination)
            need(file_hash(destination) == expected, "artifact changed while staging")
        env = dict(os.environ)
        env["LEAN_PATH"] = directory
        yield env


def repository_artifact_context(index, artifact_ids, receipts):
    """Bind non-selected baseline modules to the exact runtime artifact used."""
    owner_ids = {receipt["artifact_id"] for receipt in receipts}
    context = {}
    for artifact_id in artifact_ids:
        row = index["artifacts"][artifact_id]
        if artifact_id in owner_ids or row["repository"]["kind"] != "baseline":
            continue
        need(row["module"] not in context, f"multiple repository runtime artifacts: {row['module']}")
        context[row["module"]] = {"artifact_id": artifact_id, "source": row["source"],
                                  "repository_commit": row["repository"]["commit"]}
    return context


def registry_evidence(index, artifact_ids, receipts, policy):
    """Canonical review-facing provenance; large closures are committed by Merkle-style digests."""
    artifact_ids = sorted(set(artifact_ids))
    repository_rows = {}
    grouped = {}
    module_ids = {}
    for artifact_id in artifact_ids:
        row = index["artifacts"][artifact_id]
        repository_id = digest(row["repository"])
        repository_rows[repository_id] = row["repository"]
        grouped.setdefault(repository_id, {})[artifact_id] = row
        module_ids[row["module"]] = artifact_id
    repositories = []
    for repository_id in sorted(grouped):
        rows = grouped[repository_id]
        repositories.append({"repository_id": repository_id, "identity": repository_rows[repository_id],
                             "artifact_count": len(rows), "artifact_merkle_root": digest(rows),
                             "module_source_root": digest(sorted(
                                 ({"module": row["module"], "source": row["source"]} for row in rows.values()),
                                 key=lambda value: canonical(value))),
                             "olean_root": digest(sorted(
                                 ({"module": row["module"], "olean_files": row["olean_files"]} for row in rows.values()),
                                 key=lambda value: canonical(value)))})
    owner_ids = sorted(r["artifact_id"] for r in receipts)
    owner_id_set = set(owner_ids)
    external_ids = sorted(artifact_id for artifact_id in artifact_ids
                          if artifact_id not in owner_id_set
                          and index["artifacts"][artifact_id]["repository"]["kind"] == "lake-git")
    repository_runtime_ids = sorted(artifact_id for artifact_id in artifact_ids
                                    if artifact_id not in owner_id_set
                                    and index["artifacts"][artifact_id]["repository"]["kind"] == "baseline")
    direct_ids = set()
    set_ids = set()
    for receipt in receipts:
        set_ids.add(receipt["dependency_set"])
        root_entry = index["roots"].get(receipt["module"])
        need(root_entry is not None, "missing registry root evidence for owner")
        need(root_entry["root_id"] == receipt["root_id"], "registry evidence root mismatch")
        set_ids.add(root_entry["dependency_set"])
        for module in root_entry["direct_modules"]:
            need(module in module_ids, f"direct dependency absent from selected artifact set: {module}")
            direct_ids.add(module_ids[module])
    dependency_sets = []
    for set_id in sorted(set_ids):
        members = dependency_members(index, set_id)
        dependency_sets.append({"dependency_set_id": set_id, "artifact_count": len(members),
                                "members_digest": digest(members)})
    return {"evidence_type": "completion-artifact-registry-summary", "schema_version": REGISTRY_VERSION,
            "lean_version": index["lean_version"], "manifest": index["manifest"],
            "artifact_count": len(artifact_ids), "artifact_set_digest": artifact_set_digest(index, artifact_ids),
            "dependency_policy": policy,
            "artifact_classes": {
                "focused_owner": {"claim": "focused-source-elaboration", "artifact_count": len(owner_ids),
                                  "members_digest": digest(owner_ids)},
                "manifest_pinned_external": {"claim": "dependency-trust-not-source-build",
                                             "artifact_count": len(external_ids),
                                             "members_digest": digest(external_ids)},
                "repository_runtime": {"claim": "runtime-dependency-not-material-claim-evidence",
                                       "artifact_count": len(repository_runtime_ids),
                                       "members_digest": digest(repository_runtime_ids)}},
            "repositories": repositories, "dependency_sets": dependency_sets,
            "selected_owner_artifacts": [{"artifact_id": artifact_id, "metadata": index["artifacts"][artifact_id]}
                                         for artifact_id in owner_ids],
            "direct_dependency_artifacts": [{"artifact_id": artifact_id, "metadata": index["artifacts"][artifact_id]}
                                            for artifact_id in sorted(direct_ids)]}


def collect(repo, mapping_path, receipt_paths, output, base="origin/main", registry=None):
    need(registry is not None, "registry is required by the dependency policy")
    mapping = read(mapping_path)
    validate_map(mapping)
    validate_mapping_repository(repo, mapping)
    snap = snapshot(repo)
    head = snap["head"]
    mapping_ref = blob(repo, head, mapping_path)
    goal = blob(repo, head, mapping["goal_path"])
    report = blob(repo, head, mapping["report_path"])
    receipts = [read(p) for p in receipt_paths]
    need(receipts, "no focused receipts")
    registry = Path(registry).resolve()
    rows = [validate_registry_receipt(repo, registry, r) for r in receipts]
    modules = sorted(r["module"] for r in receipts)
    _, index_path, _ = registry_paths(registry)
    index = read(index_path)
    artifact_ids = sorted(set(a for r in receipts for a in
                              [r["artifact_id"], *dependency_members(index, r["dependency_set"])]))
    index = validate_registry(repo, registry, artifact_ids)
    distinct(modules, "receipt modules")
    for row in rows:
        need(row["repository"]["kind"] == "baseline", "selected owner must belong to baseline repository")
        need(not PLACEHOLDER.search((repo / row["source"]["path"]).read_text()), "placeholder scan failed")
    extractor = "research/lean/ResearchLean/Tools/CompletionAudit.lean"
    extractor_ref = blob(repo, head, extractor)
    environment = registry_environment(repo, registry, artifact_ids)
    with environment as env:
        result = run(["lean", "--run", extractor, *modules], repo, env)
    extraction = json.loads(result, object_pairs_hook=unique_pairs)
    repository_artifacts = repository_artifact_context(index, artifact_ids, receipts)
    core = material(mapping, extraction, (repo / goal["path"]).read_text(), repository_artifacts)
    source = {"snapshot": snap, "base_oid": run(["git", "rev-parse", base + "^{commit}"], repo),
              "goal": goal, "report": report, "mapping": mapping_ref,
              "extractor": extractor_ref, "generator_sha256": file_hash(__file__)}
    bundle = {"schema_version": VERSION, "source": source, "mapping": mapping,
              "extraction": extraction, "receipts": receipts, "core": core}
    bundle["registry"] = {"path": relative(repo, registry), "artifact_ids": artifact_ids,
                          "artifact_set_digest": artifact_set_digest(index, artifact_ids),
                          "evidence": registry_evidence(index, artifact_ids, receipts,
                                                        mapping["dependency_policy"])}
    write(output, bundle)
    return bundle


def validate_bundle(repo, b):
    fields(b, ["schema_version", "source", "mapping", "extraction", "receipts", "core", "registry"])
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
    validate_map(b["mapping"])
    validate_mapping_repository(repo, b["mapping"])
    fields(b["registry"], ["path", "artifact_ids", "artifact_set_digest", "evidence"])
    registry = repo / relative(repo, b["registry"]["path"])
    artifact_ids = b["registry"]["artifact_ids"]
    index = validate_registry(repo, registry, artifact_ids)
    need(b["registry"]["artifact_set_digest"] == artifact_set_digest(index, artifact_ids),
         "bundle registry artifact set mismatch")
    need(b["registry"]["evidence"] == registry_evidence(index, artifact_ids, b["receipts"],
                                                          b["mapping"]["dependency_policy"]),
         "bundle registry evidence mismatch")
    for r in b["receipts"]:
        validate_registry_receipt(repo, registry, r)
    environment = registry_environment(repo, registry, artifact_ids)
    need(sorted(r["module"] for r in b["receipts"]) == b["extraction"]["modules"], "extract scope mismatch")
    # Re-extract from the checked artifacts; a consistent edit of bundle/core is not evidence.
    with environment as env:
        actual = json.loads(run(["lean", "--run", b["source"]["extractor"]["path"], *b["extraction"]["modules"]], repo, env))
    need(actual == b["extraction"], "extraction differs from Lean artifacts")
    core = material(b["mapping"], b["extraction"], (repo / b["source"]["goal"]["path"]).read_text(),
                    repository_artifact_context(index, artifact_ids, b["receipts"]))
    need(core == b["core"], "core was edited")


def _render_validated(bundle, auxiliary):
    need("registry" in bundle, "registry is required by the dependency policy")
    fields(auxiliary, ["notes", "refs"])
    need(isinstance(auxiliary["notes"], str), "notes type")
    need(isinstance(auxiliary["refs"], list), "aux refs type")
    for ref in auxiliary["refs"]:
        string(ref)
    packet = {"packet_type": "target_theorem_final_review", "schema_version": VERSION,
              "head_oid": bundle["source"]["snapshot"]["head"], "base_oid": bundle["source"]["base_oid"],
              "goal": bundle["mapping"]["goal"],
              "source_digest": digest(bundle["source"]), "claim_map_digest": digest(bundle["mapping"]),
              "core_evidence_digest": digest({"extraction": bundle["extraction"], "core": bundle["core"],
                                                "receipts": bundle["receipts"],
                                                "registry": bundle.get("registry")}),
              "bundle_digest": digest(bundle), "core": bundle["core"], "auxiliary": auxiliary}
    return packet


def render(repo, bundle, auxiliary):
    """Validate every live input before rendering a public completion packet."""
    validate_bundle(repo, bundle)
    return _render_validated(bundle, auxiliary)


def _validate_packet_generated(bundle, packet):
    need(packet == _render_validated(bundle, packet.get("auxiliary", {})),
         "packet differs from generated result")


def validate_packet(repo, bundle, packet):
    """Validate the live bundle and exact generated packet."""
    validate_bundle(repo, bundle)
    _validate_packet_generated(bundle, packet)


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


def _ledger_validated(packet, review, gates, recheck=None, old=None):
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


def ledger(repo, bundle, packet, review, gates, recheck=None, old=None):
    """Validate packet and stored review evidence before emitting a proved ledger."""
    validate_packet(repo, bundle, packet)
    for row in review["lane_evidence"].values():
        resolve_evidence(repo, row["ref"])
    for row in gates["stage_evidence"].values():
        resolve_evidence(repo, row["ref"])
    if recheck:
        resolve_evidence(repo, recheck["evidence"])
    return _ledger_validated(packet, review, gates, recheck, old)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    sub = p.add_subparsers(dest="command", required=True)
    c = sub.add_parser("index")
    c.add_argument("--source", required=True)
    c.add_argument("--module", required=True)
    c.add_argument("--registry", required=True)
    c = sub.add_parser("check")
    c.add_argument("--source", required=True)
    c.add_argument("--module", required=True)
    c.add_argument("--out", required=True)
    c.add_argument("--registry", required=True)
    c.add_argument("--dependency-receipt", action="append", default=[])
    c = sub.add_parser("collect")
    c.add_argument("--mapping", required=True)
    c.add_argument("--receipt", action="append", required=True)
    c.add_argument("--out", required=True)
    c.add_argument("--base", default="origin/main")
    c.add_argument("--registry", required=True)
    for command in ("render", "validate", "ledger"):
        c = sub.add_parser(command)
        c.add_argument("--bundle", required=True)
        c.add_argument("--packet", required=True)
        c.add_argument("--registry", required=True)
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
    if a.command == "index":
        index_dependencies(repo, a.source, a.module, a.registry)
    elif a.command == "check":
        r = check_registry(repo, a.source, a.module, a.out, a.registry, a.dependency_receipt)
        write(repo / relative(repo, Path(a.out) / (a.module + ".receipt.json")), r)
    elif a.command == "collect":
        collect(repo, a.mapping, a.receipt, a.out, a.base, a.registry)
    elif a.command == "route":
        print(route_findings(read(a.old), read(a.new), read(a.review)))
    else:
        b = read(a.bundle)
        need(a.registry is not None, "--registry is required by the dependency policy")
        need(relative(repo, a.registry) == b["registry"]["path"], "explicit registry does not match bundle")
        if a.command == "render":
            packet = render(repo, b, read(a.auxiliary) if a.auxiliary else {"notes": "", "refs": []})
            write(a.packet, packet)
            Path(a.packet + ".md").write_text("```json\n" + json.dumps(packet, ensure_ascii=False, indent=2) + "\n```\n")
        else:
            packet = read(a.packet)
            if a.command == "validate":
                validate_packet(repo, b, packet)
            else:
                review, gates = read(a.review), read(a.gates)
                write(a.out, ledger(repo, b, packet, review, gates,
                                    read(a.recheck) if a.recheck else None,
                                    read(a.old_packet) if a.old_packet else None))
    print("ok")


if __name__ == "__main__":
    try:
        main()
    except (Invalid, OSError, ValueError, KeyError, TypeError) as error:
        print(f"completion audit failed: {error}", file=sys.stderr)
        sys.exit(1)
