#!/usr/bin/env bash
set -euo pipefail

[ "$#" -eq 7 ] || {
  echo "usage: $0 BASE HEAD MANIFEST OLD_AUDIT NEW_AUDIT BATCH OUT_DIR" >&2
  exit 2
}

python3 - "$@" <<'PY'
import hashlib
import json
import pathlib
import re
import os
import subprocess
import sys

base_ref, head_ref, manifest_path, old_audit_path, new_audit_path, batch, out_arg = sys.argv[1:]
out_dir = pathlib.Path(out_arg)
test_mode = bool(os.environ.get("AAT_MIGRATION_TEST_PREFIXES"))
test_source_root = pathlib.Path(os.environ["AAT_MIGRATION_TEST_SOURCE_ROOT"]) if test_mode else None
old_prefix = "FixtureOld.AG" if test_mode else "Formal.AG." + "Research"
new_prefix = "FixtureNew.AG" if test_mode else "ResearchLean.AG"
if not re.fullmatch(r"R[34]", batch):
    print("E_MIGRATION_BATCH", file=sys.stderr); raise SystemExit(1)

def sha(value: str) -> str:
    return hashlib.sha256(value.encode()).hexdigest()

def read_audit(path: str):
    result = {}
    metadata = {}
    for number, raw in enumerate(pathlib.Path(path).read_text().splitlines(), 1):
        fields = raw.split("\t")
        if fields[0] == "MIGRATION_META":
            if len(fields) != 5:
                print(f"E_MIGRATION_META_FORMAT: {path}:{number}", file=sys.stderr); raise SystemExit(1)
            _, commit, module, source, source_digest = fields
            if module in metadata:
                print(f"E_MIGRATION_META_DUPLICATE: {module}", file=sys.stderr); raise SystemExit(1)
            metadata[module] = {"commit": commit, "source": source, "sourceDigest": source_digest}
            continue
        if len(fields) != 7 or fields[0] != "MIGRATION_DECL":
            print(f"E_MIGRATION_AUDIT_FORMAT: {path}:{number}", file=sys.stderr); raise SystemExit(1)
        _, module, name, levels, type_value, body, axioms = fields
        module_result = result.setdefault(module, {})
        if name in module_result:
            print(f"E_MIGRATION_DECL_DUPLICATE: {module}:{name}", file=sys.stderr); raise SystemExit(1)
        module_result[name] = {
            "levelDigest": sha(levels), "typeDigest": sha(type_value),
            "valueDigest": sha(body), "axiomSetDigest": sha(axioms), "axioms": axioms,
        }
    if not result or any(not declarations for declarations in result.values()):
        print("E_MIGRATION_AUDIT_EMPTY", file=sys.stderr); raise SystemExit(1)
    if not metadata:
        print("E_MIGRATION_META_MISSING", file=sys.stderr); raise SystemExit(1)
    return result, metadata

rows = []
for number, raw in enumerate(pathlib.Path(manifest_path).read_text().splitlines(), 1):
    if not raw or raw.startswith("#"): continue
    fields = raw.split("\t")
    if len(fields) != 4:
        print(f"E_MIGRATION_MANIFEST_FORMAT: line {number}", file=sys.stderr); raise SystemExit(1)
    old_source, new_source, old_module, new_module = fields
    if not old_module.startswith(old_prefix + ".") or not new_module.startswith(new_prefix + "."):
        print(f"E_MIGRATION_MODULE_MAPPING: line {number}", file=sys.stderr); raise SystemExit(1)
    old_suffix = old_module[len(old_prefix) + 1:].replace(".", "/") + ".lean"
    new_suffix = new_module[len(new_prefix) + 1:].replace(".", "/") + ".lean"
    expected_old = ("old/" if test_mode else "Formal/AG/" + "Research/") + old_suffix
    expected_new = "research-lean/ResearchLean/AG/" + new_suffix
    if old_source != expected_old or new_source != expected_new:
        print(f"E_MIGRATION_SOURCE_MODULE_PROVENANCE: line {number}", file=sys.stderr); raise SystemExit(1)
    rows.append((old_source, new_source, old_module, new_module))
if not rows:
    print("E_MIGRATION_MANIFEST_EMPTY", file=sys.stderr); raise SystemExit(1)

old_audits, old_metadata = read_audit(old_audit_path)
new_audits, new_metadata = read_audit(new_audit_path)
if set(old_audits) != set(new_audits):
    print("E_MIGRATION_DECLARATION_SET", file=sys.stderr); raise SystemExit(1)
expected_modules = {old_module.replace(old_prefix, "$RESEARCH") for _, _, old_module, _ in rows}
if set(old_audits) != expected_modules:
    print("E_MIGRATION_AUDIT_MODULE_SET", file=sys.stderr); raise SystemExit(1)
if set(old_metadata) != {row[2] for row in rows} or set(new_metadata) != {row[3] for row in rows}:
    print("E_MIGRATION_META_MODULE_SET", file=sys.stderr); raise SystemExit(1)

records = []
keys = set()
if test_mode:
    base_sha, head_sha = "TEST_BASE", "TEST_HEAD"
else:
    def resolve(ref):
        try: return subprocess.check_output(["git", "rev-parse", "--verify", ref + "^{commit}"], text=True).strip()
        except subprocess.CalledProcessError:
            print(f"E_MIGRATION_REF: {ref}", file=sys.stderr); raise SystemExit(2)
    base_sha, head_sha = resolve(base_ref), resolve(head_ref)

def source_at(ref, path):
    if test_mode:
        return (test_source_root / path).read_text()
    try: return subprocess.check_output(["git", "show", f"{ref}:{path}"], text=True)
    except subprocess.CalledProcessError:
        print(f"E_MIGRATION_SOURCE_MISSING: {ref}:{path}", file=sys.stderr); raise SystemExit(1)

for old_source, new_source, old_module, new_module in rows:
    canonical_module = old_module.replace(old_prefix, "$RESEARCH")
    if canonical_module != new_module.replace(new_prefix, "$RESEARCH"):
        print(f"E_MIGRATION_MODULE_MAPPING: {new_module}", file=sys.stderr); raise SystemExit(1)
    if canonical_module not in old_audits or canonical_module not in new_audits:
        print(f"E_MIGRATION_AUDIT_MODULE_MISSING: {canonical_module}", file=sys.stderr); raise SystemExit(1)
    old_audit = old_audits[canonical_module]
    new_audit = new_audits[canonical_module]
    if set(old_audit) != set(new_audit):
        print(f"E_MIGRATION_DECLARATION_SET: {canonical_module}", file=sys.stderr); raise SystemExit(1)
    old_text = source_at(base_sha, old_source)
    new_text = source_at(head_sha, new_source)
    for metadata, module, source, commit, text in (
        (old_metadata, old_module, old_source, base_sha, old_text),
        (new_metadata, new_module, new_source, head_sha, new_text),
    ):
        if module not in metadata:
            print(f"E_MIGRATION_META_MODULE_MISSING: {module}", file=sys.stderr); raise SystemExit(1)
        meta = metadata[module]
        raw_digest = hashlib.sha256(text.encode()).hexdigest()
        if meta["source"] != source or (not test_mode and (meta["commit"] != commit or meta["sourceDigest"] != raw_digest)):
            print(f"E_MIGRATION_META_PROVENANCE: {module}", file=sys.stderr); raise SystemExit(1)
    def canonical_source(text):
        text = text.replace("\r\n", "\n")
        for prefix in (old_prefix, new_prefix):
            text = re.sub(r"(?<![\w'.])" + re.escape(prefix) + r"\.", "$RESEARCH.", text)
        text = re.sub(r"(?<![\w/.-])Formal/AG/" + "Research/", "$RESEARCH_PATH/", text)
        text = re.sub(r"(?<![\w/.-])research-lean/ResearchLean/AG/", "$RESEARCH_PATH/", text)
        return text
    old_source_digest = sha(canonical_source(old_text))
    new_source_digest = sha(canonical_source(new_text))
    if old_source_digest != new_source_digest:
        print(f"E_MIGRATION_SOURCE_DIGEST: {new_source}", file=sys.stderr); raise SystemExit(1)
    prefix = "research-lean/ResearchLean/AG/"
    if not new_source.startswith(prefix):
        print(f"E_MIGRATION_NEW_SOURCE_PATH: {new_source}", file=sys.stderr); raise SystemExit(1)
    relative = new_source[len(prefix):]
    leaf_counts = {}
    for name in old_audit:
        leaf = name.rsplit(".", 1)[-1]
        leaf_counts[leaf] = leaf_counts.get(leaf, 0) + 1
    for name in sorted(old_audit):
        old = old_audit[name]; new = new_audit[name]
        if any(not old.get(field) or not new.get(field) for field in ("typeDigest", "valueDigest", "axiomSetDigest")):
            print("E_MIGRATION_DIGEST_MISSING", file=sys.stderr); raise SystemExit(1)
        if old != new:
            print(f"E_MIGRATION_DECLARATION_DIGEST: {name}", file=sys.stderr); raise SystemExit(1)
        leaf = name.rsplit(".", 1)[-1]
        research_root = "$RESEARCH."
        suffix = name[len(research_root):] if name.startswith(research_root) else name
        declaration_name = suffix if leaf_counts[leaf] > 1 else leaf
        key = f"{batch}/{relative}#{declaration_name}"
        if ("Formal.AG." + "Research") in key or "ResearchLean.AG" in key or "$RESEARCH" in key or not re.fullmatch(r"R[34]/[A-Za-z0-9_./'-]+\.lean#[A-Za-z0-9_.$']+", key):
            print(f"E_MIGRATION_RECORD_FORMAT: {key}", file=sys.stderr); raise SystemExit(1)
        if key in keys:
            print(f"E_MIGRATION_RECORD_DUPLICATE: {key}", file=sys.stderr); raise SystemExit(1)
        keys.add(key)
        records.append({"migration_record": key, "canonicalDeclaration": name, "sourceDigest": new_source_digest, **new})

out_dir.mkdir(parents=True, exist_ok=True)
(out_dir / "declarations.jsonl").write_text("".join(json.dumps(row, sort_keys=True) + "\n" for row in records))
(out_dir / "metadata.json").write_text(json.dumps({
    "schema": "aat-research-migration/v1", "batch": batch,
    "base": base_sha, "head": head_sha,
    "moduleCount": len(rows), "declarationCount": len(records),
}, sort_keys=True, indent=2) + "\n")
print(f"Research migration audit passed ({len(rows)} modules, {len(records)} declarations).")
PY
