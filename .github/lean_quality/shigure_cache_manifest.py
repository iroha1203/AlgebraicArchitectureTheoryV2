#!/usr/bin/env python3
"""Manage hash-verified SHIGURE build cache artifacts and audit stamps."""

from __future__ import annotations

import argparse
import hashlib
import os
from pathlib import Path
import sys

AUDIT_SOURCES = {
    "Formal/SHIGURE/AxiomAudit.lean",
    "Formal/SHIGURE/AssertStandardAxiomsTest.lean",
}
VALID_STATUSES = {"checked", "frontend"}
ARTIFACT_EXTS = (".olean.private", ".olean.server", ".olean", ".ilean", ".trace")


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def module_of_file(rel_path: str) -> str:
    if not rel_path.endswith(".lean"):
        raise ValueError(f"expected .lean path, got {rel_path}")
    return rel_path[:-5].replace("/", ".")


def artifact_base(build_root: Path, rel_path: str) -> Path:
    return build_root / rel_path[:-5]


def read_nul_files(path: Path) -> list[str]:
    raw = path.read_bytes()
    if not raw:
        return []
    return [chunk.decode("utf-8") for chunk in raw.split(b"\x00") if chunk]


def load_manifest(path: Path) -> dict[str, tuple[str, str, str, str, str]]:
    entries: dict[str, tuple[str, str, str, str, str]] = {}
    if not path.is_file():
        return entries
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line or line.startswith("#"):
            continue
        parts = line.split("\t")
        if len(parts) != 6:
            continue
        mod, status, src_h, trace_h, olean_h, priv_h = parts
        if status in VALID_STATUSES:
            entries[mod] = (status, src_h, trace_h, olean_h, priv_h)
    return entries


def current_hashes(rel_path: str, build_root: Path) -> tuple[str, str, str, str] | None:
    src = Path(rel_path)
    base = artifact_base(build_root, rel_path)
    trace = Path(f"{base}.trace")
    olean = Path(f"{base}.olean")
    priv = Path(f"{base}.olean.private")
    if not (src.is_file() and trace.is_file() and olean.is_file()):
        return None
    priv_h = sha256_file(priv) if priv.is_file() else "-"
    return (sha256_file(src), sha256_file(trace), sha256_file(olean), priv_h)


def remove_module_artifacts(build_root: Path, rel_path: str) -> int:
    base = artifact_base(build_root, rel_path)
    removed = 0
    for ext in ARTIFACT_EXTS:
        p = Path(f"{base}{ext}")
        if p.exists():
            p.unlink()
            removed += 1
    return removed


def cmd_prune(args: argparse.Namespace) -> int:
    files = read_nul_files(Path(args.files))
    build_root = Path(args.build_root)
    manifest = load_manifest(Path(args.manifest))

    tracked_bases: set[Path] = set()
    kept = 0
    invalidated = 0
    for rel in files:
        if rel in AUDIT_SOURCES:
            continue
        mod = module_of_file(rel)
        tracked_bases.add(artifact_base(build_root, rel).resolve())
        entry = manifest.get(mod)
        hashes = current_hashes(rel, build_root)
        if entry is not None and hashes is not None and entry[1:] == hashes:
            kept += 1
        else:
            if remove_module_artifacts(build_root, rel) > 0:
                invalidated += 1

    # Remove stale cached artifacts for deleted SHIGURE modules only.
    stale_removed = 0
    shigure_dir = build_root / "Formal" / "SHIGURE"
    candidates: list[Path] = []
    if shigure_dir.is_dir():
        for root, _, names in os.walk(shigure_dir):
            for name in names:
                candidates.append(Path(root) / name)
    formal_dir = build_root / "Formal"
    for ext in ARTIFACT_EXTS:
        p = formal_dir / f"SHIGURE{ext}"
        if p.is_file():
            candidates.append(p)

    for p in candidates:
        matched_ext = None
        for ext in ARTIFACT_EXTS:
            if p.name.endswith(ext):
                matched_ext = ext
                break
        if matched_ext is None:
            continue
        stem_path = Path(str(p)[: -len(matched_ext)]).resolve()
        if stem_path not in tracked_bases:
            p.unlink()
            stale_removed += 1

    print(
        f"SHIGURE cache prune: kept {kept} verified modules, "
        f"invalidated {invalidated} modules, removed {stale_removed} stale files."
    )
    return 0


def cmd_verify(args: argparse.Namespace) -> int:
    files = read_nul_files(Path(args.files))
    build_root = Path(args.build_root)
    stamps_dir = Path(args.stamps)
    manifest = load_manifest(Path(args.manifest))

    new_rows: list[tuple[str, str, str, str, str, str]] = []
    source_checks: list[str] = []
    fresh_count = 0
    reused_count = 0

    for rel in files:
        if rel in AUDIT_SOURCES:
            source_checks.append(rel)
            continue

        mod = module_of_file(rel)
        hashes = current_hashes(rel, build_root)
        if hashes is None:
            print(f"{rel}: missing compiled artifacts (.olean/.trace)", file=sys.stderr)
            return 1

        stamp_file = stamps_dir / mod
        if stamp_file.is_file():
            audit_status = stamp_file.read_text(encoding="utf-8").strip()
            if audit_status not in VALID_STATUSES:
                print(f"{rel}: invalid source audit result", file=sys.stderr)
                return 1
            fresh_count += 1
        else:
            entry = manifest.get(mod)
            if entry is None or entry[1:] != hashes:
                print(
                    f"{rel}: the source audit did not reach the end of the file",
                    file=sys.stderr,
                )
                return 1
            audit_status = entry[0]
            reused_count += 1

        if audit_status == "frontend":
            source_checks.append(rel)
        new_rows.append((mod, audit_status, *hashes))

    new_rows.sort(key=lambda r: r[0])
    new_manifest_path = Path(args.new_manifest)
    new_manifest_path.parent.mkdir(parents=True, exist_ok=True)
    with new_manifest_path.open("w", encoding="utf-8") as f:
        for row in new_rows:
            f.write("\t".join(row) + "\n")

    source_checks_path = Path(args.source_checks_out)
    source_checks_path.parent.mkdir(parents=True, exist_ok=True)
    with source_checks_path.open("wb") as f:
        for rel in source_checks:
            f.write(rel.encode("utf-8") + b"\x00")

    print(
        f"SHIGURE audit stamps verified: {fresh_count} freshly built, "
        f"{reused_count} reused from verified cache, {len(source_checks)} frontend checks."
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)

    p_prune = sub.add_parser("prune")
    p_prune.add_argument("--files", required=True)
    p_prune.add_argument("--manifest", required=True)
    p_prune.add_argument("--build-root", required=True)
    p_prune.set_defaults(func=cmd_prune)

    p_verify = sub.add_parser("verify")
    p_verify.add_argument("--files", required=True)
    p_verify.add_argument("--manifest", required=True)
    p_verify.add_argument("--stamps", required=True)
    p_verify.add_argument("--build-root", required=True)
    p_verify.add_argument("--new-manifest", required=True)
    p_verify.add_argument("--source-checks-out", required=True)
    p_verify.set_defaults(func=cmd_verify)

    args = parser.parse_args()
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
