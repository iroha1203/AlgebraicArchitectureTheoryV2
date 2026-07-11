#!/usr/bin/env bash
set -euo pipefail

repo_root="$(git rev-parse --show-toplevel 2>/dev/null || pwd)"
scan_root="$repo_root"

if [ "${1:-}" = "--root" ]; then
  if [ "$#" -ne 2 ]; then
    echo "usage: $0 [--root REPOSITORY_ROOT]" >&2
    exit 2
  fi
  scan_root="$2"
elif [ "$#" -ne 0 ]; then
  echo "usage: $0 [--root REPOSITORY_ROOT]" >&2
  exit 2
fi

if ! command -v python3 >/dev/null 2>&1; then
  echo "E_IMPORT_GATE_RUNTIME: python3 is required" >&2
  exit 2
fi

python3 - "$scan_root" <<'PY'
from __future__ import annotations

import collections
import pathlib
import re
import sys

root = pathlib.Path(sys.argv[1]).resolve()
if not root.is_dir():
    print(f"E_IMPORT_GATE_ROOT: not a directory: {root}", file=sys.stderr)
    raise SystemExit(2)

roots = [root / "Formal.lean", root / "Main.lean", root / "ResearchLean.lean"]
for directory in (root / "Formal", root / "ResearchLean"):
    if directory.is_dir():
        roots.extend(directory.rglob("*.lean"))
files = sorted({path.resolve() for path in roots if path.is_file()})
if not files:
    print("E_IMPORT_GATE_EMPTY: no Lean modules found", file=sys.stderr)
    raise SystemExit(2)

def module_name(path: pathlib.Path) -> str:
    relative = path.relative_to(root).as_posix()
    return relative[:-5].replace("/", ".")

modules: dict[str, pathlib.Path] = {}
for path in files:
    name = module_name(path)
    if name in modules:
        print(f"E_DUPLICATE_MODULE: {name}", file=sys.stderr)
        raise SystemExit(2)
    modules[name] = path

def strip_comments(text: str) -> str:
    out: list[str] = []
    index = 0
    block_depth = 0
    while index < len(text):
        pair = text[index:index + 2]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                out.extend("  ")
                index += 2
            elif pair == "-/":
                block_depth -= 1
                out.extend("  ")
                index += 2
            else:
                out.append("\n" if text[index] == "\n" else " ")
                index += 1
        elif pair == "/-":
            block_depth = 1
            out.extend("  ")
            index += 2
        elif pair == "--":
            while index < len(text) and text[index] != "\n":
                out.append(" ")
                index += 1
        else:
            out.append(text[index])
            index += 1
    if block_depth:
        raise ValueError("unterminated block comment")
    return "".join(out)

import_re = re.compile(
    r"^\s*(?:(public)\s+)?(?:(meta)\s+)?import\s+(?:(all)\s+)?"
    r"([A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*)\s*$"
)
edges: dict[str, list[tuple[str, frozenset[str], int]]] = collections.defaultdict(list)
for source, path in modules.items():
    try:
        stripped = strip_comments(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, ValueError) as error:
        print(f"E_IMPORT_PARSE: {path.relative_to(root)}: {error}", file=sys.stderr)
        raise SystemExit(2)
    for line_number, line in enumerate(stripped.splitlines(), 1):
        if not re.match(r"^\s*(?:public\s+)?(?:meta\s+)?import\b", line):
            continue
        match = import_re.fullmatch(line)
        if not match:
            print(
                f"E_IMPORT_SYNTAX: {path.relative_to(root)}:{line_number}",
                file=sys.stderr,
            )
            raise SystemExit(2)
        public, meta, all_modifier, target = match.groups()
        modifiers = frozenset(
            name for name, present in (("public", public), ("meta", meta), ("all", all_modifier))
            if present
        )
        if target.startswith(("Formal.", "ResearchLean.")) and target not in modules:
            print(
                f"E_UNRESOLVED_LOCAL_IMPORT: {source} imports {target}",
                file=sys.stderr,
            )
            raise SystemExit(2)
        if target in modules:
            edges[source].append((target, modifiers, line_number))

def is_research(name: str) -> bool:
    legacy_prefix = "Formal.AG." + "Research"
    return (
        name == legacy_prefix
        or name.startswith(legacy_prefix + ".")
        or name == "ResearchLean.AG"
        or name.startswith("ResearchLean.AG.")
    )

def is_aggregate(name: str) -> bool:
    path = modules[name]
    return name in {"Formal", "Main", "ResearchLean"} or path.with_suffix("").is_dir()

violations: list[tuple[str, str, str]] = []
for start in sorted(name for name in modules if not is_research(name)):
    queue = collections.deque([(start, [start], [])])
    visited = {start}
    found = None
    while queue and found is None:
        current, path, path_modifiers = queue.popleft()
        for target, modifiers, _line in sorted(edges[current], key=lambda item: item[0]):
            next_path = path + [target]
            next_modifiers = path_modifiers + [modifiers]
            if is_research(target):
                found = (next_path, next_modifiers)
                break
            if target not in visited:
                visited.add(target)
                queue.append((target, next_path, next_modifiers))
    if found is None:
        continue
    path, path_modifiers = found
    if is_aggregate(start):
        kind = "aggregate"
    elif any("public" in modifiers for modifiers in path_modifiers):
        kind = "public"
    elif len(path) == 2:
        kind = "direct"
    else:
        kind = "indirect"
    violations.append((kind, start, " -> ".join(path)))

if violations:
    for kind, start, path in violations:
        print(f"E_RESEARCH_REACHABILITY kind={kind} root={start} path={path}", file=sys.stderr)
    raise SystemExit(1)

print(f"Research import direction gate passed ({len(modules)} modules scanned).")
PY
