"""原始項とソースの照合、二入力の独立性、ID 改名と入力変更の検算。"""

import ast
import copy
import hashlib
import importlib.util
import itertools
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

from calculate import Presentation, Record, calculate, key, read_json, wire


ROOT = Path(__file__).parent
A = read_json(ROOT / "game.archmap.json")
L = read_json(ROOT / "game.law.json")
result = calculate(A, L)
assert result["runStatus"] == "complete"
queries = {q["name"]: q for q in result["results"]}
operations = queries["operations"]["data"]
assert {k: len(operations[k]) for k in ("states", "inputs", "classes", "action")} == {
    "states": 58, "inputs": 192, "classes": 7, "action": 406}
candidates = {c["label"]: c for c in queries["recordings"]["data"]["candidates"]}
assert {k: v["status"] for k, v in candidates.items()} == {"keys": "refuted", "commands": "refuted", "events": "established"}
assert candidates["events"]["realizesCanonicalResolution"]

# calculate.py と二入力だけを置いた別ディレクトリで結果を生成する。
with tempfile.TemporaryDirectory(prefix="archsig-game-two-inputs-") as directory:
    isolated = Path(directory)
    for name in ("calculate.py", "game.archmap.json", "game.law.json"):
        shutil.copyfile(ROOT / name, isolated / name)
    subprocess.run([sys.executable, "calculate.py", "--archmap", "game.archmap.json", "--law", "game.law.json", "--out", "result.json"], cwd=isolated, check=True, capture_output=True)
    standalone = read_json(isolated / "result.json")
    assert {k: v for k, v in standalone.items() if k != "inputs"} == result
    assert standalone == read_json(ROOT / "expected" / "result.json")

# すべての参照 ID を置換する。意味を持つ列挙値・field 名・局所変数は変えない。
subjects = {a["subject"] for a in A["atoms"]}
atom_ids = {a["id"] for a in A["atoms"]}
source_ids = {s["id"] for s in A["sources"]}
all_ids = sorted(subjects | atom_ids | source_ids)
renaming = {old: f"renamed-{len(all_ids)-i:04}" for i, old in enumerate(all_ids)}


def rename_refs(value):
    if isinstance(value, dict):
        return {k: renaming[v] if k == "ref" else rename_refs(v) for k, v in value.items()}
    if isinstance(value, list):
        return [rename_refs(v) for v in value]
    return value


renamed = copy.deepcopy(A)
for a in renamed["atoms"]:
    a["id"], a["subject"] = renaming[a["id"]], renaming[a["subject"]]
    a["payload"] = rename_refs(a["payload"])
    a["sourceRefs"] = [renaming[s] for s in a["sourceRefs"]]
for s in renamed["sources"]:
    s["id"] = renaming[s["id"]]
renamed["atoms"].reverse()
renamed["sources"].reverse()
renamed_result = calculate(renamed, L)
inverse = {v: k for k, v in renaming.items()}


def restore(value):
    if isinstance(value, str):
        return inverse.get(value, value)
    if isinstance(value, dict):
        result = {k: restore(v) for k, v in value.items()}
        if "atomIds" in result:
            result["atomIds"].sort()
        return result
    if isinstance(value, list):
        return [restore(v) for v in value]
    return value


assert restore(renamed_result) == result

# ソース登録・式と、観測された役割・原始項を別の実行で照合する。
spec = importlib.util.spec_from_file_location("game_example_source", ROOT / "game.py")
source = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = source
spec.loader.exec_module(source)
source_ports = dict(source.MODEL_PORTS)
source_recorders = dict(source.RECORDERS)
tree = ast.parse((ROOT / "game.py").read_text())
nodes = {n.lineno: n for n in tree.body if isinstance(n, (ast.FunctionDef, ast.ClassDef))}
source_refs = {s["id"]: s for s in A["sources"]}
p = Presentation(A, L)


def source_object(value):
    if isinstance(value, Record):
        definition = p.definitions[value.type_id]
        ref = source_refs[definition["sourceRefs"][0]]
        record_name = nodes[ref["startLine"]].name
        return getattr(source, record_name)(*(source_object(v) for v in value.values))
    if isinstance(value, tuple):
        return tuple(source_object(v) for v in value)
    return value


for name, binding in L["bindings"].items():
    for choice in p.bound[name]:
        original = source_recorders[choice["label"]] if binding["cardinality"] == "many" else source_ports[binding["slot"]]
        ref = source_refs[p.definitions[choice["target"]]["sourceRefs"][0]]
        assert ref["startLine"] == original.__code__.co_firstlineno

action_query = L["queries"][0]
states = p.invoke(p.one(action_query["states"]["invoke"]), [])
inputs = p.invoke(p.one(action_query["inputs"]["invoke"]), [])
assert set(map(source_object, states)) == set(source_ports[L["bindings"][action_query["states"]["invoke"]]["slot"]]())
assert set(map(source_object, inputs)) == set(source_ports[L["bindings"][action_query["inputs"]["invoke"]]["slot"]]())
source_step = source_ports[L["bindings"][action_query["step"]]["slot"]]
for state, scenario in itertools.product(states, inputs):
    assert source_object(p.invoke(p.one(action_query["step"]), [state, scenario])) == source_step(source_object(state), source_object(scenario))
for binding in p.bound[L["queries"][1]["encoders"]]:
    for scenario in inputs:
        assert source_object(p.invoke(binding["target"], [scenario])) == source_recorders[binding["label"]](source_object(scenario))

# 候補一つの本体が欠けても、その候補を消さず、作用の構成を維持する。
selected = next(c for c in p.bound[L["queries"][1]["encoders"]] if c["label"] == "events")
definition_id = p.definitions[selected["target"]]["id"]
missing = copy.deepcopy(A)
missing["atoms"] = [a for a in missing["atoms"] if a["id"] != definition_id]
missing_result = calculate(missing, L)
assert missing_result["runStatus"] == "partial"
assert missing_result["results"][0]["data"] == operations
missing_candidates = {c["label"]: c for c in missing_result["results"][1]["data"]["candidates"]}
assert missing_candidates["events"]["status"] == "undetermined"
assert missing_candidates["events"]["issues"][0]["code"] == "missing_fact"
assert missing_candidates["keys"]["status"] == missing_candidates["commands"]["status"] == "refuted"

# 同じ Law のまま原始のダメージ式から bonus を取り除く。
# 6 類になり、「コマンドだけ」の候補が十分になる。7 類は計算器に埋めていない。
changed = copy.deepcopy(A)
replacements = [0]


def remove_bonus(value):
    if value == ["add", ["literal", 1], ["local", "damage_bonus"]]:
        replacements[0] += 1
        return ["literal", 1]
    if isinstance(value, list):
        return [remove_bonus(v) for v in value]
    if isinstance(value, dict):
        return {k: remove_bonus(v) for k, v in value.items()}
    return value


changed = remove_bonus(changed)
# if を純粋な項へ変換すると後続部分が各枝に現れるため、同じ式が複数ある。
assert replacements[0] > 0
changed_result = calculate(changed, L)
assert len(changed_result["results"][0]["data"]["classes"]) == 6
changed_candidates = {c["label"]: c for c in changed_result["results"][1]["data"]["candidates"]}
assert changed_candidates["commands"]["status"] == "established"
assert changed_candidates["commands"]["realizesCanonicalResolution"]
assert changed_candidates["events"]["status"] == "established"
assert not changed_candidates["events"]["realizesCanonicalResolution"]

# 非対応の項を「偽」、未解決参照を「欠落値」として処理しない。
unsupported = copy.deepcopy(A)
next(a for a in unsupported["atoms"] if a["id"] == definition_id)["payload"]["term"]["body"] = ["external_effect"]
unsupported_result = calculate(unsupported, L)
assert unsupported_result["results"][0]["data"] == operations
u = next(c for c in unsupported_result["results"][1]["data"]["candidates"] if c["label"] == "events")
assert u["status"] == "undetermined" and u["issues"][0]["code"] == "unsupported"
invalid = copy.deepcopy(A)
target_atom = next(a for a in invalid["atoms"] if a["subject"] == selected["usage"] and a["predicate"] == L["vocabulary"]["target"]["predicate"])
target_atom["payload"] = {"ref": "absent-declaration"}
assert calculate(invalid, L)["runStatus"] == "invalid_input"

report = {"two_input_isolation": "passed", "same_law_after_id_renaming": "passed", "renamed_identifiers": len(all_ids),
          "source_and_terms": {"states": len(states), "inputs": len(inputs), "step_comparisons": len(states) * len(inputs)},
          "derived_classes": len(operations["classes"]), "derived_action_rows": len(operations["action"]),
          "missing_candidate": "preserved_as_undetermined", "unsupported_candidate": "undetermined", "unresolved_reference": "invalid_input",
          "primitive_effect_change": {"classes": len(changed_result["results"][0]["data"]["classes"]), "commands": changed_candidates["commands"]["status"]},
          "law_sha256": hashlib.sha256((ROOT / "game.law.json").read_bytes()).hexdigest()}
print(json.dumps(report, ensure_ascii=False, indent=2))
