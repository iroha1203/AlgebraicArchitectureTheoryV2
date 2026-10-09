"""二入力から有限作用の商を再計算する、文書例の補助計算。

ゲームのソースや期待出力を import / 読込みしない。ArchSig の実装ではない。
"""

import argparse
import hashlib
import itertools
import json
from dataclasses import dataclass
from pathlib import Path


class Diagnostic(Exception):
    def __init__(self, code, detail, invalid=False):
        self.code, self.detail, self.invalid = code, detail, invalid
        super().__init__(f"{code}: {detail}")

    def issue(self):
        result = {"code": self.code, "message": str(self.detail)}
        if isinstance(self.detail, dict):
            result.update({k: v for k, v in self.detail.items()
                           if k in {"subject", "predicate", "atomIds", "location"}})
        return result


@dataclass(frozen=True)
class Record:
    type_id: str
    values: tuple


def wire(value):
    if isinstance(value, Record):
        return {"type": {"ref": value.type_id}, "values": [wire(v) for v in value.values]}
    if isinstance(value, frozenset):
        return {"set": [wire(v) for v in sorted(value, key=key)]}
    if isinstance(value, (tuple, list)):
        return [wire(v) for v in value]
    if isinstance(value, dict):
        return {"map": [[wire(k), wire(v)] for k, v in sorted(value.items(), key=lambda item: key(item[0]))]}
    return value


def key(value):
    return json.dumps(wire(value), ensure_ascii=False, sort_keys=True, separators=(",", ":"))


def unique(values):
    return [v for _, v in sorted({key(v): v for v in values}.items())]


def references(value):
    if isinstance(value, dict):
        if set(value) == {"ref"}:
            yield value["ref"]
        else:
            for item in value.values():
                yield from references(item)
    elif isinstance(value, list):
        for item in value:
            yield from references(item)


def strict_object(pairs):
    result = {}
    for name, value in pairs:
        if name in result:
            raise Diagnostic("duplicate_key", name, True)
        result[name] = value
    return result


def read_json(path):
    return json.loads(Path(path).read_text(), object_pairs_hook=strict_object)


class Presentation:
    def __init__(self, archmap, law):
        if archmap["schema"] != "archmap.atom/v1" or law["schema"] != "lawdsl.finite-action/v1":
            raise Diagnostic("unsupported_version", "input schema", True)
        if law["use"] != [{"module": "finite_terms", "version": 1}, {"module": "finite_action", "version": 1}]:
            raise Diagnostic("unsupported_version", "term/action semantics", True)
        self.law = law
        self.atoms = archmap["atoms"]
        ids = [a["id"] for a in self.atoms]
        if len(ids) != len(set(ids)):
            raise Diagnostic("duplicate_id", "atoms", True)
        self.used = set()
        self.stack = []
        self.constants = {}
        self.declarations = {a["subject"]: a for a in self.select("declarations")}
        self.definitions = {}
        for a in self.select("definitions"):
            if a["subject"] in self.definitions:
                raise Diagnostic("duplicate_field", a["subject"], True)
            if a["subject"] not in self.declarations:
                raise Diagnostic("unresolved_reference", a["subject"], True)
            self.definitions[a["subject"]] = a
        for a in self.atoms:
            for ref in references(a["payload"]):
                if ref not in self.declarations:
                    raise Diagnostic("unresolved_reference", ref, True)
        self.bound = {}
        for name, rule in law["bindings"].items():
            choices = []
            for use in self.select("usages"):
                slot = self.field(use["subject"], "slot")
                if slot["payload"]["enum"] != rule["slot"]:
                    continue
                target = self.field(use["subject"], "target")
                label = self.field(use["subject"], "label")
                choices.append({"usage": use["subject"], "target": target["payload"]["ref"], "label": label["payload"]["enum"]})
                self.used.update((use["id"], slot["id"], target["id"], label["id"]))
            if rule["cardinality"] == "one" and len(choices) != 1:
                raise Diagnostic("missing_binding" if not choices else "ambiguous_binding", {"binding": name, "count": len(choices)})
            if rule["cardinality"] not in {"one", "many"}:
                raise Diagnostic("invalid_binding", name, True)
            self.bound[name] = sorted(choices, key=lambda c: (c["label"], c["usage"]))

    def select(self, selector):
        spec = self.law["vocabulary"][selector]
        return [a for a in self.atoms if all(a.get(k) == v for k, v in spec.items())]

    def field(self, subject, selector):
        found = [a for a in self.select(selector) if a["subject"] == subject]
        if len(found) != 1:
            raise Diagnostic("missing_fact" if not found else "duplicate_field", {"subject": subject, "field": selector}, bool(found))
        return found[0]

    def definition(self, ref):
        if ref not in self.definitions:
            raise Diagnostic("missing_fact", {"subject": ref, "predicate": self.law["vocabulary"]["definitions"]["predicate"]})
        a = self.definitions[ref]
        self.used.update((a["id"], self.declarations[ref]["id"]))
        return a["payload"]["term"]

    def one(self, binding):
        choices = self.bound[binding]
        if len(choices) != 1:
            raise Diagnostic("ambiguous_binding", binding)
        return choices[0]["target"]

    def law_value(self, expression, variables):
        if set(expression) == {"variable"}:
            return variables[expression["variable"]]
        if set(expression) == {"invoke", "arguments"}:
            return self.invoke(self.one(expression["invoke"]), [self.law_value(a, variables) for a in expression["arguments"]])
        raise Diagnostic("unsupported", "Law evaluation expression")

    def matches(self, value, value_type):
        if isinstance(value_type, dict):
            return isinstance(value, Record) and value.type_id == value_type["ref"]
        return {"Infer": lambda: True, "Int": lambda: isinstance(value, int) and not isinstance(value, bool),
                "String": lambda: isinstance(value, str), "Tuple": lambda: isinstance(value, tuple),
                "Bool": lambda: isinstance(value, bool)}[value_type]()

    def invoke(self, ref, args):
        d = self.definition(ref)
        if d["form"] == "record":
            fields = d["fields"]
            if len(args) > len(fields):
                raise Diagnostic("type_error", ref, True)
            vals = tuple(args[i] if i < len(args) else self.evaluate(f["default"], {}) for i, f in enumerate(fields))
            if not all(self.matches(v, f["type"]) for v, f in zip(vals, fields)):
                raise Diagnostic("type_error", ref, True)
            return Record(ref, vals)
        if d["form"] != "function" or len(args) != len(d["parameters"]):
            raise Diagnostic("type_error", ref, True)
        if not all(self.matches(v, p["type"]) for v, p in zip(args, d["parameters"])):
            raise Diagnostic("type_error", ref, True)
        if ref in self.stack:
            raise Diagnostic("unsupported", {"recursive_operation": ref})
        self.stack.append(ref)
        try:
            result = self.evaluate(d["body"], {p["name"]: v for p, v in zip(d["parameters"], args)})
            if not self.matches(result, d["resultType"]):
                raise Diagnostic("type_error", ref, True)
            return result
        finally:
            self.stack.pop()

    def evaluate(self, term, env):
        op, *args = term
        if op == "literal":
            return args[0]
        if op == "local":
            return env[args[0]]
        if op == "global":
            ref = args[0]["ref"]
            d = self.definition(ref)
            if d["form"] != "constant":
                raise Diagnostic("type_error", ref, True)
            if ref not in self.constants:
                if ref in self.stack:
                    raise Diagnostic("unsupported", {"recursive_constant": ref})
                self.stack.append(ref)
                try:
                    self.constants[ref] = self.evaluate(d["value"], {})
                finally:
                    self.stack.pop()
            return self.constants[ref]
        if op == "field":
            record = self.evaluate(args[0], env)
            fields = self.definition(record.type_id)["fields"]
            index = next(i for i, f in enumerate(fields) if f["name"] == args[1])
            return record.values[index]
        if op in {"tuple", "finite_set"}:
            return (tuple if op == "tuple" else frozenset)(self.evaluate(a, env) for a in args)
        if op == "finite_map":
            return {self.evaluate(k, env): self.evaluate(v, env) for k, v in args[0]}
        if op == "lookup":
            return self.evaluate(args[0], env)[self.evaluate(args[1], env)]
        if op == "if":
            condition = self.evaluate(args[0], env)
            if not isinstance(condition, bool):
                raise Diagnostic("type_error", "if condition", True)
            return self.evaluate(args[1] if condition else args[2], env)
        if op == "let":
            return self.evaluate(args[2], {**env, args[0]: self.evaluate(args[1], env)})
        if op in {"all", "any"}:
            return (all if op == "all" else any)(self.evaluate(a, env) for a in args)
        if op == "collect":
            ranges, guard, body = args
            def visit(index, local):
                if index == len(ranges):
                    if self.evaluate(guard, local):
                        yield self.evaluate(body, local)
                    return
                name, values = ranges[index]
                for value in sorted(self.evaluate(values, local), key=key):
                    yield from visit(index + 1, {**local, name: value})
            return tuple(visit(0, env))
        if op == "record_copy":
            record = self.evaluate(args[0], env)
            fields = self.definition(record.type_id)["fields"]
            updates = {name: self.evaluate(t, env) for name, t in args[1].items()}
            if not set(updates) <= {f["name"] for f in fields}:
                raise Diagnostic("type_error", "unknown record field", True)
            vals = tuple(updates.get(f["name"], v) for f, v in zip(fields, record.values))
            if not all(self.matches(v, f["type"]) for v, f in zip(vals, fields)):
                raise Diagnostic("type_error", "record update", True)
            return Record(record.type_id, vals)
        if op == "apply":
            return self.invoke(args[0]["ref"], [self.evaluate(a, env) for a in args[1]])
        if op == "builtin":
            if args[0] not in {"abs", "max"}:
                raise Diagnostic("unsupported", args[0])
            values = [self.evaluate(a, env) for a in args[1]]
            return {"abs": abs, "max": max}[args[0]](*values)
        if op == "negate":
            return -self.evaluate(args[0], env)
        if op not in {"add", "subtract", "multiply", "equal", "different", "greater", "member"}:
            raise Diagnostic("unsupported", op)
        a, b = [self.evaluate(t, env) for t in args]
        return {"add": lambda: a + b, "subtract": lambda: a - b, "multiply": lambda: a * b,
                "equal": lambda: a == b, "different": lambda: a != b, "greater": lambda: a > b,
                "member": lambda: a in b}[op]()


def quotient(p, query):
    declared_evaluation = {"invoke": query["reading"], "arguments": [{"invoke": query["step"], "arguments": [{"variable": "state"}, {"variable": "input"}]}]}
    if query["evaluation"] != declared_evaluation:
        raise Diagnostic("unsupported", "finite_action/1 requires the reading of the declared step")
    states = unique(p.invoke(p.one(query["states"]["invoke"]), []))
    inputs = unique(p.invoke(p.one(query["inputs"]["invoke"]), []))
    if not states or not inputs:
        raise Diagnostic("empty_domain", {"states": len(states), "inputs": len(inputs)})
    step, reading = p.one(query["step"]), p.one(query["reading"])
    observed = [p.invoke(reading, [s]) for s in states]
    if len({key(v) for v in observed}) != len(states):
        raise Diagnostic("condition_failed", "state reading is not injective")
    index = {key(s): i for i, s in enumerate(states)}
    table = []
    signatures = []
    for u in inputs:
        images = [p.invoke(step, [s, u]) for s in states]
        if any(key(t) not in index for t in images):
            raise Diagnostic("condition_failed", "step does not preserve the state domain")
        table.append(tuple(index[key(t)] for t in images))
        signatures.append(tuple(key(p.law_value(query["evaluation"], {"state": s, "input": u})) for s in states))
    grouped = {}
    for i, sig in enumerate(signatures):
        grouped.setdefault(sig, []).append(i)
    groups = [grouped[sig] for sig in sorted(grouped)]
    class_of = {u: c for c, members in enumerate(groups) for u in members}
    action = [table[members[0]] for members in groups]
    # 読取りの単射性と閉性を検査した後、代表によらない作用を直接再照合する。
    for u, image in enumerate(table):
        if image != action[class_of[u]]:
            raise Diagnostic("condition_failed", "representative dependence")
    public = {"states": [{"id": f"g{i}", "value": wire(s), "reading": wire(observed[i])} for i, s in enumerate(states)],
              "inputs": [{"id": f"u{i}", "value": wire(u)} for i, u in enumerate(inputs)],
              "classes": [{"id": f"q{c}", "members": [f"u{i}" for i in members], "representative": f"u{members[0]}"} for c, members in enumerate(groups)],
              "action": [{"state": f"g{s}", "operation": f"q{c}", "nextState": f"g{image[s]}"} for c, image in enumerate(action) for s in range(len(states))],
              "evaluationCount": len(states) * len(inputs),
              "conditions": {"nonemptyDomains": True, "injectiveStateReading": True, "closedStateDomain": True, "representativeIndependent": True},
              "finiteSequenceGuarantee": {"rule": "finite_action/1:factorization_induction", "initialStates": "states", "inputAlphabet": "inputs"}}
    return public, {"states": states, "inputs": inputs, "table": table, "groups": groups, "class_of": class_of, "action": action}


def compare_encodings(p, query, action):
    findings = []
    for binding in p.bound[query["encoders"]]:
        try:
            values = [p.invoke(binding["target"], [u]) for u in action["inputs"]]
            fibers = {}
            for i, value in enumerate(values):
                fibers.setdefault(key(value), []).append(i)
            witness = None
            for indices in fibers.values():
                for i, j in itertools.combinations(indices, 2):
                    if action["class_of"][i] != action["class_of"][j]:
                        state = next(s for s in range(len(action["states"])) if action["table"][i][s] != action["table"][j][s])
                        witness = {"state": f"g{state}", "inputs": [f"u{i}", f"u{j}"], "sameEncoding": wire(values[i]),
                                   "nextStates": [f"g{action['table'][i][state]}", f"g{action['table'][j][state]}"]}
                        break
                if witness:
                    break
            exact = {frozenset(x) for x in fibers.values()} == {frozenset(x) for x in action["groups"]}
            findings.append({**binding, "status": "refuted" if witness else "established", "fiberCount": len(fibers),
                             "realizesCanonicalResolution": exact, "counterexample": witness,
                             "classEncodings": [{"class": f"q{c}", "values": [wire(v) for v in unique(values[i] for i in members)]} for c, members in enumerate(action["groups"])], "issues": []})
        except Diagnostic as error:
            if error.invalid:
                raise
            findings.append({**binding, "status": "undetermined", "issues": [error.issue()]})
    return {"candidates": findings}


def compositions(action):
    pairs = []
    for a, b in itertools.combinations(range(len(action["groups"])), 2):
        first, second = action["action"][a], action["action"][b]
        witness = next((s for s in range(len(action["states"])) if second[first[s]] != first[second[s]]), None)
        pairs.append({"operations": [f"q{a}", f"q{b}"], "commutes": witness is None,
                      "counterexample": None if witness is None else {"state": f"g{witness}", "firstThenSecond": f"g{second[first[witness]]}", "secondThenFirst": f"g{first[second[witness]]}"}})
    return {"pairs": pairs}


def calculate(archmap, law):
    result = {"schema": "archsig.engine.result/v1", "engine": {"interface": "proposal/1", "semantics": "finite_action/1"},
              "requestedQueries": [q["name"] for q in law["queries"]], "runStatus": "complete", "results": [], "issues": [],
              "reuse": {"source": None, "status": "not_requested"}}
    try:
        p = Presentation(archmap, law)
        actions = {}
        for query_index, q in enumerate(law["queries"]):
            law_refs = ["/vocabulary", "/bindings", f"/queries/{query_index}"]
            if "law" in q:
                law_refs.append(f"/laws/{q['law']}")
            try:
                if q["operator"] == "finite_action_quotient":
                    data, actions[q["name"]] = quotient(p, q)
                    data["bindings"] = p.bound
                    action_name = q["name"]
                elif q["operator"] in {"compare_encodings", "compare_compositions"}:
                    if q["operator"] == "compare_encodings":
                        requirement = law["laws"][q["law"]]
                        if requirement["operator"] != "factors_action" or requirement["quantification"] != "all_finite_states_and_inputs":
                            raise Diagnostic("unsupported", "recording Law")
                        action_name = requirement["action"]
                    else:
                        action_name = q["action"]
                    if action_name not in actions:
                        raise Diagnostic("missing_derivation", action_name)
                    a = actions[action_name]
                    data = compare_encodings(p, q, a) if q["operator"] == "compare_encodings" else compositions(a)
                else:
                    raise Diagnostic("unsupported", q["operator"])
                status = "undetermined" if any(c["status"] == "undetermined" for c in data.get("candidates", [])) else "established"
                active = actions[action_name]
                scope = {"family": "input", "domain": "finite", "action": action_name,
                         "stateCount": len(active["states"]), "inputCount": len(active["inputs"])}
                conditions = [{"name": name, "status": "established"} for name in ("nonempty_domains", "injective_state_reading", "closed_state_domain", "representative_independence")]
                result["results"].append({"name": q["name"], "analysis": q["operator"], "status": status,
                                          "scope": scope, "data": data,
                                          "evidence": {"atomIds": sorted(p.used), "lawDecls": law_refs, "builtinRules": [f"finite_action/1:{q['operator']}"]}, "conditions": conditions, "issues": []})
                if status == "undetermined":
                    result["runStatus"] = "partial"
            except Diagnostic as error:
                if error.invalid:
                    raise
                result["runStatus"] = "partial"
                result["results"].append({"name": q["name"], "analysis": q["operator"], "status": "undetermined", "scope": {"family": "input", "domain": "unresolved"},
                                          "data": None, "evidence": {"atomIds": sorted(p.used), "lawDecls": law_refs, "builtinRules": []},
                                          "conditions": [{"name": "query_dependencies_available", "status": "undetermined"}],
                                          "issues": [error.issue()]})
    except Diagnostic as error:
        result["runStatus"] = "invalid_input" if error.invalid else "partial"
        result["results"] = []
        result["issues"] = [error.issue()]
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--archmap", type=Path, required=True)
    parser.add_argument("--law", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    archmap, law = read_json(args.archmap), read_json(args.law)
    result = calculate(archmap, law)
    result["inputs"] = {"archmap": {"file": args.archmap.name, "sha256": hashlib.sha256(args.archmap.read_bytes()).hexdigest(), "document": archmap["document"], "revision": archmap["revision"]},
                        "law": {"file": args.law.name, "sha256": hashlib.sha256(args.law.read_bytes()).hexdigest(), "module": law["module"], "version": law["version"]}}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("x") as f:
        json.dump(result, f, ensure_ascii=False, indent=2)
        f.write("\n")
    print(args.out)


if __name__ == "__main__":
    main()
