"""同じ有限 Map を二つの ArchSig バイナリで検査し、結果と実行時間を比較する。"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import statistics
import subprocess
import tempfile
import time


def write_inputs(directory, size):
    fixture = Path(__file__).resolve().parents[2] / "common" / "known_map.rs"
    definition = json.loads(
        re.search(r'DEFINITIONS: &str = r#"(.*?)"#;', fixture.read_text()).group(1)
    )
    vocabulary = definition["vocabularies"][0]
    vocabulary["declarations"].sort(key=lambda declaration: declaration["name"])
    canonical = json.dumps(vocabulary, separators=(",", ":"), sort_keys=True).encode()
    digest = "sha256:" + hashlib.sha256(canonical).hexdigest()

    def ref(index):
        return ["v", f"row-{index:03}"]

    subjects = [{"id": "s", "type": "Maps.Sample", "origin": "fixture"}]
    subjects += [
        {"id": ref(i)[1], "type": "Maps.Item", "origin": "fixture"} for i in range(size)
    ]
    rows = [[ref(i), ref((i + 1) % size)] for i in range(size)]
    atoms = [
        {"id": name, "subject": "s", "field": f"Maps.Sample.{name}",
         "value": value, "origin": "fixture"}
        for name, value in [("m", rows), ("n", list(reversed(rows)))]
    ]
    archmap = {
        "format": "archsig.archmap/2",
        "semantics": "archsig/0.6.0",
        "vocabularies": [{"namespace": "Maps", "version": "1", "digest": digest}],
        "sources": [],
        "origins": [{"id": "fixture", "mode": "specification", "locations": [],
                     "method": "有限 Map の検索を比較する。", "note": "有限例。"}],
        "snapshots": [{"id": "v", "origin": "fixture", "subjects": subjects, "atoms": atoms}],
    }
    (directory / "d.json").write_text(json.dumps(definition), encoding="utf-8")
    (directory / "a.json").write_text(json.dumps(archmap), encoding="utf-8")
    (directory / "l.law").write_text(
        f'''law "archsig.law/2" semantics "archsig/0.6.0";
reading R {{
    use vocabulary Maps version "1" digest "{digest}";
    view repeated(s:Maps.Sample,x:Maps.Item):Bool = let f=s.m in f(f(x))=s.n(f(x));
    law required equal(s:Maps.Sample):s.m=s.n;
}}
''',
        encoding="utf-8",
    )


def measure(binary, directory, size):
    command = [
        binary, "run", "--atom-definition", "d.json", "--archmap", "a.json",
        "--law", "l.law", "--ask", "eq=check(R.equal,bind.s=@v/s)",
    ]
    for index in range(size):
        command += ["--ask", f"p{index}=evaluate(R.repeated,bind.s=@v/s,bind.x=@v/row-{index:03})"]
    timings = []
    result = None
    for _ in range(4):
        start = time.perf_counter()
        run = subprocess.run(command, cwd=directory, capture_output=True, check=True, timeout=20)
        timings.append(time.perf_counter() - start)
        receipt = json.loads(run.stdout)
        assert receipt["status"] == "complete"
        assert len(receipt["answers"]) == size + 1
        assert all(answer["status"] == "established" for answer in receipt["answers"])
        assert all(answer["outputs"]["value"]["value"] is True for answer in receipt["answers"][1:])
        if result is None:
            result = receipt
        assert result == receipt
    return result, round(1000 * statistics.median(timings[1:]), 2)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("before", type=Path)
    parser.add_argument("after", type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="archsig-map-index-") as tmp:
        directory = Path(tmp)
        for size in [8, 16, 32]:
            write_inputs(directory, size)
            before, before_ms = measure(args.before.resolve(), directory, size)
            after, after_ms = measure(args.after.resolve(), directory, size)
            assert before == after
            print(f"{size:2d} 行  {before_ms:8.2f} ms → {after_ms:8.2f} ms")


if __name__ == "__main__":
    main()
