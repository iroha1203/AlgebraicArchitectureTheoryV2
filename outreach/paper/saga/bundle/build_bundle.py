#!/usr/bin/env python3
"""saga-zenodo-bundle の組成スクリプト。

repository root から実行する。共通 CLI で paper PDF と build.json を生成しておく:
    python3 outreach/paper/_tools/paper.py build outreach/paper/saga/paper.json --out .tmp/saga-build
組成:
    python3 outreach/paper/saga/bundle/build_bundle.py --pdf .tmp/saga-build/build/main.pdf [--ci-run URL] [--out DIR]
--ci-run は公開時の証拠 commit に対応する CI run URL を指定する。
"""

import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import zipfile
import tempfile
from pathlib import Path

TAG = "saga-paper-v1.0.0"
DOI = "10.5281/zenodo.21605207"
CONCEPT_DOI = "10.5281/zenodo.21603761"
EVIDENCE_COMMIT = "5246d5326f01c0879f2305d9a7872d35e97c9380"
TOOL_VERSION = "0.5.4"
SCHEMA_VERSIONS = {
    "repairPlan": "archsig-repair-plan/v0.5.7",
    "runManifest": "archsig-run-manifest/v0.5.4",
}
EXPECTED = [
    ("head analyze", "MEASURED_NONGLUING_RESIDUAL", "run:78c31d6a3172"),
    ("repaired analyze", "REPAIR_GLUES_WITHIN_SELECTED_COMPLEX", "run:6685bab8db21"),
    ("compare head->repaired", "MEASURED_OBSTRUCTION_NO_LONGER_RECORDED_AFTER_CHANGE", "-"),
    ("gate head", "BLOCKED_BY_GATE_POLICY (nonzero exit code)", "-"),
    ("gate repaired", "PASS_WITHIN_GATE_POLICY", "-"),
]

REPRO_COMMANDS = """EV=<bundle>/evidence/saga
C=tools/archsig/Cargo.toml
cargo run --manifest-path $C -- analyze \\
  --archmap $EV/archmap-saga-head.json \\
  --law-policy $EV/law-policy-saga.json \\
  --law-surface $EV/law-surface-saga.json \\
  --measurement-profile $EV/measurement-profile-saga.json \\
  --repair-plan $EV/repair-plan-head.json \\
  --out-dir .tmp/repro/head
cargo run --manifest-path $C -- analyze \\
  --archmap $EV/archmap-saga-repaired.json \\
  --law-policy $EV/law-policy-saga.json \\
  --law-surface $EV/law-surface-saga.json \\
  --measurement-profile $EV/measurement-profile-saga.json \\
  --repair-plan $EV/repair-plan-repaired.json \\
  --out-dir .tmp/repro/repaired
cargo run --manifest-path $C -- compare \\
  --base-run .tmp/repro/head \\
  --head-run .tmp/repro/repaired \\
  --out-dir .tmp/repro/compare
cargo run --manifest-path $C -- gate \\
  --packet .tmp/repro/head/archsig-measurement-packet.json \\
  --policy $EV/gate-policy-saga.json \\
  --out .tmp/repro/gate-head.json
cargo run --manifest-path $C -- gate \\
  --packet .tmp/repro/repaired/archsig-measurement-packet.json \\
  --policy $EV/gate-policy-saga.json \\
  --out .tmp/repro/gate-repaired.json"""


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", default=".tmp/saga-zenodo-bundle")
    ap.add_argument("--ci-run", default=None,
                    help="公開時の固定 evidence commit の CI run URL")
    ap.add_argument("--pdf", default="outreach/paper/saga/en/main.pdf",
                    help="今回同梱する PDF。再生成版として manifest に hash を記録")
    ap.add_argument("--build-record", help="指定 PDF の build.json (共通ビルドなら自動検出)")
    args = ap.parse_args()

    root = Path.cwd()
    if not (root / "outreach/paper/saga/en/main.tex").exists():
        sys.exit("run from the repository root")
    pdf = Path(args.pdf).resolve()
    if not pdf.exists():
        sys.exit("build the PDF with the common CLI and pass --pdf")

    verify = [sys.executable, "outreach/paper/_tools/paper.py", "check",
              "outreach/paper/saga/paper.json", "--pdf", str(pdf)]
    if args.build_record:
        verify += ["--build-record", args.build_record]
    checked = subprocess.run(verify, capture_output=True, text=True)
    if checked.returncode:
        sys.exit("PDF/source verification failed: " + checked.stdout + checked.stderr)

    out = Path(args.out)
    if out.exists() or (out.parent / (out.name + ".zip")).exists():
        sys.exit("output already exists; choose a new --out")

    # 公開時の証拠と供給工程を固定 commit から取得する。
    tagged = subprocess.check_output(["git", "rev-parse", TAG + "^{commit}"], text=True).strip()
    if tagged != EVIDENCE_COMMIT:
        sys.exit("release tag does not match the recorded evidence commit")
    paths = ["docs/reports/train_ticket_dogfooding/evidence/saga",
             "docs/reports/train_ticket_dogfooding/saga_diagnosis.md",
             "tools/archsig/skills/archmap-creater",
             "outreach/paper/zenodo_claim_evidence_matrix.md"]
    temporary = tempfile.TemporaryDirectory(prefix="saga-evidence-")
    snapshot = Path(temporary.name)
    for prefix in paths:
        names = subprocess.check_output(["git", "ls-tree", "-r", "--name-only", EVIDENCE_COMMIT, "--", prefix], text=True).splitlines()
        if not names:
            sys.exit("missing historical source: " + prefix)
        for name in names:
            target = snapshot / name
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(subprocess.check_output(["git", "show", EVIDENCE_COMMIT + ":" + name]))

    # paper/: PDF + figures + bib(paper/ 直下)、tex source(paper/src/)。
    # src/ からの ../ 参照(bib・図)が paper/ 直下に解決される配置。
    paper = out / "paper"
    src = paper / "src"
    src.mkdir(parents=True)
    shutil.copy2(pdf, paper / "main.pdf")
    for fig in ["zenodo_saga_figure1_comparison.png", "zenodo_saga_figure2_one_cent.png"]:
        shutil.copy2(root / "outreach/paper/saga" / fig, paper / fig)
    shutil.copy2(root / "outreach/paper/saga/zenodo_saga_references.bib",
                 paper / "zenodo_saga_references.bib")
    for tex in sorted((root / "outreach/paper/saga/en").glob("*.tex")):
        shutil.copy2(tex, src / tex.name)

    # evidence/
    shutil.copytree(snapshot / "docs/reports/train_ticket_dogfooding/evidence/saga",
                    out / "evidence/saga")

    # report/
    (out / "report").mkdir()
    shutil.copy2(snapshot / "docs/reports/train_ticket_dogfooding/saga_diagnosis.md",
                 out / "report/saga_diagnosis.md")

    # reproduction/
    repro = out / "reproduction"
    repro.mkdir()
    shutil.copytree(snapshot / "tools/archsig/skills/archmap-creater",
                    repro / "archmap-creater")
    expected_rows = "\n".join(
        f"| {step} | `{concl}` | {rid} |" for step, concl, rid in EXPECTED)
    (repro / "README.md").write_text(f"""# Reproduction

Release identity: tag `{TAG}`, DOI `{DOI}`, ArchSig `{TOOL_VERSION}`,
schemas `{SCHEMA_VERSIONS['repairPlan']}` / `{SCHEMA_VERSIONS['runManifest']}`.

Historical evidence commit: `{EVIDENCE_COMMIT}`.
This is a local reconstruction; the paper source and supplied PDF are recorded
separately in the manifest. The historical audit describes the published snapshot.

1. Obtain the repository at the release tag:

```bash
git clone --branch {TAG} https://github.com/iroha1203/AlgebraicArchitectureTheoryV2
cd AlgebraicArchitectureTheoryV2
```

2. From the repository root, with `$EV` pointing at this bundle's
`evidence/saga` (byte-identical to
`docs/reports/train_ticket_dogfooding/evidence/saga` in the repository,
as certified by `MANIFEST.json`), run:

```bash
{REPRO_COMMANDS}
```

Note: `gate` exits nonzero on BLOCKED, so under `set -e` the sequence
stops at the head gate; run the invocations individually.

3. Expected outputs (agreement is checked by runId and verdict; the
`inputDigests` of the primary outputs use location-independent stable
references):

| Step | Conclusion | runId |
| --- | --- | --- |
{expected_rows}

The authoring process for the observation input (ArchMap) is documented
in `archmap-creater/` (the authoring SKILL); the canonical diagnosis
report with the condition matrix is `../report/saga_diagnosis.md`.
""")

    # audit/
    (out / "audit").mkdir()
    shutil.copy2(snapshot / "outreach/paper/zenodo_claim_evidence_matrix.md",
                 out / "audit/claim_evidence_matrix.md")

    # CITATION.md
    (out / "CITATION.md").write_text(f"""# Citation

Published evidence deposit (v1.0.0) version DOI: https://doi.org/{DOI}

Concept DOI: https://doi.org/{CONCEPT_DOI}

This locally reconstructed bundle combines the supplied PDF and current paper
sources with the historical evidence snapshot. Its hashes identify this build;
the DOI identifies the published deposit, not this reconstructed archive.

Cite the version DOI when referring to the verified evidence and Lean
status of this release; cite the concept DOI for the paper in general.

```
Nakahata, H. (2026). SAGA: A Comparison Theorem for Local-to-Global
Software Architecture. Zenodo. https://doi.org/{DOI}
```

License: CC BY 4.0.
""")

    # MANIFEST.json(自身を除く全ファイルの sha256)
    commit = subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True,
                            text=True, check=True).stdout.strip()
    files = {}
    for f in sorted(out.rglob("*")):
        if f.is_file():
            files[str(f.relative_to(out))] = sha256(f)
    manifest = {
        "schema": "saga-zenodo-bundle-manifest/v2",
        "kind": "local-reconstruction",
        "evidenceCommit": EVIDENCE_COMMIT,
        "paperSourceCommit": commit,
        "suppliedPdfSha256": sha256(pdf),
        "workingTreeDirty": bool(subprocess.check_output(
            ["git", "status", "--porcelain"], text=True).strip()),
        "releaseIdentity": {
            "tag": TAG,
            "tagVerified": True,
            "commit": EVIDENCE_COMMIT,
            "versionDoi": DOI,
            "license": "CC-BY-4.0",
            "archsigToolVersion": TOOL_VERSION,
            "schemaVersions": SCHEMA_VERSIONS,
            "releaseCiRun": args.ci_run,
        },
        "files": files,
    }
    (out / "MANIFEST.json").write_text(json.dumps(manifest, indent=2,
                                                  sort_keys=True) + "\n")
    # deposit 用 zip(単一アーカイブ)。Zenodo 等はディレクトリ構造を持たないため、
    # 構造付き bundle は必ず zip で upload する(flat upload は同名ファイルが衝突する)。
    zip_path = out.parent / (out.name + ".zip")
    with zipfile.ZipFile(zip_path, "w", zipfile.ZIP_DEFLATED) as z:
        for f in sorted(out.rglob("*")):
            if f.is_file():
                info = zipfile.ZipInfo(
                    str(Path(out.name) / f.relative_to(out)),
                    date_time=(2026, 7, 26, 0, 0, 0))
                info.external_attr = 0o644 << 16
                z.writestr(info, f.read_bytes())

    n = len(files)
    print(f"bundle built at {out} ({n} files + MANIFEST.json)")
    print(f"deposit zip: {zip_path} sha256={sha256(zip_path)}")
    print("local reconstruction; PDF/source hashes verified; complete submission review before publication")
    temporary.cleanup()
    return 0


if __name__ == "__main__":
    sys.exit(main())
