#!/usr/bin/env python3
"""saga-zenodo-bundle の組成スクリプト。

repository root から実行する。paper PDF は事前に tectonic でビルドしておく:
    cd outreach/paper/saga/en && tectonic main.tex
組成:
    python3 outreach/paper/saga/bundle/build_bundle.py [--ci-run URL] [--out DIR]
tag 押下後に --ci-run で release CI run URL を渡すと MANIFEST に記録される。
"""

import argparse
import hashlib
import json
import shutil
import subprocess
import sys
import zipfile
from pathlib import Path

TAG = "saga-paper-v1.0.0"
DOI = "10.5281/zenodo.21603762"
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
                    help="release CI run URL (tag 押下後に指定)")
    args = ap.parse_args()

    root = Path.cwd()
    if not (root / "outreach/paper/saga/en/main.tex").exists():
        sys.exit("run from the repository root")
    pdf = root / "outreach/paper/saga/en/main.pdf"
    if not pdf.exists():
        sys.exit("build the PDF first: cd outreach/paper/saga/en && tectonic main.tex")

    out = Path(args.out)
    if out.exists():
        shutil.rmtree(out)

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
    shutil.copytree(root / "docs/reports/train_ticket_dogfooding/evidence/saga",
                    out / "evidence/saga")

    # report/
    (out / "report").mkdir()
    shutil.copy2(root / "docs/reports/train_ticket_dogfooding/saga_diagnosis.md",
                 out / "report/saga_diagnosis.md")

    # reproduction/
    repro = out / "reproduction"
    repro.mkdir()
    shutil.copytree(root / "tools/archsig/skills/archmap-creater",
                    repro / "archmap-creater")
    expected_rows = "\n".join(
        f"| {step} | `{concl}` | {rid} |" for step, concl, rid in EXPECTED)
    (repro / "README.md").write_text(f"""# Reproduction

Release identity: tag `{TAG}`, DOI `{DOI}`, ArchSig `{TOOL_VERSION}`,
schemas `{SCHEMA_VERSIONS['repairPlan']}` / `{SCHEMA_VERSIONS['runManifest']}`.

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
    shutil.copy2(root / "outreach/paper/saga/zenodo_claim_evidence_matrix.md",
                 out / "audit/claim_evidence_matrix.md")

    # CITATION.md
    (out / "CITATION.md").write_text(f"""# Citation

Version DOI (this deposit, v1.0.0): https://doi.org/{DOI}

Concept DOI (resolves to the latest version): see the Zenodo record
page of this deposit — assigned automatically at publication.

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
    tag_at = subprocess.run(["git", "tag", "--points-at", "HEAD"],
                            capture_output=True, text=True).stdout.split()
    files = {}
    for f in sorted(out.rglob("*")):
        if f.is_file():
            files[str(f.relative_to(out))] = sha256(f)
    manifest = {
        "schema": "saga-zenodo-bundle-manifest/v1",
        "releaseIdentity": {
            "tag": TAG,
            "tagPresentOnHead": TAG in tag_at,
            "commit": commit,
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
    print("upload to Zenodo: the zip above + the standalone paper/main.pdf "
          "(never the unzipped tree — flat upload collides same-named files)")
    if TAG not in tag_at:
        print(f"WARNING: HEAD is not tagged {TAG} — rebuild after tagging")
    if not args.ci_run:
        print("NOTE: releaseCiRun is null — pass --ci-run after the tag CI finishes")
    return 0


if __name__ == "__main__":
    sys.exit(main())
