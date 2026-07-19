#!/usr/bin/env python3
"""コミット済み証拠束の digest 整合検査。

各 analyze summary / gate report の inputDigests と、コミット済み入力 artifact の
canonical JSON digest(キーを再帰的にソートした compact 直列化の sha256。
ArchSig の canonical_json_file_digest と同一規約)の一致を検査する。
リポジトリルートから実行する。
"""

import hashlib
import json
import sys
from pathlib import Path

EV = Path("docs/reports/train_ticket_dogfooding/evidence")


def canonical_digest(path):
    value = json.loads(Path(path).read_text())
    blob = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(blob.encode("utf-8")).hexdigest()


ANALYZE_CHECKS = [
    # (summary, archmap, law_policy, law_surface, measurement_profile)
    (EV / "trial/analyze/archsig-analysis-summary.json",
     EV / "trial/archmap.json",
     EV / "trial/law/law_policy.json",
     EV / "trial/law/law_surface.json",
     EV / "trial/law/measurement_profile.json"),
    (EV / "trial/analyze-postfix/archsig-analysis-summary.json",
     EV / "trial/archmap.json",
     EV / "trial/law/law_policy.json",
     EV / "trial/law/law_surface.json",
     EV / "trial/law/measurement_profile.json"),
    (EV / "fullbuild/analyze-money/archsig-analysis-summary.json",
     EV / "fullbuild/archmap-money-variant.json",
     EV / "fullbuild/law/law-policy-money.json",
     EV / "fullbuild/law/law-surface-money.json",
     EV / "fullbuild/law/measurement-profile-money.json"),
    (EV / "fullbuild/analyze-status/archsig-analysis-summary.json",
     EV / "fullbuild/archmap-status-variant.json",
     EV / "fullbuild/law/law-policy-status.json",
     EV / "fullbuild/law/law-surface-status.json",
     EV / "fullbuild/law/measurement-profile-status.json"),
    (EV / "saga/out/head/archsig-analysis-summary.json",
     EV / "saga/archmap-saga-head.json",
     EV / "saga/law-policy-saga.json",
     EV / "saga/law-surface-saga.json",
     EV / "saga/measurement-profile-saga.json"),
    (EV / "saga/out/repaired/archsig-analysis-summary.json",
     EV / "saga/archmap-saga-repaired.json",
     EV / "saga/law-policy-saga.json",
     EV / "saga/law-surface-saga.json",
     EV / "saga/measurement-profile-saga.json"),
]

GATE_PACKET_CHECKS = [
    # (gate_report, packet, gate_policy or None if not preserved)
    (EV / "trial/analyze/archsig-gate-report.json",
     EV / "trial/analyze/archsig-measurement-packet.json",
     None),  # 試運転の gate policy は実体未保存(digest のみ)
    (EV / "fullbuild/analyze-money/archsig-gate-report.json",
     EV / "fullbuild/analyze-money/archsig-measurement-packet.json",
     Path("tools/archsig/tests/fixtures/ag_measurement/gate_policy_conservative.json")),
    (EV / "fullbuild/analyze-status/archsig-gate-report.json",
     EV / "fullbuild/analyze-status/archsig-measurement-packet.json",
     Path("tools/archsig/tests/fixtures/ag_measurement/gate_policy_conservative.json")),
    (EV / "saga/out/gate-head.json",
     EV / "saga/out/head/archsig-measurement-packet.json",
     EV / "saga/gate-policy-saga.json"),
    (EV / "saga/out/gate-repaired.json",
     EV / "saga/out/repaired/archsig-measurement-packet.json",
     EV / "saga/gate-policy-saga.json"),
]


def main():
    failures = 0
    total = 0

    def check(label, want, path):
        nonlocal failures, total
        total += 1
        got = canonical_digest(path)
        ok = want == got
        if not ok:
            failures += 1
        print(f"{'OK      ' if ok else 'MISMATCH'} {label}: {path}")

    for summary, archmap, law_policy, law_surface, profile in ANALYZE_CHECKS:
        digests = json.loads(summary.read_text())["inputDigests"]
        run = summary.parent.relative_to(EV)
        check(f"{run} archmap", digests["archmap"]["sha256"], archmap)
        check(f"{run} lawPolicy", digests["lawPolicy"]["sha256"], law_policy)
        check(f"{run} lawSurface", digests["lawSurface"]["sha256"], law_surface)
        check(f"{run} measurementProfile", digests["measurementProfile"]["sha256"], profile)

    for gate_report, packet, policy in GATE_PACKET_CHECKS:
        digests = json.loads(gate_report.read_text())["inputDigests"]
        label = gate_report.relative_to(EV)
        check(f"{label} measurementPacket", digests["measurementPacket"]["sha256"], packet)
        if policy is not None:
            check(f"{label} gatePolicy", digests["gatePolicy"]["sha256"], policy)

    print(f"{total - failures}/{total} OK")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
