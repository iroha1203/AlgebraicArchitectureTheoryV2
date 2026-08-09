#!/usr/bin/env python3
"""Generate the canonical deterministic checkpoint results.json."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import necessity_map
import r2_hunt


def results_report() -> dict[str, object]:
    return {
        "artifact": "G-104 C0-C6 necessity map off-loop checkpoint",
        "arithmetic": "exact fractions.Fraction linear algebra over Q",
        "randomness": "none",
        "serialization": "UTF-8, LF, indent=2, sort_keys=True, trailing newline",
        "r0": necessity_map.r0_report(),
        "r1": necessity_map.r1_report(),
        "r2": {
            "round1_direct": r2_hunt.round1_report(),
            "round2_component": r2_hunt.round2_report(),
            "round3_certified": r2_hunt.round3_report(),
            "round4_closed_2d": r2_hunt.round4_report(),
            "round5_mixed_support": r2_hunt.round5_report(),
            "round6_nonfree_linear_face_chain": r2_hunt.round6_report(),
            "round7_nonfree_branching_face_chain": r2_hunt.round7_report(),
        },
        "terminal": {
            "kind": "C",
            "task_complete": False,
            "issue_remains_open": True,
            "prd_retained": True,
            "partial_verdict_map_complete_for_C0_through_C6": True,
            "last_progress_round": "post-round5 independent audit correction",
            "consecutive_no_progress_rounds": ["R2-round-6", "R2-round-7"],
            "blocker_id": "PB-R2-NONFREE-GLOBAL-FACE-CHAIN",
            "coverage_limit": (
                "Finite fixed-label populations only; no general theorem for "
                "arbitrary non-free two-dimensional face chains."
            ),
        },
    }


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(description=__doc__)
    command.add_argument(
        "--output",
        type=Path,
        default=Path(__file__).with_name("results.json"),
    )
    return command


def main() -> int:
    args = parser().parse_args()
    rendered = json.dumps(
        results_report(),
        ensure_ascii=False,
        indent=2,
        sort_keys=True,
    ) + "\n"
    args.output.write_text(rendered, encoding="utf-8")
    print(args.output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
