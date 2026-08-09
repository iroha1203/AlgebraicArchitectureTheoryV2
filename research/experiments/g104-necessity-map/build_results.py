#!/usr/bin/env python3
"""Generate the canonical deterministic checkpoint results.json."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import necessity_map
import r2_hunt


def results_report() -> dict[str, object]:
    r0 = necessity_map.r0_report()
    r1 = necessity_map.r1_report()
    r2 = {
        "round1_direct": r2_hunt.round1_report(),
        "round2_component": r2_hunt.round2_report(),
        "round3_certified": r2_hunt.round3_report(),
        "round4_closed_2d": r2_hunt.round4_report(),
        "round5_mixed_support": r2_hunt.round5_report(),
        "round6_nonfree_linear_face_chain": r2_hunt.round6_report(),
        "round7_nonfree_branching_face_chain": r2_hunt.round7_report(),
        "round8_invalid_diagnostic_relation_grammar": r2_hunt.round8_report(),
        "round9_valid_mixed_relation_support": r2_hunt.round9_report(),
        "round10_valid_multichart_face_chain": r2_hunt.round10_report(),
        "round11_post_punit_wheel_bipartite": r2_hunt.round11_report(),
        "round12_post_punit_octahedral_partitioned": r2_hunt.round12_report(),
    }
    round8 = r2["round8_invalid_diagnostic_relation_grammar"]
    round9 = r2["round9_valid_mixed_relation_support"]
    round10 = r2["round10_valid_multichart_face_chain"]
    round11 = r2["round11_post_punit_wheel_bipartite"]
    round12 = r2["round12_post_punit_octahedral_partitioned"]
    r0_sha256 = r2_hunt._canonical_report_sha256(r0)
    round11_sha256 = r2_hunt._canonical_report_sha256(round11)
    round12_sha256 = r2_hunt._canonical_report_sha256(round12)
    if not (
        r0["r0_pass"]
        and r0_sha256 == r2_hunt.POST_PUNIT_R0_SEMANTIC_SHA256
        and len(r1["verdicts"]) == 7
        and r1["all_seven_verdicts_fixed"]
        and round8["valid"] is False
        and round8["progress_audit"]["streak_after_round"] == 0
        and round9["valid"] is True
        and round10["valid"] is True
        and round11_sha256 == r2_hunt.ROUND11_VALID_PAYLOAD_SHA256
        and round11["valid"] is True
        and round11["progress_audit"]["entry_streak"] == 0
        and round11["progress_audit"]["progress"] is False
        and round11["progress_audit"]["streak_after_round"] == 1
        and round11["same_blocker_evidence"]["valid_no_progress_1_of_2"]
        and round11["queries"]["prior_sufficiency_or_necessity_break_count"]
        == 0
        and round11["queries"]["new_sufficiency_break_count"] == 0
        and round11["queries"]["new_necessity_break_count"] == 0
        and round11["canonical_code_audit"]["registered_code_count"] == 12
        and round11["blocker_id"] == "PB-R2-NONFREE-GLOBAL-FACE-CHAIN"
        and round12_sha256
        == "c9ab928190491610ff1e394fb16fb4e132f117374a317505fbd2025ab5a09f90"
        and round12["valid"] is True
        and round12["progress_audit"]["entry_streak"] == 1
        and round12["progress_audit"]["progress"] is False
        and round12["progress_audit"]["streak_after_round"] == 2
        and round12["same_blocker_evidence"]["valid_no_progress_2_of_2"]
        and round12["queries"]["prior_sufficiency_or_necessity_break_count"]
        == 0
        and round12["queries"]["new_sufficiency_break_count"] == 0
        and round12["queries"]["new_necessity_break_count"] == 0
        and round12["stop_audit"][
            "stop_condition_C_two_valid_same_blocker_no_progress"
        ]
        and round12["stop_audit"]["stop_condition_A_completion"] is False
        and round12["stop_audit"]["stop_condition_B_finite_exhaustion"] is False
        and round12["population"]["total_raw_cases"] == 1918
        and round12["population"]["total_full_semantic_payload_ids"] == 1918
        and round12["population"]["total_truncated_semantic_payload_ids"]
        == 1918
        and round12["canonical_code_audit"]["registered_code_count"] == 14
        and round12["blocker_id"] == "PB-R2-NONFREE-GLOBAL-FACE-CHAIN"
    ):
        raise AssertionError("Stop-C terminal audit is not satisfied")

    return {
        "artifact": "G-104 C0-C6 necessity map off-loop checkpoint",
        "arithmetic": "exact fractions.Fraction linear algebra over Q",
        "randomness": "none",
        "serialization": "UTF-8, LF, indent=2, sort_keys=True, trailing newline",
        "r0": r0,
        "r1": r1,
        "r2": r2,
        "terminal": {
            "kind": "C",
            "task_complete": False,
            "issue_remains_open": True,
            "prd_retained": True,
            "draft_pr_checkpoint": True,
            "r1_verdict_map_complete": True,
            "r2_characterization_complete": False,
            "last_progress_event": "R0(d) PUnit provenance calibration fix",
            "last_progress_issue_comment": 5231149474,
            "last_provenance_correction": (
                "indicator law_type corrected from historical Unit label to the "
                "actual PUnit field; counted as PRD progress and reset Stop-C streak"
            ),
            "round8_diagnostic_counted_in_stop_streak": False,
            "historical_pre_punit_rounds_not_counted_in_final_streak": [
                "R2-round-8",
                "R2-round-9",
                "R2-round-10",
            ],
            "consecutive_no_progress_rounds": ["R2-round-11", "R2-round-12"],
            "round9_result_issue_comment": 5230876303,
            "round10_preregistration_issue_comment": 5230881464,
            "historical_retracted_stop_c_result_issue_comment": 5230966215,
            "round11_preregistration_issue_comment": 5231154236,
            "round11_result_issue_comment": 5231263023,
            "round11_payload_sha256": round11_sha256,
            "round12_preregistration_issue_comment": 5231270132,
            "round12_result_issue_comment": 5231343121,
            "round12_payload_sha256": round12_sha256,
            "stop_c_result_issue_comment": 5231343121,
            "final_population": 1918,
            "blocker_id": "PB-R2-NONFREE-GLOBAL-FACE-CHAIN",
            "coverage_limit": (
                "Finite exact populations through 1918 semantic cases, fixed W5, "
                "K3,3, octahedral, house, and star graphs, and lift count at most "
                "six only; no general theorem for arbitrary retained non-free "
                "face-chain graphs, certificate coloring, chart count, cross-chart "
                "coupled incidence, face multiplicity, or compatible support "
                "distribution."
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
