#!/usr/bin/env python3
"""Generate deterministic full and summary checkpoint result artifacts."""

from __future__ import annotations

import argparse
from copy import deepcopy
from dataclasses import asdict
import json
from pathlib import Path

import necessity_map
import r2_hunt


FULL_RESULTS_EXPECTED_SHA256 = (
    "cabfbcae7075280a6d10de3c819c25ca2396a21deaed2099bafdd71daa252306"
)
SUMMARY_RESULTS_EXPECTED_SHA256 = (
    "afa334056b52938044c0acad9b693a0c437300382b855f32450af5750020caa5"
)
CHECKPOINT_AMENDMENT_ISSUE_COMMENT = 5231857267
ROUND1_THROUGH_ROUND7_HASH_RESYNC_ISSUE_COMMENT = 5230523348

R2_ROUND_KEYS_THROUGH_ROUND12 = (
    "round1_direct",
    "round2_component",
    "round3_certified",
    "round4_closed_2d",
    "round5_mixed_support",
    "round6_nonfree_linear_face_chain",
    "round7_nonfree_branching_face_chain",
    "round8_invalid_diagnostic_relation_grammar",
    "round9_valid_mixed_relation_support",
    "round10_valid_multichart_face_chain",
    "round11_post_punit_wheel_bipartite",
    "round12_post_punit_octahedral_partitioned",
)
R2_ROUND_KEYS = R2_ROUND_KEYS_THROUGH_ROUND12

# Historical result comment IDs cannot be added to the registered round payloads
# without changing their hashes.  This immutable projection-only ledger records
# the public Issue #3948 chronology fixed before amendment comment 5231857267.
R2_ROUND_PROVENANCE_THROUGH_ROUND12 = {
    "round1_direct": {
        "preregistration_issue_comments": [5230386108, 5230405605],
        "additional_pre_run_issue_comments": [5230443070],
        "result_issue_comments": [5230444735],
        "valid": True,
        "progress": True,
        "history_classification": "progress",
    },
    "round2_component": {
        "preregistration_issue_comments": [5230446212],
        "additional_pre_run_issue_comments": [5230449728],
        "result_issue_comments": [5230451462],
        "valid": True,
        "progress": True,
        "history_classification": "progress",
    },
    "round3_certified": {
        "preregistration_issue_comments": [5230453578],
        "additional_pre_run_issue_comments": [5230457738],
        "result_issue_comments": [5230459292],
        "valid": True,
        "progress": True,
        "history_classification": "progress",
    },
    "round4_closed_2d": {
        "preregistration_issue_comments": [5230462990],
        "additional_pre_run_issue_comments": [],
        "result_issue_comments": [5230466829],
        "valid": True,
        "progress": False,
        "history_classification": "historical_no_progress",
    },
    "round5_mixed_support": {
        "preregistration_issue_comments": [5230467922],
        "additional_pre_run_issue_comments": [],
        "result_issue_comments": [5230475473],
        "valid": True,
        "progress": False,
        "history_classification": "stop_streak_ineligible",
    },
    "round6_nonfree_linear_face_chain": {
        "preregistration_issue_comments": [5230507176],
        "additional_pre_run_issue_comments": [],
        "result_issue_comments": [5230512797],
        "valid": True,
        "progress": False,
        "history_classification": "historical_no_progress",
    },
    "round7_nonfree_branching_face_chain": {
        "preregistration_issue_comments": [5230514887],
        "additional_pre_run_issue_comments": [],
        "result_issue_comments": [5230519971],
        "valid": True,
        "progress": False,
        "history_classification": "historical_no_progress",
    },
    "round8_invalid_diagnostic_relation_grammar": {
        "preregistration_issue_comments": [5230713854],
        "additional_pre_run_issue_comments": [],
        "result_issue_comments": [5230818358],
        "valid": False,
        "progress": False,
        "history_classification": "invalid_diagnostic",
    },
    "round9_valid_mixed_relation_support": {
        "preregistration_issue_comments": [5230824089],
        "additional_pre_run_issue_comments": [],
        "result_issue_comments": [5230876303],
        "valid": True,
        "progress": False,
        "history_classification": "historical_no_progress",
    },
    "round10_valid_multichart_face_chain": {
        "preregistration_issue_comments": [5230881464],
        "additional_pre_run_issue_comments": [],
        "result_issue_comments": [5230966215],
        "valid": True,
        "progress": False,
        "history_classification": "historical_retracted_stop_c",
    },
    "round11_post_punit_wheel_bipartite": {
        "preregistration_issue_comments": [5231154236],
        "additional_pre_run_issue_comments": [],
        "result_issue_comments": [5231263023],
        "valid": True,
        "progress": False,
        "history_classification": "final_valid_no_progress_1_of_2",
    },
    "round12_post_punit_octahedral_partitioned": {
        "preregistration_issue_comments": [5231270132],
        "additional_pre_run_issue_comments": [],
        "result_issue_comments": [5231343121],
        "valid": True,
        "progress": False,
        "history_classification": "final_valid_no_progress_2_of_2",
    },
}
R2_ROUND_PROVENANCE = R2_ROUND_PROVENANCE_THROUGH_ROUND12

if tuple(R2_ROUND_PROVENANCE_THROUGH_ROUND12) != (
    R2_ROUND_KEYS_THROUGH_ROUND12
):
    raise AssertionError("Round-12 provenance keys do not match the parent boundary")


def results_report_through_round12() -> dict[str, object]:
    """Build the immutable parent checkpoint through R2 Round 12."""

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


def results_report() -> dict[str, object]:
    """Return the current canonical full report, detached from its parent build."""

    return deepcopy(results_report_through_round12())


def render_json(report: dict[str, object]) -> str:
    return json.dumps(
        report,
        ensure_ascii=False,
        indent=2,
        sort_keys=True,
    ) + "\n"


def _block_h1_summary(block: dict[str, object]) -> dict[str, object]:
    return {
        "coarse_targets_A": block["coarse_targets_A"],
        "fine_targets_pi_preimage_A": block["fine_targets_pi_preimage_A"],
        "h1": block["h1"],
    }


def _named_block_h1_summary(
    blocks: dict[str, dict[str, object]],
) -> dict[str, dict[str, object]]:
    return {
        name: _block_h1_summary(block)
        for name, block in sorted(blocks.items())
    }


def _r0_summary(r0: dict[str, object]) -> dict[str, object]:
    calibration = r0["calibration"]
    gate_a = calibration["a_three_lean_obstructions"]
    gate_b = calibration["b_derived_support_hole"]
    gate_c = calibration["c_block_reduction"]
    gate_d = calibration["d_indicator_realizability"]
    gate_e = calibration["e_canonical_firing_oracle"]
    return {
        "phase": r0["phase"],
        "pass": r0["r0_pass"],
        "payload_sha256": r2_hunt._canonical_report_sha256(r0),
        "gates": {
            "a_three_lean_obstructions": {
                "pass": all(row["calibration_pass"] for row in gate_a),
                "fixtures": [
                    {
                        "name": row["fixture"]["name"],
                        "pass": row["calibration_pass"],
                        "blocks": [
                            _block_h1_summary(block) for block in row["blocks"]
                        ],
                    }
                    for row in gate_a
                ],
            },
            "b_derived_support_hole": {
                "pass": gate_b["calibration_pass"],
                "global_h1": gate_b["law_value_singleton_block_direct_sum"],
                "blocks": [
                    _block_h1_summary(block) for block in gate_b["blocks"]
                ],
            },
            "c_block_reduction": {
                "pass": gate_c["pass"],
                "global_h1": gate_c["law_generated_global"]["h1"],
                "blocks": _named_block_h1_summary(
                    gate_c["actual_law_blocks"]
                ),
            },
            "d_indicator_realizability": {
                "pass": gate_d["all_nonempty_A_realized"],
                "factors": [
                    {
                        "name": factor["name"],
                        "pass": factor["all_pass"],
                        "factor_pi": factor["factor_pi"],
                        "law_type": factor["law_type"],
                        "value_type": factor["value_type"],
                        "blocks": [
                            {
                                "coarse_targets_A": case["coarse_targets_A"],
                                "fine_targets_pi_preimage_A": case[
                                    "fine_targets_pi_preimage_A"
                                ],
                                "h1": case["A_subnerve_constant_Q_block"]["h1"],
                            }
                            for case in factor["cases"]
                        ],
                    }
                    for factor in gate_d["factors"]
                ],
            },
            "e_canonical_firing_oracle": {
                "pass": gate_e["canonical_oracle_pass"],
                "global_h1": gate_e["law_generated_global"]["h1"],
                "blocks": [
                    _block_h1_summary(block) for block in gate_e["blocks"]
                ],
            },
        },
    }


def _r1_summary(r1: dict[str, object]) -> dict[str, object]:
    return {
        "phase": r1["phase"],
        "pass": r1["all_seven_verdicts_fixed"],
        "payload_sha256": r2_hunt._canonical_report_sha256(r1),
        "preregistered_issue_comment": r1["preregistered_issue_comment"],
        "verdicts": r1["verdicts"],
        "witnesses": [
            {
                "clause": witness["clause"],
                "verdict": witness["verdict"],
                "uniform": witness["uniform"],
                "failure_scope": witness["failure_scope"],
                "witness_pass": witness["witness_pass"],
                "fixture": witness["fixture"],
                "blocks": [
                    _block_h1_summary(block) for block in witness["blocks"]
                ],
            }
            for witness in r1["necessity_witnesses"]
        ],
    }


def _fixture_summary(
    comparison: necessity_map.UniformComparison,
) -> dict[str, object]:
    return {
        "fixture": comparison.summary(),
        "name_free_semantic_id_20hex": r2_hunt._case_id(comparison),
        "name_free_semantic_sha256": r2_hunt._case_semantic_sha256(comparison),
        "blocks": [
            {
                "coarse_targets_A": sorted(targets),
                "h1": asdict(analysis),
            }
            for targets, analysis in comparison.block_analyses()
        ],
    }


def _case_observation(case: dict[str, object]) -> dict[str, object]:
    return {
        "id": case["id"],
        "candidate_aggregate": case["candidate"]["aggregate"],
        "candidate_all": case["candidate"]["all"],
        "uniform": case["uniform"],
        "sufficiency_break": case["sufficiency_break"],
        "necessity_break": case["necessity_break"],
    }


def _counterexample_fixture_summaries(
    r2: dict[str, dict[str, object]],
) -> dict[str, object]:
    chain3 = _fixture_summary(r2_hunt.chain3_fixture())
    chain3["query_history"] = [
        {
            "round": r2[key]["round"],
            "candidate_semantic_id": r2[key]["candidate"]["semantic_id"],
            **_case_observation(r2[key]["registered_chain3"]),
        }
        for key in (
            "round1_direct",
            "round2_component",
            "round3_certified",
        )
    ]
    unkilled = _fixture_summary(r2_hunt.unkilled_twin_fixture())
    unkilled["query_history"] = [
        {
            "round": r2[key]["round"],
            "candidate_semantic_id": r2[key]["candidate"]["semantic_id"],
            **_case_observation(r2[key]["registered_unkilled_twin"]),
        }
        for key in ("round2_component", "round3_certified")
    ]
    return {"Chain3": chain3, "UnkilledTwin": unkilled}


def _population_summary(population: dict[str, object]) -> dict[str, object]:
    raw = population.get("total_raw_cases", population.get("total"))
    if raw is None:
        raise AssertionError("round population has no total case count")
    full_unique = population.get("total_full_semantic_payload_ids")
    if full_unique is None and "prior_full_semantic_payload_ids" in population:
        full_unique = population["prior_full_semantic_payload_ids"] + len(
            population.get("new_full_semantic_payload_ids", [])
        )
    if full_unique is None:
        full_unique = raw
    prefix_unique = population.get("total_truncated_semantic_payload_ids")
    if (
        prefix_unique is None
        and "prior_truncated_semantic_payload_ids" in population
    ):
        prefix_unique = population["prior_truncated_semantic_payload_ids"] + len(
            population.get("new_truncated_semantic_payload_ids", [])
        )
    if prefix_unique is None:
        prefix_unique = raw
    return {
        "raw_cases": raw,
        "full_semantic_unique_ids": full_unique,
        "prefix_20hex_unique_ids": prefix_unique,
        "full_sha256_collision_count": population.get(
            "full_sha256_collision_count",
            raw - full_unique,
        ),
        "prefix_20hex_collision_count": population.get(
            "truncated_20hex_collision_count",
            raw - prefix_unique,
        ),
        "strict_superset": population.get("strict_superset"),
        "all_cases_evaluated": population["all_cases_evaluated"],
    }


def _canonical_code_summary(report: dict[str, object]) -> dict[str, object] | None:
    audit = report.get("canonical_code_audit")
    if audit is not None:
        return {
            key: value
            for key, value in audit.items()
            if key.endswith("count") or key == "strict_new"
        }
    for field in (
        "canonical_colored_relation_graph_codes",
        "canonical_relation_graph_support_codes",
        "canonical_colored_graph_support_codes",
    ):
        if field in report:
            return {
                "registered_code_count": len(report[field]),
                "full_sha256_collision_count": 0,
                "truncated_20hex_collision_count": 0,
            }
    return None


def _normalized_progress_audit(
    key: str,
    report: dict[str, object],
) -> dict[str, object]:
    if key == "round1_direct":
        audit = {
            "new_verdicts": [],
            "new_nonisomorphic_counterexamples": report["queries"][
                "necessity_break_ids"
            ],
            "candidate_semantic_change": False,
            "calibration_fixes": [],
        }
    elif key == "round2_component":
        audit = {
            "new_verdicts": [],
            "new_nonisomorphic_counterexamples": report["queries"][
                "sufficiency_break_ids"
            ],
            "candidate_semantic_change": True,
            "calibration_fixes": [],
        }
    elif key == "round3_certified":
        audit = {
            "new_verdicts": [],
            "new_nonisomorphic_counterexamples": [],
            "candidate_semantic_change": True,
            "calibration_fixes": [],
        }
    else:
        audit = dict(report["progress_audit"])
    audit["progress"] = R2_ROUND_PROVENANCE_THROUGH_ROUND12[key]["progress"]
    audit.setdefault("streak_after_round", None)
    return audit


def _round_summary(
    key: str,
    report: dict[str, object],
    previous_raw_cases: int,
) -> dict[str, object]:
    provenance = R2_ROUND_PROVENANCE_THROUGH_ROUND12[key]
    population = _population_summary(report["population"])
    recorded_streak = _normalized_progress_audit(key, report)[
        "streak_after_round"
    ]
    counted_in_final_streak = key in {
        "round11_post_punit_wheel_bipartite",
        "round12_post_punit_octahedral_partitioned",
    }
    final_streak = {
        "round11_post_punit_wheel_bipartite": 1,
        "round12_post_punit_octahedral_partitioned": 2,
    }.get(key, 0)
    return {
        "key": key,
        "round": report["round"],
        "payload_sha256": r2_hunt._canonical_report_sha256(report),
        "candidate_semantic_id": report["candidate"]["semantic_id"],
        "issue_comments": {
            "preregistration": provenance["preregistration_issue_comments"],
            "additional_pre_run": provenance[
                "additional_pre_run_issue_comments"
            ],
            "result": provenance["result_issue_comments"],
        },
        "population": {
            **population,
            "new_raw_cases": population["raw_cases"] - previous_raw_cases,
        },
        "queries": report["queries"],
        "progress_audit": _normalized_progress_audit(key, report),
        "status": {
            "valid": provenance["valid"],
            "history_classification": provenance["history_classification"],
            "recorded_streak_after_round": recorded_streak,
            "counted_in_final_stop_c_streak": counted_in_final_streak,
            "final_stop_c_streak_after_round": final_streak,
        },
        "canonical_code_audit": _canonical_code_summary(report),
        "same_blocker_evidence": report.get("same_blocker_evidence"),
        "stop_audit": report.get("stop_audit"),
        "blocker_id": report.get("blocker_id"),
        "coverage_limit": report["coverage_limit"],
    }


def results_summary_report_through_round12(
    full_report: dict[str, object] | None = None,
) -> dict[str, object]:
    """Project the immutable parent checkpoint through R2 Round 12."""

    full = results_report_through_round12() if full_report is None else full_report
    r0 = full["r0"]
    r1 = full["r1"]
    r2 = full["r2"]
    rounds = []
    previous_raw_cases = 0
    for key in R2_ROUND_KEYS_THROUGH_ROUND12:
        round_summary = _round_summary(key, r2[key], previous_raw_cases)
        rounds.append(round_summary)
        previous_raw_cases = round_summary["population"]["raw_cases"]
    terminal = {
        **full["terminal"],
        "stop_audit": r2[
            "round12_post_punit_octahedral_partitioned"
        ]["stop_audit"],
        "same_blocker_evidence": r2[
            "round12_post_punit_octahedral_partitioned"
        ]["same_blocker_evidence"],
    }
    summary = {
        "artifact": "G-104 C0-C6 necessity map slim checkpoint summary",
        "schema_version": 1,
        "randomness": full["randomness"],
        "serialization": full["serialization"],
        "provenance": {
            "checkpoint_amendment_issue_comment": (
                CHECKPOINT_AMENDMENT_ISSUE_COMMENT
            ),
            "full_results": {
                "repository_status": "derived; not committed",
                "canonical_generator": "build_results.py --output <path>",
                "expected_sha256": FULL_RESULTS_EXPECTED_SHA256,
            },
            "round1_through_round7_hash_resync_issue_comment": (
                ROUND1_THROUGH_ROUND7_HASH_RESYNC_ISSUE_COMMENT
            ),
            "post_punit_manifest_sha256": (
                r2_hunt.POST_PUNIT_MANIFEST_REGISTERED_SHA256
            ),
        },
        "terminal": terminal,
        "r0": _r0_summary(r0),
        "r1": _r1_summary(r1),
        "r2": {
            "candidate_generations": [
                r2["round1_direct"]["candidate"],
                r2["round2_component"]["candidate"],
                r2["round3_certified"]["candidate"],
            ],
            "counterexample_fixtures": _counterexample_fixture_summaries(r2),
            "rounds": rounds,
        },
    }
    return deepcopy(summary)


def results_summary_report(
    full_report: dict[str, object] | None = None,
) -> dict[str, object]:
    """Return the current canonical summary via the fixed Round-12 parent API."""

    return results_summary_report_through_round12(full_report)


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(description=__doc__)
    command.add_argument(
        "--output",
        type=Path,
        help="write the canonical full results JSON",
    )
    command.add_argument(
        "--summary-output",
        type=Path,
        help="write the deterministic slim summary JSON",
    )
    return command


def main() -> int:
    args = parser().parse_args()
    if args.output is None and args.summary_output is None:
        args.output = Path(__file__).with_name("results.json")
    full = results_report()
    if args.output is not None:
        args.output.write_text(render_json(full), encoding="utf-8", newline="\n")
        print(args.output)
    if args.summary_output is not None:
        args.summary_output.write_text(
            render_json(results_summary_report(full)),
            encoding="utf-8",
            newline="\n",
        )
        print(args.summary_output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
