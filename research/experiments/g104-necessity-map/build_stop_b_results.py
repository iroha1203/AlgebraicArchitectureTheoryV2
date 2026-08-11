#!/usr/bin/env python3
"""Build the deterministic G_local-v1 final Stop-B artifacts.

Round 1 through Round 12 are regenerated through the immutable parent API.
Rounds 13 through 15 are provenance-only history: this builder never reruns
their reports, candidates, populations, or H1 queries.  The builder directly
requests the pure G_local-v1 permanent contract once and the Stop-B checker
once.  The checker performs its own admitted contract reconstruction, so the
effective contract construction count is exactly two.
"""

from __future__ import annotations

import argparse
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path

import build_results as parent_source
from build_results import (
    render_json as parent_render_json,
    results_report_through_round12,
    results_summary_report_through_round12,
)
import g_local_v1_stop_b as stop_b_source
from g_local_v1_stop_b import (
    check_g_local_v1_stop_b,
    g_local_v1_permanent_contract_manifest,
)
import r2_hunt as historical_source


PARENT_FULL_EXPECTED_SHA256 = (
    "cabfbcae7075280a6d10de3c819c25ca2396a21deaed2099bafdd71daa252306"
)
PARENT_SUMMARY_EXPECTED_SHA256 = (
    "afa334056b52938044c0acad9b693a0c437300382b855f32450af5750020caa5"
)
PARENT_SUMMARY_EXPECTED_BYTES = 95_410
PARENT_ROUND12_EXPECTED_SHA256 = (
    "c9ab928190491610ff1e394fb16fb4e132f117374a317505fbd2025ab5a09f90"
)

PERMANENT_CONTRACT_COMPACT_EXPECTED_SHA256 = (
    "955b75d7f88c2d7e3f7e516cb83928127fed9cbd8d28bb50572b17c49a7531af"
)
PERMANENT_CONTRACT_COMPACT_EXPECTED_BYTES = 314_821
CHECKER_RESULT_COMPACT_EXPECTED_SHA256 = (
    "834d97547d037ebe76fea942a95996f2b2a0bdcfe9f14eda73bc450c4ac9ebca"
)
CHECKER_RESULT_COMPACT_EXPECTED_BYTES = 56_940
COMMON_OBSERVATION_EXPECTED_SHA256 = (
    "742e6395bb21221fcac070975cbe9505d49d0c75f826289984288776836aa7dc"
)
COMMON_OBSERVATION_EXPECTED_BYTES = 53_279

PERMANENT_CONTRACT_REGRESSION_PROVENANCE = {
    "issue_comment": 5246749681,
    "created_at": "2026-08-10T22:28:47Z",
    "updated_at": "2026-08-10T22:28:47Z",
}
HISTORICAL_STOP_B_EXECUTION_PROVENANCE = {
    "role": "opaque-git-and-issue-history-provenance",
    "stop_b_result": {
        "issue_comment": 5245347326,
        "created_at": "2026-08-10T20:04:41Z",
        "updated_at": "2026-08-10T20:04:41Z",
    },
    "downstream_sync": [
        {
            "surface": "PR-3955",
            "comment": 5245356130,
            "created_at": "2026-08-10T20:05:35Z",
            "updated_at": "2026-08-10T20:05:35Z",
        },
        {
            "surface": "Issue-3954",
            "comment": 5245356137,
            "created_at": "2026-08-10T20:05:35Z",
            "updated_at": "2026-08-10T20:05:35Z",
        },
    ],
}

CANONICAL_GENERATOR = {
    "working_directory": "repository-root",
    "argv": [
        "python3",
        "research/experiments/g104-necessity-map/build_stop_b_results.py",
        "--output",
        "/tmp/g104-necessity-map-stop-b-results.json",
        "--summary-output",
        (
            "research/experiments/g104-necessity-map/"
            "results-stop-b-summary.json"
        ),
    ],
}

CANONICAL_SERIALIZATION = {
    "encoding": "UTF-8",
    "ensure_ascii": False,
    "indent": 2,
    "sort_keys": True,
    "trailing_newline": True,
}
COMPACT_CHECK_SERIALIZATION = {
    "encoding": "UTF-8",
    "ensure_ascii": True,
    "sort_keys": True,
    "separators": [",", ":"],
    "trailing_newline": False,
}

ROUND13_THROUGH_15_IMMUTABLE_HISTORY = (
    {
        "key": "round13_cross_chart_triangle_support",
        "round": "R2-round-13",
        "valid": True,
        "progress": True,
        "progress_recomputed": False,
        "payload_sha256_commits_progress_field": True,
        "canonical_payload_sha256": (
            "e15fc8dcb99ea7e8e17b1a52cc045379f9757c558a92f25e9d1bfc2bda5450e3"
        ),
        "canonical_bytes": 5_604_143,
        "preregistration": {
            "issue_comment": 5234690436,
            "created_at": "2026-08-10T00:34:52Z",
            "updated_at": "2026-08-10T00:34:52Z",
            "manifest_sha256": (
                "8bebea1711e8e786f0a4b4c3dd73458c83db7432facbf04d5abcbfdb7d285a6c"
            ),
        },
        "result": {
            "issue_comment": 5234839619,
            "created_at": "2026-08-10T01:08:00Z",
            "updated_at": "2026-08-10T01:08:00Z",
        },
        "report_or_query_reexecuted": False,
    },
    {
        "key": "round14_nonfree_mutual_kill_split",
        "round": "R2-round-14",
        "valid": True,
        "progress": True,
        "progress_recomputed": False,
        "payload_sha256_commits_progress_field": True,
        "canonical_payload_sha256": (
            "17c9907928a63cdf97e474e7f8813447601010ede07bbe7a43b525ef8551b450"
        ),
        "canonical_bytes": 22_818,
        "preregistration": {
            "issue_comment": 5234939066,
            "created_at": "2026-08-10T01:28:53Z",
            "updated_at": "2026-08-10T01:28:53Z",
            "manifest_sha256": (
                "eaa0c96376bb1d724505b16c6df6b7d519e27b7451da6a94d06b673d65e1f309"
            ),
        },
        "result": {
            "issue_comment": 5235064396,
            "created_at": "2026-08-10T01:55:17Z",
            "updated_at": "2026-08-10T01:55:17Z",
        },
        "report_or_query_reexecuted": False,
    },
    {
        "key": "round15_v5_semantic_safety_calibration",
        "round": "R2-round-15",
        "valid": True,
        "progress": True,
        "progress_recomputed": False,
        "payload_sha256_commits_progress_field": True,
        "canonical_payload_sha256": (
            "21b59632026d5ec0f104700f26808a8455e2ca607802a108c6934f68e8911969"
        ),
        "canonical_bytes": 97_792,
        "preregistration": {
            "issue_comment": 5235347217,
            "created_at": "2026-08-10T02:51:13Z",
            "updated_at": "2026-08-10T02:51:13Z",
            "manifest_sha256": (
                "e5f2d6630ee2f37de409f5e2c0757eed17b24509ca3cd3f7d924c130b6219c3b"
            ),
        },
        "result": {
            "issue_comment": 5235636358,
            "created_at": "2026-08-10T03:46:15Z",
            "updated_at": "2026-08-10T03:46:15Z",
        },
        "report_or_query_reexecuted": False,
    },
)


def render_json(report: dict[str, object]) -> str:
    """Render the public artifacts with the repository canonical contract."""

    return json.dumps(
        report,
        ensure_ascii=False,
        indent=2,
        sort_keys=True,
    ) + "\n"


def _compact_json(value: object) -> str:
    return json.dumps(
        value,
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    )


def _rendered_record(rendered: str) -> dict[str, object]:
    encoded = rendered.encode("utf-8")
    return {
        "canonical_sha256": sha256(encoded).hexdigest(),
        "canonical_bytes": len(encoded),
        "serialization": deepcopy(CANONICAL_SERIALIZATION),
    }


def _compact_record(value: object) -> dict[str, object]:
    encoded = _compact_json(value).encode("utf-8")
    return {
        "canonical_sha256": sha256(encoded).hexdigest(),
        "canonical_bytes": len(encoded),
        "serialization": deepcopy(COMPACT_CHECK_SERIALIZATION),
    }


def _admit_parent_relation(
    parent_full: dict[str, object],
    full_record: dict[str, object],
    summary_record: dict[str, object],
) -> str:
    round12 = parent_full["r2"][
        "round12_post_punit_octahedral_partitioned"
    ]
    round12_sha256 = _rendered_record(render_json(round12))[
        "canonical_sha256"
    ]
    if not (
        historical_source.ROUND13_PARENT_RESULTS_JSON_SHA256
        == PARENT_FULL_EXPECTED_SHA256
        == full_record["canonical_sha256"]
        and historical_source.ROUND13_PARENT_RESULTS_SUMMARY_JSON_SHA256
        == PARENT_SUMMARY_EXPECTED_SHA256
        == summary_record["canonical_sha256"]
        and historical_source.ROUND13_PARENT_ROUND12_PAYLOAD_SHA256
        == PARENT_ROUND12_EXPECTED_SHA256
        == round12_sha256
    ):
        raise AssertionError("Round12-to-Round13 parent relation drift")
    return round12_sha256


def _admit_parent_checkpoint() -> tuple[
    dict[str, object],
    dict[str, object],
    dict[str, object],
]:
    if not (
        parent_source.FULL_RESULTS_EXPECTED_SHA256
        == PARENT_FULL_EXPECTED_SHA256
        and parent_source.SUMMARY_RESULTS_EXPECTED_SHA256
        == PARENT_SUMMARY_EXPECTED_SHA256
        and len(parent_source.R2_ROUND_KEYS_THROUGH_ROUND12) == 12
        and parent_source.R2_ROUND_KEYS
        is parent_source.R2_ROUND_KEYS_THROUGH_ROUND12
    ):
        raise AssertionError("immutable Round-12 parent constants drift")

    parent_full = results_report_through_round12()
    parent_summary = results_summary_report_through_round12(parent_full)
    full_rendered = render_json(parent_full)
    summary_rendered = render_json(parent_summary)
    if not (
        full_rendered == parent_render_json(parent_full)
        and summary_rendered == parent_render_json(parent_summary)
    ):
        raise AssertionError("parent and Stop-B serialization contracts differ")
    full_record = _rendered_record(full_rendered)
    summary_record = _rendered_record(summary_rendered)
    round12_sha256 = _admit_parent_relation(
        parent_full,
        full_record,
        summary_record,
    )
    if not (
        full_record["canonical_sha256"] == PARENT_FULL_EXPECTED_SHA256
        and summary_record["canonical_sha256"]
        == PARENT_SUMMARY_EXPECTED_SHA256
        and summary_record["canonical_bytes"]
        == PARENT_SUMMARY_EXPECTED_BYTES
        and parent_full["terminal"]["kind"] == "C"
        and parent_summary["schema_version"] == 1
        and tuple(parent_full["r2"])
        == parent_source.R2_ROUND_KEYS_THROUGH_ROUND12
    ):
        raise AssertionError("immutable Round-12 parent reproduction failed")
    return parent_full, parent_summary, {
        "full": full_record,
        "summary": summary_record,
        "round12_payload_sha256": round12_sha256,
        "round_count": 12,
        "reproduced_fail_closed": True,
    }


def _admit_historical_rounds() -> tuple[dict[str, object], ...]:
    expected = ROUND13_THROUGH_15_IMMUTABLE_HISTORY
    round15_result = stop_b_source.ROUND15_LABEL_LEDGER["result_provenance"]
    source_rows = (
        {
            "payload_sha256": (
                historical_source.ROUND14_PARENT_ROUND13_PAYLOAD_SHA256
            ),
            "canonical_bytes": (
                historical_source.ROUND14_PARENT_ROUND13_CANONICAL_BYTES
            ),
            "preregistration_issue_comment": (
                historical_source.ROUND13_PREREGISTERED_ISSUE_COMMENT
            ),
            "preregistration_created_at": (
                historical_source.ROUND13_PREREGISTERED_CREATED_AT
            ),
            "preregistration_updated_at": (
                historical_source.ROUND13_PREREGISTERED_UPDATED_AT
            ),
            "manifest_sha256": (
                historical_source.ROUND13_REGISTERED_MANIFEST_SHA256
            ),
            "result_issue_comment": (
                historical_source.ROUND14_PARENT_ROUND13_RESULT_ISSUE_COMMENT
            ),
            "result_created_at": (
                historical_source.ROUND14_PARENT_ROUND13_RESULT_CREATED_AT
            ),
            "result_updated_at": (
                historical_source.ROUND14_PARENT_ROUND13_RESULT_UPDATED_AT
            ),
        },
        {
            "payload_sha256": (
                historical_source.ROUND15_PARENT_ROUND14_PAYLOAD_SHA256
            ),
            "canonical_bytes": (
                historical_source.ROUND15_PARENT_ROUND14_CANONICAL_BYTES
            ),
            "preregistration_issue_comment": (
                historical_source.ROUND14_PREREGISTERED_ISSUE_COMMENT
            ),
            "preregistration_created_at": (
                historical_source.ROUND14_PREREGISTERED_CREATED_AT
            ),
            "preregistration_updated_at": (
                historical_source.ROUND14_PREREGISTERED_UPDATED_AT
            ),
            "manifest_sha256": (
                historical_source.ROUND14_REGISTERED_MANIFEST_SHA256
            ),
            "result_issue_comment": (
                historical_source.ROUND15_PARENT_ROUND14_RESULT_ISSUE_COMMENT
            ),
            "result_created_at": (
                historical_source.ROUND15_PARENT_ROUND14_RESULT_CREATED_AT
            ),
            "result_updated_at": (
                historical_source.ROUND15_PARENT_ROUND14_RESULT_UPDATED_AT
            ),
        },
        {
            "payload_sha256": round15_result["canonical_payload_sha256"],
            "canonical_bytes": round15_result["canonical_bytes"],
            "preregistration_issue_comment": (
                stop_b_source.ROUND15_PREREGISTRATION_COMMENT
            ),
            "preregistration_created_at": (
                stop_b_source.ROUND15_PREREGISTRATION_CREATED_AT
            ),
            "preregistration_updated_at": (
                stop_b_source.ROUND15_PREREGISTRATION_UPDATED_AT
            ),
            "manifest_sha256": (
                stop_b_source.ROUND15_REGISTERED_MANIFEST_SHA256
            ),
            "result_issue_comment": round15_result["issue_comment"],
            "result_created_at": round15_result["created_at"],
            "result_updated_at": round15_result["updated_at"],
        },
    )
    projected_expected = tuple(
        {
            "payload_sha256": row["canonical_payload_sha256"],
            "canonical_bytes": row["canonical_bytes"],
            "preregistration_issue_comment": row["preregistration"][
                "issue_comment"
            ],
            "preregistration_created_at": row["preregistration"][
                "created_at"
            ],
            "preregistration_updated_at": row["preregistration"][
                "updated_at"
            ],
            "manifest_sha256": row["preregistration"]["manifest_sha256"],
            "result_issue_comment": row["result"]["issue_comment"],
            "result_created_at": row["result"]["created_at"],
            "result_updated_at": row["result"]["updated_at"],
        }
        for row in expected
    )
    if not (
        source_rows == projected_expected
        and tuple(row["round"] for row in expected)
        == ("R2-round-13", "R2-round-14", "R2-round-15")
        and all(row["valid"] is True for row in expected)
        and all(row["progress"] is True for row in expected)
        and all(row["progress_recomputed"] is False for row in expected)
        and all(
            row["report_or_query_reexecuted"] is False for row in expected
        )
    ):
        raise AssertionError("immutable Round13-15 history drift")
    return deepcopy(expected)


def _admit_permanent_contract(
    contract: dict[str, object],
) -> dict[str, object]:
    record = _compact_record(contract)
    source_provenance = {
        "sha256": stop_b_source.G_LOCAL_V1_PERMANENT_CONTRACT_SHA256,
        "migration_issue_comment": (
            stop_b_source.G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_ISSUE_COMMENT
        ),
        "migration_created_at": (
            stop_b_source.G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_CREATED_AT
        ),
        "migration_updated_at": (
            stop_b_source.G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_UPDATED_AT
        ),
    }
    expected_provenance = {
        "sha256": PERMANENT_CONTRACT_COMPACT_EXPECTED_SHA256,
        "migration_issue_comment": 5246699114,
        "migration_created_at": "2026-08-10T22:22:12Z",
        "migration_updated_at": "2026-08-10T22:22:12Z",
    }
    historical_bridge = contract["historical_execution_bridge"]
    admitted = (
        source_provenance == expected_provenance
        and record["canonical_sha256"]
        == PERMANENT_CONTRACT_COMPACT_EXPECTED_SHA256
        and record["canonical_bytes"]
        == PERMANENT_CONTRACT_COMPACT_EXPECTED_BYTES
        and contract["kind"]
        == "G-local-v1-permanent-structural-contract-v1"
        and contract["current_registration_values_in_contract"] is False
        and contract["checker_executed"] is False
        and contract["observation_executed"] is False
        and contract["contract_contains_its_own_sha256"] is False
        and contract["dependency_contract"][
            "contract_calls_round13_14_15_report_or_population"
        ]
        is False
        and contract["dependency_contract"][
            "later_checker_new_global_or_A_block_H1_queries"
        ]
        == 0
        and contract["dependency_contract"][
            "later_checker_new_population_queries"
        ]
        == 0
        and contract["immutable_round15_label_ledger"]["value"]
        == stop_b_source.ROUND15_LABEL_LEDGER
        and historical_bridge["role"]
        == "opaque history bridge; no current-source reconstruction claim"
        and historical_bridge["record"]
        == stop_b_source.G_LOCAL_V1_HISTORICAL_EXECUTION
        and historical_bridge["record"][
            "old_manifest_reconstructed_from_current_source"
        ]
        is False
        and historical_bridge["record"][
            "old_checker_reconstructed_from_current_source"
        ]
        is False
    )
    if not admitted:
        raise AssertionError("G_local-v1 permanent contract admission failed")
    return {
        **record,
        "current_permanent_contract_provenance": source_provenance,
        "builder_direct_contract_requests": 1,
        "checker_internal_contract_admission_reconstructions": 1,
        "effective_contract_constructions": 2,
        "admitted": admitted,
    }


def _admit_checker_result(
    result: dict[str, object],
    contract: dict[str, object],
) -> dict[str, object]:
    checker_record = _compact_record(result)
    observation = result["observation_evidence"]["common_observation"]
    observation_record = _compact_record(observation)
    component_equality = result["component_equality"]
    expected_components = {
        "aggregate_C0_through_C6",
        "whole_conditions",
        "whole_packet_kind_union",
        "whole_rooted_ball_histogram",
        "A_record_row_count",
        "A_record_multiplicities",
        "A_record_conditions",
        "A_record_packet_kind_unions",
        "A_record_rooted_ball_histograms",
        "A_record_histogram",
        "final_canonical_bytes",
    }
    query_counts = {
        "Obs_G_structural_evaluations": 2,
        "new_v5_candidate_evaluation_calls": 0,
        "new_global_or_A_block_H1_queries": 0,
        "new_population_queries": 0,
    }
    expected_contract_provenance = {
        "sha256": PERMANENT_CONTRACT_COMPACT_EXPECTED_SHA256,
        "migration_issue_comment": 5246699114,
        "migration_created_at": "2026-08-10T22:22:12Z",
        "migration_updated_at": "2026-08-10T22:22:12Z",
    }
    admitted = (
        checker_record["canonical_sha256"]
        == CHECKER_RESULT_COMPACT_EXPECTED_SHA256
        and checker_record["canonical_bytes"]
        == CHECKER_RESULT_COMPACT_EXPECTED_BYTES
        and observation_record["canonical_sha256"]
        == COMMON_OBSERVATION_EXPECTED_SHA256
        and observation_record["canonical_bytes"]
        == COMMON_OBSERVATION_EXPECTED_BYTES
        and result["observation_evidence"]["common_observation_sha256"]
        == COMMON_OBSERVATION_EXPECTED_SHA256
        and result["observation_evidence"][
            "common_observation_canonical_bytes"
        ]
        == COMMON_OBSERVATION_EXPECTED_BYTES
        and result["valid"] is True
        and result["stop_B"] is True
        and result["verdict"]
        == "CSTAR-not-expressible-in-G_local-v1"
        and result["semantic_id"] == "G_local-v1"
        and result["current_permanent_contract_provenance"]
        == expected_contract_provenance
        and result["historical_execution_provenance"]
        == contract["historical_execution_bridge"]["record"]
        and result["observations_equal"] is True
        and set(component_equality) == expected_components
        and all(component_equality.values())
        and result["labels"]
        == {"TERNARY-CYCLE-3": True, "TERNARY-CYCLE-6": False}
        and result["labels_differ"] is True
        and all(result[key] == value for key, value in query_counts.items())
        and result["migration_invariants"]
        == {
            "observation_meaning_unchanged": True,
            "historical_labels_admitted_after_observation": True,
            "query_zero_contract_unchanged": True,
            "old_manifest_reconstruction_claimed": False,
            "old_checker_reconstruction_claimed": False,
        }
    )
    if not admitted:
        raise AssertionError("G_local-v1 Stop-B checker result drift")
    return {
        "checker_result": checker_record,
        "common_observation": observation_record,
        "query_counts": query_counts,
        "component_count": len(component_equality),
        "all_components_equal": all(component_equality.values()),
        "admitted": admitted,
    }


def _terminal_metadata(coverage_limit: str) -> dict[str, object]:
    return {
        "kind": "B",
        "role": "final-mathematical-terminal",
        "verdict": "CSTAR-not-expressible-in-G_local-v1",
        "stop_condition_reached": True,
        "stop_condition_A_completion": False,
        "stop_condition_B_G_local_v1_two_point_separation": True,
        "stop_condition_B_finite_exhaustion": False,
        "stop_condition_C_two_valid_same_blocker_no_progress": False,
        "grammar_relative": True,
        "absolute_impossibility_claim": False,
        "coverage_limit": coverage_limit,
    }


def stop_b_results_report() -> dict[str, object]:
    """Build full results with one direct contract and one checker request.

    The checker independently reconstructs and admits the contract once, so
    one builder run has two effective contract constructions in total.
    """

    parent_full, parent_summary, parent_admission = _admit_parent_checkpoint()
    history = _admit_historical_rounds()
    contract = g_local_v1_permanent_contract_manifest()
    contract_admission = _admit_permanent_contract(contract)
    checker_result = check_g_local_v1_stop_b()
    checker_admission = _admit_checker_result(checker_result, contract)
    coverage_limit = checker_result["coverage_limit"]
    return {
        "artifact": "G-104 G_local-v1 final Stop-B result",
        "schema_version": 2,
        "randomness": "none",
        "serialization": deepcopy(CANONICAL_SERIALIZATION),
        "immutable_parent_through_round12": {
            "admission": parent_admission,
            "full_report": deepcopy(parent_full),
            "summary_report": deepcopy(parent_summary),
        },
        "historical_rounds_13_through_15": list(history),
        "historical_provenance": {
            "superseded_execution_bridge": deepcopy(
                contract["historical_execution_bridge"]
            ),
            "stop_b_execution_and_downstream_sync": deepcopy(
                HISTORICAL_STOP_B_EXECUTION_PROVENANCE
            ),
        },
        "g_local_v1": {
            "permanent_contract_manifest": deepcopy(contract),
            "contract_admission": contract_admission,
            "round15_hash_roles": {
                "registered_manifest_sha256": contract[
                    "round15_immutable_ledger_provenance"
                ]["sha256"],
                "label_ledger_sha256": contract[
                    "immutable_round15_label_ledger"
                ]["sha256"],
            },
            "permanent_contract_regression_provenance": deepcopy(
                PERMANENT_CONTRACT_REGRESSION_PROVENANCE
            ),
            "checker_result": deepcopy(checker_result),
            "checker_admission": checker_admission,
        },
        "terminal": _terminal_metadata(coverage_limit),
    }


def stop_b_results_summary(
    full_report: dict[str, object] | None = None,
) -> dict[str, object]:
    """Project a sub-100KB summary from a supplied full report.

    If ``full_report`` is omitted, build the full report once before taking
    the projection; the CLI always supplies its already-built full report.
    """

    full = stop_b_results_report() if full_report is None else full_report
    full_record = _rendered_record(render_json(full))
    parent = full["immutable_parent_through_round12"]
    parent_summary = parent["summary_report"]
    stop_b = full["g_local_v1"]
    checker = stop_b["checker_result"]
    evidence = checker["observation_evidence"]
    summary = {
        "artifact": "G-104 G_local-v1 final Stop-B terminal summary",
        "schema_version": 2,
        "randomness": full["randomness"],
        "serialization": full["serialization"],
        "full_results": {
            **full_record,
            "canonical_generator": deepcopy(CANONICAL_GENERATOR),
        },
        "parent_through_round12": {
            "admission": deepcopy(parent["admission"]),
            "r0": {
                key: deepcopy(parent_summary["r0"][key])
                for key in ("phase", "pass", "payload_sha256")
            },
            "r1": {
                key: deepcopy(parent_summary["r1"][key])
                for key in (
                    "phase",
                    "pass",
                    "payload_sha256",
                    "preregistered_issue_comment",
                    "verdicts",
                )
            },
        },
        "historical_rounds_13_through_15": deepcopy(
            full["historical_rounds_13_through_15"]
        ),
        "historical_provenance": deepcopy(full["historical_provenance"]),
        "stop_B": {
            "reached": checker["stop_B"],
            "valid": checker["valid"],
            "verdict": checker["verdict"],
            "semantic_id": checker["semantic_id"],
            "permanent_contract": deepcopy(stop_b["contract_admission"]),
            "current_permanent_contract_provenance": deepcopy(
                checker["current_permanent_contract_provenance"]
            ),
            "permanent_contract_regression_provenance": deepcopy(
                stop_b["permanent_contract_regression_provenance"]
            ),
            "round15_hash_roles": deepcopy(stop_b["round15_hash_roles"]),
            "round15_label_ledger_sha256": checker[
                "round15_label_ledger_sha256"
            ],
            "witness_structural_sha256": deepcopy(
                checker["witness_structural_sha256"]
            ),
            "observations_equal": checker["observations_equal"],
            "component_equality": deepcopy(checker["component_equality"]),
            "observation_evidence": {
                "serialization": deepcopy(evidence["serialization"]),
                "witness_sha256": deepcopy(evidence["witness_sha256"]),
                "witness_canonical_bytes": deepcopy(
                    evidence["witness_canonical_bytes"]
                ),
                "common_observation_sha256": evidence[
                    "common_observation_sha256"
                ],
                "common_observation_canonical_bytes": evidence[
                    "common_observation_canonical_bytes"
                ],
            },
            "checker_admission": deepcopy(stop_b["checker_admission"]),
            "query_counts": {
                key: checker[key]
                for key in (
                    "Obs_G_structural_evaluations",
                    "new_v5_candidate_evaluation_calls",
                    "new_global_or_A_block_H1_queries",
                    "new_population_queries",
                )
            },
            "labels": deepcopy(checker["labels"]),
            "labels_differ": checker["labels_differ"],
            "migration_invariants": deepcopy(
                checker["migration_invariants"]
            ),
            "general_two_point_argument": checker[
                "general_two_point_argument"
            ],
            "coverage_limit": checker["coverage_limit"],
        },
        "terminal": deepcopy(full["terminal"]),
    }
    rendered = render_json(summary)
    if len(rendered.encode("utf-8")) >= 100_000:
        raise AssertionError("Stop-B slim summary exceeds 100KB")
    return summary


def parser() -> argparse.ArgumentParser:
    command = argparse.ArgumentParser(description=__doc__)
    command.add_argument(
        "--output",
        type=Path,
        help="write the canonical full Stop-B results JSON",
    )
    command.add_argument(
        "--summary-output",
        type=Path,
        help="write the deterministic slim Stop-B summary JSON",
    )
    return command


def main() -> int:
    command = parser()
    args = command.parse_args()
    if args.output is None and args.summary_output is None:
        command.error("at least one of --output or --summary-output is required")
    full = stop_b_results_report()
    if args.output is not None:
        args.output.write_text(
            render_json(full),
            encoding="utf-8",
            newline="\n",
        )
        print(args.output)
    if args.summary_output is not None:
        summary = stop_b_results_summary(full)
        args.summary_output.write_text(
            render_json(summary),
            encoding="utf-8",
            newline="\n",
        )
        print(args.summary_output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
