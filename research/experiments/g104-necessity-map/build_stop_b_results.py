#!/usr/bin/env python3
"""Build the deterministic G_local-v1 final Stop-B artifacts.

Round 1 through Round 12 are regenerated through the current lifecycle-free
mathematical parent API.
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


HISTORICAL_ROUND13_PARENT_FULL_SHA256 = (
    "cabfbcae7075280a6d10de3c819c25ca2396a21deaed2099bafdd71daa252306"
)
HISTORICAL_ROUND13_PARENT_FULL_BYTES = 3_446_046
HISTORICAL_ROUND13_PARENT_SUMMARY_SHA256 = (
    "afa334056b52938044c0acad9b693a0c437300382b855f32450af5750020caa5"
)
HISTORICAL_ROUND13_PARENT_SUMMARY_BYTES = 95_410
HISTORICAL_ROUND13_PARENT_GIT_COMMIT = (
    "ded12203d2f95fa8f83aadfd3a1e453f6e7efa06"
)
HISTORICAL_PERMANENT_MIGRATION_GIT_COMMIT = (
    "c3a6bada111978a08d82bff5fceffbbea2aa0f51"
)
PARENT_ROUND12_EXPECTED_SHA256 = (
    "c9ab928190491610ff1e394fb16fb4e132f117374a317505fbd2025ab5a09f90"
)

# Calibrated candidate SHA/byte fields are staged here first.  The Issue fields
# remain None until the pure contract and sanitized parent artifacts are
# registered together, and every admission below requires the complete record.
# Mathematical sources contain hashes only; this builder is the sole owner of
# external Issue provenance.
CURRENT_EXTERNAL_REGISTRATION: dict[str, object] | None = {
    "contract_sha256": (
        "5a14faf44049b8906200d5dbd052bc9fd5669ff84dfb6452e6137e98dfbd51c8"
    ),
    "contract_canonical_bytes": 314_114,
    "parent_full_sha256": (
        "7d01eb3a8fb22334644f6a8c6cef1f7cde235e9f17e4607da85969a17109eede"
    ),
    "parent_full_canonical_bytes": 3_446_023,
    "parent_summary_sha256": (
        "556c7279626a4395bc2446bc2f2a1f9af725c24e3ce6aacddfe59cc8ab11ee3e"
    ),
    "parent_summary_canonical_bytes": 95_635,
    "round12_payload_sha256": PARENT_ROUND12_EXPECTED_SHA256,
    "issue_comment": 5248074852,
    "created_at": "2026-08-11T01:43:10Z",
    "updated_at": "2026-08-11T01:43:10Z",
}
CURRENT_EXTERNAL_REGISTRATION_KEYS = frozenset(
    {
        "contract_sha256",
        "contract_canonical_bytes",
        "parent_full_sha256",
        "parent_full_canonical_bytes",
        "parent_summary_sha256",
        "parent_summary_canonical_bytes",
        "round12_payload_sha256",
        "issue_comment",
        "created_at",
        "updated_at",
    }
)
CURRENT_CHECKER_REGRESSION: dict[str, object] | None = {
    "sha256": (
        "645d4ca27215bcd6687734bf2abff87a3a7bb0e778134c051b546937e7ebfde9"
    ),
    "canonical_bytes": 56_881,
    "issue_comment": 5248116625,
    "created_at": "2026-08-11T01:51:03Z",
    "updated_at": "2026-08-11T01:51:03Z",
}
CURRENT_CHECKER_REGRESSION_KEYS = frozenset(
    {"sha256", "canonical_bytes", "issue_comment", "created_at", "updated_at"}
)
COMMON_OBSERVATION_EXPECTED_SHA256 = (
    "742e6395bb21221fcac070975cbe9505d49d0c75f826289984288776836aa7dc"
)
COMMON_OBSERVATION_EXPECTED_BYTES = 53_279

HISTORICAL_PERMANENT_MIGRATION_PROVENANCE = {
    "role": "opaque-git-and-issue-history-provenance",
    "git_commit": HISTORICAL_PERMANENT_MIGRATION_GIT_COMMIT,
    "contract_registration": {
        "sha256": (
            "955b75d7f88c2d7e3f7e516cb83928127fed9cbd8d28bb50572b17c49a7531af"
        ),
        "canonical_bytes": 314_821,
        "issue_comment": 5246699114,
        "created_at": "2026-08-10T22:22:12Z",
        "updated_at": "2026-08-10T22:22:12Z",
    },
    "checker_regression": {
        "sha256": (
            "834d97547d037ebe76fea942a95996f2b2a0bdcfe9f14eda73bc450c4ac9ebca"
        ),
        "canonical_bytes": 56_940,
        "issue_comment": 5246749681,
        "created_at": "2026-08-10T22:28:47Z",
        "updated_at": "2026-08-10T22:28:47Z",
    },
    "current_source_reconstruction_claimed": False,
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
STOP_B_TERMINAL_KEYS = frozenset(
    {
        "kind",
        "role",
        "verdict",
        "stop_condition_reached",
        "stop_condition_A_completion",
        "stop_condition_B_G_local_v1_two_point_separation",
        "stop_condition_B_finite_exhaustion",
        "stop_condition_C_two_valid_same_blocker_no_progress",
        "grammar_relative",
        "absolute_impossibility_claim",
        "coverage_limit",
    }
)
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


def _external_record_complete(
    record: dict[str, object] | None,
    expected_keys: frozenset[str],
) -> bool:
    return (
        record is not None
        and set(record) == expected_keys
        and all(value is not None for value in record.values())
    )


def _round12_payload_sha256(parent_full: dict[str, object]) -> str:
    round12 = parent_full["r2"][
        "round12_post_punit_octahedral_partitioned"
    ]
    return _rendered_record(render_json(round12))[
        "canonical_sha256"
    ]


def _admit_historical_round13_parent(
    round12_sha256: str,
) -> dict[str, object]:
    if not (
        historical_source.ROUND13_PARENT_RESULTS_JSON_SHA256
        == HISTORICAL_ROUND13_PARENT_FULL_SHA256
        and historical_source.ROUND13_PARENT_RESULTS_SUMMARY_JSON_SHA256
        == HISTORICAL_ROUND13_PARENT_SUMMARY_SHA256
        and historical_source.ROUND13_PARENT_ROUND12_PAYLOAD_SHA256
        == PARENT_ROUND12_EXPECTED_SHA256
        == round12_sha256
        and parent_source.HISTORICAL_ROUND13_PARENT_FULL_SHA256
        == HISTORICAL_ROUND13_PARENT_FULL_SHA256
        and parent_source.HISTORICAL_ROUND13_PARENT_SUMMARY_SHA256
        == HISTORICAL_ROUND13_PARENT_SUMMARY_SHA256
    ):
        raise AssertionError("historical Round13 parent provenance drift")
    return {
        "role": "opaque-git-and-issue-history-provenance",
        "git_commit": HISTORICAL_ROUND13_PARENT_GIT_COMMIT,
        "full": {
            "canonical_sha256": HISTORICAL_ROUND13_PARENT_FULL_SHA256,
            "canonical_bytes": HISTORICAL_ROUND13_PARENT_FULL_BYTES,
        },
        "summary": {
            "canonical_sha256": HISTORICAL_ROUND13_PARENT_SUMMARY_SHA256,
            "canonical_bytes": HISTORICAL_ROUND13_PARENT_SUMMARY_BYTES,
        },
        "round12_payload_sha256": PARENT_ROUND12_EXPECTED_SHA256,
        "current_parent_reconstruction_claimed": False,
    }


def _admit_current_parent() -> tuple[
    dict[str, object],
    dict[str, object],
    dict[str, object],
    dict[str, object],
]:
    registration = CURRENT_EXTERNAL_REGISTRATION
    if not (
        _external_record_complete(
            registration,
            CURRENT_EXTERNAL_REGISTRATION_KEYS,
        )
        and parent_source.FULL_RESULTS_EXPECTED_SHA256
        == registration["parent_full_sha256"]
        and parent_source.SUMMARY_RESULTS_EXPECTED_SHA256
        == registration["parent_summary_sha256"]
        and len(parent_source.R2_ROUND_KEYS_THROUGH_ROUND12) == 12
        and parent_source.R2_ROUND_KEYS
        is parent_source.R2_ROUND_KEYS_THROUGH_ROUND12
    ):
        raise AssertionError("current Round-12 parent is not registered")

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
    round12_sha256 = _round12_payload_sha256(parent_full)
    historical_round13_parent = _admit_historical_round13_parent(
        round12_sha256
    )
    if not (
        full_record["canonical_sha256"]
        == registration["parent_full_sha256"]
        and full_record["canonical_bytes"]
        == registration["parent_full_canonical_bytes"]
        and summary_record["canonical_sha256"]
        == registration["parent_summary_sha256"]
        and summary_record["canonical_bytes"]
        == registration["parent_summary_canonical_bytes"]
        and round12_sha256
        == registration["round12_payload_sha256"]
        == PARENT_ROUND12_EXPECTED_SHA256
        and full_record["canonical_sha256"]
        != HISTORICAL_ROUND13_PARENT_FULL_SHA256
        and summary_record["canonical_sha256"]
        != HISTORICAL_ROUND13_PARENT_SUMMARY_SHA256
        and parent_full["schema_version"] == 2
        and parent_full["terminal"]["kind"] == "C"
        and parent_full["terminal"]["role"]
        == "historical-mathematical-stop-C-checkpoint"
        and set(parent_full["terminal"])
        == parent_source.ROUND12_PARENT_TERMINAL_KEYS
        and parent_full["terminal"]["last_provenance_correction"]
        == parent_source.ROUND12_LAST_PROVENANCE_CORRECTION
        and parent_summary["schema_version"] == 2
        and set(parent_summary["terminal"])
        == parent_source.ROUND12_PARENT_SUMMARY_TERMINAL_KEYS
        and parent_summary["terminal"]["last_provenance_correction"]
        == parent_source.ROUND12_LAST_PROVENANCE_CORRECTION
        and tuple(parent_full["r2"])
        == parent_source.R2_ROUND_KEYS_THROUGH_ROUND12
    ):
        raise AssertionError("current Round-12 parent reproduction failed")
    return parent_full, parent_summary, {
        "full": full_record,
        "summary": summary_record,
        "round12_payload_sha256": round12_sha256,
        "round_count": 12,
        "external_registration_exact": True,
        "reproduced_fail_closed": True,
    }, historical_round13_parent


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
    registration = CURRENT_EXTERNAL_REGISTRATION
    if not _external_record_complete(
        registration,
        CURRENT_EXTERNAL_REGISTRATION_KEYS,
    ):
        raise AssertionError("current permanent contract is not registered")
    record = _compact_record(contract)
    source_sha256 = stop_b_source.G_LOCAL_V1_PERMANENT_CONTRACT_SHA256
    historical_bridge = contract["historical_execution_bridge"]
    admitted = (
        set(registration) == CURRENT_EXTERNAL_REGISTRATION_KEYS
        and source_sha256 == registration["contract_sha256"]
        and record["canonical_sha256"]
        == registration["contract_sha256"]
        and record["canonical_bytes"]
        == registration["contract_canonical_bytes"]
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
        "current_permanent_contract_sha256": source_sha256,
        "external_registration_exact": True,
        "builder_direct_contract_requests": 1,
        "checker_internal_contract_admission_reconstructions": 1,
        "effective_contract_constructions": 2,
        "admitted": admitted,
    }


def _admit_checker_result(
    result: dict[str, object],
    contract: dict[str, object],
) -> dict[str, object]:
    registration = CURRENT_EXTERNAL_REGISTRATION
    regression = CURRENT_CHECKER_REGRESSION
    if not (
        _external_record_complete(
            registration,
            CURRENT_EXTERNAL_REGISTRATION_KEYS,
        )
        and _external_record_complete(
            regression,
            CURRENT_CHECKER_REGRESSION_KEYS,
        )
    ):
        raise AssertionError("current Stop-B checker is not registered")
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
    admitted = (
        set(registration) == CURRENT_EXTERNAL_REGISTRATION_KEYS
        and set(regression) == CURRENT_CHECKER_REGRESSION_KEYS
        and checker_record["canonical_sha256"]
        == regression["sha256"]
        and checker_record["canonical_bytes"]
        == regression["canonical_bytes"]
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
        and result["current_permanent_contract_sha256"]
        == registration["contract_sha256"]
        and result["historical_execution_provenance"]
        == contract["historical_execution_bridge"]["record"]
        and result["observations_equal"] is True
        and set(component_equality) == expected_components
        and all(component_equality.values())
        and result["labels"]
        == {"TERNARY-CYCLE-3": True, "TERNARY-CYCLE-6": False}
        and result["labels_differ"] is True
        and all(result[key] == value for key, value in query_counts.items())
        and result["verification_invariants"]
        == {
            "historical_common_observation_bridge_matched": True,
            "historical_round15_label_separation_reproduced": True,
            "new_v5_candidate_evaluation_calls": 0,
            "new_global_or_A_block_H1_queries": 0,
            "new_population_queries": 0,
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
        "checker_regression_exact": True,
        "component_count": len(component_equality),
        "all_components_equal": all(component_equality.values()),
        "admitted": admitted,
    }


def _terminal_metadata(coverage_limit: str) -> dict[str, object]:
    terminal = {
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
    if set(terminal) != STOP_B_TERMINAL_KEYS:
        raise AssertionError("Stop-B terminal schema drift")
    return terminal


def stop_b_results_report() -> dict[str, object]:
    """Build full results with one direct contract and one checker request.

    The checker independently reconstructs and admits the contract once, so
    one builder run has two effective contract constructions in total.
    """

    (
        parent_full,
        parent_summary,
        parent_admission,
        historical_round13_parent,
    ) = _admit_current_parent()
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
        "current_external_registration": deepcopy(
            CURRENT_EXTERNAL_REGISTRATION
        ),
        "current_parent_through_round12": {
            "admission": parent_admission,
            "full_report": deepcopy(parent_full),
            "summary_report": deepcopy(parent_summary),
        },
        "historical_rounds_13_through_15": list(history),
        "historical_provenance": {
            "round13_parent": historical_round13_parent,
            "superseded_permanent_migration": deepcopy(
                HISTORICAL_PERMANENT_MIGRATION_PROVENANCE
            ),
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
            "current_checker_regression": deepcopy(
                CURRENT_CHECKER_REGRESSION
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
    if set(full["terminal"]) != STOP_B_TERMINAL_KEYS:
        raise AssertionError("Stop-B summary terminal schema drift")
    if not (
        _external_record_complete(
            CURRENT_EXTERNAL_REGISTRATION,
            CURRENT_EXTERNAL_REGISTRATION_KEYS,
        )
        and full["current_external_registration"]
        == CURRENT_EXTERNAL_REGISTRATION
        and set(full["current_external_registration"])
        == CURRENT_EXTERNAL_REGISTRATION_KEYS
        and _external_record_complete(
            CURRENT_CHECKER_REGRESSION,
            CURRENT_CHECKER_REGRESSION_KEYS,
        )
        and full["g_local_v1"]["current_checker_regression"]
        == CURRENT_CHECKER_REGRESSION
        and set(full["g_local_v1"]["current_checker_regression"])
        == CURRENT_CHECKER_REGRESSION_KEYS
    ):
        raise AssertionError("Stop-B external provenance projection drift")
    full_record = _rendered_record(render_json(full))
    parent = full["current_parent_through_round12"]
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
        "current_external_registration": deepcopy(
            full["current_external_registration"]
        ),
        "current_parent_through_round12": {
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
            "current_permanent_contract_sha256": checker[
                "current_permanent_contract_sha256"
            ],
            "current_checker_regression": deepcopy(
                stop_b["current_checker_regression"]
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
            "verification_invariants": deepcopy(
                checker["verification_invariants"]
            ),
            "general_two_point_argument": checker[
                "general_two_point_argument"
            ],
            "coverage_limit": checker["coverage_limit"],
        },
        "terminal": deepcopy(full["terminal"]),
    }
    if set(summary["terminal"]) != STOP_B_TERMINAL_KEYS:
        raise AssertionError("Stop-B summary terminal projection drift")
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
