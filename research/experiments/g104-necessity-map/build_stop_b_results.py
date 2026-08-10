#!/usr/bin/env python3
"""Build the deterministic G_local-v1 Stop-B full and slim artifacts.

Round 1 through Round 12 are regenerated through the immutable parent API.
Rounds 13 through 15 are provenance-only history: this builder never reruns
their reports, candidates, populations, or H1 queries.  The builder directly
requests the pure G_local-v1 manifest once and the Stop-B checker once.  The
checker performs its own admitted manifest reconstruction, so the effective
manifest construction count is exactly two.
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
    g_local_v1_preregistration_manifest,
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

CHECKER_RESULT_COMPACT_EXPECTED_SHA256 = (
    "0d644121840591cd4303fbda99d94cd887836b001d3993bd9d284bb3c0366c80"
)
CHECKER_RESULT_COMPACT_EXPECTED_BYTES = 55_566
COMMON_OBSERVATION_EXPECTED_SHA256 = (
    "742e6395bb21221fcac070975cbe9505d49d0c75f826289984288776836aa7dc"
)
COMMON_OBSERVATION_EXPECTED_BYTES = 53_279

STOP_B_RESULT_PROVENANCE = {
    "issue_comment": 5245347326,
    "created_at": "2026-08-10T20:04:41Z",
    "updated_at": "2026-08-10T20:04:41Z",
}
G107_STOP_B_SYNC_PROVENANCE = (
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
)

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


def _admit_manifest(manifest: dict[str, object]) -> dict[str, object]:
    record = _compact_record(manifest)
    if not (
        stop_b_source.G_LOCAL_V1_REGISTERED_MANIFEST_SHA256
        == "32e5db03f8f66b091b2594954bd121e2c97c5bfb70fb049c50cd97a070b59969"
        and stop_b_source.G_LOCAL_V1_PREREGISTRATION_COMMENT == 5245279192
        and stop_b_source.G_LOCAL_V1_PREREGISTRATION_CREATED_AT
        == "2026-08-10T19:57:54Z"
        and stop_b_source.G_LOCAL_V1_PREREGISTRATION_UPDATED_AT
        == "2026-08-10T19:57:54Z"
        and record["canonical_sha256"]
        == stop_b_source.G_LOCAL_V1_REGISTERED_MANIFEST_SHA256
        and manifest["preregistered_issue_comment"] is None
        and manifest["checker_executed"] is False
        and manifest["observation_executed"] is False
        and manifest["manifest_contains_its_own_sha256"] is False
        and manifest["dependency_contract"][
            "manifest_calls_round13_14_15_report_or_population"
        ]
        is False
        and manifest["dependency_contract"][
            "later_checker_new_global_or_A_block_H1_queries"
        ]
        == 0
        and manifest["dependency_contract"][
            "later_checker_new_population_queries"
        ]
        == 0
        and manifest["immutable_round15_label_ledger"]["value"]
        == stop_b_source.ROUND15_LABEL_LEDGER
    ):
        raise AssertionError("G_local-v1 pure manifest admission failed")
    return {
        **record,
        "registered_sha256": (
            stop_b_source.G_LOCAL_V1_REGISTERED_MANIFEST_SHA256
        ),
        "preregistration_issue_comment": (
            stop_b_source.G_LOCAL_V1_PREREGISTRATION_COMMENT
        ),
        "preregistration_created_at": (
            stop_b_source.G_LOCAL_V1_PREREGISTRATION_CREATED_AT
        ),
        "preregistration_updated_at": (
            stop_b_source.G_LOCAL_V1_PREREGISTRATION_UPDATED_AT
        ),
        "builder_direct_manifest_requests": 1,
        "checker_internal_manifest_admission_reconstructions": 1,
        "effective_manifest_constructions": 2,
        "admitted": True,
    }


def _admit_checker_result(result: dict[str, object]) -> dict[str, object]:
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
    if not (
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
        and result["registered_manifest_sha256"]
        == stop_b_source.G_LOCAL_V1_REGISTERED_MANIFEST_SHA256
        and result["observations_equal"] is True
        and set(component_equality) == expected_components
        and all(component_equality.values())
        and result["labels"]
        == {"TERNARY-CYCLE-3": True, "TERNARY-CYCLE-6": False}
        and result["labels_differ"] is True
        and all(result[key] == value for key, value in query_counts.items())
    ):
        raise AssertionError("G_local-v1 Stop-B checker result drift")
    return {
        "checker_result": checker_record,
        "common_observation": observation_record,
        "query_counts": query_counts,
        "component_count": len(component_equality),
        "all_components_equal": True,
        "admitted": True,
    }


def _terminal_metadata(coverage_limit: str) -> dict[str, object]:
    return {
        "kind": "B",
        "verdict": "CSTAR-not-expressible-in-G_local-v1",
        "stop_condition_reached": True,
        "stop_condition_A_completion": False,
        "stop_condition_B_G_local_v1_two_point_separation": True,
        "stop_condition_B_finite_exhaustion": False,
        "stop_condition_C_two_valid_same_blocker_no_progress": False,
        "grammar_relative": True,
        "absolute_impossibility_claim": False,
        "task_complete": False,
        "issue_remains_open_until_non_draft_PR_merge": True,
        "prd_retained_until_completion_closeout": True,
        "result_provenance": deepcopy(STOP_B_RESULT_PROVENANCE),
        "G107_sync_provenance": deepcopy(list(G107_STOP_B_SYNC_PROVENANCE)),
        "coverage_limit": coverage_limit,
    }


def stop_b_results_report() -> dict[str, object]:
    """Build full results with one direct manifest and one checker request.

    The checker independently reconstructs and admits the manifest once, so
    one builder run has two effective manifest constructions in total.
    """

    parent_full, parent_summary, parent_admission = _admit_parent_checkpoint()
    history = _admit_historical_rounds()
    manifest = g_local_v1_preregistration_manifest()
    manifest_admission = _admit_manifest(manifest)
    checker_result = check_g_local_v1_stop_b()
    checker_admission = _admit_checker_result(checker_result)
    coverage_limit = checker_result["coverage_limit"]
    return {
        "artifact": "G-104 G_local-v1 Stop-B full result",
        "schema_version": 1,
        "randomness": "none",
        "serialization": deepcopy(CANONICAL_SERIALIZATION),
        "immutable_parent_through_round12": {
            "admission": parent_admission,
            "full_report": deepcopy(parent_full),
            "summary_report": deepcopy(parent_summary),
        },
        "historical_rounds_13_through_15": list(history),
        "g_local_v1": {
            "preregistration_manifest": deepcopy(manifest),
            "manifest_admission": manifest_admission,
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
        "artifact": "G-104 G_local-v1 Stop-B slim result summary",
        "schema_version": 1,
        "randomness": full["randomness"],
        "serialization": full["serialization"],
        "full_results": {
            **full_record,
            "canonical_generator": (
                "build_stop_b_results.py --output <full-path> "
                "--summary-output <summary-path>"
            ),
            "repository_status": "derived; not committed",
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
        "stop_B": {
            "valid": checker["valid"],
            "verdict": checker["verdict"],
            "semantic_id": checker["semantic_id"],
            "registered_manifest": deepcopy(stop_b["manifest_admission"]),
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
            "general_two_point_argument": checker[
                "general_two_point_argument"
            ],
            "coverage_limit": checker["coverage_limit"],
            "result_provenance": deepcopy(STOP_B_RESULT_PROVENANCE),
            "G107_sync_provenance": deepcopy(
                list(G107_STOP_B_SYNC_PROVENANCE)
            ),
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
