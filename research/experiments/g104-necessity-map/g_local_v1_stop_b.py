#!/usr/bin/env python3
"""Permanent structural contract, immutable ledger, and Stop-B checker.

The dependency direction is intentionally one way::

    structural input -> g_local_v1 observation -> equality checker <- ledger

The pure permanent contract does not construct either witness and does not
call the observation evaluator or checker.  Historical execution values are
opaque Git/Issue provenance rather than a claim that an old manifest can be
reconstructed from current source.  The checker fails closed until the current
permanent contract has separately registered migration provenance.
"""

from __future__ import annotations

import ast
from collections import Counter
from copy import deepcopy
from fractions import Fraction as StdFraction
from hashlib import sha256
import json
from pathlib import Path
import sys
from typing import Iterable

import g_local_v1 as structural
import necessity_map as base_structural
import r2_hunt as r2_structural


ROUND15_PREREGISTRATION_COMMENT = 5235347217
ROUND15_PREREGISTRATION_CREATED_AT = "2026-08-10T02:51:13Z"
ROUND15_PREREGISTRATION_UPDATED_AT = "2026-08-10T02:51:13Z"
ROUND15_REGISTERED_MANIFEST_SHA256 = (
    "e5f2d6630ee2f37de409f5e2c0757eed17b24509ca3cd3f7d924c130b6219c3b"
)
ROUND15_RESULT_COMMENT = 5235636358
ROUND15_RESULT_CREATED_AT = "2026-08-10T03:46:15Z"
ROUND15_RESULT_UPDATED_AT = "2026-08-10T03:46:15Z"
ROUND15_RESULT_PAYLOAD_SHA256 = (
    "21b59632026d5ec0f104700f26808a8455e2ca607802a108c6934f68e8911969"
)
ROUND15_RESULT_CANONICAL_BYTES = 97_792
ROUND15_RESULT_SERIALIZATION = {
    "encoding": "UTF-8",
    "ensure_ascii": False,
    "indent": 2,
    "sort_keys": True,
    "trailing_newline": True,
}

TERNARY_CYCLE_3_INPUT_SHA256 = (
    "452517a5dd3df09eea96f4de0c0b737f274384c239267aeba2d5ba06fda616a2"
)
TERNARY_CYCLE_6_INPUT_SHA256 = (
    "0e92de476cd0af4dbeb80290afff463354da87c01c4548bab5d7806927d1d180"
)

ROUND15_LABEL_LEDGER = {
    "kind": "immutable-round15-uniformity-label-ledger-v1",
    "preregistration_issue_comment": ROUND15_PREREGISTRATION_COMMENT,
    "result_provenance": {
        "issue_comment": ROUND15_RESULT_COMMENT,
        "created_at": ROUND15_RESULT_CREATED_AT,
        "updated_at": ROUND15_RESULT_UPDATED_AT,
        "canonical_payload_sha256": ROUND15_RESULT_PAYLOAD_SHA256,
        "canonical_bytes": ROUND15_RESULT_CANONICAL_BYTES,
        "serialization": ROUND15_RESULT_SERIALIZATION,
    },
    "labels": (
        {
            "fixture": "TERNARY-CYCLE-3",
            "field_path": (
                "exact_verification.fixtures[name=\"TERNARY-CYCLE-3\"]"
                ".uniform"
            ),
            "uniform": True,
            "name_free_structural_sha256": TERNARY_CYCLE_3_INPUT_SHA256,
            "fixture_source": "r2_hunt.py::round15_verification_fixtures()",
            "registered_projection_source": (
                "round15_preregistration_manifest.fixtures[name=\""
                "TERNARY-CYCLE-3\"].name_free_semantic_sha256"
            ),
            "registered_projection_value": TERNARY_CYCLE_3_INPUT_SHA256,
        },
        {
            "fixture": "TERNARY-CYCLE-6",
            "field_path": (
                "exact_verification.fixtures[name=\"TERNARY-CYCLE-6\"]"
                ".uniform"
            ),
            "uniform": False,
            "name_free_structural_sha256": TERNARY_CYCLE_6_INPUT_SHA256,
            "fixture_source": "r2_hunt.py::round15_verification_fixtures()",
            "registered_projection_source": (
                "round15_preregistration_manifest.fixtures[name=\""
                "TERNARY-CYCLE-6\"].name_free_semantic_sha256"
            ),
            "registered_projection_value": TERNARY_CYCLE_6_INPUT_SHA256,
        },
    ),
    "caller_supplied_labels_permitted": False,
}

G_LOCAL_V1_PERMANENT_CONTRACT_SERIALIZATION = {
    "encoding": "UTF-8",
    "ensure_ascii": True,
    "sort_keys": True,
    "separators": [",", ":"],
    "trailing_newline": False,
    "self_contained_hash": False,
}

G_LOCAL_V1_HISTORICAL_EXECUTION = {
    "role": "opaque-git-and-issue-history-provenance",
    "git_commit": "ded12203d2f95fa8f83aadfd3a1e453f6e7efa06",
    "preregistration": {
        "issue_comment": 5245279192,
        "manifest_sha256": (
            "32e5db03f8f66b091b2594954bd121e2c97c5bfb70fb049c50cd97a070b59969"
        ),
        "manifest_canonical_bytes": 311_163,
    },
    "result": {
        "issue_comment": 5245347326,
        "checker_sha256": (
            "0d644121840591cd4303fbda99d94cd887836b001d3993bd9d284bb3c0366c80"
        ),
        "checker_canonical_bytes": 55_566,
        "common_observation_sha256": (
            "742e6395bb21221fcac070975cbe9505d49d0c75f826289984288776836aa7dc"
        ),
        "common_observation_canonical_bytes": 53_279,
    },
    "old_manifest_reconstructed_from_current_source": False,
    "old_checker_reconstructed_from_current_source": False,
}

# Filled only after the permanent contract has been generated, reviewed, and
# posted as a migration record.  None keeps every pre-registration checker
# call fail-closed and is excluded from the permanent source fingerprint.
G_LOCAL_V1_PERMANENT_CONTRACT_SHA256: str | None = "955b75d7f88c2d7e3f7e516cb83928127fed9cbd8d28bb50572b17c49a7531af"
G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_ISSUE_COMMENT: int | None = 5246699114
G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_CREATED_AT: str | None = "2026-08-10T22:22:12Z"
G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_UPDATED_AT: str | None = "2026-08-10T22:22:12Z"


def _compact_json(value: object) -> str:
    return json.dumps(
        value,
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    )


def round15_label_ledger_canonical_json() -> str:
    return _compact_json(ROUND15_LABEL_LEDGER)


def round15_label_ledger_sha256() -> str:
    return sha256(
        round15_label_ledger_canonical_json().encode("utf-8")
    ).hexdigest()


def _identity_split_payload(
    neutral_edge_count: int,
    faces: tuple[tuple[int, int, int], ...],
) -> dict[str, object]:
    edges = [[0, 0]] + [[1, 1] for _ in range(neutral_edge_count)]
    coarse_neutral_supports = [[0, 1] for _ in range(neutral_edge_count)]
    fine_neutral_supports = [[2] for _ in range(neutral_edge_count)]
    return {
        "K1_supports_derived_by_intersection": True,
        "chartSupport_compatible": True,
        "targets": {
            "coarse_count": 2,
            "fine_count": 3,
            "canonical_surjective_factor_pi": [0, 0, 1],
        },
        "coarse": {
            "nerve": {
                "vertices": 2,
                "edges": edges,
                "faces": [list(face) for face in faces],
            },
            "chart_supports": [[0], [0, 1]],
            "derived_edge_supports": [[0]] + coarse_neutral_supports,
            "derived_face_supports": [[0, 1] for _ in faces],
        },
        "fine": {
            "nerve": {
                "vertices": 2,
                "edges": edges,
                "faces": [list(face) for face in faces],
            },
            "chart_supports": [[0, 1], [2]],
            "derived_edge_supports": [[0, 1]] + fine_neutral_supports,
            "derived_face_supports": [[2] for _ in faces],
        },
        "morphism": {
            "vertex_map": [0, 1],
            "edge_map": list(range(neutral_edge_count + 1)),
            "face_map": list(range(len(faces))),
        },
    }


G_LOCAL_V1_WITNESS_INPUTS = {
    "TERNARY-CYCLE-3": _identity_split_payload(
        3,
        ((1, 2, 3), (2, 3, 1), (3, 1, 2)),
    ),
    "TERNARY-CYCLE-6": _identity_split_payload(
        6,
        (
            (1, 2, 3),
            (2, 3, 4),
            (3, 4, 5),
            (4, 5, 6),
            (5, 6, 1),
            (6, 1, 2),
        ),
    ),
}
G_LOCAL_V1_WITNESS_INPUT_SHA256 = {
    "TERNARY-CYCLE-3": TERNARY_CYCLE_3_INPUT_SHA256,
    "TERNARY-CYCLE-6": TERNARY_CYCLE_6_INPUT_SHA256,
}


def _hand_rows(
    payloads_with_counts: Iterable[tuple[dict[str, object], int]],
    payload_key: str,
) -> list[dict[str, object]]:
    """Canonicalize hand-written rows without calling the Obs evaluator."""

    counts: Counter[str] = Counter()
    for payload, count in payloads_with_counts:
        if count not in (1, 2):
            raise AssertionError("hand expectation escaped clip2")
        counts[_compact_json(payload)] += count
    return [
        {
            payload_key: json.loads(payload),
            "count": min(count, 2),
        }
        for payload, count in sorted(counts.items())
    ]


def _hand_flags(
    side: str,
    cell_type: str,
) -> dict[str, bool]:
    flags = {
        "critical": False,
        "guard": False,
        "port": False,
        "bridge": False,
        "self-loop": False,
        "FaceTwin": False,
    }
    if cell_type == "vertex":
        flags["critical"] = True
        flags["port"] = side == "fine"
    elif cell_type == "edge":
        flags["critical"] = True
        flags["guard"] = side == "coarse"
        flags["self-loop"] = True
    return flags


def _hand_label(
    side: str,
    cell_type: str,
    support: tuple[int, ...],
    pi_image: tuple[int, ...],
) -> dict[str, object]:
    return {
        "side": side,
        "cell_type": cell_type,
        "map_status": "mapped",
        "support": list(support),
        "pi_image": list(pi_image),
        "flags": _hand_flags(side, cell_type),
    }


def _hand_relation(kind: str, slot: str | int) -> dict[str, object]:
    sign = "+" if kind == "boundary" and slot in (0, 2) else None
    if kind == "boundary" and slot == 1:
        sign = "-"
    return {"kind": kind, "slot": slot, "sign": sign}


def _hand_stub_rows(
    *rows: tuple[str, str | int, int],
) -> list[dict[str, object]]:
    return _hand_rows(
        (
            ({"cell_type": cell_type, "slot": slot}, count)
            for cell_type, slot, count in rows
        ),
        "stub",
    )


def _hand_descriptor(
    neighbor_label: dict[str, object],
    relations: tuple[dict[str, object], ...],
    outward_stub_histogram: list[dict[str, object]],
) -> dict[str, object]:
    return {
        "neighbor_label": neighbor_label,
        "relations": sorted(relations, key=_compact_json),
        "outward_stub_histogram": outward_stub_histogram,
    }


def _hand_ball(
    root_label: dict[str, object],
    *descriptors_with_counts: tuple[dict[str, object], int],
) -> dict[str, object]:
    return {
        "root_label": root_label,
        "neighbor_descriptors": _hand_rows(
            descriptors_with_counts,
            "descriptor",
        ),
    }


def _hand_anchor_balls(
    side: str,
    support: tuple[int, ...],
    pi_image: tuple[int, ...],
) -> tuple[dict[str, object], ...]:
    chart = _hand_label(side, "chart", support, pi_image)
    vertex = _hand_label(side, "vertex", support, pi_image)
    edge = _hand_label(side, "edge", support, pi_image)
    chart_at = _hand_relation("chart-at", "chart-at")
    endpoint0 = _hand_relation("endpoint", 0)
    endpoint1 = _hand_relation("endpoint", 1)
    return (
        _hand_ball(
            chart,
            (
                _hand_descriptor(
                    vertex,
                    (chart_at,),
                    _hand_stub_rows(
                        ("edge", 0, 1),
                        ("edge", 1, 1),
                    ),
                ),
                1,
            ),
        ),
        _hand_ball(
            vertex,
            (
                _hand_descriptor(chart, (chart_at,), []),
                1,
            ),
            (
                _hand_descriptor(edge, (endpoint0, endpoint1), []),
                1,
            ),
        ),
        _hand_ball(
            edge,
            (
                _hand_descriptor(
                    vertex,
                    (endpoint0, endpoint1),
                    _hand_stub_rows(("chart", "chart-at", 1)),
                ),
                1,
            ),
        ),
    )


def _hand_neutral_balls(
    side: str,
    support: tuple[int, ...],
    pi_image: tuple[int, ...],
) -> tuple[dict[str, object], ...]:
    chart = _hand_label(side, "chart", support, pi_image)
    vertex = _hand_label(side, "vertex", support, pi_image)
    edge = _hand_label(side, "edge", support, pi_image)
    face = _hand_label(side, "face", support, pi_image)
    chart_at = _hand_relation("chart-at", "chart-at")
    endpoints = (
        _hand_relation("endpoint", 0),
        _hand_relation("endpoint", 1),
    )
    boundaries = tuple(_hand_relation("boundary", slot) for slot in range(3))

    chart_ball = _hand_ball(
        chart,
        (
            _hand_descriptor(
                vertex,
                (chart_at,),
                _hand_stub_rows(
                    ("edge", 0, 2),
                    ("edge", 1, 2),
                ),
            ),
            1,
        ),
    )
    vertex_ball = _hand_ball(
        vertex,
        (_hand_descriptor(chart, (chart_at,), []), 1),
        (
            _hand_descriptor(
                edge,
                endpoints,
                _hand_stub_rows(
                    ("face", 0, 1),
                    ("face", 1, 1),
                    ("face", 2, 1),
                ),
            ),
            2,
        ),
    )
    edge_descriptors: list[tuple[dict[str, object], int]] = [
        (
            _hand_descriptor(
                vertex,
                endpoints,
                _hand_stub_rows(
                    ("chart", "chart-at", 1),
                    ("edge", 0, 2),
                    ("edge", 1, 2),
                ),
            ),
            1,
        )
    ]
    for slot in range(3):
        edge_descriptors.append(
            (
                _hand_descriptor(
                    face,
                    (boundaries[slot],),
                    _hand_stub_rows(
                        *tuple(
                            ("edge", other, 1)
                            for other in range(3)
                            if other != slot
                        )
                    ),
                ),
                1,
            )
        )
    edge_ball = _hand_ball(edge, *edge_descriptors)

    face_descriptors: list[tuple[dict[str, object], int]] = []
    for slot in range(3):
        face_descriptors.append(
            (
                _hand_descriptor(
                    edge,
                    (boundaries[slot],),
                    _hand_stub_rows(
                        ("vertex", 0, 1),
                        ("vertex", 1, 1),
                        *tuple(
                            ("face", other, 1)
                            for other in range(3)
                            if other != slot
                        ),
                    ),
                ),
                1,
            )
        )
    face_ball = _hand_ball(face, *face_descriptors)
    return chart_ball, vertex_ball, edge_ball, face_ball


def _hand_scope(
    *,
    whole: bool,
    coarse_anchor: tuple[tuple[int, ...], tuple[int, ...]] | None,
    coarse_neutral: tuple[tuple[int, ...], tuple[int, ...]] | None,
    fine_anchor: tuple[tuple[int, ...], tuple[int, ...]] | None,
    fine_neutral: tuple[tuple[int, ...], tuple[int, ...]] | None,
) -> dict[str, object]:
    ball_rows: list[tuple[dict[str, object], int]] = []
    for side, anchor, neutral in (
        ("coarse", coarse_anchor, coarse_neutral),
        ("fine", fine_anchor, fine_neutral),
    ):
        if anchor is not None:
            ball_rows.extend(
                (ball, 1)
                for ball in _hand_anchor_balls(side, *anchor)
            )
        if neutral is not None:
            neutral_balls = _hand_neutral_balls(side, *neutral)
            ball_rows.extend(
                (ball, 2 if index in (2, 3) else 1)
                for index, ball in enumerate(neutral_balls)
            )
    conditions = (
        {"C0*": False, "C5*": True, "C6*": True}
        if whole
        else {}
    )
    return {
        "conditions": conditions,
        "packet_kind_union": [],
        "rooted_ball_histogram": _hand_rows(ball_rows, "ball"),
    }


G_LOCAL_V1_HAND_SCOPE_SHAPES = {
    "whole": {
        "coarse_anchor": ((0,), (0,)),
        "coarse_neutral": ((0, 1), (0, 1)),
        "fine_anchor": ((0, 1), (0,)),
        "fine_neutral": ((2,), (1,)),
    },
    "A0": {
        "coarse_anchor": ((0,), (0,)),
        "coarse_neutral": ((0,), (0,)),
        "fine_anchor": ((0, 1), (0,)),
        "fine_neutral": None,
    },
    "A1": {
        "coarse_anchor": None,
        "coarse_neutral": ((1,), (1,)),
        "fine_anchor": None,
        "fine_neutral": ((2,), (1,)),
    },
    "A01": {
        "coarse_anchor": ((0,), (0,)),
        "coarse_neutral": ((0, 1), (0, 1)),
        "fine_anchor": ((0, 1), (0,)),
        "fine_neutral": ((2,), (1,)),
    },
}
G_LOCAL_V1_HAND_CONDITIONS = {
    "whole": {"C0*": False, "C5*": True, "C6*": True},
    "A0": {"C1*": False, "C2*": False, "C3*": True, "C4*": False},
    "A1": {"C1*": True, "C2*": True, "C3*": True, "C4*": True},
    "A01": {"C1*": True, "C2*": True, "C3*": True, "C4*": True},
}


def _hand_expected_common_observation() -> dict[str, object]:
    scopes = {
        name: _hand_scope(
            whole=name == "whole",
            **shape,
        )
        for name, shape in G_LOCAL_V1_HAND_SCOPE_SHAPES.items()
    }
    for name, conditions in G_LOCAL_V1_HAND_CONDITIONS.items():
        if scopes[name]["conditions"] not in ({}, conditions):
            raise AssertionError("hand scope carried an unexpected condition")
        scopes[name]["conditions"] = conditions
    return {
        "aggregate_C0_through_C6": [
            False,
            False,
            False,
            True,
            False,
            True,
            True,
        ],
        "whole": scopes["whole"],
        "A_record_histogram": _hand_rows(
            ((scopes[name], 1) for name in ("A0", "A1", "A01")),
            "record",
        ),
    }


# This is constructed solely from the hand-authored local schema above.  It is
# never sampled from either witness and never calls the structural evaluator.
G_LOCAL_V1_EXPECTED_COMMON_OBS = _hand_expected_common_observation()
G_LOCAL_V1_HAND_EXPECTATION = {
    "aggregate_C0_through_C6": [False, False, False, True, False, True, True],
    "whole_conditions": {"C0*": False, "C5*": True, "C6*": True},
    "A_condition_multiset": (
        {"C1*": False, "C2*": False, "C3*": True, "C4*": False},
        {"C1*": True, "C2*": True, "C3*": True, "C4*": True},
        {"C1*": True, "C2*": True, "C3*": True, "C4*": True},
    ),
    "packet_kind_union_every_scope": (),
    "map_status_every_root": "mapped",
    "flags": {
        "coarse_vertex": ("critical",),
        "coarse_edge": ("critical", "guard", "self-loop"),
        "fine_vertex": ("critical", "port"),
        "fine_edge": ("critical", "self-loop"),
        "face_true_flags": (),
        "bridge_true_roots": (),
        "FaceTwin_true_roots": (),
    },
    "outer_histogram": {
        "anchor_chart": 1,
        "anchor_vertex": 1,
        "anchor_edge": 1,
        "neutral_chart": 1,
        "neutral_vertex": 1,
        "neutral_edge": 2,
        "neutral_face": 2,
        "A0_fine_roots": "anchor-only",
        "A1_roots": "neutral-only",
    },
    "component_equality_required": (
        "aggregate",
        "whole",
        "all_nonempty_A_histogram",
        "every_side_and_root_type_histogram",
        "final_canonical_bytes",
    ),
    "generated_from_engine_observation": False,
}
G_LOCAL_V1_HAND_CONTROL_EXPECTATIONS = {
    "multiplicity": {
        "one_differs_from_two": True,
        "two_equals_three_equals_six_after_clip2": True,
    },
    "mutations_that_must_change_the_observation": (
        "self-loop-to-nonloop-neighbor-identity",
        "fine-edge-mapped-to-None",
        "fine-face-mapped-to-None",
        "support",
        "FaceTwin",
        "bridge",
        "guard",
        "port",
        "packet-positive",
    ),
    "raw_A_fixture_truth_or_ledger_fields_in_observation": False,
}

G_LOCAL_V1_CHECKER_SOURCE_ENTRYPOINTS = (
    "check_g_local_v1_stop_b",
    "g_local_v1_permanent_contract_manifest",
)
G_LOCAL_V1_R2_WITNESS_ADMISSION_ENTRYPOINTS = (
    "_case_semantic_payload_json",
    "round15_verification_fixtures",
)
G_LOCAL_V1_STANDARD_LIBRARY_DEPENDENCIES = (
    "ast",
    "collections.Counter",
    "copy.deepcopy",
    "dataclasses.dataclass",
    "fractions.Fraction",
    "hashlib.sha256",
    "itertools.combinations",
    "itertools.permutations",
    "itertools.product",
    "json",
    "pathlib.Path",
    "sys",
    "typing.Iterable",
)
G_LOCAL_V1_FORBIDDEN_REACHABLE_SYMBOLS = (
    "ROUND15_LABEL_LEDGER",
    "STOP_B_VERDICT",
    "analyze_h1",
    "block_analyses",
    "candidate_and_nonuniform",
    "comparison_rank",
    "injective",
    "is_uniform",
    "round13_report",
    "round14_report",
    "round15_report",
    "surjective",
    "uniform_and_not_candidate",
)
G_LOCAL_V1_SOURCE_FILES = {
    "observation": "g_local_v1.py",
    "checker": "g_local_v1_stop_b.py",
    "r2_structural": "r2_hunt.py",
    "base_structural": "necessity_map.py",
}
G_LOCAL_V1_SOURCE_NORMALIZATION = {
    "read_encoding": "UTF-8",
    "newline_normalization": "CRLF-and-CR-to-LF",
    "trailing_newline_preserved": True,
    "hash_input": "normalized-UTF-8-bytes",
}
G_LOCAL_V1_PERMANENT_CONTRACT_REGISTRATION_FIELDS = (
    "G_LOCAL_V1_PERMANENT_CONTRACT_SHA256",
    "G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_ISSUE_COMMENT",
    "G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_CREATED_AT",
    "G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_UPDATED_AT",
)
G_LOCAL_V1_PERMANENT_CONTRACT_REGISTRATION_NORMALIZATION = {
    "base_normalization": G_LOCAL_V1_SOURCE_NORMALIZATION,
    "normalized_assignment_fields": (
        G_LOCAL_V1_PERMANENT_CONTRACT_REGISTRATION_FIELDS
    ),
    "canonical_assignment_value": "None",
    "all_other_source_bytes_preserved": True,
}
G_LOCAL_V1_REQUIRED_IMPORT_BINDINGS = {
    "g_local_v1.py": {
        "necessity_map": {
            "UniformComparison": "UniformComparison",
            "nonempty_subsets": "nonempty_subsets",
        },
        "r2_hunt": {
            "ReducedSide": "ReducedSide",
            "ScopedComparison": "ScopedComparison",
            "V5CollapseState": "V5CollapseState",
            "_apply_v5_packet": "_apply_v5_packet",
            "_a_scope": "_a_scope",
            "_active_fine_vertices": "_active_fine_vertices",
            "_c0": "_c0",
            "_c1": "_c1",
            "_c2": "_c2",
            "_c3": "_c3",
            "_c4": "_c4",
            "_face_classes": "_face_classes",
            "_path_without_edge": "_path_without_edge",
            "_v4_c5_c6": "_v4_c5_c6",
            "_v5_packet_variants": "_v5_packet_variants",
            "_v5_terminal_reductions": "_v5_terminal_reductions",
        },
    },
    "r2_hunt.py": {
        "necessity_map": {
            "H1Analysis": "H1Analysis",
            "Matrix": "Matrix",
            "Nerve": "Nerve",
            "NerveMorphism": "NerveMorphism",
            "UniformComparison": "UniformComparison",
            "analyze_h1": "analyze_h1",
            "calibration_fixtures": "calibration_fixtures",
            "canonical_core_factors": "canonical_core_factors",
            "canonical_firing_fixture": "canonical_firing_fixture",
            "core_incidence_templates": "core_incidence_templates",
            "derived_cell_supports": "derived_cell_supports",
            "legacy_positive_fixture": "legacy_positive_fixture",
            "nonempty_subsets": "nonempty_subsets",
            "r0_report": "r0_report",
            "r1_report": "r1_report",
            "r1_necessity_witnesses": "r1_necessity_witnesses",
            "required_fixture_catalog_summary": (
                "required_fixture_catalog_summary"
            ),
            "support_hole_fixture": "support_hole_fixture",
        },
    },
    "g_local_v1_stop_b.py": {
        "g_local_v1": {"g_local_v1": "structural"},
        "necessity_map": {"necessity_map": "base_structural"},
        "r2_hunt": {"r2_hunt": "r2_structural"},
    },
    "necessity_map.py": {
        "fractions": {"Fraction": "Fraction"},
    },
}


def _source_text(filename: str) -> str:
    source = (Path(__file__).resolve().parent / filename).read_text(
        encoding="utf-8"
    )
    return source.replace("\r\n", "\n").replace("\r", "\n")


def _normalized_full_source_record(
    source: str,
    *,
    include_source: bool,
) -> dict[str, object]:
    encoded = source.encode("utf-8")
    record: dict[str, object] = {
        "normalization": G_LOCAL_V1_SOURCE_NORMALIZATION,
        "normalized_full_source_sha256": sha256(encoded).hexdigest(),
        "normalized_full_source_bytes": len(encoded),
    }
    if include_source:
        record["normalized_full_source"] = source
    return record


def _registration_normalized_checker_source(
    source: str,
    tree: ast.Module,
) -> str:
    encoded = source.encode("utf-8")
    lines = encoded.splitlines(keepends=True)
    spans: list[tuple[int, int]] = []
    found: set[str] = set()
    registered_fields = set(
        G_LOCAL_V1_PERMANENT_CONTRACT_REGISTRATION_FIELDS
    )
    for node in tree.body:
        if not isinstance(node, (ast.Assign, ast.AnnAssign)):
            continue
        targets = node.targets if isinstance(node, ast.Assign) else (node.target,)
        names = {
            target.id for target in targets if isinstance(target, ast.Name)
        }
        selected = names & registered_fields
        if not selected:
            continue
        if len(selected) != 1 or node.value is None:
            raise AssertionError("checker registration assignment drift")
        value = node.value
        start = sum(len(line) for line in lines[: value.lineno - 1])
        start += value.col_offset
        end = sum(len(line) for line in lines[: value.end_lineno - 1])
        end += value.end_col_offset
        spans.append((start, end))
        found.update(selected)
    if found != registered_fields:
        raise AssertionError("checker registration field domain drift")
    for start, end in sorted(spans, reverse=True):
        encoded = encoded[:start] + b"None" + encoded[end:]
    return encoded.decode("utf-8")


def _registration_normalized_checker_source_record(
    source: str,
    tree: ast.Module,
) -> dict[str, object]:
    normalized = _registration_normalized_checker_source(source, tree)
    encoded = normalized.encode("utf-8")
    return {
        "registration_normalization": (
            G_LOCAL_V1_PERMANENT_CONTRACT_REGISTRATION_NORMALIZATION
        ),
        "registration_normalized_full_source_sha256": sha256(
            encoded
        ).hexdigest(),
        "registration_normalized_full_source_bytes": len(encoded),
    }


def _top_level_definitions(
    tree: ast.Module,
) -> dict[str, ast.FunctionDef | ast.AsyncFunctionDef | ast.ClassDef]:
    return {
        node.name: node
        for node in tree.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef))
    }


def _function_definitions(
    tree: ast.Module,
) -> dict[str, ast.FunctionDef | ast.AsyncFunctionDef]:
    nodes = [
        node
        for node in tree.body
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
    ]
    result = {node.name: node for node in nodes}
    if len(result) != len(nodes):
        raise AssertionError("duplicate top-level function definition")
    return result


def _direct_name_calls(node: ast.AST) -> frozenset[str]:
    return frozenset(
        child.func.id
        for child in ast.walk(node)
        if isinstance(child, ast.Call) and isinstance(child.func, ast.Name)
    )


def _function_closure(
    tree: ast.Module,
    entrypoints: Iterable[str],
) -> tuple[str, ...]:
    functions = _function_definitions(tree)
    pending = list(entrypoints)
    closure: set[str] = set()
    while pending:
        name = pending.pop()
        if name in closure:
            continue
        if name not in functions:
            raise AssertionError(f"missing structural source entrypoint: {name}")
        closure.add(name)
        pending.extend(
            sorted(_direct_name_calls(functions[name]) & functions.keys())
        )
    return tuple(sorted(closure))


def _node_source(source: str, node: ast.AST) -> str:
    if not hasattr(node, "lineno") or not hasattr(node, "end_lineno"):
        raise AssertionError("AST node has no exact source extent")
    lines = source.splitlines(keepends=True)
    decorators = getattr(node, "decorator_list", ())
    start = min(
        [node.lineno] + [decorator.lineno for decorator in decorators]
    )
    chunk = "".join(lines[start - 1 : node.end_lineno])
    return chunk.rstrip("\n") + "\n"


def _source_rows(
    source: str,
    tree: ast.Module,
    names: Iterable[str],
) -> list[dict[str, object]]:
    definitions = _top_level_definitions(tree)
    rows = []
    for name in sorted(names):
        if name not in definitions:
            raise AssertionError(f"source definition disappeared: {name}")
        exact = _node_source(source, definitions[name])
        rows.append(
            {
                "locator": name,
                "source": exact,
                "source_sha256": sha256(exact.encode("utf-8")).hexdigest(),
            }
        )
    return rows


def _qualified_node(tree: ast.Module, locator: str) -> ast.AST:
    parts = locator.split(".")
    definitions = _top_level_definitions(tree)
    if parts[0] not in definitions:
        raise AssertionError(f"qualified source owner disappeared: {locator}")
    node: ast.AST = definitions[parts[0]]
    for part in parts[1:]:
        if not isinstance(node, ast.ClassDef):
            raise AssertionError(f"non-class source owner in locator: {locator}")
        matches = [
            child
            for child in node.body
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef))
            and child.name == part
        ]
        if len(matches) != 1:
            raise AssertionError(f"qualified source method disappeared: {locator}")
        node = matches[0]
    return node


def _qualified_source_rows(
    source: str,
    tree: ast.Module,
    locators: Iterable[str],
) -> list[dict[str, object]]:
    rows = []
    for locator in sorted(locators):
        exact = _node_source(source, _qualified_node(tree, locator))
        rows.append(
            {
                "locator": locator,
                "source": exact,
                "source_sha256": sha256(exact.encode("utf-8")).hexdigest(),
            }
        )
    return rows


def _identifier_set(nodes: Iterable[ast.AST]) -> frozenset[str]:
    identifiers: set[str] = set()
    for node in nodes:
        for child in ast.walk(node):
            if isinstance(child, ast.Name):
                identifiers.add(child.id)
            elif isinstance(child, ast.Attribute):
                identifiers.add(child.attr)
    return frozenset(identifiers)


def _annotated_class_field_schemas(
    tree: ast.Module,
    class_names: Iterable[str],
) -> dict[str, tuple[str, ...]]:
    definitions = _top_level_definitions(tree)
    result: dict[str, tuple[str, ...]] = {}
    for class_name in sorted(class_names):
        node = definitions.get(class_name)
        if not isinstance(node, ast.ClassDef):
            raise AssertionError(
                f"base structural dataclass disappeared: {class_name}"
            )
        fields = tuple(
            child.target.id
            for child in node.body
            if isinstance(child, ast.AnnAssign)
            and isinstance(child.target, ast.Name)
        )
        if not fields:
            raise AssertionError(
                f"base structural dataclass has no fields: {class_name}"
            )
        result[class_name] = fields
    return result


def _import_source_rows(
    source: str,
    tree: ast.Module,
) -> list[dict[str, object]]:
    top_level_ids = {
        id(node)
        for node in tree.body
        if isinstance(node, (ast.Import, ast.ImportFrom))
    }
    imports = sorted(
        (
            node
            for node in ast.walk(tree)
            if isinstance(node, (ast.Import, ast.ImportFrom))
        ),
        key=lambda node: (node.lineno, node.col_offset),
    )
    rows = []
    for node in imports:
        module = node.module if isinstance(node, ast.ImportFrom) else None
        bindings = []
        for alias in node.names:
            source_name = alias.name
            bound_name = alias.asname or alias.name.split(".")[0]
            bindings.append(
                {"source_name": source_name, "bound_name": bound_name}
            )
        rows.append(
            {
                "scope": "top-level" if id(node) in top_level_ids else "nested",
                "kind": type(node).__name__,
                "module": module,
                "level": node.level if isinstance(node, ast.ImportFrom) else 0,
                "bindings": bindings,
                "source": _node_source(source, node),
            }
        )
    return rows


def _top_level_import_binding_map(
    tree: ast.Module,
) -> dict[str, dict[str, str]]:
    result: dict[str, dict[str, str]] = {}
    for node in tree.body:
        if isinstance(node, ast.ImportFrom) and node.level == 0:
            module = node.module or ""
            for alias in node.names:
                result.setdefault(module, {})[alias.name] = (
                    alias.asname or alias.name
                )
        elif isinstance(node, ast.Import):
            for alias in node.names:
                result.setdefault(alias.name, {})[alias.name] = (
                    alias.asname or alias.name.split(".")[0]
                )
    return result


def _top_level_bound_names_excluding_imports(
    tree: ast.Module,
) -> frozenset[str]:
    names: set[str] = set()
    for node in tree.body:
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            names.add(node.name)
        elif isinstance(node, (ast.Assign, ast.AnnAssign, ast.AugAssign)):
            targets = node.targets if isinstance(node, ast.Assign) else (node.target,)
            for target in targets:
                for child in ast.walk(target):
                    if isinstance(child, ast.Name):
                        names.add(child.id)
    return frozenset(names)


def _named_top_level_assignment_source(
    source: str,
    tree: ast.Module,
    name: str,
    expected_value_name: str,
) -> dict[str, str]:
    matches = []
    for node in tree.body:
        if not isinstance(node, (ast.Assign, ast.AnnAssign)):
            continue
        targets = node.targets if isinstance(node, ast.Assign) else (node.target,)
        if any(
            isinstance(target, ast.Name) and target.id == name
            for target in targets
        ):
            matches.append(node)
    if len(matches) != 1:
        raise AssertionError(f"top-level assignment drift: {name}")
    node = matches[0]
    value = node.value
    if not isinstance(value, ast.Name) or value.id != expected_value_name:
        raise AssertionError(f"top-level assignment source drift: {name}")
    exact = _node_source(source, node)
    return {
        "name": name,
        "value_name": expected_value_name,
        "source": exact,
        "source_sha256": sha256(exact.encode("utf-8")).hexdigest(),
    }


def _assert_required_import_bindings(
    filename: str,
    tree: ast.Module,
) -> dict[str, dict[str, str]]:
    actual = _top_level_import_binding_map(tree)
    required = G_LOCAL_V1_REQUIRED_IMPORT_BINDINGS[filename]
    for module, bindings in required.items():
        if actual.get(module, {}) != bindings:
            raise AssertionError(
                f"required import binding drift in {filename}: {module}"
            )
    imported_bound_names = {
        bound_name
        for bindings in actual.values()
        for bound_name in bindings.values()
    }
    rebound = imported_bound_names & _top_level_bound_names_excluding_imports(tree)
    if rebound:
        raise AssertionError(
            f"top-level imported name rebound in {filename}: {sorted(rebound)}"
        )
    return required


def _runtime_binding_rows() -> list[dict[str, str]]:
    bindings = (
        (
            "g_local_v1.UniformComparison",
            structural.UniformComparison,
            base_structural.UniformComparison,
            "necessity_map",
            "UniformComparison",
        ),
        (
            "g_local_v1.nonempty_subsets",
            structural.nonempty_subsets,
            base_structural.nonempty_subsets,
            "necessity_map",
            "nonempty_subsets",
        ),
        (
            "necessity_map.Q",
            base_structural.Q,
            StdFraction,
            "fractions",
            "Fraction",
        ),
        *tuple(
            (
                f"g_local_v1.{name}",
                getattr(structural, name),
                getattr(r2_structural, name),
                "r2_hunt",
                name,
            )
            for name in G_LOCAL_V1_REQUIRED_IMPORT_BINDINGS[
                "g_local_v1.py"
            ]["r2_hunt"]
        ),
        *tuple(
            (
                f"r2_hunt.{name}",
                getattr(r2_structural, name),
                getattr(base_structural, name),
                "necessity_map",
                name,
            )
            for name in (
                "Matrix",
                "Nerve",
                "NerveMorphism",
                "UniformComparison",
                "derived_cell_supports",
                "nonempty_subsets",
            )
        ),
    )
    rows = []
    for binding, actual, expected, module_name, object_name in bindings:
        if actual is not expected:
            raise AssertionError(
                f"runtime structural binding identity drift: {binding}"
            )
        if not (
            getattr(actual, "__module__", None) == module_name
            and getattr(actual, "__name__", None) == object_name
        ):
            raise AssertionError(
                f"runtime structural binding source drift: {binding}"
            )
        rows.append(
            {
                "binding": binding,
                "module": module_name,
                "name": object_name,
            }
        )
    return rows


def _runtime_qualified_source_rows(
    module: object,
    module_name: str,
    filename: str,
    source: str,
    tree: ast.Module,
    locators: Iterable[str],
) -> list[dict[str, object]]:
    expected_path = (Path(__file__).resolve().parent / filename).resolve()
    rows = []
    for locator in sorted(locators):
        node = _qualified_node(tree, locator)
        parts = locator.split(".")
        owner = getattr(module, parts[0], None)
        descriptor = vars(owner).get(parts[-1]) if owner is not None else None
        if isinstance(descriptor, property):
            descriptor_kind = "property"
            actual = descriptor.fget
        elif isinstance(descriptor, staticmethod):
            descriptor_kind = "staticmethod"
            actual = descriptor.__func__
        elif isinstance(descriptor, classmethod):
            descriptor_kind = "classmethod"
            actual = descriptor.__func__
        else:
            descriptor_kind = "instance-method"
            actual = descriptor
        code = getattr(actual, "__code__", None)
        decorators = getattr(node, "decorator_list", ())
        decorator_names = tuple(
            decorator.id
            for decorator in decorators
            if isinstance(decorator, ast.Name)
        )
        expected_descriptor_kind = (
            "property"
            if "property" in decorator_names
            else "staticmethod"
            if "staticmethod" in decorator_names
            else "classmethod"
            if "classmethod" in decorator_names
            else "instance-method"
        )
        expected_first_line = min(
            [node.lineno] + [decorator.lineno for decorator in decorators]
        )
        if descriptor_kind != expected_descriptor_kind or code is None or not (
            getattr(actual, "__module__", None) == module_name
            and getattr(actual, "__name__", None) == parts[-1]
            and Path(code.co_filename).resolve() == expected_path
            and code.co_firstlineno == expected_first_line
        ):
            raise AssertionError(
                f"runtime qualified structural source drift: {locator}"
            )
        exact = _node_source(source, node)
        rows.append(
            {
                "binding": f"{module_name}.{locator}",
                "module": module_name,
                "name": parts[-1],
                "descriptor_kind": descriptor_kind,
                "source_path": filename,
                "source_first_line": expected_first_line,
                "source_sha256": sha256(exact.encode("utf-8")).hexdigest(),
            }
        )
    return rows


def _runtime_function_source_rows(
    module: object,
    module_name: str,
    filename: str,
    source: str,
    tree: ast.Module,
    function_names: Iterable[str],
    *,
    include_source_first_line: bool = True,
) -> list[dict[str, object]]:
    functions = _function_definitions(tree)
    expected_path = (Path(__file__).resolve().parent / filename).resolve()
    rows = []
    for name in sorted(function_names):
        node = functions.get(name)
        actual = getattr(module, name, None)
        code = getattr(actual, "__code__", None)
        if node is None or code is None:
            raise AssertionError(f"runtime structural function disappeared: {name}")
        if not (
            getattr(actual, "__module__", None) == module_name
            and getattr(actual, "__name__", None) == name
            and Path(code.co_filename).resolve() == expected_path
            and code.co_firstlineno == node.lineno
        ):
            raise AssertionError(f"runtime structural function source drift: {name}")
        exact = _node_source(source, node)
        row: dict[str, object] = {
            "binding": f"{module_name}.{name}",
            "module": module_name,
            "name": name,
            "source_path": filename,
            "source_sha256": sha256(exact.encode("utf-8")).hexdigest(),
        }
        if include_source_first_line:
            row["source_first_line"] = node.lineno
        rows.append(row)
    return rows


def _referenced_r2_data_classes(
    g_tree: ast.Module,
    g_closure: tuple[str, ...],
    r2_tree: ast.Module,
    r2_closure: tuple[str, ...],
) -> tuple[str, ...]:
    g_functions = _function_definitions(g_tree)
    r2_functions = _function_definitions(r2_tree)
    referenced = _identifier_set(
        [g_functions[name] for name in g_closure]
        + [r2_functions[name] for name in r2_closure]
    )
    r2_definitions = _top_level_definitions(r2_tree)
    return tuple(
        sorted(
            name
            for name in referenced
            if name in r2_definitions
            and isinstance(r2_definitions[name], ast.ClassDef)
        )
    )


def _source_bundle() -> dict[str, object]:
    g_source = _source_text(G_LOCAL_V1_SOURCE_FILES["observation"])
    stop_source = _source_text(G_LOCAL_V1_SOURCE_FILES["checker"])
    r2_source = _source_text(G_LOCAL_V1_SOURCE_FILES["r2_structural"])
    base_source = _source_text(G_LOCAL_V1_SOURCE_FILES["base_structural"])
    g_tree = ast.parse(g_source)
    stop_tree = ast.parse(stop_source)
    r2_tree = ast.parse(r2_source)
    base_tree = ast.parse(base_source)

    required_imports = {
        G_LOCAL_V1_SOURCE_FILES["observation"]: _assert_required_import_bindings(
            G_LOCAL_V1_SOURCE_FILES["observation"],
            g_tree,
        ),
        G_LOCAL_V1_SOURCE_FILES["checker"]: _assert_required_import_bindings(
            G_LOCAL_V1_SOURCE_FILES["checker"],
            stop_tree,
        ),
        G_LOCAL_V1_SOURCE_FILES["r2_structural"]: (
            _assert_required_import_bindings(
                G_LOCAL_V1_SOURCE_FILES["r2_structural"],
                r2_tree,
            )
        ),
        G_LOCAL_V1_SOURCE_FILES["base_structural"]: (
            _assert_required_import_bindings(
                G_LOCAL_V1_SOURCE_FILES["base_structural"],
                base_tree,
            )
        ),
    }
    runtime_binding_rows = _runtime_binding_rows()
    q_assignment = _named_top_level_assignment_source(
        base_source,
        base_tree,
        "Q",
        "Fraction",
    )

    g_closure = _function_closure(
        g_tree,
        structural.G_LOCAL_V1_LOCAL_SOURCE_ENTRYPOINTS,
    )
    stop_closure = _function_closure(
        stop_tree,
        G_LOCAL_V1_CHECKER_SOURCE_ENTRYPOINTS,
    )
    r2_closure = _function_closure(
        r2_tree,
        structural.G_LOCAL_V1_R2_STRUCTURAL_ENTRYPOINTS,
    )
    r2_admission_closure = _function_closure(
        r2_tree,
        G_LOCAL_V1_R2_WITNESS_ADMISSION_ENTRYPOINTS,
    )
    r2_classes = _referenced_r2_data_classes(
        g_tree,
        g_closure,
        r2_tree,
        r2_closure,
    )
    base_locators = structural.G_LOCAL_V1_NECESSITY_MAP_SOURCE_LOCATORS
    base_field_schemas = _annotated_class_field_schemas(
        base_tree,
        structural.G_LOCAL_V1_BASE_STRUCTURAL_TYPE_FIELDS,
    )
    if base_field_schemas != structural.G_LOCAL_V1_BASE_STRUCTURAL_TYPE_FIELDS:
        raise AssertionError("base structural dataclass field schema drift")
    g_runtime_function_rows = _runtime_function_source_rows(
        structural,
        "g_local_v1",
        G_LOCAL_V1_SOURCE_FILES["observation"],
        g_source,
        g_tree,
        g_closure,
    )
    r2_runtime_function_rows = _runtime_function_source_rows(
        r2_structural,
        "r2_hunt",
        G_LOCAL_V1_SOURCE_FILES["r2_structural"],
        r2_source,
        r2_tree,
        set(r2_closure) | set(r2_admission_closure),
    )
    base_runtime_function_rows = _runtime_function_source_rows(
        base_structural,
        "necessity_map",
        G_LOCAL_V1_SOURCE_FILES["base_structural"],
        base_source,
        base_tree,
        (
            locator
            for locator in base_locators
            if "." not in locator
        ),
    )
    base_runtime_qualified_rows = _runtime_qualified_source_rows(
        base_structural,
        "necessity_map",
        G_LOCAL_V1_SOURCE_FILES["base_structural"],
        base_source,
        base_tree,
        (
            locator
            for locator in base_locators
            if "." in locator
        ),
    )
    stop_runtime_function_rows = _runtime_function_source_rows(
        sys.modules[__name__],
        "g_local_v1_stop_b",
        G_LOCAL_V1_SOURCE_FILES["checker"],
        stop_source,
        stop_tree,
        stop_closure,
        include_source_first_line=False,
    )

    g_functions = _function_definitions(g_tree)
    r2_functions = _function_definitions(r2_tree)
    stop_functions = _function_definitions(stop_tree)
    g_identifiers = _identifier_set(g_functions[name] for name in g_closure)
    r2_identifiers = _identifier_set(r2_functions[name] for name in r2_closure)
    r2_admission_identifiers = _identifier_set(
        r2_functions[name] for name in r2_admission_closure
    )
    stop_identifiers = _identifier_set(
        stop_functions[name] for name in stop_closure
    )
    forbidden = set(G_LOCAL_V1_FORBIDDEN_REACHABLE_SYMBOLS)
    if g_identifiers & forbidden:
        raise AssertionError("Obs_G local closure reached a forbidden symbol")
    if stop_identifiers & {
        "analyze_h1",
        "block_analyses",
        "is_uniform",
        "v5_candidate_evaluation",
    }:
        raise AssertionError("Stop-B checker reached a forbidden oracle")

    c3_closure = _function_closure(
        r2_tree,
        (structural.G_LOCAL_V1_LOCAL_C3_EXCEPTION["entrypoint"],),
    )
    c3_identifiers = _identifier_set(
        r2_functions[name] for name in c3_closure
    )
    non_c3_identifiers = _identifier_set(
        r2_functions[name]
        for name in r2_closure
        if name not in c3_closure
    )
    direct_structural_symbols = set(
        structural.G_LOCAL_V1_LOCAL_C3_EXCEPTION[
            "required_direct_r2_structural_symbols"
        ]
    )
    direct_linear_symbols = set(
        structural.G_LOCAL_V1_LOCAL_C3_EXCEPTION[
            "permitted_direct_r2_linear_algebra_symbols"
        ]
    )
    transitive_base_locators = set(
        structural.G_LOCAL_V1_LOCAL_C3_EXCEPTION[
            "required_transitive_base_locators"
        ]
    )
    if not (
        direct_structural_symbols | direct_linear_symbols
    ) <= c3_identifiers:
        raise AssertionError("registered local C3 exception source drift")
    if not transitive_base_locators <= set(base_locators):
        raise AssertionError("registered local C3 base closure drift")
    if non_c3_identifiers & direct_linear_symbols:
        raise AssertionError("local C3 linear algebra escaped its closure")
    if r2_identifiers & (forbidden - direct_linear_symbols):
        raise AssertionError("r2 structural closure reached forbidden oracle")
    if r2_admission_identifiers & (
        forbidden
        | {
            "candidate_evaluation",
            "v5_candidate_evaluation",
            "v5_terminal_states",
        }
    ):
        raise AssertionError("r2 witness admission reached a forbidden oracle")

    return {
        "observation_module": {
            "path": G_LOCAL_V1_SOURCE_FILES["observation"],
            **_normalized_full_source_record(
                g_source,
                include_source=True,
            ),
            "all_import_rows": _import_source_rows(g_source, g_tree),
            "required_import_bindings": required_imports[
                G_LOCAL_V1_SOURCE_FILES["observation"]
            ],
            "top_level_import_rebindings": [],
            "entrypoints": list(structural.G_LOCAL_V1_LOCAL_SOURCE_ENTRYPOINTS),
            "reachable_function_names": list(g_closure),
            "reachable_function_source": _source_rows(
                g_source,
                g_tree,
                g_closure,
            ),
            "runtime_function_source_bindings": g_runtime_function_rows,
            "forbidden_identifier_hits": [],
        },
        "r2_structural_helpers": {
            "path": G_LOCAL_V1_SOURCE_FILES["r2_structural"],
            **_normalized_full_source_record(
                r2_source,
                include_source=False,
            ),
            "all_import_rows": _import_source_rows(r2_source, r2_tree),
            "required_import_bindings": required_imports[
                G_LOCAL_V1_SOURCE_FILES["r2_structural"]
            ],
            "top_level_import_rebindings": [],
            "entrypoints": list(structural.G_LOCAL_V1_R2_STRUCTURAL_ENTRYPOINTS),
            "reachable_function_names": list(r2_closure),
            "reachable_function_source": _source_rows(
                r2_source,
                r2_tree,
                r2_closure,
            ),
            "runtime_function_source_bindings": r2_runtime_function_rows,
            "witness_admission": {
                "entrypoints": list(
                    G_LOCAL_V1_R2_WITNESS_ADMISSION_ENTRYPOINTS
                ),
                "reachable_function_names": list(r2_admission_closure),
                "reachable_function_source": _source_rows(
                    r2_source,
                    r2_tree,
                    r2_admission_closure,
                ),
                "forbidden_identifier_hits": [],
            },
            "referenced_data_class_names": list(r2_classes),
            "referenced_data_class_source": _source_rows(
                r2_source,
                r2_tree,
                r2_classes,
            ),
            "local_C3_exception": {
                **structural.G_LOCAL_V1_LOCAL_C3_EXCEPTION,
                "reachable_function_names": list(c3_closure),
            },
            "forbidden_identifier_hits_outside_C3": [],
        },
        "base_structural_helpers": {
            "path": G_LOCAL_V1_SOURCE_FILES["base_structural"],
            **_normalized_full_source_record(
                base_source,
                include_source=False,
            ),
            "all_import_rows": _import_source_rows(base_source, base_tree),
            "required_import_bindings": required_imports[
                G_LOCAL_V1_SOURCE_FILES["base_structural"]
            ],
            "top_level_import_rebindings": [],
            "module_constants": {
                "Q": {
                    "runtime_module": "fractions",
                    "runtime_name": "Fraction",
                    "assignment": q_assignment,
                }
            },
            "registered_dataclass_field_schemas": (
                structural.G_LOCAL_V1_BASE_STRUCTURAL_TYPE_FIELDS
            ),
            "extracted_dataclass_field_schemas": base_field_schemas,
            "exact_locators": list(base_locators),
            "exact_source": _qualified_source_rows(
                base_source,
                base_tree,
                base_locators,
            ),
            "runtime_top_level_function_source_bindings": (
                base_runtime_function_rows
            ),
            "runtime_qualified_method_source_bindings": (
                base_runtime_qualified_rows
            ),
            "purpose": (
                "support-active restriction and structural validation; no "
                "global or A-block H1 analysis"
            ),
        },
        "checker_module": {
            "path": G_LOCAL_V1_SOURCE_FILES["checker"],
            **_registration_normalized_checker_source_record(
                stop_source,
                stop_tree,
            ),
            "all_import_rows": _import_source_rows(stop_source, stop_tree),
            "required_import_bindings": required_imports[
                G_LOCAL_V1_SOURCE_FILES["checker"]
            ],
            "top_level_import_rebindings": [],
            "entrypoints": list(G_LOCAL_V1_CHECKER_SOURCE_ENTRYPOINTS),
            "reachable_function_names": list(stop_closure),
            "reachable_function_source": _source_rows(
                stop_source,
                stop_tree,
                stop_closure,
            ),
            "runtime_function_source_bindings": (
                stop_runtime_function_rows
            ),
            "forbidden_oracle_identifier_hits": [],
        },
        "standard_library_dependencies": list(
            G_LOCAL_V1_STANDARD_LIBRARY_DEPENDENCIES
        ),
        "runtime_structural_bindings": runtime_binding_rows,
    }


def g_local_v1_permanent_contract_manifest() -> dict[str, object]:
    """Return the pure, self-contained permanent structural contract."""

    input_rows = []
    for name in ("TERNARY-CYCLE-3", "TERNARY-CYCLE-6"):
        payload = deepcopy(G_LOCAL_V1_WITNESS_INPUTS[name])
        expected_digest = G_LOCAL_V1_WITNESS_INPUT_SHA256[name]
        actual_digest = sha256(
            _compact_json(payload).encode("utf-8")
        ).hexdigest()
        if actual_digest != expected_digest:
            raise AssertionError("hand witness input digest drift")
        input_rows.append(
            {
                "ledger_key": name,
                "name_free_structural_payload": payload,
                "name_free_structural_sha256": expected_digest,
                "fixture_source": "r2_hunt.py::round15_verification_fixtures()",
                "registered_projection_source": (
                    "round15_preregistration_manifest.fixtures[name=\""
                    f"{name}\"].name_free_semantic_sha256"
                ),
                "registered_projection_value": expected_digest,
            }
        )
    return {
        "kind": "G-local-v1-permanent-structural-contract-v1",
        "contract_serialization": G_LOCAL_V1_PERMANENT_CONTRACT_SERIALIZATION,
        "semantic": {
            "semantic_id": structural.G_LOCAL_V1_SEMANTIC_ID,
            "grammar_spec": structural.G_LOCAL_V1_SPEC,
            "packet_kind_registry": list(
                structural.G_LOCAL_V1_PACKET_KIND_REGISTRY
            ),
            "all_path_trace_union_overlap_control": (
                structural.G_LOCAL_V1_TRACE_UNION_OVERLAP_CONTROL
            ),
            "flag_registry": list(structural.G_LOCAL_V1_FLAG_REGISTRY),
            "side_registry": list(structural.G_LOCAL_V1_SIDE_REGISTRY),
            "cell_type_registry": list(
                structural.G_LOCAL_V1_CELL_TYPE_REGISTRY
            ),
            "partial_map_status_registry": list(
                structural.G_LOCAL_V1_MAP_STATUS_REGISTRY
            ),
            "coarse_map_status": "mapped",
            "fine_chart_vertex_map_status": "mapped",
            "fine_edge_face_map_status": "actual-None-or-mapped",
            "third_map_status_permitted": False,
            "relation_registry": [
                {"kind": kind, "slot": slot, "sign": sign}
                for kind, slot, sign in structural.G_LOCAL_V1_RELATION_REGISTRY
            ],
            "count_buckets": list(structural.G_LOCAL_V1_COUNT_BUCKETS),
            "serialization": structural.G_LOCAL_V1_SERIALIZATION,
            "chart_at_contract": {
                "one_chart_role_per_retained_nerve_vertex": True,
                "one_chart_at_edge_only_to_same_vertex": True,
                "chart_to_incident_edge_or_face": False,
            },
            "actual_face_member_is_separate_root": True,
            "FaceTwin_flag_only_if_class_member_count_at_least_two": True,
        },
        "source_bundle": _source_bundle(),
        "immutable_round15_label_ledger": {
            "value": ROUND15_LABEL_LEDGER,
            "canonical_json": round15_label_ledger_canonical_json(),
            "sha256": round15_label_ledger_sha256(),
        },
        "round15_immutable_ledger_provenance": {
            "issue_comment": ROUND15_PREREGISTRATION_COMMENT,
            "created_at": ROUND15_PREREGISTRATION_CREATED_AT,
            "updated_at": ROUND15_PREREGISTRATION_UPDATED_AT,
            "sha256": ROUND15_REGISTERED_MANIFEST_SHA256,
            "fixture_projection_paths": [
                row["registered_projection_source"] for row in input_rows
            ],
        },
        "witness_inputs": input_rows,
        "hand_expectation": {
            "schema": G_LOCAL_V1_HAND_EXPECTATION,
            "expected_common_observation": G_LOCAL_V1_EXPECTED_COMMON_OBS,
            "controls": G_LOCAL_V1_HAND_CONTROL_EXPECTATIONS,
            "engine_observation_called_to_build_expectation": False,
        },
        "historical_execution_bridge": {
            "record": G_LOCAL_V1_HISTORICAL_EXECUTION,
            "role": (
                "opaque history bridge; no current-source reconstruction "
                "claim"
            ),
            "current_checker_must_match_historical_common_observation": True,
        },
        "dependency_contract": {
            "direction": (
                "structural-input->Obs_G-serialization->equality-checker<-"
                "immutable-label-ledger"
            ),
            "contract_calls_observation": False,
            "contract_calls_witness_constructors": False,
            "contract_calls_v5_candidate_or_terminal": False,
            "contract_calls_H1_rank_or_uniformity": False,
            "contract_calls_round13_14_15_report_or_population": False,
            "checker_accepts_caller_labels": False,
            "registered_local_C3_exception_only": True,
            "later_checker_Obs_G_structural_evaluations": 2,
            "later_checker_new_v5_candidate_evaluation_calls": 0,
            "later_checker_new_global_or_A_block_H1_queries": 0,
            "later_checker_new_population_queries": 0,
        },
        "expected_later_verdict_if_reproduced": (
            "CSTAR-not-expressible-in-G_local-v1"
        ),
        "coverage_limit": (
            "This is a two-point separation result relative only to the "
            "registered finite observation grammar G_local-v1, not an "
            "absolute impossibility result for other grammars."
        ),
        "current_registration_values_in_contract": False,
        "current_registration_fields": list(
            G_LOCAL_V1_PERMANENT_CONTRACT_REGISTRATION_FIELDS
        ),
        "checker_executed": False,
        "observation_executed": False,
        "contract_contains_its_own_sha256": False,
    }


def g_local_v1_permanent_contract_manifest_canonical_json() -> str:
    return _compact_json(g_local_v1_permanent_contract_manifest())


def g_local_v1_permanent_contract_manifest_sha256() -> str:
    return sha256(
        g_local_v1_permanent_contract_manifest_canonical_json().encode("utf-8")
    ).hexdigest()


def _admit_current_permanent_contract() -> dict[str, object]:
    if (
        G_LOCAL_V1_PERMANENT_CONTRACT_SHA256 is None
        or G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_ISSUE_COMMENT is None
        or G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_CREATED_AT is None
        or G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_UPDATED_AT is None
    ):
        raise AssertionError("G_local-v1 permanent contract is not registered")
    contract = g_local_v1_permanent_contract_manifest()
    actual_sha = sha256(_compact_json(contract).encode("utf-8")).hexdigest()
    if actual_sha != G_LOCAL_V1_PERMANENT_CONTRACT_SHA256:
        raise AssertionError("G_local-v1 permanent contract drift")
    if contract["current_registration_values_in_contract"] is not False:
        raise AssertionError("pure contract acquired self-registration state")
    return contract


def _admit_round15_ledger(
    contract: dict[str, object],
) -> dict[str, bool]:
    registered = contract["immutable_round15_label_ledger"]
    canonical = round15_label_ledger_canonical_json()
    digest = sha256(canonical.encode("utf-8")).hexdigest()
    if not (
        registered["value"] == ROUND15_LABEL_LEDGER
        and registered["canonical_json"] == canonical
        and registered["sha256"] == digest
        and ROUND15_LABEL_LEDGER["preregistration_issue_comment"]
        == ROUND15_PREREGISTRATION_COMMENT
        and ROUND15_LABEL_LEDGER["result_provenance"]
        == {
            "issue_comment": ROUND15_RESULT_COMMENT,
            "created_at": ROUND15_RESULT_CREATED_AT,
            "updated_at": ROUND15_RESULT_UPDATED_AT,
            "canonical_payload_sha256": ROUND15_RESULT_PAYLOAD_SHA256,
            "canonical_bytes": ROUND15_RESULT_CANONICAL_BYTES,
            "serialization": ROUND15_RESULT_SERIALIZATION,
        }
        and ROUND15_LABEL_LEDGER["caller_supplied_labels_permitted"] is False
    ):
        raise AssertionError("Round15 immutable label ledger admission failed")
    labels = tuple(ROUND15_LABEL_LEDGER["labels"])
    expected_rows = {
        "TERNARY-CYCLE-3": {
            "field_path": (
                "exact_verification.fixtures[name=\"TERNARY-CYCLE-3\"]"
                ".uniform"
            ),
            "uniform": True,
            "digest": TERNARY_CYCLE_3_INPUT_SHA256,
            "projection_path": (
                "round15_preregistration_manifest.fixtures[name=\""
                "TERNARY-CYCLE-3\"].name_free_semantic_sha256"
            ),
        },
        "TERNARY-CYCLE-6": {
            "field_path": (
                "exact_verification.fixtures[name=\"TERNARY-CYCLE-6\"]"
                ".uniform"
            ),
            "uniform": False,
            "digest": TERNARY_CYCLE_6_INPUT_SHA256,
            "projection_path": (
                "round15_preregistration_manifest.fixtures[name=\""
                "TERNARY-CYCLE-6\"].name_free_semantic_sha256"
            ),
        },
    }
    if {row["fixture"] for row in labels} != set(expected_rows):
        raise AssertionError("Round15 ledger fixture domain drift")
    for row in labels:
        expected = expected_rows[row["fixture"]]
        if not (
            row["field_path"] == expected["field_path"]
            and row["uniform"] is expected["uniform"]
            and row["name_free_structural_sha256"] == expected["digest"]
            and row["registered_projection_source"]
            == expected["projection_path"]
            and row["registered_projection_value"] == expected["digest"]
        ):
            raise AssertionError("Round15 ledger field admission failed")
    return {row["fixture"]: row["uniform"] for row in labels}


def _admit_witness_structures(
    contract: dict[str, object],
) -> dict[str, object]:
    """Lazy historical import after contract admission and before labels."""

    from r2_hunt import (
        _case_semantic_payload_json,
        ROUND15_PREREGISTERED_CREATED_AT,
        ROUND15_PREREGISTERED_ISSUE_COMMENT,
        ROUND15_PREREGISTERED_UPDATED_AT,
        ROUND15_REGISTERED_MANIFEST_SHA256 as source_manifest_sha256,
        round15_verification_fixtures,
    )

    if not (
        ROUND15_PREREGISTERED_ISSUE_COMMENT == ROUND15_PREREGISTRATION_COMMENT
        and ROUND15_PREREGISTERED_CREATED_AT == ROUND15_PREREGISTRATION_CREATED_AT
        and ROUND15_PREREGISTERED_UPDATED_AT == ROUND15_PREREGISTRATION_UPDATED_AT
        and source_manifest_sha256 == ROUND15_REGISTERED_MANIFEST_SHA256
        and contract["round15_immutable_ledger_provenance"]
        == {
            "issue_comment": ROUND15_PREREGISTRATION_COMMENT,
            "created_at": ROUND15_PREREGISTRATION_CREATED_AT,
            "updated_at": ROUND15_PREREGISTRATION_UPDATED_AT,
            "sha256": ROUND15_REGISTERED_MANIFEST_SHA256,
            "fixture_projection_paths": [
                (
                    "round15_preregistration_manifest.fixtures[name=\""
                    "TERNARY-CYCLE-3\"].name_free_semantic_sha256"
                ),
                (
                    "round15_preregistration_manifest.fixtures[name=\""
                    "TERNARY-CYCLE-6\"].name_free_semantic_sha256"
                ),
            ],
        }
    ):
        raise AssertionError("Round15 registered manifest provenance drift")

    fixtures = round15_verification_fixtures()
    expected_fixture_domain = (
        "NONFREE-MUTUAL-KILL-SPLIT",
        "WEIGHTED-2",
        "TERNARY-CYCLE-3",
        "TERNARY-CYCLE-6",
        "SINGULAR-PERFECT-MATCH-3",
        "WEIGHTED-ORPHAN-SELFLOOP",
    )
    if tuple(fixture.name for fixture in fixtures) != expected_fixture_domain:
        raise AssertionError("Round15 verification fixture domain/order drift")
    fixture_by_name = {fixture.name: fixture for fixture in fixtures}
    pure_rows = {
        row["ledger_key"]: row for row in contract["witness_inputs"]
    }
    expected_names = {"TERNARY-CYCLE-3", "TERNARY-CYCLE-6"}
    if not (
        expected_names <= fixture_by_name.keys()
        and pure_rows.keys() == expected_names
    ):
        raise AssertionError("Round15 witness admission domain drift")

    admitted: dict[str, object] = {}
    for name in sorted(expected_names):
        fixture = fixture_by_name[name]
        payload_json = _case_semantic_payload_json(fixture)
        payload = json.loads(payload_json)
        digest = sha256(payload_json.encode("utf-8")).hexdigest()
        expected_projection_path = (
            "round15_preregistration_manifest.fixtures[name=\""
            f"{name}\"].name_free_semantic_sha256"
        )
        if not (
            payload == G_LOCAL_V1_WITNESS_INPUTS[name]
            and payload == pure_rows[name]["name_free_structural_payload"]
            and digest == G_LOCAL_V1_WITNESS_INPUT_SHA256[name]
            and digest == pure_rows[name]["name_free_structural_sha256"]
            and digest == pure_rows[name]["registered_projection_value"]
            and pure_rows[name]["registered_projection_source"]
            == expected_projection_path
        ):
            raise AssertionError("Round15 witness structure admission failed")
        admitted[name] = fixture
    return admitted


def _assert_hand_observation_components(
    observation: dict[str, object],
) -> None:
    expected = G_LOCAL_V1_EXPECTED_COMMON_OBS
    if observation["aggregate_C0_through_C6"] != expected[
        "aggregate_C0_through_C6"
    ]:
        raise AssertionError("G_local-v1 aggregate hand calibration mismatch")
    if observation["whole"]["conditions"] != expected["whole"]["conditions"]:
        raise AssertionError("G_local-v1 whole condition mismatch")
    if observation["whole"]["packet_kind_union"] != []:
        raise AssertionError("G_local-v1 whole packet union mismatch")
    if observation["whole"]["rooted_ball_histogram"] != expected["whole"][
        "rooted_ball_histogram"
    ]:
        raise AssertionError("G_local-v1 whole side/type histogram mismatch")
    actual_a_rows = observation["A_record_histogram"]
    expected_a_rows = expected["A_record_histogram"]
    if len(actual_a_rows) != len(expected_a_rows):
        raise AssertionError("G_local-v1 A component count mismatch")
    for actual, hand in zip(actual_a_rows, expected_a_rows):
        if actual["count"] != hand["count"]:
            raise AssertionError("G_local-v1 A multiplicity mismatch")
        for component in (
            "conditions",
            "packet_kind_union",
            "rooted_ball_histogram",
        ):
            if actual["record"][component] != hand["record"][component]:
                raise AssertionError(
                    f"G_local-v1 A {component} hand calibration mismatch"
                )
    if observation != expected:
        raise AssertionError("G_local-v1 final hand observation mismatch")


def _observation_component_equality(
    left: dict[str, object],
    right: dict[str, object],
    left_serialized: str,
    right_serialized: str,
) -> dict[str, bool]:
    left_a = left["A_record_histogram"]
    right_a = right["A_record_histogram"]
    same_a_shape = len(left_a) == len(right_a)
    return {
        "aggregate_C0_through_C6": (
            left["aggregate_C0_through_C6"]
            == right["aggregate_C0_through_C6"]
        ),
        "whole_conditions": (
            left["whole"]["conditions"] == right["whole"]["conditions"]
        ),
        "whole_packet_kind_union": (
            left["whole"]["packet_kind_union"]
            == right["whole"]["packet_kind_union"]
        ),
        "whole_rooted_ball_histogram": (
            left["whole"]["rooted_ball_histogram"]
            == right["whole"]["rooted_ball_histogram"]
        ),
        "A_record_row_count": same_a_shape,
        "A_record_multiplicities": (
            same_a_shape
            and all(
                left_row["count"] == right_row["count"]
                for left_row, right_row in zip(left_a, right_a)
            )
        ),
        "A_record_conditions": (
            same_a_shape
            and all(
                left_row["record"]["conditions"]
                == right_row["record"]["conditions"]
                for left_row, right_row in zip(left_a, right_a)
            )
        ),
        "A_record_packet_kind_unions": (
            same_a_shape
            and all(
                left_row["record"]["packet_kind_union"]
                == right_row["record"]["packet_kind_union"]
                for left_row, right_row in zip(left_a, right_a)
            )
        ),
        "A_record_rooted_ball_histograms": (
            same_a_shape
            and all(
                left_row["record"]["rooted_ball_histogram"]
                == right_row["record"]["rooted_ball_histogram"]
                for left_row, right_row in zip(left_a, right_a)
            )
        ),
        "A_record_histogram": left_a == right_a,
        "final_canonical_bytes": left_serialized == right_serialized,
    }


def _admit_historical_observation_bridge(
    contract: dict[str, object],
    serializations: dict[str, str],
) -> dict[str, object]:
    bridge = contract["historical_execution_bridge"]
    historical = bridge["record"]
    expected_result = G_LOCAL_V1_HISTORICAL_EXECUTION["result"]
    witness_rows = {
        name: {
            "sha256": sha256(serialized.encode("utf-8")).hexdigest(),
            "canonical_bytes": len(serialized.encode("utf-8")),
        }
        for name, serialized in serializations.items()
    }
    expected_witness_names = {"TERNARY-CYCLE-3", "TERNARY-CYCLE-6"}
    if not (
        set(witness_rows) == expected_witness_names
        and historical == G_LOCAL_V1_HISTORICAL_EXECUTION
        and bridge["role"]
        == "opaque history bridge; no current-source reconstruction claim"
        and bridge[
            "current_checker_must_match_historical_common_observation"
        ]
        is True
        and all(
            row
            == {
                "sha256": expected_result["common_observation_sha256"],
                "canonical_bytes": expected_result[
                    "common_observation_canonical_bytes"
                ],
            }
            for row in witness_rows.values()
        )
    ):
        raise AssertionError("historical common observation bridge mismatch")
    return {
        "matched": True,
        "historical_sha256": expected_result["common_observation_sha256"],
        "historical_canonical_bytes": expected_result[
            "common_observation_canonical_bytes"
        ],
        "current_witness_rows": witness_rows,
    }


def check_g_local_v1_stop_b() -> dict[str, object]:
    """Run the permanent-contract two-point checker after every gate.

    No label, fixture, truth value, or structural input is accepted from the
    caller.  A mismatch is a calibration failure and never a valid Stop-B
    result.
    """

    contract = _admit_current_permanent_contract()
    witnesses = _admit_witness_structures(contract)

    observations = {
        name: structural.observe_g_local_v1(witnesses[name])
        for name in ("TERNARY-CYCLE-3", "TERNARY-CYCLE-6")
    }
    serializations = {
        name: _compact_json(observation)
        for name, observation in observations.items()
    }
    for observation in observations.values():
        _assert_hand_observation_components(observation)
    component_equality = _observation_component_equality(
        observations["TERNARY-CYCLE-3"],
        observations["TERNARY-CYCLE-6"],
        serializations["TERNARY-CYCLE-3"],
        serializations["TERNARY-CYCLE-6"],
    )
    if not (
        all(component_equality.values())
        and observations["TERNARY-CYCLE-3"]
        == observations["TERNARY-CYCLE-6"]
    ):
        raise AssertionError("G_local-v1 structural equality was not reproduced")

    historical_observation_bridge = _admit_historical_observation_bridge(
        contract,
        serializations,
    )

    # Uniformity truth is deliberately admitted only after exact structural
    # equality, hand calibration, final bytes equality, and the observation
    # migration bridge have all succeeded.
    labels = _admit_round15_ledger(contract)
    if len(set(labels.values())) != 2:
        raise AssertionError("Round15 admitted labels do not separate")

    return {
        "valid": True,
        "verdict": "CSTAR-not-expressible-in-G_local-v1",
        "semantic_id": structural.G_LOCAL_V1_SEMANTIC_ID,
        "historical_execution_provenance": G_LOCAL_V1_HISTORICAL_EXECUTION,
        "current_permanent_contract_provenance": {
            "sha256": G_LOCAL_V1_PERMANENT_CONTRACT_SHA256,
            "migration_issue_comment": (
                G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_ISSUE_COMMENT
            ),
            "migration_created_at": (
                G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_CREATED_AT
            ),
            "migration_updated_at": (
                G_LOCAL_V1_PERMANENT_CONTRACT_MIGRATION_UPDATED_AT
            ),
        },
        "round15_label_ledger_sha256": round15_label_ledger_sha256(),
        "witness_structural_sha256": G_LOCAL_V1_WITNESS_INPUT_SHA256,
        "observations_equal": all(component_equality.values()),
        "component_equality": component_equality,
        "observation_evidence": {
            "serialization": structural.G_LOCAL_V1_SERIALIZATION,
            "witness_sha256": {
                name: sha256(serialized.encode("utf-8")).hexdigest()
                for name, serialized in serializations.items()
            },
            "witness_canonical_bytes": {
                name: len(serialized.encode("utf-8"))
                for name, serialized in serializations.items()
            },
            "common_observation_sha256": sha256(
                serializations["TERNARY-CYCLE-3"].encode("utf-8")
            ).hexdigest(),
            "common_observation_canonical_bytes": len(
                serializations["TERNARY-CYCLE-3"].encode("utf-8")
            ),
            "common_observation": observations["TERNARY-CYCLE-3"],
            "historical_bridge": historical_observation_bridge,
        },
        "Obs_G_structural_evaluations": 2,
        "new_v5_candidate_evaluation_calls": 0,
        "new_global_or_A_block_H1_queries": 0,
        "new_population_queries": 0,
        "migration_invariants": {
            "observation_meaning_unchanged": True,
            "historical_labels_admitted_after_observation": True,
            "query_zero_contract_unchanged": True,
            "old_manifest_reconstruction_claimed": False,
            "old_checker_reconstruction_claimed": False,
        },
        "labels": labels,
        "labels_differ": True,
        "general_two_point_argument": (
            "Every admissible condition family factors through Obs_G. "
            "Equal Obs_G values force equal condition values, while the "
            "admitted immutable Round15 ledger gives different uniformity "
            "truth values for these two structural inputs."
        ),
        "coverage_limit": contract["coverage_limit"],
        "stop_B": True,
    }
