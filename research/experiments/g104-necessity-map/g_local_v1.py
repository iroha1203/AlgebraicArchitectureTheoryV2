#!/usr/bin/env python3
"""Structural-only ``G_local-v1`` observation grammar.

This module reads only the supported comparison structure and the
preregistered v5 structural reduction.  External evidence and verdict logic
live in a separate, one-way consumer module.
"""

from __future__ import annotations

from collections import Counter
from itertools import permutations
import json
from typing import Iterable

from necessity_map import UniformComparison, nonempty_subsets
from r2_hunt import (
    ReducedSide,
    ScopedComparison,
    V5CollapseState,
    _apply_v5_packet,
    _a_scope,
    _active_fine_vertices,
    _c0,
    _c1,
    _c2,
    _c3,
    _c4,
    _face_classes,
    _path_without_edge,
    _v4_c5_c6,
    _v5_packet_variants,
    _v5_terminal_reductions,
)


G_LOCAL_V1_SEMANTIC_ID = "G_local-v1"
G_LOCAL_V1_SPEC = "\n".join(
    (
        "scope:observe the full support-active scope once and every nonempty A-scope without sampling or order labels",
        "terminal:read every v5 irreducible terminal but only retained cells and retained FaceTwin classes, never removed cells or certificate arguments",
        "conditions:whole records contain C0,C5,C6; A-records contain C1-C4; the aggregate seven-vector is derived by conjunction",
        "packets:retain only the union of v4-coarse,v4-fine-only,coordinate-dependency,closed-doubled-cycle kinds across terminal traces",
        "chart-role:each retained incidence vertex v has exactly one chart-role c_v and exactly one chart-at edge c_v--v; charts have no direct edge or face incidence",
        "ball:serialize only root-preserving radius-one typed incidence stars on side-local retained chart,vertex,edge,face cells",
        "relations:retain chart-at, endpoint slots 0,1, and ordered face slots 0,1,2 with signs +,-,+",
        "map-status:fine chart and vertex are mapped, fine edge and face use actual None or mapped, and every coarse root is canonical mapped; no third value exists",
        "neighbor:preserve radius-one neighbor identity and the full multiset of root-neighbor slot/sign relations",
        "stubs:replace every outward half-edge by only its cell type and slot, discard identity and sharedness, and clip each typed histogram at two",
        "multiplicity:clip equal neighbor descriptors, rooted ball occurrences, and equal A-record occurrences to 0,1,at-least-2",
        "flags:the closed flags are critical,guard,port,bridge,self-loop,FaceTwin and are false outside their stated domains",
        "supports:labels carry only scoped support and its pi-image; support cardinality is not derived",
        "faces:each actual member of a retained FaceTwin class is a separate face root and only the FaceTwin flag records class multiplicity at least two",
        "targets:minimize the whole record plus clipped A-record histogram over every simultaneous target relabel preserving pi",
        "forbidden:no raw cell or A identifiers, fixture names, semantic hashes, exact counts above two, parity, global cycle length, full graph lookup, global or A-block H1, comparison rank, or unregistered atom",
    )
)

G_LOCAL_V1_PACKET_KIND_REGISTRY = (
    "v4-coarse",
    "v4-fine-only",
    "coordinate-dependency",
    "closed-doubled-cycle",
)
G_LOCAL_V1_TRACE_UNION_OVERLAP_CONTROL = {
    "kind": "all-path-packet-kind-union-overlap-control",
    "coarse": {
        "vertices": 1,
        "edges": ((0, 0),),
        "faces": ((0, 0, 0),),
        "chart_supports": ((0,),),
    },
    "fine": {
        "vertices": 1,
        "edges": ((0, 0),),
        "faces": ((0, 0, 0),),
        "chart_supports": ((0,),),
    },
    "morphism": {
        "vertex_map": (0,),
        "edge_map": (0,),
        "face_map": (0,),
    },
    "targets": {"coarse": 1, "fine": 1, "pi": (0,)},
    "same_terminal_cell_key": ((), (), (), ()),
    "distinct_path_packet_kinds": ("v4-coarse", "coordinate-dependency"),
    "expected_union": ("coordinate-dependency", "v4-coarse"),
    "lexicographic_single_trace_is_insufficient": True,
}
G_LOCAL_V1_FLAG_REGISTRY = (
    "critical",
    "guard",
    "port",
    "bridge",
    "self-loop",
    "FaceTwin",
)
G_LOCAL_V1_SIDE_REGISTRY = ("coarse", "fine")
G_LOCAL_V1_CELL_TYPE_REGISTRY = ("chart", "vertex", "edge", "face")
G_LOCAL_V1_MAP_STATUS_REGISTRY = ("None", "mapped")
G_LOCAL_V1_COUNT_BUCKETS = (0, 1, 2)
G_LOCAL_V1_RELATION_REGISTRY = (
    ("chart-at", "chart-at", None),
    ("endpoint", 0, None),
    ("endpoint", 1, None),
    ("boundary", 0, "+"),
    ("boundary", 1, "-"),
    ("boundary", 2, "+"),
)
G_LOCAL_V1_SERIALIZATION = {
    "encoding": "UTF-8",
    "ensure_ascii": True,
    "sort_keys": True,
    "separators": [",", ":"],
    "trailing_newline": False,
    "count_bucket_2_means": "at-least-2",
}
G_LOCAL_V1_LOCAL_SOURCE_ENTRYPOINTS = (
    "observe_g_local_v1",
    "serialize_g_local_v1_observation",
)
G_LOCAL_V1_R2_STRUCTURAL_ENTRYPOINTS = (
    "_a_scope",
    "_apply_v5_packet",
    "_active_fine_vertices",
    "_c0",
    "_c1",
    "_c2",
    "_c3",
    "_c4",
    "_face_classes",
    "_path_without_edge",
    "_v4_c5_c6",
    "_v5_packet_variants",
    "_v5_terminal_reductions",
)
G_LOCAL_V1_NECESSITY_MAP_SOURCE_LOCATORS = (
    "Matrix.__post_init__",
    "Matrix.__matmul__",
    "Matrix.from_mutable",
    "Matrix.is_zero",
    "Matrix.kernel_basis",
    "Matrix.rank",
    "Matrix.zero",
    "Nerve.__post_init__",
    "Nerve.d0",
    "Nerve.d1",
    "NerveMorphism.__post_init__",
    "UniformComparison.__post_init__",
    "UniformComparison.coarse_edge_supports",
    "UniformComparison.coarse_face_supports",
    "UniformComparison.coordinate_subcomparison",
    "UniformComparison.fine_edge_supports",
    "UniformComparison.fine_face_supports",
    "UniformComparison.summary",
    "derived_cell_supports",
    "nerve_summary",
    "nonempty_subsets",
    "restrict_nerve",
    "supports_summary",
)
G_LOCAL_V1_LOCAL_C3_EXCEPTION = {
    "entrypoint": "_c3",
    "helper": "_local_unmapped_h1_dimension",
    "required_direct_r2_structural_symbols": (
        "Nerve",
        "d0",
        "d1",
    ),
    "permitted_direct_r2_linear_algebra_symbols": (
        "kernel_basis",
        "rank",
    ),
    "required_transitive_base_locators": (
        "Matrix.__post_init__",
        "Matrix.__matmul__",
        "Matrix.from_mutable",
        "Matrix.is_zero",
        "Matrix.kernel_basis",
        "Matrix.rank",
        "Matrix.zero",
        "Nerve.__post_init__",
        "Nerve.d0",
        "Nerve.d1",
    ),
    "purpose": "registered local unmapped-fiber C3 acyclicity only",
}
G_LOCAL_V1_BASE_STRUCTURAL_TYPE_FIELDS = {
    "Matrix": ("rows", "cols", "entries"),
    "Nerve": ("vertices", "edges", "faces"),
    "NerveMorphism": (
        "coarse",
        "fine",
        "vertex_map",
        "edge_map",
        "face_map",
    ),
    "RestrictedNerve": ("nerve", "vertices", "edges", "faces"),
    "CoordinateSubcomparison": (
        "coarse_targets",
        "fine_targets",
        "coarse",
        "fine",
        "morphism",
    ),
    "UniformComparison": (
        "name",
        "morphism",
        "coarse_target_count",
        "fine_target_count",
        "factor_pi",
        "coarse_chart_supports",
        "fine_chart_supports",
    ),
}
CellKey = tuple[str, str, int]
RelationLabel = dict[str, object]


def _g_canonical_json(value: object) -> str:
    return json.dumps(
        value,
        ensure_ascii=True,
        sort_keys=True,
        separators=(",", ":"),
    )


def _g_clip2(count: int) -> int:
    if count < 0:
        raise ValueError("G_local-v1 cannot clip a negative count")
    return min(count, 2)


def _g_relation(kind: str, slot: str | int, sign: str | None) -> RelationLabel:
    registered = (kind, slot, sign)
    if registered not in G_LOCAL_V1_RELATION_REGISTRY:
        raise AssertionError("relation is outside the closed G_local-v1 registry")
    return {"kind": kind, "slot": slot, "sign": sign}


def _g_retained_faces(reduced: ReducedSide) -> tuple[tuple[int, int], ...]:
    return tuple(
        (face, class_index)
        for class_index in reduced.retained_face_classes
        for face in reduced.face_classes[class_index].members
    )


def _g_support(
    reduced: ReducedSide,
    cell_type: str,
    cell: int,
) -> frozenset[int]:
    if cell_type in ("chart", "vertex"):
        return reduced.data.chart_supports[cell]
    if cell_type == "edge":
        return reduced.data.edge_supports[cell]
    if cell_type == "face":
        return reduced.data.face_supports[cell]
    raise AssertionError("unknown G_local-v1 cell type")


def _g_map_status(
    scope: ScopedComparison,
    side: str,
    cell_type: str,
    cell: int,
) -> str:
    if side == "coarse" or cell_type in ("chart", "vertex"):
        return "mapped"
    if cell_type == "edge":
        mapped = scope.morphism.edge_map[cell]
    elif cell_type == "face":
        mapped = scope.morphism.face_map[cell]
    else:
        raise AssertionError("unknown fine partial-map domain")
    return "None" if mapped is None else "mapped"


def _g_flags(
    scope: ScopedComparison,
    side: str,
    reduced: ReducedSide,
    cell_type: str,
    cell: int,
    *,
    face_class: int | None,
    guarded_coarse_edges: frozenset[int],
    ports: frozenset[int],
) -> dict[str, bool]:
    flags = {flag: False for flag in G_LOCAL_V1_FLAG_REGISTRY}
    if cell_type == "vertex":
        flags["critical"] = cell in reduced.critical_vertices
        flags["port"] = side == "fine" and cell in ports
    elif cell_type == "edge":
        endpoints = reduced.data.nerve.edges[cell]
        self_loop = endpoints[0] == endpoints[1]
        flags["critical"] = cell in reduced.critical_edges
        flags["guard"] = side == "coarse" and cell in guarded_coarse_edges
        flags["self-loop"] = self_loop
        flags["bridge"] = (
            not self_loop
            and not _path_without_edge(
                reduced.data.nerve,
                set(reduced.retained_edges),
                cell,
            )
        )
    elif cell_type == "face":
        if face_class is None:
            raise AssertionError("retained face lost its FaceTwin class")
        flags["FaceTwin"] = (
            len(reduced.face_classes[face_class].members) >= 2
        )
    return flags


def _g_cell_label(
    comparison: UniformComparison,
    scope: ScopedComparison,
    side: str,
    reduced: ReducedSide,
    cell_type: str,
    cell: int,
    *,
    face_class: int | None,
    guarded_coarse_edges: frozenset[int],
    ports: frozenset[int],
) -> dict[str, object]:
    support = _g_support(reduced, cell_type, cell)
    pi_image = (
        support
        if side == "coarse"
        else frozenset(comparison.factor_pi[target] for target in support)
    )
    label = {
        "side": side,
        "cell_type": cell_type,
        "map_status": _g_map_status(scope, side, cell_type, cell),
        "support": sorted(support),
        "pi_image": sorted(pi_image),
        "flags": _g_flags(
            scope,
            side,
            reduced,
            cell_type,
            cell,
            face_class=face_class,
            guarded_coarse_edges=guarded_coarse_edges,
            ports=ports,
        ),
    }
    if label["map_status"] not in G_LOCAL_V1_MAP_STATUS_REGISTRY:
        raise AssertionError("map status escaped the binary registry")
    return label


def _g_terminal_incidence(
    comparison: UniformComparison,
    scope: ScopedComparison,
    coarse: ReducedSide,
    fine: ReducedSide,
    guarded_coarse_edges: frozenset[int],
) -> tuple[
    dict[CellKey, dict[str, object]],
    dict[CellKey, list[tuple[CellKey, RelationLabel]]],
]:
    active = _active_fine_vertices(scope, coarse, fine)
    ports = frozenset(
        vertex
        for vertex in active
        if scope.morphism.vertex_map[vertex] in coarse.critical_vertices
    )
    cells: dict[CellKey, dict[str, object]] = {}
    adjacency: dict[CellKey, list[tuple[CellKey, RelationLabel]]] = {}

    def add_cell(
        side: str,
        reduced: ReducedSide,
        cell_type: str,
        cell: int,
        face_class: int | None = None,
    ) -> CellKey:
        key = (side, cell_type, cell)
        if key in cells:
            raise AssertionError("duplicate retained G_local-v1 cell")
        cells[key] = _g_cell_label(
            comparison,
            scope,
            side,
            reduced,
            cell_type,
            cell,
            face_class=face_class,
            guarded_coarse_edges=guarded_coarse_edges,
            ports=ports,
        )
        adjacency[key] = []
        return key

    def add_relation(left: CellKey, right: CellKey, relation: RelationLabel) -> None:
        adjacency[left].append((right, relation))
        adjacency[right].append((left, relation))

    for side, reduced in (("coarse", coarse), ("fine", fine)):
        for vertex in range(reduced.data.nerve.vertices):
            chart = add_cell(side, reduced, "chart", vertex)
            incidence_vertex = add_cell(side, reduced, "vertex", vertex)
            add_relation(
                chart,
                incidence_vertex,
                _g_relation("chart-at", "chart-at", None),
            )
        for edge in reduced.retained_edges:
            edge_key = add_cell(side, reduced, "edge", edge)
            for slot, vertex in enumerate(reduced.data.nerve.edges[edge]):
                add_relation(
                    edge_key,
                    (side, "vertex", vertex),
                    _g_relation("endpoint", slot, None),
                )
        for face, face_class in _g_retained_faces(reduced):
            face_key = add_cell(
                side,
                reduced,
                "face",
                face,
                face_class,
            )
            for slot, edge in enumerate(reduced.data.nerve.faces[face]):
                sign = "+" if slot in (0, 2) else "-"
                add_relation(
                    face_key,
                    (side, "edge", edge),
                    _g_relation("boundary", slot, sign),
                )
    return cells, adjacency


def _g_clipped_rows(
    canonical_payloads: Iterable[str],
    payload_key: str,
) -> list[dict[str, object]]:
    counts = Counter(canonical_payloads)
    return [
        {
            payload_key: json.loads(payload),
            "count": _g_clip2(count),
        }
        for payload, count in sorted(counts.items())
    ]


def _g_rooted_ball(
    root: CellKey,
    cells: dict[CellKey, dict[str, object]],
    adjacency: dict[CellKey, list[tuple[CellKey, RelationLabel]]],
) -> dict[str, object]:
    root_neighbours: dict[CellKey, list[RelationLabel]] = {}
    for neighbour, relation in adjacency[root]:
        root_neighbours.setdefault(neighbour, []).append(relation)
    descriptor_payloads = []
    for neighbour, relations in root_neighbours.items():
        outward_stubs = []
        for outside, relation in adjacency[neighbour]:
            if outside == root:
                continue
            outward_stubs.append(
                _g_canonical_json(
                    {
                        "cell_type": cells[outside]["cell_type"],
                        "slot": relation["slot"],
                    }
                )
            )
        descriptor = {
            "neighbor_label": cells[neighbour],
            "relations": sorted(
                relations,
                key=_g_canonical_json,
            ),
            "outward_stub_histogram": _g_clipped_rows(
                outward_stubs,
                "stub",
            ),
        }
        descriptor_payloads.append(_g_canonical_json(descriptor))
    return {
        "root_label": cells[root],
        "neighbor_descriptors": _g_clipped_rows(
            descriptor_payloads,
            "descriptor",
        ),
    }


def _g_terminal_ball_payloads(
    comparison: UniformComparison,
    scope: ScopedComparison,
    coarse: ReducedSide,
    fine: ReducedSide,
    guarded_coarse_edges: frozenset[int],
) -> tuple[str, ...]:
    cells, adjacency = _g_terminal_incidence(
        comparison,
        scope,
        coarse,
        fine,
        guarded_coarse_edges,
    )
    return tuple(
        _g_canonical_json(_g_rooted_ball(root, cells, adjacency))
        for root in cells
    )


def _g_all_v5_trace_packet_kinds(
    scope: ScopedComparison,
) -> frozenset[str]:
    """Union packet kinds over every path in the finite v5 removal DAG."""

    coarse_classes = _face_classes(scope.coarse)
    fine_classes = _face_classes(scope.fine)
    initial = V5CollapseState(
        retained_coarse_edges=tuple(range(len(scope.coarse.nerve.edges))),
        retained_coarse_face_classes=tuple(range(len(coarse_classes))),
        retained_fine_edges=tuple(range(len(scope.fine.nerve.edges))),
        retained_fine_face_classes=tuple(range(len(fine_classes))),
        trace=(),
    )
    pending = [initial]
    seen: set[
        tuple[tuple[int, ...], tuple[int, ...], tuple[int, ...], tuple[int, ...]]
    ] = set()
    packet_kinds: set[str] = set()
    while pending:
        state = pending.pop()
        if state.cell_key in seen:
            continue
        seen.add(state.cell_key)
        packets = _v5_packet_variants(
            scope,
            coarse_classes,
            fine_classes,
            state,
        )
        for packet in packets:
            if packet.kind not in G_LOCAL_V1_PACKET_KIND_REGISTRY:
                raise AssertionError("v5 trace escaped the closed packet registry")
            packet_kinds.add(packet.kind)
            next_state = _apply_v5_packet(
                scope,
                coarse_classes,
                fine_classes,
                state,
                packet,
            )
            pending.append(V5CollapseState(*next_state.cell_key, trace=()))
    return frozenset(packet_kinds)


def _g_scope_record(
    comparison: UniformComparison,
    scope: ScopedComparison,
    *,
    whole: bool,
) -> dict[str, object]:
    reductions = _v5_terminal_reductions(scope)
    if not reductions:
        raise AssertionError("G_local-v1 observed no v5 terminal")
    packet_kinds = _g_all_v5_trace_packet_kinds(scope)
    condition_rows = []
    ball_payloads = []
    for _state, coarse, fine in reductions:
        c5, c6, _, guarded = _v4_c5_c6(scope, coarse, fine)
        guarded_set = frozenset(guarded)
        if whole:
            conditions = {
                "C0*": _c0(
                    scope,
                    coarse,
                    fine,
                    comparison.factor_pi,
                ),
                "C5*": c5,
                "C6*": c6,
            }
        else:
            conditions = {
                "C1*": _c1(scope, coarse, fine),
                "C2*": _c2(scope, coarse, fine),
                "C3*": _c3(scope, fine),
                "C4*": _c4(scope, coarse, fine),
            }
        condition_rows.append(conditions)
        ball_payloads.extend(
            _g_terminal_ball_payloads(
                comparison,
                scope,
                coarse,
                fine,
                guarded_set,
            )
        )
    condition_keys = (
        ("C0*", "C5*", "C6*")
        if whole
        else ("C1*", "C2*", "C3*", "C4*")
    )
    return {
        "conditions": {
            clause: all(row[clause] for row in condition_rows)
            for clause in condition_keys
        },
        "packet_kind_union": sorted(packet_kinds),
        "rooted_ball_histogram": _g_clipped_rows(
            ball_payloads,
            "ball",
        ),
    }


def _g_pi_preserving_relabels(
    factor_pi: tuple[int, ...],
    coarse_target_count: int,
    fine_target_count: int,
) -> tuple[tuple[tuple[int, ...], tuple[int, ...]], ...]:
    relabels = tuple(
        (coarse_relabel, fine_relabel)
        for coarse_relabel in permutations(range(coarse_target_count))
        for fine_relabel in permutations(range(fine_target_count))
        if all(
            coarse_relabel[factor_pi[target]]
            == factor_pi[fine_relabel[target]]
            for target in range(fine_target_count)
        )
    )
    if not relabels:
        raise AssertionError("factor pi has no identity-preserving relabel")
    return relabels


def _g_relabel_cell_label(
    label: dict[str, object],
    coarse_relabel: tuple[int, ...],
    fine_relabel: tuple[int, ...],
) -> dict[str, object]:
    support_relabel = (
        coarse_relabel if label["side"] == "coarse" else fine_relabel
    )
    return {
        **label,
        "support": sorted(support_relabel[target] for target in label["support"]),
        "pi_image": sorted(
            coarse_relabel[target] for target in label["pi_image"]
        ),
    }


def _g_relabel_ball(
    ball: dict[str, object],
    coarse_relabel: tuple[int, ...],
    fine_relabel: tuple[int, ...],
) -> dict[str, object]:
    descriptor_payloads = []
    for row in ball["neighbor_descriptors"]:
        descriptor = row["descriptor"]
        relabelled = {
            **descriptor,
            "neighbor_label": _g_relabel_cell_label(
                descriptor["neighbor_label"],
                coarse_relabel,
                fine_relabel,
            ),
        }
        descriptor_payloads.extend(
            [_g_canonical_json(relabelled)] * row["count"]
        )
    return {
        "root_label": _g_relabel_cell_label(
            ball["root_label"],
            coarse_relabel,
            fine_relabel,
        ),
        "neighbor_descriptors": _g_clipped_rows(
            descriptor_payloads,
            "descriptor",
        ),
    }


def _g_relabel_scope_record(
    record: dict[str, object],
    coarse_relabel: tuple[int, ...],
    fine_relabel: tuple[int, ...],
) -> dict[str, object]:
    ball_payloads = []
    for row in record["rooted_ball_histogram"]:
        relabelled = _g_relabel_ball(
            row["ball"],
            coarse_relabel,
            fine_relabel,
        )
        ball_payloads.extend([_g_canonical_json(relabelled)] * row["count"])
    return {
        "conditions": record["conditions"],
        "packet_kind_union": record["packet_kind_union"],
        "rooted_ball_histogram": _g_clipped_rows(
            ball_payloads,
            "ball",
        ),
    }


def _g_aggregate_vector(
    whole_record: dict[str, object],
    a_records: tuple[dict[str, object], ...],
) -> list[bool]:
    whole_conditions = whole_record["conditions"]
    relative = {
        clause: all(record["conditions"][clause] for record in a_records)
        for clause in ("C1*", "C2*", "C3*", "C4*")
    }
    aggregate = {
        "C0*": whole_conditions["C0*"],
        **relative,
        "C5*": whole_conditions["C5*"],
        "C6*": whole_conditions["C6*"],
    }
    return [aggregate[f"C{index}*"] for index in range(7)]


def observe_g_local_v1(comparison: UniformComparison) -> dict[str, object]:
    """Return the ID-free, multiplicity-truncated ``Obs_G`` value."""

    whole_targets = frozenset(range(comparison.coarse_target_count))
    whole_record = _g_scope_record(
        comparison,
        _a_scope(comparison, whole_targets),
        whole=True,
    )
    a_records = tuple(
        _g_scope_record(
            comparison,
            _a_scope(comparison, targets),
            whole=False,
        )
        for targets in nonempty_subsets(comparison.coarse_target_count)
    )
    aggregate_vector = _g_aggregate_vector(whole_record, a_records)
    canonical_candidates = []
    for coarse_relabel, fine_relabel in _g_pi_preserving_relabels(
        comparison.factor_pi,
        comparison.coarse_target_count,
        comparison.fine_target_count,
    ):
        relabelled_whole = _g_relabel_scope_record(
            whole_record,
            coarse_relabel,
            fine_relabel,
        )
        relabelled_a_payloads = (
            _g_canonical_json(
                _g_relabel_scope_record(
                    record,
                    coarse_relabel,
                    fine_relabel,
                )
            )
            for record in a_records
        )
        candidate = {
            "aggregate_C0_through_C6": aggregate_vector,
            "whole": relabelled_whole,
            "A_record_histogram": _g_clipped_rows(
                relabelled_a_payloads,
                "record",
            ),
        }
        canonical_candidates.append(_g_canonical_json(candidate))
    return json.loads(min(canonical_candidates))


def serialize_g_local_v1_observation(comparison: UniformComparison) -> str:
    """Serialize ``Obs_G`` with the preregistered compact JSON contract."""

    return _g_canonical_json(observe_g_local_v1(comparison))
