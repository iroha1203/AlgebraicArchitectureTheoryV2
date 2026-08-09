#!/usr/bin/env python3
"""Deterministic R2 candidate evaluation for the G-104 necessity map.

The predicates in this module use only finite incidence, derived Target
supports, and the partial cell map.  Cohomology is used only by the two
counterexample queries, never by the candidate clauses themselves.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
from fractions import Fraction
from hashlib import sha256
from itertools import permutations, product
import json
from typing import Iterable, Iterator

from necessity_map import (
    H1Analysis,
    Nerve,
    NerveMorphism,
    UniformComparison,
    calibration_fixtures,
    canonical_core_factors,
    canonical_firing_fixture,
    core_incidence_templates,
    derived_cell_supports,
    legacy_positive_fixture,
    nonempty_subsets,
    r0_report,
    r1_report,
    r1_necessity_witnesses,
    required_fixture_catalog_summary,
    support_hole_fixture,
)


CANDIDATE_SEMANTIC_ID = "R2-CSTAR-DIRECT-v1"
CANDIDATE_SPEC = "\n".join(
    (
        "scope:C1-C4 reduce both A-subnerves per nonempty A; C0,C5,C6 reduce both whole supported nerves once",
        "facetwin:exact ordered edge triple and exact derived Target-support signature",
        "reduction:quotient FaceTwin then simultaneously once remove every self-loop e and class (e,e,e) when e occurs in no other class",
        "critical:remaining self-loop or nonloop whose endpoints remain path-connected after deleting that edge",
        "active-fine-chart:endpoint of retained fine lift of a critical coarse edge or retained fine face mapping a retained coarse FaceTwin class",
        "C0:critical coarse vertex support equals union of pi-images of active fine chart supports in its phi-fiber",
        "C1:critical port is nonempty and connected by all selected fine edges with both endpoints in the port",
        "C2:every critical coarse edge has a retained mapped fine lift",
        "C3:retained edgeMap-none fiber cycles are spanned over Q by retained faceMap-none internal face boundaries",
        "C4:every retained coarse FaceTwin class has a retained fine face mapping one of its members",
        "direct-lifttwin:same retained fine face co-occurrence or occurrence in retained fine faces mapping one coarse FaceTwin class, with equal lift support signatures",
        "C5:the direct LiftTwin graph on each critical coarse edge lift set is a clique",
        "C6:each connected component of that graph over a critical coarse self-loop has a fine self-loop representative",
    )
)
CANDIDATE_SEMANTIC_SHA256 = sha256(CANDIDATE_SPEC.encode("ascii")).hexdigest()

COMPONENT_SEMANTIC_ID = "R2-CSTAR-COMPONENT-v2"
COMPONENT_SPEC = CANDIDATE_SPEC.replace(
    "C5:the direct LiftTwin graph on each critical coarse edge lift set is a clique",
    "C5:the direct LiftTwin graph on each critical coarse edge lift set has at most one connected component",
)
COMPONENT_SEMANTIC_SHA256 = sha256(COMPONENT_SPEC.encode("ascii")).hexdigest()

CERTIFIED_SEMANTIC_ID = "R2-CSTAR-CERTIFIED-v3"
CERTIFIED_SPEC = "\n".join(
    line
    for line in COMPONENT_SPEC.splitlines()
    if not line.startswith("direct-lifttwin:")
).replace(
    "C5:the direct LiftTwin graph on each critical coarse edge lift set has at most one connected component",
    "C5:the CertifiedDirect SLOT-or-KILL graph on each critical coarse edge lift set has at most one connected component",
).replace(
    "C6:each connected component of that graph over a critical coarse self-loop has a fine self-loop representative",
    "C6:each CertifiedDirect connected component over a critical coarse self-loop has a fine self-loop representative",
) + "\n" + "\n".join(
    (
        "certified-slot:two retained fine faces map one coarse FaceTwin class and differ in exactly one ordered boundary slot occupied by the two lifts; other edges and support signatures are exact",
        "certified-kill:a retained fine face has boundary (u,v,z) or (v,u,z), another has (z,z,z), mapped coarse boundaries are (E,E,Z) and (Z,Z,Z), and edge/face support signatures are exact",
        "certified-swap:reflexive transitive closure of the undirected SLOT-or-KILL relation",
    )
)
CERTIFIED_SEMANTIC_SHA256 = sha256(CERTIFIED_SPEC.encode("ascii")).hexdigest()

REGISTERED_ROUND_PAYLOAD_SHA256 = (
    "82aa4aa6895bbde75e5092f265f18d217fa66c17b63c16ebad92011a239861de",
    "ebc6f486a661e4fa53598d0c53efaaacf3cd1c4535e79fa31afedc222f7b260a",
    "bcd3408ebe16429dec1a136a64c1ee4fffc99c6adcd31c548cd90cdf9cb6e381",
    "d35620af9bfee3bf2e301ad91b562f3e788a063873a0042cee8425c20d72ce94",
    "09012de4338717f4332336a4a51b1d6103e59264f600c17827004d17699982c4",
    "26de136bd3ace9b399560242655ad7027be2e82d67749aeaa4e199163f7d2429",
    "6cd110d05b6e1537589ac5f002818a68d0778f3534190f125abd14438eac4c56",
)
FINAL_R0_SEMANTIC_SHA256 = (
    "dd982e5ded6395371c421e1d6223c2bf7489a07b723797fdeda55d99a172b455"
)
FINAL_R1_SEMANTIC_SHA256 = (
    "ff2d9fa12eb64bf343d3148f081e1164d4216d8548e53d90550eb53886dd359a"
)
ROUND8_DIAGNOSTIC_PAYLOAD_SHA256 = (
    "a239fbd921b7fd97de25ad0d00a43b5d5195116c9ecbf8d83e1f1911dffe3178"
)
ROUND9_VALID_PAYLOAD_SHA256 = (
    "596fe4631155389798e5590953f7582048b3b37da7766859115f66a197f8aceb"
)
ROUND9_RESULT_ISSUE_COMMENT = 5230876303


def _canonical_report_sha256(report: dict[str, object]) -> str:
    rendered = json.dumps(report, ensure_ascii=False, indent=2, sort_keys=True) + "\n"
    return sha256(rendered.encode("utf-8")).hexdigest()


def _assert_registered_round_payload_hashes(
    actual: tuple[str, ...],
) -> None:
    if actual != REGISTERED_ROUND_PAYLOAD_SHA256:
        raise AssertionError("Round8 registered Round1-7 payload SHA drift")


def _assert_round9_hash_baseline(
    *,
    r0_sha256: str,
    r1_sha256: str,
    round8_sha256: str,
    round8: dict[str, object],
) -> None:
    population = round8.get("population", {})
    progress = round8.get("progress_audit", {})
    baseline_hashes = round8.get("baseline_payload_sha256", {})
    candidate = round8.get("candidate", {})
    if not (
        r0_sha256 == FINAL_R0_SEMANTIC_SHA256
        and r1_sha256 == FINAL_R1_SEMANTIC_SHA256
        and round8_sha256 == ROUND8_DIAGNOSTIC_PAYLOAD_SHA256
        and round8.get("valid") is False
        and progress.get("streak_after_round") == 0
        and tuple(baseline_hashes.values()) == REGISTERED_ROUND_PAYLOAD_SHA256
        and candidate.get("semantic_id") == CERTIFIED_SEMANTIC_ID
        and candidate.get("semantic_sha256") == CERTIFIED_SEMANTIC_SHA256
        and population.get("total_raw_cases") == 1910
        and population.get("prior_full_semantic_payload_ids") == 1908
        and population.get("prior_truncated_semantic_payload_ids") == 1908
        and len(population.get("new_full_semantic_payload_ids", ())) == 2
        and len(population.get("new_truncated_semantic_payload_ids", ())) == 2
        and population.get("full_sha256_collision_count") == 0
        and population.get("truncated_20hex_collision_count") == 0
    ):
        raise AssertionError("Round9 R0/R1/Round1-8 hash baseline drift")


def _assert_round10_hash_baseline(
    *,
    round9_sha256: str,
    round9: dict[str, object],
) -> None:
    """Fail closed before admitting either prior or new Round10 queries."""

    baseline = round9.get("baseline_payload_sha256", {})
    diagnostic = round9.get("round8_diagnostic_baseline", {})
    candidate = round9.get("candidate", {})
    population = round9.get("population", {})
    queries = round9.get("queries", {})
    progress = round9.get("progress_audit", {})
    blocker = round9.get("same_blocker_evidence", {})
    if not (
        round9_sha256 == ROUND9_VALID_PAYLOAD_SHA256
        and round9.get("valid") is True
        and round9.get("final_R0_calibration_comment") == 5230818358
        and baseline.get("r0") == FINAL_R0_SEMANTIC_SHA256
        and baseline.get("r1") == FINAL_R1_SEMANTIC_SHA256
        and tuple(baseline.get("round1_through_round7", ()))
        == REGISTERED_ROUND_PAYLOAD_SHA256
        and baseline.get("round8_diagnostic")
        == ROUND8_DIAGNOSTIC_PAYLOAD_SHA256
        and diagnostic.get("valid") is False
        and diagnostic.get("streak_after_round") == 0
        and diagnostic.get("counted_in_stop_streak") is False
        and candidate.get("semantic_id") == CERTIFIED_SEMANTIC_ID
        and candidate.get("semantic_sha256") == CERTIFIED_SEMANTIC_SHA256
        and population.get("prior_raw_cases_recomputed") == 1910
        and population.get("prior_full_semantic_payload_ids") == 1910
        and population.get("prior_truncated_semantic_payload_ids") == 1910
        and len(population.get("new_full_semantic_payload_ids", ())) == 2
        and len(population.get("new_truncated_semantic_payload_ids", ())) == 2
        and population.get("total_raw_cases") == 1912
        and population.get("total_full_semantic_payload_ids") == 1912
        and population.get("total_truncated_semantic_payload_ids") == 1912
        and population.get("full_sha256_collision_count") == 0
        and population.get("truncated_20hex_collision_count") == 0
        and queries.get("prior_sufficiency_or_necessity_break_count") == 0
        and queries.get("new_sufficiency_break_count") == 0
        and queries.get("new_necessity_break_count") == 0
        and queries.get("new_counterexample_count") == 0
        and progress.get("progress") is False
        and progress.get("streak_after_round") == 1
        and blocker.get("valid_no_progress_1_of_2") is True
    ):
        raise AssertionError("Round10 R0/R1/Round1-9 hash baseline drift")


@dataclass(frozen=True)
class SideData:
    nerve: Nerve
    chart_supports: tuple[frozenset[int], ...]
    edge_supports: tuple[frozenset[int], ...]
    face_supports: tuple[frozenset[int], ...]


@dataclass(frozen=True)
class FaceClass:
    members: tuple[int, ...]
    boundary: tuple[int, int, int]
    support: frozenset[int]


@dataclass(frozen=True)
class ReducedSide:
    data: SideData
    face_classes: tuple[FaceClass, ...]
    retained_face_classes: tuple[int, ...]
    retained_edges: tuple[int, ...]
    critical_edges: tuple[int, ...]
    critical_vertices: tuple[int, ...]
    removed_free_pairs: tuple[tuple[int, int], ...]

    @property
    def retained_face_members(self) -> frozenset[int]:
        return frozenset(
            member
            for index in self.retained_face_classes
            for member in self.face_classes[index].members
        )

    @property
    def retained_face_member_to_class(self) -> dict[int, int]:
        return {
            member: index
            for index in self.retained_face_classes
            for member in self.face_classes[index].members
        }


@dataclass(frozen=True)
class ScopedComparison:
    coarse: SideData
    fine: SideData
    morphism: NerveMorphism


def _intersect_supports(
    supports: Iterable[frozenset[int]],
    targets: frozenset[int],
) -> tuple[frozenset[int], ...]:
    return tuple(support & targets for support in supports)


def _whole_scope(comparison: UniformComparison) -> ScopedComparison:
    coarse_edges, coarse_faces = derived_cell_supports(
        comparison.morphism.coarse,
        comparison.coarse_chart_supports,
    )
    fine_edges, fine_faces = derived_cell_supports(
        comparison.morphism.fine,
        comparison.fine_chart_supports,
    )
    return ScopedComparison(
        coarse=SideData(
            comparison.morphism.coarse,
            comparison.coarse_chart_supports,
            coarse_edges,
            coarse_faces,
        ),
        fine=SideData(
            comparison.morphism.fine,
            comparison.fine_chart_supports,
            fine_edges,
            fine_faces,
        ),
        morphism=comparison.morphism,
    )


def _a_scope(
    comparison: UniformComparison,
    coarse_targets: frozenset[int],
) -> ScopedComparison:
    sub = comparison.coordinate_subcomparison(coarse_targets)
    coarse_all_edges, coarse_all_faces = derived_cell_supports(
        comparison.morphism.coarse,
        comparison.coarse_chart_supports,
    )
    fine_all_edges, fine_all_faces = derived_cell_supports(
        comparison.morphism.fine,
        comparison.fine_chart_supports,
    )
    return ScopedComparison(
        coarse=SideData(
            sub.coarse.nerve,
            _intersect_supports(
                (comparison.coarse_chart_supports[index] for index in sub.coarse.vertices),
                coarse_targets,
            ),
            _intersect_supports(
                (coarse_all_edges[index] for index in sub.coarse.edges),
                coarse_targets,
            ),
            _intersect_supports(
                (coarse_all_faces[index] for index in sub.coarse.faces),
                coarse_targets,
            ),
        ),
        fine=SideData(
            sub.fine.nerve,
            _intersect_supports(
                (comparison.fine_chart_supports[index] for index in sub.fine.vertices),
                sub.fine_targets,
            ),
            _intersect_supports(
                (fine_all_edges[index] for index in sub.fine.edges),
                sub.fine_targets,
            ),
            _intersect_supports(
                (fine_all_faces[index] for index in sub.fine.faces),
                sub.fine_targets,
            ),
        ),
        morphism=sub.morphism,
    )


def _face_classes(side: SideData) -> tuple[FaceClass, ...]:
    groups: dict[tuple[tuple[int, int, int], tuple[int, ...]], list[int]] = {}
    for face, boundary in enumerate(side.nerve.faces):
        key = (boundary, tuple(sorted(side.face_supports[face])))
        groups.setdefault(key, []).append(face)
    return tuple(
        FaceClass(tuple(members), boundary, frozenset(support))
        for (boundary, support), members in sorted(groups.items())
    )


def _path_without_edge(nerve: Nerve, retained: set[int], omitted: int) -> bool:
    left, right = nerve.edges[omitted]
    if left == right:
        return True
    adjacency = {vertex: set() for vertex in range(nerve.vertices)}
    for edge in retained:
        if edge == omitted:
            continue
        source, target = nerve.edges[edge]
        adjacency[source].add(target)
        adjacency[target].add(source)
    reached = {left}
    frontier = [left]
    while frontier:
        current = frontier.pop()
        for neighbour in sorted(adjacency[current] - reached):
            reached.add(neighbour)
            frontier.append(neighbour)
    return right in reached


def reduce_side(side: SideData) -> ReducedSide:
    classes = _face_classes(side)
    eligible: list[tuple[int, int]] = []
    for class_index, face_class in enumerate(classes):
        edge0, edge1, edge2 = face_class.boundary
        if not edge0 == edge1 == edge2:
            continue
        edge = edge0
        if side.nerve.edges[edge][0] != side.nerve.edges[edge][1]:
            continue
        if any(
            edge in other.boundary
            for other_index, other in enumerate(classes)
            if other_index != class_index
        ):
            continue
        eligible.append((edge, class_index))

    removed_edges = {edge for edge, _ in eligible}
    removed_classes = {face_class for _, face_class in eligible}
    retained_edges = set(range(len(side.nerve.edges))) - removed_edges
    retained_classes = tuple(
        index for index in range(len(classes)) if index not in removed_classes
    )
    critical_edges = tuple(
        edge
        for edge in sorted(retained_edges)
        if _path_without_edge(side.nerve, retained_edges, edge)
    )
    critical_vertices = {
        vertex
        for edge in critical_edges
        for vertex in side.nerve.edges[edge]
    }
    for class_index in retained_classes:
        for edge in classes[class_index].boundary:
            critical_vertices.update(side.nerve.edges[edge])
    return ReducedSide(
        data=side,
        face_classes=classes,
        retained_face_classes=retained_classes,
        retained_edges=tuple(sorted(retained_edges)),
        critical_edges=critical_edges,
        critical_vertices=tuple(sorted(critical_vertices)),
        removed_free_pairs=tuple(sorted(eligible)),
    )


def _connected(vertices: set[int], edges: Iterable[tuple[int, int]]) -> bool:
    if not vertices:
        return False
    adjacency = {vertex: set() for vertex in vertices}
    for left, right in edges:
        if left in vertices and right in vertices:
            adjacency[left].add(right)
            adjacency[right].add(left)
    reached = {min(vertices)}
    frontier = list(reached)
    while frontier:
        current = frontier.pop()
        for neighbour in sorted(adjacency[current] - reached):
            reached.add(neighbour)
            frontier.append(neighbour)
    return reached == vertices


def _active_fine_vertices(
    scope: ScopedComparison,
    coarse: ReducedSide,
    fine: ReducedSide,
) -> set[int]:
    active: set[int] = set()
    critical_coarse_edges = set(coarse.critical_edges)
    for edge in fine.retained_edges:
        mapped = scope.morphism.edge_map[edge]
        if mapped in critical_coarse_edges:
            active.update(scope.fine.nerve.edges[edge])

    retained_coarse_faces = coarse.retained_face_members
    for class_index in fine.retained_face_classes:
        for face in fine.face_classes[class_index].members:
            mapped = scope.morphism.face_map[face]
            if mapped in retained_coarse_faces:
                for edge in scope.fine.nerve.faces[face]:
                    active.update(scope.fine.nerve.edges[edge])
    return active


def _c0(scope: ScopedComparison, coarse: ReducedSide, fine: ReducedSide, pi: tuple[int, ...]) -> bool:
    active = _active_fine_vertices(scope, coarse, fine)
    for coarse_vertex in coarse.critical_vertices:
        image_support = frozenset(
            pi[target]
            for fine_vertex in sorted(active)
            if scope.morphism.vertex_map[fine_vertex] == coarse_vertex
            for target in scope.fine.chart_supports[fine_vertex]
        )
        if image_support != scope.coarse.chart_supports[coarse_vertex]:
            return False
    return True


def _c1(scope: ScopedComparison, coarse: ReducedSide, fine: ReducedSide) -> bool:
    active = _active_fine_vertices(scope, coarse, fine)
    for coarse_vertex in coarse.critical_vertices:
        ports = {
            vertex
            for vertex in active
            if scope.morphism.vertex_map[vertex] == coarse_vertex
        }
        if not _connected(ports, scope.fine.nerve.edges):
            return False
    return True


def _c2(scope: ScopedComparison, coarse: ReducedSide, fine: ReducedSide) -> bool:
    retained_maps = {
        scope.morphism.edge_map[edge]
        for edge in fine.retained_edges
        if scope.morphism.edge_map[edge] is not None
    }
    return all(edge in retained_maps for edge in coarse.critical_edges)


def _local_unmapped_h1_dimension(
    scope: ScopedComparison,
    fine: ReducedSide,
    coarse_vertex: int,
) -> int:
    fiber = tuple(
        vertex
        for vertex, mapped in enumerate(scope.morphism.vertex_map)
        if mapped == coarse_vertex
    )
    vertex_index = {vertex: index for index, vertex in enumerate(fiber)}
    edges = tuple(
        edge
        for edge in fine.retained_edges
        if scope.morphism.edge_map[edge] is None
        and all(vertex in vertex_index for vertex in scope.fine.nerve.edges[edge])
    )
    edge_index = {edge: index for index, edge in enumerate(edges)}
    local_edges = tuple(
        tuple(vertex_index[vertex] for vertex in scope.fine.nerve.edges[edge])
        for edge in edges
    )
    local_faces: list[tuple[int, int, int]] = []
    for class_index in fine.retained_face_classes:
        face_class = fine.face_classes[class_index]
        if not any(scope.morphism.face_map[face] is None for face in face_class.members):
            continue
        if all(edge in edge_index for edge in face_class.boundary):
            local_faces.append(tuple(edge_index[edge] for edge in face_class.boundary))
    local = Nerve(len(fiber), local_edges, tuple(local_faces))
    return local.d1().kernel_basis().cols - local.d0().rank()


def _c3(scope: ScopedComparison, fine: ReducedSide) -> bool:
    return all(
        _local_unmapped_h1_dimension(scope, fine, coarse_vertex) == 0
        for coarse_vertex in range(scope.coarse.nerve.vertices)
    )


def _c4(scope: ScopedComparison, coarse: ReducedSide, fine: ReducedSide) -> bool:
    mapped_fine_faces = {
        scope.morphism.face_map[face]
        for class_index in fine.retained_face_classes
        for face in fine.face_classes[class_index].members
        if scope.morphism.face_map[face] is not None
    }
    return all(
        bool(set(coarse.face_classes[index].members) & mapped_fine_faces)
        for index in coarse.retained_face_classes
    )


def _direct_lifttwin_graph(
    scope: ScopedComparison,
    coarse: ReducedSide,
    fine: ReducedSide,
    coarse_edge: int,
    *,
    relation_mode: str,
) -> tuple[tuple[int, ...], dict[int, set[int]]]:
    if relation_mode not in {"broad", "certified"}:
        raise ValueError(f"unsupported LiftTwin relation: {relation_mode}")
    lifts = tuple(
        edge
        for edge in fine.retained_edges
        if scope.morphism.edge_map[edge] == coarse_edge
    )
    adjacency = {edge: set() for edge in lifts}
    retained_fine_faces = tuple(
        face
        for class_index in fine.retained_face_classes
        for face in fine.face_classes[class_index].members
    )
    coarse_face_to_class = coarse.retained_face_member_to_class

    for left_index, left in enumerate(lifts):
        for right in lifts[left_index + 1 :]:
            if scope.fine.edge_supports[left] != scope.fine.edge_supports[right]:
                continue
            related = (
                _broad_pair(
                    scope,
                    retained_fine_faces,
                    coarse_face_to_class,
                    left,
                    right,
                )
                if relation_mode == "broad"
                else _certified_pair(
                    scope,
                    coarse,
                    retained_fine_faces,
                    coarse_face_to_class,
                    coarse_edge,
                    left,
                    right,
                )
            )
            if related:
                adjacency[left].add(right)
                adjacency[right].add(left)
    return lifts, adjacency


def _broad_pair(
    scope: ScopedComparison,
    retained_fine_faces: tuple[int, ...],
    coarse_face_to_class: dict[int, int],
    left: int,
    right: int,
) -> bool:
    same_face = any(
        left in scope.fine.nerve.faces[face]
        and right in scope.fine.nerve.faces[face]
        for face in retained_fine_faces
    )
    same_coarse_class = any(
        left in scope.fine.nerve.faces[left_face]
        and right in scope.fine.nerve.faces[right_face]
        and scope.morphism.face_map[left_face] in coarse_face_to_class
        and scope.morphism.face_map[right_face] in coarse_face_to_class
        and coarse_face_to_class[scope.morphism.face_map[left_face]]
        == coarse_face_to_class[scope.morphism.face_map[right_face]]
        for left_face in retained_fine_faces
        for right_face in retained_fine_faces
    )
    return same_face or same_coarse_class


def _certified_pair(
    scope: ScopedComparison,
    coarse: ReducedSide,
    retained_fine_faces: tuple[int, ...],
    coarse_face_to_class: dict[int, int],
    coarse_edge: int,
    left: int,
    right: int,
) -> bool:
    # SLOT certificate.
    for left_face in retained_fine_faces:
        for right_face in retained_fine_faces:
            mapped_left = scope.morphism.face_map[left_face]
            mapped_right = scope.morphism.face_map[right_face]
            if (
                mapped_left not in coarse_face_to_class
                or mapped_right not in coarse_face_to_class
                or coarse_face_to_class[mapped_left]
                != coarse_face_to_class[mapped_right]
                or scope.fine.face_supports[left_face]
                != scope.fine.face_supports[right_face]
            ):
                continue
            left_boundary = scope.fine.nerve.faces[left_face]
            right_boundary = scope.fine.nerve.faces[right_face]
            different = [
                slot
                for slot in range(3)
                if left_boundary[slot] != right_boundary[slot]
            ]
            if len(different) == 1:
                slot = different[0]
                if {left_boundary[slot], right_boundary[slot]} == {left, right}:
                    return True

    # KILL certificate.
    retained_coarse_faces = coarse.retained_face_members
    for relation_face in retained_fine_faces:
        boundary = scope.fine.nerve.faces[relation_face]
        if boundary[:2] not in ((left, right), (right, left)):
            continue
        z = boundary[2]
        if not (
            scope.fine.edge_supports[left]
            == scope.fine.edge_supports[right]
            == scope.fine.edge_supports[z]
        ):
            continue
        mapped_z = scope.morphism.edge_map[z]
        mapped_relation = scope.morphism.face_map[relation_face]
        if mapped_z is None or mapped_relation not in retained_coarse_faces:
            continue
        if scope.coarse.nerve.faces[mapped_relation] != (
            coarse_edge,
            coarse_edge,
            mapped_z,
        ):
            continue
        for kill_face in retained_fine_faces:
            if scope.fine.nerve.faces[kill_face] != (z, z, z):
                continue
            mapped_kill = scope.morphism.face_map[kill_face]
            if (
                mapped_kill in retained_coarse_faces
                and scope.coarse.nerve.faces[mapped_kill]
                == (mapped_z, mapped_z, mapped_z)
                and scope.fine.face_supports[relation_face]
                == scope.fine.face_supports[kill_face]
            ):
                return True
    return False


def _components(vertices: tuple[int, ...], adjacency: dict[int, set[int]]) -> tuple[tuple[int, ...], ...]:
    remaining = set(vertices)
    result: list[tuple[int, ...]] = []
    while remaining:
        start = min(remaining)
        reached = {start}
        frontier = [start]
        while frontier:
            current = frontier.pop()
            for neighbour in sorted(adjacency[current] - reached):
                reached.add(neighbour)
                frontier.append(neighbour)
        remaining -= reached
        result.append(tuple(sorted(reached)))
    return tuple(result)


def _c5_c6(
    scope: ScopedComparison,
    coarse: ReducedSide,
    fine: ReducedSide,
    *,
    c5_mode: str,
) -> tuple[bool, bool, dict[str, object]]:
    if c5_mode not in {"clique", "component", "certified"}:
        raise ValueError(f"unsupported C5 mode: {c5_mode}")
    c5 = True
    c6 = True
    details: dict[str, object] = {}
    for edge in coarse.critical_edges:
        relation_mode = "certified" if c5_mode == "certified" else "broad"
        lifts, adjacency = _direct_lifttwin_graph(
            scope,
            coarse,
            fine,
            edge,
            relation_mode=relation_mode,
        )
        clique = all(
            right in adjacency[left]
            for index, left in enumerate(lifts)
            for right in lifts[index + 1 :]
        )
        components = _components(lifts, adjacency)
        c5_edge = clique if c5_mode == "clique" else len(components) <= 1
        if not c5_edge:
            c5 = False
        coarse_selfloop = scope.coarse.nerve.edges[edge][0] == scope.coarse.nerve.edges[edge][1]
        component_has_selfloop = tuple(
            any(
                scope.fine.nerve.edges[lift][0] == scope.fine.nerve.edges[lift][1]
                for lift in component
            )
            for component in components
        )
        if coarse_selfloop and not all(component_has_selfloop):
            c6 = False
        details[str(edge)] = {
            "lifts": list(lifts),
            "direct_edges": [
                [left, right]
                for left in lifts
                for right in sorted(adjacency[left])
                if left < right
            ],
            "clique": clique,
            "c5_mode": c5_mode,
            "c5_edge_holds": c5_edge,
            "components": [list(component) for component in components],
            "component_has_fine_selfloop": list(component_has_selfloop),
        }
    return c5, c6, details


def _reduction_summary(reduced: ReducedSide) -> dict[str, object]:
    return {
        "face_classes": [
            {
                "members": list(face_class.members),
                "boundary": list(face_class.boundary),
                "support": sorted(face_class.support),
            }
            for face_class in reduced.face_classes
        ],
        "removed_free_pairs": [list(pair) for pair in reduced.removed_free_pairs],
        "retained_edges": list(reduced.retained_edges),
        "retained_face_classes": list(reduced.retained_face_classes),
        "critical_edges": list(reduced.critical_edges),
        "critical_vertices": list(reduced.critical_vertices),
    }


def candidate_evaluation(
    comparison: UniformComparison,
    *,
    c5_mode: str = "clique",
) -> dict[str, object]:
    whole = _whole_scope(comparison)
    coarse_whole = reduce_side(whole.coarse)
    fine_whole = reduce_side(whole.fine)
    c0 = _c0(whole, coarse_whole, fine_whole, comparison.factor_pi)
    c5, c6, twin_details = _c5_c6(
        whole,
        coarse_whole,
        fine_whole,
        c5_mode=c5_mode,
    )

    per_subset = []
    aggregate = {"C0*": c0, "C1*": True, "C2*": True, "C3*": True, "C4*": True, "C5*": c5, "C6*": c6}
    for targets in nonempty_subsets(comparison.coarse_target_count):
        scope = _a_scope(comparison, targets)
        coarse = reduce_side(scope.coarse)
        fine = reduce_side(scope.fine)
        relative = {
            "C1*": _c1(scope, coarse, fine),
            "C2*": _c2(scope, coarse, fine),
            "C3*": _c3(scope, fine),
            "C4*": _c4(scope, coarse, fine),
        }
        for clause, value in relative.items():
            aggregate[clause] = aggregate[clause] and value
        per_subset.append(
            {
                "coarse_targets_A": sorted(targets),
                "conditions": relative,
                "coarse_reduction": _reduction_summary(coarse),
                "fine_reduction": _reduction_summary(fine),
            }
        )
    return {
        "aggregate": aggregate,
        "all": all(aggregate.values()),
        "whole": {
            "conditions": {"C0*": c0, "C5*": c5, "C6*": c6},
            "coarse_reduction": _reduction_summary(coarse_whole),
            "fine_reduction": _reduction_summary(fine_whole),
            "direct_lifttwin": twin_details,
        },
        "per_subset": per_subset,
    }


def chain3_fixture() -> UniformComparison:
    coarse = Nerve(1, ((0, 0), (0, 0), (0, 0)), ((1, 1, 1), (2, 2, 2), (0, 0, 1), (0, 0, 2)))
    fine = Nerve(1, ((0, 0), (0, 0), (0, 0), (0, 0), (0, 0)), ((3, 3, 3), (4, 4, 4), (0, 1, 3), (1, 2, 4)))
    unit = (frozenset((0,)),)
    return UniformComparison(
        name="R2_round1_Chain3",
        morphism=NerveMorphism(coarse, fine, (0,), (0, 0, 0, 1, 2), (0, 1, 2, 3)),
        coarse_target_count=1,
        fine_target_count=1,
        factor_pi=(0,),
        coarse_chart_supports=unit,
        fine_chart_supports=unit,
    )


def unkilled_twin_fixture() -> UniformComparison:
    coarse = Nerve(1, ((0, 0), (0, 0)), ((0, 0, 1),))
    fine = Nerve(1, ((0, 0), (0, 0), (0, 0)), ((0, 1, 2),))
    unit = (frozenset((0,)),)
    return UniformComparison(
        name="R2_round2_UnkilledTwin",
        morphism=NerveMorphism(coarse, fine, (0,), (0, 0, 1), (0,)),
        coarse_target_count=1,
        fine_target_count=1,
        factor_pi=(0,),
        coarse_chart_supports=unit,
        fine_chart_supports=unit,
    )


def _full_identity_comparison(name: str, nerve: Nerve) -> UniformComparison:
    return UniformComparison(
        name=name,
        morphism=NerveMorphism(
            nerve,
            nerve,
            tuple(range(nerve.vertices)),
            tuple(range(len(nerve.edges))),
            tuple(range(len(nerve.faces))),
        ),
        coarse_target_count=3,
        fine_target_count=4,
        factor_pi=(0, 0, 1, 2),
        coarse_chart_supports=tuple(
            frozenset((0, 1, 2)) for _ in range(nerve.vertices)
        ),
        fine_chart_supports=tuple(
            frozenset((0, 1, 2, 3)) for _ in range(nerve.vertices)
        ),
    )


def closed_2d_expansion_fixtures() -> tuple[UniformComparison, ...]:
    duplicate_triangle = Nerve(
        3,
        ((0, 1), (0, 2), (1, 2), (0, 1)),
        ((0, 1, 2), (0, 1, 2)),
    )
    shared_triangles = Nerve(
        4,
        ((0, 1), (0, 2), (1, 2), (0, 3), (1, 3), (0, 1)),
        ((0, 1, 2), (0, 3, 4)),
    )
    tetrahedron = Nerve(
        4,
        ((0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3), (0, 1)),
        ((0, 1, 3), (0, 2, 4), (1, 2, 5), (3, 4, 5)),
    )
    return (
        _full_identity_comparison("R2_round4_D0_duplicate_triangle", duplicate_triangle),
        _full_identity_comparison("R2_round4_D1_shared_triangles", shared_triangles),
        _full_identity_comparison("R2_round4_D2_tetrahedron_parallel", tetrahedron),
    )


def mixed_support_square_variants() -> Iterator[UniformComparison]:
    square = Nerve(4, ((0, 1), (1, 2), (2, 3), (3, 0)), ())
    morphism = NerveMorphism(square, square, (0, 1, 2, 3), (0, 1, 2, 3), ())
    pi = (0, 0, 1, 2, 3)
    masks = (
        frozenset((0,)),
        frozenset((1,)),
        frozenset((0, 1)),
        frozenset((2,)),
        frozenset((3,)),
        frozenset((0, 1, 2, 3)),
    )
    for coarse_supports in product(masks, repeat=4):
        fine_supports = tuple(
            frozenset(
                fine_target
                for fine_target, coarse_target in enumerate(pi)
                if coarse_target in support
            )
            for support in coarse_supports
        )
        yield UniformComparison(
            name=f"R2_round5_mixed_square:{coarse_supports}",
            morphism=morphism,
            coarse_target_count=4,
            fine_target_count=5,
            factor_pi=pi,
            coarse_chart_supports=tuple(coarse_supports),
            fine_chart_supports=fine_supports,
        )


def face_chain_fixture(
    name: str,
    lift_count: int,
    *,
    coarse_target_count: int = 1,
    fine_target_count: int = 1,
    factor_pi: tuple[int, ...] = (0,),
) -> UniformComparison:
    if lift_count < 2:
        raise ValueError("a face chain needs at least two lifts")
    relation_count = lift_count - 1
    coarse_edges = tuple((0, 0) for _ in range(1 + relation_count))
    fine_edges = tuple((0, 0) for _ in range(lift_count + relation_count))
    coarse_faces: list[tuple[int, int, int]] = []
    fine_faces: list[tuple[int, int, int]] = []
    for index in range(relation_count):
        coarse_z = 1 + index
        fine_z = lift_count + index
        coarse_faces.extend(((coarse_z, coarse_z, coarse_z), (0, 0, coarse_z)))
        fine_faces.extend(((fine_z, fine_z, fine_z), (index, index + 1, fine_z)))
    coarse = Nerve(1, coarse_edges, tuple(coarse_faces))
    fine = Nerve(1, fine_edges, tuple(fine_faces))
    coarse_full = frozenset(range(coarse_target_count))
    fine_full = frozenset(range(fine_target_count))
    return UniformComparison(
        name=name,
        morphism=NerveMorphism(
            coarse,
            fine,
            (0,),
            tuple(0 for _ in range(lift_count))
            + tuple(1 + index for index in range(relation_count)),
            tuple(range(2 * relation_count)),
        ),
        coarse_target_count=coarse_target_count,
        fine_target_count=fine_target_count,
        factor_pi=factor_pi,
        coarse_chart_supports=(coarse_full,),
        fine_chart_supports=(fine_full,),
    )


def round6_face_chains() -> tuple[UniformComparison, ...]:
    return (
        face_chain_fixture("R2_round6_LinearChain4", 4),
        face_chain_fixture("R2_round6_LinearChain5", 5),
    )


def face_chain_graph_fixture(
    name: str,
    lift_count: int,
    relations: tuple[tuple[int, int], ...],
) -> UniformComparison:
    if any(
        not (0 <= left < lift_count and 0 <= right < lift_count and left != right)
        for left, right in relations
    ):
        raise ValueError("face-chain graph relation leaves the lift set")
    coarse_edges = tuple((0, 0) for _ in range(1 + len(relations)))
    fine_edges = tuple((0, 0) for _ in range(lift_count + len(relations)))
    coarse_faces: list[tuple[int, int, int]] = []
    fine_faces: list[tuple[int, int, int]] = []
    for index, (left, right) in enumerate(relations):
        coarse_z = 1 + index
        fine_z = lift_count + index
        coarse_faces.extend(((coarse_z, coarse_z, coarse_z), (0, 0, coarse_z)))
        fine_faces.extend(((fine_z, fine_z, fine_z), (left, right, fine_z)))
    coarse = Nerve(1, coarse_edges, tuple(coarse_faces))
    fine = Nerve(1, fine_edges, tuple(fine_faces))
    return UniformComparison(
        name=name,
        morphism=NerveMorphism(
            coarse,
            fine,
            (0,),
            tuple(0 for _ in range(lift_count))
            + tuple(1 + index for index in range(len(relations))),
            tuple(range(2 * len(relations))),
        ),
        coarse_target_count=4,
        fine_target_count=5,
        factor_pi=(0, 0, 1, 2, 3),
        coarse_chart_supports=(frozenset((0, 1, 2, 3)),),
        fine_chart_supports=(frozenset((0, 1, 2, 3, 4)),),
    )


def round7_face_chain_graphs() -> tuple[UniformComparison, ...]:
    return (
        face_chain_graph_fixture(
            "R2_round7_B0_branching_tree",
            5,
            ((0, 1), (1, 2), (1, 3), (3, 4)),
        ),
        face_chain_graph_fixture(
            "R2_round7_B1_cyclic_chain",
            4,
            ((0, 1), (1, 2), (2, 3), (3, 0)),
        ),
    )


R8_L6_KILL_RELATIONS = (
    (0, 1),
    (1, 2),
    (2, 3),
    (3, 4),
    (4, 5),
)
R8_CL3_SLOT_RELATIONS = (
    (0, 1),
    (1, 2),
    (2, 0),
    (3, 4),
    (4, 5),
    (5, 3),
    (0, 3),
    (1, 4),
    (2, 5),
)
R9_DIAMOND_KILL_RELATIONS = ((0, 1), (1, 2), (2, 0))
R9_DIAMOND_SLOT_RELATIONS = ((1, 3), (3, 2))
R9_FIGURE8_KILL_RELATIONS = (
    (0, 1),
    (1, 2),
    (2, 0),
    (0, 3),
    (3, 4),
    (4, 0),
)
R10_A_KILL_RELATIONS = ((0, 2), (0, 3), (1, 4))
R10_A_SLOT_RELATIONS = ((0, 4), (1, 2), (1, 3))
R10_B_K4_KILL_RELATIONS = ((0, 1), (1, 2), (2, 0))
R10_B_K4_SLOT_RELATIONS = ((0, 3), (1, 3), (2, 3))
R10_B_STAR_KILL_RELATIONS = ((0, 1),)
R10_B_STAR_SLOT_RELATIONS = ((0, 2), (0, 3))


def _checked_relations(
    lift_count: int,
    relations: tuple[tuple[int, int], ...],
) -> tuple[tuple[int, int], ...]:
    if not 1 <= lift_count <= 6:
        raise ValueError("relation grammar supports one through six lifts")
    normalized = tuple(
        (min(left, right), max(left, right)) for left, right in relations
    )
    if any(
        not (0 <= left < right < lift_count) for left, right in normalized
    ):
        raise ValueError("relation leaves the lift vertex set or is a self-edge")
    if len(normalized) != len(set(normalized)):
        raise ValueError("duplicate relation")
    return normalized


def relation_grammar_fixture(
    name: str,
    lift_count: int,
    *,
    kill_relations: tuple[tuple[int, int], ...] = (),
    slot_relations: tuple[tuple[int, int], ...] = (),
) -> UniformComparison:
    """Build the preregistered exact common KILL/SLOT grammar."""

    checked_kill = _checked_relations(lift_count, kill_relations)
    checked_slot = _checked_relations(lift_count, slot_relations)
    if set(checked_kill) & set(checked_slot):
        raise ValueError("one unordered pair cannot have two relation colors")

    kill_count = len(kill_relations)
    slot_count = len(slot_relations)
    coarse_edges = tuple(
        (0, 0) for _ in range(1 + kill_count + 2 * slot_count)
    )
    fine_edges = tuple(
        (0, 0) for _ in range(lift_count + kill_count + 2 * slot_count)
    )
    coarse_faces: list[tuple[int, int, int]] = []
    fine_faces: list[tuple[int, int, int]] = []
    face_map: list[int] = []

    # KILL(u,v): Z=(z,z,z), F=(e,e,z) and their exact fine lifts.
    for index, (left, right) in enumerate(kill_relations):
        coarse_z = 1 + index
        fine_z = lift_count + index
        coarse_face_start = len(coarse_faces)
        coarse_faces.extend(
            ((coarse_z, coarse_z, coarse_z), (0, 0, coarse_z))
        )
        fine_faces.extend(
            ((fine_z, fine_z, fine_z), (left, right, fine_z))
        )
        face_map.extend((coarse_face_start, coarse_face_start + 1))

    # SLOT(u,v): one coarse (e,a,b), and two fine faces differing only in e.
    coarse_slot_edge_start = 1 + kill_count
    fine_slot_edge_start = lift_count + kill_count
    for index, (left, right) in enumerate(slot_relations):
        coarse_a = coarse_slot_edge_start + 2 * index
        coarse_b = coarse_a + 1
        fine_a = fine_slot_edge_start + 2 * index
        fine_b = fine_a + 1
        coarse_face = len(coarse_faces)
        coarse_faces.append((0, coarse_a, coarse_b))
        fine_faces.extend(
            ((left, fine_a, fine_b), (right, fine_a, fine_b))
        )
        face_map.extend((coarse_face, coarse_face))

    edge_map = (
        tuple(0 for _ in range(lift_count))
        + tuple(1 + index for index in range(kill_count))
        + tuple(
            coarse_slot_edge_start + index for index in range(2 * slot_count)
        )
    )
    coarse = Nerve(1, coarse_edges, tuple(coarse_faces))
    fine = Nerve(1, fine_edges, tuple(fine_faces))
    return UniformComparison(
        name=name,
        morphism=NerveMorphism(
            coarse,
            fine,
            (0,),
            edge_map,
            tuple(face_map),
        ),
        coarse_target_count=4,
        fine_target_count=5,
        factor_pi=(0, 0, 1, 2, 3),
        coarse_chart_supports=(frozenset((0, 1, 2, 3)),),
        fine_chart_supports=(frozenset((0, 1, 2, 3, 4)),),
    )


def round8_relation_fixtures() -> tuple[UniformComparison, ...]:
    return (
        relation_grammar_fixture(
            "R8-L6-KILL",
            6,
            kill_relations=R8_L6_KILL_RELATIONS,
        ),
        relation_grammar_fixture(
            "R8-CL3-SLOT",
            6,
            slot_relations=R8_CL3_SLOT_RELATIONS,
        ),
    )


def round9_figure8_split_support_fixture() -> UniformComparison:
    coarse_edges = tuple((0, 0) for _ in range(7)) + ((1, 1),)
    fine_edges = tuple((0, 0) for _ in range(11)) + ((1, 1),)
    coarse_faces: list[tuple[int, int, int]] = []
    fine_faces: list[tuple[int, int, int]] = []
    for index, (left, right) in enumerate(R9_FIGURE8_KILL_RELATIONS):
        coarse_z = 1 + index
        fine_z = 5 + index
        coarse_faces.extend(
            ((coarse_z, coarse_z, coarse_z), (0, 0, coarse_z))
        )
        fine_faces.extend(
            ((fine_z, fine_z, fine_z), (left, right, fine_z))
        )
    coarse = Nerve(2, coarse_edges, tuple(coarse_faces))
    fine = Nerve(2, fine_edges, tuple(fine_faces))
    return UniformComparison(
        name="R9-FIGURE8-SPLIT-SUPPORT",
        morphism=NerveMorphism(
            coarse,
            fine,
            (0, 1),
            (0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7),
            tuple(range(12)),
        ),
        coarse_target_count=4,
        fine_target_count=5,
        factor_pi=(0, 0, 1, 2, 3),
        coarse_chart_supports=(frozenset((0, 1)), frozenset((2, 3))),
        fine_chart_supports=(
            frozenset((0, 1, 2)),
            frozenset((3, 4)),
        ),
    )


def round9_relation_fixtures() -> tuple[UniformComparison, ...]:
    return (
        relation_grammar_fixture(
            "R9-DIAMOND-MIXED",
            4,
            kill_relations=R9_DIAMOND_KILL_RELATIONS,
            slot_relations=R9_DIAMOND_SLOT_RELATIONS,
        ),
        round9_figure8_split_support_fixture(),
    )


def round10_k23_mixed_overlap_fixture() -> UniformComparison:
    coarse_faces = (
        (1, 1, 1),
        (0, 0, 1),
        (2, 2, 2),
        (0, 0, 2),
        (3, 3, 3),
        (0, 0, 3),
        (0, 4, 5),
        (0, 6, 7),
        (0, 8, 9),
    )
    fine_faces = (
        (5, 5, 5),
        (0, 2, 5),
        (6, 6, 6),
        (0, 3, 6),
        (7, 7, 7),
        (1, 4, 7),
        (0, 8, 9),
        (4, 8, 9),
        (1, 10, 11),
        (2, 10, 11),
        (1, 12, 13),
        (3, 12, 13),
    )
    coarse = Nerve(
        2,
        tuple((0, 0) for _ in range(10)) + ((1, 1),),
        coarse_faces,
    )
    fine = Nerve(
        2,
        tuple((0, 0) for _ in range(14)) + ((1, 1),),
        fine_faces,
    )
    return UniformComparison(
        name="R10-A-K23-MIXED-OVERLAP",
        morphism=NerveMorphism(
            coarse,
            fine,
            (0, 1),
            (0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10),
            (0, 1, 2, 3, 4, 5, 6, 6, 7, 7, 8, 8),
        ),
        coarse_target_count=4,
        fine_target_count=5,
        factor_pi=(0, 0, 1, 2, 3),
        coarse_chart_supports=(frozenset((0, 1, 2)), frozenset((2, 3))),
        fine_chart_supports=(
            frozenset((0, 1, 2, 3)),
            frozenset((3, 4)),
        ),
    )


def round10_k4_star_multichart_fixture() -> UniformComparison:
    coarse_faces = (
        (1, 1, 1),
        (0, 0, 1),
        (2, 2, 2),
        (0, 0, 2),
        (3, 3, 3),
        (0, 0, 3),
        (0, 4, 5),
        (0, 6, 7),
        (0, 8, 9),
        (11, 11, 11),
        (10, 10, 11),
        (10, 12, 13),
        (10, 14, 15),
    )
    fine_faces = (
        (4, 4, 4),
        (0, 1, 4),
        (5, 5, 5),
        (1, 2, 5),
        (6, 6, 6),
        (2, 0, 6),
        (0, 7, 8),
        (3, 7, 8),
        (1, 9, 10),
        (3, 9, 10),
        (2, 11, 12),
        (3, 11, 12),
        (17, 17, 17),
        (13, 14, 17),
        (13, 18, 19),
        (15, 18, 19),
        (13, 20, 21),
        (16, 20, 21),
    )
    coarse = Nerve(
        3,
        tuple((0, 0) for _ in range(10))
        + tuple((1, 1) for _ in range(6))
        + ((2, 2),),
        coarse_faces,
    )
    fine = Nerve(
        3,
        tuple((0, 0) for _ in range(13))
        + tuple((1, 1) for _ in range(9))
        + ((2, 2),),
        fine_faces,
    )
    return UniformComparison(
        name="R10-B-K4-STAR-CHAIN-SUPPORT",
        morphism=NerveMorphism(
            coarse,
            fine,
            (0, 1, 2),
            (
                0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
                10, 10, 10, 10, 11, 12, 13, 14, 15, 16,
            ),
            (0, 1, 2, 3, 4, 5, 6, 6, 7, 7, 8, 8, 9, 10, 11, 11, 12, 12),
        ),
        coarse_target_count=4,
        fine_target_count=5,
        factor_pi=(0, 0, 1, 2, 3),
        coarse_chart_supports=(
            frozenset((0, 1)),
            frozenset((1, 2)),
            frozenset((2, 3)),
        ),
        fine_chart_supports=(
            frozenset((0, 1, 2)),
            frozenset((2, 3)),
            frozenset((3, 4)),
        ),
    )


def round10_relation_fixtures() -> tuple[UniformComparison, ...]:
    return (
        round10_k23_mixed_overlap_fixture(),
        round10_k4_star_multichart_fixture(),
    )


def relation_graph_canonical_code(
    lift_count: int,
    *,
    kill_relations: tuple[tuple[int, int], ...] = (),
    slot_relations: tuple[tuple[int, int], ...] = (),
) -> str:
    """Return the all-vertex-permutation minimum 0/1/2 colored-edge word."""

    kill = _checked_relations(lift_count, kill_relations)
    slot = _checked_relations(lift_count, slot_relations)
    if set(kill) & set(slot):
        raise ValueError("one unordered pair cannot have two relation colors")
    colors = {relation: 1 for relation in kill}
    colors.update({relation: 2 for relation in slot})
    words = (
        tuple(
            colors.get(
                tuple(sorted((ordering[left], ordering[right]))),
                0,
            )
            for left in range(lift_count)
            for right in range(left + 1, lift_count)
        )
        for ordering in permutations(range(lift_count))
    )
    return f"{lift_count}:" + "".join(str(color) for color in min(words))


def _relation_graph_invariant(
    lift_count: int,
    *,
    kill_relations: tuple[tuple[int, int], ...] = (),
    slot_relations: tuple[tuple[int, int], ...] = (),
) -> dict[str, object]:
    kill = _checked_relations(lift_count, kill_relations)
    slot = _checked_relations(lift_count, slot_relations)
    relations = kill + slot
    degrees = [0 for _ in range(lift_count)]
    adjacency = {vertex: set() for vertex in range(lift_count)}
    for left, right in relations:
        degrees[left] += 1
        degrees[right] += 1
        adjacency[left].add(right)
        adjacency[right].add(left)
    components = 0
    remaining = set(range(lift_count))
    while remaining:
        components += 1
        frontier = [min(remaining)]
        reached = set(frontier)
        while frontier:
            current = frontier.pop()
            for neighbour in sorted(adjacency[current] - reached):
                reached.add(neighbour)
                frontier.append(neighbour)
        remaining -= reached
    color_word = (
        f"K^{len(kill)}" if kill and not slot else
        f"S^{len(slot)}" if slot and not kill else
        f"K^{len(kill)}S^{len(slot)}"
    )
    return {
        "n": lift_count,
        "m": len(relations),
        "degrees": sorted(degrees),
        "beta1": len(relations) - lift_count + components,
        "colors": color_word,
    }


def relation_graph_support_code(
    comparison: UniformComparison,
    lift_count: int,
    *,
    kill_relations: tuple[tuple[int, int], ...] = (),
    slot_relations: tuple[tuple[int, int], ...] = (),
) -> str:
    payload = {
        "relation_graph_canonical_code": relation_graph_canonical_code(
            lift_count,
            kill_relations=kill_relations,
            slot_relations=slot_relations,
        ),
        "coarse_chart_count": comparison.morphism.coarse.vertices,
        "fine_chart_count": comparison.morphism.fine.vertices,
        "coarse_chart_supports": [
            sorted(support) for support in comparison.coarse_chart_supports
        ],
        "fine_chart_supports": [
            sorted(support) for support in comparison.fine_chart_supports
        ],
        "factor_pi": list(comparison.factor_pi),
        "vertex_map": list(comparison.morphism.vertex_map),
    }
    rendered = json.dumps(payload, sort_keys=True, separators=(",", ":"))
    return sha256(rendered.encode("ascii")).hexdigest()


@dataclass(frozen=True)
class RelationBlockCodeSpec:
    lift_count: int
    kill_relations: tuple[tuple[int, int], ...]
    slot_relations: tuple[tuple[int, int], ...] = ()


@dataclass(frozen=True)
class ChartCodeSpec:
    coarse_support: frozenset[int]
    fine_support: frozenset[int]
    relation_blocks: tuple[RelationBlockCodeSpec, ...] = ()
    identity_loop_count: int = 0


def colored_graph_support_canonical_code(
    *,
    factor_pi: tuple[int, ...],
    chart_records: tuple[ChartCodeSpec, ...],
    coarse_cell_counts: tuple[int, int, int],
    fine_cell_counts: tuple[int, int, int],
) -> dict[str, str]:
    """Canonicalize lift, chart, and pi-compatible target relabelings."""

    fine_target_count = len(factor_pi)
    coarse_target_count = max(factor_pi, default=-1) + 1
    if not (
        coarse_target_count > 0
        and set(factor_pi) == set(range(coarse_target_count))
        and len(chart_records) == coarse_cell_counts[0] == fine_cell_counts[0]
        and all(record.identity_loop_count >= 0 for record in chart_records)
        and all(
            set(record.coarse_support) <= set(range(coarse_target_count))
            and set(record.fine_support) <= set(range(fine_target_count))
            for record in chart_records
        )
    ):
        raise ValueError("invalid colored graph/support canonicalization input")

    block_codes = tuple(
        tuple(
            sorted(
                relation_graph_canonical_code(
                    block.lift_count,
                    kill_relations=block.kill_relations,
                    slot_relations=block.slot_relations,
                )
                for block in record.relation_blocks
            )
        )
        for record in chart_records
    )
    fiber_profile = sorted(
        sum(mapped == coarse for mapped in factor_pi)
        for coarse in range(coarse_target_count)
    )
    candidates: list[str] = []
    for coarse_permutation in permutations(range(coarse_target_count)):
        for fine_permutation in permutations(range(fine_target_count)):
            if not all(
                coarse_permutation[factor_pi[target]]
                == factor_pi[fine_permutation[target]]
                for target in range(fine_target_count)
            ):
                continue
            transformed_records = sorted(
                [
                    [
                        sorted(
                            coarse_permutation[target]
                            for target in record.coarse_support
                        ),
                        sorted(
                            fine_permutation[target]
                            for target in record.fine_support
                        ),
                        list(block_codes[index]),
                        record.identity_loop_count,
                    ]
                    for index, record in enumerate(chart_records)
                ]
            )
            payload = [
                [coarse_target_count, fine_target_count],
                fiber_profile,
                transformed_records,
                [list(coarse_cell_counts), list(fine_cell_counts)],
            ]
            candidates.append(json.dumps(payload, separators=(",", ":")))
    if not candidates:
        raise AssertionError("no pi-compatible target relabeling")
    compact_json = min(candidates)
    return {
        "compact_json": compact_json,
        "sha256": sha256(compact_json.encode("ascii")).hexdigest(),
    }


def _required_catalog() -> tuple[UniformComparison, ...]:
    return (
        *calibration_fixtures(),
        support_hole_fixture(),
        canonical_firing_fixture(),
        legacy_positive_fixture(),
        *r1_necessity_witnesses().values(),
    )


def _core_population() -> Iterator[UniformComparison]:
    for template_name, morphism in core_incidence_templates():
        for coarse_count, fine_count, factor_pi in canonical_core_factors():
            coarse_options = nonempty_subsets(coarse_count)
            fine_options = nonempty_subsets(fine_count)
            for coarse_supports in product(coarse_options, repeat=morphism.coarse.vertices):
                for fine_supports in product(fine_options, repeat=morphism.fine.vertices):
                    if not all(
                        {factor_pi[target] for target in fine_supports[fine_chart]}
                        <= set(coarse_supports[morphism.vertex_map[fine_chart]])
                        for fine_chart in range(morphism.fine.vertices)
                    ):
                        continue
                    yield UniformComparison(
                        name=f"core:{template_name}:{coarse_count}:{fine_count}:{factor_pi}:{coarse_supports}:{fine_supports}",
                        morphism=morphism,
                        coarse_target_count=coarse_count,
                        fine_target_count=fine_count,
                        factor_pi=factor_pi,
                        coarse_chart_supports=tuple(coarse_supports),
                        fine_chart_supports=tuple(fine_supports),
                    )


def _case_semantic_payload_json(comparison: UniformComparison) -> str:
    semantic_summary = dict(comparison.summary())
    semantic_summary.pop("name")
    return json.dumps(semantic_summary, sort_keys=True, separators=(",", ":"))


def _case_semantic_sha256(comparison: UniformComparison) -> str:
    payload = _case_semantic_payload_json(comparison)
    return sha256(payload.encode("utf-8")).hexdigest()


def _case_id(comparison: UniformComparison) -> str:
    return _case_semantic_sha256(comparison)[:20]


def _case_result(
    comparison: UniformComparison,
    category: str,
    *,
    c5_mode: str = "clique",
) -> dict[str, object]:
    candidate = candidate_evaluation(comparison, c5_mode=c5_mode)
    blocks = comparison.block_analyses()
    uniform = all(analysis.isomorphism for _, analysis in blocks)
    bad_blocks = [
        {"coarse_targets_A": sorted(targets), "h1": asdict(analysis)}
        for targets, analysis in blocks
        if not analysis.isomorphism
    ]
    return {
        "id": _case_id(comparison),
        "name": comparison.name,
        "category": category,
        "uniform": uniform,
        "bad_blocks": bad_blocks,
        "candidate": candidate,
        "sufficiency_break": candidate["all"] and bool(bad_blocks),
        "necessity_break": uniform and not candidate["all"],
    }


def round1_report() -> dict[str, object]:
    cases: list[dict[str, object]] = []
    cases.extend(_case_result(comparison, "core") for comparison in _core_population())
    cases.extend(_case_result(comparison, "required_catalog") for comparison in _required_catalog())
    chain = _case_result(chain3_fixture(), "round1_chain3")
    cases.append(chain)

    if len([case for case in cases if case["category"] == "core"]) != 590:
        raise AssertionError("round1 core population drifted from preregistration")
    expected_chain = {
        "C0*": True,
        "C1*": True,
        "C2*": True,
        "C3*": True,
        "C4*": True,
        "C5*": False,
        "C6*": True,
    }
    chain_analysis = chain3_fixture().block_analyses()[0][1]
    if not (
        chain["uniform"]
        and chain["candidate"]["aggregate"] == expected_chain
        and chain_analysis == H1Analysis(1, 1, 1, True, True, True)
    ):
        raise AssertionError("registered Chain3 calibration mismatch")

    sufficiency = [case for case in cases if case["sufficiency_break"]]
    necessity = [case for case in cases if case["necessity_break"]]
    return {
        "round": "R2-round-1",
        "preregistered_issue_comments": [5230386108, 5230405605],
        "candidate": {
            "semantic_id": CANDIDATE_SEMANTIC_ID,
            "semantic_sha256": CANDIDATE_SEMANTIC_SHA256,
            "spec": CANDIDATE_SPEC,
        },
        "population": {
            "core": 590,
            "required_catalog": len(_required_catalog()),
            "round_fixture": 1,
            "total": len(cases),
            "all_cases_evaluated": True,
        },
        "queries": {
            "sufficiency_break_count": len(sufficiency),
            "necessity_break_count": len(necessity),
            "sufficiency_break_ids": [case["id"] for case in sufficiency],
            "necessity_break_ids": [case["id"] for case in necessity],
        },
        "registered_chain3": chain,
        "counterexamples": {
            "sufficiency": sufficiency,
            "necessity": necessity,
        },
        "coverage_limit": "Exactly the 590 preregistered core cases, 13 required fixtures, and Chain3; arbitrary larger incidence is not covered.",
    }


def round2_report() -> dict[str, object]:
    cases: list[dict[str, object]] = []
    cases.extend(
        _case_result(comparison, "core", c5_mode="component")
        for comparison in _core_population()
    )
    cases.extend(
        _case_result(comparison, "required_catalog", c5_mode="component")
        for comparison in _required_catalog()
    )
    chain = _case_result(chain3_fixture(), "round1_chain3", c5_mode="component")
    unkilled = _case_result(
        unkilled_twin_fixture(),
        "round2_unkilled_twin",
        c5_mode="component",
    )
    cases.extend((chain, unkilled))

    if len(cases) != 605:
        raise AssertionError("round2 population is not the registered strict superset")
    chain_expected = {f"C{index}*": True for index in range(7)}
    unkilled_analysis = unkilled_twin_fixture().block_analyses()[0][1]
    if not (
        chain["uniform"]
        and chain["candidate"]["aggregate"] == chain_expected
        and unkilled["candidate"]["aggregate"] == chain_expected
        and unkilled_analysis == H1Analysis(1, 2, 1, True, False, False)
        and unkilled["sufficiency_break"]
    ):
        raise AssertionError("registered round2 fixture calibration mismatch")

    sufficiency = [case for case in cases if case["sufficiency_break"]]
    necessity = [case for case in cases if case["necessity_break"]]
    return {
        "round": "R2-round-2",
        "preregistered_issue_comment": 5230446212,
        "candidate": {
            "semantic_id": COMPONENT_SEMANTIC_ID,
            "semantic_sha256": COMPONENT_SEMANTIC_SHA256,
            "spec": COMPONENT_SPEC,
        },
        "population": {
            "round1_population": 604,
            "new_fixture": 1,
            "total": len(cases),
            "strict_superset": True,
            "all_cases_evaluated": True,
        },
        "queries": {
            "sufficiency_break_count": len(sufficiency),
            "necessity_break_count": len(necessity),
            "sufficiency_break_ids": [case["id"] for case in sufficiency],
            "necessity_break_ids": [case["id"] for case in necessity],
        },
        "registered_chain3": chain,
        "registered_unkilled_twin": unkilled,
        "counterexamples": {
            "sufficiency": sufficiency,
            "necessity": necessity,
        },
        "coverage_limit": "Exactly the round1 population plus UnkilledTwin; arbitrary larger incidence is not covered.",
    }


def round3_report() -> dict[str, object]:
    cases: list[dict[str, object]] = []
    cases.extend(
        _case_result(comparison, "core", c5_mode="certified")
        for comparison in _core_population()
    )
    cases.extend(
        _case_result(comparison, "required_catalog", c5_mode="certified")
        for comparison in _required_catalog()
    )
    chain = _case_result(chain3_fixture(), "round1_chain3", c5_mode="certified")
    unkilled = _case_result(
        unkilled_twin_fixture(),
        "round2_unkilled_twin",
        c5_mode="certified",
    )
    cases.extend((chain, unkilled))

    expected_true = {f"C{index}*": True for index in range(7)}
    if not (
        len(cases) == 605
        and chain["uniform"]
        and chain["candidate"]["aggregate"] == expected_true
        and not unkilled["uniform"]
        and not unkilled["candidate"]["aggregate"]["C5*"]
        and not unkilled["sufficiency_break"]
    ):
        raise AssertionError("registered CERTIFIED-v3 calibration mismatch")

    sufficiency = [case for case in cases if case["sufficiency_break"]]
    necessity = [case for case in cases if case["necessity_break"]]
    return {
        "round": "R2-round-3",
        "preregistered_issue_comment": 5230453578,
        "candidate": {
            "semantic_id": CERTIFIED_SEMANTIC_ID,
            "semantic_sha256": CERTIFIED_SEMANTIC_SHA256,
            "spec": CERTIFIED_SPEC,
        },
        "population": {
            "round2_population": 605,
            "total": len(cases),
            "all_cases_evaluated": True,
        },
        "queries": {
            "sufficiency_break_count": len(sufficiency),
            "necessity_break_count": len(necessity),
            "sufficiency_break_ids": [case["id"] for case in sufficiency],
            "necessity_break_ids": [case["id"] for case in necessity],
        },
        "registered_chain3": chain,
        "registered_unkilled_twin": unkilled,
        "counterexamples": {
            "sufficiency": sufficiency,
            "necessity": necessity,
        },
        "coverage_limit": "Exactly the round2 population under CERTIFIED-v3; arbitrary larger incidence is not covered.",
    }


def round4_report() -> dict[str, object]:
    baseline: list[dict[str, object]] = []
    baseline.extend(
        _case_result(comparison, "core", c5_mode="certified")
        for comparison in _core_population()
    )
    baseline.extend(
        _case_result(comparison, "required_catalog", c5_mode="certified")
        for comparison in _required_catalog()
    )
    baseline.extend(
        (
            _case_result(chain3_fixture(), "round1_chain3", c5_mode="certified"),
            _case_result(
                unkilled_twin_fixture(),
                "round2_unkilled_twin",
                c5_mode="certified",
            ),
        )
    )
    expansion = [
        _case_result(comparison, "round4_closed_2d", c5_mode="certified")
        for comparison in closed_2d_expansion_fixtures()
    ]
    cases = baseline + expansion
    baseline_ids = {case["id"] for case in baseline}
    new_ids = [case["id"] for case in expansion if case["id"] not in baseline_ids]
    if not (
        len(baseline) == 605
        and len(cases) == 608
        and len(new_ids) == 3
        and all(case["candidate"]["all"] and case["uniform"] for case in expansion)
    ):
        raise AssertionError("registered CLOSED-2D-CORE expansion calibration mismatch")

    sufficiency = [case for case in cases if case["sufficiency_break"]]
    necessity = [case for case in cases if case["necessity_break"]]
    new_counterexamples = [
        case
        for case in expansion
        if case["sufficiency_break"] or case["necessity_break"]
    ]
    return {
        "round": "R2-round-4",
        "preregistered_issue_comment": 5230462990,
        "candidate": {
            "semantic_id": CERTIFIED_SEMANTIC_ID,
            "semantic_sha256": CERTIFIED_SEMANTIC_SHA256,
            "spec": CERTIFIED_SPEC,
        },
        "population": {
            "baseline": 605,
            "new_incidence_cases": 3,
            "total": len(cases),
            "strict_superset": len(new_ids) == 3,
            "new_ids": new_ids,
            "all_cases_evaluated": True,
        },
        "queries": {
            "sufficiency_break_count": len(sufficiency),
            "necessity_break_count": len(necessity),
            "new_counterexample_count": len(new_counterexamples),
            "new_counterexample_ids": [case["id"] for case in new_counterexamples],
        },
        "expansion_cases": expansion,
        "progress_audit": {
            "new_verdicts": [],
            "new_nonisomorphic_counterexamples": [
                case["id"] for case in new_counterexamples
            ],
            "candidate_semantic_change": False,
            "calibration_fixes": [],
        },
        "blocker_id": "PB-R2-NONFREE-GLOBAL-FACE-CHAIN",
        "coverage_limit": "Three fixed-label closed two-dimensional identity cores; general face multiplicities and nonidentity refinements are not covered.",
    }


def round5_report() -> dict[str, object]:
    # The prior result is invoked as the exact 608-case baseline.  Its compact
    # counterexample query is retained; the 1,296 new cases are recorded in full.
    prior = round4_report()
    expansion = [
        _case_result(comparison, "round5_mixed_support", c5_mode="certified")
        for comparison in mixed_support_square_variants()
    ]
    baseline_ids = {
        *prior["population"]["new_ids"],
        _case_id(chain3_fixture()),
        _case_id(unkilled_twin_fixture()),
        *(_case_id(comparison) for comparison in _required_catalog()),
        *(_case_id(comparison) for comparison in _core_population()),
    }
    new_ids = [case["id"] for case in expansion if case["id"] not in baseline_ids]
    new_counterexamples = [
        case
        for case in expansion
        if case["sufficiency_break"] or case["necessity_break"]
    ]
    if not (
        len(expansion) == 1296
        and len(new_ids) == 1296
        and len(set(new_ids)) == 1296
        and all(case["uniform"] and case["candidate"]["all"] for case in expansion)
    ):
        raise AssertionError("registered MIXED-SUPPORT-A-UNION expansion calibration mismatch")

    return {
        "round": "R2-round-5",
        "preregistered_issue_comment": 5230467922,
        "candidate": {
            "semantic_id": CERTIFIED_SEMANTIC_ID,
            "semantic_sha256": CERTIFIED_SEMANTIC_SHA256,
            "spec": CERTIFIED_SPEC,
        },
        "population": {
            "baseline": 608,
            "raw_support_assignments": 1296,
            "valid_support_assignments": 1296,
            "new_fixed_label_ids": len(new_ids),
            "total": 608 + len(expansion),
            "strict_superset": len(new_ids) == 1296,
            "all_cases_evaluated": True,
            "nonempty_A_per_new_case": 15,
            "new_A_block_queries": 1296 * 15,
        },
        "queries": {
            "baseline_sufficiency_break_count": prior["queries"]["sufficiency_break_count"],
            "baseline_necessity_break_count": prior["queries"]["necessity_break_count"],
            "new_sufficiency_break_count": sum(case["sufficiency_break"] for case in expansion),
            "new_necessity_break_count": sum(case["necessity_break"] for case in expansion),
            "new_counterexample_count": len(new_counterexamples),
            "new_counterexample_ids": [case["id"] for case in new_counterexamples],
        },
        "new_case_ids": new_ids,
        "support_histogram": {
            "coarse_mask_assignments": 1296,
            "fine_support_rule": "exact pi-preimage",
            "target_sizes": {"coarse": 4, "fine": 5},
        },
        "progress_audit": {
            "new_verdicts": [],
            "new_nonisomorphic_counterexamples": [
                case["id"] for case in new_counterexamples
            ],
            "candidate_semantic_change": False,
            "calibration_fixes": [],
        },
        "blocker_id": "PB-R2-NONFREE-GLOBAL-FACE-CHAIN",
        "coverage_limit": "One fixed-label identity square with six coarse chart masks and exact pi-preimages; arbitrary support masks and nonidentity incidence are not covered.",
    }


def _prior_semantic_ids_through_round5() -> set[str]:
    return {
        *(_case_id(comparison) for comparison in _core_population()),
        *(_case_id(comparison) for comparison in _required_catalog()),
        _case_id(chain3_fixture()),
        _case_id(unkilled_twin_fixture()),
        *(_case_id(comparison) for comparison in closed_2d_expansion_fixtures()),
        *(_case_id(comparison) for comparison in mixed_support_square_variants()),
    }


def round6_report() -> dict[str, object]:
    prior = round5_report()
    prior_ids = _prior_semantic_ids_through_round5()
    expansion = [
        _case_result(comparison, "round6_nonfree_linear_chain", c5_mode="certified")
        for comparison in round6_face_chains()
    ]
    new_ids = [case["id"] for case in expansion if case["id"] not in prior_ids]
    expected = H1Analysis(1, 1, 1, True, True, True)
    new_counterexamples = [
        case
        for case in expansion
        if case["sufficiency_break"] or case["necessity_break"]
    ]
    if not (
        prior["population"]["total"] == 1904
        and len(new_ids) == len(set(new_ids)) == 2
        and all(case["uniform"] and case["candidate"]["all"] for case in expansion)
        and all(
            comparison.block_analyses()[0][1] == expected
            for comparison in round6_face_chains()
        )
        and all(
            not case["candidate"]["whole"]["coarse_reduction"]["removed_free_pairs"]
            and not case["candidate"]["whole"]["fine_reduction"]["removed_free_pairs"]
            for case in expansion
        )
    ):
        raise AssertionError("registered NONFREE-LINEAR-FACE-CHAIN calibration mismatch")

    return {
        "round": "R2-round-6",
        "preregistered_issue_comment": 5230507176,
        "candidate": {
            "semantic_id": CERTIFIED_SEMANTIC_ID,
            "semantic_sha256": CERTIFIED_SEMANTIC_SHA256,
            "spec": CERTIFIED_SPEC,
        },
        "population": {
            "prior_raw_cases_recomputed": 1904,
            "prior_semantic_unique_ids": len(prior_ids),
            "new_nonidentity_face_chains": 2,
            "new_semantic_ids": new_ids,
            "strict_superset": len(new_ids) == 2,
            "total_raw_cases": 1906,
            "all_cases_evaluated": True,
        },
        "queries": {
            "prior_new_counterexample_count": prior["queries"]["new_counterexample_count"],
            "new_sufficiency_break_count": sum(case["sufficiency_break"] for case in expansion),
            "new_necessity_break_count": sum(case["necessity_break"] for case in expansion),
            "new_counterexample_count": len(new_counterexamples),
            "new_counterexample_ids": [case["id"] for case in new_counterexamples],
        },
        "expansion_cases": expansion,
        "progress_audit": {
            "new_verdicts": [],
            "new_nonisomorphic_counterexamples": [
                case["id"] for case in new_counterexamples
            ],
            "candidate_semantic_change": False,
            "calibration_fixes": [],
        },
        "blocker_id": "PB-R2-NONFREE-GLOBAL-FACE-CHAIN",
        "same_blocker_evidence": {
            "nonidentity": True,
            "retained_face_chain_lengths": [3, 4],
            "free_pair_count": 0,
            "remaining_gap": "No general proof for arbitrary length or branching of retained face chains.",
        },
        "coverage_limit": "Two linear nonfree face chains of lift counts four and five; branching and arbitrary length are not covered.",
    }


def round7_report() -> dict[str, object]:
    prior = round6_report()
    prior_ids = _prior_semantic_ids_through_round5() | {
        _case_id(comparison) for comparison in round6_face_chains()
    }
    expansion = [
        _case_result(
            comparison,
            "round7_nonfree_branching_face_chain",
            c5_mode="certified",
        )
        for comparison in round7_face_chain_graphs()
    ]
    new_ids = [case["id"] for case in expansion if case["id"] not in prior_ids]
    expected = H1Analysis(1, 1, 1, True, True, True)
    new_counterexamples = [
        case
        for case in expansion
        if case["sufficiency_break"] or case["necessity_break"]
    ]
    if not (
        prior["population"]["total_raw_cases"] == 1906
        and len(new_ids) == len(set(new_ids)) == 2
        and all(case["uniform"] and case["candidate"]["all"] for case in expansion)
        and all(
            all(analysis == expected for _, analysis in comparison.block_analyses())
            for comparison in round7_face_chain_graphs()
        )
        and all(
            not case["candidate"]["whole"]["coarse_reduction"]["removed_free_pairs"]
            and not case["candidate"]["whole"]["fine_reduction"]["removed_free_pairs"]
            for case in expansion
        )
    ):
        raise AssertionError("registered NONFREE-BRANCHING-FACE-CHAIN calibration mismatch")

    return {
        "round": "R2-round-7",
        "preregistered_issue_comment": 5230514887,
        "candidate": {
            "semantic_id": CERTIFIED_SEMANTIC_ID,
            "semantic_sha256": CERTIFIED_SEMANTIC_SHA256,
            "spec": CERTIFIED_SPEC,
        },
        "population": {
            "prior_raw_cases_recomputed": 1906,
            "prior_semantic_unique_ids": len(prior_ids),
            "new_nonidentity_face_chain_graphs": 2,
            "new_semantic_ids": new_ids,
            "strict_superset": len(new_ids) == 2,
            "total_raw_cases": 1908,
            "all_cases_evaluated": True,
            "nonempty_A_per_new_case": 15,
        },
        "queries": {
            "prior_new_counterexample_count": prior["queries"]["new_counterexample_count"],
            "new_sufficiency_break_count": sum(case["sufficiency_break"] for case in expansion),
            "new_necessity_break_count": sum(case["necessity_break"] for case in expansion),
            "new_counterexample_count": len(new_counterexamples),
            "new_counterexample_ids": [case["id"] for case in new_counterexamples],
        },
        "expansion_cases": expansion,
        "progress_audit": {
            "new_verdicts": [],
            "new_nonisomorphic_counterexamples": [
                case["id"] for case in new_counterexamples
            ],
            "candidate_semantic_change": False,
            "calibration_fixes": [],
        },
        "blocker_id": "PB-R2-NONFREE-GLOBAL-FACE-CHAIN",
        "same_blocker_evidence": {
            "nonidentity": True,
            "relation_graphs": ["branching-tree", "cycle"],
            "free_pair_count": 0,
            "remaining_gap": "No general proof for arbitrary retained face-chain graphs.",
        },
        "coverage_limit": "One branching tree and one cycle relation graph at full Target support; arbitrary graph size and support distribution are not covered.",
    }


def _all_comparisons_through_round7() -> Iterator[UniformComparison]:
    yield from _core_population()
    yield from _required_catalog()
    yield chain3_fixture()
    yield unkilled_twin_fixture()
    yield from closed_2d_expansion_fixtures()
    yield from mixed_support_square_variants()
    yield from round6_face_chains()
    yield from round7_face_chain_graphs()


def _registered_relation_graph_codes() -> dict[str, str]:
    rows = (
        (
            "R6-L4-KILL",
            4,
            ((0, 1), (1, 2), (2, 3)),
            (),
        ),
        (
            "R6-L5-KILL",
            5,
            ((0, 1), (1, 2), (2, 3), (3, 4)),
            (),
        ),
        (
            "R7-B0-KILL",
            5,
            ((0, 1), (1, 2), (1, 3), (3, 4)),
            (),
        ),
        (
            "R7-B1-KILL",
            4,
            ((0, 1), (1, 2), (2, 3), (3, 0)),
            (),
        ),
        (
            "R8-L6-KILL",
            6,
            R8_L6_KILL_RELATIONS,
            (),
        ),
        (
            "R8-CL3-SLOT",
            6,
            (),
            R8_CL3_SLOT_RELATIONS,
        ),
    )
    return {
        name: relation_graph_canonical_code(
            lift_count,
            kill_relations=kill,
            slot_relations=slot,
        )
        for name, lift_count, kill, slot in rows
    }


def _all_comparisons_through_round8() -> Iterator[UniformComparison]:
    yield from _all_comparisons_through_round7()
    yield from round8_relation_fixtures()


def _all_comparisons_through_round9() -> Iterator[UniformComparison]:
    yield from _all_comparisons_through_round8()
    yield from round9_relation_fixtures()


def _registered_relation_graph_support_codes_through_round9(
) -> dict[str, dict[str, str]]:
    round6 = round6_face_chains()
    round7 = round7_face_chain_graphs()
    round8 = round8_relation_fixtures()
    round9 = round9_relation_fixtures()
    rows = (
        (
            "R6-L4-KILL",
            round6[0],
            4,
            ((0, 1), (1, 2), (2, 3)),
            (),
        ),
        (
            "R6-L5-KILL",
            round6[1],
            5,
            ((0, 1), (1, 2), (2, 3), (3, 4)),
            (),
        ),
        (
            "R7-B0-KILL",
            round7[0],
            5,
            ((0, 1), (1, 2), (1, 3), (3, 4)),
            (),
        ),
        (
            "R7-B1-KILL",
            round7[1],
            4,
            ((0, 1), (1, 2), (2, 3), (3, 0)),
            (),
        ),
        (
            "R8-L6-KILL",
            round8[0],
            6,
            R8_L6_KILL_RELATIONS,
            (),
        ),
        (
            "R8-CL3-SLOT",
            round8[1],
            6,
            (),
            R8_CL3_SLOT_RELATIONS,
        ),
        (
            "R9-DIAMOND-MIXED",
            round9[0],
            4,
            R9_DIAMOND_KILL_RELATIONS,
            R9_DIAMOND_SLOT_RELATIONS,
        ),
        (
            "R9-FIGURE8-SPLIT-SUPPORT",
            round9[1],
            5,
            R9_FIGURE8_KILL_RELATIONS,
            (),
        ),
    )
    return {
        name: {
            "relation_graph_canonical_code": relation_graph_canonical_code(
                lift_count,
                kill_relations=kill,
                slot_relations=slot,
            ),
            "relation_graph_support_code": relation_graph_support_code(
                comparison,
                lift_count,
                kill_relations=kill,
                slot_relations=slot,
            ),
        }
        for name, comparison, lift_count, kill, slot in rows
    }


def _comparison_cell_counts(
    comparison: UniformComparison,
) -> tuple[tuple[int, int, int], tuple[int, int, int]]:
    return (
        (
            comparison.morphism.coarse.vertices,
            len(comparison.morphism.coarse.edges),
            len(comparison.morphism.coarse.faces),
        ),
        (
            comparison.morphism.fine.vertices,
            len(comparison.morphism.fine.edges),
            len(comparison.morphism.fine.faces),
        ),
    )


def _registered_colored_graph_support_codes_through_round10(
) -> dict[str, dict[str, str]]:
    round6 = round6_face_chains()
    round7 = round7_face_chain_graphs()
    round8 = round8_relation_fixtures()
    round9 = round9_relation_fixtures()
    round10 = round10_relation_fixtures()
    rows = (
        (
            "R6-L4-KILL",
            round6[0],
            (
                ChartCodeSpec(
                    frozenset((0,)),
                    frozenset((0,)),
                    (RelationBlockCodeSpec(4, ((0, 1), (1, 2), (2, 3))),),
                ),
            ),
        ),
        (
            "R6-L5-KILL",
            round6[1],
            (
                ChartCodeSpec(
                    frozenset((0,)),
                    frozenset((0,)),
                    (
                        RelationBlockCodeSpec(
                            5,
                            ((0, 1), (1, 2), (2, 3), (3, 4)),
                        ),
                    ),
                ),
            ),
        ),
        (
            "R7-B0-KILL",
            round7[0],
            (
                ChartCodeSpec(
                    frozenset((0, 1, 2, 3)),
                    frozenset((0, 1, 2, 3, 4)),
                    (
                        RelationBlockCodeSpec(
                            5,
                            ((0, 1), (1, 2), (1, 3), (3, 4)),
                        ),
                    ),
                ),
            ),
        ),
        (
            "R7-B1-KILL",
            round7[1],
            (
                ChartCodeSpec(
                    frozenset((0, 1, 2, 3)),
                    frozenset((0, 1, 2, 3, 4)),
                    (
                        RelationBlockCodeSpec(
                            4,
                            ((0, 1), (1, 2), (2, 3), (3, 0)),
                        ),
                    ),
                ),
            ),
        ),
        (
            "R8-L6-KILL",
            round8[0],
            (
                ChartCodeSpec(
                    frozenset((0, 1, 2, 3)),
                    frozenset((0, 1, 2, 3, 4)),
                    (RelationBlockCodeSpec(6, R8_L6_KILL_RELATIONS),),
                ),
            ),
        ),
        (
            "R8-CL3-SLOT",
            round8[1],
            (
                ChartCodeSpec(
                    frozenset((0, 1, 2, 3)),
                    frozenset((0, 1, 2, 3, 4)),
                    (RelationBlockCodeSpec(6, (), R8_CL3_SLOT_RELATIONS),),
                ),
            ),
        ),
        (
            "R9-DIAMOND-MIXED",
            round9[0],
            (
                ChartCodeSpec(
                    frozenset((0, 1, 2, 3)),
                    frozenset((0, 1, 2, 3, 4)),
                    (
                        RelationBlockCodeSpec(
                            4,
                            R9_DIAMOND_KILL_RELATIONS,
                            R9_DIAMOND_SLOT_RELATIONS,
                        ),
                    ),
                ),
            ),
        ),
        (
            "R9-FIGURE8-SPLIT-SUPPORT",
            round9[1],
            (
                ChartCodeSpec(
                    frozenset((0, 1)),
                    frozenset((0, 1, 2)),
                    (RelationBlockCodeSpec(5, R9_FIGURE8_KILL_RELATIONS),),
                ),
                ChartCodeSpec(
                    frozenset((2, 3)),
                    frozenset((3, 4)),
                    identity_loop_count=1,
                ),
            ),
        ),
        (
            "R10-A-K23-MIXED-OVERLAP",
            round10[0],
            (
                ChartCodeSpec(
                    frozenset((0, 1, 2)),
                    frozenset((0, 1, 2, 3)),
                    (
                        RelationBlockCodeSpec(
                            5,
                            R10_A_KILL_RELATIONS,
                            R10_A_SLOT_RELATIONS,
                        ),
                    ),
                ),
                ChartCodeSpec(
                    frozenset((2, 3)),
                    frozenset((3, 4)),
                    identity_loop_count=1,
                ),
            ),
        ),
        (
            "R10-B-K4-STAR-CHAIN-SUPPORT",
            round10[1],
            (
                ChartCodeSpec(
                    frozenset((0, 1)),
                    frozenset((0, 1, 2)),
                    (
                        RelationBlockCodeSpec(
                            4,
                            R10_B_K4_KILL_RELATIONS,
                            R10_B_K4_SLOT_RELATIONS,
                        ),
                    ),
                ),
                ChartCodeSpec(
                    frozenset((1, 2)),
                    frozenset((2, 3)),
                    (
                        RelationBlockCodeSpec(
                            4,
                            R10_B_STAR_KILL_RELATIONS,
                            R10_B_STAR_SLOT_RELATIONS,
                        ),
                    ),
                ),
                ChartCodeSpec(
                    frozenset((2, 3)),
                    frozenset((3, 4)),
                    identity_loop_count=1,
                ),
            ),
        ),
    )
    result: dict[str, dict[str, str]] = {}
    for name, comparison, charts in rows:
        coarse_counts, fine_counts = _comparison_cell_counts(comparison)
        result[name] = colored_graph_support_canonical_code(
            factor_pi=comparison.factor_pi,
            chart_records=charts,
            coarse_cell_counts=coarse_counts,
            fine_cell_counts=fine_counts,
        )
    return result


def round8_report() -> dict[str, object]:
    """Run the preregistered longer-linear/circular-ladder strict expansion."""

    if not (
        CERTIFIED_SEMANTIC_ID == "R2-CSTAR-CERTIFIED-v3"
        and CERTIFIED_SEMANTIC_SHA256
        == "cbb02677a055c69ecf0bb50a5de884fb55bbd4b4b59b75d256815eae69ec4daa"
    ):
        raise AssertionError("Round8 candidate semantic payload drifted")

    # Re-run and byte-canonically hash every registered payload before admitting
    # either prior or new Round8 queries.
    prior_reports = (
        round1_report(),
        round2_report(),
        round3_report(),
        round4_report(),
        round5_report(),
        round6_report(),
        round7_report(),
    )
    actual_round_payload_sha256 = tuple(
        _canonical_report_sha256(report) for report in prior_reports
    )
    _assert_registered_round_payload_hashes(actual_round_payload_sha256)
    prior_round = prior_reports[-1]
    prior_comparisons = tuple(_all_comparisons_through_round7())
    prior_full_ids = tuple(
        _case_semantic_sha256(comparison) for comparison in prior_comparisons
    )
    prior_short_ids = tuple(identifier[:20] for identifier in prior_full_ids)
    if not (
        prior_round["population"]["total_raw_cases"] == 1908
        and len(prior_comparisons) == 1908
        and len(set(prior_full_ids)) == 1908
        and len(set(prior_short_ids)) == 1908
    ):
        raise AssertionError("Round8 prior 1908-case baseline is invalid")

    fixtures = round8_relation_fixtures()
    expansion = []
    for comparison in fixtures:
        case = _case_result(
            comparison,
            "round8_relation_grammar",
            c5_mode="certified",
        )
        case["semantic_sha256"] = _case_semantic_sha256(comparison)
        expansion.append(case)
    expected_relations = (
        tuple(sorted(_checked_relations(6, R8_L6_KILL_RELATIONS))),
        tuple(sorted(_checked_relations(6, R8_CL3_SLOT_RELATIONS))),
    )
    expected_cells = ((1, 6, 10, 1, 11, 10), (1, 19, 9, 1, 24, 18))
    expected_h1 = (
        H1Analysis(1, 1, 1, True, True, True),
        H1Analysis(10, 10, 10, True, True, True),
    )
    expected_invariants = (
        {
            "n": 6,
            "m": 5,
            "degrees": [1, 1, 2, 2, 2, 2],
            "beta1": 0,
            "colors": "K^5",
        },
        {
            "n": 6,
            "m": 9,
            "degrees": [3, 3, 3, 3, 3, 3],
            "beta1": 4,
            "colors": "S^9",
        },
    )
    actual_invariants = (
        _relation_graph_invariant(
            6,
            kill_relations=R8_L6_KILL_RELATIONS,
        ),
        _relation_graph_invariant(
            6,
            slot_relations=R8_CL3_SLOT_RELATIONS,
        ),
    )

    for comparison, case, cells, analysis, relations in zip(
        fixtures,
        expansion,
        expected_cells,
        expected_h1,
        expected_relations,
    ):
        coarse = comparison.morphism.coarse
        fine = comparison.morphism.fine
        actual_cells = (
            coarse.vertices,
            len(coarse.edges),
            len(coarse.faces),
            fine.vertices,
            len(fine.edges),
            len(fine.faces),
        )
        direct_edges = tuple(
            tuple(edge)
            for edge in case["candidate"]["whole"]["direct_lifttwin"]["0"][
                "direct_edges"
            ]
        )
        block_analyses = comparison.block_analyses()
        all_reductions = (
            case["candidate"]["whole"],
            *case["candidate"]["per_subset"],
        )
        if not (
            actual_cells == cells
            and sum(mapped == 0 for mapped in comparison.morphism.edge_map) == 6
            and len(block_analyses) == 15
            and all(item == analysis for _, item in block_analyses)
            and case["uniform"]
            and case["candidate"]["all"]
            and direct_edges == relations
            and all(
                not reduction["coarse_reduction"]["removed_free_pairs"]
                and not reduction["fine_reduction"]["removed_free_pairs"]
                for reduction in all_reductions
            )
        ):
            raise AssertionError(
                f"Round8 fixture/modeling calibration failed: {comparison.name}"
            )
    if actual_invariants != expected_invariants:
        raise AssertionError("Round8 colored relation-graph invariant mismatch")

    graph_codes = _registered_relation_graph_codes()
    if len(set(graph_codes.values())) != len(graph_codes):
        raise AssertionError("Round6/7/8 canonical colored-graph code collision")

    new_full_ids = tuple(case["semantic_sha256"] for case in expansion)
    new_short_ids = tuple(case["id"] for case in expansion)
    all_full_ids = prior_full_ids + new_full_ids
    all_short_ids = prior_short_ids + new_short_ids
    full_collision_count = len(all_full_ids) - len(set(all_full_ids))
    truncated_collision_count = len(all_short_ids) - len(set(all_short_ids))
    if not (
        all(full.startswith(short) for full, short in zip(new_full_ids, new_short_ids))
        and not (set(new_full_ids) & set(prior_full_ids))
        and not (set(new_short_ids) & set(prior_short_ids))
        and len(set(new_full_ids)) == len(set(new_short_ids)) == 2
        and len(all_full_ids) == len(all_short_ids) == 1910
        and full_collision_count == truncated_collision_count == 0
    ):
        raise AssertionError("Round8 semantic payload strict-expansion mismatch")

    prior_counterexamples: list[dict[str, str]] = []
    for comparison in prior_comparisons:
        result = _case_result(comparison, "round0_through_round7", c5_mode="certified")
        if result["sufficiency_break"] or result["necessity_break"]:
            prior_counterexamples.append(
                {
                    "id": result["id"],
                    "semantic_sha256": _case_semantic_sha256(comparison),
                    "query": (
                        "sufficiency_break"
                        if result["sufficiency_break"]
                        else "necessity_break"
                    ),
                }
            )
    if prior_counterexamples:
        raise AssertionError("Round8 prior 1908-case query baseline is invalid")
    new_counterexamples = [
        case
        for case in expansion
        if case["sufficiency_break"] or case["necessity_break"]
    ]
    new_verdicts = sorted(
        {
            "CSTAR-not-sufficient"
            for case in new_counterexamples
            if case["sufficiency_break"]
        }
        | {
            "CSTAR-not-necessary"
            for case in new_counterexamples
            if case["necessity_break"]
        }
    )
    new_canonical_counterexamples = [
        case["semantic_sha256"] for case in new_counterexamples
    ]
    candidate_semantic_change = False
    additional_calibration_fixes: list[str] = []
    progress = bool(
        new_verdicts
        or new_canonical_counterexamples
        or candidate_semantic_change
        or additional_calibration_fixes
    )

    return {
        "round": "R2-round-8",
        "preregistered_issue_comment": 5230713854,
        "calibration_reset_comment": 5230709695,
        "valid": False,
        "invalid_reason": (
            "Round8 query ran before final R0(e) Issue synchronization and "
            "coordinator release"
        ),
        "diagnostic_zero_result": not progress,
        "baseline_payload_sha256": {
            f"round{index}": payload_hash
            for index, payload_hash in enumerate(
                actual_round_payload_sha256,
                start=1,
            )
        },
        "candidate": {
            "semantic_id": CERTIFIED_SEMANTIC_ID,
            "semantic_sha256": CERTIFIED_SEMANTIC_SHA256,
            "spec": CERTIFIED_SPEC,
        },
        "population": {
            "prior_raw_cases_recomputed": len(prior_comparisons),
            "prior_full_semantic_payload_ids": len(set(prior_full_ids)),
            "prior_truncated_semantic_payload_ids": len(set(prior_short_ids)),
            "new_relation_grammar_cases": 2,
            "new_full_semantic_payload_ids": list(new_full_ids),
            "new_truncated_semantic_payload_ids": list(new_short_ids),
            "full_sha256_collision_count": full_collision_count,
            "truncated_20hex_collision_count": truncated_collision_count,
            "strict_superset": True,
            "total_raw_cases": 1910,
            "new_A_block_queries": sum(
                len(comparison.block_analyses()) for comparison in fixtures
            ),
            "all_cases_evaluated": True,
        },
        "canonical_colored_relation_graph_codes": graph_codes,
        "relation_graph_invariants": {
            comparison.name: invariant
            for comparison, invariant in zip(fixtures, actual_invariants)
        },
        "queries": {
            "prior_sufficiency_or_necessity_break_count": len(
                prior_counterexamples
            ),
            "prior_counterexamples": prior_counterexamples,
            "new_sufficiency_break_count": sum(
                case["sufficiency_break"] for case in expansion
            ),
            "new_necessity_break_count": sum(
                case["necessity_break"] for case in expansion
            ),
            "new_counterexample_count": len(new_counterexamples),
            "new_counterexample_ids": [
                case["semantic_sha256"] for case in new_counterexamples
            ],
        },
        "expansion_cases": expansion,
        "progress_audit": {
            "new_verdicts": new_verdicts,
            "new_canonical_nonisomorphic_counterexamples": (
                new_canonical_counterexamples
            ),
            "candidate_semantic_change": candidate_semantic_change,
            "additional_calibration_fixes": additional_calibration_fixes,
            "progress": progress,
            "streak_after_round": 0,
        },
        "blocker_id": "PB-R2-NONFREE-GLOBAL-FACE-CHAIN",
        "same_blocker_evidence": {
            "valid_no_progress_1_of_2": False,
            "finite_registered_graphs_close": True,
            "remaining_gap": "No general proof for an arbitrary retained nonfree face-chain relation graph.",
        },
        "coverage_limit": "The two fixed full-support six-lift relation graphs (a KILL path and the SLOT circular ladder C3 x K2) plus the recomputed prior 1908 cases; arbitrary relation graphs, larger lift sets, and mixed KILL/SLOT graphs are not covered.",
    }


def round9_report() -> dict[str, object]:
    """Run the preregistered mixed-color/split-support strict expansion."""

    if not (
        CERTIFIED_SEMANTIC_ID == "R2-CSTAR-CERTIFIED-v3"
        and CERTIFIED_SEMANTIC_SHA256
        == "cbb02677a055c69ecf0bb50a5de884fb55bbd4b4b59b75d256815eae69ec4daa"
    ):
        raise AssertionError("Round9 candidate semantic payload drifted")

    r0 = r0_report()
    r1 = r1_report()
    round8 = round8_report()
    r0_sha256 = _canonical_report_sha256(r0)
    r1_sha256 = _canonical_report_sha256(r1)
    round8_sha256 = _canonical_report_sha256(round8)
    _assert_round9_hash_baseline(
        r0_sha256=r0_sha256,
        r1_sha256=r1_sha256,
        round8_sha256=round8_sha256,
        round8=round8,
    )

    prior_comparisons = tuple(_all_comparisons_through_round8())
    prior_full_ids = tuple(
        _case_semantic_sha256(comparison) for comparison in prior_comparisons
    )
    prior_short_ids = tuple(identifier[:20] for identifier in prior_full_ids)
    if not (
        len(prior_comparisons) == 1910
        and len(set(prior_full_ids)) == 1910
        and len(set(prior_short_ids)) == 1910
    ):
        raise AssertionError("Round9 prior 1910-case semantic ID baseline drift")

    prior_counterexamples: list[dict[str, str]] = []
    for comparison in prior_comparisons:
        result = _case_result(
            comparison,
            "round0_through_round8",
            c5_mode="certified",
        )
        if result["sufficiency_break"] or result["necessity_break"]:
            prior_counterexamples.append(
                {
                    "id": result["id"],
                    "semantic_sha256": _case_semantic_sha256(comparison),
                    "query": (
                        "sufficiency_break"
                        if result["sufficiency_break"]
                        else "necessity_break"
                    ),
                }
            )
    if prior_counterexamples:
        raise AssertionError("Round9 prior 1910-case query baseline drift")

    diamond, figure8 = round9_relation_fixtures()
    fixtures = (diamond, figure8)
    expansion = []
    colored_relations = (
        {
            "KILL": tuple(sorted(_checked_relations(4, R9_DIAMOND_KILL_RELATIONS))),
            "SLOT": tuple(sorted(_checked_relations(4, R9_DIAMOND_SLOT_RELATIONS))),
        },
        {
            "KILL": tuple(sorted(_checked_relations(5, R9_FIGURE8_KILL_RELATIONS))),
            "SLOT": (),
        },
    )
    for comparison, registered_colors in zip(fixtures, colored_relations):
        case = _case_result(
            comparison,
            "round9_relation_grammar",
            c5_mode="certified",
        )
        case["semantic_sha256"] = _case_semantic_sha256(comparison)
        actual_direct = tuple(
            tuple(edge)
            for edge in case["candidate"]["whole"]["direct_lifttwin"]["0"][
                "direct_edges"
            ]
        )
        registered_direct = tuple(
            sorted(registered_colors["KILL"] + registered_colors["SLOT"])
        )
        case["certified_colored_adjacency"] = {
            "KILL": [list(edge) for edge in registered_colors["KILL"]],
            "SLOT": [list(edge) for edge in registered_colors["SLOT"]],
            "actual_uncolored": [list(edge) for edge in actual_direct],
            "unintended_edge_count": len(set(actual_direct) - set(registered_direct)),
        }
        case["all_block_h1"] = [
            {
                "coarse_targets_A": sorted(targets),
                "h1": asdict(analysis),
            }
            for targets, analysis in comparison.block_analyses()
        ]
        expansion.append(case)

    diamond_expected_h1 = H1Analysis(3, 3, 3, True, True, True)
    diamond_blocks = diamond.block_analyses()
    diamond_expected_faces = (
        (1, 1, 1),
        (0, 0, 1),
        (2, 2, 2),
        (0, 0, 2),
        (3, 3, 3),
        (0, 0, 3),
        (0, 4, 5),
        (0, 6, 7),
    )
    diamond_expected_fine_faces = (
        (4, 4, 4),
        (0, 1, 4),
        (5, 5, 5),
        (1, 2, 5),
        (6, 6, 6),
        (2, 0, 6),
        (1, 7, 8),
        (3, 7, 8),
        (3, 9, 10),
        (2, 9, 10),
    )
    if not (
        diamond.morphism.coarse.vertices == diamond.morphism.fine.vertices == 1
        and len(diamond.morphism.coarse.edges) == 8
        and len(diamond.morphism.coarse.faces) == 8
        and len(diamond.morphism.fine.edges) == 11
        and len(diamond.morphism.fine.faces) == 10
        and diamond.morphism.coarse.faces == diamond_expected_faces
        and diamond.morphism.fine.faces == diamond_expected_fine_faces
        and diamond.morphism.vertex_map == (0,)
        and diamond.morphism.edge_map == (0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7)
        and diamond.morphism.face_map == (0, 1, 2, 3, 4, 5, 6, 6, 7, 7)
        and diamond.coarse_chart_supports == (frozenset((0, 1, 2, 3)),)
        and diamond.fine_chart_supports == (frozenset((0, 1, 2, 3, 4)),)
        and len(diamond_blocks) == 15
        and all(analysis == diamond_expected_h1 for _, analysis in diamond_blocks)
    ):
        raise AssertionError("Round9 DIAMOND exact fixture/H1 calibration mismatch")

    figure8_blocks = figure8.block_analyses()
    first_support = frozenset((0, 1))
    second_support = frozenset((2, 3))
    support_distribution = {
        "first_support_only": 0,
        "second_support_only": 0,
        "both_supports": 0,
    }
    for targets, analysis in figure8_blocks:
        meets_first = bool(targets & first_support)
        meets_second = bool(targets & second_support)
        dimension = int(meets_first) + int(meets_second)
        expected = H1Analysis(
            dimension,
            dimension,
            dimension,
            True,
            True,
            True,
        )
        if analysis != expected:
            raise AssertionError("Round9 FIGURE8 A-block H1 calibration mismatch")
        if meets_first and meets_second:
            support_distribution["both_supports"] += 1
        elif meets_first:
            support_distribution["first_support_only"] += 1
        elif meets_second:
            support_distribution["second_support_only"] += 1
    if not (
        figure8.morphism.coarse.vertices == figure8.morphism.fine.vertices == 2
        and len(figure8.morphism.coarse.edges) == 8
        and len(figure8.morphism.coarse.faces) == 12
        and len(figure8.morphism.fine.edges) == 12
        and len(figure8.morphism.fine.faces) == 12
        and figure8.morphism.vertex_map == (0, 1)
        and figure8.morphism.edge_map == (0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7)
        and figure8.morphism.face_map == tuple(range(12))
        and figure8.coarse_chart_supports
        == (frozenset((0, 1)), frozenset((2, 3)))
        and figure8.fine_chart_supports
        == (frozenset((0, 1, 2)), frozenset((3, 4)))
        and len(figure8_blocks) == 15
        and support_distribution
        == {
            "first_support_only": 3,
            "second_support_only": 3,
            "both_supports": 9,
        }
    ):
        raise AssertionError("Round9 FIGURE8 exact fixture/support calibration mismatch")

    expected_invariants = (
        {
            "n": 4,
            "m": 5,
            "degrees": [2, 2, 3, 3],
            "beta1": 2,
            "colors": "K^3S^2",
        },
        {
            "n": 5,
            "m": 6,
            "degrees": [2, 2, 2, 2, 4],
            "beta1": 2,
            "colors": "K^6",
        },
    )
    actual_invariants = (
        _relation_graph_invariant(
            4,
            kill_relations=R9_DIAMOND_KILL_RELATIONS,
            slot_relations=R9_DIAMOND_SLOT_RELATIONS,
        ),
        _relation_graph_invariant(
            5,
            kill_relations=R9_FIGURE8_KILL_RELATIONS,
        ),
    )
    for case, registered_colors in zip(expansion, colored_relations):
        registered_direct = tuple(
            sorted(registered_colors["KILL"] + registered_colors["SLOT"])
        )
        actual_direct = tuple(
            tuple(edge)
            for edge in case["certified_colored_adjacency"]["actual_uncolored"]
        )
        all_reductions = (
            case["candidate"]["whole"],
            *case["candidate"]["per_subset"],
        )
        if not (
            case["uniform"]
            and case["candidate"]["all"]
            and actual_direct == registered_direct
            and case["certified_colored_adjacency"]["unintended_edge_count"] == 0
            and all(
                not reduction["coarse_reduction"]["removed_free_pairs"]
                and not reduction["fine_reduction"]["removed_free_pairs"]
                for reduction in all_reductions
            )
        ):
            raise AssertionError("Round9 candidate/free-pair/adjacency calibration mismatch")
    if actual_invariants != expected_invariants:
        raise AssertionError("Round9 colored relation-graph invariant mismatch")

    graph_support_codes = _registered_relation_graph_support_codes_through_round9()
    graph_codes = tuple(
        item["relation_graph_canonical_code"]
        for item in graph_support_codes.values()
    )
    support_codes = tuple(
        item["relation_graph_support_code"]
        for item in graph_support_codes.values()
    )
    if not (
        len(graph_support_codes) == 8
        and len(set(graph_codes)) == 8
        and len(set(support_codes)) == 8
    ):
        raise AssertionError("Round9 graph/support canonicalization collision")

    new_full_ids = tuple(case["semantic_sha256"] for case in expansion)
    new_short_ids = tuple(case["id"] for case in expansion)
    all_full_ids = prior_full_ids + new_full_ids
    all_short_ids = prior_short_ids + new_short_ids
    full_collision_count = len(all_full_ids) - len(set(all_full_ids))
    short_collision_count = len(all_short_ids) - len(set(all_short_ids))
    if not (
        all(full.startswith(short) for full, short in zip(new_full_ids, new_short_ids))
        and not (set(new_full_ids) & set(prior_full_ids))
        and not (set(new_short_ids) & set(prior_short_ids))
        and len(set(new_full_ids)) == len(set(new_short_ids)) == 2
        and len(all_full_ids) == len(all_short_ids) == 1912
        and full_collision_count == short_collision_count == 0
    ):
        raise AssertionError("Round9 semantic payload strict-expansion mismatch")

    new_counterexamples = [
        case
        for case in expansion
        if case["sufficiency_break"] or case["necessity_break"]
    ]
    new_verdicts = sorted(
        {
            "CSTAR-not-sufficient"
            for case in new_counterexamples
            if case["sufficiency_break"]
        }
        | {
            "CSTAR-not-necessary"
            for case in new_counterexamples
            if case["necessity_break"]
        }
    )
    new_canonical_counterexamples = [
        case["semantic_sha256"] for case in new_counterexamples
    ]
    candidate_semantic_change = False
    additional_calibration_fixes: list[str] = []
    progress = bool(
        new_verdicts
        or new_canonical_counterexamples
        or candidate_semantic_change
        or additional_calibration_fixes
    )

    return {
        "round": "R2-round-9",
        "preregistered_issue_comment": 5230824089,
        "final_R0_calibration_comment": 5230818358,
        "valid": True,
        "baseline_payload_sha256": {
            "r0": r0_sha256,
            "r1": r1_sha256,
            "round1_through_round7": list(REGISTERED_ROUND_PAYLOAD_SHA256),
            "round8_diagnostic": round8_sha256,
        },
        "round8_diagnostic_baseline": {
            "valid": round8["valid"],
            "streak_after_round": round8["progress_audit"]["streak_after_round"],
            "diagnostic_zero_result": round8["diagnostic_zero_result"],
            "counted_in_stop_streak": False,
        },
        "candidate": {
            "semantic_id": CERTIFIED_SEMANTIC_ID,
            "semantic_sha256": CERTIFIED_SEMANTIC_SHA256,
            "spec": CERTIFIED_SPEC,
        },
        "population": {
            "prior_raw_cases_recomputed": len(prior_comparisons),
            "prior_full_semantic_payload_ids": len(set(prior_full_ids)),
            "prior_truncated_semantic_payload_ids": len(set(prior_short_ids)),
            "new_relation_grammar_cases": 2,
            "new_full_semantic_payload_ids": list(new_full_ids),
            "new_truncated_semantic_payload_ids": list(new_short_ids),
            "full_sha256_collision_count": full_collision_count,
            "truncated_20hex_collision_count": short_collision_count,
            "strict_superset": True,
            "total_raw_cases": 1912,
            "total_full_semantic_payload_ids": len(set(all_full_ids)),
            "total_truncated_semantic_payload_ids": len(set(all_short_ids)),
            "new_A_block_queries": sum(
                len(comparison.block_analyses()) for comparison in fixtures
            ),
            "all_cases_evaluated": True,
        },
        "canonical_relation_graph_support_codes": graph_support_codes,
        "relation_graph_invariants": {
            comparison.name: invariant
            for comparison, invariant in zip(fixtures, actual_invariants)
        },
        "figure8_A_block_distribution": support_distribution,
        "queries": {
            "prior_sufficiency_or_necessity_break_count": len(
                prior_counterexamples
            ),
            "prior_counterexamples": prior_counterexamples,
            "new_sufficiency_break_count": sum(
                case["sufficiency_break"] for case in expansion
            ),
            "new_necessity_break_count": sum(
                case["necessity_break"] for case in expansion
            ),
            "new_counterexample_count": len(new_counterexamples),
            "new_counterexample_ids": [
                case["semantic_sha256"] for case in new_counterexamples
            ],
        },
        "expansion_cases": expansion,
        "progress_audit": {
            "new_verdicts": new_verdicts,
            "new_canonical_nonisomorphic_counterexamples": (
                new_canonical_counterexamples
            ),
            "candidate_semantic_change": candidate_semantic_change,
            "additional_calibration_fixes": additional_calibration_fixes,
            "progress": progress,
            "streak_after_round": 0 if progress else 1,
        },
        "blocker_id": "PB-R2-NONFREE-GLOBAL-FACE-CHAIN",
        "same_blocker_evidence": {
            "valid_no_progress_1_of_2": not progress,
            "finite_mixed_or_split_support_cases_close": True,
            "remaining_gap": "No general proof for arbitrary retained nonfree face-chain graphs and arbitrary support distributions.",
        },
        "coverage_limit": "The fixed mixed-color diamond and one fixed split-support figure-eight, plus the recomputed prior 1910 cases; arbitrary graph size, certificate coloring, face multiplicity, and support distribution are not covered.",
    }


def _normalized_direct_edges(
    case: dict[str, object],
    coarse_edge: int,
) -> tuple[tuple[int, int], ...]:
    detail = case["candidate"]["whole"]["direct_lifttwin"][str(coarse_edge)]
    lifts = tuple(detail["lifts"])
    local_index = {lift: index for index, lift in enumerate(lifts)}
    return tuple(
        sorted(
            (local_index[left], local_index[right])
            for left, right in detail["direct_edges"]
        )
    )


def _target_relabelled_chart_records(
    chart_records: tuple[ChartCodeSpec, ...],
    *,
    coarse_permutation: tuple[int, ...],
    fine_permutation: tuple[int, ...],
) -> tuple[ChartCodeSpec, ...]:
    return tuple(
        ChartCodeSpec(
            frozenset(
                coarse_permutation[target]
                for target in record.coarse_support
            ),
            frozenset(
                fine_permutation[target]
                for target in record.fine_support
            ),
            record.relation_blocks,
            record.identity_loop_count,
        )
        for record in chart_records
    )


def round10_report() -> dict[str, object]:
    """Run the preregistered K2,3/K4+star multichart expansion."""

    if not (
        CERTIFIED_SEMANTIC_ID == "R2-CSTAR-CERTIFIED-v3"
        and CERTIFIED_SEMANTIC_SHA256
        == "cbb02677a055c69ecf0bb50a5de884fb55bbd4b4b59b75d256815eae69ec4daa"
    ):
        raise AssertionError("Round10 candidate semantic payload drifted")

    # The complete registered Round9 payload is the query-admission gate.  A
    # drift, a nonzero prior query, or loss of the first valid no-progress
    # observation stops this round before any Round10 fixture is evaluated.
    round9 = round9_report()
    round9_sha256 = _canonical_report_sha256(round9)
    _assert_round10_hash_baseline(
        round9_sha256=round9_sha256,
        round9=round9,
    )

    prior_comparisons = tuple(_all_comparisons_through_round9())
    prior_full_ids = tuple(
        _case_semantic_sha256(comparison) for comparison in prior_comparisons
    )
    prior_short_ids = tuple(identifier[:20] for identifier in prior_full_ids)
    if not (
        len(prior_comparisons) == 1912
        and len(set(prior_full_ids)) == 1912
        and len(set(prior_short_ids)) == 1912
    ):
        raise AssertionError("Round10 prior 1912-case semantic ID baseline drift")

    prior_counterexamples: list[dict[str, str]] = []
    for comparison in prior_comparisons:
        result = _case_result(
            comparison,
            "round0_through_round9",
            c5_mode="certified",
        )
        if result["sufficiency_break"] or result["necessity_break"]:
            prior_counterexamples.append(
                {
                    "id": result["id"],
                    "semantic_sha256": _case_semantic_sha256(comparison),
                    "query": (
                        "sufficiency_break"
                        if result["sufficiency_break"]
                        else "necessity_break"
                    ),
                }
            )
    if prior_counterexamples:
        raise AssertionError("Round10 prior 1912-case query baseline drift")

    k23, k4_star = round10_relation_fixtures()
    fixtures = (k23, k4_star)
    expansion: list[dict[str, object]] = []
    for comparison in fixtures:
        case = _case_result(
            comparison,
            "round10_multichart_relation_grammar",
            c5_mode="certified",
        )
        case["semantic_payload_json"] = _case_semantic_payload_json(comparison)
        case["semantic_sha256"] = _case_semantic_sha256(comparison)
        if sha256(case["semantic_payload_json"].encode("utf-8")).hexdigest() != case[
            "semantic_sha256"
        ]:
            raise AssertionError("Round10 full semantic JSON/SHA mismatch")
        case["all_block_h1"] = [
            {
                "coarse_targets_A": sorted(targets),
                "h1": asdict(analysis),
            }
            for targets, analysis in comparison.block_analyses()
        ]
        expansion.append(case)

    k23_expected_coarse_faces = (
        (1, 1, 1), (0, 0, 1),
        (2, 2, 2), (0, 0, 2),
        (3, 3, 3), (0, 0, 3),
        (0, 4, 5), (0, 6, 7), (0, 8, 9),
    )
    k23_expected_fine_faces = (
        (5, 5, 5), (0, 2, 5),
        (6, 6, 6), (0, 3, 6),
        (7, 7, 7), (1, 4, 7),
        (0, 8, 9), (4, 8, 9),
        (1, 10, 11), (2, 10, 11),
        (1, 12, 13), (3, 12, 13),
    )
    if not (
        _comparison_cell_counts(k23) == ((2, 11, 9), (2, 15, 12))
        and k23.morphism.coarse.faces == k23_expected_coarse_faces
        and k23.morphism.fine.faces == k23_expected_fine_faces
        and k23.morphism.vertex_map == (0, 1)
        and k23.morphism.edge_map
        == (0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10)
        and k23.morphism.face_map
        == (0, 1, 2, 3, 4, 5, 6, 6, 7, 7, 8, 8)
        and k23.coarse_target_count == 4
        and k23.fine_target_count == 5
        and k23.factor_pi == (0, 0, 1, 2, 3)
        and k23.coarse_chart_supports
        == (frozenset((0, 1, 2)), frozenset((2, 3)))
        and k23.fine_chart_supports
        == (frozenset((0, 1, 2, 3)), frozenset((3, 4)))
    ):
        raise AssertionError("Round10 K2,3 exact fixture calibration mismatch")

    k4_star_expected_coarse_faces = (
        (1, 1, 1), (0, 0, 1),
        (2, 2, 2), (0, 0, 2),
        (3, 3, 3), (0, 0, 3),
        (0, 4, 5), (0, 6, 7), (0, 8, 9),
        (11, 11, 11), (10, 10, 11),
        (10, 12, 13), (10, 14, 15),
    )
    k4_star_expected_fine_faces = (
        (4, 4, 4), (0, 1, 4),
        (5, 5, 5), (1, 2, 5),
        (6, 6, 6), (2, 0, 6),
        (0, 7, 8), (3, 7, 8),
        (1, 9, 10), (3, 9, 10),
        (2, 11, 12), (3, 11, 12),
        (17, 17, 17), (13, 14, 17),
        (13, 18, 19), (15, 18, 19),
        (13, 20, 21), (16, 20, 21),
    )
    if not (
        _comparison_cell_counts(k4_star) == ((3, 17, 13), (3, 23, 18))
        and k4_star.morphism.coarse.faces == k4_star_expected_coarse_faces
        and k4_star.morphism.fine.faces == k4_star_expected_fine_faces
        and k4_star.morphism.vertex_map == (0, 1, 2)
        and k4_star.morphism.edge_map
        == (
            0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9,
            10, 10, 10, 10, 11, 12, 13, 14, 15, 16,
        )
        and k4_star.morphism.face_map
        == (0, 1, 2, 3, 4, 5, 6, 6, 7, 7, 8, 8, 9, 10, 11, 11, 12, 12)
        and k4_star.coarse_target_count == 4
        and k4_star.fine_target_count == 5
        and k4_star.factor_pi == (0, 0, 1, 2, 3)
        and k4_star.coarse_chart_supports
        == (
            frozenset((0, 1)),
            frozenset((1, 2)),
            frozenset((2, 3)),
        )
        and k4_star.fine_chart_supports
        == (
            frozenset((0, 1, 2)),
            frozenset((2, 3)),
            frozenset((3, 4)),
        )
    ):
        raise AssertionError("Round10 K4+star exact fixture calibration mismatch")

    h1_expected_tables: dict[str, list[dict[str, object]]] = {}
    h1_dimension_histograms: dict[str, dict[str, int]] = {}
    k23_first_support = frozenset((0, 1, 2))
    k23_second_support = frozenset((2, 3))
    k4_star_expected_dimensions = {
        frozenset((0,)): 4,
        frozenset((1,)): 7,
        frozenset((2,)): 4,
        frozenset((3,)): 1,
        frozenset((0, 1)): 7,
        frozenset((0, 2)): 8,
        frozenset((0, 3)): 5,
        frozenset((1, 2)): 8,
        frozenset((1, 3)): 8,
        frozenset((2, 3)): 4,
        frozenset((0, 1, 2)): 8,
        frozenset((0, 1, 3)): 8,
        frozenset((0, 2, 3)): 8,
        frozenset((1, 2, 3)): 8,
        frozenset((0, 1, 2, 3)): 8,
    }
    expected_histograms = (
        {"1": 1, "4": 3, "5": 11},
        {"1": 1, "4": 3, "5": 1, "7": 2, "8": 8},
    )
    for fixture_index, comparison in enumerate(fixtures):
        table: list[dict[str, object]] = []
        histogram: dict[str, int] = {}
        blocks = comparison.block_analyses()
        if len(blocks) != 15:
            raise AssertionError("Round10 fixture did not enumerate all 15 A")
        for targets, analysis in blocks:
            expected_dimension = (
                4 * int(bool(targets & k23_first_support))
                + int(bool(targets & k23_second_support))
                if fixture_index == 0
                else k4_star_expected_dimensions[targets]
            )
            expected = H1Analysis(
                expected_dimension,
                expected_dimension,
                expected_dimension,
                True,
                True,
                True,
            )
            if analysis != expected:
                raise AssertionError("Round10 exact A-block H1 calibration mismatch")
            dimension_key = str(expected_dimension)
            histogram[dimension_key] = histogram.get(dimension_key, 0) + 1
            table.append(
                {
                    "coarse_targets_A": sorted(targets),
                    "expected_h1": asdict(expected),
                }
            )
        if histogram != expected_histograms[fixture_index]:
            raise AssertionError("Round10 A-block H1 histogram mismatch")
        h1_expected_tables[comparison.name] = table
        h1_dimension_histograms[comparison.name] = histogram

    registered_colored_adjacencies = (
        {
            "K23": {
                "coarse_edge": 0,
                "KILL": tuple(sorted(_checked_relations(5, R10_A_KILL_RELATIONS))),
                "SLOT": tuple(sorted(_checked_relations(5, R10_A_SLOT_RELATIONS))),
            },
        },
        {
            "K4": {
                "coarse_edge": 0,
                "KILL": tuple(sorted(_checked_relations(4, R10_B_K4_KILL_RELATIONS))),
                "SLOT": tuple(sorted(_checked_relations(4, R10_B_K4_SLOT_RELATIONS))),
            },
            "STAR": {
                "coarse_edge": 10,
                "KILL": tuple(sorted(_checked_relations(4, R10_B_STAR_KILL_RELATIONS))),
                "SLOT": tuple(sorted(_checked_relations(4, R10_B_STAR_SLOT_RELATIONS))),
            },
        },
    )
    for fixture_index, (comparison, case) in enumerate(zip(fixtures, expansion)):
        adjacency_report: dict[str, dict[str, object]] = {}
        for block_name, registered in registered_colored_adjacencies[
            fixture_index
        ].items():
            registered_edges = tuple(
                sorted(registered["KILL"] + registered["SLOT"])
            )
            actual_edges = _normalized_direct_edges(
                case,
                registered["coarse_edge"],
            )
            adjacency_report[block_name] = {
                "coarse_edge": registered["coarse_edge"],
                "KILL": [list(edge) for edge in registered["KILL"]],
                "SLOT": [list(edge) for edge in registered["SLOT"]],
                "actual_uncolored": [list(edge) for edge in actual_edges],
                "unintended_edge_count": len(
                    set(actual_edges) - set(registered_edges)
                ),
            }
            if actual_edges != registered_edges:
                raise AssertionError("Round10 exact colored adjacency mismatch")
        case["certified_colored_adjacency"] = adjacency_report

        whole_details = case["candidate"]["whole"]["direct_lifttwin"]
        nontrivial_edges = {
            registered["coarse_edge"]
            for registered in registered_colored_adjacencies[fixture_index].values()
        }
        auxiliary_details = tuple(
            detail
            for edge, detail in whole_details.items()
            if int(edge) not in nontrivial_edges
        )
        all_reductions = (
            case["candidate"]["whole"],
            *case["candidate"]["per_subset"],
        )
        if not (
            case["uniform"]
            and case["candidate"]["all"]
            and all(case["candidate"]["aggregate"].values())
            and len(case["candidate"]["per_subset"]) == 15
            and all(
                not reduction["coarse_reduction"]["removed_free_pairs"]
                and not reduction["fine_reduction"]["removed_free_pairs"]
                for reduction in all_reductions
            )
            and len(whole_details) == len(comparison.morphism.coarse.edges)
            and all(
                len(detail["lifts"]) == 1
                and detail["direct_edges"] == []
                and len(detail["components"]) == 1
                for detail in auxiliary_details
            )
        ):
            raise AssertionError("Round10 C*/free-pair/auxiliary-lift mismatch")

    expected_relation_invariants = {
        "R10-A-K23-MIXED-OVERLAP": {
            "K23": {
                "n": 5,
                "m": 6,
                "degrees": [2, 2, 2, 3, 3],
                "beta1": 2,
                "colors": "K^3S^3",
            },
        },
        "R10-B-K4-STAR-CHAIN-SUPPORT": {
            "K4": {
                "n": 4,
                "m": 6,
                "degrees": [3, 3, 3, 3],
                "beta1": 3,
                "colors": "K^3S^3",
            },
            "STAR": {
                "n": 4,
                "m": 3,
                "degrees": [1, 1, 1, 3],
                "beta1": 0,
                "colors": "K^1S^2",
            },
        },
    }
    actual_relation_invariants = {
        k23.name: {
            "K23": _relation_graph_invariant(
                5,
                kill_relations=R10_A_KILL_RELATIONS,
                slot_relations=R10_A_SLOT_RELATIONS,
            ),
        },
        k4_star.name: {
            "K4": _relation_graph_invariant(
                4,
                kill_relations=R10_B_K4_KILL_RELATIONS,
                slot_relations=R10_B_K4_SLOT_RELATIONS,
            ),
            "STAR": _relation_graph_invariant(
                4,
                kill_relations=R10_B_STAR_KILL_RELATIONS,
                slot_relations=R10_B_STAR_SLOT_RELATIONS,
            ),
        },
    }
    if actual_relation_invariants != expected_relation_invariants:
        raise AssertionError("Round10 colored relation invariant mismatch")

    graph_support_codes = _registered_colored_graph_support_codes_through_round10()
    graph_full_ids = tuple(item["sha256"] for item in graph_support_codes.values())
    graph_short_ids = tuple(identifier[:20] for identifier in graph_full_ids)
    graph_payloads = tuple(
        item["compact_json"] for item in graph_support_codes.values()
    )
    if not (
        len(graph_support_codes) == 10
        and len(set(graph_full_ids)) == 10
        and len(set(graph_short_ids)) == 10
        and len(set(graph_payloads)) == 10
    ):
        raise AssertionError("Round10 graph/support canonicalization collision")

    k23_charts = (
        ChartCodeSpec(
            frozenset((0, 1, 2)),
            frozenset((0, 1, 2, 3)),
            (
                RelationBlockCodeSpec(
                    5,
                    R10_A_KILL_RELATIONS,
                    R10_A_SLOT_RELATIONS,
                ),
            ),
        ),
        ChartCodeSpec(
            frozenset((2, 3)),
            frozenset((3, 4)),
            identity_loop_count=1,
        ),
    )
    k4_star_charts = (
        ChartCodeSpec(
            frozenset((0, 1)),
            frozenset((0, 1, 2)),
            (
                RelationBlockCodeSpec(
                    4,
                    R10_B_K4_KILL_RELATIONS,
                    R10_B_K4_SLOT_RELATIONS,
                ),
            ),
        ),
        ChartCodeSpec(
            frozenset((1, 2)),
            frozenset((2, 3)),
            (
                RelationBlockCodeSpec(
                    4,
                    R10_B_STAR_KILL_RELATIONS,
                    R10_B_STAR_SLOT_RELATIONS,
                ),
            ),
        ),
        ChartCodeSpec(
            frozenset((2, 3)),
            frozenset((3, 4)),
            identity_loop_count=1,
        ),
    )
    k23_base_code = graph_support_codes[k23.name]
    k4_star_base_code = graph_support_codes[k4_star.name]
    lift_relabel = (4, 2, 0, 3, 1)
    lift_relabelled_charts = (
        ChartCodeSpec(
            k23_charts[0].coarse_support,
            k23_charts[0].fine_support,
            (
                RelationBlockCodeSpec(
                    5,
                    tuple(
                        (lift_relabel[left], lift_relabel[right])
                        for left, right in R10_A_KILL_RELATIONS
                    ),
                    tuple(
                        (lift_relabel[left], lift_relabel[right])
                        for left, right in R10_A_SLOT_RELATIONS
                    ),
                ),
            ),
        ),
        k23_charts[1],
    )
    lift_relabelled_code = colored_graph_support_canonical_code(
        factor_pi=k23.factor_pi,
        chart_records=lift_relabelled_charts,
        coarse_cell_counts=(2, 11, 9),
        fine_cell_counts=(2, 15, 12),
    )
    chart_relabelled_code = colored_graph_support_canonical_code(
        factor_pi=k4_star.factor_pi,
        chart_records=tuple(reversed(k4_star_charts)),
        coarse_cell_counts=(3, 17, 13),
        fine_cell_counts=(3, 23, 18),
    )
    target_relabelled_code = colored_graph_support_canonical_code(
        factor_pi=k4_star.factor_pi,
        chart_records=_target_relabelled_chart_records(
            k4_star_charts,
            coarse_permutation=(0, 2, 1, 3),
            fine_permutation=(0, 1, 3, 2, 4),
        ),
        coarse_cell_counts=(3, 17, 13),
        fine_cell_counts=(3, 23, 18),
    )
    support_drift_code = colored_graph_support_canonical_code(
        factor_pi=k23.factor_pi,
        chart_records=(
            ChartCodeSpec(
                frozenset((0, 1)),
                frozenset((0, 1, 2)),
                k23_charts[0].relation_blocks,
            ),
            k23_charts[1],
        ),
        coarse_cell_counts=(2, 11, 9),
        fine_cell_counts=(2, 15, 12),
    )
    if not (
        lift_relabelled_code == k23_base_code
        and chart_relabelled_code == k4_star_base_code
        and target_relabelled_code == k4_star_base_code
        and support_drift_code != k23_base_code
        and len(k4_star_charts) == 3
        and sum(bool(chart.relation_blocks) for chart in k4_star_charts) == 2
    ):
        raise AssertionError("Round10 graph/support relabel or drift calibration mismatch")

    new_full_ids = tuple(case["semantic_sha256"] for case in expansion)
    new_short_ids = tuple(case["id"] for case in expansion)
    all_full_ids = prior_full_ids + new_full_ids
    all_short_ids = prior_short_ids + new_short_ids
    full_collision_count = len(all_full_ids) - len(set(all_full_ids))
    short_collision_count = len(all_short_ids) - len(set(all_short_ids))
    if not (
        all(full.startswith(short) for full, short in zip(new_full_ids, new_short_ids))
        and not (set(new_full_ids) & set(prior_full_ids))
        and not (set(new_short_ids) & set(prior_short_ids))
        and len(set(new_full_ids)) == len(set(new_short_ids)) == 2
        and len(all_full_ids) == len(all_short_ids) == 1914
        and full_collision_count == short_collision_count == 0
    ):
        raise AssertionError("Round10 semantic payload strict-expansion mismatch")

    new_counterexamples = [
        case
        for case in expansion
        if case["sufficiency_break"] or case["necessity_break"]
    ]
    new_verdicts = sorted(
        {
            "CSTAR-not-sufficient"
            for case in new_counterexamples
            if case["sufficiency_break"]
        }
        | {
            "CSTAR-not-necessary"
            for case in new_counterexamples
            if case["necessity_break"]
        }
    )
    new_canonical_counterexamples = [
        case["semantic_sha256"] for case in new_counterexamples
    ]
    candidate_semantic_change = False
    additional_calibration_fixes: list[str] = []
    progress = bool(
        new_verdicts
        or new_canonical_counterexamples
        or candidate_semantic_change
        or additional_calibration_fixes
    )
    stop_condition_c = not progress

    return {
        "round": "R2-round-10",
        "preregistered_issue_comment": 5230881464,
        "final_R0_calibration_comment": 5230818358,
        "round9_result_comment": ROUND9_RESULT_ISSUE_COMMENT,
        "valid": True,
        "baseline_payload_sha256": {
            "r0": FINAL_R0_SEMANTIC_SHA256,
            "r1": FINAL_R1_SEMANTIC_SHA256,
            "round1_through_round7": list(REGISTERED_ROUND_PAYLOAD_SHA256),
            "round8_diagnostic": ROUND8_DIAGNOSTIC_PAYLOAD_SHA256,
            "round9_valid": round9_sha256,
        },
        "round8_diagnostic_baseline": {
            "valid": False,
            "counted_in_stop_streak": False,
        },
        "round9_valid_baseline": {
            "valid": round9["valid"],
            "streak_after_round": round9["progress_audit"]["streak_after_round"],
            "valid_no_progress_1_of_2": round9["same_blocker_evidence"][
                "valid_no_progress_1_of_2"
            ],
        },
        "candidate": {
            "semantic_id": CERTIFIED_SEMANTIC_ID,
            "semantic_sha256": CERTIFIED_SEMANTIC_SHA256,
            "spec": CERTIFIED_SPEC,
        },
        "population": {
            "prior_raw_cases_recomputed": len(prior_comparisons),
            "prior_full_semantic_payload_ids": len(set(prior_full_ids)),
            "prior_truncated_semantic_payload_ids": len(set(prior_short_ids)),
            "new_multichart_relation_cases": 2,
            "new_full_semantic_payload_ids": list(new_full_ids),
            "new_truncated_semantic_payload_ids": list(new_short_ids),
            "full_sha256_collision_count": full_collision_count,
            "truncated_20hex_collision_count": short_collision_count,
            "strict_superset": True,
            "total_raw_cases": 1914,
            "total_full_semantic_payload_ids": len(set(all_full_ids)),
            "total_truncated_semantic_payload_ids": len(set(all_short_ids)),
            "new_A_block_queries": sum(
                len(comparison.block_analyses()) for comparison in fixtures
            ),
            "all_cases_evaluated": True,
        },
        "canonical_colored_graph_support_codes": {
            name: {
                **code,
                "id20": code["sha256"][:20],
            }
            for name, code in graph_support_codes.items()
        },
        "canonical_code_audit": {
            "prior_registered_code_count": 8,
            "new_registered_code_count": 2,
            "registered_code_count": len(graph_support_codes),
            "full_sha256_collision_count": len(graph_full_ids) - len(set(graph_full_ids)),
            "truncated_20hex_collision_count": len(graph_short_ids) - len(set(graph_short_ids)),
            "compact_json_collision_count": len(graph_payloads) - len(set(graph_payloads)),
            "lift_relabel_invariant": lift_relabelled_code == k23_base_code,
            "chart_relabel_invariant": chart_relabelled_code == k4_star_base_code,
            "target_relabel_invariant": target_relabelled_code == k4_star_base_code,
            "support_drift_detected": support_drift_code != k23_base_code,
            "strict_new": True,
        },
        "relation_graph_invariants": actual_relation_invariants,
        "A_block_expected_h1": h1_expected_tables,
        "A_block_dimension_histograms": h1_dimension_histograms,
        "queries": {
            "prior_sufficiency_or_necessity_break_count": len(
                prior_counterexamples
            ),
            "prior_counterexamples": prior_counterexamples,
            "new_sufficiency_break_count": sum(
                case["sufficiency_break"] for case in expansion
            ),
            "new_necessity_break_count": sum(
                case["necessity_break"] for case in expansion
            ),
            "new_counterexample_count": len(new_counterexamples),
            "new_counterexample_ids": [
                case["semantic_sha256"] for case in new_counterexamples
            ],
        },
        "expansion_cases": expansion,
        "progress_audit": {
            "new_verdicts": new_verdicts,
            "new_canonical_nonisomorphic_counterexamples": (
                new_canonical_counterexamples
            ),
            "candidate_semantic_change": candidate_semantic_change,
            "additional_calibration_fixes": additional_calibration_fixes,
            "progress": progress,
            "streak_after_round": 0 if progress else 2,
        },
        "blocker_id": "PB-R2-NONFREE-GLOBAL-FACE-CHAIN",
        "same_blocker_evidence": {
            "valid_no_progress_2_of_2": not progress,
            "finite_multichart_relation_cases_close": True,
            "remaining_gap": "No general proof for arbitrary retained nonfree face-chain graphs and arbitrary compatible multichart support distributions.",
        },
        "stop_audit": {
            "stop_condition_A_completion": False,
            "stop_condition_B_finite_exhaustion": False,
            "stop_condition_C_two_valid_same_blocker_no_progress": stop_condition_c,
            "terminal_reason": (
                "Stop-C: two consecutive valid same-blocker no-progress rounds"
                if stop_condition_c
                else None
            ),
        },
        "coverage_limit": "The exact K2,3 mixed overlap-support fixture and exact K4-plus-star three-chart chain-support fixture, all 15 nonempty A for each, plus the recomputed prior 1912 cases. Cross-chart nonloop edges or faces, arbitrary graph size and coloring, arbitrary face multiplicity, and arbitrary compatible support distributions remain outside this finite coverage.",
    }


if __name__ == "__main__":
    print(json.dumps(round1_report(), ensure_ascii=False, indent=2, sort_keys=True))
