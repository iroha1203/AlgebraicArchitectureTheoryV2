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
from itertools import product
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


def _case_id(comparison: UniformComparison) -> str:
    semantic_summary = dict(comparison.summary())
    semantic_summary.pop("name")
    payload = json.dumps(semantic_summary, sort_keys=True, separators=(",", ":"))
    return sha256(payload.encode("utf-8")).hexdigest()[:20]


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


if __name__ == "__main__":
    print(json.dumps(round1_report(), ensure_ascii=False, indent=2, sort_keys=True))
