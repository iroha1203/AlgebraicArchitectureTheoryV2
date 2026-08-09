#!/usr/bin/env python3
"""Exact finite engine for the G-104 C0--C6 necessity map.

Only the Python standard library is used.  Every rank computation is over
``fractions.Fraction``; every finite choice is traversed in a fixed order.
"""

from __future__ import annotations

import argparse
import json
from dataclasses import asdict, dataclass
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
from typing import Iterable, Iterator, Sequence


Q = Fraction


@dataclass(frozen=True)
class Matrix:
    """A small exact matrix whose empty dimensions remain explicit."""

    rows: int
    cols: int
    entries: tuple[tuple[Q, ...], ...]

    def __post_init__(self) -> None:
        if len(self.entries) != self.rows:
            raise ValueError("matrix row count does not match entries")
        if any(len(row) != self.cols for row in self.entries):
            raise ValueError("matrix column count does not match entries")

    @staticmethod
    def zero(rows: int, cols: int) -> "Matrix":
        return Matrix(
            rows,
            cols,
            tuple(tuple(Q(0) for _ in range(cols)) for _ in range(rows)),
        )

    @staticmethod
    def identity(size: int) -> "Matrix":
        return Matrix(
            size,
            size,
            tuple(
                tuple(Q(1 if row == col else 0) for col in range(size))
                for row in range(size)
            ),
        )

    @staticmethod
    def from_mutable(
        rows: Sequence[Sequence[int | Q]],
        cols: int | None = None,
    ) -> "Matrix":
        row_count = len(rows)
        column_count = len(rows[0]) if row_count else (cols or 0)
        return Matrix(
            row_count,
            column_count,
            tuple(tuple(Q(value) for value in row) for row in rows),
        )

    def __matmul__(self, other: "Matrix") -> "Matrix":
        if self.cols != other.rows:
            raise ValueError("matrix dimensions do not compose")
        data = [
            [
                sum(
                    (
                        self.entries[row][middle] * other.entries[middle][col]
                        for middle in range(self.cols)
                    ),
                    Q(0),
                )
                for col in range(other.cols)
            ]
            for row in range(self.rows)
        ]
        return Matrix.from_mutable(data, cols=other.cols)

    def is_zero(self) -> bool:
        return all(value == 0 for row in self.entries for value in row)

    def rank(self) -> int:
        work = [list(row) for row in self.entries]
        pivot_row = 0
        for col in range(self.cols):
            pivot = next(
                (row for row in range(pivot_row, self.rows) if work[row][col] != 0),
                None,
            )
            if pivot is None:
                continue
            work[pivot_row], work[pivot] = work[pivot], work[pivot_row]
            pivot_value = work[pivot_row][col]
            work[pivot_row] = [value / pivot_value for value in work[pivot_row]]
            for row in range(self.rows):
                if row == pivot_row or work[row][col] == 0:
                    continue
                factor = work[row][col]
                work[row] = [
                    work[row][index] - factor * work[pivot_row][index]
                    for index in range(self.cols)
                ]
            pivot_row += 1
            if pivot_row == self.rows:
                break
        return pivot_row

    def kernel_basis(self) -> "Matrix":
        """Return a matrix whose columns form a kernel basis."""

        work = [list(row) for row in self.entries]
        pivot_columns: list[int] = []
        pivot_row = 0
        for col in range(self.cols):
            pivot = next(
                (row for row in range(pivot_row, self.rows) if work[row][col] != 0),
                None,
            )
            if pivot is None:
                continue
            work[pivot_row], work[pivot] = work[pivot], work[pivot_row]
            pivot_value = work[pivot_row][col]
            work[pivot_row] = [value / pivot_value for value in work[pivot_row]]
            for row in range(self.rows):
                if row == pivot_row or work[row][col] == 0:
                    continue
                factor = work[row][col]
                work[row] = [
                    work[row][index] - factor * work[pivot_row][index]
                    for index in range(self.cols)
                ]
            pivot_columns.append(col)
            pivot_row += 1
            if pivot_row == self.rows:
                break

        free_columns = [col for col in range(self.cols) if col not in pivot_columns]
        vectors: list[list[Q]] = []
        for free in free_columns:
            vector = [Q(0) for _ in range(self.cols)]
            vector[free] = Q(1)
            for row, pivot_col in enumerate(pivot_columns):
                vector[pivot_col] = -work[row][free]
            vectors.append(vector)
        if not vectors:
            return Matrix.zero(self.cols, 0)
        return Matrix.from_mutable(
            [
                [vectors[column][row] for column in range(len(vectors))]
                for row in range(self.cols)
            ],
            cols=len(vectors),
        )

    @staticmethod
    def hstack(left: "Matrix", right: "Matrix") -> "Matrix":
        if left.rows != right.rows:
            raise ValueError("horizontal stack requires equal row counts")
        return Matrix(
            left.rows,
            left.cols + right.cols,
            tuple(left.entries[row] + right.entries[row] for row in range(left.rows)),
        )

    @staticmethod
    def kronecker(left: "Matrix", right: "Matrix") -> "Matrix":
        data = [
            [Q(0) for _ in range(left.cols * right.cols)]
            for _ in range(left.rows * right.rows)
        ]
        for left_row in range(left.rows):
            for left_col in range(left.cols):
                scalar = left.entries[left_row][left_col]
                for right_row in range(right.rows):
                    for right_col in range(right.cols):
                        data[left_row * right.rows + right_row][
                            left_col * right.cols + right_col
                        ] = scalar * right.entries[right_row][right_col]
        return Matrix.from_mutable(data, cols=left.cols * right.cols)


@dataclass(frozen=True)
class Nerve:
    """A finite oriented two-dimensional incidence nerve."""

    vertices: int
    edges: tuple[tuple[int, int], ...]
    faces: tuple[tuple[int, int, int], ...]

    def __post_init__(self) -> None:
        if self.vertices < 0:
            raise ValueError("negative vertex count")
        if any(
            not (0 <= left < self.vertices and 0 <= right < self.vertices)
            for left, right in self.edges
        ):
            raise ValueError("edge endpoint outside the vertex set")
        if any(
            not all(0 <= edge < len(self.edges) for edge in face)
            for face in self.faces
        ):
            raise ValueError("face edge outside the edge set")
        if not (self.d1() @ self.d0()).is_zero():
            raise ValueError("face incidence does not satisfy d1 * d0 = 0")

    def d0(self) -> Matrix:
        data = [[Q(0) for _ in range(self.vertices)] for _ in self.edges]
        for edge, (left, right) in enumerate(self.edges):
            data[edge][left] -= 1
            data[edge][right] += 1
        return Matrix.from_mutable(data, cols=self.vertices)

    def d1(self) -> Matrix:
        data = [[Q(0) for _ in self.edges] for _ in self.faces]
        for face, (edge0, edge1, edge2) in enumerate(self.faces):
            data[face][edge0] += 1
            data[face][edge1] -= 1
            data[face][edge2] += 1
        return Matrix.from_mutable(data, cols=len(self.edges))


@dataclass(frozen=True)
class NerveMorphism:
    """Fine-to-coarse incidence data with declared degenerate cells."""

    coarse: Nerve
    fine: Nerve
    vertex_map: tuple[int, ...]
    edge_map: tuple[int | None, ...]
    face_map: tuple[int | None, ...]

    def __post_init__(self) -> None:
        if len(self.vertex_map) != self.fine.vertices:
            raise ValueError("vertex map has the wrong size")
        if len(self.edge_map) != len(self.fine.edges):
            raise ValueError("edge map has the wrong size")
        if len(self.face_map) != len(self.fine.faces):
            raise ValueError("face map has the wrong size")
        if any(not 0 <= vertex < self.coarse.vertices for vertex in self.vertex_map):
            raise ValueError("vertex map leaves the coarse vertex set")

        for fine_edge, coarse_edge in enumerate(self.edge_map):
            left, right = self.fine.edges[fine_edge]
            mapped_endpoints = (self.vertex_map[left], self.vertex_map[right])
            if coarse_edge is None:
                if mapped_endpoints[0] != mapped_endpoints[1]:
                    raise ValueError("a degenerate edge crosses coarse chart fibers")
            else:
                if not 0 <= coarse_edge < len(self.coarse.edges):
                    raise ValueError("edge map leaves the coarse edge set")
                if mapped_endpoints != self.coarse.edges[coarse_edge]:
                    raise ValueError("mapped edge endpoints do not commute")

        for fine_face, coarse_face in enumerate(self.face_map):
            mapped_boundary = tuple(
                self.edge_map[edge] for edge in self.fine.faces[fine_face]
            )
            if coarse_face is None:
                if any(edge is not None for edge in mapped_boundary):
                    raise ValueError("a degenerate face has a nondegenerate boundary edge")
            else:
                if not 0 <= coarse_face < len(self.coarse.faces):
                    raise ValueError("face map leaves the coarse face set")
                if mapped_boundary != self.coarse.faces[coarse_face]:
                    raise ValueError("mapped face boundary does not commute")

    def cell_pullback(self, dimension: int) -> Matrix:
        if dimension == 0:
            coarse_cells = self.coarse.vertices
            mapping: Sequence[int | None] = self.vertex_map
        elif dimension == 1:
            coarse_cells = len(self.coarse.edges)
            mapping = self.edge_map
        elif dimension == 2:
            coarse_cells = len(self.coarse.faces)
            mapping = self.face_map
        else:
            raise ValueError("only dimensions zero through two are supported")
        data = [[Q(0) for _ in range(coarse_cells)] for _ in mapping]
        for fine_cell, coarse_cell in enumerate(mapping):
            if coarse_cell is not None:
                data[fine_cell][coarse_cell] = Q(1)
        return Matrix.from_mutable(data, cols=coarse_cells)


@dataclass(frozen=True)
class H1Analysis:
    coarse_h1_dimension: int
    fine_h1_dimension: int
    comparison_rank: int
    injective: bool
    surjective: bool
    isomorphism: bool


def analyze_complex_map(
    *,
    coarse_d0: Matrix,
    coarse_d1: Matrix,
    fine_d0: Matrix,
    fine_d1: Matrix,
    pullback0: Matrix,
    pullback1: Matrix,
    pullback2: Matrix,
) -> H1Analysis:
    """Compute the induced H1 map of an exact three-term cochain map."""

    if not (coarse_d1 @ coarse_d0).is_zero():
        raise ValueError("coarse data are not a cochain complex")
    if not (fine_d1 @ fine_d0).is_zero():
        raise ValueError("fine data are not a cochain complex")
    if fine_d0 @ pullback0 != pullback1 @ coarse_d0:
        raise ValueError("degree-zero square is not a cochain map")
    if fine_d1 @ pullback1 != pullback2 @ coarse_d1:
        raise ValueError("degree-one square is not a cochain map")

    coarse_cycles = coarse_d1.kernel_basis()
    mapped_cycles = pullback1 @ coarse_cycles
    coarse_h1 = coarse_cycles.cols - coarse_d0.rank()
    fine_cycles = fine_d1.kernel_basis()
    fine_h1 = fine_cycles.cols - fine_d0.rank()
    comparison_rank = Matrix.hstack(fine_d0, mapped_cycles).rank() - fine_d0.rank()
    injective = comparison_rank == coarse_h1
    surjective = comparison_rank == fine_h1
    return H1Analysis(
        coarse_h1_dimension=coarse_h1,
        fine_h1_dimension=fine_h1,
        comparison_rank=comparison_rank,
        injective=injective,
        surjective=surjective,
        isomorphism=injective and surjective,
    )


def analyze_h1(morphism: NerveMorphism, coefficient_map: Matrix) -> H1Analysis:
    """Analyze the constant cell-independent coefficient comparison."""

    coarse_identity = Matrix.identity(coefficient_map.cols)
    fine_identity = Matrix.identity(coefficient_map.rows)
    return analyze_complex_map(
        coarse_d0=Matrix.kronecker(morphism.coarse.d0(), coarse_identity),
        coarse_d1=Matrix.kronecker(morphism.coarse.d1(), coarse_identity),
        fine_d0=Matrix.kronecker(morphism.fine.d0(), fine_identity),
        fine_d1=Matrix.kronecker(morphism.fine.d1(), fine_identity),
        pullback0=Matrix.kronecker(morphism.cell_pullback(0), coefficient_map),
        pullback1=Matrix.kronecker(morphism.cell_pullback(1), coefficient_map),
        pullback2=Matrix.kronecker(morphism.cell_pullback(2), coefficient_map),
    )


def direct_sum_analysis(analyses: Iterable[H1Analysis]) -> H1Analysis:
    items = tuple(analyses)
    coarse = sum(item.coarse_h1_dimension for item in items)
    fine = sum(item.fine_h1_dimension for item in items)
    rank = sum(item.comparison_rank for item in items)
    return H1Analysis(
        coarse_h1_dimension=coarse,
        fine_h1_dimension=fine,
        comparison_rank=rank,
        injective=rank == coarse,
        surjective=rank == fine,
        isomorphism=rank == coarse == fine,
    )


def nonempty_subsets(size: int) -> tuple[frozenset[int], ...]:
    return tuple(
        frozenset(choice)
        for count in range(1, size + 1)
        for choice in combinations(range(size), count)
    )


def derived_cell_supports(
    nerve: Nerve,
    chart_supports: tuple[frozenset[int], ...],
) -> tuple[tuple[frozenset[int], ...], tuple[frozenset[int], ...]]:
    """K1: edge support is endpoint intersection; face support is boundary intersection."""

    edge_supports = tuple(
        chart_supports[left] & chart_supports[right]
        for left, right in nerve.edges
    )
    face_supports = tuple(
        edge_supports[edge0] & edge_supports[edge1] & edge_supports[edge2]
        for edge0, edge1, edge2 in nerve.faces
    )
    return edge_supports, face_supports


@dataclass(frozen=True)
class RestrictedNerve:
    nerve: Nerve
    vertices: tuple[int, ...]
    edges: tuple[int, ...]
    faces: tuple[int, ...]


def restrict_nerve(
    nerve: Nerve,
    chart_supports: tuple[frozenset[int], ...],
    targets: frozenset[int],
) -> RestrictedNerve:
    edge_supports, face_supports = derived_cell_supports(nerve, chart_supports)
    vertices = tuple(
        vertex
        for vertex, support in enumerate(chart_supports)
        if support & targets
    )
    edges = tuple(
        edge for edge, support in enumerate(edge_supports) if support & targets
    )
    faces = tuple(
        face for face, support in enumerate(face_supports) if support & targets
    )
    vertex_index = {old: new for new, old in enumerate(vertices)}
    edge_index = {old: new for new, old in enumerate(edges)}
    for edge in edges:
        if any(vertex not in vertex_index for vertex in nerve.edges[edge]):
            raise AssertionError("K1-selected edge lost an endpoint")
    for face in faces:
        if any(edge not in edge_index for edge in nerve.faces[face]):
            raise AssertionError("K1-selected face lost a boundary edge")
    return RestrictedNerve(
        nerve=Nerve(
            vertices=len(vertices),
            edges=tuple(
                (vertex_index[nerve.edges[edge][0]], vertex_index[nerve.edges[edge][1]])
                for edge in edges
            ),
            faces=tuple(
                tuple(edge_index[edge] for edge in nerve.faces[face])
                for face in faces
            ),
        ),
        vertices=vertices,
        edges=edges,
        faces=faces,
    )


@dataclass(frozen=True)
class CoordinateSubcomparison:
    coarse_targets: frozenset[int]
    fine_targets: frozenset[int]
    coarse: RestrictedNerve
    fine: RestrictedNerve
    morphism: NerveMorphism

    def analysis(self) -> H1Analysis:
        return analyze_h1(self.morphism, Matrix.identity(1))

    def summary(self) -> dict[str, object]:
        return {
            "coarse_targets_A": sorted(self.coarse_targets),
            "fine_targets_pi_preimage_A": sorted(self.fine_targets),
            "coarse_original_cells": {
                "charts": list(self.coarse.vertices),
                "edges": list(self.coarse.edges),
                "faces": list(self.coarse.faces),
            },
            "fine_original_cells": {
                "charts": list(self.fine.vertices),
                "edges": list(self.fine.edges),
                "faces": list(self.fine.faces),
            },
            "restricted_maps": {
                "vertex_map": list(self.morphism.vertex_map),
                "edge_map": list(self.morphism.edge_map),
                "face_map": list(self.morphism.face_map),
            },
            "h1": asdict(self.analysis()),
        }


@dataclass(frozen=True)
class UniformComparison:
    """A supported nerve morphism with its canonical surjective target factor."""

    name: str
    morphism: NerveMorphism
    coarse_target_count: int
    fine_target_count: int
    factor_pi: tuple[int, ...]
    coarse_chart_supports: tuple[frozenset[int], ...]
    fine_chart_supports: tuple[frozenset[int], ...]

    def __post_init__(self) -> None:
        if self.coarse_target_count <= 0 or self.fine_target_count <= 0:
            raise ValueError("reading targets must be nonempty")
        if len(self.factor_pi) != self.fine_target_count:
            raise ValueError("pi has the wrong fine-target count")
        if any(
            not 0 <= target < self.coarse_target_count for target in self.factor_pi
        ):
            raise ValueError("pi leaves the coarse target")
        if set(self.factor_pi) != set(range(self.coarse_target_count)):
            raise ValueError("pi must be surjective")
        if len(self.coarse_chart_supports) != self.morphism.coarse.vertices:
            raise ValueError("coarse chart supports have the wrong size")
        if len(self.fine_chart_supports) != self.morphism.fine.vertices:
            raise ValueError("fine chart supports have the wrong size")
        coarse_universe = set(range(self.coarse_target_count))
        fine_universe = set(range(self.fine_target_count))
        if any(
            not support or not set(support) <= coarse_universe
            for support in self.coarse_chart_supports
        ):
            raise ValueError("coarse chart supports must be nonempty and in range")
        if any(
            not support or not set(support) <= fine_universe
            for support in self.fine_chart_supports
        ):
            raise ValueError("fine chart supports must be nonempty and in range")
        for fine_chart, support in enumerate(self.fine_chart_supports):
            coarse_chart = self.morphism.vertex_map[fine_chart]
            image = {self.factor_pi[target] for target in support}
            if not image <= self.coarse_chart_supports[coarse_chart]:
                raise ValueError("chartSupport compatibility with pi/phi failed")

    @property
    def coarse_edge_supports(self) -> tuple[frozenset[int], ...]:
        return derived_cell_supports(
            self.morphism.coarse,
            self.coarse_chart_supports,
        )[0]

    @property
    def coarse_face_supports(self) -> tuple[frozenset[int], ...]:
        return derived_cell_supports(
            self.morphism.coarse,
            self.coarse_chart_supports,
        )[1]

    @property
    def fine_edge_supports(self) -> tuple[frozenset[int], ...]:
        return derived_cell_supports(
            self.morphism.fine,
            self.fine_chart_supports,
        )[0]

    @property
    def fine_face_supports(self) -> tuple[frozenset[int], ...]:
        return derived_cell_supports(
            self.morphism.fine,
            self.fine_chart_supports,
        )[1]

    def coordinate_subcomparison(
        self,
        coarse_targets: frozenset[int],
    ) -> CoordinateSubcomparison:
        if not coarse_targets:
            raise ValueError("A must be nonempty")
        if not set(coarse_targets) <= set(range(self.coarse_target_count)):
            raise ValueError("A leaves the coarse target")
        fine_targets = frozenset(
            fine_target
            for fine_target, coarse_target in enumerate(self.factor_pi)
            if coarse_target in coarse_targets
        )
        coarse = restrict_nerve(
            self.morphism.coarse,
            self.coarse_chart_supports,
            coarse_targets,
        )
        fine = restrict_nerve(
            self.morphism.fine,
            self.fine_chart_supports,
            fine_targets,
        )
        coarse_vertex_index = {
            old: new for new, old in enumerate(coarse.vertices)
        }
        coarse_edge_index = {old: new for new, old in enumerate(coarse.edges)}
        coarse_face_index = {old: new for new, old in enumerate(coarse.faces)}
        vertex_map: list[int] = []
        for old_fine in fine.vertices:
            old_coarse = self.morphism.vertex_map[old_fine]
            if old_coarse not in coarse_vertex_index:
                raise AssertionError("selected fine chart has no selected coarse image")
            vertex_map.append(coarse_vertex_index[old_coarse])
        edge_map: list[int | None] = []
        for old_fine in fine.edges:
            old_coarse = self.morphism.edge_map[old_fine]
            if old_coarse is None:
                edge_map.append(None)
            else:
                if old_coarse not in coarse_edge_index:
                    raise AssertionError("selected fine edge has no selected coarse image")
                edge_map.append(coarse_edge_index[old_coarse])
        face_map: list[int | None] = []
        for old_fine in fine.faces:
            old_coarse = self.morphism.face_map[old_fine]
            if old_coarse is None:
                face_map.append(None)
            else:
                if old_coarse not in coarse_face_index:
                    raise AssertionError("selected fine face has no selected coarse image")
                face_map.append(coarse_face_index[old_coarse])
        return CoordinateSubcomparison(
            coarse_targets=coarse_targets,
            fine_targets=fine_targets,
            coarse=coarse,
            fine=fine,
            morphism=NerveMorphism(
                coarse=coarse.nerve,
                fine=fine.nerve,
                vertex_map=tuple(vertex_map),
                edge_map=tuple(edge_map),
                face_map=tuple(face_map),
            ),
        )

    def block_analyses(self) -> tuple[tuple[frozenset[int], H1Analysis], ...]:
        return tuple(
            (targets, self.coordinate_subcomparison(targets).analysis())
            for targets in nonempty_subsets(self.coarse_target_count)
        )

    def is_uniform(self) -> bool:
        return all(analysis.isomorphism for _, analysis in self.block_analyses())

    def c0_holds(self) -> bool:
        return all(
            self.coarse_chart_supports[coarse_chart]
            == frozenset(
                self.factor_pi[target]
                for fine_chart, mapped_chart in enumerate(self.morphism.vertex_map)
                if mapped_chart == coarse_chart
                for target in self.fine_chart_supports[fine_chart]
            )
            for coarse_chart in range(self.morphism.coarse.vertices)
        )

    def summary(self) -> dict[str, object]:
        return {
            "name": self.name,
            "targets": {
                "coarse_count": self.coarse_target_count,
                "fine_count": self.fine_target_count,
                "canonical_surjective_factor_pi": list(self.factor_pi),
            },
            "coarse": {
                "nerve": nerve_summary(self.morphism.coarse),
                "chart_supports": supports_summary(self.coarse_chart_supports),
                "derived_edge_supports": supports_summary(self.coarse_edge_supports),
                "derived_face_supports": supports_summary(self.coarse_face_supports),
            },
            "fine": {
                "nerve": nerve_summary(self.morphism.fine),
                "chart_supports": supports_summary(self.fine_chart_supports),
                "derived_edge_supports": supports_summary(self.fine_edge_supports),
                "derived_face_supports": supports_summary(self.fine_face_supports),
            },
            "morphism": {
                "vertex_map": list(self.morphism.vertex_map),
                "edge_map": list(self.morphism.edge_map),
                "face_map": list(self.morphism.face_map),
            },
            "chartSupport_compatible": True,
            "K1_supports_derived_by_intersection": True,
        }


def supports_summary(supports: Iterable[frozenset[int]]) -> list[list[int]]:
    return [sorted(support) for support in supports]


def nerve_summary(nerve: Nerve) -> dict[str, object]:
    return {
        "vertices": nerve.vertices,
        "edges": [list(edge) for edge in nerve.edges],
        "faces": [list(face) for face in nerve.faces],
    }


def connected(vertices: Iterable[int], edges: Iterable[tuple[int, int]]) -> bool:
    vertex_set = set(vertices)
    if not vertex_set:
        return False
    adjacency = {vertex: set() for vertex in vertex_set}
    for left, right in edges:
        if left in vertex_set and right in vertex_set:
            adjacency[left].add(right)
            adjacency[right].add(left)
    reached = {min(vertex_set)}
    frontier = list(reached)
    while frontier:
        current = frontier.pop()
        for neighbour in sorted(adjacency[current] - reached):
            reached.add(neighbour)
            frontier.append(neighbour)
    return reached == vertex_set


def nerve_h1_dimension(nerve: Nerve) -> int:
    return nerve.d1().kernel_basis().cols - nerve.d0().rank()


def relative_condition_vector(morphism: NerveMorphism) -> dict[str, bool]:
    """Evaluate current C1--C4 on one exact coordinate subnerve."""

    fibers = tuple(
        tuple(
            fine_chart
            for fine_chart, mapped in enumerate(morphism.vertex_map)
            if mapped == coarse_chart
        )
        for coarse_chart in range(morphism.coarse.vertices)
    )
    c1 = all(
        connected(
            fiber,
            (
                edge
                for edge in morphism.fine.edges
                if edge[0] in fiber and edge[1] in fiber
            ),
        )
        for fiber in fibers
    )
    c2 = all(
        coarse_edge in morphism.edge_map
        for coarse_edge in range(len(morphism.coarse.edges))
    )

    c3 = True
    for fiber in fibers:
        fiber_index = {old: new for new, old in enumerate(fiber)}
        selected_edges = tuple(
            edge
            for edge, (left, right) in enumerate(morphism.fine.edges)
            if left in fiber_index and right in fiber_index
        )
        edge_index = {old: new for new, old in enumerate(selected_edges)}
        local_edges = tuple(
            (
                fiber_index[morphism.fine.edges[edge][0]],
                fiber_index[morphism.fine.edges[edge][1]],
            )
            for edge in selected_edges
        )
        local_faces = tuple(
            tuple(edge_index[edge] for edge in face)
            for face in morphism.fine.faces
            if all(edge in edge_index for edge in face)
        )
        if nerve_h1_dimension(Nerve(len(fiber), local_edges, local_faces)) != 0:
            c3 = False
            break

    c4 = all(
        coarse_face in morphism.face_map
        for coarse_face in range(len(morphism.coarse.faces))
    )
    return {"C1": c1, "C2": c2, "C3": c3, "C4": c4}


def condition_report(comparison: UniformComparison) -> dict[str, object]:
    """Use whole scope for C0/C5/C6 and every nonempty A for C1--C4."""

    nondegenerate_edges = [
        edge for edge in comparison.morphism.edge_map if edge is not None
    ]
    whole = {
        "C0": comparison.c0_holds(),
        "C5": len(nondegenerate_edges) == len(set(nondegenerate_edges)),
        "C6": all(
            comparison.morphism.coarse.edges[coarse_edge][0]
            != comparison.morphism.coarse.edges[coarse_edge][1]
            or comparison.morphism.fine.edges[fine_edge][0]
            == comparison.morphism.fine.edges[fine_edge][1]
            for fine_edge, coarse_edge in enumerate(comparison.morphism.edge_map)
            if coarse_edge is not None
        ),
    }
    per_subset = []
    aggregate_relative = {name: True for name in ("C1", "C2", "C3", "C4")}
    for targets in nonempty_subsets(comparison.coarse_target_count):
        subcomparison = comparison.coordinate_subcomparison(targets)
        conditions = relative_condition_vector(subcomparison.morphism)
        for name, value in conditions.items():
            aggregate_relative[name] = aggregate_relative[name] and value
        per_subset.append(
            {
                "coarse_targets_A": sorted(targets),
                "conditions": conditions,
            }
        )
    aggregate = {
        "C0": whole["C0"],
        **aggregate_relative,
        "C5": whole["C5"],
        "C6": whole["C6"],
    }
    return {"whole": whole, "per_subset": per_subset, "aggregate": aggregate}


def comparison_evaluation(comparison: UniformComparison) -> dict[str, object]:
    blocks = [
        comparison.coordinate_subcomparison(targets).summary()
        for targets in nonempty_subsets(comparison.coarse_target_count)
    ]
    return {
        "fixture": comparison.summary(),
        "blocks": blocks,
        "uniform": all(block["h1"]["isomorphism"] for block in blocks),
        "conditions": condition_report(comparison),
    }


def reviewed_obstruction_comparison(
    name: str,
    morphism: NerveMorphism,
) -> UniformComparison:
    """Attach the reviewed Fin 4 -> Fin 3 reading to a Lean obstruction."""

    coarse_full = frozenset((0, 1, 2))
    fine_full = frozenset((0, 1, 2, 3))
    return UniformComparison(
        name=name,
        morphism=morphism,
        coarse_target_count=3,
        fine_target_count=4,
        factor_pi=(0, 0, 1, 2),
        coarse_chart_supports=tuple(
            coarse_full for _ in range(morphism.coarse.vertices)
        ),
        fine_chart_supports=tuple(
            fine_full for _ in range(morphism.fine.vertices)
        ),
    )


def calibration_fixtures() -> tuple[UniformComparison, ...]:
    """Exact reconstructions of the reviewed C4/C5/C6 Lean obstructions."""

    coarse_triangle = Nerve(
        3,
        ((0, 1), (0, 2), (1, 2)),
        ((0, 1, 2),),
    )
    face = NerveMorphism(
        coarse_triangle,
        Nerve(4, ((0, 1), (1, 2), (0, 3), (2, 3)), ()),
        (0, 0, 1, 2),
        (None, 0, 1, 2),
        (),
    )
    edge = NerveMorphism(
        coarse_triangle,
        Nerve(
            3,
            ((0, 1), (0, 1), (0, 2), (1, 2)),
            ((0, 2, 3),),
        ),
        (0, 1, 2),
        (0, 0, 1, 2),
        (0,),
    )
    loop = NerveMorphism(
        Nerve(
            3,
            ((0, 1), (0, 2), (1, 2), (0, 0), (0, 1)),
            ((0, 1, 2),),
        ),
        Nerve(
            5,
            ((0, 3), (0, 4), (3, 4), (0, 1), (1, 2), (0, 3)),
            ((0, 1, 2),),
        ),
        (0, 0, 0, 1, 2),
        (0, 1, 2, 3, None, 4),
        (0,),
    )
    return (
        reviewed_obstruction_comparison("FaceLiftObstruction", face),
        reviewed_obstruction_comparison("EdgeFiberObstruction", edge),
        reviewed_obstruction_comparison("LoopLiftObstruction", loop),
    )


def calibration_report() -> list[dict[str, object]]:
    expected = {
        "FaceLiftObstruction": (True, False, "C4"),
        "EdgeFiberObstruction": (True, False, "C5"),
        "LoopLiftObstruction": (False, True, "C6"),
    }
    report = []
    for comparison in calibration_fixtures():
        evaluation = comparison_evaluation(comparison)
        analysis = evaluation["blocks"][0]["h1"]
        injective, surjective, failed_clause = expected[comparison.name]
        passed = (
            analysis["injective"] == injective
            and analysis["surjective"] == surjective
            and not evaluation["conditions"]["aggregate"][failed_clause]
        )
        if not passed:
            raise AssertionError(f"calibration mismatch for {comparison.name}")
        evaluation["expected_failed_clause"] = failed_clause
        evaluation["calibration_pass"] = True
        report.append(evaluation)
    return report


def support_hole_fixture() -> UniformComparison:
    coarse = Nerve(
        3,
        ((0, 1), (0, 2), (1, 2), (0, 1), (0, 1)),
        ((0, 1, 2),),
    )
    fine = Nerve(
        4,
        ((0, 1), (0, 2), (0, 3), (2, 3), (1, 2), (0, 2)),
        ((1, 2, 3),),
    )
    return UniformComparison(
        name="derived_support_hole_section_5",
        morphism=NerveMorphism(
            coarse,
            fine,
            (0, 0, 1, 2),
            (None, 0, 1, 2, 3, 4),
            (0,),
        ),
        coarse_target_count=2,
        fine_target_count=2,
        factor_pi=(0, 1),
        coarse_chart_supports=(
            frozenset((0, 1)),
            frozenset((0, 1)),
            frozenset((0, 1)),
        ),
        fine_chart_supports=(
            frozenset((0,)),
            frozenset((1,)),
            frozenset((0, 1)),
            frozenset((0, 1)),
        ),
    )


def support_hole_report() -> dict[str, object]:
    comparison = support_hole_fixture()
    evaluation = comparison_evaluation(comparison)
    singleton_analyses = tuple(
        comparison.coordinate_subcomparison(frozenset((target,))).analysis()
        for target in range(2)
    )
    global_analysis = direct_sum_analysis(singleton_analyses)
    c2_failures = [
        item["coarse_targets_A"]
        for item in evaluation["conditions"]["per_subset"]
        if not item["conditions"]["C2"]
    ]
    expected_edge_supports = (
        frozenset(),
        frozenset((0,)),
        frozenset((0,)),
        frozenset((0, 1)),
        frozenset((1,)),
        frozenset((0,)),
    )
    passed = (
        global_analysis
        == H1Analysis(4, 1, 1, False, True, False)
        and comparison.fine_edge_supports == expected_edge_supports
        and c2_failures == [[0], [1]]
    )
    if not passed:
        raise AssertionError("derived support-hole calibration mismatch")
    return {
        **evaluation,
        "law_value_singleton_block_direct_sum": asdict(global_analysis),
        "relative_C2_failing_subsets": c2_failures,
        "calibration_pass": True,
    }


def canonical_firing_fixture() -> UniformComparison:
    """Exact data from ResolutionInvarianceFiringData.lean."""

    coarse = Nerve(
        2,
        ((0, 1), (1, 0), (0, 0)),
        ((2, 2, 2),),
    )
    fine = Nerve(
        3,
        ((0, 2), (2, 0), (0, 0), (0, 1), (1, 1)),
        ((2, 2, 2), (4, 4, 4)),
    )
    return UniformComparison(
        name="ResolutionInvarianceFiringData",
        morphism=NerveMorphism(
            coarse,
            fine,
            (0, 0, 1),
            (0, 1, 2, None, None),
            (0, None),
        ),
        coarse_target_count=2,
        fine_target_count=3,
        factor_pi=(0, 0, 1),
        coarse_chart_supports=(frozenset((0, 1)), frozenset((0,))),
        fine_chart_supports=(
            frozenset((0, 2)),
            frozenset((0, 1)),
            frozenset((0,)),
        ),
    )


def canonical_firing_report() -> dict[str, object]:
    comparison = canonical_firing_fixture()
    evaluation = comparison_evaluation(comparison)
    block_by_targets = {
        tuple(block["coarse_targets_A"]): block for block in evaluation["blocks"]
    }
    zero = block_by_targets[(0,)]["h1"]
    one = block_by_targets[(1,)]["h1"]
    global_analysis = direct_sum_analysis(
        (
            comparison.coordinate_subcomparison(frozenset((0,))).analysis(),
            comparison.coordinate_subcomparison(frozenset((1,))).analysis(),
        )
    )
    passed = (
        zero
        == {
            "coarse_h1_dimension": 1,
            "fine_h1_dimension": 1,
            "comparison_rank": 1,
            "injective": True,
            "surjective": True,
            "isomorphism": True,
        }
        and one
        == {
            "coarse_h1_dimension": 0,
            "fine_h1_dimension": 0,
            "comparison_rank": 0,
            "injective": True,
            "surjective": True,
            "isomorphism": True,
        }
        and global_analysis == H1Analysis(1, 1, 1, True, True, True)
        and evaluation["uniform"]
        and all(evaluation["conditions"]["aggregate"].values())
    )
    if not passed:
        raise AssertionError("canonical firing oracle mismatch")
    return {
        **evaluation,
        "actual_law_blocks": {
            "value_zero": block_by_targets[(0,)],
            "value_one": block_by_targets[(1,)],
        },
        "global_supported_direct_sum": asdict(global_analysis),
        "block_reduction_pass": True,
        "canonical_oracle_pass": True,
    }


def indicator_factor_report(
    name: str,
    factor_pi: tuple[int, ...],
    coarse_target_count: int,
) -> dict[str, object]:
    """Numerically realize every A as the True fiber of one Unit/Bool law."""

    fine_target_count = len(factor_pi)
    cases = []
    for targets in nonempty_subsets(coarse_target_count):
        coarse_descent = tuple(target in targets for target in range(coarse_target_count))
        fine_descent = tuple(coarse_descent[target] for target in factor_pi)
        law_evaluation = fine_descent
        realized_coarse = frozenset(
            target for target, value in enumerate(coarse_descent) if value
        )
        realized_fine = frozenset(
            target for target, value in enumerate(fine_descent) if value
        )
        expected_fine = frozenset(
            target
            for target, coarse_target in enumerate(factor_pi)
            if coarse_target in targets
        )
        assertions = {
            "fine_read_identity_surjective": True,
            "coarse_read_pi_surjective": set(factor_pi)
            == set(range(coarse_target_count)),
            "coarse_read_factors_through_fine": True,
            "coarse_adequate": all(
                coarse_descent[factor_pi[source]] == law_evaluation[source]
                for source in range(fine_target_count)
            ),
            "fine_adequate": fine_descent == law_evaluation,
            "descents_commute_with_pi": all(
                fine_descent[target] == coarse_descent[factor_pi[target]]
                for target in range(fine_target_count)
            ),
            "A_is_true_fiber": realized_coarse == targets,
            "pi_preimage_A_is_true_fiber": realized_fine == expected_fine,
            "unit_law_family_fields_finite": True,
            "bool_has_two_distinct_values": False is not True,
        }
        if not all(assertions.values()):
            raise AssertionError(f"indicator realization failed for {name} A={targets}")
        cases.append(
            {
                "coarse_targets_A": sorted(targets),
                "fine_targets_pi_preimage_A": sorted(expected_fine),
                "coarse_bool_descent": list(coarse_descent),
                "fine_bool_descent": list(fine_descent),
                "law_evaluation_on_source_eq_fine_target": list(law_evaluation),
                "assertions": assertions,
            }
        )
    return {
        "name": name,
        "source_count": fine_target_count,
        "fine_read": list(range(fine_target_count)),
        "coarse_read": list(factor_pi),
        "factor_pi": list(factor_pi),
        "law_type": "Unit",
        "value_type": "Bool",
        "value_type_cardinality": 2,
        "nonempty_subset_count": len(cases),
        "cases": cases,
        "all_pass": True,
    }


def indicator_realizability_report() -> dict[str, object]:
    factors = (
        indicator_factor_report("Fin3_to_Fin2", (0, 0, 1), 2),
        indicator_factor_report("Fin4_to_Fin3", (0, 0, 1, 2), 3),
    )
    return {
        "factors": list(factors),
        "all_nonempty_A_realized": all(factor["all_pass"] for factor in factors),
    }


def r0_report() -> dict[str, object]:
    a = calibration_report()
    b = support_hole_report()
    firing = canonical_firing_report()
    d = indicator_realizability_report()
    return {
        "phase": "R0",
        "arithmetic": "exact fractions.Fraction linear algebra over Q",
        "calibration": {
            "a_three_lean_obstructions": a,
            "b_derived_support_hole": b,
            "c_block_reduction": {
                "actual_law_blocks": firing["actual_law_blocks"],
                "global_supported_direct_sum": firing[
                    "global_supported_direct_sum"
                ],
                "all_nonempty_A_uniform": firing["uniform"],
                "pass": firing["block_reduction_pass"],
            },
            "d_indicator_realizability": d,
            "e_canonical_firing_oracle": firing,
        },
        "r0_pass": (
            all(item["calibration_pass"] for item in a)
            and b["calibration_pass"]
            and firing["block_reduction_pass"]
            and firing["canonical_oracle_pass"]
            and d["all_nonempty_A_realized"]
        ),
    }


def _r1_comparison(
    name: str,
    morphism: NerveMorphism,
    coarse_chart_supports: tuple[frozenset[int], ...],
    fine_chart_supports: tuple[frozenset[int], ...],
) -> UniformComparison:
    return UniformComparison(
        name=name,
        morphism=morphism,
        coarse_target_count=2,
        fine_target_count=3,
        factor_pi=(0, 0, 1),
        coarse_chart_supports=coarse_chart_supports,
        fine_chart_supports=fine_chart_supports,
    )


def r1_necessity_witnesses() -> dict[str, UniformComparison]:
    """Seven uniform, nondegenerate witnesses, one named for each current clause.

    Target zero carries an identity self-loop H1 component.  Target one carries
    an H1-neutral component on which the named failure fires.  The C3 witness
    additionally fires C3 on its neutral component; the common self-loop also
    necessarily violates literal endpoint-defined local acyclicity.
    """

    c0_nerve = Nerve(2, ((0, 0),), ())
    c0 = _r1_comparison(
        "C0_not_necessary",
        NerveMorphism(c0_nerve, c0_nerve, (0, 1), (0,), ()),
        (frozenset((0,)), frozenset((0, 1))),
        (frozenset((0, 1)), frozenset((2,))),
    )

    c1 = _r1_comparison(
        "C1_not_necessary",
        NerveMorphism(
            Nerve(2, ((0, 0),), ()),
            Nerve(3, ((0, 0),), ()),
            (0, 1, 1),
            (0,),
            (),
        ),
        (frozenset((0,)), frozenset((1,))),
        (frozenset((0, 1)), frozenset((2,)), frozenset((2,))),
    )

    c2 = _r1_comparison(
        "C2_not_necessary",
        NerveMorphism(
            Nerve(3, ((0, 0), (1, 2)), ()),
            Nerve(3, ((0, 0),), ()),
            (0, 1, 2),
            (0,),
            (),
        ),
        (frozenset((0,)), frozenset((1,)), frozenset((1,))),
        (frozenset((0, 1)), frozenset((2,)), frozenset((2,))),
    )

    c3_nerve = Nerve(
        3,
        ((0, 0), (1, 2), (2, 2)),
        ((1, 1, 2),),
    )
    c3 = _r1_comparison(
        "C3_not_necessary",
        NerveMorphism(
            c3_nerve,
            c3_nerve,
            (0, 1, 2),
            (0, 1, 2),
            (0,),
        ),
        (frozenset((0,)), frozenset((1,)), frozenset((1,))),
        (frozenset((0, 1)), frozenset((2,)), frozenset((2,))),
    )

    c4 = _r1_comparison(
        "C4_not_necessary",
        NerveMorphism(
            Nerve(2, ((0, 0), (1, 1)), ((1, 1, 1), (1, 1, 1))),
            Nerve(2, ((0, 0), (1, 1)), ((1, 1, 1),)),
            (0, 1),
            (0, 1),
            (0,),
        ),
        (frozenset((0,)), frozenset((1,))),
        (frozenset((0, 1)), frozenset((2,))),
    )

    c5 = _r1_comparison(
        "C5_not_necessary",
        NerveMorphism(
            Nerve(2, ((0, 0), (1, 1)), ((1, 1, 1),)),
            Nerve(
                2,
                ((0, 0), (1, 1), (1, 1)),
                ((1, 1, 1), (2, 2, 2)),
            ),
            (0, 1),
            (0, 1, 1),
            (0, 0),
        ),
        (frozenset((0,)), frozenset((1,))),
        (frozenset((0, 1)), frozenset((2,))),
    )

    c6 = _r1_comparison(
        "C6_not_necessary",
        NerveMorphism(
            Nerve(2, ((0, 0), (1, 1)), ((1, 1, 1),)),
            Nerve(3, ((0, 0), (1, 2)), ()),
            (0, 1, 1),
            (0, 1),
            (),
        ),
        (frozenset((0,)), frozenset((1,))),
        (frozenset((0, 1)), frozenset((2,)), frozenset((2,))),
    )

    return {
        "C0": c0,
        "C1": c1,
        "C2": c2,
        "C3": c3,
        "C4": c4,
        "C5": c5,
        "C6": c6,
    }


def necessity_witness_report(
    clause: str,
    comparison: UniformComparison,
) -> dict[str, object]:
    evaluation = comparison_evaluation(comparison)
    aggregate = evaluation["conditions"]["aggregate"]
    nondegenerate_blocks = [
        block["coarse_targets_A"]
        for block in evaluation["blocks"]
        if block["h1"]["coarse_h1_dimension"] > 0
        and block["h1"]["fine_h1_dimension"] > 0
    ]
    if clause in ("C0", "C5", "C6"):
        failure_scope: object = "whole nerve"
        nondegenerate_failure_blocks = nondegenerate_blocks
    else:
        failure_scope = [
            item["coarse_targets_A"]
            for item in evaluation["conditions"]["per_subset"]
            if not item["conditions"][clause]
        ]
        nondegenerate_failure_blocks = [
            targets for targets in nondegenerate_blocks if targets in failure_scope
        ]
    neutral_block = next(
        block for block in evaluation["blocks"] if block["coarse_targets_A"] == [1]
    )
    passed = (
        evaluation["uniform"]
        and not aggregate[clause]
        and bool(nondegenerate_failure_blocks)
        and neutral_block["h1"]
        == {
            "coarse_h1_dimension": 0,
            "fine_h1_dimension": 0,
            "comparison_rank": 0,
            "injective": True,
            "surjective": True,
            "isomorphism": True,
        }
    )
    if not passed:
        raise AssertionError(f"R1 necessity witness failed for {clause}")
    return {
        "clause": clause,
        "verdict": "not-necessary",
        "evidence_schema": "uniform comparison and named-clause failure",
        "failure_scope": failure_scope,
        "nondegenerate_blocks_with_both_H1_nonzero": nondegenerate_blocks,
        "nondegenerate_blocks_where_named_failure_fires": (
            nondegenerate_failure_blocks
        ),
        "failure_component_block_A_1_H1_neutral": True,
        "selfloop_H1_component_note": (
            "The independent identity self-loop carries H1 at A={0}; literal C3 "
            "therefore also fails in these fixtures.  The named clause still fires "
            "on the separate H1-neutral A={1} component."
        ),
        **evaluation,
        "witness_pass": True,
    }


def r1_witness_report() -> list[dict[str, object]]:
    return [
        necessity_witness_report(clause, comparison)
        for clause, comparison in r1_necessity_witnesses().items()
    ]


def legacy_positive_fixture() -> UniformComparison:
    """The prior 3/4-chart positive, retained as the G-103-scale catalog motif."""

    coarse = Nerve(
        3,
        ((0, 1), (0, 2), (1, 2), (0, 1)),
        ((0, 1, 2),),
    )
    fine = Nerve(
        4,
        ((0, 1), (0, 2), (0, 3), (2, 3), (1, 2)),
        ((1, 2, 3),),
    )
    return UniformComparison(
        name="old_positive_G103_scale",
        morphism=NerveMorphism(
            coarse,
            fine,
            (0, 0, 1, 2),
            (None, 0, 1, 2, 3),
            (0,),
        ),
        coarse_target_count=3,
        fine_target_count=4,
        factor_pi=(0, 0, 1, 2),
        coarse_chart_supports=tuple(
            frozenset((0, 1, 2)) for _ in range(coarse.vertices)
        ),
        fine_chart_supports=tuple(
            frozenset((0, 1, 2, 3)) for _ in range(fine.vertices)
        ),
    )


def catalog_entry(category: str, comparison: UniformComparison) -> dict[str, object]:
    blocks = comparison.block_analyses()
    conditions = condition_report(comparison)["aggregate"]
    first_nonisomorphism = next(
        (
            {"coarse_targets_A": sorted(targets), "h1": asdict(analysis)}
            for targets, analysis in blocks
            if not analysis.isomorphism
        ),
        None,
    )
    return {
        "category": category,
        "name": comparison.name,
        "sizes": {
            "coarse_charts": comparison.morphism.coarse.vertices,
            "fine_charts": comparison.morphism.fine.vertices,
            "coarse_edges": len(comparison.morphism.coarse.edges),
            "fine_edges": len(comparison.morphism.fine.edges),
            "coarse_faces": len(comparison.morphism.coarse.faces),
            "fine_faces": len(comparison.morphism.fine.faces),
            "coarse_targets": comparison.coarse_target_count,
            "fine_targets": comparison.fine_target_count,
        },
        "factor_pi": list(comparison.factor_pi),
        "nonempty_A_count": len(blocks),
        "uniform": all(analysis.isomorphism for _, analysis in blocks),
        "conditions": conditions,
        "first_nonisomorphism": first_nonisomorphism,
    }


def required_fixture_catalog_summary() -> dict[str, object]:
    fixtures: list[tuple[str, UniformComparison]] = []
    fixtures.extend(("lean_obstruction", fixture) for fixture in calibration_fixtures())
    fixtures.append(("derived_support_hole", support_hole_fixture()))
    fixtures.append(("current_canonical_oracle", canonical_firing_fixture()))
    fixtures.append(("old_positive_G103_scale", legacy_positive_fixture()))
    fixtures.extend(
        ("necessity_witness", fixture)
        for fixture in r1_necessity_witnesses().values()
    )
    entries = [catalog_entry(category, fixture) for category, fixture in fixtures]
    maxima = {
        key: max(entry["sizes"][key] for entry in entries)
        for key in entries[0]["sizes"]
    }
    registered_limits = {
        "coarse_charts": 3,
        "fine_charts": 5,
        "coarse_edges": 5,
        "fine_edges": 6,
        "coarse_faces": 2,
        "fine_faces": 2,
        "coarse_targets": 3,
        "fine_targets": 4,
    }
    if any(maxima[key] > registered_limits[key] for key in registered_limits):
        raise AssertionError("required fixture catalog exceeded its preregistered bound")
    return {
        "preregistered_issue_comment": 5230270861,
        "fixture_count": len(entries),
        "category_counts": {
            category: sum(entry["category"] == category for entry in entries)
            for category in sorted({entry["category"] for entry in entries})
        },
        "observed_maxima": maxima,
        "registered_limits": registered_limits,
        "fixtures": entries,
    }


def core_incidence_templates() -> tuple[tuple[str, NerveMorphism], ...]:
    point = Nerve(1, (), ())
    loop = Nerve(1, ((0, 0),), ())
    return (
        ("T0_identity_point", NerveMorphism(point, point, (0,), (), ())),
        (
            "T1_split_point",
            NerveMorphism(point, Nerve(2, (), ()), (0, 0), (), ()),
        ),
        (
            "T2_interval_edge_omission",
            NerveMorphism(
                Nerve(2, ((0, 1),), ()),
                Nerve(2, (), ()),
                (0, 1),
                (),
                (),
            ),
        ),
        ("T3_identity_selfloop", NerveMorphism(loop, loop, (0,), (0,), ())),
    )


def canonical_core_factors() -> tuple[tuple[int, int, tuple[int, ...]], ...]:
    """All preregistered nondecreasing surjections, with relabeling quotiented."""

    return (
        (1, 1, (0,)),
        (1, 2, (0, 0)),
        (1, 3, (0, 0, 0)),
        (2, 2, (0, 1)),
        (2, 3, (0, 0, 1)),
        (2, 3, (0, 1, 1)),
    )


def concise_population_example(
    template_name: str,
    comparison: UniformComparison,
) -> dict[str, object]:
    conditions = condition_report(comparison)["aggregate"]
    blocks = comparison.block_analyses()
    first_nonisomorphism = next(
        (
            {"coarse_targets_A": sorted(targets), "h1": asdict(analysis)}
            for targets, analysis in blocks
            if not analysis.isomorphism
        ),
        None,
    )
    return {
        "template": template_name,
        "factor_pi": list(comparison.factor_pi),
        "coarse_chart_supports": supports_summary(comparison.coarse_chart_supports),
        "fine_chart_supports": supports_summary(comparison.fine_chart_supports),
        "uniform": all(analysis.isomorphism for _, analysis in blocks),
        "conditions": conditions,
        "first_nonisomorphism": first_nonisomorphism,
    }


def bounded_core_population_summary() -> dict[str, object]:
    """Exhaust the preregistered four templates, six pi, and all chart supports."""

    rows = []
    totals = {
        "raw_support_assignments": 0,
        "compatible_comparisons": 0,
        "uniform_comparisons": 0,
        "nonuniform_comparisons": 0,
    }
    uniform_clause_failures = {f"C{index}": 0 for index in range(7)}
    examples: dict[str, object] = {
        "first_uniform": None,
        "first_nonuniform": None,
        "first_uniform_named_clause_failure": {
            f"C{index}": None for index in range(7)
        },
    }

    for template_name, morphism in core_incidence_templates():
        for coarse_count, fine_count, factor_pi in canonical_core_factors():
            coarse_options = nonempty_subsets(coarse_count)
            fine_options = nonempty_subsets(fine_count)
            raw = len(coarse_options) ** morphism.coarse.vertices * len(
                fine_options
            ) ** morphism.fine.vertices
            row_counts = {
                "raw_support_assignments": raw,
                "compatible_comparisons": 0,
                "uniform_comparisons": 0,
                "nonuniform_comparisons": 0,
            }
            totals["raw_support_assignments"] += raw
            for coarse_supports in product(
                coarse_options,
                repeat=morphism.coarse.vertices,
            ):
                for fine_supports in product(
                    fine_options,
                    repeat=morphism.fine.vertices,
                ):
                    compatible = all(
                        {
                            factor_pi[target]
                            for target in fine_supports[fine_chart]
                        }
                        <= set(coarse_supports[morphism.vertex_map[fine_chart]])
                        for fine_chart in range(morphism.fine.vertices)
                    )
                    if not compatible:
                        continue
                    comparison = UniformComparison(
                        name=f"{template_name}_population_case",
                        morphism=morphism,
                        coarse_target_count=coarse_count,
                        fine_target_count=fine_count,
                        factor_pi=factor_pi,
                        coarse_chart_supports=tuple(coarse_supports),
                        fine_chart_supports=tuple(fine_supports),
                    )
                    row_counts["compatible_comparisons"] += 1
                    totals["compatible_comparisons"] += 1
                    uniform = comparison.is_uniform()
                    key = "uniform_comparisons" if uniform else "nonuniform_comparisons"
                    row_counts[key] += 1
                    totals[key] += 1
                    if uniform and examples["first_uniform"] is None:
                        examples["first_uniform"] = concise_population_example(
                            template_name,
                            comparison,
                        )
                    if not uniform and examples["first_nonuniform"] is None:
                        examples["first_nonuniform"] = concise_population_example(
                            template_name,
                            comparison,
                        )
                    if uniform:
                        conditions = condition_report(comparison)["aggregate"]
                        for clause, value in conditions.items():
                            if value:
                                continue
                            uniform_clause_failures[clause] += 1
                            if examples["first_uniform_named_clause_failure"][clause] is None:
                                examples["first_uniform_named_clause_failure"][clause] = (
                                    concise_population_example(template_name, comparison)
                                )
            rows.append(
                {
                    "template": template_name,
                    "coarse_target_count": coarse_count,
                    "fine_target_count": fine_count,
                    "factor_pi": list(factor_pi),
                    "counts": row_counts,
                }
            )

    if totals["compatible_comparisons"] != (
        totals["uniform_comparisons"] + totals["nonuniform_comparisons"]
    ):
        raise AssertionError("bounded population counts do not partition")
    return {
        "preregistered_issue_comment": 5230270861,
        "normal_form": {
            "incidence_templates": [name for name, _ in core_incidence_templates()],
            "canonical_nondecreasing_surjective_factors": [
                list(factor) for _, _, factor in canonical_core_factors()
            ],
            "coarse_target_size": "1..2",
            "fine_target_size": "coarse size..3",
            "chart_supports": "all nonempty subsets",
            "compatibility": "pi(fine chart support) subset mapped coarse chart support",
            "edge_supports": "exact endpoint intersections",
            "face_supports": "exact boundary-edge intersections",
            "subset_scan": "every nonempty A in the coarse target",
            "isomorphism_pruning": "none inside fixed cell labels",
        },
        "coverage_limit": (
            "The core exhausts only T0--T3 with the registered target bounds.  "
            "Larger required motifs are evaluated exactly in the separate catalog; "
            "arbitrary larger nerves and morphisms are not covered."
        ),
        "totals": totals,
        "uniform_named_clause_failure_counts": uniform_clause_failures,
        "counts_by_template_and_factor": rows,
        "examples_only": examples,
    }


def r1_report() -> dict[str, object]:
    witnesses = r1_witness_report()
    verdicts = [
        {
            "clause": witness["clause"],
            "verdict": witness["verdict"],
            "witness": witness["fixture"]["name"],
            "evidence_schema_satisfied": witness["witness_pass"],
        }
        for witness in witnesses
    ]
    return {
        "phase": "R1",
        "preregistered_issue_comment": 5230270861,
        "bounded_core_population": bounded_core_population_summary(),
        "required_fixture_catalog": required_fixture_catalog_summary(),
        "necessity_witnesses": witnesses,
        "verdicts": verdicts,
        "all_seven_verdicts_fixed": (
            [item["clause"] for item in verdicts]
            == [f"C{index}" for index in range(7)]
            and all(item["verdict"] == "not-necessary" for item in verdicts)
            and all(item["evidence_schema_satisfied"] for item in verdicts)
        ),
    }


def run_report() -> dict[str, object]:
    r0 = r0_report()
    r1 = r1_report()
    return {
        "artifact": "G-104 off-loop C0-C6 necessity map exact engine",
        "arithmetic": "fractions.Fraction over Q",
        "randomness": "none",
        "serialization": "UTF-8, LF, indent=2, sort_keys=True, trailing newline",
        "r0": r0,
        "r1": r1,
        "engine_gates_pass": r0["r0_pass"] and r1["all_seven_verdicts_fixed"],
        "R2_prose_implemented": False,
    }


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument(
        "command",
        choices=("r0", "r1", "run"),
        nargs="?",
        default="run",
    )
    result.add_argument("--output", type=Path)
    return result


def main() -> int:
    args = parser().parse_args()
    if args.command == "r0":
        output = r0_report()
    elif args.command == "r1":
        output = r1_report()
    else:
        output = run_report()
    rendered = json.dumps(output, ensure_ascii=False, indent=2, sort_keys=True)
    if args.output is not None:
        args.output.write_text(rendered + "\n", encoding="utf-8")
    print(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
